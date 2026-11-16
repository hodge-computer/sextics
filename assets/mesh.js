/* Decoding and validation of the homepage's saved mesh, independent of GPU resource lifetime.
   Atlas meshes are generated locally by slice-mesh.js. */
((root) => {
  async function validateMesh(buffer, indexBuffer, meta, checkpoint) {
    const STRIDE = 9;
    if (!(buffer instanceof ArrayBuffer) || !(indexBuffer instanceof ArrayBuffer))
      throw new Error('Missing geometry buffers.');
    if (meta?.format !== 'indexed-p3-n3-phase2-d1-v3' || meta.stride !== STRIDE)
      throw new Error('Unrecognized vertex layout.');
    if (!Number.isInteger(meta.vertexCount) || meta.vertexCount < 3 || meta.vertexCount > 2000000)
      throw new Error('Vertex budget exceeded.');
    if (
      !Number.isInteger(meta.triangleCount) ||
      meta.triangleCount < 1 ||
      meta.triangleCount > 4000000
    )
      throw new Error('Triangle budget exceeded.');
    if (
      buffer.byteLength !== meta.vertexCount * STRIDE * 4 ||
      indexBuffer.byteLength !== meta.triangleCount * 3 * 4
    )
      throw new Error('Geometry buffer length mismatch.');
    if (buffer.byteLength + indexBuffer.byteLength > 128 * 1024 * 1024)
      throw new Error('Geometry memory budget exceeded.');
    if (
      !Number.isFinite(meta.displayScale) ||
      meta.displayScale <= 0 ||
      !Array.isArray(meta.centerOriginal) ||
      meta.centerOriginal.length !== 3 ||
      !meta.centerOriginal.every(Number.isFinite)
    )
      throw new Error('Invalid mesh transform.');
    if (!Number.isFinite(meta.edgeBound) || meta.edgeBound <= 0)
      throw new Error('Missing triangle bound.');
    const v = new Float32Array(buffer),
      ix = new Uint32Array(indexBuffer);
    // Compact-domain meshes may extend beyond the usual normalized box.
    const positionBound =
      meta.samplingMode === 'sphere' ? Math.min(4, Number(meta.positionBound) || 1.01) : 1.01;
    for (let n = 0; n < meta.vertexCount; n++) {
      if (n % 8192 === 0) await checkpoint();
      const o = n * STRIDE;
      for (let j = 0; j < STRIDE; j++)
        if (!Number.isFinite(v[o + j])) throw new Error('Non-finite mesh attribute rejected.');
      if (Math.max(Math.abs(v[o]), Math.abs(v[o + 1]), Math.abs(v[o + 2])) > positionBound)
        throw new Error('Corrupt position data rejected.');
      if (Math.abs(Math.hypot(v[o + 3], v[o + 4], v[o + 5]) - 1) > 0.015)
        throw new Error('Corrupt normal data rejected.');
    }
    const bound = meta.edgeBound + 1e-5;
    for (let q = 0; q < ix.length; q += 3) {
      if (q % 24576 === 0) await checkpoint();
      for (let j = 0; j < 3; j++) {
        const a = ix[q + j],
          b = ix[q + ((j + 1) % 3)];
        if (a >= meta.vertexCount || b >= meta.vertexCount)
          throw new Error('Triangle index out of range.');
        const i = a * STRIDE,
          k = b * STRIDE;
        if (Math.hypot(v[i] - v[k], v[i + 1] - v[k + 1], v[i + 2] - v[k + 2]) > bound)
          throw new Error('Corrupt triangle extent rejected.');
      }
    }
    return true;
  }

  function unpackDeltaPlanes(buffer, elementBytes, stride) {
    const bytes = new Uint8Array(buffer);
    if (bytes.length % (elementBytes * stride) !== 0)
      throw new Error('Invalid delta-packed mesh stream.');
    const count = bytes.length / elementBytes,
      output = new Uint8Array(bytes.length);
    // Restore byte order, then the exact unsigned modular differences.
    for (let byte = 0; byte < elementBytes; byte++)
      for (let i = 0; i < count; i++) output[i * elementBytes + byte] = bytes[byte * count + i];
    const values =
      elementBytes === 2 ? new Uint16Array(output.buffer) : new Uint32Array(output.buffer);
    for (let i = stride; i < count; i++) values[i] += values[i - stride];
    return output.buffer;
  }
  function create(assetBase, usable = () => true) {
    let entry = null;
    async function decode(path, signal) {
      const url = new URL(path, assetBase);
      const check = () => {
        signal.throwIfAborted();
        if (!usable()) throw new Error('Cancelled');
      };
      // Share one work budget across decoding and validation. Yield to controls
      // and the worker heartbeat without paying a timer delay for every chunk.
      let deadline = performance.now() + 16;
      async function checkpoint() {
        check();
        if (performance.now() < deadline) return;
        await new Promise((resolve) => setTimeout(resolve, 0));
        check();
        deadline = performance.now() + 16;
      }
      const response = await fetch(url, { signal });
      if (!response.ok) throw new Error('Missing saved slice.');
      const manifest = await response.json(),
        root = new URL('.', url);
      check();
      async function bytes(name) {
        check();
        const response = await fetch(new URL(name, root), { signal });
        if (!response.ok) throw new Error('Missing local mesh asset: ' + name);
        if (typeof DecompressionStream === 'undefined')
          throw new Error('This browser cannot decompress the saved mesh.');
        const stream = response.body.pipeThrough(new DecompressionStream('gzip'), { signal });
        const buffer = await new Response(stream).arrayBuffer();
        check();
        return buffer;
      }
      let buffer, indexBuffer;
      if (manifest.encoding === 'quantized-p3-n3-phase2-delta-v1') {
        const parts = await Promise.all(
          ['position', 'normal', 'complex', 'indices'].map((name) => bytes(manifest[name]))
        );
        check();
        for (let i = 0; i < 4; i++)
          parts[i] = unpackDeltaPlanes(parts[i], i === 3 ? 4 : 2, i < 2 ? 3 : i === 2 ? 2 : 1);
        const pos = new Uint16Array(parts[0]),
          normal = new Int16Array(parts[1]),
          phase = new Int16Array(parts[2]),
          n = manifest.meta.vertexCount;
        if (
          !Number.isInteger(n) ||
          n < 3 ||
          n > 2000000 ||
          pos.length !== 3 * n ||
          normal.length !== 3 * n ||
          phase.length !== 2 * n
        )
          throw new Error('Invalid packed mesh.');
        const data = new Float32Array(n * 9);
        for (let i = 0; i < n; i++) {
          if (i % 8192 === 0) await checkpoint();
          for (let j = 0; j < 3; j++) {
            data[9 * i + j] =
              manifest.positionMin[j] +
              ((manifest.positionMax[j] - manifest.positionMin[j]) * pos[3 * i + j]) / 65535;
            data[9 * i + 3 + j] = normal[3 * i + j] / 32767;
          }
          data[9 * i + 6] = (phase[2 * i] / 32767) * manifest.complexScale;
          data[9 * i + 7] = (phase[2 * i + 1] / 32767) * manifest.complexScale;
        }
        buffer = data.buffer;
        indexBuffer = parts[3];
      } else throw new Error('Unrecognized mesh encoding.');
      check();
      await validateMesh(buffer, indexBuffer, manifest.meta, checkpoint);
      check();
      return { buffer, indexBuffer, meta: manifest.meta };
    }
    function load(path) {
      const url = new URL(path, assetBase).href;
      if (entry?.url === url) return entry.pending;
      entry?.controller.abort();
      const current = (entry = { url, controller: new AbortController(), complete: false });
      current.pending = decode(url, current.controller.signal).then(
        (mesh) => {
          current.complete = true;
          return mesh;
        },
        (error) => {
          if (entry === current) entry = null;
          throw error;
        }
      );
      return current.pending;
    }
    // Keep only the last completed mesh for front-page navigation; superseded
    // in-flight loads are aborted, including their decompression and validation.
    return {
      load,
      cancel() {
        if (entry && !entry.complete) {
          entry.controller.abort();
          entry = null;
        }
      },
      dispose() {
        entry?.controller.abort();
        entry = null;
      }
    };
  }
  root.HodgeMeshes = { create };
})(globalThis);
