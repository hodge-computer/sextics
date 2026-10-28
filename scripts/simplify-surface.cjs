#!/usr/bin/env node
// Offline adaptive simplification; does not change instance selection or cameras.
// Usage: node scripts/simplify-surface.cjs INPUT_MANIFEST OUTPUT_MANIFEST [TOLERANCE]
const fs = require('fs'),
  path = require('path'),
  os = require('os'),
  zlib = require('zlib'),
  { execFileSync } = require('child_process');
const [input, output, toleranceArg] = process.argv.slice(2);
const tolerance = toleranceArg === undefined ? 0.00018 : Number(toleranceArg);
if (!Number.isFinite(tolerance) || tolerance <= 0 || tolerance > 0.01)
  throw Error('Invalid plane tolerance');
if (!input || !output) throw Error('Provide input and output mesh manifests.');
const src = JSON.parse(fs.readFileSync(input)),
  root = path.dirname(input);
if (src.encoding !== 'float32-p3-n3-phase2-d1' || src.meta?.stride !== 9)
  throw Error('Expected an interleaved float mesh.');
const read = (name, T) => {
  const b = zlib.gunzipSync(fs.readFileSync(path.join(root, name)));
  return new T(b.buffer.slice(b.byteOffset, b.byteOffset + b.byteLength));
};
const v = read(src.vertices, Float32Array),
  ix = read(src.indices, Uint32Array),
  n = v.length / 9;
if (!Number.isInteger(n) || n !== src.meta.vertexCount || ix.length !== 3 * src.meta.triangleCount)
  throw Error('Invalid buffer lengths.');
if (v.some((x) => !Number.isFinite(x)) || ix.some((x) => x >= n)) throw Error('Invalid mesh data.');
const tmp = fs.mkdtempSync(path.join(os.tmpdir(), 'hodge-simplify-'));
try {
  const pos = new Float32Array(n * 6);
  for (let i = 0; i < n; i++) pos.set(v.subarray(9 * i, 9 * i + 6), 6 * i);
  fs.writeFileSync(path.join(tmp, 'positions'), Buffer.from(pos.buffer));
  fs.writeFileSync(path.join(tmp, 'indices'), Buffer.from(ix.buffer));
  const exe = path.join(tmp, 'simplify');
  execFileSync('c++', [
    '-O3',
    '-std=c++17',
    path.join(__dirname, 'simplify-surface.cpp'),
    '-o',
    exe
  ]);
  execFileSync(
    exe,
    [
      path.join(tmp, 'positions'),
      path.join(tmp, 'indices'),
      path.join(tmp, 'result'),
      String(tolerance)
    ],
    { stdio: ['ignore', 'ignore', 'inherit'] }
  );
  const raw = fs.readFileSync(path.join(tmp, 'result')),
    result = new Uint32Array(raw.buffer.slice(raw.byteOffset, raw.byteOffset + raw.byteLength));
  const remap = new Uint32Array(n).fill(0xffffffff),
    vertices = [];
  let count = 0;
  for (let i = 0; i < result.length; i++) {
    const old = result[i];
    if (old >= n) throw Error('Bad simplified index');
    if (remap[old] === 0xffffffff) {
      remap[old] = count++;
      vertices.push(...v.subarray(old * 9, old * 9 + 9));
    }
    result[i] = remap[old];
  }
  const data = new Float32Array(vertices);
  let maxEdge = 0;
  for (let q = 0; q < result.length; q += 3)
    for (let j = 0; j < 3; j++) {
      const a = 9 * result[q + j],
        b = 9 * result[q + ((j + 1) % 3)];
      maxEdge = Math.max(
        maxEdge,
        Math.hypot(data[a] - data[b], data[a + 1] - data[b + 1], data[a + 2] - data[b + 2])
      );
    }
  const base = path.basename(output, '.json'),
    dest = path.dirname(output);
  fs.mkdirSync(dest, { recursive: true });
  for (const [name, arr] of [
    ['vertices', data],
    ['indices', result]
  ])
    fs.writeFileSync(
      path.join(dest, base + '.' + name + '.bin.gz'),
      zlib.gzipSync(Buffer.from(arr.buffer), { level: 9 })
    );
  const meta = {
    ...src.meta,
    vertexCount: count,
    triangleCount: result.length / 3,
    geometryBytes: data.byteLength + result.byteLength,
    maxEdge,
    edgeBound: Math.max(src.meta.edgeBound, maxEdge + 1e-5),
    adaptiveSourceTriangleCount: src.meta.triangleCount,
    adaptivePlaneTolerance: tolerance,
    adaptiveMethod: `endpoint link-condition collapses; incident plane tolerance ${tolerance}; fixed boundaries; face orientation and normal constraints; 8 passes`
  };
  fs.writeFileSync(
    output,
    JSON.stringify({
      encoding: 'float32-p3-n3-phase2-d1',
      vertices: base + '.vertices.bin.gz',
      indices: base + '.indices.bin.gz',
      meta
    }) + '\n'
  );
  console.log(`${src.meta.triangleCount} → ${meta.triangleCount} triangles`);
} finally {
  fs.rmSync(tmp, { recursive: true, force: true });
}
