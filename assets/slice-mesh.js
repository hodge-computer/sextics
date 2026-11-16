/* Local generation of atlas slice meshes.
   The surface is F = 0 restricted to a phase-rotated real four-plane, on the
   unit three-sphere, stereographically projected and clipped to |q| <= box.
   Floating point is presentation only; exact records are never changed. */
((root) => {
  'use strict';
  const DEGREE = 6,
    MONOMIALS = [];
  for (let a = DEGREE; a >= 0; a--)
    for (let b = DEGREE - a; b >= 0; b--)
      for (let c = DEGREE - a - b; c >= 0; c--) MONOMIALS.push([a, b, c, DEGREE - a - b - c]);
  const key = (e) => ((e[0] * 7 + e[1]) * 7 + e[2]) * 7 + e[3];

  // Expand F(diag(phase) B u) into a real homogeneous sextic in u. A phase
  // sign of -1 multiplies that coordinate by i; the saved phases make every
  // term's power of i even, so the restriction is real up to one global factor.
  function restrict(terms, plane, signs) {
    const total = new Float64Array(7 ** 4);
    let parity = null;
    for (const [c, exps] of terms) {
      const [p, q = 1] = String(c).split('/').map(Number);
      let turns = 0;
      exps.forEach((e, i) => signs[i] < 0 && (turns += e));
      if (parity === null) parity = turns % 2;
      if (turns % 2 !== parity) throw new Error('The slice polynomial is not scalar-real.');
      let poly = new Map([[0, 1]]);
      exps.forEach((e, i) => {
        for (let k = 0; k < e; k++) {
          const next = new Map();
          for (const [m, v] of poly)
            for (let j = 0; j < 4; j++) {
              const n = m + 7 ** (3 - j);
              next.set(n, (next.get(n) || 0) + v * plane[i][j]);
            }
          poly = next;
        }
      });
      const scale = ((p / q) * (turns % 4 >= 2 ? -1 : 1));
      for (const [m, v] of poly) total[m] += scale * v;
    }
    const coef = new Float64Array(MONOMIALS.length);
    MONOMIALS.forEach((e, i) => (coef[i] = total[key(e)]));
    const norm = Math.max(...coef.map(Math.abs));
    if (!(norm > 0)) throw new Error('The polynomial vanishes on this slice.');
    return coef.map((c) => c / norm);
  }

  function evaluator(coef) {
    const n = MONOMIALS.length,
      e = Int8Array.from(MONOMIALS.flat()),
      pw = new Float64Array(28);
    function powers(s) {
      for (let v = 0; v < 4; v++) {
        pw[7 * v] = 1;
        for (let k = 1; k <= DEGREE; k++) pw[7 * v + k] = pw[7 * v + k - 1] * s[v];
      }
    }
    return {
      value(s) {
        powers(s);
        let sum = 0;
        for (let i = 0, j = 0; i < n; i++, j += 4)
          sum += coef[i] * pw[e[j]] * pw[7 + e[j + 1]] * pw[14 + e[j + 2]] * pw[21 + e[j + 3]];
        return sum;
      },
      gradient(s, out) {
        powers(s);
        let sum = 0;
        out.fill(0);
        for (let i = 0, j = 0; i < n; i++, j += 4) {
          const a = e[j], b = e[j + 1], c = e[j + 2], d = e[j + 3],
            A = pw[a], B = pw[7 + b], C = pw[14 + c], D = pw[21 + d], k = coef[i];
          sum += k * A * B * C * D;
          if (a) out[0] += k * a * pw[a - 1] * B * C * D;
          if (b) out[1] += k * b * A * pw[7 + b - 1] * C * D;
          if (c) out[2] += k * c * A * B * pw[14 + c - 1] * D;
          if (d) out[3] += k * d * A * B * C * pw[21 + d - 1];
        }
        return sum;
      }
    };
  }

  /* Sample g on the inverse stereographic image of the grid. With
     C = x² + y² - 1, the sphere point is (2x, 2y, 2z, z² + C) / (z² + C + 2),
     so along each grid column g·den⁶ is a degree-12 polynomial in z. Its
     coefficients are formed once per column and evaluated by Horner's rule. */
  async function sampleGrid(coef, axis, values, checkpoint) {
    const n = axis.length - 1,
      m = n + 1,
      pairs = [];
    // Group monomials u0^a u1^b u2^c u3^d by (c, d).
    for (let c = 0; c <= DEGREE; c++)
      for (let d = 0; c + d <= DEGREE; d++) {
        const list = [];
        MONOMIALS.forEach(([a, b, cc, dd], i) => cc === c && dd === d && list.push(a, b, i));
        if (list.length) pairs.push([c, d, list]);
      }
    const binom = [[1]];
    for (let d = 1; d <= DEGREE; d++)
      binom.push(Array.from({ length: d + 1 }, (_, j) => (binom[d - 1][j - 1] || 0) + (binom[d - 1][j] || 0)));
    const P = new Float64Array(2 * DEGREE + 1),
      px = new Float64Array(DEGREE + 1),
      py = new Float64Array(DEGREE + 1),
      pc = new Float64Array(DEGREE + 1);
    px[0] = py[0] = pc[0] = 1;
    for (let i = 0; i <= n; i++) {
      for (let t = 1; t <= DEGREE; t++) px[t] = px[t - 1] * 2 * axis[i];
      for (let j = 0; j <= n; j++) {
        for (let t = 1; t <= DEGREE; t++) py[t] = py[t - 1] * 2 * axis[j];
        const C = axis[i] * axis[i] + axis[j] * axis[j] - 1;
        for (let t = 1; t <= DEGREE; t++) pc[t] = pc[t - 1] * C;
        P.fill(0);
        for (const [c, d, list] of pairs) {
          let w = 0;
          for (let t = 0; t < list.length; t += 3) w += coef[list[t + 2]] * px[list[t]] * py[list[t + 1]];
          if (!w) continue;
          w *= 2 ** c;
          // (2z)^c (z² + C)^d = 2^c Σ_j binom(d, j) C^(d-j) z^(c+2j)
          for (let t = 0; t <= d; t++) P[c + 2 * t] += w * binom[d][t] * pc[d - t];
        }
        const row = (i * m + j) * m;
        for (let k = 0; k <= n; k++) {
          const z = axis[k];
          let h = P[2 * DEGREE];
          for (let t = 2 * DEGREE - 1; t >= 0; t--) h = h * z + P[t];
          const den = z * z + C + 2,
            d2 = den * den;
          values[row + k] = h / (d2 * d2 * d2);
        }
      }
      await checkpoint();
    }
  }

  // Inverse stereographic projection to the unit three-sphere.
  function sphere(q, s) {
    const r2 = q[0] * q[0] + q[1] * q[1] + q[2] * q[2],
      den = 1 + r2;
    s[0] = (2 * q[0]) / den;
    s[1] = (2 * q[1]) / den;
    s[2] = (2 * q[2]) / den;
    s[3] = (r2 - 1) / den;
    return den;
  }

  /* Build an indexed mesh in the renderer's layout: display position (3),
     unit normal (3), colour observable (2), unused (1).
     options: { terms, planeMatrix, phaseSigns, centerOriginal, displayScale,
                complexScale, box = 10, resolution = 128, warp = 2.5 }
     The optional async checkpoint is awaited between rows so the caller can
     yield or cancel. */
  async function build(options, checkpoint = async () => {}) {
    const {
      terms,
      planeMatrix,
      phaseSigns,
      centerOriginal: center,
      displayScale: scale,
      complexScale,
      box = 10,
      resolution: n = 128,
      warp = 2.5
    } = options;
    const coef = restrict(terms, planeMatrix, phaseSigns),
      g = evaluator(coef);
    // A sinh-warped grid: fine near the origin, where the slice is bounded,
    // and coarse towards the box boundary.
    const axis = new Float64Array(n + 1);
    for (let i = 0; i <= n; i++)
      axis[i] = (box * Math.sinh(warp * (2 * i / n - 1))) / Math.sinh(warp);
    const m = n + 1,
      values = new Float32Array(m * m * m),
      q = new Float64Array(3),
      s = new Float64Array(4);
    await sampleGrid(coef, axis, values, checkpoint);
    // Surface nets: one vertex per sign-changing cell, at the mean of its
    // edge crossings, then Newton-corrected onto F = 0.
    const cellVertex = new Int32Array(n * n * n).fill(-1),
      positions = [];
    const corner = (i, j, k) => values[(i * m + j) * m + k];
    const EDGES = [
      [0, 0, 0, 1, 0, 0], [0, 1, 0, 1, 1, 0], [0, 0, 1, 1, 0, 1], [0, 1, 1, 1, 1, 1],
      [0, 0, 0, 0, 1, 0], [1, 0, 0, 1, 1, 0], [0, 0, 1, 0, 1, 1], [1, 0, 1, 1, 1, 1],
      [0, 0, 0, 0, 0, 1], [1, 0, 0, 1, 0, 1], [0, 1, 0, 0, 1, 1], [1, 1, 0, 1, 1, 1]
    ];
    for (let i = 0; i < n; i++) {
      for (let j = 0; j < n; j++)
        for (let k = 0; k < n; k++) {
          const base = (i * m + j) * m + k,
            negative =
              (values[base] < 0) + (values[base + 1] < 0) +
              (values[base + m] < 0) + (values[base + m + 1] < 0) +
              (values[base + m * m] < 0) + (values[base + m * m + 1] < 0) +
              (values[base + m * m + m] < 0) + (values[base + m * m + m + 1] < 0);
          if (negative === 0 || negative === 8) continue;
          let x = 0, y = 0, z = 0, count = 0;
          for (const [a, b, c, d, e, f] of EDGES) {
            const v0 = corner(i + a, j + b, k + c),
              v1 = corner(i + d, j + e, k + f);
            if (v0 < 0 === v1 < 0) continue;
            const t = v0 / (v0 - v1);
            x += axis[i + a] + t * (axis[i + d] - axis[i + a]);
            y += axis[j + b] + t * (axis[j + e] - axis[j + b]);
            z += axis[k + c] + t * (axis[k + f] - axis[k + c]);
            count++;
          }
          if (!count) continue;
          cellVertex[(i * n + j) * n + k] = positions.length / 4;
          positions.push(x / count, y / count, z / count, axis[i + 1] - axis[i]);
        }
      await checkpoint();
    }
    const vertexCount = positions.length / 4,
      data = new Float32Array(vertexCount * 9),
      grad = new Float64Array(4);
    for (let v = 0; v < vertexCount; v++) {
      q[0] = positions[4 * v];
      q[1] = positions[4 * v + 1];
      q[2] = positions[4 * v + 2];
      const limit = 0.5 * positions[4 * v + 3];
      let gx = 0, gy = 0, gz = 0;
      for (let step = 0; step < 6; step++) {
        const den = sphere(q, s),
          f = g.gradient(s, grad),
          dot = q[0] * grad[0] + q[1] * grad[1] + q[2] * grad[2],
          w = (4 * (grad[3] - dot)) / (den * den);
        gx = (2 * grad[0]) / den + q[0] * w;
        gy = (2 * grad[1]) / den + q[1] * w;
        gz = (2 * grad[2]) / den + q[2] * w;
        const g2 = gx * gx + gy * gy + gz * gz;
        if (!(g2 > 0)) break;
        let t = f / g2;
        const length = Math.abs(t) * Math.sqrt(g2);
        if (length > limit) t *= limit / length;
        q[0] -= t * gx;
        q[1] -= t * gy;
        q[2] -= t * gz;
        if (length < 1e-9 * limit) break;
      }
      const gl = Math.hypot(gx, gy, gz) || 1,
        r = 1 + q[0] * q[0] + q[1] * q[1] + q[2] * q[2],
        a = (2 * q[0]) / r, b = (2 * q[1]) / r, c = (2 * q[2]) / r,
        o = 9 * v;
      for (let d = 0; d < 3; d++) data[o + d] = (q[d] - center[d]) / scale;
      data[o + 3] = gx / gl;
      data[o + 4] = gy / gl;
      data[o + 5] = gz / gl;
      data[o + 6] = (a * a - b * b + 0.5 * c * c) / complexScale;
      data[o + 7] = (2 * a * b) / complexScale;
      if (v % 8192 === 0) await checkpoint();
    }
    // One quad per sign-changing grid edge, joining the four cells around it.
    const indices = [];
    const cell = (i, j, k) => cellVertex[(i * n + j) * n + k];
    const quad = (a, b, c, d, flip) => {
      if (flip) [b, d] = [d, b];
      // Split along the shorter diagonal.
      const dist = (u, w) => {
        let sum = 0;
        for (let t = 0; t < 3; t++) sum += (data[9 * u + t] - data[9 * w + t]) ** 2;
        return sum;
      };
      if (dist(a, c) <= dist(b, d)) indices.push(a, b, c, a, c, d);
      else indices.push(a, b, d, b, c, d);
    };
    for (let i = 0; i < n; i++) {
      for (let j = 0; j < n; j++)
        for (let k = 0; k < n; k++) {
          const v0 = corner(i, j, k) < 0;
          if (j && k && v0 !== corner(i + 1, j, k) < 0)
            quad(cell(i, j - 1, k - 1), cell(i, j, k - 1), cell(i, j, k), cell(i, j - 1, k), v0);
          if (i && k && v0 !== corner(i, j + 1, k) < 0)
            quad(cell(i - 1, j, k - 1), cell(i - 1, j, k), cell(i, j, k), cell(i, j, k - 1), v0);
          if (i && j && v0 !== corner(i, j, k + 1) < 0)
            quad(cell(i - 1, j - 1, k), cell(i, j - 1, k), cell(i, j, k), cell(i - 1, j, k), v0);
        }
      await checkpoint();
    }
    if (!indices.length) throw new Error('The saved section contains no real surface.');
    // Wind each triangle to agree with the gradient normals, as the renderer
    // shades front faces with the stored normal and back faces with its negative.
    for (let t = 0; t < indices.length; t += 3) {
      const [a, b, c] = [9 * indices[t], 9 * indices[t + 1], 9 * indices[t + 2]];
      const ux = data[b] - data[a], uy = data[b + 1] - data[a + 1], uz = data[b + 2] - data[a + 2],
        vx = data[c] - data[a], vy = data[c + 1] - data[a + 1], vz = data[c + 2] - data[a + 2];
      const nx = data[a + 3] + data[b + 3] + data[c + 3],
        ny = data[a + 4] + data[b + 4] + data[c + 4],
        nz = data[a + 5] + data[b + 5] + data[c + 5];
      if ((uy * vz - uz * vy) * nx + (uz * vx - ux * vz) * ny + (ux * vy - uy * vx) * nz < 0)
        [indices[t + 1], indices[t + 2]] = [indices[t + 2], indices[t + 1]];
    }
    for (let i = 0; i < data.length; i++)
      if (!Number.isFinite(data[i])) throw new Error('Non-finite surface sample rejected.');
    return {
      buffer: data.buffer,
      indexBuffer: Uint32Array.from(indices).buffer,
      meta: {
        vertexCount,
        triangleCount: indices.length / 3,
        planeMatrix,
        phaseSigns,
        centerOriginal: center,
        displayScale: scale,
        complexScale,
        projectionBox: box,
        samplingMode: 'box'
      }
    };
  }
  root.HodgeSliceMesh = Object.freeze({ build, restrict });
})(globalThis);
