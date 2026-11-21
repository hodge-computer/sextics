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
      const scale = (p / q) * (turns % 4 >= 2 ? -1 : 1);
      for (const [m, v] of poly) total[m] += scale * v;
    }
    const coef = new Float64Array(MONOMIALS.length);
    MONOMIALS.forEach((e, i) => (coef[i] = total[key(e)]));
    const norm = Math.max(...coef.map(Math.abs));
    if (!(norm > 0)) throw new Error('The polynomial vanishes on this slice.');
    return coef.map((c) => c / norm);
  }

  // Compile g and its gradient into straight-line code for this slice: the
  // Newton projections evaluate them a few hundred thousand times.
  function evaluator(coef) {
    const lines = ['const a=s[0],b=s[1],c=s[2],d=s[3];'];
    const names = ['a', 'b', 'c', 'd'];
    for (const x of names)
      for (let k = 2; k <= DEGREE; k++)
        lines.push(`const ${x}${k}=${x}${k - 1 > 1 ? k - 1 : ''}*${x};`);
    const power = (v, e) => (e === 0 ? '1' : e === 1 ? names[v] : names[v] + e);
    const value = [],
      grad = [[], [], [], []];
    MONOMIALS.forEach((e, i) => {
      if (!coef[i]) return;
      const c = coef[i].toPrecision(17);
      value.push(`${c}*${e.map((k, v) => power(v, k)).join('*')}`);
      e.forEach((k, v) => {
        if (k)
          grad[v].push(
            `${(coef[i] * k).toPrecision(17)}*${e.map((j, w) => power(w, w === v ? j - 1 : j)).join('*')}`
          );
      });
    });
    const sum = (terms) => (terms.length ? terms.join('+') : '0');
    lines.push(...grad.map((terms, v) => `out[${v}]=${sum(terms)};`), `return ${sum(value)};`);
    const gradient = new Function('s', 'out', lines.join('\n'));
    return { gradient };
  }

  /* Sample g on the inverse stereographic image of the grid. With
     C = x² + y² - 1, the sphere point is (2x, 2y, 2z, z² + C) / (z² + C + 2),
     so along each grid column g·den⁶ is a degree-12 polynomial in z. Its
     coefficients are formed once per column and evaluated by Horner's rule. */
  async function sampleGrid(coef, [ax, ay, az], values, checkpoint) {
    const n = ax.length - 1,
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
      binom.push(
        Array.from({ length: d + 1 }, (_, j) => (binom[d - 1][j - 1] || 0) + (binom[d - 1][j] || 0))
      );
    const P = new Float64Array(2 * DEGREE + 1),
      px = new Float64Array(DEGREE + 1),
      py = new Float64Array(DEGREE + 1),
      pc = new Float64Array(DEGREE + 1);
    px[0] = py[0] = pc[0] = 1;
    for (let i = 0; i <= n; i++) {
      for (let t = 1; t <= DEGREE; t++) px[t] = px[t - 1] * 2 * ax[i];
      for (let j = 0; j <= n; j++) {
        for (let t = 1; t <= DEGREE; t++) py[t] = py[t - 1] * 2 * ay[j];
        const C = ax[i] * ax[i] + ay[j] * ay[j] - 1;
        for (let t = 1; t <= DEGREE; t++) pc[t] = pc[t - 1] * C;
        P.fill(0);
        for (const [c, d, list] of pairs) {
          let w = 0;
          for (let t = 0; t < list.length; t += 3)
            w += coef[list[t + 2]] * px[list[t]] * py[list[t + 1]];
          if (!w) continue;
          w *= 2 ** c;
          // (2z)^c (z² + C)^d = 2^c Σ_j binom(d, j) C^(d-j) z^(c+2j)
          for (let t = 0; t <= d; t++) P[c + 2 * t] += w * binom[d][t] * pc[d - t];
        }
        const row = (i * m + j) * m;
        for (let k = 0; k <= n; k++) {
          const z = az[k];
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
                complexScale, resolution = 128 }
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
      resolution: n = 128
    } = options;
    const coef = restrict(terms, planeMatrix, phaseSigns),
      g = evaluator(coef);
    const m = n + 1,
      values = new Float32Array(m * m * m),
      q = new Float64Array(3),
      s = new Float64Array(4);
    // A uniform grid over the display cube |p| <= 1: each saved display
    // transform frames its whole slice inside that cube, within the ±10 box.
    const uniform = [0, 1, 2].map((d) =>
      Float64Array.from({ length: n + 1 }, (_, i) => center[d] + scale * ((2 * i) / n - 1))
    );
    let pass = await contour(uniform);
    // Where cells hold more than one sheet or an ambiguous face (pinches,
    // thin gaps), resample once with grid lines concentrated through those
    // spots along each axis. The grid stays a tensor product, so the mesh
    // stays crack-free; the number of samples is unchanged.
    if (pass.difficult.length) pass = await contour(adapt(pass.difficult));
    const { cellBase, edgeVertex, positions } = pass;

    function adapt(points) {
      const BINS = 2048,
        h = (2 * scale) / n,
        width = 2 * h;
      return [0, 1, 2].map((d) => {
        const lo = center[d] - scale,
          density = new Float64Array(BINS).fill(1);
        for (let p = d; p < points.length; p += 3) {
          const c = ((points[p] - lo) / (2 * scale)) * BINS,
            reach = Math.ceil(((3 * width) / (2 * scale)) * BINS);
          for (let b = Math.max(0, Math.floor(c - reach)); b < Math.min(BINS, c + reach); b++) {
            const x = (((b + 0.5) / BINS) * 2 * scale - (points[p] - lo)) / width;
            density[b] += 3 * Math.exp(-x * x);
          }
        }
        // At most 4x finer, and the rest of the axis at most 1.5x coarser.
        let mean = 0;
        for (let b = 0; b < BINS; b++) mean += (density[b] = Math.min(4, density[b])) / BINS;
        const shrink = mean > 1.5 ? 0.5 / (mean - 1) : 1;
        const cumulative = new Float64Array(BINS + 1);
        for (let b = 0; b < BINS; b++)
          cumulative[b + 1] = cumulative[b] + 1 + (density[b] - 1) * shrink;
        const axis = new Float64Array(n + 1);
        for (let i = 0, b = 0; i <= n; i++) {
          const target = (cumulative[BINS] * i) / n;
          while (b < BINS - 1 && cumulative[b + 1] < target) b++;
          const t = (target - cumulative[b]) / (cumulative[b + 1] - cumulative[b] || 1);
          axis[i] = lo + ((b + Math.min(1, Math.max(0, t))) / BINS) * 2 * scale;
        }
        axis[0] = lo;
        axis[n] = lo + 2 * scale;
        return axis;
      });
    }

    async function contour(axes) {
      /* Dual contouring with one vertex per surface sheet in each cell, so
       that two sheets crossing one cell (at a pinch or a thin gap) stay
       apart. Crossings on each face are paired by the asymptotic decider
       (the saddle value of the bilinear interpolant), which neighbouring
       cells evaluate identically; pairs chain into one loop per sheet. */
      await sampleGrid(coef, axes, values, checkpoint);
      // Edges by axis: x-edges at (y,z) offsets, y-edges at (x,z), z-edges at (x,y).
      const EDGES = [
        [0, 0, 0, 1, 0, 0],
        [0, 1, 0, 1, 1, 0],
        [0, 0, 1, 1, 0, 1],
        [0, 1, 1, 1, 1, 1],
        [0, 0, 0, 0, 1, 0],
        [1, 0, 0, 1, 1, 0],
        [0, 0, 1, 0, 1, 1],
        [1, 0, 1, 1, 1, 1],
        [0, 0, 0, 0, 0, 1],
        [1, 0, 0, 1, 0, 1],
        [0, 1, 0, 0, 1, 1],
        [1, 1, 0, 1, 1, 1]
      ];
      // Faces as cyclic corners [A, B, C, D] (bit 1 = x, 2 = y, 4 = z) and
      // their edges [AB, BC, CD, DA].
      const FACES = [
        [
          [0, 2, 6, 4],
          [4, 10, 6, 8]
        ],
        [
          [1, 3, 7, 5],
          [5, 11, 7, 9]
        ],
        [
          [0, 1, 5, 4],
          [0, 9, 2, 8]
        ],
        [
          [2, 3, 7, 6],
          [1, 11, 3, 10]
        ],
        [
          [0, 1, 3, 2],
          [0, 5, 1, 4]
        ],
        [
          [4, 5, 7, 6],
          [2, 7, 3, 6]
        ]
      ];
      const cellBase = new Int32Array(n * n * n).fill(-1),
        edgeVertex = [],
        positions = [],
        difficult = [],
        corners = new Float64Array(8),
        parent = new Int8Array(12),
        cross = new Float64Array(36),
        crossed = new Uint8Array(12),
        sums = new Float64Array(48),
        vertexOf = new Int32Array(12);
      const find = (e) => {
        while (parent[e] !== e) e = parent[e] = parent[parent[e]];
        return e;
      };
      const join = (a, b) => (parent[find(a)] = find(b));
      for (let i = 0; i < n; i++) {
        for (let j = 0; j < n; j++)
          for (let k = 0; k < n; k++) {
            const base = (i * m + j) * m + k;
            let negative = 0;
            for (let c = 0; c < 8; c++) {
              const v = values[base + (c & 1 ? m * m : 0) + (c & 2 ? m : 0) + (c & 4 ? 1 : 0)];
              corners[c] = v;
              negative += v < 0;
            }
            if (negative === 0 || negative === 8) continue;
            let ambiguous = false;
            for (let e = 0; e < 12; e++) {
              parent[e] = e;
              const [a, b, c, d, f, g2] = EDGES[e],
                v0 = corners[a | (b << 1) | (c << 2)],
                v1 = corners[d | (f << 1) | (g2 << 2)];
              crossed[e] = v0 < 0 !== v1 < 0;
              if (!crossed[e]) continue;
              const t = v0 / (v0 - v1);
              cross[3 * e] = axes[0][i + a] + t * (axes[0][i + d] - axes[0][i + a]);
              cross[3 * e + 1] = axes[1][j + b] + t * (axes[1][j + f] - axes[1][j + b]);
              cross[3 * e + 2] = axes[2][k + c] + t * (axes[2][k + g2] - axes[2][k + c]);
            }
            for (const [[A, B, C, D], [ab, bc, cd, da]] of FACES) {
              const count = crossed[ab] + crossed[bc] + crossed[cd] + crossed[da];
              if (count === 2) {
                const pair = [ab, bc, cd, da].filter((e) => crossed[e]);
                join(pair[0], pair[1]);
              } else if (count === 4) {
                ambiguous = true;
                const a = corners[A],
                  b = corners[B],
                  c = corners[C],
                  d = corners[D],
                  saddle = (a * c - b * d) / (a + c - b - d);
                // A and C are joined through the face when the saddle shares their sign.
                if (saddle < 0 === a < 0) {
                  join(ab, bc);
                  join(cd, da);
                } else {
                  join(da, ab);
                  join(bc, cd);
                }
              }
            }
            sums.fill(0);
            for (let e = 0; e < 12; e++) {
              if (!crossed[e]) continue;
              const r = find(e);
              sums[4 * r] += cross[3 * e];
              sums[4 * r + 1] += cross[3 * e + 1];
              sums[4 * r + 2] += cross[3 * e + 2];
              sums[4 * r + 3]++;
            }
            vertexOf.fill(-1);
            const offset = edgeVertex.length,
              first = positions.length,
              size = Math.min(
                axes[0][i + 1] - axes[0][i],
                axes[1][j + 1] - axes[1][j],
                axes[2][k + 1] - axes[2][k]
              );
            cellBase[(i * n + j) * n + k] = offset;
            for (let e = 0; e < 12; e++) {
              if (!crossed[e]) {
                edgeVertex.push(-1);
                continue;
              }
              const r = find(e);
              if (vertexOf[r] < 0) {
                vertexOf[r] = positions.length / 4;
                const w = sums[4 * r + 3];
                positions.push(sums[4 * r] / w, sums[4 * r + 1] / w, sums[4 * r + 2] / w, size);
              }
              edgeVertex.push(vertexOf[r]);
            }
            if (ambiguous || positions.length - first > 4)
              difficult.push(
                (axes[0][i] + axes[0][i + 1]) / 2,
                (axes[1][j] + axes[1][j + 1]) / 2,
                (axes[2][k] + axes[2][k + 1]) / 2
              );
          }
        await checkpoint();
      }
      return { cellBase, edgeVertex, positions, difficult };
    }
    // Vertex attributes, nine per vertex: display position, unit normal,
    // colour observable, unused.
    const V = [],
      grad = new Float64Array(4),
      normal = new Float64Array(3);
    // Bounded Newton steps onto F = 0 in stereographic coordinates. Leaves the
    // ambient gradient direction at the final point in `normal`.
    function project(limit, steps) {
      for (let step = 0; step < steps; step++) {
        const den = sphere(q, s),
          f = g.gradient(s, grad),
          dot = q[0] * grad[0] + q[1] * grad[1] + q[2] * grad[2],
          w = (4 * (grad[3] - dot)) / (den * den);
        normal[0] = (2 * grad[0]) / den + q[0] * w;
        normal[1] = (2 * grad[1]) / den + q[1] * w;
        normal[2] = (2 * grad[2]) / den + q[2] * w;
        const g2 = normal[0] ** 2 + normal[1] ** 2 + normal[2] ** 2;
        if (!(g2 > 0)) return;
        let t = f / g2;
        const length = Math.abs(t) * Math.sqrt(g2);
        if (length > limit) t *= limit / length;
        q[0] -= t * normal[0];
        q[1] -= t * normal[1];
        q[2] -= t * normal[2];
        if (length < 1e-9 * limit) return;
      }
    }
    function emit() {
      const gl = Math.hypot(normal[0], normal[1], normal[2]) || 1,
        r = 1 + q[0] * q[0] + q[1] * q[1] + q[2] * q[2],
        a = (2 * q[0]) / r,
        b = (2 * q[1]) / r,
        c = (2 * q[2]) / r;
      V.push(
        (q[0] - center[0]) / scale,
        (q[1] - center[1]) / scale,
        (q[2] - center[2]) / scale,
        normal[0] / gl,
        normal[1] / gl,
        normal[2] / gl,
        (a * a - b * b + 0.5 * c * c) / complexScale,
        (2 * a * b) / complexScale,
        0
      );
    }
    for (let v = 0; v < positions.length / 4; v++) {
      q[0] = positions[4 * v];
      q[1] = positions[4 * v + 1];
      q[2] = positions[4 * v + 2];
      project(0.5 * positions[4 * v + 3], 6);
      emit();
      if (v % 8192 === 0) await checkpoint();
    }
    // One quad per sign-changing grid edge, joining the sheet vertices of
    // the four cells around it.
    let indices = [];
    const at = (i, j, k, e) => edgeVertex[cellBase[(i * n + j) * n + k] + e];
    const distance2 = (u, w) =>
      (V[9 * u] - V[9 * w]) ** 2 +
      (V[9 * u + 1] - V[9 * w + 1]) ** 2 +
      (V[9 * u + 2] - V[9 * w + 2]) ** 2;
    const quad = (a, b, c, d) => {
      // Split along the shorter diagonal.
      if (distance2(a, c) <= distance2(b, d)) indices.push(a, b, c, a, c, d);
      else indices.push(a, b, d, b, c, d);
    };
    for (let c = 0; c < cellBase.length; c++) {
      if (cellBase[c] < 0) continue;
      const k = c % n,
        j = ((c - k) / n) % n,
        i = (c - k - j * n) / (n * n);
      if (j && k && edgeVertex[cellBase[c]] >= 0)
        quad(at(i, j - 1, k - 1, 3), at(i, j, k - 1, 2), at(i, j, k, 0), at(i, j - 1, k, 1));
      if (i && k && edgeVertex[cellBase[c] + 4] >= 0)
        quad(at(i - 1, j, k - 1, 7), at(i - 1, j, k, 5), at(i, j, k, 4), at(i, j, k - 1, 6));
      if (i && j && edgeVertex[cellBase[c] + 8] >= 0)
        quad(at(i - 1, j - 1, k, 11), at(i, j - 1, k, 10), at(i, j, k, 8), at(i - 1, j, k, 9));
      if (c % 65536 === 0) await checkpoint();
    }
    if (!indices.length) throw new Error('The saved section contains no real surface.');
    // Geometric normal of triangle (a, b, c) dotted with a direction.
    function facing(a, b, c, nx, ny, nz) {
      const ux = V[9 * b] - V[9 * a],
        uy = V[9 * b + 1] - V[9 * a + 1],
        uz = V[9 * b + 2] - V[9 * a + 2],
        vx = V[9 * c] - V[9 * a],
        vy = V[9 * c + 1] - V[9 * a + 1],
        vz = V[9 * c + 2] - V[9 * a + 2];
      return (uy * vz - uz * vy) * nx + (uz * vx - ux * vz) * ny + (ux * vy - uy * vx) * nz;
    }
    const normalSum = (a, b, c, d) => V[9 * a + 3 + d] + V[9 * b + 3 + d] + V[9 * c + 3 + d];
    // Wind each triangle to agree with the gradient normals: the renderer
    // shades front faces with the stored normal and back faces with its negative.
    for (let t = 0; t < indices.length; t += 3) {
      const [a, b, c] = [indices[t], indices[t + 1], indices[t + 2]];
      if (facing(a, b, c, normalSum(a, b, c, 0), normalSum(a, b, c, 1), normalSum(a, b, c, 2)) < 0)
        [indices[t + 1], indices[t + 2]] = [c, b];
    }
    indices = await refine(indices);
    const data = Float32Array.from(V);
    for (let i = 0; i < data.length; i++)
      if (!Number.isFinite(data[i])) throw new Error('Non-finite surface sample rejected.');

    /* Curvature refinement. Split edges whose endpoint normals disagree and
       whose exact midpoint departs from the chord, placing the new vertex on
       F = 0; triangles are split conformingly. A split is withheld when its
       midpoint did not reach the surface or a child triangle would oppose the
       surface normals. Across a tight fold the midpoint lies far from the
       chord and the children turn away from the flat parent; both are
       expected there. Distances are in display coordinates. */
    async function refine(tris) {
      const CURVED = 0.985,
        SHARP = 0.9659,
        MIDPOINT_ERROR = 0.0003,
        MIN_SHARP_EDGE = 0.00025,
        STEP_FRACTION = 0.1,
        // Eight bounded steps cover at most 0.8 of the edge; a midpoint that far has not converged.
        SAFE_SHIFT = 0.75;
      const dotNormals = (a, b) =>
        V[9 * a + 3] * V[9 * b + 3] + V[9 * a + 4] * V[9 * b + 4] + V[9 * a + 5] * V[9 * b + 5];
      for (let pass = 0; pass < 4; pass++) {
        // Only edges whose endpoint normals disagree can split, so only
        // triangles with such an edge are revisited; the rest are kept as is.
        const nv = V.length / 9,
          curved = [],
          edgeOf = new Map(),
          ends = [];
        for (let t = 0; t < tris.length; t += 3) {
          const a = tris[t],
            b = tris[t + 1],
            c = tris[t + 2];
          if (dotNormals(a, b) < CURVED || dotNormals(b, c) < CURVED || dotNormals(c, a) < CURVED)
            curved.push(t);
        }
        const triEdges = new Int32Array(3 * curved.length);
        curved.forEach((t, i) => {
          for (let k = 0; k < 3; k++) {
            const a = tris[t + k],
              b = tris[t + ((k + 1) % 3)];
            if (dotNormals(a, b) >= CURVED) {
              triEdges[3 * i + k] = -1;
              continue;
            }
            const id = a < b ? a * nv + b : b * nv + a;
            let e = edgeOf.get(id);
            if (e === undefined) {
              e = ends.length / 2;
              edgeOf.set(id, e);
              ends.push(a, b);
            }
            triEdges[3 * i + k] = e;
          }
        });
        const E = ends.length / 2,
          split = new Int32Array(E).fill(-1),
          midpoints = [];
        for (let e = 0; e < E; e++) {
          const a = 9 * ends[2 * e],
            b = 9 * ends[2 * e + 1];
          const dot = dotNormals(ends[2 * e], ends[2 * e + 1]);
          const length = Math.hypot(V[a] - V[b], V[a + 1] - V[b + 1], V[a + 2] - V[b + 2]);
          for (let d = 0; d < 3; d++) q[d] = ((V[a + d] + V[b + d]) / 2) * scale + center[d];
          const mx = q[0],
            my = q[1],
            mz = q[2];
          project(STEP_FRACTION * length * scale, 8);
          const err = Math.hypot(q[0] - mx, q[1] - my, q[2] - mz) / scale;
          const wanted = err > MIDPOINT_ERROR || (dot < SHARP && length > MIN_SHARP_EDGE);
          if (!wanted || err >= SAFE_SHIFT * length) continue;
          split[e] = midpoints.length / 6;
          midpoints.push(q[0], q[1], q[2], normal[0], normal[1], normal[2]);
          if (e % 4096 === 0) await checkpoint();
        }
        if (!midpoints.length) break;
        const base = V.length / 9;
        for (let i = 0; i < midpoints.length; i += 6) {
          q[0] = midpoints[i];
          q[1] = midpoints[i + 1];
          q[2] = midpoints[i + 2];
          normal[0] = midpoints[i + 3];
          normal[1] = midpoints[i + 4];
          normal[2] = midpoints[i + 5];
          emit();
        }
        // Retry until no child triangle opposes its normals.
        for (let attempt = 0; ; attempt++) {
          const replaced = new Map(),
            bad = [];
          curved.forEach((t, i) => {
            const a = tris[t],
              b = tris[t + 1],
              c = tris[t + 2];
            const id = (k) => {
              const e = triEdges[3 * i + k];
              return e < 0 || split[e] < 0 ? -1 : base + split[e];
            };
            const ab = id(0),
              bc = id(1),
              ca = id(2),
              mask = (ab >= 0) | ((bc >= 0) << 1) | ((ca >= 0) << 2);
            if (!mask) return;
            const children =
              mask === 1
                ? [a, ab, c, ab, b, c]
                : mask === 2
                  ? [b, bc, a, bc, c, a]
                  : mask === 4
                    ? [c, ca, b, ca, a, b]
                    : mask === 3
                      ? [ab, b, bc, a, ab, c, ab, bc, c]
                      : mask === 6
                        ? [bc, c, ca, b, bc, a, bc, ca, a]
                        : mask === 5
                          ? [ca, a, ab, c, ca, b, ca, ab, b]
                          : [a, ab, ca, b, bc, ab, c, ca, bc, ab, bc, ca];
            for (let j = 0; j < children.length; j += 3) {
              const u = children[j],
                v = children[j + 1],
                w = children[j + 2];
              if (
                facing(
                  u,
                  v,
                  w,
                  normalSum(u, v, w, 0),
                  normalSum(u, v, w, 1),
                  normalSum(u, v, w, 2)
                ) <= 0
              ) {
                bad.push(i);
                return;
              }
            }
            replaced.set(t, children);
          });
          if (bad.length) {
            if (attempt >= 20) throw new Error('Surface refinement did not converge.');
            for (const i of bad)
              for (let k = 0; k < 3; k++)
                if (triEdges[3 * i + k] >= 0) split[triEdges[3 * i + k]] = -1;
            continue;
          }
          const next = [];
          for (let t = 0; t < tris.length; t += 3) {
            const children = replaced.get(t);
            if (children) for (const v of children) next.push(v);
            else next.push(tris[t], tris[t + 1], tris[t + 2]);
          }
          tris = next;
          break;
        }
        await checkpoint();
      }
      return tris;
    }
    return {
      buffer: data.buffer,
      indexBuffer: Uint32Array.from(indices).buffer,
      meta: {
        vertexCount: data.length / 9,
        triangleCount: indices.length / 3,
        planeMatrix,
        phaseSigns,
        centerOriginal: center,
        displayScale: scale,
        complexScale,
        projectionBox: 10,
        samplingMode: 'box'
      }
    };
  }
  root.HodgeSliceMesh = Object.freeze({ build, restrict });
})(globalThis);
