/* Compile display polynomials into per-pixel value/gradient expressions.
   Floating point is presentation only; accepted proof data is never changed. */
(() => {
  'use strict';
  const GLSL = `
struct DivJet { float v; vec3 a; vec3 b; };
DivJet dc(float v) { return DivJet(v,vec3(0.0),vec3(0.0)); }
DivJet da(DivJet x,DivJet y) { return DivJet(x.v+y.v,x.a+y.a,x.b+y.b); }
DivJet dm(DivJet x,DivJet y) { return DivJet(x.v*y.v,x.a*y.v+x.v*y.a,x.b*y.v+x.v*y.b); }
DivJet ds(DivJet x,float s) { return DivJet(x.v/s,x.a/s,x.b/s); }
float divisorDistance(DivJet r,DivJet i,bool complexValue) {
  float scale=max(max(max(abs(r.a.x),abs(r.a.y)),max(abs(r.a.z),abs(r.b.x))),max(abs(r.b.y),abs(r.b.z)));
  scale=max(scale,max(max(max(abs(i.a.x),abs(i.a.y)),max(abs(i.a.z),abs(i.b.x))),max(abs(i.b.y),abs(i.b.z))));
  if(scale==0.0) return complexValue?length(vec2(r.v,i.v)):r.v;
  vec3 a=r.a/scale,b=r.b/scale,c=i.a/scale,d=i.b/scale;
  float norm=sqrt(dot(a,a)+dot(b,b)+dot(c,c)+dot(d,d));
  return (complexValue?length(vec2(r.v,i.v)/scale):r.v/scale)/norm;
}
`;
  function compile(formula, signs, surface = false) {
    if (!formula || (Array.isArray(formula) && !formula.length))
      return {
        source: GLSL + 'float divisorField(vec3 a,vec3 b){return 1.0;}',
        operations: 0,
        factors: 0
      };
    const nodes = [],
      keys = new Map();
    function node(op, a, b) {
      const key = JSON.stringify([op, a, b]);
      if (keys.has(key)) return keys.get(key);
      if (nodes.length >= 4096)
        throw new Error('Divisor expression exceeds the pixel shader budget.');
      const n = nodes.length;
      nodes.push([op, a, b]);
      keys.set(key, n);
      return n;
    }
    const constant = (v) => {
      if (!Number.isFinite(v)) throw new Error('Non-finite divisor coefficient.');
      return node('c', v);
    };
    const zero = constant(0),
      one = constant(1);
    const cv = (n) => (nodes[n][0] === 'c' ? nodes[n][1] : null);
    function add(a, b) {
      if (a === zero) return b;
      if (b === zero) return a;
      if (cv(a) !== null && cv(b) !== null) return constant(cv(a) + cv(b));
      // Preserve precision when phase rotation turns a sum of squares into a
      // difference: x*x-y*y is evaluated as (x-y)*(x+y).
      const square = (n) =>
        nodes[n][0] === '*' && nodes[n][1] === nodes[n][2] ? nodes[n][1] : null;
      const negativeSquare = (n) => {
        const [op, x, y] = nodes[n];
        return op === '*' ? (cv(x) === -1 ? square(y) : cv(y) === -1 ? square(x) : null) : null;
      };
      let x = square(a),
        y = negativeSquare(b);
      if (x === null || y === null) {
        x = square(b);
        y = negativeSquare(a);
      }
      if (x !== null && y !== null) return mul(add(x, mul(constant(-1), y)), add(x, y));
      return node('+', Math.min(a, b), Math.max(a, b));
    }
    function mul(a, b) {
      if (a === zero || b === zero) return zero;
      if (a === one) return b;
      if (b === one) return a;
      if (cv(a) !== null && cv(b) !== null) return constant(cv(a) * cv(b));
      return node('*', Math.min(a, b), Math.max(a, b));
    }
    const neg = (a) => mul(constant(-1), a);
    const ca = (a, b) => [add(a[0], b[0]), add(a[1], b[1])];
    const cm = (a, b) => [
      add(mul(a[0], b[0]), neg(mul(a[1], b[1]))),
      add(mul(a[0], b[1]), mul(a[1], b[0]))
    ];
    function cp(a, n) {
      let out = [one, zero];
      while (n) {
        if (n & 1) out = cm(out, a);
        n >>= 1;
        if (n) a = cm(a, a);
      }
      return out;
    }
    const variables = Array.from({ length: 6 }, (_, j) => node('v', j));
    const z = variables.map((v, j) => (signs[j] < 0 ? [zero, v] : [v, zero]));
    const factors = [];
    function factor(v) {
      if (cv(v[0]) !== null && cv(v[1]) !== null) {
        if (cv(v[0]) === 0 && cv(v[1]) === 0) throw new Error('Identically zero divisor factor.');
        return;
      }
      if (!factors.some((f) => f[0] === v[0] && f[1] === v[1])) factors.push(v);
    }
    function sparse(terms) {
      if (!terms.length) return [zero, zero];
      // Multivariate Horner form shares powers/products instead of expanding a
      // six-variable derivative separately for every monomial.
      function horner(list, j) {
        if (j === 6) return list.reduce((out, [c]) => ca(out, c), [zero, zero]);
        const groups = new Map();
        for (const [c, e] of list) {
          if (!groups.has(e[j])) groups.set(e[j], []);
          groups.get(e[j]).push([c, e]);
        }
        const exponents = [...groups.keys()].sort((a, b) => b - a);
        let power = exponents[0],
          out = horner(groups.get(power), j + 1);
        for (const e of exponents.slice(1)) {
          out = ca(cm(out, cp(z[j], power - e)), horner(groups.get(e), j + 1));
          power = e;
        }
        return cm(out, cp(z[j], power));
      }
      const scale = Math.max(
        ...terms.flatMap(([c]) => (Array.isArray(c) ? c.map(Math.abs) : [Math.abs(c)]))
      );
      if (!Number.isFinite(scale) || scale === 0) throw new Error('Invalid divisor coefficients.');
      return horner(
        terms.map(([c, e]) => [
          [
            constant((Array.isArray(c) ? c[0] : c) / scale),
            constant(Array.isArray(c) ? c[1] / scale : 0)
          ],
          e
        ]),
        0
      );
    }
    if (Array.isArray(formula)) {
      const common = variables.map((_, j) => surface ? 0 : Math.min(...formula.map(([, e]) => e[j])));
      for (let j = 0; j < 6; j++) if (common[j]) factor(z[j]);
      factor(sparse(formula.map(([c, e]) => [c, e.map((p, j) => p - common[j])])));
    } else if (formula.kind === 'polynomial-program') {
      const values = [];
      for (const [op, a, b] of formula.nodes) {
        if (op === 'variable') values.push(z[a]);
        else if (op === 'rational') {
          const [p, q = '1'] = a.split('/');
          values.push([constant(Number(p) / Number(q)), zero]);
        } else if (op === 'sqrt')
          values.push(a < 0 ? [zero, constant(Math.sqrt(-a))] : [constant(Math.sqrt(a)), zero]);
        else if (op === 'add') values.push(ca(values[a], values[b]));
        else if (op === 'mul') values.push(cm(values[a], values[b]));
        else if (op === 'pow') values.push(cp(values[a], b));
        else throw new Error('Unknown divisor instruction.');
      }
      // A product vanishes exactly where one of its factors does. Drawing the
      // factors individually removes multiplicity/underflow, not any component.
      function collect(n) {
        const [op, a, b] = formula.nodes[n];
        if (op === 'mul') {
          collect(a);
          collect(b);
        } else if (op === 'pow') collect(a);
        else factor(values[n]);
      }
      collect(formula.output);
    } else throw new Error('Unsupported pixel divisor formula.');
    const used = new Set();
    function visit(n) {
      if (used.has(n)) return;
      const [op, a, b] = nodes[n];
      if (op === '+' || op === '*') {
        visit(a);
        visit(b);
      }
      used.add(n);
    }
    factors.flat().forEach(visit);
    visit(zero);
    const literal = (x) => {
      const s = String(x);
      return /[.e]/i.test(s) ? s : s + '.0';
    };
    // Evaluate a homogeneous polynomial in its quadratic inputs at their own
    // projective scale. The same factor divides its value and gradient, so
    // divisorDistance is unchanged without forming tiny high-degree products.
    const degrees = nodes.map(([op]) => (op === 'v' ? 1 : 0));
    for (let n = 0; n < nodes.length; n++) {
      const [op, a, b] = nodes[n];
      if (op === '+') degrees[n] = Math.max(degrees[a], degrees[b]);
      else if (op === '*') degrees[n] = degrees[a] + degrees[b];
    }
    const quadratic = new Set(),
      cuts = new Map();
    function quadraticCut(n) {
      if (cuts.has(n)) return cuts.get(n);
      if (degrees[n] === 0) return true;
      if (degrees[n] === 2) {
        quadratic.add(n);
        return true;
      }
      if (degrees[n] < 2) return false;
      const [, a, b] = nodes[n];
      const valid = quadraticCut(a) && quadraticCut(b);
      cuts.set(n, valid);
      return valid;
    }
    const canRescale = factors.flat().every((n) => degrees[n] <= 1 || quadraticCut(n));
    if (!canRescale) quadratic.clear();
    const basis = new Set();
    function visitBasis(n) {
      if (basis.has(n)) return;
      const [op, a, b] = nodes[n];
      if (op === '+' || op === '*') {
        visitBasis(a);
        visitBasis(b);
      }
      basis.add(n);
    }
    quadratic.forEach(visitBasis);
    const order = quadratic.size
      ? [...basis, ...[...used].filter((n) => !basis.has(n))]
      : [...used];
    const lines = surface
      ? ['DivJet surfaceField(vec3 a,vec3 b) {']
      : [GLSL, 'float divisorField(vec3 a,vec3 b) {'];
    // All factors are homogeneous. Projectively rescaling the coordinates
    // prevents degree-48/60 values from underflowing on small saved sections.
    lines.push(
      'float scale=max(max(max(abs(a.x),abs(a.y)),max(abs(a.z),abs(b.x))),max(abs(b.y),abs(b.z)));',
      'a/=max(scale,1e-20); b/=max(scale,1e-20);'
    );
    for (const [at, n] of order.entries()) {
      if (quadratic.size && at === basis.size) {
        const values = [...quadratic].map((n) => `abs(d${n}.v)`);
        const maximum = values.reduce((a, b) => `max(${a},${b})`);
        lines.push(`float quadraticScale=max(${maximum},1e-20);`);
        quadratic.forEach((n) => lines.push(`d${n}=ds(d${n},quadraticScale);`));
      }
      const [op, a, b] = nodes[n];
      let expr;
      if (op === 'c') expr = `dc(${literal(a)})`;
      else if (op === 'v') {
        const unit = [0, 0, 0, 0, 0, 0];
        unit[a] = 1;
        expr = `DivJet(${a < 3 ? 'a' : 'b'}[${a % 3}],vec3(${unit.slice(0, 3).map(literal)}),vec3(${unit.slice(3).map(literal)}))`;
      } else expr = `${op === '+' ? 'da' : 'dm'}(d${a},d${b})`;
      lines.push(`DivJet d${n}=${expr};`);
    }
    if (surface) {
      const [r, i] = factors[0];
      if (factors.length !== 1 || (r !== zero && i !== zero))
        throw new Error('The surface polynomial must be scalar-real on this slice.');
      const value = `d${r === zero ? i : r}`;
      lines.push(`return DivJet(${value}.v,${value}.a/max(scale,1e-20),${value}.b/max(scale,1e-20));`, '}');
      return { source: lines.join('\n'), operations: used.size };
    }
    lines.push('float distance=1e30,orientation=1.0;');
    factors.forEach(([r, i], n) => {
      const complex = r !== zero && i !== zero;
      lines.push(
        `float f${n}=divisorDistance(d${r === zero ? i : r},d${complex ? i : zero},${complex ? 'true' : 'false'});`,
        `distance=min(distance,abs(f${n}));orientation*=sign(f${n});`
      );
    });
    lines.push('return orientation*distance;', '}');
    return { source: lines.join('\n'), operations: used.size, factors: factors.length };
  }
  globalThis.HodgeDivisor = Object.freeze({
    fragment: (formula, signs) => compile(formula, signs),
    surface: (terms, signs) => compile(terms.map(([c, e]) => {
      const [p, q = 1] = String(c).split('/').map(Number);
      return [p / q, e];
    }), signs, true)
  });
})();
