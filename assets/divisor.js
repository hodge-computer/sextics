/* Compile display polynomials into per-pixel value/gradient expressions.
   Floating point is presentation only; accepted proof data is never changed. */
(() => {
  'use strict';
  /* A jet is a value and its derivatives. It carries only the derivatives its use needs: D is
     differentiated along the two directions of the screen, F along the four coordinates of
     the sphere it is projected in.
     Single precision spans 2^±126. A sub-expression of degree at most six whose coefficients
     keep it within 2^±60 cannot leave that range, except closer than a fraction of a pixel
     to where all its terms vanish, so it is evaluated in plain arithmetic (pa, pm). F is
     always such an expression. Anything larger is a jet times 2^(64 e): a product is brought
     back near 1 whenever it drifts, and a sum first aligns its two exponents (da, dm, with dn
     admitting a plain jet). Every rescaling multiplies by a literal power of two, which is
     exact on any hardware. Only ratios within one jet are ever used, so the exponent itself
     never reaches the screen. */
  const PLAIN_DEGREE = 6,
    PLAIN_SIZE = 2 ** 60;
  const jets = (n) => `
struct DivJet${n} { float v; vec${n} g; float e; };
DivJet${n} pa(DivJet${n} x,DivJet${n} y) { return DivJet${n}(x.v+y.v,x.g+y.g,0.0); }
DivJet${n} pm(DivJet${n} x,DivJet${n} y) { return DivJet${n}(x.v*y.v,x.g*y.v+x.v*y.g,0.0); }
DivJet${n} dn(DivJet${n} x) {
  vec${n} g=abs(x.g);
  float m=max(abs(x.v),${n === 2 ? 'max(g.x,g.y)' : 'max(max(g.x,g.y),max(g.z,g.w))'});
  if(m==0.0) x.e=DIV_NONE;
  else if(m<2.3283064365386963e-10) { x.v*=DIV_UP; x.g*=DIV_UP; x.e-=1.0; }
  else if(m>4294967296.0) { x.v*=DIV_DOWN; x.g*=DIV_DOWN; x.e+=1.0; }
  return x;
}
void dalign(inout DivJet${n} x,inout DivJet${n} y) {
  float d=x.e-y.e;
  // One step apart is an exact shift; further apart, the smaller term is below rounding.
  if(d>0.0) { float s=d>1.5?0.0:DIV_DOWN; y.v*=s; y.g*=s; y.e=x.e; }
  else if(d<0.0) { float s=d<-1.5?0.0:DIV_DOWN; x.v*=s; x.g*=s; x.e=y.e; }
}
DivJet${n} da(DivJet${n} x,DivJet${n} y) {
  dalign(x,y);
  DivJet${n} r=DivJet${n}(x.v+y.v,x.g+y.g,x.e);
  if(r.v==0.0) r=dn(r);
  return r;
}
DivJet${n} dm(DivJet${n} x,DivJet${n} y) {
  return dn(DivJet${n}(x.v*y.v,x.g*y.v+x.v*y.g,x.e+y.e));
}`;
  const GLSL = `
const float DIV_NONE=-1e30;
const float DIV_UP=18446744073709551616.0;      // 2^64
const float DIV_DOWN=5.421010862427522e-20;     // 2^-64
// How the six coordinates change across one pixel, horizontally and vertically.
vec3 divAx,divAy,divBx,divBy;${jets(2)}${jets(4)}
// Newton's step from this pixel to a factor's zero set, in pixels, from the exact derivatives.
vec2 divisorStep(DivJet2 x) {
  float scale=max(abs(x.g.x),abs(x.g.y));
  if(scale==0.0) return vec2(1e15);
  vec2 g=x.g/scale;
  return clamp(x.v/scale,-1e15,1e15)*g/dot(g,g);
}
// A zero of order k lies k steps away, and walking one pixel towards it shortens the step by
// 1/k of a pixel. That change, read from the neighbouring pixels, supplies k; the step itself
// is exact, so simple curves owe nothing to differences between pixels.
float divisorPixels(vec2 step) {
  float size=length(step),change=length(step.x*dFdx(step)+step.y*dFdy(step));
  return size*max(1.0,size/max(change,1e-30));
}
`;
  function compile(formula, signs, surface = false) {
    if (!formula || (Array.isArray(formula) && !formula.length))
      return {
        source: GLSL + 'float divisorField(vec3 a,vec3 b){return 1e30;}',
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
    // A complex factor vanishes where its squared modulus does, to twice the order.
    const real = factors.map(([r, i]) =>
      r === zero ? i : i === zero ? r : add(mul(r, r), mul(i, i))
    );
    real.forEach(visit);
    visit(zero);
    const literal = (x) => {
      const s = String(x);
      return /[.e]/i.test(s) ? s : s + '.0';
    };
    const order = [...used];
    const n = surface ? 4 : 2,
      lines = surface
        ? ['DivJet4 surfaceField(vec3 a,vec3 b) {']
        : [GLSL, 'float divisorField(vec3 a,vec3 b) {'];
    // All factors are homogeneous, so the coordinates may be rescaled to unit size.
    lines.push(
      'float scale=max(max(max(abs(a.x),abs(a.y)),max(abs(a.z),abs(b.x))),max(abs(b.y),abs(b.z)));',
      'scale=max(scale,1e-20); a/=scale; b/=scale;'
    );
    if (!surface) lines.push('divAx/=scale; divAy/=scale; divBx/=scale; divBy/=scale;');
    // Degree and size bounds, taking each coordinate to be at most one, decide which
    // sub-expressions need the exponent.
    const plain = new Map(),
      bound = new Map(),
      admitted = new Set();
    for (const m of order) {
      const [op, a, b] = nodes[m];
      let degree, high, low, expr;
      if (op === 'c') {
        [degree, high, low] = [0, Math.abs(a), a ? Math.abs(a) : Infinity];
        expr = `DivJet${n}(${literal(a)},vec${n}(0.0),0.0)`;
      } else if (op === 'v') {
        [degree, high, low] = [1, 1, 1];
        const side = a < 3 ? 'A' : 'B',
          k = a % 3;
        expr = surface
          ? `DivJet4(${a < 3 ? 'a' : 'b'}[${k}],uDivisorPlane[${a}]/scale,0.0)`
          : `DivJet2(${a < 3 ? 'a' : 'b'}[${k}],vec2(div${side}x[${k}],div${side}y[${k}]),0.0)`;
      } else {
        const [x, y] = [bound.get(a), bound.get(b)];
        [degree, high, low] =
          op === '+'
            ? [Math.max(x[0], y[0]), x[1] + y[1], Math.min(x[2], y[2])]
            : [x[0] + y[0], x[1] * y[1], x[2] * y[2]];
      }
      bound.set(m, [degree, high, low]);
      plain.set(
        m,
        expr !== undefined ||
          (plain.get(a) &&
            plain.get(b) &&
            degree <= PLAIN_DEGREE &&
            high <= PLAIN_SIZE &&
            low >= 1 / PLAIN_SIZE)
      );
      if (expr === undefined) {
        const use = (x) => {
          if (plain.get(m) || !plain.get(x)) return `d${x}`;
          if (!admitted.has(x)) {
            admitted.add(x);
            lines.push(`DivJet${n} t${x}=dn(d${x});`);
          }
          return `t${x}`;
        };
        expr = `${(plain.get(m) ? 'p' : 'd') + (op === '+' ? 'a' : 'm')}(${use(a)},${use(b)})`;
      }
      lines.push(`DivJet${n} d${m}=${expr};`);
    }
    if (surface) {
      const [r, i] = factors[0];
      if (factors.length !== 1 || (r !== zero && i !== zero))
        throw new Error('The surface polynomial must be scalar-real on this slice.');
      lines.push(`return d${real[0]};`, '}');
      return { source: lines.join('\n'), operations: used.size };
    }
    lines.push('float distance=1e30;');
    for (const m of real) lines.push(`distance=min(distance,divisorPixels(divisorStep(d${m})));`);
    lines.push('return distance;', '}');
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
