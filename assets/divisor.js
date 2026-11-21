/* Compile display polynomials into per-pixel value/gradient expressions.
   Floating point is presentation only; accepted proof data is never changed. */
(() => {
  'use strict';
  /* A jet is a value and its six ambient derivatives, times 2^(64 e). Carrying the exponent
     separately keeps factors of any degree inside single-precision range: a product is brought
     back near 1 whenever it drifts, and a sum first aligns its two exponents. Every rescaling
     multiplies by a literal power of two, which is exact on any hardware. Only ratios within
     one jet are ever used, so the exponent itself never reaches the screen. */
  const GLSL = `
struct DivJet { float v; vec3 a; vec3 b; float e; };
const float DIV_NONE=-1e30;
const float DIV_UP=18446744073709551616.0;      // 2^64
const float DIV_DOWN=5.421010862427522e-20;     // 2^-64
// How the six coordinates change across one pixel, horizontally and vertically.
vec3 divAx,divAy,divBx,divBy;
DivJet dc(float v) { return DivJet(v,vec3(0.0),vec3(0.0),v==0.0?DIV_NONE:0.0); }
DivJet dn(DivJet x) {
  vec3 g=max(abs(x.a),abs(x.b));
  float m=max(abs(x.v),max(g.x,max(g.y,g.z)));
  if(m==0.0) x.e=DIV_NONE;
  else if(m<2.3283064365386963e-10) { x.v*=DIV_UP; x.a*=DIV_UP; x.b*=DIV_UP; x.e-=1.0; }
  else if(m>4294967296.0) { x.v*=DIV_DOWN; x.a*=DIV_DOWN; x.b*=DIV_DOWN; x.e+=1.0; }
  return x;
}
void dalign(inout DivJet x,inout DivJet y) {
  float d=x.e-y.e;
  // One step apart is an exact shift; further apart, the smaller term is below rounding.
  if(d>0.0) { float s=d>1.5?0.0:DIV_DOWN; y.v*=s; y.a*=s; y.b*=s; y.e=x.e; }
  else if(d<0.0) { float s=d<-1.5?0.0:DIV_DOWN; x.v*=s; x.a*=s; x.b*=s; x.e=y.e; }
}
DivJet da(DivJet x,DivJet y) {
  dalign(x,y);
  DivJet r=DivJet(x.v+y.v,x.a+y.a,x.b+y.b,x.e);
  if(r.v==0.0) r=dn(r);
  return r;
}
DivJet dm(DivJet x,DivJet y) {
  return dn(DivJet(x.v*y.v,x.a*y.v+x.v*y.a,x.b*y.v+x.v*y.b,x.e+y.e));
}
// Newton's step from this pixel to a factor's zero set, in pixels, from the exact derivatives.
vec2 divisorStep(DivJet x) {
  vec2 g=vec2(dot(x.a,divAx)+dot(x.b,divBx),dot(x.a,divAy)+dot(x.b,divBy));
  float scale=max(abs(g.x),abs(g.y));
  if(scale==0.0) return vec2(1e15);
  g/=scale;
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
    const lines = surface
      ? ['DivJet surfaceField(vec3 a,vec3 b) {']
      : [GLSL, 'float divisorField(vec3 a,vec3 b) {'];
    // All factors are homogeneous, so the coordinates may be rescaled to unit size.
    lines.push(
      'float scale=max(max(max(abs(a.x),abs(a.y)),max(abs(a.z),abs(b.x))),max(abs(b.y),abs(b.z)));',
      'a/=max(scale,1e-20); b/=max(scale,1e-20);'
    );
    if (!surface)
      lines.push('divAx/=max(scale,1e-20); divAy/=max(scale,1e-20); divBx/=max(scale,1e-20); divBy/=max(scale,1e-20);');
    for (const n of order) {
      const [op, a, b] = nodes[n];
      let expr;
      if (op === 'c') expr = `dc(${literal(a)})`;
      else if (op === 'v') {
        const unit = [0, 0, 0, 0, 0, 0];
        unit[a] = 1;
        expr = `DivJet(${a < 3 ? 'a' : 'b'}[${a % 3}],vec3(${unit.slice(0, 3).map(literal)}),vec3(${unit.slice(3).map(literal)}),0.0)`;
      } else expr = `${op === '+' ? 'da' : 'dm'}(d${a},d${b})`;
      lines.push(`DivJet d${n}=${expr};`);
    }
    if (surface) {
      const [r, i] = factors[0];
      if (factors.length !== 1 || (r !== zero && i !== zero))
        throw new Error('The surface polynomial must be scalar-real on this slice.');
      const value = `d${real[0]}`;
      lines.push(`return DivJet(${value}.v,${value}.a/max(scale,1e-20),${value}.b/max(scale,1e-20),${value}.e);`, '}');
      return { source: lines.join('\n'), operations: used.size };
    }
    lines.push('float distance=1e30;');
    for (const n of real) lines.push(`distance=min(distance,divisorPixels(divisorStep(d${n})));`);
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
