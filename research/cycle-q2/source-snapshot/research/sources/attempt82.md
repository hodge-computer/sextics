# Cycle-q2 attempt 82 — an unsuccessful closure attempt, with exact failure witnesses

**Verdict: no original certificate, no disproof of unrestricted existence, and no Lean existence proof.**

This is a new attempt in the current response. It does not claim continuous work between conversations. The new computations are direct exact polynomial/rational calculations, not a purported completion of any unreviewed prior research theorem.

## 1. Protected original problem

The variable order is `(X0,X1,X2,Y0,Y1,Y2)` and

```
F = X0^6+X1^6+X2^6+Y0^6+Y1^6+Y2^6
    +(X0^3 X1 Y0 Y1 + X1^3 X2 Y1 Y2 + X2^3 X0 Y2 Y0)/2
A = X0^2 X1^2 X2^3 Y0^2 Y1^2 Y2
q = 2.
```

The only accepted target here is nonzero homogeneous D, gcd_C(D,F)=1,
six homogeneous Ni of degree deg(D)+7, and a polynomial Q such that

```
E = A D^2 - 2D sum_i Ni Fi
    + F (D sum_i partial_i Ni - sum_i Ni partial_i D) = F^3 Q.
```

No restriction on Q is introduced. No different sextic or lower-pole target is substituted.

## 2. The K3 route: what was available and what was missing

The uploaded Round-5 synthesis reports a moving-discriminant enlargement with
(6,15) remaining boundary conditions at mu=infinity,0. It does **not print the
21 equations or their generic coefficient matrices**. Their references are
local `file:///Users/ben/...` paths, not accessible mounted files.

The public discussion supplies the proper weighted K3 polynomial and a generic
weighted-Jacobian construction of its connection. Its reported frozen slice
explicitly omits `partial_lambda h_lambda`; a frozen solution is not a solution
of the coupled two-variable equation.

The actual system is

```
partial_lambda h_lambda + Gamma_lambda h_lambda
+ partial_mu h_mu + Gamma_mu h_mu = C_source.
```

I did not reconstruct and solve the full generic 18-component connection or the
claimed 21-boundary-equation system in this attempt. No assertion that these
boundary equations have been solved is justified by the calculations below.

### Direct source and infinity-chart check

On X1=1 use x=X0, z=X2, D=Y1,
lambda=Y0/X0, mu=Y2/X2, U=x^2, V=z^2. With homogeneous K3 variable C,

```
W = (1+lambda^6) U^3 + (1+mu^6) V^3 + C^6 + D^6
    +(lambda U^2 C D + mu V C^3 D + lambda mu U V^2)/2.
```

The exact original projective source on C=1 is

```
(lambda^2 mu U^2 V^2 D^2 / (4 W^3))
  dU wedge dV wedge dD wedge dlambda wedge dmu.
```

The sign and factor 1/4 are checked from the original coordinate order, not
inferred from an old residue statement. Put mu=1/t, V=t^2 Z. Then

```
W_infinity = (1+lambda^6)U^3 + (1+t^6)Z^3 + C^6+D^6
           +(lambda U^2 C D+t Z C^3 D+lambda t^3 U Z^2)/2.
```

The five-form Jacobian is exactly -1. The transformed source numerator is

```
-lambda^2 t^3 U^2 Z^2 D^2/4.
```

Thus the source has no parameter-axis pole in these coordinates: it vanishes
at least to order 1 at mu=0 and to order 3 at t=0. The two endpoint equations
agree after renaming V as Z. These assertions are exact symbolic identities.

**Scope:** regularity of the source is not rational exactness, not a solution
of the boundary conditions, and not proof of smoothness at every lambda.
Current residues, frame transitions and their lambda derivatives still matter.

### Why boundary residues cannot simply be dropped

Here is a useful generic local fact, not an assertion that the original PDE is
solved. Suppose a flat connection on a rational vector bundle is regular at
mu=0, and a rational current satisfies

```
nabla_lambda U + nabla_mu V = C,
```

with C regular there. A finite Laurent curl

```
U -> U - nabla_mu H,
V -> V + nabla_lambda H
```

preserves the equation by flatness. It can remove every pole of U of order
at least two: cancel the most negative Laurent term with a term of H whose
mu derivative has that order, and repeat. All coefficients used in this
finite operation are rational in lambda.

After this, U=a(lambda)/mu + regular. Any pole of V would produce a pole of
order at least two in nabla_mu V, which no other term can cancel; hence V is
regular. The remaining coefficient of mu^(-1) is necessarily

```
(partial_lambda + Gamma_lambda(lambda,0)) a(lambda) = 0.
```

The possible horizontal residue a is **not automatically zero** and cannot be
discarded without a global lift/connecting-map argument. This is exactly why
axis regularity does not justify declaring the reported boundary ODEs solved.
The argument applies separately in a regular frame at infinity; simultaneous
global gauge assembly is an additional obligation.

## 3. A direct original-coordinate candidate: complete two-normal-order repair

The prior attempt81 first-normal Hessian candidate was not rerun as a research
job. Instead, I constructed a new second-normal completion and tested the
literal original expression.

Let

```
H = Hess(F),       h=det(H),       K=adj(H),
v0=(5/24) H^(-1) grad(A),
b=div(v0),
w=(5/6) H^(-1) grad(b),
v=v0+F w.
```

Euler's identities are

```
H z = 5 grad(F),
z.grad(A)=12 A.
```

Consequently

```
v0(F)=A/2.
```

The coefficients of v0 have homogeneous degree 7, so b has degree 6. Applying
Euler a second time gives

```
w(F)=(5/6)*(z.grad(b)/5)=b.
```

Retaining every derivative, not merely normal contractions,

```
div(v)=b + w(F) + F div(w)=2b+F div(w),
v(F)=A/2+F b.
```

Thus the complete rational expression satisfies the exact identity

```
A - 2 v(F) + F div(v) = F^2 div(w).              (1)
```

The first two normal orders therefore cancel exactly, for this particular
source and candidate. The remaining condition would be that div(w) vanish
modulo F. That condition is not automatic.

### Explicit polynomial circuit; no implicit denominator clearing

The candidate can be written using ordinary homogeneous polynomials:

```
M = (5/24) K grad(A),
B = h div(M) - M.grad(h),
T = (5/6) K [h grad(B) - 2 B grad(h)],
D = h^4,
N = h^3 M + F T.
```

Indeed b=B/h^2 and w=T/h^4, so N/D=v. The degrees are

```
deg h=24, deg M=31, deg B=54, deg T=97,
deg D=96, deg Ni=103=deg D+7.
```

Substituting into the literal original expression gives

```
E = F^2 h^3 [h div(T) - 4 T.grad(h)].            (2)
```

This equation retains the full regular polynomial remainder. It is **not**
the required F^3Q identity unless the bracket is divisible by F.

### Legality of this candidate's denominator

The original F is smooth over C: choose a largest-absolute-value nonzero
coordinate of modulus M at a hypothetical gradient zero. Its pure sixth-power
derivative has modulus 6 M^5. The coupling derivatives have total modulus at
most 2 M^5 for an X-coordinate and at most M^5 for a Y-coordinate. This is
impossible. Hence the projective hypersurface is smooth and geometrically
irreducible.

The exact point in the next section has F=0 and h nonzero. Therefore F does
not divide h, and irreducibility gives gcd_C(h^4,F)=1. This establishes the
required complex coprimality, not just a rational gcd computation.

The diagonal source character is also preserved: F has weight 0 under
(2,1,0,3,2,1), A has weight 5 modulo 6, and the volume has weight 3, giving
residue character 2. The Hessian transforms covariantly; h has weight
-2*(2+1+0+3+2+1)=0 modulo 6. The constructed currents transform with the
source's required component weights. No invariant averaging is used.

## 4. Exact third-normal failure, over characteristic zero

Work in the explicitly defined number field

```
K0=Q(a),    2 a^6+a^2+2=0,
```

whose displayed polynomial is irreducible over Q. At

```
z0=(1,1,1,a,a,a)
```

one has F=0, and

```
h(z0)=647522500+901358750 a^2+429615000 a^4 != 0.
```

Exact differentiation, using all third Taylor coefficients of the inverse
Hessian, gives

```
div(w)(z0) =
 -24794482878626528643751031440349 a
    /113627755274144570873730106659000
 +1613879643062374465291739720377 a^3
    /138878367557287808845670130361000
 -55623037682695961238563707233679 a^5
    /208317551335931713268505195541500.
```

This is a nonzero degree-five representative in a degree-six number field.
It is not a floating-point nonzero, a finite-field inconsistency, or a
numerical approximation.

### Independent literal original-E check

A second calculation expands the actual polynomial-circuit expression

```
A D^2-2D N.grad(F)+F(D div(N)-N.grad(D))
```

at `(1,1,1,a,a,a+epsilon)` **without substituting its simplified formula (2)**.
It retains the derivatives of D and all six divergence components. Its
constant and epsilon coefficients vanish, whereas its epsilon^2 coefficient
is nonzero. The exact equality checked is

```
[epsilon^2]E = D(z0)^2 * (a+6 a^5)^2 * div(w)(z0) != 0.
```

The complete algebraic-number coefficient is stored in
`check_literal_original_jet.json`.

Since F has a simple zero along this line (`a+6 a^5 != 0`), every F^3Q has
order at least three. The nonzero epsilon^2 coefficient therefore proves
that **no polynomial Q makes this candidate a certificate**.

This failure excludes this explicitly constructed numerator tuple only.
It does not exclude every tuple with D=h^4, every Hessian-supported current,
or unrestricted cycle-q2 existence.

## 5. Other routes examined but not claimed executed or solved

The supplied old first-order-deformation archive concerns differentiating
the accepted q1 construction on the original cyclic family; it is not a
finished q2 primitive. It was inspected for deduplication, not executed anew.

The older tangent-hyperplane denominator `(X0^6+Y0^6)(X1^6+Y1^6)` looked like
an open full linear solve in attempt56, but the later attempt57 checkpoint
reports a complete exclusion. Likewise, the tangent-times-two-variation
pencil from attempt63 is reported excluded in attempt65. Those old solves
were **not repeated**, and their reports are not used as premises in the new
Hessian proof.

A source-compatible degree-six Fermat deformation was considered, but an
invariant degree-six continuation would return to an already reported
excluded profile. It was not promoted into a new computation.

No new geometry, trace, isogeny, conditional Lean theorem, chart regularity
result, or partial-current identity is being presented as a global solution.

## 6. Execution and access record

New executed programs:

1. `k3_boundary_chart.py`: direct original source, exact infinity chart,
   five-form Jacobian and boundary source orders.
2. `hessian_second_normal.py`: new exact two-normal-order repair,
   84 inverse-Hessian Taylor coefficients through order three,
   independent right-inverse checks, exact characteristic-zero failure.
3. `check_literal_original_jet.py`: independent construction of the literal
   original E through epsilon^2, with all moving denominator derivatives.

Python and SymPy 1.14.0 ran locally. No Lean executable was run. The runtime
was available, unlike some prior attempts. No private working tree or the
pasted report's `/Users/ben/...` scripts was accessed. Public GitHub text
was available; the referenced K3 binary attachment could not be retrieved
through the attempted web/container routes. Library copies of older K3
archives were accessible, but they did not provide the newer reported
boundary equations.

The final pipeline has **not** reached a successful E=F^3Q check. Its only
full original-candidate test is the exact failure in Section 4.

No external messages, publications, repository writes, or new scheduled
tasks were made. This packet is saved in the current conversation's working
container; no Library upload is claimed.

## 7. Exact unresolved problem

The original certificate remains missing. In the chosen K3 route, one must
construct a rational solution of the genuinely coupled equation, retaining
`partial_lambda h_lambda`, or construct an adequate open-boundary extension,
and then perform complete source reconstruction and the original identity
check. This attempt did not solve those equations.

The uploaded report's 21 boundary counts are not an executable specification
of their coefficients. That access gap prevents using its claimed reduction
as-is; it does not imply that the mathematical problem is impossible or that
no independent reconstruction can be made.

## Sources consulted

- The user's exact original target in this conversation.
- Uploaded `Pasted text(20261104-035259).txt`, especially the Route02 account.
- https://raw.githubusercontent.com/hodge-computer/sextics/main/data/cycle-q2/instance.rec
- https://raw.githubusercontent.com/hodge-computer/sextics/main/formal/README.md
- https://github.com/hodge-computer/sextics/discussions/61
- https://gist.github.com/fqlx/6e65179d28dfbd05fd0e94e831a52323/5643a96366bee5f659c4f99dd1eca4605c941e21
- Saved attempt81 report and Hessian scripts, read as prior construction input.
- Saved attempts56,57,63,64,65 checkpoints, consulted to prevent duplicate work.

The generic K3 derivation and prior exclusion claims were not independently
re-executed. The new Hessian identities and their exact failure depend only
on the original F,A and the programs included here.
