# Cycle-q2 — disproof audit (checkpoint 79)

**Verdict:** No disproof of the original unrestricted certificate was obtained. No certificate was obtained either. This is a direct audit of what a nonexistence proof must establish, not another restricted-denominator obstruction or a claim that conjectural status prevents research.

## 1. Exact target and quantifiers

In the fixed order `(X0,X1,X2,Y0,Y1,Y2)`, retain

```
F = X0^6+X1^6+X2^6+Y0^6+Y1^6+Y2^6
    +(X0^3 X1 Y0 Y1+X1^3 X2 Y1 Y2+X2^3 X0 Y2 Y0)/2,
A = X0^2 X1^2 X2^3 Y0^2 Y1^2 Y2, q=2.
```

A certificate has nonzero homogeneous `D`, `gcd_C(D,F)=1`, six homogeneous `Ni` of degree `deg(D)+7`, and arbitrary polynomial `Q`, with

```
A D^2-2D sum(Ni Fi)+F(D sum(partial_i Ni)-sum(Ni partial_i D))=F^3 Q.
```

A genuine disproof must rule out every such tuple, with no degree bound, no rational-coefficient restriction, and no restriction to the currents used in earlier attempts. The attempt-78 report was read, but its computations were not rerun and its scoped obstructions are not used as premises here. In particular its one-weight k2-only obstruction is not a general nonexistence theorem.

## 2. Checked hypotheses for the geometric formulation

Let `tau(X,Y)=(X,-Y)`. Direct symbolic substitution gives `tau*F=F` and `tau*A=-A`. Since tau has determinant -1 on the six coordinates, it also sends the projective volume form Omega to -Omega. Thus `A Omega/F^3` and its residue class are invariant under tau. The different sixth-root character does not change this assertion: these are different group actions.

Here is a direct complex smoothness proof. At any nonzero complex vector choose a coordinate of maximum absolute value `M>0`. Its pure sixth-power derivative has absolute value `6 M^5`. For an X coordinate, the sum of absolute coupling-derivative coefficients is 2; for a Y coordinate it is 1. Consequently the coupling derivative has absolute value at most `2 M^5`, strictly smaller than `6 M^5`. The full derivative in the selected coordinate cannot vanish. Thus the homogeneous gradient has no nonzero zero and `X=V(F) in P^5_C` is smooth.

These derivative coefficient bounds were reconstructed exactly by the attached program; they are `(2,2,2,1,1,1)`. Smoothness also implies complex irreducibility here: two positive-degree projective hypersurface components in P^5 would intersect, making their product singular on the intersection.

The primary project overview and Diamond's vanishing criterion identify the existence statement with divisor support of the appropriate Griffiths residue. The invariant rational Hodge substructure has Hodge coniveau at least one, because tau acts as -1 on H^(4,0). The generalized Hodge conjecture predicts that this whole invariant substructure is supported on a divisor. Its complexification contains the actual class of A.

**Logical implication:** generalized Hodge conjecture for this invariant substructure implies the requested certificate. A rigorous unrestricted nonexistence proof for this fixed smooth F and odd A would therefore contradict that generalized Hodge prediction. This is not an unconditional existence proof and is not a reason to rule out researching nonexistence. It is also not automatically a counterexample to the ordinary rational (p,p) Hodge conjecture.

## 3. Explicit denominator-independent residue test from the original F,A

This calculation uses neither the prior cubic chart nor any partial-current assembly.

Work on the affine chart X2=1 and put

```
x=X0, y=X1, u=Y0, v=Y1, t=Y2,
a=x^2 y^2 u^2 v^2,
c=(y^3 v+x u)/2,
h=x^6+y^6+u^6+v^6+1+x^3 y u v/2,
f=t^6+c t+h,
g=f_t=6t^5+c.
```

The projective source pulls back, with the standard orientation, to

```
a t dx wedge dy wedge du wedge dv wedge dt / f^3.
```

Let the normal derivative keeping `(x,y,u,v)` fixed be `T=g^(-1) partial_t`. Changing the normal variable to s=f, the simple-pole residue coefficient of this third-order-pole form is

```
rho = (1/2) T^2(a t/g)
    = 15 a t^4 (48 t^5-7c) / (6t^5+c)^5,
```

restricted to f=0. The attached program proves this rational identity before restricting to f=0. The factor 1/2 is the Taylor coefficient, not an adjustable source multiplier.

Let K=C(X)=Frac(C[x,y,u,v,t]/(f)). Define the four commuting, implicitly moving derivations

```
delta_j = partial_j-(f_j/g) partial_t,
   j in {x,y,u,v}.
```

Every rational 3-form over K is represented using the four differentials dx,dy,du,dv. Thus the class of

```
alpha = rho dx wedge dy wedge du wedge dv
```

vanishes in H^4_dR(K/C) exactly when rho is a sum `sum_j delta_j(h_j)` for four arbitrary rational functions h_j in K, with the standard contraction convention for their associated 3-form.

A certificate forces this class to vanish: writing vi=Ni/D, the original identity says

```
A/F^3 + div(v/F^2) = Q/D^2.
```

Its right side is regular at the generic point of F=0. By projective contraction and residue, the source therefore has exact rational residue. Accordingly, **a proof that [alpha] is nonzero in H^4_dR(K/C) would rule out every legal denominator and all six original components.** No such proof has been obtained here. Nonzero rho as a rational function is not the same as nonzero [alpha].

This is a diagnostic necessary condition, not an additional certificate or an asserted computation of the entire function-field cohomology.

## 4. Exact trace test: no contradiction

The trace to the rational base K0=C(x,y,u,v) commutes with exterior differentiation. Hence a nonzero trace class would give a nonexistence obstruction. Here the trace itself is zero:

```
Tr_{K/K0}(rho)=0.
```

The program proves this universally over Q(c,h), by inverting `6t^5+c` modulo `t^6+c t+h`, reducing the displayed rational density, and taking the trace of its six-by-six multiplication matrix. The result is exactly zero, not numerically close to zero and not a finite-field result. Multiplication by a does not change the zero trace.

Conceptually, for the generic normal family `t^6+c t+h-s=0`, the sum over its six roots of `t/f_t` is zero (numerator degree 1 is less than 5). Twice differentiating with respect to s gives the same trace identity. The executable calculation independently checks its algebra.

Zero trace is inconclusive: the trace-zero component of a finite extension can still contain nonexact differential forms. This test neither disproves nor proves the original certificate.

## 5. What was and was not executed

Executed locally with Python/SymPy: exact original polynomial/parity reconstruction; derivative coefficient bounds; affine source identity; exact twice-normal source formula; generic characteristic-zero trace calculation. `verification.log` and `EXACT_CHECKS.json` record the output.

Read but not replayed: attempt78 REPORT and RESEARCH_INDEX; a Library search also located an attempt28 report of an SNC-polar-divisor obstruction. The latter is not asserted as a newly checked theorem here and is not used in the argument.

Not executed or established: full cohomological nonvanishing, a general period witness, a universal denominator bound, a completed original polynomial tuple, or any Lean proof. No external messages, publications, repository modifications, or task changes were made.

## 6. Non-repetition / next meaningful disproof step

Do not report one-direction, one-weight, fixed-degree, or single-curve failures as nonexistence for the original problem. Do not rerun the zero trace test as though a nonzero scalar residue were sufficient. The actual missing disproof step is a functional or geometric argument proving that the original residue survives in H^4_dR(C(X)/C), equivalently cannot be removed on any dense open. The existence search remains logically viable.

## Primary sources checked

- https://raw.githubusercontent.com/hodge-computer/sextics/main/data/cycle-q2/instance.rec
- https://raw.githubusercontent.com/hodge-computer/sextics/main/data/cycle-q2/why.md
- https://raw.githubusercontent.com/hodge-computer/sextics/main/formal/README.md
- https://github.com/hodge-computer/sextics/blob/main/docs/overview.md
- Benjamin E. Diamond, *Hodge Structures in Sextic Fourfolds Equipped with an Involution*, arXiv:2603.29157v2, especially Section 2 and the vanishing criterion: https://arxiv.org/html/2603.29157v2

**Bottom line: original existence and original nonexistence are both unproved in this audit. The prior restricted failures do not decide between them.**
