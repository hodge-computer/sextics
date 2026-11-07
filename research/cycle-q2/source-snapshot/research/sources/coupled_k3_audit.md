# Cycle-q2: coupled-K3 solver scope audit

**Date:** 2026-11-04. **Original certificate: NOT FOUND.**

## Executive result and correction

The requested next experiment was generalized Hermite elimination of the full proper K3 equation in `mu`, followed by a rational ODE solve in `lambda`, with reconstruction witnesses. Before a generic elimination was completed, a conflict was found in the accessible research record: an older report excluded *all polar supports depending on two of the original ratios*. The proposed proper K3 parameters are exactly two such ratios.

This packet resolves the scope identification and supplies new, independent exact algebra supporting the exclusion. In particular, two explicitly reconstructed 16-by-16 minors prove that the relevant K3 family varies along every nonconstant curve in its parameter torus. An independent, deliberately coarse rigorous Fermat-pairing calculation confirms that the actual source has a nonzero (3,1) component. The geometric support argument is written out below with its standard mathematical inputs identified.

**Conclusion of the argument:** the actual source cannot be closed by rational currents in the stated *proper K3 module over C(lambda,mu)*. Increasing base-denominator degrees, adding the moving K3 discriminant, or retaining more boundary coefficients within this same proper module does not remove this obstruction. This is not a finite ansatz failure. It is also **not nonexistence of the original cycle-q2 certificate**: currents with additional fibre-dependent pole divisors and residue channels are outside this module.

This corrects the preceding recommendation. A completed generic Hermite reduction, its induced ODE, and a rational ODE solution were **not** computed in this run. No such execution or witness is claimed. The conclusion here is a mathematical scope obstruction, using the proofs and computational witnesses below, not a Lean formalization or an independently peer-reviewed theorem.

## 1. Protected target and literal source binding

The coordinates remain `(X0,X1,X2,Y0,Y1,Y2)`, with

```
F = X0^6+X1^6+X2^6+Y0^6+Y1^6+Y2^6
    +(X0^3 X1 Y0 Y1+X1^3 X2 Y1 Y2+X2^3 X0 Y2 Y0)/2,
A = X0^2 X1^2 X2^3 Y0^2 Y1^2 Y2, q=2.
```

The required output is a nonzero homogeneous polynomial D coprime to F **over C**, six homogeneous Ni of degree `deg D+7`, and unrestricted polynomial Q, satisfying the literal identity

```
A D^2 - 2D sum_i Ni F_i
+F (D sum_i partial_i Ni - sum_i Ni partial_i D) = F^3 Q.
```

No such tuple is produced here. No complete candidate was available to pass to this polynomial verifier. In particular, the support argument does not silently impose Q=0 or change q.

Set

```
lambda=Y0/X0, mu=Y2/X2,
U=X0^2, V=X2^2, C=X1, Df=Y1.
```

Here `Df` is a fibre coordinate, **not** the certificate denominator. The weighted sextic, of weights `(2,2,1,1)`, is

```
W=(1+lambda^6)U^3+(1+mu^6)V^3+C^6+Df^6
  +(lambda U^2 C Df+mu V C^3 Df+lambda mu U V^2)/2.
```

Exactly, `W=F` after the substitution, and

```
A=lambda^2 mu U^2 V^2 C^2 Df^2.
```

The determinant of the six-coordinate transformation, with output order `(U,V,C,Df,lambda,mu)`, is **+4**. The ordinary physical Euler field becomes the weighted fibre Euler field, with zero action on lambda and mu. Thus, with the indicated orientations,

```
A Omega_P5/F^3 = [lambda^2 mu U^2 V^2 C^2 Df^2 Omega_W/(4 W^3)]
                 wedge dlambda wedge dmu.
```

`check_source_chart.py` checks the literal polynomials, determinant, Euler action, and source symmetries. The diagonal sixth-root weights `(2,1,0,3,2,1)` give residue character 2 modulo 6. No averaging over this sixth-root symmetry is used.

The independent pair flips `(Xi,Yi)->(-Xi,-Yi)` preserve both the numerator and the volume. The projective pair-sign group is `(mu_2)^3/diagonal(mu_2)`, of order four. The source is invariant under this smaller group, which is the quotient group used for the K3 model. This does not erase the nontrivial sixth-root character.

### Exact match with the archived two-ratio family

The older support report uses

```
Wold=(1+p^6)a^3+(p u/2)a^2 b+(1+u^6)b^3
     +(u/2)b^2 z w+(p/2)a z^3 w+z^6+w^6.
```

The exact identity is

```
(p,u,a,b,z,w)=(mu,lambda,V,U,C,Df).
```

It is checked as a polynomial identity in `check_k3_scope.py`. This is not a comparison based on naming two unrelated parameters the same way.

## 2. Standard mathematical inputs and evidence boundary

The argument uses the following mathematical facts, rather than claiming to reprove all of algebraic Hodge theory by a finite calculation.

1. Weighted adjunction, binary-quartic Jacobians, and the minimal Weierstrass description of elliptic K3 surfaces. A degree-(8,12) Weierstrass model on P1 with nonzero discriminant and no (4,6) point resolves to a K3. Huybrechts, *Lectures on K3 Surfaces*, Chapter 11, Remark 2.1, states the needed criterion.
2. Local Torelli for smooth complex K3 surfaces: contraction with a nonzero holomorphic two-form identifies the Kodaira--Spencer map with the differential of the period map. The same source, Chapter 6, Proposition 2.8, supplies this input. Along an ADE stratum one uses simultaneous resolution after finite base change and the polarized contraction model.
3. Holomorphic differential forms on a smooth projective variety are closed; K3 surfaces have no holomorphic one-forms. These imply the threefold lemma in Section 5.
4. Gysin localization and strictness of mixed Hodge structures. In degree four, the (3,1) part supported on a divisor comes from (2,0) on resolutions of its components. Contributions whose image has codimension at least two have no (3,1) part. This also handles finite unions and resolution exceptional divisors.
5. Griffiths residue reduction, Gauss--Manin flat transport, and the standard Fermat residue polarization formula recorded in the archived source proof. The exact formula is displayed in Section 6. Its normalization is an explicitly declared input to the independent arithmetic audit; the full Pham intersection lattice was **not** recomputed in this run.

The older report's broad support conclusion is **not substituted for the new calculations**. The polynomial/source identification, the two maximal deformation minors, their independent standard-library verification, the fibre invariant identities, and a separate rational sign-and-tail computation were all executed here. The geometric implications of these calculations use the standard inputs above.

## 3. Every torus parameter gives a K3 model after resolution

Use the cyclic ordering `(a,b,h)=(V,U,C^2)` and `t=Df/C`. The genus-one cubic is

```
a0 a^3 + d a^2 b + b0 b^3 + e b^2 h + f a h^2 + c0 h^3,
a0=1+mu^6, b0=1+lambda^6, c0=1+t^6,
d=lambda mu/2, e=lambda t/2, f=mu t/2.
```

The binary cubic at `h=0` has at least one simple root: a binary cubic with no simple root would be a cube of a linear form, impossible here because its a^2 b coefficient is nonzero and its a b^2 coefficient is zero. Thus, over C, a point at infinity gives a section. Over the generic parameter-curve field, a finite constant-field extension suffices for this argument.

For a general cyclic cubic with coefficient names `(a,b,c,d,e,f)`, put

```
Aell=a e^2 f+b d f^2+c d^2 e,
Bell=-(27a^2 b^2 c^2+4a^2 c e^3+4a b^2 f^3
       +6a b c d e f+4b c^2 d^3-d^2 e^2 f^2)/4.
```

These are not taken on faith from a numerical fibre. A projection from `(r:1:0)`, with `a r^3+d r^2+b=0`, gives the binary quartic

```
[(3ar+d)u^2+fr]^2
 -4[(3ar^2+2dr)u+e][a u^3+fu+c].
```

Its classical invariants satisfy, as generic exact polynomial identities,

```
I=-48 Aell, J=-1728 Bell.
```

The standard quartic Jacobian is consequently constant-scaled to

```
y^2=x^3+Aell*x+Bell.
```

`check_fibre_geometry.py` verifies these identities before specializing the parameters.

For the actual K3 family,

```
Aell(t)=mu^2 lambda^3 t/8 *
 [t^6+(1+mu^6)/(mu lambda)*t^2
       +mu(1+lambda^6)/lambda^2*t+1].
```

The bracket's third derivative is **120 t^3**. For nonzero lambda,mu, its zeros in the t-torus therefore have multiplicity at most three. At t=0 and t=infinity, Aell has order one as a section of O(8). Bell is a section of O(12). There is no (4,6) point.

The discriminant is not the zero polynomial for any such pair: Aell has degree exactly seven and a nonzero leading coefficient. If `4 Aell^3+27 Bell^2` vanished identically, the odd degree 21 of the first term could not equal the even degree of the second. The minimal Weierstrass surface is therefore a K3 for every torus parameter pair.

For completeness, the weighted cubic model is normal, not just generically a K3. Each plane cubic fibre is reduced. On the t-torus its three cyclic mixed coefficients d,e,f are nonzero. If a repeated linear factor omitted one variable, one of these three coefficients would vanish. Otherwise normalize it to x+y+z. The three absent mixed monomials in `(x+y+z)^2(lx+my+nz)` force

```
n+2l=0, l+2m=0, m+2n=0,
```

whose determinant is 9; hence the remaining linear factor is zero, a contradiction. At t=0 and infinity the h^3 coefficient is nonzero, and its partial derivative excludes a repeated factor. The generic fibre is smooth, so the singular locus of the total surface is finite. The finitely many points at the projection's indeterminacy locus do not change normality. The normal weighted degree-six hypersurface is Gorenstein with trivial dualizing sheaf. Being birational to a smooth K3, it has canonical surface singularities, hence ADE singularities. One can also see this by comparing the nonzero holomorphic two-form on its minimal resolution with the trivial canonical form: its effective canonical divisor pushes to an effective linearly trivial divisor on the normal projective model, which is zero, so all discrepancies are nonnegative.

This establishes the proper K3 fibre input even on parameter curves contained in the discriminant of the weighted model. Merely checking generic smooth parameters would not have sufficed for an all-denominator support argument.

## 4. New exact deformation witnesses: no contracted parameter curve

There are 30 weighted-degree-six monomials in `(U,V,C,Df)`. Form the 30-by-16 coefficient matrix with columns

```
W_U * (U,V,C^2,C Df,Df^2),
W_V * (U,V,C^2,C Df,Df^2),
W_C * (C,Df), W_Df * (C,Df), W_lambda, W_mu.
```

The first fourteen columns are precisely the weighted coordinate-orbit directions, including equation scaling. This completeness has a geometric explanation: O(2) embeds the model as a (2,3) complete intersection in P4. Its unique quadric is the rank-three cone `Z0 Z2-Z1^2=0`. Every polarized model isomorphism preserves that quadric. Its projective stabilizer consists of GL2 on `(U,V)`, additions of the three quadratic coordinates to each of U,V, and the symmetric-square GL2 action on `(C,Df)`, modulo the projective scalar. Adding the cubic's scalar gives exactly the fourteen displayed directions.

Rows are indexed in this order:

```
[(i,j,k,6-2*i-2*j-k)
 for i in range(4) for j in range(4-i)
 for k in range(7-2*i-2*j)].
```

Two exact maximal minors are

```
rows I1=(0,1,3,4,5,6,9,10,12,13,14,15,19,22,24,26),
det M[I1,:] = (243/256) lambda^5 mu^9 (mu^6-1),

rows I2=(0,1,3,4,5,6,9,10,12,13,14,15,19,24,26,29),
det M[I2,:] = -(243/512) lambda^5 mu^10 (3 lambda^6-1).
```

Both were computed symbolically with SymPy and then **independently reconstructed from W** by a Python-standard-library sparse polynomial Laplace expansion. The second verifier imports neither the first verifier's matrix nor a CAS determinant. It checks the complete two-variable polynomial identities, not sample values.

On the parameter torus the common zero set of these two minors is contained in the 36 points

```
mu^6=1, 3 lambda^6=1.
```

Thus no algebraic curve is contained in the possible rank-drop set. The two parameter tangent directions are independent modulo coordinate changes at the generic point of **every** curve. Local Torelli therefore implies that the resolved K3 family is non-isotrivial on every such curve.

A separate exact calculation over `Q(a)`, `3 a^6=1`, at `(lambda,mu)=(a,1)` gives orbit rank 14 and total rank 15. Its parameter-kernel direction is `(2a,1)`. This is a diagnostic at one exceptional point; it is **not needed** for the no-curve conclusion, and no unsupported classification of all 36 points is claimed.

## 5. Why two-ratio supports cannot carry the source's (3,1) part

Let Z be any irreducible divisor obtained by imposing an algebraic relation `g(lambda,mu)=0` on the original fourfold, with lambda,mu nonzero generically. Take its quotient by the pair-sign group and a smooth projective resolution. Over a dense open of the normalization of the parameter curve, its fibres resolve to K3 surfaces.

Suppose this resolved quotient threefold had a nonzero holomorphic two-form eta.

* If its restriction to a general K3 fibre were nonzero, closedness of eta would make that restriction a flat family of cohomology classes lying in the one-dimensional H20 line. The period line would be constant. Local Torelli would force the K3 family to be locally isotrivial, contradicting Section 4.
* If the fibre restriction were zero, eta would be mixed base/fibre degree `(1,1)`. Its fibre part would give a holomorphic one-form on a K3, which is impossible. The curve base has no two-forms either.

Hence the quotient threefold has H20=0. Equivariant resolution and finite-group descent identify this with the invariant H20 sector of the original support. Only that invariant sector is needed, because the actual source is pair-sign invariant. This does **not** assert vanishing of all non-invariant forms on the covering divisor.

The cases lambda=0,infinity or mu=0,infinity are coordinate hyperplane sections. Each is smooth: in every coordinate stratum the pure-power gradient term has modulus `6 M^5`, while the coupling terms have total modulus at most `2 M^5` at a coordinate of maximal modulus M. Smooth sextic threefold hyperplane sections have H20=0.

For finite unions and arbitrary multiplicities, the relevant weight-four (3,1) support image is generated by the component Gysin images H20(-1). Intersections and exceptional divisors mapping to codimension at least two in the original fourfold cannot add a (3,1) image; their weight-four contribution is of type (2,2), and higher-weight overlap terms do not map into pure H4 of the smooth projective fourfold. Thus arbitrary finite unions and pole orders do not evade the conclusion.

In particular, **every finite pole divisor pulled back from the lambda,mu base, together with coordinate chart divisors, has zero source-sector (3,1) support image**.

This is the same geometric exclusion recorded in Section 34 of the archived report, now with the exact proper-K3 parameter identification and the new two-minor proof of non-isotriviality. The earlier record's old support theorem, and the newer record's label 'proper K3 route open', were not silently assumed consistent.

## 6. Independent arithmetic check that the actual source has nonzero H31

Set

```
F_t = sum Zi^6 + (t/2)(T0+T1+T2),
alpha_t=Res(A Omega/F_t^3),
beta_t=Res(B Omega/F_t^2), B=X0 X1^2 Y0 Y1^2.
```

The three Ti are the actual cyclic coupling monomials, and `B*T2=A`. The family is smooth for complex `|t|<3` by the same gradient bound `6-2|t|`.

Negation of all three X coordinates fixes alpha_t and beta_t, while acting by -1 on H40. Since beta_t lies in F3, it therefore has pure type (3,1). A nonzero cup pairing of alpha_1 with the complex conjugate of beta_1 detects the original source's (3,1) component.

### Coefficients computed in two independent ways

Expand at the Fermat fibre, retaining all coupling degrees n up to **22**. For coupling multiplicities `(k0,k1,k2)` with sum n, let

```
e_i = a_i + sum_j k_j E[j,i],
E0=(3,1,0,1,1,0), E1=(0,3,1,0,1,1), E2=(1,0,3,1,0,1).
```

Terms with an exponent congruent to 5 modulo 6 vanish after reduction. Otherwise put `b_i=(e_i mod 6)+1`, `k=sum b_i/6`, and `r_i=(e_i+1-b_i)/6`. For initial pole p, the reduced coefficient is

```
(-1)^n Gamma(k)/(Gamma(p)*2^n*k0!*k1!*k2!) * product_i (b_i/6)_(r_i).
```

The first code path uses this exact rational product. The second directly performs each elementary Griffiths reduction

```
z_i^e / F0^q  ->  (e-5)/(6(q-1)) * z_i^(e-6)/F0^(q-1).
```

All coefficients agree exactly. Each truncated vector has 38 nonzero coefficients.

### Declared polarization input

The standard Fermat residue polarization formula, in the normalization used in the archived source proof, is

```
Q(epsilon_b,conjugate(epsilon_b))/C0
 = (-1)^(3-k)/Gamma(k)^2 * product_i Gamma(b_i/6)/Gamma(1-b_i/6),
C0=(2*pi)^4/6^5.
```

Distinct character components are orthogonal. This formula is a mathematical input here; the full Pham intersection matrix was not regenerated. It is also consistent with the publicly reported sign certificate for the unchanged source. This packet independently reconstructs the coefficients, interval arithmetic, and tail bound using that explicitly stated formula.

The two required independent gamma ratios are enclosed using exact rational arithmetic: shift log Gamma by 20, use seven Stirling correction terms, and bound the remainder by the absolute first omitted term. This is the positive-real remainder estimate in NIST DLMF 5.11(ii). Logarithms and exponentials are themselves enclosed by rational series bounds. All rounding is outward; no floating-point value is used in an assertion.

### All-order tail, not a numerical sign guess

Put `q_i=(a_i+1)/6` and

```
Kp=product Gamma(q_i)/(Gamma(p)*pi^3).
```

On the unit simplex, weighted AM--GM gives

```
sum_j product_i t_i^(E[j,i]/6) <= 2/3.
```

The Dirichlet integral then bounds the full degree-n coefficient vector in the absolute-polarization norm by

```
Kp * binomial(n+p-1,p-1) / 3^n.
```

For our two starting monomials every qi lies in `[1/6,1)`, so
`Gamma(qi) < 1/qi+exp(-1) < 7`, and `pi>3`. Therefore the deliberately coarse rational bounds

```
KA=7^6/54, KB=7^6/27
```

suffice. Let `TA=sum_(n>=23) binomial(n+2,2)/3^n` and
`TB=sum_(n>=23) (n+1)/3^n`. Exact geometric-series summation and Cauchy--Schwarz bound the omitted pairing by

```
KA*KB*[TA*(3/2)^2 + TB*(3/2)^3 + TA*TB]
 = 607227253784650937769793/5105052356919840631255104
 < 0.119.
```

The exact interval for the truncated pairing is near `-0.251002385281725`; the full rigorous interval is contained in

```
-2/5 < Q(alpha_1,conjugate(beta_1))/C0 < -1/10.
```

Both endpoints are tested as exact rational inequalities. This is weaker than the older tight interval but independently sufficient for nonvanishing. It does not infer H31 from the pole order or from a nonzero rational representative.

## 7. Consequence for the proposed coupled solve

The proposed proper-module equation is

```
(partial_lambda+Gamma_lambda) J_lambda
 +(partial_mu+Gamma_mu) J_mu = s,
J_lambda,J_mu in C(lambda,mu)^18,
```

where s is the actual K3 source of Section 1. Allow arbitrary rational functions in all eighteen components: no degree, pole-order, initial-value, or preferred-horizontal-lift constraint is imposed.

A rational solution would be defined over a nonempty Zariski-open part of the base, obtained by deleting finitely many parameter curves and possibly isolated points. It would make the actual source exact in the proper relative de Rham module. The usual retained Griffiths homotopies provide the corresponding total-space boundary; equivalently, on an affine base of dimension two the relevant degree-four Leray piece is `H2(base,R2)`, with no R1 or R3 fibre contributions. The base-current equality kills that piece. The remaining degree-zero/R4 piece is Tate and cannot contain H31. Thus the source's (3,1) part would be supported on the deleted vertical divisors and the chart boundary.

Section 5 proves that these supports have zero invariant (3,1) image; Section 6 proves the source has a nonzero component there. Contradiction.

A concrete pole check helps keep the scope transparent: a base denominator g of bidegree (a,b) clears in physical coordinates as

```
ghat = X0^a X2^b g(Y0/X0,Y2/X2).
```

Its divisor is precisely a two-original-ratio divisor plus coordinate boundary. Arbitrarily complicated moving factors such as the intrinsic K3 discriminant are still of this form. Matrix inversion/gauge changes in the proper K3 frame introduce further *base* factors, not a new horizontal source-carrying divisor. Finite algebraic extensions of the coefficient field do not repair rational exactness: characteristic-zero normalized field trace commutes with the extended connection and would give a solution over C(lambda,mu).

**This rules out the specific proper-module rational-ODE route proposed in the preceding answer.** It is not merely a warning that a particular bounded ansatz may fail. No completed Hermite reduction or ODE solve is being claimed; this necessary geometric test decides the proposed class before that computation.

### What is NOT ruled out

* Rational primitives with pole divisors moving inside the K3 fibres, or residue/third-kind extensions of the proper module.
* The full three-original-ratio elliptic equation, with genuinely three-ratio pole divisors.
* Any original certificate whose polar support is not contained in the two-ratio-plus-coordinate class.

The original generalized-Hodge/coniveau question is therefore untouched by a purported unrestricted disproof. No unrestricted disproof is asserted.

## 8. Execution and access record

The supplied report recorded the counts `(6,15)` but did not supply the actual generic boundary equations. Public supporting attachment download was attempted and failed; local prior K3 ZIPs were inspected but did not supply the needed generic 18-dimensional matrices. A fetched public `gm_engine.py` concerned a different degree-18 surface model and was not silently substituted for W. No private user-machine paths were accessed. The generic 18-by-18 elimination, a Hermite quotient basis, its induced ODE, and a source preimage were **not computed**.

The following new programs were executed successfully with Python and SymPy 1.14:

1. `check_source_chart.py`: literal source, determinant, Euler action, symmetries, gradient bounds.
2. `check_k3_scope.py`: exact family identification, 30-by-16 matrix, first generic determinant.
3. `check_minors.py`: two generic determinant formulas and gcd.
4. `independent_minors.py`: independent standard-library reconstruction and exact polynomial Laplace verification of both minors.
5. `check_exceptional.py`: one exceptional point over an exact degree-six number field.
6. `check_fibre_geometry.py`: generic quartic invariants, exact K3 minimality coefficients, and repeated-line determinant.
7. `check_hodge_pairing.py`: two exact Fermat reduction methods, rational gamma enclosures, and the full tail/sign bound.

`RUN_ALL.log` and `CHECKS.json` record the final execution. The mathematical support proof is not itself a software formalization; its named Hodge-theoretic inputs are explicit above. No Lean compiler or proof kernel was run. No remote repository changes, external messages, or new automations were made. The packet is saved locally; no new Library upload is claimed.

## 9. Non-repetition checkpoint

Do not resume the proposed base-only proper-K3 Hermite/ODE solve while treating it as a plausible route to the unchanged source. Do not interpret slice consistency, higher jets, the `(6,15)` boundary counts, or removal of apparent frame poles as evidence against the support obstruction. They can all coexist with absence of a global rational solution.

A genuinely changed computational problem must include a source-carrying *horizontal* divisor/residue extension or use the full three-ratio geometry. Its connecting map and the actual source must be checked before a large coefficient solve. No particular such extension is solved or recommended as guaranteed here.

The original target, character, regular remainder, legal homogeneous clearing, and literal E=F^3 Q remain mandatory. None has been replaced by the present restricted no-go theorem.
