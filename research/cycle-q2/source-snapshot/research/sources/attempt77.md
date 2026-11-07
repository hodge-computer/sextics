# Cycle-q2 — Attempt 77: new elementary four-direction rational moment lift, exact source audit, nonzero scalar remainder

**Date:** 2026-11-03 (America/Chicago). **VERDICT: ORIGINAL CERTIFICATE OPEN.** No full six-variable `(D,N0,...,N5,Q)` and no Lean existence theorem. The strongest new result is a **fully explicit, source-serving rational four-direction current** whose denominator involves a simple polynomial `tau`, **not** the 12-by-12 Sylvester determinant used in attempt 75. It serves the full two-component cubic source moments, and its complete covariant divergence has an exactly specified **nonzero** scalar remainder. A direct independent source audit was executed in this attempt. A prior claim that the normal source is `-Rcal` is now independently proved as a rational identity *before cubic reduction*. The regular remainder of the normal integration-by-parts formula is retained.

## 1. Protected original target, character, and provenance

In fixed physical order `z=(X0,X1,X2,Y0,Y1,Y2)`:

```
F = X0^6+X1^6+X2^6+Y0^6+Y1^6+Y2^6
    +(X0^3*X1*Y0*Y1+X1^3*X2*Y1*Y2+X2^3*X0*Y2*Y0)/2
A = X0^2*X1^2*X2^3*Y0^2*Y1^2*Y2, q=2.
```

Only a nonzero homogeneous polynomial `D` coprime to `F` over C, homogeneous `Ni` of degree `deg(D)+7`, and unrestricted polynomial `Q` with

`A D^2 - 2D Σ Ni Fi + F(D Σ∂i Ni - Σ Ni ∂i D) = F^3 Q`

can close the task. The diagonal sixth-root weights `(2,1,0,3,2,1)` give source weight 17 and projective volume weight 9, so the residue character is `zeta6^2`, **not invariant**. We did not average this character away. No denominator-degree or parity restriction is introduced. Primary source records accessed:

- `https://raw.githubusercontent.com/hodge-computer/sextics/main/data/cycle-q2/instance.rec`
- `https://raw.githubusercontent.com/hodge-computer/sextics/main/data/cycle-q2/why.md`
- `https://raw.githubusercontent.com/hodge-computer/sextics/main/formal/README.md`

The private Math-project checkout was not accessible or used. Python/SymPy 1.14 was available and all included scripts ran successfully. The previous attempt-76 `D_b+D_U` continuity conjugation and restricted integrating-factor failure were read as context, not rerun. Prior attempt-69 source transport was **independently checked** here, rather than taken as an unverified premise.

## 2. Fresh direct audit of original physical source and normal remainder

Define the six monomial coordinates

```
R=X2^2,  P=Y0*Y1/(X0*X1),  U=Y1^3/X1^3,
Z=Y2/X2,  a=X0^2*X1/(X2^2*Y1),  b=X1^3/(X2^2*Y1).
```

Let

```
L=P^6+U^2, M=P*U^2*b/2, N=P*U*Z/2,
K=(U^4+U^2)*b^3+U*(1+Z^6)+Z*U^2*b^2/2,
G=L*a^3+M*a^2+N*a+K, h=P^2*Z*U^4*b^2/24.
```

The exact monomial exponent Jacobian has determinant **+24**. Direct symbolic substitution verifies

`F = R^3 G/U`

and the complete six-form identity

`A dX0∧dX1∧dX2∧dY0∧dY1∧dY2 / F^3
 = (dR/R)∧ [h*a^2/G^3] dP∧dU∧dZ∧da∧db`.

`verify_physical.py` reconstructed both identities over `Q(z)` without calling an inherited script. Its resulting `PHYSICAL_AUDIT.json` also proves the character. The projective radial derivation becomes `2R d/dR`, so the Euler factor and moving-`da` orientation must be preserved when passing to the projective residue.

**The complete normal integration-by-parts formula, including its nonconstant simple-pole term**, holds with

`delta=(1/G_a)∂a`, `f=h*a^2/G_a`:

`h*a^2/G^3 da = d_a[-f/(2G^2)-delta(f)/(2G)] + [delta^2(f)/(2G)] dG`.

Only the restriction of the coefficient `delta²(f)/2` to `G=0` is the residue. Its variation off `G=0` contributes a **regular remainder**, which is *not* declared zero or discarded. This formula was verified as a literal rational identity in `Q[L,M,N,K,a,h]` (`verify_normal_remainder.py`).

Set `theta=a+M/(3L)`, `d=M/(3L)`, `p=N/L-M²/(3L²)`, `q_c=K/L-MN/(3L²)+2M³/(27L³)` and `V=3theta²+p`. The normalized residue is

`rho=(h/(2L³)) (V^-1 ∂theta)^2 ((theta-d)^2/V)`.

Define `k2=-6theta/V³`, and *moving-root* derivatives

`∇p k2=(∂p - (theta/V)∂theta)k2`,
`∇q k2=-(1/V)∂theta k2`.

The exact factor identity, **true before imposing the cubic equation**, is

```
(V^-1 ∂theta)^2 ((theta-d)^2/V)
    = -[-2d ∇p + (d²-p/3) ∇q] k2.
```

Since `c=M² N/(6 P U L²)=h/(2L²)`, `m_p=-2d/L`, and `m_q=(d²-p/3)/L`, this independently proves

**`rho = -Rcal`, with `Rcal=c(m_p ∇p k2 + m_q ∇q k2)`**.

This is exact for the true asymmetric source and preserves *both* cubic channels and their moving derivatives. See `verify_source_binding.py` and `SOURCE_BINDING_WITNESS.json`.

## 3. NEW: divergence-free Hamiltonian partial current in the simple coefficient chart

Use `(P,L,M,N)` as moving coordinates, with `U²=L-P^6`. The polynomial Jacobian satisfies

`det ∂(L,M,N,P)/∂(P,U,Z,b) = P² U⁴/2`.

Consequently the volume density in `(P,L,M,N)` is `±2/(P²U⁴)`, **independent of M and N**. The exact cubic constant in these coordinates is

```
K = U + 8M³/(P³U²)+8M³/(P³U⁴)
      +4M²N/(P³U³)+64N⁶/(P⁶U⁵).
```

Take `k=1/(6PUL²)` and `c=k M² N`. Define the stream function

`H = k( M⁴N/(6L) - M⁶/(54L²) )
   = M⁴(9LN-M²)/(324 L⁴ P U)`.

Its **exact rational Hamiltonian current** is

```
V_M=∂N H = M⁴/(36 L³ P U),
V_N=-∂M H = -M³(6LN-M²)/(54 L⁴ P U),
V_P=V_L=0.
```

The complete moving divergence is **zero**, including the chart density. Furthermore

`V(p)=(-2M/(3L²))*c = c*m_p`.

Both statements are exact polynomial/rational identities over `Q(P,L,M,N,U)` (with the actual relation `U²=L-P^6`); no parameter was frozen while differentiating M and N. Thus

`∇M(V_M k2)+∇N(V_N k2) = c*m_p∇p k2 + V(q_c)∇q k2`.

No `k2` scalar divergence error appears. The actual remaining source is one moving derivative channel,

**`R_q ∇q k2`, where `R_q = c*m_q - V(q_c)`**.

This is a new strict partial integration with an explicitly rational stream potential; it does NOT integrate the full source. The complete formula for `R_q` is defined by the displayed rational formulas and reconstructed in `verify.py`.

## 4. NEW: elementary transverse Euler current and a full rational *moment* lift

Consider, in the **original four cubic-base coordinates** `(P,U,Z,b)`,

`E=P∂P+3U∂U+2Z∂Z-b∂b`, `W=P^-5 E`.

Direct differentiation gives

```
div E=5,  div W=0,   E(p)=0,
E(q_c)=3U/L * [3Z^6+(U³-U)b³-1].
```

All FOUR moving derivatives are retained. In the coefficient chart, `E` acts by weights
`(P,L,M,N,U)=(1,6,6,6,3)` and respects `U²=L-P^6`.

Let the **simple, explicitly identified pole polynomial** be

`tau=3Z^6+(U³-U)b³-1`.

Then `W(q_c)=3U*tau/(P⁵L)`. On the open set `tau≠0`, define the *finite global rational function*

**`psi=R_q/W(q_c) = P⁵ L R_q/(3U tau)`**.

The four-direction rational field

**`J=V+psi W`**

obeys **both exact source-moment identities**

`J(p)=c*m_p`, `J(q_c)=c*m_q`.

Its **full** covariant divergence is the exact identity

**`Σ_j ∇j(J_j k2) = Rcal + [W(psi)] k2`**.

No Sylvester cofactors or determinants are needed, and no `T` ramification denominator is introduced. The source-moment construction is genuinely rational for all four parameters, not merely a `b`-adic power series. However its scalar remainder is **not zero**, so it is NOT a cubic primitive.

At the exact admissible coefficient point `(P,L,M,N,U)=(1,2,1,1,1)` (equivalently `(P,U,Z,b)=(1,1,2,2)`), all denominators are nonzero and

```
R_q=8189/3456,
psi=8189/990144,
W(psi)=379495/47279376 ≠0.
```

The verifier also reconstructed both rank-two connection components of the full source and current divergence at this point. Thus the nonzero scalar remainder is not inferred from a truncated Taylor series or a missing moving derivative. See `verify_full_moments.py`, `FULL_MOMENT_WITNESS.json`.

The pole divisor `tau` is **genuine for this finite current**: at `P=U=b=1`, its equation is `3Z^6-1=0`, and the exact numerator of `R_q` has nonzero remainder `-24Z^5-24Z^2+25Z+46` modulo it. This prevents cancelling `tau` from `psi` by naive algebraic simplification; it is **not a no-go** against all other currents. See `test_new_pole.py`.

## 5. Complete narrow two-direction obstruction (without extrapolation)

Any rational `(M,N)`-supported correction `T` with `div T=0` and `T(p)=0` must have

`T=(f(p)*p_N, -f(p)*p_M)`

where `f∈C(P,L,U,p)` (the constant field of `∂M|p`; this follows from the rational coordinate substitution `N=Lp+M²/(3L)` and `char C=0`). Its `q` moment is `f(p) D`, where

`D=p_N q_M - p_M q_N`.

To cancel the displayed residual it would require `f(p)=R_q/D`. This is **impossible**: at fixed `(P,U,L)=(1,1,2)`, the two rational points

`(M,N)=(0,5/6)` and `(M,N)=(1,1)`

both have `p=5/12` and `D≠0`, but

`R_q/D=0` at the first and `8189/159984` at the second.

Therefore no rational divergence-free **(M,N)-only** correction can complete this specified Hamiltonian partial current. This does *not* exclude other currents or directions.

A further exact 3×3 determinant witness excludes the particular two-generator correction combining `f(p)` Hamiltonian and an Euler-invariant coefficient times `W`: on a single Euler scaling orbit the source moments would require a constant pair, but the determinant is

`105030345284479954579/2507653251072 ≠0`.

This excludes **only that two-coefficient invariant class**, not general noninvariant scalar multipliers or independent tangent generators. See `restricted_two_tangent_test.py`.

## 6. Remaining exact mathematical obligation

The constructive advance is a **simple rational global moment lift** of the authentic source with a *single explicitly known nonzero scalar forcing*

`W(psi) k2`.

It remains to construct a rational correction with zero source moments and full covariant divergence `-W(psi) k2`, potentially using both independent tangent directions and/or lower connection vectors (`k1,k0`). The pole geometry of `tau` must be handled, not blindly cleared. In particular, `W(psi)≠0` blocks claiming this current is itself a primitive. The full normal regular remainder in Section 2 must also be transported when returning to the six physical coordinates. Complex gcd legality, homogenization, exact required degrees, polynomial `Q`, and the **literal** `E=F^3 Q` check remain completely outstanding.

No physical `(D,N,Q)` candidate was constructed, so none was passed or represented as passing the full original identity. No Lean existence proof was produced. This run did not publish anything, modify remote source code, contact anyone, or schedule another task.

## 7. Executed local evidence and repeatability

Python 3 with SymPy 1.14 was used. Run in this directory:

```
python verify_physical.py
python verify_normal_remainder.py
python verify_source_binding.py
python verify_chart_density.py
python verify.py
python verify_euler_tangent.py
python verify_full_moments.py
python test_new_pole.py
python restricted_two_tangent_test.py
```

All passed using exact rational or polynomial arithmetic; JSON outputs are included. No floating-point numerical fitting and no finite-field no-go extrapolation were used. For the current rational-source identity, the proof is algebraic and generic, and the rational points supply independent nonzero witnesses.
