# Cycle-q2 — fresh attempt 78: exact constant-volume rectification, cubic Euler connection, and minimal two-scale rational source-moment lift

**Status: ORIGINAL CERTIFICATE OPEN.** No polynomial tuple `(D,N0,...,N5,Q)` satisfying the original equation, and no closed Lean proof, was obtained. This attempt derived a different coordinate system that preserves the actual source, verified a complete two-component identity in the trace-zero cubic connection, proved a new full-covariant obstruction to an *arbitrary rational one-weight current* in that chart, and constructed a source-serving *global rational two-weight current* by a six-by-six exact inverse. Its full divergence is nonzero, verified with all moving derivatives, so it is **not** the desired primitive.

## 1. Protected immutable polynomial target

Fixed physical coordinates `(X0,X1,X2,Y0,Y1,Y2)`:

```
F= X0^6+X1^6+X2^6+Y0^6+Y1^6+Y2^6
   +(X0^3*X1*Y0*Y1+X1^3*X2*Y1*Y2+X2^3*X0*Y2*Y0)/2,
A=X0^2*X1^2*X2^3*Y0^2*Y1^2*Y2,
q=2.
```

The only accepted goal requires homogeneous `D≠0`, `gcd_C(D,F)=1`, six homogeneous `Ni` of degree `deg D+7`, unrestricted polynomial `Q`, and the **literal identity**

`A*D^2 - 2*D*Σ Ni ∂iF + F*(D*Σ∂iNi - ΣNi∂iD) = F^3*Q`.

Primary project records were read at `data/cycle-q2/instance.rec`, `data/cycle-q2/why.md`, and `formal/README.md`. Its nontrivial diagonal residue character `ζ6²` remains unchanged. The complete original-source-to-cubic binding and regular normal remainder were independently audited in saved attempt 77; this attempt uses that audited binding and **newly verifies** the explicit cubic source moments and the new coordinate identities. The inherited binding was not unnecessarily re-executed. The private Math-project checkout was not accessed; Lean was not run. No substitution of a different physical numerator or a q=1 primitive is made.

## 2. New constant-volume birational chart (finite algebraic cover not needed)

Retain the previously source-bound cubic coefficients in `(P,U,Z,b)`:

`L=P^6+U², M=P U² b/2, N=P U Z/2, K=(U⁴+U²)b³+U(1+Z⁶)+Z U² b²/2`,

`p=N/L - M²/(3L²), q_c=K/L - M N/(3L²)+2M³/(27L³)`.

The inherited actual source is `R_cub = c (m_p ∇p k2 + m_q ∇q_c k2)` with

`c=M²N/(6PUL²), m_p=-2M/(3L²), m_q=-N/(3L²)+2M²/(9L³)`.

Define the *different*, source-preserving rational coordinates

```
r=P^5/5,        u=U/P^3,       w=P b,       z=Z/P^2,
ℓ=1+u²,         α=u/(2ℓ),      β=u⁴/(12ℓ²),
p=α z - β w², v=-w/α.
```

The inverse rationally recovers `U=uP³`, `b=w/P`, `Z=zP²` and `w=-αv`, `z=(p+βw²)/α`. The coordinate `r` is rational in `P`; if `r` alone is used to replace `P`, there is a degree-five algebraic extension, but **all constructions remain rational in the original P-chart**. The exact four-form Jacobian is

`dP ∧ dU ∧ dZ ∧ db = − dr ∧ du ∧ dp ∧ dv`.

The coefficient-wise equality and Jacobian were independently checked over characteristic zero (`verify_rectification.py`). Thus the moving divergence is the ordinary one with *constant density* in `(r,u,p,v)`. The two elementary divergence-free fields inherited from attempt 77 rectify to **commuting coordinate derivatives**:

`P⁻⁵(P ∂P+3U ∂U+2Z ∂Z−b ∂b)=∂r`,

`P (p_b ∂Z−p_Z ∂b)=∂v`.

This is a useful improvement over the old dense Sylvester determinant approach. The auxiliary `P`-scaling must NOT be confused with the original sixth-root character.

## 3. Fully explicit actual source, cubic coefficient, and weights

Writing `q_c=Σ_{k∈{-3,0,3,9}} P^k q_k(u,p,v)`, with `w,z` the displayed rational functions of `(u,p,v)`, the coefficients are **exact**:

```
q_-3 = u(1+u w³)/ℓ,
q_0  = u² z w²/(2ℓ) − u³ w z/(12ℓ²) + u⁶ w³/(108ℓ³),
q_3  = u⁴ w³/ℓ,
q_9  = u z⁶/ℓ.
```

The **actual** cubic source moments obey

`c m_p = P⁻⁴ A0(u,p,v)`, `c m_q = P⁻⁴ B0(u,p,v)` exactly, with

```
A0 = −u⁶ w³ z/(144ℓ⁴),
B0 = −u⁵ w² z²/(288ℓ⁴)+u⁸ w⁴ z/(864ℓ⁵).
```

These identities were checked without specializing any moving coordinate. Notice four *different* `P` powers in `q_c`, even though the source moments each have a single power `P⁻⁴`. That mismatch drives the one-weight obstruction below.

## 4. NEW universal rank-two covariant Euler identity

For the trace-zero vector `k2=(6(2p³−27q_c²),162p q_c)^T/Δ²`, `Δ=4p³+27q_c²`, use the **actual moving-root matrices** `B_p,B_q` from attempt77; `∇p=∂p+B_p`, `∇q=∂q+B_q`. An exact symbolic calculation proves

`2p ∇p k2 +3q_c ∇q_c k2 +5 k2 =0`, and

`det(∇p k2, ∇q_c k2)=−1080/Δ³ ≠0`.

Thus the **full** covariant source equation for *any* base current `J` multiplying `k2` has precisely the two necessary and sufficient conditions

```
J(p) − (2p/5) div J = c m_p,
J(q_c) − (3q_c/5) div J = c m_q.
```

This is stronger than merely matching `J(p),J(q_c)` and hoping its divergence vanishes. The moving derivative and nonconstant `k2` factor are kept. The identities and determinant were independently checked (`verify_root_euler.py`). They apply to the cubic root source and do not themselves prove a physical certificate or dispose of the normal regular remainder.

## 5. NEW exact exclusion of a completely arbitrary *one-weight* cubic current

Call a rational current *one-weight* here if in `(r,u,p,v)` it has

`J_r=P F`, `J_u=P⁻⁴ G`, `J_p=P⁻⁴ C`, `J_v=P⁻⁴ H`,

with **arbitrary** `F,G,C,H∈C(u,p,v)`, no restrictions on denominators or degrees. Let `D0=F+G_u+C_p+H_v` be its actual divergence coefficient. The two covariant conditions in Section 4 are equivalent to

`C=A0+(2p/5)D0`, together with the four algebraic equations, one per `k∈{-3,0,3,9}`:

`k q_k F + (q_k)_u G + (q_k)_v H + [(2p/5)(q_k)_p−(3/5)q_k]D0 = δ_{k0} B0 − A0(q_k)_p`.

At `(u,p,v)=(1,0,1)` the exact determinant of this **4×4 matrix** is

`−43/622577612487697367040 ≠ 0`.

Therefore there is a unique *algebraically permissible* rational tuple `(F,G,H,D0)` over the generic field, and it specializes to

`F=1/73728, G=−1/24576, H=1/73728, D0=−5/73728`, with `C=1/28311552`.

But **differentiating the unique rational candidate using the complete parameter-dependent inverse before evaluating** gives

`F+G_u+H_v+C_p−D0 = −323/7133184 ≠0`

at that exact point. A second and third independent rational fiber produced nonzero mismatches. Since this is a nonzero rational function over characteristic zero, **no one-weight rational `k2`-only current exists with full covariant source equality**, even allowing arbitrary denominators in `u,p,v`. This does not exclude mixtures of multiple `P` weights, a rational function with essential mixed `P` denominators, lower cubic root sections, or the unrestricted original six-coordinate certificate. The exact calculation is in `euler_covariant.py` and its execution log.

A separate first test imposing `div J=0` before using Euler gave a nonzero 4×4 augmented determinant `43/9180280442698590295425024` at the same point. The **new full-covariant test** above is the stronger relevant result.

## 6. NEW constructive global rational **two-weight source-moment lift**

To investigate the first case not excluded by Section 5, allow

```
J_r=P(F0+P³F1),
J_u=P⁻⁴(G0+P³G1),
J_p=P⁻⁴ A0,
J_v=P⁻⁴(H0+P³H1).
```

All six unknown coefficients lie in `Q(u,p,v)` and are reconstructed **exactly** using a finite 6×6 inverse; they are not numerical fitted coefficients. Let `x=(F0,G0,H0,F1,G1,H1)^T`, and index rows by `n=-1,0,1,2,3,4`. Define the explicitly reconstructible matrix:

`M[n,(3j+0,3j+1,3j+2)] = (k q_k,(q_k)_u,(q_k)_v)` whenever `j∈{0,1}` and `k=3(n−j)∈{-3,0,3,9}`; otherwise enter zero.

Set `r_n=δ_{n0}B0−(3n∈{-3,0,3,9}? A0(q_{3n})_p:0)`.

**Reconstruction witness**: `x=M⁻¹r` over `Q(u,p,v)`. At `(u,p,v)=(1,0,1)`, the selected determinant is

`−111365/919799811598869109911291833232352346112 ≠0`,

so the rational inverse exists generically. By construction (the six exact coefficient equations), the resulting current globally satisfies the **two exact source moments**

`J(p)=c m_p`, `J(q_c)=c m_q`.

This is a genuine algebraic rational current with no `b`-adic truncation, not the original certificate. Because it need not be divergence-free, its full covariant divergence remains

`R_cub + (d0 +P³ d1) P⁻⁴ k2`, where

`d0=F0+(G0)_u+(H0)_v+(A0)_p`, `d1=4F1+(G1)_u+(H1)_v`.

All derivatives of `M⁻¹r` were evaluated **implicitly and exactly**, using `∂x=M⁻¹(∂r−(∂M)x)`. At the first rational point they are

`d0=−270735123916183/914386690252800`,

`d1=−3881872907/1190607669600`,

both **nonzero**. Two other independent rational points also gave nonzero values (`two_weight_witness.json`). Thus the uniquely reconstructed **strict-moment** two-weight current is not a primitive. Since the first weight fails even the full covariant conditions, and this strict two-weight moment lift fails divergence, a solution should use the full Euler freedom and/or additional weights or root sections.

## 7. A precise new construction route for the unsolved step (not a certificate)

The cubic Euler identity suggests allowing the two weights while letting their divergence be nonzero. Put

`J_r=Σ_{j=0,1} P^(1+3j) F_j`, `J_u=ΣP^(−4+3j) G_j`, `J_v=ΣP^(−4+3j) H_j`, `J_p=ΣP^(−4+3j) C_j`.

Introduce actual divergence coefficients `D_j=(1+3j)F_j+(G_j)_u+(H_j)_v+(C_j)_p` and enforce

`C_j=δ_{j0}A0+(2p/5)D_j`.

The six coefficient equations of the exact `q_c` condition then read

`M x = r+Σ_{j=0,1} D_j s^{(j)}`,

where the same invertible matrix `M` is used, and

`s_n^(j)= [(3/5)q_k−(2p/5)(q_k)_p]` if `k=3(n−j)∈{-3,0,3,9}`, otherwise zero.

Therefore **all** `F_j,G_j,H_j` are reconstructed *rationally and linearly* in the two unknown scalar functions `D_0,D_1` by the fixed `6×6` inverse, and the **only remaining equations** in this two-weight `k2`-only class are the two explicit first-order linear PDEs

`(3/5)D_j−(2p/5)(D_j)_p −(1+3j)F_j−(G_j)_u−(H_j)_v−δ_{j0}(A0)_p =0`, for `j=0,1`.

These equations were **not solved**. This finite construction is an actual suggested rational-integration route with an invertible reconstruction matrix, not a claim of global rational solvability. A successful rational `D_0,D_1` would provide a *cubic `k2`-only* current; it would STILL require complete original physical transport, normal regular remainder, character, homogeneous legal complex-coprime denominator, degree checks, and the literal original equation.

## 8. Evidence, provenance, and exact unresolved step

The scripts were executed with Python and SymPy exact rational arithmetic, not numerical fitting. `verify_rectification.py` proves the coordinate/source identities and constant Jacobian, `verify_root_euler.py` proves the covariant Euler relation and determinant, `homogeneous_current.py` checks the stricter moment obstruction, `euler_covariant.py` establishes the **full-covariant one-weight no-go**, and `two_weight.py` reconstructs the global rational two-weight moment current and evaluates its complete nonzero divergence. All three independent samples are saved with precise rational values.

The strongest newly established theorem is the **one-weight full-covariant no-go** inside the genuine source-bound cubic chart, plus a **constructive two-weight global rational source-moment lift** and an exact 2-scalar PDE/inverse-reconstruction route. None is an original cycle-q2 certificate. The exact unsolved step is **global rational integration with nontrivial mixed weights and/or additional cubic-root sections**, followed by the literal physical polynomial identity. There is **no six-variable candidate** to check against `F³` and no Lean proof. Nothing was published, sent externally, or scheduled.
