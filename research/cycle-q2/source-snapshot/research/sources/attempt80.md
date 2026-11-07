# Cycle-q2 — Fresh attempt 80: source-preserving elliptic quotient, finite rational relative Green reduction, and complete moving two-channel equation

**Date:** 2026-11-03/04 (America/Chicago). **VERDICT: ORIGINAL CERTIFICATE OPEN.** No homogeneous nonzero complex-coprime `D`, no six degree-(`deg(D)+7`) physical numerators, no polynomial `Q` satisfying the literal identity, and no closed Lean existence proof. The strongest new result is an **exact, generically defined rational partial primitive of the ACTUAL original five-form**, constructed by an invertible 28-by-28/10-by-10 linear-algebra circuit in a new quotient-by-pair-signs plane-cubic fibration, with a complete two-dimensional rational elliptic remainder and **all three moving Gauss–Manin derivatives explicitly accounted for**. This is not one of the old moving-`a`, `Z`, or Euler-only constructions.

## 1. Immutable protected target

In the ordered original coordinates `Zphys=(X0,X1,X2,Y0,Y1,Y2)`, fix

\[
F=\sum_{i=0}^2(X_i^6+Y_i^6)+\tfrac12(X_0^3X_1Y_0Y_1+X_1^3X_2Y_1Y_2+X_2^3X_0Y_2Y_0),\quad
A=X_0^2X_1^2X_2^3Y_0^2Y_1^2Y_2,\quad q=2.
\]

The unchanged acceptance test is

\[
\boxed{AD^2-2D\sum_{i=0}^{5}N_i\partial_iF+F\bigl(D\sum_i\partial_iN_i-\sum_iN_i\partial_iD\bigr)=F^3Q.}
\]

Here `D != 0` homogeneous with `gcd_C(D,F)=1`, all `Ni` homogeneous of degree `deg D+7`, and `Q` unrestricted polynomial. The source's diagonal sixth-root weights `(2,1,0,3,2,1)` give residue character `zeta_6^2`, not the invariant character. No character-averaging or changed physical input is used.

The primary GitHub/raw pages and hodge.computer URL could not be fetched in this run (web cache misses and container DNS failure). The exact target was taken from this run's user prompt, and prior saved reports were consulted for **provenance**, not silently treated as independently verified new theorems. The private Math-project checkout and Lean were not available. All new calculations below were executed in the working Python/SymPy container, with executable scripts and exact rational witnesses in this packet.

## 2. NEW: a direct projective-to-elliptic quotient of the *exact original source*

On the dense affine chart `X2=1`, write `x=X0, y=X1` and

\[
z_0=Y_0/X_0,\quad z_1=Y_1/X_1,\quad z_2=Y_2,\quad
 t_0=x^2,\quad t_1=y^2,\quad t_2=1.
\]

For the homogeneous ternary cubic in `t`, define

\[
G(t;z)=\sum_{i=0}^2(1+z_i^6)t_i^3+\frac12\sum_{i=0}^2z_i z_{i+1}\,t_i^2t_{i+1},\qquad i\bmod3.
\]

**Exact original polynomial identity:** `F|_{X2=1}=G(t0=x²,t1=y²,t2=1;z)`. These coordinates quotient the independent sign flips of `(X0,Y0)` and `(X1,Y1)`. The original numerator and projective volume, with their true sign and degree, give **literally**

\[
\boxed{\left.\frac{A\,\Omega_{\mathbb P^5}}{F^3}\right|_{X_2=1}
=\frac{z_0^2z_1^2z_2}{4}\frac{t_0^2t_1^2}{g^3}
\,dt_0\wedge dt_1\wedge dz_0\wedge dz_1\wedge dz_2},
\quad g=G(t_0,t_1,1;z).
\]

The Jacobian is `dx dy dY0 dY1 dY2 = (1/4) dt0 dt1 dz0 dz1 dz2` (with wedge signs in that order). The exact source factor `1/4` is important. Its sixth-root character is retained: `wt(t0,t1,z0,z1,z2)=(4,2,1,1,1)` modulo six; the numerator has weight 5, the five-form weight 3, so the actual character is still `zeta_6^2`. This is a **direct new source binding**, not an inherited cubic-normal source claim. See `verify_elliptic_chart.py`.

The generic cubic `G=0` in `P²_t` is a smooth elliptic curve: the exact full-rank Jacobian-ideal witness at `z=(1,1,1)` below proves generic smoothness; the fiber at that point is itself smooth, e.g. a largest-coordinate derivative has diagonal contribution magnitude `6M²` versus total mixed contribution ≤`3/2 M²`.

## 3. NEW: globally rational finite-matrix *relative* integration of the literal third-order pole

Use the homogeneous projective form `Omega_t=t0 dt1∧dt2−t1 dt0∧dt2+t2 dt0∧dt1`. Write

\[
P=t_0^2t_1^2t_2^2,\quad S=t_0t_1t_2,\quad G_i=\partial_{t_i}G.
\]

Let `M4` list all 15 degree-four monomials of `(t0,t1,t2)` in the exact order of combinations-with-replacement. Let `M6` list all 28 degree-six monomials, similarly. Form all 45 columns of the degree-six coefficient matrix of `m*Gi` (`m∈M4`, `i=0,1,2`). **Select these exact 0-based columns:**

`[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,21,22,25,26,30,31,32,33]`.

Denote the resulting square matrix `M(z)` (28-by-28). Define `K(z)` (10-by-10) using nine degree-three columns `ti*Gj`, plus the final column `t0*t1*t2`. In a full characteristic-zero rational point `z0=z1=z2=1`, the **exact determinant witnesses** are

\[
\boxed{\det M(1,1,1)=-\frac{737315465160105}{524288}\ne0,\qquad
\det K(1,1,1)=-\frac{5204679057}{512}\ne0.}
\]

Therefore the same fixed matrices are invertible over `Q(z0,z1,z2)` generically, without a denominator-degree guess or a finite-field inference. Define `R_i(z,t)`, **homogeneous quartics in t**, from the entries of `M(z)^(-1)[P]`, placing zero in nonselected monomial slots. This yields exactly

\[P=\sum_i R_iG_i.\]

Define `H=(1/2)Σ ∂_{ti}Ri` and invert `K(z)` on its ten degree-three coefficients to get three **homogeneous linear** `Si` and scalar `lambda(z)` such that

\[H=\sum_i S_iG_i+\lambda(z)S.\]

Finally set `C(z)=Σ∂_{ti}Si`. Every coefficient in these formulas is an **explicit rational function** over `Q(z)`, reconstructible by the fixed inverses. No unbounded search or formal expansion is involved. In affine `t2=1`, set

\[
u_i=R_i-t_iR_2,\quad v_i=S_i-t_iS_2\quad(i=0,1),
\quad\eta_t=\frac{u_0dt_1-u_1dt_0}{2g^2}+\frac{v_0dt_1-v_1dt_0}{g}.
\]

Then the **complete literal rational meromorphic two-form identity** is

\[
\boxed{\frac{t_0^2t_1^2}{g^3}dt_0\wedge dt_1
=-d_t\eta_t+
\biggl(\frac{C(z)}g+\frac{\lambda(z)t_0t_1}{g^2}\biggr)dt_0\wedge dt_1.}\tag{REL}
\]

This holds generically as an exact identity, not just after imposing `g=0` or taking a residue. It follows from Euler's homogeneous cubic and the two checked polynomial identities above. We **independently cleared `g^3` and verified every affine polynomial coefficient at the witness fiber**; the identity was zero. Wedge with the full `dz0∧dz1∧dz2` and multiply by `phi=z0²z1²z2/4`: any `d_z eta_t` contribution vanishes because there are already three base differentials. Thus this is a source-serving *rational partial current for the entire original five-form*, and no normal regular remainder or moving product rule has been suppressed.

### Characteristic-zero reconstruction witness at the actual point

At `z0=z1=z2=1`, **without any variation of the physical source**, the full exact matrices reconstruct

\[
\boxed{C=-\frac{2464}{13029237},\qquad\lambda=-\frac{20544}{7238465}.}
\]

The unscaled values are nonzero, so the compact elliptic remainder is genuinely nonzero for the actual cubic family. Including the physical prefactor `phi=1/4`, the two source coefficients at this point are `(-616/13029237,-5136/7238465)`. The file `ELLIPTIC_EXACT_WITNESS.json` stores all 28 pivot columns, both determinants, **every Ri and Si**, the independently checked affine identity, and both moving connection channels. Do not confuse nonzero fiber residue with a disproof of the original *global* certificate: base-direction currents can still cancel it.

## 4. NEW: full moving two-channel base system, with exact connection at the witness fiber

Let

\[
e_0=\frac{dt_0\wedge dt_1}{g},\qquad e_1=\frac{t_0t_1dt_0\wedge dt_1}{g^2}.
\]

These represent a basis of the compact genus-one relative de Rham classes over the generic `z`-field. To derive their moving `z_j` derivatives, **do not freeze the cubic**:

- `∂_{z_j}e0=-(∂_{z_j}g)dt0∧dt1/g²`, reduced by the exact `10×10` inverse.
- `∂_{z_j}e1=-2 t0t1 (∂_{z_j}g)dt0∧dt1/g³`, reduced by the same `28×28` then `10×10` inverses.

Write the resulting *full* connection `∇_{z_j}=∂_{z_j}+Gamma_j(z)` on column coefficients of `(e0,e1)`. The explicit rational reconstruction is completely specified by these inverses, and at the original exact fiber `z=(1,1,1)` its **three independently computed matrices agree**:

\[
\boxed{\Gamma_{z_0}=\Gamma_{z_1}=\Gamma_{z_2}=
\begin{pmatrix}
-578/579&7360/13029237\\
4/193&-43209092/21715395
\end{pmatrix}.}
\]

A separate cyclic-family computation checked the difficult moving-frame contribution: along `z0=z1=z2=s` the original cubic is `a(s)G_h` with `a=1+s^6`, `h=s²/(2a)`. At `s=1`, an independent exact derivative of the moving basis including `a^-1,a^-2` yields **exactly `3Gamma_z`**. See `verify_moving_crosscheck.py`. Thus the connection displayed above includes parameter changes and basis motion, not merely entry-wise derivatives of frozen representatives.

The actual remaining **source-serving integration question in this new chart** is explicit: seek rational two-vectors `J_0,J_1,J_2∈Q(z0,z1,z2)^2` such that

\[
\boxed{\sum_{j=0}^2(\partial_{z_j}+\Gamma_j)J_j=
\frac{z_0^2z_1^2z_2}{4}\begin{pmatrix}C(z)\\\lambda(z)\end{pmatrix}.}\tag{BASE}
\]

The exact rational inverses above specify every coefficient of `(BASE)` and supply a **finite, reproducible, geometrically motivated** global rational integration route. If one constructs rational solutions, the rational relative homotopies (also reconstructed from the matrices) can be inserted to produce a full meromorphic five-form primitive on the dense chart. This would then have to be pulled back, descended/homogenized, checked for legal complex-coprime denominator, and tested in the **literal original six-coordinate identity**. **No rational solution of `(BASE)` was found or claimed here.** This base-only current is a sufficient *restricted* route; horizontal poles along moving divisors in the elliptic fibers may be necessary for an unrestricted original certificate.

## 5. NEW exact cubic source-character filtration (independent check on the geometric shape)

For a diagnostic auxiliary deformation only, set `A_i=1+z_i^6`, `B_i=z_i z_(i+1)/2` and temporarily replace `G` with `G_epsilon=Σ A_i t_i³+epsilon Σ B_i t_i²t_(i+1)`. The actual input is `epsilon=1`; **no deformation is substituted into the acceptance target**. Ordinary monomial Griffiths reduction on the Fermat fiber gives an exact **selection rule**: the compact relative class of `P/G_epsilon³` has zero Taylor coefficients for `epsilon^0,epsilon^1,epsilon^2`. The first possible terms are **at order epsilon³**, and both basis coefficients are explicitly

\[
\begin{aligned}
[C]_{\epsilon^3}&=-\frac4{243}\left(
\frac{B_1^2B_2}{A_0 A_1^2 A_2^2}+
\frac{B_0 B_2^2}{A_0^2 A_1 A_2^2}+
\frac{B_0^2B_1}{A_0^2 A_1^2 A_2}\right),\\
[\lambda]_{\epsilon^3}&=-\frac{10}{81}\left(
\frac{B_1B_2^2}{A_0 A_1 A_2^2}+
\frac{B_0B_1^2}{A_0 A_1^2 A_2}+
\frac{B_0^2 B_2}{A_0^2 A_1 A_2}
\right).
\end{aligned}
\]

These are exact characteristic-zero rationals from all six cubic terms, not a numerical Taylor fit. The independent cyclic exact inverse below reproduces the aggregate leading coefficients `-4/81` and `-10/27` at all `Ai=Bi=1`. See `verify_character_leading.py`. This character selection is a way to constrain a source-serving answer, **not** a formal-series certificate and not a replacement for the actual `epsilon=1` remainder.

## 6. A further *failed* exact-integration attempt (different auxiliary direction; scope explicit)

We also pursued the cyclic plane-cubic deformation `G_h=Σ ti³+hΣ ti²ti+1`, a **one-dimensional auxiliary coefficient family**, to test whether an especially simple rational elliptic integration strategy could bypass `(BASE)`. The same independent finite inverse gives the complete **unscaled** compact source

\[
C_h=-\frac{2h^3(h^3+6)}{9(h^3+1)(h^3+3)(h^3+9)},\qquad
\lambda_h=-\frac{2h^3(h^3+5)}{(h^3+1)(h^3+3)(h^3+9)},
\]

and the moving connection

\[
\Gamma_h=\begin{pmatrix}
-\frac{h^2}{h^3+3}&\frac{2h^2(h^3-9)}{3(h^3+1)(h^3+3)(h^3+9)}\\
-\frac{6h^2}{h^3+3}&-\frac{2h^2(h^6+4h^3+27)}{(h^3+1)(h^3+3)(h^3+9)}
\end{pmatrix}.
\]

**We exactly tested the scalar auxiliary antiderivative equation `J'(h)+Gamma_h J(h)=(C_h,lambda_h)` for arbitrary rational `J∈C(h)^2`**. Its forced `mu_3`-character component is `J=h^4 f(x)`, `x=h³`, and the full rational equation is `3x f'+(4I+x Gamma_tilde(x))f=v_tilde(x)` where `Gamma_h=h² Gamma_tilde(h³)`, `v_h=h³ v_tilde(h³)`. Poles are only possible at `x=-3` and of order at most one: the normalized homogeneous residues at `x=0,-1,-3,-9` have eigenvalue sets `{4/3}`, `{0,-1}`, `{0,1}`, `{0,-1}`; at infinity positive exponents prohibit a polynomial part. Hence the only candidate is `f=(a,b)/(x+3)`. The exact numerator equations force `b=-6a`, then `36a+1=0`, but then the first numerator's constant term equals **1** instead of 0. Thus there is **no rational solution for this auxiliary one-dimensional antiderivative**. All calculations and the complete pole proof are independently reconstructible in `verify_cyclic_auxiliary.py`.

**Crucial scope limitation:** This is a different one-dimensional coefficient deformation, not a necessary restriction of the original 3-base unknown current; the original top base form even pulls back to zero on a diagonal one-dimensional slice. Its failure must **not** be extrapolated into nonexistence of `(BASE)` or the original certificate. It does, however, prove that one tempting shortcut in the new elliptic integration strategy cannot work.

## 7. Exact unresolved task and saved non-repetition state

**Unresolved:** construct a genuinely global rational base or mixed horizontal elliptic current that eliminates the exact two-channel source while permitting the necessary legal horizontal pole divisor, and then transport and verify the immutable six-coordinate identity. Neither `(BASE)` nor a more general punctured-fiber integration was solved. The fact that the compact source is nonzero at one fiber is not an unrestricted obstruction. The new rational relative current is not the accepted certificate.

**What is new and should not be repeated:** the pair-sign quotient with original 1/4 Jacobian and zeta6² character; the 28×28 and 10×10 generic rational inverses and exact determinants; the full literal affine source decomposition including both pole orders; the three independently moving rank-two connection matrices and cyclic consistency check; the cubic monomial-character leading coefficients; and the scoped, fully solved negative test for the auxiliary cyclic h-antiderivative. The user-supplied target and saved attempts70–79 remain the comparison; do not redo their old Euler-only/one-weight/Sylvester or restricted one-direction obstructions as though they solved this target.

**Executed:** five Python/SymPy exact verifiers (no float fitting or finite-field inference). All passed. The complete report, scripts, exact JSON reconstruction witnesses and SHA-256 manifest are in this packet. The original full `E=F³Q` checker was **not** executed on a new physical candidate because there is no completed tuple; saying otherwise would be false. No Lean run, messages, external publication, repository change, or new scheduled task.
