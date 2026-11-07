# Cycle-q2 attempt 73 — generic-parameter Euler rationality obstruction by a 48-column pole-complete witness

**Date 2026-11-03. Original certificate remains OPEN.** No admissible homogeneous `(D,N0,...,N5,Q)` with `E=F^3 Q`, no closed Lean existence proof. This is a *new generic-parameter strengthening of the preceding attempt 72 one-orbit theorem*, not a polynomial certificate, a general nonexistence theorem, or a proof of the source's nonintegrability with all transverse directions.

## Exact target and provenance

Physical coordinates `(X0,X1,X2,Y0,Y1,Y2)` and unchanged

\[
F=\sum_{i=0}^2(X_i^6+Y_i^6)+\tfrac12(X_0^3X_1Y_0Y_1+X_1^3X_2Y_1Y_2+X_2^3X_0Y_2Y_0),
\quad A=X_0^2X_1^2X_2^3Y_0^2Y_1^2Y_2,\quad q=2.
\]

The **only accepted certificate** has `D` homogeneous nonzero, `gcd_C(D,F)=1`, `N_i` homogeneous degree `deg(D)+7`, and unrestricted polynomial `Q` such that

\[
\boxed{AD^2-2D\sum_iN_i\partial_iF+F(D\sum_i\partial_iN_i-\sum_iN_i\partial_iD)=F^3Q.}
\]

Public primary sources inspected anew: `https://raw.githubusercontent.com/hodge-computer/sextics/main/data/cycle-q2/instance.rec`, `why.md`, `formal/README.md`, `formal/lean/HodgeComputer/Constructions/HigherResidues/README.md`, `formal/lean/HodgeComputer/Constructions/TransitiveCubic/README.md`. The physical diagonal weights `(2,1,0,3,2,1)` give `wt A=17`, `wt volume=9`, residue character `zeta6^2`: no invariant averaging. Attempts 64–71 remain research inputs, not a completed original certificate. **Prior attempt 72**, saved separately in `/Math/cycle_q2_attempt72.zip`, had already proved via an exact 97-by-65 linear system and rational dual that the same Euler source is not rationally integrable on the single orbit `v=Z=b=1`. That exact one-orbit fact is not claimed as new here. **The new result is a genuine generic-parameter theorem** using a sharper 48-term pole-complete model and an algebraic positive minor that is nonzero over `C(v,Z,b)`. The physical-to-cubic source binding below was previously checked in archived attempt 69; it was reviewed here, but its unchanged physical Jacobian computation was not rerun. The **displayed source formula and all the new algebra were independently recomputed**.

## The actual source and the new one-parameter curve

Use the source-bound cubic chart with coordinates `(P,U,Z,b,a)`:

\[
L=P^6+U^2,\quad M=PU^2b/2,\quad N=PUZ/2,
\quad K=(U^4+U^2)b^3+U(1+Z^6)+ZU^2b^2/2,\quad G=La^3+Ma^2+Na+K.
\]

The original second-normal source, with all normal derivatives, is

\[
\rho=\tfrac12\left(G_a^{-1}\partial_a\right)^2\left(\frac{b^2h_2 a^2}{G_a}\right)
=\frac{b^2h_2}{G_a^5}\bigl(N^2-15LNa^2-12LMa^3-2M^2a^2-2MNa\bigr),\qquad h_2=P^2 ZU^4/24.
\]

This is the previously source-bound `rho = -Rcal`, not an altered numerator. `verify_source_change.py` checks the new rescaling coefficientwise. The previously audited physical source binding includes the finite monomial coordinate map, its determinant 24, original character, normal orientation, projective Euler factor 2, and regular remainder; this attempt **does not assert a new global physical reconstruction**.

For the global rationality question left open by attempt 71, consider the **precise Euler-only ansatz**

\[
J_P=P\Phi,\quad J_U=3U\Phi,\quad J_Z=J_b=0,\qquad
(4+P\delta_P+3U\delta_U)\Phi=\rho,
\]

where `delta_j=partial_j-(G_j/G_a)partial_a` includes the moving cubic root. The formal `b`-adic coefficient recurrence of attempt 71 does not prove this PDE has a rational solution.

Set `s=P`, `v=U/P^3`, `alpha=P*a`, with `Z,b` independent. Then `G=s^3 H` where

\[
\boxed{H=(1+v^2)\alpha^3+\frac{vZ}{2}\alpha+v(1+Z^6)
+\frac{s^2v^2b}{2}\alpha^2
+s^3v^2(b^3+Zb^2/2)+s^9v^4b^3.}
\]

Put `C=1+v^2`, `T=H_alpha`, and

\[
\begin{aligned}
K_0&=v^2Z^2/4-(15/2)CvZ\alpha^2,\\
K_2&=-6Cv^2b\alpha^3-(v^3bZ/2)\alpha,\\
K_4&=-v^4b^2\alpha^2/2,\qquad K_*=K_0+s^2K_2+s^4K_4.
\end{aligned}
\]

**Exact identity:** `rho=s² b² Z v^4 K_* / (24 T^5)`. The original Euler-only PDE is **equivalent** to rational exactness on the generic cubic curve `H(s,alpha)=0` of

\[
\boxed{\omega=s^3\rho\,ds=\frac{s^5 b^2 Z v^4 K_*}{24 T^5}\,ds.}
\]

Indeed `delta_S=s delta_s` at fixed `v,Z,b` and `d(s^4 Phi)/ds=s^3 rho`. The moving derivative `delta_s=partial_s-(H_s/H_alpha)partial_alpha` is retained, not replaced by partial differentiation at fixed alpha.

## NEW theorem: generic Euler-only primitive nonexistence, upgrading attempt 72's one-orbit result

**Theorem (new generic extension of attempt 72).** Let `k=C(v,Z,b)` and `L=k(s)[alpha]/(H)`, with derivation `delta_s`. Then `omega` above has **no primitive in L**, and none in any finite algebraic extension of L. Hence no rational `Phi` solves the Euler-only PDE, even though its formal `b`-adic recursion can be solved to every finite order. Attempt 72 established only the one-orbit instance by a different exact rational dual. The determinant here is nonzero as a rational function of all three independent parameters, so this theorem is genuinely generic. It does **not** exclude currents with a nonzero `v`, `Z`, or `b` component and therefore does not decide original cycle-q2 existence.

### Pole completeness (not an ansatz degree cutoff)

The cubic `H` is irreducible over `k(s)`: a rational alpha root would be integral over `k[s]` and hence polynomial of degree 3 in s. Its leading coefficient would have cube equal to `-v^4 b^3/(1+v²)`, which is not a cube in `k` (e.g. order one at v=i). The generic cubic discriminant in alpha has degree 18 and is squarefree: at `(v,Z,b)=(1,1,1)` the exact polynomial is

\[
-16\operatorname{disc}_\alpha(H)=1728s^{18}+8s^{15}+5184s^{12}-144s^{11}+6924s^9+3904s^6-216s^5-s^4+10368s^3-288s^2+6928,
\]

whose gcd with its derivative is 1 over Q. The covering `s` has 18 simple finite ramification points and three unramified points at infinity, and the smooth generic curve has genus 7.

`omega` is regular away from the 18 finite ramification points. At each such point, `T=H_alpha` has a simple zero and `ds` a simple zero, so `omega` has pole order <=4. At all three infinity points `alpha~kappa s³`, `T~s^6`, `K_* =O(s^11)`, hence `omega=O(s^-14) ds` and is regular. Any rational primitive `R` is thus regular outside the ramification points and has poles of order at most 3 at them. Therefore `T³ R` is regular on the affine curve, hence belongs to `k[s,alpha]/(H)`. The infinity growth bound on `T³ R` is `s^18`; independence of the three leading cube roots at infinity implies the **complete exact representation**

\[
\boxed{R=\frac{B_0(s)+B_1(s)\alpha+B_2(s)\alpha^2}{T^3},\quad
\deg B_0\le18,\quad\deg B_1\le15,\quad\deg B_2\le12.}
\]

There are exactly 48 coefficients. This is **derived from the actual pole divisor and valuations**, not an arbitrary denominator search.

### Exact linear equation and positive characteristic-zero rank obstruction

Let `B` denote the numerator. With full implicit differentiation,

\[
\delta_s(B/T^3)=\frac{T^2 B_s-T H_s B_\alpha-3B T H_{s\alpha}+3B H_sH_{\alpha\alpha}}{T^5}.
\]

Thus the full rational primitive problem is equivalent to the coefficientwise polynomial identity **modulo the original cubic H**:

\[
\boxed{T^2 B_s-T H_s B_\alpha-3B T H_{s\alpha}+3B H_sH_{\alpha\alpha}
=\frac{s^5 b^2 Z v^4}{24}K_*\pmod H.}
\]

This has 48 unknown coefficients. There is a **universal exact nonzero kernel vector** `B=T³` (the constant primitive), hence the coefficient matrix `M` has rank at most 47 **over characteristic zero**, for every parameter set. No other kernel assumption is needed.

`verify_sparse_rank.py` reconstructs **all 78 coefficient rows** at the single exact rational parameter fiber `v=Z=b=1` and gives a 48x48 augmented minor, using all columns except the coefficient of `s^8 alpha²` and including the source column. At the good prime 101 its determinant is

\[
\boxed{\det=32\pmod{101}\ne0.}
\]

The row indices, monomial coordinates, exact source terms, and column indices are saved in `DET_WITNESS_101.json`. Independent reconstruction using SymPy polynomial division in `GF(101)(s)[alpha]` reproduces **32**. Identical selected minors yield determinants **19 mod103, 8 mod107, 14 mod109**, verified by exact modular polynomial arithmetic. This is a *positive determinant witness*: nonzero reduction of an explicitly reconstructed rational determinant proves it is nonzero over characteristic zero for generic parameters. It is NOT an inference from finite-field failure.

Thus `rank_k M <=47` but `rank_k [M|RHS] >=48`. Contradiction. The source is nonintegrable in the single Euler direction over C(v,Z,b). Any finite algebraic extension cannot help: trace of a hypothetical primitive commutes with the extended derivation in characteristic zero and would descend a primitive to L.

## Consequences and limitations

The formal coefficientwise `b`-adic current reported in attempt 71 can be mathematically consistent **without** coming from a rational function; this theorem proves that, for the exact global Euler-only ansatz, it does **not** rationalize. A successful cubic current must include at least one additional independent direction: the transverse ratio `v=U/P³`, `Z`, or `b`, with all moving-coordinate and regular-density corrections retained. In `(s,v)`, the two-coordinate density is `dP wedge dU=s³ ds wedge dv`, so the full P/U divergence is `s^-3[delta_s(s³ J_s)+delta_v(s³ J_v)]` in the appropriately transported current. Allowing nonzero `J_v` is exactly the first excluded-free extension.

There is NO six-variable `(D,N,Q)` candidate in this attempt, no final `E=F³Q` check to claim, no denominator legality conclusion for the physical target, and no Lean existence proof. The private Math-project checkout/Lean were not present. This is a rigorous new restricted theorem that closes the *global rationality question of one specific attempted integration*, not the overall project.

Earlier orbit result distinguished explicitly; no unchanged 97-by-65 rank rerun was made. No repository edits, external messages, publications, or scheduled jobs were created.
