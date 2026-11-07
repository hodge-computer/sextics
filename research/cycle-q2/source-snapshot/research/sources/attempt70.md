# Cycle-q2 — fresh attempt 70: source-specific three-jet transverse integration and special-fiber character filtration

**Date:** 2026-11-03. **Verdict: ORIGINAL CERTIFICATE OPEN.** A new exact partial rational primitive is reconstructed in a formal neighborhood of `b=0`, through the `b^4` source coefficient, including the **moving `b`-connection derivative**. The leading three compact source coefficients occupy the `mu_3` character `omega`; the next two occupy the trivial character; the fifth-order-free third jet has two trivial and three `omega^2` coefficients. By order `b^4`, all eight compact basis *positions* are activated. This is **not** an all-order rational primitive and **not** an original homogeneous six-coordinate certificate.

## 1. Protected target and provenance

In the ordered physical coordinates `(X0,X1,X2,Y0,Y1,Y2)`, keep

\[
F=\sum_{i=0}^2(X_i^6+Y_i^6)+\frac12(X_0^3X_1Y_0Y_1+X_1^3X_2Y_1Y_2+X_2^3X_0Y_2Y_0),\quad
A=X_0^2X_1^2X_2^3Y_0^2Y_1^2Y_2,\quad q=2.
\]

The only accepted existence statement requests `D != 0` homogeneous, `gcd_C(D,F)=1`, six `N_i` homogeneous of degree `deg(D)+7`, and unrestricted polynomial `Q` with the **complete** identity

\[
\boxed{A D^2-2D\sum_iN_i F_i+F\left(D\sum_i\partial_iN_i-\sum_iN_i\partial_iD\right)=F^3Q.}\tag{ORIGINAL}
\]

Primary records fetched again:

- `https://raw.githubusercontent.com/hodge-computer/sextics/main/data/cycle-q2/instance.rec`
- `https://raw.githubusercontent.com/hodge-computer/sextics/main/data/cycle-q2/why.md`
- `https://raw.githubusercontent.com/hodge-computer/sextics/main/formal/README.md`

The original diagonal weight tuple `(2,1,0,3,2,1)` gives numerator weight 17, volume weight 9, residue character `zeta6^2`. No invariant averaging, altered numerator, or reduced q is used. The physical-to-cubic source binding was **established in the prior saved attempt69**; it was *read* in this run but not re-executed as an unchanged verification job. Its specific assertion is `rho=-Rcal`, with the projective factor 2 and sign specified in that report. All **new** claims in this packet are exact statements about that explicitly displayed original-source cubic residue. The full physical-to-cubic binding was not independently re-derived anew here. Attempt68's denominator exclusions and earlier reports were not used as mathematical premises.

## 2. Source over the moving cubic field

On the prior source-bound monomial chart use base coordinates `(P,U,Z,b)` and cubic root `theta`:

\[
L=P^6+U^2,\quad M=PU^2b/2,\quad N=PUZ/2,\quad
K=(U^4+U^2)b^3+U(1+Z^6)+ZU^2b^2/2,
\]
\[
p=N/L-M^2/(3L^2),\quad q_c=K/L-MN/(3L^2)+2M^3/(27L^3),
\quad\theta^3+p\theta+q_c=0,\quad \Delta=4p^3+27q_c^2.
\]

The **actual inherited source** in the two-dimensional trace-zero root frame is

\[
\boxed{\mathcal R=c(m_p\nabla_p k_2+m_q\nabla_{q_c}k_2),}
\quad
c=\frac{M^2N}{6PUL^2},\quad m_p=-\frac{2M}{3L^2},\quad m_q=-\frac{N}{3L^2}+\frac{2M^2}{9L^3}.
\]

Here `k2=(6(2p^3-27q_c^2),162p q_c)^T/Delta^2`; its *covariant* derivatives are `Kp/Delta^3,Kq/Delta^3`, where

\[
K_p=\binom{-12p^2(10p^3-297q_c^2)}{-108q_c(23p^3-27q_c^2)},\quad
K_q=\binom{-54q_c(34p^3-135q_c^2)}{18p(32p^3-513q_c^2)}.
\]

These derivatives were **independently and symbolically verified** this run from the full `2x2` moving-root matrices `B_p,B_q`. The source begins at `b^2`, not at `b^0`:

\[
p_0=\frac{PUZ}{2L},\ q_0=\frac{U(1+Z^6)}L,\quad
p_1=0,\ q_1=-\frac{P^2U^3Z}{12L^2}.
\]

Set `S(b)= (c/b^2)(m_p K_p+m_q K_q)`, so `Rcal=b^2 S(b)/Delta(b)^3`. Its first two **polynomial numerator** coefficients, verified identically over `Q(P,U,Z)` in `verify_source_jet.py`, are

\[
\boxed{S_0=-\frac{P^3U^5Z^2}{288L^4}K_q(p_0,q_0),}
\]
\[
\boxed{S_1=-\frac{P^3U^6Z}{144L^4}K_p(p_0,q_0)
+\frac{P^5U^8Z^3}{3456L^6}\partial_{q_c}K_q(p_0,q_0).}
\]

The coefficient `S_2` is computed by *exact* second differentiation of the same original-source `S(b)`, not an independently chosen target. The omitted term that affected attempts53/54 is irrelevant: their reconstructed scalar `g` is never used.

## 3. New special-fiber symmetry, with source character retained

At `b=0` the cubic becomes

\[
\theta^3+\frac{PU}{2L}Z\theta+\frac UL(1+Z^6)=0.
\]

For a primitive cube root `omega`, its automorphism `sigma:(Z,theta) -> (omega^2 Z,omega theta)` preserves this equation. The eight *compact* differentials inherited from attempt69 are

\[
\omega_{j,i}=\frac{Z^i\theta^j}{3\theta^2+p}\,dZ,\qquad
(j,i)=(0,0),(0,1),(0,2),(0,4),(1,0),(1,2),(1,3),(1,4).
\]

Direct substitution gives `sigma^* omega_{j,i} = omega^(2i+j) omega_{j,i}`. Thus the eight-dimensional compact fiber splits into eigenspaces of dimensions `(2,3,3)` for characters `(1,omega,omega^2)`.

The actual leading `b^2` source differential is in the **omega** eigenspace (it includes `Z^2 ∇_q k2 dZ`), so only basis positions `(0,2),(1,0),(1,3)` can occur in its compact class. Exact reconstruction confirms **all three coefficients are nonzero generically**, via their nonzero rational specialization at `(P,U)=(1,1)`.

The `b^3` coefficient is in the **trivial** eigenspace. Exactly `(0,0),(1,4)` occur, both nonzero at `(1,1)`. This is not automatic from the leading term: it uses the moving deformation `q_1=-P^2U^3Z/(12L^2)` and the full product rule. At `b^4`, the terms from `q_1^2`, `p_2`, and `m_{q,2}` have character `omega^2`, while the `q_2 ∝ Z` contribution has trivial character; no `omega` component is permitted by these exact transformation weights. The `b^4` coefficient has **two trivial and three omega^2 positions**. Across orders `b^2,b^3,b^4` every one of the eight basis positions occurs (this is a union-of-support statement, NOT a claim that three vectors span an eight-dimensional space).

## 4. Exact rational reconstruction and the three-jet transverse current

Write `Omega` for the 2-component column of eight compact basis coefficients `omega_{j,i}/dZ`. The inherited exact relative reduction is

\[
\mathcal R=\nabla_Z(W/\Delta^2)+\Omega\,r,\quad
W=(W_0,W_1)^T,\quad \deg_Z W_i\le23,\quad r\in\mathbb Q(P,U,b)^8.
\]

Its 70-by-56 coefficient matrix `A(b)` is constructed explicitly in `verify_b_adic.py` and `extend_b4.py`, with 48 columns for `W` and 8 for `r`. Set `A_n=[b^n]A`, `S_n=[b^n]S` and use the fixed selected 56-row submatrix. `A_0` has a nonzero 56x56 determinant: at `(P,U)=(1,1)` the rational matrix's good reductions are `54 mod101`, `85 mod103`, `353 mod1009`. In particular the same selected minor is invertible over `Q(P,U)`.

The **exact reconstruction formulas** are

\[
A_0y_0=S_0,\qquad
A_0y_1+A_1y_0=S_1,\qquad
A_0y_2+A_1y_1+A_2y_0=S_2.
\]

All 70 coefficient rows, not just the 56 pivot rows, were checked over exact rationals at each saved specialization. Geometric compatibility over the generic coefficient field follows from the zero-residue Hermite reduction of the preceding source-bound compact model; this generic reduction was not independently reconstructed from scratch this run. The rational finite-inverse formulas define `W_0,W_1,W_2` and `r_2,r_3,r_4` over `Q(P,U)`.

For moving `b` one must also retain

\[
\nabla_b\Omega=\nabla_Z H_b+\Omega\Gamma_b,\qquad
\Gamma_b=\Gamma_0+b\Gamma_1+O(b^2).
\]

The first two connection coefficients were reconstructed from **all 70 rows of the original moving-derivative identities**, differentiating both the frame and the reduction matrix. Define the transverse compact coefficients

\[
\boxed{
 u_3=\frac{r_2}{3},\quad
 u_4=\frac{r_3-\Gamma_0u_3}{4},\quad
 u_5=\frac{r_4-\Gamma_0u_4-\Gamma_1u_3}{5}.
}
\]

Put `u(b)=b^3 u_3+b^4 u_4+b^5 u_5`. Then, over the **generic** field `Q(P,U)` as a formal series, the exact coefficient identities give

\[
\boxed{(\partial_b+\Gamma_b)u(b)=b^2r_2+b^3r_3+b^4r_4+O(b^5).}
\]

An explicit two-direction **partial current** is therefore

\[
J_Z=\frac{b^2(W^{[0]}+bW^{[1]}+b^2W^{[2]})}{\Delta(b)^2}
-\sum_\ell u_\ell(b)H_{b,\ell}(b),\qquad
J_b=\sum_\ell u_\ell(b)\frac{\omega_\ell(b)}{dZ}.
\]

Its full covariant divergence satisfies

\[
\boxed{\nabla_ZJ_Z+\nabla_bJ_b=\mathcal R+O(b^5),}
\]

where **all `b`-dependent root-frame derivatives and the regular relative remainder** are kept. There are no `P` or `U` current components in this partial construction, though their values remain arbitrary rational parameters. This is an identity in the completed coefficient field near `b=0`, **not** a global rational identity in `b`.

## 5. Characteristic-zero coefficient witnesses (not a finite-field existence claim)

In basis order `(0,0),(0,1),(0,2),(0,4),(1,0),(1,2),(1,3),(1,4)`, at `(P,U)=(1,1)`:

\[
r_2=(0,0,6193240/36691107843,0,2304/12230369281,0,4866076/36691107843,0)^T.
\]

\[
r_3=(-410520704/1352568769155071,0,0,0,0,0,0,40769261568/1352568769155071)^T.
\]

The five nonzero components of `r_4`, in positions `0,1,3,5,7`, are exactly

\[
\left(
\frac{3397438464}{1352568769155071},
-\frac{86604615863894312}{1346237394746656112649},
-\frac{400790390882816}{149581932749628456961},
-\frac{159627991864909832}{4038712184239968337947},
-\frac{305773608963}{1352568769155071}
\right).
\]

At that fiber the computed transverse `b^3` coefficients have support `2,4,6`, `b^4` coefficients support `0,7`, and `b^5` coefficients support `0,1,3,5,7`. The full 8-component rational vectors, all 8x8 connection matrices, root-frame primitive coefficients, coefficient-polynomials of `W` (degrees `21,22`; `22,23`; `23,23`), exact matrix row indices, and copies for `(2,1)` and `(1,2)` are in `B_ADIC_WITNESSES.json` and `B4_EXTENSION.json`.

These are actual exact `Q`-coefficient solutions to the stated finite coefficient identities, checked in all 70 rows. The modular determinants only certify **nonzero rational determinants**; no nonexistence statement is inferred from a modular inconsistency.

## 6. What was established and what remains

**Genuinely new here:** the special-fiber character decomposition of the **actual source**; exact reconstruction of its first three nonzero compact Taylor coefficients; the two *moving* `b`-connection coefficients; and an explicit rationally reconstructible transverse `b`-current integrating the actual cubic source through order `b^4`. The fact that all eight basis positions are activated by these three orders is useful for choosing a full multi-direction ansatz. An all-order formal `b`-adic solution with zero initial condition also exists recursively because the Gauss-Manin coefficients are regular at `b=0` generically; **formal power series exactness does not imply a rational primitive**.

**Absolutely not established:** a rational full-`b` compact solution, other needed parameter directions, globally regular source transport, a physical homogeneous denominator, complex coprimality, six original numerator polynomials, a polynomial remainder `Q`, exact `E=F^3Q`, or a closed Lean existence proof. There is no completed tuple to test against the full original polynomial identity; this partial current must not be presented as such. Lean and a private Math-project checkout were not available/used.

The exact next step is **rational reconstruction of the full transverse compact equation**, ideally using the identified character filtration to constrain its pole divisor, and then full physical transport and literal original-identity verification. Do not redo old excluded diagonal/degree-six profiles, the attempt69 Z-only reduction, or present this b-adic Taylor jet as a global certificate. No external messages, publications, repository modifications or new scheduled tasks were made.
