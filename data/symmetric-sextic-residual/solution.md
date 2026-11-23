# Moving lines on a cubic threefold and global residue cancellation on an \(S_3 \times S_3\) quotient

This proof establishes `HodgeComputer.HasCertificate HodgeSubmission.F HodgeSubmission.q HodgeSubmission.A` for the protected instance `symmetric-sextic-residual`,
\[
F = \sum_{i=0}^{2}(X_i^6 + Y_i^6) + \frac{5}{7} Q_X^2 Q_Y + \frac{10}{7} Q_X Q_Y^2,
\qquad
A = X_0 X_1 X_2 Y_0 Y_1 Y_2,
\qquad
q = 1,
\]
where \(Q_X = X_0 X_1 + X_0 X_2 + X_1 X_2\) and \(Q_Y = Y_0 Y_1 + Y_0 Y_2 + Y_1 Y_2\).

Rather than exhibiting a giant cleared polynomial tuple directly, the proof descends the first-order residue-divergence equation on \(X = \{F = 0\}\) to an \(S_3 \times S_3\)-invariant quotient hypersurface \(F_5 = 0\), eliminates the vertical part of the source by an explicit \(7\)-term Poisson identity, and cancels the remaining horizontal obstruction by summing \(34\) moving-line sheets on an auxiliary cubic threefold \(H_{\mathrm{cub}} = 0\) over a finite splitting field via the global residue theorem on \(\mathbb{P}^1_U\) and normalized-trace descent.

## 1. Quotient reduction and ambient Piola pullback

Set the elementary symmetric polynomials \(e_{1,X} = \sum X_i\), \(Q_X = \sum_{i<j} X_i X_j\), \(e_{3,X} = X_0 X_1 X_2\) (and analogously \(e_{1,Y}, Q_Y, e_{3,Y}\)), together with the Vandermonde discriminants \(\Delta_X = \prod_{i<j}(X_i - X_j)\) and \(\Delta_Y = \prod_{i<j}(Y_i - Y_j)\). As explained in [why.md](why.md), transpositions in either block fix \(A\) while negating the residue volume, so the invariant ansatz carries the sign-character weight \(W^{-1}\), where \(W\) is proportional to \(\Delta_X \Delta_Y\).

De-homogenizing by \(Q_Y\), introduce the six ambient rational coordinates \((Q_Y, S, Q, T, x, y)\) defined by
\[
S = \frac{e_{1,X}^2}{Q_Y}, \qquad
Q = \frac{Q_X}{Q_Y}, \qquad
T = \frac{e_{1,Y}^2}{Q_Y}, \qquad
x = \frac{e_{1,X}^3 - 2 e_{1,X} Q_X + e_{3,X}}{e_{1,X} Q_Y}, \qquad
y = \frac{e_{1,Y}^3 - 2 e_{1,Y} Q_Y + e_{3,Y}}{e_{1,Y} Q_Y}.
\]
In these coordinates, \(F = Q_Y^3 F_5(S, Q, T, x, y)\) where
\[
F_5(S, Q, T, x, y) = 3 S x^2 + 3 T y^2 + H_0(S, Q, T),
\]
\[
H_0(S, Q, T) = -2 S^3 + 6 S^2 Q - 3 S Q^2 - 2 Q^3 - 2 T^3 + 6 T^2 - 3 T - 2 + \frac{5}{7} Q^2 + \frac{10}{7} Q.
\]
The discriminant factor squares to the polynomial \(W_2(S, Q, T, x, y) = S T \Delta_X^2(S, Q, x) \Delta_Y^2(T, y)\), and the monomial target pulls back to \(M_A(S, Q, T, x, y) = S T (x - S + 2 Q)(y - T + 2)\).

Let \(K_4 = \operatorname{Frac}(\mathbb{C}[S, Q, T, y])\) and let \(K_5 = K_4[x] / (F_5)\) be the quadratic function field of the quotient hypersurface \(F_5 = 0\), with tangent derivations \(\delta_0, \delta_1, \delta_2, \delta_3\) along \((S, Q, T, y)\) constrained to \(F_5 = 0\). Define the weighted residue divergence
\[
\operatorname{resDiv}_W(w) = \sum_{i=0}^{3} \left( \delta_i w_i - w_i \frac{\delta_i F_x}{F_x} - w_i \frac{\delta_i W_2}{2 W_2} \right),
\qquad F_x = 6 S x.
\]
Using the \(6 \times 6\) ambient Piola identity ([PiolaContraction.lean](../../formal/lean/HodgeComputer/Constructions/ResidueTransport/PiolaContraction.lean)), [SymmetricPiola.lean](SymmetricPiola.lean) (`certificate_of_K5_pde`) proves that any solution \(w \in K_5^4\) of
\[
\operatorname{src}_X + \operatorname{resDiv}_W(w) = 0
\]
pulls back to a legal ambient rational vector field whose cleared numerator, denominator, and quotient satisfy `HodgeComputer.Verify` (assembled via [Explicit.lean](../../formal/lean/HodgeComputer/Constructions/Explicit.lean)), yielding `HasCertificate`.

Furthermore, [K5Field.lean](K5Field.lean) (`radial_normal_chart_identity`) establishes the radial normal-chart identity
\[
2 \operatorname{src}_X - \operatorname{resDiv}_W\!\left(0, 0, 0, \frac{y M_A}{H_0}\right) + \frac{N_{A,Q}}{2 W_2 H_0} = 0,
\]
where \(N_{A,Q} = 2 W_2 E_{\mathrm{rad}}(M_A) - M_A E_{\mathrm{rad}}(W_2)\) and \(E_{\mathrm{rad}} = x \partial_x + y \partial_y\). Thus it suffices to solve
\[
2 W_2 H_0^2 \operatorname{resDiv}_W(w_{\mathrm{tot}}) = N_{A,Q} H_0
\]
in \(K_5\) (or, by normalized-trace descent, over any finite extension \(L / K_5\)).

## 2. Seven-term vertical identity

An explicit \(4\)-component rational vector field \(w_V \in K_5^4\) built from seven bivariate polynomials \(u_0, \dots, u_6 \in \mathbb{Q}[S, Q, T, x, y]\) (stored in [VerticalData.lean](VerticalData.lean)) eliminates the vertical component of \(N_{A,Q} H_0\) up to a single residual horizontal polynomial \(P_{\mathrm{horiz}} \in \mathbb{Q}[S, Q, T, x, y]\):
\[
2 W_2 H_0^2 \operatorname{resDiv}_W(w_V) + P_{\mathrm{horiz}} = N_{A,Q} H_0 \qquad \text{in } K_5.
\]
Each term in \(w_V\) is a Poisson bracket on \(F_5 = 0\) with denominator \(H_0\) or \(H_0^2\). In [VerticalIdentity.lean](VerticalIdentity.lean), the cleared \(5\)-variable polynomial identity `vertical_poly5_identity` is verified in the Lean kernel via sparse \((x, y)\)-bivariate encoding and \(3\)-variable \((S, Q, T)\) Kronecker substitution ([KroneckerCheck.lean](../../formal/lean/HodgeComputer/Constructions/PolynomialEncoding/KroneckerCheck.lean), built on [BivariateExpressions.lean](../../formal/lean/HodgeComputer/Constructions/PolynomialEncoding/BivariateExpressions.lean)), and then evaluated in \(K_5\) to yield `vertical_K5_identity`.

## 3. Moving-line sheets on the auxiliary cubic threefold

To cancel the remaining obstruction \(P_{\mathrm{horiz}}\), consider the weighted cubic polynomial
\[
H_{\mathrm{cub}}(S, Q, T, V_0; U, V)
\]
defined in [SheetCalculus.lean](SheetCalculus.lean), which satisfies the two simultaneous decompositions
\[
H_{\mathrm{cub}}(S, Q, T, 1; U, V)
= U V (F_5 - G) - P_Q
= U V H_0 + u A_1 + v B_1,
\]
where \(u = (U - 1)/9\), \(v = (V - 1)/9\), \(G = u \Delta_X^2 + v \Delta_Y^2\), and \(P_Q = 3 V S L_X^2 + 3 U T L_Y^2\) is a sum of two squares linear in \(x\) and \(y\).

At fixed \((U, V)\), the locus \(H_{\mathrm{cub}}(S, Q, T, 1; U, V) = 0\) is a cubic surface in \((S, Q, T)\). A line \((\xi_S + a t, \xi_Q + b t, t)\) through \((S, Q, T)\) lies on this cubic surface precisely when the four polarization equations \(E_0 = E_1 = E_2 = E_3 = 0\) hold in \((a, b, U, V)\). Over any finite extension \(L / K_5\), [SheetCalculus.lean](SheetCalculus.lean) (`sheet_horiz_identity`) constructs an explicit moving-sheet vector field \(w_{\mathrm{horiz}}(a, b, U, V) \in L^4\) by contracting three \(1\)-forms supported on the moving line and proves that for every nondegenerate sheet (with \(U, V \notin \{0, 1\}\), \(\det J_{\mathrm{fib}} \ne 0\), and \(\det M_{abSQ} \ne 0\)),
\[
2 W_2 H_0^2 \operatorname{resDiv}_{W,L}\bigl(w_{\mathrm{horiz}}(a, b, U, V)\bigr)
= -\frac{P_{18}(S, Q, T, x, y, a, b, U, V)}{81 \det J_{\mathrm{fib}}(S, Q, T, a, b, U, V)},
\]
where \(P_{18}\) is the exact numerator assembled from the \(10\) invariant line weights (`numM`) and the \(3\)-form contractions (`QY_num`, `QX_num`, `cA1_of`, `EB_of`).

## 4. Elimination cover and rational 1-form on \(\mathbb{P}^1_U\)

On a fiber with fixed \(U\), the equation \(E_0 = 0\) is quadratic in \(W = U V\):
\[
W^2 + b_W(U) W + c_W(U) = 0.
\]
[CoverAlgebra.lean](CoverAlgebra.lean) constructs this quadratic extension \(A_C = \operatorname{RatFunc}(K_5)[W] / (W^2 + b_W(U) W + c_W(U))\) together with the exact resultant \(\operatorname{res}_z(U, W)\) eliminating \((a, b)\) from \(E_1, E_2, E_3 = 0\) and its norm \(\operatorname{nm}_z(U) = N_{A_C / \operatorname{RatFunc}(K_5)}(\operatorname{res}_z) \in K_5[U]\). Factoring \(\operatorname{nm}_z\) isolates the degree-\(34\) horizontal branch polynomial \(P_{34}(U)\) from the spurious locus \(Q_5(U)^3\) (a degree-\(5\) factor) and powers of \(U\):
\[
\operatorname{nm}_z(U) = c_{\mathrm{nm}} \, U^m \, Q_5(U)^3 \, P_{34}(U).
\]
Nonvanishing and pairwise coprimality of \(U\), \(Q_5(U)\), \(P_{34}(U)\), and the fiber discriminants are certified in [CoverAlgebra.lean](CoverAlgebra.lean) by specialization at an explicit nonsingular rational point \((S, Q, T) = (2, 1, 5)\) (`spec_nm_z`, `isCoprime_P34_Q5`, `isCoprime_P34_P34_deriv`, `isCoprime_Q5_Q5_deriv`).

In [CoverResidue.lean](CoverResidue.lean), the meromorphic differential \(\eta_{A_C} \in A_C\) is formed from the Lagrange-interpolated polynomial remainder of \(P_{18}\) modulo \(E_2\), divided by \(81 A_{v,0} Q_5(U)^3 \operatorname{res}_z (2 W + b_W(U))\), and pushed down to \(\mathbb{P}^1_U\) by trace:
\[
\eta = \operatorname{Tr}_{A_C / \operatorname{RatFunc}(K_5)}(\eta_{A_C}) \in \operatorname{RatFunc}(K_5).
\]
Passing to a finite splitting field \(\mathrm{CoverL} / K_5\) that splits \(\eta\)'s denominator, \(P_{34}\), \(Q_5\), and every fiber quadratic above the \(34\) roots \(R_{34}\) of \(P_{34}\), [CoverResidue.lean](CoverResidue.lean) proves:

- `regularAt_eta_L_of_notMem`: \(\eta_L\) has no finite poles outside \(\{0\} \cup R_{Q_5} \cup R_{34}\), where \(R_{Q_5}\) is the set of \(5\) roots of \(Q_5\).
- `residue_eta_L_at_R34` and `sum_R34_eq_sheet_div`: at every \(r \in R_{34}\), the simple-pole residue \(\operatorname{Res}_{U = r}(\eta_L)\) coincides with \(-P_{18} / (81 \det J_{\mathrm{fib}})\) on a nondegenerate sheet above \(r\), so there exists \(w_{H,L} \in \mathrm{CoverL}^4\) satisfying
\[
2 W_2 H_0^2 \operatorname{resDiv}_{W,\mathrm{CoverL}}(w_{H,L}) = \sum_{r \in R_{34}} \operatorname{Res}_{U = r}(\eta_L).
\]

## 5. Local residues at \(U = 0\), \(U = \infty\), and \(Q_5 = 0\)

The remaining poles of \(\eta_L\) on \(\mathbb{P}^1_U\) are evaluated exactly in three dedicated modules, with the exact target polynomials stored in [LocalResidueData.lean](LocalResidueData.lean) and [Q5WeightsData.lean](Q5WeightsData.lean) and denominator factor \(L_K = 77 S - 210 Q + 45\):

1. **Pole at \(U = 0\) ([LocalResidueU0.lean](LocalResidueU0.lean)):** Over `LaurentSeries K5`, the two branches of \(W^2 + b_W W + c_W = 0\) around \(U = 0\) have valuations \(v_U(W_1) = 0\) and \(v_U(W_2) = 1\). Tracking exact leading valuations and dual-number jets proves that branch \(1\) has vanishing residue (`br1_0_eta_AC_coeff_neg_one`) while branch \(2\) contributes `toK5_RU` (`br2_0_eta_AC_coeff_neg_one`), establishing
\[
\operatorname{Res}_{U = 0}(\eta) = R_U.
\]
2. **Pole at \(U = \infty\) ([LocalResidueInfAlg.lean](LocalResidueInfAlg.lean), [LocalResidueInf.lean](LocalResidueInf.lean)):** Expanding in \(t = U^{-1}\) over `LaurentSeries K5`, the two branches satisfy \(v_t(W_1) = -2\) and \(v_t(W_2) = -1\). Branch \(2\) vanishes at order \(t^1\) (`br2_inf_eta_AC_coeff_one`) while branch \(1\) evaluates to \(-R_\infty / L_K^2\) (`br1_inf_eta_AC_coeff_one`), establishing
\[
\operatorname{coeff}_\infty(\eta) = -\frac{R_\infty}{L_K^2}.
\]
3. **Spurious poles at \(Q_5(U) = 0\) ([LocalResidueQ5Alg.lean](LocalResidueQ5Alg.lean), [LocalResidueQ5Poly.lean](LocalResidueQ5Poly.lean), [LocalResidueQ5Bridge.lean](LocalResidueQ5Bridge.lean), [LocalResidueQ5Trace.lean](LocalResidueQ5Trace.lean), [LocalResidueQ5CheckA.lean](LocalResidueQ5CheckA.lean), [LocalResidueQ5CheckB.lean](LocalResidueQ5CheckB.lean), [LocalResidueQ5.lean](LocalResidueQ5.lean)):** Splitting \(\eta_{A_C}\) into its principal part at \(Q_5 = 0\) plus a remainder regular at every \(r \in R_{Q_5}\) reduces \(\sum_{r \in R_{Q_5}} \operatorname{Res}_{U = r}(\eta_L)\) to a linear combination of the \(13\) Euler power sums \(\sum_{r \in R_{Q_5}} r^k / (Q_7(r) Q_5'(r))\) (\(0 \le k \le 12\)). These power sums are certified algebraically in \(K_5\) from the exact recurrence relations of \(Q_5\) and \(Q_7\) (`Q5_Q7_recurrences_K5`, `sum_RQ5_power_eq_W_k`). The resulting polynomial identity in \((S, Q, T, x, y)\) is verified in the kernel by a factored \(2\text{D}\) Kronecker (in \(S, Q\)) \(\times\) \(1\text{D}\) centered grid (in \(T\)) check (`master_bivL_zero_K5`), proving
\[
\sum_{r \in R_{Q_5}} \operatorname{Res}_{U = r}(\eta_L) = \iota_L\!\left(\frac{R_{Q_5}}{L_K^2}\right).
\]
4. **Global residue cancellation ([LocalResidueQ5.lean](LocalResidueQ5.lean)):** An exact \(5\)-variable Kronecker check (`global_residue_cancellation`) verifies
\[
P_{\mathrm{horiz}} = -\frac{R_\infty}{L_K^2} - R_U - \frac{R_{Q_5}}{L_K^2} \qquad \text{in } K_5.
\]

## 6. Global residue theorem, descent, and certificate closure

In [Certificate.lean](Certificate.lean), the global rational residue theorem ([Residues.lean](../../formal/lean/HodgeComputer/Constructions/EllipticCompanions/Residues.lean), `CrossedRationalResidue.residue_sum_eq_infinity`) applied to \(\eta_L\) over \(\{0\} \cup R_{Q_5} \cup R_{34}\) gives
\[
\operatorname{Res}_{U = 0}(\eta_L) + \sum_{r \in R_{Q_5}} \operatorname{Res}_{U = r}(\eta_L) + \sum_{r \in R_{34}} \operatorname{Res}_{U = r}(\eta_L) = \operatorname{coeff}_\infty(\eta_L).
\]
Substituting the three local evaluations and `global_residue_cancellation` yields `sum_R34_eta_L`:
\[
\sum_{r \in R_{34}} \operatorname{Res}_{U = r}(\eta_L) = \iota_L(P_{\mathrm{horiz}}).
\]
Adding the vertical field \(\iota_L(w_V)\) to the summed horizontal sheet field \(w_{H,L}\) cancels \(P_{\mathrm{horiz}}\) completely:
\[
\operatorname{resDiv}_{W,\mathrm{CoverL}}\bigl(\iota_L(w_V) + w_{H,L}\bigr) = \iota_L\!\left(\frac{N_{A,Q}}{2 W_2 H_0}\right).
\]
Applying finite normalized-trace descent ([FiniteTrace.lean](../../formal/lean/HodgeComputer/Constructions/HoldoutCover/FiniteTrace.lean), `HoldoutConstruction.finiteNormalizedTrace_firstOrder`) over the finite extension \(\mathrm{CoverL} / K_5\) descends this equation to a rational field \(w_{\mathrm{tot}} \in K_5^4\). Setting
\[
w_{\mathrm{final}} = \frac{1}{2}\!\left(w_{\mathrm{tot}} - \left(0, 0, 0, \frac{y M_A}{H_0}\right)\right) \in K_5^4
\]
satisfies \(\operatorname{src}_X + \operatorname{resDiv}_W(w_{\mathrm{final}}) = 0\) by `radial_normal_chart_identity` (`exists_K5_pde_solution`). Finally, `SymmetricPiola.certificate_of_K5_pde` lifts \(w_{\mathrm{final}}\) back to \(\mathbb{C}[X_0, X_1, X_2, Y_0, Y_1, Y_2]\) and closes `Submission.certificate` in [Solution.lean](Solution.lean).

**Constructive explicitness and why no expanded `witness.json` is exported.** Although [Certificate.lean](Certificate.lean) uses finite normalized-trace descent for economy of formalization, the construction determines an explicit rational certificate \((N, D)\) over \(\mathbb{Q}\): above each simple root \(r \in R_{34}\) of \(P_{34}(U)\), the moving-line coordinates \((W, a, b)\) are rational functions of \(r\) over \(K_5\), so the summed horizontal field \(w_H = \sum_{r \in R_{34}} w_{\mathrm{horiz}}(r) = \operatorname{Tr}_{K_5[U]/(P_{34})}(w_{\mathrm{horiz}})\) is already Galois-invariant and lies directly in \(K_5^4\). Clearing denominators and pulling back through `SymmetricPiola.certificate_of_K5_pde` therefore yields an explicit polynomial pair \((N, D)\). The sole reason for not materializing \((N, D)\) as an expanded `witness.json` is combinatorial size: even though the branch discriminant \(\operatorname{Disc}_U(P_{34})\) cancels from the denominator of \(w_H\) (because Jacobi's complementary-minor identity lowers the apparent \((\det J_{\mathrm{fib}})^{-2}\) factor in \(dU \wedge dV\) to a single \((\det J_{\mathrm{fib}})^{-1}\), which cancels against \(P_{34}'(U)\) in the Euler–Lagrange trace), clearing the remaining denominators \(G = u \Delta_X^2 + v \Delta_Y^2\), \(\det M_{abSQ}\), and \(U V\) across the \(34\) sheets produces their degree-\(34\) norms \(\operatorname{Nm}_{P_{34}}(G)\), \(\operatorname{Nm}_{P_{34}}(\det M_{abSQ})\), and \(\operatorname{Nm}_{P_{34}}(UV)\) in \(K_5\). Already \(\operatorname{Nm}_{P_{34}}(G)\) alone has degree \(34\) in \((\Delta_X^2, \Delta_Y^2)\) — homogeneous degree at least \(204\) in \((X, Y)\) before multiplying by the norms of \(\det M_{abSQ}\) and \(U V\) and clearing the rational quotient coordinates — pushing an expanded six-variable polynomial tuple to homogeneous degree in the high hundreds or thousands. Descending the residue-divergence equation on the cover keeps every verified polynomial identity compact and structured.

## Module map and attribution

- [PhysicalField.lean](PhysicalField.lean), [K5Field.lean](K5Field.lean), [SymmetricPiola.lean](SymmetricPiola.lean): \(S_3 \times S_3\) quotient field \(K_5\), radial normal-chart identity, and \(6 \times 6\) ambient Piola lift.
- [VerticalData.lean](VerticalData.lean), [VerticalIdentity.lean](VerticalIdentity.lean): \(7\)-term vertical Poisson field \(w_V\) and kernel-verified vertical identity modulo \(P_{\mathrm{horiz}}\).
- [SheetCalculus.lean](SheetCalculus.lean), [CoverAlgebra.lean](CoverAlgebra.lean), [CoverResidue.lean](CoverResidue.lean): moving-line incidence calculus on \(H_{\mathrm{cub}} = 0\), quadratic elimination cover \(A_C\), splitting field \(\mathrm{CoverL}\), and the \(34\)-sheet residue sum.
- [LocalResidueData.lean](LocalResidueData.lean), [Q5WeightsData.lean](Q5WeightsData.lean), [LocalResidueU0.lean](LocalResidueU0.lean), [LocalResidueInfAlg.lean](LocalResidueInfAlg.lean), [LocalResidueInf.lean](LocalResidueInf.lean), [LocalResidueQ5Alg.lean](LocalResidueQ5Alg.lean), [LocalResidueQ5Poly.lean](LocalResidueQ5Poly.lean), [LocalResidueQ5Bridge.lean](LocalResidueQ5Bridge.lean), [LocalResidueQ5Trace.lean](LocalResidueQ5Trace.lean), [LocalResidueQ5CheckA.lean](LocalResidueQ5CheckA.lean), [LocalResidueQ5CheckB.lean](LocalResidueQ5CheckB.lean), [LocalResidueQ5.lean](LocalResidueQ5.lean): local residue evaluations at \(U = 0\), \(U = \infty\), and \(Q_5 = 0\), plus global residue cancellation.
- [Certificate.lean](Certificate.lean), [Solution.lean](Solution.lean): global residue assembly, normalized-trace descent, and final theorem `Submission.certificate`.

The mathematical existence background and moving-lines residue construction are developed in [Chapter 3](../../docs/03-geometric-support.md), [Chapter 3B, §3B.11](../../docs/03b-weighted-threefolds.md#3b11-moving-lines-on-a-cubic-threefold-and-global-residue-cancellation), and [Chapter 5, §5.8](../../docs/05-computation.md#58-factored-kronecker-grid-verification-and-algebraic-residue-evaluation). The formal proof builds on the shared library packages [QuadraticCovers](../../formal/lean/HodgeComputer/Constructions/QuadraticCovers/README.md) (`PairAlgebra`, `LaurentJets`, `RationalCoverResidues`), [PolynomialEncoding](../../formal/lean/HodgeComputer/Constructions/PolynomialEncoding/README.md) (`BivariateExpressions`, `KroneckerCheck`, `PolyOps`), [PiolaContraction.lean](../../formal/lean/HodgeComputer/Constructions/ResidueTransport/PiolaContraction.lean), [FiniteTrace.lean](../../formal/lean/HodgeComputer/Constructions/HoldoutCover/FiniteTrace.lean), and [Residues.lean](../../formal/lean/HodgeComputer/Constructions/EllipticCompanions/Residues.lean). Symbolic discovery, residue elimination, and Lean formalization were carried out with AI assistance under contributor supervision.
