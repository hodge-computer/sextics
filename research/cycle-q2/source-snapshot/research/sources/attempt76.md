# Cycle-q2: direct rational-equation solve attempt (follow-up to attempt 75)

**Date: 2026-11-03. Result: no global rational solution or original certificate was obtained.**

This work addresses the exact displayed equation from attempt 75,

\[
\boxed{ B(\psi)+(\operatorname{div}B)\psi=-g,\qquad g=\operatorname{div}(cX). }
\]

It does not replace this requirement by formal power-series solvability. The new result is an exact obstruction to **every correction polynomial in Z of degree at most five**, even when its coefficients are arbitrary rational functions of the other three parameters. This is a restricted-class theorem, not an unrestricted nonexistence theorem.

## 1. Protected original target and scope

In the fixed coordinate order `(X0,X1,X2,Y0,Y1,Y2)`, retain

\[
F=\sum_{i=0}^2(X_i^6+Y_i^6)+\frac12(X_0^3X_1Y_0Y_1+X_1^3X_2Y_1Y_2+X_2^3X_0Y_2Y_0),
\quad A=X_0^2X_1^2X_2^3Y_0^2Y_1^2Y_2,\quad q=2.
\]

The original goal is a nonzero homogeneous D, coprime to F over C, homogeneous Ni of degree deg(D)+7, and a polynomial Q, with

\[
AD^2-2D\sum_iN_iF_i+F\left(D\sum_i\partial_iN_i-\sum_iN_i\partial_iD\right)=F^3Q.
\]

The current public instance and mathematical-context files were read. No change to F, A, pole order, or source character was made. No physical D,N,Q tuple is produced here. Thus there is no new physical candidate to subject to the complete original identity. Homogeneity, complex coprimality, regular-remainder transport, and physical reassembly are not claimed completed.

The attempt-75 Google Doc was actually retrieved with the connected Google Drive tool. It explicitly treats its physical-to-cubic transport as an inherited research input. This follow-up reconstructs the displayed cubic coefficient functions and their derivatives independently; it does not claim a new proof of the full six-coordinate transport. Its new obstruction is unconditional for the rational equation specified below.

Primary records:

- https://raw.githubusercontent.com/hodge-computer/sextics/main/data/cycle-q2/instance.rec
- https://raw.githubusercontent.com/hodge-computer/sextics/main/data/cycle-q2/why.md
- https://github.com/hodge-computer/sextics/discussions/61
- Previous equation and definitions: https://docs.google.com/document/d/1FwjBaLCiQdF_VSqpGy0g1LJTHX1o_Q87O0KfOXTQImQ/edit

## 2. Exact rational equation: every coefficient specified

Let `(P,U,Z,b)` be independent parameters and define

\[
\begin{aligned}
L&=P^6+U^2,&M&=PU^2b/2,&N&=PUZ/2,\\
K&=(U^4+U^2)b^3+U(1+Z^6)+ZU^2b^2/2,\\
p&=N/L-M^2/(3L^2),&q_c&=K/L-MN/(3L^2)+2M^3/(27L^3),\\
m_p&=-2M/(3L^2),&m_q&=-N/(3L^2)+2M^2/(9L^3),\\
c&=P^2U^4Zb^2/(48L^2).
\end{aligned}
\]

Here `q_c` is a cubic coefficient, not a change to the original pole parameter q=2. Code uses the local symbol `q` for `q_c` only.

Write

\[
J_{ij}=p_i(q_c)_j-p_j(q_c)_i,
\qquad f=J_{PZ},\quad h=J_{UZ}.
\]

Over Q(P,U,b), let u,v be the unique degree-at-most-five polynomials in Z such that

\[
uf+vh=1.
\]

Their reconstruction is the 12-by-12 coefficient matrix S for the map `(u,v) -> uf+vh`: column i is the coefficient vector of Z^i f for i=0,...,5; column 6+i is that of Z^i h. Solve `S w=e0`. The selected test point has invertible S, also modulo 101, which is a positive witness that this rational reconstruction exists generically.

Set

\[
\begin{aligned}
X_P&=u(m_p(q_c)_Z-m_qp_Z),\\
X_U&=v(m_p(q_c)_Z-m_qp_Z),\\
X_Z&=u(m_qp_P-m_p(q_c)_P)+v(m_qp_U-m_p(q_c)_U),&X_b&=0,\\
B_P&=-uJ_{bZ},&B_U&=-vJ_{bZ},\\
B_Z&=uJ_{bP}+vJ_{bU},&B_b&=1.
\end{aligned}
\]

The Nambu/minor identities and Bezout equality give

\[
X(p)=m_p,\quad X(q_c)=m_q,\quad B(p)=B(q_c)=0.
\]

Consequently `cX+psi B` always preserves these two prescribed moments. Its divergence is zero exactly when the stated scalar PDE holds. All derivatives in P,U,Z,b act on u,v,c and the moving coefficient functions. In particular it is **not** permissible to integrate in b while holding P,U,Z fixed along B.

## 3. Denominator-cleared reduction

Let R=det(S), let \(\widetilde u=Ru\), \(\widetilde v=Rv\), and define the rational fields

\[
\mathcal V=RB,\qquad \mathcal Y=RX.
\]

They are given by Sylvester cofactors rather than unspecified integrations. Since B_b=1, V_b=R. Multiplying the scalar equation by R^2 yields exactly

\[
\boxed{
R\mathcal V(\psi)+[R\operatorname{div}\mathcal V-\mathcal V(R)]\psi
=c\mathcal Y(R)-R\operatorname{div}(c\mathcal Y).
}
\]

All remaining coefficient denominators come from the explicitly displayed rational functions and powers of L, and can be cleared. This is a concrete linear PDE for a rational function, not a solution or an original certificate.

This reduction follows directly from

\[
\operatorname{div}(\psi\mathcal V/R)
=\mathcal V(\psi)/R+\psi\operatorname{div}\mathcal V/R-\psi\mathcal V(R)/R^2.
\]

## 4. Direct global check of the preceding finite correction

The preceding current used

\[
\psi_{\rm lead}=-b^3g_2/3,
\quad
g_2=\frac{P^3U^4Z^2(53P^{18}+19P^{12}U^2-17P^6U^4+17U^6)}
{1728(P^6+U^2)^4(P^6-U^2)^2}.
\]

It cancels the leading b-adic coefficient, but this run checked its **complete** rational PDE residual

\[
\mathcal E=g+B(\psi_{\rm lead})+(\operatorname{div}B)\psi_{\rm lead}.
\]

At `(P,U,Z,b)=(2,1,1,1)`, exact rational arithmetic gives

\[
\mathcal E=
\frac{221104032117500751369598324699453702731465140739760566092042569466456757233}
{5061588920764561649834983405943986344765087669626360948544711775542597029002260000}
\ne0.
\]

Its good reduction is 13 modulo 101. This is an exact counterexample to that particular rational expression being a complete solution, not an obstruction to arbitrary corrections. The long rational value is saved in `FINITE_CORRECTION_FAILURE.json`.

## 5. New theorem: no polynomial-in-Z solution of degree at most five

**Theorem.** There are no \(H_0,\ldots,H_5\in\mathbb C(P,U,b)\) for which

\[
\psi=\sum_{j=0}^{5} H_j(P,U,b)Z^j
\]

satisfies the exact scalar equation of section 2. No degree or pole bounds are imposed on the parameter functions H_j.

### Proof construction

B_P,B_U,div(B) have Z-degree at most 10; B_Z has degree at most 11; g has degree at most 11. Substituting the displayed psi yields sixteen Z-coefficient equations. Write these as

\[
\sum_{j=0}^5\left[
Z^j B_P(H_j)_P+Z^j B_U(H_j)_U+Z^j(H_j)_b
+\bigl(jZ^{j-1}B_Z+Z^j\operatorname{div}B\bigr)H_j
\right]=-g.
\]

Differentiate each coefficient equation once in each of P,U,b. There are 64 scalar equations. Their unknown values are the six H_j and all their parameter partial derivatives of total order at most two. There are ten such multi-indices per H_j, hence **60 unknowns**. Mixed partials use the same unknown; they are not allowed to vary independently under different orderings.

This gives a necessary linear algebraic system

\[
\mathsf M\mathbf h=\mathbf r,
\qquad \mathsf M\in\mathbb Q(P,U,b)^{64\times60}.
\]

Every proposed rational solution supplies a solution of this necessary system over the same characteristic-zero field. At `(P,U,b)=(2,1,1)`, choose the 61 rows recorded in `DEGREE5_OBSTRUCTION.json` from the augmented matrix. Its determinant satisfies

\[
\boxed{\det\bigl([\mathsf M\mid\mathbf r]_{\rm selected}\bigr)
\equiv86\pmod{101}\ne0.}
\]

Every denominator used in this reduction is a unit at this arithmetic point. Therefore this rational determinant is not identically zero in characteristic zero. It follows that the generic augmented rank is at least 61, whereas the coefficient matrix has only 60 columns. The necessary system is inconsistent. This proves the theorem, including over C.

**Why this is not an invalid modular-failure inference:** the witness is a **nonzero determinant** of a characteristic-zero rational matrix. The upper bound 60 for its coefficient rank is universal, coming from its number of columns. We do not assume that an observed smaller modular rank equals a generic rational rank. Nor do we assume that the hypothetical H_j can themselves be specialized at this point; their possible poles do not invalidate the generic rank contradiction.

### Smaller-case diagnostics

These are supplementary, not needed for the degree-five theorem:

- Degree at most two: the original coefficient system has size 13 by 12 and exact ranks 12 versus 13 after adjoining the source.
- Degree at most three: coefficient matching alone is consistent. Once the three first parameter derivatives are included, the system has size 56 by 40 and exact rational ranks 40 versus 41. Thus merely solving coefficient equations at one parameter value would have missed a necessary integrability condition.
- Degree at most four: the corresponding 60 by 50 coefficient matrix has full column rank and a nonzero 51-column augmented minor at good modular points.

## 6. Independent reconstruction and actual execution

Two independently coded approaches were run locally:

1. `check_operator.py`, `polynomial_Z_test.py`, `prolong_solver.py`, and `export_witness.py` use SymPy 1.14.0 over exact rational arithmetic. Derivatives of u,v are obtained from differentiating `S w=e0`, not by freezing the parameter-dependent inverse. Second derivatives are retained for the prolonged equations. They generate the operator, exact defect, matrices, and selected determinant witness.
2. `independent_modular_verify.py` uses only the Python standard library. It starts again from the defining L,M,N,K,p,q_c formulas and uses truncated multivariate Taylor arithmetic modulo 101. It reconstructs the Bezout inverse, all relevant moving derivatives, B, cX, and every one of the **64 by 61 augmented entries**. It compares them with the independently generated witness and recomputes the determinant.

Executed output:

```
PASS: all 64 x 61 entries independently reconstructed from p,q with moving derivatives.
PASS: 61 x 61 augmented minor determinant = 86 mod 101
```

An additional test of an integrating multiplier built from constant powers of P,U,L,det(S),b gave an inconsistent exact linear system at seven regular rational points. That only excludes this particular factor-product proposal; it is not a classification of rational integrating factors.

No Lean compiler or private Math-project checkout was used. The local Python/container runtime was available in this turn. No claim relies on an unavailable JavaScript execution environment.

## 7. Exact unresolved step and non-repetition checkpoint

This run did **not** solve the arbitrary rational equation. A rational psi with Z-dependent denominator, or a polynomial in Z of higher degree, is outside the new obstruction. The choice of the single B-tangent direction is itself only a restriction of the larger source-serving current problem. There may also be useful currents not preserving both moments separately.

The all-order formal recurrence does not establish any of those rational solutions. No primitive/certificate should be claimed until the scalar residual vanishes identically and the full physical transport and original E=F^3 Q verification are complete.

Do not repeat: the attempt-75 leading b-adic cancellation; its global finite-correction check now recorded here; the degree<=2 coefficient test; the degree<=3 mixed-partial consistency test; or the degree<=5 prolonged augmented-minor calculation. Reuse the explicit operator circuit and independent reconstruction instead. Do not cite this as unrestricted rational nonexistence or as proof against the original target.

No external messages, repository changes, publications, or additional tasks were made. Output is saved locally in the linked research packet; no new Library or Google Drive upload is claimed.
