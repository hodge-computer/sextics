# Cycle-q2 — attempt 74: full four-direction polynomial-in-Z tangent module and a new U-moving source-serving current

Date: 2026-11-03. **Original unrestricted existence remains OPEN; no accepted polynomial certificate and no closed Lean proof.** This is a genuinely new **constructive statement in the explicitly specified source-bound cubic chart**, extending the attempt-53 *three-coordinate* tangent classification to **all four moving coordinates**. It does not claim to integrate the nonzero scalar remainder, descend to the original physical coordinates, or solve the protected target.

## 1. Protected exact original statement

In ordered coordinates `z=(X0,X1,X2,Y0,Y1,Y2)` let

\[
F=\sum_{i=0}^2(X_i^6+Y_i^6)+\tfrac12(X_0^3X_1Y_0Y_1+X_1^3X_2Y_1Y_2+X_2^3X_0Y_2Y_0),\quad
A=X_0^2X_1^2X_2^3Y_0^2Y_1^2Y_2,\quad q=2.
\]

The only acceptable certificate is a nonzero homogeneous `D` with `gcd_C(D,F)=1`, homogeneous `Ni` of degree `deg(D)+7`, and unrestricted polynomial `Q` such that

\[
\boxed{AD^2-2D\sum_i N_iF_i+F(D\sum_i\partial_iN_i-\sum_iN_i\partial_iD)=F^3Q}.\tag{O}
\]

The source weights `(2,1,0,3,2,1)` give weight 17=5 (mod 6) for A, volume weight 9=3, residue weight 2. No invariant projection is applied. Primary current files read: `data/cycle-q2/instance.rec`, `why.md`, and `formal/README.md` in `hodge-computer/sextics` (linked below). **The private Math-project checkout and Lean were not accessible**. The source-to-cubic identity from saved attempt69 was read as previous research and is not re-executed here; the new theorems below are verified directly from the displayed cubic definitions and hence are not contingent on any unreviewed old rank claim.

## 2. The actual-source cubic field (not alternate physical coordinates)

Let independent variables be `(P,U,Z,b)`, and write

\[
L=P^6+U^2,\quad M=PU^2b/2,\quad N=PUZ/2,\quad
K=(U^4+U^2)b^3+U(1+Z^6)+ZU^2b^2/2,\quad
p=N/L-M^2/(3L^2),\quad
q_c=K/L-MN/(3L^2)+2M^3/(27L^3).
\]

The normal cubic has equation `theta^3+p theta+q_c=0` and two-dimensional trace-zero Gauss-Manin connection `∇_j=∂_j+p_j B_p+(q_c)_j B_q` on its distinguished rational vector `k2`. Put

\[
 m_p=-2M/(3L^2),\quad m_q=-N/(3L^2)+2M^2/(9L^3),\quad
 c=M^2N/(6PUL^2)=P^2U^4Zb^2/(48L^2).
\]

The *inherited but directly source-bound in attempt69* exact rank-two forcing is

\[
\mathcal R=c\{m_p\nabla_p k_2+m_q\nabla_{q_c}k_2\}.\tag{R}
\]

No old scalar `g` value is assumed; attempts53/54 had an omitted Z product-rule term and their uncorrected numerical remainders must not be used. This run independently reconstructs a new fiber's full corrected scalar divergence.

## 3. NEW theorem — explicit free tangent module over K0[Z] with U movement

Let `K0=Q(P,U,b)`, `R0=K0[Z]`, `C=1728 L^5`, and

\[
J_{ij}=p_i(q_c)_j-p_j(q_c)_i.
\]

All six scaled Jacobian minors

`CJ_bZ, CJ_PZ, CJ_Pb, CJ_UZ, CJ_Ub, CJ_UP`

are **polynomials in** `Q[P,U,b,Z]`, of respective Z-degrees `(5,6,6,6,6,7)`—verified symbolically. The first two are coprime in `K0[Z]`. As a *fresh separate exact fiber witness* at `(P,U,b)=(2,1,1)` the polynomials are

\[
\begin{aligned}
f &=CJ_{bZ}=-29203200Z^5-472118400Z-2849745600,\\
g &=CJ_{PZ}=-5585112000Z^6+71660160Z^5+112666320Z+4211232480.
\end{aligned}
\]

Their polynomial GCD is **1** over Q and both specialize without degree loss. Thus their generic resultant is nonzero and there exist uniquely degree-constrained Bezout coefficients `u,v ∈ K0[Z]` with `degZ u≤5`, `degZ v≤4`, such that

\[
\boxed{u f+v g=1}.\tag{1}
\]

The precise reconstruction is `u=f^{-1} mod g` (degree <6) and `v=(1-uf)/g` (degree <5). This is an explicit finite rational algorithm, not an unevaluated integral. The older `(1,1,1)` fiber was not used to establish the new `U`-moving claim.

For any triple `(i,j,k)` of distinct coordinates define the Nambu field

\[
T^{ijk}=J_{jk}\partial_i-J_{ik}\partial_j+J_{ij}\partial_k.
\]

It satisfies **exactly** `T^{ijk}(p)=T^{ijk}(q_c)=0` and `div T^{ijk}=0`, the latter by cancelling all mixed second partial derivatives. Define

\[
\begin{aligned}
T&=T^{P,b,Z}=J_{bZ}\partial_P-J_{PZ}\partial_b+J_{Pb}\partial_Z,\\
B&=T^{U,b,Z}=J_{bZ}\partial_U-J_{UZ}\partial_b+J_{Ub}\partial_Z,\\
B'&=T^{U,P,Z}=J_{PZ}\partial_U-J_{UZ}\partial_P+J_{UP}\partial_Z,\\
\boxed{S}&=C(uB+vB').
\end{aligned}
\]

Then `S(p)=S(q_c)=0` and, by (1), **`S_U=1`**. Its other components are completely explicit:

\[
\boxed{S_P=-v(CJ_{UZ}),\qquad S_b=-u(CJ_{UZ}),\qquad S_Z=u(CJ_{Ub})+v(CJ_{UP}).}\tag{2}
\]

All lie in `K0[Z]`, with `degZ S_P≤10`, `degZ S_b,S_Z≤11`. There is no denominator depending on Z, and no special chart factor `1/T_old` or `1/Δ` in the **coefficients of S**. Denominators in `P,U,b` do remain.

**Theorem.** The module of all polynomial-in-Z, all-four-coordinate rational vector fields `V∈R0^4` satisfying `V(p)=V(q_c)=0` is free of rank two, with explicit basis `T,S`:

\[
\boxed{\ker_{R0}(dp,dq_c)=R0 T\oplus R0 S}.\tag{3}
\]

**Proof.** Given `V`, subtract `V_U S`. The difference has U-component zero. The remaining `(P,b,Z)`-supported tangent fields have generic rank one over `K0(Z)` and are multiples of `T`. Because `gcd_{R0}(J_bZ,J_PZ)=1`, a rational multiple of T with all components in R0 must have a polynomial-in-Z multiplier. Independence follows from `S_U=1`, `T_U=0`. This proves full coverage within the stated polynomial-Z class, not merely that T and S give two examples.

This addresses the genuinely independent U direction missing from attempt53's 3-coordinate classification. It does not cover arbitrary rational Z-poles, all rank-two currents, or all physical six-coordinate vector fields.

## 4. NEW source-serving four-direction current, with nonzero moving divergence

For any pair `(i,j)` set

\[
W^{ij}=(m_p(q_c)_j-m_qp_j)\partial_i+(m_qp_i-m_p(q_c)_i)\partial_j.
\]

Its two moment identities are `W^{ij}(p)=m_p J_ij`, `W^{ij}(q_c)=m_q J_ij`. Thus

\[
X=C\{uW^{bZ}+vW^{PZ}\},\qquad X(p)=m_p,\quad X(q_c)=m_q,\quad X_U=0.
\]

This source-serving lift `X` itself is inherited from attempt53; no novelty is claimed for it. **The new construction is**

\[
\boxed{\mathcal J=cX+S},\tag{4}
\]

whose *U component is exactly 1*. It continues to serve both moments of the original cubic source:

\[
\mathcal J(p)=c m_p,\quad\mathcal J(q_c)=c m_q.
\]

For `g0=div(cX)`—with `∂P`, `∂b`, **and ∂Z acting on c and the moving Bezout coefficients**—we have the full identity

\[
\boxed{\sum_{j=P,U,Z,b}\nabla_j(\mathcal J_j k_2)
=\mathcal R+(g_0+\operatorname{div}S)k_2}.\tag{5}
\]

The scalar is **not zero**, and we have not integrated it. This is an exact partial current, **not** the original certificate.

At the new good rational point `(P,U,Z,b)=(2,1,1,1)`, `verify_moving_divergence.py` computes derivatives of **u,v before specialization** using the differentiated identity

\[
 u_xf+v_xg=-u f_x-v g_x,\qquad x=P,U,b.
\]

It checks the new U-moving field and its complete divergence:

\[
\operatorname{div}S
=-\frac{224228135969208580744492176084996414278828234079017862598102}
{77059206094410474557885443247423340907997825634715836080025}\ne0.
\]

Its full new regular scalar at that point is

\[
 g_0+\operatorname{div}S=
-\frac{6995917718609654923405871104692923920701598864238897482458349}
{2404247230145606806206025829319608236329532159803134085696780}\ne0.
\]

The exact moment values `(-1/321311250, -193/125311387500)` equal `(c m_p,c m_q)` there. The two coordinates of the actual rank-two source `R` were reconstructed separately and checked against (5). See `MOVING_DIVERGENCE_WITNESS.json` for every long rational value and the actual executed checks.

**New complete scalar-correction criterion for this class:** all `R0`-polynomial-in-Z coefficient fields serving `(cm_p,cm_q)` are

\[
\mathcal J=cX+\phi T+\psi S,\quad \phi,\psi\in R0,
\]

and their covariant divergences are

\[
\boxed{\mathcal R+
\bigl[g_0+T(\phi)+S(\psi)+\psi\operatorname{div}S\bigr]k_2}.\tag{6}
\]

Hence an exact **k2-only, polynomial-in-Z** primitive would follow from the concrete two-scalar PDE

\[
 T(\phi)+S(\psi)+\psi\operatorname{div}S=-g_0.\tag{7}
\]

This PDE has **not** been solved. It is a sufficient-and-necessary criterion only inside the stated current class. It is not a reformulation of unrestricted original six-coordinate existence and does not suppress the still nonzero regular remainder.

## 5. Provenance, evidence and exact missing step

**Proven independently here, over rational functions of characteristic zero:** generic polynomiality and Z-degrees of the six Jacobian minors; the new distinct-fiber Bezout witness; all Nambu tangency/divergence identities; the direct-sum/free rank-two module theorem; the actual U-moving polynomial lift S; the explicit source moment identities for X and X+S; the nonzero, fully moving and independently reconstructed corrected scalar at a different exact fiber; both cubic source components. Symbolic polynomial/rational assertions were executed using SymPy 1.14.0. No nonexistence inference was made from modular failures, and no arbitrary denominator sweep was performed.

**Missing for the original problem:** solve the concrete scalar equation (7), or construct a more general full rank-two rational current; transport its *complete* source, character and regular remainder into the physical six coordinates; descend any finite cover; legally clear a homogeneous nonzero D coprime to F **over C**, produce homogeneous Ni of degree d+7, and verify literally **E=F³Q** with unrestricted Q. There is no `(D,N,Q)` candidate in this run to check against the full identity. No Lean compiler or private Math-project checkout was used. No messages were sent or repository changes/publications/new tasks made.

## 6. Saved scripts, exact checks and checkpoint

`verify.py` independently reconstructs all six coefficient Jacobians, original F/A and nontrivial residue weight, tangent fields, moments, div-free identities, and two rational-fiber Bezout witnesses. `verify_moving_divergence.py` independently reconstructs the canonical u,v and their P,U,b derivatives at the new fiber, evaluates the full rank-two source and true regular remainder. Both scripts ran successfully; outputs are `RUN_VERIFY.log`, `RUN_MOVING.log`, `EXACT_WITNESS.json` and `MOVING_DIVERGENCE_WITNESS.json`. See `RESEARCH_INDEX.md` to avoid repeating the work.

Primary source URLs:
- https://raw.githubusercontent.com/hodge-computer/sextics/main/data/cycle-q2/instance.rec
- https://raw.githubusercontent.com/hodge-computer/sextics/main/data/cycle-q2/why.md
- https://raw.githubusercontent.com/hodge-computer/sextics/main/formal/README.md

Prior saved records used as provenance only: `cycle_q2_attempt69/REPORT.md`, `cycle_q2_attempt73/RESEARCH_INDEX.md`, and `cycle_q2_transverse_derivative_audit_20261102_REPORT.md`.
