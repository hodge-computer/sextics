# 3B. Weighted threefolds and two-reflection sextics

[Previous: split sextics and K3 correspondences](#technical-information/split-and-k3) · [Contents](#technical-information/introduction) · [Next: quadratic nets and pair correspondences](#technical-information/quadratic-nets)

A smooth even sextic with one additional reflection in an \(X\)-coordinate and one in a \(Y\)-coordinate has its entire invariant fourth cohomology supported on a divisor. The individual reflection quotients are Fano and supply the sectors where either reflection acts positively. The remaining simultaneous negative sector comes from a family of weighted Calabi–Yau threefolds. This chapter proves the required threefold theorem and the passage from its fibers to the fourfold.

The proof constructs genus-four curves whose sums with their involution translates are complete intersections of two quadrics. Their normal sequence computes the Abel–Jacobi differential, and a finite exact spanning calculation supplies a surjective curve correspondence. Openness and a supported projector then extend the result to every smooth member. This retains the curve-correspondence strategy of [Voisin, Proposition 2.1](https://www.numdam.org/item/ASNSP_1992_4_19_4_473_0.pdf), with an explicit contact construction supplying the curves. We work over \(\mathbb C\) with rational cohomology; coefficient descent is addressed at the end.

## 3B.1 The weighted threefold theorem

Let

\[
T\subset\mathbb P(1,1,1,1,2),\qquad
\sigma(x_0,x_1,y_0,y_1,u)=(x_0,x_1,-y_0,-y_1,u).
\]

**Weighted threefold theorem.** Suppose \(T\) is a quasismooth degree-six hypersurface with \(\sigma\)-invariant equation. Then

\[
H^3(T,\mathbb Q)^-\subset N^1H^3(T,\mathbb Q).
\]

More precisely, the algebraic anti-projector

\[
P^-=(\Delta_T-\Gamma_\sigma)/2
\]

is cohomologous to a rational algebraic cycle supported on \(D\times D\) for some divisor \(D\subset T\).

Quasismoothness forces the coefficient of \(u^3\) to be nonzero. Otherwise every partial derivative of the cone equation vanishes at a nonzero point of the \(u\)-axis. Thus \(T\) avoids the unique weighted singular vertex and is an ordinary smooth projective threefold. Weighted adjunction gives \(K_T\simeq\mathcal O_T\). The determinant of \(\sigma\) is positive, so \(H^{3,0}(T)\) is invariant and the minus part has types \((2,1)+(1,2)\). This Hodge-theoretic coniveau does not itself give the divisor; the proof below constructs the required algebraic image.

Weighted weak Lefschetz and duality give

\[
H^1(T)=H^5(T)=0,\qquad
H^2(T)=\mathbb Qh,\qquad H^4(T)=\mathbb Qh^2.
\]

Consequently \(P^-\) acts only on \(H^3(T)^-\). The weighted residue and Lefschetz statements used here and below are in [Dolgachev, §§3.2–3.3 and 4.2–4.3](https://sites.lsa.umich.edu/idolga/wp-content/uploads/sites/1334/2024/08/weighted82.pdf).

## 3B.2 Genus-four norm contacts

Write \(S=\mathbb C[a,b,c,d,u]\), with weights \((1,1,1,1,2)\), and let \(\sigma\) negate \(c,d\). Superscripts indicate its eigenspaces. Consider the polynomial map

\[
\begin{aligned}
\Phi:(S_2^+)^2\times(S_4^+)^2\times S_3^+\times S_3^-
&\longrightarrow S_6^+,\\
(f_1,f_2,g_1,g_2,A,B)&\longmapsto
f_1g_1+f_2g_2+A^2-B^2.
\end{aligned}
\]

Its source has dimension \(2\cdot7+2\cdot26+12+12=90\), and its target has dimension 70. Put \(h=A+B\), \(k=A-B=\sigma h\). A presentation \(G=\Phi(f_1,f_2,g_1,g_2,A,B)\) gives curves

\[
C=(f_1=f_2=h=0),\qquad
\sigma C=(f_1=f_2=k=0)
\]

on \(T=(G=0)\). We call this a **norm contact**, since \(hk=h\sigma h\). On the open where these are complete intersections,

\[
C+\sigma C=T\cap(f_1=f_2=0)\sim4h_{\mathrm{hyp}}^2.
\qquad\text{(3B.2.1)}
\]

Assume one quadric has a nonzero \(u\)-coefficient. Eliminating \(u\) identifies \(C\) with an ordinary complete intersection of degrees \((2,3)\) in \(\mathbb P^3\). If \(C\) is smooth, adjunction gives

\[
K_C=\mathcal O_C(1),\qquad \deg\mathcal O_C(1)=6,\qquad g(C)=4.
\]

**Construction from a cubic-surface line.** Suppose
\[
G=A^2-B^2+H(q_0,q_1,q_2,q_3),
\qquad q_i\in S_2^+,\quad A\in S_3^+,\quad B\in S_3^-,
\]
where \(H\) is an ordinary cubic form. A line \(L=(\ell_1=\ell_2=0)\) on \(H=0\) gives \(H=\ell_1H_1+\ell_2H_2\), with quadratic \(H_i\). Pulling back supplies the norm presentation
\[
f_i=\ell_i(q_0,q_1,q_2,q_3),\qquad
g_i=H_i(q_0,q_1,q_2,q_3).
\]
This replaces a search for all six contact forms by a line calculation on a cubic surface. The pulled-back curve must still be a smooth complete intersection with the stated \(u\)-coefficient condition; the line alone does not imply these properties or the normal-rank and spanning conditions below.

### Presentation changes and actual curve motion

For a fixed embedded curve \(C\) and a fixed equation \(G\), the presentation fiber has dimension 19 on this open. There are four parameters for changing the basis \(f_1,f_2\), eight for replacing

\[
h\longmapsto h+f_1\ell_1+f_2\ell_2,
\qquad \ell_i\in S_1,
\]

and seven for the syzygy

\[
(g_1,g_2)\longmapsto(g_1+f_2q,g_2-f_1q),\qquad q\in S_2^+.
\]

There is no further continuous scaling of \(h\): modulo \((f_1,f_2)\), the identity \(G=h\sigma h\ne0\) forces that scaling to have square one. Conversely, the minimal complete-intersection generators show that these are all presentation changes. Thus, where \(d\Phi\) is surjective, its 20-dimensional fixed-\(G\) fiber supplies a genuine one-dimensional family of curves.

### An intrinsic chart

The same incidence has a smaller description useful for explicit finite-cover constructions. On the chart where the quadrics' \(u\) and \(ab\) coefficients are independent, choose their basis so that

\[
f_1=u+Q_1,\qquad
f_2=Q_2=ab+\lambda a^2+\mu b^2+q(c,d),
\]

where \(Q_1\) has no \(ab\) term. Each quadric has five free coefficients. Reduce the cubics \(A,B\) modulo \(Q_2\), using monomials not divisible by \(ab\). There are eight such monomials of each parity, giving \(5+5+8+8=26\) parameters.

This reduction is defined on a precise open chart. Put \(z=\lambda\mu\). The determinant for cubic reduction is \(1-z\); the determinant for invariant sextic reduction is

\[
\Delta=(1-z)(1-3z)(1-2z)^3.
\qquad\text{(3B.2.2)}
\]

To check this, project multiplication by \(Q_2\) onto monomials divisible by \(ab\). Ordering by the \(c,d\)-degree gives triangular blocks with tridiagonal determinants \(D_m=D_{m-1}-zD_{m-2}\), \(D_0=D_1=1\). In degree six the blocks are \(D_5=(1-z)(1-3z)\), three copies of \(D_3=1-2z\), and five copies of \(D_1\). The degree-three blocks give \(1-z\).

On \(\Delta\ne0\), the condition for a fixed invariant weighted sextic is

\[
\operatorname{rem}_{Q_2}\!\left(G(a,b,c,d,-Q_1)-A^2+B^2\right)=0.
\qquad\text{(3B.2.3)}
\]

The invariant sextic quotient has dimension \(44-19=25\), so this is a system of 25 equations in 26 parameters. For a cyclic equation \(G=u^3+H\), its argument is \(H-Q_1^3-A^2+B^2\).

Suppose a curve component of this incidence has universal surface dominating the ratio plane \(r=b/a, s=d/c\). On \(a=1, c=t, d=st\), a moving point is specified by (3B.2.3) and

\[
Q_2(1,r,t,st)=0,\qquad
(A+B)(1,r,t,st)=0,\qquad u=-Q_1(1,r,t,st).
\]

There are 27 equations in the 26 parameters and \(t\), over \(\mathbb C(r,s)\). Dominance, rather than this equation count alone, makes the resulting component generically finite; in characteristic zero it is generically étale. This supplies a finite algebraic moving-point field for the differential and trace constructions of [Chapter 2, §2.8](#technical-information/explicit-constructions). The closed forms needed there come from the next section.

## 3B.3 Normal obstructions and residue forms

### The normal sequence and the correspondence pairing

For a smooth norm-contact curve, the normal sequence is

\[
0\longrightarrow N_{C/T}\longrightarrow
E:=\mathcal O_C(2)^2\oplus\mathcal O_C(3)
\xrightarrow{(g_1,g_2,k)}\mathcal O_C(6)
\longrightarrow0.
\qquad\text{(3B.3.1)}
\]

Riemann–Roch gives \(h^0(E)=h^0(\mathcal O_C(6))=33\) and \(H^1(E)=0\). Complete-intersection restriction maps are surjective. Hence

\[
H^1(N_{C/T})\simeq
S_6/(f_1,f_2,g_1,g_2,A,B)_6,
\qquad h^0(N_{C/T})=h^1(N_{C/T}).
\qquad\text{(3B.3.2)}
\]

The invariant part of the displayed ideal is exactly the image of \(d\Phi\). If \(d\Phi\) has rank 70 and the negative part of this ideal has codimension one, then \(h^0N=h^1N=1\). The actual family from §3B.2 is therefore a smooth local Hilbert curve.

Choose the residue volume form \(\Omega_T=\operatorname{Res}_T(\Omega_{\mathbb P}/G)\). It identifies \(T_T\simeq\Omega_T^2\) and \(\det N_{C/T}\simeq K_C\). For a deformation \(\kappa\in H^1(T,T_T)\), let \(\rho_C(\kappa)\in H^1(C,N_{C/T})\) be the obstruction to carrying \(C\) along that deformation. Let \(\Lambda\) be the smooth projective completion of a parameter curve and \(\Gamma\subset\Lambda\times T\) its closed universal correspondence. For a tangent vector \(D\) at a smooth member, with normal velocity \(v_D\), the correspondence pullback satisfies

\[
\bigl(\Gamma^*(\kappa\mathbin{\lrcorner}\Omega_T)\bigr)(D)
=\operatorname{Tr}_C\bigl(v_D\wedge\rho_C(\kappa)\bigr),
\qquad\text{(3B.3.3)}
\]

with compatible wedge conventions. Indeed, pullback by the universal curve followed by integration over its fibers evaluates the left side by contracting the \((2,1)\)-form with the normal velocity. Restricting a Dolbeault representative of \(\kappa\) to \(C\) gives its normal obstruction; contraction with \(\Omega_T\) turns the resulting integrand into the Serre pairing on the right. This is the infinitesimal Abel–Jacobi pairing, expressed entirely on the smooth threefold and its curve; see [Westhoff, pp. 375–377 and §3](https://msp.org/pjm/1998/183-2/pjm-v183-n2-p08-s.pdf) for the contraction description and its reduction to residues.

The Euler and normal sequences identify \(H^1(T,T_T)\) with the degree-six Jacobian ring

\[
R_6(G)=\bigl(S/(G_a,G_b,G_c,G_d,G_u)\bigr)_6.
\]

Under (3B.3.2), \(\rho_C\) is the quotient map on polynomial deformations. The map is surjective, so its Serre transpose is injective on \(H^0(N_{C/T})\). In particular, nonzero curve motion has nonzero Abel–Jacobi derivative. Relation (3B.2.1) places this derivative in the negative sector.

### A canonical residue formula

There is an algebraic normalization of (3B.3.3). Suppose \(g_1,g_2\) have no common zero on \(C\), equivalently the sequence

\[
\mathbf f=(f_1,f_2,h,g_1,g_2)
\]

is regular in \(S\). Its weighted degrees are \((2,2,3,4,4)\), so its Artinian quotient has length 96 and socle degree 9. Let \(\tau_{\mathbf f}\) be its Grothendieck residue, normalized by

\[
\tau_{\mathbf f}\!\left(
\det\frac{\partial(f_1,f_2,h,g_1,g_2)}
{\partial(a,b,c,d,u)}\right)=96.
\]

For a fixed negative sextic \(R\) and a family of contacts on the fixed threefold \(T\), the corresponding one-form on the parameter curve is, up to one overall sign convention,

\[
\boxed{\qquad \eta_R=\tau_{\mathbf f}(R\,d_\Lambda h).\qquad}
\qquad\text{(3B.3.4)}
\]

Here \(d_\Lambda\) differentiates coefficients while holding the ambient coordinates fixed. The degree is \(6+3=9\), as required.

For completeness, on the cover \(g_1\ne0, g_2\ne0\), lifts of \(R|_C\) through (3B.3.1) are \((R/g_1,0,0)\) and \((0,R/g_2,0)\). Their difference represents the obstruction. If \(v=(v_1,v_2,v_3)\), then \(g_1v_1+g_2v_2+kv_3=0\), and its Serre pairing is represented by

\[
\frac{Rv_3}{g_1g_2}\,\theta_C,
\qquad
\theta_C=\operatorname{Res}_C\frac{\Omega_{\mathbb P}}{f_1f_2h}.
\]

The adjunction form \(\theta_C\) has twist \(K_C\otimes\mathcal O_C(-1)\), canceled by the degree-one coefficient. Its Serre trace is exactly the residue above; the actual velocity has \(v_3=-D(h)\). This proves (3B.3.4), including a constant normalization rather than an unspecified function of the parameter.

If \(f_1=\lambda u+q\), eliminating \(u\) contributes \(1/\lambda\) to the four-variable residue. One differentiates \(h\) first and then substitutes \(u=-q/\lambda\); differentiating the already substituted cubic gives a different expression. At nonreduced intersections the Artinian residue remains valid without division by a pointwise Jacobian.

On \(\Lambda\), these forms extend holomorphically because they equal \(\Gamma^*H^{2,1}(T)^-\). They are therefore closed. Once the pullback is injective, the polarization argument in §3B.6 makes \(\Gamma_*\Gamma^*\) invertible on the negative sector. Thus these canonical forms suffice to recover every source after applying that inverse. The identity \(\Gamma_*\eta_R=R\) does not follow without this inversion; the moving-point trace formula still requires its exact differential correction.

## 3B.4 A finite spanning criterion and an exact witness

### The criterion

Weighted residues give

\[
H^{2,1}(T)^-\simeq R_6(G)^-,\qquad \dim R_6(G)^-=48.
\]

For example, at the weighted Fermat equation the ring is
\(\mathbb C[a,b,c,d,u]/(a^5,b^5,c^5,d^5,u^2)\); its negative degree-six monomials have dimensions 32 without \(u\) and 16 with \(u\). The dimensions are constant throughout the smooth invariant family.

Suppose a nonconstant algebraic family of curves on a fixed \(T\) has smooth general member, \(h^0N=h^1N=1\), and a nonzero formal obstruction functional

\[
\ell(t)\in\bigl(R_6(G)^-\bigr)^\vee((t)).
\]

By (3B.3.3), this functional differs from the actual correspondence differential by a common nonzero meromorphic scalar. If its coefficient rows span the 48-dimensional dual, then

\[
\Gamma^*:H^{2,1}(T)^-\hookrightarrow H^{1,0}(\Lambda).
\qquad\text{(3B.4.1)}
\]

Indeed, a constant class in the kernel is killed by every coefficient row. Conjugation and Poincaré duality then give

\[
\Gamma_*:H^1(\Lambda)(-1)\twoheadrightarrow H^3(T)^-.
\qquad\text{(3B.4.2)}
\]

In particular \(g(\Lambda)\ge48\). It is the genus of the parameter curve, not the genus four of its fibers, that appears in this inequality. A nodal member is allowed at \(t=0\); the pairing is applied on the smooth punctured branch.

### A smooth algebraic norm presentation

We construct one smooth threefold and one contact family satisfying the criterion. Put

\[
\begin{aligned}
\Theta(x,y,u)&=2x^6+y^6+30x^4u+30x^2u^2+2u^3,\\
Q_x&=a^2+2ab-u,\qquad Q_y=c^2+2cd-u,\\
G&=\Theta(a,b,u)+\Theta(c,d,u)
       +\frac57Q_x^2Q_y+\frac{10}{7}Q_xQ_y^2.
\end{aligned}
\]

Modulo five, this is \(2a^6+b^6+2c^6+d^6+4u^3\). Its affine cone is smooth away from the origin, proving quasismoothness in characteristic zero by properness of the singular locus. The nonzero \(u^3\)-coefficient excludes the weighted vertex, so \(T=(G=0)\) is smooth.

The square completion

\[
\begin{aligned}
S_x&=(2a+b)^2,\qquad
R_x=(a^2-u)b+(2a+b)^3-2(2a+b)Q_x,\\
S_y&=(2c+d)^2,\qquad
R_y=(c^2-u)d+(2c+d)^3-2(2c+d)Q_y,\\
\Psi(S,Q)&=-2S^3+6S^2Q-3SQ^2-2Q^3
\end{aligned}
\]

gives \(\Theta(a,b,u)=3R_x^2+\Psi(S_x,Q_x)\), and similarly for \(c,d\). Thus

\[
G=3R_x^2+3R_y^2+H(S_x,Q_x,S_y,Q_y),
\quad
H(S,Q,T,V)=\Psi(S,Q)+\Psi(T,V)+\frac57Q^2V+\frac{10}{7}QV^2.
\]

Choose a graph line on this cubic surface by imposing the four coefficient equations

\[
H(S,Q,kS+lQ,nS+mQ)\equiv0.
\]

They have the simple solution

\[
(k,l,n,m)\equiv(2,-3,-2,15)\pmod{37},
\]

where their Jacobian determinant is \(3\). Hensel's lemma gives a unique lift in these residue classes. The invertible Jacobian makes this an isolated algebraic solution, so its coordinates lie in a number field with a place over 37. Adjoin the simple roots \(i^2=-1\), \((\sqrt3)^2=3\), choosing \(i\equiv6\), \(\sqrt3\equiv15\) at that place.

Set \(T_0=kS_x+lQ_x\), \(V_0=nS_x+mQ_x\), and use the cubic-surface construction of §3B.2:

\[
\begin{aligned}
f_1&=S_y-T_0,&f_2&=Q_y-V_0,\\
A&=\sqrt3R_x,&B&=i\sqrt3R_y,\\
g_1&=\frac{H(S_x,Q_x,S_y,Q_y)-H(S_x,Q_x,T_0,Q_y)}{S_y-T_0},\\
g_2&=\frac{H(S_x,Q_x,T_0,Q_y)-H(S_x,Q_x,T_0,V_0)}{Q_y-V_0}.
\end{aligned}
\]

The two divided differences are polynomials, of weighted degree four. These forms satisfy \(G=f_1g_1+f_2g_2+A^2-B^2\) over the number field, with the required characters. The equation \(G\) itself remains the displayed rational polynomial.

The exact verifier `scripts/verify-norm-contact-span.py`, in the repository's [reproduction scripts](https://github.com/hodge-computer/sextics/tree/main/scripts), reconstructs this presentation, its coefficient matrices, tangent direction and formal coefficients from the defining equations. It reads no witness data. It uses lexicographically ordered weighted monomials and exact arithmetic in \(\mathbb F_{37}\). Run it with Python and NumPy:

```sh
python3 scripts/verify-norm-contact-span.py
```

The finite results needed in the proof are:

| Calculation modulo 37 | Result |
| --- | --- |
| \(d\Phi\) at the presentation | rank 70; a 70-minor is 21 |
| Negative degree-six ideal \(I_6^-\), \(I=(f_1,f_2,g_1,g_2,A,B)\) | rank 59; a 59-minor is 4 |
| Singular ideal of the eliminated \((2,3)\) curve, degree six | rank 84 of 84 |
| \((f_1,f_2,A+B,g_1,g_2)\), weighted degree ten | rank 581 of 581 |
| 70 pivot directions, one essential tangent and 19 presentation directions | determinant 10 |
| First 48 obstruction coefficient rows | rank 48; a 48-minor is 17 |

The \(u\)-coefficient of \(f_1\) is \(l\), a unit at the chosen place. Eliminating \(u\) identifies \(C_0=(f_1=f_2=A+B=0)\) with an ordinary \((2,3)\) complete intersection. Its singular ideal consists of those two equations and the six two-by-two Jacobian minors. Containing every degree-six monomial excludes a projective singular point over the algebraic closure. The unit minor proves the same in characteristic zero. Thus \(C_0\) is a smooth connected genus-four curve. The degree-ten calculation makes the five-form ideal supported only at the affine origin, so its generators are a regular sequence. The residue formula of §3B.3 therefore applies on a neighborhood of this contact.

### A smooth branch and its full span

Let \(z_0\) be the 90 coefficients of the lifted presentation. Choose the 70 pivot coordinate directions of the displayed minor, collected in a matrix \(E\), and the first nullspace basis vector \(v\) outside the 19 presentation directions. Construct \(v\) in characteristic zero by fixing the same free coordinates and solving with the unit 70-minor. This gives a genuine tangent with the computed reduction; no modular vector is treated as a literal characteristic-zero tangent. The determinant 10 proves transversality to presentation changes, and reduction in the curve coordinate ring also verifies that the normal velocity is nonzero.

The fixed-equation fiber in this 71-dimensional affine slice is an actual smooth algebraic parameter curve, with local parametrization

\[
z(t)=z_0+tv+Ex(t),\qquad x(0)=x'(0)=0,
\qquad \Phi(z(t))=G.
\]

The algebraic implicit function theorem applies because \(d\Phi(z_0)E\) is invertible. Since \(\Phi\) is quadratic, each coefficient of \(x(t)\) is obtained by applying this one inverse matrix to the quadratic convolution of earlier coefficients. All denominators are units at the chosen place; neither factorials nor the coefficient order are inverted. The recurrence therefore reduces to the computation modulo 37 even beyond order 37. Smoothness of the embedded curves and nonzero normal motion persist near \(t=0\).

We also need a characteristic-zero upper bound on the negative ideal rank. Actual motion gives \(h^0(N_{C/T})\ge1\), and (3B.3.2) gives \(h^1N=h^0N\). The invariant cokernel vanishes because \(d\Phi\) has rank 70. Thus the negative ideal has rank at most 59. Its unit 59-minor proves equality, both at the seed and over the branch function field. In particular \(h^0N=h^1N=1\).

Normalize the left kernel of the \(60\)-by-\(72\) matrix \(I_6^-(t)\) by its unit 59-minor, fixing the remaining coordinate to one. The rank bound makes the resulting \(\ell(t)\) annihilate every ideal column to every order. It also annihilates the fixed Jacobian ideal: differentiating the identity \(G=f_1g_1+f_2g_2+(A+B)(A-B)\) puts every partial derivative of \(G\) in \(I(t)\). The negative degree-six Jacobian part has dimension 12: eight directions multiply the weight-five derivatives by opposite-character linear forms, and four multiply \(G_u\) by negative quadrics.

The verifier checks the fixed equation and all 72 ideal columns through order 50, annihilation of all 12 fixed Jacobian directions, and the nonzero minor of \(\ell_0,\ldots,\ell_{47}\). Unit denominators lift the minor 17 to a nonzero characteristic-zero minor. These rows consequently span the entire dual of \(R_6(G)^-\), proving (3B.4.1).

Finally, use the residue normalization \(\tau_{\mathbf f}(\det\partial\mathbf f)=96\) from §3B.3, where \(\mathbf f=(f_1,f_2,A+B,g_1,g_2)\). The degree-nine Artinian quotient is one-dimensional, and the verifier checks for every negative degree-six monomial \(R\) that

\[
\tau_{\mathbf f}\bigl(R\,\dot h\bigr)=14\ell_0(R)\pmod{37}.
\]

Thus the canonical one-form and the normalized obstruction series differ by a formal unit. Multiplication by that common unit preserves the rank of their first 48 coefficient rows. The criterion gives the surjection (3B.4.2) for this smooth contact family.

## 3B.5 Openness in the full weighted family

The smooth contact family just constructed proves surjectivity on one fixed threefold. To obtain an open family of such threefolds, choose smooth points of its parameter curve. Their obstruction lines span the 48-dimensional dual: otherwise a constant nonzero class would annihilate all of them and hence every formal coefficient. Choose 48 points with independent lines, where \(d\Phi\) has rank 70 and \(h^0N=h^1N=1\).

Let \(\mathcal S\) be the smooth open of the full 70-dimensional space \(S_6^+\), and let \(\mathcal P\) be the open of norm presentations satisfying these rank and smoothness conditions. The map \(\mathcal P\to\mathcal S\) is smooth. The obstruction line is algebraic in the dual of the rank-48 Jacobian bundle. In the 48-fold fiber product of \(\mathcal P\) over \(\mathcal S\), independence of these lines is a Zariski-open condition. This open contains the selected tuple. Smooth morphisms are open, so its image contains a nonempty Zariski open \(\mathcal U\subset\mathcal S\).

For every member of \(\mathcal U\), each selected presentation lies on an actual local Hilbert curve: the fixed-equation fiber has dimension 20, its presentation fibers have dimension 19, and \(h^0N=1\). Complete and normalize these parameter curves. Their combined pullback on \(H^{2,1}(T)^-\) is injective by the 48 independent tangent lines. They may belong to different components; take their finite disjoint union. Conjugation and duality give a surjective curve correspondence onto \(H^3(T)^-\) for every member of \(\mathcal U\).

## 3B.6 Supported projectors and specialization

To apply the supported-projector specialization lemma of [Chapter 3, §3.6](#technical-information/geometric-support), we first produce the required cycle on the square of a divisor. The anti-projector acts on the single primitive degree \(H^3(T)^-\), and the preceding curve correspondences surject onto that degree on a nonempty Zariski open of the parameter space. Its transpose supplies the polarization adjoint.

In this case, replace \(\Gamma\) by \(P^-\circ\Gamma\), choose a \(\sigma\)-stable divisor \(D\) containing its image, and set \(S=\Gamma\circ{}^t\Gamma\). The polarization on \(H^1(\Lambda)(-1)\) and the primitive polarization on \(H^3(T)\) make \({}^t\Gamma\) the adjoint up to a fixed nonzero sign. Surjectivity makes \(S|_{H^3(T)^-}\) invertible. On all other cohomology it is zero. If its rational characteristic polynomial is \(t^m+a_{m-1}t^{m-1}+\cdots+a_0\), then \(a_0\ne0\) and

\[
[P^-]=-\frac{[S^m]+a_{m-1}[S^{m-1}]+\cdots+a_1[S]}{a_0}
\quad\text{in }H^6(T\times T,\mathbb Q).
\]

Every term has a cycle representative supported on \(D\times D\). Equality of all cohomological actions implies equality of classes by Künneth and Poincaré duality. Thus the inverse is a polynomial in an existing algebraic correspondence; no algebraic inverse conjecture is needed.

The family of smooth invariant weighted sextics is connected. The shared specialization lemma now applies: the projector is algebraic throughout the family, and it has a supported representative on a nonempty Zariski open, hence at very general fibers. Proper relative flag Hilbert schemes give such a representative at every smooth member. Fixed Hilbert polynomials keep the limiting support a divisor, and the flag conditions keep the limiting cycle on its square. Acting on cohomology proves the weighted threefold theorem.

This step includes the cyclic covers \(u^3=h(x_0,x_1,y_0,y_1)\). They lie in a special subfamily, so this inclusion uses the all-smooth specialization step rather than an openness assertion within the cyclic subfamily.

## 3B.7 The two-reflection support theorem

**Two-reflection support theorem.** Let \(X=(F=0)\subset\mathbb P^5\) be smooth, with coordinates \((X_0,X_1,s,Y_0,Y_1,t)\). Suppose \(F\) is invariant under

\[
\tau:(X,Y)\mapsto(X,-Y),\qquad
r_s:s\mapsto-s,\qquad r_t:t\mapsto-t.
\]

Then \(H^4(X,\mathbb Q)^\tau\subset N^1H^4(X,\mathbb Q)\).

**Proof.** The reflection theorem of [§3.3](#technical-information/geometric-support/33-reflection-quotients) supports \(H^4(X)^{r_s=+}\) and \(H^4(X)^{r_t=+}\): each quotient is a smooth Fano sextic in \(\mathbb P(1^5,2)\). Its weighted vertex is absent because the relevant pure sixth-power coefficient is nonzero; otherwise the corresponding coordinate-axis point would be singular on \(X\). The branch divisor is smooth and the quotient action is a reflection in its normal direction.

It remains to support the simultaneous character

\[
V_{--}=H^4(X)^{\tau=+,\ r_s=-,\ r_t=-}.
\]

Put \(\beta=r_sr_t\) and \(\sigma=\tau r_t\). On this subspace \(\beta=+\) and \(\sigma=-\). The latter involution negates precisely \(Y_0,Y_1\), fixing \(X_0,X_1,s,t\).

Write \(x=(X_0,X_1,Y_0,Y_1)\). The pencil \([s:t]\) has base

\[
S=X\cap(s=t=0)=\{h_6(x)=0\}\subset\mathbb P^3.
\]

Both binary derivatives vanish there by separate evenness. A singular point of \(S\) would therefore be singular on \(X\), so \(S\) is smooth. Blow up \(S\) to obtain a morphism to \(\mathbb P^1\). Bertini gives smooth general fibers

\[
V_\lambda=\{F(x,s,\lambda s)=0\}\subset\mathbb P^4.
\]

All pencil members are smooth along their base surface, where the core gradient is nonzero. Blowing up restricts to an isomorphism on a smooth fiber because \(S\) is a Cartier divisor in it.

The involution \(\beta\) fixes \(\lambda\) and acts on \(V_\lambda\) by \(s\mapsto-s\). With \(w=s^2\), its quotient is

\[
T_\lambda:
h_6(x)+w h_4(x,\lambda)+w^2h_2(x,\lambda)+w^3h_0(\lambda)=0
\subset\mathbb P(1,1,1,1,2).
\]

Each core coefficient is invariant under \(\sigma\). The binary restriction \(F(0,s,t)\) is nonzero and squarefree: separate evenness forces every core monomial degree to be even, so all core first derivatives vanish on the binary line; a zero restriction or a multiple root would make \(X\) singular. Excluding its roots makes \(h_0(\lambda)\ne0\), so the weighted vertex is absent. The only remaining fixed locus of \(\beta\) in a fiber is the smooth branch surface \(s=0\), where it is a reflection. Thus, after removing finitely many parameters and one affine-chart boundary, the quotients form a smooth projective family \(p:\mathcal T\to U\) of the weighted threefolds just treated.

The relative support lemma of [Chapter 3, §3.6](#technical-information/geometric-support) now applies. Its two requirements are

\[
(R^jp_*\mathbb Q)^-=0\quad(j\ne3),
\qquad
P^-_\lambda\text{ has a representative supported on }D_\lambda\times D_\lambda.
\]

The second is the weighted threefold theorem, including special members. For the first, finite quotient cohomology identifies \(H^j(T_\lambda)\) with the \(\beta\)-invariants in \(H^j(V_\lambda)\). Ordinary weak Lefschetz and duality on the smooth sextic \(V_\lambda\) make all its nonmiddle cohomology invariant under \(\sigma\).

The shared lemma therefore supports

\[
H^4(\mathcal T)^-=H^1(U,(R^3p_*\mathbb Q)^-)
\]

on a horizontal divisor. Its spread and finite-trace argument supplies the relative cycle; no choice of a continuously varying divisor is assumed here.

For \(\alpha\in V_{--}\), pull back to the blowup and restrict over \(U\). Its \(\beta\)-invariance identifies it with the pullback of a class on the finite quotient \(\mathcal T\), and its \(\sigma\)-character is negative. Hence it vanishes off the inverse image of the supporting divisor. Taking closures and adding the omitted fibers and exceptional divisor supports the pullback on the blowup. Proper birational pushforward supports \(\alpha\) on \(X\). Together with the two Fano-supported sectors, this exhausts \(H^4(X)^\tau\). ∎

## 3B.8 Scope, examples and certificates

The theorem covers the entire smooth locus of a 104-coefficient linear family, of projective dimension 103 before changes of coordinates. The spaces of core forms of degrees \(6,4,2,0\), even in \((Y_0,Y_1)\), have dimensions \(44,19,6,1\). The powers \(s^{2a}t^{2b}\) with \(a+b=m\) give \(m+1\) choices, so the coefficient count is

\[
44+2\cdot19+3\cdot6+4\cdot1=104.
\]

The coordinate orbit and comparison with other supported families are discussed in [Chapter 4](#technical-information/known-locus). The Fano quotient results remain part of the theorem: they supply the sectors with either reflection positive, while the weighted family supplies the simultaneous negative sector.

The two-reflection and [quadratic-net families](#technical-information/quadratic-nets) are incomparable, even after block-linear changes. In the bidegree-\((4,2)\) part of a general two-reflection equation, the quadrics appearing as coefficients of \(X\)-quartics span the four-dimensional space
\[
\langle Y_0^2,Y_0Y_1,Y_1^2,t^2\rangle.
\]
A presentation through three \(Y\)-quadrics would bound this rank by three; the mirrored bidegree-\((2,4)\) calculation excludes an \(X\)-quadric presentation. Conversely, the 127-dimensional saturated net family cannot be contained in the 111-dimensional saturated two-reflection family. These dimensions are proved in Chapter 4.

Two immediate applications illustrate the coefficient scope.

- If \(F=h(X_0,X_1,Y_0,Y_1)+b(s,t)\), with \(h\) even in \((Y_0,Y_1)\) and \(b\) even in \(t\), homogeneity makes \(b\) even in \(s\). Thus every smooth member of this \(4+2\) split family is covered, including a sum of two arbitrary same-parity binary sextics and a separately even binary sextic. That binary-block subfamily also admits the torsion-contact construction of [Chapter 2A](#technical-information/binary-blocks), which gives explicit fields through two general Wronskian spanning theorems.
- If an even sextic is invariant under an \(X\)-coordinate transposition and an independent \(Y\)-coordinate transposition, their sums and differences diagonalize them over \(\mathbb Q\) to the required reflections. Block-symmetric even sextics therefore satisfy the theorem after such a coordinate change.

Over a characteristic-zero field, the support-to-certificate equivalence and coefficient descent of [Chapter 1](#technical-information/certificates), followed by the higher-pole reduction of [Chapter 3, §3.5](#technical-information/geometric-support), give legal certificates at every positive pole order.

The two extra reflections are essential hypotheses of this proof. Global \(Y\)-evenness alone does not provide either the weighted quotient fibers or their two-minus core involution.

## 3B.9 Paired signs

The proof of the two-reflection theorem uses the two reflections only through the involutions \(\beta=r_sr_t\) and \(\sigma=\tau r_t\), each of which negates a pair of coordinates. The same proof therefore applies to three paired signs.

**Paired-sign proposition.** Let \(X=(F=0)\subset\mathbb P^5\) be a smooth sextic and \(\mathbb C^6=P_0\oplus P_1\oplus P_2\) a decomposition into coordinate planes. Suppose \(F\) is invariant under the three involutions \(s_i\) acting by \(-1\) on \(P_i\) and by \(+1\) on the other two planes. Let \(\pi_P\) be the averaging projector of the group \(P=\{1,s_0,s_1,s_2\}\subset PGL_6\). Then

\[
(1-\pi_P)\,H^4(X,\mathbb Q)\subset N^1H^4(X,\mathbb Q).
\]

**Proof.** A nontrivial character of \(P\) is \(+1\) on exactly one \(s_i\). Call that involution \(\beta\), let \(\sigma\) be another one, write \((s,t)\) for the coordinates of the plane of \(\beta\) and \(x\) for the remaining four. On the corresponding isotypic part \(\beta=+\) and \(\sigma=-\), as for \(V_{--}\) in §3B.7, and each step of that proof holds with evenness in the pair \((s,t)\) and in each of the other two planes:

- on \(X\cap\{s=t=0\}\) the derivatives \(\partial_sF,\partial_tF\) vanish, being odd in \((s,t)\), so this surface is smooth;
- every monomial has even degree in each plane, so the four core derivatives vanish on the line \(x=0\); hence \(F(0,s,t)\) is nonzero and squarefree, and the weighted vertex is absent for general \(\lambda=t/s\);
- \(\beta\) fixes \(\lambda\) and acts on \(V_\lambda=X\cap\{t=\lambda s\}\) as the reflection \(s\mapsto-s\), so \(T_\lambda=V_\lambda/\beta\) is a quasismooth sextic in \(\mathbb P(1,1,1,1,2)\) with \(\sigma\)-invariant equation, and \(\sigma\) negates exactly two of its four coordinates of weight one.

The weighted threefold theorem and the relative support lemma apply as before. ∎

No further involution is assumed, and \(H^{4,0}(X)\) is \(P\)-invariant. When the planes are the pairs \((X_i,Y_i)\), the \(Y\)-even invariant sextics form the 74-coefficient family of [Chapter 4, §4.6](#technical-information/known-locus). On its smooth members the proposition supports the part of type \((150,636,150)\) of the \(Y\)-even primitive cohomology, and leaves the \(P\)-invariant part, of type \((58,230,58)\). A \(Y\)-odd numerator is served when it has odd degree in at least one pair \((X_i,Y_i)\). [Chapter 3D](#technical-information/hodge-loci) supports part of the remaining sector in the presence of an order-three symmetry.
