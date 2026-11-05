# 2. Explicit constructions: transport, contact, and algebraic cycles

[Previous: certificates](#technical-information/certificates) · [Contents](#technical-information/introduction) · [Next: binary blocks](#technical-information/binary-blocks)

The useful common structure behind the explicit certificates is a transport identity. A change of variables converts \(F\) into an equation with accessible geometry; a rational field on that equation is pulled back by cofactors. Its Jacobian determines the target. Geometry becomes decisive when it proves that the available targets span the required space.

We first work at \(q=1\). An Euler-normalized strict certificate satisfies \(v(F)=A\) and \(\operatorname{div} v=0\). After writing \(v=N/D\), these are \(N(F)=A\cdot D\) and \(D\cdot \operatorname{div} N-N(D)=0\). The residue constructions in §§2.7–2.9 also permit a nonzero quotient in the cleared certificate equation. Every construction requires the homogeneity, involution parity, and denominator legality of [Chapter 1](#technical-information/certificates). Finite sums and normalized field traces preserve the identities.

## 2.1 Cofactor transport

Let \(\Phi \) be a polynomial or rational map between affine spaces of the same dimension. Put \(J=d\Phi \) and \(\Delta =\operatorname{det} J\). For a target-space rational field \(w\) and a target function \(G\), define

\[
\begin{gathered}
V = \operatorname{adj}(J)\cdot w(\Phi ).\\
V(G(\Phi )) = \Delta\cdot w(G)(\Phi ),\\
\operatorname{div} V = \Delta\cdot (\operatorname{div} w)(\Phi ).
\end{gathered}
\]

To prove both identities, let \(\Theta \) and \(\Theta _t\) denote the source and target volume forms. Expansion by minors gives \(\Phi^{*}(\iota _w\Theta _t)=\iota _V\Theta \). Taking exterior derivatives gives \(\operatorname{div} V=\Delta\cdot (\operatorname{div} w)(\Phi )\). Independently, \(J\cdot\operatorname{adj}(J)=\Delta\cdot I\) and the chain rule give the identity on \(G\). This argument uses polynomial identities among derivatives and therefore remains valid for rational \(\Phi \) on its domain. Every coordinate is differentiated, including parameters written as ratios. Thus a divergence-free field serving \(B\) downstairs serves \(\Delta\cdot B(\Phi )\) upstairs. The determinant is the transformation law for the differential-form density.

A useful polynomial constructor makes \(G\) spectrally simple. Give \(\Phi _{i}\) positive degrees \(m_{i}\), let \(G\) have weighted degree six, and let \(w\) be a polynomial derivation of weighted degree zero. Choose a polynomial density \(b\) of weight \(12-\sum m_{i}\). Suppose, for constants \(\mu ,\nu \),

\[
\begin{gathered}
D_{0} = w(G),\\
w(D_{0}) = (\mu +\nu )\cdot D_{0}-\mu\cdot\nu\cdot G,\\
\operatorname{div}(b\cdot w) = (\mu +\nu )\cdot b.
\end{gathered}
\]

Then

\[
\begin{gathered}
F = G(\Phi ),       A = b(\Phi )\cdot\Delta,\\
D = D_{0}(\Phi ),     N = \operatorname{adj}(d\Phi )\cdot(b\cdot w)(\Phi ),\\
N(F) = A\cdot D,\\
D\cdot \operatorname{div} N-N(D) = \mu\cdot\nu\cdot A\cdot F.
\end{gathered}
\]

Indeed, cofactor transport gives \(N(F)=\Delta\cdot b(\Phi )\cdot w(G)(\Phi )=A\cdot D, \operatorname{div} N=(\mu +\nu )\cdot A\), and \(N(D)=A\cdot((\mu +\nu )\cdot D-\mu\cdot\nu\cdot F)\). Subtraction proves the displayed \(E_{2}\) identity, hence the \(q=1\) certificate assertion. The degrees are \(\operatorname{deg} A=6, \operatorname{deg} D=6\) and \(\operatorname{deg} N_{i}=7\): the \(i\)-th target coordinate contributes \(m_{i}\) to \(w\), while its adjugate column has source degree \(\sum m_{j}-m_{i}-5\). Legality still requires \(D\ne 0\) and \(\operatorname{gcd}(D,F)=1\).

There is also a homogeneous nilpotent branch. If \(w\) has weighted degree \(e, w^{2}(G)=0\) and \(\operatorname{div}(b\cdot w)=0\), the same calculation gives \(N(F)=A\cdot D\) and \(\operatorname{div} N=N(D)=0\). Its denominator has degree \(6+e\) and numerator degree \(7+e\). When \(e\ne 0\), a constant-spectrum quadratic equation for \(w\) on \(G\) can have only the nilpotent form: its three terms have distinct weights unless their nonhomogeneous coefficients vanish.

These spectral hypotheses are sufficient conditions for explicit fields. They are not a characterization of certificates. For nonlinear polynomial \(\Phi \), the determinant-density targets have a broader finite weighted-Fano interpretation without a spectral condition, proved in [Chapter 3](#technical-information/geometric-support/34-nonlinear-polynomial-piola-maps-are-finite-fano-maps). Rational maps can introduce additional boundary terms. The scope and necessity questions belong to [Chapter 4](#technical-information/known-locus).

## 2.2 Euler and Nambu fields

Subset Euler is the simplest spectral instance. Write \(E_I=\sum _{i\in I} Z_{i}\partial _{i}\). If \(E_I^{2}(F)=6\cdot E_I(F)\), and a target monomial satisfies \(\operatorname{deg}_I A+|I|=6\), then

\[
\begin{gathered}
v = A\cdot E_I / E_I(F)
\end{gathered}
\]

is strict, provided its denominator is legal. Its value on \(F\) is \(A\), while the product rule gives

\[
\operatorname{div}(A\cdot E_I/E_I(F)) = A[\operatorname{deg}_I A+|I|-E_I^{2}(F)/E_I(F)]/E_I(F)=0.
\]

The same calculation proves that \(A\cdot E_I/[qE_I(F)]\) works at any \(q\) under the stated subset condition. Finite sums serve the linear span of these targets; a sum need not itself be a single spectral atom.

Nambu fields provide the contact version. Choose homogeneous \(P,h_{1},\ldots ,h_{4}\) with \(\sum (\operatorname{deg} h_{i}-1)=2\), and define \(W\) by

\[
\begin{gathered}
\iota _W(dZ_{0}\wedge \cdots \wedge dZ_{5}) = dP\wedge dh_{1}\wedge \cdots \wedge dh_{4}.
\end{gathered}
\]

The defining five-form is closed, which proves \(\operatorname{div} W=0\). Wedging it with the differential of any of its five first integrals gives zero, so \(W\) annihilates each of them. Consequently

\[
\begin{gathered}
F = \Gamma (h_{1},\ldots ,h_{4})+P\cdot K,      A = W(K)
\end{gathered}
\]

gives the strict field \(W/P: W(F)=P\cdot W(K)\), and \(\operatorname{div}(W/P)=0\) because \(W(P)=0\). Its degree is one since \(\operatorname{deg} W=\operatorname{deg} P-1+\sum (\operatorname{deg} h_{i}-1)=\operatorname{deg} P+1\). It is cofactor transport through \(\Phi =(K,P,h_{1},\ldots ,h_{4})\), with target equation \(t_{0}\cdot t_{1}+\Gamma \) and target derivation \(\partial _{0}\). Rational first integrals obey exactly the same exterior-calculus proof, but polynomiality of \(A\) and cancellation of unwanted poles must be checked.

The determinant target has an adjunction interpretation. Suppose \(\operatorname{deg} K>0\) and \(E=V(P,h_{1},\ldots ,h_{4})\subset \mathbb P^{5}\) is a zero-dimensional complete intersection. The five equation degrees sum to \(\deg(P)+6\). Twist the Koszul resolution by \(\deg(P)\): its last term is \(\mathcal O(-6)\), with one-dimensional \(H^{5}\), while every preceding term has no \(H^{5}\) and all intermediate projective-space cohomology vanishes. Hence restriction of degree-\(\deg(P)\) polynomials to \(H^{0}(E,\mathcal O_E(\deg(P)))\) has one-dimensional cokernel.

The four positive degrees \(\operatorname{deg} h_{i}\) sum to six, so \(\Gamma \) has no linear term in the \(h_{i}\). Thus \(dF=K dP\) on \(E\) and smoothness forces \(K\) to be a unit there. Choose an affine chart containing \(E\). Euler column reduction in \(\operatorname{det} d(K,P,h_{1},\ldots ,h_{4})\) gives \((A/K)|_E=(\operatorname{deg} K)J_E\), where \(J_E\) is the affine complete-intersection Jacobian. The residue functional representing the Koszul cokernel has \(\operatorname{Res}(J_E)=\operatorname{length}(E)\): at a reduced point its local value is one, and the same identity follows at a multiple point from the local algebra trace. It annihilates polynomial restrictions of degree \(\deg(P)\) by the preceding Koszul calculation. Therefore \(A/K\) has nonzero residue and spans the missing adjoint direction. This proves that the contact selects a specific target through a residue pairing; it does not serve an arbitrary prescribed \(A\).

## 2.3 Perfect-power contact and its source surface

For a split ternary equation \(F=P(U)+Q(V)\), first suppose \(D,H,K\) are homogeneous polynomials with

\[
\begin{gathered}
Q = cH^{m}+D\cdot K,      m\in \{2,3,6\},      c\ne 0,\\
k = \operatorname{deg} H = 6/m,\\
W = \nabla D\times \nabla H.
\end{gathered}
\]

Take \(B(U,T)\) of weighted degree \(3-k\), with weights \((1,1,1,k)\). Then

\[
\begin{gathered}
v = B(U,H)W/D,      A = B(U,H)W(K)
\end{gathered}
\]

is strict: \(W(D)=W(H)=\operatorname{div} W=0\) and \(W(Q)=D\cdot W(K)\). The support \(V(F,D)\) maps to the cyclic surface

\[
\begin{gathered}
S = \{P(U)+cT^{m}=0\} \subset  \mathbb P(1,1,1,k),      T=H(V).
\end{gathered}
\]

Smoothness of the separated \(F\) implies smoothness of \(P=0\): a singular point of \(P\), with \(V=0\), would be singular on \(F\). The cyclic surface \(S\) is smooth by the chain rule and misses the singular vertex of its weighted ambient space. Weighted adjunction gives \(K_S=\mathcal O_S(6-3-k)=\mathcal O_S(3-k)\). In these degrees its sections are exactly the weighted polynomials \(B\), since the defining equation has larger degree. Thus its holomorphic two-forms are residues with numerator \(B\): one constant direction for \(m=2\), three passive linear directions for \(m=3\), and ten quadratic directions for \(m=6\). This explains the allowed multiplier in the field.

The identification of the source form follows from the same computation, not merely adjunction. Namely \(\iota _W \mathrm{vol}_V=dD\wedge dH\), so the residue of \(\iota _W \mathrm{vol}_V/D\) along a reduced component of \(D\) is its multiplicity times \(dH\). In the six-dimensional volume form, multiply this identity by the passive volume form and \(B\), then take the residue along \(F\). On \(D\), substitute \(F=P+cH^{m}\) and \(T=H\); contracting by the homogeneous Euler field gives precisely \(\operatorname{Res}_S(B\cdot \Omega _{\mathrm{weighted}}/(P+cT^{m}))\), up to orientation and the stated multiplicities. Resolve the graph of this rational substitution. The pulled-back source two-form is holomorphic, and the residue boundary map for the supporting divisor is its Gysin map. The displayed exact field identity identifies its image with the class of \(A\); possible boundary components are retained on the graph. Nonvanishing still requires checking that target class.

The identity also has a rational version. If \(H\) and \(K\) are rational homogeneous functions with \(Q=cH^{m}+D\cdot K\), the same derivatives give \(v(F)=A\) and \(\operatorname{div} v=0\) in the function field. This is a certificate only when \(A\) is the required polynomial and all remaining poles are legal. A root \(H\) on the normalization of \(D\) need not descend to an ambient polynomial: distinct branches of a node can have distinct root values. Enforcing an ambient polynomial root would exclude such contacts. Conversely, permitting rational roots without checking their extra poles would admit many false candidates.

The relevant geometric distinction is between a contact relation and the class of its lift to the cyclic surface. An ambient divisor has invariant class; a correspondence applied to this class can vanish in the nontrivial character required by the target. A useful model is a smooth cubic surface \(S\) with hyperplane class \(H_S\) and a twisted cubic \(\Gamma \subset S\). Adjunction gives \(\Gamma ^{2}=1\) because \(\Gamma \) is rational, \(K_S=-H_S\), and \(H_S\cdot \Gamma =3\). Consequently \(r=[\Gamma ]-H_S\) satisfies \(r^{2}=-2\) and \(r\cdot H_S=0\). These are root classes in the negative-definite \(E_{6}\) lattice \(H_S^\perp \). If \(S\to \mathbb P^{2}\) is a cyclic triple-plane quotient, its invariant rational Picard space is generated by \(H_S; \Gamma \) cannot have invariant class, since an invariant class of degree three would have square three. Movement within a linear system preserves its cycle class, although it changes the projected denominator.

This model explains why line constructions and normalized nodal contacts can encode the same Picard geometry. A rational Nambu field may need a second divergence-free field to cancel its poles away from the intended denominator. Such cancellation is an additional rational-function identity, not a consequence of the perfect-power relation.

## 2.4 A complete target map on cubic surfaces

**Cubic-surface theorem.** Let \(G\) be a homogeneous cubic in four variables over a characteristic-zero field \(K\), with smooth projective zero set. For every \(q\ge 1\) and homogeneous \(B\) of degree \(3\cdot q-1\), there is a rational field \(w_q\), with components of degree \(3\cdot q-3\), satisfying \(q w_q(G)=B\) and \(\operatorname{div} w_q=0\). One common denominator of active degree 45 suffices for every \(B\) and \(q\), and is coprime to \(G\).

We use the following classical geometric input. Over an algebraic closure, a smooth cubic surface is the blowup of \(\mathbb P^{2}\) at six points in general position; in particular it has six mutually skew lines, Picard rank seven, and 27 lines in total. Its 45 tritangent planes each cut three distinct lines, and five pass through any given line. These statements include special smooth cubics; see [Huybrechts, Chapter 4, §3](https://www.math.uni-bonn.de/people/huybrech/Notes.pdf). The residue realization needed below is the specialization of [Villaflor Loyola, Theorem 1.1](https://arxiv.org/pdf/1812.03964): if \(G=\ell _{1}Q_{1}+\ell _{2}Q_{2}\) and \(L=V(\ell _{1},\ell _{2})\), then \(\operatorname{Res}(\operatorname{det} d(\ell _{1},Q_{1},\ell _{2},Q_{2})\Omega /G^{2})\) is a fixed nonzero scalar times \(H_S-3[L]\), the scalar depending only on the residue normalization. Together with Griffiths' residue description \(R(G)_{2}\cong H^{2}(S)_{\mathrm{prim}}\), this identifies explicit determinant polynomials with primitive line classes. The remainder of the theorem follows from the calculations below.

Choose a line \(L\) given by \(\ell _{1}=\ell _{2}=0\) and write \(G=\ell _{1}Q_{1}+\ell _{2}Q_{2}\). Cofactor transport through \(\Phi _L=(\ell _{1},Q_{1},\ell _{2},Q_{2})\) gives

\[
\begin{gathered}
J_L = \operatorname{det}(d\Phi _L),\\
w_L = \operatorname{adj}(d\Phi _L)e_{2}/\ell _{1},\\
w_L(G)=J_L,      \operatorname{div} w_L=0,
\end{gathered}
\]

where \(e_{2}\) is the second coordinate vector. The map has output weights (1,2,1,2). Downstairs \(G\) becomes \(a\cdot b+c\cdot d\), and \((1/a)\partial _b\) has value one on this polynomial and zero divergence. The cofactor identity proves both displayed equations, including the derivative of \(1/\ell _{1}\). Equivalently, the second adjugate column annihilates \(\ell _{1}\) and has zero divergence. Thus \(J_L\) is quadratic and \(w_L\) has degree zero.

The four partial derivatives \(G_{i}\) are independent: a constant linear relation would make \(G\) independent of one linear coordinate and its projective hypersurface a singular cone. They account for four of the ten quadratic directions. For six mutually skew lines, the classes \(r_{i}=[L_{i}]-H_S/3\) have intersection matrix \(-I_{6}-11^{T}/3\), because \(L_{i}^{2}=-1, L_{i}\cdot L_{j}=0\) for \(i\ne j\), and \(H_S\cdot L_{i}=1\). Its eigenvalues are \(-3\) and five copies of \(-1\), so its determinant is three. The \(r_{i}\) are independent. The cited residue formula therefore proves that their six \(J_L\) classes form a basis of the six-dimensional quadratic Jacobian quotient. A \(10\times 10\) linear solve expresses \(B\) as \(\sum a_{i}G_{i}+\sum b_{j}J_{L_{j}}\); the field \(\sum a_{i}\partial _{i}+\sum b_{j}\cdot w_{L_{j}}\) serves \(B\) strictly.

Find the lines over a finite extension \(E/K\) and descend by

\[
\begin{gathered}
\overline{w} = \operatorname{Tr}_{E/K}(w)/[E:K].
\end{gathered}
\]

All line coordinates and the coefficients \(a_i,b_j\) lie in some finite extension \(E/K\). Its elements are constants for the four active derivatives, so these commute with normalized trace. Hence \(\overline{w}(G)=B\) and \(\operatorname{div} \overline{w}=0\). Multiplication matrices compute the trace without root approximation: for a component \(N/D\), its normalized trace is \(\operatorname{tr}(\operatorname{adj}(M_D)M_N)/([E:K]\operatorname{det}M_D)\). Every conjugate denominator is a product of linear equations, so cannot contain the geometrically irreducible cubic \(G\). This proves both descent and legality at \(q=1\).

Higher \(q\) requires no new surface cycles. The four quadratic partial derivatives have only the origin as common zero, so form a regular sequence in \(K[u_{0},\ldots ,u_{3}]\). Their quotient has Hilbert series \((1+t)^{4}\), obtained from its Koszul resolution; in particular it vanishes above degree four. For \(\operatorname{deg} B=3\cdot q-1\) and \(q\ge 2\), ordinary polynomial linear algebra therefore gives \(B=\sum b_{i}G_{i}\), with \(\operatorname{deg} b_{i}=3\cdot q-3\). Put \(c=\operatorname{div} b\). Inductively choose \(w\) with \((q-1)w(G)=c\) and \(\operatorname{div} w=0\), and define

\[
\begin{gathered}
v_q = [b+G\cdot w-c\cdot E_{4}/(3(q-1))]/q
\end{gathered}
\]

The two added terms cancel on \(G\) because \(E_{4}(G)=3\cdot G\). For divergence, \(\operatorname{div} b=c, \operatorname{div}(G\cdot w)=c/(q-1)\), and \(\operatorname{div}(c\cdot E_4)=(\operatorname{deg}c+4)c=3\cdot qc\). Their sum is zero. The component degree is \(3\cdot q-3\), and the recursion introduces no new active denominator.

To obtain one denominator over \(K\), choose \(p\in K^{4}\) outside the 45 tritangent planes and normalize each plane equation \(\ell \) by \(\ell (p)=1\). Such \(p\) exists because \(K\) is infinite. Galois permutes the normalized equations, so \(T=\prod \ell \) lies in \(K[u]\) and has degree 45. For each chosen line use a containing tritangent plane as \(\ell _{1}\) in its cofactor field. Its denominator divides \(T\); so do their sum and normalized coefficient trace. The recursion retains \(T\) for every \(q\), and its numerator has degree \(45+3\cdot q-3\). Since \(T\) is a product of linear forms over an algebraic closure, \(\operatorname{gcd}(T,G)=1\). This completes the theorem, including its common-denominator assertion.

### Finite-algebra realization of line contact

The line calculation has an algebraic form that does not require selecting algebraic roots. Let \(R\) be a characteristic-zero domain of passive coefficients and let \(E\) be a commutative finite free \(R\)-algebra of rank \(m\). Active differentiation fixes \(E\). Suppose a line-contact field \(n/\ell\) over \(E\) satisfies

\[
n(G)=\ell J,\qquad \operatorname{div}(n/\ell)=0,
\]

where \(\ell\) and the components of \(n\) are linear in the four active variables and \(J\) is quadratic. For multiplication matrices in an \(R\)-basis of \(E\), put

\[
D=\det M_\ell,\qquad
N_i=\lambda\bigl(M_{n_i}\operatorname{adj}(M_\ell)e\bigr),
\]

where \(e\) represents the unit of \(E\) and \(\lambda:E\to R\) is any \(R\)-linear functional, extended over the active polynomial ring. Assume \(D\ne0\). The adjugate identity makes \(\ell\) invertible after inverting \(D\), and gives \(N_i/D=\lambda(n_i/\ell)\). Active derivatives commute with \(\lambda\), so

\[
N(G)=D\lambda(J),\qquad D\operatorname{div}N-N(D)=0.
\]

Both \(D\) and \(N_i\) have active degree \(m\). This is a coefficient-functional construction; \(\lambda\) need not be the trace. It works in a finite free algebra even when its defining polynomial is reducible or has repeated roots. Coprimality of \(D\) with \(G\) remains a separate obligation. For a line algebra on a smooth cubic, the norm is a product of linear plane equations over an algebraic closure, which supplies that obligation; after a rational substitution, the physical denominator must also be checked.

Together with the four constant fields serving \(G_i\), selected functionals of \(J\) give a finite matrix of quadratic sources. An invertible ten-by-ten minor makes the construction serve every quadratic. This can be certified without writing its inverse as a huge rational expression. Localize the passive coefficient ring at polynomials nonzero at one specified fiber; an exactly nonzero specialized determinant is then a unit. The line-coordinate denominators and the source matrix are handled in the same way. The resulting formulas hold over that localization and its fraction field, not at every specialization indiscriminately. A zero minor at a different fiber means that this chart fails, not that the target has no certificate.

This realization underlies `HeadOfNaps`'s [quadric-contact](#case/quadric-contact-broken) and [endpoint-cubic](#case/holdout-q2) constructions. In the latter, a monic degree-27 line algebra and six coefficient functionals, together with the four gradients, span all ten quadratic sources. The concrete algebra replaces the need to formalize the general geometric line-class argument; the determinant, source identities, and denominator legality can instead be checked directly.

## 2.5 From sextics to cubic surfaces

Suppose \(F\) is coordinatewise-even. For a monomial \(A\), choose coordinates \(x\) from \(X\) and \(y\) from \(Y\) with odd exponents; write the remaining \(X\) coordinates as \((a,b)\) and the remaining \(Y\) coordinates as \((c,d)\). Introduce passive ratios and active squares:

\[
\begin{gathered}
\alpha =b/a,      \beta =d/c,\\
\Psi =(x^{2},a^{2},\alpha ,y^{2},c^{2},\beta ),      \operatorname{det}(d\Psi )=16\cdot x\cdot y.
\end{gathered}
\]

In this coordinate order the determinant has the displayed sign; another ordering contributes its permutation sign. For example, each triple map \((x,a,b)\mapsto (x^{2},a^{2},b/a)\) has Jacobian \(4\cdot x\), giving 16xy in six variables. Write \(F=f(Z_{0}^{2},\ldots ,Z_{5}^{2})\). Over \(K=k(\alpha ,\beta )\), it becomes

\[
\begin{gathered}
G(u,s,w,t)=f(u,s,\alpha ^{2}s,w,t,\beta ^{2}t),
\end{gathered}
\]

with coordinates in the corresponding physical order. It is homogeneous cubic in \((u,s,w,t)\). At \(\alpha =\beta =0\), a singular point of this cubic would lift through square roots to a singular point of \(F\), with \(b=d=0\). All omitted derivatives vanish because \(F\) is even in those omitted coordinates. Therefore this specialization is smooth, and so is the cubic over \(K\).

If \(A=x^{r}\cdot a^{m}\cdot b^{n}\cdot y^{j}\cdot c^{h}d^{l}\), its globally odd \(Y\) degree and even total degree ensure that \(j,r\) are odd and \(m+n,h+l\) are even after the selected odd pair has been chosen. Hence its transformed density is

\[
\begin{gathered}
B=\alpha ^{n}\cdot \beta ^{l}u^{(r-1)/2}\cdot s^{(m+n)/2}\cdot w^{(j-1)/2}\cdot t^{(h+l)/2}/16,
\end{gathered}
\]

with the permutation sign inserted if necessary. This is a polynomial of active degree \(3\cdot q-1\). Apply the cubic theorem, append zero passive components in the order of \(\Psi \), and put \(v=\operatorname{adj}(d\Psi )w_q(\Psi )\). Cofactor transport gives \(q\cdot v(F)=A\) and \(\operatorname{div} v=0\), with physical component degree \(6\cdot q-5\).

The target coordinates \(\Psi \) are globally \(Y\)-even. If \(S=\operatorname{diag}(1,1,1,-1,-1,-1)\), differentiating \(\Psi (SZ)=\Psi (Z)\) gives \(\operatorname{adj}(d\Psi )(SZ)=-S \operatorname{adj}(d\Psi )(Z)\). Thus \(v(SZ)=-Sv(Z)\), exactly the required component parities. A homogeneous common denominator can be made \(Y\)-even by multiplication with its involution transform.

Legality follows on the ratio chart from the finite square map: its restriction maps the irreducible hypersurface \(F=0\) dominantly onto \(G=0\). Consequently a denominator coprime to \(G\) cannot pull back to a multiple of \(F\). A passive coefficient pole cannot contain \(F\) either, since the map from \(F\) to the passive parameter plane is dominant; nor can either ratio-chart boundary contain the smooth irreducible hypersurface \(F\). Clearing all these denominators therefore gives \(\operatorname{gcd}(D,F)=1\). Finite sums serve every allowed polynomial \(A\). This proves the all-\(q\), all-target theorem on every smooth coordinatewise-even sextic, and constant block-linear coordinate changes preserve the construction.

**Two-reflection extension.** Suppose \(F\) is globally \(Y\)-even and even separately in one \(X\) coordinate \(x\) and one \(Y\) coordinate \(y\). The same construction serves every allowed \(A\) odd in \(x\) and \(y\). Indeed, the remaining \(X\) pair is jointly even by total degree, and the remaining \(Y\) pair is jointly even by global \(Y\)-parity. Thus the ratio substitution still gives a polynomial cubic and polynomial density.

Here the coordinate-face smoothness argument need not apply, but the generic cubic is smooth nonetheless. If it had a singular point over an algebraic closure of \(k(\alpha ,\beta )\), choose an affine projective chart there and differentiate \(G=0\) with respect to \(\alpha ,\beta \). Characteristic zero lets the derivations extend to this algebraic field. All active derivatives vanish, so \(G_\alpha =G_\beta =0\) at the point. Lift it by square roots. When \(a\ne 0\), the identities

\[
\begin{gathered}
F_b=G_\alpha /a,       F_a=2\cdot aG_s-\alpha G_\alpha /a
\end{gathered}
\]

show that both derivatives vanish; when \(a=0\), also \(b=0\) and joint evenness gives the same conclusion. The pair \((c,d)\) is identical. Finally \(F_x=2\cdot xG_u\) and \(F_y=2\cdot yG_w\) vanish. This contradicts smoothness of \(F\). The previous transport and legality proof now applies without change. This is a partial-target theorem on the larger family: global \(Y\)-evenness alone does not supply the selected reflections.

The degree-45 common denominator lies over \(K\). Clearing passive coefficients contributes physical poles, so it is not a numerical degree bound in the six original coordinates. Nevertheless one finite physical support serves every \(q\) for a fixed \(F\) and pair: fix the quadratic line basis and decompositions of the 56 degree-five active monomials into the partial derivatives. Multiplying these decompositions by monomials supplies every higher-degree decomposition used in the recursion. Only their finitely many passive coefficient poles, the line poles, and the chart boundaries occur. Taking all nine coordinate pairs still gives finite support. This argument bounds neither its physical degree nor its pole multiplicities.

The theorem is a finite algebraic recipe over effectively presented coefficient fields: solve the finite line scheme over the passive field, perform finite linear algebra and trace, then substitute and clear denominators. It gives no practical bound on the size of that calculation.

### Passive functions and the scope of a certificate

Cofactor transport distinguishes active coordinates from passive ratios. Suppose a strict physical field satisfies \(qv(F)=A\), \(\operatorname{div}v=0\), and \(v(r_j)=0\) for every passive ratio. For any rational function \(h(r)\),

\[
q(hv)(F)=hA,\qquad \operatorname{div}(hv)=h\operatorname{div}v+v(h)=0.
\]

To obtain another atlas target, \(hA\) must be polynomial of the required degree and parity, and clearing \(h\) must introduce only legal poles. Degree-zero passive multipliers preserve the component degree. This is a useful family extension, but it preserves the density sector selected by the map. It does not give arbitrary targets merely because they lie on the same sextic.

### A binary-cubic Hessian construction

Write the physical variables as \((x,a,c,y,b,d)=(X_0,X_1,X_2,Y_0,Y_1,Y_2)\), and consider

\[
F_R=x^6+a^6+c^6+y^6+b^6+d^6+x^3ayb+a^3cyb.
\]

The rational coordinates

\[
u=x^2,\quad p=yb,\quad v=d^2,\quad z=(y^3-b^3)/d,
\quad r=a/x,\quad s=c/x
\]

give \(F_R=f(u,p)+v^3+vz^2\), where

\[
f=\alpha u^3+\beta u^2p+2p^3,
\qquad \alpha=1+r^6+s^6,\quad \beta=r+r^3s.
\]

The Jacobian in the displayed order is \(12(y^3+b^3)/x\). Thus the active density \(u^2/24\) serves the half-target \(x^3(y^3+b^3)/2\). The symmetry \((a,b)\mapsto(-a,-b)\) preserves \(F_R\) and supplies the complementary half-target. This reduces the prescribed \(x^3y^3\) to one explicit calculation on a cubic surface.

For the binary cubic define

\[
\begin{aligned}
\delta&=324\alpha^2+24\beta^3,\\
h&=-\beta^2u^2+18\alpha up+6\beta p^2,\\
H&=(18\alpha u+12\beta p)\partial_u+(2\beta^2u-18\alpha p)\partial_p,\qquad k=H(f)/3.
\end{aligned}
\]

Direct differentiation gives

\[
H(h)=0,\qquad H(k)=3\delta f,\qquad
\delta f^2-k^2=4h^3/9,
\]

and

\[
\delta u^2=108\alpha f_u+12\beta^2 f_p-12\beta h.
\]

Over a field containing \(\sqrt\delta\), the eigen-coordinates of \(H\) write \(f\) as two cubes \(f_\pm=(f\pm k/\sqrt\delta)/2\). Independently, with \(\lambda^2=3\),

\[
v^3+vz^2=\tfrac12(v+\lambda z/3)^3+\tfrac12(v-\lambda z/3)^3.
\]

Put \(g=(v+\lambda z/3)^3/2\). The Euler field on the coordinate of \(f_+\) and the coordinate of \(g\) has divergence two, acts on \(h\) with weight one, and acts on \(f_++g\) with weight three. Therefore \(h(E_++E_g)/(3(f_++g))\) is divergence-free and sends the full cubic to \(h\). Average this field with its \(\sqrt\delta\)-conjugate, **including its denominator**. The square root disappears. Combining the resulting field with the constant fields \(\partial_u,\partial_p\), using the displayed target identity, serves \(u^2/24\). Cofactor transport and the sign symmetry then serve \(x^3y^3\).

The [explicit certificate](#case/one-reflection), contributed by `fqlx`, carries this calculation through homogeneous clearing and denominator legality: its two half-denominators have degree 30 and their product has degree 60. It builds on `fringewidth`'s hidden-reflection observation and the binary-cubic constructions described in this chapter. Both half-fields annihilate \(a/x,c/x\). Their polynomial numerators have a common \(x^3\) factor, so replacing that factor by any homogeneous cubic \(P_3(x,a,c)\) gives the family of targets \(P_3y^3\) with the same denominator. The resulting fields retain the strict identities and the same denominator legality.

### Endpoint cubics and pole order two

For the central holdout the second mixed term is different:

\[
F_H=x^6+a^6+c^6+y^6+b^6+d^6+x^3ayb+a^3cbd.
\]

Let \(\kappa^2+\kappa+1=0\). Use passive ratios \(\alpha=y/x,\beta=b/a\) and active coordinates

\[
U=x^2,\quad V=a^2,\quad S=c^2+\kappa^2d^2,\quad T=\kappa cd.
\]

Then

\[
G=S^3-3ST^2+(1+\alpha^6)U^3+(1+\beta^6)V^3
       +\alpha\beta U^2V+\beta\kappa^2V^2T
\]

satisfies \(G=F_H\) after substitution. The finite-algebra quadratic solver in §2.4 applies to this cubic over the passive field. In its explicit realization, the coefficient fiber \((1+\alpha^6,1+\beta^6,\alpha\beta,\beta\kappa^2)=(2,2,1,1)\) certifies the necessary inverses.

At \(q=2\), write \(U^3V^2=b(G)\) with \(b\) a polynomial field of component degree three, put \(h=\operatorname{div}b\), and solve \(w_1(G)=h\), \(\operatorname{div}w_1=0\). The recursion in §2.4 becomes

\[
w_2=(b+Gw_1)/2-hE_4/6,
\qquad 2w_2(G)=U^3V^2,\qquad \operatorname{div}w_2=0.
\]

Thus the higher-pole step uses a quadratic solver and a polynomial Jacobian reduction, without requiring new line geometry.

To return to the physical variables, put \(\Delta_\kappa=c^2-\kappa^2d^2\). The four horizontal fields

\[
\begin{aligned}
C_U&=\frac{\Delta_\kappa}{x}\partial_x+
       \frac{\Delta_\kappa y}{x^2}\partial_y,&
C_V&=\frac{\Delta_\kappa}{a}\partial_a+
       \frac{\Delta_\kappa b}{a^2}\partial_b,\\
C_S&=c\partial_c-d\partial_d,&
C_T&=-2\kappa d\partial_c+2\kappa^2c\partial_d
\end{aligned}
\]

have zero divergence, annihilate \(\alpha,\beta\), and act on \((U,V,S,T)\) as \(2\Delta_\kappa\) times the respective coordinate derivatives. Consequently lifting \((\alpha^3\beta^2/2)w_2\) gives a strict pole-two field for \(P\Delta_\kappa\), where \(P=x^3a^2y^3b^2\). The identity

\[
Pc^2=\frac{2+\kappa}{3}P\Delta_\kappa+
      \frac{2+\kappa^2}{3}P\Delta_{\kappa^2}
\]

gives [Holdout · pole order two](#case/holdout-q2). `HeadOfNaps`'s construction proves the required homogeneous clearing and coprimality, as well as the field identities. Passive multiplication and the same endpoint combination also serve the polynomial monomials

\[
x^{6-i}y^i a^{4-j}b^j c^2,\qquad
x^{6-i}y^i a^{4-j}b^j d^2,
\quad 0\le i\le6,\quad0\le j\le4,\quad i+j\text{ odd}.
\]

There are 34 such monomials; this is a list of targets, not a claim that their residue classes are linearly independent. Any extra passive-ratio denominators are coordinate factors and do not contain the smooth sextic.

### The density boundary

A cubic target solver is complete downstairs; a particular map to that cubic need not reach every target upstairs. If a linear reflection \(\rho\) fixes the map \(\Phi\), then differentiating \(\Phi\rho=\Phi\) gives

\[
\det(d\Phi)(\rho Z)=-\det(d\Phi)(Z).
\]

Hence every density target \(\det(d\Phi)B(\Phi)\) is odd under \(\rho\). Passive multipliers fixed by the reflection retain this restriction. In the endpoint example, \(\rho_\kappa(c,d)=(\kappa d,\kappa^2c)\) fixes the active coordinates and negates \(\Delta_\kappa\). The central \(q=1\) target \(x^3y^3\) is invariant. Even combining these endpoint constructions does not reach it: averaging over the finite group generated by the endpoint reflections kills every reflection-odd target, while fixing \(x^3y^3\). Thus this target is outside the linear span of those density sectors. It does not exclude a different map or support. The distinction between a missing density sector and a missing cubic solver is central to the frontier in [Chapter 4](#technical-information/known-locus).

## 2.6 The conic specialization and physical degree bounds

**Conic theorem.** Let \(\Phi _{0}=(Q_{1},Q_{2},Q_{3},Q_{4},r,s)\), where the \(Q_{i}\) are homogeneous quadratics and \(r,s\) are linear forms, and let \(F=H(\Phi _{0})\) be a smooth sextic. Give \(H\) weights (2,2,2,2,1,1). For every \(q\ge 1\) and density \(B\) of weight \(6\cdot q-4\), the target \(A=\operatorname{det}(d\Phi _{0})B(\Phi _{0})\) has a strict certificate \(N_q/D^q\) over an extension of degree at most 27, with \(\operatorname{deg} D=10\) and \(\operatorname{deg} N_q=16\cdot q-5\). For a fixed line chosen in the construction, the same \(D\) serves every density and \(q\). The parity bounds are stated after the proof.

First, \(\Phi _{0}\) is finite. A nonzero common zero of its six coordinates would be singular on \(F\), since \(H\) and its first derivatives vanish at the origin. Thus the homogeneous ideal generated by the coordinates has finite-dimensional quotient. Lifting a homogeneous basis of that quotient and inducting on degree expresses \(k[Z]\) as a finite module over \(k[\Phi _{0}]\). Equality of dimensions forces the six coordinates to be algebraically independent. The map is therefore finite and surjective; its Jacobian is nonzero in characteristic zero. Any nonzero singular point of \(H\) would lift to one of \(F\), so \(H\) is quasismooth. The cubic surface \(H(Q,0,0)=0\) is smooth as well, because the omitted \(r,s\) derivatives vanish there for weight reasons.

Choose a line on this cubic surface. The 27 lines form a finite étale scheme: each line has normal bundle \(\mathcal O(-1)\), whose \(H^{0}\) and \(H^{1}\) vanish, and the classical count is 27. Hence some line is defined over an extension \(K/k\) of degree at most 27. Choose quadratic coordinates \((x,y,U,V)\) so that it is \(U=V=0\). The equation then has the form

\[
\begin{gathered}
G=a\cdot x^{2}+h\cdot x\cdot y+b\cdot y^{2}+c\cdot x+d\cdot y+e,\\
Q=\begin{pmatrix} a & h/2 & c/2 \\ h/2 & b & d/2 \\ c/2 & d/2 & e \end{pmatrix}.
\end{gathered}
\]

The coefficients depend only on \((U,V,r,s)\). Their physical degrees are two for \(a,h,b\), four for \(c,d\), and six for \(e\). There are no terms cubic in \(x,y\) because the chosen line lies on the restricted cubic surface.

The determinant of \(Q\) is nonzero. Otherwise choose a nonzero kernel vector \(p\) over the spectator function field and homogenize \(G\) with a third active coordinate \(z\). At \(p\) its value and every active derivative vanish. Differentiating its value with respect to any spectator gives zero as well: terms differentiating \(p\) vanish by the active equations. If \(p_z\ne 0\), dehomogenization gives a nonzero singular point of \(H\). If \(p_z=0\), the resulting \(U,V\) derivative equations are the \(U,V\) derivatives of \(H\) at \((p_x,p_y,0,0,0,0)\), since \(a,h,b\) are linear in \(U,V\) plus quadratics in \(r,s\). The \(x,y\) derivatives vanish along the chosen line, and the \(r,s\) derivatives vanish at that point for weight reasons. This again gives a singular point of \(H\), a contradiction. Thus \(D=-8\operatorname{det} Q\) is nonzero of physical degree ten.

At \(q=1\), dividing the target by the Jacobian of the adjusted map gives an affine-linear density \(B_{1}=\kappa\cdot x+\lambda\cdot y+\mu \), with spectator coefficients. Solve

\[
\begin{gathered}
\begin{pmatrix}2\cdot a & h & -c \\ h & 2\cdot b & -d \\ c & d & -2\cdot e\end{pmatrix}
\cdot\begin{pmatrix}p_1\\p_2\\\rho\end{pmatrix}
=\begin{pmatrix}\kappa\\\lambda\\\mu\end{pmatrix}
\end{gathered}
\]

by its adjugate; its determinant is \(D\). The field \(w=(\rho\cdot x+p_{1})\partial _{x}+(\rho\cdot y+p_{2})\partial _y\) satisfies \(w(G)-G \operatorname{div} w=B_{1}\), as coefficient comparison shows: the quadratic terms cancel and the remaining coefficients are exactly the three rows of this system. Also \(\operatorname{div} w=2\cdot \rho \). Cofactor transport gives a physical field \(V\) with \(V(F)-F\cdot \operatorname{div} V=A\). It has degree one, so \(s=\operatorname{div} V\) has degree zero. The Euler correction

\[
\begin{gathered}
v_{1}=V-sE_{6}/6
\end{gathered}
\]

has \(v_{1}(F)=A\) and \(\operatorname{div} v_{1}=0\), since \(E_{6}(F)=6\cdot F\) and \(\operatorname{div}(sE_{6})=6\cdot s\). The numerator of each active component of \(w\) over \(D\) has degree eight, and its cofactor column has degree three; hence \(v_{1}\) has numerator degree eleven. The correction retains \(D\) because \(\operatorname{div} V=2\cdot \rho  \operatorname{det}(d\Phi )\).

The denominator is legal. The irreducibility of \(F\) and finite surjectivity of \(\Phi \) imply irreducibility of \(H\). If \(F\) divided the pullback of \(D\), then \(D\) would vanish on all \(H=0\). But \(D\) is independent of \(x,y\), whereas \(H\) has positive active degree, so \(H\) cannot divide it. The same argument works over every coefficient-field embedding. Normalized trace consequently gives a ground-field certificate with denominator \(\operatorname{Norm}_{K/k}(D)\), of degree at most 270.

### Coefficient raising and the bound at every \(q\)

The following identity is useful beyond conics. Suppose \(F_t=F+tT\) is a family of sextics and \(v_q(t)\) has degree \(6\cdot q-5\), with \(q\cdot v_q(t)(F_t)=A\) and \(\operatorname{div} v_q(t)=0\), where \(A\) is independent of \(t\). A dot denotes coefficient differentiation at zero. Set

\[
\begin{gathered}
v_{q+1}=(qTv_q-F\dot{v}_q)/(q+1)-v_q(T)E_{6}/[6(q+1)].
\end{gathered}
\]

Differentiation gives \(\dot{v}_q(F)=-v_q(T)\) and \(\operatorname{div} \dot{v}_q=0\). If \(W\) denotes the first term, then \(W(F)=(A\cdot T+Fv_q(T))/(q+1)\) and \(\operatorname{div} W=v_q(T)\). The scalar \(v_q(T)\) has degree \(6\cdot q\), so the Euler correction has the required value on \(F\) and divergence to give \((q+1)v_{q+1}(F)=A\cdot T\) and \(\operatorname{div} v_{q+1}=0\). If \(v_q=N_q/D^q\), the numerator identity is

\[
\begin{gathered}
N_{q+1}=[q(T\cdot D+F\dot{D})N_q-F\cdot D\cdot \dot{N}_q-(D/6)N_q(T)E_{6}]/(q+1).
\end{gathered}
\]

Thus coefficient differentiation raises the power of \(D\) by at most one and introduces no new physical divisor.

The necessary coefficient derivatives exist at every smooth member, not merely for a generic choice of coefficients. Keep \(\Phi _{0}\) fixed and vary \(H\) in its weighted coefficient space. Over its smooth locus, the 27-line scheme of \(H(Q,0,0)\) is finite étale, by the normal-bundle calculation above. A chosen line over \(K\) therefore has a unique formal lift in every coefficient direction. A Grassmannian chart and complementary coordinates chosen with nonzero minors at the initial line make the conic formulas regular at that point. All these minors are coefficient units. Every finite derivative needed in the recursion is consequently defined over the same \(K\); no successive field extensions are required.

A monomial of weight \(6\cdot q-4\) in four weight-two and two weight-one variables is a product of \(3\cdot q-2\) weight-two units: pair occurrences of the weight-one variables. Reserve one unit for the initial density, and group the remaining units in triples to form \(q-1\) sextic coefficient directions \(T\). The raising identity constructs the desired target. Add monomials to obtain every \(B\), using the same \(D\). This proves the field-degree, denominator and numerator bounds in the theorem.

### Parity and the relation to all-target coverage

For a globally even \(F\) and odd \(A\), replace \(v\) by \((v(Z)-Sv(SZ))/2\). This preserves both strict identities and gives the required parity. Its denominator divides \(D(Z)^q\cdot D(SZ)^q\), giving degree at most \(20\cdot q\) over \(K\) and \(540\cdot q\) after trace.

If \(\Phi _{0}\) is equivariant for linear involutions on its quadratic and linear coordinate spaces, the bounds improve. The induced involution permutes 27 lines, so fixes at least one. The fixed-line scheme has degree at most 27; choose a line over its residue field and use an adapted eigenbasis. If \(\epsilon _{x},\epsilon _y\) are the active eigenvalues, \(Q\) transforms by conjugation with \(\operatorname{diag}(\epsilon _{x},\epsilon _y,1)\). Its determinant is invariant. Parity projection therefore retains \(D\) itself, and its norm is invariant as well. The resulting bounds are

| Conditions | Degree over the line field | Degree after trace |
|---|---:|---:|
| Equivariant \(\Phi _{0}\) and required target parity | \(\le 10\cdot q\) | \(\le 270\cdot q\) |
| General \(\Phi _{0}\), followed by parity projection | \(\le 20\cdot q\) | \(\le 540\cdot q\) |

For coordinatewise-even \(F\) at \(q=1\), square four chosen coordinates and retain two linearly in \(\Phi _{0}\). Its determinant is a nonzero scalar times their product \(C_I\). The initial density has weight two, giving \(C_I(\sum b_{j}\cdot Z_{j}^{2}+b_{rs}\cdot r\cdot s)\). There are six globally odd four-coordinate carriers, each giving six distinct four-odd target monomials; the single all-six-odd monomial is also obtained. Thus the degree-ten construction covers 37 of the 226 allowed monomials. The six-line construction serves the other 189 two-odd monomials too, but has no stated physical degree bound. Arbitrary quadratics enlarge the bounded construction beyond coordinatewise-even equations while retaining its determinant-density target restriction.


## 2.7 Creating a reflection on a finite cover

A useful reflection need not act on the original sextic. It can appear after a finite cover, provided that the resulting certificate descends to the prescribed target. This separates two tasks: constructing primitives on the auxiliary quotient, and identifying the physical target selected by trace.

Consider the chain sextic

\[
F_H=\sum_{i=0}^{2}(X_i^6+Y_i^6)
 +X_0^3\cdot X_1\cdot Y_0\cdot Y_1
 +X_1^3\cdot X_2\cdot Y_1\cdot Y_2.
\]

It is smooth: at a nonzero common zero of its partial derivatives, a coordinate of maximal modulus would contribute a pure derivative of modulus \(6M^5\), while all its mixed derivative terms together have modulus at most \(4M^5\). This is impossible. The endpoint cubic construction of §2.5 does not reach the reflection-invariant target \(X_0^3\cdot Y_0^3\). The following cover supplies a different density sector.

Adjoin \(T^6=Y_0^6+Y_2^6\), set \(\alpha=Y_0/T\), \(\beta=Y_2/T\), and write \(y=Y_1\). The coefficient field is the function field

\[
K_b=\operatorname{Frac}\bigl(\mathbb C[\alpha,\beta]/(\alpha^6+\beta^6-1)\bigr).
\]

Over this field the equation becomes symmetric in \(y,T\). With \(S=y^2+T^2\) and \(P=yT\), its quotient is

\[
H=\sum_{i=0}^{2}X_i^6
  +P\cdot(\alpha X_0^3\cdot X_1+\beta X_1^3\cdot X_2)
  +S^3-3S\cdot P^2.
\]

The weights of \((X_0,X_1,X_2,S,P)\) are \((1,1,1,2,2)\). The parameters \(\alpha,\beta\) satisfy the Fermat relation; they are not two independent passive ratios.

### A polynomial primitive on the quotient

Write \(K_H=\operatorname{Frac}(K_b[X_0,X_1,X_2,S,P]/(H))\), choose the normal coordinate \(X_0\), and put \(g=H_{X_0}\). For the remaining four coordinates let

\[
\mathcal E_i=\partial_i-\frac{H_i}{g}\partial_{X_0},\qquad
\operatorname{div}_g(w)=\sum_i\left(\mathcal E_iw_i-\frac{w_i\mathcal E_i g}{g}\right).
\]

**Moving-conic primitive.** For every polynomial \(B\in K_b[X_0,X_1,X_2,S,P]\), there is \(w\in K_H^4\) with

\[
\operatorname{div}_g(w)=-r_B,\qquad
r_B=\frac{\partial_{X_0}B}{g}-\frac{B\cdot H_{X_0X_0}}{g^2}.
\]

The construction is due to `fqlx`; its [exact conic seed and coefficient calculations](https://github.com/hodge-computer/sextics/pull/128) and [shared implementation](https://github.com/hodge-computer/sextics/tree/main/formal/lean/HodgeComputer/Constructions/HoldoutCover) supply the algebraic data. Its mechanism is as follows.

Start with an endpoint on \(X_1=0\). Seek a polynomial curve \(\phi(t)\) with \(\phi(0)\) equal to that endpoint, \(X_1=kt\) with \(k\ne0\), the other \(X\) coordinates quadratic in \(t\), and \(S,P\) quartic. The equation \(H(\phi(t))=0\) gives twelve positive-degree coefficient equations for twelve coefficients. An exact complex seed, lying on an actual fiber of the Fermat coefficient curve, makes their Jacobian invertible. Localizing at this determinant gives a nonzero étale algebra over the endpoint ring. Flatness preserves nontriviality at the generic point; a finite field factor supplies the curve coefficients. The resulting evaluation embeds \(K_H\) in a finite extension of it of the form \(E(t)\), with \(E\) finite over the endpoint function field.

The same invertible coefficient matrix constructs a polynomial normal vector \(\psi(t)\) satisfying \(\nabla H(\phi)\cdot\psi=1\). Complete it by the curve tangent and the three endpoint tangent vectors. The resulting five-by-five matrix has a nonzero polynomial determinant \(J(t)\). The residue Piola identity expresses the pullback of \(r_B\) through polynomial combinations of \(\phi,\psi,J\), their derivatives, and the first two derivatives of \(H\). All of these are polynomial in \(t\). Integrating \(\sum c_nt^n\) as \(\sum c_nt^{n+1}/(n+1)\), and then dividing by \(J\), gives the residue primitive over \(E(t)\). No rational antiderivative of an arbitrary algebraic function is assumed.

Normalized trace returns the primitive to \(K_H\). In characteristic zero, derivations extend uniquely through finite field extensions and commute with trace. This is the reason trace is suitable here; an arbitrary linear coefficient functional would not suffice. The argument constructs a primitive for every polynomial \(B\) on this fixed quotient, but does not yet identify which physical targets its pullback serves.

### Changing the ternary part

The quotient and the curve used on it are separate pieces of the construction. Replacing \(\sum X_i^6\) by another ternary sextic \(f(X)\) preserves the exchange of \(y,T\), the Fermat coefficient curve, and the target-selection identities below. It need not preserve a chosen conic. One must solve the incidence for the changed equation; the original curve is not deformation data for a different hypersurface merely because the same coordinates are available.

For example, take

\[
f(X)=\sum_iX_i^6+\frac1{14}(X_0^5\cdot X_1+2\cdot X_1^5\cdot X_2+X_2^5\cdot X_0).
\]

For this \(f\), let \(G=f(X)+P(\alpha X_0^3X_1+\beta X_1^3X_2)+S^3-3SP^2\). At \((\alpha,\beta)=(1,0)\) in characteristic five, the following curve lies on \(14G=0\):

\[
\begin{aligned}
X_0&=1+2t^2,&X_1&=t,&X_2&=4+2t+2t^2,\\
S&=4+t+t^2+3t^3+3t^4,&&P=4+t+4t^2+4t^3+3t^4.
\end{aligned}
\]

Use as variables all three coefficients of \(X_0\), the two positive coefficients of \(X_2\), and the four positive coefficients of each of \(S,P\). The thirteen coefficients of the substituted degree-twelve equation give a square system with invertible Jacobian. The [construction of `hodgepodgeconjecture`](https://github.com/hodge-computer/sextics/pull/151) proves the seed and inverse matrix exactly. The integral lifting principle of §5.4 supplies characteristic-zero incidence data and a finite family over the generic coefficient field. A normal constructed for \(14G\) must be multiplied by fourteen before using it for \(G\).

The integration, trace and target extraction then apply to the actual deformed equation. This illustrates the reusable part of the method: the transport identities survive a change in the ternary polynomial, while the curve, its Jacobian and dominance remain mathematical obligations. If a perturbation destroys the exchange or makes the coefficient curve depend on an active coordinate, replacing the conic alone does not repair that different failure.

### Target selection by the deck character

Take \(\beta\) as the base coordinate, retaining the full change of variables when returning to the physical field. The physical-to-quotient Jacobian is

\[
J_c=\frac{2\alpha^5(T^2-y^2)}{T}.
\]

The quotient and physical normal derivatives agree because \(X_0\) is unchanged. Suppose a homogeneous physical sextic \(A\), a physical polynomial \(C\), and a polynomial quotient source \(B\) satisfy

\[
J_c B=A-Ct,\qquad
J_c\partial_{X_0}B=\partial_{X_0}A-(\partial_{X_0}C)t,
\]

where \(t\) is an element of the common cover field with normalized trace zero over the physical field. Then Piola transport and trace give the residue equation for \(A\). The second identity is needed because the source is \(r_B\), not merely \(B\). In the applications below it follows by differentiation: \(J_c\) and \(t\) are independent of \(X_0\). The derivatives of the Fermat base coordinates are included in the full transport, rather than silently treated as physical constants.

For the central target the choice

\[
B=\frac{X_0^3\cdot S}{2\alpha^2}
\]

gives

\[
J_cB=X_0^3\cdot Y_0^3
 -X_0^3\cdot Y_0^3\cdot Y_1^4\cdot T^{-4}.
\]

The deck action fixes all physical coordinates and sends \((T,\alpha,\beta)\) to \((\zeta T,\zeta^{-1}\alpha,\zeta^{-1}\beta)\), where \(\zeta^6=1\). The correction has a nontrivial character, so its trace is zero. Thus the original target is recovered exactly.

The same calculation gives a convenient monomial criterion. Write

\[
A=M(X)\cdot Y_0^a\cdot Y_1^b\cdot Y_2^c,\qquad
m=a+c+1,\qquad e=b-m,
\]

with total degree six and odd total \(Y\)-degree. Then \(m,b\) have the same parity. The expression

\[
B=\frac{M(X)\alpha^{a-5}\beta^c}{2}\,
       \frac{y^mT^b-T^my^b}{y^2-T^2}
\]

is a polynomial in \(S,P\) over \(K_b\): the quotient is symmetric in \(y,T\), invariant under their simultaneous sign change, and polynomial because \(m-b\) is even. Direct multiplication gives

\[
J_cB=A-C T^e,\qquad
C=M(X)\cdot Y_0^a\cdot Y_2^c\cdot Y_1^m.
\]

Whenever \(e\not\equiv0\pmod6\), the correction has trace zero. For these degree-six monomials the useful exponents are \(-4,-2,2,4\). This criterion includes the central target and all nine other single-monomial \(q=1\) holdout entries; the target-specific source identities are the additional input, not another conic construction. Linear combinations of served targets are served as well. The source-by-source extension and its per-target identities were independently recorded by `DiamondJM` in [the holdout discussion](https://github.com/hodge-computer/sextics/discussions/44#discussioncomment-19046728), with the cover and moving-conic construction credited to `fqlx`.

The exclusions reveal the scope of this particular projection. When \(e=0\), the numerator defining \(B\) is zero. When \(e=-6\), the correction is deck-invariant, since \(T^{-6}=(Y_0^6+Y_2^6)^{-1}\) is physical. Neither case is removed by this trace argument. These are limitations of the selected source map, not nonexistence results for certificates.

### Equal coupling coefficients

The cover construction can survive a change of equation, but its conic seed must then be checked on the new coefficient locus. Consider

\[
F_{\mathrm{eq}}=\sum_{i=0}^{2}(X_i^6+Y_i^6)
 +Y_0\cdot Y_1\cdot(X_0^3\cdot X_1+X_1^3\cdot X_2).
\]

The same Fermat cover gives

\[
H_{\mathrm{eq}}=\sum_{i=0}^{2}X_i^6
 +\alpha P\cdot(X_0^3\cdot X_1+X_1^3\cdot X_2)
 +S^3-3S\cdot P^2.
\]

The two coupling coefficients now coincide. The base still satisfies \(\alpha^6+\beta^6=1\): replacing the second coupling coefficient by \(\alpha\) does **not** replace the base coordinate \(\beta=Y_2/T\), or impose \(2\alpha^6=1\).

An equal-coefficient conic seed, constructed by `DiamondJM` from `fqlx`'s conic family, supplies the missing incidence check. In that family equality of the coupling coefficients reduces to

\[
g(r)=r^8+7r^7-58r^6+149r^5-178r^4+115r^3-44r^2+10r-1=0.
\]

The values \(g(-13)=35869443\) and \(g(-12)=-35000185\) give a root in \((-13,-12)\). The same interval makes the seed denominators and both even and odd Jacobian factors nonzero. The resulting conic lies on \(H_{\mathrm{eq}}\); choosing a separate sixth root \(\beta_c^6=1-\alpha_c^6\) places it over the actual Fermat base. The [exact seed and incidence identities](https://github.com/hodge-computer/sextics/pull/144) therefore permit the moving-conic primitive for every polynomial source on this quotient. An isolated formal substitution in the old coefficient field would not establish this: the new coefficient locus needs a nonsingular seed of its own.

For the [transverse target](#case/one-reflection-y2-sector), put

\[
A=X_0^3\cdot Y_0\cdot Y_1\cdot Y_2,\qquad
B=\frac{\beta X_0^3\cdot P}{2\alpha^4}.
\]

The source identity is

\[
J_cB=A-X_0^3\cdot Y_0\cdot Y_1^3\cdot Y_2\cdot T^{-2}.
\]

Its \(X_0\)-derivative gives the normal-source identity, and the inverse-square deck character kills the correction under trace. This yields a checked finite-algebraic certificate for a target outside both binary-cubic density sectors of §2.5. The general monomial criterion above applies to \(F_{\mathrm{eq}}\) as well, because the physical cover and its Jacobian are unchanged. Geometric existence for every odd target at every positive pole order follows more directly from §3.3: in the coordinates \(U=Y_0+Y_1\), \(V=Y_0-Y_1\), the equation is separately even in \(U,V,Y_2\). The geometric support theorem and the checked target construction have different scopes.

### Returning to a homogeneous polynomial certificate

For either \(F=F_H\) or \(F=F_{\mathrm{eq}}\), a residue primitive in \(K_F=\operatorname{Frac}(\mathbb C[X,Y]/(F))\) has representatives \(w_i=n_i/d\) with \(d\) nonzero modulo \(F\). Put \(g_i=\partial_iF\) and

\[
D=g_0d,\qquad N_0=Ad-\sum_{i=1}^5g_in_i,\qquad N_i=g_0n_i\quad(i>0).
\]

Then \(N(F)=AD\) exactly. The residue equation says that

\[
D\operatorname{div}N-N(D)=FQ,
\]

so the full cleared defect is \(F^2Q\). The quotient need not vanish. Both \(g_0\) and \(d\) are nonzero in \(K_F\), giving denominator legality. Finite homogeneous extraction produces a homogeneous denominator and numerators of degree \(\deg D+1\), preserving these identities; see the [extraction argument](https://github.com/hodge-computer/sextics/pull/128).

This is a finite algebraic existence proof of the required certificate. It does not provide an expanded denominator or a numerical degree bound. Extracting a usable divisor requires making the finite coefficient algebra, traces, and clearing explicit. The certificate statement, the source-map criterion, and the practical size of a witness are distinct questions.

## 2.8 A complementary quotient and its polynomial densities

The trace-zero construction of §2.7 misses the monomial \(A_*=X_0^3\cdot Y_0\cdot Y_1^2\): its deck exponent is zero, and its antisymmetrized quotient source vanishes. A different quotient serves this target on the same chain sextic \(F_H\). The construction of `fqlx` supplies both an explicit incidence system and its [formal certificate](https://github.com/hodge-computer/sextics/pull/161).

Let \(g\) fix \(X\) and act on \((Y_0,Y_1,Y_2)\) with weights \((5,1,5)\) modulo six. Both the equation and the residue with numerator \(A_*\) are invariant: the numerator has character \(\zeta\), and the volume form has character \(\zeta^5\). On a rational coordinate open put

\[
p=Y_0Y_1,\qquad v=Y_1Y_2,\qquad
\lambda=\frac{Y_1^3}{Y_0^3+iY_2^3},\qquad i^2=-1.
\]

These invariant coordinates give, over \(k=\mathbb C(\lambda)\), the hypersurface

\[
K=\sum_{j=0}^2X_j^6+X_0^3X_1p+X_1^3X_2v
  +a p^3+b v^3,\qquad
a=\lambda+\lambda^{-1},\quad b=i(\lambda-\lambda^{-1}).
\]

For the full six-coordinate map \(\theta=(X_0,X_1,X_2,p,v,\lambda)\), direct calculation gives

\[
K(\theta)=F_H,\qquad J_\theta=-6\lambda Y_1,\qquad
\rho=-\frac{X_0^3p}{6\lambda},\qquad J_\theta\rho(\theta)=A_*.
\]

Thus the required quotient density is polynomial in the five fiber coordinates, with coefficients in \(k\). This observation identifies the source; constructing its primitive is a separate step.

### Curves, normals, and integration

Take a generic endpoint \((c_0,0,c_2,p_0,v_0)\) satisfying

\[
c_0^6+c_2^6+a p_0^3+b v_0^3=0.
\]

Over its function field seek a curve with \(\Phi_1=t\), with \(\Phi_0,\Phi_2\) quadratic in \(t\), and with \(\Phi_p,\Phi_v\) quartic. Fix the constant coefficients to be the endpoint. The twelve positive coefficients are unknowns, and the twelve equations are \([t^j]K(\Phi)=0\), \(1\le j\le12\). In the order of the two coefficients of \(\Phi_0\), two of \(\Phi_2\), four of \(\Phi_p\), and four of \(\Phi_v\), a nonsingular seed over \(\mathbb F_5\) is

\[
\begin{gathered}
(a,b)=(0,3),\qquad(c_0,c_2,p_0,v_0)=(1,1,4,1),\\
u=(1,0,4,1,4,2,2,4,4,1,1,2),\qquad \det\Delta=3.
\end{gathered}
\]

Here \(\Delta\) is the Jacobian of all twelve incidence equations. The endpoint relation also holds over the integers at \((a,b)=(0,-2)\), and \(\lambda=i\) realizes this parameter value. The integral lifting principle of §5.4 therefore produces a nonsingular complex point on the actual coefficient locus. Localizing at \(\det\Delta\), étale flatness carries nontriviality to the generic endpoint; a finite field factor supplies the curve coefficients. No inversion of \(a\) or \(\lambda^2+1\) is permitted at the seed, where both vanish.

The incidence matrix does more than move the curve. Start a normal vector with \(e_0/(6c_0^5)\), whose gradient pairing has constant coefficient one. Its remaining coefficients are canceled using \(\Delta^{-1}\) and the twelve coefficient variations of the curve. This gives a polynomial vector \(\Psi(t)\) with \(\nabla K(\Phi)\cdot\Psi=1\). The determinant formed from this normal, the curve tangent, and the three independent endpoint derivatives has constant coefficient \(1/(6c_0^5)\ne0\). This is the evaluation determinant needed for residue transport, distinct from the incidence determinant.

The curve defines a finite embedding of the quotient function field into \(E(t)\), where \(E\) is finite over the endpoint field. Injectivity follows from the independent endpoint coordinates, the exact identity \(\Phi_1=t\), and irreducibility of the hypersurface equation. The polynomial normal and evaluation determinant then put every polynomial source on \(K\) into the integration mechanism of §2.7. Coefficientwise integration in \(t\), followed by normalized trace, gives its residue primitive.

For \(\rho\) above, full Piola transport through \(\theta\) and legal homogeneous clearing give a certificate for \(A_*\). Although the relative construction is over \(\mathbb C(\lambda)\), the physical change of variables includes the derivatives of \(\lambda\). It is not a constant on the original sextic. Combining this certificate with the cover certificate for \(X_0^3Y_0^3\) gives the character-separating bundle, using the common-denominator identity in Chapter 1. The quotient remainders are retained; neither summand is required to have a strict certificate.

### Polynomial and rational source boundaries

For an odd sextic monomial \(A=M(X)Y_0^aY_1^bY_2^c\), put \(e=b-a-c-1\) as in §2.7. The cover handles \(e\not\equiv0\pmod6\). In the complementary sector, there are two possibilities:

\[
\begin{array}{c|c}
e & A/J_\theta\text{ in the quotient coordinates}\\
\hline
0 & -M(X)p^a v^c/(6\lambda)\\[2pt]
-6 & -M(X)p^a v^c/\bigl(6\lambda^2(p^3+i v^3)\bigr).
\end{array}
\]

The second identity uses \(Y_1^6=\lambda(p^3+i v^3)\). The \(e=0\) sources are polynomial on the fiber, so the same curve and integration theorem serve them, with their own source identities. The \(e=-6\) densities have a fiber denominator and require a different source representative or primitive construction: rational integration can encounter nonzero residues. Geometric existence still follows from the descent criterion of §4.6.

The displayed source maps need not exhaust their closure under automorphisms. Coordinate transport can supply a different polynomial presentation of a target with a fiber pole. The [holdout explanation](#case/holdout), under “Geometric scope of the Fermat cover,” records the exact character counts and such an exchange. These distinguish the scope of a chosen integration formula from the support of the underlying classes.

Cofactor transport makes fields explicit, algebraic cycle classes prove target spanning, and finite covers can expose symmetries absent on the original variety. Each method must still identify its physical target image. None establishes that a suitable map or supporting family exists for a general \(Y\)-even sextic.


## 2.9 Moving cubic maps and Jacobian residue transport

A genus-one curve can have a useful map to its Jacobian even when the curve has no chosen rational origin. For a family of cubics, this map varies with the coefficients. Transporting a differentiated residue therefore requires both its invariant differential and the correction caused by the moving map. A primitive on the Jacobian alone does not establish a primitive for the original source.

### Change of normal density

For commuting tangent derivations \(\partial_i\) and a nonzero normal derivative \(g\), write
\[
\operatorname{ResDiv}_g(w)
 =\sum_i\partial_iw_i-\frac{\sum_iw_i\partial_i g}{g}
 =g\sum_i\partial_i(w_i/g).
\]
If \(M\) is the coordinate Jacobian, \(N=M^{-1}\), and the new normal derivative is \(h\), the Piola identity gives
\[
\operatorname{ResDiv}_g\left(\frac gh\det(M)Nw\right)
 =\frac gh\det(M)\operatorname{ResDiv}_h(w).
\]
Indeed, the identity with density \(h\) follows from §2.1; replacing the vector by \((g/h)\) times itself changes the density to \(g\). Both the normal ratio and the determinant matter. The coordinate calculation includes derivatives of all parameter ratios.

For a balanced numerator there is also a direct normal-chart identity. Let \(p,q\) be two coordinates, put \(f=F_p\), \(g=F_q\), and take \(A=Bpq\) with \(B\) independent of \(p,q\). Define
\[
G=pf+qg,\qquad H=p^2F_{pp}+2pqF_{pq}+q^2F_{qq},\qquad
D=\partial_q-\frac gf\partial_p.
\]
When \(f,G\ne0\), the correction \(C=-Bpq^2/G\) satisfies
\[
\frac{A_p}{f}-\frac{AF_{pp}}{f^2}
 =\frac{A(3G-H)}{G^2}+DC-C\frac{Df}{f}.
\]
The last two terms are the residue divergence of the vector with \(q\)-component \(C\). Thus passing to the paired normal has a specified correction even when the source involves both coordinates. The identity follows from the product and quotient rules and is formalized over any field in `ResidueTransport.NormalChange`; the application supplies the normal and Hessian identities.

### First variation of a Weierstrass map

Let \(D\) be a tangent derivation on a characteristic-zero field. Suppose
\[
\eta^2=\xi^3+a\xi+b,\qquad Da=Db=0,
\qquad \frac{D\xi}{2\eta}=\frac m g,
\]
with \(m,g,\eta\ne0\). A dot denotes a compatible first variation fixing the tangent coordinate and \(m\). Differentiating the two identities gives
\[
2\eta\dot\eta=(3\xi^2+a)\dot\xi+\dot a\xi+\dot b,
\qquad
\frac{D\dot\xi}{2\eta}-\frac{D\xi\dot\eta}{2\eta^2}
 =-\frac{m\dot g}{g^2}.
\]
Differentiate the curve identity with \(D\), substitute these two relations, and collect terms. The result is
\[
\boxed{\frac{\dot g}{g}
 =\frac{\dot a\xi+\dot b}{2\eta^2}
  -\frac g m D\left(\frac{\dot\xi}{2\eta}\right).}
\]
The last term is the exact differential correction. Omitting it changes the source.

These hypotheses can be established at a single coefficient value using dual numbers \(K[\epsilon]/(\epsilon^2)\). One proves the curve and differential identities for the first-order deformation and compares their constant and linear terms. This avoids the invalid assumption that differentiation in an auxiliary coefficient is a derivation on the already specialized function field. The shared Lean module `ResidueTransport.MovingMap` gives both the jet formulation and the formulation with commuting derivations.

### A cyclic paired-sign cubic

Consider the fixed sextic
\[
F_C=\sum_{i=0}^2(X_i^6+Y_i^6)
 +\frac12\sum_{i\bmod3}X_i^3\cdot X_{i+1}\cdot Y_i\cdot Y_{i+1}.
\]
It has a certificate for \(q=1\), \(A=X_0^3\cdot Y_0^3\). The [construction of `hodgepodgeconjecture`](https://github.com/hodge-computer/sextics/pull/165) supplies a finite-algebraic realization of the transport mechanism, using the shared polynomial-family machinery of `fqlx` and the project contributors.

Put \(r=X_2^2\), \(v=Y_0/X_0\), \(c_i=(Y_i/X_i)/v\), and \(x=X_0^2/r\), \(y=X_1^2/r\). The paired sign changes allow the equation to descend to
\[
U=ax^3+by^3+cz^3+dx^2y+ey^2z+fz^2x,
\]
where
\[
(a,b,c)=(1+v^6,1+c_1^6v^6,1+c_2^6v^6),
\qquad(d,e,f)=\tfrac12v^2(c_1,c_1c_2,c_2).
\]
The physical chart has \(z=1\). For the integral ternary-cubic covariants \(H,\Theta,J\) in the construction, define
\[
s_4=ae^2f+bdf^2+cd^2e,\qquad
s_6=27a^2b^2c^2+4a^2ce^3+4ab^2f^3+6abcdef+4bc^2d^3-d^2e^2f^2.
\]
Their exact syzygy on \(U=0\) is
\[
J^2=4\Theta^3+4s_4\Theta H^4-s_6H^6.
\]
Thus \(\xi=\Theta/H^2\), \(\eta=-J/(2H^3)\) satisfy
\(\eta^2=\xi^3+s_4\xi-s_6/4\), and their tangent differential obeys
\(D_y\xi/(2\eta)=3/U_x\). The syzygy and differential identity are polynomial identities, not tests at a sampled cubic. Their normalization and exact definitions are recorded in [the construction explanation](#case/cycle-three).

Set \(T=rv^6\), \(X=r^2\xi\), \(Y=r^3\eta\). After these substitutions the Jacobian equation is polynomial:
\[
V=Y^2-X^3-\frac18a_8(c_1,c_2,r,T)X
             -\frac1{256}b_{256}(c_1,c_2,r,T)=0,
\]
where \(a_8=8r^4s_4\), \(b_{256}=-64r^6s_6\). Their degrees in \((r,T)\) are four and six. A polynomial curve on this hypersurface has degrees \((2,4,6)\) in \((r,X,Y)\), with curve parameter \(T\). The thirteen coefficient equations admit the nonsingular seed
\[
\begin{aligned}
r(T)&=1+2T+4T^2,\\
X(T)&=3+T+3T^2+4T^3+4T^4,\\
Y(T)&=2+3T+3T^2+4T^3+4T^4+T^5+T^6
\end{aligned}
\qquad\text{over }\mathbb F_5,\quad(c_1,c_2)=(2,3).
\]
The retained endpoint parameters are \(r(0),X(0)\); the other thirteen coefficients are incidence unknowns. The integral square-system lifting theorem of §5.4, an explicit inverse coefficient Jacobian, and independent endpoints yield a dominant family with a polynomial normal. Polynomial integration and normalized trace then give residue primitives for every polynomial numerator on this **specified Jacobian model**.

To recover the physical target, vary \(a=\alpha+v^6\) to first order at \(\alpha=1\). The source \(P_J=-V_\alpha/(144r)\) is polynomial: the coefficient derivative has the required factor \(r\). The full coordinate matrix from physical tangent coordinates to \((T,c_1,c_2,r,X)\) has residue-volume multiplier
\[
\frac{F_{X_0}\det M}{2Y}=-144rv^3.
\]
Pull back the primitive for \(P_J\), add the moving-map correction above, and subtract the correction for changing the physical normal chart. The result solves the original residue-divergence equation. Legal clearing and ordinary homogeneous extraction give \(D,N,Q\) with numerator degree \(\deg D+1\); no bound on \(\deg D\), and no expanded witness, is asserted.

### Transitive paired-sign cubics

The directed cycle is not required for this method. Consider instead
\[
U=ax^3+by^3+cz^3+dx^2y+ey^2z+fx^2z.
\]
Its three mixed monomials form a transitive triangle. In the normalization of the [mixed-biweight construction of `fqlx`](https://github.com/hodge-computer/sextics/pull/170), the invariants are
\[
\begin{aligned}
s_4&=-3bcdf+cd^2e-\tfrac13e^2f^2,\\
s_6&=27a^2b^2c^2+4a^2ce^3+4b^2cf^3+4bc^2d^3
       -4bcdef^2+\tfrac83cd^2e^2f+\tfrac8{27}e^3f^3.
\end{aligned}
\]
The corresponding covariants satisfy the same form of syzygy and invariant-differential identity as above. These are identities for arbitrary coefficients in this transitive family. The shared Lean library `TransitiveCubic` contains their exact coefficient proofs; the change of cubic family changes the covariants themselves, not the moving-map principle.

For the mixed-biweight sextic the diagonal coefficients remain
\((a,b,c)=(1+v^6,1+c_1^6v^6,1+c_2^6v^6)\), while
\[
d=\tfrac12c_1v^2,\qquad e=\tfrac12c_1c_2v^2,
\qquad f=\tfrac13c_2v^4.
\]
The substitution \(T=rv^6\), \(X=r^2\xi\), \(Y=r^3\eta\) again makes
\[
V=Y^2-X^3-A_4(r,T)X-B_6(r,T),\quad
A_4=r^4s_4,\quad B_6=-r^6s_6/4
\]
polynomial, with degrees four and six. At \(c_1=c_2=1\), its incidence has the exact seed
\[
r=1+T^2,\qquad X=3+4T^2+3T^4,\qquad Y=2+3T^6
\quad\text{over }\mathbb F_5.
\]
The thirteen-by-thirteen coefficient Jacobian is invertible. Lifting, independent endpoint parameters, and polynomial integration therefore supply primitives on this Jacobian family. Varying \(a=\alpha+v^6\) gives the polynomial source \(-V_\alpha/(144r)\), and the residue-volume multiplier is again \(-144rv^3\). The two correction terms recover the physical target \(X_0^3\cdot Y_0^3\).

The [moving-branch sextic](#case/holdout-moving-branch) gives a second specialization of the same covariants. It has
\[
d=c_1v^2,\qquad e=c_1c_2v^2,\qquad f=\tfrac17c_2^2v^4,
\]
with the same diagonal coefficients. Its integral Jacobian equation uses the scale \(111132\). A nonsingular seed at \(c_1=c_2=1\) is
\[
\begin{aligned}
r&=1+2T^2,\\
X&=4+4T+T^2+3T^3+T^4,\\
Y&=1+3T^2+4T^4+2T^6
\end{aligned}
\quad\text{over }\mathbb F_5.
\]
Fixing \(r(0)=1\) and \(X(0)=4\) leaves a square system with thirteen coefficients and invertible incidence derivative. The same lifting and source-transport construction serves \(X_0^3\cdot Y_0^3\). The coefficient specialization and seed change, while the transitive covariants and residue mechanism remain the same.

### Reducing equations and source variations

A coordinate change can reduce both an equation and its required deformation to a coefficient family with known covariant identities. Let \(U\) be homogeneous over a characteristic-zero field, let \(Q\) be a variation of the same degree, and let \(v(x)=Mx\) with \(\operatorname{tr}M=0\). For \(\epsilon^2=0\),
\[
(U+\epsilon Q)(x+\epsilon v(x))
 =U+\epsilon\left(Q+\sum_i v_iU_{x_i}\right),
\qquad \det(1+\epsilon M)=1.
\]
Thus the variation may be reduced modulo the Jacobian directions arising from trace-zero linear vector fields. When the resulting variation lies in a known coefficient family, evaluate that family's polynomial identities over the dual numbers to obtain its first-order relations. The coordinate change and its normal-source correction remain part of the construction.

The scalar correction has a useful general form. For any field derivation \(\delta\) and \(g\ne0\),
\[
\delta\!\left(\frac{h-cg}{g}\right)
 =\delta\!\left(\frac h g\right)-\delta c.
\]
If \(\delta c=0\), replacing \(h\) by \(h-cg\) preserves the complete normal expression \((\delta h)/g-h\delta g/g^2\). Otherwise the displayed correction must be retained. This identity is formalized in `ResidueTransport.NormalChange`; it includes the derivative of the denominator.

For example, consider
\[
U=ax^3+by^3+cz^3+dx^2y+ey^2z+fxy^2.
\]
Assume \(a\ne0\) and \(d^2-3af\ne0\). Over a finite extension choose \(k\) with \(3ak^2+2dk+f=0\). The determinant-one shear \(x=X+ky\) gives
\[
U=aX^3+b'y^3+cz^3+d'X^2y+ey^2z,
\quad b'=b+ak^3+dk^2+fk,\quad d'=d+3ak,
\]
with \((d')^2=d^2-3af\). This is the transitive family with its last coefficient zero. The source \(xyz\) becomes \((X+ky)yz\). The further infinitesimal shear \(X\mapsto X-\epsilon z/(2d')\) replaces it by
\[
(X+ky)yz-\frac{zU_X}{2d'}
 =ky^2z-\frac{3a}{2d'}X^2z,
\]
two coefficient directions already present in that family. On \(z=1\), the normal derivative \(\partial_X\), taken before restriction to \(U=0\), fixes the correction coefficient \(1/(2d')\). The normal-source identity above therefore applies. The transitive invariant formulas give, for the original \(xyz\) variation,
\[
\dot I_4=\frac{9abc-cdf}{2},\qquad \dot I_6=acde^2,
\quad I_4=s_4,\quad I_6=-s_6/4.
\]
The family identities are maintained in `TransitiveCubic.Shear`. This cubic reduction and source calculation are due to `fqlx`'s [shear construction](https://github.com/hodge-computer/sextics/discussions/58#discussioncomment-19111681), prepared with OpenAI Codex assistance.

The algebraic extension also carries the derivations and trace used in transport. A derivation fixing \(a,d,f\) fixes \(k\); parameter derivations may move it and must be included in the physical coordinate matrix. Required covariant denominators can be proved nonzero by the [specialization criterion in §5.4](#technical-information/computation). Once a primitive for the original-field source is established over the finite separable extension, normalized trace descends it as in Chapter 1. These steps change the presentation of a source; they do not enlarge the supported representations of the quotient.

### Coefficient and source scope

The degree-four and degree-six Jacobian model is a consequence of symmetry, not a peculiarity of the displayed edge patterns. Impose the three paired signs and the diagonal action with weights \((2,1,0,3,2,1)\) modulo six, in addition to global \(Y\)-evenness. The equation space then has 26 monomials. In the paired chart its general cubic has the form
\[
\begin{aligned}
U={}&\sum_{i=0}^2(a_i+b_i v^6)u_i^3
 +(g_0+g_1v^6)u_0u_1u_2\\
 &+v^2(d_0u_0^2u_1+d_1u_1^2u_2+d_2u_2^2u_0)
 +v^4(e_0u_0u_1^2+e_1u_1u_2^2+e_2u_2u_0^2),
\end{aligned}
\]
where the coefficients lie in the passive field. The count is six pure sixth powers, two balanced monomials, and nine monomials for each edge orientation. The induced weights of \((u_0,u_1,u_2)\) are \((4,2,0)\), whose sum is zero modulo six.

The classical \(SL_3\)-invariants \(I_4=s_4\) and \(I_6=-s_6/4\) have coefficient degrees four and six; see [Fisher, *The invariants of a genus one curve*](https://arxiv.org/abs/math/0610318). Consequently \(I_d(U(v))\) has degree at most \(6d\) in \(v\), and its powers of \(v\) are divisible by six. Thus
\[
r^d I_d(U(v))\big|_{v^6=T/r}
\]
is a homogeneous polynomial of degree \(d\) in \((r,T)\). The same polynomial Jacobian form is therefore available throughout this coefficient space, wherever the generic cubic is smooth. The determinant-one action on the ternary coordinates preserves the cubic residue differential, so these invariants describe the descended Jacobian over the field of \(v^6\), without a further differential-character twist. The genus-one surface itself can have multiple fibers; its Jacobian need not be birational to it.

There are 22 odd degree-six monomials invariant under the paired signs whose residues are invariant under the diagonal action: six have \(Y\)-degree one, ten have degree three, and six have degree five. Their polynomial-source condition follows from the same weights. Write one such target, divided by \(r^3\), as \(c\,v^j M(u)\), with \(c\) passive, \(j\in\{1,3,5\}\), and cubic monomial \(M\). Let \(k_M\) denote its coefficient in \(U\). Then
\[
P_{d,M,j}=r^{d-1}v^{j-3}
 \frac{\partial I_d}{\partial k_M}(U(v)),\qquad d=4,6,
\]
becomes a polynomial in \((r,T)\). Indeed, an invariant derivative has coefficient degree \(d-1\), hence \(v\)-degree between zero and \(6(d-1)\). Multiplication by \(v^{j-3}\) gives possible exponents between \(-2\) and \(6(d-1)+2\); residue invariance forces them to be divisible by six. They therefore lie between zero and \(6(d-1)\). This also excludes negative powers of \(r\) after the substitution. In the normalization above, the resulting Jacobian source is
\[
\frac{c}{144}\bigl(P_{4,M,j}X+P_{6,M,j}\bigr).
\]

This calculation supplies polynomial sources for an explicit implementation. Chapter 4 proves the stronger geometric statement: when the associated \((3,3)\) surface is smooth over the passive field, the entire \(\Gamma\)-invariant fourth cohomology has divisor support. That hypothesis holds on a nonempty coefficient open. Extracting a certificate through the present Jacobian method still requires the covariant differential, its first variation, a serving curve family with polynomial normal and the physical transport. A nonsingular incidence persists on an open, but a particular seed need not survive every specialization. These are extraction requirements inside the geometric theorem's scope, not additional hypotheses for its cohomological conclusion.

### Character and geometry beyond this family

The all-polynomial-source theorem on an auxiliary Jacobian serves the physical classes which reach it with the specified density and correction terms. For the diagonal action above, with weights \(w=(2,1,0,3,2,1)\), a monomial residue with exponent vector \(e\) has character
\[
\zeta^{\langle w,e\rangle+9}.
\]
The added nine is the determinant character of the projective volume. Averaging to the invariant quotient retains precisely character one, independently of the pole order. The averaging-ideal criterion of §3.1 describes how further serving quotients can enlarge that image.

The resulting invariant sector has primitive Hodge dimensions \((22,74,22)\), compared with \((208,866,208)\) for the global involution. The nontrivial order-three surface eigenspaces retain holomorphic two-forms, as computed in §4.7. Removing the extra diagonal symmetry, or the paired signs themselves, can also change the surface's geometric genus. These are geometric and representation-theoretic hypotheses on the construction; an elliptic correspondence alone does not integrate an arbitrary rational differential.
