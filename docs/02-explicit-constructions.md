# 2. Algebraic constructions and residue transport

[Previous: certificates](#technical-information/certificates) · [Contents](#technical-information/introduction) · [Next: geometric support](#technical-information/geometric-support)

A transport identity relates rational primitives on different equations. A change of variables converts \(F\) into an equation with accessible geometry; a rational field on that equation is pulled back by cofactors. Its Jacobian determines the target. Algebraic cycle classes can then prove that the resulting targets span the required space.

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

**Cubic-surface theorem.** Let \(G\) be a homogeneous cubic in four variables over a characteristic-zero field \(K\), with smooth projective zero set. For every \(q\ge 1\) and homogeneous \(B\) of degree \(3\cdot q-1\), there is a rational field \(w_q\), with components of degree \(3\cdot q-3\), satisfying \(q w_q(G)=B\) and \(\operatorname{div} w_q=0\). Its denominator is coprime to \(G\).

We use the following classical geometric input. Over an algebraic closure, a smooth cubic surface is the blowup of \(\mathbb P^{2}\) at six points in general position; in particular it has six mutually skew lines, Picard rank seven, and 27 lines in total. These statements include special smooth cubics; see [Huybrechts, Chapter 4, §3](https://www.math.uni-bonn.de/people/huybrech/Notes.pdf). The residue realization needed below is the specialization of [Villaflor Loyola, Theorem 1.1](https://arxiv.org/pdf/1812.03964): if \(G=\ell _{1}Q_{1}+\ell _{2}Q_{2}\) and \(L=V(\ell _{1},\ell _{2})\), then \(\operatorname{Res}(\operatorname{det} d(\ell _{1},Q_{1},\ell _{2},Q_{2})\Omega /G^{2})\) is a fixed nonzero scalar times \(H_S-3[L]\), the scalar depending only on the residue normalization. Together with Griffiths' residue description \(R(G)_{2}\cong H^{2}(S)_{\mathrm{prim}}\), this identifies explicit determinant polynomials with primitive line classes. The remainder of the theorem follows from the calculations below.

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

The induction preserves denominator legality, completing the proof.

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

The four constant fields serving \(G_i\), together with selected functionals of \(J\), give a matrix of quadratic sources. An invertible ten-by-ten minor proves spanning. Localizing the passive coefficient ring at that determinant makes the construction valid throughout the corresponding open set.

## 2.5 The image of a transport map

A complete target map downstairs need not reach every target upstairs. Suppose a linear transformation \(\rho\) fixes a rational map \(\Phi\). Differentiating \(\Phi\rho=\Phi\) gives

\[
\det(d\Phi)(\rho Z)=\det(\rho)^{-1}\det(d\Phi)(Z).
\]

Thus every target \(\det(d\Phi)B(\Phi)\) has this same character. For a reflection it is odd. This restriction follows from the differential-form density, even when the auxiliary equation has no restriction on its targets. The averaging criterion in [Chapter 3](#technical-information/geometric-support) describes how the images of several such maps combine.

First integrals provide another general operation. If \(qv(F)=A\), \(\operatorname{div}v=0\), and \(v(r_j)=0\), then for any rational function \(h(r)\),

\[
q(hv)(F)=hA,\qquad
\operatorname{div}(hv)=h\operatorname{div}v+v(h)=0.
\]

When the \(r_j\) have degree zero, multiplication by \(h\) preserves the component degree. To obtain a polynomial target, \(hA\) must be polynomial of the required degree and character, and the additional poles must be coprime to \(F\).

As an example of a weighted density map, take
\(\Phi=(Q_1,Q_2,Q_3,Q_4,r,s)\), with four quadratic and two linear coordinates. A smooth sextic \(F=H(\Phi)\) has an auxiliary equation of weights \((2,2,2,2,1,1)\). The determinant has degree four, so a density of weight \(6q-4\) gives a target of degree \(6q\). This is an instance of the finite weighted-Fano theorem in [Chapter 3](#technical-information/geometric-support/34-nonlinear-polynomial-piola-maps-are-finite-fano-maps). The determinant records precisely which targets come from this presentation.

## 2.6 Coefficient differentiation

A family of certificates can be differentiated to raise the pole order. Write

\[
K_q(F,A;v)=A-qv(F)+F\operatorname{div}v,
\qquad F_t=F+tT,
\]

and suppose \(A\) is independent of \(t\). Assume that \(v_q(t)\) is defined in a coefficient family regular at \(t=0\); a dot denotes its coefficient derivative there. Put

\[
W=\frac{qTv_q-F\dot v_q}{q+1}.
\]

The product rules give the exact identity

\[
K_{q+1}(F,AT;W)
=T K_q(F,A;v_q)-\frac{F}{q+1}
\left.\partial_tK_q(F_t,A;v_q(t))\right|_{t=0}.
\]

Consequently,

\[
K_q(F_t,A;v_q(t))=F_t^{q+1}R_t
\quad\Longrightarrow\quad
K_{q+1}(F,AT;W)=-\frac{F^{q+2}\dot R}{q+1}.
\]

The component degree increases from \(6q-5\) to \(6(q+1)-5\), and the required character is preserved when \(T\) is even. If \(v_q(t)=N(t)/D(t)\), with polynomial \(N,D\) coefficientwise regular at zero and \(D(0)\) coprime to \(F\), then \(W\) has a legal denominator dividing \(D(0)^2\). This uses a denominator for the whole family; cancellation in \(v_q(0)\) need not persist in its derivative. The operation requires a coefficient family or a derivation on its coefficient field; an isolated certificate does not supply its derivative.

For the normalized input \(qv_q(t)(F_t)=A\), \(\operatorname{div}v_q(t)=0\), the Euler correction

\[
v_{q+1}=W-\frac{v_q(T)}{6(q+1)}E_6
\]

retains both separate identities. Indeed,
\(W(F)=(AT+Fv_q(T))/(q+1)\) and
\(\operatorname{div}W=v_q(T)\). Since \(v_q(T)\) has degree \(6q\), the Euler correction has value \(Fv_q(T)/(q+1)\) on \(F\) and divergence \(v_q(T)\). Thus \((q+1)v_{q+1}(F)=AT\) and \(\operatorname{div}v_{q+1}=0\).

## 2.7 Creating a reflection on a finite cover

A reflection useful for support can appear on a finite cover without acting on the original hypersurface. The quotient geometry and the trace back to the original variety are distinct parts of this method.

For a general illustration, let \(f(X)\) be a ternary sextic and \(L_0(X),L_2(X)\) quartics, and consider

\[
F=f(X)+Y_0^6+Y_1^6+Y_2^6
  +Y_1\bigl(Y_0L_0(X)+Y_2L_2(X)\bigr).
\]

Adjoin \(T^6=Y_0^6+Y_2^6\), set \(\alpha=Y_0/T\), \(\beta=Y_2/T\), and write \(y=Y_1\). The base is the Fermat curve \(\alpha^6+\beta^6=1\). Over its function field, the equation is symmetric in \(y,T\). The exchange quotient, with \(S=y^2+T^2\), \(P=yT\), is

\[
H=f(X)+P\bigl(\alpha L_0(X)+\beta L_2(X)\bigr)
  +S^3-3SP^2.
\]

Its coordinate weights are \((1,1,1,2,2)\). The Fano support and quotient-descent results of Chapter 3, §§3.1–3.2, apply when their geometric hypotheses hold. The coordinate identity itself requires no choice of a curve or primitive on this quotient.

### Polynomial integration on a finite parameterization

Here is the algebraic integration principle used with such quotients. Let \(K\) be a function field of transcendence degree \(n\) over a fixed characteristic-zero field \(k\). Suppose a finite separable extension \(L/K\) has a presentation \(L=E(t)\), where \(E/k\) has transcendence degree \(n-1\), and a rational top form \(\omega\) on \(K\) pulls back to

\[
\omega_L=\left(\sum_{j=0}^m c_jt^j\right)dt\wedge\eta,
\qquad c_j\in E,
\qquad \eta\in\Omega_E^{n-1}.
\]

Then

\[
\beta=\left(\sum_{j=0}^m\frac{c_jt^{j+1}}{j+1}\right)\eta
\quad\text{satisfies}\quad d\beta=\omega_L.
\]

The terms differentiated in \(E\) vanish after wedging with its top form \(\eta\). Field trace commutes with exterior differentiation: derivations extend uniquely through finite separable extensions, and differentiating the sum of conjugates gives the trace identity. Therefore \([L:K]^{-1}\operatorname{Tr}_{L/K}\beta\) is a primitive of \(\omega\).

A dominant family of polynomial curves can provide the presentation \(E(t)\). For a hypersurface \(H=0\), a polynomial normal \(\psi(t)\) satisfying \(\nabla H(\phi(t))\cdot\psi(t)=1\), together with the curve tangent and independent endpoint derivatives, supplies the residue-volume determinant. The Piola identity then tests whether the pulled-back source has the polynomial form above. Dominance, finiteness, a nonzero determinant, and polynomiality of the source must all be established. The existence of a rational curve alone does not give this integration theorem for arbitrary rational densities.

### Selecting a source by trace

Choose \(\beta\) as a coordinate on the Fermat base. For the full physical-to-quotient map, including this base coordinate, the Jacobian is

\[
J_c=\frac{2\alpha^5(T^2-y^2)}{T}.
\]

It includes the derivatives of the ratios \(\alpha,\beta\). Suppose the quotient has a residue primitive for a polynomial source \(B\). Choose a common normal coordinate, say \(X_0\). If

\[
J_cB=A-Ct,\qquad
J_c\partial_{X_0}B=\partial_{X_0}A-(\partial_{X_0}C)t,
\qquad \operatorname{Tr}(t)=0,
\]

where \(A,C\) are physical functions and the trace is normalized over the physical function field, Piola transport and trace give the source associated with \(A\). Both displayed source identities matter because a differentiated residue depends on \(B\) and its normal derivative.

For example,

\[
B=\frac{X_0^3S}{2\alpha^2}
\quad\Longrightarrow\quad
J_cB=X_0^3Y_0^3-X_0^3Y_0^3Y_1^4T^{-4}.
\]

The deck action sends \((T,\alpha,\beta)\) to
\((\zeta T,\zeta^{-1}\alpha,\zeta^{-1}\beta)\), with \(\zeta^6=1\), while fixing all physical coordinates. The correction has a nontrivial deck character and hence trace zero. This computation identifies the image of a quotient primitive; the existence of that primitive is a separate hypothesis.

### Clearing a residue primitive

On a hypersurface \(F=0\), put \(g_i=\partial_iF\), with \(g_0\ne0\) in its function field, and let

\[
\mathcal E_i=\partial_i-\frac{g_i}{g_0}\partial_0
\qquad(i>0).
\]

Suppose \(w_i=n_i/d\), with \(d\ne0\) in this field, satisfies

\[
\frac{\partial_0A}{g_0}-\frac{A\partial_0g_0}{g_0^2}
+\sum_{i>0}\left(\mathcal E_iw_i-w_i\frac{\mathcal E_ig_0}{g_0}\right)=0.
\]

For polynomial representatives define

\[
D=g_0d,\qquad
N_0=Ad-\sum_{i>0}g_in_i,\qquad
N_i=g_0n_i\quad(i>0).
\]

Then \(N(F)=AD\) identically. The residue equation says that
\(D\operatorname{div}N-N(D)\) vanishes modulo \(F\), so it is \(FQ\) for some polynomial \(Q\). The cleared pole-one defect is therefore \(F^2Q\). If \(F\) is irreducible, nonvanishing of \(g_0d\) in its function field gives denominator legality.

For homogeneous sextics \(F,A\), homogeneity can also be recovered algebraically. Write \(V=N/D\). Since \((F)\) is a homogeneous ideal, remove from \(D\) every homogeneous component divisible by \(F\), obtaining \(D'=D+FU\) whose lowest nonzero component \(D'_e\) is not divisible by \(F\). Put

\[
V'=\frac{D}{D'}V+\frac{FU}{g_0D'}A\partial_0.
\]

Then \(V'(F)=A\), and \(V'-V=FW\) with \(W(F)=0\). Hence \(\operatorname{div}V'\) still vanishes modulo \(F\). Expand \(V'(tZ)\) as a Laurent series at \(t=0\) and retain its \(t^1\) coefficient. This is a rational field with homogeneous components of degree one; its denominator is a power of \(g_0D'_e\), so is legal. The normal and divergence identities, compared coefficientwise, show that it sends \(F\) to \(A\) and has divergence divisible by \(F\). Only finitely many terms of the expansion contribute to this coefficient. Clearing its denominator gives a homogeneous pole-one certificate, and the averaging of Chapter 1 gives the required involution character.

## 2.8 A cyclic quotient and its density character

The same family illustrates a complementary quotient. Let \(g\) fix \(X\) and act on \((Y_0,Y_1,Y_2)\) with weights \((5,1,5)\) modulo six. Its invariant coordinates on a rational open include

\[
p=Y_0Y_1,\qquad v=Y_1Y_2,\qquad
\lambda=\frac{Y_1^3}{Y_0^3+iY_2^3},\qquad i^2=-1.
\]

Over \(k=\mathbb C(\lambda)\), the equation becomes

\[
K=f(X)+L_0(X)p+L_2(X)v
  +(\lambda+\lambda^{-1})p^3
  +i(\lambda-\lambda^{-1})v^3.
\]

For \(\theta=(X_0,X_1,X_2,p,v,\lambda)\), direct differentiation gives

\[
K(\theta)=F,\qquad \det(d\theta)=-6\lambda Y_1.
\]

This determinant determines the source on the quotient. For a sextic monomial \(A=M(X)Y_0^aY_1^bY_2^c\) whose residue is \(g\)-invariant, put \(e=b-a-c-1\). The invariant condition is \(e\equiv0\pmod6\), because the volume form contributes the character \(\zeta^5\). The two possible exponents are \(e=0,-6\), and

\[
\frac{A}{\det(d\theta)}=
\begin{cases}
-\dfrac{M(X)p^av^c}{6\lambda},&e=0,\\[6pt]
-\dfrac{M(X)p^av^c}{6\lambda^2(p^3+iv^3)},&e=-6.
\end{cases}
\]

The second expression uses \(Y_1^6=\lambda(p^3+iv^3)\). Thus one character can contain both polynomial and rational fiber densities. The polynomial integration principle of §2.7 applies only after checking its source hypothesis. The deck/exchange criterion of Chapter 3, §3.1, can establish support without such a polynomial presentation. This example explains why the image of an integration formula and the invariant cohomology of its quotient are different objects.

## 2.9 Moving cubic maps and Jacobian residue transport

A genus-one curve can have a useful map to its Jacobian even when the curve has no chosen rational origin. For a family of cubics, this map varies with the coefficients. Transporting a differentiated residue requires both its invariant differential and the correction caused by that variation.

### Change of normal density

For commuting tangent derivations \(\partial_i\) and a nonzero normal derivative \(g\), write

\[
\operatorname{ResDiv}_g(w)
 =\sum_i\partial_iw_i-\frac{\sum_iw_i\partial_i g}{g}
 =g\sum_i\partial_i(w_i/g).
\]

If \(M\) is the coordinate Jacobian, \(N=M^{-1}\), and the new normal derivative is \(h\), then

\[
\operatorname{ResDiv}_g\left(\frac gh\det(M)Nw\right)
 =\frac gh\det(M)\operatorname{ResDiv}_h(w).
\]

The identity with density \(h\) is the Piola identity of §2.1; multiplying the vector by \(g/h\) changes the density to \(g\). Both the normal ratio and the determinant are required, and derivatives of parameter ratios are part of the coordinate calculation.

For a balanced numerator there is a direct normal-chart identity. Let \(p,q\) be two coordinates, put \(f=F_p\), \(g=F_q\), and take \(A=Bpq\) with \(B\) independent of \(p,q\). Define

\[
G=pf+qg,\qquad H=p^2F_{pp}+2pqF_{pq}+q^2F_{qq},\qquad
D=\partial_q-\frac gf\partial_p.
\]

When \(f,G\ne0\), the correction \(C=-Bpq^2/G\) satisfies

\[
\frac{A_p}{f}-\frac{AF_{pp}}{f^2}
 =\frac{A(3G-H)}{G^2}+DC-C\frac{Df}{f}.
\]

Expanding both sides by the product and quotient rules proves the identity. The last two terms are the residue divergence of a vector with \(q\)-component \(C\), giving the correction for the change of normal.

### First variation of a Weierstrass map

Let \(D\) be a tangent derivation on a characteristic-zero field. Suppose

\[
\eta^2=\xi^3+a\xi+b,\qquad Da=Db=0,
\qquad \frac{D\xi}{2\eta}=\frac m g,
\]

with \(m,g,\eta\ne0\). A dot denotes a compatible first variation fixing the tangent coordinate and \(m\). Differentiating gives

\[
2\eta\dot\eta=(3\xi^2+a)\dot\xi+\dot a\xi+\dot b,
\qquad
\frac{D\dot\xi}{2\eta}-\frac{D\xi\dot\eta}{2\eta^2}
 =-\frac{m\dot g}{g^2}.
\]

Differentiate the curve equation with \(D\), substitute these relations, and collect terms:

\[
\boxed{\frac{\dot g}{g}
 =\frac{\dot a\xi+\dot b}{2\eta^2}
  -\frac g m D\left(\frac{\dot\xi}{2\eta}\right).}
\]

The last term is the exact differential correction produced by the moving map. These hypotheses can be established at a single coefficient value using dual numbers \(K[\epsilon]/(\epsilon^2)\): prove the curve and differential identities for the first-order deformation and compare their two coefficients. Differentiation in an auxiliary coefficient need not be a derivation on the already specialized function field.

### Reducing a source variation

A volume-preserving coordinate change can simplify both a cubic and its required first variation. Let \(U\) be homogeneous, let \(Q\) have the same degree, and let \(v(x)=Mx\) with \(\operatorname{tr}M=0\). For \(\epsilon^2=0\),

\[
(U+\epsilon Q)(x+\epsilon v(x))
 =U+\epsilon\left(Q+\sum_i v_iU_{x_i}\right),
\qquad \det(1+\epsilon M)=1.
\]

Thus the source variation may be reduced modulo these Jacobian directions before applying a covariant formula for the Jacobian curve. The coordinate change and its normal correction remain part of the residue calculation. For a derivation \(\delta\) and \(g\ne0\), the relevant scalar identity is

\[
\delta\!\left(\frac{h-cg}{g}\right)
 =\delta\!\left(\frac h g\right)-\delta c.
\]

When \(\delta c=0\), replacing \(h\) by \(h-cg\) preserves the complete normal expression \((\delta h)/g-h\delta g/g^2\). Otherwise the correction \(-\delta c\) must be retained. Finite separable extensions used to choose coordinates carry the extended derivations, and normalized trace descends a primitive for an original-field source. These identities apply independently of any particular cubic family; the surface quotient in Chapter 4 supplies a geometric setting for their use.
