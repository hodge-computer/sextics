# 2a. Binary blocks: finite contact covers and target spanning

[Previous: explicit constructions](#technical-information/explicit-constructions) · [Contents](#technical-information/introduction) · [Next: geometric support](#technical-information/geometric-support)

This chapter constructs strict certificates for every target on the binary-block family below at \(q=1,2\). Ordinary certificate existence on this family, at every positive pole order, also follows from the [two-reflection support theorem](#technical-information/weighted-threefolds), because \(X_2\) and \(Y_2\) are separate reflection coordinates. The constructions here specify finite algebraic operations and prove strictness. As in Chapter 2, finite covers produce cofactor fields and a spanning theorem for their targets completes the construction. Here the cover is the nonzero three-torsion of a genus-two Jacobian. Its two relevant moment spaces are proved below; no numerical rank test enters the theorem.

**Theorem.** Let

\[
\begin{gathered}
F=P_{0}(X_{0},X_{1})+P_{1}(Y_{0},Y_{1})+P_{2}(X_{2}^{2},Y_{2}^{2}),
\end{gathered}
\]

where \(P_{0},P_{1}\) are binary sextics and \(P_{2}\) is a binary cubic over an effectively presented characteristic-zero field. Suppose \(F=0\) is smooth. For \(q=1,2\) and every allowed \(Y\)-odd \(A\) of degree \(6\cdot q\), there is a constructive strict certificate, after Euler normalization if necessary. Finite trace gives a certificate over the original field. No uniform denominator-degree bound is asserted.

Write the three binary variable blocks as \(V_{0},V_{1},V_{2}\), and let \(P_{i}\) also denote the ordinary sextic in its block. Smoothness is equivalent to squarefreeness of all three sextics. Indeed, a multiple projective root of one block gives a nonzero zero of both its partials and hence a singular point of \(F\) with the other blocks zero. Conversely, the partials of a squarefree binary form vanish simultaneously only at the origin. For the third block, squarefreeness says that the endpoint coefficients and discriminant of \(P_{2}\) are nonzero.

## 2a.1 The elementary fields behind the construction

Suppose a block admits \(P_{i}=C_{i}^{3}+r_{i}^{2}\), with \(\operatorname{deg} C_{i}=2\) and \(\operatorname{deg} r_{i}=3\). Put

\[
\begin{gathered}
J_{i}=\{C_{i},r_{i}\}=C_{i,x}r_{i,y}-C_{i,y}r_{i,x},\\
e_{i}=r_{i}(-C_{i,y}\partial _{x}+C_{i,x}\partial _y)/(2\cdot J_{i}).
\end{gathered}
\]

Direct differentiation gives \(e_{i}(C_{i})=0, e_{i}(r_{i}^{2})=r_{i}^{2}\), and \(\operatorname{div}(J_{i}e_{i})=J_{i}/2\). In the last identity, the Hamiltonian field of \(C_{i}\) has zero divergence and takes \(r_{i}\) to \(J_{i}\). Squarefreeness implies \(J_{i}\ne 0\): otherwise \(C_{i}\) and \(r_{i}\) would be algebraically dependent, so \(P_{i}\) could not be squarefree.

For a different block \(j\) let \(E_{j}\) be its Euler field and set \(e=e_{i}+E_{j}/6\) and \(D=r_{i}^{2}+P_{j}\). Then \(e(F)=e(D)=D\). If a cubic multiplier \(M\) satisfies \(e(M)=M/6\), the field

\[
\begin{gathered}
v=J_{i}M e/D
\end{gathered}
\]

is strict for \(J_{i}M\). Indeed \(\operatorname{div}(J_{i}e)=5\cdot J_{i}/6\), so \(\operatorname{div}(J_i M e)=J_i M\); differentiation of \(1/D\) cancels this divergence. Two useful choices are \(M=C_{i}L_{j}\) and \(M=L_{j}Q_{k}\), where \(L_{j}\) is linear in block \(j, Q_{k}\) is quadratic in the remaining block, and \(i,j,k\) are distinct. They supply the \(C\cdot J\)-times-linear and raw-\(J\)-times-(linear,quadratic) packets.

For two decomposed blocks \(i,j\), take \(e=e_{i}+e_{j}, D=r_{i}^{2}+r_{j}^{2}\), and \(A=J_{i}J_{j}\). The same calculation gives \(e(F)=e(D)=D\) and \(\operatorname{div}(Ae)=A\). Hence \(Ae/D\) is strict for \(A\). Multiplying it by a homogeneous degree-six first integral \(\beta \) and dividing by two gives a strict \(q=2\) field for \(\beta A\). In particular \(\beta =C_{i}C_{j}Q_{k}\) gives the \(C\cdot J\times C\cdot J\) packet.

All these numerators are polynomial after multiplication by their displayed Jacobians. Their denominators involve only two blocks, whereas smooth \(F\) has a nonzero third block, so they are coprime to \(F\). The fields can be averaged for global \(Y\)-parity and traced in their coefficient fields. Polynomial fields \(L_{j}\partial _{x}\) and \(L_{j}\partial _y\) additionally serve \(L_{j}P_{i,x},L_{j}P_{i,y}\) strictly. Thus the remaining question is exactly what the cubics \(J\) and quintics \(C\cdot J\) span as the decompositions vary.

## 2a.2 The forty-sheet contact cover

For every squarefree binary sextic \(P\), the presentations

\[
\begin{gathered}
P=C^{3}+r^{2},       \operatorname{deg} C=2,       \operatorname{deg} r=3,
\end{gathered}
\]

modulo \(C\mapsto \zeta _{3}C\) and \(r\mapsto -r\) form a finite étale cover of degree 40. Keeping these normalizations gives degree 240. This includes quadratic forms with double roots and all affine degree-drop charts; \(C\) and \(r\) remain homogeneous binary forms throughout.

To prove the claim, let \(C_P\) be the smooth genus-two curve \(w^{2}=P\). Its canonical bundle is the pullback of \(\mathcal O_{\mathbb P^{1}}(1)\). For nonzero \(T\in \operatorname{Jac}(C_P)[3]\), the degree-two line bundle \(L=K_{C_P}\otimes T\) has exactly one section up to scalar, by Riemann–Roch and \(H^{0}(T^{-1})=0\). If \(s\) is such a section, then \(s^{3}\) belongs to \(H^{0}(K^{3})=\operatorname{Sym}^{3}H^{0}(K)\oplus kw\), so \(s^3=r+a\cdot w\).

Here \(a\ne 0\). If \(a=0\), the divisor \(3\operatorname{div}(s)\) is pulled back from \(\mathbb P^{1}\), forcing \(\operatorname{div}(s)\) to be a canonical fiber: at a branch point a pulled-back multiplicity is even, and at an unramified fiber its two multiplicities agree. A degree-two divisor with these properties is canonical, which would give \(T=0\). Normalize \(a\), and multiply the identity for \(s^{3}\) by its hyperelliptic conjugate. Since the involution sends \(T\) to \(T^{-1}\), the product \(s\iota (s)\) is a quadratic canonical section. After a harmless sign and cube-root normalization the result is \(P=C^{3}+r^{2}\).

Conversely, squarefreeness forces \(\operatorname{gcd}(C,r)=1\). The identity \((w-r)(w+r)=C^{3}\) then gives \(\operatorname{div}(w-r)=3\cdot D\) for an effective degree-two divisor \(D\), and \(\mathcal O(D)\otimes K^{-1}\) is nonzero three-torsion. It cannot be zero: a canonical fiber would contain both conjugate points, whereas \(w-r\) vanishes on only one of them; branch fibers would force a common zero of \(C\) and \(r\). Changing the sign of \(r\) interchanges \(T\) and \(-T\). These operations are inverse.

Multiplication by three on a characteristic-zero abelian surface is étale of degree \(3^{4}=81\). Removing zero and dividing by the free inversion involution gives 40 sheets. One can also check étaleness of the normalized polynomial system directly: its differential is

\[
\begin{gathered}
(\delta C,\delta r) \mapsto  3\cdot C^{2}\delta C+2\cdot r\delta r.
\end{gathered}
\]

If it vanishes, coprimality forces \(r\) to divide \(\delta C\), which has degree two; thus \(\delta C=\delta r=0\). The seven-dimensional coefficient spaces therefore have invertible differential at every presentation. This also proves the coefficientwise lifting used later.

## 2a.3 Raw Wronskians span every cubic

**Raw moment theorem.** For every squarefree \(P\), the cubics \(J=\{C,r\}\) from the contact cover span \(\operatorname{Sym}^{3}\) of the binary variables.

Here is an explicit determinant proof. Rescale one initial presentation to \(P=U^{3}-V^{2}\) and form the plane cubic \(E:z^{3}-3\cdot U\cdot z+2\cdot V=0\). It is smooth. Indeed, a singular point satisfies \(z^{2}=U\) and \(V=z^{3}\); differentiating \(P\) then gives \(dP=0\). If \(z=0, U=V=0\) already makes \(P\) nonsquarefree. Either possibility contradicts the hypothesis.

For any flex tangent \(z=\xi \), where \(\xi \) is binary linear, restriction of \(E\) to the tangent is the cube of a linear form \(\eta \):

\[
\begin{gathered}
\eta ^{3}=\xi ^{3}-3\cdot U\cdot\xi +2\cdot V.
\end{gathered}
\]

For each \(\zeta ^{3}=1\) put

\[
\begin{gathered}
C_\zeta =U-\xi ^{2}-\zeta\cdot\xi\cdot\eta -\zeta ^{2}\cdot \eta ^{2},\\
S_\zeta =\eta ^{3}+2\cdot \zeta ^{2}\cdot \eta ^{2}\cdot \xi +2\cdot \zeta\cdot\eta\cdot\xi ^{2}+\xi ^{3}-2\cdot \zeta\cdot\eta\cdot U-\xi\cdot U.
\end{gathered}
\]

Expansion gives \(C_\zeta ^{3}+3\cdot S_\zeta ^{2}/4=P\). Thus these are presentations on the same cover after scaling \(S_\zeta \) by \(\sqrt 3/2\). Their Wronskians satisfy

\[
\begin{gathered}
\{C_\zeta ,S_\zeta \}=-2\{U,V\}/3+\zeta\cdot R,\\
R=(\xi ^{2}-2\cdot U)\{U,\eta \}-\xi\cdot\eta \{U,\xi \}+2\{\xi ,\eta \}V.
\end{gathered}
\]

Both identities follow by substituting \(2\cdot V=\eta ^{3}-\xi ^{3}+3\cdot U\cdot\xi \) and collecting powers of \(\zeta \) modulo \(\zeta ^{3}-1\). In particular each flex contributes the direction \(R\) to the span of the cover's raw Wronskians.

Over an algebraic closure put \(E\) in Hesse form \(X^{3}+Y^{3}+Z^{3}-3\cdot \kappa\cdot X\cdot Y\cdot Z\) and its projection center at \(O=(a:b:1)\). The Hesse normal-form theorem says that every smooth plane cubic over an algebraically closed characteristic-zero field is projectively equivalent to such a member; see [Artebani–Dolgachev, Lemma 1](https://arxiv.org/pdf/math/0611590). The center is outside \(E\), and outside every flex tangent: projection along a flex tangent has ramification order three and gives a multiple branch point, contradicting squarefreeness of \(P\).

The following formulas specify a nonzero maximal determinant without any elimination. Write

\[
\begin{gathered}
e=a^{3}+b^{3}+1-3\cdot \kappa\cdot a\cdot b,\\
L=(a^{2}-\kappa\cdot b)x+(b^{2}-\kappa\cdot a)y,\\
q_{0}=3\cdot a\cdot x^{2}+3\cdot b\cdot y^{2}-3\cdot \kappa\cdot x\cdot y,       c_{0}=x^{3}+y^{3},\\
\overline{U}=L^{2}-e\cdot q_{0}/3,\\
\overline{V}=e^{2}c_{0}/2-e\cdot q_{0}L/2+L^{3}.
\end{gathered}
\]

Depressing the projection coordinate gives \(U=\overline{U}/e^{2}\) and \(V=\overline{V}/e^{3}\). For a flex \(p=(p_{0}:p_{1}:p_{2})\), let \((t_{0},t_{1},t_{2})=\nabla E(p), T=t_{0}\cdot a+t_{1}\cdot b+t_{2}\), and define

\[
\begin{gathered}
\overline{\xi }=T\cdot L-e(t_{0}\cdot x+t_{1}\cdot y),\\
\eta =(p_{1}-b\cdot p_{2})x-(p_{0}-a\cdot p_{2})y,\\
\overline{R}_p=(\overline{\xi }^{2}-2\overline{U}T^{2})\{\overline{U},\eta \}-\overline{\xi }\eta \{\overline{U},\overline{\xi }\}+2\cdot T\{\overline{\xi },\eta \}\overline{V}.
\end{gathered}
\]

This is a nonzero scalar multiple of the flex direction \(R\), after clearing the nonzero denominators \(e,T\) and normalizing \(\eta \). Let \(M\) be the coefficient matrix, in the basis \(x^3,x^2\cdot y,x\cdot y^2,y^3\), of

\[
\begin{gathered}
\{\overline{U},\overline{V}\}, \overline{R}_{(0:1:-1)}, \overline{R}_{(0:1:-\zeta )}, \overline{R}_{(1:0:-1)},\\
\zeta ^{2}+\zeta +1=0.
\end{gathered}
\]

Writing

\[
\begin{gathered}
l_{1}=a+b+\kappa ,              l_{2}=a+\zeta\cdot b+\zeta ^{2}\cdot \kappa ,       l_{3}=a+\zeta ^{2}b+\zeta \kappa ,\\
l_{4}=a\kappa +\zeta\cdot b+\zeta ^{2},           l_{5}=b\kappa +\zeta ^{2}a+\zeta ,       l_{6}=b\kappa +\zeta\cdot a+\zeta ^{2},\\
l_{7}=a\kappa +b+1,             l_{8}=a\kappa +\zeta ^{2}b+\zeta ,       l_{9}=b\kappa +a+1,
\end{gathered}
\]

coefficient expansion gives, up to the sign determined by column order,

\[
\begin{gathered}
\operatorname{det} M=8748(\zeta +2)e^{5}l_{1}\cdot l_{2}\cdot l_{3}\cdot l_{4}\cdot l_{5}\cdot l_{6}\cdot l_{7}^{4}\cdot l_{8}^{4}\cdot l_{9}^{4}.
\end{gathered}
\]

The nine \(l_{i}\) are the nine flex-tangent evaluations at \(O\) up to nonzero constants. Thus every factor is nonzero. This proves rank four in the Hesse chart. Projective changes of the plane and linear changes of the projection pencil preserve the span rank, proving the theorem for every squarefree \(P\). The displayed matrix and factorization reduce the rank claim to an explicit polynomial identity.

## 2a.4 The quintic moment theorem

**Theorem.** For every squarefree binary sextic \(P\) over an algebraically closed field of characteristic zero, the forty decompositions \(P=C^{3}+r^{2}\) give classes \(C\{C,r\}\) spanning the four-dimensional quotient \(S_{5}/\langle P_x,P_y\rangle \). Together with \(P_x,P_y\) they therefore span all binary quintics.

**Proof: residue duality.** Put \(S=k[x,y]\) and \(J=\{C,r\}\). The complete intersection \(R=S/(P_x,P_y)\) has socle degree eight. Its residue pairing identifies \(R_{5}\) with the dual of \(R_{3}=S_{3}\), both of dimension four. The polynomial identity

\[
\begin{gathered}
\begin{pmatrix}P_x\\P_y\end{pmatrix}
=\begin{pmatrix}2\cdot r_x&3\cdot C_x\\2\cdot r_y&3\cdot C_y\end{pmatrix}
\cdot\begin{pmatrix}r\\C^2\end{pmatrix},\\
\det\begin{pmatrix}2\cdot r_x&3\cdot C_x\\2\cdot r_y&3\cdot C_y\end{pmatrix}=-6\cdot J
\end{gathered}
\]

and the transformation law for complete-intersection residues give

\[
\begin{gathered}
\operatorname{Res}_{P_x,P_y}(B\cdot C\cdot J)=-\operatorname{Res}_{r,C^{2}}(B\cdot C)/6,       B\in S_{3}.
\end{gathered}
\]

For \(C=a(t-\alpha )(t-\beta )\), the right-hand functional, up to its fixed nonzero scalar, is

\[
\begin{gathered}
\ell _{C,r}(B)=[B(\alpha )r(\beta )-B(\beta )r(\alpha )]/[a(\alpha -\beta )r(\alpha )r(\beta )].
\end{gathered}
\]

Indeed, reducing the one-variable residue to the two simple roots of \(C\) gives \(\sum _{C(t)=0}B(t)/(r(t)C'(t))\). Squarefreeness of \(P\) forces \(\operatorname{gcd}(C,r)=1\), so the denominators are nonzero. At \(\alpha =\beta \) the expression has the limit \([B'(\alpha )r(\alpha )-B(\alpha )r'(\alpha )]/[a r(\alpha )^{2}]\). The homogeneous residue construction includes roots at infinity. In particular, the kernel is \(\langle r\rangle +C S_{1}\), of dimension three.

**The global divisor defined by a missing moment.** Let \(H=\{w^{2}=P(x,y)\}\) be the genus-two curve and \(A=\operatorname{Jac}(H)\). Suppose a nonzero \(B\in S_{3}\) annihilated all forty \(C\cdot J\) classes. In \(H^{0}(H,3\cdot K_H)=S_3\oplus kw\), consider on \(H\times H\) the antisymmetric section

\[
\begin{gathered}
s_B(p,q)=B(p)w(q)-B(q)w(p).
\end{gathered}
\]

It is not identically zero because \(B\) and \(w\) are independent. It vanishes on the diagonal \(\Delta \). After removing \(\Delta \) it descends to a nonzero section on \(H^{(2)}=\operatorname{Sym}^2H\), since the sign change of the diagonal factor cancels the antisymmetry.

Here is its divisor class, with all multiplicities retained. Let \(x\) be the class of \(\{p_{0}+q\}\) on \(H^{(2)}\), choosing a Weierstrass point \(p_{0}\), and let \(\delta \) denote its diagonal. The canonical bundle of \(H\) is \(\mathcal O_H(2\cdot p_{0})\). Therefore the section before division has class \(6\cdot x\), and its descended divisor has numerical class \(6\cdot x-\delta /2\). The Abel map \(a:H^{(2)}\to A, D\mapsto\mathcal O(D-K_H)\), is the blowup of the origin. Riemann–Roch gives its unique point over each nonzero class and its exceptional curve \(E=|K_H|\) over zero; the graph of the hyperelliptic involution in \(H\times H\) has self-intersection \(-2\), so \(E^{2}=-1\). The quotient canonical formula gives \(K_{H^{(2)}}=2\cdot x-\delta /2\). Since \(K_A=0\), this is \(E\). A translate \(\Theta \) of the principal polarization has strict transform \(x\), hence \(a^*\Theta=x+E\). Consequently

\[
\begin{gathered}
6\cdot x-\delta /2=4\cdot a^{*}\Theta -3\cdot E.
\end{gathered}
\]

Pushing the effective divisor of \(s_B/\Delta \) to \(A\) gives a nonzero effective divisor \(Z_B\) of numerical class \(4\Theta \). In particular, \(Z_B\cdot \Theta =8\).

For every nonzero \(T\in A[3]\), its unique divisor \(D=p+q\) with \(\mathcal O(D)=K_H\otimes T\) comes from one of our decompositions. At the roots \(\alpha ,\beta \) of \(C\) its points have \(w=r\), so \(s_B(p,q)=0\) is exactly \(\ell _{C,r}(B)=0\). At double support the divided-diagonal value is the tangent expression above: on \(C=0\), differentiating \(P=C^{3}+r^{2}\) gives \(w'=r'\). Thus \(Z_B\) contains all eighty nonzero three-torsion points, including all double-support and infinity cases. We now exclude that possibility.

**A torsion-intersection bound.** Let \(G=A[3]\), of order 81, and let \(Z\) be any effective divisor of \(\Theta \)-degree at most eight on the indecomposable principally polarized surface \(A\). Every irreducible component \(E\) has \(a=E\cdot\Theta\ge2\). For \(E^{2}>0\) this follows from the Hodge index inequality \(E^{2}\le a^{2}/2\) and the fact that \(E^{2}\) is a positive even integer. If \(E^{2}=0, E\) is a translate of an elliptic curve: normalization cannot be rational on an abelian surface, and adjunction forces arithmetic genus one. If an elliptic curve had \(\Theta \)-degree one, the quotient \(A\to A/E\) would restrict to a degree-one map from the smooth genus-two theta curve to an elliptic curve, which is impossible. Such an elliptic translate contains either zero or nine points of \(G\).

Now assume \(E^{2}>0\), put \(m=|E\cap G|\) and \(h=|\operatorname{Stab}(E)\cap G|\). The stabilizer subgroup acts freely, so \(h\) divides \(m\). Passing to its étale quotient gives \(E^{2}=h(E')^{2}\), hence \(h\le E^{2}/2\). Since \(E^{2}\le a^{2}/2\le 32, h\) is one of 1,3,9. Count the \(m^{2}\) ordered pairs of points of \(E\cap G\) by their difference \(g\in G\). The \(h\) stabilizer differences each contribute \(m\); each other translate is a distinct irreducible curve and contributes at most \(E^{2}\) intersection points. Therefore

\[
\begin{gathered}
m^{2} \le  h\cdot m+(81-h)E^{2},       h\mid m,\\
E^{2}\in2\mathbb Z_{>0},       E^{2}\le a^{2}/2,       h\le E^{2}/2.
\end{gathered}
\]

These inequalities give the following upper bounds; the elliptic bound nine is included:

| a | 2 | 3 | 4 | 5 | 6 | 7 | 8 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| Number of points, at most | 13 | 18 | 25 | 31 | 39 | 45 | 51 |

To verify the table, substitute the largest allowed even value of \(E^{2}\), solve the quadratic inequality for \(h=1,3,9\) subject to \(h\le E^{2}/2\), and retain multiples of \(h\). The bounds are deliberately permissive: the additional divisibility \(E^{2}\in 2\cdot h\mathbb Z\) is unnecessary. For a divisor of \(\Theta \)-degree eight, the partitions into component degrees are 2+2+2+2, 2+2+4, 2+3+3, 2+6, 3+5, 4+4 and 8. Their bounds are respectively 52,51,49,52,49,50,51. Multiplicities only overcount the number of distinct torsion points, so the same upper bound 52 holds for nonreduced divisors. A smaller total degree gives no larger bound.

Thus \(Z_B\) cannot contain eighty nonzero points of \(G\). There is no missing \(B\), and residue duality proves that the \(C\cdot J\) packet spans \(R_{5}\). ∎

## 2a.5 Completion at \(q=1\)

The two moment theorems say that raw \(J\) spans every active cubic, and that gradients together with \(C\cdot J\) span every active quintic. The fields in §2a.1 therefore supply the corresponding literal target packets. It remains a finite block-degree argument, which we give explicitly.

For a target monomial let \((d_{0},d_{1},d_{2})\) be its total degrees in the three blocks, so their sum is six. A block Euler field applies whenever one \(d_{i}=4\). All remaining profiles, up to permutation, are (5,1,0), (3,3,0), (3,2,1), (2,2,2), and (6,0,0). The first three are exactly the quintic-linear, two-cubic, and cubic-linear-quadratic packets. For (2,2,2), global \(Y\)-oddness forces the mixed quadratic to be \(X_{2}\cdot Y_{2}\), so the strict cubic-field construction in Chapter 2 serves it. For (6,0,0), the only globally odd targets lie entirely in the mixed block; their \(X_{2}\) and \(Y_{2}\) exponents are both odd, so the same doubly odd construction applies. These alternatives exhaust every monomial.

For reference, counting globally odd monomials in these disjoint packets gives

| Packet | Dimension |
|---|---:|
| A block has degree four: subset Euler | 54 |
| Quintic times a passive linear form | 48 |
| Cubic times passive degrees one and two | 80 |
| Two block cubics | 32 |
| Mixed degree-two character in profile (2,2,2) | 9 |
| Entirely mixed sextic targets | 3 |
| Total | 226 |

The counts use only \(\operatorname{dim}\operatorname{Sym}^d\) of two variables \(=d+1\) and the parity condition \(d_1+\operatorname{deg}_{Y_2} A\) odd; the preceding profile argument proves exhaustion independently of the totals. Linear target separation on the finite covers supplies the required combinations, and normalized trace descends the fields. Every \(q=1\) target thus has a strict certificate.

## 2a.6 Completion at \(q=2\)

The binary Jacobian ring \(k[x,y]/(P_x,P_y)\) is the complete intersection of two quintics, with Hilbert function

\[
\begin{gathered}
h=(1,2,3,4,5,4,3,2,1).
\end{gathered}
\]

This follows from the Hilbert series \((1-t^{5})^{2}/(1-t)^{2}\). The full Jacobian ring of \(F\) is the tensor product of the three block rings. For the mixed even block, its even and odd \(Y_{2}\)-character dimensions in degrees zero through eight are

\[
\begin{gathered}
h_{\mathrm{even}}=(1,1,2,2,3,2,2,1,1),\\
h_{\mathrm{odd}} =(0,1,1,2,2,2,1,1,0).
\end{gathered}
\]

To obtain these, begin with the even/odd monomial counts and subtract the two quintic generators, of opposite parity, times degrees zero through three; their first syzygy has degree ten and does not occur here. Thus the degree-12 globally odd quotient has dimension 866, obtained by summing \(h(d_{0})\cdot h(d_{1})\cdot h_{\mathrm{parity}}(d_{2})\) over \(d_{0}+d_{1}+d_{2}=12\), with even mixed parity when \(d_{1}\) is odd and odd mixed parity otherwise.

First consider profiles with \(d_{0}\ge 6\) or \(d_{1}\ge 6\). Every monomial in that block factors into a binary sextic coefficient direction \(T\) and a remaining monomial. The \(q=1\) theorem, differentiated in the coefficient direction \(T\) by Chapter 2's raising identity, serves the product. If \(d_{2}\ge 7\), the same reasoning works with the mixed block's even sextic directions: multiplication of their four monomials by degrees one or two spans every binary degree-seven or degree-eight monomial. If \(d_{2}=6\) and \(d_{1}\) is odd, the required mixed character is even, so it too is a coefficient direction.

These derivatives exist pointwise at every smooth member. The contact presentations form a finite étale cover. For each target choose spanning columns with a nonzero minor at the point; their inverse coefficient matrix and the polynomial flux formulas have regular formal coefficient lifts. The doubly odd cubic fields have such lifts as well: their cubic-surface lines form a finite étale cover over the passive field, and the line-basis determinant is nonzero. Consequently every fixed target has a local strict family in every coefficient direction used above. The raising identity requires only its first derivative and preserves denominator legality.

Of the remaining profiles, any \(d_{i}=4\) is served by block Euler. Since each \(d_{i}\le 8\) in the quotient, the only profiles not yet covered are

\[
\begin{gathered}
(5,5,2), (5,2,5), (2,5,5).
\end{gathered}
\]

Indeed, the first two degrees are at most five and the third at most six; after excluding four, the only additional possibility with third degree six has odd second degree and was already covered. The \(C\cdot J\) moment theorem spans the degree-five quotient in each of the two active blocks. The first-integral product fields of §2a.1, multiplied by every quadratic in the remaining block, therefore span exactly these three profiles. Their globally odd dimensions are 32,24,24.

This completes the Jacobian quotient. For completeness, a target \(A\) in the degree-12 Jacobian ideal admits a parity-correct polynomial field \(w\) with \(2\cdot w(F)=A\). Put \(B=\operatorname{div} w\) and choose a \(q=1\) field \(u\) serving \(B\). Direct expansion gives

\[
\begin{gathered}
K_{2}(F,A;w+F\cdot u)=F K_{1}(F,B;u)=0.
\end{gathered}
\]

Thus the Jacobian ideal is served too, and Euler normalization supplies a strict field with zero divergence. The construction covers the 866 quotient dimensions and all 2214 Jacobian dimensions, totaling the 3080 allowed degree-twelve monomials. Every step is finite algebraic arithmetic on explicit covers or the cubic-surface construction, and all field extensions are removed by trace. This proves the theorem.
