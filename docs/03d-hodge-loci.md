# 3D. Hodge loci on Fano extensions

[Previous: quadratic nets and pair correspondences](#technical-information/quadratic-nets) · [Contents](#technical-information/introduction) · [Next: families, representations and deformation](#technical-information/known-locus)

A Calabi–Yau threefold can be a fixed section of a varying Fano fourfold. Rational Hodge classes on the fourfold are algebraic, and when the fourfold has more deformations fixing the section than such a class imposes conditions, its algebraic representatives restrict to a moving family of one-cycles on the threefold. The derivative of their Abel–Jacobi images is a product in Jacobian rings. A finite rank calculation can then show that an entire invariant sector of the third cohomology is supported on a divisor.

This is the strategy of [Voisin, Proposition 2.1](https://www.numdam.org/item/ASNSP_1992_4_19_4_473_0.pdf). Chapter 3B follows the same strategy with explicitly constructed curves. Here the curves are supplied by the Hodge conjecture on the Fano fourfold, and the calculation uses only the equations. The chapter applies the method to weighted sextic threefolds with an order-three symmetry that moves the holomorphic three-form, and then to sextic fourfolds with a paired sign and such a symmetry.

## 3D.1 Fixed sections and the dimension count

Let \(S=\mathbb C[z_0,\ldots,z_4,t]\) have weights \((w_0,\ldots,w_4,w_t)\), put \(S_0=\mathbb C[z_0,\ldots,z_4]\) and \(d=w_0+\cdots+w_4\). Let a finite abelian group \(G\) act diagonally, with character \(\chi_t\) on \(t\), and let \(\delta\) be the product of the characters of \(z_0,\ldots,z_4\). For a character \(\chi\), the superscript \([\chi]\) denotes the \(\chi\)-isotypic part.

Let \(\widetilde F\in S_d\) be \(G\)-invariant and \(F_0=\widetilde F|_{t=0}\). Put

\[
Y=\{\widetilde F=0\}\subset\mathbb P(w_0,\ldots,w_4,w_t),
\qquad
T=Y\cap\{t=0\}=\{F_0=0\}\subset\mathbb P(w_0,\ldots,w_4).
\]

Assume that \(Y\) and \(T\) are quasismooth and avoid the singular loci of their ambient spaces. Then both are smooth, \(K_T\) is trivial, and \(K_Y=\mathcal O_Y(-w_t)\), so \(Y\) is a Fano fourfold. Its rational Hodge classes of degree four are algebraic by the [corollary of Chapter 3, §3.2](#technical-information/geometric-support), and weighted weak Lefschetz gives \(H^3(Y)=H^5(Y)=0\).

Let \(R=S/J(\widetilde F)\) and \(R_0=S_0/J(F_0)\) be the Jacobian rings. The weighted residue theorems of [Dolgachev, §4.2–4.3](https://sites.lsa.umich.edu/idolga/wp-content/uploads/sites/1334/2024/08/weighted82.pdf) give

\[
H^{4-p,p}(Y)_{\mathrm{prim}}\simeq R_{pd-w_t},
\qquad
H^{3-j,j}(T)\simeq(R_0)_{jd}.
\]

The residue of \(P\,\Omega/\widetilde F^{p+1}\) has character \(\chi(P)\delta\chi_t\), and the residue of \(B\,\Omega/F_0^{j+1}\) has character \(\chi(B)\delta\). In particular \(G\) acts on \(H^{3,0}(T)\) through \(\delta\), and

\[
H^{2,2}(Y)^G_{\mathrm{prim}}\simeq R_{2d-w_t}^{[(\delta\chi_t)^{-1}]},
\qquad
H^{1,3}(Y)^G\simeq R_{3d-w_t}^{[(\delta\chi_t)^{-1}]},
\qquad
H^{1,2}(T)^G\simeq(R_0)_{2d}^{[\delta^{-1}]}.
\]

A first-order invariant deformation of \(Y\) fixing \(T\) is \(\widetilde F+\varepsilon tK\) with \(K\in S_{d-w_t}^{[\chi_t^{-1}]}\). For \(Q\) representing a class in \(H^{2,2}(Y)^G_{\mathrm{prim}}\), the first-order condition for that class to remain of type \((2,2)\) is the vanishing of

\[
\mu_Q:S_{d-w_t}^{[\chi_t^{-1}]}\longrightarrow R_{3d-w_t}^{[(\delta\chi_t)^{-1}]},
\qquad K\longmapsto[tKQ].
\]

The source has dimension \(n=\dim R_{d-w_t}^{[\chi_t^{-1}]}\) modulo the Jacobian ideal. The socle of \(R\) has degree \(4d-2w_t\) and character \((\delta\chi_t)^{-2}\), so the target is dual to \(R_{d-w_t}^{[(\delta\chi_t)^{-1}]}\). The expected dimension of the locus of fourfolds through \(T\) on which an invariant class remains Hodge is therefore

\[
n-c=\dim R_{d-w_t}^{[\chi_t^{-1}]}-\dim R_{d-w_t}^{[(\delta\chi_t)^{-1}]}.
\]

For \(\delta=1\) the two spaces coincide and the count is zero. This is necessary: the invariant part of \(H^3(T)\) then contains \(H^{3,0}(T)\), and for a general member of a family with irreducible invariant variation no nonzero part of it is supported on a divisor. A positive count requires a symmetry that moves the holomorphic three-form. The comparison in [Chapter 4, §4.6](#technical-information/known-locus) is the analogous count for a sixfold containing a sextic fourfold, where the source is too small.

## 3D.2 The derivative of the normal function

Suppose \(K\in\ker\mu_Q\). Then

\[
tKQ=\sum_{z\in\{z_0,\ldots,z_4,t\}}c_z\,\partial_z\widetilde F
\]

for homogeneous \(c_z\), and we put

\[
\beta_Q(K)=\bigl[c_t|_{t=0}\bigr]\in(R_0)_{2d}^{[\delta^{-1}]}\simeq H^{1,2}(T)^G.
\]

The partial derivatives of \(\widetilde F\) form a regular sequence, so two solutions differ by a Koszul syzygy. Their coefficients \(c_t\) differ by an element of the ideal \((\partial_z\widetilde F)_{z\ne t}\), which restricts to \(J(F_0)\) on \(t=0\). Thus \(\beta_Q(K)\) is well defined. It depends only on the class of \(Q\) in \(R\), and it vanishes on the rescaling direction \(K=\partial_t\widetilde F\), for which \(c_t=tQ\).

Let \(N^1H^3(T,\mathbb Q)\) be the part supported on divisors. It is \(G\)-stable. Put

\[
W_T=H^{1,2}(T)\cap\bigl(N^1H^3(T,\mathbb Q)^G\otimes\mathbb C\bigr).
\]

**Normal-function lemma.** Let \(\lambda\in H^4(Y,\mathbb Q)^G_{\mathrm{prim}}\) be a Hodge class whose \((2,2)\)-component is represented by \(Q\), and suppose \(\mu_Q\) is surjective. Then

\[
\beta_Q(\ker\mu_Q)\subset W_T.
\]

**Proof.** Let \(\mathcal A\) parametrize the invariant \(\widetilde F'\) restricting to \(F_0\), with smooth zero locus. The locus \(M\subset\mathcal A\) on which the flat transport of \(\lambda\) remains of type \((2,2)\) has tangent space the kernel of \(\overline\nabla\lambda:T\mathcal A\to H^{1,3}(Y)^G\), and \(\overline\nabla_K\lambda\) is a constant multiple of \([tKQ]\). By surjectivity \(M\) is smooth near \(\widetilde F\) with tangent space \(\ker\mu_Q\). Modulo the directions in the Jacobian ideal, along which \(Y\) moves by automorphisms fixing \(T\), its dimension is \(n-c\).

For \(s\in M\) the class \(\lambda\) is a rational Hodge class on the Fano fourfold \(Y_s\), hence the class of a cycle \(Z_s\) with rational coefficients. Relative Hilbert schemes have countably many components. By Baire's theorem there is a dense open subset of \(M\) near each point of which, after a finite cover, the \(Z_s\) form an algebraic family. The spaces \(\ker\mu\) and the maps \(\beta\) vary continuously along \(M\) and \(W_T\) is closed, so it suffices to treat such points.

Every \(Y_s\) contains \(T\), and \(Z_s|_T\) is homologous to zero because \(\lambda\) is primitive. The cycles \(Z_s|_T-Z_{s_0}|_T\) are algebraically equivalent to zero. Their Abel–Jacobi images \(\nu(s)\) lie in the image \(J_a(T)\) of the Abel–Jacobi map on such cycles. A family of one-cycles over a curve acts through a correspondence whose image is supported on a surface, so the tangent space of \(J_a(T)\) is the \((1,2)\)-part of a Hodge structure contained in \(N^1H^3(T,\mathbb Q)\). Hence \(d\nu(K)\) lies in \(H^{1,2}(T)\cap(N^1H^3(T,\mathbb Q)\otimes\mathbb C)\).

It remains to identify \(d\nu(K)\) with a nonzero multiple of \(\beta_Q(K)\). Since \(H^3(Y_s)=0\), the pair gives an exact sequence of mixed Hodge structures

\[
0\longrightarrow H^3(T)\longrightarrow H^4(Y_s,T)\longrightarrow H^4(Y_s)\longrightarrow H^4(T).
\]

The Abel–Jacobi image of \(Z_s|_T\) is the class of \(\widetilde\lambda_F-\widetilde\lambda_{\mathbb Q}\) in \(H^3(T,\mathbb C)/(F^2+H^3(T,\mathbb Q))\), for lifts of \(\lambda\) to \(F^2H^4(Y_s,T)\) and to \(H^4(Y_s,T;\mathbb Q)\). The threefold does not move. Hence \(H^3(T)\) and \(F^2H^3(T)\) are constant, the rational lift is flat, and

\[
d\nu(K)=\bigl[\nabla_K\widetilde\lambda_F\bigr]\in H^3(T,\mathbb C)/F^2H^3(T).
\]

Let \(\mathbb P'\) be the ambient space of \(Y\) and \(D=\{t=0\}\). Both \(\mathbb P'\) and \(D\) are locally quotients of smooth varieties by finite groups, and \(Y\) and \(T\) avoid their singular points. Rational forms, residues and pole orders are taken on these local uniformizing covers, as in the weighted residue theorems of §3D.1; there the filtrations below are compatible with restriction to \(t=0\). Residues identify \(H^4(Y,T)_{\mathrm{prim}}\) with \(H^5(\mathbb P'\setminus Y,D\setminus T)\). A class there is represented by a pair \((\varphi,\eta)\): a rational five-form on \(\mathbb P'\) with poles on \(Y\) and a rational four-form on \(D\) with poles on \(T\), modulo pairs \((d\alpha,\alpha|_D+d\gamma)\). Every such pair is a relative cocycle for reasons of degree. By the comparison of the Hodge filtration with the filtration by order of pole in [Deligne, Théorie de Hodge II, §3.1](https://numdam.org/item/PMIHES_1971__40__5_0/), applied to the cone of the restriction map, pairs with pole orders at most three and two lie in \(F^2H^4(Y,T)\), and \((0,\eta)\) is the image of the residue of \(\eta\).

Take \(\widetilde\lambda_F=[(P_s\Omega/\widetilde F_s^3,0)]\). At the base point \(P\equiv Q\) modulo the Jacobian ideal, and we may take \(Q=P\). Along \(\widetilde F+\varepsilon tK\),

\[
\frac{d}{d\varepsilon}\frac{P_s\Omega}{\widetilde F_s^3}
=\frac{\dot P\,\Omega}{\widetilde F^3}-3\frac{tKQ\,\Omega}{\widetilde F^4}.
\]

Let \(E\) be the weighted Euler field, \(v=\sum_zc_z\partial_z\), and \(\alpha=\widetilde F^{-3}\iota_E\iota_v(dz_0\wedge\cdots\wedge dz_4\wedge dt)\). Griffiths' reduction formula gives

\[
3\frac{tKQ\,\Omega}{\widetilde F^4}
=\pm d\alpha+\frac{(\sum_z\partial_zc_z)\Omega}{\widetilde F^3}.
\]

The derivative of the lift is therefore a pair with pole order at most three, plus \(\mp(d\alpha,0)\sim\pm(0,\alpha|_D)\). On \(D\) both \(t\) and \(dt\) vanish, so only the \(\partial_t\)-component of \(v\) survives:

\[
\alpha|_D=\pm\frac{c_t|_{t=0}\,\Omega_D}{F_0^3}.
\]

The derivative lies in \(H^3(T)\) because \(\lambda\) is flat. By strictness \(H^3(T)\cap F^2H^4(Y,T)=F^2H^3(T)\). Hence \(d\nu(K)\) is a nonzero multiple of the class of \(c_t|_{t=0}\) in \((R_0)_{2d}=H^{1,2}(T)\). Its character shows that it is \(G\)-invariant. ∎

The argument is the weighted form of [Voisin, §§2.12–2.15](https://www.numdam.org/item/ASNSP_1992_4_19_4_473_0.pdf). It does not use the dimension: for a hypersurface \(Y\) of dimension \(2m\) with section \(T\), a primitive Hodge class of degree \(2m\) and its restricted cycles, the same recipe gives the derivative of the normal function in \(H^{m-1,m}(T)\).

There is an equivalent formula without a choice of \(c_z\). The ring

\[
R_{\log}=S/\bigl(\partial_z\widetilde F\ (z\ne t),\ t\,\partial_t\widetilde F\bigr)
\]

is a complete intersection, and multiplication by \(\partial_t\widetilde F\) embeds \(R_0\) in it with cokernel \(R\). Its socle is the image of the socle of \(R_0\). Consequently, for \(A\in(R_0)_d^{[\delta^{-1}]}\simeq H^{2,1}(T)^G\),

\[
\operatorname{soc}_{R_0}\bigl(A\,\beta_Q(K)\bigr)=\kappa\,\operatorname{soc}_{R_{\log}}(tKQ\,A)
\]

with a nonzero constant \(\kappa\) depending only on the two socle generators.

**Example: a line on a quartic surface.** Let \(Y=\{\ell_1G_1+\ell_2G_2=0\}\subset\mathbb P^3\) be a smooth quartic surface containing the line \(L=\{\ell_1=\ell_2=0\}\), and let \(T=Y\cap\{t=0\}\) be a smooth plane quartic. The primitive class of \(L\) is represented in \(R_4\) by the Jacobian determinant

\[
Q=\det\frac{\partial(\ell_1,G_1,\ell_2,G_2)}{\partial(x,y,z,t)},
\]

by the formula for complete-intersection cycles in [Villaflor Loyola, Theorem 1](https://arxiv.org/abs/1812.03964). The target \(R_8\) of \(\mu_Q\) is the one-dimensional socle, so \(\ker\mu_Q\subset S_3\) has dimension nineteen: these are the quartics through \(T\) that still contain a line \(L_s\). The Abel–Jacobi image of \(L_s\cap T\) is a point of \(T\subset J(T)\) near \(p=L\cap T\). Its derivative spans the tangent line of the canonical curve at \(p\), which pairs with \(H^{1,0}(T)\simeq(R_0)_1\) by evaluation at \(p\). The recipe must therefore return, for every \(K\in\ker\mu_Q\), a class in \((R_0)_5\) whose socle pairing with a linear form \(A\) is a multiple of \(A(p)\). The verifier of §3D.4 confirms this on an explicit example: the nineteen functionals span one line, and that line is evaluation at \(p\).

## 3D.3 A spanning criterion

A rational Hodge class is needed only to produce cycles. The inclusion it yields extends to all classes by density.

**Density lemma.** Let \(\mathcal O_T\) be the set of pairs \((\widetilde F,Q)\) with \(\widetilde F|_{t=0}=F_0\), \(Y\) smooth, and \(\mu_Q\) surjective. Then \(\beta_Q(\ker\mu_Q)\subset W_T\) for every pair in \(\mathcal O_T\).

**Proof.** Over \(\mathcal A\) the graded pieces

\[
\operatorname{Gr}^2_FH^4(Y)^G_{\mathrm{prim}}\simeq R_{2d-w_t}^{[(\delta\chi_t)^{-1}]}
\]

form an algebraic vector bundle \(\mathcal H\), and \(\mathcal O_T\) is Zariski open in it. On \(\mathcal O_T\) the kernels of \(\mu\) form an algebraic bundle and \(\beta\) is algebraic, so the locus \(\mathcal S\) where the inclusion holds is Zariski closed in \(\mathcal O_T\).

The subspaces \(H^{2,2}(Y)\) of the flat bundle do not vary algebraically, but each projects isomorphically onto the fiber of \(\mathcal H\). Let \(\mathcal H_{\mathbb R}\subset\mathcal H\) be the image of the real classes of type \((2,2)\). It is a real form of each fiber and varies real-analytically. At a point of \(\mathcal O_T\cap\mathcal H_{\mathbb R}\) the flat transport map from the real \((2,2)\)-classes to a fixed fiber \(H^4(Y_0,\mathbb R)^G_{\mathrm{prim}}\) is a submersion: its image contains the real \((2,2)\)-classes and the real parts of \(\overline\nabla_K\lambda\), the map \(\overline\nabla\lambda\) is onto \(H^{1,3}(Y)^G\), and \(H^{4,0}(Y)=0\). This is Green's density criterion in equivariant form, as used in [Voisin, §2.17](https://www.numdam.org/item/ASNSP_1992_4_19_4_473_0.pdf). Hence rational Hodge classes are dense in \(\mathcal O_T\cap\mathcal H_{\mathbb R}\). They lie in \(\mathcal S\) by the normal-function lemma, so \(\mathcal O_T\cap\mathcal H_{\mathbb R}\subset\mathcal S\). A real form is Zariski dense in each fiber. Therefore \(\mathcal S=\mathcal O_T\). ∎

**Spanning criterion.** Suppose \(\delta\ne1\) and there are pairs \((\widetilde F_i,Q_i)\in\mathcal O_T\), \(1\le i\le m\), whose subspaces \(\beta_{Q_i}(\ker\mu_{Q_i})\) together span \((R_0)_{2d}^{[\delta^{-1}]}\). Then

\[
H^3(T,\mathbb Q)^G\subset N^1H^3(T,\mathbb Q).
\]

For fixed polynomials \(\widetilde F_i-F_0\) and \(Q_i\), the hypothesis is a Zariski-open condition on \(F_0\).

**Proof.** The density lemma gives \(W_T=H^{1,2}(T)^G\). The rational Hodge structure \(N^1H^3(T,\mathbb Q)^G\) then has the full \((1,2)\)-part of \(H^3(T)^G\), and by conjugation the full \((2,1)\)-part, while \(H^{3,0}(T)^G=0\) because \(\delta\ne1\). Smoothness, surjectivity of the \(\mu_{Q_i}\) and the rank of the span are open conditions; the last one because \(\beta\) varies algebraically where \(\mu\) has constant rank. ∎

The hypothesis is the surjectivity of one explicit linear map. Let \(\Theta\) send a tuple

\[
\bigl(K_i,(c^{(i)}_z)_z\bigr)_{1\le i\le m},\qquad (e_z)_{z\ne t},
\]

of homogeneous polynomials of the appropriate degrees and characters to

\[
\Bigl(tK_iQ_i-\sum_zc^{(i)}_z\partial_z\widetilde F_i\Bigr)_{1\le i\le m}
\quad\text{and}\quad
\sum_ic^{(i)}_t|_{t=0}-\sum_{z\ne t}e_z\,\partial_zF_0 .
\]

If \(\Theta\) is surjective, then each \(\mu_{Q_i}\) is surjective, and an arbitrary last component is attained with all first components zero, which is the spanning condition. The converse is equally direct. For polynomials with integer coefficients \(\Theta\) is an integer matrix. Its rank over \(\mathbb Q\) is at least its rank modulo any prime. Full row rank modulo one prime therefore proves the hypothesis in characteristic zero, without comparing kernels in the two characteristics. Elimination block by block computes this rank as

\[
\operatorname{rank}\Theta=\sum_i\operatorname{rank}\bigl[J(\widetilde F_i)\mid tQ_iS_{d-w_t}\bigr]
+\dim\Bigl(J(F_0)+\sum_i\{c_t|_{t=0}\}\Bigr),
\]

in the relevant graded pieces.

The same remark covers part of the span. Let \(\pi\) be a linear map on \((S_0)_{2d}^{[\delta^{-1}]}\) vanishing on \(J(F_0)\), and let \(\Theta_\pi\) be \(\Theta\) with its last component composed with \(\pi\). It is surjective exactly when each \(\mu_{Q_i}\) is surjective and the subspaces \(\pi\beta_{Q_i}(\ker\mu_{Q_i})\) span the image of \(\pi\). For integral data, full row rank modulo one prime again proves this in characteristic zero. For a single pair and a linear form \(\pi\), it is enough to find, modulo the prime, that \(\mu_Q\) is surjective and that one solution of \(tKQ=\sum_zc_z\partial_z\widetilde F\) has \(\pi(c_t|_{t=0})\ne0\).

## 3D.4 Order-three weighted sextics

Let \(\omega\) be a primitive cube root of unity and let

\[
g=(\omega^2,\omega^2,\omega,1;1)
\]

act on \(\mathbb P(1,1,1,1,2)\) with coordinates \((x_0,x_1,x_2,x_3;w)\).

**Order-three weighted threefold theorem.** Let \(T\subset\mathbb P(1,1,1,1,2)\) be a quasismooth sextic with \(g\)-invariant equation. Then

\[
H^3(T,\mathbb Q)^g\subset N^1H^3(T,\mathbb Q).
\]

More precisely, the projector of \(H^*(T,\mathbb Q)\) onto \(H^3(T,\mathbb Q)^g\), zero in the other degrees and on the other eigenspaces, is cohomologous to a rational algebraic cycle supported on \(D\times D\) for some divisor \(D\subset T\).

As in [Chapter 3B, §3B.1](#technical-information/weighted-threefolds), \(T\) avoids the weighted vertex and is a smooth Calabi–Yau threefold with \(h^{2,1}=103\). Here \(\delta=\omega^5=\omega^2\). The Jacobian ring gives the Hodge numbers of the three eigenspaces:

| Eigenvalue of \(g\) | \((h^{3,0},h^{2,1},h^{1,2},h^{0,3})\) |
| --- | --- |
| \(1\) | \((0,33,33,0)\) |
| \(\omega\) | \((0,35,35,1)\) |
| \(\omega^2\) | \((1,35,35,0)\) |

The theorem concerns the first row. Its Hodge type predicts divisor support; the proof supplies it.

**The extension.** Give \(t\) weight three and trivial character. Up to rescaling \(t\), the invariant sextics restricting to \(F_0\) with a nonzero coefficient of \(t^2\) are

\[
\widetilde F=F_0+t\,a+t^2,\qquad a\in\mathbb C[x,w]_3^{g},
\]

a nine-dimensional family. Neither singular point of \(\mathbb P(1,1,1,1,2,3)\) lies on \(Y\). A quasismooth \(Y\) is thus a smooth del Pezzo fourfold of degree one, the double cover of \(\mathbb P(1,1,1,1,2)\) branched along \(\{a^2=4F_0\}\). In the notation of §3D.1, \(d=6\), \(w_t=3\), and

\[
\bigl(h^{3,1},h^{2,2}_{\mathrm{prim}},h^{1,3}\bigr)(Y)^g=(7,52,7),
\qquad
n-c=\dim R_3^{[1]}-\dim R_3^{[\omega]}=9-7=2.
\]

When \(\mu_Q\) is surjective, the invariant class has a two-dimensional locus of fourfolds through \(T\), and \(\beta_Q\) maps its tangent space to a subspace of the 33-dimensional space \((R_0)_{12}^{[\omega]}\) of dimension at most two.

**A witness.** Take the Fermat member

\[
F_0=x_0^6+x_1^6+x_2^6+x_3^6+w^3
\]

and the single pair

\[
a=5\bigl(x_0^3+x_1^3+x_2^3+x_3^3+x_0x_2x_3+x_1x_2x_3+x_3w\bigr),
\qquad Q=x_2w^4.
\]

Modulo five \(\widetilde F=F_0+ta+t^2\) is \(F_0+t^2\), whose partial derivatives are monomials. The fourfold is therefore quasismooth. Because \(F_0\) is Fermat, \(J(F_0)\) is spanned by monomials, and \((R_0)_{12}^{[\omega]}\) has as a basis the 33 standard monomials

\[
x_0^{e_0}x_1^{e_1}x_2^{e_2}x_3^{e_3}w^{e_w},\qquad e_i\le4,\quad e_w\le1,
\]

of degree twelve and character \(\omega\).

The verifier `scripts/verify-hodge-locus-span.py`, in the repository's [reproduction scripts](https://github.com/hodge-computer/sextics/tree/main/scripts), reconstructs the map \(\mu_Q\), its kernel, solutions \(c_z\) and the classes \(\beta_Q(K)\). It reads no witness data and uses exact arithmetic modulo \(2^{31}-1\). Run it with Python and NumPy:

```sh
python3 scripts/verify-hodge-locus-span.py
```

The finite results are:

| Calculation modulo \(2^{31}-1\) | Result |
| --- | --- |
| \(\dim S_{15}^{[\omega]}\), and rank of \(J(\widetilde F)\) in it | \(1247\), \(1240\) |
| Rank of \(\mu_Q\) on the ten invariant cubics | \(7\) |
| Dimension of \(\ker\mu_Q\) and of its image under \(\beta\) | \(3\) and \(2\) |
| Standard monomials with a nonzero coefficient in some \(\beta_Q(K)\) | all \(33\) |

The kernel contains the rescaling direction, on which \(\beta\) vanishes, so the image has dimension \(n-c=2\). By the last remark of §3D.3, applied to the 33 coordinate forms, the last line holds in characteristic zero: for every standard monomial \(m\), the space \(\beta_Q(\ker\mu_Q)\) contains a class with a nonzero coefficient on \(m\).

**From two dimensions to thirty-three.** The group \(\mu_6^4\times\mu_3\) acts diagonally on \((x_0,x_1,x_2,x_3;w)\). It preserves \(F_0\) and commutes with \(g\), so it preserves \(W_T\). Each standard monomial spans an eigenline of \((R_0)_{12}^{[\omega]}\). The 33 characters are pairwise distinct, because the exponents of a standard monomial are determined by their residues modulo six and three. A stable subspace is therefore spanned by the standard monomials it contains, and it contains every standard monomial on which one of its vectors has a nonzero coefficient. The density lemma gives \(\beta_Q(\ker\mu_Q)\subset W_T\). Hence \(W_T=(R_0)_{12}^{[\omega]}\) at the Fermat member.

This is not yet a witness for the spanning criterion, and support at the Fermat member alone says nothing about its neighbors. Extend each element \(h\) of the diagonal group to the ambient space of \(Y\) by fixing \(t\). Since \(h^*F_0=F_0\), the pairs \((h^*\widetilde F,h^*Q)\) lie in \(\mathcal O_T\), and

\[
\beta_{h^*Q}(\ker\mu_{h^*Q})=h^*\beta_Q(\ker\mu_Q).
\]

By the preceding paragraph these subspaces together span \((R_0)_{12}^{[\omega]}\). The finite orbit of the pair is thus a witness for the spanning criterion, whose hypothesis is open in \(F_0\). Only one pair needs a calculation.

**Proof of the theorem.** The witness and the spanning criterion give a nonempty Zariski-open set \(\mathcal U\) of invariant sextics with \(H^3(T,\mathbb Q)^g\subset N^1H^3(T,\mathbb Q)\). For \(T\in\mathcal U\) there are a smooth projective curve \(\Lambda\), possibly disconnected, and a correspondence \(\Gamma\) with \(\Gamma_*H^1(\Lambda,\mathbb Q)\supset H^3(T,\mathbb Q)^g\). Let \(D\) be a \(g\)-stable divisor containing its image. Let \(\pi_g=(1+g+g^2)/3\), and let \(\pi_1^\Lambda\) be the projector onto \(H^1(\Lambda)\): on a component with a chosen point \(p\) it is \(\Delta_\Lambda-[p]\times\Lambda-\Lambda\times[p]\). Replace \(\Gamma\) by

\[
\pi_g\circ\Gamma\circ\pi_1^\Lambda .
\]

Its image is still contained in \(D\). The second projector is needed here: unlike the anti-projector of [§3B.6](#technical-information/weighted-threefolds), \(\pi_g\) fixes the even cohomology of \(T\), on which a curve correspondence acts through \(H^0(\Lambda)\) and \(H^2(\Lambda)\). Now \(\Gamma_*\) vanishes outside \(H^1(\Lambda)\) and maps it onto \(H^3(T)^g\). As in §3B.6, the transpose is the adjoint for the polarizations up to a sign, so \(\Gamma\circ{}^t\Gamma\) is invertible on \(H^3(T)^g\). It is zero on the rest of the cohomology, and a polynomial in it without constant term represents the projector by a cycle supported on \(D\times D\).

Weighted weak Lefschetz gives \(H^{2k}(T)=\mathbb Qh^k\) and \(h^3=3\). The projector is thus the class of the relative algebraic cycle

\[
\pi_g-\sum_{k=0}^3\pi_{2k},\qquad
\pi_{2k}=\tfrac13\,\mathrm{pr}_1^*h^{3-k}\cdot\mathrm{pr}_2^*h^k,
\]

over the connected family of all smooth invariant sextics. The supported-projector specialization lemma of [Chapter 3, §3.6](#technical-information/geometric-support) extends the supported representative from \(\mathcal U\) to every member. ∎

Without the group the method gives nothing, as it must: for the trivial group \(n=c\). For the involution \((+,+,-,-;+)\) of Chapter 3B and classes on \(Y\) anti-invariant under it, the same weight-three extension has \(n=c=12\), so that sector is not reached by this extension; its support comes from the norm-contact curves.

## 3D.5 Sextic fourfolds with a paired sign and an order-three symmetry

The passage to a fourfold uses the relative support lemma for an invariant sector in [Chapter 3, §3.6](#technical-information/geometric-support).

**Theorem.** Let \(X=(F=0)\subset\mathbb P^5\) be a smooth sextic with coordinates \((x_0,x_1,x_2,x_3,u,v)\). Suppose \(F\) is invariant under

\[
\beta:(u,v)\mapsto(-u,-v),
\qquad
\gamma=\operatorname{diag}(\omega^2,\omega^2,\omega,1,1,1).
\]

Then

\[
H^4(X,\mathbb Q)^{\langle\beta,\gamma\rangle}\subset N^1H^4(X,\mathbb Q).
\]

The determinant of \(\gamma\) is \(\omega^2\), so \(H^{4,0}(X)\) is not invariant and the statement is consistent with coniveau. The invariant sextics form an 85-coefficient linear system.

**Proof.** Follow the proof of the two-reflection theorem in [§3B.7](#technical-information/weighted-threefolds) with the pencil \(\lambda=v/u\). The base surface \(X\cap\{u=v=0\}\) is smooth: there \(\partial_uF\) and \(\partial_vF\) vanish because they are odd in \((u,v)\), so a singular point of the surface would be singular on \(X\). The restriction \(F(0,u,v)\) is not identically zero. Otherwise \(X\) would contain the line \(x=0\), along which the four core derivatives vanish, being coefficients of monomials of odd degree in \((u,v)\). Blow up the base surface. For \(\lambda\) in a nonempty open \(U\subset\mathbb P^1\), the fiber \(V_\lambda=X\cap\{v=\lambda u\}\) is smooth, \(\beta\) acts on it as the reflection \(u\mapsto-u\), and with \(w=u^2\) the quotient

\[
T_\lambda=V_\lambda/\beta\subset\mathbb P(1,1,1,1,2)
\]

is a quasismooth sextic avoiding the vertex. Its equation is invariant under \(g\), the action of \(\gamma\).

By the order-three weighted threefold theorem, the projector onto \(H^3(T_\lambda)^g\) has a supported representative at every fiber. The relative support lemma for an invariant sector supplies a divisor of the total space \(\mathcal T\to U\) supporting \(H^1(U,(R^3p_*\mathbb Q)^g)\).

Let \(\alpha\) be an invariant class. Its pullback to the blowup, restricted over \(U\), is \(\beta\)-invariant, hence the pullback of a \(g\)-invariant class \(\alpha'\) on \(\mathcal T\). Leray gives \(\alpha'=c\,h^2+\alpha''\) with \(\alpha''\in H^1(U,(R^3p_*\mathbb Q)^g)\). Both terms vanish off a divisor. Adding the omitted fibers and the exceptional divisor and pushing forward supports \(\alpha\) on \(X\). ∎

In the coordinates of this book, take \((u,v)=(X_2,Y_2)\) and \((x_0,x_1,x_2,x_3)=(X_0,X_1,Y_0,Y_1)\). Then \(\beta\) is the paired sign \(s_2\) and

\[
\gamma=\operatorname{diag}(\omega^2,\omega^2,1,\omega,1,1)
\quad\text{on}\quad(X_0,X_1,X_2,Y_0,Y_1,Y_2).
\]

Of the 85 invariant monomials, 45 are \(Y\)-even. A \(Y\)-odd numerator \(A\) is served when its residue is invariant, that is, when \(A\) is even in \((X_2,Y_2)\) and \(\gamma^*A=\omega A\). The support-to-certificate equivalence of [Chapter 1](#technical-information/certificates) then gives a certificate for pole orders \(1\le q\le4\). The reduction of [Chapter 3, §3.5](#technical-information/geometric-support) extends this to larger pole orders once its auxiliary field is averaged over \(\langle\beta,\gamma\rangle\), which keeps the reduced target in the invariant sector.

**Example: three cyclic links.** Let \(\rho\) permute the three pairs \((X_i,Y_i)\) cyclically. The conjugates \(\gamma_i=\rho^i\gamma\rho^{-i}\) and the paired signs \(s_i\) generate, with \(\tau\), a diagonal group of projective order 72. It contains the element \(h\) of [Chapter 4, §4.2](#technical-information/known-locus). Its invariant sextics are

\[
F=\sum_i\bigl(a_iX_i^6+b_iY_i^6\bigr)
+\sum_ic_i\,X_i^3X_{i+1}Y_iY_{i+1}
+\sum_ie_i\,X_i^2Y_{i-1}^2Y_i^2,
\]

with indices modulo three. For a smooth member, the \(Y\)-even primitive cohomology, of type \((208,866,208)\), splits into three parts according to the characters of this group:

| Characters | Hodge numbers | Support |
| --- | --- | --- |
| Nontrivial on the paired signs | \((150,636,150)\) | [Paired signs, §3B.9](#technical-information/weighted-threefolds) |
| Trivial on the paired signs and on \(h^2\) | \((22,74,22)\) | [Paired-sign sector theorem, §4.2](#technical-information/known-locus), when its surface is smooth |
| Trivial on some \(s_i\) and on \(\gamma_{i+1}\) | \((36,156,36)\) | The theorem above, applied to the three pairs \((s_i,\gamma_{i+1})\) |

Here \(\gamma_{i+1}\) is the conjugate acting trivially on \((X_i,Y_i)\). The three rows exhaust the characters. The last row consists of six characters of type \((6,26,6)\): two for each cyclic conjugate. Thus, when the surface of §4.2 is smooth, all of \(H^4(X,\mathbb Q)^\tau\) is supported on a divisor, although none of the three mechanisms reaches it alone. The member \(a_i=b_i=1\), \(c_i=\tfrac12\), \(e_i=0\) is smooth. Indeed, at a nonzero point where the gradient vanishes, let \(M>0\) be the largest modulus of a coordinate. If \(X_i\) attains it, then

\[
6X_i^5=-\tfrac12\bigl(3X_i^2X_{i+1}Y_iY_{i+1}+X_{i-1}^3Y_{i-1}Y_i\bigr)
\]

has modulus \(6M^5\) on the left and at most \(2M^5\) on the right. If \(Y_i\) attains it, then

\[
6Y_i^5=-\tfrac12\bigl(X_i^3X_{i+1}Y_{i+1}+X_{i-1}^3X_iY_{i-1}\bigr)
\]

has modulus \(6M^5\) on the left and at most \(M^5\) on the right. Both are impossible.

This member illustrates the last row: at pole order two, the numerator \(A=X_0^2X_1^2X_2^3Y_0^2Y_1^2Y_2\) has its residue there, invariant under \(s_2\) and \(\gamma\).
