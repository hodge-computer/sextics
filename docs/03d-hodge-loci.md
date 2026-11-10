# 3D. Hodge loci of surface sections

[Previous: quadratic nets and pair correspondences](#technical-information/quadratic-nets) · [Contents](#technical-information/introduction) · [Next: families, representations and deformation](#technical-information/known-locus)

A divisor class on a surface section of a Calabi–Yau threefold stays algebraic along a locus of sections. When a symmetry moves the holomorphic three-form, the invariant part of this locus has positive expected dimension. Curves in the class then move on the threefold, and the derivative of their Abel–Jacobi images is a trace on an Artinian algebra. If the invariant variation of Hodge structure has no proper sub-variation, one nonzero derivative supports the whole invariant sector of the third cohomology on a divisor.

Moving cycles along Hodge loci is the strategy of [Voisin, Proposition 2.1](https://www.numdam.org/item/ASNSP_1992_4_19_4_473_0.pdf), and the loci of surface sections of a Calabi–Yau threefold are studied in [Voisin, §2](https://www.cmls.polytechnique.fr/perso/voisin/Articlesweb/griffithsgroup.pdf). Chapter 3B follows the same strategy with explicitly constructed curves. This chapter applies it to weighted sextic threefolds with an order-three symmetry that moves the holomorphic three-form, and then to sextic fourfolds with a paired sign and such a symmetry.

## 3D.1 Invariant sections and the dimension count

Let \(S=\mathbb C[z_0,\ldots,z_4]\) have weights \((w_0,\ldots,w_4)\) and put \(d=w_0+\cdots+w_4\). Let a finite abelian group \(G\) act diagonally, and let \(\delta\) be the product of the characters of the variables. For a character \(\chi\), the superscript \([\chi]\) denotes the \(\chi\)-isotypic part, and the superscript \(G\) the invariants.

Let \(F\in S_d^G\) define a quasismooth threefold \(T\subset\mathbb P(w_0,\ldots,w_4)\) that avoids the singular locus. It is a smooth Calabi–Yau threefold. With \(R(F)=S/J(F)\), the weighted residue theorems of [Dolgachev, §4.2–4.3](https://sites.lsa.umich.edu/idolga/wp-content/uploads/sites/1334/2024/08/weighted82.pdf) give

\[
H^{3-j,j}(T)\simeq R(F)_{jd},
\]

and the residue of \(B\,\Omega/F^{j+1}\) has character \(\chi(B)\delta\). Thus \(G\) acts on \(H^{3,0}(T)\) through \(\delta\), and \(H^{2,1}(T)^G\simeq R(F)_d^{[\delta^{-1}]}\).

Let \(h\in S_e^G\), with \(0<e<d\), cut a smooth surface \(D=T\cap\{h=0\}\). Then \(K_D=N_{D/T}=\mathcal O_D(e)\) and \(H^1(D,\mathcal O_D)=0\). The invariant first-order motions of \(D\) in \(T\) and the invariant holomorphic two-forms are

\[
H^0(N_{D/T})^G=S_e^G/\mathbb Ch,
\qquad
H^{2,0}(D)^G\simeq(S_e/\mathbb Ch)^{[\delta^{-1}]},
\]

the second through the residues of \(\sigma\,\Omega/(Fh)\).

Let \(\lambda\) be a \(G\)-invariant divisor class on \(D\). Its flat transport to \(T\cap\{h+\varepsilon L=0\}\) stays of type \((1,1)\) to first order exactly when \(L\) lies in the kernel of

\[
\operatorname{NL}_\lambda:S_e^G\longrightarrow\bigl(H^{2,0}(D)^G\bigr)^\vee,
\qquad
\operatorname{NL}_\lambda(L)(\sigma)=\langle\overline\nabla_L\lambda,\sigma\rangle .
\]

Modulo rescaling of \(h\), the expected dimension of the locus of invariant sections on which \(\lambda\) stays algebraic is therefore

\[
n-c=\dim S_e^G-1-\dim(S_e/\mathbb Ch)^{[\delta^{-1}]} .
\]

For \(\delta=1\) the two spaces coincide and the count is zero. This is necessary: the invariant part of \(H^3(T)\) then contains \(H^{3,0}(T)\), and for a general member of a family with irreducible invariant variation no nonzero part of it is supported on a divisor. For \(\delta\ne1\) the count is \(\dim S_e^G-1-\dim S_e^{[\delta^{-1}]}\). A positive count requires a symmetry that moves the holomorphic three-form.

**Integration lemma.** Suppose \(\operatorname{NL}_\lambda\) is surjective. Near \((F,h)\), the pairs \((F',h')\) of invariant polynomials for which \(\lambda\) remains of type \((1,1)\) form a smooth family. It is submersive over the invariant \(F'\), with fibers of dimension \(n-c\) modulo rescaling. On it \(\lambda\) is the class of a unique line bundle \(\mathcal L'\), which is \(G\)-invariant, and for large \(m\) the curves of \(|\mathcal L'(m)|\) form a projective bundle over it.

**Proof.** The locus is the zero set of a holomorphic section of the bundle with fibers \(H^{0,2}(D')^G\): the \((0,2)\)-part of the flat transport of \(\lambda\). Its derivative is \(\overline\nabla\lambda\), as in [Voisin, §2, Lemma 2](https://www.cmls.polytechnique.fr/perso/voisin/Articlesweb/griffithsgroup.pdf). By hypothesis this derivative is already surjective on the directions in which only \(h\) moves. That gives smoothness and both dimension statements. A class of type \((1,1)\) is the class of a line bundle. It is unique because \(H^1(\mathcal O_{D'})=0\), hence invariant. Serre vanishing and base change give the projective bundle. ∎

## 3D.2 Two trace formulas

Suppose

\[
F=f_1g_1+f_2g_2+hk
\]

with homogeneous \(f_i\), \(g_i\) and \(k\), not assumed to be eigenvectors of \(G\), and suppose that \(C=V(f_1,f_2,h)\) is a smooth curve. It lies on \(D\). Along \(C\) we have \(dF=g_1\,df_1+g_2\,df_2+k\,dh\), and \(D\) is smooth, so \(g_1\) and \(g_2\) have no common zero on \(C\). Hence

\[
\mathcal A=S/(f_1,f_2,g_1,g_2,h)
\]

is an Artinian complete intersection, with one-dimensional socle in degree \(d+e\). Let \(\tau:\mathcal A_{d+e}\to\mathbb C\) be a nonzero linear form.

**Obstruction lemma.** Let \(A\in S_d\) and \(L,\sigma\in S_e\). On \(V(F+\varepsilon A,\ h+\varepsilon L)\), the first-order obstruction to the class of \(C\) remaining of type \((1,1)\), paired with the two-form of numerator \(\sigma\), is a fixed nonzero multiple of

\[
\tau\bigl((A-kL)\,\sigma\bigr).
\]

In particular \(\operatorname{NL}_{[C]}(L)(\sigma)\) is a nonzero multiple of \(\tau(kL\sigma)\).

**Proof.** Let \(\rho\in H^1(T_D)\) be the Kodaira–Spencer class of the deformation and \(\omega\) the two-form. The intersection form is flat and \(F^2\) is orthogonal to \(F^1\), so

\[
\langle\overline\nabla[C],\omega\rangle=-\langle\overline\nabla\omega,[C]\rangle=-\int_C(\rho\mathbin{\lrcorner}\omega)|_C .
\]

The integrand depends only on the image of \(\rho|_C\) in \(H^1(N_{C/D})\). That image is the class of the differences of local first-order deformations of \(C\) inside the moving surface. The normal bundle of \(C\) in the ambient space is \(\mathcal O_C(\deg f_1)\oplus\mathcal O_C(\deg f_2)\oplus\mathcal O_C(e)\), and a normal field \((u_1,u_2,u_3)\) follows the deformation when

\[
u_3=-L,\qquad g_1u_1+g_2u_2+ku_3=-A .
\]

Take \(u_2=0\) where \(g_1\ne0\), and \(u_1=0\) where \(g_2\ne0\). The two solutions differ by \((kL-A)/(g_1g_2)\) times the generator \((g_2,-g_1)\) of \(N_{C/D}\simeq\mathcal O_C(\deg f_1+\deg f_2-d)\). Multiplication by \(\sigma\) gives the Čech class of

\[
\frac{(kL-A)\,\sigma}{g_1g_2}\quad\text{in}\quad H^1(C,K_C),\qquad K_C=\mathcal O_C(\deg f_1+\deg f_2+e-d).
\]

The trace of such a class is a nonzero multiple of \(\tau\) of its numerator. Indeed \(g_1,g_2\) is a regular sequence on the coordinate ring of \(C\), so the class determines its numerator in \(\mathcal A\), and both spaces are one-dimensional. ∎

**Derivative lemma.** Let \(\lambda\) be a divisor class on \(D\), and let \(h_s\) be a family of sections of the fixed \(T\) along which \(\lambda\) stays algebraic, with tangent \(L\) at \(h\). Let \(\nu(s)\) be the Abel–Jacobi image of a curve of class \(\lambda+mH\) on \(D_s\), for \(m\) large; it does not depend on the curve. For \(A\in S_d\), with class \(\eta_A\in H^{2,1}(T)\), the number

\[
\langle d\nu(L),\eta_A\rangle
\]

is a fixed nonzero multiple of the obstruction of \(\lambda\) on \(V(F+\varepsilon A,\ h)\), paired with the two-form of numerator \(L\). For \(\lambda=[C]\) it is a nonzero multiple of \(\tau(AL)\).

**Proof.** Let \(\Gamma\) be a smooth curve of the class moving with \(D_s\), with normal field \(v\in H^0(N_{\Gamma/T})\) over \(L|_\Gamma\). By Griffiths's formula for the differential of the Abel–Jacobi map (compare [Voisin, §2, Lemma 7](https://www.cmls.polytechnique.fr/perso/voisin/Articlesweb/griffithsgroup.pdf), which computes the derivative of this normal function),

\[
\langle d\nu(L),\eta\rangle=\int_\Gamma(v\mathbin{\lrcorner}\eta)|_\Gamma .
\]

Since \(H^1(K_D)=0\), the restriction of \(\eta\) to \(D\) lifts to a class \(\widetilde\eta\) in \(H^1(N_{D/T}^*\otimes\Omega^1_D)\), through

\[
0\longrightarrow N_{D/T}^*\otimes\Omega_D^1\longrightarrow\Omega_T^2|_D\longrightarrow K_D\longrightarrow0 .
\]

For a local section \(dh\wedge\beta\) of the subbundle, \((v\mathbin{\lrcorner}(dh\wedge\beta))|_\Gamma=L\,\beta|_\Gamma\), because \(dh\) vanishes on the tangent directions of \(\Gamma\). Hence

\[
\langle d\nu(L),\eta\rangle=\int_D L\,\widetilde\eta\cup[\Gamma],
\]

and the part \(mH\) of \([\Gamma]\) contributes nothing, because complete-intersection curves of \(T\) move in a rational family. Contraction with the holomorphic three-form identifies the sequence above with \(0\to T_D\to T_T|_D\to N_{D/T}\to0\), and \(\eta_A\) with the Kodaira–Spencer class of \(F+\varepsilon A\). A lift of its restriction to \(H^1(T_D)\) is the Kodaira–Spencer class \(\rho\) of \(V(F+\varepsilon A,h)\), and \(L\,\widetilde\eta\) becomes a constant multiple of \(\rho\mathbin{\lrcorner}\omega_L\), where \(\omega_L\) is the two-form of numerator \(L\). The pairing is thus \(\int_D(\rho\mathbin{\lrcorner}\omega_L)\cup\lambda\), which the obstruction lemma computes. ∎

**Orbit sums.** Suppose the translates \(\gamma C\), \(\gamma\in G\), are pairwise disjoint, and put \(E=\sum_\gamma\gamma C\). For invariant \(L\), and for \(\sigma\) and \(A\) of character \(\delta^{-1}\), every translate contributes equally to the two pairings. The formulas \(\tau(kL\sigma)\) and \(\tau(AL)\) therefore hold for \(E\), up to the factor \(|G|\).

## 3D.3 One moving class and the Higgs field

**Higgs lemma.** Let \(\mathbb V\) be a polarized rational variation of Hodge structure of weight three with \(V^{3,0}=0\) over a smooth connected base \(B\). For a tangent vector \(v\) at \(b\), the map \(\overline\nabla_v:V^{2,1}_b\to V^{1,2}_b\simeq(V^{2,1}_b)^\vee\) is a symmetric bilinear form \(H_v\) on \(V^{2,1}_b\). Suppose that at one point the only endomorphisms \(P\) of \(V^{2,1}_b\) with

\[
P^{\mathsf T}H_v=H_vP\quad\text{for all }v
\]

are the scalars. Then on every finite étale cover of a dense open subset of \(B\), the pullback of \(\mathbb V\) has no rational sub-variation other than zero and itself.

**Proof.** The condition fails only on a proper closed analytic subset, so it holds at some point of the given open subset. A rational sub-variation has an orthogonal complement for the polarization, and the projector onto it is flat, self-adjoint and of type \((0,0)\). Flatness makes it commute with every \(\overline\nabla_v\). Self-adjointness makes its action on \(V^{1,2}\) the transpose of its action \(P\) on \(V^{2,1}\). Hence \(P^{\mathsf T}H_v=H_vP\), so \(P\) is a scalar idempotent: zero or the identity. By conjugation the same holds on \(V^{1,2}\). ∎

**Moving-class criterion.** Let \(\mathcal B\) be an irreducible family of invariant polynomials \(F\) as in §3D.1, with \(\delta\ne1\), all defining smooth threefolds. Suppose that

1. at one member there are an invariant section \(h\) and an invariant divisor class \(\lambda\) on \(D\) with \(\operatorname{NL}_\lambda\) surjective, together with \(L\in\ker\operatorname{NL}_\lambda\) and \(A\in S_d^{[\delta^{-1}]}\) for which the pairing of the derivative lemma is nonzero;
2. at one member the hypothesis of the Higgs lemma holds for \(\mathbb V=(R^3p_*\mathbb Q)^G\) over \(\mathcal B\).

Then for \(T\) in a nonempty Zariski-open subset of \(\mathcal B\) there are a smooth projective curve \(\Lambda\) and a correspondence \(\Gamma\) with

\[
\Gamma_*H^1(\Lambda,\mathbb Q)\supset H^3(T,\mathbb Q)^G .
\]

In particular \(H^3(T,\mathbb Q)^G\subset N^1H^3(T,\mathbb Q)\).

In Jacobian rings the forms of the second hypothesis are \(H_A(B,B')=\operatorname{soc}(ABB')\) on \(R(F)_d^{[\delta^{-1}]}\), for the \(A\in R(F)_d^G\) tangent to \(\mathcal B\).

**Proof.** By the integration lemma, the pairs carrying the class form a smooth family that is submersive over \(\mathcal B\) near the first member, with a projective bundle of curves of class \(\lambda+mH\). Its image contains a nonempty Zariski-open subset. The pairing is nonzero, so \(L\) is not a multiple of \(h\) and the fibers have positive dimension. Choose in the fibers a curve of sections tangent to \(L\), and a section of the projective bundle over it. Spread this out over a finite étale cover of an open subset of \(\mathcal B\), and complete and normalize the parameter curves. The result is a family of smooth projective curves \(\Lambda\) with a relative correspondence \(\Gamma\) to the threefolds. By the derivative lemma its Abel–Jacobi map is not constant near the first member, and its derivative pairs nontrivially with \(H^{2,1}(T)^G\). The image of \(\pi_G\circ\Gamma_*\), with \(\pi_G\) the averaging projector, is therefore a nonzero rational sub-variation of the pullback of \(\mathbb V\). Since \(\delta\ne1\), \(\mathbb V\) has no \((3,0)\)-part, and by the Higgs lemma the sub-variation is everything. ∎

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

More precisely, the projector of \(H^*(T,\mathbb Q)\) onto \(H^3(T,\mathbb Q)^g\), zero in the other degrees and on the other eigenspaces, is cohomologous to a rational algebraic cycle supported on \(Z\times Z\) for some divisor \(Z\subset T\).

As in [Chapter 3B, §3B.1](#technical-information/weighted-threefolds), \(T\) avoids the weighted vertex and is a smooth Calabi–Yau threefold with \(h^{2,1}=103\). Here \(\delta=\omega^5=\omega^2\). The Jacobian ring gives the Hodge numbers of the three eigenspaces:

| Eigenvalue of \(g\) | \((h^{3,0},h^{2,1},h^{1,2},h^{0,3})\) |
| --- | --- |
| \(1\) | \((0,33,33,0)\) |
| \(\omega\) | \((0,35,35,1)\) |
| \(\omega^2\) | \((1,35,35,0)\) |

The theorem concerns the first row. Its Hodge type predicts divisor support; the proof supplies it.

**The count.** Take cubic sections, \(e=3\). There are nine invariant cubic monomials and seven of character \(\omega=\delta^{-1}\), so

\[
n-c=9-1-7=1 .
\]

A surjective \(\operatorname{NL}_\lambda\) leaves a one-parameter family of sections of each threefold.

**A seed.** Let \(F_0=x_0^6+x_1^6+x_2^6+x_3^6+w^3\) be the Fermat member, let \(b\) be an invariant cubic, and put \(F_b=F_0+b^2\). Choose \(r^3=2\) and \(i^2=-1\), and set

\[
\begin{aligned}
f_1&=x_0^2-r\,x_1x_3,&g_1&=x_0^4+r\,x_0^2x_1x_3+r^2x_1^2x_3^2,\\
f_2&=w+x_2^2,&g_2&=w^2-w\,x_2^2+x_2^4,\\
h&=b-i(x_1^3+x_3^3),&k&=b+i(x_1^3+x_3^3).
\end{aligned}
\]

Then \(F_b=f_1g_1+f_2g_2+hk\). On the del Pezzo fourfold \(F_0+t^2=0\) in \(\mathbb P(1,1,1,1,2,3)\), the equations \(f_1=f_2=t-i(x_1^3+x_3^3)=0\) define a surface of Aoki–Shioda type, as in [Braun–Fortin–Lopez Garcia–Villaflor Loyola, §2.2](https://arxiv.org/abs/2401.00470), and \(T_b\) is its section \(t=b\). Put

\[
D=V(F_b,h),\qquad C=V(f_1,f_2,h),\qquad E=C+gC+g^2C .
\]

The polynomials \(f_1\) and \(f_2\) are not eigenvectors of \(g\), while \(h\) is invariant. Thus \(D\) and the divisor \(E\) are invariant, and \(C\) is not.

For general \(b\) the threefold \(T_b\), the surface \(D\) and the curve \(C\) are smooth, and the three translates of \(C\) are disjoint. Indeed \(T_0\) is the Fermat member. The surface \(D\) is the section \(h=0\) of \(\{x_0^6+x_2^6+w^3=2x_1^3x_3^3\}\), whose only singular points are the two points where \(x_1\) or \(x_3\) is the only nonzero coordinate. The invariant cubics have no common zero on that threefold, so a general \(h\) avoids the two points and cuts a smooth surface. After elimination of \(w\), the curve \(C\) is the intersection of a quadric cone and a cubic in \(\mathbb P^3\), and it is smooth for the same reason. Two translates can meet only at the same two points.

**Finite results.** The verifier `scripts/verify-hodge-locus-span.py`, in the repository's [reproduction scripts](https://github.com/hodge-computer/sextics/tree/main/scripts), reconstructs the algebra \(\mathcal A\), its trace and the pairings of §3D.2 modulo \(109\), with \(r=57\), \(i=33\) and

\[
b=5x_0^3+10x_0^2x_1+25x_0x_1^2+20x_0x_2x_3+30x_1^3+25x_1x_2x_3-25x_2^3-20x_3^3+10x_3w ,
\]

and the Higgs forms at the Fermat member. It reads no witness data. Run it with Python and NumPy:

```sh
python3 scripts/verify-hodge-locus-span.py
```

| Calculation | Result |
| --- | --- |
| Length and socle degree of \(\mathcal A\) | \(96\) and \(9\) |
| Rank of \(\tau(kL\sigma)\), for the nine \(L\in S_3^g\) and the seven \(\sigma\in S_3^{[\omega]}\) | \(7\) |
| Rank after adjoining the row \(L\mapsto\tau(x_2x_3^3w\,L)\) | \(8\) |
| Matrices \(P\) with \(P^{\mathsf T}H_m=H_mP\) for the \(35\) invariant monomials \(m\) at \(F_0\) | the scalars |

The first three lines are computed at a prime of \(\mathbb Q(r,i)\) above \(109\). Length \(96\) there is the length in characteristic zero, so \(\mathcal A\) and \(\tau\) reduce well, and a rank modulo the prime is a lower bound for the rank in characteristic zero. Rank eight says that \(\operatorname{NL}_E\) is surjective and that \(\tau(x_2x_3^3w\,L)\ne0\) for some \(L\) in its kernel. Both are open conditions on \(b\), so they hold together with the smoothness conditions for general \(b\).

For the last line, the Jacobian ring of \(F_0\) is \(\mathbb C[x,w]/(x_0^5,\ldots,x_3^5,w^2)\) with its monomial basis: 33 monomials of degree six and character \(\omega\), and 35 invariant ones. For an invariant monomial \(m\), the form \(H_m(a,b)\) is one if \(abm=x_0^4x_1^4x_2^4x_3^4w\) and zero otherwise. Each entry of \(P^{\mathsf T}H_m=H_mP\) therefore identifies two entries of \(P\) or annihilates one. Over the 35 monomials these relations leave a single free class of entries, the diagonal.

For the seed, the sequence

\[
0\longrightarrow\mathcal O_D(4)\longrightarrow\mathcal O_D(E+4H)\longrightarrow\bigoplus_{j}\mathcal O_{g^jC}(2)\longrightarrow0
\]

shows that \(m=4\) suffices in the integration lemma: the higher cohomology of \(\mathcal O_D(E+4H)\) vanishes, it has \(69\) sections, and its curves have degree \(54\) and arithmetic genus \(208\).

**Proof of the theorem.** The seed and the finite results verify the hypotheses of the moving-class criterion for the family of all smooth invariant sextics, with \(\lambda=[E]\), the orbit-sum formulas of §3D.2 and \(A=x_2x_3^3w\). The criterion gives a nonempty Zariski-open set \(\mathcal U\) of invariant sextics and, for \(T\in\mathcal U\), a smooth projective curve \(\Lambda\), possibly disconnected, and a correspondence \(\Gamma\) with \(\Gamma_*H^1(\Lambda,\mathbb Q)\supset H^3(T,\mathbb Q)^g\). Let \(Z\) be a \(g\)-stable divisor containing its image. Let \(\pi_g=(1+g+g^2)/3\), and let \(\pi_1^\Lambda\) be the projector onto \(H^1(\Lambda)\): on a component with a chosen point \(p\) it is \(\Delta_\Lambda-[p]\times\Lambda-\Lambda\times[p]\). Replace \(\Gamma\) by

\[
\pi_g\circ\Gamma\circ\pi_1^\Lambda .
\]

Its image is still contained in \(Z\). The second projector is needed here: unlike the anti-projector of [§3B.6](#technical-information/weighted-threefolds), \(\pi_g\) fixes the even cohomology of \(T\), on which a curve correspondence acts through \(H^0(\Lambda)\) and \(H^2(\Lambda)\). Now \(\Gamma_*\) vanishes outside \(H^1(\Lambda)\) and maps it onto \(H^3(T)^g\). As in §3B.6, the transpose is the adjoint for the polarizations up to a sign, so \(\Gamma\circ{}^t\Gamma\) is invertible on \(H^3(T)^g\). It is zero on the rest of the cohomology, and a polynomial in it without constant term represents the projector by a cycle supported on \(Z\times Z\).

Weighted weak Lefschetz gives \(H^{2k}(T)=\mathbb QH^k\) and \(H^3=3\). The projector is thus the class of the relative algebraic cycle

\[
\pi_g-\sum_{k=0}^3\pi_{2k},\qquad
\pi_{2k}=\tfrac13\,\mathrm{pr}_1^*H^{3-k}\cdot\mathrm{pr}_2^*H^k,
\]

over the connected family of all smooth invariant sextics. The supported-projector specialization lemma of [Chapter 3, §3.6](#technical-information/geometric-support) extends the supported representative from \(\mathcal U\) to every member. ∎

**Remark: the same theorem through a Fano fourfold.** The moving curves can also be obtained from Hodge classes on a fourfold containing \(T\), as in [Voisin, Proposition 2.1](https://www.numdam.org/item/ASNSP_1992_4_19_4_473_0.pdf). The proof above does not use this route. It is sketched here.

*The extension.* Give \(t\) weight three and trivial character. For an invariant cubic \(a\), the sextic \(\widetilde F=F+ta+t^2\) defines a fourfold \(Y\subset\mathbb P(1,1,1,1,2,3)\) with \(T=Y\cap\{t=0\}\). It is the double cover of \(\mathbb P(1,1,1,1,2)\) branched along \(a^2=4F\). Neither singular point of the ambient space lies on \(Y\), so a quasismooth \(Y\) is a smooth del Pezzo fourfold of degree one. Its rational Hodge classes of degree four are algebraic by the [corollary of Chapter 3, §3.2](#technical-information/geometric-support), and \(H^3(Y)=0\). With \(R=R(\widetilde F)\), residues give \(H^{4-p,p}(Y)_{\mathrm{prim}}\simeq R_{6p-3}\), and the invariant classes have numerators of character \(\omega\). The invariant Hodge numbers are \((h^{3,1},h^{2,2}_{\mathrm{prim}},h^{1,3})=(7,52,7)\).

*Hodge loci.* The fourfolds through \(T\) are deformed by \(\widetilde F+\varepsilon tK\), with \(K\) an invariant cubic in \((x,w,t)\). A class whose \((2,2)\)-part is represented by \(Q\in R_9^{[\omega]}\) stays of type \((2,2)\) to first order when \(K\) lies in the kernel of

\[
\mu_Q:K\longmapsto[tKQ]\in R_{15}^{[\omega]} .
\]

Modulo the Jacobian ideal the source has dimension nine and the target seven. When \(\mu_Q\) is surjective, the Hodge locus of a rational Hodge class is therefore smooth of dimension two. Relative Hilbert schemes have countably many components, so by Baire's theorem the algebraic representatives of the class form algebraic families over a dense open subset of that locus. They restrict to a moving family of one-cycles on \(T\).

*The derivative.* If \(tKQ=\sum_zc_z\,\partial_z\widetilde F\), the derivative of the Abel–Jacobi images of the restricted cycles is a nonzero multiple of

\[
\beta_Q(K)=\bigl[c_t|_{t=0}\bigr]\in R(F)_{12}^{[\omega]}\simeq H^{1,2}(T)^g .
\]

This is the weighted form of [Voisin, §§2.12–2.15](https://www.numdam.org/item/ASNSP_1992_4_19_4_473_0.pdf). The Abel–Jacobi image is read from the extension \(0\to H^3(T)\to H^4(Y,T)\to H^4(Y)\): it is the difference of a lift of the class to \(F^2H^4(Y,T)\) and a rational lift. The threefold does not move, so the rational lift is flat, and the derivative is the class in \(H^3(T)/F^2H^3(T)\) of the derivative of the first lift. The Hodge filtration is the filtration by order of pole. Take the lift given by the pair \((Q\,\Omega/\widetilde F^3,0)\) of rational forms on the ambient space and on \(\{t=0\}\). Griffiths's reduction with the vector field \(\sum_zc_z\partial_z\) lowers the pole order of the term \(tKQ\,\Omega/\widetilde F^4\) of its derivative. The exact term restricts to \(\{t=0\}\) as the form of numerator \(c_t|_{t=0}\) and pole order three, since \(t\) and \(dt\) vanish there. The class does not depend on the choice of the \(c_z\), because the partial derivatives form a regular sequence, and it vanishes on the rescaling direction \(K=\partial_t\widetilde F\).

*Density.* For surjective \(\mu_Q\), Green's density criterion, as in [Voisin, §2.17](https://www.numdam.org/item/ASNSP_1992_4_19_4_473_0.pdf), makes the rational Hodge classes dense among the real classes of type \((2,2)\) on the nearby fourfolds through \(T\). The inclusion of \(\beta_Q(\ker\mu_Q)\) in the divisor-supported part of \(H^{1,2}(T)^g\) is a Zariski-closed condition on \(Q\) in the bundle of the spaces \(R_9^{[\omega]}\), over the pairs \((a,Q)\) with \(\mu_Q\) surjective. It therefore extends from rational Hodge classes to every such pair. Surjectivity of \(\mu_Q\) and \(\beta_Q\ne0\) are open conditions on \((F,a,Q)\). One such triple therefore gives a nonzero divisor-supported part of \(H^3(T)^g\) on a nonempty open set of threefolds, and the Higgs lemma applies to it as in the moving-class criterion.

*Two witnesses.* The verifier of this section reconstructs \(\mu_Q\), its kernel and the classes \(\beta_Q(K)\) modulo \(109\) in two cases. At the Fermat member, take

\[
a=5\bigl(x_0^3+x_1^3+x_2^3+x_3^3+x_0x_2x_3+x_1x_2x_3+x_3w\bigr),\qquad Q=x_2w^4 .
\]

Modulo five the fourfold is \(F_0+t^2=0\), so it is smooth. The map \(\mu_Q\) has rank seven, and \(\beta_Q(\ker\mu_Q)\) has dimension two and a nonzero coefficient on each of the 33 standard monomials of \(R(F_0)_{12}^{[\omega]}\). These three statements persist in characteristic zero. The diagonal automorphisms \(\mu_6^4\times\mu_3\) of the Fermat sextic preserve the divisor-supported part and act on those monomials through pairwise distinct characters, so the divisor-supported part of \(H^{1,2}(T)^g\) is everything at the Fermat member. Moreover the translates of \(\beta_Q(\ker\mu_Q)\) are the spaces \(\beta_{Q'}(\ker\mu_{Q'})\) of the translated pairs \((a',Q')\). That finitely many such spaces span is an open condition on \(F\), so the same holds for general \(F\). This argument needs no Higgs lemma.

For the seed of this section, write \(F_b+2bt+t^2=(t+h)(t+k)+f_1g_1+f_2g_2\), and let \(Q\) be the part of character \(\omega\) of the Jacobian determinant of \((f_1,g_1,f_2,g_2,t+h,t+k)\). As in [Villaflor Loyola, Theorem 1](https://arxiv.org/abs/1812.03964), it represents the invariant part of the class of the surface \(f_1=f_2=t+h=0\). The substitution \(t\mapsto t-b\) carries this fourfold and this surface to the fourfold \(F_0+t^2=0\) and the surface of the seed. Modulo \(109\), \(\mu_Q\) has rank seven, and its kernel is spanned by \(\partial_t\widetilde F\), by \(h-k\), and by one further direction. On \(h-k\) the class \(\beta_Q\) vanishes: the move \((h,k)\mapsto(ch,k/c)\) changes the fourfold and keeps the curve. On the further direction, the pairing of \(\beta_Q\) with \(A\in R(F_b)_6^{[\omega]}\) through the socle of \(R(F_b)\) is proportional to \(A\mapsto\tau(AL)\), for \(L\) in the kernel of \(\operatorname{NL}_E\). At that prime the two routes compute the same Abel–Jacobi derivative on this seed.

The count \(9-7\) is the fourfold counterpart of the count of §3D.1, and it also vanishes when the symmetry fixes the holomorphic three-form. This route needs the Hodge conjecture on the fourfold and the density argument, which the proof above avoids.

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

Let \(\alpha\) be an invariant class. Its pullback to the blowup, restricted over \(U\), is \(\beta\)-invariant, hence the pullback of a \(g\)-invariant class \(\alpha'\) on \(\mathcal T\). Leray gives \(\alpha'=c\,H^2+\alpha''\) with \(\alpha''\in H^1(U,(R^3p_*\mathbb Q)^g)\). Both terms vanish off a divisor. Adding the omitted fibers and the exceptional divisor and pushing forward supports \(\alpha\) on \(X\). ∎

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
