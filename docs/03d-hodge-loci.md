# 3D. Hodge loci of surface sections

[Previous: quadratic nets and pair correspondences](03c-quadratic-nets.md) · [Contents](README.md) · [Next: families, representations and deformation](04-known-locus-and-frontier.md)

A divisor class on a surface section of a Calabi–Yau threefold stays algebraic along a locus of sections. When a symmetry moves the holomorphic three-form, the invariant part of this locus has positive expected dimension. Curves in the class then move on the threefold, and the derivative of their Abel–Jacobi images is a trace on an Artinian algebra. If the invariant variation of Hodge structure has no proper sub-variation, one nonzero derivative supports the whole invariant sector of the third cohomology on a divisor.

Moving cycles along Hodge loci is the strategy of [Voisin, Proposition 2.1](https://www.numdam.org/item/ASNSP_1992_4_19_4_473_0.pdf), and the loci of surface sections of a Calabi–Yau threefold are studied in [Voisin, §2](https://www.cmls.polytechnique.fr/perso/voisin/Articlesweb/griffithsgroup.pdf). Chapter 3B follows the same strategy with explicitly constructed curves. This chapter applies it to weighted sextic threefolds with an order-three symmetry that moves the holomorphic three-form, and then to sextic fourfolds with a paired sign and such a symmetry. §3D.6 counts sections and classes of other characters, and applies the method to an order-three symmetry that fixes the three-form. §3D.7 proves the criterion and the theorem of §3D.4 again, using Hodge theory only for the first cohomology of curves. §3D.8 applies the method directly to a family of fourfolds invariant under the paired signs and two coordinate exchanges: Hodge classes on a second smooth sextic are cut by a quadric section with six nodes, common to the two fourfolds, that moves in a pencil.

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

For \(\delta=1\) the two spaces coincide and the count is zero. This is necessary: the invariant part of \(H^3(T)\) then contains \(H^{3,0}(T)\), and for a general member of a family with irreducible invariant variation no nonzero part of it is supported on a divisor. For \(\delta\ne1\) the count is \(\dim S_e^G-1-\dim S_e^{[\delta^{-1}]}\). For invariant classes on invariant sections, a positive count therefore requires a symmetry that moves the holomorphic three-form. §3D.6 counts sections and classes of other characters, where it does not.

**Integration lemma.** Suppose \(\operatorname{NL}_\lambda\) is surjective. Near \((F,h)\), the pairs \((F',h')\) of invariant polynomials for which \(\lambda\) remains of type \((1,1)\) form a smooth family. It is submersive over the invariant \(F'\), with fibers of dimension \(n-c\) modulo rescaling. On it \(\lambda\) is the class of a unique line bundle \(\mathcal L'\), which is \(G\)-invariant, and for large \(m\) the curves of \(|\mathcal L'(m)|\) form a projective bundle over it. This bundle is an open subset, in the classical topology, of the relative Hilbert scheme of curves in the surfaces \(D'\), and that scheme is smooth along it.

**Proof.** The locus is the zero set of a holomorphic section of the bundle with fibers \(H^{0,2}(D')^G\): the \((0,2)\)-part of the flat transport of \(\lambda\). Its derivative is \(\overline\nabla\lambda\), as in [Voisin, §2, Lemma 2](https://www.cmls.polytechnique.fr/perso/voisin/Articlesweb/griffithsgroup.pdf). By hypothesis this derivative is already surjective on the directions in which only \(h\) moves. That gives smoothness and both dimension statements. A class of type \((1,1)\) is the class of a line bundle. It is unique because \(H^1(\mathcal O_{D'})=0\), hence invariant. Serre vanishing and base change give the projective bundle.

The bundle maps injectively and holomorphically to the relative Hilbert scheme of curves in the surfaces \(D'\), over the space of invariant pairs. Let \(\Gamma'\subset D'\) be one of its curves. A tangent vector to that scheme at \(\Gamma'\) lies over a tangent vector to the space of pairs along which the class of \(\Gamma'\) stays of type \((1,1)\) to first order, that is, over a tangent vector to the smooth family. The tangent vectors lying over zero form \(H^0(N_{\Gamma'/D'})\). Its dimension is \(h^0(\mathcal L'(m))-1\), that of the linear system, again because \(H^1(\mathcal O_{D'})=0\). The tangent space of the Hilbert scheme at \(\Gamma'\) therefore has at most the dimension of the bundle. So the scheme is smooth there, and the bundle is a neighborhood of \(\Gamma'\) in it. ∎

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

**Derivative lemma.** Let \(\lambda\) be a divisor class on \(D\), and let \(h_s\) be a family of sections of the fixed \(T\) along which \(\lambda\) stays algebraic, with tangent \(L\) at \(h\). Let \(\Gamma_s\) be a curve of class \(\lambda+mH\) on \(D_s\), for \(m\) large, and let \(\nu(s)\) be the Abel–Jacobi image of \(\Gamma_s-\Gamma_{s_0}\), for a fixed \(s_0\). This cycle is homologous to zero on \(T\), and \(\nu(s)\) does not depend on the choice of \(\Gamma_s\), because the curves of one class on \(D_s\) are linearly equivalent. For \(A\in S_d\), with class \(\eta_A\in H^{2,1}(T)\), the number

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

The lift is unique up to the image of \(H^0(K_D)\) under the connecting map. That map is contraction with the extension class of the conormal sequence, so the image of a two-form \(\omega\) changes \(L\,\widetilde\eta\) by \(\pm\rho_L\mathbin{\lrcorner}\omega\), where \(\rho_L\) is the Kodaira–Spencer class of the motion \(L\). The integral below then changes by \(\pm\langle\overline\nabla_L[\Gamma],\omega\rangle\), which is zero because the class of \(\Gamma\) stays of type \((1,1)\) along \(h_s\). So the integral does not depend on the lift.

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

For a sector at a Fermat member, the [sector alternative of Chapter 4, §4.4](04-known-locus-and-frontier.md#strict-growth-and-sectors) gives the same conclusion from a matching condition on monomials, with Hodge symmetry in place of the polarization. §3D.7 proves the criterion below from that condition and the first cohomology of curves.

**Moving-class criterion.** Let \(\mathcal B\) be an irreducible family of invariant polynomials \(F\) as in §3D.1, with \(\delta\ne1\), all defining smooth threefolds. Suppose that

1. at one member there are an invariant section \(h\) and an invariant divisor class \(\lambda\) on \(D\) with \(\operatorname{NL}_\lambda\) surjective, together with \(L\in\ker\operatorname{NL}_\lambda\) and \(A\in S_d^{[\delta^{-1}]}\) for which the pairing of the derivative lemma is nonzero;
2. at one member the hypothesis of the Higgs lemma holds for \(\mathbb V=(R^3p_*\mathbb Q)^G\) over \(\mathcal B\).

Then for \(T\) in a nonempty Zariski-open subset of \(\mathcal B\) there are a smooth projective curve \(\Lambda\) and a correspondence \(\Gamma\) with

\[
\Gamma_*H^1(\Lambda,\mathbb Q)\supset H^3(T,\mathbb Q)^G .
\]

In particular \(H^3(T,\mathbb Q)^G\subset N^1H^3(T,\mathbb Q)\).

In Jacobian rings the forms of the second hypothesis are \(H_A(B,B')=\operatorname{soc}(ABB')\) on \(R(F)_d^{[\delta^{-1}]}\), for the \(A\in R(F)_d^G\) tangent to \(\mathcal B\).

**Proof.** By the integration lemma, the pairs carrying the class form a smooth family that is submersive over \(\mathcal B\) near the first member, with a projective bundle of curves of class \(\lambda+mH\), and this bundle is open in the relative Hilbert scheme of curves in the surfaces. Let \(\mathcal H\) be the irreducible component of that scheme containing it. It is an algebraic family of curves on the threefolds, and its image in \(\mathcal B\) contains a nonempty Zariski-open subset. The pairing is nonzero, so \(L\) is not a multiple of \(h\) and the fibers of the smooth family over \(\mathcal B\) have positive dimension. Cut \(\mathcal H\) by hypersurfaces through a point of the bundle over the first member, chosen so that the result has relative dimension one over \(\mathcal B\) near that point and its fiber there is tangent to a lift of \(L\). After a finite étale cover of an open subset of \(\mathcal B\), complete and normalize the parameter curves. The result is a family of smooth projective curves \(\Lambda\) with a relative correspondence \(\Gamma\) to the threefolds. By the derivative lemma its Abel–Jacobi map is not constant near the first member, and its derivative pairs nontrivially with \(H^{2,1}(T)^G\). The image of \(\pi_G\circ\Gamma_*\), with \(\pi_G\) the averaging projector, is therefore a nonzero rational sub-variation of the pullback of \(\mathbb V\). Since \(\delta\ne1\), \(\mathbb V\) has no \((3,0)\)-part, and by the Higgs lemma the sub-variation is everything. ∎

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

As in [Chapter 3B, §3B.1](03b-weighted-threefolds.md), \(T\) avoids the weighted vertex and is a smooth Calabi–Yau threefold with \(h^{2,1}=103\). Here \(\delta=\omega^5=\omega^2\). The Jacobian ring gives the Hodge numbers of the three eigenspaces:

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

**Finite results.** The verifier [`scripts/verify-hodge-locus-span.py`](../scripts/verify-hodge-locus-span.py) reconstructs the algebra \(\mathcal A\), its trace and the pairings of §3D.2 modulo \(109\), with \(r=57\), \(i=33\) and

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

Its image is still contained in \(Z\). The second projector is needed here: unlike the anti-projector of [§3B.6](03b-weighted-threefolds.md), \(\pi_g\) fixes the even cohomology of \(T\), on which a curve correspondence acts through \(H^0(\Lambda)\) and \(H^2(\Lambda)\). Now \(\Gamma_*\) vanishes outside \(H^1(\Lambda)\) and maps it onto \(H^3(T)^g\). As in §3B.6, the transpose is the adjoint for the polarizations up to a sign, so \(\Gamma\circ{}^t\Gamma\) is invertible on \(H^3(T)^g\). It is zero on the rest of the cohomology, and a polynomial in it without constant term represents the projector by a cycle supported on \(Z\times Z\).

Weighted weak Lefschetz gives \(H^{2k}(T)=\mathbb QH^k\) and \(H^3=3\). The projector is thus the class of the relative algebraic cycle

\[
\pi_g-\sum_{k=0}^3\pi_{2k},\qquad
\pi_{2k}=\tfrac13\,\mathrm{pr}_1^*H^{3-k}\cdot\mathrm{pr}_2^*H^k,
\]

over the connected family of all smooth invariant sextics. The supported-projector specialization lemma of [Chapter 3, §3.6](03-geometric-support.md) extends the supported representative from \(\mathcal U\) to every member. ∎

**Remark: the same theorem through a Fano fourfold.** The moving curves can also be obtained from Hodge classes on a fourfold containing \(T\), as in [Voisin, Proposition 2.1](https://www.numdam.org/item/ASNSP_1992_4_19_4_473_0.pdf). The proof above does not use this route. It is sketched here.

*The extension.* Give \(t\) weight three and trivial character. For an invariant cubic \(a\), the sextic \(\widetilde F=F+ta+t^2\) defines a fourfold \(Y\subset\mathbb P(1,1,1,1,2,3)\) with \(T=Y\cap\{t=0\}\). It is the double cover of \(\mathbb P(1,1,1,1,2)\) branched along \(a^2=4F\). Neither singular point of the ambient space lies on \(Y\), so a quasismooth \(Y\) is a smooth del Pezzo fourfold of degree one. Its rational Hodge classes of degree four are algebraic by the [corollary of Chapter 3, §3.2](03-geometric-support.md), and \(H^3(Y)=0\). With \(R=R(\widetilde F)\), residues give \(H^{4-p,p}(Y)_{\mathrm{prim}}\simeq R_{6p-3}\), and the invariant classes have numerators of character \(\omega\). The invariant Hodge numbers are \((h^{3,1},h^{2,2}_{\mathrm{prim}},h^{1,3})=(7,52,7)\).

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

The passage to a fourfold uses the relative support lemma for an invariant sector in [Chapter 3, §3.6](03-geometric-support.md).

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

**Proof.** Follow the proof of the two-reflection theorem in [§3B.7](03b-weighted-threefolds.md) with the pencil \(\lambda=v/u\). The base surface \(X\cap\{u=v=0\}\) is smooth: there \(\partial_uF\) and \(\partial_vF\) vanish because they are odd in \((u,v)\), so a singular point of the surface would be singular on \(X\). The restriction \(F(0,u,v)\) is not identically zero. Otherwise \(X\) would contain the line \(x=0\), along which the four core derivatives vanish, being coefficients of monomials of odd degree in \((u,v)\). Blow up the base surface. For \(\lambda\) in a nonempty open \(U\subset\mathbb P^1\), the fiber \(V_\lambda=X\cap\{v=\lambda u\}\) is smooth, \(\beta\) acts on it as the reflection \(u\mapsto-u\), and with \(w=u^2\) the quotient

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

Of the 85 invariant monomials, 45 are \(Y\)-even. A \(Y\)-odd numerator \(A\) is served when its residue is invariant, that is, when \(A\) is even in \((X_2,Y_2)\) and \(\gamma^*A=\omega A\). The support-to-certificate equivalence of [Chapter 1](01-certificates.md) then gives a certificate for pole orders \(1\le q\le4\). The reduction of [Chapter 3, §3.5](03-geometric-support.md) extends this to larger pole orders once its auxiliary field is averaged over \(\langle\beta,\gamma\rangle\), which keeps the reduced target in the invariant sector.

**Example: three cyclic links.** Let \(\rho\) permute the three pairs \((X_i,Y_i)\) cyclically. The conjugates \(\gamma_i=\rho^i\gamma\rho^{-i}\) and the paired signs \(s_i\) generate, with \(\tau\), a diagonal group of projective order 72. It contains the element \(h\) of [Chapter 4, §4.2](04-known-locus-and-frontier.md). Its invariant sextics are

\[
F=\sum_i\bigl(a_iX_i^6+b_iY_i^6\bigr)
+\sum_ic_i\,X_i^3X_{i+1}Y_iY_{i+1}
+\sum_ie_i\,X_i^2Y_{i-1}^2Y_i^2,
\]

with indices modulo three. For a smooth member, the \(Y\)-even primitive cohomology, of type \((208,866,208)\), splits into three parts according to the characters of this group:

| Characters | Hodge numbers | Support |
| --- | --- | --- |
| Nontrivial on the paired signs | \((150,636,150)\) | [Paired signs, §3B.9](03b-weighted-threefolds.md) |
| Trivial on the paired signs and on \(h^2\) | \((22,74,22)\) | [Paired-sign sector theorem, §4.2](04-known-locus-and-frontier.md), when its surface is smooth |
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

## 3D.6 Other sectors and a symmetry that fixes the three-form

The count of §3D.1 concerns invariant classes on invariant sections. Neither restriction is needed. Without them, a symmetry that fixes the holomorphic three-form can also give a positive count, for the part of the cohomology on which it has no invariants.

**Sectors.** Let \(G\) act as in §3D.1, by pullback on cohomology. Let \(\Psi\) be a set of characters of \(G\) that contains \(\psi^a\) whenever it contains \(\psi\) and \(a\) is prime to \(|G|\). Then

\[
\pi_\Psi=\frac1{|G|}\sum_{\psi\in\Psi}\sum_{\gamma\in G}\psi(\gamma)^{-1}\gamma
\]

is an idempotent of \(\mathbb Q[G]\). For a rational Hodge structure \(H\) with an action of \(G\), write \(H_\Psi=\pi_\Psi H\). Over \(\mathbb C\) it is the sum of the eigenspaces with characters in \(\Psi\). By §3D.1,

\[
H^{3,0}(T)_\Psi=0\iff\delta\notin\Psi,
\qquad
H^{2,1}(T)_\Psi\simeq\bigoplus_{\psi\in\Psi}R(F)_d^{[\psi\delta^{-1}]} .
\]

Let \(h\in S_e\), with \(0<e<d\), have character \(\kappa\) and cut a smooth surface \(D\). Then \(D\) is \(G\)-stable, and so are the surfaces cut by \(h+\varepsilon L\) for \(L\in S_e^{[\kappa]}\). The residue of \(\sigma\,\Omega/(Fh)\) has character \(\chi(\sigma)\delta\kappa^{-1}\), so

\[
H^{2,0}(D)_\Psi\simeq\bigoplus_{\psi\in\Psi}(S_e/\mathbb Ch)^{[\psi\kappa\delta^{-1}]} .
\]

Let \(\lambda\) be a divisor class on \(D\) with \(\pi_\Psi\lambda=\lambda\). Its flat transport along these sections stays in the image of \(\pi_\Psi\). Eigenspaces pair to zero unless their characters are inverse to each other, and \(\Psi\) is stable under inversion, so the \((0,2)\)-part of the transport pairs to zero with every two-form outside \(H^{2,0}(D)_\Psi\). The first-order condition is thus the kernel of

\[
\operatorname{NL}_\lambda:S_e^{[\kappa]}\longrightarrow\bigl(H^{2,0}(D)_\Psi\bigr)^\vee,
\]

and the expected dimension, modulo rescaling of \(h\), is

\[
n-c=\dim S_e^{[\kappa]}-1-\sum_{\psi\in\Psi}\dim(S_e/\mathbb Ch)^{[\psi\kappa\delta^{-1}]} .
\]

For \(\Psi=\{1\}\) and \(\kappa=1\) this is the count of §3D.1.

**The criterion for a sector.** Suppose \(\delta\notin\Psi\). The integration lemma holds for the pairs \((F',h')\) with \(F'\) invariant and \(h'\) of character \(\kappa\), for a class with \(\pi_\Psi\lambda=\lambda\), and with \(H^{0,2}(D')_\Psi\) in place of \(H^{0,2}(D')^G\). Its line bundle need not be invariant, and no later step uses that. The moving-class criterion holds with \(h\) of character \(\kappa\), with \(\pi_\Psi\lambda=\lambda\), with \(A\in S_d\) of a character in \(\Psi\delta^{-1}\), and with \(\mathbb V=(R^3p_*\mathbb Q)_\Psi\) and \(\pi_\Psi\) in place of the invariant variation and \(\pi_G\). Its conclusion is

\[
\Gamma_*H^1(\Lambda,\mathbb Q)\supset H^3(T,\mathbb Q)_\Psi .
\]

The forms of its second hypothesis are \(H_A(B,B')=\operatorname{soc}(ABB')\) on \(\bigoplus_{\psi\in\Psi}R(F)_d^{[\psi\delta^{-1}]}\), for the \(A\in R(F)_d^G\) tangent to \(\mathcal B\). The proofs are those of §3D.1 and §3D.3. They used \(\delta\ne1\) only to exclude a \((3,0)\)-part, and \(\delta\notin\Psi\) does the same.

**Translates.** In the setting of §3D.2, let \(a=\sum_\gamma a_\gamma\gamma\in\mathbb Q[G]\) and \(\lambda=\sum_\gamma a_\gamma[\gamma C]\). For a character \(\psi\) put \(\psi(a)=\sum_\gamma a_\gamma\psi(\gamma)\). Let \(L\) have character \(\kappa\).

- If the two-form of numerator \(\sigma\) has character \(\psi\), then \(\operatorname{NL}_\lambda(L)(\sigma)\) is a nonzero multiple of \(\psi(a)\,\tau(kL\sigma)\).
- If \(\eta_A\) has character \(\psi\), then the pairing of the derivative lemma is a nonzero multiple of \(\psi(a)\,\tau(AL)\).

Indeed, \(\gamma^{-1}\) carries \(\gamma C\) to \(C\). It preserves the surfaces \(V(F,h+\varepsilon L)\), and it carries \(V(F+\varepsilon A,h)\) to \(V(F+\varepsilon\chi(A)(\gamma)A,h)\). The obstruction of \([\gamma C]\) is therefore the pullback by \(\gamma^{-1}\) of the obstruction of \([C]\), multiplied by \(\chi(A)(\gamma)\) in the second case. Its pairing with a two-form \(\omega\) is the pairing of the obstruction of \([C]\) with \(\gamma^*\omega\). In the first case \(\gamma^*\omega=\psi(\gamma)\omega\). In the second \(\omega\) has numerator \(L\) and \(\gamma^*\omega=\delta(\gamma)\omega\), while \(\chi(A)\delta\) is the character of \(\eta_A\). For \(a=\sum_\gamma\gamma\) these are the orbit sums of §3D.2.

**An order-three symmetry that fixes the three-form.** Let

\[
g=(1,\omega,\omega,\omega;1)
\]

act on \(\mathbb P(1,1,1,1,2)\), and let \(\Psi\) consist of the two nontrivial characters of \(\langle g\rangle\). Then \(\delta=1\notin\Psi\) and \(\pi_\Psi=1-\pi_g\), with \(\pi_g=(1+g+g^2)/3\).

**Order-three sector theorem.** Let \(T\subset\mathbb P(1,1,1,1,2)\) be a quasismooth sextic with \(g\)-invariant equation. Then

\[
(1-\pi_g)\,H^3(T,\mathbb Q)\subset N^1H^3(T,\mathbb Q).
\]

More precisely, the correspondence \(1-\pi_g\), which acts on \(H^*(T,\mathbb Q)\) as the projector onto \((1-\pi_g)H^3(T,\mathbb Q)\), is cohomologous to a rational algebraic cycle supported on \(Z\times Z\) for some divisor \(Z\subset T\).

The invariant sextics are the polynomials in \(x_0\), \(w\) and the forms of degree divisible by three in \((x_1,x_2,x_3)\). They have 52 coefficients. As in §3D.4, \(T\) is a smooth Calabi–Yau threefold with \(h^{2,1}=103\), and the Jacobian ring gives the Hodge numbers of the three eigenspaces:

| Eigenvalue of \(g\) | \((h^{3,0},h^{2,1},h^{1,2},h^{0,3})\) |
| --- | --- |
| \(1\) | \((1,40,40,1)\) |
| \(\omega\) | \((0,33,30,0)\) |
| \(\omega^2\) | \((0,30,33,0)\) |

The theorem concerns the last two rows together, a rational Hodge structure of type \((0,63,63,0)\). The first row contains \(H^{3,0}(T)\), and its count in §3D.1 is zero.

**The count.** Take linear sections of character \(\omega\), so \(e=1\), \(\kappa=\omega\) and \(S_1^{[\omega]}=\langle x_1,x_2,x_3\rangle\). For \(\psi\in\Psi\) the characters \(\psi\kappa\) are \(\omega^2\) and \(1\). No linear form has character \(\omega^2\), and only \(x_0\) has character \(1\). Hence

\[
n-c=3-1-1=1 .
\]

**A seed.** Let \(i^2=-1\) and \(\ell=x_1+x_2\), and set

\[
\begin{aligned}
f_1&=x_0-i\,x_1,&g_1&=\sum_{j=0}^5i^j\,x_0^{5-j}x_1^j,\\
f_2&=w+x_2^2,&g_2&=w^2-w\,x_2^2+x_2^4,\\
h&=x_3-\ell,&k&=\sum_{j=0}^5x_3^{5-j}\ell^j .
\end{aligned}
\]

Then

\[
F=f_1g_1+f_2g_2+hk=x_0^6+x_1^6+x_2^6+x_3^6+w^3-\ell^6
\]

is invariant, \(h\) has character \(\omega\), and \(f_1\) is not an eigenvector of \(g\). Put

\[
D=V(F,h),\qquad C=V(f_1,f_2,h),\qquad\lambda=[C]-[gC] .
\]

Then \(\pi_g\lambda=0\). The threefold is quasismooth. Indeed \(F=x_0^6+w^3+x_3^6+b(x_1,x_2)\) with \(b=x_1^6+x_2^6-(x_1+x_2)^6=-x_1x_2\,q\) and

\[
q=6x_1^4+15x_1^3x_2+20x_1^2x_2^2+15x_1x_2^3+6x_2^4=x_1^2x_2^2\,(6u^2+15u+8),
\qquad u=\frac{x_1}{x_2}+\frac{x_2}{x_1}.
\]

The two roots of \(6u^2+15u+8\) are distinct and different from \(\pm2\), so \(b\) has six distinct roots and the partial derivatives of \(F\) have no common zero. Eliminating \(x_3\) identifies \(D\) with the Fermat surface \(x_0^6+x_1^6+x_2^6+w^3=0\) in \(\mathbb P(1,1,1,2)\), which is smooth, and \(C\) with the line \(x_0=i\,x_1\), \(w=-x_2^2\) on it.

Eliminating \(x_0\), \(x_3\) and \(w\) through \(f_1\), \(h\) and \(f_2\) sends \(g_1\) to \(6i\,x_1^5\) and \(g_2\) to \(3x_2^4\). Thus

\[
\mathcal A\simeq\mathbb C[x_1,x_2]/(x_1^5,x_2^4),
\]

of length \(20\), with socle spanned by \(x_1^4x_2^3\) in degree seven. Let \(\tau\) be the coefficient of \(x_1^4x_2^3\). In \(\mathcal A\) we have \(k=6\ell^5\) and \(x_0=i\,x_1\), so

\[
\tau(k\,x_1x_0)=\tau(k\,x_2x_0)=6i\binom52=60\,i .
\]

The only two-form of \(H^{2,0}(D)_\Psi\) has numerator \(x_0\) and character \(\omega^2\). By the formulas for translates with \(a=1-g\), the map \(\operatorname{NL}_\lambda\) is a nonzero multiple of \(L\mapsto\tau(kLx_0)\). It is surjective, and its kernel modulo \(h\) is spanned by \(L_0=x_1-x_2\). For \(A=x_0^2x_1^2x_2^2\), of character \(\omega\),

\[
\tau(AL_0)=\tau\bigl(-x_1^4x_2^2(x_1-x_2)\bigr)=1 ,
\]

so the pairing of the derivative lemma is nonzero.

**Finite results.** The verifier of §3D.4 also recomputes this seed from its generators modulo \(109\), with \(i=33\), and the Higgs forms at the Fermat member \(F_0\).

| Calculation | Result |
| --- | --- |
| Standard monomials of degrees \(0,6,12,18\), by character | the table above |
| Length and socle degree of \(\mathcal A\) | \(20\) and \(7\) |
| \(\tau(kx_1x_0)\), \(\tau(kx_2x_0)\) and \(60\,i\,\tau(AL_0)\) | equal and nonzero |
| Matrices \(P\) with \(P^{\mathsf T}H_m=H_mP\) for the \(40\) invariant monomials \(m\) at \(F_0\) | the scalars |

For the last line, \(P\) acts on the span of the 63 standard monomials of degree six and nonzero character, and the relations are found by merging entries as in §3D.4.

**Proof of the theorem.** The seed and the finite results verify the hypotheses of the criterion for a sector, for the family of all smooth invariant sextics, with \(\lambda=[C]-[gC]\), \(L=L_0\) and \(A=x_0^2x_1^2x_2^2\). The criterion gives a nonempty Zariski-open set \(\mathcal U\) of invariant sextics and, for \(T\in\mathcal U\), a smooth projective curve \(\Lambda\), possibly disconnected, and a correspondence \(\Gamma\) with \(\Gamma_*H^1(\Lambda,\mathbb Q)\supset(1-\pi_g)H^3(T,\mathbb Q)\). Let \(Z\) be a \(g\)-stable divisor containing its image, and replace \(\Gamma\) by \((1-\pi_g)\circ\Gamma\). Its image is still contained in \(Z\). Since \(g\) acts trivially on \(H^{2k}(T)=\mathbb QH^k\), the new \(\Gamma_*\) vanishes on \(H^0(\Lambda)\) and \(H^2(\Lambda)\), and it maps \(H^1(\Lambda)\) onto \((1-\pi_g)H^3(T)\). No projector on \(\Lambda\) is needed, as for the anti-projector of [§3B.6](03b-weighted-threefolds.md). As there, \(\Gamma\circ{}^t\Gamma\) is invertible on \((1-\pi_g)H^3(T)\) and zero on the rest of the cohomology, and a polynomial in it without constant term represents \(1-\pi_g\) by a cycle supported on \(Z\times Z\). The correspondence \(1-\pi_g\) is a relative algebraic cycle over the connected family of all smooth invariant sextics. The supported-projector specialization lemma of [Chapter 3, §3.6](03-geometric-support.md) extends the supported representative from \(\mathcal U\) to every member. ∎

**Fourfolds.** The passage of §3D.5 applies to this sector.

**Theorem.** Let \(X=(F=0)\subset\mathbb P^5\) be a smooth sextic with coordinates \((x_0,x_1,x_2,x_3,u,v)\). Suppose \(F\) is invariant under

\[
\beta:(u,v)\mapsto(-u,-v),
\qquad
\gamma=\operatorname{diag}(1,\omega,\omega,\omega,1,1),
\]

and put \(\pi_\gamma=(1+\gamma+\gamma^2)/3\). Then

\[
(1-\pi_\gamma)\,H^4(X,\mathbb Q)^{\beta}\subset N^1H^4(X,\mathbb Q).
\]

The determinant of \(\gamma\) is one, so \(H^{4,0}(X)\) is \(\gamma\)-invariant and the statement is consistent with coniveau. The invariant sextics form an 84-coefficient linear system, and the supported part of the primitive cohomology has type \((156,612,156)\).

**Proof.** The construction in the proof in §3D.5 uses only \(\beta\). It gives the pencil \(\lambda=v/u\) and, over a nonempty open \(U\subset\mathbb P^1\), the family \(p:\mathcal T\to U\) of quasismooth sextics \(T_\lambda=V_\lambda/\beta\) avoiding the vertex. Their equations are invariant under \(g\), the action of \(\gamma\). By the order-three sector theorem, \(1-\pi_g\) has a supported representative at every fiber. The proof of the relative support lemma for an invariant sector uses the sector only through its projector. With \(V=(1-\pi_g)R^3p_*\mathbb Q\) it supplies, after removing finitely many points of \(U\), a divisor of \(\mathcal T\) supporting \(H^1(U,V)\).

Let \(\alpha\) be a \(\beta\)-invariant class with \(\pi_\gamma\alpha=0\). Its pullback to the blowup, restricted over \(U\), is the pullback of a class \(\alpha'\) on \(\mathcal T\) with \(\pi_g\alpha'=0\). The image of \(\alpha'\) in \(H^0(U,R^4p_*\mathbb Q)\) vanishes, because \(g\) acts trivially on \(R^4p_*\mathbb Q=\mathbb QH^2\). Hence \(\alpha'\in H^1(U,V)\), and it vanishes off a divisor. Adding the omitted fibers and the exceptional divisor and pushing forward supports \(\alpha\) on \(X\). ∎

In the coordinates of this book, take \((u,v)=(X_2,Y_2)\) and \((x_0,x_1,x_2,x_3)=(X_0,X_1,Y_0,Y_1)\). Then \(\beta\) is the paired sign \(s_2\) and

\[
\gamma=\operatorname{diag}(1,\omega,1,\omega,\omega,1)
\quad\text{on}\quad(X_0,X_1,X_2,Y_0,Y_1,Y_2).
\]

Of the 84 invariant monomials, 44 are \(Y\)-even. On a smooth \(Y\)-even member, the \(Y\)-even primitive cohomology, of type \((208,866,208)\), splits into three parts:

| Part | Hodge numbers | Support |
| --- | --- | --- |
| \(s_2\)-invariant, without \(\gamma\)-invariants | \((74,298,74)\) | The theorem above |
| \(s_2\)-invariant and \(\gamma\)-invariant | \((34,144,34)\) | Not given by this theorem |
| \(s_2\)-anti-invariant | \((100,424,100)\) | Not given by this theorem |

A \(Y\)-odd numerator \(A\) has its residue in the first part when it is even in \((X_2,Y_2)\) and none of its monomials has degree divisible by three in \((X_1,Y_0,Y_1)\). The support-to-certificate equivalence of [Chapter 1](01-certificates.md) then gives a certificate for pole orders \(1\le q\le4\).

## 3D.7 The criterion from weight one

The proofs above use the Hodge decomposition of the second cohomology of the surface sections, Griffiths's formula for the Abel–Jacobi map, and the polarization of the third cohomology of the threefold. This section proves the moving-class criterion and the order-three weighted threefold theorem of §3D.4 from one transcendental input: the complex conjugation that the comparison with singular cohomology puts on de Rham cohomology, and its positivity on the first cohomology of a curve. Everything else is deformation theory and the algebraic theory of de Rham cohomology. The hypothesis on the Higgs field changes. Strict growth, as in [Chapter 4, §4.4](04-known-locus-and-frontier.md#strict-growth-and-sectors), replaces the commutant condition of the Higgs lemma.

**Conjugation.** For a smooth projective complex variety \(X\), let \(H^k(X)\) be the algebraic de Rham cohomology, with its cup product, its Hodge filtration \(F\), whose graded pieces are the groups \(H^q(X,\Omega^p_X)\), and the trace \(\operatorname{tr}_X\) on the top degree. The comparison isomorphism \(H^k(X)\simeq H^k(X^{\mathrm{an}},\mathbb Q)\otimes\mathbb C\) carries complex conjugation of the coefficients to an antilinear involution \(x\mapsto\bar x\) of \(H^k(X)\). Two of its properties are used.

1. Conjugation commutes with pullbacks and cup products, and \(\overline{c_1(\mathcal L)}=-c_1(\mathcal L)\) for every line bundle \(\mathcal L\), because the de Rham Chern class is \(2\pi i\) times a rational class.
2. On a smooth projective curve \(\Lambda\), the number \(\operatorname{tr}_\Lambda(\omega\cup\bar\omega)=(2\pi i)^{-1}\int_\Lambda\omega\wedge\bar\omega\) is real and nonzero for every nonzero \(\omega\in F^1H^1(\Lambda)=H^0(\Lambda,\Omega^1_\Lambda)\), and its sign depends neither on \(\omega\) nor on \(\Lambda\).

The first property extends to pushforwards. On a connected \(X\) of dimension \(r\), the top cohomology is spanned by the \(r\)-th power of an ample class, whose trace is rational, so \(\operatorname{tr}_X(\bar z)=(-1)^r\,\overline{\operatorname{tr}_X(z)}\). Proper pushforwards are the adjoints of pullbacks for the trace pairings, and the class of a subvariety is the pushforward of the unit class of a resolution. Hence pushforwards, classes of algebraic cycles and actions of correspondences commute with conjugation up to signs that depend only on the dimensions.

On a curve \(\Lambda\), the subspace \(F^1H^1(\Lambda)\) is isotropic for the cup product, because \(F^2H^2(\Lambda)=0\). If \(\omega\) and \(\bar\omega\) both lie in it, then \(\operatorname{tr}_\Lambda(\omega\cup\bar\omega)=0\), and \(\omega=0\) by the second property. Therefore

\[
H^1(\Lambda)=F^1H^1(\Lambda)\oplus\overline{F^1H^1(\Lambda)} .
\]

**Strict growth.** Let \(G\), \(\delta\ne1\) and \(\mathcal B\) be as in the moving-class criterion, with \(\mathcal B\) smooth. For a member \(T\) put \(V=H^3(T)^G\). Since \(\delta\ne1\), we have \(F^3V=0\) and \(F^1V=V\). Write \(V^{2,1}=F^2V\) and \(V^{1,2}=V/F^2V\). These spaces are dual to each other by Serre duality, of dimension \(N=\dim R(F)_d^{[\delta^{-1}]}\), and they form algebraic vector bundles over \(\mathcal B\). The Gauss–Manin connection induces the Higgs maps \(\overline\nabla_v:V^{2,1}\to V^{1,2}\), for \(v\) tangent to \(\mathcal B\). In Jacobian rings they are the multiplications \(R(F)_d^{[\delta^{-1}]}\to R(F)_{2d}^{[\delta^{-1}]}\) by the \(A\in R(F)_d^G\) tangent to \(\mathcal B\).

Say that the Higgs maps of \(\mathcal B\) *grow strictly* at a member if the images \(\overline\nabla_vV^{2,1}\) span \(V^{1,2}\) and, for every subspace \(W\subset V^{2,1}\) with \(0<\dim W<N\), the images \(\overline\nabla_vW\) span a space of dimension greater than \(\dim W\). The members at which this fails form a closed subset of \(\mathcal B\), as in the proof of the sector alternative. For the family of all smooth \(G\)-invariant sextics in \(\mathbb P(1,1,1,1,2)\), the strict-growth lemma gives the condition at the Fermat member when the graph of the sector alternative has a perfect matching and satisfies the hypothesis of the lemma. The second row of the table of §4.4 is the case of §3D.4.

**Weight-one alternative.** Suppose that the Higgs maps of \(\mathcal B\) grow strictly at one member. Let \(\phi:B'\to\mathcal B\) be a dominant morphism from a smooth connected variety, and let \(\Lambda\to B'\) be a smooth projective family of curves. Let \(\Gamma\) be a relative correspondence from \(\Lambda\) to the pulled-back family of threefolds: a cycle on their fiber product over \(B'\) whose components are flat over \(B'\), with fibers of dimension two. For \(b\in B'\) put

\[
\Theta_b=\pi_G\circ\Gamma_{b*}:H^1(\Lambda_b)\longrightarrow V_b=H^3(T_b)^G .
\]

Then either \(\Theta_b=0\) for every \(b\), or the following hold for every \(b\).

1. The map \(\Theta_b\) is surjective.
2. It maps \(F^1H^1(\Lambda_b)\) onto \(F^2V_b\), and \(V_b=F^2V_b\oplus\overline{F^2V_b}\).
3. The cup product of \(H^1(\Lambda_b)\) is nondegenerate on \(\ker\Theta_b\), and \(\Theta_b\circ{}^t\Theta_b\) is invertible on \(V_b\), where \({}^t\Theta_b=\Gamma_b^*\circ\pi_G\).

**Proof.** The class of \(\Gamma\) in the relative de Rham cohomology of the fiber product is horizontal for the Gauss–Manin connection, and pullbacks, cup products and proper pushforwards are horizontal. So \(\Theta\) is a horizontal map between bundles with integrable connections. Its rank is constant, and its image \(\mathcal U\) is a subbundle of the pullback of \(V\) that is stable under the connection. A correspondence of this dimension raises the Hodge filtration by one, so \(\Theta_b\) maps \(F^1=F^1H^1(\Lambda_b)\) into \(F^2V_b\). By the first property of conjugation, \(\Theta_b(\bar x)=\pm\overline{\Theta_b(x)}\), with a sign that does not depend on \(x\).

Fix \(b\), and put \(U=\mathcal U_b\), \(a=\dim(U\cap F^2V_b)\) and \(a'=\dim U-a\). Since \(H^1(\Lambda_b)=F^1\oplus\overline{F^1}\),

\[
U=\Theta_b(F^1)+\overline{\Theta_b(F^1)},
\qquad
\dim U\le2\dim\Theta_b(F^1)\le2a .
\]

Hence \(a'\le a\).

Now let \(b\) be a point at which \(\phi\) is submersive, the Higgs maps grow strictly at \(\phi(b)\), and \(\mathcal U\cap F^2\) has locally constant rank. Such points exist, because \(\phi\) is dominant and strict growth is an open condition. Let \(W=U\cap F^2V_b\), a subspace of \(V^{2,1}\), and let \(W'\) be the image of \(U\) in \(V^{1,2}\). Their dimensions are \(a\) and \(a'\). A vector of \(W\) extends to a local section of \(\mathcal U\cap F^2\), and the derivatives of that section are sections of \(\mathcal U\). Hence \(\overline\nabla_vW\subset W'\) for every \(v\) tangent to \(B'\) at \(b\), and these \(v\) map onto the tangent space of \(\mathcal B\). If \(0<a<N\), strict growth gives \(a'>a\), a contradiction. If \(a=0\), then \(a'=0\) and \(U=0\). If \(a=N\), then \(W'\) contains every \(\overline\nabla_vV^{2,1}\), so \(W'=V^{1,2}\) and \(U=V_b\). Since the rank of \(\Theta\) is constant, \(\Theta_b\) is zero for every \(b\) or surjective for every \(b\).

Suppose that \(\Theta_b\) is surjective. Then \(V_b=\Theta_b(F^1)+\overline{\Theta_b(F^1)}\), where \(\Theta_b(F^1)\) lies in \(F^2V_b\), of dimension \(N\), and \(\dim V_b=2N\). So \(\Theta_b(F^1)=F^2V_b\) and the sum is direct. This is the second statement.

Let \(K=\ker\Theta_b\). It is stable under conjugation. Let \(x=x'+\bar y'\in K\) with \(x',y'\in F^1\). Then \(\Theta_b(x')=\mp\overline{\Theta_b(y')}\) lies in \(F^2V_b\cap\overline{F^2V_b}=0\), so \(x'\) and \(y'\) lie in \(K\). Suppose in addition that \(x\) is orthogonal to \(K\). Then

\[
0=\operatorname{tr}(x\cup\bar x')=\operatorname{tr}(x'\cup\bar x')+\operatorname{tr}(\bar y'\cup\bar x'),
\]

and the last term is \(\pm\overline{\operatorname{tr}(y'\cup x')}=0\), because \(F^1\) is isotropic. By the second property of conjugation, \(x'=0\). Pairing with \(y'\) gives \(y'=0\) in the same way. So the cup product is nondegenerate on \(K\). The trace pairing of \(H^3(T_b)\) is \(G\)-invariant, hence nondegenerate on \(V_b\), and for these pairings \({}^t\Theta_b\) is the adjoint of \(\Theta_b\) up to a sign. So \({}^t\Theta_b\) is injective, and its image is the orthogonal complement of \(K\), which meets \(K\) in zero. Hence \(\Theta_b\circ{}^t\Theta_b\) is injective on \(V_b\). ∎

The sector alternative of Chapter 4 applies to every real sub-variation and takes the Hodge decomposition of the sector as known. Here the sub-variation is the image of the first cohomology of curves, and the decomposition of \(V_b\) is a conclusion.

**The integration lemma in coherent cohomology.** In the setting of §3D.1, let \(\rho_L\in H^1(D,T_D)\) be the Kodaira–Spencer class of \(V(F,\ h+\varepsilon L)\). Up to a fixed factor,

\[
\operatorname{NL}_\lambda(L)(\sigma)=\operatorname{tr}_D\bigl(\rho_L\cup c_1(\lambda)\cup\sigma\bigr),
\qquad c_1(\lambda)\in H^1(D,\Omega^1_D),
\]

and \(\rho_L\cup c_1(\lambda)\in H^2(D,\mathcal O_D)\) is the obstruction to extending a line bundle of class \(\lambda\) to \(V(F,\ h+\varepsilon L)\). It vanishes for the class \(H\) of \(\mathcal O_D(1)\), which extends.

Let \(\Sigma\subset D\) be a curve of class \(\lambda+mH\), with \(\lambda\) invariant under \(G\) and \(H^1(D,\mathcal O_D(\Sigma))=0\). Let \(\mathcal P\) be the space of pairs \((F',h')\) of invariant polynomials, with \(F'\in\mathcal B\), that define smooth surfaces \(D'\), and let \(\mathcal H\to\mathcal P\) be the relative Hilbert scheme of curves in these surfaces. Suppose that \(\operatorname{NL}_\lambda\) is surjective. Then \(\mathcal H\) is smooth at \([\Sigma]\), and so is the morphism \(\mathcal H\to\mathcal B\). The tangent vectors to its fiber at \([\Sigma]\) lie over \(\ker\operatorname{NL}_\lambda\), and every element of this kernel lies under one.

**Proof.** Let \(\mathcal M=\mathcal O_D(\Sigma)\), and let \(R\) be the complete local ring of \(\mathcal P\) at \((F,h)\), with maximal ideal \(\mathfrak m\). For a local Artinian quotient \(A\) of \(R\), let \(D_A\) be the corresponding surface over \(A\). Since \(H^1(D,\mathcal O_D)=0\), a line bundle on \(D_A\) that restricts to \(\mathcal M\) is unique up to isomorphism, and the relative Picard scheme is unramified over \(\mathcal P\) at \(\mathcal M\). Its completion there is \(R/J\) for an ideal \(J\): the line bundle \(\mathcal M\) extends to \(D_A\) exactly when \(J\) maps to zero in \(A\).

A curve \(\Sigma_A\subset D_A\) extending \(\Sigma\) gives the extension \(\mathcal O(\Sigma_A)\) of \(\mathcal M\). Conversely, let \(A'\to A\) be a small extension and suppose that \(\mathcal O(\Sigma_A)\) extends to \(D_{A'}\). Since \(H^1(D,\mathcal M)=0\), the section that cuts \(\Sigma_A\) lifts, and a lift cuts a curve in \(D_{A'}\) extending \(\Sigma_A\). So the completion of \(\mathcal H\) at \([\Sigma]\) is formally smooth over \(R/J\), of relative dimension \(h^0(\mathcal M)-1\).

For a small extension \(A'\to A\) with kernel \(I\), the obstruction to extending a line bundle from \(D_A\) to \(D_{A'}\) lies in \(H^2(D,\mathcal O_D)\otimes I\). The group \(G\) acts on \(D_A\) and on \(D_{A'}\), because the equations are invariant. An extension of \(\mathcal M\) to \(D_A\) is isomorphic to its pullbacks under \(G\), by uniqueness and the invariance of the class. The obstruction is functorial, so it is \(G\)-invariant. The space \(H^2(D,\mathcal O_D)^G\) is dual to \(H^0(D,K_D)^G\) and has dimension \(c\).

It follows that \(J\) is generated by at most \(c\) elements. Indeed, by the Artin–Rees lemma the extension \(R/(\mathfrak mJ+\mathfrak m^k)\to R/(J+\mathfrak m^k)\) has kernel \(J/\mathfrak mJ\) for large \(k\), and its obstruction is a linear map from the dual of \(H^2(D,\mathcal O_D)^G\) to \(J/\mathfrak mJ\). Let \(J'\supset\mathfrak mJ\) be an ideal with \(J'/\mathfrak mJ\) the image. The obstruction for \(R/(J'+\mathfrak m^k)\to R/(J+\mathfrak m^k)\) is then zero, so \(\mathcal M\) extends over \(R/(J'+\mathfrak m^k)\) and \(J\subset J'+\mathfrak m^k\). This holds for all large \(k\), so \(J=J'\).

On first-order deformations the obstruction is \(\rho\cup c_1(\mathcal M)\), with \(\rho\) the Kodaira–Spencer class, and on the directions \(L\in S_e^G\) it is \(\operatorname{NL}_\lambda\). By hypothesis these directions already map onto \(H^2(D,\mathcal O_D)^G\). So the tangent space of \(R/J\) has codimension \(c\) in that of \(\mathcal P\), and it maps onto the tangent space of \(\mathcal B\). Hence \(R/J\) is regular, of codimension \(c\), and smooth over \(\mathcal B\). Its tangent vectors over a fixed \(F\) are the elements of \(\ker\operatorname{NL}_\lambda\). ∎

No class of type \((1,1)\) is transported here: the line bundle is extended, and the count \(n-c\) of §3D.1 is the dimension of \(R/J\) over \(\mathcal B\), modulo rescaling of \(h\).

**The trace formulas in coherent cohomology.** With \(\operatorname{NL}\) read as above, the first display in the proof of the obstruction lemma is, up to signs, the identity

\[
\operatorname{tr}_D\bigl(\rho\cup c_1(\mathcal O_D(C))\cup\omega\bigr)
=\operatorname{tr}_D\bigl((\rho\mathbin{\lrcorner}\omega)\cup c_1(\mathcal O_D(C))\bigr)
=\operatorname{tr}_C\bigl((\rho\mathbin{\lrcorner}\omega)|_C\bigr).
\]

The first equality holds because \((\xi\mathbin{\lrcorner}\omega)\wedge\alpha=-\alpha(\xi)\,\omega\) for a vector \(\xi\), a one-form \(\alpha\) and a two-form \(\omega\) on a surface. The second is the Gysin property of the class of \(C\). The rest of that proof is a Čech computation.

In the derivative lemma, read \(\langle d\nu(L),\eta\rangle\) as the number

\[
\operatorname{tr}_\Sigma\bigl((v\mathbin{\lrcorner}\eta)|_\Sigma\bigr),
\]

for a smooth curve \(\Sigma\subset D\) of class \(\lambda+mH\) and a normal field \(v\in H^0(N_{\Sigma/T})\) over \(L|_\Sigma\). Here \(\eta\) acts through its image in \(H^1(T,\Omega^2_T)\). By the lemma above, such a field exists when \(L\in\ker\operatorname{NL}_\lambda\) and \(H^1(D,\mathcal O_D(\Sigma))=0\). The proof of the derivative lemma computes this number in coherent cohomology. It shows that the number is \(\operatorname{tr}_D(L\,\widetilde\eta\cup c_1(\mathcal O_D(\Sigma)))\), for any lift \(\widetilde\eta\), and so depends only on the class of \(\Sigma\). It uses the Abel–Jacobi map at one further place, to discard the part \(mH\). That part is the same number for a complete-intersection curve \(D\cap\{\ell=0\}\), with \(\ell\) of degree \(m\). By the next lemma, it is a value of a one-form on a smooth projective completion of the space of pairs \((h',\ell')\). That space is rational, so the form is zero.

**Fiber integration.** Let \(T\) be a smooth projective threefold and \(S\) a smooth variety. Let \(\mathcal Z\subset S\times T\) be a family of curves, smooth and proper over \(S\), with projections \(p\) and \(q\). Let \(\bar S\) be a smooth projective completion of \(S\), and let \(\Gamma\) be the closure of \(\mathcal Z\) in \(\bar S\times T\). For \(\eta\in F^2H^3(T)\), the class \(\Gamma^*\eta\in F^1H^1(\bar S)\) is a one-form on \(\bar S\). Up to a fixed sign, its value on a tangent vector \(\xi\) at \(s\in S\) is

\[
\operatorname{tr}_{Z_s}\bigl((v_\xi\mathbin{\lrcorner}\eta)|_{Z_s}\bigr),
\]

where \(Z_s\) is the fiber and \(v_\xi\in H^0(N_{Z_s/T})\) is the normal field of \(\xi\).

**Proof.** Resolve \(\Gamma\) by a morphism that is an isomorphism over \(\mathcal Z\), and extend \(p\) and \(q\) to the resolution. Then \(\Gamma^*=p_*q^*\). Proper pushforward commutes with restriction to \(S\). Along the smooth morphism \(p\), of relative dimension one, it is induced on Hodge cohomology by the quotient map \(\Omega^2_{\mathcal Z}\to p^*\Omega^1_S\otimes\Omega^1_{\mathcal Z/S}\) and the relative trace \(R^1p_*\Omega^1_{\mathcal Z/S}\to\mathcal O_S\). Evaluating at \(\xi\) contracts with a lift \(\widetilde\xi\) of \(\xi\) along \(Z_s\) and restricts to \(Z_s\). Finally \(\widetilde\xi\mathbin{\lrcorner}q^*\eta=q^*(dq(\widetilde\xi)\mathbin{\lrcorner}\eta)\), and \(dq(\widetilde\xi)\) lifts \(v_\xi\). ∎

**The moving-class criterion from weight one.** Let \(\mathcal B\) be as in the moving-class criterion, and smooth. Suppose that its first hypothesis holds and that the Higgs maps of \(\mathcal B\) grow strictly at one member. Then for \(T\) in a nonempty Zariski-open subset of \(\mathcal B\) there are a smooth projective curve \(\Lambda\) and a correspondence \(\Gamma\) such that \(\Theta=\pi_G\circ\Gamma_*\) has the three properties of the weight-one alternative. In particular

\[
\Gamma_*H^1(\Lambda,\mathbb Q)\supset H^3(T,\mathbb Q)^G ,
\]

and \(\Theta\circ{}^t\Theta\) is invertible on \(H^3(T)^G\).

**Proof.** Let \(m\) be large and let \(\Sigma\subset D\) be a smooth curve of class \(\lambda+mH\). Then \(H^1(D,\mathcal O_D(\Sigma))=0\). By the integration lemma in coherent cohomology, \(\mathcal H\) is smooth over \(\mathcal B\) at \([\Sigma]\), and \(L\) lies under a tangent vector \(\xi\) to its fiber. Choose a locally closed subvariety \(\mathcal C\subset\mathcal H\) through \([\Sigma]\) that is smooth over \(\mathcal B\) of relative dimension one there, with fiber tangent to \(\xi\). As in the proof of the moving-class criterion, pass to a finite étale cover \(B'\) of an open subset of \(\mathcal B\), and complete and normalize the parameter curves. The result is a smooth projective family of curves \(\Lambda\to B'\), with the closure \(\Gamma\) of the universal curve as a relative correspondence.

Let \(\mathcal C^\circ\subset\mathcal C\) be the open subset on which \(\mathcal C\) is smooth over \(\mathcal B\) and the universal curve is smooth over \(\mathcal C\). It contains \([\Sigma]\), and its fibers are open subsets of the curves \(\Lambda_b\). By the fiber integration lemma, the forms \(\Gamma_b^*\eta_A\) restrict on \(\mathcal C^\circ\) to an algebraic relative one-form over \(\mathcal B\). Its value on \(\xi\) at \([\Sigma]\) is the pairing of the derivative lemma, which is nonzero. The component of \(\mathcal C^\circ\) through \([\Sigma]\) dominates \(\mathcal B\), so the relative form is nonzero at its general point. For general \(b\) the form \(\Gamma_b^*\eta_A\) is therefore nonzero. Hence \({}^t\Theta_b\ne0\) and \(\Theta_b\ne0\), and the weight-one alternative applies. The inclusion of rational spaces follows from the surjectivity over \(\mathbb C\). ∎

**The order-three theorem.** In the proof of §3D.4, the first three finite results verify the first hypothesis, in the coherent reading of the two trace formulas. The second row of the table of §4.4 gives strict growth at \(F_0\), in place of the fourth finite result. The criterion above then supplies \(\mathcal U\), \(\Lambda\) and \(\Gamma\). After \(\Gamma\) is replaced by \(\pi_g\circ\Gamma\circ\pi_1^\Lambda\), the operator \(\Gamma\circ{}^t\Gamma\) is \(\Theta\circ{}^t\Theta\) on \(H^3(T)^g\), and it is invertible there by the third property. No polarization of \(H^3(T)\) enters. The remaining steps are algebraic. The Hodge numbers of the eigenspaces come from the residue theorems of §3D.1, and the even cohomology of \(T\) from weak Lefschetz, which has an algebraic proof. The specialization lemma uses relative Hilbert schemes and the horizontality of the classes of flat families of cycles.

**Scope.** With the changes of §3D.6, the same proofs apply to the part of \(H^3(T)\) on which \(G\) acts through a character \(\chi\ne\delta\) with values \(\pm1\), with the projector of \(\chi\) in place of \(\pi_G\). They do not cover the sector of §3D.6. That sector is the sum of two eigenspaces exchanged by conjugation, and in each of them the pieces \(V^{2,1}\) and \(V^{1,2}\) have different dimensions, so the strict-growth lemma does not apply. On a fourfold, the classes supported on a divisor are images of the second cohomology of threefolds, and the argument would need the decomposition of that cohomology in place of the one for curves.

## 3D.8 Split quadric sections and a paired-exchange fourfold family

The Hodge-locus method also acts directly on a family of sextic fourfolds in \(\mathbb P^5\), without passing through a pencil of threefolds. The role of the ambient Fano fourfold in the remark of §3D.4 is played by a second smooth sextic fourfold in the same symmetry family, whose reflection quotient makes its invariant Hodge classes algebraic. The role of the threefold is played by a common quadric section of the two fourfolds, which has six nodes and moves in a pencil.

Let \(H\subset\operatorname{GL}_6(\mathbb Z)\) be the finite group of order \(64\) generated by \(\tau:(X,Y)\mapsto(X,-Y)\), the three paired signs \(s_i:(X_i,Y_i)\mapsto(-X_i,-Y_i)\) for \(i=0,1,2\), and the two coordinate exchanges \(\sigma_0:X_0\leftrightarrow Y_0\) and \(\sigma_1:X_1\leftrightarrow Y_1\). The subgroup \(P=\langle s_0,s_1,s_2\rangle\) is central in \(H\) and contains \(-I_6=s_0s_1s_2\), while \(\sigma_i\tau\sigma_i\tau=s_i\) for \(i=0,1\). Thus \(H/P\simeq(\mathbb Z/2)^3\) is abelian. The invariant sextics \(S_6^H\) form a \(40\)-coefficient linear system. Let \(\mathcal B_H\subset\mathbb P(S_6^H)\) be its smooth locus and \(\widetilde{\mathcal B}_H\subset S_6^H\) the affine cone over \(\mathcal B_H\). For a character \(\psi:H\to\{\pm1\}\), the superscript \([\psi]\) denotes the part on which \(H\) acts through \(\psi\).

Let \(\chi:H\to\{\pm1\}\) be the character that is \(+1\) on \(\tau,s_0,s_1,s_2\) and \(-1\) on \(\sigma_0,\sigma_1\), and let

\[
e_\chi=\frac1{|H|}\sum_{g\in H}\chi(g)\,g\in\mathbb Q[H]
\]

be its projector.

**Paired-exchange support theorem.** Let \(X=(F=0)\subset\mathbb P^5\) be a smooth \(H\)-invariant sextic fourfold. Then

\[
H^4(X,\mathbb Q)^\tau\subseteq N^1H^4(X,\mathbb Q).
\]

More precisely, \(e_\chi\) acts on \(H^*(X,\mathbb Q)\) as the projector onto \(H^4(X,\mathbb Q)[\chi]\), zero in the other degrees and on the complementary sectors, and its class is that of a rational algebraic cycle supported on \(D\times D\) for some \(H\)-stable divisor \(D\subset X\).

**Decomposition of the invariant cohomology.** Since \(P\) is normal in \(H\) and commutes with \(\tau\), the primitive invariant cohomology \(H^4(X,\mathbb Q)^\tau_{\mathrm{prim}}\), of Hodge type \((208,866,208)\), splits into \((1-\pi_P)H^4(X,\mathbb Q)^\tau_{\mathrm{prim}}\) and the \(P\)-invariant part, of type \((58,230,58)\). On the latter, \(\sigma_0\) and \(\sigma_1\) commute with each other and with \(\tau\), giving four joint eigenspaces. In the coordinates \(X_i+Y_i\) and \(X_i-Y_i\), the exchange \(\sigma_i\) is the reflection of \(X_i-Y_i\), so the [reflection theorem of §3.3](03-geometric-support.md#33-reflection-quotients) supports both \(H^4(X,\mathbb Q)^{\sigma_0}\) and \(H^4(X,\mathbb Q)^{\sigma_1}\). The Hodge numbers are computed at the Fermat member \(F_0=\sum_{i=0}^2(X_i^6+Y_i^6)\). Its Jacobian ring has the basis of reduced monomials, which \(H\) permutes up to sign, and the numbers are the multiplicities of the characters:

| Sector in \(H^4(X,\mathbb Q)^\tau_{\mathrm{prim}}\) | Hodge numbers | Support |
| --- | --- | --- |
| Nontrivial on \(P=\langle s_0,s_1,s_2\rangle\) | \((150,636,150)\) | [Paired signs, §3B.9](03b-weighted-threefolds.md#3b9-paired-signs) |
| Trivial on \(P\), fixed by \(\sigma_0\) or \(\sigma_1\) | \((25,128,25)\) | [Reflection theorem, §3.3](03-geometric-support.md#33-reflection-quotients) |
| Trivial on \(P\), anti-invariant under \(\sigma_0\) and \(\sigma_1\): \(H^4(X)[\chi]\) | \((33,102,33)\) | Proved below |

The middle row consists of the \(H\)-invariant part \(H^4(X)_{\mathrm{prim}}^H\), of type \((3,26,3)\), and the two mixed sectors, each of type \((11,51,11)\). Because \(\chi(\sigma_0)=-1\) and \(\sigma_0\) fixes the hyperplane class \(h\), the projector \(e_\chi\) annihilates \(h^2\) and every \(H^{2k}(X)\) with \(k\ne2\).

Let \(\det\) be the determinant character of \(H\): it is \(-1\) on \(\tau,\sigma_0,\sigma_1\) and \(+1\) on the \(s_i\). An element \(g\in H\) multiplies the form \(\Omega\) by \(\det(g)\), so the residue of a form with numerator in \(S^{[\psi]}\) lies in the sector of character \(\psi\det\). Residues in \(H^4(X)^H_{\mathrm{prim}}\) therefore have numerators in \(R(F)^{[\det]}\): odd in \(Y\), even in each pair, and odd under both exchanges. Residues in \(H^4(X)[\chi]\) have numerators in \(R(F)^{[\chi\det]}\): odd in \(Y\), even in each pair, and even under both exchanges. The Hessian determinant of \(F\) spans the socle \(R(F)_{24}\), and \(g\in H\) multiplies it by \(\det(g)^{-2}=1\). So \(H\) acts trivially on \(R(F)_{24}\), and the functional \(\operatorname{soc}_{R(F)}\) vanishes on \(R(F)_{24-k}^{[\psi]}\cdot R(F)_k^{[\psi']}\) unless \(\psi=\psi'\).

**Weight-four Higgs lemma.** Let \(\mathbb V\) be a polarized rational variation of Hodge structure of weight four with \(V^{4,0}=0\) over a smooth connected base \(B\). For tangent vectors \(u,v\) at \(b\in B\), the composite \(\overline\nabla_v\circ\overline\nabla_u:V^{3,1}_b\to V^{1,3}_b\simeq(V^{3,1}_b)^\vee\) is a symmetric bilinear form \(\theta_{u,v}\) on \(V^{3,1}_b\). Suppose that at one point \(b\in B\):

1. the images \(\overline\nabla_uV^{3,1}_b\) span \(V^{2,2}_b\), and the maps \(\overline\nabla_u:V^{2,2}_b\to V^{1,3}_b\) have zero common kernel;
2. the only endomorphisms \(\Xi\) of \(V^{3,1}_b\) with \(\Xi^{\mathsf T}\theta_{u,v}=\theta_{u,v}\,\Xi\) for all \(u,v\) are the scalars.

Then over every smooth connected variety with a dominant morphism to \(B\), the pullback of \(\mathbb V\) has no rational sub-variation other than zero and itself.

**Proof.** Each condition fails only on a proper closed analytic subset of \(B\). Let \(\phi:B'\to B\) be dominant, from a smooth connected variety, and choose \(b'\in B'\) at which \(\phi\) is submersive and both conditions hold at \(\phi(b')\). Let \(\mathbb U\subset\phi^*\mathbb V\) be a rational sub-variation. As in the Higgs lemma of §3D.3, the projector \(\Pi\) onto \(\mathbb U\) along its orthogonal complement for the polarization is flat, self-adjoint and of type \((0,0)\). Flatness makes \(\Pi\) commute with every \(\overline\nabla_u\), hence with every composite \(\overline\nabla_v\circ\overline\nabla_u\). Self-adjointness makes its action on \(V^{1,3}\) the transpose of its action \(\Xi\) on \(V^{3,1}\). Thus \(\Xi^{\mathsf T}\theta_{u,v}=\theta_{u,v}\,\Xi\) at \(\phi(b')\), in all directions, and \(\Xi\) is a scalar idempotent: zero or the identity. The rest is as in the [sector alternative of Chapter 4, §4.4](04-known-locus-and-frontier.md#strict-growth-and-sectors). If \(\Xi\) is the identity, then \(U^{3,1}=V^{3,1}\), by conjugation \(U^{1,3}=V^{1,3}\), and \(U^{2,2}\) contains every \(\overline\nabla_uV^{3,1}\), so it is \(V^{2,2}\). If \(\Xi=0\), then \(U^{3,1}=0\) and \(U^{1,3}=0\), so every \(\overline\nabla_u\) kills \(U^{2,2}\), which is therefore zero. The ranks of the Hodge pieces of \(\mathbb U\) are constant on \(B'\). ∎

For \(\mathbb V=H^4(\mathcal X/\mathcal B_H,\mathbb Q)[\chi]\) the Higgs maps at \(F\) are the multiplications by the \(g\in R(F)_6^H\), and \(\theta_{g,h}(a,b)\) is a fixed nonzero multiple of \(\operatorname{soc}_{R(F)}(ghab)\) on \(R(F)_6^{[\chi\det]}\). By Macaulay duality, an element of \(R(F)_{12}^{[\chi\det]}\) killed by every \(g\) is orthogonal to \(R(F)_6^H\cdot R(F)_6^{[\chi\det]}\). Both parts of the first condition therefore hold when the multiplication \(R(F)_6^H\otimes R(F)_6^{[\chi\det]}\to R(F)_{12}^{[\chi\det]}\) is surjective.

**Split quadrics and the second fourfold.** Put

\[
\delta_0=X_0^2-Y_0^2,\qquad \delta_1=X_1^2-Y_1^2,\qquad q_s=\delta_0+s\,\delta_1\quad(s\in\mathbb G_m).
\]

The exchange \(\sigma_i\) negates \(\delta_i\) and fixes the other one, and \(\tau\) and the paired signs fix both. So \(\sigma_0\) carries \(q_s\) to \(-q_{-s}\) and \(\sigma_1\) carries it to \(q_{-s}\), and the quartic \(q_sq_{-s}=\delta_0^2-s^2\delta_1^2\) is \(H\)-invariant. The invariant quadrics are \(S_2^H=\langle X_0^2+Y_0^2,\,X_1^2+Y_1^2,\,X_2^2,\,Y_2^2\rangle\). Let \(\mathcal K=S_2^H\times\mathbb G_m\), of dimension five, and for \(F\in\widetilde{\mathcal B}_H\) and \((R,s)\in\mathcal K\) put

\[
F'=F-R\,q_sq_{-s}.
\]

Let \(\mathcal I\) be the set of triples \((F,R,s)\) with \(F'\in\widetilde{\mathcal B}_H\). The two maps \(\pi_1:(F,R,s)\mapsto F\) and \(\pi_2:(F,R,s)\mapsto F'\) each identify \(\mathcal I\) with an open subset of \(\widetilde{\mathcal B}_H\times\mathcal K\), because \(F=F'+R\,q_sq_{-s}\). Both are smooth, with fibers open in \(\mathcal K\).

Write \(X=V(F)\), \(X'=V(F')\), \(Q_s=V(q_s)\) and \(Y_s=X\cap Q_s\). Since \(F'\equiv F\) modulo \(q_s\), also \(Y_s=X'\cap Q_s\). Let \(\operatorname{Sing}(Y_s)\) be the set of points of \(Y_s\) at which \(dF\) and \(dq_s\) are proportional.

For every smooth \(X'\) with \(H\)-invariant equation, the quotient \(X'/\langle\sigma_0\rangle\) is a smooth Fano fourfold, by the proof of the [reflection theorem of §3.3](03-geometric-support.md#33-reflection-quotients). By the [corollary of §3.2](03-geometric-support.md#degree-four-hodge-classes) its rational Hodge classes of degree four are algebraic. Pulling back, every class in \(H^{2,2}(X',\mathbb Q)^{\sigma_0}\) is algebraic, and in particular every class in \(H^{2,2}(X',\mathbb Q)^H\).

**The six nodes and their resolution.** Let \(L=\{X_0=Y_0=X_1=Y_1=0\}\). Every monomial of \(F\in S_6^H\) has even degree in each pair, so the four partial derivatives of \(F\) in the directions normal to \(L\) vanish on \(L\). If \(X\) is smooth, the binary sextic \(F|_L\) is therefore nonzero and squarefree. It cuts six points \(\Sigma=\{p_1,\ldots,p_6\}=X\cap L\), at which \(X\) is transverse to \(L\). The quartic \(q_sq_{-s}\) vanishes to order four along \(L\), so \(F'|_L=F|_L\), and \(X'\) passes through \(\Sigma\) with the same tangent hyperplanes as \(X\).

The quadric \(Q_s\) has rank four. It is the cone with vertex \(L\) over the smooth quadric surface \(\overline Q_s=\{\delta_0+s\,\delta_1=0\}\subset\mathbb P^3\). Near \(p_j\) it is the product of \(L\) and a three-dimensional quadratic cone, and \(X\) is the graph of a function on the second factor. So each \(p_j\) is an ordinary double point of \(Y_s\), and \(\Sigma\subset\operatorname{Sing}(Y_s)\).

Let \(\rho:\widehat P\to\mathbb P^5\) be the blow-up of \(L\), with exceptional divisor \(E\simeq L\times\mathbb P^3\). Projection from \(L\) is a morphism \(\widehat P\to\mathbb P^3\), a \(\mathbb P^2\)-bundle. Let \(\widehat Q_s\) be the preimage of \(\overline Q_s\). It is a smooth \(\mathbb P^2\)-bundle over \(\overline Q_s\) and the strict transform of \(Q_s\), and \(\rho^*q_s\) vanishes to order two along \(E\). The strict transforms \(\widetilde X\) and \(\widetilde X'\) are the blow-ups of \(X\) and \(X'\) at \(\Sigma\). They are the full preimages \(\rho^{-1}(X)\) and \(\rho^{-1}(X')\) as divisors, because neither fourfold contains \(L\). Put

\[
\widetilde Y_s=\widetilde X\cap\widehat Q_s=\widetilde X'\cap\widehat Q_s .
\]

It contains the six quadric surfaces \(D_j=\{p_j\}\times\overline Q_s\), and \(\widetilde Y_s\setminus\bigcup_jD_j\simeq Y_s\setminus\Sigma\).

**Nodal resolution lemma.** Let \(X\) and \(X'\) be smooth, and suppose \(\operatorname{Sing}(Y_s)=\Sigma\). Then \(\widetilde X\) and \(\widehat Q_s\) are transverse, and \(\widetilde Y_s\) is a smooth projective threefold, the blow-up of \(Y_s\) at its six nodes. Every class in \(H^4(X',\mathbb C)_{\mathrm{prim}}\) pulls back to zero on \(\widetilde Y_s\).

**Proof.** Away from \(E\), transversality is the hypothesis. Near \(D_j\), take coordinates \((x_0,\ldots,x_3,t)\) with \(L=\{x=0\}\) and \(X=\{t=0\}\), in which \(q_s\) is a nondegenerate quadratic form in \(x\). In a chart \(x=e\,u\) of the blow-up, \(\widetilde X=\{t=0\}\) and \(\widehat Q_s=\{q_s(u)=0\}\). They are transverse, and their intersection is smooth, with exceptional divisor \(\overline Q_s\).

By the [residue theorem of Chapter 1](01-certificates.md#residues-of-forms-with-higher-poles), a primitive class on \(X'\) is the residue of a five-form on \(\mathbb P^5\) with poles along \(X'\). The preimage of \(X'\) in \(\widehat Q_s\) is the smooth divisor \(\widetilde Y_s\), with multiplicity one, so the pullback of the class is the residue of the pullback of the form. That pullback is a five-form on a fourfold. ∎

In particular the class of an algebraic cycle of primitive class on \(X'\) pulls back to zero on \(\widetilde Y_s\): the one-cycles that it cuts there are homologous to zero.

**Fermat nodality.** At the Fermat member \(F_0\) and \(s=2\), one has \(\operatorname{Sing}(Y_2)=\Sigma\). Indeed, consider a point outside \(L\) at which \(dF_0=c\,dq_2\). There \(c\ne0\), so \(X_2=Y_2=0\), and after rescaling the coordinates \(c=3\) and

\[
X_0^5=X_0,\qquad Y_0^5=-Y_0,\qquad X_1^5=2X_1,\qquad Y_1^5=-2Y_1 .
\]

Hence \(X_0^2=a_0\), \(Y_0^2=i\,a_1\), \(X_1^2=\sqrt2\,b_0\) and \(Y_1^2=i\sqrt2\,b_1\) with \(a_0,a_1,b_0,b_1\in\{0,\pm1\}\), and the equation \(q_2=0\) reads \((a_0-i\,a_1)+2\sqrt2\,(b_0-i\,b_1)=0\). Taking squared absolute values gives \(a_0^2+a_1^2=8(b_0^2+b_1^2)\). The left side is at most two, so both sides vanish and the point lies on \(L\), a contradiction.

**Residues in a family.** The two-form formula below rests on one general statement. Let \(\pi:N\to\Delta\) be a smooth morphism of complex manifolds onto a polydisc of dimension two, with fibers \(N_z\) of dimension four, and let \(\mathcal Y\subset N\) be a smooth divisor, proper and smooth over \(\Delta\), with fibers \(Y_z\). On \(\mathcal Y\), let \(\mathcal L^i\Omega^k_{\mathcal Y}\) be the Koszul filtration: the image of \(\pi^*\Omega^i_\Delta\otimes\Omega^{k-i}_{\mathcal Y}\), so that \(\mathcal L^1\Omega^k_{\mathcal Y}/\mathcal L^2\Omega^k_{\mathcal Y}=\pi^*\Omega^1_\Delta\otimes\Omega^{k-1}_{\mathcal Y/\Delta}\).

Let \(\varpi\) be a closed meromorphic five-form on \(N\), regular outside \(\mathcal Y\), with a pole of order at most \(m+1\) along \(\mathcal Y\), where \(m\) is \(1\) or \(2\). The [pole-order lemma of Chapter 1](01-certificates.md#residues-of-forms-with-higher-poles) and its proof are local, and hold for a smooth divisor in any complex manifold. By that lemma \(\varpi\), a cocycle of degree five of the pole-order complex \(P^{5-m}\Omega^\bullet_N(*\mathcal Y)\), has a residue in \(\mathbb H^4(\mathcal Y,\sigma_{\ge4-m}\Omega^\bullet_{\mathcal Y})\), with a leading component \([\varpi]_{\mathcal Y}\in H^m(\mathcal Y,\Omega^{4-m}_{\mathcal Y})\). For a vector field \(v\) on \(\Delta\) and a lift \(\widetilde v\) of \(v\) to \(N\), the form \((\widetilde v\mathbin{\lrcorner}\varpi)|_{N_z}\) is a meromorphic four-form on \(N_z\) with a pole of order at most \(m+1\) along \(Y_z\). It does not depend on the lift, because a five-form vanishes on the four-dimensional \(N_z\).

**Lemma.** The class \([\varpi]_{\mathcal Y}\) is the image of a class in \(H^m(\mathcal Y,\mathcal L^1\Omega^{4-m}_{\mathcal Y})\) whose image in

\[
H^m\bigl(\mathcal Y,\pi^*\Omega^1_\Delta\otimes\Omega^{3-m}_{\mathcal Y/\Delta}\bigr)
=H^0\bigl(\Delta,\Omega^1_\Delta\otimes R^m\pi_*\Omega^{3-m}_{\mathcal Y/\Delta}\bigr)
\]

has the following value on \(v\) at \(z\), up to a sign that depends on nothing: the component in \(H^m(Y_z,\Omega^{3-m}_{Y_z})\) of the residue of \((\widetilde v\mathbin{\lrcorner}\varpi)|_{N_z}\) along \(Y_z\).

**Proof.** The Koszul filtration is also defined on \(\Omega^\bullet_N(\log\mathcal Y)\) and on the pole-order complexes of Chapter 1. Its graded pieces are the corresponding complexes of relative forms, tensored with \(\pi^*\Omega^i_\Delta\) and shifted by \(i\). The proof of the pole-order lemma applies to the relative complexes, so the inclusion of the logarithmic complexes into the pole-order complexes is a quasi-isomorphism on each graded piece, and the residue \(\Omega^\bullet_N(\log\mathcal Y)\to\Omega^{\bullet-1}_{\mathcal Y}\) preserves the filtration. The form \(\varpi\) lies in \(\mathcal L^1\), because \(N_z\) has dimension four. Its image in the first graded piece is \(\sum_adt_a\otimes(\widetilde\partial_a\mathbin{\lrcorner}\varpi)\), read as a relative four-form. Taking residues gives the statement. ∎

**Two-form formula.** Fix \(F\in\widetilde{\mathcal B}_H\) and \(X=V(F)\). Let \(\mathcal K^\circ\subset\mathcal K\) be the open set of the \((R,s)\) for which \(X'\) is smooth and \(\operatorname{Sing}(Y_s)=\Sigma\). Let \(Z\) be a smooth algebraic surface with an unramified morphism \(z\mapsto(R_z,s_z)\) to \(\mathcal K^\circ\), and let \(\mathcal W\) be a cycle with rational coefficients on the family \(\mathcal X'_Z\) of the fourfolds \(X'_z\), whose components are flat over \(Z\) with fibers of dimension two. Suppose that the classes \(\gamma_z\in H^4(X'_z,\mathbb Q)\) of its fibers are primitive. The threefolds \(Y_{s_z}\) form a Cartier divisor \(\mathcal Y^\flat\) of \(\mathcal X'_Z\) that lies in \(Z\times X\). Let \(\Gamma\) be the intersection of \(\mathcal W\) with this divisor, a cycle class of dimension three on \(\mathcal Y^\flat\) ([Fulton, Intersection Theory, §2.3](https://doi.org/10.1007/978-1-4612-1700-8)), regarded on \(Z\times X\). Its fibers are classes of one-cycles on \(X\), and for \(\alpha\in H^{3,1}(X)=H^1(X,\Omega^3_X)\) the class \(\Gamma^*\alpha\) is a holomorphic two-form on \(Z\).

Fix \(z_0\in Z\), and write \(X'\), \(q\), \(q^-\) and \(\widetilde Y\) for \(X'_{z_0}\), \(q_s\), \(q_{-s}\) and \(\widetilde Y_s\) at \(s=s_{z_0}\). Let \(\gamma_{z_0}\) be the residue of \(G\,\Omega/(F')^3\) with \(G\in S_{12}\), and let \(\lambda\) be the class of \(G\) in \(R(F')_{12}\). Let \(\alpha\) be the \((3,1)\)-component of the residue of \(A\,\Omega/F^2\), with \(A\in S_6\). For tangent vectors \(v_1,v_2\) to \(Z\) at \(z_0\), with components \((\dot R_a,\dot s_a)\), put \(\kappa=\dot R_1\dot s_2-\dot R_2\dot s_1\in S_2^H\). Then

\[
(\Gamma^*\alpha)(v_1,v_2)=c_0\,\operatorname{soc}_{R(F')}\bigl(\lambda\,A\,\kappa\,\delta_1\,q^-\bigr),
\]

where \(c_0\ne0\) depends on none of the data. If \(\gamma_{z_0}\) is \(H\)-invariant and \(\alpha\) lies in \(H^{3,1}(X)[\chi]\), the right side is

\[
c_0\,\operatorname{soc}_{R(F')}\bigl(\lambda\,A\,\kappa\,\delta_0\delta_1\bigr).
\]

**Proof.** Let \(\pi:\mathcal Y\to Z\) be the family of the threefolds \(\widetilde Y_{s_z}\). It is proper and smooth, by the nodal resolution lemma, it resolves \(\mathcal Y^\flat\), and it maps to \(\mathcal X'_Z\) and to \(X\). Let \(\Phi\in H^2(\mathcal Y,\Omega^2_{\mathcal Y})\) be the pullback of the class of \(\mathcal W\), and \(\Psi\in H^1(\mathcal Y,\Omega^3_{\mathcal Y})\) the pullback of \(\alpha\).

*Fiber integration.* On \(\mathcal Y^\flat\), the class \(\Gamma\) is the cap product of its fundamental class with the restriction of the class of \(\mathcal W\). The resolution \(\mathcal Y\to\mathcal Y^\flat\) is birational, so by the projection formula \(\Gamma\) is the pushforward of the cap product of the fundamental class of \(\mathcal Y\) with the pullback of the class of \(\mathcal W\). The cycle class in Hodge cohomology is compatible with proper pushforward to \(Z\times X\). Hence \(\Gamma^*\alpha=\pi_*(\Phi\cup\Psi)\). As in the fiber integration lemma of §3D.7, the map \(\pi_*\) from \(H^3(\mathcal Y,\Omega^5_{\mathcal Y})\) to the two-forms on \(Z\) is induced by \(\Omega^5_{\mathcal Y}=\pi^*\Omega^2_Z\otimes\Omega^3_{\mathcal Y/Z}\) and the relative trace.

The rest of the proof is local on \(Z\). Let \(\Delta\subset Z\) be a polydisc around \(z_0\), with coordinates \((t_1,t_2)\) and \(\partial_a=v_a\) at \(z_0\), and restrict the families to it.

*The two classes as residues.* Let \(N\to\Delta\) be the family of the fourfolds \(\widehat Q_{s_z}\). It is smooth over \(\Delta\), it maps to \(\Delta\times\mathbb P^5\) through \(\rho\), and the preimages of \(\Delta\times X\) and of \(\mathcal X'_\Delta\) in it are both the smooth divisor \(\mathcal Y\), with multiplicity one. Residues commute with pullback along such a map.

The form \(A\,\Omega/F^2\) is closed on \(\mathbb P^5\setminus X\). So \(\Psi=[\varpi_\Psi]_{\mathcal Y}\), in the notation of the lemma on residues in a family, where \(\varpi_\Psi\) is the pullback of \(A\,\Omega/F^2\) to \(N\), with a pole of order two.

By the residue theorem of Chapter 1, \(\gamma_z\) is the residue of \(G_z\,\Omega/(F'_z)^3\) for polynomials \(G_z\in S_{12}\) that depend holomorphically on \(z\), with \(G_{z_0}=G\). The class \(\gamma_z\) is flat, and the residue of \(\partial_a(G_z\,\Omega/(F'_z)^3)\), a form with a pole of order four, is its derivative. So this residue is zero, and the class of the form in \(H^5(\mathbb P^5\setminus X'_z,\mathbb C)\) is zero. By the pole-order lemma and the degeneration of the logarithmic Hodge spectral sequence ([Deligne, Corollaire 3.2.13](https://www.numdam.org/item/PMIHES_1971__40__5_0/)), the class of the form in \(\mathbb H^5(\mathbb P^5,P^2\Omega^\bullet(*X'_z))\) is then zero. By Bott vanishing, as in the proof of the residue theorem, this group is computed by global sections. So the form is the differential of a global section of \(\Omega^4_{\mathbb P^5}(3X'_z)\). Such a section is \((\xi_a\mathbin{\lrcorner}\Omega)/(F'_z)^3\) for a vector field \(\xi_a\) with homogeneous polynomial coefficients of degree thirteen, which can be taken holomorphic in \(z\), and

\[
d\,\frac{\xi\mathbin{\lrcorner}\Omega}{(F')^3}=\frac{\bigl(F'\operatorname{div}\xi-3\,\xi(F')\bigr)\,\Omega}{(F')^4}.
\]

Comparing numerators shows that \(\xi_a(F'_z)-G_z\,\partial_aF'_z\) is a multiple of \(F'_z\). The Euler field \(\epsilon\) satisfies \(\epsilon(F')=6F'\) and \(\epsilon\mathbin{\lrcorner}\Omega=0\), so after adding a multiple of it to \(\xi_a\),

\[
\xi_a(F'_z)=G_z\,\partial_aF'_z,
\qquad
\partial_aF'_z=-\dot R_a\,q_sq_{-s}+2s\,\dot s_a\,R\,\delta_1^2 .
\qquad(1)
\]

Hence there is a closed meromorphic five-form on \(\Delta\times\mathbb P^5\), with a pole of order three along \(\mathcal X'_\Delta\),

\[
\varpi=\frac{G_z\,\Omega}{(F'_z)^3}+\sum_{a=1}^2dt_a\wedge\frac{\xi_a\mathbin{\lrcorner}\Omega}{(F'_z)^3}+dt_1\wedge dt_2\wedge c_z .
\]

Here \(c_z\) is a global section of \(\Omega^3_{\mathbb P^5}(3X'_z)\), holomorphic in \(z\). It exists by the argument just given: the form \(\partial_1(\xi_2\mathbin{\lrcorner}\Omega/(F'_z)^3)-\partial_2(\xi_1\mathbin{\lrcorner}\Omega/(F'_z)^3)\) is closed, with a pole of order four, so it is a cocycle of degree four of \(P^1\Omega^\bullet(*X'_z)\), and \(H^4(\mathbb P^5\setminus X'_z,\mathbb C)=0\). The residue of \(\varpi\) and the class of \(\mathcal W\) are two classes in \(\mathbb H^4(\mathcal X'_\Delta,\sigma_{\ge2}\Omega^\bullet)\) with the same image \(\gamma\) in \(H^4(\mathcal X'_\Delta,\mathbb C)=H^4(X',\mathbb C)\). They are equal, because the kernel of the map to \(H^4(\mathcal X'_\Delta,\mathbb C)\) is a quotient of \(\mathbb H^3(\mathcal X'_\Delta,\mathcal O\to\Omega^1)\), which vanishes: a smooth sextic fourfold has \(h^{0,2}=h^{0,3}=h^{1,2}=0\). Therefore \(\Phi=[\varpi_\Phi]_{\mathcal Y}\), where \(\varpi_\Phi\) is the pullback of \(\varpi\) to \(N\), with a pole of order three.

*The symbols.* By the lemma, \(\Phi\) and \(\Psi\) are the images of classes with coefficients in \(\mathcal L^1\Omega^2_{\mathcal Y}\) and \(\mathcal L^1\Omega^3_{\mathcal Y}\), with images

\[
\overline\Phi\in H^0\bigl(\Delta,\Omega^1_\Delta\otimes R^2\pi_*\Omega^1_{\mathcal Y/\Delta}\bigr),
\qquad
\overline\Psi\in H^0\bigl(\Delta,\Omega^1_\Delta\otimes R^1\pi_*\Omega^2_{\mathcal Y/\Delta}\bigr)
\]

given by residues of contractions. Since \(\Delta\) has dimension two, \(\mathcal L^3=0\), and the product of two classes with coefficients in \(\mathcal L^1\) depends only on these images. Up to a sign that depends on nothing, therefore,

\[
(\Gamma^*\alpha)(v_1,v_2)
=\bigl\langle\overline\Phi(v_1),\overline\Psi(v_2)\bigr\rangle-\bigl\langle\overline\Phi(v_2),\overline\Psi(v_1)\bigr\rangle,
\qquad(2)
\]

for the Serre pairing of \(H^2(\widetilde Y,\Omega^1)\) and \(H^1(\widetilde Y,\Omega^2)\).

Let \(\Omega_s\) be the Poincaré residue of \(\Omega/q_s\) on the smooth part of \(Q_s\). For a vector field \(\zeta\) on \(\mathbb P^5\), the restriction of \(\zeta\mathbin{\lrcorner}\Omega\) to \(Q_s\) is \(\zeta(q_s)\,\Omega_s\). A lift of \(\partial_a\) to \(N\) is \(\partial_a+\zeta_a\) with \(\zeta_a(q_s)=-\dot s_a\,\delta_1\) on \(Q_s\), since \(\partial q_s/\partial s=\delta_1\). On \(Q_s\) we have \(F=F'\). So the contractions of \(\varpi_\Psi\) and \(\varpi_\Phi\) with this lift restrict to

\[
-\dot s_a\,\frac{A\,\delta_1\,\Omega_s}{(F')^2}
\qquad\text{and}\qquad
\frac{\bigl(\xi_a(q)-\dot s_a\,\delta_1G\bigr)\,\Omega_s}{(F')^3}.
\]

By the lemma, with the same sign for both,

\[
\overline\Psi(v_a)=-\dot s_a\,\beta,
\qquad
\overline\Phi(v_a)=\Bigl[\operatorname{Res}_{\widetilde Y}\frac{(\xi_a(q)-\dot s_a\,\delta_1G)\,\Omega_s}{(F')^3}\Bigr]^{1,2},
\]

where \(\beta\in H^1(\widetilde Y,\Omega^2)\) is the component of the residue of \(A\,\delta_1\,\Omega_s/(F')^2\). In (2) the terms with \(\delta_1G\) cancel. With \(\xi=\dot s_1\xi_2-\dot s_2\xi_1\),

\[
(\Gamma^*\alpha)(v_1,v_2)=\pm\Bigl\langle\operatorname{Res}_{\widetilde Y}\frac{\xi(q)\,\Omega_s}{(F')^3},\ \operatorname{Res}_{\widetilde Y}\frac{A\,\delta_1\,\Omega_s}{(F')^2}\Bigr\rangle,
\qquad(3)
\]

the cup product on \(H^3(\widetilde Y,\mathbb C)\): the first class lies in \(F^1\) and the second in \(F^2\), so their product is that of the two components. By (1),

\[
\xi(F')=q\,\nu,\qquad \nu=\kappa\,q^-G\in S_{16}.
\qquad(4)
\]

The vector \(\dot s_1v_2-\dot s_2v_1\) is tangent to the curve \(s=s_{z_0}\) of \(Z\), along which the threefold does not move. The first class in (3) is the derivative along it of the Abel–Jacobi images of the one-cycles, read from the extension of \(H^4(\widetilde X')\) by \(H^3(\widetilde Y)\) as in the remark of §3D.4. Its numerator \(\xi(q)\) is the counterpart, for a quadric section, of the polynomial \(A_5\) of [Voisin, Corollaire 2.14](https://www.numdam.org/item/ASNSP_1992_4_19_4_473_0.pdf).

*Duality on the fourfold.* For a smooth divisor \(D\) in a complex manifold \(M\), write \(\Omega^\bullet_{(M,D)}=\Omega^\bullet_M(\log D)(-D)\) for the kernel of the restriction \(\Omega^\bullet_M\to\Omega^\bullet_D\). It computes \(H^\bullet(M,D;\mathbb C)\), and \(\Omega^\bullet_M(\log D)\) computes \(H^\bullet(M\setminus D,\mathbb C)\). The product \(\Omega^\bullet_{(M,D)}\otimes\Omega^\bullet_M(\log D)\to\Omega^\bullet_M\) induces the Poincaré pairing of these two groups. When \(M\) is compact, for this pairing and the one of \(D\), the connecting map \(H^k(D)\to H^{k+1}(M,D)\) is the transpose of the residue, up to a fixed factor.

Consider the forms

\[
\eta=\frac{\xi\mathbin{\lrcorner}\Omega}{(F')^3},
\qquad
\vartheta=\frac{A\,\delta_1\,\Omega}{q\,(F')^2}
\]

on \(\widehat P\). The first is regular outside \(\widetilde X'\). The second has a pole of order two along \(\widetilde X'\) and a simple pole along \(\widehat Q=\widehat Q_s\). It is regular along \(E\), where \(\rho^*\Omega\) vanishes to order three and \(\rho^*q\) to order two. Their restriction and residue on \(\widehat Q\) are the two forms of (3). Residues along \(\widehat Q\) and \(\widetilde X'\) anticommute, so the second class in (3) is, up to sign, the residue along \(\widetilde Y\) of the class \(\operatorname{Res}_{\widetilde X'}\vartheta\) on \(\widetilde X'\setminus\widetilde Y\). By this transposition, (3) becomes

\[
(\Gamma^*\alpha)(v_1,v_2)=\pm\bigl\langle\partial\operatorname{Res}_{\widetilde Y}(\eta|_{\widehat Q}),\ \operatorname{Res}_{\widetilde X'}\vartheta\bigr\rangle,
\qquad(5)
\]

with \(\partial:H^3(\widetilde Y)\to H^4(\widetilde X',\widetilde Y)\) and the pairing of \(H^4(\widetilde X',\widetilde Y)\) with \(H^4(\widetilde X'\setminus\widetilde Y)\).

The divisors \(\widetilde X'\) and \(\widehat Q\) are transverse. The proof of the pole-order lemma therefore applies to the forms of \(\Omega^\bullet_{(\widehat P,\widehat Q)}\) and of \(\Omega^\bullet_{\widehat P}(\log\widehat Q)\) with poles along \(\widetilde X'\): in both cases the graded quotients are exact, because \(dF'\) is nowhere zero on \(\widetilde X'\) as a logarithmic form. It defines residues along \(\widetilde X'\) with values in \(\Omega^\bullet_{(\widetilde X',\widetilde Y)}\) and in \(\Omega^\bullet_{\widetilde X'}(\log\widetilde Y)\), in which a five-form with a pole of order \(k\) has a residue in the hypercohomology of the truncation \(\sigma_{\ge5-k}\). These residues are compatible with the restriction sequences of the pairs \((\widehat P,\widehat Q)\) and \((\widetilde X',\widetilde Y)\). The connecting map of the first sequence carries the class of \(\eta|_{\widehat Q}\) to that of \(d\eta\), a five-form, which vanishes on \(\widehat Q\). By (4) and the formula above for the differential,

\[
\partial\operatorname{Res}_{\widetilde Y}(\eta|_{\widehat Q})=\pm\operatorname{Res}_{\widetilde X'}(d\eta),
\qquad
d\eta=\frac{\operatorname{div}\xi\;\Omega}{(F')^3}-\frac{3\,q\,\nu\,\Omega}{(F')^4}.
\]

The residue of the first term lies in the image of \(\mathbb H^4(\sigma_{\ge2}\Omega^\bullet_{(\widetilde X',\widetilde Y)})\), and that of \(\vartheta\) in the image of \(\mathbb H^4(\sigma_{\ge3}\Omega^\bullet_{\widetilde X'}(\log\widetilde Y))\). Their product lies in the image of \(\mathbb H^8(\widetilde X',\sigma_{\ge5}\Omega^\bullet)=0\). For the second term the product factors through the leading components

\[
x\in H^3\bigl(\widetilde X',\Omega^1_{\widetilde X'}(\log\widetilde Y)(-\widetilde Y)\bigr),
\qquad
y\in H^1\bigl(\widetilde X',\Omega^3_{\widetilde X'}(\log\widetilde Y)\bigr)
\]

of the residues of \(q\,\nu\,\Omega/(F')^4\) and of \(\vartheta\), and (5) is \(\pm3\langle x,y\rangle\) for the Serre pairing.

*The Jacobian ring.* In the proof of the pole-order lemma the graded quotients have \(\mathcal O\)-linear differentials, and the leading component of a residue is the image of the polar part of the form under their iterated connecting maps, as recalled in Chapter 1 after [Diamond, Lemma 2.2](https://arxiv.org/html/2603.29157#S2.SS1). These components are therefore compatible with multiplication by sections of line bundles. Both \(q\) and \(\delta_1\) vanish to order two along \(L\). Let \(\widehat q\) and \(\widehat\delta_1\) be the sections of \(\mathcal O_{\widehat P}(\widehat Q)\) they define, so that \(\widehat\delta_1/\widehat q=\delta_1/q\).

The form \(q\,\nu\,\Omega/(F')^4\) is \(\widehat q\) times a form with values in \(\mathcal O(-\widehat Q)\), and multiplication by \(\widehat q\) carries \(\Omega^\bullet_{\widehat P}\otimes\mathcal O(-\widehat Q)\) into \(\Omega^\bullet_{(\widehat P,\widehat Q)}\). So \(x\) is the image of the leading component \(x_0\in H^3(\widetilde X',\Omega^1_{\widetilde X'}(-\widetilde Y))\) of that form. A logarithmic form has at most a simple pole, and \(\vartheta=(\widehat\delta_1/\widehat q)\cdot A\,\Omega/(F')^2\). So the image of \(y\) in \(H^1(\widetilde X',\Omega^3_{\widetilde X'}(\widetilde Y))\) is \(\widehat\delta_1\,\alpha'\), where \(\alpha'\in H^1(\widetilde X',\Omega^3_{\widetilde X'})\) is the pullback of the \((3,1)\)-component of the residue of \(A\,\Omega/(F')^2\) on \(X'\). Hence

\[
\langle x,y\rangle=\langle x_0,\widehat\delta_1\,\alpha'\rangle=\langle\widehat\delta_1\,x_0,\alpha'\rangle,
\]

and \(\widehat\delta_1\,x_0\) is the pullback of the \((1,3)\)-component of the residue of \(\delta_1\nu\,\Omega/(F')^4\) on \(X'\). The last pairing is the Serre pairing on \(X'\) of the classes with numerators \(\delta_1\nu\in S_{18}\) and \(A\in S_6\). By the theorem of Carlson and Griffiths, in the form of [Voisin, Theorem 0.5](https://arxiv.org/abs/2004.09310), it is a fixed nonzero multiple of \(\operatorname{soc}_{R(F')}(\delta_1\nu A)\). With (4) this is the first formula.

For the second, \(\delta_1q^-=\delta_0\delta_1-s\,\delta_1^2\). If \(\lambda\in R(F')^{[\det]}\) and \(A\in S_6^{[\chi\det]}\), the product \(\lambda A\kappa\,\delta_1^2\) changes sign under \(\sigma_0\), and \(\operatorname{soc}_{R(F')}\) vanishes on it. ∎

**Remark: three checks.** The right side of the formula has the properties that the left side requires.

1. For a linear vector field \(\ell\), the residue of \(\ell(F)\,\Omega/F^2\) has no \((3,1)\)-component, so the right side must vanish for \(A=\ell(F)\). By (1), the polynomials \(\kappa\,q\,q^-G\) and \(\kappa R\,\delta_1^2G\) lie in \(J(F')\), and hence so does \(\kappa R\,\delta_0^2G\). Modulo \(J(F')\), the polynomial \(\ell(F)\) is \(\ell(R)\,q\,q^-+R\,\ell(q)\,q^-+R\,q\,\ell(q^-)\). After multiplication by \(G\kappa\,\delta_1q^-\), the first and third terms contain \(\kappa\,q\,q^-G\), and the second is \(\kappa R\,G\,\ell(q)\,\delta_1(q^-)^2\), each monomial of which in \(\delta_0,\delta_1\) contains \(\delta_0^2\) or \(\delta_1^2\).
2. The same fourfolds and threefolds are described by \((\delta_1,\delta_0,-s^2R,s^{-1})\) in place of \((\delta_0,\delta_1,R,s)\). This leaves \(\kappa\) unchanged and replaces \(\delta_1q^-\) by \(-s^{-1}\delta_0q^-\). The right side is unchanged, because \(\kappa\,G\,q^-(\delta_0+s\,\delta_1)\) lies in \(J(F')\).
3. The exchange \(\sigma_0\) carries \(Y_s\) to \(Y_{-s}\) and fixes an invariant class on \(X'\), and it multiplies \(\alpha\in H^{3,1}(X)[\chi]\) by \(-1\). Correspondingly, replacing \(s\) by \(-s\) changes the sign of \(\kappa\) and of the second formula.

The verifier below confirms the first check on its seed.

**Remark: degree of the split section and Jacobian annihilators.** The same residue argument applies to a split-section family \(F'=F-R\,q_sq_{-s}\) with \(q_{\pm s}=\delta_0\pm s\,\delta_1\in S_d\) and \(R\in S_{6-2d}\) for \(d\in\{1,2,3\}\), whenever the base locus \(\{\delta_0=\delta_1=0\}\) is resolved: the pairing is proportional to \(\operatorname{soc}_{R(F')}(\lambda A\kappa\,\delta_0\delta_1)\) with \(\kappa=\dot R_1\dot s_2-\dot R_2\dot s_1\in S_{6-2d}\) (or, when \(d=3\) and \(R\) is constant while \(q_{\pm}=a\pm b\) vary, \(\operatorname{soc}_{R(F')}(\lambda A(\dot a_1\dot b_2-\dot a_2\dot b_1))\)). However, outside \(d=2\), symmetries of \(X'\) create automatic Jacobian annihilators that absorb kernel directions of \(\mu_\lambda\) without producing a nonzero two-form:

- At \(d=1\), if \(X'\) retains separate sign changes on the linear forms \(\delta_0\) and \(\delta_1\) (for instance from a paired sign together with a coordinate exchange \(X_2\leftrightarrow Y_2\)), then \(F'\) is even in both, so \(G_4=\partial_{\delta_0}F'/(2\delta_0)\) and \(H_4=\partial_{\delta_1}F'/(2\delta_1)\) lie in \(S_4\) and satisfy \(\delta_0\delta_1G_4,\delta_0\delta_1H_4\in J(F')\). Two directions of \(\dot R\in S_4\) therefore pair to zero with \(\delta_0\delta_1\) modulo \(J(F')\), lowering the effective moving dimension by two.
- At \(d=3\), if \(F'\) is invariant under \(X_2\leftrightarrow Y_2\) and \((X_2,Y_2)\mapsto(\omega X_2,\omega^2Y_2)\) and \(b=X_2^3-Y_2^3\) is fixed up to scale, every term of \((X_2\partial_{X_2}-Y_2\partial_{Y_2})F'\in J(F')\) is divisible by \(b\), yielding a symmetric cubic \(H_3\in S_3\) with \(bH_3\in J(F')\) that absorbs one kernel direction of \(\dot a\).

At \(d=2\) the partial derivatives of \(F'\) have degree five and create no such annihilators in \(S_2\), allowing the two-dimensional kernel of \(\mu_\lambda\) below to produce a nonzero pairing.

**Finite results.** Consider the \(H\)-invariant pencil \(F_\varepsilon=F_0+\varepsilon(X_0^2+Y_0^2)X_1Y_1X_2Y_2\), and at \(\varepsilon=5\) take

\[
\begin{gathered}
F_*=F_0+5(X_0^2+Y_0^2)X_1Y_1X_2Y_2,
\qquad
R=5\bigl(X_0^2+Y_0^2+X_1^2+Y_1^2+X_2^2+2Y_2^2\bigr),
\qquad s=2,\\
\lambda=(X_0^9Y_0-X_0Y_0^9)(X_1^2-Y_1^2)+(X_0^8-Y_0^8)(X_1^3Y_1-X_1Y_1^3)\in S_{12}^{[\det]}.
\end{gathered}
\]

Both \(F_*\) and \(F'=F_*-R\,q_2q_{-2}\) reduce modulo \(5\) to the smooth Fermat sextic \(F_0\), so both are smooth over \(\mathbb Q\). A class with numerator \(\lambda\) stays of type \((2,2)\) to first order along a tangent vector \((\dot R,\dot s)\) of \(\mathcal K\) exactly when that vector lies in the kernel of

\[
\mu_\lambda:(\dot R,\dot s)\longmapsto\bigl[(-\dot R\,q_sq_{-s}+2s\,\dot s\,R\,\delta_1^2)\,\lambda\bigr]\in R(F')_{18}^{[\det]} .
\]

The verifier [`scripts/verify-hodge-locus-span.py`](../scripts/verify-hodge-locus-span.py) checks the following finite statements modulo \(109\):

| Calculation | Result |
| --- | --- |
| \(\dim S_6^H\) and the four \(P\)-invariant sectors at \(F_0\) | \(40\), and the table above |
| Rank of the multiplication \(R(F_0)_6^H\otimes R(F_0)_6^{[\chi\det]}\to R(F_0)_{12}^{[\chi\det]}\) | \(102\), the dimension of the target |
| Matrices \(\Xi\) on \(R(F_0)_6^{[\chi\det]}\) with \(\Xi^{\mathsf T}\theta=\theta\,\Xi\) for three combinations \(\theta\) of the forms \(\theta_{g,h}\) | the scalars: rank \(1088\) of \(1089\) |
| \(\dim R(F')_{18}^{[\det]}\) and \(\dim R(F')_{24}^H\) modulo \(109\) | \(3\) and \(1\) |
| Rank of \(\mu_\lambda\) on the five-dimensional tangent space of \(\mathcal K\) | \(3\), with a kernel of dimension \(2\) |
| \(\operatorname{soc}_{R(F')}\bigl(\lambda\cdot X_0^3Y_0^3\cdot\kappa\cdot\delta_0\delta_1\bigr)\) for a basis \(v_1,v_2\) of \(\ker\mu_\lambda\) | nonzero modulo \(109\) |
| \(\operatorname{soc}_{R(F')}\bigl(\lambda\cdot\ell(F_*)\cdot\kappa\cdot\delta_1q_{-2}\bigr)\) for the \(36\) coordinate vector fields \(\ell=Z_i\partial_j\) | zero modulo \(109\) |

The first three lines verify the hypotheses of the weight-four Higgs lemma at \(F_0\). A rank modulo \(109\) is a lower bound for the rank in characteristic zero, and the scalars always commute with the forms.

For the next three lines, smoothness of \(F'\) gives \(\dim_{\mathbb Q}R(F')_{18}^{[\det]}=3\) and \(\dim_{\mathbb Q}R(F')_{24}^H=1\). The corresponding modules over the discrete valuation ring \(\mathbb Z_{(109)}\) are finitely generated, and their reductions modulo \(109\) have the same dimensions, so they are free. Surjectivity of \(\mu_\lambda\) modulo \(109\) therefore lifts to \(\mathbb Z_{(109)}\), its kernel is free of rank two and reduces onto the kernel modulo \(109\), and the pairing is nonzero over \(\mathbb Q\). The last line is the first check of the remark above, on this seed and modulo \(109\); the proof does not use it.

The polynomial \((X_0^2+Y_0^2)X_1Y_1X_2Y_2\) vanishes to order four along \(L\). So every member of the pencil meets \(L\) in the same six points \(\Sigma\), and the threefolds \(\widehat Q_2\cap\rho^{-1}V(F_\varepsilon)\) form a flat proper family over the line of \(\varepsilon\). Its fiber at \(\varepsilon=0\) is smooth, by the Fermat nodality above and the nodal resolution lemma. So the condition \(\operatorname{Sing}(Y_2)=\Sigma\) holds for \(\varepsilon\) in a Zariski-open set that contains \(0\). Smoothness of \(F_\varepsilon\) and of \(F'_\varepsilon=F_\varepsilon-R\,q_2q_{-2}\), surjectivity of \(\mu_\lambda\) and nonvanishing of the pairing hold in a Zariski-open set that contains \(5\). Choose \(\varepsilon_0\) in both. Let \(\mathcal I^\circ\subset\mathcal I\) be the open set of the triples with \(\operatorname{Sing}(Y_s)=\Sigma\). Then \(p_0=(F_{\varepsilon_0},R,2)\) is a point of \(\mathcal I^\circ\) at which \(\mu_\lambda\) is surjective and the pairing on \(A=X_0^3Y_0^3\) is nonzero.

**Proof of the paired-exchange support theorem.** By the table of sectors, it remains to prove the assertion for \(e_\chi\) and \(H^4(X,\mathbb Q)[\chi]\). Throughout, \(A=X_0^3Y_0^3\), with class \(\alpha_A\in H^{3,1}(X)[\chi]\) on each member \(X\), and "the pairing" at a point of \(\mathcal I^\circ\) and a class with numerator \(\lambda\) and surjective \(\mu_\lambda\) is the number \(\operatorname{soc}_{R(F')}(\lambda A\kappa\,\delta_0\delta_1)\) for a basis of \(\ker\mu_\lambda\).

*A rational class.* At \(p_0\), surjectivity of \(\mu_\lambda\) and nonvanishing of the pairing are Zariski-open conditions on \(\lambda\in R(F')_{12}^{[\det]}=H^{2,2}(X',\mathbb C)^H_{\mathrm{prim}}\), and they hold for one \(\lambda\). So they hold on a nonempty open subset of the real form \(H^{2,2}(X',\mathbb R)^H_{\mathrm{prim}}\). Choose \(\gamma_{\mathbb R}\) in it. Keep \(F_{\varepsilon_0}\) fixed and let \((R,s)\) vary near \(p_0\). The invariant primitive cohomology of the fourfolds \(X'\) is a variation of Hodge structure of type \((3,26,3)\), and \(\mu_{\gamma_{\mathbb R}}\) is the derivative of the \((1,3)\)-part of the flat transport of \(\gamma_{\mathbb R}\). Since it is surjective, the map from the real classes of type \((2,2)\) on the nearby fourfolds to the fixed real vector space \(H^4(X',\mathbb R)^H_{\mathrm{prim}}\), by flat transport, is submersive at \(\gamma_{\mathbb R}\). This is Green's density criterion, as in [Voisin, §2.17](https://www.numdam.org/item/ASNSP_1992_4_19_4_473_0.pdf). Its image contains rational classes arbitrarily close to that of \(\gamma_{\mathbb R}\). So there are a point \(p_1=(F_{\varepsilon_0},R_1,s_1)\in\mathcal I^\circ\) and a rational class \(\gamma\in H^{2,2}(X'_1,\mathbb Q)^H_{\mathrm{prim}}\) on its fourfold \(X'_1\), for which \(\mu_\gamma\) is still surjective and the pairing is still nonzero.

*Algebraic representatives.* Put \(F'_1=\pi_2(p_1)\), and let \(\mathbb B\subset\widetilde{\mathcal B}_H\) be a small ball around \(F'_1\). Let \(N_\gamma\subset\mathbb B\) be the locus on which the flat transport of \(\gamma\) stays of type \((2,2)\). As in the integration lemma of §3D.1, it is the zero set of a section of the bundle of the spaces \(H^{1,3}(X')^H\), of rank three, with derivative \(\mu_\gamma\). This derivative is surjective already on the tangent space of \(\mathcal K\). So, for \(\mathbb B\) small, \(N_\gamma\) is a connected submanifold of codimension three, and \(\pi_2^{-1}(N_\gamma)\) is a submanifold of \(\mathcal I\) that \(\pi_2\) maps submersively to \(N_\gamma\). The points of \(\pi_2^{-1}(N_\gamma)\cap\mathcal I^\circ\) at which \(\mu_\gamma\) is surjective on the tangent space of \(\mathcal K\) and the pairing is nonzero form an open subset that contains \(p_1\). Shrink \(\mathbb B\) until every point of \(N_\gamma\) lies under such a point.

At every point of \(N_\gamma\) the class \(\gamma\) is an \(H\)-invariant rational Hodge class on a smooth \(H\)-invariant sextic. It is algebraic, so a positive multiple of it is the difference of the classes of two effective cycles of dimension two. As in the proof of the specialization lemma of §3.6, such pairs of cycles, with their integral multiplicities, are parametrized by countably many products of relative Hilbert schemes, projective over \(\widetilde{\mathcal B}_H\), each with finitely many irreducible components. Over \(\mathbb B\), the difference of the two classes is locally constant on each of them. Consider the connected components of their parts over \(\mathbb B\) on which this difference is a multiple of the transport of \(\gamma\), and intersect them with the irreducible components. This gives countably many analytic spaces, proper over \(\mathbb B\), whose images are closed analytic subsets of \(\mathbb B\) that lie in \(N_\gamma\) and cover it. By Baire's theorem one image contains a nonempty open subset of \(N_\gamma\). It is then all of \(N_\gamma\), a connected manifold.

So there are an integer \(m>0\), an irreducible component \(\mathcal M\) of one of these parameter spaces, and an open subset \(\mathcal M_\gamma\subset\mathcal M\) that maps onto \(N_\gamma\), such that the pairs of \(\mathcal M_\gamma\) have class \(m\gamma\). The image \(M\) of \(\mathcal M\) in \(\widetilde{\mathcal B}_H\) is an irreducible closed subvariety that contains \(N_\gamma\) and has its dimension. Replace \(\mathcal M\) by an irreducible subvariety through a general point of \(\mathcal M_\gamma\) that is generically finite over \(M\). At a general point of \(N_\gamma\) the variety \(M\) is smooth and coincides with \(N_\gamma\), and \(\mathcal M\to M\) is étale over it. So there are a point \(F'_2\in N_\gamma\) and a point \(m_2\in\mathcal M_\gamma\) over it such that, near \(m_2\), the map \(\mathcal M\to\widetilde{\mathcal B}_H\) is an isomorphism onto \(N_\gamma\) near \(F'_2\).

*A family of surfaces.* Let \(p_2\in\mathcal I^\circ\) be a point over \(F'_2\) at which \(\mu_\gamma\) is surjective on the tangent space of \(\mathcal K\) and the pairing is nonzero. Let \(\mathcal T=\mathcal I^\circ\times_{\widetilde{\mathcal B}_H}\mathcal M\), formed with \(\pi_2\), and let \(\psi:\mathcal T\to\widetilde{\mathcal B}_H\) be induced by \(\pi_1\). Near \(t_2=(p_2,m_2)\) the variety \(\mathcal T\) is \(\pi_2^{-1}(N_\gamma)\), a submanifold of \(\mathcal I^\circ\) of codimension three. The map \(\psi\) is submersive at \(t_2\), because \(\mu_\gamma\) is surjective on the tangent space of \(\mathcal K\). Near \(t_2\) its fiber \(Z\) through \(t_2\) is a smooth algebraic surface, and its map to \(\mathcal K^\circ\) is unramified, with tangent plane \(\ker\mu_\gamma\). The universal pairs of cycles, with the coefficients \(\pm1/m\), give a cycle \(\mathcal W\) over \(\mathcal T\) near \(t_2\) whose fibers have class \(\gamma\). By the two-form formula, for a basis \(v_1,v_2\) of \(\ker\mu_\gamma\) and the correspondence \(\Gamma\) of that formula,

\[
(\Gamma^*\alpha_A)(v_1,v_2)=c_0\,\operatorname{soc}_{R(F')}\bigl(\lambda\,A\,\kappa\,\delta_0\delta_1\bigr)\ne0
\qquad\text{at }t_2 ,
\]

where \(\lambda\) is the numerator of \(\gamma\).

Let \(\mathcal T_0\) be the irreducible component of \(\mathcal T\) through \(t_2\). It dominates \(\widetilde{\mathcal B}_H\) with fibers of dimension two, and it carries the universal cycles and their intersections with the threefolds \(Y_s\). Complete \(\psi:\mathcal T_0\to\widetilde{\mathcal B}_H\) to a projective morphism, resolve its singularities, and restrict to a nonempty Zariski-open \(\mathcal U\subset\widetilde{\mathcal B}_H\) over which the result is smooth. After a finite étale cover \(B'\to\mathcal U\), this gives a smooth projective family of surfaces \(\overline{\mathcal Z}\to B'\), whose fibers may be disconnected, with a section through each component of each fiber and a relatively ample class \(\ell\). It also gives a relative correspondence \(\Gamma\in\operatorname{CH}^3(\overline{\mathcal Z}\times_{B'}\mathcal X_{B'})_{\mathbb Q}\), the closure of the one above. The classes \(\Gamma_{b'}^*\alpha_A\) form a holomorphic section of the bundle of the spaces \(H^{2,0}(\overline Z_{b'})\). At the points \(b'\) over sextics near \(\psi(t_2)\), it restricts to a nonzero two-form on an open subset of \(\overline Z_{b'}\), by the display and the openness of nonvanishing. So \(\Gamma_{b'}^*\alpha_A\ne0\) for general \(b'\).

*The sector.* On each component of \(\overline Z_{b'}\), with its point \(p\), let

\[
\pi_{\mathrm{prim}}=\Delta-[p]\times\overline Z_{b'}-\overline Z_{b'}\times[p]-\frac1{\ell^2}\,\ell\times\ell ,
\]

a symmetric correspondence that kills \(H^0\), \(H^4\) and \(\ell\), and fixes the rest of the cohomology. Put \(\Gamma'=e_\chi\circ\Gamma\circ\pi_{\mathrm{prim}}\). The odd cohomology of \(X_{b'}\) vanishes, and \(e_\chi\) kills \(h^2\) and \(H^{2k}(X_{b'})\) for \(k\ne2\). So \(\Gamma'_*\) vanishes outside \(H^2(\overline Z_{b'})_{\mathrm{prim}}\), the orthogonal complement of \(\ell\), and maps it into \(H^4(X_{b'})[\chi]\). The projector \(e_\chi\) is self-adjoint for the intersection form and fixes \(\alpha_A\), and holomorphic two-forms are primitive. So \(\Gamma'^*\alpha_A=\Gamma^*\alpha_A\ne0\) for general \(b'\), and the spaces \(\Gamma'_*H^2(\overline Z_{b'},\mathbb Q)_{\mathrm{prim}}\) form a nonzero rational sub-variation of the pullback of \(H^4(\mathcal X/\mathcal B_H,\mathbb Q)[\chi]\) to \(B'\). The first three finite results verify the hypotheses of the weight-four Higgs lemma at \(F_0\), and \(B'\) dominates \(\mathcal B_H\). The sub-variation is therefore everything: for every \(b'\),

\[
\Gamma'_*H^2(\overline Z_{b'},\mathbb Q)_{\mathrm{prim}}=H^4(X_{b'},\mathbb Q)[\chi].
\]

*The projector.* Let \(D\subset X_{b'}\) be an \(H\)-stable divisor that contains the image of \(\Gamma_{b'}\). Then \(\Gamma'_{b'}\) is supported on \(\overline Z_{b'}\times D\). On \(H^2(\overline Z_{b'})_{\mathrm{prim}}\) the intersection form has the signs \((+,-,+)\) on the types \((2,0)\), \((1,1)\), \((0,2)\). On \(H^4(X_{b'})_{\mathrm{prim}}\) it has the signs \((-,+,-)\) on the types \((3,1)\), \((2,2)\), \((1,3)\). The map \(\Gamma'_*\) raises both Hodge indices by one, so \(-{}^t\Gamma'_*\) is the adjoint of \(\Gamma'_*\) for the two positive definite Hodge metrics. Consequently \(\Gamma'\circ{}^t\Gamma'\) is invertible on \(H^4(X_{b'},\mathbb Q)[\chi]\), and it is zero on the other degrees and sectors of \(H^*(X_{b'},\mathbb Q)\). A polynomial in it without constant term has the class of \(e_\chi\), and it is a rational cycle supported on \(D\times D\).

This holds for every member in \(\mathcal U\). Since \(e_\chi\) is a relative algebraic correspondence over the connected family \(\mathcal B_H\), the [supported-projector specialization of §3.6](03-geometric-support.md#36-supported-projectors-in-families) extends the supported representative to every smooth member. ∎

The route needs the Hodge conjecture on the second fourfold and the density argument, as in the remark of §3D.4. The cycles are not constructed, and neither is the divisor \(D\).

**Example: a quadric-contact sextic.** Consider

\[
F=\sum_{i=0}^2\bigl(X_i^6+Y_i^6\bigr)
+5(X_0^2+Y_0^2)\bigl(X_0^2Y_0^2+X_1^2Y_1^2+X_1X_2Y_1Y_2+X_2^2Y_2^2\bigr)
+\tfrac57 X_0X_1Y_0Y_1\bigl(X_2^2+2Y_2^2\bigr).
\]

Every term is invariant under \(H\), and modulo \(5\) the equation reduces to the smooth Fermat sextic \(F_0\). Hence \(X=V(F)\) is smooth and \(H^4(X,\mathbb Q)^\tau\subseteq N^1H^4(X,\mathbb Q)\). By [Chapter 1](01-certificates.md) and the [pole-order reduction of §3.5](03-geometric-support.md#35-from-divisor-support-to-every-pole-order), every \(Y\)-odd numerator admits a rational certificate at every positive pole order. In particular, at \(q=1\) the numerator \(A=X_0^3Y_0^3\) is invariant under both exchanges and even in each pair \((X_i,Y_i)\), so its residue lies in \(H^{3,1}(X)[\chi]\). The theorem gives the existence of a certificate. It gives no denominator.
