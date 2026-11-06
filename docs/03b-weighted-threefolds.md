# 3B. Weighted threefolds and two-reflection sextics

[Previous: split sextics and K3 correspondences](#technical-information/split-and-k3) · [Contents](#technical-information/introduction) · [Next: families, representations and deformation](#technical-information/known-locus)

A smooth even sextic with one additional reflection in an \(X\)-coordinate and one in a \(Y\)-coordinate has its entire invariant fourth cohomology supported on a divisor. The individual reflection quotients are Fano and supply the sectors where either reflection acts positively. The remaining simultaneous negative sector comes from a family of weighted Calabi–Yau threefolds. This chapter proves the required threefold theorem and the passage from its fibers to the fourfold.

The threefold argument adapts [Voisin, Proposition 2.1 and §§2.2–2.19](https://www.numdam.org/item/ASNSP_1992_4_19_4_473_0.pdf): embed the fixed threefold in varying Fano fourfolds, represent their rational Hodge classes by surfaces, and restrict those surfaces to curves. Two multiplication maps make the resulting Abel–Jacobi image nonzero. Monodromy, a supported projector, and specialization then give the full statement on every smooth member. We work over \(\mathbb C\) with rational cohomology; coefficient descent is addressed at the end.

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

## 3B.2 A containing Fano fourfold

Put \(W_5=\mathbb P(1,1,1,1,1,2)\), with weight-one coordinates \(z_0,\ldots,z_4\) and weight-two coordinate \(u\). Let \(Y=(G=0)\subset W_5\) be smooth of weighted degree six, and let \(H\) be an invariant weight-one linear form with smooth section \(T=Y\cap(H=0)\). Extend the involution on \(T\) by a positive normal coordinate. The nonzero \(u^3\) coefficient excludes the ambient singular vertex, and

\[
-K_Y=\mathcal O_Y(1).
\]

Thus \(Y\) is a smooth Fano fourfold. The Fano support theorem of [Chapter 3, §3.2](#technical-information/geometric-support) gives \(H^4(Y)=N^1H^4(Y)\), and its degree-four Hodge-class corollary makes every rational \((2,2)\) class algebraic. In that corollary, a splitting of the surjection from \(\bigoplus_iH^2(D_i)(-1)\) lifts a rational Hodge class to rational \((1,1)\) classes on smooth projective resolutions of the supporting divisors; the Lefschetz \((1,1)\) theorem and Gysin pushforward supply the algebraic cycles. This recovers the uniruled-fourfold theorem of Conte–Murre recalled in [Murre, §§2.3–2.5](https://seminariomatematico.polito.it/rendiconti/71-34/473.pdf), and supplies the algebraicity needed below from the existing Fano support construction.

Let

\[
R(G)=\mathbb C[z_0,\ldots,z_4,u]/(G_{z_0},\ldots,G_{z_4},G_u).
\]

The sum of the weights is seven. Weighted residues therefore identify

\[
H^{3,1}(Y)=R_5,\qquad
H^{2,2}(Y)_{\mathrm{prim}}=R_{11},\qquad
H^{1,3}(Y)=R_{17}.
\]

There is no determinant twist in these eigenspaces, because the involution negates two coordinates. Infinitesimal variation follows by differentiating the residue:

\[
\nabla_\eta\operatorname{Res}\frac{Q\Omega}{G^3}
\equiv-3\operatorname{Res}\frac{Q\eta\Omega}{G^4}
\pmod{F^2H^4(Y)}.
\]

Here \(\deg Q=11\), \(\deg\eta=6\), and \(\deg(Q\eta)=17\).

The deformations keeping the section fixed are governed by \(H^1(T_Y(-1))\). The weighted Euler and normal sequences, restricted to the smooth \(Y\), are

\[
\begin{gathered}
0\longrightarrow\mathcal O_Y(-1)
\longrightarrow\mathcal O_Y^5\oplus\mathcal O_Y(1)
\longrightarrow T_{W_5}|_Y(-1)\longrightarrow0,\\
0\longrightarrow T_Y(-1)
\longrightarrow T_{W_5}|_Y(-1)
\longrightarrow\mathcal O_Y(5)\longrightarrow0.
\end{gathered}
\]

Intermediate line-bundle cohomology vanishes, giving

\[
H^1(T_Y(-1))\simeq R_5.
\]

The degree-five Jacobian ideal includes \(G_u\) multiplied by every weight-one linear form. These terms account for the weighted coordinate changes in \(u\) fixing the section. An invariant fixed-section deformation is represented by \(H\theta\), with \(\theta\in R_5^+\).

## 3B.3 An exact multiplication witness

At the Fermat fourfold

\[
G_0=z_0^6+z_1^6+z_2^6+z_3^6+z_4^6+u^3,
\]

use the involution \(\sigma=(z_0\ z_1)(z_2\ z_3)\), fixing \(z_4,u\). Its weight-one eigenspaces have dimensions three and two, as required. The Jacobian ring is

\[
R=\mathbb Q[z_0,\ldots,z_4,u]/(z_0^5,\ldots,z_4^5,u^2),
\qquad\deg z_i=1,\quad\deg u=2.
\]

Its socle has weighted degree 22. Define

\[
\begin{gathered}
L=z_0+z_1+z_2+z_3+z_4,\qquad
D=z_0-z_1+z_2-z_3,\\
H=z_0+z_1+z_2+z_3,\qquad
Q=D(L^2+u)^5=DL^{10}+5uDL^8.
\end{gathered}
\]

Thus \(H\) is invariant and \(Q\in R_{11}^-\). Multiplication gives the following exact ranks.

| Map | Source dimension | Target dimension | Rank | Maximal minor modulo 1009 |
| --- | ---: | ---: | ---: | ---: |
| \(Q:R_5^+\to R_{16}^-\) | 82 | 120 | 82 | 45 |
| \(HQ:R_5^+\to R_{17}^-\) | 82 | 74 | 74 | 286 |

The exact verifier `scripts/verify-weighted-voisin.py`, in the repository's [reproduction scripts](https://github.com/hodge-computer/sextics/tree/main/scripts), reconstructs the matrices and their nonzero minors. Its monomial basis consists of \(z^eu^b\) with \(0\le e_i\le4\), \(b\in\{0,1\}\), and the prescribed weighted degree. For each two-element \(\sigma\)-orbit, use its sum in the plus space and its difference in the minus space, choosing the lexicographically smaller monomial first. Fixed monomials occur only in the plus basis. Expanding multiplication by the displayed integral polynomial gives integral matrices, so the nonzero determinants modulo 1009 prove the ranks over \(\mathbb Q\). Run

```sh
python3 scripts/verify-weighted-voisin.py
```

The section \(H=0\) is smooth. A singular point would satisfy

\[
u=z_4=0,\qquad z_i^5=\lambda\ (0\le i\le3),\qquad
z_0+z_1+z_2+z_3=0.
\]

If \(\lambda=0\), every coordinate vanishes. Otherwise this is a vanishing sum of four fifth roots of unity. For a primitive fifth root \(\zeta\), a relation \(\sum_{j=0}^4n_j\zeta^j=0\) with nonnegative integral \(n_j\) forces all \(n_j\) equal, by the minimal polynomial \(1+t+\cdots+t^4\). Its length must be divisible by five, which excludes four terms.

## 3B.4 Hodge loci and the Abel–Jacobi derivative

### From a polynomial witness to a rational Hodge class

Rational polynomial coefficients in \(Q\) do not make its associated Betti class rational. The passage to a rational Hodge class uses the real Hodge bundle, as in [Voisin, §§2.4–2.11](https://www.numdam.org/item/ASNSP_1992_4_19_4_473_0.pdf).

The two rank conditions are nonempty open conditions in \((Y,H,Q)\). The real form of \(H^{2,2}(Y)^-\) is Zariski dense in its complexification, so choose a real class satisfying them. In the directions keeping \(T\) fixed, the differential of its Hodge condition is

\[
\theta\longmapsto HQ\theta\in R_{17}^-=H^{1,3}(Y)^-.
\]

Its surjectivity makes the real Hodge bundle map to the locally constant real cohomology space a submersion. Rational classes are dense in that real space. After a small deformation of \(Y\) keeping \(T\) fixed, a Betti-rational anti-invariant Hodge class therefore satisfies both rank conditions. Its local Hodge locus has complex dimension \(82-74=8\).

This construction also applies to nearby \(T\). Before imposing smoothness, containing equations form an affine bundle over section equations. The rank conditions are open; more precisely, surjectivity in the fixed-section directions makes the rational Hodge locus project submersively onto nearby sections by the implicit function theorem. The construction consequently holds on a nonempty analytic open in the full invariant weighted-threefold family, containing very general members of that family.

Algebraicity on \(Y\) represents a multiple of the rational Hodge class by a difference of surfaces. Their classes can be made anti-invariant by averaging. Relative cycle parameter spaces dominate the local Hodge locus: their countably many proper images cover it, so one contains an open subset, and a multisection supplies a generically finite base change. Restricting the cycles to the fixed \(T\) gives an algebraic family of homologically trivial curves, since \(H^4(T)^-=0\). Weighted weak Lefschetz gives \(H^3(Y)=0\); naturality of Abel–Jacobi then makes the value of the restriction independent of the representative on \(Y\).

### The intrinsic derivative

Write \(\lambda\in H^2(\Omega_Y^2)^-\) for the Hodge class and \(\theta\in H^1(T_Y(-1))^+\) for a fixed-section deformation. Their contraction lies in \(H^3(\Omega_Y^1(-1))^-\). On the Hodge-locus tangent space, it is killed by multiplication by \(H\), hence lies in the image of the boundary map

\[
\delta:H^2(\Omega_Y^1|_T)\longrightarrow H^3(\Omega_Y^1(-1))
\]

from restriction. This map is injective because \(H^2(\Omega_Y^1)=0\). The restriction and conormal sequences give the normal-function derivative

\[
d\nu(\theta)=\psi\,\delta^{-1}(\lambda\mathbin{\lrcorner}\theta),
\qquad
\psi:H^2(\Omega_Y^1|_T)\longrightarrow H^2(\Omega_T^1).
\]

The map \(\psi\) is injective: its kernel comes from \(H^2(\mathcal O_T(-1))\), which equals \(H^1(\mathcal O_T(1))^*=0\) by Serre duality and Kodaira vanishing. This intrinsic calculation is the one underlying [Voisin, Lemma 2.12 and Corollary 2.14](https://www.numdam.org/item/ASNSP_1992_4_19_4_473_0.pdf); it uses the smooth pair and its restriction sequences.

Serre duality, \(K_Y=\mathcal O_Y(-1)\), and the Jacobian residue pairing identify

\[
H^3(\Omega_Y^1(-1))\simeq H^1(T_Y)^*
\simeq R_6^*\simeq R_{16}.
\]

Under these identifications, contraction with \(\lambda\) is multiplication by \(Q\). Indeed, pair it with \(\eta\in H^1(T_Y)\simeq R_6\). Cup/contraction symmetry identifies the pairing, up to a fixed nonzero sign, with the pairing of \(\lambda\mathbin{\lrcorner}\eta\) and \(\theta\). Ordinary weighted infinitesimal variation identifies the first factor with \(Q\eta\in R_{17}\), and the Serre–Macaulay pairing is the residue trace of \(Q\eta\theta\in R_{22}\). Therefore the injectivity of \(Q:R_5^+\to R_{16}^-\) makes \(d\nu\) injective on the eight-dimensional Hodge-locus tangent space.

There is also a polynomial form of the calculation. Make an invariant weight-one coordinate change so that \(H=z_4\). For \(\theta\in\ker(HQ)\), write

\[
HQ\theta=\sum_{i=0}^4 A_iG_{z_i}+BG_u,
\qquad \deg A_i=12,\quad\deg B=13.
\]

Then \(d\nu(\theta)\), up to a nonzero normalization, is \([A_4|_T]\in R_{12}(G|_T)^-=H^{1,2}(T)^-\). If this class vanishes, lift its Jacobian relation to write

\[
A_4=HP+\sum_{i=0}^3B_iG_{z_i}+CG_u.
\]

Substitution shows that \(H(Q\theta-PG_{z_4})\) lies in \((G_{z_0},\ldots,G_{z_3},G_u)\). Quasismoothness of \(T\) makes \((H,G_{z_0},\ldots,G_{z_3},G_u)\) a homogeneous system of parameters in the polynomial ring. It is a regular sequence in any order. Thus \(H\) is a nonzerodivisor modulo the other five generators, giving \(Q\theta=0\) in \(R_{16}\), and injectivity again gives \(\theta=0\).

The resulting Abel–Jacobi map is nonconstant. The minus intermediate Jacobian is an abelian variety, because its Hodge structure has level one. Taking a suitable parameter curve and compactifying its cycle family supplies a nonzero algebraic curve correspondence into \(H^3(T)^-\). The next step proves that these images span the whole minus part for a very general member.

## 3B.5 Monodromy and the weighted vertex

Let \(W=\mathbb P(1,1,1,1,2)\), and let \(\mathcal B\) be the smooth locus of the full invariant degree-six linear system. The monodromy representation on \(V=H^3(T_b)^-\) is irreducible over \(\mathbb Q\).

### The discriminant components

The fixed loci in \(W\) are

\[
\Sigma_x=(y_0=y_1=0),\qquad
\Sigma_y=(x_0=x_1=0),
\]

two copies of \(\mathbb P(1,1,2)\) meeting at the weighted vertex \(v\). Away from \(v\), the ambient tangent action at either fixed surface has two positive and two negative eigenvalues.

The second Veronese of the invariant coordinate ring is generated by

\[
x_0^2,x_0x_1,x_1^2,y_0^2,y_0y_1,y_1^2,u.
\]

It realizes the quotient as

\[
W/\sigma=\{a_0a_2=a_1^2,\ b_0b_2=b_1^2\}\subset\mathbb P^6,
\]

and invariant sextics are its complete linear system of cubic sections. Ambient cubics separate second jets at one smooth point and first jets at two distinct points. In an affine chart, constants, linear forms and quadratics are represented by cubics after multiplying by a nonvanishing coordinate. At two coordinate points, the monomials giving their first jets have disjoint coefficients.

It follows that the free-node discriminant is irreducible: the incidence of a singular section and a marked smooth quotient point is a projective bundle over the irreducible smooth quotient locus. A general singularity there is a node; upstairs it is a pair of nodes exchanged by \(\sigma\). Two marked free orbits impose independent conditions, so the locus with two pairs has codimension at least two.

A general pencil encounters only four kinds of codimension-one degeneration:

1. A pair of ordinary nodes in the free locus, exchanged by \(\sigma\).
2. An ordinary node on \(\Sigma_x\setminus\{v\}\).
3. An ordinary node on \(\Sigma_y\setminus\{v\}\).
4. A member with zero \(u^3\) coefficient and nondegenerate quadratic term on the index-two cover at \(v\).

For a marked point on either fixed surface, the value and two tangent derivatives impose three conditions against a two-dimensional choice of point. The invariant Hessian has independent tangent and normal quadratic blocks; cubic sections on the quotient allow both blocks to be nondegenerate. A degenerate block or an additional singular point imposes another condition. At the vertex, use \(u=1\) on the cover \(\mathbb C^4\to\mathbb C^4/\{\pm1\}\). The equation is

\[
c+q_2(x,y)+q_4(x,y)+q_6(x,y)=0.
\]

The quadratic is an arbitrary sum of a quadratic in \(x\) and a quadratic in \(y\), so it is generically nondegenerate on the coefficient hyperplane \(c=0\). Degeneracy or further singularities has additional codimension. These strata exhaust the possible locations of singularities, so a general pencil avoids the higher-codimension exceptions.

### The local actions

At a fixed ordinary node, the vanishing sphere is \(S^3\). The involution has two negative coordinates and degree \(+1\) on this sphere, so its vanishing class is invariant. The local monodromy acts trivially on \(V\).

At the vertex, an equivariant holomorphic Morse lemma gives the smoothing \(\{q_2=t\}/\{\pm1\}\). Its Milnor fiber retracts onto \(\mathbb{RP}^3\) and has one-dimensional reduced rational cohomology, in degree three. The lift of \(\sigma\) has degree \(+1\) on \(S^3\), so this local cohomology is invariant. The variation map factors through \(H^3(F_{\mathrm{Mil}},\partial F_{\mathrm{Mil}};\mathbb Q)\), which is also invariant by Poincaré–Lefschetz duality. Its equivariance therefore excludes an anti-invariant transformation in global cohomology.

The geometry of the resolved vertex gives the same check. In

\[
\widetilde W=\mathbb P_{\mathbb P^3}(\mathcal O\oplus\mathcal O(2))\longrightarrow W,
\]

the exceptional section \(E\simeq\mathbb P^3\) has normal bundle \(\mathcal O(-2)\). The pencil equation is locally \(c+rq_2+r^2q_4+r^3q_6=0\). At \(c=0\), its fiber is \(E\cup T'_0\), meeting along the smooth quadric \((q_2=0)\subset\mathbb P^3\). The determinant-positive involution preserves both rulings of the quadric. All cohomology of this quadric and of \(E\) is invariant.

### Vanishing cycles span the minus part

The base \(B\) of a general pencil is a smooth complete intersection of degrees \((6,6)\), avoiding \(v\). Its Koszul resolution and intermediate line-bundle vanishing on \(W\) give \(H^1(B,\mathcal O_B)=0\), hence \(H^1(B,\mathbb Q)=0\). The smooth projective total pencil is

\[
M=\operatorname{Bl}_B(\widetilde W),\qquad
H^3(M)=H^3(\widetilde W)\oplus H^1(B)(-1)=0.
\]

[Deligne's global invariant cycle theorem, Theorem 4.1.1(ii)](https://www.numdam.org/item/PMIHES_1971__40__5_0.pdf), therefore says that pencil monodromy has no fixed vectors in \(H^3(T_b)\). The theorem applies to this smooth projective total space even though the vertex fiber is not an ordinary Lefschetz fiber.

For an exchanged node pair, write \(w=\delta-\sigma\delta\). The two vanishing cycles are disjoint, and their combined Picard–Lefschetz transformation on \(V\) is

\[
v\longmapsto v+\frac{\varepsilon}{2}\langle v,w\rangle w,
\qquad\varepsilon\in\{1,-1\}.
\]

Every other local transformation is trivial on \(V\). The common fixed space is consequently the orthogonal complement of the span of these \(w\)'s. Nondegeneracy of the alternating pairing and the invariant cycle theorem show that they span \(V\).

Irreducibility of the free-node discriminant makes its vanishing differences one full-family monodromy orbit up to sign. A nonzero stable rational subspace pairs nontrivially with some \(w\); the displayed transvection puts \(w\) in that subspace, and its orbit then spans \(V\). This proves irreducibility. For comparison, the weighted Fermat threefold has 103 degree-six Jacobian monomials, seven fixed by the double swap. Thus \(h^{2,1}(T)^-=(103-7)/2=48\), and \(\dim V=96\).

At very general fibers, the span of images of curve correspondences is monodromy-invariant: spread the cycles in the countably many relative parameter spaces and take their monodromy translates. Section 3B.4 makes it nonzero. Irreducibility therefore gives a surjective algebraic correspondence

\[
\Gamma_*:H^1(C)(-1)\twoheadrightarrow H^3(T)^-
\]

for a very general \(T\), with \(C\) a smooth projective curve, allowing a finite disjoint union.

## 3B.6 Supported projectors and specialization

To apply the supported-projector specialization lemma of [Chapter 3, §3.6](#technical-information/geometric-support), we first produce the required cycle on the square of a divisor. The anti-projector acts on the single primitive degree \(H^3(T)^-\), and the preceding curve correspondence surjects onto that degree at very general fibers. Its transpose supplies the polarization adjoint.

In this case, replace \(\Gamma\) by \(P^-\circ\Gamma\), choose a \(\sigma\)-stable divisor \(D\) containing its image, and set \(S=\Gamma\circ{}^t\Gamma\). The polarization on \(H^1(C)(-1)\) and the primitive polarization on \(H^3(T)\) make \({}^t\Gamma\) the adjoint up to a fixed nonzero sign. Surjectivity makes \(S|_{H^3(T)^-}\) invertible. On all other cohomology it is zero. If its rational characteristic polynomial is \(t^m+a_{m-1}t^{m-1}+\cdots+a_0\), then \(a_0\ne0\) and

\[
[P^-]=-\frac{[S^m]+a_{m-1}[S^{m-1}]+\cdots+a_1[S]}{a_0}
\quad\text{in }H^6(T\times T,\mathbb Q).
\]

Every term has a cycle representative supported on \(D\times D\). Equality of all cohomological actions implies equality of classes by Künneth and Poincaré duality. Thus the inverse is a polynomial in an existing algebraic correspondence; no algebraic inverse conjecture is needed.

The family of smooth invariant weighted sextics is connected. The shared specialization lemma now applies: the projector is algebraic throughout the family, and it has a supported representative at very general fibers. Proper relative flag Hilbert schemes give such a representative at every smooth member. Fixed Hilbert polynomials keep the limiting support a divisor, and the flag conditions keep the limiting cycle on its square. Acting on cohomology proves the weighted threefold theorem.

This step includes the cyclic covers \(u^3=h(x_0,x_1,y_0,y_1)\). They lie in a special subfamily; the proof does not assume that full-family monodromy remains irreducible after restricting to that subfamily.

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

Two immediate applications illustrate the coefficient scope.

- If \(F=h(X_0,X_1,Y_0,Y_1)+b(s,t)\), with \(h\) even in \((Y_0,Y_1)\) and \(b\) even in \(t\), homogeneity makes \(b\) even in \(s\). Thus every smooth member of this \(4+2\) split family is covered, including a sum of two arbitrary same-parity binary sextics and a separately even binary sextic.
- If an even sextic is invariant under an \(X\)-coordinate transposition and an independent \(Y\)-coordinate transposition, their sums and differences diagonalize them over \(\mathbb Q\) to the required reflections. Block-symmetric even sextics therefore satisfy the theorem after such a coordinate change.

For data over a characteristic-zero field, the support-to-certificate equivalence and coefficient descent of [Chapter 1](#technical-information/certificates) give legal certificates for every invariant target with \(1\le q\le4\), including all central \(q=1,2\) targets. The higher-pole reduction of [Chapter 3, §3.5](#technical-information/geometric-support) preserves legal denominators and extends existence to every positive \(q\).

The two extra reflections are essential hypotheses of this proof. Global \(Y\)-evenness alone does not provide either the weighted quotient fibers or their two-minus core involution.
