# 4. Families, representations and deformation

[Previous: quadratic nets and pair correspondences](#technical-information/quadratic-nets) · [Contents](#technical-information/introduction) · [Next: computation](#technical-information/computation)

Support theorems have two kinds of hypotheses: restrictions on the coefficient family and restrictions on the cohomological representation. This chapter computes the dimensions of coefficient families, applies finite quotients and deck/exchange descent, and proves a criterion propagating one nonzero supported class over a dominant deformation family. The final section analyzes the representations of natural quotients and a dimension obstruction to an ordinary Fano-extension argument.

## 4.1 Coefficient spaces, Hodge structures and orbit dimensions

Write \(S=\mathbb C[X_{0},X_{1},X_{2},Y_{0},Y_{1},Y_{2}]\) and let \(\pm \) indicate total \(Y\)-parity. Counting by \(Y\)-degree gives

\[
\begin{gathered}
\operatorname{dim} S_{6}^{+} = 28+90+90+28 = 236,\\
\operatorname{dim} S_{6}^{-} = 63+100+63 = 226.
\end{gathered}
\]

Indeed, the summand of \(Y\)-degree \(j\) has dimension \(\binom{8-j}{2}\binom{j+2}{2}\). Hence the parameter space of even sextics is \(\mathbb P^{235}\). For smooth \(F\) its six quintic partial derivatives form a regular sequence: their affine common zero is only the origin, and a homogeneous system of parameters in a polynomial ring is regular. The Koszul resolution, with three even and three odd generators, gives the Hilbert and trace series

\[
\begin{gathered}
H(t) = (1+t+t^{2}+t^{3}+t^{4})^{6},\\
\Theta (t) = (1+t^{2}+t^{4}+t^{6}+t^{8})^{3},\\
\operatorname{dim} (R_F)_d^\pm  = ([t^{d}]H \pm  [t^{d}]\Theta )/2,\\
R_F = S/J(F).
\end{gathered}
\]

For example, the trace follows by dividing \((1-t^{5})^{3}(1+t^{5})^{3}\) by \((1-t)^{3}(1+t)^{3}\). Griffiths' residue identification from Chapter 1 therefore gives primitive invariant Hodge numbers \((208,866,208)\), in types \((3,1),(2,2),(1,3)\). In degree six, the same calculation is \(226-18=208\): the odd Jacobian directions are \(Y_{j}F_{X_{i}}\) and \(X_{i}F_{Y_{j}}\), and there are no linear syzygies among the quintic partials. The ambient \(h^{2}\) adds one algebraic middle direction.

Let \(G=GL_{3}(X)\times GL_{3}(Y)\), of dimension eighteen. For a linear coefficient family \(V\) preserved by a connected subgroup \(H\subset G\), the image of \(G\times V\to S_{6}\) has dimension at most \(\operatorname{dim} V+18-\operatorname{dim} H\): the action of \(H\) on the source, \((g,F)\mapsto(gh^{-1},hF)\), supplies fibres of dimension \(\operatorname{dim} H\). A matching differential rank at any point proves equality. At the Fermat member \(F_{0}=\sum Z_{i}^{6}\) the eighteen orbit derivatives are the distinct monomials \(6\cdot Z_{i}^{5}\cdot Z_{j}\), with \(i,j\) in the same parity block. Thus, for a monomial coefficient family containing \(F_{0}\), counting those derivatives outside \(V\) proves the required lower bound without a generic-rank assumption.

The same eighteen independent derivatives give affine orbit dimension eighteen at \(F_{0}\) and generically on each family below. Projectivization removes the common scalar direction, so the generic projective orbit has dimension seventeen. The equation-locus dimensions below include all block coordinate changes; their rational quotient dimensions are seventeen smaller. In particular, the ambient quotient has dimension 218.

Each family in the following table has \(H^4(X)^\tau\subset N^1H^4(X)\) throughout its smooth locus. The support mechanisms are proved in Chapters 3A–3C and §4.2 below.

| Smooth sextic family | Support mechanism | Projective equation locus | Quotient |
| --- | --- | ---: | ---: |
| \(G(X,Q_0(Y),Q_1(Y),Q_2(Y))\), or its \(X/Y\) mirror | Quadratic-net pair correspondence | 127 | 110 |
| One extra \(X\) reflection and one extra \(Y\) reflection | Fano quotients and weighted threefolds | 111 | 94 |
| Cyclic-six family of §4.2 | Deck/exchange descent | 91 | 74 |
| Block-sign split \(f(X)+g(Y)\) | Elliptic companions and contraction | 55 | 38 |
| Polarized split \(f(X+Y)+f(X-Y)\), with the order-three plane family | Algebraic Kuga–Satake correspondence | 24 | 7 |

The order-three family is \(f(z_0,z_1,z_2)=g_6(z_0,z_1)+z_2^3g_3(z_0,z_1)+a z_2^6\). The two-reflection theorem also applies to additive splittings and coordinate symmetries that give these reflections after a block-linear coordinate change, as described in [Chapter 3B](#technical-information/weighted-threefolds).

### Quadratic nets and recovery from the equation

Let \(N\subset S^2Y^*\) be a basepoint-free net. Its map of projective planes is finite and dominant, so the three quadratic generators are algebraically independent. For a fixed \(N\), the coefficient space is

\[
S^6X^*\oplus S^4X^*\otimes N
\oplus S^2X^*\otimes\operatorname{Sym}^2N
\oplus\operatorname{Sym}^3N,
\]

of dimension \(28+15\cdot3+6\cdot6+10=119\). These spaces form a rank-119 vector subbundle of the trivial sextic bundle over the basepoint-free open subset of \(\operatorname{Gr}(3,6)\), of dimension nine. Its projectivization has dimension \(119+9-1=127\).

This is the dimension of the image, rather than only of its presentations. On the open set where the bidegree-\((4,2)\) contraction \(S^4X\to S^2Y^*\) has rank three, its image recovers \(N\). The recovery is regular on that rank locus. Basepoint-freeness is open, and membership of the remaining coefficient pieces in \(S^2X^*\otimes\operatorname{Sym}^2N\) and \(\operatorname{Sym}^3N\) is a closed condition in quotient bundles. Thus the smooth rank-three presentation locus is a quasiprojective subvariety of \(\mathbb P^{235}\), isomorphic to the corresponding open subset of the projective bundle. Its smooth locus is nonempty by the observation in Chapter 3C. The family is already \(G\)-stable, and its quotient dimension is \(127-17=110\).

**Example: diagonal nets.** Separate evenness in the three \(Y_i\) is composition through \(N=\langle Y_0^2,Y_1^2,Y_2^2\rangle\). Its coefficient space has projective dimension 118. The only rank-one conics in this net are the three coordinate squares, so its stabilizer in \(GL_3(Y)\) has dimension three. The net orbit has dimension six; hence this special locus has projective dimension \(119+6-1=124\), quotient dimension 107. Its full support is the diagonal-net corollary of Chapter 3C.

### The other coefficient families

For the two-reflection family, take the reflected coordinates to be \(X_2,Y_2\). Chapter 3B counts 104 coefficients. The preserving subgroup \(GL_2(X_0,X_1)\times G_m(X_2)\times GL_2(Y_0,Y_1)\times G_m(Y_2)\) has dimension ten. Exactly eight Fermat orbit derivatives mix a reflected coordinate with an unreflected coordinate in the same block, and lie outside the coefficient family. Thus its saturated cone has dimension \(104+8=112\), proving the projective dimensions \((103,111,94)\).

The cyclic-six family has 88 coefficients. Its preserving subgroup \(GL_3(X)\times GL_1(y)\times GL_2(z_0,z_1)\) has dimension fourteen. At Fermat, the four orbit monomials mixing \(y\) with \(z_0,z_1\) lie outside its invariant coefficient space. Its projective normal form therefore has dimension 87, its saturation dimension \(88+4-1=91\), and its quotient dimension 74.

The block-sign split family has \(28+28=56\) coefficients and is already \(G\)-stable, giving projective dimension 55 and quotient dimension 38.

For the polarized family, the twelve coefficients are \(7+4+1\). Put \(U=X+Y\) and \(V=X-Y\). At \(f=\sum z_{i}^{6}\) the family tangent consists of \(h(U)+h(V)\) for the twelve order-three monomials \(h\). A block-linear infinitesimal change in \(X,Y\) becomes

\[
\begin{gathered}
\delta U=C\cdot U+E\cdot V,     \delta V=C\cdot V+E\cdot U,\\
\delta F=6\sum _{i} [U_{i}^{5}(C\cdot U+E\cdot V)_{i}+V_{i}^{5}(C\cdot V+E\cdot U)_{i}],
\end{gathered}
\]

with arbitrary \(3\times 3\) matrices \(C,E\). The eighteen displayed directions are independent. The nine \(E\) directions have mixed \(U,V\) degree and do not meet the family tangent. Of the nine \(C\) directions, exactly five meet it: \(i,j\in \{0,1\}\), and \(i=j=2\). Thus the combined tangent dimension is \(12+18-5=25\). The simultaneous \(GL_{2}(z_{0},z_{1})\times G_{m}(z_{2})\), of dimension five, supplies the matching upper bound. Subtracting one for projectivization and seventeen for the generic orbit proves every entry in the table. All witnesses used here are smooth; for the polarized witness, the invertible \(U,V\) change reduces smoothness to Fermat. ∎

### Larger quadratic spaces

More generally, let \(N\subset S^2Y^*\) have dimension \(r\), and let \(b_r,c_r\) be the generic dimensions of its quadratic and cubic multiplication images. Sextics composed through \(N\) have coefficient-fiber dimension

\[
28+15r+6b_r+c_r.
\]

On the rank-\(r\) contraction locus the equation again recovers \(N\), so the projective image dimension is this number plus \(r(6-r)-1\). The resulting dimensions are

| \(r\) | \(b_r\) | \(c_r\) | Projective presentation locus |
| ---: | ---: | ---: | ---: |
| 3 | 6 | 10 | 127 |
| 4 | 10 | 20 | 175 |
| 5 | 15 | 28 | 225 |
| 6 | 15 | 28 | 235 |

The multiplication ranks have elementary witnesses. For \(r=4\), take \(N=\langle x^2,y^2,z^2,xy+xz+yz\rangle\). Over \(\mathbb C(x^2,y^2,z^2)\), the fourth generator has four distinct conjugates under sign changes modulo simultaneous sign, and therefore minimal polynomial of degree four. There is no relation of degree at most three among the four generators, proving \(b_4=10,c_4=20\). For \(r=5\), take
\[
N=\langle xy,xz,yz,x^2-y^2,y^2-z^2\rangle.
\]
Its pairwise products span every quartic monomial: the cross-products give \(x^2y^2,x^2z^2,y^2z^2,xyz^2\) and their permutations; products of the two square differences give the pure fourth powers; multiplying a square difference by \(xy,xz,yz\) gives the remaining monomials. Thus \(N^2=S^4Y^*\). It follows that \(N^3=N S^4Y^*=S^6Y^*\): use \(S^4Y^*=N^2\subset N S^2Y^*\) and multiply by \(S^2Y^*\). Maximal rank is open, giving the generic values. The cases \(r=3,6\) are immediate from algebraic independence and the full quadratic space.

These are dimensions of presentation loci. The support theorem in Chapter 3C uses the degree-four map supplied by a net; larger multiplication images do not supply that theorem's geometric hypotheses. Its final section explains the change in the auxiliary threefolds.

## 4.2 Representations and surface quotients

A finite quotient transfers the image of its averaging projector. Divisor support for the quotient therefore need not support every cohomology class of the covering fourfold. For a polynomial map \(\Phi\), the weighted-Fano theorem of Chapter 3 identifies its residue image by the density condition \(A=\det(d\Phi)b(\Phi)\). The group-algebra formulation in §3.1 describes the corresponding restriction for finite symmetries.

For arbitrary smooth ternary \(f\), the polarized split decomposition of [Chapter 3A](#technical-information/split-and-k3) illustrates this distinction. It supports a rank-1073 substructure, including the ambient class, with primitive Hodge numbers \((189,694,189)\). The complementary rank-210 piece has Hodge numbers \((19,172,19)\) and is an exterior square of primitive K3 cohomology. Supporting this piece by the Kuga–Satake criterion requires algebraicity of that correspondence. The order-three family in §4.1 satisfies this additional hypothesis.

### A cyclic-six family and complementary quotients

The deck/exchange criterion of [Chapter 3, §3.1](#technical-information/geometric-support) can support an entire involution-invariant Hodge structure even when neither quotient alone supplies it. Let \(\zeta\) be a primitive sixth root and write the coordinates as \((X_0,X_1,X_2,y,z_0,z_1)\), with \(y,z_0,z_1\) the globally odd coordinates. Set

\[
g(X,y,z_0,z_1)=(X,\zeta y,\zeta^{-1}z_0,\zeta^{-1}z_1),
\qquad g^3=\tau.
\]

The complete \(g\)-invariant sextic family is

\[
F=f_6(X)+a y^6+P_6(z_0,z_1)
  +\sum_{m=1}^{3}y^mH_{6-2m,m}(X;z_0,z_1),
\]

where the subscripts record the degrees in the ternary and binary blocks. Indeed, a monomial with \(y\)-exponent \(k\) and binary degree \(\ell\) is invariant exactly when \(k-\ell\equiv0\pmod6\). With \(k+\ell\le6\), this gives \(k=\ell=0,1,2,3\) and the two pure degree-six cases. The coefficient dimension is

\[
28+1+7+15\cdot2+6\cdot3+4=88.
\]

**Cyclic-six support theorem.** Every smooth member \(X_F=V(F)\) satisfies

\[
H^4(X_F,\mathbb Q)^\tau\subseteq N^1H^4(X_F,\mathbb Q).
\]

**Proof.** Smoothness forces \(a\ne0\), squarefreeness of \(P_6\), and smoothness of \(f_6=0\). If one condition failed, the corresponding coordinate point or plane would contain a singular point of \(F\): all omitted transverse first derivatives vanish there. Thus

\[
C=\{P_6(\alpha,\beta)=aZ^6\}\subset\mathbb P^2
\]

is a smooth integral curve. Over its affine chart \(Z=1\), consider the family of sextic threefolds

\[
V_{\alpha,\beta}:
f_6(X)+a(y^6+T^6)
 +\sum_{m=1}^{3}(yT)^mH_{6-2m,m}(X;\alpha,\beta)=0
\quad\text{in }\mathbb P^4_{X,y,T}.
\]

It maps to \(X_F\) by

\[
p(X,y,T;\alpha,\beta)=(X,y,\alpha T,\beta T).
\]

This map has degree six: over a general target point, \(T^6=P_6(z_0,z_1)/a\). Its generic fiber over \(C\) is a smooth, geometrically integral threefold. Indeed, it is a base change of a general hyperplane section in the pencil \([z_0:z_1]\). The pencil base \(f_6(X)+ay^6=0\) in \(\mathbb P^3\) is smooth, and its nonzero core gradient makes every pencil member smooth along the base. Bertini gives smoothness elsewhere; connectedness of ample hyperplane sections gives geometric integrality.

On this cover define

\[
\begin{aligned}
d &: (X,y,T;\alpha,\beta)
 \longmapsto(X,y,\zeta T;\zeta^{-1}\alpha,\zeta^{-1}\beta),\\
\sigma &: (X,y,T;\alpha,\beta)
 \longmapsto(X,T,y;\alpha,\beta),\\
r &: (X,y,T;\alpha,\beta)
 \longmapsto(X,-y,-T;\alpha,\beta),\\
e=\sigma d\sigma &: (X,y,T;\alpha,\beta)
 \longmapsto(X,\zeta y,T;\zeta^{-1}\alpha,\zeta^{-1}\beta).
\end{aligned}
\]

Homogeneity verifies that they preserve the equation and that

\[
pd=p,\qquad pe=gp,\qquad pr=\tau p,
\qquad r=d^3e^3,\qquad r\sigma=\sigma r.
\]

The independent multipliers of \(y,T\) make \(\langle d,e\rangle\cong(\mathbb Z/6)^2\), and \(\sigma\) exchanges these two factors. The group is therefore the finite semidirect product \((\mathbb Z/6)^2\rtimes\mathbb Z/2\), of order 72. Compactify and resolve the cover and its projection equivariantly under this finite group. The resulting smooth projective fourfold \(\mathcal V\), its degree-six morphism \(p\), and the displayed actions meet the algebraic hypotheses of the deck/exchange criterion.

We check its two quotient hypotheses. First, \(r,\sigma\) fix the parameter curve. On a smooth general fiber their invariant ring in \(y,T\) is generated by

\[
S=y^2+T^2,\qquad P=yT,
\]

and the quotient equation is

\[
f_6(X)+a(S^3-3SP^2)
 +\sum_{m=1}^{3}P^mH_{6-2m,m}(X;\alpha,\beta)=0
\quad\text{in }\mathbb P(1^3,2^2).
\]

Its Fano property follows directly from the finite quotient. The smooth sextic threefold \(V\subset\mathbb P^4\) has \(K_V=\mathcal O_V(1)\). The only divisorial ramification of \(\pi:V\to V/\langle r,\sigma\rangle\) is along \(y=T\) and \(y=-T\), each a hyperplane section of ramification index two; \(r\) has no divisorial fixed locus. Hurwitz gives

\[
\pi^*(-K_{V/\langle r,\sigma\rangle})=\mathcal O_V(1).
\]

The quotient is normal with quotient singularities and ample rational anticanonical divisor. Its general fibers are therefore uniruled. A smooth projective model of the total quotient \(\mathcal V/\langle r,\sigma\rangle\) is uniruled as well, so Chapter 3's covering-curve theorem supports its entire fourth cohomology.

For the second quotient, choose any of the six simple projective roots of \(P_6\). It gives a fixed point of \(g\) on \(X_F\) with \(X=y=0\). In a chart with a nonzero binary coordinate, the three \(X\)-directions have eigenvalue \(\zeta\), the \(y\)-direction has eigenvalue \(\zeta^2\), and the binary-ratio direction has eigenvalue one. The simple-root derivative eliminates this last direction from the tangent space to \(X_F\). Hence the tangent age is

\[
\operatorname{age}(g)=\frac{1+1+1+2}{6}=\frac56<1.
\]

Since \(X_F\) is smooth projective with trivial canonical bundle, [Kollár–Larsen, Theorem 2](https://arxiv.org/pdf/math/0701466) makes \(X_F/\langle g\rangle\) uniruled. Its smooth projective models also have divisor-supported fourth cohomology. Both quotient hypotheses now hold, and the deck/exchange criterion proves the theorem. ∎

This family is not contained in the quadratic-net family in the \(Y\) orientation. For a general member, its bidegree-\((4,2)\) contraction has image \(\langle yz_0,yz_1\rangle\). No basepoint-free three-dimensional net can contain this pencil: on \(y=0\), both forms vanish and any third homogeneous quadric has a projective zero. The net theorem and the present deck/exchange theorem therefore have distinct hypotheses.

### Paired signs and a surface quotient

Let \(P\) be generated by the paired signs \(s_i:(X_i,Y_i)\mapsto(-X_i,-Y_i)\), and let
\[
h=\operatorname{diag}(\zeta^2,\zeta,1,\zeta^3,\zeta^2,\zeta),
\qquad \zeta^6=1.
\]
Projectively \(P\cong(\mathbb Z/2)^2\), since \(s_0s_1s_2\) is scalar. Its intersection with \(\langle h\rangle\) is trivial, and \(\tau=s_1h^3\). Thus \(\Gamma=P\times\langle h\rangle\) has order 24 and contains the prescribed involution. The \(\Gamma\)-invariant sextics form a 26-coefficient space: a monomial exponent \(e\) satisfies \(e_i+e_{i+3}\equiv0\pmod2\) for each pair and has \(h\)-weight zero modulo six. These conditions also imply global \(Y\)-evenness.

**Paired-sign sector theorem.** Suppose \(F\) lies in this space and \(X=V(F)\) is smooth. If the surface \(S\) over the passive field defined below is geometrically smooth, then
\[
H^4(X,\mathbb Q)^\Gamma\subseteq N^1H^4(X,\mathbb Q).
\]
The surface-smoothness condition holds on a nonempty open of the coefficient space. The supported primitive sector has Hodge dimensions \((22,74,22)\), hence rank 118; the ambient class raises the invariant rank to 119.

**The quotient field.** On the coordinate open put
\[
[u_0:u_1:u_2]=[X_0^2:X_1^2:X_2^2],\qquad
v=Y_0/X_0,\qquad c_i=(Y_i/X_i)/v\quad(i=1,2).
\]
These generate the \(P\)-invariant function field. Substitution \(Y_i=vc_iX_i\), with \(c_0=1\), turns the sextic into a ternary cubic in the \(u_i\): the pair-degree conditions make every exponent of \(X_i\) even, and their total degree is six. Its coefficients are polynomials in \(v\) and the two parameters \(c_i\). The diagonal action fixes \(c_1,c_2\) and sends
\[
v\mapsto\zeta v,\qquad
(u_0,u_1,u_2)\mapsto(\zeta^4u_0,\zeta^2u_1,u_2).
\]
Quotienting also by \(\tau\) replaces \(v\) by \(b=v^2\). Over \(K=\mathbb C(c_1,c_2)\), homogenization gives
\[
S=\{H=0\}\subset\mathbb P^2_u\times\mathbb P^1_{(b:r)},
\qquad H=\sum_{j=0}^3 b^jr^{3-j}C_j(u).
\]
Here \(C_0,C_3\) lie in the span of \(u_0^3,u_1^3,u_2^3,u_0u_1u_2\), \(C_1\) in the span of \(u_0^2u_1,u_1^2u_2,u_2^2u_0\), and \(C_2\) in the span of \(u_0u_1^2,u_1u_2^2,u_2u_0^2\). In particular \(S\) has bidegree \((3,3)\). The remaining order-three action, with \(\omega=\zeta^2\), is
\[
\phi:(b:r;u_0:u_1:u_2)\mapsto
(\omega b:r;\omega^2u_0:\omega u_1:u_2).
\]
It preserves \(H\), and \(X/\Gamma\) is birational over the passive surface to the family \(T=S/\langle\phi\rangle\).

**The surface cohomology.** Adjunction and the hypersurface exact sequence give
\[
K_S=\mathcal O_S(0,1),\qquad q(S)=0,\qquad p_g(S)=2.
\]
For example, \(H^1(\mathcal O_S)=0\) follows from Künneth applied to \(\mathcal O(-3,-3)\), and the two canonical sections are represented on \(r=1\) by residues with numerators \(1,b\). The determinant of the action on \(u\) is one, while \(db\) has character \(\omega\). The two holomorphic forms therefore have characters \(\omega,\omega^2\).

The action is free. A fixed point would lie over \(b=0\) or \(r=0\) and at one of the three coordinate vertices in \(\mathbb P^2\). None is on \(S\): the six pure sixth-power coefficients are nonzero, since otherwise the corresponding coordinate vertex would be singular on \(X\). Thus \(T\) is smooth and
\[
p_g(T)=q(T)=0.
\]
It has \(\chi(\mathcal O_T)=1\) and \(b_2(T)=10\), since the free cover has degree three, \(\chi(\mathcal O_S)=3\), and \(K_S^2=0\). The surface-fibration theorem of §3.2 supports all fourth cohomology on a smooth projective model of \(X/\Gamma\). Quotient transfer proves the claimed support on \(X\).

Since \(S\to T\) is étale, \(K_S\) is the pullback of \(K_T\), and \(T\) has Kodaira dimension one. Its genus-one fibration has multiple fibers of order three over the images of \(b=0,\infty\). The support input is the algebraicity of \(H^2(T)\); this example shows why the surface-fibration theorem also applies beyond uniruled fibers. The quotient construction follows the [surface-quotient argument of `hodgepodgeconjecture`](https://github.com/hodge-computer/sextics/discussions/55#discussioncomment-19077807).

**Openness and dimensions.** At the Fermat member,
\[
H=\sum_{i=0}^2(r^3+c_i^6b^3)u_i^3,\qquad c_0=1.
\]
Choose nonzero \(c_i\) with distinct sixth powers. The zero sets of the three coefficients on \(\mathbb P^1\) are disjoint and reduced. At a putative singular point, the \(u\)-partials force all but one coordinate to vanish; the derivative of its nonzero coordinate's coefficient then excludes singularity. At \(b=0,\infty\), the fiber is a smooth diagonal cubic. Properness and openness of smoothness therefore give the required nonempty coefficient open. The theorem is stated with this condition; it does not infer it for every special member from smoothness of \(X\) alone.

The equivariant Koszul series is constant on the smooth coefficient locus, so the Hodge dimensions may be counted in the Fermat ring \(\mathbb C[Z]/(Z_0^5,\ldots,Z_5^5)\). The projective volume has \(h\)-weight nine, hence numerator weight three modulo six is required. The exact count is

```python
from itertools import product

w = (2, 1, 0, 3, 2, 1)
def character(e, weight):
    return (all((e[i]+e[i+3]) % 2 == 0 for i in range(3))
            and sum(a*b for a, b in zip(e, w)) % 6 == weight)

assert sum(sum(e) == 6 and character(e, 0)
           for e in product(range(7), repeat=6)) == 26
assert [sum(sum(e) == d and character(e, 3)
            for e in product(range(5), repeat=6))
        for d in (6, 12, 18)] == [22, 74, 22]
```

These are the \((3,1),(2,2),(1,3)\) dimensions of the primitive representation. The normal-form projective dimension is 25. Its block-linear saturation has dimension 37: the diagonal six-dimensional torus preserves the coefficient space and the twelve off-diagonal Fermat orbit derivatives lie outside it. The corresponding quotient dimension is 20. The representation has rank 118, compared with rank 1282 for the full invariant primitive cohomology.

## 4.3 Cyclic-seven symmetry

Let \(\sigma\) act on \((x,y,z)=(X_0,X_1,X_2)\) with weights \((1,2,4)\) modulo seven and fix \(Y\). The complete \(\sigma\)-invariant, \(Y\)-even sextic family is

\[
F=a\cdot x^{5}\cdot y+b\cdot y^{5}\cdot z+c\cdot z^{5}\cdot x+d\cdot x^{2}\cdot y^{2}\cdot z^{2}+x\cdot y^{3}\cdot Q_{0}(Y)+x^{3}\cdot z\cdot Q_{1}(Y)+y\cdot z^{3}\cdot Q_{2}(Y)+g(Y).
\]

where \(Q_i\) are arbitrary ternary quadratics and \(g\) is an arbitrary ternary sextic. This is a fifty-dimensional coefficient space.

**Cyclic-seven sector theorem.** Every smooth member of this family has \(H^4(X)^{\tau,\sigma}\subset N^1H^4(X)\). Its invariant primitive Hodge numbers are \((19,128,19)\).

**Proof.** Introduce the rational coordinates

\[
\begin{gathered}
U=x^{2}\cdot y/z,     V=y^{2}\cdot z/x,     W=z^{2}\cdot x/y,\\
p=aU^{2}W+bV^{2}U+cW^{2}V+dUVW,\\
P=p+UVQ_{0}+UWQ_{1}+VWQ_{2}+g.
\end{gathered}
\]

Substitution gives \(F=P\). The target is the weighted fourfold \(\mathcal W=\{P=0\}\subset \mathbb P(2,2,2,1,1,1)\). On a chart \(Y_{j}=1\) and \(x\cdot y\cdot z\ne0\), the exponent matrix for \((x,y,z)\mapsto (U,V,W)\) is

\[
\begin{gathered}
\begin{pmatrix}2&1&-1\\-1&2&1\\1&-1&2\end{pmatrix},
\qquad \det=14.
\end{gathered}
\]

Its kernel consists of \(\sigma \) and the simultaneous sign change of \(x,y,z\), the latter being \(\tau \) projectively on this chart. Thus the rational map has degree fourteen and identifies the function field of \(\mathcal W\) with the invariant function field of \(X\). The full inverse image of \(P=0\) is \(F=0\), which is irreducible because a reducible projective hypersurface of this dimension is singular along an intersection of components.

We check quasismoothness on every coordinate stratum. Smoothness of \(F\) implies smoothness of its plane restrictions \(F(X,0)\) and \(g(Y)\), because derivatives in the omitted coordinates vanish there. It also forces \(ab\cdot c\ne0\) by examining the three \(X\)-coordinate points. On \(U\cdot V\cdot W\ne 0\), the coordinate map is étale, with Jacobian \(14\cdot x\cdot y\cdot z\), so a singular cone point of \(P\) would lift to one of \(F\). If \(U=0\) and \(V\cdot W\ne 0\), then \(P_V=W(cW+Q_{2})\) and \(P_W=V(2\cdot cW+Q_{2})\); these cannot both vanish. The other two such strata follow cyclically. If \(U\ne 0,V=W=0\), the equation reduces to \(g=0\): for \(Y\ne 0\) use \(\nabla g\ne 0\), while for \(Y=0\) use \(P_W=aU^{2}\ne 0\). Treat the \(V\)-only and \(W\)-only strata in the same way. If \(U=V=W=0\), use smoothness of \(g\) once more. These exhaust the nonzero cone points.

The singular locus of the weighted ambient space meets \(\mathcal W\) along the smooth plane cubic \(p=0\) at \(Y=0\). Transversely the singularities are \(\frac12(1,1,1)\), since the three \(Y\) directions are the odd stabilizer directions. Their age is \(\frac32\), so they are terminal. Weighted adjunction gives \(-K_\mathcal W=\mathcal O(3)\). The normal-Fano support theorem of Chapter 3 gives divisor-supported \(H^4\) on a resolution. Quotient transfer then supports \(H^4(X)^{\tau,\sigma}\), including the boundary terms introduced when resolving the rational map. ∎

**Character dimensions.** The residue volume is invariant under \(\sigma\) and anti-invariant under \(\tau\). The corresponding degree-six numerator space is

\[
x\cdot y\cdot z\cdot k[Y_{0},Y_{1},Y_{2}]_{3} \oplus  \operatorname{span}\{x^{3}\cdot y^{2},y^{3}\cdot z^{2},z^{3}\cdot x^{2}\}\cdot k[Y_{0},Y_{1},Y_{2}]_{1}.
\]

There are \(10+9=19\) directions. The degree-six odd Jacobian generators \(Y_jF_{X_i}\) and \(X_iF_{Y_j}\) have nonzero \(\sigma\)-characters \(-w_i\) and \(w_i\), with \(w_i\in\{1,2,4\}\). None of the nineteen invariant directions is therefore Jacobian-trivial.

For completeness, all character dimensions here follow from one explicit Koszul series. In the ring with \(u^{7}=v^{2}=1\), take the coefficient of \(t^{6\cdot q}\cdot u^{0}\cdot v^{1}\) in

\[
\begin{gathered}
\prod _{i} (1-t^{5}\cdot u^{-w_{i}}v^{e_{i}})/(1-t\cdot u^{w_{i}}v^{e_{i}}),\\
w=(1,2,4,0,0,0),     e=(0,0,0,1,1,1).
\end{gathered}
\]

At \(q=1\) it is 19; at \(q=2\) it is \(395-276+9=128\), the three terms being the polynomial, first Koszul and second Koszul contributions. Hodge symmetry gives \((19,128,19)\). The same monomial count in \(S_6\) gives fifty coefficients. Diagonal \(X\) changes and all \(Y\) changes preserve the family, so its projective saturation has dimension at most \(49+6=55\). At the smooth split Klein member, the six off-diagonal \(X\) orbit derivatives are nonzero and have the six distinct nontrivial \(\sigma\)-characters. They supply six independent directions outside the invariant family, proving equality. The member is smooth: a zero coordinate at a common zero of the ternary Klein gradient forces all coordinates to vanish; on the coordinate torus, multiplying its three derivative equations gives \(1=(-5)^3\), a contradiction. Thus the family has projective dimension 49 and saturated dimension 55, while the supported primitive representation has rank 166.

## 4.4 A generic support criterion

Here “generic” refers to the geometric generic point of the full even-sextic parameter space. A support defined there spreads to a finite-type family dominating that space; the dominance hypothesis is essential to the deformation argument.

**Theorem.** A polarizable subvariation of the invariant primitive fourth cohomology, over a dominant finite-type base change of the smooth even-sextic family, is the whole variation if its \((3,1)\) part is nonzero. Consequently, if a dominating family of reduced divisor supports carries one nonzero invariant primitive \((3,1)\) class at the geometric generic point, its Gysin image carries the entire invariant primitive \(H^4\) there. In particular, a generic \(q=1\) certificate for any nonzero invariant primitive target implies divisor support for that whole Hodge structure. If \(E_i\) are the resolved support components, necessarily \(\sum _i h^{2,0}(E_i)\ge208\).

We use two standard inputs from variation of Hodge structure. First, the infinitesimal residue variation for a hypersurface is multiplication by the deformation polynomial in its Jacobian ring. Second, images of morphisms of polarizable variations are polarizable subvariations, their polarization-orthogonal complements are again subvariations, and such morphisms are strict for the Hodge filtration. The first identification follows by differentiating \(A\cdot \Omega /F^{2}\): its next leading numerator is \(-2\cdot gA\), a harmless nonzero scalar times multiplication. For the second input, a morphism preserves the Hodge decomposition, so its image and kernel are Hodge substructures and the map is strict. Positivity of the associated Hodge metric makes the polarization nondegenerate on a substructure; its orthogonal complement is flat and is again a Hodge substructure, giving the required splitting. These arguments apply fibrewise and in families of constant rank. Resolve the support family and shrink its base before applying them.

**Proof of the linear-algebra step.** At Fermat,

\[
\begin{gathered}
R=\mathbb C[Z_{0},\ldots ,Z_{5}]/(Z_{0}^{5},\ldots ,Z_{5}^{5}),\\
V=R_{6}^{-},     G=R_{6}^{+},     W=R_{12}^{-},\\
(\operatorname{dim} G,\operatorname{dim} V,\operatorname{dim} W)=(218,208,866).
\end{gathered}
\]

For \(g\in G\) the Higgs map is \(M_g:V\to W, u\mapsto gu\). The diagonal Fermat automorphisms act by distinct characters on the monomial basis in each fixed degree, so its Hodge metric is diagonal. For a monomial \(g=Z^{a}\), the positive operator \(M_g^{\dagger} M_g\) is consequently diagonal, and its entry on \(Z^{u}\) is nonzero exactly when \(u+a\le (4,\ldots ,4)\) coordinatewise.

The following finite calculation proves three combinatorial facts: these support signatures distinguish all 208 monomials \(u\); every \(u\) has a common nonzero product with the anchor \(b=(1,1,1,1,1,1)\); and \(G\cdot V=W\). It is included in full, uses only integer comparisons and sets, and also checks the one-reflection variant used below.

```python
from itertools import product

def check(extra, anchor, expected):
    def parity(u): return sum(u[3:]) % 2
    box = list(product(range(5), repeat=6))
    G = [u for u in box if sum(u)==6 and parity(u)==0 and extra(u)]
    V = [u for u in box if sum(u)==6 and parity(u)==1 and extra(u)]
    W = {u for u in box if sum(u)==12 and parity(u)==1 and extra(u)}
    signatures, images = [], []
    for u in V:
        image = {tuple(x+y for x,y in zip(u,a)) for a in G
                 if all(x+y<=4 for x,y in zip(u,a))}
        images.append(image)
        signatures.append(tuple(all(x+y<=4 for x,y in zip(u,a)) for a in G))
    assert (len(G),len(V),len(W)) == expected
    assert len(set(signatures)) == len(V)
    anchor_image = images[V.index(anchor)]
    assert all(image & anchor_image for image in images)
    assert set().union(*images) == W
    return expected

assert check(lambda u: True, (1,1,1,1,1,1), (218,208,866)) == (218,208,866)
assert check(lambda u: u[5]%2==0, (1,1,1,1,2,0), (144,126,492)) == (144,126,492)
```

Distinct support signatures give distinct joint eigenvalue tuples, regardless of the actual positive metric coefficients. Polynomial interpolation in the commuting diagonal operators therefore supplies every monomial projector \(P_u\). Given a common product exponent \(w\ge u,b\), write \(a=w-u\) and \(c=w-b\). Both are allowed even sextic exponents, so \(P_b M_{Z^{c}}^{\dagger} M_{Z^{a}}P_u\) is a nonzero matrix unit from the \(u\)-line to the \(b\)-line. Taking adjoints and composing supplies every matrix unit. Thus the \(M_h^{\dagger} M_g\) generate \(\operatorname{End}(V)\).

**Proof of the geometric step.** Let \(U\) be a polarizable subvariation of the invariant primitive variation, over a dominant base change. Orthogonal splitting shows that every \(M_h^{\dagger} M_g\) preserves \(U^{3,1}\). The full endomorphism algebra forces that piece to be zero or all of \(V\). To justify using Fermat even when the support family is defined only over a different open set, choose finitely many matrix-unit words witnessing generation. Their nonzero determinant persists in a real-analytic neighbourhood of Fermat. The smooth locus of a dominant finite-type map meets that neighbourhood with surjective tangent map; it therefore supplies all allowed Higgs directions there. Hodge numbers of the subvariation are locally constant, so the zero-or-full alternative holds generically.

If \(U^{3,1}=V\), stability under the Higgs field and the verified equality \(G\cdot V=W\) force \(U^{2,2}=W\). Complex conjugation gives its whole (1,3) part as well. Apply this to the image of the component Gysin maps, intersected with the invariant primitive sector. The assumed nonzero class rules out the zero alternative. Strictness gives a surjection \(\bigoplus _i H^{2,0}(E_i)\to H^{3,1}(X)^\tau \), proving the lower bound 208. Exceptional components whose image has codimension at least two contribute no (3,1) part, so they do not weaken that bound. ∎

A certificate over the algebraic closure of the universal coefficient field uses finitely many algebraic coefficients. They lie in a finite extension; the denominator and its support spread over a nonempty open of a finite-type base change. Thus the theorem applies. Chapter 1 then converts the resulting support back to certificates for every \(q=1\) and \(q=2\) target. In particular, an odd sextic monomial with every exponent at most four is nonzero in the Fermat Jacobian ring, hence represents a nonzero generic class to which the criterion applies.

### Curve families and the parity of deformations

**Corollary.** Let an algebraic family of smooth curves on even sextics have a smooth incidence chart dominating the full even-sextic coefficient space. At a point where the coefficient projection is submersive, suppose two actual motions of the curve in the fixed fourfold have

\[
\operatorname{Tr}_C\bigl(s\wedge t\wedge\delta_C(A|_C)\bigr)\ne0
\]

for an odd sextic \(A\). Then the invariant primitive fourth cohomology of the geometric generic even sextic is divisor-supported.

**Proof.** The normal pairing is the curve-family two-form of [Chapter 3, §3.2](#technical-information/geometric-support). Close the family in the relative Hilbert scheme, choose a geometric generic component after finite base change if necessary, resolve, and take relative surface sections. Shrinking the base gives a smooth projective surface family with its universal curve correspondence. Nonvanishing of the pairing on a smooth chart is an open condition, so it holds generically on the dominating component. Average the correspondence under \(\tau\) and project away from the ambient hyperplane-square class. Since \(A\) represents an invariant \((3,1)\) class, the resulting primitive image is nonzero. This image is a polarizable subvariation, so the theorem makes it the whole invariant primitive variation. The correspondence is divisor-supported by Chapter 3. ∎

If \(T\) is the resulting smooth projective parameter surface, strictness gives \(h^{2,0}(T)\ge208\). The same argument requires at least 126 holomorphic two-forms for a parameter surface whose correspondence serves the residual variation in the one-reflection criterion below. These bounds concern a construction dominating the specified coefficient family; a surface with fewer two-forms may still detect classes on special fourfolds.

The parity distinction explains why dominance and the nonzero pairing are compatible. The residue volume form is \(\tau\)-odd, so invariant \(H^{3,1}(X)\) has odd numerators. Allowed embedded deformations have even numerators. Submersivity of the curve incidence projection therefore gives

\[
\delta_C(B|_C)=0\qquad(B\in S_6^+),
\]

while permitting \(\delta_C(A|_C)\ne0\) for odd \(A\). Indeed, a lift of the deformation of \(X\) to the incidence gives an ambient normal section of \(C\) mapping to \(B|_C\). Its connecting class is zero.

There is a useful restriction test before computing the trace. Put \(E_C^\pm=\operatorname{im}(S_6^\pm\to H^0(C,\mathcal O_C(6)))\). At such a submersive incidence point, the odd-numerator pairing factors through

\[
E_C^-/(E_C^-\cap E_C^+).
\]

In particular, it vanishes for every odd target if \(E_C^-\subseteq E_C^+\). One geometric sufficient condition is

\[
C\cap\tau C=\varnothing,
\qquad
H^1\bigl(\mathbb P^5,\mathcal I_{C\cup\tau C}(6)\bigr)=0.
\]

To prove this, prescribe a section on the disjoint union by \(A|_C\) on \(C\) and its \(\tau\)-translate on \(\tau C\). The cohomology vanishing extends that invariant section to a sextic on \(\mathbb P^5\); averaging the extension gives an even sextic with the same restriction to \(C\). Hence every odd restriction lies in \(E_C^+\). Thus a nonzero pairing in a dominating curve construction requires either intersection with the conjugate curve or failure of this degree-six interpolation condition.

**Example: an injective block projection.** Write the coordinate space as \(V_X\oplus V_Y\). If \(C\subset\mathbb P(W)\) and either projection \(W\to V_X\) or \(W\to V_Y\) is injective, every sextic on \(\mathbb P(W)\) extends to a pure-block sextic, which is even. Thus \(E_C^-\subseteq E_C^+\). The pairing vanishes at a submersive even-incidence point for every curve in such a linear subspace, independently of its degree and genus.

For equations \(E(c,u)=0\) defining a verified smooth incidence chart, with coefficient variables \(c\) and curve variables \(u\), submersivity is the finite rank condition

\[
\operatorname{im}(\partial_cE)\subseteq\operatorname{im}(\partial_uE),
\qquad
\operatorname{rank}[\partial_uE\ \partial_cE]
=\operatorname{rank}(\partial_uE).
\]

The relative kernel supplies actual curve motions through the chart. A tangent-rank calculation on an unverified or nonreduced incidence scheme does not establish the smoothness hypothesis.

### The one-reflection criterion

Retain the \(Y_{2}\) reflection \(r\) as well as \(\tau\). The residual sector has \(\tau\)-character \(+1\) and \(r\)-character \(-1\); its residue numerators are \(Y\)-odd and \(Y_{2}\)-even. The second calculation above proves dimensions \((126,492,126)\), all monomial projectors, anchor connectivity and middle-piece multiplication surjectivity for the allowed 144-dimensional infinitesimal deformation space.

**Corollary.** A finite-type family of divisor supports dominating the one-reflection coefficient space and carrying a nonzero residual \((3,1)\) class generically supports the entire residual sector. Consequently it supports \(H^4(X)^\tau\), and its residual support components satisfy \(\sum_i h^{2,0}(E_i)\ge126\).

**Proof.** Apply the preceding argument with the second set of monomial calculations. The \(r\)-invariant complement has the Fano support of Chapter 3. ∎

The coefficient dimension of this family is 158, by counting even-\(Y\), even-\(Y_{2}\) sextics. The preserving subgroup \(GL_{3}(X)\times GL_{2}(Y_{0},Y_{1})\times G_{m}(Y_{2})\) has dimension fourteen. Four outside Fermat orbit monomials, \(Y_{2}^{5}\cdot Y_{0},Y_{2}^{5}\cdot Y_{1},Y_{1}^{5}\cdot Y_{2},Y_{0}^{5}\cdot Y_{2}\), attain the upper bound \(158+18-14=162\). Its projective normal-form, saturated and quotient dimensions are therefore \((157,161,144)\). The two-reflection theorem of Chapter 3B concerns a proper sublocus with an additional \(X\) reflection. Neither that support family nor the 127-dimensional quadratic-net family dominates this 161-dimensional one-reflection locus, so neither supplies the hypothesis of this corollary.

## 4.5 Coefficient variation and pole order

The coefficient-raising identity of [Chapter 2](#technical-information/explicit-constructions) gives a second propagation argument over the generic coefficient field. Differentiating in an even sextic direction \(C\) takes a certificate for \((q,A)\) to one for \((q+1,AC)\), preserving the reduced denominator support.

Over the universal coefficient field, the direction \(\dot{F}=C\) is a derivation. It extends uniquely to every finite separable coefficient extension in characteristic zero. Applying the identity there and then the normalized trace of Chapter 1 produces a certificate over the original field. Thus an analytic choice of solutions is unnecessary, but a generic family is necessary.

Every odd monomial of degree \(6\cdot q\) is a product of an odd sextic and \(q-1\) even sextics. To prove this, let its total \(Y\)-degree be \(s\), and choose \(b\in \{1,3,5\}\) congruent to \(s\) modulo six. Select \(b Y\) factors and \(6-b X\) factors for the odd sextic; there are enough since both remaining totals are nonnegative multiples of six. Group the remaining \(Y\) factors into all-\(Y\) sextics and the remaining \(X\) factors into all-\(X\) sextics. Iterating the raising identity and taking linear combinations proves the all-positive-\(q\) assertion.

## 4.6 Quotient representations and extension obstructions

An auxiliary quotient must both have divisor-supported cohomology and reach the required representation of the covering variety. The averaging ideal of §3.1 separates these two conditions: a new correspondence can enlarge the supported image, whereas changing a residue representative within an existing quotient does not enlarge its averaging ideal.

Deformation imposes a further condition. The generic criterion of §4.4 requires a family dominating the relevant coefficient space. The following calculations determine the dimensions and cohomological images of the paired-sign and natural cubic-cover constructions, then compare the source and target dimensions of a direct Fano-extension density test.

### The transcendental part of the surface fibers

The dimension gap is explicit. Paired signs and global \(Y\)-evenness leave 74 coefficients, since for pair degrees \(2k_i\) their monomial count is
\[
\frac12\sum_{k_0+k_1+k_2=3}
\left(\prod_i(2k_i+1)+1\right)=74.
\]
The diagonal torus preserves this space and the twelve off-diagonal Fermat orbit derivatives lie outside it, so its block-linear saturation has affine dimension \(74+12=86\), against 236 for all even sextics. No construction confined to these symmetries can dominate the full coefficient space.

The fibers show what is lost geometrically. Write an arbitrary even sextic as
\[
F=\sum_{j=0}^3F_{6-2j,2j}(X,Y).
\]
Fix \(c_i=(Y_i/X_i)/(Y_0/X_0)\), with \(c_0=1\), and quotient by \(\tau\). With \(b=(Y_0/X_0)^2\), the surface over these passive parameters compactifies to
\[
\sum_{j=0}^3 b^jr^{3-j}F_{6-2j,2j}(X,cX)=0
\quad\text{in}\quad\mathbb P^2_X\times\mathbb P^1_{(b:r)}.
\]
Its bidegree is \((6,3)\). For general coefficients it is smooth, with
\[
K=\mathcal O(3,1),\qquad q=0,\qquad p_g=20.
\]
Indeed, at fixed nonzero \(c_i\) every degree-six \(X\)-monomial occurs in each coefficient of \(b^jr^{3-j}\), so the original coefficient space surjects onto the complete \((6,3)\) linear system. Bertini and adjunction apply. Paired signs replace \(X_i\) by \(u_i=X_i^2\), giving bidegree \((3,3)\) and \(p_g=2\). The additional order-three quotient of §4.2 removes the two holomorphic forms, giving \(p_g=0\). The sequence
\[
20\quad\longrightarrow\quad2\quad\longrightarrow\quad0
\]
records the dimensions of holomorphic two-forms after the successive quotients.

Even on the smooth \((3,3)\) surface, the nontrivial order-three characters remain substantial. Its Euler number is 36 and \(b_2=34\), while its free quotient has \(b_2=10\). Each nontrivial complex eigenspace therefore has dimension twelve; the characters of the holomorphic forms give Hodge dimensions \((1,10,1)\). The ten-dimensional invariant eigenspace is entirely algebraic; the other two contain holomorphic two-forms. Thus the surface-fibration theorem does not extend to a nontrivial character merely by replacing the numerator or increasing its pole order.

Without the extra diagonal symmetry, the paired cubic has coefficients of degree at most three in \(b\); its Jacobian coefficients have degrees at most twelve and eighteen. A minimal Weierstrass model with fundamental line bundle \(\mathcal O_{\mathbb P^1}(n)\) has \(\chi(\mathcal O)=n\) and canonical bundle pulled back from \(\mathcal O(n-2)\); see [Schütt–Shioda, §§6.6 and 8.2](https://arxiv.org/abs/0907.0298). The minimal degree-\((12,18)\) case has \(n=3\) and Kodaira dimension one, so the surface is not dominated by a family of rational curves with passive parameters fixed. Coprime coefficients and an exact degree-eighteen coefficient give a useful minimality criterion: they exclude nonminimality at finite places and infinity, respectively.

### The natural cubic cover and its standard representation

There is a second useful reduction for every even sextic. Let
\[
B=\mathbb P^2_X\times\mathbb P^2_Y,\qquad
(a,b,c,d)=(F_{6,0},F_{4,2},F_{2,4},F_{0,6}).
\]
Along the line \([\lambda X:\mu Y]\), the quotient \(Q=X/\tau\) has equation
\[
a+bt+ct^2+dt^3=0,\qquad t=(\mu/\lambda)^2,
\]
on the corresponding trivializations. Its discriminant is the section of \(\mathcal O_B(12,12)\)
\[
\Delta=b^2c^2-4ac^3-4b^3d-27a^2d^2+18abcd.
\]
For a general sextic, the cubic cover has monodromy \(S_3\): it is connected, and its general branch points have simple ramification. On the open \(B^\circ\) where it is étale, its rank-three permutation local system splits as
\[
\mathbb Q\oplus V_{\mathrm{std}},
\]
where \(V_{\mathrm{std}}\) is the rank-two standard representation. The weight-four part contributed by the constant summand comes from \(H^4(B)\), hence is algebraic. Up to boundary-supported classes, the primitive problem therefore requires the standard summand. The discriminant double cover carries the sign representation, and \(V_{\mathrm{std}}^{A_3}=0\). Pulling the standard local system to that cover splits it over \(\mathbb C\) into two nontrivial cubic characters; it does not make it constant.

The quotient \(Q\) itself is not uniruled. The fixed locus of \(\tau\) consists of the two smooth plane sextic curves \(X\cap\{X=0\}\) and \(X\cap\{Y=0\}\). The tangent eigenvalues there are \((1,-1,-1,-1)\), of age \(3/2\); elsewhere the action is free. Thus the quotient has terminal transverse singularities \(\frac12(1,1,1)\) and torsion canonical class. [Kollár–Larsen, Theorem 2](https://arxiv.org/pdf/math/0701466) gives Kodaira dimension zero and nonuniruledness of a smooth projective model.

Let \(Z\) be a smooth equivariant projective model of the \(S_3\)-Galois closure. The subgroup quotients which could serve the standard representation are determined without computing their equations:

| Subgroup \(K\subset S_3\), up to conjugacy | \(\dim V_{\mathrm{std}}^K\) | Quotient |
| --- | ---: | --- |
| \(1\) | 2 | \(Z\), which dominates \(Q\) generically finitely |
| \(C_2\) | 1 | A model of \(Q\) |
| \(A_3\) | 0 | The discriminant double cover |
| \(S_3\) | 0 | The rational base \(B\) |

The first two quotients are not uniruled: uniruledness of \(Z\) would descend through its generically finite map to \(Q\). The other two have no standard invariants. Consequently no collection of uniruled intermediate quotients of this natural Galois closure can serve \(V_{\mathrm{std}}\) through the averaging ideal of §3.1. This is a restriction on that quotient strategy. As the surface-fibration theorem shows, nonuniruledness itself is compatible with divisor support.

### A dimension obstruction to the direct Fano-extension density test

Another possible source of cycles is a containing Fano variety: vary it while keeping the section fixed, find rational Hodge classes on it, and restrict their algebraic representatives. This is the strategy of [Voisin's threefold argument](https://www.numdam.org/item/ASNSP_1992_4_19_4_473_0.pdf). Its direct ordinary extension to a sextic fourfold has a dimension obstruction. A one-coordinate extension is a fivefold, whose middle cohomology has odd weight and supplies no middle \(p,p\) classes. Consider instead the two-coordinate extension

\[
X=Y\cap\{u=v=0\},\qquad Y=\{G=0\}\subset\mathbb P^7,
\]

where \(Y\) is a smooth sextic sixfold, \(G|_{u=v=0}=F\), and the involution has the original three positive and three negative eigendirections plus signs \((\epsilon_u,\epsilon_v)\). Let \(R(G)\) be its Jacobian ring. The residue identification includes the determinant character:

\[
H^{6-p,p}(Y)_{\mathrm{prim}}^\sigma
\simeq R(G)_{6(p+1)-8}^{\det\sigma},
\qquad \det\sigma=-\epsilon_u\epsilon_v.
\]

Thus an invariant \((3,3)\) class is represented by \(Q\in R_{16}^{\det\sigma}\), and its first-order Hodge condition in a fixed-section direction \(g\) is multiplication

\[
g\longmapsto Qg\in R_{22}^{\det\sigma}
\simeq H^{2,4}(Y)^\sigma.
\]

The required surjectivity is impossible by dimension. Exact monomial counts give:

| Signs on \((u,v)\) | Invariant sextic coefficients | Fixed-section directions | After pointwise-fixing coordinate changes | \(h^{2,4}(Y)^\sigma\) |
| --- | ---: | ---: | ---: | ---: |
| \((+,+)\) or \((-,-)\) | 883 | 647 | at most 637 | 6503 |
| \((+,-)\) | 868 | 632 | at most 624 | 6596 |

There are 236 invariant sextic coefficients on the fixed \(\mathbb P^5\), explaining the subtraction in the third column. The equivariant projective transformations fixing that \(\mathbb P^5\) pointwise have dimension ten for equal normal signs and eight for opposite signs. They contribute trivial Hodge variation. Even the unquotiented dimensions 647 and 632 are already too small, so the conclusion does not depend on this refinement.

For reproducibility, if \(a+b=8\) are the positive and negative coordinate counts, the first numeric column is

\[
\sum_{\substack{0\le j\le6\\j\text{ even}}}
\binom{j+b-1}{b-1}\binom{6-j+a-1}{a-1}.
\]

The last column counts degree-ten monomials with each exponent at most four and polynomial character \((-1)^b\), rather than invariably taking polynomial character \(+1\). This is the determinant twist above; complex conjugation identifies the \((4,2)\) and \((2,4)\) dimensions. The equivariant Koszul formula makes these counts constant on the smooth invariant locus. The same calculation gives \(h^{5,1}(Y)^\sigma=155\) and 170, respectively. The command `python3 scripts/verify-extension-dimensions.py` reconstructs these counts by exact monomial enumeration.

Consequently this fixed-section sixfold construction cannot provide the full invariant Hodge-bundle submersion used to obtain dense rational middle Hodge classes in the Voisin argument. The dimension bound concerns that density map: it gives no obstruction to divisor support from independently supplied cycles, smaller subvariations or different ambient geometry.
