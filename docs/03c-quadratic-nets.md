# 3C. Quadratic nets and pair correspondences

[Previous: weighted threefolds and two-reflection sextics](#technical-information/weighted-threefolds) · [Contents](#technical-information/introduction) · [Next: families, representations and deformation](#technical-information/known-locus)

A basepoint-free net of ternary quadrics defines a four-to-one map of projective planes. The six unordered pairs in a general fiber are parametrized by the component lines of singular conics in the net. For sextics obtained by substitution through the net, this pair cover becomes a fourfold fibered in Fano threefolds. Its incidence with the original cover supplies the invariant fourth cohomology.

We work over \(\mathbb C\) with rational cohomology. The support and boundary arguments are those of [Chapter 3, §§3.1–3.2](#technical-information/geometric-support).

## 3C.1 The quadratic-net theorem

Let \(Q_0,Q_1,Q_2\) be quadratic forms in \(Y_0,Y_1,Y_2\), and give \(X_0,X_1,X_2,U_0,U_1,U_2\) weights \((1,1,1,2,2,2)\).

**Theorem.** Suppose
\[
F(X,Y)=G\bigl(X,Q_0(Y),Q_1(Y),Q_2(Y)\bigr)
\]
defines a smooth sextic fourfold \(V\subset\mathbb P^5\), with \(G\) of weighted degree six. For \(\tau(X,Y)=(X,-Y)\),
\[
H^4(V,\mathbb Q)^\tau\subseteq N^1H^4(V,\mathbb Q).
\]
One divisor therefore supports the entire invariant fourth cohomology. The conclusion holds for every smooth factorization of this form, including nets with singular or reducible discriminant. No additional linear symmetry is assumed.

The theorem also applies after interchanging the two coordinate blocks: their sign involutions agree projectively. By [Chapter 3, §3.5](#technical-information/geometric-support), the cohomological statement gives certificate existence for every allowed numerator at every positive pole order.

## 3C.2 Transfer through unordered pairs

The finite-cover argument is independent of the geometry of quadrics.

**Pair-transfer proposition.** Let \(M\) be a smooth projective variety with a faithful action of a finite group \(K\), and let \(f:M\to B\) be a dominant generically finite \(K\)-invariant morphism to an integral projective variety. Suppose \(M/K\to B\) has degree \(n>2\). On a dense open \(B^\circ\), take its finite étale cover \(S^\circ\to B^\circ\), and let \(Z^\circ\to B^\circ\) be the associated cover of unordered pairs of distinct sheets. If smooth projective models \(\widetilde B\) and \(\widetilde Z\) satisfy
\[
H^k(\widetilde B)=N^1H^k(\widetilde B),
\qquad
H^k(\widetilde Z)=N^1H^k(\widetilde Z),
\]
then
\[
H^k(M)^K\subseteq N^1H^k(M).
\]
For a disconnected pair cover, the hypothesis is imposed on every component.

**Proof.** A point of an \(n\)-element set belongs to \(n-1\) pairs, and two distinct points belong together to one pair. Thus the incidence matrix \(A\), with rows indexed by pairs and columns by points, satisfies
\[
A^tA=(n-2)I_n+J_n,
\]
where \(J_n\) has every entry equal to one. This identity is invariant under every permutation of the sheets.

Shrink \(B^\circ\) so that \(M^\circ\to S^\circ\) is a \(K\)-torsor. Pull point-pair incidence back to
\[
C^\circ\subset M^\circ\times_{B^\circ}Z^\circ.
\]
Its matrix repeats each column of \(A\) exactly \(|K|\) times. Consequently
\[
{}^tC^\circ\circ C^\circ
=(n-2)\sum_{g\in K}\Gamma_g
 +{}^t\Gamma_{f^\circ}\circ\Gamma_{f^\circ}. \qquad\text{(1)}
\]

Compactify the pair cover by normalizing \(B\) in its function fields, and resolve this compactification and \(B\). After further shrinking \(B^\circ\), the resulting models are isomorphisms over the open. Let \(\mathcal C\subset M\times\widetilde Z\) and \(\Gamma\subset M\times\widetilde B\) be the closures of the incidence and graph. Every component dominates its source and target component. Both correspondences remain relative over \(B\).

The common-base boundary lemma of Chapter 3 therefore makes
\[
\mathcal R
=({}^t\mathcal C)_*\mathcal C_*
-({}^t\Gamma)_*\Gamma_*
-(n-2)\sum_{g\in K}g^*
\]
divisor-supported in its image: restriction of the output to \(M^\circ\) forces all intermediate and input points over \(B^\circ\), where (1) holds. For \(\alpha\in H^k(M)^K\), it follows that
\[
|K|(n-2)\alpha
=({}^t\mathcal C)_*\mathcal C_*\alpha
-({}^t\Gamma)_*\Gamma_*\alpha-\mathcal R\alpha.
\]
The first two terms factor through the supported cohomology of \(\widetilde Z\) and \(\widetilde B\); the return correspondences preserve support by Chapter 3. Division by \(|K|(n-2)\) proves the claim. ∎

## 3C.3 The finite quadratic map

We begin the proof of the quadratic-net theorem by constructing the base
\[
W=\{G(X,U)=0\}\subset\mathbb P(1,1,1,2,2,2).
\]

### Basepoint-freeness and degree

Smoothness of \(V\) forces the quadrics to have no common projective zero. If \(Q(y)=0\) for \(y\ne0\), then \((0,y)\) is a singular point of the affine cone of \(F\): the weighted degree-six polynomial \(G\) has no constant or linear terms, so \(G(0)=\nabla G(0)=0\), and the chain rule gives \(\nabla F(0,y)=0\).

The resulting morphism
\[
q:\mathbb P^2_Y\longrightarrow\mathbb P^2_U,
\qquad [Y]\longmapsto[Q_0(Y):Q_1(Y):Q_2(Y)]
\]
is finite. Its pullback of a line is the ample bundle \(\mathcal O_{\mathbb P^2}(2)\), which excludes positive-dimensional fibers. Its degree is \(2^2=4\); in particular, the quadrics are linearly independent.

The affine map \(Q:\mathbb A^3\to\mathbb A^3\) is finite and flat of degree eight. Indeed, the three quadrics form a homogeneous system of parameters and a regular sequence. The polynomial ring in the \(Y\)'s is a finite free module over \(\mathbb C[Q_0,Q_1,Q_2]\), of rank \(2^3\). Thus
\[
\Phi:V\longrightarrow W,\qquad [X,Y]\longmapsto[X,Q(Y)]
\]
is finite of degree eight, as seen on a chart \(X_i\ne0\). The induced map \(V/\tau\to W\) has degree four.

### The weighted Fano base

The affine cone map \((X,Y)\mapsto(X,Q(Y))\) is finite and surjective, with only the origin over the origin. A singular nonzero point of the cone of \(W\) would lift, by the chain rule, to a singular nonzero point of the cone of \(V\). Hence \(W\) is quasismooth. Weighted adjunction gives
\[
K_W=\mathcal O_W(6-3-6)=\mathcal O_W(-3).
\]
The adjunction and local quotient descriptions are [Dolgachev, Theorems 3.3.4 and 3.1.6](https://sites.lsa.umich.edu/idolga/wp-content/uploads/sites/1334/2024/08/weighted82.pdf).

For the singularities needed here, one can check the discrepancy directly. At \(X=0\), an ambient uniformizing chart is \(\mathbb A^3_X\times\mathbb A^2_U\) modulo sign change in \(X\). All \(X\)-degrees of \(G\) are even. Quasismoothness supplies a nonzero derivative in an invariant \(U\)-direction; eliminating it leaves the local quotient
\[
\mathbb A^1\times\bigl(\mathbb A^3/\{\pm1\}\bigr).
\]
Blowing up the vertex of \(\mathbb A^3/\{\pm1\}\), the cone over the quadratic Veronese surface, gives the total space of \(\mathcal O_{\mathbb P^2}(-2)\). Its exceptional divisor \(E\) has normal bundle \(\mathcal O_{\mathbb P^2}(-2)\), and adjunction gives \(K_{\widetilde T}|_E=\mathcal O_{\mathbb P^2}(-1)\). Therefore
\[
K_{\widetilde T}=r^*K_T+\tfrac12E.
\]
This is a log resolution with discrepancy greater than \(-1\), so the singularity and its product with a smooth factor are klt. Thus \(W\) is a klt Fano fourfold. Chapter 3, §3.2 gives
\[
H^4(\widetilde W)=N^1H^4(\widetilde W)
\]
on a smooth projective model.

The projection \(W\dashrightarrow\mathbb P^2_U\) is dominant. To see this, \(G(X,0)=F(X,0)\) defines a smooth plane sextic: a singular point of that restriction would be singular for \(F\), whose derivatives in \(Y\) vanish along \(Y=0\). For fixed \(u\ne0\), the polynomial \(G(x,u)\) in three affine variables has this nonzero degree-six leading term, so its zero set is nonempty. Consequently the inverse image in \(W\) of the generic étale locus of \(q\) is nonempty.

## 3C.4 The singular-conic curve and its threefold fibers

Write
\[
Q_\lambda(Y)=\sum_i\lambda_iQ_i(Y)=Y^tA(\lambda)Y,
\qquad A(\lambda)=\sum_i\lambda_iA_i,
\]
with symmetric matrices \(A_i\), and set
\[
E=\{\det A(\lambda)=0\}\subset\mathbb P^2_\lambda.
\]

A general fiber \(q^{-1}(u)\) consists of four distinct points, with no three collinear. Otherwise the two independent conics defining the fiber would both contain their line, contradicting finiteness. The conics through the four points form the pencil \(\lambda\cdot u=0\). Its three singular members are the unions of pair-lines given by the three partitions into two pairs. They are distinct and have rank two. Since a general line in the \(\lambda\)-plane has these three distinct intersections, \(E\) is a reduced cubic, every component is generically rank two, and the rank-one locus is finite.

Let \(\widehat E\) be the normalization of the closure of the curve of pairs \((\lambda,L)\), where \(Q_\lambda\) has rank two and \(L\) is one of its component lines. It is a possibly disconnected smooth projective curve, generically two-to-one over \(E\). Define
\[
Z=\{(e,p)\in\widehat E\times W:
       \lambda(e)\cdot U(p)=0\}.
\]
The fiber over \(e\) is
\[
W_{\lambda(e)}
=\{G(X,U)=0,\ \lambda(e)\cdot U=0\}
\subset\mathbb P(1^3,2^3),
\]
a degree-six hypersurface in \(\mathbb P(1,1,1,2,2)\) after eliminating one weight-two coordinate. Every fiber has pure dimension three because \(G(X,0)\ne0\); hence every four-dimensional component of \(Z\) dominates its component of \(\widehat E\).

Restrict to \(X\ne0\), \(U\ne0\), and the generic étale locus of \(q\). On a further dense open \(W^\circ\), the map \(Z^\circ\to W^\circ\) is precisely the six-sheeted unordered-pair cover of \((V/\tau)^\circ\to W^\circ\). A pair of the four projective \(Y\)-points lies on a unique component line of a unique singular conic in their pencil. This identification is invariant under monodromy and hence identifies the finite étale covers themselves.

### Quasismoothness along every discriminant component

**Lemma.** For each irreducible component of \(E\), the hypersurface \(W_\lambda\) is quasismooth for general \(\lambda\) on that component.

**Proof.** Suppose the incidence of nonzero singular cone points of \(W_\lambda\) dominates a component \(E_0\). After a finite extension of its function field, choose affine cone representatives \(\lambda\) and \((x,u)\) for such a point. The critical equations are
\[
G_X(x,u)=0,\qquad
G_U(x,u)=c\lambda,\qquad
G(x,u)=0,\qquad
\lambda\cdot u=0. \qquad\text{(2)}
\]
Quasismoothness of \(W\) gives \(c\ne0\). Also \(u\ne0\): if \(u=0\), then \((x,0)\) is already a singular nonzero cone point of \(F\).

A nonzero derivation of \(\mathbb C(E_0)\) extends to the finite field extension. Differentiating \(G(x,u)=0\), with its fixed coefficients, gives
\[
0=dG=c\,\lambda\cdot du.
\]
Differentiating \(\lambda\cdot u=0\) therefore yields
\[
\lambda\cdot u=0,\qquad d\lambda\cdot u=0.
\]
At the generic point of the reduced curve \(E_0\), the vectors \(\lambda,d\lambda\) span its projective tangent line. Thus
\[
u\ \text{is proportional to}\ \nabla_\lambda\det A(\lambda).
\]

Let \(y_\lambda\) generate the kernel of the rank-two matrix \(A(\lambda)\). Its adjugate is \(c'y_\lambda y_\lambda^t\), with \(c'\ne0\), and hence
\[
\partial_{\lambda_i}\det A
=\operatorname{tr}\bigl(\operatorname{adj}(A)A_i\bigr)
=c'Q_i(y_\lambda).
\]
Basepoint-freeness makes \(Q(y_\lambda)\ne0\). After a further quadratic extension and rescaling \(y_\lambda\), we may assume \(Q(y_\lambda)=u\). Equation (2) now gives
\[
F(x,y_\lambda)=0,\qquad F_X(x,y_\lambda)=0,\qquad
\nabla_YF(x,y_\lambda)
=2cA(\lambda)y_\lambda=0.
\]
This contradicts smoothness of \(V\). ∎

### Fano fibers and the support conclusion

A quasismooth \(W_\lambda\) is integral: distinct components of its affine hypersurface cone would intersect away from the vertex, producing singularities there. Weighted adjunction gives
\[
K_{W_\lambda}=\mathcal O_{W_\lambda}(6-3-4)
             =\mathcal O_{W_\lambda}(-1).
\]
Its only possible local quotient singularities are \(\mathbb A^3/\{\pm1\}\), obtained by eliminating the invariant coordinate in a chart along \(X=0\). The discrepancy calculation in §3C.3 makes it klt.

Thus the general fibers on each component of \(Z\to\widehat E\) are klt Fano threefolds. After resolving \(Z\) and shrinking its curve base, the fibers are uniruled smooth models of \(W_\lambda\). The relative spaces of rational curves have countably many components. Since they cover a dense open in every general fiber over \(\mathbb C\), uncountability implies that one evaluation dominates each total-space component. Hence every component of \(\widetilde Z\) is uniruled, and Chapter 3 gives
\[
H^4(\widetilde Z)=N^1H^4(\widetilde Z).
\]
Apply the pair-transfer proposition with \(K=\langle\tau\rangle\), \(n=4\), and \(f=\Phi\). Its identity recovers \(2|K|=4\) times every invariant class from \(\widetilde Z\), \(\widetilde W\), and divisor-supported boundary terms. A finite union of supports for a rational basis gives one divisor for the entire invariant subspace. This proves the quadratic-net theorem.

## 3C.5 Scope of the construction

The diagonal net \(\langle Y_0^2,Y_1^2,Y_2^2\rangle\) gives sextics even in each \(Y_i\); arbitrary nets allow the same conclusion without requiring three coordinate reflections. Every basepoint-free net has smooth members: a general pullback \(g_3(Q(Y))\) is a smooth plane sextic by Bertini, and its sum with a smooth plane sextic in \(X\) is smooth by the affine-cone gradient criterion. The parameter space and its dimension are described in [Chapter 4](#technical-information/known-locus).

The pair identity also identifies a limitation of this particular transfer. For \(n=2\), it becomes \(A^tA=J_2\) and annihilates the trace-free part. This occurs for the quadratic space
\[
\langle Y_0^2,Y_0Y_1,Y_1^2,Y_2^2\rangle,
\]
whose plane map has degree two onto a quadric cone.

A general four-dimensional space of ternary quadrics instead maps the plane birationally onto a quartic surface in \(\mathbb P^3\). On a general line in the \(Y\)-plane, its restrictions span the three binary quadrics. Eliminating their one linear relation leaves three weight-two coordinates with the quartic relation defining a conic. The resulting threefold is a weighted complete intersection of degrees \((4,6)\) in \(\mathbb P(1,1,1,2,2,2)\), with
\[
K=\mathcal O(4+6-9)=\mathcal O(1).
\]
It therefore supplies no Fano-fiber argument of the kind used above. Extending this construction to larger quadratic spaces requires a different incidence correspondence or a support theorem for these threefolds.
