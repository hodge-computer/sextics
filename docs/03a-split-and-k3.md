# 3A. Split sextics, elliptic contraction and the K3 remainder

[Previous: geometric support](#technical-information/geometric-support) · [Contents](#technical-information/introduction) · [Next: weighted threefolds and two-reflection sextics](#technical-information/weighted-threefolds)

The Fano machinery of Chapter 3 applies to arbitrary ternary sextics through an elliptic companion. This proves the complete block-sign case \(F=f(X)+g(Y)\), including \(f=g\). When the involution exchanges two equal blocks instead, the same construction supports most classes and isolates an exterior square of K3 cohomology. We prove the quotient maps, support transfer, character calculations and remaining Kuga–Satake criterion here.

## 3A.1 Triple planes and the required character

**Split theorem.** Let \(f\) and \(g\) be ternary homogeneous sextics, and suppose \(X=\{f(X)+g(Y)=0\}\subset \mathbb P^{5}\) is smooth. For \(\tau [X:Y]=[X:-Y]\), all \(H^{4}(X)^\tau \) is divisor-supported.

Smoothness of \(X\) is equivalent to smoothness of the two plane curves \(C_f=\{f=0\}\) and \(C_g=\{g=0\}\). A singular point of either curve gives a singular point in the corresponding coordinate plane of \(X\). Conversely, the two groups of partial derivatives of \(F\) are precisely those of \(f\) and \(g\), and neither group can vanish at a nonzero point if its plane curve is smooth.

Introduce the triple plane

\[
\begin{gathered}
T_f=\{u^{3}=f(z_{0},z_{1},z_{2})\} \subset  \mathbb P(1,1,1,2),\\
\rho (z,u)=(z,\zeta\cdot u),       \zeta ^{3}=1, \zeta \ne 1,\\
V_f=H^{2}(T_f)_{\mathrm{prim}}.
\end{gathered}
\]

It avoids the weighted singular vertex. Its cone gradient and smoothness of \(C_f\) show that \(T_f\) is smooth. The triple-cover algebra gives \(\pi _*\mathcal O_{T_f}=\mathcal O\oplus \mathcal O(-2)\oplus \mathcal O(-4)\) on \(\mathbb P^{2}\). Since these line bundles have vanishing \(H^{1}, H^{1}(T_f)=0\); duality gives \(H^{3}(T_f)=0\). The quotient \(T_f/\rho \) is \(\mathbb P^{2}\), so the invariant part of \(H^{2}(T_f)\) is exactly its hyperplane line.

The branch curve has genus ten and Euler characteristic \(-18\). Hence \(e(T_f)=3\cdot e(\mathbb P^{2})-2\cdot e(C_f)=45\), so \(b_{2}(T_f)=43\) and \(\operatorname{dim} V_f=42\). Its conjugate nontrivial deck eigenspaces have dimension 21 each. Adjunction gives \(K_{T_f}=\mathcal O(1)\), so \(h^{2,0}=3\). In an affine residue expression the denominator \(u^{2}\) makes every holomorphic two-form transform by \(\zeta \). The eigenspace Hodge triples, in order (2,0),(1,1),(0,2), are therefore

\[
\begin{gathered}
V_{f,\zeta }: (3,18,0),       V_{f,\zeta ^{2}}: (0,18,3).
\end{gathered}
\]

Use the Fermat elliptic curve \(E=\{a^{3}+b^{3}+c^{3}=0\}\) with \(\epsilon [a:b:c]=[a:b:\zeta c]\). On \(c=1, \epsilon \) sends \((a,b)\) to \((\zeta ^{-1}a,\zeta ^{-1}b)\), so its holomorphic form \(\mathrm da/b^{2}\) has eigenvalue \(\zeta \). Thus

\[
\begin{gathered}
U_f=[V_f\otimes H^{1}(E)]^{\operatorname{diag} \mu _{3}}
\end{gathered}
\]

has only Hodge types (2,1),(1,2), both of dimension 21. The same character on the two holomorphic factors excludes an invariant (3,0) part. This character observation motivates the construction; the following geometry proves support.

## 3A.2 The Fano elliptic companion

Set

\[
\begin{gathered}
W_f=\{f(z)+s^{3}+t^{3}=0\} \subset  \mathbb P(1,1,1,2,2).
\end{gathered}
\]

There is a rational map

\[
\begin{gathered}
T_f\times E \dashrightarrow  W_f,\\
([z:u],[a:b:c]) \mapsto  [c\cdot z:u\cdot a\cdot c:u\cdot b\cdot c].
\end{gathered}
\]

Scaling either input scales the output according to its weights. Substitution gives \(c^{6}f(z)+u^{3}\cdot c^{3}(a^{3}+b^{3})=0\). On \(c=1\), the map is \(s=u\cdot a,t=u\cdot b\). Its deck transformation is \((u,a,b)\mapsto (\zeta\cdot u,\zeta ^{-1}a,\zeta ^{-1}b)\), exactly \((\rho ,\epsilon )\). Conversely, adjoining \(u\) with \(u^{3}=f\) recovers \(a=s/u\) and \(b=t/u\). Thus the map is generically degree three and identifies \(W_f\) birationally with \((T_f\times E)/\operatorname{diag} \mu _{3}\).

The cone gradient is \((\nabla f,3\cdot s^{2},3\cdot t^{2})\), so the cone is smooth away from its vertex. The ambient singular locus is the weighted line \(z=0\). Its intersection with \(W_f\) consists of the three distinct points \(s^{3}+t^{3}=0\). Near each, the derivative along that weighted line is nonzero, leaving three transverse coordinates on which \(\mu _{2}\) acts by simultaneous negation. The local singularity is 1/2(1,1,1). These quotient points are the only singularities; their terminality also follows from the quotient age 3/2>1, though normality and the anticanonical class already suffice for the curve theorem used here.

Weighted adjunction gives \(-K_{W_f}=\mathcal O(1)\), an ample rational line bundle. Thus \(W_f\) is Fano. The covering-curve theorem of Chapter 3 gives a divisor supporting all \(H^{3}(\widetilde W_f)\) on a smooth resolution.

The quotient-transfer lemma then supplies a divisor \(D_f\subset T_f\times E\) supporting \(U_f\). Indeed, \(H^{1}(T_f)=H^{3}(T_f)=0\), and the invariant hyperplane part of \(H^{2}(T_f)\) contributes nothing after tensoring with \(H^{1}(E)\), which has no \(\epsilon \)-invariants. Thus \(U_f\) is exactly \(H^{3}(T_f\times E)^{\operatorname{diag} \mu _{3}}\). All graph and exceptional boundaries are included by the transfer proof. This is an algebraic support construction, not an inference from a Hodge-theoretic half twist.

## 3A.3 Contracting the elliptic factors

Construct \(D_f\) and \(D_g\) as above. Their product has dimension four in \((T_f\times E)\times (T_g\times E)\). Intersect with the pullback of a general translated diagonal \(\Delta _a\subset E\times E\) and project to \(T_f\times T_g\). This intersection has dimension at most three. To see properness directly, apply the difference map \(E\times E\to E\) to each of the finitely many components of \(D_f\times D_g\). A general value either avoids its image or has fibers of dimension one less. The required translation can therefore be selected by a finite dimension test over a finite extension.

Translation acts trivially on cohomology, so cup product with \([\Delta _a]\) followed by pushforward contracts the elliptic factors through their intersection pairing:

\[
\begin{gathered}
(U_f\otimes U_g)(1) \to  [V_f\otimes V_g]^{\operatorname{diag} \mu _{3}}.
\end{gathered}
\]

This sends \(H^{6}\) of the sixfold to \(H^{4}\) of the fourfold: cup product adds two degrees and projection along \(E\times E\) removes four. Its image is supported on the proper projection of the three-dimensional intersection.

Over \(\mathbb C, U_f\) is the sum of \(V_{f,\zeta }\otimes H^{1}(E)_{\zeta ^{2}}\) and \(V_{f,\zeta ^{2}}\otimes H^{1}(E)_\zeta \). The two elliptic eigenspaces are one-dimensional, and their opposite pairing is nonzero by Poincaré duality. Contraction therefore surjects onto \(V_{f,\zeta }\otimes V_{g,\zeta ^{2}}\) and \(V_{f,\zeta ^{2}}\otimes V_{g,\zeta }\), exactly the invariant tensor. All operations and the diagonal class are rational, so the resulting support statement descends.

Now compare quotients. On \(X_{0}\cdot Y_{0}\ne 0\) write \(x_i=X_i/X_{0}, y_i=Y_i/Y_{0}\) and \(t=Y_{0}/X_{0}\). Then

\[
\begin{gathered}
f(1,x)+t^{6}g(1,y)=0,       \tau (t)=-t.
\end{gathered}
\]

The quotient field has \(r=t^{2}\) satisfying \(r^{3}=-f/g\). On \(T_f\times T_g, u^{3}=f\) and \(v^{3}=g\), and the diagonal invariant \(r=-u/v\) satisfies the same equation. Adjoining \(v\) recovers the degree-three extension, so these are the entire invariant fields. Hence \(X/\tau \) is birational to \((T_f\times T_g)/\operatorname{diag} \mu _{3}\).

Künneth, the vanishing of \(H^{1}\) and \(H^{3}\) of the triple planes, and their invariant hyperplane classes give

\[
H^{4}(T_f\times T_g)^{\operatorname{diag} \mu _{3}} = \mathbb Q(-2)^{3} \oplus  [V_f\otimes V_g]^{\operatorname{diag} \mu _{3}}.
\]

The Tate terms are algebraic and the preceding contraction supports the tensor term. Transfer first to a smooth model of the quotient, then back to \(X/\tau \) and \(X\). This supports all \(H^{4}(X)^\tau \) and proves the split theorem. The support-to-certificate theorem and higher-pole reduction of Chapter 3 then give legal certificates at every positive pole order. No Hodge conjecture for abelian varieties enters this proof. ∎

The [quadratic-net theorem](#technical-information/quadratic-nets) has different coefficient hypotheses. A ternary sextic expressible as a cubic in three quadratic forms belongs to a family of dimension at most \(9+10=19\): nine parameters for their span in \(\operatorname{Gr}(3,6)\), and ten for the cubic. All ternary sextics form a 28-dimensional space. The split theorem therefore covers general pairs \(f,g\) outside both orientations of the quadratic-net family.

### Involution-stable ternary decompositions

The same theorem holds whenever \(F=p(U)+q(V)\) for complementary three-dimensional subspaces \(U,V\) preserved by \(\tau \). If all three negative eigendirections lie in one summand, this is the theorem just proved. Otherwise their multiplicities are one and two, after exchange of the summands. The normal form is \(p(X_{0},X_{1},Y_{0})+q(X_{2},Y_{1},Y_{2})\). Global invariance forces \(p\) to be even in \(Y_{0}\) and, by its even total degree, \(q\) to be even in \(X_{2}\). Divisor support is therefore a direct corollary of the [two-reflection theorem](#technical-information/weighted-threefolds).

## 3A.4 When the involution swaps the blocks

Now let \(F_f(X,Y)=f(X+Y)+f(X-Y)\), with arbitrary smooth ternary \(f\). Under \(U=X+Y,V=X-Y\), the global involution becomes the block swap. It is not the block-sign involution of the split theorem.

Introduce \(S_{6}=\{u^{6}=f(z)\}\subset \mathbb P^{3}\) and \(\delta (z,u)=(z,\eta u)\), where \(\eta \) is a primitive sixth root. Put \(H_k=(H^{2}(S_{6},\mathbb C)_{\mathrm{prim}})_{\delta^*=\eta^k}\) for \(1\le k\le 5\). The surface Jacobian ring is \(R_f\otimes k[u]/(u^{5})\), where

\[
\begin{gathered}
\operatorname{Hilb}(R_f,t)=(1+t+t^{2}+t^{3}+t^{4})^{3}.
\end{gathered}
\]

The surface residue volume contributes \(\eta \), so \(u^{k-1}\) has character \(\eta ^{k}\). The three Hodge pieces occur in total Jacobian degrees 2,8,14. Reading the coefficients of \(R_f\) at degrees \(2-(k-1), 8-(k-1), 14-(k-1)\) gives

| \(k\) | \((h^{2,0},h^{1,1},h^{0,2})\) | Rank |
| --- | --- | ---: |
| 1 | (6,15,0) | 21 |
| 2 | (3,18,0) | 21 |
| 3 | (1,19,1) | 21 |
| 4 | (0,18,3) | 21 |
| 5 | (0,15,6) | 21 |

This uses the weighted Griffiths–Steenbrink residue grading stated in Chapter 3. The order-two summand \(H_{3}\) is rational and is the pullback of \(V_{2}=H^{2}(S_{2})_{\mathrm{prim}}\) from the K3 double plane \(S_{2}=\{w^{2}=f\}\subset \mathbb P(1,1,1,3)\), via \(w=u^{3}\).

### The algebraic split decomposition and its boundaries

Choose \(\alpha \) with \(\alpha ^{6}=-1\) and \(\alpha ^{2}=\eta \). The map

\[
\begin{gathered}
\Phi :S_{6}\times S_{6} \dashrightarrow  \{f(U)+f(V)=0\},\\
((z,u),(z',v)) \mapsto  [v\cdot z:\alpha\cdot u\cdot z']
\end{gathered}
\]

has generic fibers the diagonal \(\mu _{6}\)-orbits. Its indeterminacy locus is \(C\times C\), where \(C=\{f=0\}\). Blow up that smooth codimension-two center. The map extends, and the diagonal action on the blowup has smooth quotient \(B\). Locally on the chart \(v=u\lambda \), the action sends \(u\) to \(\eta u\) and fixes \(\lambda \). Eliminating \(u^{6}=f(z)\) identifies the quotient chart with \(f(z')=\lambda ^{6}f(z)\); the induced map is \([\lambda z:\alpha z']\). This is a blowup chart of the target along its pure-block copy of \(C\). The chart \(u=v\lambda '\) gives the other copy. Thus \(B\) is the blowup of the split fourfold along its two disjoint pure-block curves. This is the split blowup construction of [Shioda–Katsura, Theorem 1.7 and Remark 1.10](https://www.jstage.jst.go.jp/article/tmj1949/31/1/31_1_97/_pdf); the chart description shows why it applies to arbitrary smooth \(f\).

The blowup formula now accounts for all summands. Blowing up \(S_{6}\times S_{6}\) adds \(H^{2}(C\times C)(-1)\) in degree four; the diagonal group acts trivially on this addition. Künneth gives two Tate directions and \((H^{1}(C)\otimes H^{1}(C))(-1)\). The invariant \(H^{4}\) of the original product contributes three Tate directions and its primitive invariant tensor. On the other side, each pure-block \(C\) has codimension three in the fourfold, so its blowup adds \(H^{2}(C)(-1)\) and \(H^{0}(C)(-2)\), two Tate directions per curve. Cancelling these four algebraic summands leaves

\[
\begin{gathered}
H^{4}(\{f(U)+f(V)=0\})_{\mathrm{prim}} \cong  [H^{2}(S_{6})_{\mathrm{prim}}\otimes H^{2}(S_{6})_{\mathrm{prim}}]^{\operatorname{diag} \mu _{6}}\\
\oplus  [H^{1}(C)\otimes H^{1}(C)](-1).
\end{gathered}
\]

The maps and projectors are algebraic: they are made from the blowup maps, finite averaging, hyperplane projectors and the projective-bundle formula. The joining term is supported on the joining divisor swept out by lines connecting points of the two copies of \(C\); it is the image of the exceptional \(\mathbb P^{1}\)-bundle over \(C\times C\). This also identifies, rather than discards, the boundary contribution.

The block swap lifts to \(j=(\delta^{-1},\operatorname{id})\circ\operatorname{flip}\), since \(\Phi \circ j\) is the swap of \(\Phi \) after multiplication by \(\alpha \). Its square is \((\delta ^{-1},\delta ^{-1})\), trivial on the diagonal quotient. On \(H_k\otimes H_{6-k}\), pullback by \(j\) is \(\eta ^{-k}\) times the tensor flip. At \(k=3\) it is minus the flip. Therefore the fixed K3 contribution is \(\Lambda ^{2}V_{2}\). On the joining term, the factor exchange on \(H^{1}(C)\otimes H^{1}(C)\) has the graded sign \(-1\), so its fixed part is \(\Lambda ^{2}H^{1}(C)(-1)\). The exterior square, rather than a symmetric square, is forced by these signs.

## 3A.5 The second elliptic companion and the supported ranks

The triple-plane construction already supports the pair \(H_{2}\otimes H_{4}\) and \(H_{4}\otimes H_{2}\): pull back the support along \(S_{6}\to T_f, u\mapsto u^{2}\). For the primitive sixth-root pair, use

\[
\begin{gathered}
E_{23}=\{a^{2}+b^{3}+c^{6}=0\} \subset  \mathbb P(3,2,1),\\
\epsilon (a,b,c)=(a,b,\eta\cdot c),\\
W_{23,f}=\{f(z)+s^{2}+t^{3}=0\} \subset  \mathbb P(1,1,1,3,2).
\end{gathered}
\]

The holomorphic differential \(\mathrm db/a\) on \(c=1\) transforms by \(\eta \). The homogeneous map

\[
\begin{gathered}
S_{6}\times E_{23} \dashrightarrow  W_{23,f},\\
((z,u),(a,b,c)) \mapsto  [c\cdot z:u^{3}\cdot a:u^{2}\cdot b]
\end{gathered}
\]

satisfies the equation because substitution gives \(u^{6}(c^{6}+a^{2}+b^{3})\). On \(c=1\), adjoining \(u\) with \(u^{6}=f\) recovers \(a=s/u^3,b=t/u^2\); the map is the diagonal \(\mu _{6}\) quotient of degree six.

The cone gradient \((\nabla f,2\cdot s,3\cdot t^{2})\) has no nonzero critical zero. The ambient singularities are the isolated weight-three and weight-two vertices, both excluded by the equation. Where \(s,t\) are both nonzero their weights are coprime, so the stabilizer is trivial. Thus \(W_{23,f}\) is smooth. Adjunction gives \(-K=\mathcal O(2)\), and \(\mathcal O(1)\) is an ample line bundle, so this is a smooth Fano threefold.

Chapter 3 therefore constructs support for \(H^{3}(W_{23,f})\), and quotient transfer supports \([(H_{1}\oplus H_{5})\otimes H^{1}(E_{23})]^{\operatorname{diag} \mu _{6}}\). The other characters pair with no elliptic eigenspace. The same translated-diagonal intersection and nonzero opposite pairing as in §3A.3 then support both \(H_{1}\otimes H_{5}\) and \(H_{5}\otimes H_{1}\). This includes the whole required tensor, not merely its leading Hodge piece.

The swap fixes one copy of each paired tensor. Multiplying the Hodge triples above, and using \(\operatorname{genus}(C)=10\) for its exterior square, gives the complete invariant decomposition:

| Invariant summand | Rank | \((h^{3,1},h^{2,2},h^{1,3})\) | Support |
| --- | ---: | --- | --- |
| Primitive sixth-root pair | 441 | (90,261,90) | Second elliptic companion |
| Primitive third-root pair | 441 | (54,333,54) | Triple-plane companion |
| Joining-curve exterior square | 190 | (45,100,45) | Joining divisor |
| K3 exterior square \(\Lambda ^{2}V_{2}\) | 210 | (19,172,19) | Conditional on algebraicity of the Kuga–Satake correspondence |

For example, \(\Lambda ^{2}V_{2}\) has middle dimension \(1\cdot1+\binom{19}{2}=172\), and \(\Lambda ^{2}H^{1}(C)\) has extreme dimensions \(\binom{10}{2}=45\). The supported primitive part has rank 1072 and Hodge numbers (189,694,189). Adding the ambient class gives rank 1073. The full primitive numbers are (208,866,208). No generic Picard-rank assumption is used; additional algebraic K3 classes simply make additional exterior-square terms already supported.

### A polynomial test for the constructed part

For a globally \(Y\)-odd \(A\) of degree \(6\cdot q\), set \(\widehat{A}(U,V)=A((U+V)/2,(U-V)/2)\). It is antisymmetric under the block swap. Let \(P_{0}\) retain its monomials whose total \(V\)-degree is divisible by six. Then

\[
\begin{gathered}
P_{0}\widehat{A}=0  \Longrightarrow   \text{the residue target has the constructed divisor support.}
\end{gathered}
\]

To prove the test, use \(h(U,V)=(U,\eta V)\). A monomial of \(V\)-degree \(b\) has residue character \(\eta ^{b+3}\), since the three-coordinate volume contributes \(\eta ^{3}\). Under \(\Phi , h\) lifts to \((\delta ,\operatorname{id})\). The K3 summand has character \(\eta ^{3}\), so it receives exactly the terms with \(b\equiv 0\) mod 6. The other characters lie in the supported summands above. All finite-group actions commute with residue and pole reduction, so this is a test on the full class at arbitrary \(q\), not merely on its leading associated-graded term.

At \(q=1\) the excluded terms are just \(B(U)-B(V)\), where \(B(U)=\widehat{A}(U,0)=2^{-6}A(U,U)\). Thus \(P_{0}\widehat{A}=0\) is equivalent to \(A(X,X)=0\). There are 198 mixed antisymmetric sextic monomials; nine independent mixed Jacobian directions are \(f_i(U)V_j-f_i(V)U_j\). The partials form a regular sequence, so they have no degree-one syzygies. The image dimension is therefore \(198-9=189\), matching the supported (3,1) count. For \(q>1\), intermediate bidegrees such as (6,6) can occur, and \(A(X,X)=0\) alone is not the stated test.

## 3A.6 An algebraic Kuga–Satake criterion

**Exterior-power theorem.** If a projective K3 surface \(S\) has an algebraic Kuga–Satake correspondence, then \(\Lambda ^{r}H^{2}(S)\subset H^{2\cdot r}(S^{r})\) is supported in codimension at least \(r-1\) for every \(r\ge 1\). In particular, the criterion supports \(\Lambda ^{2}V_{2}\) and completes all targets on \(F_f\) whenever it applies to its double plane.

Here algebraicity means algebraicity of the standard Clifford embedding, not merely the existence of a Kuga–Satake Hodge structure. We use the following classical input. For \(T=H^{2}(S)_{\mathrm{tr}}\) and a nonisotropic \(e\in T\), the Kuga–Satake variety \(A\) has \(W=H^{1}(A)=C^{+}(T)\), and

\[
\begin{gathered}
j:T(1) \to  \operatorname{End}(W),       j(v)(w)=v\cdot w\cdot e
\end{gathered}
\]

is a Hodge embedding. A polarization identifies \(\operatorname{End}(W)(-1)\) with \(W\otimes W\subset H^{2}(A\times A)\). This precise model is stated in [Floccari, §5.2](https://www.cambridge.org/core/journals/compositio-mathematica/article/sixfolds-of-generalized-kummer-type-and-k3-surfaces/F6E8A0F77300183F77DADC8F699B2BAE). Standard algebraic polarizations and projectors for surfaces and abelian varieties will be used below; the relevant semisimplicity consequence is explained in that paper's Remark 5.5.

**Clifford calculation.** Left and right multiplication commute, so

\[
\begin{gathered}
j(v_{1})\cdots j(v_{r})=L_{v_{1}\cdots v_{r}}R_{e^{r}}.
\end{gathered}
\]

Antisymmetrize in \(v_{1},\ldots ,v_{r}\). The Clifford symbol map \(\operatorname{Alt}:\Lambda ^{r}T\to C(T)\), sending a wedge to \(\frac{1}{r!}\sum_\pi\operatorname{sign}(\pi)v_{\pi(1)}\cdots v_{\pi(r)}\), is injective: in an orthogonal basis its distinct increasing products form part of the Clifford basis. The resulting operator is \(J_r=L_{\operatorname{Alt}}R_{e^{r}}\). If \(r\) is even, \(e^{r}\) is a nonzero scalar and left multiplication on \(C^{+}\) is faithful. If \(r\) is odd, evaluation at 1 gives a nonzero scalar times \(\operatorname{Alt}\cdot e\), also injective because \(e\) is invertible. Consequently

\[
\begin{gathered}
J_r: \Lambda ^{r}T(r-1) \hookrightarrow  H^{2}(A\times A)
\end{gathered}
\]

is injective. For \(r=2\), it is the commutator \([j(v),j(w)]=q(e)L_{v\cdot w-w\cdot v}\); antisymmetrization removes the scalar contraction.

**Algebraicity and the support dimension.** Assume \(j\) is algebraic. Its external products, the contractions composing endomorphisms and the antisymmetrizer are algebraic, so \(J_r\) is induced by a cycle \(\Gamma \in \operatorname{CH}^{r+1}(S^{r}\times B)_\mathbb Q\) with \(B=A\times A\). The codimension is forced by the degree change \(H^{2\cdot r}\to H^{2}\). These operations need no Hodge conjecture for arbitrary powers of \(A\). The projector onto \(H^{1}(A)\) is a polynomial in a multiplication-by-\(n\) graph, and the polarization pairing and its inverse come from the polarization isogeny. For \(S\), the degree-two projector comes from the diagonal and point classes, and the transcendental projector subtracts the Néron–Severi projector formed using the inverse intersection matrix. Permutation graphs supply the exterior-power projector.

Choose a smooth complete-intersection surface \(\Sigma \subset B\). Weak Lefschetz makes \(H^{2}(B)\to H^{2}(\Sigma )\) injective, so the restricted correspondence still embeds \(\Lambda ^{r}T(r-1)\) into \(H^{2}(\Sigma )\). Its polarization adjoint, followed by the algebraic exterior-power projector, is an algebraic correspondence \(\Sigma \to S^{r}\) surjecting onto \(\Lambda ^{r}T\). To check surjectivity, compose the injection with its adjoint: on this polarized Hodge structure the resulting Gram operator is nondegenerate. Its inverse, if a retraction is desired, is a rational polynomial in that operator by Cayley–Hamilton. The required polarization on \(H^{2}(\Sigma )\) is algebraic by the Lefschetz decomposition for a surface; the one on \(\Lambda ^{r}T\) is induced by the tensor product of the K3 polarizations. Thus taking this adjoint does not assume an algebraicity conjecture on \(S^{r}\).

The adjoint cycle has codimension \(r+1\) in \(\Sigma \times S^{r}\). Its support has dimension at most \(2+2\cdot r-(r+1)=r+1\); its proper projection to \(S^{r}\) has codimension at least \(r-1\) and supports the image. Terms in \(\Lambda ^{r}H^{2}(S)\) involving \(p\) Néron–Severi factors acquire \(p\) more support codimensions from products with curves; the remaining \(\Lambda ^{r-p}T\) contributes \(r-p-1\). The entirely algebraic term has codimension \(r\). This proves the theorem for the full \(H^{2}(S)\). ∎

### An unconditional order-three family

We use one external algebraicity theorem: a K3 surface with a non-symplectic automorphism of order three whose fixed locus contains a curve has algebraic Kuga–Satake correspondence. This is [Bolognesi–Laterveer, introduction's corollary, Theorem 4.4 and §6](https://arxiv.org/html/2310.11981). Their theorem supplies the algebraic cycle; its proof is not replaced here by the abstract Clifford calculation.

Let

\[
\begin{gathered}
f(z_{0},z_{1},z_{2})=g_{6}(z_{0},z_{1})+z_{2}^{3}g_{3}(z_{0},z_{1})+a z_{2}^{6}
\end{gathered}
\]

define a smooth plane sextic. On \(S=\{w^{2}=f\}\), the automorphism \(z_{2}\mapsto \zeta _{3}z_{2},w\mapsto w\) multiplies the holomorphic two-form by \(\zeta _{3}\). Its fixed locus contains \(z_{2}=0\), the genus-two curve \(w^{2}=g_{6}(z_{0},z_{1})\). Smoothness forces \(a\ne 0\) and \(g_{6}\) squarefree, so this fixed curve is smooth. The external theorem applies, and the exterior-square argument supports the entire invariant fourth cohomology of the polarized-split fourfold \(F_f\). The support-to-certificate theorem then applies at every positive pole order.

For completeness, smoothness is equivalent to \(a\ne 0\) and squarefreeness of both \(g_{6}\) and \(\Delta=g_3^2-4\cdot a\cdot g_6\). On \(z_{2}=0\), the criterion is exactly that \(g_{6}\) have no repeated root. Away from \(z_{2}=0\) put \(t=z_{2}^{3}\). A singular zero satisfies \(t=-g_{3}/(2\cdot a), \Delta =0\) and \(d\Delta =0\). Conversely, a repeated root of \(\Delta \) with \(g_{3}\ne 0\) yields such a nonzero \(t\) and a singular point. If \(g_{3}\) vanishes at that root, \(g_{6}\) has a repeated root already. The point [0:0:1] is excluded when \(a\ne 0\) and singular when \(a=0\). This proves the criterion.

There is a direct boundary to the successful elliptic trick. The double-plane involution acts by \(-1\) on the K3 transcendental cohomology. For any curve with nonzero anti-invariant \(H^{1}\), its anti-invariant \(H^{1,0}\) is also nonzero. The diagonal invariant tensor therefore contains \(H^{2,0}(S)\otimes H^{1,0}(C)_-\). A smooth quotient model then has a holomorphic three-form and cannot be uniruled. The third- and sixth-root companion selections avoid this piece; the K3 exterior square requires its antisymmetry to enter a larger correspondence, as above.
