Over six complex variables \(X_0,X_1,X_2,Y_0,Y_1,Y_2\), consider a smooth sextic fourfold \(X\subset\mathbb P^5\) defined by a homogeneous sextic polynomial \(F(X_0,X_1,X_2,Y_0,Y_1,Y_2)\) invariant under the involution

\[
\iota:(X_0,X_1,X_2,Y_0,Y_1,Y_2)\mapsto(X_0,X_1,X_2,-Y_0,-Y_1,-Y_2).
\]
The involution \(\iota\) induces an action on \(X\), and so also on \(H^4(X,\mathbb Q)\). As noted by [Voisin](https://www.ms.u-tokyo.ac.jp/journal/abstract_e/jms220116_e.html), the Hodge substructure \(H\subset H^4(X,\mathbb Q)\) *fixed* by the induced action \(\iota^*\) has *Hodge coniveau* 1. Indeed, \(\iota^*\) acts as \(-1\) on the nowhere-vanishing Calabi–Yau form \(\omega\in H^{4,0}(X)\).

The generalized Hodge conjecture thus predicts that \(H\)’s *geometric coniveau* should also be 1; that is, there should exist a divisor \(Y\subset X\) such that

\[
H\subset\ker\left(H^4(X,\mathbb Q)\longrightarrow H^4(X\setminus Y,\mathbb Q)\right).
\]
This particular instance of the GHC is interesting in its own right. Further, as [Voisin](https://www.ms.u-tokyo.ac.jp/journal/abstract_e/jms220116_e.html) points out, if true for general smooth even \(F\), it would imply [Voisin’s conjecture](https://www.cmls.polytechnique.fr/perso/voisin/Articlesweb/symmetriccycles1.pdf) for K3 surfaces that are double covers of \(\mathbb P^2\) ramified over a sextic curve.

> **Parity convention.** In these coordinates, “even” and “odd” mean even and odd total degree in the three \(Y\) variables.

In a recent work, [Diamond](https://arxiv.org/abs/2603.29157) shows that the prediction of the GHC as regards \(H\subset H^4(X,\mathbb Q)\) is *equivalent* to a purely algebraic one. For \(F\) given as above—an even homogeneous sextic whose vanishing locus is smooth—is it true that, for each \(q\in\{1,2\}\) and each *odd* monomial \(A\) of degree \(6\cdot q\), there exists a vector field \(v=(v_0,\ldots,v_5)\) whose components are homogeneous *rational* functions of total degree \(6\cdot q-5\), and whose common denominator \(D\) is not divisible by \(F\), such that

\[
F^{q+1}\;\bigm|\;A-q\cdot\mathrm dF(v)+F\cdot\operatorname{div}(v)?
\]
Divisibility is interpreted in \(\mathbb C[X_0,X_1,X_2,Y_0,Y_1,Y_2]_{(F)}\).

This algebraic formulation makes divisor support accessible through rational differential forms and exact polynomial identities.

The book proves support on several complete coefficient families. [Chapter 3C](#technical-information/quadratic-nets) treats every smooth sextic \(F(X,Y)=G(X,Q_0(Y),Q_1(Y),Q_2(Y))\) obtained from three ternary quadrics: point-pair incidence combines a weighted Fano quotient with a family of Fano threefolds. This includes the three-reflection family through the diagonal net. The complementary [two-reflection theorem](#technical-information/weighted-threefolds) combines Fano quotients with norm-contact curves and includes the full \(4+2\) split family with binary block \((X_2,Y_2)\). [Chapter 4](#technical-information/known-locus) compares their coefficient spaces and treats further finite-symmetry families. The general even-sextic case remains open.
