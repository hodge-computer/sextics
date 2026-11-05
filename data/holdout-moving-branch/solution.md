# A transitive Jacobian primitive for the moving branch

## Construction and scope

The extra term \(X_0^2\cdot Y_0^2\cdot Y_2^2/7\) breaks the Fermat-cover exchange used for the central holdout. It preserves the paired signs, however, and its squared-coordinate cubic belongs to the transitive family of `fqlx`'s [mixed-biweight construction](../mixed-biweight/solution.md). This proof applies that method to the new coefficient functions and supplies a new nonsingular polynomial-curve seed. It does not introduce a new general geometric mechanism.

Set
\[
R=X_2^2,\qquad v=Y_0/X_0,\qquad
c_i=\frac{Y_i/X_i}{v},\qquad x=X_0^2/R,\quad y=X_1^2/R.
\]
The exact sextic satisfies \(F=R^3U(x,y,1)\), where
\[
U=ax^3+by^3+cz^3+dx^2y+ey^2z+fx^2z,
\]
\[
(a,b,c)=(1+v^6,1+c_1^6v^6,1+c_2^6v^6),\qquad
(d,e,f)=(c_1v^2,c_1c_2v^2,c_2^2v^4/7).
\]
The target is \(A=v^3R^3x^3\). [PhysicalCoordinates](PhysicalCoordinates.lean) establishes the equation and the legality of its coordinate denominators.

The maintained [transitive-cubic library](../../formal/lean/HodgeComputer/Constructions/TransitiveCubic/README.md) supplies exact covariants \(H,\Theta,J\). On \(U=0\), the coordinates
\[
\xi=\Theta/H^2,\qquad \eta=-J/(2H^3)
\]
satisfy \(\eta^2=\xi^3+s_4\xi-s_6/4\) and the invariant-differential identity \(D_y\xi/(2\eta)=3/U_x\). Nonvanishing is proved on an explicit localization by evaluation at a point, rather than assumed for an arbitrary rational expression.

## Polynomial curves on the Jacobian

With \(T=Rv^6\), \(X=R^2\xi\), and \(Y=R^3\eta\), write
\[
V=Y^2-X^3-A_4(R,T)X-B_6(R,T),\qquad
A_4=R^4s_4,\quad B_6=-R^6s_6/4.
\]
The coefficients are polynomials of degrees four and six in \((R,T)\). [JacobianModel](JacobianModel.lean) uses the integral equation \(111132V=0\), with coefficient names `a8` and `b256` retained for compatibility: they mean \(4116A_4\) and \(111132B_6\), respectively.

At \(c_1=c_2=1\), the following polynomial curve lies on this equation modulo five:
\[
\begin{aligned}
R(T)&=1+2T^2,\\
X(T)&=4+4T+T^2+3T^3+T^4,\\
Y(T)&=1+3T^2+4T^4+2T^6.
\end{aligned}
\]
Fixing the endpoint coefficients \(R(0)=1\), \(X(0)=4\) leaves thirteen unknown coefficients. Their thirteen incidence equations have an invertible Jacobian over \(\mathbb F_5\). [JacobianSeed](JacobianSeed.lean) supplies an exact inverse; [JacobianSeedBinding](JacobianSeedBinding.lean) identifies that matrix with the derivatives of the actual incidence equations. The modular identity alone would not suffice without this nonsingularity.

Arithmetic lifting retains \(c_1,c_2,R(0),X(0)\) as independent parameters and yields a solution over a finite extension of their generic field. Independent endpoints, the curve parameter, and a polynomial normal provide the dominant family needed for polynomial integration. Normalized trace descends the resulting primitive. The construction thereby integrates polynomial sources on this specified Jacobian model; it makes no assertion about arbitrary rational differentials on an elliptic curve.

## Transport and certificate

Vary \(a=\alpha+v^6\) at \(\alpha=1\). The source \(-V_\alpha/(144R)\) is polynomial and is bound exactly in [JacobianSource](JacobianSource.lean). [PhysicalJacobianMap](PhysicalJacobianMap.lean) pulls its primitive back with residue-volume multiplier \(-144Rv^3\). The moving-map and normal-chart corrections in [PhysicalPrimitive](PhysicalPrimitive.lean) then recover the prescribed physical target.

Irreducibility, coordinate nonvanishing, finite descent, legal denominator clearing, and homogeneous extraction give a nonzero homogeneous \(D\), six numerators of degree \(\deg D+1\), and a polynomial \(Q\), with \(D\) relatively prime to \(F\), satisfying
\[
AD^2-D\sum_iN_iF_i+
 F\left(D\sum_i\partial_iN_i-\sum_iN_i\partial_iD\right)=F^2Q.
\]
[Solution](Solution.lean) binds this existential certificate to the protected target. No expanded witness or denominator-degree bound is exported.

## Attribution

The transitive-cubic construction and covariant identities are due to `fqlx`'s [mixed-biweight submission](https://github.com/hodge-computer/sextics/pull/170), building on `hodgepodgeconjecture`'s [cyclic construction](https://github.com/hodge-computer/sextics/pull/165). The classical invariant theory follows Tom Fisher and SageMath. Arithmetic lifting, polynomial integration, trace, residue transport, and homogeneous clearing use the maintained constructions of `fqlx` and the project collaborators, together with Mathlib. This coefficient specialization, its new modular seed, and the target binding were prepared for `benediamond` with OpenAI Codex assistance. The shared library avoids duplicating the covariant coefficient proofs in this submission.
