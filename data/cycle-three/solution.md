# A paired-sign cubic and its Jacobian residue primitive

## Statement and scope

This construction addresses the fixed cycle-three equation and the individual
source \(A=X_0^3Y_0^3\), with \(q=1\). The three cyclic couplings all retain
coefficient \(1/2\). The final theorem is the exact protected
`HodgeComputer.HasCertificate` statement in [Solution.lean](Solution.lean).

The argument proves existence of a legal homogeneous polynomial certificate.
It does not export a displayed polynomial witness or assert a particular
denominator degree. Its intermediate rational functions lie in the function
field of the original sextic. An auxiliary Jacobian supplies a primitive, and
explicit coordinate and first-variation identities transfer that primitive
back to the original source.

## The paired-sign cubic

Write \(p=(X_0,X_1,X_2,Y_0,Y_1,Y_2)\) for the images of the six coordinates
in the sextic function field. Set
\[
 R=p_2^2,\qquad v=p_3/p_0,\qquad
 c_1=(p_4/p_1)/v,\qquad c_2=(p_5/p_2)/v,
 \qquad x=p_0^2/R,\qquad y=p_1^2/R.
\]
Then the sextic equation is \(R^3U(x,y,1)=0\), where
\[
 U(x,y,z)=ax^3+by^3+cz^3+dx^2y+ey^2z+fz^2x
\]
and
\[
\begin{aligned}
 a&=1+v^6,& b&=1+c_1^6v^6,& c&=1+c_2^6v^6,\\
 d&=v^2c_1/2,& e&=v^2c_1c_2/2,& f&=v^2c_2/2.
\end{aligned}
\]
[PhysicalField.lean](PhysicalField.lean) proves irreducibility of the actual
sextic using a monic Eisenstein specialization. Consequently its quotient is
a domain. [PhysicalCoordinates.lean](PhysicalCoordinates.lean) and
[PhysicalChart.lean](PhysicalChart.lean) establish the coordinate identities
and nonvanishing needed to use this chart. These conditions are proved in the
function field; they are not extra hypotheses on the final theorem.

## Covariants and their exact identities

The integral covariants \(H,\Theta,J\) are specified in
[Covariants.lean](CyclicCubicCovariants.lean). Their normalization is fixed
throughout. Define
\[
\begin{aligned}
 s_4&=ae^2f+bdf^2+cd^2e,\\
 s_6&=27a^2b^2c^2+4a^2ce^3+4ab^2f^3+6abcdef
       +4bc^2d^3-d^2e^2f^2.
\end{aligned}
\]
On \(U=0\), the covariant identity is
\[
 J^2=4\Theta^3+4s_4\Theta H^4-s_6H^6.
\]
Thus
\[
 \xi=\Theta/H^2,\qquad \eta=-J/(2H^3)
 \quad\text{satisfy}\quad
 \eta^2=\xi^3+s_4\xi-s_6/4.
\]
The proof establishes the full polynomial syzygy, including the term divisible
by \(U\), in [Syzygy.lean](CyclicCubicSyzygy.lean). In particular, the
specialization to the physical field is not a numerical check at a selected
cubic.

The large polynomial identity is verified by an exact encoding argument.
[BivariateExpressions.lean](../../formal/lean/HodgeComputer/Constructions/PolynomialEncoding/BivariateExpressions.lean) proves the semantics of
the polynomial operations used to form its 190 coefficients. Each coefficient
has a fixed diagonal weight in the six parameters. At a fixed weight, the
exponents of \(a,b,c\) are determined by those of \(d,e,f\); the latter are
less than 19. [Kronecker.lean](CyclicCubicKronecker.lean) therefore proves
injectivity of their encoding with exponents \(1,19,361\). Signed expressions
are split into two polynomials with natural coefficients. A proved coefficient
bound makes evaluation at \(2^{42}\) injective on these polynomials.
[PolynomialDigitCheck.lean](../../formal/lean/HodgeComputer/Constructions/PolynomialEncoding/PolynomialDigitCheck.lean) proves this last step.
The coefficient files use kernel reduction to check the resulting finite
equalities and bounds. The syntax, grading, products, and evaluation bindings
are all proved in Lean; generated data are not trusted as an external oracle.

Let \(g=U_x\). The physical derivation \(D_y\) fixes \(R,v,c_1,c_2\), sends
\(y\) to 1, and sends \(x\) to \(-U_y/g\). The covariant differential identity
gives
\[
 \frac{D_y\xi}{2\eta}=\frac3g.
\]
See [PhysicalCubicTangent.lean](PhysicalCubicTangent.lean) and
[CubicFieldDifferential.lean](CubicFieldDifferential.lean). The nonvanishing of
\(g,H,J\), and hence of \(\eta\) and \(D_y\xi\), is proved separately.

## A polynomial primitive on the auxiliary Jacobian

Put
\[
 T=Rv^6,\qquad X=R^2\xi,\qquad Y=R^3\eta.
\]
The homogeneous coefficient polynomials `a8` and `b256` in
[JacobianModel.lean](JacobianModel.lean) give the equation
\[
 V=Y^2-X^3-\frac18 a_8(c_1,c_2,1,R,T)X
             -\frac1{256}b_{256}(c_1,c_2,1,R,T)=0.
\]
Their physical values are \(8R^4s_4\) and \(-64R^6s_6\), respectively.

The key existence result on this model is stronger than the one source needed
here: every polynomial source has a rational residue primitive.
[JacobianResidue.lean](JacobianResidue.lean) proves this via a polynomial family,
polynomial integration, and normalized finite trace.

The family has coordinate degrees \((2,4,6)\) in \((R,X,Y)\), with parameter
\(T\), and independent endpoint parameters \(R(0),X(0)\). Its thirteen unknown
coefficients satisfy thirteen integral coefficient equations. A nonsingular
seed over \(\mathbb F_5\), at \((c_1,c_2,R(0),X(0))=(2,3,1,3)\), is
\[
\begin{aligned}
 R(T)&=1+2T+4T^2,\\
 X(T)&=3+T+3T^2+4T^3+4T^4,\\
 Y(T)&=2+3T+3T^2+4T^3+4T^4+T^5+T^6.
\end{aligned}
\]
[JacobianSeedBinding.lean](JacobianSeedBinding.lean) binds the displayed
matrix and its checked inverse to the actual derivatives of the incidence
equations. The shared arithmetic lifting theorem then supplies a nonsingular
generic solution over a finite separable extension of
\(\mathbb C(c_1,c_2,R(0),X(0))\). This characteristic-changing step uses the
integral square-system theorem, not an inference that a single modular point
automatically lifts to characteristic zero.

The coefficient Jacobian also constructs a polynomial normal whose pairing
with the hypersurface gradient is 1. The retained endpoint parameters give
the required independence and finite function-field extension. Polynomial
integration constructs the primitive on the family; normalized finite trace
returns it to the Jacobian function field. These steps are developed in
[JacobianFamily.lean](JacobianFamily.lean),
[JacobianDimension.lean](JacobianDimension.lean), and
[JacobianNormal.lean](JacobianNormal.lean).

## First variation at the fixed coefficient

For the calculation only, replace \(a=1+v^6\) by \(a=\alpha+v^6\),
differentiate, and evaluate at \(\alpha=1\). A dot denotes this first
variation. This procedure leaves the submitted equation unchanged.

It is important that differentiation is not postulated as a derivation of the
already specialized function field. Instead,
[CubicJetCalculus.lean](CubicJetCalculus.lean) uses the dual-number ring
\(K[\epsilon]/(\epsilon^2)\), with
\[
 a_\epsilon=a+\epsilon,\qquad
 x_\epsilon=x-\epsilon x^3/g,
\]
and the other cubic coefficients and \(y\) fixed. It proves the cubic equation
and covariant identities in this ring. Their two components give the ordinary
identity and its first variation.

Writing \(a_W=s_4\), \(b_W=-s_6/4\), this yields the exact source relation
\[
 \frac{\dot g}{g}
 =\frac{\dot a_W\xi+\dot b_W}{2\eta^2}
  -\frac g3D_y\left(\frac{\dot\xi}{2\eta}\right),
 \qquad
 \dot g=3x^2-\frac{x^3U_{xx}}g.
\]
[PhysicalCubicJets.lean](PhysicalCubicJets.lean) proves this relation for the
actual physical map. The auxiliary polynomial source is
\(P_J=-V_\alpha/(144R)\), whose explicit polynomial form is in
[JacobianSource.lean](JacobianSource.lean). Its image in the physical field is
\[
 P_J=\frac{R^5}{144}(\dot a_W\xi+\dot b_W).
\]

## Transport to the original residue equation

Write \(F_i=\partial_iF\), with its image in the function field understood.
The physical tangent derivations are
\(\delta_i=\partial_{i+1}-(F_{i+1}/F_0)\partial_0\), for \(0\leq i<5\).
For a vector \(w\), the residue divergence with normal \(F_0\) is
\[
 \operatorname{div}_{F_0}(w)
 =\sum_i\delta_iw_i-\frac{\sum_iw_i\delta_iF_0}{F_0}.
\]

The matrix \(M_{ji}=\delta_i(T,c_1,c_2,R,X)_j\) is invertible.
[PhysicalJacobianCoordinates.lean](PhysicalJacobianCoordinates.lean) proves
its determinant and the exact residue-volume multiplier
\[
 \frac{F_0\det M}{2Y}=-144Rv^3.
\]
The inverse matrix supplies coordinate derivations. A characteristic-zero
degree-descent argument in [CoordinateIndependence.lean](../../formal/lean/HodgeComputer/Constructions/ResidueTransport/CoordinateIndependence.lean)
proves independence of the five passive coordinates. The monic irreducible
Jacobian equation then gives the function-field embedding.
[PhysicalJacobianMap.lean](PhysicalJacobianMap.lean) proves that this embedding
intertwines the tangent derivations. Piola transport of the Jacobian primitive
therefore has physical residue divergence
\[
 -v^3\frac{\dot a_W\xi+\dot b_W}{2\eta^2}.
\]

Set \(h=p_0F_0+p_3F_3\), \(h_1=p_1F_1+p_4F_4\), and
\(\lambda=p_3^3/(4p_0^5p_1^2p_2^2)\). The vector
\[
 W=(\lambda hp_1,0,-\lambda h_1p_3,\lambda hp_4,0)
\]
has zero residue divergence and acts on functions as \(v^3gD_y\).
Consequently adding \(\dot\xi W/(6\eta)\) supplies exactly the first-variation
correction. [PhysicalCubicVolume.lean](PhysicalCubicVolume.lean) proves both
identities for arbitrary rational functions.

There is also a normal-chart correction
\(C=-p_0^3p_3^4/h\), placed in the component for \(p_3\). It satisfies
\[
 \frac{A_0}{F_0}-\frac{AF_{00}}{F_0^2}
 =v^3\frac{\dot g}{g}
   +\operatorname{div}_{F_0}(0,0,C,0,0).
\]
Subtracting this vector completes the physical primitive. The full assembly
is [PhysicalPrimitive.lean](PhysicalPrimitive.lean).

## Clearing and homogeneity

The resulting vector has residue divergence equal to
\(-A_0/F_0+AF_{00}/F_0^2\). The shared residue-clearing theorem chooses a
common polynomial denominator and lifts the normal and divergence identities
from the quotient field. Irreducibility ensures the denominator can be chosen
relatively prime to \(F\). The shared homogeneous-certificate theorem then
extracts the required homogeneous data: a nonzero denominator \(D\), six
numerators of degree \(\deg D+1\), and a polynomial quotient for the cleared
defect. This permits a nonzero quotient, as required by the formal contract.

[PhysicalClearing.lean](PhysicalClearing.lean) carries out that final step.
The construction uses classical existence and finite trace, so no explicit
expanded \(D,N,Q\) is claimed or supplied. All nonvanishing, relative-primality,
degree, and divisibility obligations are part of the resulting certificate.

## Attribution and verification scope

The cubic invariant theory is classical. The normalization and research route
were informed by Tom Fisher's
[Testing Equivalence of Ternary Cubics](https://www.dpmms.cam.ac.uk/~taf1000/papers/testeqtc.pdf)
and the SageMath authors' implementation and documentation of
[classical invariant theory](https://doc.sagemath.org/html/en/reference/polynomial_rings/sage/rings/invariants/invariant_theory.html).
The explicit identities used here are proved in Lean rather than imported as
assumptions from those references.

The coefficient-incidence method, arithmetic lifting, polynomial-family
bridge, finite trace, Piola transport, residue clearing, and homogenization
build on the project's shared constructions, credited to `fqlx` and the
Hodge Computer collaborators. Mathlib supplies the underlying algebra.
The earlier discussion's bounded denominator exclusion by `rbajaj5` informed
the decision to pursue an existence construction; it is not a premise of this
proof. The contribution is prepared for `hodgepodgeconjecture` with substantial
OpenAI Codex assistance in the calculations, proof engineering, and writing.

The auxiliary all-polynomial-source theorem is broader than the single source
used here. This submission only claims the protected cycle-three certificate;
it does not claim the degree-twelve companion, a full Hodge-conjecture result,
or an explicit bounded-degree witness. Verification commands and actual run
results are recorded in the accompanying pull request.
