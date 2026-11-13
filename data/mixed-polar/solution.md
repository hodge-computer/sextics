# A reverse-edge Jacobian construction for the balanced mixed-polar target

## Exact target and construction

This is an existence proof for the fixed triple
\[
\begin{aligned}
F={}&X_0^6+X_1^6+X_2^6+Y_0^6+Y_1^6+Y_2^6\\
&+\frac12X_0^3X_1Y_0Y_1
 +\frac12X_1^3X_2Y_1Y_2
 +\frac13X_0X_1Y_0Y_1^3,\\
A={}&X_0X_1X_2Y_0Y_1Y_2,\qquad q=1.
\end{aligned}
\]
It extends the cyclic and transitive Jacobian constructions to the cubic with a reversed first edge. The target-specific ingredients are its covariants and first variations, a nonsingular polynomial-curve incidence, and the transport of the balanced source. Arithmetic lifting, polynomial integration, finite trace, and homogeneous clearing use the maintained shared constructions.

The [formal contract](../../formal/README.md) is the algebraic certificate statement associated with Diamond's general GHC reformulation, as described in the [project overview](../../docs/overview.md). The submission proves that statement for the displayed triple and exports an existential theorem.

Work in the function field of the affine cone over \(F=0\). Put
\[
R=X_2^2,\qquad v=Y_0/X_0,\qquad
u=\frac{Y_1/X_1}{v},\qquad w=\frac{Y_2/X_2}{v},
\qquad x=X_0^2/R,\quad y=X_1^2/R.
\]
Then
\[
F=R^3U(x,y,1),\qquad A=uwv^3R^3xy,
\]
where
\[
U=ax^3+by^3+cz^3+dx^2y+ey^2z+fxy^2
\]
and
\[
\begin{aligned}
(a,b,c)&=(1+v^6,\;1+u^6v^6,\;1+w^6v^6),\\
(d,e,f)&=(uv^2/2,\;uwv^2/2,\;u^3v^4/3).
\end{aligned}
\]
[PhysicalCoordinates](PhysicalCoordinates.lean) establishes these identities in the exact residue field. [PhysicalField](PhysicalField.lean) proves irreducibility over \(\mathbb C\) by a monic Eisenstein specialization, constructs that field, and supplies its tangent derivations.

## The cubic, its Jacobian, and the balanced variation

Use the Weierstrass normalization
\[
\eta^2=\xi^3+I_4\xi+I_6,
\]
with
\[
I_4=-3acef+cd^2e
\]
and
\[
I_6=-\frac{27}{4}a^2b^2c^2-a^2ce^3
 +\frac92abc^2df-ac^2f^3-bc^2d^3
 +\frac14c^2d^2f^2.
\]
The covariants in [CubicCovariants](PolarCubicCovariants.lean), with their syzygy proved in [CubicSyzygy](PolarCubicSyzygy.lean) from the exact certificate data in [CubicIdentityData](PolarCubicIdentityData.lean), give
\[
\xi=\Theta/H^2,\qquad \eta=-J/(2H^3).
\]
Writing \(g=U_x(x,y,1)\), and letting \(D\) be the relative cubic derivation with \(Dy=1\), \(Dx=-U_y/g\), and all six cubic coefficients constant, their invariant-differential identity is
\[
gD\xi=6\eta,\qquad \frac{D\xi}{2\eta}=\frac3g.
\]
[CubicDifferential](PolarCubicDifferential.lean) proves the cleared differential identity. The polynomial coefficient identities are certified using the shared signed-expression and bounded-digit machinery specialized to the reverse-edge coefficient weights; [CubicEncoding](PolarCubicEncoding.lean) supplies the injective encoding. The required nonvanishing is established on a specified localization in [PhysicalChart](PhysicalChart.lean), using the exact point
\[
(X_0,X_1,X_2,Y_0,Y_1,Y_2)=(2,2i,1-i,1+i,0,0)
\]
from [CubicPoint](CubicPoint.lean). This gives a legitimate field-valued map with nonzero \(H,J,g\).

The balanced source calls for the first variation
\[
U_\tau=U+\tau xyz.
\]
In the implementation, `cubicJet` is \(U+2kxyz\), so this variation has \(k=\tau/2\). At \(z=1\), keep \(y\) and the coefficients fixed and move
\[
\dot x=-xy/g.
\]
This preserves the cubic equation to first order and gives
\[
\dot g=y-xyU_{xx}/g,\qquad
\dot I_4=\frac{9abc-cdf}{2},\qquad
\dot I_6=acde^2.
\]
[PhysicalCubicJets](PhysicalCubicJets.lean) computes these variations in dual numbers at the fixed equation. Both the curve identity and the invariant-differential identity hold to first order there. The shared moving-map identity consequently yields
\[
\frac{\dot g}{g}
 =\frac{\dot I_4\xi+\dot I_6}{2\eta^2}
  -\frac g3D\!\left(\frac{\dot\xi}{2\eta}\right).
\]
The derivative term accounts for the motion of the cubic-to-Jacobian map and becomes an explicit divergence correction below.

## Polynomial-curve incidence on the Jacobian

Set
\[
T=Rv^6,\qquad X=R^2\xi,\qquad Y=R^3\eta.
\]
The Jacobian equation becomes
\[
V=Y^2-X^3-A_4(R,T)X-B_6(R,T)=0,
\]
where
\[
A_4=R^4I_4\big|_{v^6=T/R},\qquad
B_6=R^6I_6\big|_{v^6=T/R}.
\]
The displayed coefficient formulas make \(A_4,B_6\) homogeneous polynomials of degrees four and six in \((R,T)\), over \(\mathbb C[u,w]\). [JacobianModel](JacobianModel.lean) uses the integral equation
\[
432V=432Y^2-432X^3-54\,\mathtt{a8}\,X-\mathtt{b256},
\qquad \mathtt{a8}=8A_4,\quad \mathtt{b256}=432B_6.
\]
The historical identifier `b256` is retained as an interface name; its scale here is 432. [PhysicalJacobianCoefficients](PhysicalJacobianCoefficients.lean) binds these coefficients to the physical cubic.

Over \(\mathbb F_5\), specialize \((u,w)=(2,1)\). The polynomial curve
\[
\begin{aligned}
R(T)&=1+3T+2T^2,\\
X(T)&=3+T+T^2+2T^3+2T^4,\\
Y(T)&=2+4T+T^2+3T^4+4T^5+4T^6
\end{aligned}
\]
satisfies the equation. For general polynomials of these degrees, fixing \(R(0)\) and \(X(0)\) leaves thirteen coefficients. Equating the coefficients of \(T^0,\ldots,T^{12}\) gives thirteen equations. The Jacobian in the coefficient order
\[
(R_1,R_2,X_1,X_2,X_3,X_4,Y_0,Y_1,\ldots,Y_6)
\]
has determinant 1 for \(V\), and determinant 2 for the integral equation \(432V\), modulo five. The latter factor is \(432^{13}=2^{13}=2\) in \(\mathbb F_5\).

[JacobianSeed](JacobianSeed.lean) proves the exact modular incidence and provides an explicit inverse of the integral coefficient matrix. [JacobianSeedBinding](JacobianSeedBinding.lean) identifies it with the derivatives of the equations defined in [JacobianIncidence](JacobianIncidence.lean).

[JacobianLifting](JacobianLifting.lean) retains \(u,w,R(0),X(0)\) as four independent parameters in the same integral incidence. The nonsingular special-fiber point supplies a nontrivial étale algebra. The shared arithmetic-lifting theorem then produces a solution over a finite separable extension of
\[
\mathbb C(u,w,R(0),X(0)).
\]
Thus the modular seed establishes a characteristic-zero family through an integral lifting argument.

The full coefficient matrix also provides a polynomial normal: the permitted coefficient variations pair with the gradient to span the polynomials of degree at most twelve, including 1. [JacobianFamily](JacobianFamily.lean) constructs the normal. Independent endpoint parameters give dominance, and the resulting function-field extension is finite; these steps are established in [JacobianGeometry](JacobianGeometry.lean), [JacobianEmbedding](JacobianEmbedding.lean), and [JacobianDimension](JacobianDimension.lean).

The shared polynomial-family bridge uses the polynomial normal and the invertible evaluation matrix to reduce the primitive construction to polynomial integration in the curve parameter. Coefficientwise antiderivatives exist in characteristic zero. The compatible derivations extend through the finite separable fields, and normalized finite trace commutes with those derivations, so it descends the resulting primitive. [JacobianResidue](JacobianResidue.lean) obtains a rational residue primitive for every polynomial source on this specified Jacobian model.

## The polynomial source and its physical transport

The source needed here is polynomial:
\[
P_J=\frac{uw}{144}(P_4X+P_6),
\]
where
\[
\begin{aligned}
P_4={}&(R+w^6T)
 \left[\frac92(R+T)(R+u^6T)-\frac{u^4}{12}RT\right],\\
P_6={}&\frac{u^3w^2}{8}R^2T(R+T)(R+w^6T).
\end{aligned}
\]
Indeed, \(P_4=R^3\dot I_4\), \(P_6=R^5\dot I_6\), and hence on the physical field
\[
P_J=\frac{uwR^5}{144}(\dot I_4\xi+\dot I_6).
\]
[JacobianSource](JacobianSource.lean) applies the polynomial-source primitive theorem to this exact expression.

For tangent derivations \(D_i\), write the residue divergence with normal \(h\) as
\[
\operatorname{Div}_h(z)
 =\sum_i\left(D_i z_i-z_i\frac{D_i h}{h}\right).
\]
Because \(P_J\) is independent of \(Y\), the Jacobian primitive has divergence \(P_J/(2Y^2)\) with normal \(2Y\). [PhysicalJacobianMap](PhysicalJacobianMap.lean) constructs the field embedding and proves compatibility of all tangent derivations. The residue-volume multiplier for this coordinate change is
\[
\frac{F_{X_0}}{2Y}\det M=-144Rv^3.
\]
The change-of-density Piola identity therefore pulls the Jacobian primitive back to a vector whose physical residue divergence is
\[
-uwv^3\frac{\dot I_4\xi+\dot I_6}{2\eta^2}.
\]

Two specified corrections complete the transport. First, [PhysicalCubicVolume](PhysicalCubicVolume.lean) constructs a divergence-free physical vector \(\mathcal V\) whose action on rational functions is \(uwv^3gD\). Adding
\[
\frac{\dot\xi}{6\eta}\,\mathcal V
\]
accounts for the derivative term in the moving-map identity.

Second, changing from the physical \(X_0\)-normal to the paired cubic normal produces the identity
\[
\frac{A_{X_0}}{F_{X_0}}
 -\frac{AF_{X_0X_0}}{F_{X_0}^2}
 =uwv^3\frac{\dot g}{g}+\operatorname{Div}_{F_{X_0}}(\mathcal C).
\]
[PhysicalNormalTransport](PhysicalNormalTransport.lean) proves it explicitly. In the passive coordinate order \((X_1,X_2,Y_0,Y_1,Y_2)\), the only nonzero component of \(\mathcal C\) is its \(Y_0\)-component,
\[
-\frac{(X_1X_2Y_1Y_2)X_0Y_0^2}
 {X_0F_{X_0}+Y_0F_{Y_0}}.
\]
Subtracting this vector gives the required physical residue-divergence equation. [PhysicalPrimitive](PhysicalPrimitive.lean) assembles the pulled-back primitive, the moving-map correction, and the normal-chart correction with these signs.

## Geometric support interpretation

The surface-fibration theorem in [Chapter 3](../../docs/03-geometric-support.md), applied to the paired-sign quotient in [Chapter 4](../../docs/04-known-locus-and-frontier.md), also proves divisor support for this balanced target. The following checks establish its hypotheses for the exact equation above.

The projective hypersurface is smooth over \(\mathbb C\). Rescale any nonzero point so that \(\max_i|Z_i|=1\), and take a coordinate of maximal modulus. Its Fermat partial derivative has modulus six, while the sum of the absolute values of the remaining terms is at most \(7/3\). That partial cannot vanish.

After quotienting by the paired signs and the global involution, write \(b=v^2\) and homogenize with \(r\). At \(u=w=1\), multiplying by six gives the surface \(S=\{H=0\}\subset\mathbb P^2_{x,y,z}\times\mathbb P^1_{b,r}\), where
\[
H=6(r^3+b^3)(x^3+y^3+z^3)
  +3br^2(x^2y+y^2z)+2b^2rxy^2.
\]
Here is a finite exact smoothness check. On \(r=1\), the three projective-coordinate charts have unit singular-locus ideals modulo five:

```python
import sympy as s

x, y, z, b = s.symbols("x y z b")
H = (6*(1+b**3)*(x**3+y**3+z**3)
     + 3*b*(x*x*y+y*y*z) + 2*b*b*x*y*y)
for fixed in (x, y, z):
    variables = [b] + [a for a in (x, y, z) if a != fixed]
    f = s.expand(H.subs(fixed, 1))
    assert list(s.groebner([f] + [s.diff(f, a) for a in variables],
                           *variables, modulus=5)) == [1]
```

At \(r=0\) the fiber is the smooth Fermat cubic in characteristic five, so the total surface is smooth there too. These charts exhaust the projective surface. Properness of the relative singular locus carries this certificate to characteristic zero; openness then gives smoothness over \(\mathbb C(u,w)\) for the unchanged mixed-polar equation.

Let \(\Gamma\) be generated by the paired coordinate signs and the diagonal action \(h\) with weights \((2,1,0,3,2,1)\) modulo six. These actions preserve the fixed equation. The balanced target \(A=\prod_iX_iY_i\) has \(h\)-weight nine, as does \(\Omega\), and is fixed by the paired signs. Therefore \(\operatorname{Res}(A\Omega/F^2)\) is \(\Gamma\)-invariant, and the sector theorem proves its divisor support. This argument requires no choice of Jacobian differential normalization. The covariant construction above realizes the same target through a polynomial curve family and trace. The geometric support argument does not enter its Lean proof.

## Certificate and attribution

[PhysicalClearing](PhysicalClearing.lean) applies the shared legal-denominator and homogeneous-extraction theorems. They yield a nonzero homogeneous polynomial \(D\), six homogeneous numerators \(N_i\) of degree \(\deg D+1\), and a polynomial \(Q\), with \(\gcd(D,F)=1\), satisfying
\[
AD^2-D\sum_iN_i\partial_iF
 +F\left(D\sum_i\partial_iN_i-\sum_iN_i\partial_iD\right)
 =F^2Q.
\]
[Solution](Solution.lean) binds the existential construction to the protected exact target. No expanded witness or denominator-degree bound is exported.

The Jacobian-map and moving-map architecture follows `hodgepodgeconjecture`'s [cycle-three construction](../cycle-three/solution.md). The transitive extension, arithmetic lifting, dominant polynomial families, finite trace, and certificate-clearing machinery build on `fqlx`'s [mixed-biweight construction](../mixed-biweight/solution.md), the [holdout construction](../holdout/solution.md), and their maintained shared modules. The modular-incidence organization follows the accepted [moving-branch specialization](../holdout-moving-branch/solution.md). The classical covariant normalization follows the invariant theory used in those constructions, including the work of Tom Fisher and the SageMath authors. Diamond's general equivalence supplies the GHC interpretation of the certificate problem; the proof here establishes the algebraic contract directly.

The reverse-edge covariants and jets, the mixed-polar polynomial source, the modular seed, and the target binding were prepared for `benediamond` with OpenAI ChatGPT and Codex assistance, using Mathlib and the Hodge Computer collaborators' shared constructions.

The parameterized cubic covariants and their first-order identities are the `PolarCubic` modules of this instance, beside the physical coefficient specialization, Jacobian incidence and balanced source transport.
