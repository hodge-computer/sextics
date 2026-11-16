# Mixed polar: balanced first variation and a Jacobian primitive

This construction is a nonconstructive proof of the certificate existence
statement for the fixed `mixed-polar` instance, with \(q=1\) and
\(A=X_0X_1X_2Y_0Y_1Y_2\). It uses a finite algebraic extension, polynomial
integration, normalized trace, and homogeneous clearing. It does not output
explicit denominator or numerator polynomials.

The proof uses the
maintained `TransitiveCubic`, `PolynomialCurves`, `ResidueTransport`, and
`HoldoutCover` libraries. Their attribution to `fqlx`,
`hodgepodgeconjecture`, `HeadOfNaps`, and the Lean/mathlib contributors is
retained. The accepted mixed-biweight and cycle-three constructions supply
the polynomial-family and residue-transport architecture. The new inputs
are the reverse-edge shear, the balanced first variation, the exact
mixed-polar Jacobian model and incidence seed, and their physical binding.
Earlier bounded denominator calculations by `1337isnot1337` in the
[instance discussion](https://github.com/hodge-computer/sextics/discussions/58)
are compatible with this unrestricted existence argument.

## The exact cubic quotient

Work in the function field of the fixed sextic. On the indicated open
chart put

$$
v=Y_0/X_0,\quad c_1=(Y_1/X_1)/v,\quad c_2=(Y_2/X_2)/v,
\quad R=X_2^2,\quad x=X_0^2/R,\quad y=X_1^2/R.
$$

All physical coordinate denominators are nonzero in this field. Direct
substitution gives \(F=R^3U\) and \(A=c_1c_2v^3R^3xy\), where

$$
U=ax^3+by^3+cz^3+dx^2y+ey^2z+fxy^2,\qquad z=1,
$$

$$
(a,b,c,d,e,f)=
(1+v^6,1+c_1^6v^6,1+c_2^6v^6,c_1v^2/2,c_1c_2v^2/2,c_1^3v^4/3).
$$

Adjoin a root \(k\) of \(3ak^2+2dk+f=0\). Both \(a\) and
\(d^2-3af\) are proved nonzero on the exact physical field. The determinant-one
substitution \(x=X+ky\) changes the cubic to

$$
aX^3+b'y^3+cz^3+d'X^2y+ey^2z,
\quad b'=b+ak^3+dk^2+fk,\quad d'=d+3ak,
$$

with \((d')^2=d^2-3af\ne0\). This is precisely the maintained transitive
cubic family, with its sixth coefficient zero.

## Covariants and the actual source

Use the maintained integral covariants \(H,\Theta,J\), normalized so that

$$
\xi=\Theta/H^2,\quad \eta=-J/(2H^3),\qquad
\eta^2=\xi^3+s_4\xi-s_6/4,\qquad
U_xD_y\xi=6\eta.
$$

The normalization follows the classical constructions of
[Tom Fisher](https://www.dpmms.cam.ac.uk/~taf1000/papers/g1hessians.pdf)
and [SageMath invariant theory](https://doc.sagemath.org/html/en/reference/polynomial_rings/sage/rings/invariants/invariant_theory.html),
as recorded in the shared library. Nonvanishing after the quadratic shear
is proved by a resultant in an explicit localization. At the exact point
\((2,2i,1-i,1+i,0,0)\), the shear equation specializes to \(3ak^2\) and
both diagonal covariants are nonzero. This proves nonvanishing for either
chosen root without evaluating arbitrary rational functions at that point.

The balanced source corresponds to the first variation \(xyz\). After the
base shear it is \((X+ky)yz\). An infinitesimal determinant-one shear
\(X\mapsto X-\lambda z/(2d')\) changes this to the coefficient variation

$$
\dot e=k,\qquad \dot f_{\mathrm{transitive}}=-3a/(2d').
$$

Its source is \((X+ky)y-U_X/(2d')\), which leaves the complete
second-normal expression unchanged. Dual numbers implement this variation
before specialization; no auxiliary parameter derivation is assumed on the
fixed field. The invariant derivatives descend to

$$
\dot s_4=(9abc-cdf)/2,\qquad \dot s_6=-4acde^2.
$$

Writing \(g=U_x\), \(g_\lambda=y-xyU_{xx}/g\), and
\(\dot b=-\dot s_6/4\), the resulting moving-map identity is

$$
\frac{g_\lambda}{g}=
\frac{\dot s_4\xi+\dot b}{2\eta^2}
-\frac g3 D_y\left(\frac{\dot\xi}{2\eta}\right).
$$

The physical \(X_0\)-normal is also retained. With
\(S=X_0F_{X_0}+Y_0F_{Y_0}\), the correction has sole nonzero tangent component
\(-AY_0/S\) in the \(Y_0\) slot. The complete physical normal source equals
\(c_1c_2v^3g_\lambda/g\) plus the residue divergence of this correction.

## A polynomial source on the Jacobian

Set \(T=Rv^6\), \(X_J=R^2\xi\), \(Y_J=R^3\eta\). Then

$$
E=Y_J^2-X_J^3-A_4X_J-B_6=0,
$$

where \(A_4=R^4s_4\) and \(B_6=-R^6s_6/4\) are polynomials of
degrees four and six in \((R,T)\). `JacobianModel.lean` gives the integral
equation \(432E\). For \(A_0=R+T\), \(B_0=R+c_1^6T\), \(C_0=R+c_2^6T\), the
polynomial numerator to integrate is

$$
P_J=\frac{c_1c_2C_0}{3456}
\left[(108A_0B_0-2c_1^4RT)X_J
+3c_1^3c_2^2R^2A_0T\right].
$$

Its exact pullback is
\(c_1c_2R^5(\dot s_4\xi+\dot b)/144\).

For polynomial curves on \(432E\), use \(T=s\) and degrees \((2,4,6)\) for
\((R,X_J,Y_J)\), fixing the constant terms of \(R,X_J\). The thirteen coefficient
equations in thirteen remaining coefficients have the following exact
solution modulo five at \((c_1,c_2,R(0),X_J(0))=(1,3,1,4)\):

$$
R=1+4s+4s^2,\quad
X_J=4+3s+2s^2+2s^3+4s^4,\quad
Y_J=1+s^2+s^4+s^6.
$$

The full incidence Jacobian is invertible; its explicit inverse and its
binding to the actual polynomial partial derivatives are kernel checked.
The shared arithmetic lifting theorem therefore supplies a generic
polynomial family over a finite coefficient extension. Independent endpoint
parameters prove dominance and finiteness over the Jacobian function field.
A polynomial normal with pairing one has nonzero normal/tangent
determinant. The shared polynomial-family residue bridge and normalized
finite trace give a rational residue primitive for every polynomial
numerator, in particular \(P_J\).

## Pullback, descent, and clearing

The physical-to-Jacobian coordinate determinant is checked directly,
including derivatives of the chosen algebraic shear in passive directions.
For the distinguished normal derivatives its density multiplier is

$$
\frac{F_{X_0}\det M}{2Y_J}=-144Rv^3.
$$

Piola pullback transports the Jacobian primitive. Adding the moving-map
correction and subtracting the normal-chart correction produces the exact
physical residue-divergence solution in the finite quadratic extension.
Normalized trace descends it to the original physical function field.

Finally, the exact sextic is irreducible: the maintained specialization
reduces its monic presentation to
\(X^6+((T+1)^6-1)\), and Eisenstein applies. Shared residue clearing therefore
gives a denominator coprime to \(F\). Shared homogeneous clearing uses the
proved degrees \(\deg F=\deg A=6\) to produce the required homogeneous
\(D,N_i,Q\). The quotient \(Q\) is unrestricted. `TargetBinding.lean` binds
these physical polynomials to the fixed target, and `Solution.lean`
exports the protected theorem `Submission.certificate`.
