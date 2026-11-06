# A Jacobian primitive for the asymmetric mixed biweights

## Construction

Put \(R=X_2^2\), \(v=Y_0/X_0\),
\(c_1=X_0Y_1/(X_1Y_0)\), and \(c_2=X_0Y_2/(X_2Y_0)\).
The squared coordinates give the plane cubic
\[
U=ax^3+by^3+cz^3+dx^2y+ey^2z+fx^2z,
\]
where \(a=1+v^6\), \(b=1+c_1^6v^6\), \(c=1+c_2^6v^6\),
\(d=c_1v^2/2\), \(e=c_1c_2v^2/2\), and \(f=c_2v^4/3\).
Thus \(F=R^3U(X_0^2/R,X_1^2/R,1)\), with source \(A=v^3R^3x^3\).

The Hessian covariants give a map to the cubic's Weierstrass Jacobian.
Lean uses integral covariants scaled by \((3,9,27)\); the map coordinates
\(\xi=\Theta/H^2\), \(\eta=-J/(2H^3)\) retain their classical values.
[CubicSyzygy](../../formal/lean/HodgeComputer/Constructions/TransitiveCubic/Syzygy.lean) checks the defining identity, and
[CubicFieldDifferential](CubicFieldDifferential.lean) checks its differential.
With \(T=Rv^6\), the Jacobian coefficients are polynomials in \(R,T\).
The degree \((2,4,6)\) section in [JacobianSeed](JacobianSeed.lean) has an
invertible thirteen-variable incidence Jacobian modulo five.
Lifting this seed supplies a generically finite parameterization.
Polynomial integration and trace along a finite field extension produce the
required rational residue primitive.

## Certificate

[PhysicalPrimitive](PhysicalPrimitive.lean) transports that primitive back to
the exact sextic, including the moving-map and normal-chart corrections.
The irreducibility and nonvanishing conditions are established in
[PhysicalField](PhysicalField.lean) and the coordinate helpers.
Shared residue clearing and homogenization then give a nonzero homogeneous
denominator \(D\), six numerators \(N_i\) of degree \(\deg D+1\), and a
polynomial \(Q\), with \(\gcd(D,F)=1\), satisfying
\[
AD^2-D\sum_iN_iF_i+
 F\left(D\sum_i\partial_iN_i-\sum_iN_i\partial_iD\right)=F^2Q.
\]
[Solution](Solution.lean) binds this existential certificate to the protected
target. No explicit expanded witness is exported.

The construction adapts `hodgepodgeconjecture`'s
[cycle-three proof](../cycle-three/solution.md), including its classical
covariant normalization following Tom Fisher and the SageMath authors.
It uses the maintained lifting, trace, transport, and clearing constructions
of `fqlx` and the Hodge Computer collaborators, together with Mathlib.
Prepared for `fqlx` with OpenAI ChatGPT and Codex assistance.
