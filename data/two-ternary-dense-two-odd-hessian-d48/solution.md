# A rational certificate from ternary cubic covariants

This construction uses the splitting of the fixed sextic into two ternary blocks,

\[
F=P(X_0,X_1,Y_0)+Q_b(X_2,Y_1,Y_2),\qquad A=X_0^5\cdot Y_1.
\]

Each block is a cubic in the squares of its three variables. The useful structure is therefore the classical algebra of cubic covariants: Hessians, discriminants, and their polynomial identities. These provide a compact rational vector field even though its expanded numerator and denominator have thousands of terms.

The resulting denominator has degree \(55\), and the nonzero numerator components have degree \(56\). This is a non-strict certificate: its divergence has a nonzero multiple of \(F\), which is exactly what the divisibility problem allows. There is no claim that degree \(55\) is minimal.

## Reducing to a four-variable identity

Use the chart

\[
X_0=1,\quad X_1=x,\quad Y_0=y,\quad Y_1=\lambda,\quad X_2=\lambda\cdot r,\quad Y_2=\lambda\cdot z.
\]

With \(p(x,y)=P(1,x,y)\) and \(s(r,z)=Q_b(r,1,z)\), the equation and target become

\[
F=p+\lambda^6\cdot s,\qquad A=\lambda.
\]

The essential calculation is to construct a four-component rational field \(W\) satisfying

\[
\operatorname{div}(W)-\frac{4}{3\cdot p}\cdot\mathrm dp(W)
-\frac{2}{3\cdot s}\cdot\mathrm ds(W)=1.
\]

The unequal coefficients reflect the weights arising from the two blocks and the coordinate change. They are retained in the formal calculation. A generic divergence primitive would not by itself supply the required six-variable certificate.

The cubic covariants satisfy identities such as

\[
t^2=4\cdot H^3-27\cdot\delta\cdot f^2,
\]

where \(f\) is a cubic value, \(H\) its Hessian-related covariant, \(t\) a companion covariant, and \(\delta\) its discriminant. Differentiated identities and the weights \(0,2,4,6\) of the cubic coefficients make the cleared four-variable expression cancel. The proof establishes these small identities symbolically and then specializes them to the fixed coefficients; it does not assume a numerical cancellation of the large final expressions.

## Compact formulas for the witness

Write \(u=X_0^2\), \(w=Y_1^2\), and express the two blocks as

\[
P=a\cdot u^3+b\cdot u^2+c\cdot u+d,
\qquad
Q_b=\alpha\cdot w^3+\beta\cdot w^2+\gamma\cdot w+\delta_0,
\]

where

\[
\begin{aligned}
a&=14,& b&=7\cdot X_1^2+21\cdot Y_0^2,\\
c&=23\cdot X_1^4+12\cdot X_1^2\cdot Y_0^2+23\cdot Y_0^4,\\
d&=4\cdot X_1^6+39\cdot X_1^4\cdot Y_0^2+73\cdot X_1^2\cdot Y_0^4+8\cdot Y_0^6.
\end{aligned}
\]

The second block has

\[
\begin{aligned}
\alpha&=59,&\beta&=43\cdot X_2^2+61\cdot Y_2^2,\\
\gamma&=37\cdot X_2^4+47\cdot X_2^2\cdot Y_2^2+67\cdot Y_2^4,\\
\delta_0&=31\cdot X_2^6+41\cdot X_2^4\cdot Y_2^2+53\cdot X_2^2\cdot Y_2^4+71\cdot Y_2^6.
\end{aligned}
\]

Define the cubic discriminant polynomial

\[
\Delta(a,b,c,d)=b^2\cdot c^2-4\cdot a\cdot c^3-4\cdot b^3\cdot d-27\cdot a^2\cdot d^2+18\cdot a\cdot b\cdot c\cdot d.
\]

Let \(\Delta_P=\Delta(a,b,c,d)\), \(\Delta_Q=\Delta(\alpha,\beta,\gamma,\delta_0)\), and

\[
H_P=(b^2-3\cdot a\cdot c)\cdot u^2+(b\cdot c-9\cdot a\cdot d)\cdot u+c^2-3\cdot b\cdot d.
\]

Define \(H_Q\) by the same formula with \((a,b,c,d,u)\) replaced by \((\alpha,\beta,\gamma,\delta_0,w)\). The central denominator factor is

\[
G=H_P^3\cdot\Delta_Q\cdot Q_b^2-H_Q^3\cdot\Delta_P\cdot P^2,
\qquad D=36\cdot X_0\cdot Q_b\cdot G.
\]

To describe the six numerators, put

\[
P'=3\cdot a\cdot u^2+2\cdot b\cdot u+c,\qquad
Q_b'=3\cdot\alpha\cdot w^2+2\cdot\beta\cdot w+\gamma,
\]

where these primes mean derivatives in the squared variables. Introduce

\[
\begin{aligned}
h_0&=c^2-3\cdot b\cdot d,\\
T_Q&=3\cdot\bigl(2\cdot(\beta^2-3\cdot\alpha\cdot\gamma)\cdot w+\beta\cdot\gamma-9\cdot\alpha\cdot\delta_0\bigr)\cdot Q_b-2\cdot H_Q\cdot Q_b',\\
K_P&=(b\cdot c^2-6\cdot b^2\cdot d+9\cdot a\cdot c\cdot d)\cdot u+2\cdot c^3-9\cdot b\cdot c\cdot d+27\cdot a\cdot d^2,\\
L_P&=u\cdot(b\cdot u^2+2\cdot c\cdot u+3\cdot d),\\
U&=h_0\cdot H_P\cdot H_Q\cdot T_Q\cdot Q_b,\\
V&=K_P\cdot H_Q^3\cdot P^2-3\cdot\Delta_Q\cdot Q_b^2\cdot H_P^2\cdot L_P.
\end{aligned}
\]

Finally set

\[
R_P=6\cdot P-2\cdot u\cdot P',\qquad R_Q=6\cdot Q_b-2\cdot w\cdot Q_b',
\]

\[
R_0=P\cdot H_Q^3\cdot(R_P\cdot K_P-6\cdot u^3\cdot\Delta_P)
-18\cdot u\cdot\Delta_Q\cdot Q_b^2\cdot H_P^2\cdot(u\cdot c+3\cdot d),
\]

\[
R_1=R_0+2\cdot u\cdot Q_b'\cdot U.
\]

In the atlas variable order, the numerators and quotient are

\[
\begin{aligned}
N_0&=0,\\
N_1&=-6\cdot X_1\cdot Y_1\cdot Q_b\cdot V,\\
N_2&=X_2\cdot Y_1\cdot P\cdot R_1,\\
N_3&=-6\cdot Y_0\cdot Y_1\cdot Q_b\cdot V,\\
N_4&=P\cdot(Y_1^2\cdot R_0-X_0^2\cdot R_Q\cdot U),\\
N_5&=Y_2\cdot Y_1\cdot P\cdot R_1,\\
C&=-72\cdot X_0\cdot Y_1\cdot Q_b\cdot G\cdot R_0.
\end{aligned}
\]

These are literal polynomial formulas with rational coefficients. Their factored form is part of the proof strategy: it exposes the cancellation without repeatedly expanding the entire packet.

## Why the certificate equation holds

The four-variable field is rescaled by \(1/(18\cdot p\cdot s)\), lifted to the chart with coordinate \(\lambda\), and homogenized. The transport keeps track of the coordinate Jacobian \(\lambda^2\) and the normal component. Its divergence calculation retains the error proportional to \(F\).

The coordinate substitutions embed polynomial rings into rational function fields. Their derivative rules and injectivity are proved. After using the nonzero denominator and clearing fractions, the transported identities are polynomial equalities:

\[
\mathrm dF(N)=A\cdot D,\qquad
D\cdot\operatorname{div}(N)-\mathrm dD(N)=F\cdot C.
\]

Consequently, for the required pole parameter \(q=1\),

\[
A\cdot D^2-D\cdot\mathrm dF(N)
+F\cdot\bigl(D\cdot\operatorname{div}(N)-\mathrm dD(N)\bigr)
=F^2\cdot C.
\]

Thus \(v=N/D\) satisfies the exact divisibility condition. Requiring a zero quotient would discard this valid construction.

## Degrees and denominator admissibility over the complex numbers

The covariants \(H_P,H_Q\) have degree \(8\), the discriminants have degree \(12\), and the two blocks have degree \(6\). Hence \(G\) has degree \(48\), \(D\) has degree \(55\), each numerator is homogeneous of degree \(56\), and \(C\) has degree \(104\). The zero component \(N_0\) satisfies the homogeneous predicate as well. The homogeneous proofs are transported from rational to complex coefficients.

Admissibility is proved directly over \(\mathbb C\). Regard \(F\) as a polynomial in \(X_0\), with coefficients in the other five variables. Its leading coefficient is the nonzero constant \(14\). Specializing those other variables to \(1\) gives

\[
f(t)=14\cdot t^6+28\cdot t^4+58\cdot t^2+634.
\]

The same specialization sends \(D\) to an explicit degree-\(13\) polynomial \(d(t)\). The proof supplies rational polynomials \(u_0(t),v_0(t)\) and verifies

\[
u_0(t)\cdot f(t)+v_0(t)\cdot d(t)=1.
\]

This proves that the specialized polynomials are coprime even over \(\mathbb C\). Because the leading coefficient of \(F\) is a unit, the leading coefficients of any two factors of \(F\) are units too. Specialization therefore cannot erase the degree of a common factor. Any common divisor of \(F\) and \(D\) must have degree zero in \(X_0\), and its unit leading coefficient makes it a unit in the full polynomial ring. This establishes \(\operatorname{IsRelPrime}(F,D)\). A nonzero coefficient of \(d(t)\) separately proves \(D\ne0\).

## Correspondence with the Lean proof

`PExplicitWitnessDefinitions.lean` defines the factored witness above. The shared [binary-cubic modules](../../formal/lean/HodgeComputer/Constructions/BinaryCubic/README.md) prove the coefficient identities and radial cancellation; `PEllipticAmbientActualScalar` supplies the instance’s coefficient specialization. The shared [rational-field calculus](../../formal/lean/HodgeComputer/Constructions/RationalFields/README.md) supplies the residue and Euler corrections. The coordinate-transport modules and `PEllipticAmbientPolynomialBridge` recover the two polynomial equations. `PExplicitWitnessGrading` supplies the homogeneous degrees.

`PDenseP0.lean` transfers the identities to complex coefficients and proves complex coprimality by the specialization and Bézout argument just described. `Solution.lean` binds the resulting existence theorem to the protected atlas target. The proof concerns this fixed sextic and target; it does not establish the general sextic case or a minimal denominator degree.
