# A rational norm of two contact factors
Take \(x=X_0\), \(y=X_1\), \(R=Y_0^2+Y_2^2\), and \(B=X_2\cdot Y_1\). The Hesse cofactor in \((x^2,y^2,-R/3)\) gives a quartic denominator over \(\mathbb Q\). Over \(\mathbb Q(\sqrt{-3})\), it splits into two conjugate quadratic factors \(Q_+,Q_-\).

This splitting suggests a logarithmic Hamiltonian
\[
h=\lambda_+\log Q_++\lambda_-\log Q_-,\qquad
v=B\left(\frac{\partial h}{\partial y}\partial_x-\frac{\partial h}{\partial x}\partial_y\right).
\]
Conjugate choices of residues make \(v\) rational over \(\mathbb Q\). The logarithms are a device for describing rational derivatives; no multivalued function enters the final certificate.

## Divergence is built into the mechanism
Hamiltonian fields in two variables have zero divergence because mixed partial derivatives commute. The multiplier \(B\) is independent of the active variables, so it preserves that property. Clearing the common denominator gives \(D\cdot\operatorname{div}N=N(D)\). The residues are selected so that \(v(F)=A\), equivalently \(N(F)=A\cdot D\).

A coefficient-system approach imposes both strict equations on a degree-four denominator. For the displayed specialization, the following parameter relations hold:
\[
t_2-\frac{t_3^2}{3}=0,\qquad t_3^3+1=0.
\]
The rational projective point is \((t_2,t_3,1)=(1/3,-1,1)\); the other two points are conjugate over \(\mathbb Q(\sqrt{-3})\).

## What is special about this fiber
The displayed target uses the selected parameter pair \((4,5)\) in this family. The construction gives a rational quartic on that fiber. Neither the projective solution count nor the parameter choice is a claim about all passive quadratics and all targets.

## The retained numerator

In the fixed order \(X_0,X_1,X_2,Y_0,Y_1,Y_2\), the nonzero components are shown below; omitted components are zero. These are the literal rational tuple in the solution record.

\[
\begin{aligned}
N_{0}&=\frac{X_{1}\cdot X_{2}\cdot Y_{1}\cdot \left(12\cdot X_{0}^{2} + 3\cdot X_{1}^{2} + 5\cdot Y_{0}^{2} + 5\cdot Y_{2}^{2}\right)}{18}\\
N_{1}&=- \frac{X_{0}\cdot X_{2}\cdot Y_{1}\cdot \left(3\cdot X_{0}^{2} - 15\cdot X_{1}^{2} - 4\cdot Y_{0}^{2} - 4\cdot Y_{2}^{2}\right)}{18}
\end{aligned}
\]


## The finite certificate check
For \(v=N/D\), clearing denominators gives
\[
A-q\cdot\mathrm dF(v)+F\cdot\operatorname{div}v
=\frac{D\cdot(A\cdot D-q\cdot N(F))+F\cdot\bigl(D\cdot\operatorname{div}N-N(D)\bigr)}{D^2}.
\]
Here both bracketed expressions vanish, so the residual is identically zero. The degree condition, nonzero denominator, and coprimality with \(F\) are separate side conditions retained with the exact record. The accepted Lean proof checks the certificate identity, homogeneous degrees, nonzero denominator, and coprimality over \(\mathbb C\).

The [exact witness](witness.json) gives the denominator, all six numerators, and the quotient. The [Lean proof](Solution.lean) checks the certificate and its side conditions.

The Lean proof uses the shared [explicit-witness assembly](../../formal/lean/HodgeComputer/Constructions/Explicit.lean); its instance-specific identities and displayed witness remain in this folder.
