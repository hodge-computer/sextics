# A subset Euler field at pole order two
Let \(I=\{X_1,X_2\}\) and \(E_I=X_1\partial_{X_1}+X_2\partial_{X_2}\). The denominator is
\[
D=E_I(F)=6\cdot (X_1^6+X_2^6).
\]
For the degree-twelve target
\[
A=X_0^3\cdot X_1^2\cdot X_2^2\cdot Y_0^3\cdot Y_1^2,
\]
take \(N=(A/2)E_I\), meaning \(N_1=A\cdot X_1/2\), \(N_2=A\cdot X_2/2\), with all other components zero.

## Homogeneity supplies both identities
The first equation is immediate:
\[
2\cdot N(F)=A\cdot E_I(F)=A\cdot D.
\]
The target has degree four in the two chosen variables. Thus
\[
\operatorname{div}N=\frac{4+2}{2}\cdot A=3\cdot A.
\]
The denominator has degree six in the same subset, so \(N(D)=3\cdot A\cdot D\). Hence \(D\cdot\operatorname{div}N=N(D)\), and the full pole-order-two residual vanishes identically. It is therefore divisible by \(F^3\), as required.

## The numerical balance behind the construction
For a monomial \(A\), the same subset-Euler argument works when its degree in the subset plus the subset's cardinality equals six. The factor \(1/q\) in \(N\) adjusts the first equation for general pole order. Here \(4+2=6\) is exactly the needed balance.

The numerator degree is thirteen, equal to \(6+12-5\). This example provides a transparent higher-pole control, while the target's remaining degree lies in passive variables. On the Fermat sextic a suitable subset exists for every monomial of degree six or twelve with odd total \(Y\)-degree; this is a finite check on exponent vectors. Certificates add, so every homogeneous odd source has one at \(q=1,2\). Coupled sextics require a separate argument.

## The retained numerator

In the fixed order \(X_0,X_1,X_2,Y_0,Y_1,Y_2\), the nonzero components are shown below; omitted components are zero. These are the literal rational tuple in the solution record.

\[
\begin{aligned}
N_{1}&=\frac{X_{0}^{3}\cdot X_{1}^{3}\cdot X_{2}^{2}\cdot Y_{0}^{3}\cdot Y_{1}^{2}}{2}\\
N_{2}&=\frac{X_{0}^{3}\cdot X_{1}^{2}\cdot X_{2}^{3}\cdot Y_{0}^{3}\cdot Y_{1}^{2}}{2}
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
