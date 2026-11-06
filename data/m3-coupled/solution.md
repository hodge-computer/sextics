# A conic hidden in quadratic coordinates
Set \(U=X_0^2-X_1^2\), \(W=X_2^2-Y_1^2\), \(r=Y_0\), \(s=Y_2\), and use \(x=X_1^2\), \(y=Y_1^2\) as active coordinates. With \(U,W,r,s\) fixed, the sextic becomes a quadratic polynomial
\[
f=a\cdot x^2+h\cdot x\cdot y+b\cdot y^2+c\cdot x+d\cdot y+e.
\]
Here \(a,b,h\) are homogeneous of degree two in the original grading, \(c,d\) have degree four, and \(e\) has degree six. Their values are determined by expanding the fixed sextic in the adapted coordinates. The target factors as \(16\cdot X_0\cdot X_1\cdot X_2\cdot Y_1\cdot (k\cdot x+m)\), with \(k=9/16\) and \(m=U/4-5\cdot r^2/16\).

## Solve a three-by-three problem
Seek an affine radial field \(w=(\rho\cdot x+p_1)\partial_x+(\rho\cdot y+p_2)\partial_y\). The identity
\[
w(f)-f\cdot\operatorname{div}w=k\cdot x+m
\]
reduces to
\[
\begin{pmatrix}2a&h&-c\\h&2\cdot b&-d\\c&d&-2\cdot e\end{pmatrix}
\begin{pmatrix}p_1\\p_2\\\rho\end{pmatrix}
=\begin{pmatrix}k\\0\\m\end{pmatrix}.
\]
Cramer's rule explains the denominator:
\[
D=-2\cdot\bigl((4\cdot a\cdot b-h^2)\cdot e-b\cdot c^2-a\cdot d^2+h\cdot c\cdot d\bigr).
\]
Its degree is ten. This is the determinant of the conic's coefficient problem, rather than an arbitrary high-degree guess.

## Transport and strictify
Piola transport through the quadratic coordinate map supplies the Jacobian density \(16\cdot X_0\cdot X_1\cdot X_2\cdot Y_1\), producing the required original-coordinate target. An Euler correction then removes the divergence: if \(V\) is the transported field, replace it by \(V-(\operatorname{div}V)\cdot E/6\), where \(E\) is the six-variable Euler field. The divergence has degree zero, so the correction kills it, and Euler's identity \(E(F)=6\cdot F\) preserves the certificate equation.

The exact witness below supplies the resulting degree-eleven numerator. The result is one compatible target on the conic family; no denominator-minimality or general-even-sextic theorem is asserted.

## The finite certificate check
For \(v=N/D\), clearing denominators gives
\[
A-q\cdot\mathrm dF(v)+F\cdot\operatorname{div}v
=\frac{D\cdot(A\cdot D-q\cdot N(F))+F\cdot\bigl(D\cdot\operatorname{div}N-N(D)\bigr)}{D^2}.
\]
Here both bracketed expressions vanish, so the residual is identically zero. The degree condition, nonzero denominator, and coprimality with \(F\) are separate side conditions retained with the exact record. The accepted Lean proof establishes the exact identities, homogeneous degrees, nonzero denominator, and coprimality over \(\mathbb C\) for this tuple.

The [exact witness](witness.json) gives the denominator, all six numerators, and the quotient. The [Lean proof](Solution.lean) checks the certificate and its side conditions.

The Lean proof uses the shared [explicit-witness assembly](../../formal/lean/HodgeComputer/Constructions/Explicit.lean); its instance-specific identities and displayed witness remain in this folder.
