Put

\[
Q_X=X_0X_1+X_0X_2+X_1X_2,
\qquad Q_Y=Y_0Y_1+Y_0Y_2+Y_1Y_2.
\]

The protected sextic is exactly

\[
F=\sum_{i=0}^{2}(X_i^6+Y_i^6)
+\frac57Q_X^2Q_Y+\frac{10}{7}Q_XQ_Y^2,
\qquad A=X_0X_1X_2Y_0Y_1Y_2,
\qquad q=1.
\]

It has independent \(S_3\) symmetries in the two coordinate blocks. Although \(A\) is symmetric, a transposition negates the residue volume. The residue therefore has the sign character in each factor. The elementary-symmetric quotient's Jacobian density \(\Delta_X\Delta_Y\) serves a different character.

The [two-reflection theorem of Chapter 3B](#technical-information/weighted-threefolds) reaches this residual class. Make the rational coordinate change

\[
(X_0,X_1,X_2)=(a+s,a-s,b),
\qquad (Y_0,Y_1,Y_2)=(c+t,c-t,d).
\]

The independent transpositions become \(s\mapsto-s\) and \(t\mapsto-t\), one in each parity block. The equation is separately even in both, and the target becomes

\[
(a^2-s^2)b(c^2-t^2)d.
\]

Thus the target lies in the two-reflection residual sector supplied by the chapter's weighted-threefold correspondence. Reduction of the original equation modulo five is Fermat, proving smoothness. All hypotheses of the theorem hold for the exact protected equation, and the support-to-certificate theorem establishes rational certificate existence.

The remaining submission is a Lean proof of that protected existence statement. Chapter 3B provides the geometric proof and exact finite algebra checks, but no cleared rational certificate or accepted Lean proof for this target. The atlas's formal status changes only after a checked solve is accepted.
