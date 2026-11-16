# A Fermat-cover certificate for \(X_{0} X_{1} X_{2} Y_{0} Y_{1} Y_{2}\)

This proof specializes `fqlx`'s [accepted Fermat-cover and moving-conic construction](../holdout/solution.md) to the fixed target in [this instance](instance.rec). The geometric family is the same; the quotient source and the character removed by trace are computed for this particular target.

## The exact statement

The sextic and pole parameter are

\[
F=X_0^6+X_1^6+X_2^6+Y_0^6+Y_1^6+Y_2^6
  +X_0^3X_1Y_0Y_1+X_1^3X_2Y_1Y_2,\qquad q=1,
\]

and \(A=X_{0} X_{1} X_{2} Y_{0} Y_{1} Y_{2}\). We prove existence of a nonzero homogeneous denominator \(D\), relatively prime to \(F\), and homogeneous numerators \(N_i\) of degree \(\deg D+1\), satisfying the full cleared certificate equation. No expanded denominator or bound on its degree is supplied, and the quotient need not vanish.

## The target on the cover

Adjoin \(T^6=Y_0^6+Y_2^6\), and put

\[
\alpha=Y_0/T,\quad \beta=Y_2/T,\quad y=Y_1,
\quad S=y^2+T^2,\quad P=yT.
\]

Then \(\alpha^6+\beta^6=1\). Over the function field of this Fermat curve, the quotient equation is

\[
H=X_0^6+X_1^6+X_2^6+P(\alpha X_0^3X_1+\beta X_1^3X_2)+S^3-3SP^2.
\]

For this target, use the polynomial quotient source and physical correction

\[
B=\frac{P X_{0} X_{1} X_{2} \beta}{2 \alpha^{4}},\qquad C=X_{0} X_{1} X_{2} Y_{0} Y_{1}^{3} Y_{2}.
\]

The coefficient denominators in \(B\) are elements of the Fermat coefficient field; \(B\) is polynomial in the quotient coordinates \((X_0,X_1,X_2,S,P)\). The physical-to-quotient Jacobian is

\[
J=\frac{2\alpha^5(T^2-y^2)}{T}.
\]

Substituting the coordinates gives the exact identity

\[
J B=A-C T^{-2}.
\]

The same identity holds after differentiating \(A,B,C\) in \(X_0\). These two identities, checked directly in [Solution.lean](Solution.lean), are the target-specific inputs to the shared construction. The cover coordinate \(T\) and \(\alpha\) are nonzero in the generic function field, as established in the shared library.

## Integration, trace, and homogeneous clearing

The accepted moving-conic theorem supplies a residue primitive for every polynomial source \(B\) on this fixed quotient. Its proof constructs an exact nonsingular conic seed, obtains a finite algebraic family through the generic point, integrates a polynomial along the family, and descends by finite trace. The [original explanation](../holdout/solution.md) gives these steps and their exact hypotheses.

Piola transport returns that primitive to the cover. The deck transformation fixes the physical coordinates and sends \(T\) to \(\zeta T\), where \(\zeta^6=1\). Here the correction has exponent \(-2\), whose character is nontrivial. Its normalized trace is therefore zero. Since \(C\) and its normal derivative lie in the physical function field, their correction terms disappear under trace, leaving precisely the normal source for \(A\).

The shared clearing theorem then produces legal polynomial data with

\[
\sum_i N_i\partial_iF=AD,\qquad
D\sum_i\partial_iN_i-\sum_iN_i\partial_iD=FQ.
\]

The homogeneous-extraction theorem preserves these identities and denominator admissibility. Consequently the protected defect equals \(F^2Q\). This proves the unrestricted certificate statement without imposing a denominator degree, a zero quotient, or an additional parity condition.

## Formal correspondence and attribution

[Solution.lean](Solution.lean) defines `target`, `reflected`, and `quotientSource`, proves `source_binding` and `partial_binding`, and applies `HoldoutGeneralization.certificate_of_source_pair` to close `Submission.certificate` against the protected target. The reusable implementation is in [the shared holdout library](../../formal/lean/HodgeComputer/Constructions/HoldoutCover/README.md).

The essential Fermat-cover and moving-conic construction is `fqlx`'s work, with the prior mathematical results, collaborators, and AI assistance credited in [the accepted explanation](../holdout/solution.md#12-context-and-attribution). Those acknowledgments include Benjamin E. Diamond's certificate framework, `fringewidth`'s reflection observations, `HeadOfNaps`'s fraction-derivation construction, and the Lean/mathlib contributors. The specialization to this target, its source identities, and the shared target-parameterized assembly were prepared with OpenAI Codex assistance for `benediamond`. This application makes no claim to a new conic construction or to an optimized explicit witness.
