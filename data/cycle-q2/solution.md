# A normalized rational current for the cyclic pole-order-two target

## Construction

Use the exact sextic \(F\), degree-twelve source \(A\), and \(q=2\) from
the [instance record](instance.rec), with coordinates
\(z=(X_0,X_1,X_2,Y_0,Y_1,Y_2)\).
For a nonzero homogeneous denominator \(D\) of degree \(m\), relatively prime
to \(F\) over \(\mathbb C\), seek six homogeneous numerators \(N_i\) of
degree \(m+7\) and a polynomial \(Q\) satisfying
\[
AD^2-2D\sum_iN_i\partial_iF+
F\left(D\sum_i\partial_iN_i-\sum_iN_i\partial_iD\right)=F^3Q.
\]
There is no bound on \(m\), prescribed denominator support, or restriction
\(Q=0\).

The radial correction reduces this identity to two normalized equations.
Put \(S=AD-2\sum_iN_i\partial_iF\). The cleared identity implies
\(F\mid DS\); coprimality gives \(S=FH\), where \(H\) is homogeneous of
degree \(m+6\). Set
\[
N'_i=N_i+\frac{z_iH}{12}.
\]
Euler's identity for the sextic gives \(2\sum_iN'_i\partial_iF=AD\).
Writing \(B(D,N)=D\sum_i\partial_iN_i-\sum_iN_i\partial_iD\), Euler's
identities for \(D\) and \(H\) also give
\[
B(D,N')-B(D,N)=DH.
\]
Thus the complete cleared defect is unchanged: the added terms are
\(-DFH+FDH=0\). The same denominator and quotient satisfy
\[
2\sum_iN'_i\partial_iF=AD,\qquad B(D,N')=F^2Q.
\]
Conversely, these equations imply the original cleared identity.
[Normalization.lean](Normalization.lean) proves this equivalence, including
the numerator degrees and preservation of denominator legality. Normalization
preserves any nonzero residual defect of a partial current; it does not repair it.

## Certificate

[Workspace.lean](Workspace.lean) binds the construction to the protected target
and proves its degree, nonvanishing, and polynomial identities.
The `NormalizedRationalSolution` structure in [Assembly.lean](Assembly.lean)
retains all denominator, grading, and normalized-equation obligations.
`certificate_of_normalized_solution` converts an inhabitant into the full
maintained `HodgeComputer.Verify` witness, with an unrestricted quotient.

[Solution.lean](Solution.lean) supplies the standard protected entry point
`Submission.certificate`. **The proof is incomplete at
`Submission.missing_rational_solution`**, whose explicit `sorry` asks for an
inhabitant of `NormalizedRationalSolution`. The normalization equivalence and
conditional assembly are proved, but they do not establish this existence.
No expanded JSON witness is exported.

The construction builds on `hodgepodgeconjecture`'s
[cycle-three proof](../cycle-three/solution.md), the source-transport work of
`benediamond`, the character analysis of `DiamondJM`, and the contributions of
`fqlx` and collaborators recorded in
[Discussion #61](https://github.com/hodge-computer/sextics/discussions/61).
Prepared for `fqlx` with OpenAI ChatGPT and Codex assistance.
