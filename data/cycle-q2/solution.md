# A source-bound correction of the cyclic pole-order-two current

## Construction

Use the protected sextic \(F\), source \(A\), and \(q=2\) from the
[instance record](instance.rec). [CurrentData.lean](CurrentData.lean) defines
the saved physical current \((D_0,N_0)\), remainder \(R_0\), and quotient
\(Q_0\) through 13,874 shared polynomial expressions. Their homogeneous
weights are respectively \(3726\), \(3733\), \(7452\), and \(7446\);
the zero numerator component is allowed. These are concrete polynomial
definitions, with rational divisions only inside complex constants.
The exported equation and source are proved equal to the protected target.

Write the full cleared defect as
\[
E(D,N)=AD^2-2D\sum_iN_i\partial_iF+
F\left(D\sum_i\partial_iN_i-\sum_iN_i\partial_iD\right).
\]
The reported partial-current identity would assert
\(E(D_0,N_0)=-F^2R_0+F^3Q_0\). Its generic transport proof is not yet
formalized. The Lean construction therefore retains the literal comparison
polynomial
\[
C=E(D_0,N_0)+F^2R_0-F^3Q_0
\]
as `transportError`; it does not assume \(C=0\). The proposition
`ArchivedPartialIdentityGoal` names that separate obligation.

For a new homogeneous denominator \(H\), six correction numerators \(M_i\),
and an unrestricted quotient correction \(S\), set
\[
D_*=D_0H,\qquad N_{*,i}=HN_{0,i}+D_0M_i,\qquad Q_*=H^2Q_0+S.
\]
Let \(E_0(H,M)\) denote the same defect with zero source. The maintained
certificate-addition identity gives
\[
E(D_*,N_*)-F^3Q_*=
D_0^2E_0(H,M)+H^2C-F^2H^2R_0-F^3S.
\]
[CurrentCorrection.lean](CurrentCorrection.lean) proves this exact reconstruction
identity, including all derivatives of the moving denominator and numerators.
New denominator factors are allowed, with no degree bound, fixed support
profile, or zero-quotient restriction.

## Certificate

`ActualCurrentCorrection` requires the right-hand side above to vanish,
the correct homogeneous degrees, and nonvanishing and complex coprimality
of the new denominator \(H\). The saved denominator's nonvanishing and
coprimality are proved in [CurrentDenominator.lean](CurrentDenominator.lean),
so legality of \(D_0H\) follows automatically.
`certificate_of_actual_current_correction`
then supplies the full maintained `HodgeComputer.Verify` witness: denominator
\(D_*\), six numerators \(N_{*,i}\), and unrestricted quotient \(Q_*\).
Conversely, any original certificate can be expressed as a correction of this
fixed current after clearing denominators. The theorem
`originalGoal_iff_actual_current_correction` proves that this concrete interface
does not restrict the original existence problem.

[Solution.lean](Solution.lean) supplies the protected `Submission.certificate`
entry point. **The remaining `sorry` is
`Submission.missing_rational_correction`**, which asks for this concrete
correction. No such correction or complete original certificate is claimed,
and no expanded JSON witness is exported.

## Supporting identities

[CurrentNormalGauge.lean](CurrentNormalGauge.lean) formalizes the saved
normal-gauge construction while retaining its comparison error.
[CurrentTangents.lean](CurrentTangents.lean) provides five tangent directions
and their full moving-denominator closure equation. Its optional simplified
route explicitly requires the archived partial identity.
[CurrentAmbientLift.lean](CurrentAmbientLift.lean) proves reciprocal-cubic,
adjoint, and coordinate-transport identities with off-hypersurface errors;
instantiating the full circuit transport remains separate.

[CurrentDenominator.lean](CurrentDenominator.lean) uses exact specialization
reductions and 21 polynomial Bézout certificates, then monicity in \(X_0\)
to prove complex coprimality of the full multivariate denominator without a
dense expansion. The same witnesses prove that the denominator is nonzero.
The earlier [normalization equivalence](Normalization.lean) remains available;
normalization preserves a partial current's residual defect.

The construction builds on `hodgepodgeconjecture`'s
[cycle-three proof](../cycle-three/solution.md), the source-transport work of
`benediamond`, the character analysis of `DiamondJM`, and contributions of
`fqlx` and collaborators in
[Discussion #61](https://github.com/hodge-computer/sextics/discussions/61).
Prepared for `fqlx` with OpenAI ChatGPT and Codex assistance.
