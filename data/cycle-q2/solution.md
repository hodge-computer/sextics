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

## A compact unconditional search equation

[CanonicalTangents.lean](CanonicalTangents.lean) gives a second, small interface
that does not import the saved polynomial current or assume its transport
comparison. Set \(y=Y_2\), \(a=A/y\),
\[
e=X_0X_2^3Y_0+X_1^3X_2Y_1,\qquad
h=12y^5+e,\qquad g=F_y=h/2.
\]
The rational field \(v_0=(ay/h)e_y\) satisfies \(2v_0(F)=A\), and
\[
-\operatorname{div}v_0=\frac{a(48y^5-e)}{h^2}.
\]
With \(T_i=g\partial_i-F_i\partial_y\) for \(i<5\), it therefore
suffices to solve
\[
\sum_{i<5}T_i(t_i)=\frac{a(48y^5-e)}{h^2}+F^2s.
\]
Here the \(t_i\) must be homogeneous rational functions of degree two and
regular at the generic point of every component of \(F=0\); \(s\) must
also be regular there, with degree minus six. These conditions permit
arbitrary additional legal poles. The resulting current is
\(v_0+\sum_i t_iT_i\).

The module formalizes the cleared equation. Its canonical denominator is
\(g\), its numerator vector is \(n_0=(A/2)e_y\), and it sets
\(B=g\operatorname{div}n_0-dg(n_0)\). Writing \(t_i=P_i/H\), the
exact condition is
\[
g^2\operatorname{tangentBoundary}(H,P)+H^2B=F^2S.
\]
`CanonicalTangentSolution` includes homogeneous, nonzero, legal \(H\) and
coefficients \(P_i\) of degree \(\deg H+2\).
`originalGoal_iff_canonical_tangent_solution` proves this is an unconditional
existence equivalence with the protected target: normalize any hypothetical
certificate, subtract \(v_0\), and use the legal pivot \(g\) to express
the tangent difference in the five directions. The theorem constructs no
solution of this equation. The saved current remains useful as an alternative
starting point whose reported residual has an additional factor of \(F\).

## A conical current and an explicit connection presentation

An alternative mathematical presentation starts from the paired Euler field
\[
T=X_0\partial_{X_0}-Y_0\partial_{Y_0},\qquad
H=T(F),\quad H_1=T(H),\quad H_2=T(H_1).
\]
Since \(\operatorname{div}T=0\) and \(T(A)=0\), the two-component current
\[
V_* =\frac{A(H^2-FH_1)}{2H^3}T
\]
satisfies the exact identity
\[
A-2V_*(F)+F\operatorname{div}V_*
 =F^2\frac{A(3H_1^2-HH_2)}{2H^4}.
\]
The denominator \(H^3\) has degree 18 and is independent of \(Y_2\), so it is legal. Its residual is nonzero modulo \(F\); this remains a partial current. The cancellation order is the already available \(F^2\), and an elementary normal current has the smaller denominator degree 15. The useful distinction here is the conical denominator and six-term residual numerator.

On \(X_2=1\), write the actual equation as \(F=y^6+cy+f\), with \(y=Y_2\) and four physical base coordinates \(z\). The trace-zero basis
\[
e=(y,y^2,y^3,y^4,y^5+5c/6)
\]
of the degree-six separable coefficient algebra gives explicit connection matrices \(B_c,B_f\). The remaining correction is equivalent to a connection-divergence equation for four arbitrary columns \(u_j\in\mathbb C(z)^5\), with operators
\[
\nabla_j u_j=\partial_j u_j+(c_jB_c+f_jB_f)u_j.
\]
The [exact connection packet](https://github.com/hodge-computer/sextics/pull/223#issuecomment-6712406587) supplies both matrices, the five-entry forcing vector, their flatness check, reconstruction of a certificate from a solution, and the converse extraction from any certificate. Rational dependence on all four base coordinates is retained; the coefficients are not restricted to functions of \(c,f\). This is a concrete specialization of the canonical tangent/residue reduction, not an existence proof for the remaining equation. These additional identities have exact symbolic checks but have not been incorporated into the Lean endpoint.

For any subsequently constructed ordinary certificate with a conical denominator, the book's [fixed-denominator strictification corollary](../../docs/05-computation.md#51-fixing-a-denominator-makes-the-problem-linear) preserves that exact denominator and its pole multiplicity. It does not apply to the unfinished \(F^2\) partial current above.

## Supporting identities

[CurrentNormalGauge.lean](CurrentNormalGauge.lean) formalizes the saved
normal-gauge construction while retaining its comparison error.
[CurrentTangents.lean](CurrentTangents.lean) provides the five directions
\(T_i=F_5\partial_i-F_i\partial_5\), for \(i<5\), and their full
moving-denominator closure equation, using the general tangent calculus in
[`TangentCoordinates`](TangentCoordinates.lean).
That module treats an arbitrary polynomial over a commutative coefficient ring
and an arbitrary number of variables; [CanonicalTangents.lean](CanonicalTangents.lean)
supplies the present specialization. The theorem
`originalGoal_iff_five_tangent_solution` proves that this route loses no
certificate freedom, conditional on the archived partial identity \(C=0\).
For any polynomial vector \(M\) tangent to \(F\), the exact identity
\[
\sum_{i<5}M_i(F_5e_i-F_ie_5)=F_5M
\]
represents \(M/H\) in these five directions with denominator \(F_5H\).
The moving-denominator boundary scales by \(F_5^2\), so the derivatives of
the pivot are retained. [DenominatorSpecialization.lean](DenominatorSpecialization.lean)
proves that this new pole is legal: the same monic specialization
sends \(F\) to \(f=X^6+2X^3+X+132\) and \(F_5\) to \(X+7\), with
\(f(-7)=117088\ne0\). `FiveTangentSolution` includes all grading and
legality hypotheses, and `certificate_of_five_tangent_solution` assembles the
original certificate from a solution. Neither the source comparison nor a
solution of this five-function equation is asserted here.
[CurrentAmbientLift.lean](CurrentAmbientLift.lean) proves reciprocal-cubic,
adjoint, and coordinate-transport identities with off-hypersurface errors;
instantiating the full circuit transport remains separate.

[CurrentDenominator.lean](CurrentDenominator.lean) uses exact specialization
reductions and 21 polynomial Bézout certificates, then monicity in \(X_0\)
to prove complex coprimality of the full multivariate denominator without a
dense expansion. The same witnesses prove that the denominator is nonzero.
The [normalization equivalence](Normalization.lean) now applies
[`RadialNormalization`](RadialNormalization.lean).
For a degree-\(d\) hypersurface in projective dimension \(n\), its theorem
normalizes every certificate with \(n+1\le dq\), preserving the same denominator,
quotient, and entire cleared defect. Here \((n,d,q)=(5,6,2)\).
The saved current's explicit comparison polynomial and its remaining closure
equation are separate from this reusable normalization.

The construction builds on `hodgepodgeconjecture`'s
[cycle-three proof](../cycle-three/solution.md), the source-transport work of
`benediamond`, the character analysis of `DiamondJM`, and contributions of
`fqlx` and collaborators in
[Discussion #61](https://github.com/hodge-computer/sextics/discussions/61).
Prepared for `fqlx` with OpenAI ChatGPT and Codex assistance.
