# Radial normalization of the cycle-q2 certificate problem

## Draft status

This is an incomplete certificate submission. The missing theorem
`missing_rational_solution` still contains `sorry`; `Submission.certificate`
depends on it. No legal witness or unconditional proof of the protected target
has been obtained. In particular, the normalization below reorganizes the
existence problem without solving it.

The [Lean entry point](Solution.lean) uses the repository-generated `HodgeTarget`
and the maintained verifier. The target is not redefined by the submission.
[Workspace.lean](Workspace.lean), [Assembly.lean](Assembly.lean), and
[Normalization.lean](Normalization.lean) contain the algebra and conditional
assembly used by that entry point. The required final statement is
`HodgeComputer.HasCertificate HodgeSubmission.F HodgeSubmission.q HodgeSubmission.A`.

## Exact target and witness obligations

With the variable order
\(z=(X_0,X_1,X_2,Y_0,Y_1,Y_2)\), the existing
[instance record](instance.rec) specifies

\[
F=\sum_{i=0}^{2}(X_i^6+Y_i^6)
+\frac12\left(X_0^3X_1Y_0Y_1+X_1^3X_2Y_1Y_2+X_2^3X_0Y_2Y_0\right),
\]
\[
A=X_0^2X_1^2X_2^3Y_0^2Y_1^2Y_2,\qquad q=2.
\]

A certificate requires a nonzero homogeneous denominator \(D\), relatively
prime to \(F\) over \(\mathbb C\), six numerators \(N_i\), and a polynomial
\(Q\). Writing \(m=\deg D\), every \(N_i\) must be homogeneous of degree
\(m+7\); zero components are permitted. The full identity is

\[
E(D,N):=AD^2-2D\sum_{i=0}^{5}N_i\partial_iF
+F\left(D\sum_{i=0}^{5}\partial_iN_i
-\sum_{i=0}^{5}N_i\partial_iD\right)=F^3Q.
\]

The maintained verifier also checks the nonvanishing and homogeneity of the
hypersurface and the source homogeneity. These conditions are retained for the
protected sextic and degree-twelve source. There is no denominator-degree bound,
prescribed pole support, symmetry requirement on the current, or requirement
that \(Q=0\). This draft supplies no `witness.json` because it has no completed
tuple to display.

## Same-denominator radial normalization

Let

\[
S=AD-2\sum_iN_i\partial_iF,\qquad
B(D,N)=D\sum_i\partial_iN_i-\sum_iN_i\partial_iD.
\]

Then \(E(D,N)=DS+FB(D,N)\). For a legal certificate, \(F\mid E(D,N)\),
so \(F\mid DS\). Coprimality of \(D\) and \(F\) implies \(F\mid S\).
Thus there is a polynomial \(H\) such that \(S=FH\). Homogeneity gives
\(\deg H=m+6\) in the homogeneous-degree predicate, including the zero case.
This is polynomial divisibility; it introduces no pole along \(F\).

Define

\[
N'_i=N_i+\frac{z_iH}{12},\qquad D'=D.
\]

Euler's identity \(\sum_i z_i\partial_iF=6F\) gives

\[
2\sum_iN'_i\partial_iF
=2\sum_iN_i\partial_iF+FH=AD.
\]

The new numerators have the same required degree. The denominator is literally
unchanged, so its nonvanishing, homogeneity, and complex coprimality are preserved.

### The complete defect is preserved

Put \(\delta N_i=z_iH/12\). Applying Euler's identities to \(H\) and \(D\)
gives

\[
\sum_i\partial_i\delta N_i=\frac{m+12}{12}H,
\qquad
\sum_i\delta N_i\partial_iD=\frac m{12}DH,
\qquad
\sum_i\delta N_i\partial_iF=\frac12FH.
\]

Consequently \(B(D,N')-B(D,N)=DH\), and

\[
E(D,N')-E(D,N)=-2D\left(\frac12FH\right)+F(DH)=0.
\]

All moving derivatives are retained. The same quotient \(Q\) survives, and the
normalized equations become

\[
2\sum_iN'_i\partial_iF=AD,
\qquad B(D,N')=F^2Q.
\]

Conversely, any legal homogeneous tuple satisfying these two equations satisfies
the original cleared identity. Thus the normalized existence statement is
equivalent to the original certificate problem, without restricting \(D\) or
\(Q\).

This also identifies a limit of the method. If a partial current has
\(E(D,N)=-F^2R+F^3Q\), normalization leaves that same error. Its second
normalized equation is \(B(D,N')=-FR+F^2Q\). Renaming the quotient or canceling
common factors does not remove the regular remainder \(R\).

## Remaining existence theorem

The structure `NormalizedRationalSolution` asks for an actual nonzero legal
homogeneous denominator, the six correctly graded numerators, the unrestricted
quotient, and both normalized equations. The current draft still lacks a proof
of

```lean
Nonempty NormalizedRationalSolution
```

The algebraic equivalence and conditional assembly do not construct an inhabitant
of that structure. The intended completion may give explicit polynomials or a
nonconstructive existence proof, but it must discharge the same obligations.
The draft remains ineligible for protected acceptance while its admission remains.

## Research history: reusable results and unsuccessful approaches

The following is a condensed account of the approaches recorded in
[the source conversation](https://chatgpt.com/g/g-p-6a6d301e456881918ba2a163ea5e7e4e-math/c/6aea2396-5700-83ea-85c4-ad3a8a0ba501)
and [Discussion #61](https://github.com/hodge-computer/sextics/discussions/61).
These are historical reports, not additional Lean theorems of this submission;
their mathematical computations were not rerun to prepare this explanation.
Related successes for `cycle-three`, `holdout`, reflection, or symmetric-sextic
targets do not prove this different source and pole order.

### Source transport, residues, and geometric constructions

| Approach | What worked in the record | What remained or failed |
|---|---|---|
| Physical-to-cubic transport; deformation from pole order one; character companion bridge | Explicit source transformations and conditional reconstruction formulas retained the actual moving source. | A regular residual source remained; multiplication of an earlier primitive did not preserve all required derivatives or isolate the required character. |
| Transverse K3 reduction; Hermite decomposition of three meromorphic forms | Finite scalar poles, trace terms, compact amplitudes, and boundary residues were separated. | A decomposition into channels did not integrate the compact and third-kind channels. The transverse construction and the proper two-parameter K3 module have different scopes. |
| Moving-residue feedback; diagonal currents on the same elliptic line | Source fluxes, invertible feedback matrices, and an odd-channel cancellation were reported. | Differentiation of moving amplitudes reopened residual equations; invertibility alone did not close the source. |
| Norm-one coefficient-fibre density; single-pair tangents; scalar corrections | Audits rejected particular source-specific channels. | These were scoped exclusions; coupled horizontal currents, different channels, and additional supports remained available. |
| Six-component compact class; genus-four thirteen-channel architecture | Compact representatives, connection machinery, and conditional reconstruction were developed. | Some generic physical source data were incomplete, and a compact fit did not establish full source closure. |
| Universal elliptic connection; character-preserving genus-two correspondence | Source-independent machinery and actual-source reductions were obtained. | Moving incidence amplitudes still required differentiation and integration; machinery for another source could not replace that step. |
| Critical-centre blowups; reverse-point multiplier ideals | Chartwise regularity, transported sources, and finite-defect reductions were reported. | Global control at infinity and a saturated ideal-inclusion argument remained missing. A compact seventy-two-point graph alone did not certify an empty global defect. |
| Polar, theta, exchange, native-support, and critical-branch constructions | Particular support families were tested or excluded, and alternative multisections were identified. | A finite list of native supports or failed markings did not exhaust all moving covers or correspondences. |
| Chain-to-cycle contact continuation; constant-invariant families and traces | Incidence formulas and finite descent constructions were reusable. | Tested continuations failed, and several full-current traces vanished or did not retain the source. Other seeds and source forms were outside those tests. |
| Fold-parity Hankel elimination | One apparent fold pole could be relocated or removed at the stated level of evidence. | Eliminating that pole did not give a global primitive. |

### Rational equations, denominators, and candidate currents

| Approach | What worked in the record | What remained or failed |
|---|---|---|
| Finite projection to a rank-five trace-zero system; four-scalar cubic and toric coordinates | Alternative equations and source-preserving reconstruction interfaces were reported. | The rational preimage remained unknown; the actual base derivatives and logarithmic twist could not be dropped. |
| Generalized Hermite-to-ODE reduction; de Rham and differential-module adapters; higher-residue machinery | Algorithms and conditional reconstruction steps were formulated. | No completed target computation supplied the missing rational primitive; allocation failures and timeouts supplied no nonexistence result. |
| Coupled nine-class proper, infinity, and branch system | A full explicit connection/source system and original-coordinate reconstruction were compiled. | Proper-channel fits omitted necessary boundary conservation unless all nine equations were retained. One rejected rational-generator family did not exhaust the equation. |
| Inverse-centre, cofactor, scalar-gauge, ramification, and pivot simplifications | Forcing expressions and rational representations were shortened; removable pivots were distinguished from genuine poles. | Formula compression did not prove rational solvability. |
| Characterwise low-degree denominators; genus-five necessary loci | Necessary Jacobian-ideal conditions and bounded exclusions were reported at successive stages. | Later reports strengthened some earlier bounds, but the draft does not re-prove or rely on a complete degree-six exclusion. Passing an older necessary test was never a certificate. |
| Critical-Jacobian degree-eight denominator; degree-twenty and conductor-adjoint constructions | Specific denominator candidates and smaller relaxation families were tested. | Reported failures applied to the stated denominator or family, not every denominator of that degree. |
| Original-coordinate support profiles; discriminant and auxiliary poles; finite-projection profiles; large grid sweeps | Finite-field or finite-space screens rejected many specified ansatzes. | Their primes, supports, exponent bounds, and transfer arguments were essential. Modular inconsistency and missing raw payloads did not establish unrestricted characteristic-zero nonexistence. |
| One-coordinate rational integration | Some individual integration directions were rejected with other variables allowed as rational coefficients. | Coupled current components and different directions were not excluded. |
| Two Hessian-inverse candidates; logarithmic-gradient completion | Exact substitution detected nonzero residuals in the proposed tuples and some constant-coefficient variations. | These rejected those tuples and finite families, not all Hessian-supported or rationally varying currents. |

### Local constructions, alternative geometries, and implementation

| Approach | What worked in the record | What remained or failed |
|---|---|---|
| Noncharacteristic local jets and finite-adic currents | Formal coefficient recursions and finite Taylor approximations succeeded. | More local coefficients did not establish a global rational function. |
| Euler scaling curves and generic Euler-only currents | Directional rationality obstructions were reported at specified levels of generality. | Transverse variables and other current directions remained outside those obstructions. |
| Nambu tangents; Hamiltonian and transverse-moment lifts; constant-volume charts | Tangent modules, two source moments, and finite algebraic reconstruction were obtained. | Matching moments or inverting a finite matrix did not satisfy the full covariant divergence equation. Some older residuals required correction for an omitted moving-variable product-rule term. |
| Scalar correction and Darboux invariant integrating factors | Particular scalar equations, candidates, and invariant-generated families were excluded. | The statements did not cover all original currents or arbitrary coupled corrections. |
| Denominator-independent disproof test | A proposed route to a global obstruction was examined. | It established neither unrestricted nonexistence nor existence. |
| Three-ratio plane-cubic integration; genus-two quotients, isogeny, and auxiliary surface constructions | Relative reductions and a complete auxiliary integration were reported. | Transport of the moving original source into the solved auxiliary class remained missing. |
| Cyclic-sum projector; conic rationalization | Conditional character separation and coordinate simplifications were available. | Neither supplied the required source-serving sum current or primitive. |
| Proper coupled K3 Hermite-to-ODE proposal | A concrete rational-current problem was identified. | A later source/support audit withdrew the recommendation for its stated base-rational module. This is a reported scoped conclusion, not a new generic ODE solve or an unrestricted obstruction. |
| Compiled models and physical Hermite currents; character averaging | Software builds, representation equality, and large explicit partial currents were produced. | Compilation did not prove closure; the physical tuple retained a nonzero error, and averaging the same current did not repair it. |
| Tangent-correction interface; common-factor cancellation; radial normalization | Exact conditional repair equations, denominator cleanup, and the normalization above were developed. | They preserved the outstanding source error and did not construct the required correction. |
| Fixed-denominator linear searches; sparse elimination and checkpoints | Search tools, finite arithmetic checks, and memory-aware implementations improved reproducibility. | A completed inconsistent space stayed inconsistent; a crash, memory cap, or compiler-installation failure gave no mathematical conclusion. |
| Lean assembly and strict admission checks | The existence obligation was isolated and the strict gate correctly rejected its admission. | Counting one `sorry`, compiling a draft with an admission, or compiling separate helpers for another target did not prove the protected theorem. |

### Corrections that constrain reuse

The former elliptic-boundary rank-85/86 impossibility claim was withdrawn after a
coefficient-indexing error. An exact boundary primitive was subsequently found,
with a regular compact remainder still present. The withdrawn obstruction must
not be reused.

The reverse-point empty-defect claim retained an unfinished saturated-inclusion
step. Its stronger global conclusion must remain unproved here. Likewise,
historical descriptions of a proper K3 route as open and a later scoped audit
must not be combined into a claim that every possible current has been excluded.

Across all routes, a proposed advance must retain the exact source and its
character, all active moving derivatives, every boundary channel needed for
reconstruction, and the full regular quotient. An auxiliary primitive, a local
jet, a finite-field fit, or a rebuilt arithmetic circuit is not the missing
global certificate.

## Attribution

This draft was prepared for `fqlx` with OpenAI ChatGPT and Codex assistance from
the linked Math-project conversation. It builds on the accepted `cycle-three`
construction of `hodgepodgeconjecture`, the source-transport and connection
calculations of `benediamond`, the character and geometric analyses of
`DiamondJM`, and the research by `fqlx` and collaborators credited in
[Discussion #61](https://github.com/hodge-computer/sextics/discussions/61).
The historical summary reports those contributions at their documented scope;
it does not claim new priority or turn their partial results into a completed
proof.
