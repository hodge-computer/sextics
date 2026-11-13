# A nonconstructive geometric route for cycle-q2

## Status and protected goal

**Draft; not a completed Lean proof.** The active route is now the geometric
existence argument. One explicit admission remains:
`Submission.missing_geometric_existence`. The protected theorem therefore
still depends on `sorryAx` and must not be accepted. Changing the route does
not discharge the existence obligation.

The exact \(F,A,q=2\) remain those of the [instance record](instance.rec), in
coordinate order \((X_0,X_1,X_2,Y_0,Y_1,Y_2)\). The goal is a nonzero
homogeneous denominator \(D\), homogeneous numerators of degree
\(\deg D+7\), and unrestricted polynomial \(Q\), with
\(\gcd_{\mathbb C}(F,D)=1\), satisfying
\[
AD^2-2D\sum_iN_i\partial_iF+
F\left(D\sum_i\partial_iN_i-\sum_iN_i\partial_iD\right)=F^3Q.
\]
No explicit polynomial witness is exported.

## Classical argument and target checks

The references are [Chapter 3D](https://github.com/hodge-computer/sextics/blob/bab597060182b81323aadc09f3d51ff8d4448b64/docs/03d-hodge-loci.md)
and [Chapter 1](https://github.com/hodge-computer/sextics/blob/bab597060182b81323aadc09f3d51ff8d4448b64/docs/01-certificates.md).
These are mathematical references, not Lean imports or additional axioms.

For \(\omega^3=1\), \(\omega\ne1\), use
\[
\beta:(X_2,Y_2)\mapsto(-X_2,-Y_2),\qquad
\gamma=\operatorname{diag}(\omega^2,\omega^2,1,\omega,1,1).
\]
All nine monomials of \(F\) are fixed. The numerator has
\(\gamma\)-weight \(10\equiv1\pmod3\), whereas the projective volume form
has determinant weight \(5\equiv2\pmod3\). Their product is invariant.
Under \(\beta\), the source has pair-degree four and the determinant is
positive. Thus the actual asymmetric residue
\(\alpha=\operatorname{Res}_{F=0}(A\Omega/F^3)\) is fixed by both actions.
No cyclic source sum or source-erasing invariant average is substituted.

[GeometricTarget.lean](GeometricTarget.lean) supplies proof scripts for the
protected-polynomial evaluation identities, the two actions, their orders
and commutation, and the equation and determinant-weighted source identities.
`AlgebraicInputs` retains these facts, the nonzero equation, homogeneous
degrees, and protected pole parameter. Polynomial equivariance is not itself
a formalization of residues or cohomology.

The exact affine gradient condition is now proved in
[GeometricFormalInputs.lean](GeometricFormalInputs.lean), by choosing a maximum-modulus coordinate
\(M>0\) at a hypothetical nonzero gradient zero. The pure derivative has
modulus \(6M^5\); mixed derivatives contribute at most \(2M^5\) for an
\(X\)-coordinate and \(M^5\) for a \(Y\)-coordinate. The theorem is bound
to `HodgeSubmission.F` and proves that every nonzero affine representative
has a nonzero partial derivative. A formal geometric Jacobian criterion is
still needed when using this fact as scheme or analytic smoothness.

The same new module proves `Irreducible HodgeSubmission.F`, its primality,
and that its hypersurface quotient is a domain. This proof is purely
algebraic: view the equation as monic in \(X_0\), specialize
\((X_1,X_2,Y_0,Y_1,Y_2)=(0,0,t+1,0,i)\), and apply Eisenstein at \(t\)
to \(X_0^6+(t+1)^6-1\). It reuses the existing proved
`HoldoutConstruction.irreducible_power_add_constant` and mathlib's monic
specialization theorem.

Chapter 3D.5 supplies
\[
H^4(X,\mathbb Q)^{\langle\beta,\gamma\rangle}
\subset N^1H^4(X,\mathbb Q).
\]
Its coordinate order is
\((x_0,x_1,x_2,x_3,u,v)=(X_0,X_1,Y_0,Y_1,X_2,Y_2)\).
Use complexification; the individual residue need not be a rational Betti
class. Choose a squarefree homogeneous ambient support equation \(S\) of
degree \(e\), not divisible by \(F\). Chapter 1's filtered de Rham argument
and twisted Euler sequence supply
\[
\eta=-\frac{\iota_N\Omega}{F^2S^2},\qquad \deg N_i=2e+7,
\]
with \(A\Omega/F^3-d\eta\) regular along \(F=0\). Setting \(D=S^2\)
gives the original cleared identity, with its full polynomial quotient.
This is an existential choice, not an evaluated coefficient tuple.

## Finite seed algebra

Use auxiliary weighted coordinates \((x_0,x_1,x_2,x_3;w)\), not new protected
coordinates, and the sparse invariant cubic
\[
b=x_3^3+x_2^3+x_1x_2x_3+x_0x_2x_3+x_0x_1^2.
\]
For \(r^3=2\), \(i^2=-1\), put
\[
\begin{aligned}
f_1&=x_0^2-rx_1x_3,&g_1&=x_0^4+rx_0^2x_1x_3+r^2x_1^2x_3^2,\\
f_2&=w+x_2^2,&g_2&=w^2-wx_2^2+x_2^4,\\
h&=b-i(x_1^3+x_3^3),&k&=b+i(x_1^3+x_3^3).
\end{aligned}
\]
Normalize the degree-nine trace on the corresponding Artinian algebra by
\(\tau(x_0x_1^8)=1\). The invariant cubic column order is
\[
(x_3^3,x_2^3,x_1x_2x_3,x_1^3,x_0x_2x_3,x_0x_1^2,x_0^2x_1,x_0^3,x_3w).
\]
The first seven rows are \(\tau(kL\sigma)\), ordered by
\[
\sigma\in(x_2x_3^2,x_1x_2^2,x_1^2x_3,x_0x_2^2,x_0x_1x_3,x_0^2x_3,x_2w),
\]
and the last is \(\tau(x_2x_3^3wL)\). Scale the first five rows by
\(6/r^2\), the next two by three, and the last by six.

[GeometricSeed.lean](GeometricSeed.lean) records this \(8\times9\) matrix
\(M\), an explicit Gaussian-rational right inverse \(R\), and the tangent
\(\ell=ix_0^2x_1+(i-1)x_0^3\), with proof scripts for
\[
MR=I_8,\qquad M\ell=(0,0,0,0,0,0,0,2)^{\mathsf T}.
\]
These are finite matrix identities. Their identification with the trace
algebra and geometric pairings remains a separate formalization obligation;
they do not imply divisor support without the geometric argument.

## Active proof boundary

### New formal inputs

`GeometricFormalInputs.lean` consolidates the additional formalization into
one source file, preserving all of the earlier route within the proposal's
64-file limit. Besides the exact gradient and irreducibility theorems, it
contains the following developments.

- **Finite Higgs calculation.** The 33 character-one monomials and 35
  invariant tangent monomials are checked against the weighted socle
  `(4,4,4,4,1)`. The monomial lists, completeness, and multiplication table
  have passed kernel replay. The scalar-commutant proof and its idempotent
  corollary also compile and pass kernel replay. They use ordinary proof terms for
  1,088 matrix-entry equalities. Geometric identification with the actual
  Higgs field remains a separate obligation.
- **Finite averaging.** Verified certificates can be combined over the
  product of their denominators, with explicit numerator and quotient sums.
  All grading and coprimality conditions are proved. Weights summing to one
  retain a common source. This supplies the algebraic averaging step; it
  does not establish that the initial certificates exist.
- **Actual rational differential calculus.** Coordinate derivations on the
  fraction field are constructed using the accepted fraction-derivation
  library. Their action, quotient-rule divergence, and cleared defect are
  identified with the protected polynomial expressions.
- **Legal residual-denominator cancellation.** If the rational defect is
  `F^(q+1) * P/T` with `T` coprime to `F`, Euclid's lemma produces the
  polynomial quotient required by `Verify`. This proves the algebraic
  clearing step, while filtered de Rham existence and pole control remain
  unformalized.
- **Square denominators lose no generality.** For an irreducible sextic,
  `HasCertificate F 2 A` is equivalent to existence of a homogeneous
  `S`, with `F` not dividing `S`, and homogeneous `N` of degree
  `2 * degree(S) + 7` satisfying the localized equation for `N/S^2`.
  The forward proof rewrites `N/D` as `(D*N)/D^2`. This is an equivalence
  with the original goal, not a proof of either existential statement.

The existing `Normalization.lean` already contains same-denominator sextic
normalization. Rechecking that reduction does not discharge any new
existence obligation.

### Remaining existence theorem

[Solution.lean](Solution.lean) defines
`CycleQ2Nonconstructive.GeometricExistenceBridge`, taking the separated
`AlgebraicInputs` and `FiniteSeedInputs` to the unchanged `HasCertificate`
statement. `certificate_of_geometric_bridge` is conditional assembly only.
The single explicit `sorry` asks for the proof of the bridge. The final
protected theorem has no new parameters or assumptions, but remains admitted.

The outstanding chain is:

| Obligation | Status of this revision |
| --- | --- |
| Smoothness and geometric setup | Exact gradient condition and absolute irreducibility proved; geometric Jacobian criterion and setup remain. |
| Trace-algebra binding and obstruction/derivative formulas | Finite matrix data separated; geometric binding not formalized. |
| Hodge-locus integration to moving curves | No Lean implementation here. |
| Higgs criterion and spanning of the invariant variation | Complete finite monomial matrix calculation and scalar-idempotent consequence proved; geometric Higgs comparison and projector argument remain. |
| Supported projector and specialization | Correspondence, polarization and specialization proofs required. |
| Paired-sign quotient and relative support transfer | Quotient, Leray and boundary proofs required. |
| Support-to-certificate bridge | Rational derivations, homogeneity bookkeeping and legal clearing proved; filtered de Rham strictness, pole bounds and Euler-sequence existence remain. |

The exact unresolved assertion can now be stated without imposing an
additional denominator ansatz:

```lean
∃ (e : ℕ) (S : HodgeComputer.AmbientPoly 5)
    (N : Fin 6 → HodgeComputer.AmbientPoly 5),
  S.IsHomogeneous e ∧ ¬ HodgeSubmission.F ∣ S ∧
  (∀ i, HodgeComputer.Homogeneous (N i) (2 * (e : ℤ) + 7)) ∧
  CycleQ2Bridge.LocalizedEquation
    HodgeSubmission.F HodgeSubmission.A 2 (S ^ 2) N
```

`CycleQ2FormalInputs.protected_certificate_iff_square_primitive` binds this
equivalence to the protected target. No proof of this existential is supplied
by the new helpers. In the intended nonconstructive route, geometric support
and the filtered de Rham argument must provide it.

The existing polynomial-curve constructors require polynomial coordinates,
normal fields, or densities in a parameter. An algebraic Hilbert parameter
curve alone does not establish those hypotheses. Likewise, the existing
arithmetic-lifting theorem needs an identified square polynomial incidence
system with a nonsingular seed; the Noether--Lefschetz rank matrix is not
automatically such an incidence Jacobian. These constructions therefore do
not yet close this obligation.

## Preserved current route

All `Current*.lean` files remain unchanged, but are no longer imported by the
active entry point. [CurrentData.lean](CurrentData.lean) retains its 13,874
expressions and literal `transportError`, whose vanishing is not assumed.
[CurrentCorrection.lean](CurrentCorrection.lean) retains reconstruction and
`originalGoal_iff_actual_current_correction`: a future geometric proof would
also yield that correction existential, without making it a premise.
The denominator, normal-gauge, tangent and ambient-lift developments remain
available in their original files. No protected record, shared library,
verifier, workflow, generated file, or proof-manifest field is changed.

## Verification

Lean 4.33.1 is now installed, and compilation uses the repository's pinned
mathlib revision `0df444a360eaa60ab8c11dca51a86af692955474`. The original
`Workspace`, `GeometricTarget`, and `GeometricSeed` modules compile and pass
independent `leanchecker` replay. Minimal tactic fixes reduce the beta
vector literals, finish the gamma ring identity, and explicitly expand the
seed's matrix multiplication. Statements and numerical data are unchanged.

The new exact gradient, irreducibility, finite averaging, and localized
certificate bridge components also compile and pass kernel replay. Their
printed dependencies are exactly `propext`, `Classical.choice`, and
`Quot.sound`. The finite Higgs calculation, including the scalar-commutant
and trivial-projector theorems, also passes both checks. The consolidated
`Proposal.GeometricFormalInputs` module compiles and passes independent
kernel replay, including its exact-target equivalence. Compilation took
277.474 seconds with a 6 GiB development memory cap; replay took 31.292
seconds. The new helper also passes the protected source-policy check.

The checked consolidated source has SHA-256
`c2feeabced7e719067869d48ea255cb375ab1b90621763285ef108617ff06156`.
The unchanged protected target was generated from base commit
`e3936ff366ae2302f21fb9e5730bbbd284c81d69`; the development began at PR head
`c8a524e7b22ae9d6a1a3728ce3c081ddb01368d4`. The source comparison confirms
that the protected instance and shared formal library still match that base.

These are development compilation and kernel-replay checks, separate from
the protected sandbox verifier. `Submission.certificate` still depends on
the original admitted geometric bridge and is not an accepted certificate.
The proposal has 64 permitted files. No protected equation, source, verifier,
workflow, or proof-manifest field has been changed.

The repository content build, record validation, and local-link/KaTeX checks
also pass. These prose and record checks do not establish the certificate.

## Attribution

The geometric route is the Chapter 3D argument of `benediamond` and
collaborators in [Discussion #61](https://github.com/hodge-computer/sextics/discussions/61),
using Claire Voisin's moving-cycle strategy, Griffiths residue and Abel--Jacobi
formulas, Dolgachev's weighted residues, Aoki--Shioda-type cycles studied by
Braun--Fortin--Lopez Garcia--Villaflor Loyola, and the references of Chapters
3 and 1. The earlier work of `hodgepodgeconjecture`, `DiamondJM`, `fqlx`, and
the Hodge Computer collaborators remains preserved and credited. The sparse
seed and this draft refactor were prepared for `fqlx` with OpenAI ChatGPT assistance.
