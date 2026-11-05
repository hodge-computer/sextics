# The formal acceptance contract

The live challenge's target is existence, not minimization of the degree of a denominator. A constructive and a nonconstructive Lean proof must prove the same statement for an immutable `(F,q,A)`.

Let `R = ℂ[X0,X1,X2,Y0,Y1,Y2]`. For the chosen sextic `F`, pole parameter `q`, and homogeneous odd target `A`, the statement asks for a nonzero homogeneous `D` and a six-tuple `N` such that:

- `D` is relatively prime to `F`.
- Each `Nᵢ` is homogeneous of degree `deg(D) + 6q − 5`; zero components are allowed by the homogeneous predicate.
- The rational field `vᵢ = Nᵢ / D` satisfies `F^(q+1) ∣ A − q·dF(v) + F·div(v)` in the localization away from `F`.

The standing instances have positive integral `q`, `F(X,−Y)=F(X,Y)`, and `A(X,−Y)=−A(X,Y)`. Field parity may be enforced by averaging; it must not accidentally narrow the stated existential problem.

## A finite algebraic witness

Define the polynomial

```text
E = A D² − q D Σᵢ Nᵢ ∂ᵢF
    + F (D Σᵢ ∂ᵢNᵢ − Σᵢ Nᵢ ∂ᵢD).
```

Since `D` is invertible in the relevant localization, a witness for the equation is the exact polynomial identity `E = F^(q+1) Q`. A strict certificate has `E=0`. This cleared identity, together with homogeneity and denominator admissibility, is the constructive checker interface. The theorem `localization_identity` in `HodgeComputer/Verify.lean` establishes the bridge to the rational-vector-field statement.

## Protected verification

`formal/lean/HodgeComputer/Verify.lean` defines `Verify` and the existential `HasCertificate` over complex coefficients. Its localization identity justifies the cleared equation. The shared contract imposes no denominator-degree bound or extra parity condition on the witness.

The verifier generates a protected exact target from the base branch's record. Contributors prove its existential statement and, when exporting a JSON witness for display, an additional theorem about those exact witness polynomials. The protected pipeline compiles the source in isolation, replays its declarations with the kernel checker, and audits the statement and axioms. Allowed axioms are `propext`, `Classical.choice`, and `Quot.sound`.

A rational-coefficient identity transfers to complex coefficients, but denominator admissibility over the complex numbers must also be established. Do not infer complex coprimality merely from rational irreducibility. Nonconstructive proofs are allowed when they establish the same protected existential theorem.

The Lean project pins its toolchain and mathlib manifest. Instance-specific proofs belong to each instance's existing data folder and first enter through its solve PR. Reusable machinery from accepted proofs can be extracted into the shared library through a separate maintenance PR. A checked merge by the configured owner and a trusted acceptance receipt are required before the publisher derives solved status and leaderboard credit. See [the proposal specification](../CONTRIBUTING.md) and [verification workflow](../MAINTAINING.md#verification-sign-off-and-publication).

## Reusable constructions

The shared library is the Lean counterpart of the mathematical book: organized, reusable statements with explicit hypotheses and concrete applications. Keep exploratory calculations, unsuccessful searches, and target-specific closure arguments outside it. Preserve accepted instance sources as verification evidence; new applications import the maintained library.

[`HodgeComputer.Constructions.AveragingProjectors`](lean/HodgeComputer/Constructions/AveragingProjectors.lean) gives the algebraic mechanism of Chapter 3: if a family of operators has image in a stable submodule, every element of its generated two-sided ideal has image there. It uses Mathlib's colon ideal and subgroup averaging projector, with explicit hypotheses that the relevant invariant subspaces lie in the chosen submodule. This combines the parts served by several quotients and their group translates; geometric support, quotient transfer, and membership in the generated ideal remain application obligations.

[`HodgeComputer.CertificateOperations`](lean/HodgeComputer/CertificateOperations.lean) supplies `Verify.add` and `HasCertificate.add` for every positive pole order. It combines different legal denominators and retains both quotient remainders. `HasCertificate.zero` supplies the neutral source. These are the cleared-form operations of Chapter 1, extracted from `fqlx`'s [bundle assembly](https://github.com/hodge-computer/sextics/pull/161), which uses the addition formula in the accepted one-reflection construction.

[`HodgeComputer.Constructions.HoldoutCover`](lean/HodgeComputer/Constructions/HoldoutCover/README.md) contains the Fermat-cover and moving-conic machinery from `fqlx`'s accepted [holdout proof](https://github.com/hodge-computer/sextics/pull/128). The construction supplies a primitive for an arbitrary polynomial source on its weighted quotient; an application must prove the source and derivative identities that transport its own target back to the original sextic.

New holdout specializations can import `HodgeComputer.Constructions.HoldoutCover.GeneralizedCover` and apply `HoldoutGeneralization.certificate_of_source_pair`. The module also supplies the vanishing traces of the square and inverse square of the cover coordinate. These are ingredients for the fixed holdout sextic, not a theorem for arbitrary sextics or targets.

The original accepted files under `data/holdout/` remain unchanged as the source of the original verification record. New submissions use the maintained shared modules instead of copying those files. Imports retain the original declaration namespaces and mathematical attribution; do not import both copies into the same Lean module.

[`HodgeComputer.Constructions.AlgebraicSpecialization`](lean/HodgeComputer/Constructions/AlgebraicSpecialization.lean) proves nonvanishing at every algebraic root when an auxiliary polynomial specializes to a nonzero multiple of `(X - r)^m` and the tested polynomial is nonzero at `r`. `eval_ne_zero_of_coalescing_root_specialization` requires `m > 0`, a degree bound and the explicit kernel inclusion between coefficient maps; the quadratic-at-zero corollary is `eval_ne_zero_of_double_root_specialization`. Fixed-size resultants allow degree drops without specializing rational maps at poles. The criterion generalizes the quadratic argument in `fqlx`'s [shear construction](https://github.com/hodge-computer/sextics/discussions/58#discussioncomment-19111681), prepared with OpenAI Codex assistance.

[`HodgeComputer.Constructions.PolynomialCurves`](lean/HodgeComputer/Constructions/PolynomialCurves/README.md) contains arithmetic lifting and polynomial-family integration extracted from the accepted constructions of `fqlx` and `hodgepodgeconjecture`. It lifts a nonsingular square incidence system from a special fiber to a finite extension of the generic coefficient field, and converts a dominant polynomial-curve family with a polynomial normal into normalized certificate data. The [module guide](lean/HodgeComputer/Constructions/PolynomialCurves/README.md) lists the precise application obligations and original sources. These results supply reusable steps; each application still establishes its own incidence, dominance, coordinate transport, and exact target.

[`HodgeComputer.Constructions.EllipticCompanions`](lean/HodgeComputer/Constructions/EllipticCompanions/README.md) contains target-independent rational residue and translated elliptic-contraction machinery from `1337isnot1337`'s accepted [crossed-ternary construction](https://github.com/hodge-computer/sextics/pull/149). Its `Contraction` entry point combines two supplied scalar primitives into a product-divergence primitive, with explicit pole separation, infinity correction, and finite descent. Applications still construct their companion geometry and scalar primitives, prove the required derivative independence, and establish their exact physical target, denominator legality, and homogeneous degrees. This library does not extend the pole order of an existing companion theorem automatically.

[`HodgeComputer.Constructions.ResidueTransport`](lean/HodgeComputer/Constructions/ResidueTransport/README.md) contains the change-of-density Piola identity, moving-Weierstrass-map correction and generic first-variation calculus from `hodgepodgeconjecture`'s [cyclic cubic proof](https://github.com/hodge-computer/sextics/pull/165). Its fixed-parameter jet formulation retains the exact correction when a cubic map varies. `FirstJets` proves the polynomial chain rule over commutative rings, evaluates identities at square-zero elements, normalizes cleared covariant identities, and extracts the curve and differential variations from dual numbers. `NormalChange` supplies the paired-normal correction for a balanced source and the derivative-ratio identity for changing a source by a multiple of its normal, with explicit tangent and nonvanishing hypotheses. Applications still supply the auxiliary primitive, compatible polynomial identities, nonzero denominators, and physical source transport. These identities do not integrate arbitrary elliptic differentials.

[`HodgeComputer.Constructions.HigherResidues`](lean/HodgeComputer/Constructions/HigherResidues/README.md) provides the second-normal-residue calculus and polynomial-family integration for third-order poles, extracted from `fqlx`'s accepted split-ternary proof. It binds the numerator and determinant jets to actual derivatives and includes the tangent correction. Its entry point accepts a polynomial-curve family on a five-coordinate hypersurface; constructing that family, descent, and the final certificate remain application obligations.

[`HodgeComputer.Constructions.TransitiveCubic`](lean/HodgeComputer/Constructions/TransitiveCubic/README.md) contains the six-coefficient transitive cubic, its exact covariant syzygy, and invariant differential from `fqlx`'s [mixed-biweight construction](https://github.com/hodge-computer/sextics/pull/170), extending the cubic methods of `hodgepodgeconjecture`. `Shear` supplies the quadratic coordinate reduction and source variation from `fqlx`'s [shear construction](https://github.com/hodge-computer/sextics/discussions/58#discussioncomment-19111681), retaining their root and nonvanishing hypotheses. The physical equation, finite extension, incidence seed, and source transport remain application-specific.

[`ResidueTransport.CoordinateIndependence`](lean/HodgeComputer/Constructions/ResidueTransport/CoordinateIndependence.lean) proves that compatible coordinate derivations in characteristic zero make polynomial evaluation injective. It is the dominance criterion used by the cyclic and transitive cubic constructions; it does not assume the ambient field is purely transcendental.
