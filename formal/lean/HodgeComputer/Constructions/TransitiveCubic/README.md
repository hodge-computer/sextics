# Transitive ternary cubics

This library supplies exact covariants for the six-coefficient family

\[
U=ax^3+by^3+cz^3+dx^2y+ey^2z+fx^2z.
\]

The coefficients are arbitrary. The library proves polynomial identities for this family; it does not assert that every sextic with a paired-sign quotient has a certificate.

## Entry points

Import `HodgeComputer.Constructions.TransitiveCubic` for the covariant library, or an individual module below.

- `Cubic` defines the equation and invariants `s4`, `s6`.
- `Covariants` defines integral `H`, `Theta`, and `J`.
- `Syzygy` proves their identity on the affine chart `z=1`, including its multiple of `U` before restriction.
- `Map` supplies the invariant-differential identity for the rational map `xi=Theta/H²`, `eta=−J/(2H³)`, with its nonzero-denominator hypotheses.
- `Functorial` transports the polynomial covariants through ring homomorphisms; `Diagonal` provides a useful diagonal specialization.

`ReflectionData`, `IdentityData`, `IdentityProducts`, `IdentityEvaluation`, `CoefficientsA`–`CoefficientsH`, and `Differential` contain the exact coefficient proofs. `Kronecker`, `GradeCheck`, `EncodingCheck`, `SignedExpressions`, `BivariateExpressions`, `BivariateDifferentiation`, and `PolynomialDigitCheck` justify their finite polynomial encodings. These are proof infrastructure for the stated identities, not numerical samples or additional geometric assumptions.

The normalization is

\[
J^2=4\Theta^3+4s_4\Theta H^4-s_6H^6\quad(U=0),
\qquad \frac{D_y\xi}{2\eta}=\frac3{U_x}.
\]

An application still constructs the relevant Jacobian family, a primitive on it, and the exact physical source transport, including the moving-map and normal-density corrections. Nonsingular incidence seeds, the physical sextic, and certificate closure remain in the application.

## Attribution and applications

Extracted from `fqlx`'s accepted [mixed-biweight construction](https://github.com/hodge-computer/sextics/pull/170), which adapts the cubic machinery and polynomial encodings of `hodgepodgeconjecture`'s [cyclic construction](https://github.com/hodge-computer/sextics/pull/165). The classical covariant normalization follows Tom Fisher and SageMath, as credited in those constructions. Both submissions were prepared with OpenAI Codex assistance. The shared copy uses `Transitive…` namespaces to distinguish this family from the directed cyclic family.

The accepted mixed-biweight application imports these modules directly. Its physical equation, incidence construction, coefficient specializations, and certificate closure remain in `data/mixed-biweight/`.
