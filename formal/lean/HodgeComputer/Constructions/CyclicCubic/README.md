# Cyclic ternary cubics

The coefficient-parameterized family is

\[
U=a x^3+b y^3+c z^3+d x^2 y+e y^2 z+f z^2 x.
\]

`hodgepodgeconjecture`’s [cycle-three construction](../../../../../data/cycle-three/solution.md) ([#165](https://github.com/hodge-computer/sextics/pull/165)) proves its exact covariant syzygy and invariant differential. The classical normalization follows Tom Fisher and SageMath, as credited in that explanation; the original formalization used OpenAI Codex assistance. The accepted application now imports these identities instead of carrying a second copy.

Import `HodgeComputer.Constructions.CyclicCubic`, or the individual modules. Declaration namespaces begin with `CycleCubic` and `CycleCovariants`.

- `Cubic` defines the polynomial and its coefficient invariants `s4`, `s6`.
- `Covariants` defines the integral polynomials `H`, `Theta`, `J`.
- `Syzygy` proves the full polynomial identity, including the multiple of the cubic before restriction to its zero set.
- `Map` proves `CycleCubicMap.differential` for the rational map `xi = Theta/H²`, `eta = -J/(2H³)`, with explicit nonvanishing and derivation hypotheses.
- `Functorial` and `Diagonal` supply coefficient substitution and diagonal specializations.
- `CoefficientsA`–`CoefficientsH` and the encoding modules contain the exact coefficient proofs supporting these theorems. The family-independent encodings are the shared [PolynomialEncoding](../PolynomialEncoding/README.md) modules.

The [transitive cubic](../TransitiveCubic/README.md) has `f x²z` in place of `f z²x`; its covariants are different. Matching file shapes do not identify these two families.

The physical paired-sign reduction, coefficient specialization, incidence seed, Jacobian primitive and source transport remain in `data/cycle-three/`. The general first-variation calculus is shared through [ResidueTransport](../ResidueTransport/README.md).
