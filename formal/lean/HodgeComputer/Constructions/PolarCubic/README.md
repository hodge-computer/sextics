# Reverse-edge cubic covariants and first-order identities

This package treats the coefficient family

\[
U=a x^3+b y^3+c z^3+d x^2y+e y^2z+f xy^2
\]

and its perturbation `U + 2kxyz` to first order in a square-zero parameter. The coefficients are arbitrary; the identities do not fix a physical sextic or an incidence seed.

The construction comes from `benediamond`’s [mixed-polar proof](../../../../../data/mixed-polar/solution.md) ([#182](https://github.com/hodge-computer/sextics/pull/182)), extending the cyclic work of `hodgepodgeconjecture` and its transitive adaptation by `fqlx`, with OpenAI Codex assistance. The accepted explanation records the classical invariant-theory normalization, collaborators and prior work. Public declaration namespaces include `PolarCubic`, `PolarCovariants` and `PolarCubicMap`.

Import `HodgeComputer.Constructions.PolarCubic` or an individual module:

- `Covariants` defines the cubic, integral covariants, coefficient invariants and their first-order variations.
- `Syzygy` proves the polynomial covariant relation and its first-order version.
- `Differential` proves the cleared invariant-differential identities and their first-order versions.
- `Map` proves `PolarCubicMap.differential` with explicit normal-chart and nonvanishing hypotheses.
- `Functorial` transports the expressions through coefficient maps.
- `CoefficientExpressions`, `Bivariate`, `Encoding`, the identity tables, `CoefficientsA`–`CoefficientsD` and differential tables implement the exact coefficient proofs. They use the shared [PolynomialEncoding](../PolynomialEncoding/README.md) modules; their coefficients are different.

Square-zero evaluation and the subsequent first-variation calculus are shared with [ResidueTransport.FirstJets](../ResidueTransport/FirstJets.lean). The application still supplies the physical coefficients, Jacobian family, primitive, normal correction and balanced source identity. A first-order identity is not a full polynomial identity at arbitrary nonzero `k`.
