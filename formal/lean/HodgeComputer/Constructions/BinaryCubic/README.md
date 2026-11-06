# Binary-cubic covariants and radial cancellation

This package extracts the coefficient-polynomial core of `benediamond`’s [dense two-ternary Hessian construction](../../../../../data/two-ternary-dense-two-odd-hessian-d48/solution.md) ([#41](https://github.com/hodge-computer/sextics/pull/41)). Its mathematical attribution and assistance disclosure remain in that explanation. The declaration namespace is `HodgeTestbed.EllipticAmbient.Cubic`.

`Data R` consists of four arbitrary coefficients of a binary cubic. `Covariants` evaluates the cubic and its derivatives at the affine coordinate one, defines the Hessian and discriminant expressions, and proves the division-free identities `t_square`, `k_H`, and `mixed_bridge` over commutative rings.

`RadialIdentity` proves `radial_scalar_identity`, which gives the universal polynomial cancellation for a pair of such coefficient tuples. `Derivatives` proves `weighted_derivatives`, which binds the formal radial expressions to a genuine derivation when the four coefficients have weights `0, 2, 4, 6`; `constant_derivatives` handles independent blocks.

An application must establish those coefficient weights, nonvanishing, coordinate embeddings, homogeneous degrees and denominator legality. The package does not turn arbitrary pairs of cubics into certificates without these checks. See [RationalFields](../RationalFields/README.md) for the surrounding field calculus and affine-to-projective transfer.
