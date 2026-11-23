# Polynomial encodings for exact coefficient identities

These modules justify the finite encodings by which a large polynomial identity is checked coefficient by coefficient. They do not depend on a cubic family or on a target.

They come from `hodgepodgeconjecture`'s [cyclic construction](../../../../../data/cycle-three/solution.md). `BivariateDifferentiation` was added in `fqlx`'s [mixed-biweight construction](../../../../../data/mixed-biweight/solution.md). Both were prepared with OpenAI Codex assistance. `KroneckerCheck` and `PolyOps` were extracted from `benediamond`'s [symmetric-sextic-residual construction](../../../../../data/symmetric-sextic-residual/solution.md).

Import the individual modules. Declarations lie in the namespaces `PolynomialEncoding.SignedExpressions`, `PolynomialEncoding.BivariateExpressions`, `PolynomialEncoding.PolynomialDigits`, `PolynomialEncoding.KroneckerCheck`, and `PolynomialEncoding.PolyOps`.

- `SignedExpressions` splits a ring expression into two semiring expressions and proves that their difference evaluates to the original expression.
- `BivariateExpressions` defines sparse bivariate polynomials whose coefficients are ring expressions, and proves that their sum and product preserve evaluation.
- `BivariateDifferentiation` differentiates these polynomials in each variable and proves agreement with the partial derivatives of their evaluation.
- `PolynomialDigitCheck` proves that evaluation at `b` is injective on polynomials with natural coefficients whose coefficient sum is less than `b`.
- `KroneckerCheck` provides multi-variable mixed-radix Kronecker positional encoding (`identity_of_kronecker`, `identity_of_kronecker2`, `identity_of_kronecker3`, `biv_denote_eq_of_kronecker3`), the polymorphic ring-backend abstraction `PolyOps` / `PolyOpsRel` / `letB`, and factored 3-variable hybrid Kronecker × grid soundness theorems (`mvPoly3_eq_zero_of_kronecker_grid`, `mvPoly3_eq_zero_of_kronecker2D_gridT`).
- `PolyOps` provides dense univariate (`UPoly`), bivariate (`BivL`), and trivariate (`UBivL`) list-polynomial arithmetic over any `PolyOps` backend, together with relational lifts, synthetic division by `X - 1`, quadratic-relation reduction (`bivRedOnce`), bilinear weight contraction (`dotW` / `combineBivDot`), and ring-evaluation homomorphisms.

The [transitive cubic package](../TransitiveCubic/README.md) applies them, as do the cyclic cubic family proved in [cycle-three](../../../../../data/cycle-three/solution.md) and the moving-line residue cancellation proof in [symmetric-sextic-residual](../../../../../data/symmetric-sextic-residual/solution.md). Each family keeps its own monomial weights, grade check, and coefficient tables.
