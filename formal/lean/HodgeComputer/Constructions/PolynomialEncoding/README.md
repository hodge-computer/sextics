# Polynomial encodings for exact coefficient identities

These modules justify the finite encodings by which a large polynomial identity is checked coefficient by coefficient. They do not depend on a cubic family or on a target.

They come from `hodgepodgeconjecture`'s [cyclic construction](https://github.com/hodge-computer/sextics/pull/165). `BivariateDifferentiation` was added in `fqlx`'s [mixed-biweight construction](https://github.com/hodge-computer/sextics/pull/170). Both were prepared with OpenAI Codex assistance.

Import the individual modules. Declarations lie in the namespaces `PolynomialEncoding.SignedExpressions`, `PolynomialEncoding.BivariateExpressions` and `PolynomialEncoding.PolynomialDigits`.

- `SignedExpressions` splits a ring expression into two semiring expressions and proves that their difference evaluates to the original expression.
- `BivariateExpressions` defines sparse bivariate polynomials whose coefficients are ring expressions, and proves that their sum and product preserve evaluation.
- `BivariateDifferentiation` differentiates these polynomials in each variable and proves agreement with the partial derivatives of their evaluation.
- `PolynomialDigitCheck` proves that evaluation at `b` is injective on polynomials with natural coefficients whose coefficient sum is less than `b`.

The [transitive cubic package](../TransitiveCubic/README.md) applies them, as do the cyclic and polar cubic families proved in [cycle-three](../../../../../data/cycle-three/solution.md) and [mixed-polar](../../../../../data/mixed-polar/solution.md). Each family keeps its own monomial weights, grade check and coefficient tables.
