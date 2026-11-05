# Polynomial curves, arithmetic lifting and certificates

These modules extract target-independent steps from the constructions of
`fqlx` ([PR #150](https://github.com/hodge-computer/sextics/pull/150)) and
`hodgepodgeconjecture` ([PR #151](https://github.com/hodge-computer/sextics/pull/151)).
They build on the maintained
[HoldoutCover library](../HoldoutCover/README.md), with its attribution to
`fqlx`, `HeadOfNaps`, and the Lean/mathlib contributors. The original submissions
disclose AI assistance; this extraction was prepared with Codex assistance for
`benediamond`.

The original namespaces are retained. Import the shared version of a helper
instead of the identically named declarations in its original submission.
Accepted instance files remain unchanged.

| Module | Interface | Application obligation |
| --- | --- | --- |
| `ArithmeticLifting` | `ReflectionCoupledFano.square_system_generic_lift` | An actual special-fiber solution, invertible square Jacobian, and injective map from the integral coefficient ring to the desired generic field. |
| `ArithmeticLifting` | `ReflectionCoupledFano.anchored_polynomial_family_injective` | Independent constant terms, and a nonzero distinguished polynomial coordinate with zero constant term. The coordinate need not be linear. |
| `OpenIncidence` | `ReflectionCoupledFano.openSquare_exists_fieldFactor` | The same incidence data, with one chosen coordinate also a unit at the seed. The finite generic solution preserves both units. |
| `ComplexPoint` | `DeformedConic.complex_point_of_etale_nontrivial` | Nontriviality of the Jacobian-localized integral square incidence. A finite field factor embeds into the algebraically closed complex field. |
| `NormalizedCertificate` | `ReflectionCoupledFano.normalized_data_from_polynomial_family` | A domain for the six-variable hypersurface, a finite extension of its function field, a polynomial normal, commuting derivations, and a nonzero normal/tangent determinant. |

The last theorem supplies unrestricted normalized polynomial data with a legal
denominator. An application must still prove its coordinate transport, exact
target identity, and homogeneous certificate statement. It does not search for
a curve, assert that a finite-field point alone lifts, or supply a numerical
denominator bound.

For worked applications, see the original
[reflection quotient](../../../../../data/reflection-coupled-fano/solution.md)
and [deformed conic](../../../../../data/holdout-ternary-deformation/solution.md).
