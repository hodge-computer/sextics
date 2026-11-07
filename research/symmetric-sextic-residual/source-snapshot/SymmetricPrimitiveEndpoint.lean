import SymmetricAffineField
import WeightedPrimitiveTransport

/-!
# Exact primitive equation for the protected symmetric sextic

The quotient, its function field, its nonzero normal, and its canonical
tangent derivations are constructed for the actual polynomial. A relative
primitive has three coefficients and one explicit differential equation.

`clear_relative_primitive` proves the downstream legal polynomial identities.
This module does not prove that a `RelativePrimitive` exists. No such
existence theorem is postulated or admitted.
-/

noncomputable section

namespace SymmetricPrimitiveEndpoint

open MvPolynomial HoldoutConstruction
open WeightedPrimitiveTransport SymmetricAffineField
open scoped BigOperators

set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

def tangent (i : Fin 4) : Derivation ℤ FunctionField FunctionField :=
  chartTangent quotient quotient_surjective quotient_kernel normal_nonzero i

def residueDensity : FunctionField :=
  residueCoefficient residueMap rawWeighted rawSource

/-- Coefficients of beta = b0 dc∧dd - b1 db∧dd + b2 db∧dc.
The field is the actual chart function field; the tangent operators are
canonical. Constructing an inhabitant is the remaining existence problem. -/
structure RelativePrimitive where
  coefficient : Fin 3 → FunctionField
  differential_eq : (∑ i : Fin 3, tangent i.succ (coefficient i)) = residueDensity

/-- The actual four-component current; its lambda component is zero. -/
def current (beta : RelativePrimitive) : Fin 4 → FunctionField :=
  relativeCurrent (residueMap (normalPartial chartEquation)) beta.coefficient

theorem current_lambda (beta : RelativePrimitive) : current beta 0 = 0 := rfl

theorem current_relative (beta : RelativePrimitive) (i : Fin 3) :
    current beta i.succ =
      -residueMap (normalPartial chartEquation) * beta.coefficient i := rfl

theorem extend_self (D : Derivation ℤ FunctionField FunctionField) (x : FunctionField) :
    extendFiniteDerivation (L := FunctionField) D x = D x := by
  simpa using extendFiniteDerivation_apply (L := FunctionField) D x

/-- Legal affine polynomial data, with every chart hypothesis discharged.
The only input is an actual relative primitive. -/
theorem clear_relative_primitive (beta : RelativePrimitive) :
    ∃ D Nv : Poly, ∃ N : Fin 4 → Poly, ∃ Q : Poly,
      D ≠ 0 ∧ IsRelPrime chartEquation D ∧
      (Nv * normalPartial chartEquation +
        ∑ i, N i * tangentPartial i chartEquation = chartSource * D) ∧
      (residueDivNum normalPartial tangentPartial D Nv N = chartEquation * Q) ∧
      chartSource * D^2 - D * (Nv * normalPartial chartEquation +
        ∑ i, N i * tangentPartial i chartEquation) +
        chartEquation * residueDivNum normalPartial tangentPartial D Nv N =
          chartEquation^2 * Q := by
  apply exact_chart_clearing_of_relative_primitive (K := FunctionField)
    (L := FunctionField) quotient quotient_surjective quotient_kernel
    SymmetricAffinePrime.chart_irreducible normal_nonzero beta.coefficient
  simpa only [extend_self, Algebra.algebraMap_self, RingHom.id_apply,
    tangent, residueDensity, residueMap] using
    beta.differential_eq

#print axioms tangent
#print axioms current_lambda
#print axioms current_relative
#print axioms clear_relative_primitive

end SymmetricPrimitiveEndpoint
