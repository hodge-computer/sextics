import Proposal.CurrentVerifierBridge
import HodgeComputer.Constructions.FiniteAlgebra.FractionDerivation
import Mathlib.RingTheory.Derivation.Lie

/-!
# Actual coordinate derivations on the rational function field

This constructs, rather than assumes, the polynomial embedding and commuting
coordinate derivations used by the regular-current certificate endpoint.
The field is the fraction field of the full polynomial ring. It is not the
function field of the hypersurface, and no geometric comparison is assumed.
-/

noncomputable section

namespace CanonicalFractionCoordinates

open HodgeComputer MvPolynomial CurrentVerifierBridge

/-- A type wrapper keeps the field and scalar-module instances coherent. -/
def RationalFunctionField (n : ℕ) := FractionRing (AmbientPoly n)

instance (n : ℕ) : Field (RationalFunctionField n) :=
  inferInstanceAs (Field (FractionRing (AmbientPoly n)))

instance (n : ℕ) : Algebra (AmbientPoly n) (RationalFunctionField n) :=
  inferInstanceAs (Algebra (AmbientPoly n) (FractionRing (AmbientPoly n)))

instance (n : ℕ) : IsFractionRing (AmbientPoly n) (RationalFunctionField n) :=
  inferInstanceAs (IsFractionRing (AmbientPoly n) (FractionRing (AmbientPoly n)))

instance (n : ℕ) : CharZero (RationalFunctionField n) :=
  inferInstanceAs (CharZero (FractionRing (AmbientPoly n)))

def coordinateDerivative (n : ℕ) (i : Fin (n+1)) :
    Derivation ℚ (RationalFunctionField n) (RationalFunctionField n) :=
  QuadricContactFraction.extend (P := AmbientPoly n) (F := RationalFunctionField n)
    ((pderiv i).restrictScalars ℚ)

@[simp] theorem coordinateDerivative_polynomial (n : ℕ) (i : Fin (n+1))
    (P : AmbientPoly n) :
    coordinateDerivative n i
      (algebraMap (AmbientPoly n) (RationalFunctionField n) P) =
      algebraMap (AmbientPoly n) (RationalFunctionField n) (pderiv i P) :=
  QuadricContactFraction.extend_map
    ((pderiv i : Derivation ℂ (AmbientPoly n) (AmbientPoly n)).restrictScalars ℚ) P

def coordinates (n : ℕ) : PolynomialCoordinates n (RationalFunctionField n) where
  embed := algebraMap (AmbientPoly n) (RationalFunctionField n)
  injective := IsFractionRing.injective _ _
  derivative := coordinateDerivative n
  compatible := coordinateDerivative_polynomial n

/-- The polynomial commutator is a derivation vanishing on every generator. -/
theorem polynomial_partials_commute (n : ℕ) (i j : Fin (n+1)) (P : AmbientPoly n) :
    pderiv i (pderiv j P) = pderiv j (pderiv i P) := by
  have h : ⁅(pderiv i : Derivation ℂ (AmbientPoly n) (AmbientPoly n)),
      (pderiv j : Derivation ℂ (AmbientPoly n) (AmbientPoly n))⁆ = 0 := by
    apply MvPolynomial.derivation_ext
    intro k
    simp [Derivation.commutator_apply, MvPolynomial.pderiv_X, Pi.single_apply, apply_ite]
  have hp := DFunLike.congr_fun h P
  exact sub_eq_zero.mp (by simpa only [Derivation.commutator_apply,
    Derivation.zero_apply] using hp)

/-- A commutator vanishing on polynomials vanishes on every fraction by its
own quotient rule; a second-derivative expansion is unnecessary. -/
theorem coordinate_derivatives_commute (n : ℕ) (i j : Fin (n+1))
    (x : RationalFunctionField n) :
    coordinateDerivative n i (coordinateDerivative n j x) =
      coordinateDerivative n j (coordinateDerivative n i x) := by
  have hon (P : AmbientPoly n) :
      ⁅coordinateDerivative n i, coordinateDerivative n j⁆
        (algebraMap (AmbientPoly n) (RationalFunctionField n) P) = 0 := by
    simp only [Derivation.commutator_apply, coordinateDerivative_polynomial,
      polynomial_partials_commute n i j P, sub_self]
  have h : ⁅coordinateDerivative n i, coordinateDerivative n j⁆ x = 0 := by
    obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective (AmbientPoly n) x
    simp [Derivation.leibniz_div, hon]
  exact sub_eq_zero.mp h

theorem coordinates_commute (n : ℕ) (i j : Fin (n+1))
    (x : RationalFunctionField n) :
    (coordinates n).derivative i ((coordinates n).derivative j x) =
      (coordinates n).derivative j ((coordinates n).derivative i x) :=
  coordinate_derivatives_commute n i j x

#print axioms coordinateDerivative_polynomial
#print axioms polynomial_partials_commute
#print axioms coordinate_derivatives_commute

end CanonicalFractionCoordinates
