import Proposal.SymmetricPrimitiveEndpoint
import HodgeComputer.Constructions.ResidueTransport.CoefficientReduction

/-!
# Coefficient-field reduction on the actual symmetric chart

The generic coefficient reduction is instantiated with the constructed
function field and its three canonical relative tangent derivatives.
Only coefficient numerators, a denominator and their matching identity
remain as inputs. No alternative field or unproved chart derivative is
introduced.
-/

noncomputable section

namespace SymmetricCoefficientReduction

open MvPolynomial HoldoutConstruction WeightedPrimitiveTransport
open SymmetricAffineField SymmetricPrimitiveEndpoint
open ResidueCoefficientReduction
open scoped BigOperators

def weightedMap : Poly →+* FunctionField := residueMap.comp squareLift

def basePartial (i : Fin 3) : Derivation ℤ Poly Poly :=
  integerPartial i.succ.castSucc

def relativeTangent (i : Fin 3) : Derivation ℤ FunctionField FunctionField :=
  tangent i.succ

theorem weightedMap_equation : weightedMap rawWeighted = 0 := by
  change residueMap chartEquation = 0
  exact (residueMap_kernel chartEquation).mpr dvd_rfl

theorem weightedMap_normal : weightedMap (normalPartial rawWeighted) ≠ 0 :=
  weighted_normal_nonzero

theorem canonical_tangents :
    ImplicitTangents weightedMap normalPartial basePartial relativeTangent rawWeighted := by
  intro i p
  exact chartTangent_squareLift quotient quotient_surjective quotient_kernel
    normal_nonzero i.succ p

theorem normal_base_commute (i : Fin 3) (p : Poly) :
    normalPartial (basePartial i p) = basePartial i (normalPartial p) :=
  integerPartial_commute _ _ _

theorem residueDensity_eq : residueDensity =
    2*(weightedMap (normalPartial rawWeighted)*weightedMap (normalPartial rawSource)-
      weightedMap (normalPartial (normalPartial rawWeighted))*weightedMap rawSource)/
        (weightedMap (normalPartial rawWeighted))^3 := rfl

theorem relativePrimitive_iff :
    Nonempty RelativePrimitive ↔ HasPrimitive relativeTangent residueDensity := by
  constructor
  · rintro ⟨beta⟩
    exact ⟨beta.coefficient, beta.differential_eq⟩
  · rintro ⟨beta, hbeta⟩
    exact ⟨⟨beta, hbeta⟩⟩

/-- The concrete correction supplied by a normal-independent coefficient field. -/
theorem reduction (h J : Poly) (Z : Fin 3 → Poly)
    (hJ0 : weightedMap J ≠ 0)
    (hZ : ∀ i, normalPartial (Z i) = 0) (hJ : normalPartial J = 0)
    (hmatch : (∑ i, Z i*basePartial i rawWeighted) = J*(rawSource+h*rawWeighted)) :
    divergence relativeTangent
        (fun i => -2*(weightedMap (Z i)/weightedMap J)/
          weightedMap (normalPartial rawWeighted)) =
      residueDensity -
        2*(coefficientDivergence weightedMap basePartial J Z-weightedMap h)/
          weightedMap (normalPartial rawWeighted) := by
  rw [residueDensity_eq]
  exact cleared_coefficient_reduction weightedMap normalPartial basePartial relativeTangent
    rawWeighted rawSource h J Z weightedMap_equation weightedMap_normal hJ0
    canonical_tangents hZ hJ (fun i => normal_base_commute i rawWeighted) hmatch

/-- The protected relative primitive exists exactly when the residual
simple-normal-pole equation has a solution. -/
theorem relativePrimitive_iff_residual (h J : Poly) (Z : Fin 3 → Poly)
    (hJ0 : weightedMap J ≠ 0)
    (hZ : ∀ i, normalPartial (Z i) = 0) (hJ : normalPartial J = 0)
    (hmatch : (∑ i, Z i*basePartial i rawWeighted) = J*(rawSource+h*rawWeighted)) :
    Nonempty RelativePrimitive ↔
      HasPrimitive relativeTangent
        (2*(coefficientDivergence weightedMap basePartial J Z-weightedMap h)/
          weightedMap (normalPartial rawWeighted)) := by
  rw [relativePrimitive_iff]
  exact hasPrimitive_iff_of_reduction relativeTangent _ _ _
    (reduction h J Z hJ0 hZ hJ hmatch)

/-- A solution of the reduced equation produces the original primitive by
adding the displayed high-pole correction. -/
def relativePrimitiveOfResidual (h J : Poly) (Z : Fin 3 → Poly)
    (hJ0 : weightedMap J ≠ 0)
    (hZ : ∀ i, normalPartial (Z i) = 0) (hJ : normalPartial J = 0)
    (hmatch : (∑ i, Z i*basePartial i rawWeighted) = J*(rawSource+h*rawWeighted))
    (gamma : Fin 3 → FunctionField)
    (hgamma : divergence relativeTangent gamma =
      2*(coefficientDivergence weightedMap basePartial J Z-weightedMap h)/
        weightedMap (normalPartial rawWeighted)) : RelativePrimitive where
  coefficient := (fun i => -2*(weightedMap (Z i)/weightedMap J)/
    weightedMap (normalPartial rawWeighted)) + gamma
  differential_eq := by
    change divergence relativeTangent _ = _
    rw [divergence_add, reduction h J Z hJ0 hZ hJ hmatch, hgamma]
    ring

#print axioms canonical_tangents
#print axioms relativePrimitive_iff_residual
#print axioms relativePrimitiveOfResidual

end SymmetricCoefficientReduction
