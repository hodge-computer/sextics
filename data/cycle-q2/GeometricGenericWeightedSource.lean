import Proposal.GeometricGenericWeightedCoordinates
import Proposal.GeometricFormalInputs04

/-!
# The weighted numerator in the generic pencil

Multiplying by the coordinate ratio recovers the protected numerator
and both of its normal derivatives. The scaling therefore holds for
the full generic residue density in every pencil direction.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace CycleQ2GenericWeightedSource

open MvPolynomial CycleQ2Bridge CycleQ2AffineClearing CycleQ2GenericSpecialization
  CycleQ2GenericWeightedCoordinates
open CycleQ2AffineWeightedTransfer
  (weightedSource source_product source_first_jet_product source_second_jet_product)

theorem weightedSource_value :
    polynomialMap 4 weightedSource = z 0 ^ 2 * z 2 ^ 2 * z 3 ^ 2 * (u ^ 2) ^ 2 := by
  simp only [weightedSource, map_mul, map_pow]
  change z 0 ^ 2 * u ^ 4 * z 2 ^ 2 * z 3 ^ 2 = _
  ring

private theorem weightedSource_derivative :
    pderiv 0 weightedSource = 2 * X 0 * X 1 ^ 4 * X 2 ^ 2 * X 3 ^ 2 := by
  simp only [weightedSource, pderiv_mul, pderiv_pow, pderiv_X_self,
    pderiv_X_of_ne (R := ℂ) (by decide : (1 : Fin 5) ≠ 0),
    pderiv_X_of_ne (R := ℂ) (by decide : (2 : Fin 5) ≠ 0),
    pderiv_X_of_ne (R := ℂ) (by decide : (3 : Fin 5) ≠ 0)]
  norm_num

theorem weightedSource_firstJet_value :
    polynomialMap 4 (pderiv 0 weightedSource) = 2 * z 0 * z 2 ^ 2 * z 3 ^ 2 * (u ^ 2) ^ 2 := by
  rw [weightedSource_derivative]
  simp only [map_mul, map_pow, map_ofNat]
  change 2 * z 0 * u ^ 4 * z 2 ^ 2 * z 3 ^ 2 = _
  ring

theorem weightedSource_secondJet_value :
    polynomialMap 4 (pderiv 0 (pderiv 0 weightedSource)) = 2 * z 2 ^ 2 * z 3 ^ 2 * (u ^ 2) ^ 2 := by
  have h : pderiv 0 (pderiv 0 weightedSource) = 2 * X 1 ^ 4 * X 2 ^ 2 * X 3 ^ 2 := by
    have h₂ : pderiv 0 (2 : Poly) = 0 := (pderiv 0).map_natCast 2
    rw [weightedSource_derivative]
    simp only [pderiv_mul, pderiv_pow, pderiv_X_self, h₂,
      pderiv_X_of_ne (R := ℂ) (by decide : (1 : Fin 5) ≠ 0),
      pderiv_X_of_ne (R := ℂ) (by decide : (2 : Fin 5) ≠ 0),
      pderiv_X_of_ne (R := ℂ) (by decide : (3 : Fin 5) ≠ 0)]
    norm_num
  rw [h]
  simp only [map_mul, map_pow, map_ofNat]
  change 2 * u ^ 4 * z 2 ^ 2 * z 3 ^ 2 = _
  ring

private theorem mapped_ratio (P Q : Poly) (h : P * X 1 = Q * X 4) :
    polynomialMap 4 P = lambda * polynomialMap 4 Q := by
  have he := congrArg (polynomialMap 4) h
  simp only [map_mul] at he
  change polynomialMap 4 P * u = polynomialMap 4 Q * v at he
  rw [(eq_div_iff u_ne_zero).mpr he]
  change polynomialMap 4 Q * v / u = v / u * polynomialMap 4 Q
  ring

theorem genericDensity_source_ratio (d : Direction) :
    genericDensity d affineA = lambda * genericDensity d weightedSource := by
  have h₀ := mapped_ratio _ _ source_product
  have h₁ := mapped_ratio _ _ source_first_jet_product
  have h₂ := mapped_ratio _ _ source_second_jet_product
  simp only [genericDensity, SplitHigherResidue.normalSourceTwo, h₀, h₁, h₂]
  ring

end CycleQ2GenericWeightedSource

end

#print axioms CycleQ2GenericWeightedSource.weightedSource_value
#print axioms CycleQ2GenericWeightedSource.weightedSource_firstJet_value
#print axioms CycleQ2GenericWeightedSource.weightedSource_secondJet_value
#print axioms CycleQ2GenericWeightedSource.genericDensity_source_ratio
