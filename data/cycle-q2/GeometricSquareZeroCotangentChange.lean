import Proposal.GeometricSquareZeroReducedCotangent

/-!
# The fixed sign of the actual cotangent splitting change

Two original algebra splittings induce two lifts into the genuine
reduced cotangent tensor module. Their difference is the original
epsilon inclusion composed with the faithfully normalized derivation
tau-sigma. The coefficient retractions and the corresponding pair
coordinates have the complementary transition signs.

Prepared for fqlx with OpenAI ChatGPT assistance; see solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2GeometricSquareZeroCotangentChange

open CycleQ2GeometricSquareZeroSplittings CycleQ2GeometricSquareZeroCoefficientDerivation
  CycleQ2GeometricSquareZeroReducedCotangent

variable {K E C : Type*} [CommRing K] [CommRing E] [CommRing C]
  [Algebra K E] [Algebra K C] [Algebra E C] [IsScalarTower K E C]
  (e : C ≃ₗ[E] RingHom.ker (algebraMap E C))
  (σ : C →ₐ[K] E) (hσ : ∀ a, algebraMap E C (σ a) = a)
  (τ : C →ₐ[K] E) (hτ : ∀ a, algebraMap E C (τ a) = a)

theorem splittingLift_change_linear :
    splittingLift τ hτ - splittingLift σ hσ =
      (epsilonInclusion (K := K) e).comp (difference e σ τ hσ hτ).liftKaehlerDifferential := by
  apply Derivation.liftKaehlerDifferential_unique
  apply DFunLike.ext
  intro a
  change splittingLift τ hτ (KaehlerDifferential.D K C a) -
      splittingLift σ hσ (KaehlerDifferential.D K C a) =
    epsilonInclusion e ((difference e σ τ hσ hτ).liftKaehlerDifferential (KaehlerDifferential.D K C a))
  rw [splittingLift_D,splittingLift_D,Derivation.liftKaehlerDifferential_comp_D]
  calc
    _ = reducedUniversal (K := K) (E := E) (C := C) (τ a-σ a) :=
      (map_sub (reducedUniversal (K := K) (E := E) (C := C)) _ _).symm
    _ = reducedUniversal (K := K) (E := E) (C := C) (epsilon e (difference e σ τ hσ hτ a)) :=
      congrArg (reducedUniversal (K := K) (E := E) (C := C)) (epsilon_difference e σ τ hσ hτ a).symm
    _ = _ := reducedUniversal_epsilon e σ hσ _

theorem splittingLift_change (ω : KaehlerDifferential K C) :
    splittingLift τ hτ ω - splittingLift σ hσ ω =
      epsilonInclusion e ((difference e σ τ hσ hτ).liftKaehlerDifferential ω) :=
  LinearMap.congr_fun (splittingLift_change_linear e σ hσ τ hτ) ω

theorem coefficientRetraction_change_linear :
    coefficientRetraction e σ hσ - coefficientRetraction e τ hτ =
      (difference e σ τ hσ hτ).liftKaehlerDifferential.comp reductionMap := by
  apply (LinearMap.liftBaseChangeEquiv C).symm.injective
  apply Derivation.liftKaehlerDifferential_unique
  apply DFunLike.ext
  intro b
  change coefficientRetraction e σ hσ (reducedUniversal b) -
      coefficientRetraction e τ hτ (reducedUniversal b) =
    (difference e σ τ hσ hτ).liftKaehlerDifferential (reductionMap (reducedUniversal b))
  rw [coefficientRetraction_D,coefficientRetraction_D,reductionMap_D,
    Derivation.liftKaehlerDifferential_comp_D]
  exact coefficientDerivation_change e σ hσ τ hτ b

theorem coefficientRetraction_change (z : ReducedCotangent (K := K) (E := E) (C := C)) :
    coefficientRetraction e σ hσ z-coefficientRetraction e τ hτ z =
      (difference e σ τ hσ hτ).liftKaehlerDifferential (reductionMap z) :=
  LinearMap.congr_fun (coefficientRetraction_change_linear e σ hσ τ hτ) z

theorem splitCoordinates_change (z : ReducedCotangent (K := K) (E := E) (C := C)) :
    splitEquiv e τ hτ z =
      ((splitEquiv e σ hσ z).1,
        (splitEquiv e σ hσ z).2 -
          (difference e σ τ hσ hτ).liftKaehlerDifferential ((splitEquiv e σ hσ z).1)) := by
  apply Prod.ext
  · rfl
  · change coefficientRetraction e τ hτ z = coefficientRetraction e σ hσ z -
      (difference e σ τ hσ hτ).liftKaehlerDifferential (reductionMap z)
    have h := coefficientRetraction_change e σ hσ τ hτ z
    linear_combination (norm := abel) -h

end CycleQ2GeometricSquareZeroCotangentChange

end

#print axioms CycleQ2GeometricSquareZeroCotangentChange.splittingLift_change
#print axioms CycleQ2GeometricSquareZeroCotangentChange.splitCoordinates_change
