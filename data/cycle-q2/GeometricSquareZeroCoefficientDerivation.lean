import Proposal.GeometricSquareZeroAtiyah

/-!
# The actual coefficient derivation of a faithfully split square-zero ring

The same genuine reduction kernel and a chosen algebra splitting give
a derivation of the thick ring into the reduced ring. Its value on the
original epsilon generator is one. Thus its universal Kähler lift
detects that differential, rather than assuming its faithfulness.
Changing the splitting gives exactly the original splitting-difference
derivation with its fixed sign and epsilon normalization.

Prepared for fqlx with OpenAI ChatGPT assistance; see solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2GeometricSquareZeroCoefficientDerivation

open CycleQ2GeometricSquareZeroSplittings

variable {K E C : Type*} [CommRing K] [CommRing E] [CommRing C]
  [Algebra K E] [Algebra K C] [Algebra E C] [IsScalarTower K E C]
  (e : C ≃ₗ[E] RingHom.ker (algebraMap E C))
  (σ : C →ₐ[K] E) (hσ : ∀ a, algebraMap E C (σ a) = a)

def coefficientLinear : E →ₗ[K] C :=
  (e.symm.toLinearMap.restrictScalars K).comp
    ((LinearMap.id - σ.toLinearMap.comp (IsScalarTower.toAlgHom K E C).toLinearMap).codRestrict
      ((RingHom.ker (algebraMap E C)).restrictScalars K) (fun x => by
        change algebraMap E C (x - σ (algebraMap E C x)) = 0
        rw [map_sub,hσ,sub_self]))

theorem epsilon_coefficientLinear (x : E) :
    epsilon e (coefficientLinear e σ hσ x) = x - σ (algebraMap E C x) := by
  change (e (e.symm ⟨x - σ (algebraMap E C x),_⟩)).val = _
  exact congrArg Subtype.val (e.apply_symm_apply _)

def coefficientDerivation : Derivation K E C where
  toLinearMap := coefficientLinear e σ hσ
  map_one_eq_zero' := by
    apply epsilon_injective e
    rw [epsilon_coefficientLinear,map_one,map_one,sub_self,map_zero]
  leibniz' x y := by
    have hz : (x-σ (algebraMap E C x)) * (y-σ (algebraMap E C y)) = 0 := by
      apply kernel_mul_zero e <;> rw [map_sub,hσ,sub_self]
    apply epsilon_injective e
    simp only [Algebra.smul_def]
    change epsilon e (coefficientLinear e σ hσ (x*y)) =
      epsilon e (algebraMap E C x * coefficientLinear e σ hσ y +
        algebraMap E C y * coefficientLinear e σ hσ x)
    rw [epsilon_coefficientLinear,map_add,
      epsilon_mul_of_splitting e σ hσ,epsilon_mul_of_splitting e σ hσ,
      epsilon_coefficientLinear,epsilon_coefficientLinear,map_mul,map_mul]
    linear_combination hz

theorem epsilon_coefficientDerivation (x : E) :
    epsilon e (coefficientDerivation e σ hσ x) = x-σ (algebraMap E C x) :=
  epsilon_coefficientLinear e σ hσ x

theorem coefficientDerivation_splitting (a : C) : coefficientDerivation e σ hσ (σ a) = 0 := by
  apply epsilon_injective e
  rw [epsilon_coefficientDerivation,hσ,sub_self,map_zero]

theorem coefficientDerivation_epsilon (a : C) : coefficientDerivation e σ hσ (epsilon e a) = a := by
  apply epsilon_injective e
  rw [epsilon_coefficientDerivation,reduction_epsilon,map_zero,sub_zero]

theorem reconstruction (x : E) :
    σ (algebraMap E C x) + epsilon e (coefficientDerivation e σ hσ x) = x := by
  rw [epsilon_coefficientDerivation]
  abel

theorem coefficientDerivation_epsilon_one : coefficientDerivation e σ hσ (epsilon e 1) = 1 :=
  coefficientDerivation_epsilon e σ hσ 1

theorem coefficientDerivation_D_epsilon :
    (coefficientDerivation e σ hσ).liftKaehlerDifferential
      (KaehlerDifferential.D K E (epsilon e 1)) = 1 := by
  rw [Derivation.liftKaehlerDifferential_comp_D,coefficientDerivation_epsilon_one]

variable (τ : C →ₐ[K] E) (hτ : ∀ a, algebraMap E C (τ a) = a)

theorem coefficientDerivation_other_splitting (a : C) :
    coefficientDerivation e σ hσ (τ a) = difference e σ τ hσ hτ a := by
  apply epsilon_injective e
  rw [epsilon_coefficientDerivation,hτ,epsilon_difference]

theorem coefficientDerivation_change (x : E) :
    coefficientDerivation e σ hσ x - coefficientDerivation e τ hτ x =
      difference e σ τ hσ hτ (algebraMap E C x) := by
  apply epsilon_injective e
  rw [map_sub,epsilon_coefficientDerivation,epsilon_coefficientDerivation,epsilon_difference]
  abel

end CycleQ2GeometricSquareZeroCoefficientDerivation

end

#print axioms CycleQ2GeometricSquareZeroCoefficientDerivation.coefficientDerivation
#print axioms CycleQ2GeometricSquareZeroCoefficientDerivation.coefficientDerivation_D_epsilon
#print axioms CycleQ2GeometricSquareZeroCoefficientDerivation.coefficientDerivation_change
