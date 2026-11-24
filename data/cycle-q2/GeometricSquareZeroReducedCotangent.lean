import Proposal.GeometricSquareZeroCoefficientDerivation
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# The actual reduced cotangent module of a faithfully split square-zero ring

The module is the genuine scalar extension C tensor_E Omega(E/K).
Its original epsilon differential has a proved coefficient retraction.
The chosen original algebra splitting lifts Omega(C/K), and the two maps
give a genuine split cotangent sequence. No cotangent injectivity or
comparison equivalence is supplied as an assumption.

Prepared for fqlx with OpenAI ChatGPT assistance; see solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2GeometricSquareZeroReducedCotangent

open scoped TensorProduct
open CycleQ2GeometricSquareZeroSplittings
open CycleQ2GeometricSquareZeroCoefficientDerivation

variable {K E C : Type*} [CommRing K] [CommRing E] [CommRing C]
  [Algebra K E] [Algebra K C] [Algebra E C] [IsScalarTower K E C]

abbrev ReducedCotangent := C ⊗[E] KaehlerDifferential K E

def tensorOne : KaehlerDifferential K E →ₗ[E] ReducedCotangent (K := K) (E := E) (C := C) :=
  TensorProduct.mk E C (KaehlerDifferential K E) 1

def reducedUniversal : Derivation K E (ReducedCotangent (K := K) (E := E) (C := C)) :=
  (tensorOne (K := K) (E := E) (C := C)).compDer (KaehlerDifferential.D K E)

omit [Algebra K C] [IsScalarTower K E C] in
theorem thick_smul (b : E) (z : ReducedCotangent (K := K) (E := E) (C := C)) :
    b • z = algebraMap E C b • z :=
  (IsScalarTower.algebraMap_smul C b z).symm

def reductionMap : ReducedCotangent (K := K) (E := E) (C := C) →ₗ[C] KaehlerDifferential K C :=
  (KaehlerDifferential.map K K E C).liftBaseChange C

theorem reductionMap_D (b : E) :
    reductionMap (reducedUniversal (K := K) (E := E) (C := C) b) =
      KaehlerDifferential.D K C (algebraMap E C b) := by
  change (KaehlerDifferential.map K K E C).liftBaseChange C
    ((1 : C) ⊗ₜ[E] KaehlerDifferential.D K E b) = _
  rw [LinearMap.liftBaseChange_tmul,one_smul,KaehlerDifferential.map_D]

variable (e : C ≃ₗ[E] RingHom.ker (algebraMap E C))

def epsilonDifferential : ReducedCotangent (K := K) (E := E) (C := C) :=
  reducedUniversal (epsilon e 1)

def epsilonInclusion : C →ₗ[C] ReducedCotangent (K := K) (E := E) (C := C) :=
  LinearMap.toSpanSingleton C _ (epsilonDifferential (K := K) e)

theorem epsilonInclusion_apply (a : C) :
    epsilonInclusion (K := K) e a = a • epsilonDifferential (K := K) e := rfl

theorem reductionMap_epsilon : reductionMap (epsilonDifferential (K := K) e) = 0 := by
  rw [epsilonDifferential,reductionMap_D,reduction_epsilon,Derivation.map_zero]

theorem reductionMap_epsilonInclusion (a : C) : reductionMap (epsilonInclusion (K := K) e a) = 0 := by
  rw [epsilonInclusion_apply,map_smul,reductionMap_epsilon,smul_zero]

variable (σ : C →ₐ[K] E) (hσ : ∀ a, algebraMap E C (σ a) = a)

def coefficientRetraction : ReducedCotangent (K := K) (E := E) (C := C) →ₗ[C] C :=
  (coefficientDerivation e σ hσ).liftKaehlerDifferential.liftBaseChange C

theorem coefficientRetraction_D (b : E) :
    coefficientRetraction e σ hσ (reducedUniversal b) = coefficientDerivation e σ hσ b := by
  change (coefficientDerivation e σ hσ).liftKaehlerDifferential.liftBaseChange C
    ((1 : C) ⊗ₜ[E] KaehlerDifferential.D K E b) = _
  rw [LinearMap.liftBaseChange_tmul,one_smul,Derivation.liftKaehlerDifferential_comp_D]

theorem coefficientRetraction_epsilon : coefficientRetraction e σ hσ (epsilonDifferential (K := K) e) = 1 := by
  rw [epsilonDifferential,coefficientRetraction_D,coefficientDerivation_epsilon_one]

theorem coefficientRetraction_epsilonInclusion (a : C) :
    coefficientRetraction e σ hσ (epsilonInclusion (K := K) e a) = a := by
  rw [epsilonInclusion_apply,map_smul,coefficientRetraction_epsilon,smul_eq_mul,mul_one]

include σ hσ in
theorem epsilonInclusion_injective : Function.Injective (epsilonInclusion (K := K) e) := by
  intro a b h
  have he := congrArg (coefficientRetraction e σ hσ) h
  simpa only [coefficientRetraction_epsilonInclusion] using he

def splittingDerivation : Derivation K C (ReducedCotangent (K := K) (E := E) (C := C)) where
  toLinearMap := ((tensorOne (K := K) (E := E) (C := C)).restrictScalars K).comp
    ((KaehlerDifferential.D K E).toLinearMap.comp σ.toLinearMap)
  map_one_eq_zero' := by
    change tensorOne (KaehlerDifferential.D K E (σ 1)) = 0
    rw [map_one,Derivation.map_one_eq_zero,map_zero]
  leibniz' a b := by
    let δ := reducedUniversal (K := K) (E := E) (C := C)
    change δ (σ (a*b)) = a • δ (σ b) + b • δ (σ a)
    have hscalar (c : C) (z : ReducedCotangent (K := K) (E := E) (C := C)) : σ c • z = c • z :=
      (thick_smul (K := K) (σ c) z).trans (congrArg (fun d : C => d • z) (hσ c))
    calc
      _ = δ (σ a * σ b) := congrArg δ (map_mul σ a b)
      _ = σ a • δ (σ b) + σ b • δ (σ a) := δ.leibniz (σ a) (σ b)
      _ = _ := congrArg₂ (fun x y => x+y) (hscalar a _) (hscalar b _)

def splittingLift : KaehlerDifferential K C →ₗ[C] ReducedCotangent (K := K) (E := E) (C := C) :=
  (splittingDerivation (E := E) (C := C) σ hσ).liftKaehlerDifferential

theorem splittingLift_D (a : C) :
    splittingLift (E := E) σ hσ (KaehlerDifferential.D K C a) = reducedUniversal (σ a) :=
  (splittingDerivation σ hσ).liftKaehlerDifferential_comp_D a

theorem reductionMap_splittingLift :
    (reductionMap (K := K) (E := E) (C := C)).comp (splittingLift σ hσ) = LinearMap.id := by
  apply Derivation.liftKaehlerDifferential_unique
  apply DFunLike.ext
  intro a
  change reductionMap (splittingLift σ hσ (KaehlerDifferential.D K C a)) =
    KaehlerDifferential.D K C a
  rw [splittingLift_D,reductionMap_D,hσ]

theorem coefficientRetraction_splittingLift :
    (coefficientRetraction e σ hσ).comp (splittingLift σ hσ) = 0 := by
  apply Derivation.liftKaehlerDifferential_unique
  apply DFunLike.ext
  intro a
  change coefficientRetraction e σ hσ (splittingLift σ hσ (KaehlerDifferential.D K C a)) = 0
  rw [splittingLift_D,coefficientRetraction_D,coefficientDerivation_splitting]

include σ hσ in
theorem reducedUniversal_epsilon (a : C) :
    reducedUniversal (K := K) (E := E) (C := C) (epsilon e a) = a • epsilonDifferential (K := K) e := by
  have he : epsilon e a = σ a * epsilon e 1 := by
    simpa only [mul_one] using epsilon_mul_of_splitting e σ hσ a 1
  let δ := reducedUniversal (K := K) (E := E) (C := C)
  change δ (epsilon e a) = a • δ (epsilon e 1)
  calc
    _ = δ (σ a * epsilon e 1) := congrArg δ he
    _ = σ a • δ (epsilon e 1) + epsilon e 1 • δ (σ a) := δ.leibniz _ _
    _ = _ := by
      rw [thick_smul (K := K) (σ a),thick_smul (K := K) (epsilon e 1),hσ,
        reduction_epsilon,zero_smul,add_zero]

theorem reducedUniversal_reconstruction (b : E) :
    reducedUniversal (K := K) (E := E) (C := C) b =
      reducedUniversal (σ (algebraMap E C b)) +
        coefficientDerivation e σ hσ b • epsilonDifferential (K := K) e := by
  exact (congrArg (reducedUniversal (K := K) (E := E) (C := C)) (reconstruction e σ hσ b)).symm.trans
    (by rw [map_add,reducedUniversal_epsilon e σ hσ])

theorem split_reconstruction :
    (splittingLift σ hσ).comp reductionMap + (epsilonInclusion (K := K) e).comp (coefficientRetraction e σ hσ) =
      (LinearMap.id : ReducedCotangent (K := K) (E := E) (C := C) →ₗ[C] _) := by
  apply (LinearMap.liftBaseChangeEquiv C).symm.injective
  apply Derivation.liftKaehlerDifferential_unique
  apply DFunLike.ext
  intro b
  change splittingLift σ hσ (reductionMap (reducedUniversal b)) +
      epsilonInclusion (K := K) e (coefficientRetraction e σ hσ (reducedUniversal b)) = reducedUniversal b
  rw [reductionMap_D,splittingLift_D,coefficientRetraction_D,epsilonInclusion_apply]
  exact (reducedUniversal_reconstruction e σ hσ b).symm

def splitEquiv : ReducedCotangent (K := K) (E := E) (C := C) ≃ₗ[C] KaehlerDifferential K C × C where
  __ := (reductionMap (K := K) (E := E) (C := C)).prod (coefficientRetraction e σ hσ)
  invFun z := splittingLift σ hσ z.1 + epsilonInclusion (K := K) e z.2
  left_inv z := LinearMap.congr_fun (split_reconstruction e σ hσ) z
  right_inv z := by
    apply Prod.ext
    · change reductionMap (splittingLift σ hσ z.1 + epsilonInclusion (K := K) e z.2) = z.1
      rw [map_add,← LinearMap.comp_apply,reductionMap_splittingLift,
        LinearMap.id_apply,reductionMap_epsilonInclusion,add_zero]
    · change coefficientRetraction e σ hσ (splittingLift σ hσ z.1 + epsilonInclusion (K := K) e z.2) = z.2
      rw [map_add,← LinearMap.comp_apply,coefficientRetraction_splittingLift,
        LinearMap.zero_apply,coefficientRetraction_epsilonInclusion,zero_add]

include σ hσ in
theorem reductionMap_surjective : Function.Surjective (reductionMap (K := K) (E := E) (C := C)) := by
  intro ω
  exact ⟨splittingLift σ hσ ω,LinearMap.congr_fun (reductionMap_splittingLift σ hσ) ω⟩

include σ hσ in
theorem reductionMap_kernel (z : ReducedCotangent (K := K) (E := E) (C := C)) :
    reductionMap z = 0 ↔ ∃ a : C, epsilonInclusion (K := K) e a = z := by
  constructor
  · intro h
    refine ⟨coefficientRetraction e σ hσ z,?_⟩
    have hz := LinearMap.congr_fun (split_reconstruction e σ hσ) z
    change splittingLift σ hσ (reductionMap z) + epsilonInclusion (K := K) e (coefficientRetraction e σ hσ z) = z at hz
    simpa only [h,map_zero,zero_add] using hz
  · rintro ⟨a,rfl⟩
    exact reductionMap_epsilonInclusion e a

end CycleQ2GeometricSquareZeroReducedCotangent

end

#print axioms CycleQ2GeometricSquareZeroReducedCotangent.epsilonInclusion_injective
#print axioms CycleQ2GeometricSquareZeroReducedCotangent.splitEquiv
#print axioms CycleQ2GeometricSquareZeroReducedCotangent.reductionMap_kernel
