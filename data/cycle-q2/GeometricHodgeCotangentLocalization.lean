import Proposal.GeometricHodgeCotangentChartPresentation
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.TensorProduct.IsBaseChangePi
import Mathlib.Algebra.Module.LocalizedModule.Exact

/-!
# The hypersurface cotangent presentation after localization

The original four-coordinate Kähler presentation remains exact after
any localization of the chart ring. The maps are the actual localized
coordinate differentials and the original equation's gradient.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2HodgeCotangentLocalization

open MvPolynomial CycleQ2HodgeEulerChartDerivations
open CycleQ2HodgeCotangentChartPresentation
open scoped KaehlerDifferential

variable {K : Type} [CommRing K] (F : Poly K)
variable (B : Type) [CommRing B] [Algebra K B] [Algebra (Hyp F) B]
  [IsScalarTower K (Hyp F) B]

def gradient : Fin 4 → B := fun j => algebraMap (Hyp F) B (gradientVector F j)

def normal : B →ₗ[B] (Fin 4 → B) := LinearMap.toSpanSingleton B _ (gradient F B)

def coordinateMap : (Fin 4 → B) →ₗ[B] Ω[B⁄K] :=
  ∑ j : Fin 4, (LinearMap.proj j).smulRight
    (KaehlerDifferential.D K B (algebraMap (Hyp F) B (mk F (X j))))

theorem coordinateMap_apply (v : Fin 4 → B) :
    coordinateMap F B v = ∑ j, v j •
      KaehlerDifferential.D K B (algebraMap (Hyp F) B (mk F (X j))) := by
  simp [coordinateMap]

def tupleMap : Tuple F →ₗ[Hyp F] (Fin 4 → B) :=
  LinearMap.pi fun j => (Algebra.linearMap (Hyp F) B).comp (LinearMap.proj j)

instance tupleMap_isLocalized (S : Submonoid (Hyp F)) [IsLocalization S B] :
    IsLocalizedModule S (tupleMap F B) := by
  unfold tupleMap
  infer_instance

private theorem normal_localized (S : Submonoid (Hyp F)) [IsLocalization S B] :
    IsLocalizedModule.map S (Algebra.linearMap (Hyp F) B) (tupleMap F B)
      (LinearMap.toSpanSingleton (Hyp F) _ (gradientVector F)) =
      (normal F B).restrictScalars (Hyp F) := by
  apply IsLocalizedModule.linearMap_ext S (Algebra.linearMap (Hyp F) B) (tupleMap F B)
  rw [IsLocalizedModule.map_comp]
  apply LinearMap.ext
  intro a
  funext j
  simp [normal,gradient,tupleMap,Algebra.smul_def]

private theorem coordinateMap_localized (S : Submonoid (Hyp F)) [IsLocalization S B] :
    IsLocalizedModule.map S (tupleMap F B) (KaehlerDifferential.map K K (Hyp F) B)
      (CycleQ2HodgeCotangentChartPresentation.coordinateMap F) =
      (coordinateMap F B).restrictScalars (Hyp F) := by
  apply IsLocalizedModule.linearMap_ext S (tupleMap F B) (KaehlerDifferential.map K K (Hyp F) B)
  rw [IsLocalizedModule.map_comp]
  apply LinearMap.ext
  intro v
  simp only [LinearMap.comp_apply,LinearMap.restrictScalars_apply,
    CycleQ2HodgeCotangentChartPresentation.coordinateMap_apply,
    coordinateMap_apply,map_sum,map_smul,KaehlerDifferential.map_D]
  apply Finset.sum_congr rfl
  intro j _
  change v j •
    KaehlerDifferential.D K B (algebraMap (Hyp F) B (mk F (X j))) =
    algebraMap (Hyp F) B (v j) •
    KaehlerDifferential.D K B (algebraMap (Hyp F) B (mk F (X j)))
  exact (IsScalarTower.algebraMap_smul B (v j) _).symm

theorem exact (S : Submonoid (Hyp F)) [IsLocalization S B] :
    Function.Exact (normal F B) (coordinateMap F B) := by
  have h := IsLocalizedModule.map_exact S (Algebra.linearMap (Hyp F) B)
    (tupleMap F B) (KaehlerDifferential.map K K (Hyp F) B)
    (LinearMap.toSpanSingleton (Hyp F) _ (gradientVector F))
    (CycleQ2HodgeCotangentChartPresentation.coordinateMap F)
    (CycleQ2HodgeCotangentChartPresentation.coordinateMap_eq_zero_iff F)
  rw [normal_localized,coordinateMap_localized] at h
  exact h

theorem surjective (S : Submonoid (Hyp F)) [IsLocalization S B] :
    Function.Surjective (coordinateMap F B) := by
  have h := IsLocalizedModule.map_surjective S (tupleMap F B)
    (KaehlerDifferential.map K K (Hyp F) B)
    (CycleQ2HodgeCotangentChartPresentation.coordinateMap F)
    (CycleQ2HodgeCotangentChartPresentation.coordinateMap_surjective F)
  rw [coordinateMap_localized] at h
  exact h

end CycleQ2HodgeCotangentLocalization
end

#print axioms CycleQ2HodgeCotangentLocalization.exact
#print axioms CycleQ2HodgeCotangentLocalization.surjective
