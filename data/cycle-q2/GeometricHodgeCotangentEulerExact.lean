import Proposal.GeometricHodgeCotangentEulerSheaf
import Mathlib.Topology.Sheaves.LocallySurjective

/-!
# The actual cotangent Euler short exact sequence

On every subopen of a weight-one chart the chosen slot lifts any O(0)
section. The four original opens cover the monic threefold, so the Euler
row is an epimorphism of the actual sheaves. Its native kernel therefore
gives a short exact sequence, without a cohomology assumption.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 3000
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2HodgeCotangentEulerExact

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace
open CycleQ2GeometricIncidenceProj CycleQ2GeometricHodgeThreefold
open CycleQ2HodgeThreefoldTwist CycleQ2HodgeTwistRatios
open CycleQ2HodgeCotangentEulerSheaf
open CycleQ2SeedSectionSheafLimits (sectionProductEquiv sectionProductEquiv_symm_apply)
open CycleQ2GenericSexticGradient (CoeffRing)

variable {R : Type} [CommRing R] (φ : CoeffRing →+* R)

theorem normalized_radial_self (i : Fin 4) (V : (threefold φ).Opens) (hi : V ≤ U φ i) :
    (geometricWeight i.castSucc : Γ(threefold φ,V)) *
      normalized φ i (coord φ i.castSucc) (coord_mem_grade φ i.castSucc) V hi = 1 := by
  let e := CycleQ2HodgeEulerChartBinding.chartEquiv φ i
  have he : (geometricWeight i.castSucc : ChartRing φ i) *
      CycleQ2HodgeEulerChartBinding.ratio φ i i.castSucc = 1 := by
    apply e.injective
    simp only [map_mul,map_natCast,map_one,e,CycleQ2HodgeEulerChartBinding.chartEquiv_ratio]
    exact CycleQ2HodgeEuler.radial_self φ i
  simpa only [map_mul,map_natCast,map_one,CycleQ2HodgeEulerSheaf.sectionMap_coordinate]
    using congrArg (CycleQ2HodgeEulerSheaf.sectionMap φ i V hi) he

/-- Every O(0) section lifts on every original chart subopen. -/
theorem euler_section_surjective (i : Fin 4) (V : (threefold φ).Opens) (hi : V ≤ U φ i) :
    Function.Surjective ((eulerMap φ).app V) := by
  classical
  intro s
  let a (j : Fin 5) : Γ(pieces φ j,V) :=
    (chartFrame φ _ i V hi).symm (if j = i.castSucc then chartFrame φ 0 i V hi s else 0)
  refine ⟨(sectionProductEquiv (pieces φ) V).symm a, (chartFrame φ 0 i V hi).injective ?_⟩
  rw [euler_frame]
  simp only [sectionProductEquiv_symm_apply,a,LinearEquiv.apply_symm_apply]
  rw [Finset.sum_eq_single i.castSucc]
  · rw [if_pos rfl,normalized_radial_self,one_mul]
  · intro j _ hj
    rw [if_neg hj,mul_zero]
  · simp

theorem euler_additive_epi (h : IsUnit (φ vertexCoefficient)) :
    Epi ((SheafOfModules.toSheaf (threefold φ).ringCatSheaf).map (eulerMap φ)) := by
  apply (TopCat.Sheaf.isLocallySurjective_iff_epi _).mp
  apply (TopCat.Presheaf.isLocallySurjective_iff _).mpr
  intro V s x hx
  have hxc : x ∈ ⨆ i : Fin 4, U φ i := by rw [coordinateOpens_cover φ h]; trivial
  obtain ⟨i,hi⟩ := Opens.mem_iSup.mp hxc
  exact ⟨V ⊓ U φ i,inf_le_left,euler_section_surjective φ i _ inf_le_right _,⟨hx,hi⟩⟩

theorem euler_epi (h : IsUnit (φ vertexCoefficient)) : Epi (eulerMap φ) where
  left_cancellation {Z} f g hfg := by
    let F := SheafOfModules.toSheaf (threefold φ).ringCatSheaf
    letI : Epi (F.map (eulerMap φ)) := euler_additive_epi φ h
    have hm := congrArg (fun k => F.map k) hfg
    rw [Functor.map_comp,Functor.map_comp] at hm
    have he : F.map f = F.map g := (cancel_epi (F.map (eulerMap φ))).mp hm
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro O
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro s
    exact congrArg (fun k => k.hom.app O s) he

def eulerSequence : ShortComplex (threefold φ).Modules :=
  ShortComplex.mk (kernel.ι (eulerMap φ)) (eulerMap φ) (kernel.condition _)

/-- This is exact for the actual line-bundle maps on the original monic locus. -/
theorem euler_shortExact (h : IsUnit (φ vertexCoefficient)) : (eulerSequence φ).ShortExact := by
  letI := euler_epi φ h
  change (ShortComplex.mk (kernel.ι (eulerMap φ)) (eulerMap φ) (kernel.condition _)).ShortExact
  exact { exact := ShortComplex.exact_kernel (eulerMap φ) }

end CycleQ2HodgeCotangentEulerExact
end

#print axioms CycleQ2HodgeCotangentEulerExact.euler_section_surjective
#print axioms CycleQ2HodgeCotangentEulerExact.euler_shortExact
