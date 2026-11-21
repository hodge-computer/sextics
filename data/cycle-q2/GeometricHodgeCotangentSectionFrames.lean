import Proposal.GeometricHodgeCotangentConormalComplex
import Proposal.GeometricHodgeCotangentEulerChart

/-!
# Coefficient frames for the actual cotangent Euler kernel

Sections on every original chart subopen are precisely the five-tuples
with weighted radial contraction zero. Dropping the weight-one anchor
identifies these sections with four unrestricted coefficients.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2HodgeCotangentSectionFrames
open AlgebraicGeometry CategoryTheory Limits Opposite
open CycleQ2GeometricHodgeThreefold CycleQ2GeometricIncidenceProj
open CycleQ2GenericSexticGradient (CoeffRing)
open CycleQ2HodgeThreefoldTwist CycleQ2HodgeTwistRatios
open CycleQ2HodgeCotangentEulerSheaf
open CycleQ2HodgeCotangentAtlasForms (coefficient_add coefficient_smul coordinate)
open CycleQ2HodgeCotangentEulerChart (radialRow radialRow_apply radialEquiv)
open CycleQ2SeedSectionSheafLimits

variable (φ : CoeffRing →+* ℂ) (i : Fin 4) (V : (threefold φ).Opens) (hi : V ≤ U φ i)

abbrev radial (j : Fin 5) : Γ(threefold φ,V) :=
  (geometricWeight j : Γ(threefold φ,V)) * coordinate φ i V hi j

def coefficients : Γ(ambient φ,V) →ₗ[Γ(threefold φ,V)] (Fin 5 → Γ(threefold φ,V)) where
  toFun a := coefficient φ i V hi a
  map_add' a b := funext fun j => coefficient_add φ i V hi a b j
  map_smul' c a := funext fun j => coefficient_smul φ i V hi c a j

def ambientEquiv : Γ(ambient φ,V) ≃ₗ[Γ(threefold φ,V)] (radialRow (radial φ i V hi)).ker := by
  let m := (coefficients φ i V hi).codRestrict (radialRow (radial φ i V hi)).ker (by
    intro a
    rw [LinearMap.mem_ker,radialRow_apply]
    exact coefficient_radial_zero φ i V hi a)
  apply LinearEquiv.ofBijective m
  constructor
  · intro a b hab
    apply (sectionKernelEquiv (eulerMap φ) V).injective
    apply Subtype.ext
    rw [sectionKernelEquiv_val,sectionKernelEquiv_val]
    apply (sectionProductEquiv (pieces φ) V).injective
    funext j
    rw [sectionProductEquiv_apply,sectionProductEquiv_apply]
    apply (chartFrame φ (-(geometricWeight j : ℤ)) i V hi).injective
    exact congrFun (congrArg Subtype.val hab) j
  · intro w
    let t := (sectionProductEquiv (pieces φ) V).symm
      (fun j => (chartFrame φ (-(geometricWeight j : ℤ)) i V hi).symm (w.val j))
    have ht : (eulerMap φ).app V t = 0 := by
      apply (chartFrame φ 0 i V hi).injective
      rw [euler_frame,map_zero]
      simp only [t,sectionProductEquiv_symm_apply,LinearEquiv.apply_symm_apply]
      exact (radialRow_apply _ _).symm.trans w.property
    refine ⟨(sectionKernelEquiv (eulerMap φ) V).symm ⟨t,ht⟩,Subtype.ext ?_⟩
    funext j
    change chartFrame φ (-(geometricWeight j : ℤ)) i V hi ((Pi.π (pieces φ) j).app V
      ((kernel.ι (eulerMap φ)).app V ((sectionKernelEquiv (eulerMap φ) V).symm ⟨t,ht⟩))) = w.val j
    rw [sectionKernelEquiv_symm_val]
    simp only [t,sectionProductEquiv_symm_apply,LinearEquiv.apply_symm_apply]

theorem ambientEquiv_apply (a : Γ(ambient φ,V)) (j : Fin 5) :
    (ambientEquiv φ i V hi a).val j = coefficient φ i V hi a j := rfl

def drop : Γ(ambient φ,V) ≃ₗ[Γ(threefold φ,V)] (Fin 4 → Γ(threefold φ,V)) :=
  (ambientEquiv φ i V hi).trans
    (radialEquiv i.castSucc (radial φ i V hi)
      (CycleQ2HodgeCotangentEulerExact.normalized_radial_self φ i V hi))

theorem drop_apply (a : Γ(ambient φ,V)) (j : Fin 4) :
    drop φ i V hi a j = coefficient φ i V hi a (i.castSucc.succAbove j) := rfl

theorem drop_conormal (s : Γ(twist φ (-6),V)) (j : Fin 4) :
    drop φ i V hi ((conormalMap φ).app V s) j =
      CycleQ2HodgeCotangentConormalComplex.affineMap φ i V hi
        (CycleQ2HodgeEuler.chartMap φ i (MvPolynomial.pderiv j (CycleQ2HodgeEuler.F φ i))) *
          chartFrame φ (-6) i V hi s := by
  rw [drop_apply,CycleQ2HodgeCotangentConormalComplex.coefficient_conormal,
    ← CycleQ2HodgeCotangentConormalComplex.affineMap_partial,CycleQ2HodgeEuler.partial_succAbove]

end CycleQ2HodgeCotangentSectionFrames
end
#print axioms CycleQ2HodgeCotangentSectionFrames.ambientEquiv
#print axioms CycleQ2HodgeCotangentSectionFrames.drop_conormal
