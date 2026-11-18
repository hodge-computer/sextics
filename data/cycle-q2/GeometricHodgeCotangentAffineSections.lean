import Proposal.GeometricHodgeCotangentConormalComplex
import Proposal.GeometricAffineOpenOrdinaryDifferentials

/-!
# The original chart maps are localization maps on principal subopens

The homogeneous-localization chart is identified with the actual full
chart section ring. On each principal subopen its original coefficient
map is a localization of the native hypersurface quotient.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2HodgeCotangentAffineSections
open AlgebraicGeometry CategoryTheory Opposite
open CycleQ2GeometricHodgeThreefold
open CycleQ2GenericSexticGradient (CoeffRing)
open CycleQ2HodgeCotangentAtlasForms (complexOn)
open CycleQ2HodgeCotangentConormalComplex (affineMap)
open CycleQ2GeometricProjectiveCurve.Twisted (res res_self)
attribute [local instance] complexOn
variable (φ : CoeffRing →+* ℂ) (i : Fin 4)

def functions : CycleQ2HodgeEuler.chart φ i ≃+* Γ(threefold φ,coordinateOpen φ i) :=
  (CycleQ2HodgeEulerChartBinding.chartEquiv φ i).symm.toRingEquiv.trans
    (Proj.basicOpenIsoAway (grade φ) (coord φ i.castSucc) (weightOne_mem_grade φ i) (by decide)).commRingCatIsoToRingEquiv

theorem functions_apply (a : CycleQ2HodgeEuler.chart φ i) :
    functions φ i a = affineMap φ i (coordinateOpen φ i) le_rfl a := by
  change (Proj.awayToSection (grade φ) (coord φ i.castSucc)) _ = res _ le_rfl _
  rw [res_self]
  rfl

theorem chart_isAffine : IsAffineOpen (coordinateOpen φ i) :=
  IsAffine.of_isIso (coordinateChart φ i).hom

@[instance_reducible] def sectionAlgebra (V : (threefold φ).Opens) (hi : V ≤ coordinateOpen φ i) :
    Algebra (CycleQ2HodgeEuler.chart φ i) Γ(threefold φ,V) :=
  (affineMap φ i V hi).toRingHom.toAlgebra

theorem sectionTower (V : (threefold φ).Opens) (hi : V ≤ coordinateOpen φ i) :
    letI := sectionAlgebra φ i V hi
    IsScalarTower ℂ (CycleQ2HodgeEuler.chart φ i) Γ(threefold φ,V) :=
  IsScalarTower.of_algHom (affineMap φ i V hi)

abbrev principal (r : Γ(threefold φ,coordinateOpen φ i)) : (threefold φ).Opens :=
  (threefold φ).basicOpen r

theorem principal_le (r : Γ(threefold φ,coordinateOpen φ i)) :
    principal φ i r ≤ coordinateOpen φ i := (threefold φ).basicOpen_le r

theorem principal_isAffine (r : Γ(threefold φ,coordinateOpen φ i)) :
    IsAffineOpen (principal φ i r) := (chart_isAffine φ i).basicOpen r

theorem principal_localization (r : Γ(threefold φ,coordinateOpen φ i)) :
    letI := sectionAlgebra φ i (principal φ i r) (principal_le φ i r)
    IsLocalization.Away ((functions φ i).symm r) Γ(threefold φ,principal φ i r) := by
  letI := sectionAlgebra φ i (principal φ i r) (principal_le φ i r)
  letI := (chart_isAffine φ i).isLocalization_basicOpen r
  apply IsLocalization.of_ringEquiv_left (functions φ i)
    (M₁ := Submonoid.powers r) (M₂ := Submonoid.powers ((functions φ i).symm r))
  · rw [Submonoid.map_powers,RingEquiv.apply_symm_apply]
  · intro a
    change affineMap φ i (principal φ i r) (principal_le φ i r) a =
      res _ (principal_le φ i r) (functions φ i a)
    rw [functions_apply]
    change res (threefold φ).sheaf (principal_le φ i r)
      ((Proj.awayToSection (grade φ) (coord φ i.castSucc))
        ((CycleQ2HodgeEulerChartBinding.chartEquiv φ i).symm a)) =
      res (threefold φ).sheaf (principal_le φ i r)
        (res (threefold φ).sheaf le_rfl ((Proj.awayToSection (grade φ) (coord φ i.castSucc))
          ((CycleQ2HodgeEulerChartBinding.chartEquiv φ i).symm a)))
    rw [res_self]

end CycleQ2HodgeCotangentAffineSections
end
#print axioms CycleQ2HodgeCotangentAffineSections.functions_apply
#print axioms CycleQ2HodgeCotangentAffineSections.principal_localization
