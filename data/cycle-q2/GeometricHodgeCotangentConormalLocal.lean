import Proposal.GeometricHodgeCotangentLocalization
import Proposal.GeometricHodgeCotangentSectionFrames
import Proposal.GeometricHodgeCotangentAffineSections

/-!
# Exactness of the actual conormal maps on principal affine opens

The localized hypersurface presentation is realized by the original
coefficient frames and by the actual ordinary-to-sheaf differential map.
This proves section exactness and cotangent surjectivity on every
principal subopen of each original chart.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2HodgeCotangentConormalLocal
open AlgebraicGeometry CategoryTheory Limits Opposite MvPolynomial
open CycleQ2GeometricHodgeThreefold
open CycleQ2GenericSexticGradient (CoeffRing)
open CycleQ2HodgeThreefoldTwist CycleQ2HodgeTwistRatios
open CycleQ2HodgeCotangentEulerSheaf (ambient conormalMap coefficient)
open CycleQ2HodgeCotangentAtlasForms (complexOn Form nativeForm localForm coordinate Cotangent)
open CycleQ2HodgeCotangentConormalComplex (affineMap)
open CycleQ2HodgeCotangentSectionFrames (drop drop_apply drop_conormal)
open CycleQ2HodgeCotangentGlobalMap (toCotangent toCotangent_on_subopen)
open CycleQ2HodgeCotangentAffineSections (sectionAlgebra sectionTower principal principal_le principal_isAffine principal_localization functions)
open CycleQ2GeometricAffineChartSections (schemeCoefficient)
open CycleQ2GeometricSectionDifferentials (toSheaf)
attribute [local instance] complexOn
variable (φ : CoeffRing →+* ℂ) (i : Fin 4) (V : (threefold φ).Opens) (hi : V ≤ U φ i)

def ordinaryMap : (Fin 4 → Γ(threefold φ,V)) →ₗ[Γ(threefold φ,V)] Form φ V :=
  ∑ j : Fin 4, (LinearMap.proj j).smulRight
    (KaehlerDifferential.D ℂ Γ(threefold φ,V)
      (affineMap φ i V hi (CycleQ2HodgeEuler.chartMap φ i (X j))))

theorem ordinaryMap_apply (v : Fin 4 → Γ(threefold φ,V)) :
    ordinaryMap φ i V hi v = ∑ j : Fin 4, v j •
      KaehlerDifferential.D ℂ Γ(threefold φ,V)
        (affineMap φ i V hi (CycleQ2HodgeEuler.chartMap φ i (X j))) := by
  simp [ordinaryMap]

theorem nativeForm_eq (a : Γ(ambient φ,V)) :
    nativeForm φ i V hi a = ordinaryMap φ i V hi (drop φ i V hi a) := by
  have hp : coordinate φ i V hi i.castSucc = 1 := by
    rw [← CycleQ2HodgeCotangentConormalComplex.affineMap_coordinate]
    simp [CycleQ2HodgeEuler.coordinate]
  unfold nativeForm
  rw [Fin.sum_univ_succAbove _ i.castSucc,hp,Derivation.map_one_eq_zero,smul_zero,zero_add,
    ordinaryMap_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [drop_apply,← CycleQ2HodgeCotangentConormalComplex.affineMap_coordinate,
    CycleQ2HodgeEuler.coordinate,CycleQ2HodgeEuler.dehom_X_succAbove]

theorem globalMap_eq (h : IsUnit (φ vertexCoefficient)) (a : Γ(ambient φ,V)) :
    (toCotangent φ h).app V a = toSheaf (threefold φ).sheaf
      (schemeCoefficient (toBase φ)) V (ordinaryMap φ i V hi (drop φ i V hi a)) := by
  rw [toCotangent_on_subopen φ h i V hi,
    CycleQ2HodgeCotangentAtlasForms.localForm_eq_toSheaf,nativeForm_eq]

theorem ordinaryMap_exact (S : Submonoid (CycleQ2HodgeEuler.chart φ i))
    (hS : letI := sectionAlgebra φ i V hi
      IsLocalization S Γ(threefold φ,V)) (v : Fin 4 → Γ(threefold φ,V)) :
    ordinaryMap φ i V hi v = 0 ↔ ∃ c : Γ(threefold φ,V), ∀ j : Fin 4,
      c * affineMap φ i V hi (CycleQ2HodgeEuler.chartMap φ i (pderiv j (CycleQ2HodgeEuler.F φ i))) = v j := by
  letI := sectionAlgebra φ i V hi
  letI := sectionTower φ i V hi
  letI := hS
  have he := CycleQ2HodgeCotangentLocalization.exact (CycleQ2HodgeEuler.F φ i) Γ(threefold φ,V) S v
  change ordinaryMap φ i V hi v = 0 ↔ ∃ c : Γ(threefold φ,V),
    (fun j => c * affineMap φ i V hi
      (CycleQ2HodgeEuler.chartMap φ i (pderiv j (CycleQ2HodgeEuler.F φ i)))) = v at he
  simpa only [funext_iff] using he

theorem ordinaryMap_surjective (S : Submonoid (CycleQ2HodgeEuler.chart φ i))
    (hS : letI := sectionAlgebra φ i V hi
      IsLocalization S Γ(threefold φ,V)) : Function.Surjective (ordinaryMap φ i V hi) := by
  letI := sectionAlgebra φ i V hi
  letI := sectionTower φ i V hi
  letI := hS
  exact CycleQ2HodgeCotangentLocalization.surjective (CycleQ2HodgeEuler.F φ i) Γ(threefold φ,V) S

theorem section_exact (h : IsUnit (φ vertexCoefficient)) (hV : IsAffineOpen V)
    (S : Submonoid (CycleQ2HodgeEuler.chart φ i))
    (hS : letI := sectionAlgebra φ i V hi
      IsLocalization S Γ(threefold φ,V)) :
    Function.Exact ((conormalMap φ).app V) ((toCotangent φ h).app V) := by
  intro a
  constructor
  · intro ha
    rw [globalMap_eq φ i V hi h] at ha
    have hb := (CycleQ2AffineOpenOrdinaryDifferentials.toSheaf_bijective_of_isAffineOpen
      (schemeCoefficient (toBase φ)) V hV).injective
    have hz : ordinaryMap φ i V hi (drop φ i V hi a) = 0 := hb (ha.trans (map_zero _).symm)
    obtain ⟨c,hc⟩ := (ordinaryMap_exact φ i V hi S hS _).mp hz
    refine ⟨(chartFrame φ (-6) i V hi).symm c,(drop φ i V hi).injective ?_⟩
    funext j
    rw [drop_conormal,LinearEquiv.apply_symm_apply,mul_comm]
    exact hc j
  · rintro ⟨s,rfl⟩
    exact congrArg (fun f : twist φ (-6) ⟶ Cotangent φ => f.app V s)
      (CycleQ2HodgeCotangentConormalComplex.conormal_differential φ h)

theorem section_surjective (h : IsUnit (φ vertexCoefficient)) (hV : IsAffineOpen V)
    (S : Submonoid (CycleQ2HodgeEuler.chart φ i))
    (hS : letI := sectionAlgebra φ i V hi
      IsLocalization S Γ(threefold φ,V)) : Function.Surjective ((toCotangent φ h).app V) := by
  intro ω
  obtain ⟨w,hw⟩ := (CycleQ2AffineOpenOrdinaryDifferentials.toSheaf_bijective_of_isAffineOpen
    (schemeCoefficient (toBase φ)) V hV).surjective ω
  obtain ⟨v,hv⟩ := ordinaryMap_surjective φ i V hi S hS w
  refine ⟨(drop φ i V hi).symm v,?_⟩
  rw [globalMap_eq φ i V hi h,LinearEquiv.apply_symm_apply,hv,hw]

theorem principal_exact (h : IsUnit (φ vertexCoefficient)) (r : Γ(threefold φ,coordinateOpen φ i)) :
    Function.Exact ((conormalMap φ).app (principal φ i r))
      ((toCotangent φ h).app (principal φ i r)) :=
  section_exact φ i _ (principal_le φ i r) h (principal_isAffine φ i r)
    (Submonoid.powers ((functions φ i).symm r)) (principal_localization φ i r)

theorem principal_surjective (h : IsUnit (φ vertexCoefficient)) (r : Γ(threefold φ,coordinateOpen φ i)) :
    Function.Surjective ((toCotangent φ h).app (principal φ i r)) :=
  section_surjective φ i _ (principal_le φ i r) h (principal_isAffine φ i r)
    (Submonoid.powers ((functions φ i).symm r)) (principal_localization φ i r)

end CycleQ2HodgeCotangentConormalLocal
end
#print axioms CycleQ2HodgeCotangentConormalLocal.principal_exact
#print axioms CycleQ2HodgeCotangentConormalLocal.principal_surjective
