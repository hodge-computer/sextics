import Proposal.GeometricHodgeCotangentGlobalMap
import Proposal.GeometricHodgeCotangentEulerExact
import Proposal.GeometricHodgeGlobalConstants

/-!
# The original gradient is killed by the global cotangent map

The genuine chart algebra map carries the equation to zero and the
homogeneous gradient to its normalized section coefficients. Applying
the ordinary polynomial chain rule proves the conormal relation before
sheafification. Thus the actual global conormal and cotangent maps form
a complex. Exactness at the intrinsic cotangent sheaf is a further step.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 3000
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2HodgeCotangentConormalComplex

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace
open CycleQ2GeometricHodgeThreefold
open CycleQ2GenericSexticGradient (CoeffRing)
open CycleQ2HodgeThreefoldTwist CycleQ2HodgeTwistRatios
open CycleQ2HodgeCotangentEulerSheaf (ambient conormalMap conormalMap_ι pieceMap normalRaw normalComponent)
open CycleQ2HodgeEulerSheaf (partialValue partial_mem sectionMap sectionMap_coordinate sectionMap_gradient)
open CycleQ2HodgeCotangentAtlasForms (Cotangent Form nativeForm localForm localForm_eq_toSheaf coordinate complexOn)
open CycleQ2HodgeCotangentGlobalMap (globalForm globalForm_on_subopen toCotangent)
open CycleQ2GeometricAffineChartSections (schemeCoefficient)
open CycleQ2GeometricDifferentialSheaf (coefficientOn)
open CycleQ2GeometricProjectiveCurve.Twisted (res res_comp)
open CycleQ2SeedSectionSheafLocal (moduleRes moduleRes_app)
open CycleQ2GeometricModuleLocalIso (addSheaf)

attribute [local instance] complexOn

variable (φ : CoeffRing →+* ℂ)

private theorem sectionMap_complex (i : Fin 4) (V : (threefold φ).Opens) (hi : V ≤ U φ i) (c : ℂ) :
    sectionMap φ i V hi (chartCoefficient φ i c) =
      coefficientOn (threefold φ).sheaf (schemeCoefficient (toBase φ)) V c := by
  have he := congrArg (res (threefold φ).sheaf hi) (CycleQ2HodgeGlobalConstants.chartScalar φ i c)
  change res _ hi (res _ le_top (schemeCoefficient (toBase φ) c)) =
    sectionMap φ i V hi (chartCoefficient φ i c) at he
  rw [res_comp] at he
  exact he.symm

def affineMap (i : Fin 4) (V : (threefold φ).Opens) (hi : V ≤ U φ i) :
    CycleQ2HodgeEuler.chart φ i →ₐ[ℂ] Γ(threefold φ,V) where
  toRingHom := (sectionMap φ i V hi).comp (CycleQ2HodgeEulerChartBinding.chartEquiv φ i).symm.toRingHom
  commutes' c := by
    change sectionMap φ i V hi
      ((CycleQ2HodgeEulerChartBinding.chartEquiv φ i).symm (algebraMap ℂ _ c)) = _
    rw [AlgEquiv.commutes]
    exact sectionMap_complex φ i V hi c

theorem affineMap_coordinate (i : Fin 4) (V : (threefold φ).Opens) (hi : V ≤ U φ i) (j : Fin 5) :
    affineMap φ i V hi (CycleQ2HodgeEuler.coordinate φ i j) = coordinate φ i V hi j := by
  change sectionMap φ i V hi ((CycleQ2HodgeEulerChartBinding.chartEquiv φ i).symm _) = _
  unfold CycleQ2HodgeEuler.coordinate
  rw [← CycleQ2HodgeEulerChartBinding.chartEquiv_ratio,AlgEquiv.symm_apply_apply]
  exact sectionMap_coordinate φ i V hi j

theorem affineMap_partial (i : Fin 4) (V : (threefold φ).Opens) (hi : V ≤ U φ i) (j : Fin 5) :
    affineMap φ i V hi (CycleQ2HodgeEuler.conePartial φ i j) =
      normalized φ i (partialValue φ j) (partial_mem φ j) V hi := by
  change sectionMap φ i V hi ((CycleQ2HodgeEulerChartBinding.chartEquiv φ i).symm _) = _
  rw [← CycleQ2HodgeEulerChartBinding.chartEquiv_gradientRatio,AlgEquiv.symm_apply_apply]
  exact sectionMap_gradient φ i V hi j

/-- The conormal relation holds in the ordinary Kähler module on every chart subopen. -/
theorem gradient_relation (i : Fin 4) (V : (threefold φ).Opens) (hi : V ≤ U φ i) :
    (∑ j : Fin 5, normalized φ i (partialValue φ j) (partial_mem φ j) V hi •
      KaehlerDifferential.D ℂ Γ(threefold φ,V) (coordinate φ i V hi j)) = 0 := by
  let f := affineMap φ i V hi
  let d := KaehlerDifferential.D ℂ Γ(threefold φ,V)
  have hc := CycleQ2PolynomialChainRule.apply (f.comp (CycleQ2HodgeEuler.chartMap φ i)) d
    (CycleQ2HodgeEuler.F φ i)
  change d (f (CycleQ2HodgeEuler.chartMap φ i (CycleQ2HodgeEuler.F φ i))) = _ at hc
  rw [CycleQ2HodgeEuler.chartMap_F,map_zero,map_zero] at hc
  have hp : coordinate φ i V hi i.castSucc = 1 := by
    rw [← affineMap_coordinate]
    simp [CycleQ2HodgeEuler.coordinate]
  rw [Fin.sum_univ_succAbove _ i.castSucc,hp,Derivation.map_one_eq_zero,smul_zero,zero_add]
  calc
    _ = ∑ j : Fin 4, f (CycleQ2HodgeEuler.chartMap φ i (MvPolynomial.pderiv j (CycleQ2HodgeEuler.F φ i))) •
        d (f (CycleQ2HodgeEuler.chartMap φ i (MvPolynomial.X j))) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [← affineMap_partial,← affineMap_coordinate,CycleQ2HodgeEuler.partial_succAbove,
        CycleQ2HodgeEuler.coordinate,CycleQ2HodgeEuler.dehom_X_succAbove]
    _ = 0 := hc.symm

theorem coefficient_conormal (i : Fin 4) (V : (threefold φ).Opens) (hi : V ≤ U φ i)
    (s : Γ(twist φ (-6),V)) (j : Fin 5) :
    CycleQ2HodgeCotangentEulerSheaf.coefficient φ i V hi ((conormalMap φ).app V s) j =
      normalized φ i (partialValue φ j) (partial_mem φ j) V hi * chartFrame φ (-6) i V hi s := by
  have hm : conormalMap φ ≫ pieceMap φ j = normalComponent φ j := by
    rw [pieceMap,← Category.assoc,conormalMap_ι,normalRaw,Pi.lift_π]
  change chartFrame φ _ i V hi ((conormalMap φ ≫ pieceMap φ j).app V s) = _
  rw [hm]
  exact multiply_frame φ (partialValue φ j) (partial_mem φ j) _ _ _ i V hi s

theorem nativeForm_conormal_zero (i : Fin 4) (V : (threefold φ).Opens) (hi : V ≤ U φ i)
    (s : Γ(twist φ (-6),V)) : nativeForm φ i V hi ((conormalMap φ).app V s) = 0 := by
  unfold nativeForm
  simp_rw [coefficient_conormal]
  calc
    _ = chartFrame φ (-6) i V hi s • (∑ j : Fin 5,
        normalized φ i (partialValue φ j) (partial_mem φ j) V hi •
          KaehlerDifferential.D ℂ Γ(threefold φ,V) (coordinate φ i V hi j)) := by
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [← mul_smul,mul_comm]
    _ = 0 := by rw [gradient_relation,smul_zero]

theorem localForm_conormal_zero (i : Fin 4) (V : (threefold φ).Opens) (hi : V ≤ U φ i)
    (s : Γ(twist φ (-6),V)) : localForm φ i V hi ((conormalMap φ).app V s) = 0 := by
  rw [localForm_eq_toSheaf,nativeForm_conormal_zero,map_zero]

/-- The two actual sheaf morphisms compose to zero on the original monic locus. -/
theorem conormal_differential (h : IsUnit (φ vertexCoefficient)) :
    conormalMap φ ≫ toCotangent φ h = 0 := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro O
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  let V := O.unop
  change globalForm φ h V ((conormalMap φ).app V s) = 0
  have hcov : (⨆ i : Fin 4, V ⊓ U φ i) = V := by
    rw [← inf_iSup_eq,coordinateOpens_cover φ h,inf_top_eq]
  apply (addSheaf (Cotangent φ)).eq_of_locally_eq' (fun i : Fin 4 => V ⊓ U φ i) V
    (fun _ => homOfLE inf_le_left) hcov.ge
  intro i
  change moduleRes (Cotangent φ) inf_le_left (globalForm φ h V ((conormalMap φ).app V s)) =
    moduleRes (Cotangent φ) inf_le_left 0
  rw [globalForm_on_subopen φ h i inf_le_left inf_le_right,moduleRes_app,
    localForm_conormal_zero,map_zero]

def conormalSequence (h : IsUnit (φ vertexCoefficient)) : ShortComplex (threefold φ).Modules :=
  ShortComplex.mk (conormalMap φ) (toCotangent φ h) (conormal_differential φ h)

end CycleQ2HodgeCotangentConormalComplex
end

#print axioms CycleQ2HodgeCotangentConormalComplex.gradient_relation
#print axioms CycleQ2HodgeCotangentConormalComplex.conormal_differential
