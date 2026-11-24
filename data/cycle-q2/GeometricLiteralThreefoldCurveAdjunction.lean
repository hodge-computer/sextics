import Proposal.GeometricLiteralThreefoldCurveAdaptedValue
import Proposal.GeometricLiteralThreefoldCubicPullback
import Proposal.GeometricLiteralThreefoldJacobianChartMap
import Proposal.GeometricLiteralThreefoldCurveClassRepresentative
import Proposal.GeometricLiteralThreefoldCurveJacobianCover

/-!
# Signed cubic adjunction for the actual adapted edge

The native surface splittings define the same derivation as the Jacobian
chart tangent on every fixed threefold function. The genuine moving
velocity differentiates the cubic to its prescribed negative coefficient.
These two identifications give signed adjunction for the actual corrected
edge on the original curve cover.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 800000
set_option maxRecDepth 3000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
noncomputable section
namespace CycleQ2LiteralThreefoldCurveAdjunction

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite MvPolynomial
  CycleQ2LiteralThreefoldCurveAdaptedValue CycleQ2LiteralThreefoldCubicPullback
  CycleQ2LiteralThreefoldCurveClassRepresentative CycleQ2LiteralThreefoldCurveTestSections
  CycleQ2LiteralThreefoldVertexMotion CycleQ2LiteralThreefoldVertexPointBinding
  CycleQ2LiteralThreefoldSurfaceNormal CycleQ2LiteralThreefoldChartLift
  CycleQ2LiteralThreefoldSurfaceTestLifts CycleQ2LiteralThreefoldSurfaceAdjunction
  CycleQ2LiteralThreefoldMovingVolume CycleQ2LiteralAbelJacobiEquations CycleQ2LiteralAbelJacobiContraction
  CycleQ2LiteralAbelJacobiEvaluationChart CycleQ2LiteralAbelJacobiMovingNormal CycleQ2LiteralCylinderEvaluation
  CycleQ2LiteralMovingResidueAdjunction CycleQ2LiteralMovingResidueAdjunction.AffineFrame CycleQ2LiteralNativeGaugeSections
  CycleQ2LiteralProjectiveIntersections CycleQ2LiteralProjectiveIntersectionComplex CycleQ2SeedSectionSheafCurveBinding
  CycleQ2LiteralNativeDifferentialSections CycleQ2LiteralNativeKodairaSpencerCocycle
  CycleQ2LiteralNativeTangentEvaluation CycleQ2GeometricSurfaceAdjunction
  CycleQ2LiteralMovingResidueCurve CycleQ2LiteralThreefoldCurveVertexLifts CycleQ2LiteralThreefoldCurveVertexCochain
  CycleQ2GeometricSchemeDifferentialMap CycleQ2GeometricSheafLocalIso CycleQ2FiniteInjectiveCech CycleQ2FiniteCechDescent
  CycleQ2ThreefoldMixedCurveForm CycleQ2LiteralThreefoldSurfaceNormal CycleQ2GeometricSectionDifferentials
  CycleQ2GeometricSurfaceJacobianCharts CycleQ2FullSurfaceJacobianCover
  CycleQ2LiteralAbelJacobiContractedCocycle

attribute [local instance] CycleQ2IncidenceSeedFiber.seedAlgebra
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderAlgebra
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderModule
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderSMul
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderTower
  familyRing closedRing threefoldRing CycleQ2CurveParameterTangent.chartComplexAlgebra
  familyAlgebra familyComplexTower CycleQ2LiteralAbelJacobiContraction.fixedAlgebra
  CycleQ2LiteralAbelJacobiContraction.fixedTower reductionAlgebra fixedCurveTower familyReductionTower
  AffineFrame.surfaceAlgebra AffineFrame.curveAlgebra curveComplexOn curveSectionComplexOn closedComplexAlgebra patchAlgebra patchTower
  CycleQ2LiteralThreefoldCubicPullback.patchCurveAlgebra CycleQ2LiteralThreefoldCubicPullback.patchCurveTower
  CycleQ2LiteralThreefoldCubicPullback.ambientCurveAlgebra CycleQ2LiteralThreefoldCubicPullback.ambientCurveComplexTower
  CycleQ2LiteralThreefoldCubicPullback.ambientCurvePatchTower

section Transport
variable {C : Type} [CommRing C] [Algebra ℂ C] {i : Fin 4}

private abbrev Vel (f : T i →ₐ[ℂ] C) := letI := f.toRingHom.toAlgebra; Derivation ℂ (T i) C

private def move {f g : T i →ₐ[ℂ] C} (h : f = g) (v : Vel f) : Vel g := by
  let vl : T i →ₗ[ℂ] C := by
    letI := f.toRingHom.toAlgebra
    exact v.toLinearMap
  have ho : vl 1 = 0 := by
    letI := f.toRingHom.toAlgebra
    exact v.map_one_eq_zero
  have hl (a b : T i) : vl (a*b) = f a * vl b + f b * vl a := by
    letI := f.toRingHom.toAlgebra
    exact v.leibniz a b
  letI := g.toRingHom.toAlgebra
  refine { toLinearMap := vl, map_one_eq_zero' := ho, leibniz' := ?_ }
  intro a b
  change vl (a*b) = g a * vl b + g b * vl a
  rw [← AlgHom.congr_fun h a, ← AlgHom.congr_fun h b]
  exact hl a b

private theorem move_apply {f g : T i →ₐ[ℂ] C} (h : f = g) (v : Vel f) (r : T i) :
    move h v r = v r := rfl

private def contraction (f : T i →ₐ[ℂ] C) (k v : Vel f) : KaehlerDifferential ℂ C := by
  letI := f.toRingHom.toAlgebra
  letI := IsScalarTower.of_algHom f
  exact mixed k v (orientedVolume i)

private theorem contraction_move {f g : T i →ₐ[ℂ] C} (h : f = g) (k v : Vel f) (z : Vel g)
    (hk : ∀ r, k r = z r) : contraction f k v = contraction g z (move h v) := by
  subst g
  letI := f.toRingHom.toAlgebra
  exact congrArg (fun x => contraction f x v) (Derivation.ext hk)
end Transport

variable (t : Fin 3 → ℂ) (ht : AlgebraicIndependent ℚ t) (s : Finset Vertex)
  (u v : Vertex) (hu : u ∈ s) (hv : v ∈ s) (n a : SurfacePoly)
  (V : Over (patch n a v.2)) (hs : V.left ≤ closedOpen s)

private abbrev W := (curveToSurface t) ⁻¹ᵁ V.left
private abbrev hW : W t v n a V ≤ (curveToSurface t) ⁻¹ᵁ closedOpen s := (curveToSurface t).preimage_mono hs
private abbrev basePoint := ambientPoint t v (W t v n a V) (withinVertex t s v hv _ (hW t s v n a V hs))
private abbrev patchPoint := (patchToCurve n a v.2 V t).comp (toSurface (chartIndex v) n a)

private theorem sections_eq (r : T (chartIndex v)) : patchToSections n a v.2 V (toSurface (chartIndex v) n a r) =
    Surface.presheaf.map (homOfLE hs).op (nativeSectionsAlgEquiv s ⟨v,hv⟩ (fixedPoint s v hv r)) :=
  CycleQ2LiteralThreefoldJacobianChartMap.surface_sections_equal s ⟨v,hv⟩ v hv n a V.left V.hom.le hs r

private theorem point_eq : basePoint t s v hv n a V hs = patchPoint t v n a V := by
  refine (ambientPoint_eq_native t s ⟨v,hv⟩ v hv _ (hW t s v n a V hs)).symm.trans ?_
  apply AlgHom.ext
  intro r
  let b := nativeSectionsAlgEquiv s ⟨v,hv⟩ (fixedPoint s v hv r)
  have eq := congrArg (curveAppHom t V.left) (sections_eq s v hv n a V hs r)
  have hm := (curveToSurface t).map_appLE (V := W t v n a V) le_rfl (homOfLE hs).op
  rw [Scheme.Hom.appLE_eq_app] at hm
  exact (ConcreteCategory.congr_hom hm b).symm.trans eq.symm

private def nativeVelocity : Vel (basePoint t s v hv n a V hs) :=
  ambientMotion t v (W t v n a V) (withinVertex t s v hv _ (hW t s v n a V hs))
    (normalizedVelocity t (chartIndex v) ht)

private def nativeTangent : Vel (basePoint t s v hv n a V hs) :=
  ksVector t s u v hu hv _ (hW t s v n a V hs)

private def patchTangent : Vel (patchPoint t v n a V) :=
  (tangentAlong n a v.2 V t
    (res tangentAddSheaf hs (nativeKodairaSpencerSection s ⟨v,hv⟩ u v hu hv))).compAlgebraMap
      (T (chartIndex v))

private def patchVelocity : Vel (patchPoint t v n a V) :=
  move (point_eq t s v hv n a V hs) (nativeVelocity t ht s v hv n a V hs)

private theorem tangent_values (r : T (chartIndex v)) :
    nativeTangent t s u v hu hv n a V hs r = patchTangent t s u v hu hv n a V hs r :=
  (ksVector_apply t s u v hu hv _ (hW t s v n a V hs) r).trans
    (tangentAlong_native n a v.2 V t s ⟨v,hv⟩ u v hu hv hs (toSurface (chartIndex v) n a r)
      (fixedPoint s v hv r) (sections_eq s v hv n a V hs r)).symm

private theorem nativePoint_q (r : P) :
    seedSections t v (W t v n a V) (withinVertex t s v hv _ (hW t s v n a V hs))
      (seedChartMap t (chartIndex v) r) = basePoint t s v hv n a V hs (q (chartIndex v) r) := rfl

private theorem patchPoint_q (r : P) :
    patchPoint t v n a V (q (chartIndex v) r) =
      patchToCurve n a v.2 V t (algebraMap P (Patch (chartIndex v) n a) r) := rfl

private theorem point_polynomial (r : P) :
    seedSections t v (W t v n a V) (withinVertex t s v hv _ (hW t s v n a V hs))
      (seedChartMap t (chartIndex v) r) =
      patchToCurve n a v.2 V t (algebraMap P (Patch (chartIndex v) n a) r) :=
  (nativePoint_q t s v hv n a V hs r).trans
    ((AlgHom.congr_fun (point_eq t s v hv n a V hs) (q (chartIndex v) r)).trans
      (patchPoint_q t v n a V r))

private theorem normalized_cubic :
    nativeVelocity t ht s v hv n a V hs (cubicOnT (chartIndex v)) =
      -(seedSections t v (W t v n a V) (withinVertex t s v hv _ (hW t s v n a V hs))
        (seedChartMap t (chartIndex v) (tangentL (chartIndex v)))) :=
  ambientMotion_cubic t v _ (withinVertex t s v hv _ (hW t s v n a V hs))
    (normalizedVelocity t (chartIndex v) ht) (normalizedVelocity_epsilon t (chartIndex v) ht)

private theorem moved_value (r : T (chartIndex v)) :
    patchVelocity t ht s v hv n a V hs r = nativeVelocity t ht s v hv n a V hs r :=
  move_apply (point_eq t s v hv n a V hs) (nativeVelocity t ht s v hv n a V hs) r

private theorem cubic_velocity :
    patchVelocity t ht s v hv n a V hs (cubicOnT (chartIndex v)) =
      -(patchToCurve n a v.2 V t (algebraMap _ (Patch (chartIndex v) n a) (tangentL (chartIndex v)))) :=
  (moved_value t ht s v hv n a V hs (cubicOnT (chartIndex v))).trans
    ((normalized_cubic t ht s v hv n a V hs).trans
      (congrArg Neg.neg (point_polynomial t s v hv n a V hs (tangentL (chartIndex v)))))

private theorem native_contraction :
    adapted t ht s u v hu hv _ (hW t s v n a V hs) =
      contraction (basePoint t s v hv n a V hs) (nativeTangent t s u v hu hv n a V hs)
        (nativeVelocity t ht s v hv n a V hs) := rfl

private theorem contraction_compare :
    contraction (basePoint t s v hv n a V hs) (nativeTangent t s u v hu hv n a V hs)
      (nativeVelocity t ht s v hv n a V hs) =
    contraction (patchPoint t v n a V) (patchTangent t s u v hu hv n a V hs)
      (patchVelocity t ht s v hv n a V hs) :=
  contraction_move (point_eq t s v hv n a V hs) _ _ _ (tangent_values t s u v hu hv n a V hs)

private theorem patch_signed (hU : V.left ≤ cover u) (hV : V.left ≤ cover v) :
    (toSheaf (Curve t).sheaf (curveCoefficient t) (W t v n a V)).toFun
      (contraction (patchPoint t v n a V) (patchTangent t s u v hu hv n a V hs)
        (patchVelocity t ht s v hv n a V hs)) =
      -((pullbackForms t).hom.app (op V.left) (contractedValue u v V.left hU hV)) :=
  signed_pullback n a v.2 V t s ⟨v,hv⟩ u v hu hv hs hU hV
    (patchVelocity t ht s v hv n a V hs) (cubic_velocity t ht s v hv n a V hs)

theorem adapted_on_jacobian (hU : V.left ≤ cover u) (hV : V.left ≤ cover v) :
    (toSheaf (Curve t).sheaf (curveCoefficient t) (W t v n a V)).toFun
      (adapted t ht s u v hu hv _ (hW t s v n a V hs)) =
    -edgeValue (curveForms t) (vertexOpen t) (beta t) u v (W t v n a V)
      ((curveToSurface t).preimage_mono hU) ((curveToSurface t).preimage_mono hV) := by
  refine (congrArg (toSheaf (Curve t).sheaf (curveCoefficient t) (W t v n a V)).toFun
    ((native_contraction t ht s u v hu hv n a V hs).trans
      (contraction_compare t ht s u v hu hv n a V hs))).trans ?_
  refine (patch_signed t ht s u v hu hv n a V hs hU hV).trans ?_
  apply congrArg Neg.neg
  rw [beta_edge t u v V.left hU hV (W t v n a V) le_rfl]
  exact (res_self (curveForms t) (W t v n a V) _).symm

/-- Every curve subopen lying in one of the sixteen Jacobian patches has
the same signed section identity. -/
theorem adapted_below_jacobian (m l : Fin 4) (W : (Curve t).Opens)
    (hW : W ≤ (curveToSurface t) ⁻¹ᵁ closedOpen s)
    (hJ : W ≤ (curveToSurface t) ⁻¹ᵁ CycleQ2LiteralThreefoldCurveJacobianCover.jacobianOpen v.2 m l) :
    (toSheaf (Curve t).sheaf (curveCoefficient t) W).toFun (adapted t ht s u v hu hv W hW) =
      -edgeValue (curveForms t) (vertexOpen t) (beta t) u v W
        (withinVertex t s u hu W hW) (withinVertex t s v hv W hW) := by
  let n₀ : SurfacePoly := X (variableIndex m)
  let a₀ : SurfacePoly := X (variableIndex l)
  let O := closedOpen s ⊓ patch n₀ a₀ v.2
  have hWO : W ≤ (curveToSurface t) ⁻¹ᵁ O := le_inf hW hJ
  obtain ⟨P,hP,e⟩ := CycleQ2LiteralThreefoldCurveJacobianCover.exists_surface_refinement t O W hWO
  subst W
  let hPs := hP.trans inf_le_left
  let hPj := hP.trans inf_le_right
  have hv' (w : Vertex) (hw : w ∈ s) : P ≤ cover w := hPs.trans (by
    rw [closedOpen_eq]
    exact iInf₂_le w hw)
  exact adapted_on_jacobian t ht s u v hu hv n₀ a₀ (Over.mk (homOfLE hPj)) hPs (hv' u hu) (hv' v hv)

end CycleQ2LiteralThreefoldCurveAdjunction
end

#print axioms CycleQ2LiteralThreefoldCurveAdjunction.adapted_on_jacobian
