import Proposal.GeometricThreefoldMixedConormal
import Proposal.GeometricFiniteCechOrbitPullback
import Proposal.GeometricLiteralThreefoldCurveTestSections
import Proposal.GeometricLiteralThreefoldCubicFrame
import Proposal.GeometricLiteralMovingResidueCurve

/-!
# The signed cubic form on the original curve

The tangent of a Jacobian-chart function is computed by the genuine native
Kodaira–Spencer derivation. The signed mixed differential on the original
curve equals the pullback of the contracted Čech edge on every common open.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1400000

noncomputable section
namespace CycleQ2LiteralThreefoldCubicPullback

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
  CycleQ2LiteralAbelJacobiContraction CycleQ2LiteralThreefoldSurfaceAdjunction
  CycleQ2LiteralThreefoldSurfaceNormal CycleQ2LiteralThreefoldMovingVolume
  CycleQ2GeometricSurfaceAdjunction CycleQ2GeometricSurfaceCoefficients
  CycleQ2GeometricSurfaceDehomogenizedCharts CycleQ2GeometricSurfaceJacobianCharts
  CycleQ2GeometricAffineChartSections CycleQ2GeometricPrincipalChartSections
  CycleQ2GeometricExteriorLocalFrames CycleQ2GeometricSurfaceExteriorSections
  CycleQ2GeometricExteriorSheaf CycleQ2GeometricDifferentialSheaf
  CycleQ2LiteralAbelJacobiContractedCocycle CycleQ2LiteralAbelJacobiSheafContraction
  CycleQ2LiteralAbelJacobiSurfaceWedge CycleQ2LiteralNativeTangentEvaluation
  CycleQ2LiteralNativeDifferentialSections CycleQ2LiteralNativeKodairaSpencerCocycle
  CycleQ2LiteralNativeChernCocycle CycleQ2LiteralNativeGaugeSections
  CycleQ2LiteralProjectiveIntersections CycleQ2FiniteCechDescent
  CycleQ2SeedSectionSheafCurveBinding CycleQ2LiteralMovingResidueCurve
  CycleQ2LiteralMovingResidueAdjunction CycleQ2LiteralMovingResidueAdjunction.AffineFrame
  CycleQ2GeometricSectionDifferentials CycleQ2GeometricAffineOverlap

variable (n a : SurfacePoly) (j : Fin 3) (V : Over (patch n a j))

open CycleQ2GeometricDifferentialChartTransport CycleQ2GeometricSheafKaehlerMap
  CycleQ2GeometricSchemeDifferentialMap CycleQ2ThreefoldMixedCurveForm
  CycleQ2ThreefoldCurveEvaluation CycleQ2LiteralAbelJacobiEquations

attribute [local instance] AffineFrame.surfaceAlgebra AffineFrame.curveAlgebra
  CycleQ2LiteralNativeDifferentialSections.sectionComplexAlgebra

abbrev patchToSections : Patch j.succ n a →ₐ[ℂ] Γ(Surface,V.left) where
  toRingHom := chartSection (frameChart n a j) V
  commutes' := chartSection_complex (frameChart n a j) (CycleQ2GeometricSurfaceCoefficients.projectiveToComplex 57 1) (frameComplex n a j) V

variable (t : Fin 3 → ℂ)

abbrev patchToCurve := (curveAppHom t V.left).comp (patchToSections n a j V)

local instance patchCurveAlgebra : Algebra (Patch j.succ n a) (CurveRing t V.left) :=
  (patchToCurve n a j V t).toRingHom.toAlgebra
local instance patchCurveTower : IsScalarTower ℂ (Patch j.succ n a) (CurveRing t V.left) :=
  IsScalarTower.of_algHom (patchToCurve n a j V t)

private abbrev pullOn (t : Fin 3 → ℂ) (O : Surface.Opens) :
    DifferentialSheaf.val.obj (op O) →+ (curveDifferentials t).val.obj (op ((curveToSurface t) ⁻¹ᵁ O)) :=
  ((schemeDifferentialMap (curveToSurface t) (curveCoefficient t) globalCoefficient
    (fun _ c => curveMap_constants t c)).val.app (op O)).hom.toAddMonoidHom

private theorem pull_smul (r : Γ(Surface,V.left)) (x : DifferentialSheaf.val.obj (op V.left)) :
    pullOn t V.left (r • x) = (curveAppHom t V.left r : SectionRing (Curve t).sheaf _) • pullOn t V.left x :=
  ((schemeDifferentialMap (curveToSurface t) (curveCoefficient t) globalCoefficient
    (fun _ c => curveMap_constants t c)).val.app (op V.left)).hom.map_smul r x

private theorem pull_ordinary (α : KaehlerDifferential ℂ (Patch j.succ n a)) :
    pullOn t V.left (ordinaryOn n a j V α) =
      toSheaf (Curve t).sheaf (curveCoefficient t) ((curveToSurface t) ⁻¹ᵁ V.left)
        (KaehlerDifferential.map ℂ ℂ (Patch j.succ n a) (CurveRing t V.left) α) := by
  have h := CycleQ2ActualCubicAdjunctionBinding.sectionLift_eq_toSheaf Surface.sheaf globalCoefficient
    V.left (patchToSections n a j V) α
  change ordinaryOn n a j V α = _ at h
  exact (congrArg (pullOn t V.left) h).trans ((pullbackForms_toSheaf t V.left _).trans
    (congrArg (toSheaf (Curve t).sheaf (curveCoefficient t) _)
      ((differentialMap_comp (patchToSections n a j V) (curveAppHom t V.left) α).trans
        (CycleQ2EtaleExteriorMapBinding.differentialMap_algebraMap α))))

/-- Restrict a genuine tangent section to the patch ring with coefficients
on the image of the original curve. -/
def tangentFunctional (δ : tangentSheaf.val.obj (op V.left)) :
    KaehlerDifferential ℂ (Patch j.succ n a) →ₗ[Patch j.succ n a] CurveRing t V.left where
  toFun α := curveAppHom t V.left (evaluateTangent V.left δ (ordinaryOn n a j V α))
  map_add' α β := by simp only [map_add]
  map_smul' r α := by
    have h : ordinaryOn n a j V (r • α) = patchToSections n a j V r • ordinaryOn n a j V α :=
      sectionLift_smul _ _ _ _ _ _ _ r α
    rw [h, map_smul, smul_eq_mul, map_mul]
    rfl

def tangentAlong (δ : tangentSheaf.val.obj (op V.left)) :
    Derivation ℂ (Patch j.succ n a) (CurveRing t V.left) :=
  KaehlerDifferential.linearMapEquivDerivation ℂ (Patch j.succ n a)
    (tangentFunctional n a j V t δ)

theorem tangentAlong_lift (δ : tangentSheaf.val.obj (op V.left))
    (α : KaehlerDifferential ℂ (Patch j.succ n a)) :
    (tangentAlong n a j V t δ).liftKaehlerDifferential α =
      curveAppHom t V.left (evaluateTangent V.left δ (ordinaryOn n a j V α)) :=
  LinearMap.congr_fun ((KaehlerDifferential.linearMapEquivDerivation ℂ (Patch j.succ n a)).symm_apply_apply
    (tangentFunctional n a j V t δ)) α

/-- Pullback of the sheaf interior is the sheafification of the ordinary
one-form obtained by inserting the same tangent along the curve. -/
theorem pull_contract (δ : tangentSheaf.val.obj (op V.left))
    (ω : ⋀[Patch j.succ n a]^2 (KaehlerDifferential ℂ (Patch j.succ n a))) :
    pullOn t V.left (contract (evaluateTangent V.left δ) (exteriorOn n a j V ω)) =
      toSheaf (Curve t).sheaf (curveCoefficient t) ((curveToSurface t) ⁻¹ᵁ V.left)
        (contractRestrict (tangentAlong n a j V t δ) ω) := by
  have hw : ω ∈ Submodule.span (Patch j.succ n a) (Set.range (exteriorPower.ιMulti (Patch j.succ n a) 2)) := by
    rw [exteriorPower.ιMulti_span]; trivial
  induction hw using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨m,rfl⟩ := hz
    have hm : m = ![m 0,m 1] := by funext i; fin_cases i <;> rfl
    rw [hm, chartExteriorSection_wedge]
    erw [contract_wedge (evaluateTangent V.left δ) (ordinaryOn n a j V (m 0)) (ordinaryOn n a j V (m 1)), contractRestrict_wedge,
      map_sub, map_sub]
    simp only [pull_smul n a j V t, pull_ordinary n a j V t, map_smul, tangentAlong_lift]
  | zero => simp only [map_zero]
  | add x y _ _ hx hy => simp only [map_add, hx, hy]
  | smul r x _ hx =>
    have hs := IsScalarTower.algebraMap_smul (CurveRing t V.left) r
      (contractRestrict (tangentAlong n a j V t δ) x)
    have ht := (toSheaf (Curve t).sheaf (curveCoefficient t) ((curveToSurface t) ⁻¹ᵁ V.left)).map_smul
      (show SectionRing (Curve t).sheaf _ from algebraMap (Patch j.succ n a) (CurveRing t V.left) r)
      (contractRestrict (tangentAlong n a j V t δ) x)
    rw [LinearMap.map_smulₛₗ, map_smul, pull_smul n a j V t, hx,
      (contractRestrict (tangentAlong n a j V t δ)).map_smul, ← hs]
    exact ht.symm

/-- The one-form of the original surface Čech edge, on its actual curve
intersection and in the same oriented residue used by double contraction. -/
theorem pull_contractedValue (s : Finset Vertex) (hs : s.Nonempty) (u v : Vertex)
    (hu : u ∈ s) (hv : v ∈ s) (hW : V.left ≤ closedOpen s)
    (hU : V.left ≤ cover u) (hV : V.left ≤ cover v) :
    (pullbackForms t).hom.app (op V.left) (contractedValue u v V.left hU hV) =
      toSheaf (Curve t).sheaf (curveCoefficient t) ((curveToSurface t) ⁻¹ᵁ V.left)
        (contractRestrict (tangentAlong n a j V t
          (CycleQ2GeometricSheafLocalIso.res tangentAddSheaf hW (nativeKodairaSpencerSection s hs u v hu hv)))
          (orientedCubic n a j)) := by
  exact (congrArg (pullOn t V.left) (contractedValue_jacobian n a j V s hs u v hu hv hW hU hV)).trans
    (pull_contract n a j V t _ _)

open CycleQ2LiteralThreefoldCurveTestSections CycleQ2LiteralNativeKodairaSpencer
  CycleQ2LiteralProjectiveIntersectionComplex CycleQ2GeometricIntrinsicNormal
  CycleQ2GeometricSurfaceResidueSections

attribute [local instance] closedComplexAlgebra curveComplexOn curveSectionComplexOn

/-- The actual pullback cocycle on a smaller open of the curve is obtained
by restricting its ordinary Jacobian one-form. -/
theorem pull_contractedValue_subopen (s : Finset Vertex) (hs : s.Nonempty) (u v : Vertex)
    (hu : u ∈ s) (hv : v ∈ s) (hW : V.left ≤ closedOpen s)
    (hU : V.left ≤ cover u) (hV : V.left ≤ cover v)
    (W : (Curve t).Opens) (h : W ≤ (curveToSurface t) ⁻¹ᵁ V.left) :
    CycleQ2FiniteCechOrbitPullback.pullTo (curveToSurface t).base (pullbackForms t) h
      (contractedValue u v V.left hU hV) =
    toSheaf (Curve t).sheaf (curveCoefficient t) W
      (differentialMap (curveRestriction t h) (contractRestrict (tangentAlong n a j V t
        (CycleQ2GeometricSheafLocalIso.res tangentAddSheaf hW (nativeKodairaSpencerSection s hs u v hu hv)))
        (orientedCubic n a j))) :=
  (congrArg (CycleQ2GeometricSheafLocalIso.res (curveForms t) h)
    (pull_contractedValue n a j V t s hs u v hu hv hW hU hV)).trans
    (toSheaf_restrict (Curve t).sheaf (curveCoefficient t) h _)

/-- The tangent of any Jacobian-coordinate function that comes from a
homogeneous native function is the native Kodaira–Spencer coefficient
pulled back along the original closed immersion. -/
theorem tangentAlong_native (s : Finset Vertex) (hs : s.Nonempty) (u w : Vertex)
    (hu : u ∈ s) (hw : w ∈ s) (hW : V.left ≤ closedOpen s)
    (z : Patch j.succ n a) (b : ClosedRing s)
    (hb : patchToSections n a j V z = Surface.presheaf.map (homOfLE hW).op (nativeSectionsAlgEquiv s hs b)) :
    tangentAlong n a j V t (CycleQ2GeometricSheafLocalIso.res tangentAddSheaf hW
        (nativeKodairaSpencerSection s hs u w hu hw)) z =
      nativeToCurve t s hs ((curveToSurface t) ⁻¹ᵁ V.left)
        (((Opens.map (curveToSurface t).base).map (homOfLE hW)).le)
        (vertexKodairaSpencer s u w hu hw b) := by
  let κ := vertexKodairaSpencer s u w hu hw
  let δ := nativeKodairaSpencerSection s hs u w hu hw
  let r := Surface.presheaf.map (homOfLE hW).op
  let p := curveAppHom t V.left
  let D := KaehlerDifferential.D ℂ (ClosedRing s)
  have hf : ordinaryOn n a j V (KaehlerDifferential.D ℂ (Patch j.succ n a) z) =
      DifferentialSheaf.val.map (homOfLE hW).op (nativeFormToSheaf s hs (D b)) := by
    refine (chartKaehlerSection_D _ _ _ _ z).trans ?_
    rw [show chartSection (frameChart n a j) V z = _ from hb, nativeFormToSheaf_D]
    exact (universalDifferential Surface.sheaf globalCoefficient).d_map (homOfLE hW).op _
  have he : evaluateTangent V.left (CycleQ2GeometricSheafLocalIso.res tangentAddSheaf hW δ)
      (DifferentialSheaf.val.map (homOfLE hW).op (nativeFormToSheaf s hs (D b))) =
      r (evaluateTangent (closedOpen s) δ (nativeFormToSheaf s hs (D b))) :=
    localLinearHomEvaluate_restrict Surface.sheaf DifferentialSheaf structureModule (homOfLE hW) δ _
  change p (evaluateTangent V.left (CycleQ2GeometricSheafLocalIso.res tangentAddSheaf hW δ)
    (ordinaryOn n a j V (KaehlerDifferential.D ℂ (Patch j.succ n a) z))) = _
  have hκ : evaluateTangent (closedOpen s) δ (nativeFormToSheaf s hs (D b)) = nativeSectionsAlgEquiv s hs (κ b) :=
    (nativeTangent_on_form s hs κ (D b)).trans (congrArg (nativeSectionsAlgEquiv s hs)
      (Derivation.liftKaehlerDifferential_comp_D κ b))
  rw [hf, he, hκ, nativeToCurve_apply]
  have hm := (curveToSurface t).map_appLE (V := (curveToSurface t) ⁻¹ᵁ V.left) le_rfl (homOfLE hW).op
  rw [Scheme.Hom.appLE_eq_app] at hm
  exact ConcreteCategory.congr_hom hm (nativeSectionsAlgEquiv s hs (κ b))

attribute [local instance] CycleQ2LiteralAbelJacobiContraction.fixedCommRing
  CycleQ2LiteralAbelJacobiContraction.fixedAlgebra CycleQ2LiteralAbelJacobiContraction.fixedTower
  CycleQ2LiteralThreefoldSurfaceNormal.patchAlgebra CycleQ2LiteralThreefoldSurfaceNormal.patchTower

local instance ambientCurveAlgebra : Algebra (T j.succ) (CurveRing t V.left) :=
  ((patchToCurve n a j V t).comp (toSurface j.succ n a)).toRingHom.toAlgebra
local instance ambientCurveComplexTower : IsScalarTower ℂ (T j.succ) (CurveRing t V.left) :=
  IsScalarTower.of_algHom ((patchToCurve n a j V t).comp (toSurface j.succ n a))
local instance ambientCurvePatchTower : IsScalarTower (T j.succ) (Patch j.succ n a) (CurveRing t V.left) :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- Signed adjunction for the pulled-back edge on the original curve. -/
theorem signed_pullback
    (s : Finset Vertex) (hs : s.Nonempty) (u w : Vertex) (hu : u ∈ s) (hw : w ∈ s)
    (hW : V.left ≤ closedOpen s) (hU : V.left ≤ cover u) (hV : V.left ≤ cover w)
    (v : Derivation ℂ (T j.succ) (CurveRing t V.left))
    (hv : v (cubicOnT j.succ) = -(patchToCurve n a j V t
      (algebraMap _ (Patch j.succ n a) (tangentL j.succ)))) :
    let x := tangentAlong n a j V t (CycleQ2GeometricSheafLocalIso.res tangentAddSheaf hW
      (nativeKodairaSpencerSection s hs u w hu hw))
    toSheaf (Curve t).sheaf (curveCoefficient t) ((curveToSurface t) ⁻¹ᵁ V.left)
      (mixed (x.compAlgebraMap (T j.succ)) v (orientedVolume j.succ)) =
        -((pullbackForms t).hom.app (op V.left) (contractedValue u w V.left hU hV)) := by
  intro x
  have he : mixed (x.compAlgebraMap (T j.succ)) v (orientedVolume j.succ) =
      -(contractRestrict x (orientedCubic n a j)) := by
    exact CycleQ2ThreefoldMixedConormal.oriented_double_form n a j x v hv
  rw [he, map_neg, pull_contractedValue n a j V t s hs u w hu hw hW hU hV]

/-- The original signed mixed form on any further curve subopen. Both
ambient vectors are compared on functions before the contraction. -/
theorem signed_pullback_subopen (s : Finset Vertex) (hs : s.Nonempty) (u w : Vertex) (hu : u ∈ s) (hw : w ∈ s)
    (hW : V.left ≤ closedOpen s) (hU : V.left ≤ cover u) (hV : V.left ≤ cover w)
    (v : Derivation ℂ (T j.succ) (CurveRing t V.left))
    (hv : v (cubicOnT j.succ) = -(patchToCurve n a j V t (algebraMap _ (Patch j.succ n a) (tangentL j.succ))))
    (W : (Curve t).Opens) (h : W ≤ (curveToSurface t) ⁻¹ᵁ V.left) :
    let r := curveRestriction t h
    let φ := r.comp ((patchToCurve n a j V t).comp (toSurface j.succ n a))
    letI := φ.toRingHom.toAlgebra
    letI := IsScalarTower.of_algHom φ
    let k := (tangentAlong n a j V t (CycleQ2GeometricSheafLocalIso.res tangentAddSheaf hW
      (nativeKodairaSpencerSection s hs u w hu hw))).compAlgebraMap (T j.succ)
    ∀ (k' v' : Derivation ℂ (T j.succ) (CurveRingOn t W)),
      (∀ z, r (k z) = k' z) → (∀ z, r (v z) = v' z) →
      toSheaf (Curve t).sheaf (curveCoefficient t) W (mixed k' v' (orientedVolume j.succ)) =
        -(CycleQ2FiniteCechOrbitPullback.pullTo (curveToSurface t).base (pullbackForms t) h
          (contractedValue u w V.left hU hV)) := by
  let r := curveRestriction t h
  let φ := r.comp ((patchToCurve n a j V t).comp (toSurface j.succ n a))
  let := φ.toRingHom.toAlgebra
  let := IsScalarTower.of_algHom φ
  let k := (tangentAlong n a j V t (CycleQ2GeometricSheafLocalIso.res tangentAddSheaf hW
    (nativeKodairaSpencerSection s hs u w hu hw))).compAlgebraMap (T j.succ)
  intro _ _ _ k' v' hk hv'
  have hmix := mixed_natural r (fun _ => rfl) k v k' v' hk hv' (orientedVolume j.succ)
  have hres := toSheaf_restrict (Curve t).sheaf (curveCoefficient t) h (mixed k v (orientedVolume j.succ))
  have hsign := signed_pullback n a j V t s hs u w hu hw hW hU hV v hv
  exact (congrArg (toSheaf (Curve t).sheaf (curveCoefficient t) W) hmix.symm).trans (hres.symm.trans
    ((congrArg (CycleQ2GeometricSheafLocalIso.res (curveForms t) h) hsign).trans (map_neg _ _)))

end CycleQ2LiteralThreefoldCubicPullback
end


#print axioms CycleQ2LiteralThreefoldCubicPullback.pull_contractedValue

#print axioms CycleQ2LiteralThreefoldCubicPullback.signed_pullback

#print axioms CycleQ2LiteralThreefoldCubicPullback.tangentAlong_native
#print axioms CycleQ2LiteralThreefoldCubicPullback.signed_pullback_subopen
