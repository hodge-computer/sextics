import Proposal.GeometricLiteralThreefoldMixedRestriction
import Proposal.GeometricLiteralThreefoldSurfaceTestTransport
import Proposal.GeometricLiteralThreefoldCurveTestSections

/-!
# The adapted vertex lifts on the original central curve

The native surface splittings give actual dual-number chart coordinates
over every open in the twelve-vertex cover of the original curve. They
commute with restriction of the curve open and refinement of the surface
intersection used to express them.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2LiteralThreefoldCurveVertexLifts

open CategoryTheory AlgebraicGeometry TopologicalSpace
  CycleQ2LiteralAbelJacobiContraction CycleQ2LiteralThreefoldChartLift
  CycleQ2LiteralThreefoldLiftDifference CycleQ2LiteralThreefoldLiftTransition
  CycleQ2LiteralThreefoldTriangleLifts CycleQ2LiteralThreefoldResidueCoordinates
  CycleQ2LiteralThreefoldMixedRestriction CycleQ2LiteralThreefoldSurfaceTestLifts
  CycleQ2LiteralThreefoldCurveTestSections CycleQ2LiteralProjectiveIntersections
  CycleQ2LiteralProjectiveIntersectionComplex CycleQ2LiteralProjectiveIntersectionRestrictions
  CycleQ2LiteralProjectiveIntersectionSplittings
  CycleQ2LiteralMovingResidueAdjunction.AffineFrame CycleQ2SeedSectionSheafCurveBinding

attribute [local instance] closedComplexAlgebra closedComplexSMul closedComplexModule
  CycleQ2LiteralThreefoldCurveTestSections.curveComplexOn

variable (t : Fin 3 → ℂ) (s : Finset Vertex) (v : Vertex) (hv : v ∈ s)
  (W : (Curve t).Opens) (hW : W ≤ (curveToSurface t) ⁻¹ᵁ closedOpen s)

abbrev curvePoint : T (chartIndex v) →ₐ[ℂ] CurveRingOn t W :=
  (nativeToCurve t s ⟨v,hv⟩ W hW).comp (fixedPoint s v hv)

def curveLift (a : Fin 4) (ha : Admissible s a) : Lift (chartIndex v) (CurveRingOn t W) :=
  mapLift (nativeToCurve t s ⟨v,hv⟩ W hW) (surfaceLift s v hv a ha)

theorem curveLift_over (a : Fin 4) (ha : Admissible s a) :
    LiesOver (curveLift t s v hv W hW a ha) (curvePoint t s v hv W hW) :=
  mappedSurfaceLift_liesOver s v hv a ha _

theorem curvePoint_restrict {Z : (Curve t).Opens} (hZ : Z ≤ W) :
    (curveRestriction t hZ).comp (curvePoint t s v hv W hW) =
      curvePoint t s v hv Z (hZ.trans hW) := by
  unfold curvePoint
  rw [← AlgHom.comp_assoc, nativeToCurve_restrict]

theorem curveLift_restrict (a : Fin 4) (ha : Admissible s a) {Z : (Curve t).Opens} (hZ : Z ≤ W) :
    mapLift (curveRestriction t hZ) (curveLift t s v hv W hW a ha) =
      curveLift t s v hv Z (hZ.trans hW) a ha := by
  unfold curveLift
  rw [mapLift_comp, nativeToCurve_restrict]

theorem curveLift_refine {s u : Finset Vertex} (hsu : s ⊆ u) (v : Vertex) (hv : v ∈ s)
    (W : (Curve t).Opens) (hW : W ≤ (curveToSurface t) ⁻¹ᵁ closedOpen u)
    (a : Fin 4) (ha : Admissible s a) :
    curveLift t u v (hsu hv) W hW a (admissible_mono hsu ha) =
      curveLift t s v hv W (hW.trans ((Opens.map (curveToSurface t).base).map (homOfLE (closedOpen_mono hsu))).le) a ha := by
  unfold curveLift
  rw [← surfaceLift_restrict hsu v hv a ha, mapLift_comp, nativeToCurve_refine]

theorem curveLift_normalizes (u : Vertex) (hu : u ∈ s) (a : Fin 4) (ha : Admissible s a) :
    Normalizes (curveLift t s u hu W hW a ha) (curveLift t s v hv W hW a ha) := by
  let g := nativeToCurve t s ⟨u,hu⟩ W hW
  obtain ⟨b,hb,he⟩ := surfaceLift_normalizes s u v hu hv a ha
  refine ⟨jetMap g b, mapLift_change_inverse g _ _ b hb, ?_⟩
  exact (mapLift_change g _ _ b hb).symm.trans (congrArg (mapLift g) he)

theorem same_chart_lift {C : Type} [CommRing C] [Algebra ℂ C]
    {i : Fin 4} {x y : Lift i C} (h : Normalizes x y) : x = y := by
  obtain ⟨b,hb,rfl⟩ := h
  have hb' : b = 1 := by simpa only [linearValues, Fin.insertNth_apply_same, mul_one] using hb
  subst b
  apply lift_ext
  funext j
  cases j <;> simp [change, changedCoordinate]

/-- Restriction for two chart presentations with explicitly identified
coefficients and lifts. The velocities may use the native coefficient
structures belonging to their respective opens. -/
theorem vertexForm_restrict_to {C D : Type} [CommRing C] [Algebra ℂ C] [CommRing D] [Algebra ℂ D]
    {i : Fin 4} (f : T i →ₐ[ℂ] C) (g : C →ₐ[ℂ] D) (f' : T i →ₐ[ℂ] D) (hf : g.comp f = f')
    (x y : Lift i C) (x' y' : Lift i D) (hx : LiesOver x f) (hy : LiesOver y f)
    (hx' : LiesOver x' f') (hy' : LiesOver y' f') (ex : mapLift g x = x') (ey : mapLift g y = y') :
    letI := f.toRingHom.toAlgebra
    letI := IsScalarTower.of_algHom f
    letI := f'.toRingHom.toAlgebra
    letI := IsScalarTower.of_algHom f'
    ∀ (ν : Derivation ℂ (T i) C) (ν' : Derivation ℂ (T i) D), (∀ p, g (ν p) = ν' p) →
      CycleQ2GeometricAffineOverlap.differentialMap g (vertexForm f x y hx hy ν) =
        vertexForm f' x' y' hx' hy' ν' := by
  subst f'
  subst x'
  subst y'
  exact vertexForm_restrict f g x y hx hy

/-- The actual lifted chart attached to each vertex gives an ordinary
one-form after insertion of any ambient velocity along this curve open. -/
def curveVertex :
    let f := curvePoint t s v hv W hW
    letI := f.toRingHom.toAlgebra
    letI := IsScalarTower.of_algHom f
    Derivation ℂ (T (chartIndex v)) (CurveRingOn t W) → KaehlerDifferential ℂ (CurveRingOn t W) :=
  vertexForm (curvePoint t s v hv W hW)
    (canonical _ (curvePoint t s v hv W hW)) (curveLift t s v hv W hW v.1 ⟨v.2,hv⟩)
    (canonical_liesOver _ _) (curveLift_over t s v hv W hW v.1 ⟨v.2,hv⟩)

end CycleQ2LiteralThreefoldCurveVertexLifts
end

#print axioms CycleQ2LiteralThreefoldCurveVertexLifts.curveLift_restrict
#print axioms CycleQ2LiteralThreefoldCurveVertexLifts.curveLift_refine
#print axioms CycleQ2LiteralThreefoldCurveVertexLifts.curveVertex
