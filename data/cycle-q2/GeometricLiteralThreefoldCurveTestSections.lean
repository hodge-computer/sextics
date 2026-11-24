import Proposal.GeometricLiteralMovingResidueAffineCurve
import Proposal.GeometricLiteralNativeTangentEvaluation
import Proposal.GeometricChartSectionPullback

/-!
# Restriction of the native test surface to the section curve

The homogeneous ring of a native surface intersection maps through its
actual affine sections and the original curve immersion to every open
over that intersection. These maps commute with both types of restriction.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option maxHeartbeats 750000
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2LiteralThreefoldCurveTestSections

open AlgebraicGeometry CategoryTheory Opposite CycleQ2LiteralMovingResidueAdjunction
  CycleQ2LiteralMovingResidueAdjunction.AffineFrame CycleQ2SeedSectionSheafCurveBinding
  CycleQ2LiteralNativeDifferentialSections CycleQ2GeometricSectionDifferentials
  CycleQ2LiteralProjectiveIntersections CycleQ2LiteralProjectiveIntersectionRestrictions
  CycleQ2LiteralProjectiveIntersectionComplex CycleQ2LiteralNativeGaugeSections
  CycleQ2GeometricAffineChartSections CycleQ2LiteralNativeTangentEvaluation CycleQ2ChartSectionPullback

attribute [local instance] closedComplexAlgebra AffineFrame.curveAlgebra AffineFrame.surfaceAlgebra
  CycleQ2LiteralNativeDifferentialSections.sectionComplexAlgebra

abbrev CurveRingOn (t : Fin 3 → ℂ) (W : (Curve t).Opens) := Γ(Curve t,W)

local instance curveComplexOn (t : Fin 3 → ℂ) (W : (Curve t).Opens) :
    Algebra ℂ (CurveRingOn t W) := sectionAlgebra (Curve t).sheaf (curveCoefficient t) W

local instance curveSectionComplexOn (t : Fin 3 → ℂ) (W : (Curve t).Opens) :
    Algebra ℂ (SectionRing (Curve t).sheaf W) := sectionAlgebra (Curve t).sheaf (curveCoefficient t) W

abbrev curveRestriction (t : Fin 3 → ℂ) {W Z : (Curve t).Opens} (h : Z ≤ W) :
    CurveRingOn t W →ₐ[ℂ] CurveRingOn t Z :=
  sectionRestriction (Curve t).sheaf (curveCoefficient t) h

/-- The twelve original surface opens pulled back by the actual closed curve immersion. -/
def vertexOpen (t : Fin 3 → ℂ) (v : Vertex) : (Curve t).Opens :=
  (curveToSurface t) ⁻¹ᵁ cover v

theorem vertexOpen_cover (t : Fin 3 → ℂ) : (⨆ v, vertexOpen t v) = ⊤ := by
  change (⨆ v : Vertex, (curveToSurface t) ⁻¹ᵁ cover v) = ⊤
  rw [← Scheme.Hom.preimage_iSup, cover_covers, Scheme.Hom.preimage_top]

/-- Pullback from the genuine homogeneous intersection ring, along the
original immersion and then to any smaller curve open. -/
def nativeToCurve (t : Fin 3 → ℂ) (s : Finset Vertex) (hs : s.Nonempty) (W : (Curve t).Opens)
    (h : W ≤ (curveToSurface t) ⁻¹ᵁ closedOpen s) : ClosedRing s →ₐ[ℂ] CurveRingOn t W :=
  (curveRestriction t h).comp
    ((curveAppHom t (closedOpen s)).comp (nativeSectionsAlgEquiv s hs).toAlgHom)

theorem nativeToCurve_apply (t : Fin 3 → ℂ) (s : Finset Vertex) (hs : s.Nonempty) (W : (Curve t).Opens)
    (h : W ≤ (curveToSurface t) ⁻¹ᵁ closedOpen s) (x : ClosedRing s) :
    nativeToCurve t s hs W h x = (curveToSurface t).appLE (closedOpen s) W h (nativeSectionsAlgEquiv s hs x) :=
  rfl

/-- Restricting the curve open is the same as applying the original map
directly on that smaller open. -/
theorem nativeToCurve_restrict (t : Fin 3 → ℂ) (s : Finset Vertex) (hs : s.Nonempty)
    {W Z : (Curve t).Opens} (hW : W ≤ (curveToSurface t) ⁻¹ᵁ closedOpen s) (hZ : Z ≤ W) :
    (curveRestriction t hZ).comp (nativeToCurve t s hs W hW) =
      nativeToCurve t s hs Z (hZ.trans hW) := by
  apply AlgHom.ext
  intro x
  exact ConcreteCategory.congr_hom ((curveToSurface t).appLE_map hW (homOfLE hZ).op) (nativeSectionsAlgEquiv s hs x)

/-- Refining the native surface intersection before pulling back gives
the same map on every common open of the original curve. -/
theorem nativeToCurve_refine (t : Fin 3 → ℂ) {s u : Finset Vertex} (hsu : s ⊆ u)
    (hs : s.Nonempty) (hu : u.Nonempty) (W : (Curve t).Opens)
    (h : W ≤ (curveToSurface t) ⁻¹ᵁ closedOpen u) :
    (nativeToCurve t u hu W h).comp (closedRestrictionAlgHom hsu) =
      nativeToCurve t s hs W (h.trans ((TopologicalSpace.Opens.map (curveToSurface t).base).map
        (homOfLE (closedOpen_mono hsu))).le) := by
  apply AlgHom.ext
  intro x
  rw [AlgHom.comp_apply, nativeToCurve_apply, nativeToCurve_apply, ← nativeSectionsAlgEquiv_restrict]
  exact ConcreteCategory.congr_hom ((curveToSurface t).map_appLE h (homOfLE (closedOpen_mono hsu)).op)
    (nativeSectionsAlgEquiv s hs x)

/-- A native function identified with the restriction of an ambient section
pulls back along the composite of the two scheme morphisms on every curve subopen. -/
theorem nativeToCurve_of_surfacePull {Y : Scheme.{0}} (j : Surface ⟶ Y)
    (t : Fin 3 → ℂ) (s : Finset Vertex) (hs : s.Nonempty) (U : Y.Opens) (hU : closedOpen s ≤ j ⁻¹ᵁ U)
    (W : (Curve t).Opens) (hW : W ≤ (curveToSurface t) ⁻¹ᵁ closedOpen s) (x : ClosedRing s) (y : Γ(Y,U))
    (hx : nativeSectionsAlgEquiv s hs x = j.appLE U (closedOpen s) hU y) :
    nativeToCurve t s hs W hW x = (curveToSurface t ≫ j).appLE U W
      (hW.trans ((TopologicalSpace.Opens.map (curveToSurface t).base).map (homOfLE hU)).le) y := by
  exact (nativeToCurve_apply t s hs W hW x).trans ((congrArg ((curveToSurface t).appLE (closedOpen s) W hW) hx).trans
    (ConcreteCategory.congr_hom (Scheme.Hom.appLE_comp_appLE (curveToSurface t) j U (closedOpen s) W hU hW) y))

/-- A commuting affine chart square identifies the native pullback with the
actual composite on scheme functions, on every open of the section curve. -/
theorem nativeToCurve_chart {Y : Scheme.{0}} (j : Surface ⟶ Y) (U : Y.Opens)
    {A : Type} [CommRing A] (e : U.toScheme ≅ Spec (CommRingCat.of A))
    (t : Fin 3 → ℂ) (s : Finset Vertex) (hs : s.Nonempty) (φ : A →+* ClosedRing s)
    (hU : closedOpen s ≤ j ⁻¹ᵁ U)
    (hc : (nativeChart s hs).inv ≫ (closedOpen s).ι ≫ j = Spec.map (CommRingCat.ofHom φ) ≫ e.inv ≫ U.ι)
    (W : (Curve t).Opens) (hW : W ≤ (curveToSurface t) ⁻¹ᵁ closedOpen s) (x : A) :
    nativeToCurve t s hs W hW (φ x) = (curveToSurface t ≫ j).appLE U W
      (hW.trans ((TopologicalSpace.Opens.map (curveToSurface t).base).map (homOfLE hU)).le)
      (chartSection e (Over.mk (𝟙 U)) x) := by
  apply nativeToCurve_of_surfacePull
  exact (nativeChart_section s hs (φ x)).symm.trans (chartSection_pullback_top j e (nativeChart s hs) φ hU hc x).symm

end CycleQ2LiteralThreefoldCurveTestSections
end

#print axioms CycleQ2LiteralThreefoldCurveTestSections.vertexOpen_cover
#print axioms CycleQ2LiteralThreefoldCurveTestSections.nativeToCurve_refine
#print axioms CycleQ2LiteralThreefoldCurveTestSections.nativeToCurve_restrict
#print axioms CycleQ2LiteralThreefoldCurveTestSections.nativeToCurve_chart
