import Proposal.GeometricChartTangentMaps
import Proposal.GeometricLiteralNativeChernCocycle

/-!
# The native contraction is actual tangent/differential-sheaf evaluation

Each native degree-zero intersection has its genuine original affine
chart. The arbitrary-derivation construction gives an actual local
Hom(Ω,O) section for every native derivation. On every native Kähler
form its sheaf evaluation is the original algebraic contraction. In
particular the actual native Kodaira--Spencer derivation evaluated on
the actual Cartier dlog is precisely the already checked scalar cup.

Prepared for fqlx with OpenAI ChatGPT assistance; see solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralNativeTangentEvaluation

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
  CycleQ2CartierProjectiveCover CycleQ2CartierSurfaceGrading CycleQ2LiteralProjectiveIntersections
  CycleQ2LiteralProjectiveIntersectionRestrictions CycleQ2LiteralProjectiveIntersectionComplex
  CycleQ2GeometricDifferentialSheaf CycleQ2GeometricIntrinsicNormal
  CycleQ2GeometricAffineChartSections CycleQ2GeometricDifferentialChartTransport
  CycleQ2GeometricSheafKaehlerMap CycleQ2GeometricChartTangentMaps
  CycleQ2LiteralNativeDifferentialSections CycleQ2LiteralNativeChernCocycle
  CycleQ2LiteralNativeKodairaSpencer CycleQ2LiteralNativeCupFrameGauge

attribute [local instance] CycleQ2LiteralProjectiveIntersectionComplex.closedComplexAlgebra
  CycleQ2LiteralProjectiveIntersectionComplex.closedComplexSMul
  CycleQ2LiteralProjectiveIntersectionComplex.closedComplexModule

abbrev structureModule := SheafOfModules.unit (ringSheaf Surface.sheaf)
abbrev tangentSheaf := moduleHomSheaf Surface.sheaf DifferentialSheaf structureModule

def nativeChart (s : Finset Vertex) (hs : s.Nonempty) :
    (closedOpen s).toScheme ≅ Spec (CommRingCat.of (ClosedRing s)) :=
  Proj.basicOpenIsoSpec (surfaceGrade 57 1) (closedProduct s)
    (closedProduct_homogeneous s) (productDegree_pos hs)

theorem nativeChart_coefficient (s : Finset Vertex) (hs : s.Nonempty) :
    (nativeChart s hs).inv ≫ (closedOpen s).ι ≫
        CycleQ2GeometricSurfaceCoefficients.projectiveToComplex 57 1 =
      Spec.map (CommRingCat.ofHom (algebraMap ℂ (ClosedRing s))) :=
  closedCoefficient_scheme s hs

theorem nativeChart_section (s : Finset Vertex) (hs : s.Nonempty) (a : ClosedRing s) :
    chartSection (nativeChart s hs) (chartTop (closedOpen s)) a = nativeSectionsAlgEquiv s hs a := by
  have he : CommRingCat.ofHom (chartSection (nativeChart s hs) (chartTop (closedOpen s))) =
      Proj.awayToSection (surfaceGrade 57 1) (closedProduct s) := by
    calc
      _ = (Scheme.ΓSpecIso (CommRingCat.of (ClosedRing s))).inv ≫
          (nativeChart s hs).hom.appTop ≫ (closedOpen s).topIso.hom :=
        chartSection_top (nativeChart s hs)
      _ = _ := by
        change (Scheme.ΓSpecIso (CommRingCat.of (ClosedRing s))).inv ≫
          (Proj.basicOpenToSpec (surfaceGrade 57 1) (closedProduct s)).app ⊤ ≫
            (Proj.basicOpen (surfaceGrade 57 1) (closedProduct s)).topIso.hom = _
        rw [Proj.basicOpenToSpec_app_top]
        simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
  exact ConcreteCategory.congr_hom he a

theorem nativeFormToSheaf_eq_sectionLift (s : Finset Vertex) (hs : s.Nonempty) :
    nativeFormToSheaf s hs = sectionLift Surface.sheaf globalCoefficient DifferentialSheaf
      (universalDifferential Surface.sheaf globalCoefficient) (closedOpen s)
      (chartSection (nativeChart s hs) (chartTop (closedOpen s)))
      (chartSection_complex (nativeChart s hs)
        (CycleQ2GeometricSurfaceCoefficients.projectiveToComplex 57 1)
        (nativeChart_coefficient s hs) (chartTop (closedOpen s))) := by
  symm
  apply sectionLift_unique
  · intro a ω
    exact (nativeFormToSheaf_smul s hs a ω).trans
      (congrArg (fun b : Γ(Surface,closedOpen s) => b • nativeFormToSheaf s hs ω)
        (nativeChart_section s hs a).symm)
  · intro a
    exact (nativeFormToSheaf_D s hs a).trans
      (congrArg ((universalDifferential Surface.sheaf globalCoefficient).d (X := op (closedOpen s)))
        (nativeChart_section s hs a).symm)

def nativeTangent (s : Finset Vertex) (hs : s.Nonempty) (δ : Derivation ℂ (ClosedRing s) (ClosedRing s)) :
    tangentSheaf.val.obj (op (closedOpen s)) :=
  tangentSection (nativeChart s hs)
    (CycleQ2GeometricSurfaceCoefficients.projectiveToComplex 57 1) (nativeChart_coefficient s hs) δ

def evaluateTangent (U : Surface.Opens) (δ : tangentSheaf.val.obj (op U)) :
    DifferentialSheaf.val.obj (op U) →ₗ[Γ(Surface,U)] Γ(Surface,U) :=
  localLinearHomEvaluate Surface.sheaf DifferentialSheaf structureModule U δ

theorem nativeTangent_on_form (s : Finset Vertex) (hs : s.Nonempty)
    (δ : Derivation ℂ (ClosedRing s) (ClosedRing s)) (ω : KaehlerDifferential ℂ (ClosedRing s)) :
    evaluateTangent (closedOpen s) (nativeTangent s hs δ) (nativeFormToSheaf s hs ω) =
      nativeSectionsAlgEquiv s hs (δ.liftKaehlerDifferential ω) := by
  rw [nativeFormToSheaf_eq_sectionLift s hs]
  exact (tangentSection_on_form (nativeChart s hs)
    (CycleQ2GeometricSurfaceCoefficients.projectiveToComplex 57 1) (nativeChart_coefficient s hs) δ ω).trans
      (nativeChart_section s hs (δ.liftKaehlerDifferential ω))

def nativeKodairaSpencerSection (s : Finset Vertex) (hs : s.Nonempty) (u v : Vertex)
    (hu : u ∈ s) (hv : v ∈ s) : tangentSheaf.val.obj (op (closedOpen s)) :=
  nativeTangent s hs (vertexKodairaSpencer s u v hu hv)

theorem nativeKodairaSpencer_evaluate_chern (s : Finset Vertex) (hs : s.Nonempty) (u v w : Vertex)
    (hu : u ∈ s) (hv : v ∈ s) (hw : w ∈ s) :
    evaluateTangent (closedOpen s) (nativeKodairaSpencerSection s hs u v hu hv)
      (nativeChernSection s hs v w hv hw) =
        closedSectionsEquiv s hs (nativeCup s u v w hu hv hw) :=
  nativeTangent_on_form s hs (vertexKodairaSpencer s u v hu hv) _

end CycleQ2LiteralNativeTangentEvaluation

end

#print axioms CycleQ2LiteralNativeTangentEvaluation.nativeTangent_on_form
#print axioms CycleQ2LiteralNativeTangentEvaluation.nativeKodairaSpencer_evaluate_chern
