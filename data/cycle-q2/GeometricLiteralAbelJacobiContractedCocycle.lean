import Proposal.GeometricLiteralAbelJacobiSheafContraction
import Proposal.GeometricLiteralSheafOneClasses
import Proposal.GeometricIncidenceFirstOrderCanonicalH2

/-!
# The contracted surface Kodaira–Spencer class

Interior multiplication by the global canonical form of the retained
incidence cubic sends the ambient-test Kodaira–Spencer cocycle to a
one-cocycle of the original differential sheaf. Its derived class is
the image under this same map of sheaves.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralAbelJacobiContractedCocycle

open CategoryTheory CategoryTheory.Abelian Opposite TopologicalSpace AlgebraicGeometry
  CycleQ2InjectiveCech CycleQ2GeometricSheafLocalIso CycleQ2FiniteInjectiveCech
  CycleQ2FiniteCechDescent CycleQ2FiniteCechHOne CycleQ2LiteralProjectiveIntersections
  CycleQ2LiteralNativeDifferentialSections CycleQ2LiteralNativeTangentEvaluation
  CycleQ2LiteralNativeKodairaSpencerCocycle CycleQ2LiteralNativeChernCocycle
  CycleQ2LiteralNativeGaugeSections CycleQ2LiteralAbelJacobiSheafContraction
  CycleQ2CanonicalResidueDiagram CycleQ2LiteralSheafOneClasses

local instance surfaceHasExt :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology (show TopCat from Surface)) AddCommGrpCat.{0}) :=
  HasExt.standard _

abbrev tangentCubicForm : TwoForms.val.obj (op (⊤ : Surface.Opens)) := CycleQ2GlobalSurfaceCubics.globalCubicSection
  CycleQ2IncidenceFirstOrderCanonicalH2.firstOrderWeightedCubic

private abbrev localForm (W : Surface.Opens) : TwoForms.val.obj (op W) :=
  TwoForms.val.map W.leTop.op tangentCubicForm

private theorem localForm_restrict {U V : Surface.Opens} (f : V ⟶ U) :
    TwoForms.val.map f.op (localForm U) = localForm V := by
  unfold localForm
  rw [← PresheafOfModules.map_comp_apply]
  congr 2

private def contractSection (W : Surface.Opens) : Sections tangentAddSheaf W →+ Sections differentialAddSheaf W where
  toFun δ := interior W δ (localForm W)
  map_add' δ η := interior_add W δ η _
  map_zero' := by
    have h := interior_add W 0 0 (localForm W)
    rw [zero_add] at h
    exact add_left_cancel (h.symm.trans (add_zero _).symm)

/-- Contraction of a tangent section with the restricted global canonical form. -/
def contractionMap : tangentAddSheaf ⟶ differentialAddSheaf where
  hom :=
    { app := fun U => AddCommGrpCat.ofHom (contractSection U.unop)
      naturality := by
        intro U V f
        apply ConcreteCategory.hom_ext
        intro δ
        change interior V.unop (tangentSheaf.val.map f δ) (localForm V.unop) =
          DifferentialSheaf.val.map f (interior U.unop δ (localForm U.unop))
        exact (congrArg (interior V.unop (tangentSheaf.val.map f δ))
          (localForm_restrict f.unop).symm).trans
            (interior_restrict U.unop δ f.unop.le (localForm U.unop)).symm }

def contractedValue (u v : Vertex) (W : Surface.Opens) (hu : W ≤ cover u) (hv : W ≤ cover v) :
    Sections differentialAddSheaf W :=
  interior W (kodairaSpencerValue u v W hu hv) (localForm W)

def contractedOne : One differentialAddSheaf cover :=
  mapOne cover contractionMap kodairaSpencerOne

theorem edgeValue_contractedOne (u v : Vertex) (W : Surface.Opens) (hu : W ≤ cover u) (hv : W ≤ cover v) :
    edgeValue differentialAddSheaf cover contractedOne u v W hu hv = contractedValue u v W hu hv := by
  rw [contractedOne, edgeValue_mapOne, edgeValue_kodairaSpencerOne]
  rfl

theorem contractedValue_restrict (u v : Vertex) {W V : Surface.Opens} (h : V ≤ W)
    (hu : W ≤ cover u) (hv : W ≤ cover v) :
    res differentialAddSheaf h (contractedValue u v W hu hv) =
      contractedValue u v V (h.trans hu) (h.trans hv) := by
  rw [← edgeValue_contractedOne, ← edgeValue_contractedOne]
  exact res_comp differentialAddSheaf _ _ _

theorem contractedOne_closed : IsOneCocycle differentialAddSheaf cover contractedOne :=
  mapOne_closed cover contractionMap kodairaSpencerOne kodairaSpencerOne_closed

theorem contractedValue_cocycle (u v w : Vertex) (W : Surface.Opens)
    (hu : W ≤ cover u) (hv : W ≤ cover v) (hw : W ≤ cover w) :
    contractedValue u w W hu hw = contractedValue u v W hu hv + contractedValue v w W hv hw := by
  have h := contractedOne_closed u v w W hu hv hw
  change edgeValue differentialAddSheaf cover contractedOne u w W hu hw =
    edgeValue differentialAddSheaf cover contractedOne u v W hu hv +
      edgeValue differentialAddSheaf cover contractedOne v w W hv hw at h
  simpa only [edgeValue_contractedOne] using h

def contractedCocycle : CartierCechCoverTransfer.OneCocycle differentialAddSheaf cover where
  val := contractedOne
  condition u v w W hu hv hw := (contractedOne_closed u v w W hu hv hw).symm

def contractedClass : differentialAddSheaf.H' 1 ⊤ :=
  cechOneClass cover cover_covers contractedOne contractedOne_closed

/-- Naturality identifies the class with the image of the original ambient-test
Kodaira–Spencer class in the derived cohomology of the same surface. -/
theorem contractedClass_eq_image :
    contractedClass = kodairaSpencerDerivedClass.comp (Ext.mk₀ contractionMap) (Nat.add_zero 1) :=
  (cechOneClass_naturality cover cover_covers contractionMap kodairaSpencerOne kodairaSpencerOne_closed).symm

end CycleQ2LiteralAbelJacobiContractedCocycle
end

#print axioms CycleQ2LiteralAbelJacobiContractedCocycle.contractedOne_closed
#print axioms CycleQ2LiteralAbelJacobiContractedCocycle.contractedClass_eq_image
