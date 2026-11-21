import Proposal.GeometricLiteralMovingResiduePole
import Proposal.GeometricSeedSectionInvertible
import Proposal.GeometricSurfaceCoordinateFrames
import Proposal.GeometricCartierDeformation

/-!
# The residue quotient for the moving Cartier divisor

The regular inclusion into forms with one pole along the chosen curve is
injective. This gives a short exact sequence of additive sheaves on the
original surface with quotient the cokernel of the regular inclusion.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2LiteralMovingResidueExact

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open CycleQ2SeedProjectiveImageCocycle CycleQ2SeedSectionDivisorFrames
  CycleQ2SeedSectionDivisorTransitions CycleQ2SeedSectionSheafKernel
  CycleQ2SeedSectionSheafLocal CycleQ2SeedSectionSheafGlobal
  CycleQ2SeedSectionSheafCurveBinding CycleQ2SeedSectionAffineInjective
  CycleQ2GeometricIntrinsicNormal CycleQ2LocalHomFrame
open CycleQ2SurfaceCoordinateFrames (CanonicalForms coordinateExteriorFrame)
open CycleQ2SeedSectionSheafImage (sectionRows)
attribute [local instance] CycleQ2GeometricIntrinsicNormal.overHomCommModuleMk
  CycleQ2GeometricIntrinsicNormal.localLinearRingModule
  CycleQ2GeometricIntrinsicNormal.moduleHomObjModule

theorem regular_injective_on_pivot {W : Surface.Opens} (t : Fin 3 → ℂ)
    (ht : ∀ i, ChartRegular t i) (f : FrameData W) :
    Function.Injective ((idealRegularInclusion (curveToSurface t) CanonicalForms).val.app (op W)) := by
  let e := (coordinateExteriorFrame f.chart).app W f.within
  let gen := curveIdealFrame t ht f.chart W f.within f.pivot f.pivotUnit f.pivot_eq 1
  have heq : (kernel.ι (schemeStructureMap (curveToSurface t))).val.app (op W) gen =
      sectionRows t f.chart W f.within f.pivot.1 := by
    rw [← kernelIdealSectionEquiv_coe]
    simpa only [gen, one_mul] using
      (curveIdealFrame_coordinate t ht f.chart W f.within f.pivot f.pivotUnit f.pivot_eq 1)
  intro x y hxy
  have hv := congrArg (fun H => localLinearHomEvaluate Surface.sheaf (kernelIdealSheaf (curveToSurface t))
    CanonicalForms W H gen) hxy
  change localLinearHomEvaluate _ _ _ W ((regularInclusion _ _ _ _).val.app (op W) x) gen =
    localLinearHomEvaluate _ _ _ W ((regularInclusion _ _ _ _).val.app (op W) y) gen at hv
  rw [regularInclusion_evaluate, regularInclusion_evaluate] at hv
  let : Module Γ(Surface,W) (CanonicalForms.val.obj (op W)) := (CanonicalForms.val.obj (op W)).isModule
  let u := sectionRows t f.chart W f.within f.pivot.1
  have hh : u • x = u • y :=
    (congrArg (fun q : Γ(Surface,W) => q • x) heq).symm.trans
      (hv.trans (congrArg (fun q : Γ(Surface,W) => q • y) heq))
  apply e.injective
  apply curveEquation_regular_on_pivot t ht f.chart W f.within f.pivot f.pivotUnit f.pivot_eq
  exact (e.map_smul u x).symm.trans ((congrArg e hh).trans (e.map_smul u y))


open CycleQ2LiteralMovingResiduePole (PoleForms)
open CycleQ2GeometricModuleLocalIso (addSheaf)
open CycleQ2SeedSectionInvertible (pivotOpen pivotFrameData exists_pivotOpen_at)

/-- The actual regular-to-pole map, viewed on additive sheaves. -/
def regularInclusion (t : Fin 3 → ℂ) : addSheaf CanonicalForms ⟶ addSheaf (PoleForms t) :=
  (SheafOfModules.toSheaf (CycleQ2GeometricDifferentialSheaf.ringSheaf Surface.sheaf)).map
    (idealRegularInclusion (curveToSurface t) CanonicalForms)

theorem regular_injective (t : Fin 3 → ℂ) (ht : ∀ i, ChartRegular t i) (W : Surface.Opens) :
    Function.Injective ((regularInclusion t).hom.app (op W)) := by
  let U (a : Fin 3 × (Fin 3 × Fin 3)) := W ⊓ pivotOpen a.1 a.2
  have hWU : W ≤ ⨆ a, U a := by
    intro x hx
    obtain ⟨i,p,hp⟩ := exists_pivotOpen_at x
    exact Opens.mem_iSup.mpr ⟨(i,p), hx,hp⟩
  intro x y hxy
  apply (addSheaf CanonicalForms).eq_of_locally_eq' U W
    (fun a => homOfLE (show U a ≤ W from inf_le_left)) hWU x y
  intro a
  have f := (pivotFrameData a.1 a.2).restrict (show U a ≤ pivotOpen a.1 a.2 from inf_le_right)
  apply regular_injective_on_pivot t ht f
  let ι := regularInclusion t
  let h := homOfLE (show U a ≤ W from inf_le_left)
  change ι.hom.app (op (U a)) ((addSheaf CanonicalForms).obj.map h.op x) =
    ι.hom.app (op (U a)) ((addSheaf CanonicalForms).obj.map h.op y)
  rw [NatTrans.naturality_apply, NatTrans.naturality_apply, hxy]

theorem regular_mono (t : Fin 3 → ℂ) (ht : ∀ i, ChartRegular t i) :
    Mono (regularInclusion t) :=
  Sheaf.mono_of_injective _ (fun W => regular_injective t ht W.unop)

/-- The actual quotient sheaf of canonical pole forms by regular forms. -/
abbrev residueQuotient (t : Fin 3 → ℂ) := cokernel (regularInclusion t)

def residueComplex (t : Fin 3 → ℂ) : ShortComplex (TopCat.Sheaf AddCommGrpCat.{0} Surface) :=
  ShortComplex.mk (regularInclusion t) (cokernel.π _) (cokernel.condition _)

theorem residueShortExact (t : Fin 3 → ℂ) (ht : ∀ i, ChartRegular t i) :
    (residueComplex t).ShortExact where
  exact := ShortComplex.exact_cokernel (regularInclusion t)
  mono_f := regular_mono t ht
  epi_g := inferInstanceAs (Epi (cokernel.π (regularInclusion t)))

local instance : HasExt.{1} (Sheaf (Opens.grothendieckTopology Surface) AddCommGrpCat.{0}) :=
  HasExt.standard _

/-- Boundary of the genuine residue quotient on any original open. -/
def residueConnecting (t : Fin 3 → ℂ) (ht : ∀ i, ChartRegular t i) (U : Surface.Opens) :
    (residueQuotient t).H' 1 U →+ (addSheaf CanonicalForms).H' 2 U :=
  CycleQ2GeometricIntrinsicCartierCohomology.openConnecting (residueShortExact t ht) 1 U

local instance : HasExt.{1} (TopCat.Sheaf AddCommGrpCat.{0} (show TopCat from Surface)) :=
  HasExt.standard _

theorem residueConnecting_apply (t : Fin 3 → ℂ) (ht : ∀ i, ChartRegular t i) (U : Surface.Opens)
    (x : (residueQuotient t).H' 1 U) :
    residueConnecting t ht U x = x.comp (residueShortExact t ht).extClass rfl := rfl

end CycleQ2LiteralMovingResidueExact
end

#print axioms CycleQ2LiteralMovingResidueExact.regular_injective
#print axioms CycleQ2LiteralMovingResidueExact.residueShortExact

#print axioms CycleQ2LiteralMovingResidueExact.residueConnecting_apply
