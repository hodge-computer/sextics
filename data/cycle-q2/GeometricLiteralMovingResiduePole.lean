import Proposal.GeometricCanonicalResidueSheaf
import Proposal.GeometricSeedSectionDivisorTransitions
import Proposal.GeometricLiteralNativeDifferentialSections

/-!
# Pole sections on the original moving Cartier curve

A regular numerator and a pivot equation define a homomorphism from the
actual moving ideal to the canonical sheaf on the pivot open. The formula
uses the coefficient in the original ideal basis on every subopen.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralMovingResiduePole

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open CycleQ2GeometricDifferentialSheaf CycleQ2GeometricIntrinsicNormal
  CycleQ2GeometricIntrinsicCartierSequence CycleQ2LocalHomFrame
  CycleQ2SeedProjectiveImageCocycle CycleQ2SeedSectionAffineInjective
  CycleQ2SeedSectionDivisorFrames CycleQ2SeedSectionDivisorTransitions
  CycleQ2SeedSectionSheafLocal CycleQ2SeedSectionSheafKernel
  CycleQ2SeedSectionSheafCurveBinding CycleQ2SeedSectionSheaf
  CycleQ2SeedSectionSheafGlobal CycleQ2SeedSectionSheafImage
open CycleQ2CanonicalResidueSheaf (CanonicalForms)

abbrev PoleForms (t : Fin 3 → ℂ) := moduleHomSheaf Surface.sheaf (curveIdeal t) CanonicalForms

local instance canonicalModule (W : Surface.Opens) :
    Module Γ(Surface,W) (CanonicalForms.val.obj (op W)) := (CanonicalForms.val.obj (op W)).isModule

variable (t : Fin 3 → ℂ) (ht : ∀ i, ChartRegular t i) {W : Surface.Opens}

abbrev frame (f : FrameData W) := curveIdealFrame t ht f.chart W f.within f.pivot f.pivotUnit f.pivot_eq

private theorem frame_restrict (f : FrameData W) {V : Surface.Opens} (h : V ≤ W)
    (r : Γ(Surface,W)) :
    moduleRes (curveIdeal t) h (frame t ht f r) =
      frame t ht (f.restrict h) (targetRes h r) := by
  apply (kernelIdealSectionEquiv (curveToSurface t) V).injective
  apply Subtype.ext
  change ((kernelIdealSectionEquiv (curveToSurface t) V
    ((kernelIdealSheaf (curveToSurface t)).val.map (homOfLE h).op (frame t ht f r))) : Γ(Surface,V)) = _
  rw [kernelIdealSectionEquiv_restrict]
  simp only [frame, curveIdealFrame_coordinate, map_mul, sectionRows_restrict]
  rfl

theorem coordinate_restrict (f : FrameData W) {V : Surface.Opens} (h : V ≤ W)
    (x : Γ(curveIdeal t,W)) :
    (frame t ht (f.restrict h)).symm (moduleRes (curveIdeal t) h x) =
      targetRes h ((frame t ht f).symm x) := by
  apply (frame t ht (f.restrict h)).injective
  rw [LinearEquiv.apply_symm_apply, ← frame_restrict, LinearEquiv.apply_symm_apply]

private theorem frame_unique {V : Surface.Opens} (a b : FrameData V)
    (hc : a.chart = b.chart) (hp : a.pivot = b.pivot) : a = b := by
  rcases a with ⟨i,hi,p,u,hu⟩
  rcases b with ⟨j,hj,q,v,hv⟩
  dsimp only at hc hp
  subst j
  subst q
  have huv : u = v := Units.ext (hu.trans hv.symm)
  subst v
  rfl

/-- The value on the ideal coordinate is the prescribed numerator restricted
to the same open. This makes a section of the actual internal Hom. -/
def poleOfNumerator (f : FrameData W) (σ : CanonicalForms.val.obj (op W)) :
    (PoleForms t).val.obj (op W) :=
  ⟨{
    app V := AddCommGrpCat.ofHom
      { toFun := fun x => (frame t ht (f.restrict V.unop.hom.le)).symm x •
          CanonicalForms.val.map V.unop.hom.op σ
        map_zero' := by rw [map_zero, zero_smul]
        map_add' := by intro a b; rw [map_add, add_smul] }
    naturality {V Q} a := by
      apply ConcreteCategory.hom_ext
      intro x
      change (frame t ht (f.restrict Q.unop.hom.le)).symm
          (moduleRes (curveIdeal t) a.unop.left.le x) • CanonicalForms.val.map Q.unop.hom.op σ =
        CanonicalForms.val.map a.unop.left.op
          ((frame t ht (f.restrict V.unop.hom.le)).symm x • CanonicalForms.val.map V.unop.hom.op σ)
      rw [CanonicalForms.val.map_smul, ← PresheafOfModules.map_comp_apply]
      have e := coordinate_restrict t ht (f.restrict V.unop.hom.le) a.unop.left.le x
      have ef : (f.restrict V.unop.hom.le).restrict a.unop.left.le = f.restrict Q.unop.hom.le := by
        exact frame_unique _ _ rfl rfl
      rw [ef] at e
      rw [e]
      rfl
  }, by
    intro V r x
    change (frame t ht (f.restrict V.hom.le)).symm ((show Γ(Surface,V.left) from r) • x) • CanonicalForms.val.map V.hom.op σ =
      (show Γ(Surface,V.left) from r) • ((frame t ht (f.restrict V.hom.le)).symm x • CanonicalForms.val.map V.hom.op σ)
    rw [map_smul, smul_eq_mul, mul_smul]⟩

theorem poleOfNumerator_app (f : FrameData W) (σ : CanonicalForms.val.obj (op W))
    (V : Over W) (x : Γ(curveIdeal t,V.left)) :
    (poleOfNumerator t ht f σ).val.app (op V) x =
      (frame t ht (f.restrict V.hom.le)).symm x • CanonicalForms.val.map V.hom.op σ := rfl

theorem poleOfNumerator_app_frame (f : FrameData W) (σ : CanonicalForms.val.obj (op W))
    (V : Over W) (r : Γ(Surface,V.left)) :
    (poleOfNumerator t ht f σ).val.app (op V) (frame t ht (f.restrict V.hom.le) r) =
      r • CanonicalForms.val.map V.hom.op σ := by
  rw [poleOfNumerator_app, LinearEquiv.symm_apply_apply]

/-- Restricting a pole restricts its frame and its actual numerator. -/
theorem poleOfNumerator_restrict (f : FrameData W) (σ : CanonicalForms.val.obj (op W))
    {V : Surface.Opens} (h : V ≤ W) :
    (PoleForms t).val.map (homOfLE h).op (poleOfNumerator t ht f σ) =
      poleOfNumerator t ht (f.restrict h) (CanonicalForms.val.map (homOfLE h).op σ) := by
  apply localLinearHom_ext Surface.sheaf (curveIdeal t) CanonicalForms
  intro Q x
  change (frame t ht (f.restrict (Q.hom.le.trans h))).symm x •
      CanonicalForms.val.map (Q.hom ≫ homOfLE h).op σ =
    (frame t ht ((f.restrict h).restrict Q.hom.le)).symm x •
      CanonicalForms.val.map Q.hom.op (CanonicalForms.val.map (homOfLE h).op σ)
  rw [← PresheafOfModules.map_comp_apply]
  rw [show (f.restrict h).restrict Q.hom.le = f.restrict (Q.hom.le.trans h) from
    frame_unique _ _ rfl rfl]
  rfl

/-- Sections of the pole sheaf agree if they agree on the local ideal
basis on each subopen. -/
theorem pole_ext (f : FrameData W) {H J : (PoleForms t).val.obj (op W)}
    (he : ∀ V : Over W, H.val.app (op V) (frame t ht (f.restrict V.hom.le) 1) =
      J.val.app (op V) (frame t ht (f.restrict V.hom.le) 1)) : H = J := by
  apply localLinearHom_ext Surface.sheaf (curveIdeal t) CanonicalForms
  intro V x
  let F := frame t ht (f.restrict V.hom.le)
  obtain ⟨r, rfl⟩ := F.surjective x
  have hs : F r = r • F 1 := by rw [← F.map_smul, smul_eq_mul, mul_one]
  rw [hs, H.property, J.property, he]

/-- A regular form embedded in the actual pole sheaf, evaluated in the
moving Cartier frame on an arbitrary subopen. -/
theorem regular_app_frame (f : FrameData W) (σ : CanonicalForms.val.obj (op W))
    (V : Over W) (r : Γ(Surface,V.left)) :
    ((idealRegularInclusion (curveToSurface t) CanonicalForms).val.app (op W) σ).val.app
        (op V) (frame t ht (f.restrict V.hom.le) r) =
      (r * sectionRows t f.chart V.left (V.hom.le.trans f.within) f.pivot.1) •
        CanonicalForms.val.map V.hom.op σ := by
  have he := kernelIdealSectionEquiv_coe (curveToSurface t) V.left
    (frame t ht (f.restrict V.hom.le) r)
  have hc := curveIdealFrame_coordinate t ht f.chart V.left (V.hom.le.trans f.within)
    f.pivot (f.restrict V.hom.le).pivotUnit (f.restrict V.hom.le).pivot_eq r
  exact congrArg (fun a : Γ(Surface,V.left) => a • CanonicalForms.val.map V.hom.op σ)
    (he.symm.trans hc)

theorem frame_apply (f : FrameData W) (r : Γ(Surface,W)) :
    frame t ht f r = r • curveGenerator t f := by
  change (evaluationToCurveIdeal t).app W
    (sourceFrame f.chart W f.within f.pivot f.pivotUnit f.pivot_eq r) = _
  rw [sourceFrame_apply, Scheme.Modules.Hom.app_smul]
  rfl

theorem frame_coordinate_change (j k : FrameData W) :
    (frame t ht j).symm (frame t ht k 1) = (divisorTransition j k : Γ(Surface,W)) := by
  apply (frame t ht j).injective
  rw [LinearEquiv.apply_symm_apply, frame_apply, one_smul, frame_apply,
    curveGenerator_transition t j k]

theorem frame_coordinate_change_restrict (j k : FrameData W) {V : Surface.Opens} (h : V ≤ W) :
    targetRes h ((frame t ht j).symm (frame t ht k 1)) =
      (frame t ht (j.restrict h)).symm (frame t ht (k.restrict h) 1) := by
  rw [frame_coordinate_change, frame_coordinate_change]
  exact congrArg Units.val (divisorTransition_restrict j k h)

theorem pole_ext_generator (f : FrameData W) {H J : (PoleForms t).val.obj (op W)}
    (he : localLinearHomEvaluate Surface.sheaf (curveIdeal t) CanonicalForms W H (frame t ht f 1) =
      localLinearHomEvaluate Surface.sheaf (curveIdeal t) CanonicalForms W J (frame t ht f 1)) :
    H = J := by
  apply pole_ext t ht f
  intro V
  let q : V ⟶ Over.mk (𝟙 W) := Over.homMk V.hom
  have hn (B : (PoleForms t).val.obj (op W)) :
      B.val.app (op V) (moduleRes (curveIdeal t) V.hom.le (frame t ht f 1)) =
        CanonicalForms.val.map V.hom.op
          (localLinearHomEvaluate Surface.sheaf (curveIdeal t) CanonicalForms W B (frame t ht f 1)) :=
    ConcreteCategory.congr_hom (B.val.naturality q.op) (frame t ht f 1)
  simpa only [frame_restrict, map_one] using
    ((hn H).trans ((congrArg (CanonicalForms.val.map V.hom.op) he).trans (hn J).symm))

theorem pole_change_frame (j k : FrameData W) (σ : CanonicalForms.val.obj (op W)) :
    poleOfNumerator t ht j σ = poleOfNumerator t ht k ((divisorTransition j k : Γ(Surface,W)) • σ) := by
  apply pole_ext t ht k
  intro V
  rw [poleOfNumerator_app, frame_coordinate_change, poleOfNumerator_app_frame, one_smul,
    CanonicalForms.val.map_smul]
  obtain he := congrArg Units.val (divisorTransition_restrict j k V.hom.le)
  change targetRes V.hom.le (divisorTransition j k : Γ(Surface,W)) =
    (divisorTransition (j.restrict V.hom.le) (k.restrict V.hom.le) : Γ(Surface,V.left)) at he
  rw [← he]
  rfl

/-- The map taking a numerator to its pole is additive on the actual sheaf. -/
def poleMap (f : FrameData W) : CanonicalForms.val.obj (op W) →+ (PoleForms t).val.obj (op W) where
  toFun := poleOfNumerator t ht f
  map_zero' := by
    apply pole_ext t ht f
    intro V
    change (poleOfNumerator t ht f 0).val.app (op V) _ = 0
    rw [poleOfNumerator_app_frame, map_zero, smul_zero]
  map_add' σ τ := by
    apply pole_ext t ht f
    intro V
    change (poleOfNumerator t ht f (σ+τ)).val.app (op V) _ =
      (poleOfNumerator t ht f σ).val.app (op V) _ + (poleOfNumerator t ht f τ).val.app (op V) _
    rw [poleOfNumerator_app_frame, poleOfNumerator_app_frame, poleOfNumerator_app_frame,
      map_add, smul_add]

theorem regular_eq_poleOfNumerator (f : FrameData W) (σ : CanonicalForms.val.obj (op W)) :
    (idealRegularInclusion (curveToSurface t) CanonicalForms).val.app (op W) σ =
      poleOfNumerator t ht f ((sectionRows t f.chart W f.within f.pivot.1) • σ) := by
  apply pole_ext t ht f
  intro V
  refine (regular_app_frame t ht f σ V 1).trans (Eq.trans ?_
    (poleOfNumerator_app_frame t ht f _ V 1).symm)
  rw [one_mul, one_smul, CanonicalForms.val.map_smul]
  exact congrArg (fun s : Γ(Surface,V.left) => s • CanonicalForms.val.map V.hom.op σ)
    (sectionRows_restrict t f.chart W V.left V.hom.le f.within f.pivot.1).symm

end CycleQ2LiteralMovingResiduePole
end

#print axioms CycleQ2LiteralMovingResiduePole.poleOfNumerator_restrict
#print axioms CycleQ2LiteralMovingResiduePole.pole_change_frame
#print axioms CycleQ2LiteralMovingResiduePole.regular_eq_poleOfNumerator
#print axioms CycleQ2LiteralMovingResiduePole.pole_ext_generator
