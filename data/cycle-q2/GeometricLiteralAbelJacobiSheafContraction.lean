import Proposal.GeometricLiteralAbelJacobiSurfaceWedge
import Proposal.GeometricExteriorLocalFrames
import Proposal.GeometricLiteralNativeTangentEvaluation

/-!
# Interior multiplication of genuine surface two-form sections

A tangent section evaluates one-forms on every subopen. Interior multiplication
on presheaf exterior powers commutes with these restrictions and therefore
extends uniquely to the sheaf of two-forms on that open.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralAbelJacobiSheafContraction

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
  CycleQ2GeometricExteriorSheaf CycleQ2GeometricDifferentialSheaf
  CycleQ2GeometricIntrinsicNormal CycleQ2LocalSheafificationFrame
  CycleQ2GeometricExteriorLocalFrames CycleQ2LiteralNativeDifferentialSections
  CycleQ2LiteralNativeTangentEvaluation CycleQ2LiteralAbelJacobiSurfaceWedge

abbrev TwoForms := exteriorSheaf Surface.sheaf DifferentialSheaf.val 2
private abbrev raw := exteriorPresheaf Surface.sheaf.obj DifferentialSheaf.val 2
private abbrev present := toExteriorSheaf Surface.sheaf DifferentialSheaf.val 2

variable (U : Surface.Opens) (δ : tangentSheaf.val.obj (op U))

private abbrev presentation := @overPresentation (show TopCat from Surface)
  (ringSheaf Surface.sheaf) raw U TwoForms present

local instance presentationInjective :
    PresheafOfModules.IsLocallyInjective ((Opens.grothendieckTopology Surface).over U)
      (presentation U) :=
  @overPresentation_locallyInjective (show TopCat from Surface) (ringSheaf Surface.sheaf) raw U TwoForms
    present (exteriorPresentation_locallyInjective Surface.sheaf DifferentialSheaf.val 2)

local instance presentationSurjective :
    PresheafOfModules.IsLocallySurjective ((Opens.grothendieckTopology Surface).over U)
      (presentation U) :=
  @overPresentation_locallySurjective (show TopCat from Surface) (ringSheaf Surface.sheaf) raw U TwoForms
    present (exteriorPresentation_locallySurjective Surface.sheaf DifferentialSheaf.val 2)

/-- Evaluation of this tangent section on every object of the open's over-site. -/
def evaluateOn (V : Over U) : DifferentialSheaf.val.obj (op V.left) →ₗ[Γ(Surface,V.left)] Γ(Surface,V.left) where
  toFun := δ.val.app (op V)
  map_add' x y := (δ.val.app (op V)).hom.map_add x y
  map_smul' x y := δ.property V x y

set_option maxHeartbeats 400000 in
private def rawContract :
    overPresheaf (ringSheaf Surface.sheaf) raw U ⟶ (DifferentialSheaf.over U).val where
  app V := ModuleCat.ofHom (contract (R := Γ(Surface,V.unop.left)) (evaluateOn U δ V.unop))
  naturality {V W} f := by
    apply ConcreteCategory.hom_ext
    intro x
    change contract (evaluateOn U δ W.unop)
      (exteriorMap (Surface.presheaf.map f.unop.left.op).hom
        (DifferentialSheaf.val.restrictₛₗ f.unop.left.op) 2 x) =
      DifferentialSheaf.val.map f.unop.left.op (contract (evaluateOn U δ V.unop) x)
    apply contract_natural (Surface.presheaf.map f.unop.left.op).hom
      (DifferentialSheaf.val.restrictₛₗ f.unop.left.op)
      (evaluateOn U δ V.unop) (evaluateOn U δ W.unop)
    intro z
    exact ConcreteCategory.congr_hom (δ.val.naturality f) z

/-- The unique extension of ordinary interior multiplication to the sheaf of two-forms. -/
def contractionOver : TwoForms.over U ⟶ DifferentialSheaf.over U where
  val := (PresheafOfModules.homEquivOfIsLocallyBijective
    (presentation U) (DifferentialSheaf.over U).isSheaf).symm (rawContract U δ)

theorem contractionOver_exterior (V : Over U)
    (x : ⋀[Γ(Surface,V.left)]^2 (DifferentialSheaf.val.obj (op V.left))) :
    (contractionOver U δ).val.app (op V) (exteriorSection Surface.sheaf DifferentialSheaf.val 2 V.left x) =
      contract (evaluateOn U δ V) x := by
  have h := (PresheafOfModules.homEquivOfIsLocallyBijective
    (presentation U) (DifferentialSheaf.over U).isSheaf).apply_symm_apply (rawContract U δ)
  exact congrArg (fun f : overPresheaf (ringSheaf Surface.sheaf) raw U ⟶ (DifferentialSheaf.over U).val =>
    f.app (op V) x) h

/-- The one-form obtained by contracting a genuine two-form with an actual tangent section. -/
def interior : TwoForms.val.obj (op U) →ₗ[Γ(Surface,U)] DifferentialSheaf.val.obj (op U) :=
  ((contractionOver U δ).val.app (op (Over.mk (𝟙 U)))).hom

theorem interior_exterior (x : ⋀[Γ(Surface,U)]^2 (DifferentialSheaf.val.obj (op U))) :
    interior U δ (exteriorSection Surface.sheaf DifferentialSheaf.val 2 U x) =
      contract (evaluateTangent U δ) x :=
  contractionOver_exterior U δ (Over.mk (𝟙 U)) x

private def localInterior : LocalLinearHom Surface.sheaf TwoForms DifferentialSheaf U :=
  (localLinearHomEquiv Surface.sheaf TwoForms DifferentialSheaf U).symm (contractionOver U δ)

private theorem localInterior_ext
    (g k : LocalLinearHom Surface.sheaf TwoForms DifferentialSheaf U)
    (he : ∀ (V : Over U) (x : ⋀[Γ(Surface,V.left)]^2 (DifferentialSheaf.val.obj (op V.left))),
      g.val.app (op V) (exteriorSection Surface.sheaf DifferentialSheaf.val 2 V.left x) =
      k.val.app (op V) (exteriorSection Surface.sheaf DifferentialSheaf.val 2 V.left x)) :
    g = k := by
  apply (localLinearHomEquiv Surface.sheaf TwoForms DifferentialSheaf U).injective
  apply SheafOfModules.hom_ext
  apply (PresheafOfModules.homEquivOfIsLocallyBijective
    (presentation U) (DifferentialSheaf.over U).isSheaf).injective
  apply PresheafOfModules.hom_ext
  intro V
  apply ConcreteCategory.hom_ext
  exact he V.unop

private theorem localInterior_restrict {V : Surface.Opens} (f : V ⟶ U) :
    restrictLocalLinearHom Surface.sheaf TwoForms DifferentialSheaf f.op (localInterior U δ) =
      localInterior V (tangentSheaf.val.map f.op δ) := by
  apply localInterior_ext
  intro W x
  let W' : Over U := Over.mk (W.hom ≫ f)
  change (contractionOver U δ).val.app (op W') (exteriorSection Surface.sheaf DifferentialSheaf.val 2 W.left x) =
    (contractionOver V (tangentSheaf.val.map f.op δ)).val.app (op W)
      (exteriorSection Surface.sheaf DifferentialSheaf.val 2 W.left x)
  exact (contractionOver_exterior U δ W' x).trans
    (contractionOver_exterior V (tangentSheaf.val.map f.op δ) W x).symm

theorem interior_restrict {V : Surface.Opens} (h : V ≤ U) (ω : TwoForms.val.obj (op U)) :
    DifferentialSheaf.val.map (homOfLE h).op (interior U δ ω) =
      interior V (tangentSheaf.val.map (homOfLE h).op δ) (TwoForms.val.map (homOfLE h).op ω) := by
  have hn := localLinearHomEvaluate_restrict Surface.sheaf TwoForms DifferentialSheaf
    (homOfLE h) (localInterior U δ) ω
  rw [localInterior_restrict] at hn
  exact hn.symm

private theorem contract_add {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (v u : M →ₗ[R] R) (w : ⋀[R]^2 M) :
    contract (v + u) w = contract v w + contract u w := by
  have hw : w ∈ Submodule.span R (Set.range (exteriorPower.ιMulti R 2)) := by
    rw [exteriorPower.ιMulti_span]
    trivial
  induction hw using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      simp only [contract, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
      change (v (a 0) + u (a 0)) • a 1 - (v (a 1) + u (a 1)) • a 0 = _
      simp only [add_smul]
      change _ = (v (a 0) • a 1 - v (a 1) • a 0) + (u (a 0) • a 1 - u (a 1) • a 0)
      abel
  | zero => simp only [map_zero, add_zero]
  | add x y _ _ hx hy =>
      simp only [map_add, hx, hy]
      abel
  | smul r x _ hx => simp only [map_smul, hx, smul_add]

theorem interior_add (η : tangentSheaf.val.obj (op U)) (ω : TwoForms.val.obj (op U)) :
    interior U (δ + η) ω = interior U δ ω + interior U η ω := by
  have h : localInterior U (δ + η) = localInterior U δ + localInterior U η := by
    apply localInterior_ext
    intro W x
    change (contractionOver U (δ + η)).val.app (op W) (exteriorSection _ _ 2 W.left x) =
      (contractionOver U δ).val.app (op W) (exteriorSection _ _ 2 W.left x) +
      (contractionOver U η).val.app (op W) (exteriorSection _ _ 2 W.left x)
    have hδ : evaluateOn U (δ + η) W = evaluateOn U δ W + evaluateOn U η W := by
      exact LinearMap.ext fun _ => rfl
    exact (contractionOver_exterior U (δ + η) W x).trans
      (((congrArg (fun v => contract v x) hδ).trans (contract_add _ _ x)).trans
        (congrArg₂ (· + ·) (contractionOver_exterior U δ W x).symm
          (contractionOver_exterior U η W x).symm))
  exact congrArg (fun d : LocalLinearHom Surface.sheaf TwoForms DifferentialSheaf U =>
    d.val.app (op (Over.mk (𝟙 U))) ω) h

end CycleQ2LiteralAbelJacobiSheafContraction

end

#print axioms CycleQ2LiteralAbelJacobiSheafContraction.interior_exterior
#print axioms CycleQ2LiteralAbelJacobiSheafContraction.interior_restrict
#print axioms CycleQ2LiteralAbelJacobiSheafContraction.interior_add
