import Proposal.GeometricSeedSectionSheafEvaluation
import Proposal.GeometricFullSurfaceResidueCover

/-!
# The original section functional as a genuine global sheaf morphism

The already specified source is the global kernel sheaf of the original
chart ideals with their negative-fourth-power transition.  For every
original complex vector t, the original local evaluations agree on all
common subopens.  The actual structure-sheaf gluing property now constructs
a unique global morphism from this fixed source to O_D.

Its value on every subopen of every original chart is proved to be the
original evaluation, with all restriction and scalar maps retained.
No existence, compatibility, or gluing hypothesis is supplied by a caller.

Identifying the image with the actual closed-curve kernel, and proving the
local chart identifications of the descended source, remain separate.
This is not an affine residue-exactness theorem.  Source-only draft:
no Lean elaboration or kernel replay was run. Prepared for fqlx with
OpenAI ChatGPT assistance; see solution.md for attribution and status.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2SeedSectionSheafGlobal

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open CycleQ2SeedProjectiveImageCocycle CycleQ2SeedSectionSheaf
  CycleQ2SeedSectionSheafSections CycleQ2SeedSectionSheafEvaluation

theorem patch_cover : (⨆ i : Fin 3, Patch i) = ⊤ := by
  have h : Patch = CycleQ2FullSurfaceResidueCover.coordinateOpen := by
    funext i
    fin_cases i <;> rfl
  rw [h]
  exact CycleQ2FullSurfaceResidueCover.coordinateOpen_cover

def targetRes {V W : Surface.Opens} (h : W ≤ V) :
    Γ(Surface, V) →+* Γ(Surface, W) := (Surface.presheaf.map (homOfLE h).op).hom

def sourceRes {V W : Surface.Opens} (h : W ≤ V) :
    Γ(twistedIdeal, V) →+ Γ(twistedIdeal, W) :=
  (twistedIdeal.presheaf.map (homOfLE h).op).hom

theorem targetRes_comp {U V W : Surface.Opens} (hVU : V ≤ U) (hWV : W ≤ V)
    (a : Γ(Surface, U)) : targetRes hWV (targetRes hVU a) = targetRes (hWV.trans hVU) a := by
  change (Surface.presheaf.map (homOfLE hVU).op ≫
    Surface.presheaf.map (homOfLE hWV).op) a = _
  rw [← Functor.map_comp] <;> rfl

theorem sourceRes_comp {U V W : Surface.Opens} (hVU : V ≤ U) (hWV : W ≤ V)
    (s : Γ(twistedIdeal, U)) :
    sourceRes hWV (sourceRes hVU s) = sourceRes (hWV.trans hVU) s := by
  change (twistedIdeal.presheaf.map (homOfLE hVU).op ≫
    twistedIdeal.presheaf.map (homOfLE hWV).op) s = _
  rw [← Functor.map_comp] <;> rfl

theorem sourceRes_smul {V W : Surface.Opens} (h : W ≤ V)
    (a : Γ(Surface, V)) (s : Γ(twistedIdeal, V)) :
    sourceRes h (a • s) = targetRes h a • sourceRes h s :=
  twistedIdeal.map_smul (homOfLE h) a s

theorem cover_on (V : Surface.Opens) : V ≤ ⨆ i : Fin 3, V ⊓ Patch i := by
  rw [← inf_iSup_eq, patch_cover, inf_top_eq]

private theorem target_ext (V : Surface.Opens) (a b : Γ(Surface, V))
    (h : ∀ i : Fin 3,
      targetRes (show V ⊓ Patch i ≤ V from inf_le_left) a = targetRes inf_le_left b) :
    a = b :=
  Surface.sheaf.eq_of_locally_eq' (fun i : Fin 3 => V ⊓ Patch i) V
    (fun _ => homOfLE inf_le_left) (cover_on V) a b h

def localImage (t : Fin 3 → ℂ) (V : Surface.Opens)
    (s : Γ(twistedIdeal, V)) (i : Fin 3) : Γ(Surface, V ⊓ Patch i) :=
  evaluatedCoordinate t i (V ⊓ Patch i) inf_le_right (sourceRes inf_le_left s)

theorem localImage_compatible (t : Fin 3 → ℂ) (V : Surface.Opens)
    (s : Γ(twistedIdeal, V)) (i j : Fin 3) (W : Surface.Opens)
    (hi : W ≤ V ⊓ Patch i) (hj : W ≤ V ⊓ Patch j) :
    targetRes hi (localImage t V s i) = targetRes hj (localImage t V s j) := by
  unfold localImage
  change Surface.presheaf.map (homOfLE hi).op
      (evaluatedCoordinate t i (V ⊓ Patch i) inf_le_right (sourceRes inf_le_left s)) =
    Surface.presheaf.map (homOfLE hj).op
      (evaluatedCoordinate t j (V ⊓ Patch j) inf_le_right (sourceRes inf_le_left s))
  rw [evaluatedCoordinate_restrict, evaluatedCoordinate_restrict]
  change evaluatedCoordinate t i W (hi.trans inf_le_right)
      (sourceRes hi (sourceRes inf_le_left s)) =
    evaluatedCoordinate t j W (hj.trans inf_le_right)
      (sourceRes hj (sourceRes inf_le_left s))
  rw [sourceRes_comp, sourceRes_comp]
  exact evaluatedCoordinate_compatible t i j W _ _ _

theorem image_exists (t : Fin 3 → ℂ) (V : Surface.Opens)
    (s : Γ(twistedIdeal, V)) :
    ∃! a : Γ(Surface, V), ∀ i : Fin 3,
      targetRes (show V ⊓ Patch i ≤ V from inf_le_left) a = localImage t V s i := by
  apply Surface.sheaf.existsUnique_gluing' (fun i : Fin 3 => V ⊓ Patch i) V
    (fun _ => homOfLE inf_le_left) (cover_on V) (localImage t V s)
  intro i j
  exact localImage_compatible t V s i j _ inf_le_left inf_le_right

def gluedSection (t : Fin 3 → ℂ) (V : Surface.Opens)
    (s : Γ(twistedIdeal, V)) : Γ(Surface, V) :=
  Classical.choose (image_exists t V s)

theorem gluedSection_restrict (t : Fin 3 → ℂ) (V : Surface.Opens)
    (s : Γ(twistedIdeal, V)) (i : Fin 3) :
    targetRes (show V ⊓ Patch i ≤ V from inf_le_left) (gluedSection t V s) =
      localImage t V s i :=
  (Classical.choose_spec (image_exists t V s)).1 i

/-- Every restriction contained in an original chart has the original
functional value, not just restrictions to the chosen cover itself. -/
theorem gluedSection_restrict_patch (t : Fin 3 → ℂ) {V W : Surface.Opens}
    (hWV : W ≤ V) (i : Fin 3) (hi : W ≤ Patch i) (s : Γ(twistedIdeal, V)) :
    targetRes hWV (gluedSection t V s) =
      evaluatedCoordinate t i W hi (sourceRes hWV s) := by
  calc
    _ = targetRes (le_inf hWV hi)
        (targetRes (show V ⊓ Patch i ≤ V from inf_le_left) (gluedSection t V s)) := by
      rw [targetRes_comp]
    _ = targetRes (le_inf hWV hi) (localImage t V s i) := by
      rw [gluedSection_restrict]
    _ = _ := by
      unfold localImage
      change Surface.presheaf.map (homOfLE (le_inf hWV hi)).op
        (evaluatedCoordinate t i (V ⊓ Patch i) inf_le_right (sourceRes inf_le_left s)) = _
      rw [evaluatedCoordinate_restrict]
      change evaluatedCoordinate t i W hi
        (sourceRes (le_inf hWV hi) (sourceRes inf_le_left s)) = _
      rw [sourceRes_comp]

theorem gluedSection_naturality (t : Fin 3 → ℂ) {V W : Surface.Opens}
    (hWV : W ≤ V) (s : Γ(twistedIdeal, V)) :
    targetRes hWV (gluedSection t V s) = gluedSection t W (sourceRes hWV s) := by
  apply target_ext W
  intro i
  rw [targetRes_comp, gluedSection_restrict_patch t (inf_le_left.trans hWV) i inf_le_right,
    gluedSection_restrict]
  unfold localImage
  rw [sourceRes_comp]

theorem gluedSection_add (t : Fin 3 → ℂ) (V : Surface.Opens)
    (s r : Γ(twistedIdeal, V)) :
    gluedSection t V (s + r) = gluedSection t V s + gluedSection t V r := by
  apply target_ext V
  intro i
  simp only [gluedSection_restrict, map_add, localImage]

theorem gluedSection_smul (t : Fin 3 → ℂ) (V : Surface.Opens)
    (a : Γ(Surface, V)) (s : Γ(twistedIdeal, V)) :
    gluedSection t V (a • s) = a • gluedSection t V s := by
  apply target_ext V
  intro i
  change targetRes inf_le_left (gluedSection t V (a • s)) =
    targetRes inf_le_left (a * gluedSection t V s)
  rw [gluedSection_restrict, map_mul, gluedSection_restrict]
  unfold localImage
  rw [sourceRes_smul, map_smul] <;> rfl

/-- The global evaluation morphism from the independently specified
twisted original ideal into the original surface structure module. -/
def globalEvaluation (t : Fin 3 → ℂ) : twistedIdeal ⟶ structureModule Surface where
  val.app V := ModuleCat.ofHom
    { toFun := gluedSection t V.unop
      map_add' := gluedSection_add t V.unop
      map_smul' := gluedSection_smul t V.unop }
  val.naturality {V W} f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro s
    change gluedSection t W.unop (twistedIdeal.presheaf.map f s) =
      Surface.presheaf.map f (gluedSection t V.unop s)
    have hf : f = (homOfLE (leOfHom f.unop)).op := Subsingleton.elim _ _
    rw [hf]
    exact (gluedSection_naturality t (leOfHom f.unop) s).symm

/-- CLOSED SOURCE-LEVEL ENDPOINT: the genuine global morphism agrees
with the unchanged original functional on every original chart subopen. -/
theorem globalEvaluation_on_patch (t : Fin 3 → ℂ) (i : Fin 3)
    (V : Surface.Opens) (hi : V ≤ Patch i) (s : Γ(twistedIdeal, V)) :
    (globalEvaluation t).app V s = evaluatedCoordinate t i V hi s := by
  have h := gluedSection_restrict_patch t (le_refl V) i hi s
  simpa only [targetRes, sourceRes, homOfLE_refl, op_id, Functor.map_id,
    ConcreteCategory.id_apply] using h

/-- Uniqueness is with respect to the actual original local evaluations. -/
theorem globalEvaluation_unique (t : Fin 3 → ℂ)
    (f : twistedIdeal ⟶ structureModule Surface)
    (hf : ∀ (i : Fin 3) (V : Surface.Opens) (hi : V ≤ Patch i)
      (s : Γ(twistedIdeal, V)), f.app V s = evaluatedCoordinate t i V hi s) :
    f = globalEvaluation t := by
  apply Scheme.Modules.hom_ext
  intro V
  apply ConcreteCategory.hom_ext
  intro s
  apply target_ext V
  intro i
  have hn := ConcreteCategory.congr_hom
    (f.mapPresheaf.naturality (homOfLE (show V ⊓ Patch i ≤ V from inf_le_left)).op) s
  change f.app (V ⊓ Patch i) (sourceRes inf_le_left s) = targetRes inf_le_left (f.app V s) at hn
  change targetRes (show V ⊓ Patch i ≤ V from inf_le_left) (f.app V s) =
    targetRes inf_le_left (gluedSection t V s)
  rw [← hn, hf, gluedSection_restrict] <;> rfl

end CycleQ2SeedSectionSheafGlobal

end

#print axioms CycleQ2SeedSectionSheafGlobal.image_exists
#print axioms CycleQ2SeedSectionSheafGlobal.globalEvaluation
#print axioms CycleQ2SeedSectionSheafGlobal.globalEvaluation_on_patch
#print axioms CycleQ2SeedSectionSheafGlobal.globalEvaluation_unique
