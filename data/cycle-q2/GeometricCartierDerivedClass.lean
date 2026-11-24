import Proposal.GeometricSheafHZero
import Proposal.GeometricSheafLocalIso
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Sites.MayerVietorisSquare
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.Algebra.Homology.ShortComplex.Ab
import Mathlib.GroupTheory.QuotientGroup.Basic
import Proposal.GeometricCartierCechNonboundary
import Proposal.GeometricCartierCech
import Proposal.GeometricProjectiveCharts
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

section

/-!
# Finite Cech contractions for injective additive sheaves

The restriction maps of an injective sheaf are surjective by extension
along the free abelian sheaf maps of open inclusions. Combined with actual
sheaf gluing, this supplies finite Cech primitives. No local cohomology
vanishing or projective comparison is assumed.
-/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2InjectiveCech

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open CycleQ2GeometricSheafLocalIso CycleQ2GeometricConeCech.HZero

variable {X : TopCat.{0}}

abbrev AbSheaf (X : TopCat.{0}) :=
  Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}

abbrev Sections (F : AbSheaf X) (U : Opens X) := F.obj.obj (op U)

def freeOpen (U : Opens X) : AbSheaf X :=
  (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat).obj
    (yoneda.obj U ⋙ AddCommGrpCat.free)

def freeOpenMap {U V : Opens X} (h : U ≤ V) : freeOpen U ⟶ freeOpen V :=
  (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat).map
    (Functor.whiskerRight (yoneda.map (homOfLE h)) AddCommGrpCat.free)

instance freeOpenMap_mono {U V : Opens X} (h : U ≤ V) : Mono (freeOpenMap h) := by
  have : Mono (yoneda.map (homOfLE h)) := inferInstance
  have : Mono (Functor.whiskerRight (yoneda.map (homOfLE h)) AddCommGrpCat.free) :=
    inferInstance
  dsimp [freeOpenMap]
  infer_instance

def freeOpenSections (F : AbSheaf X) (U : Opens X) :
    (freeOpen U ⟶ F) ≃+ Sections F U :=
  (((sheafificationAdjunction (Opens.grothendieckTopology X) AddCommGrpCat).homAddEquiv
    (yoneda.obj U ⋙ AddCommGrpCat.free) F).trans
      (freeYonedaSections F.obj U))

theorem freeOpenSections_naturality (F : AbSheaf X) {U V : Opens X} (h : U ≤ V)
    (f : freeOpen V ⟶ F) :
    freeOpenSections F U (freeOpenMap h ≫ f) =
      res F h (freeOpenSections F V f) := by
  change freeYonedaSections F.obj U
    (((sheafificationAdjunction (Opens.grothendieckTopology X) AddCommGrpCat).homEquiv
      _ F) (freeOpenMap h ≫ f)) = _
  dsimp only [freeOpenMap]
  rw [(sheafificationAdjunction (Opens.grothendieckTopology X)
    AddCommGrpCat).homEquiv_naturality_left]
  exact freeYonedaSections_precomp F.obj (homOfLE h) _

/-- Every actual restriction map of an injective additive sheaf is surjective. -/
theorem injective_restriction_surjective (F : AbSheaf X) [Injective F]
    {U V : Opens X} (h : U ≤ V) : Function.Surjective (res F h) := by
  intro s
  let f : freeOpen U ⟶ F := (freeOpenSections F U).symm s
  refine ⟨freeOpenSections F V (Injective.factorThru f (freeOpenMap h)), ?_⟩
  rw [← freeOpenSections_naturality, Injective.comp_factorThru]
  exact (freeOpenSections F U).apply_symm_apply s

/-- A compatible family on subopens extends to any containing open for an
injective sheaf. The compatibility is stated on all common subopens. -/
theorem extend_family (F : AbSheaf X) [Injective F] {ι : Type}
    (U : ι → Opens X) (V : Opens X) (hUV : ∀ i, U i ≤ V)
    (s : ∀ i, Sections F (U i))
    (hs : ∀ i j (W : Opens X) (hi : W ≤ U i) (hj : W ≤ U j),
      res F hi (s i) = res F hj (s j)) :
    ∃ t : Sections F V, ∀ i, res F (hUV i) t = s i := by
  have hc : TopCat.Presheaf.IsCompatible F.obj U s := by
    intro i j
    exact hs i j (U i ⊓ U j) inf_le_left inf_le_right
  obtain ⟨g, hg, -⟩ := (show TopCat.Sheaf AddCommGrpCat X from F).existsUnique_gluing U s hc
  obtain ⟨t, ht⟩ := injective_restriction_surjective F (iSup_le hUV) g
  refine ⟨t, fun i => ?_⟩
  have hh := congrArg (res F (le_iSup U i)) ht
  rw [res_comp] at hh
  exact hh.trans (hg i)

theorem extend_pair (F : AbSheaf X) [Injective F]
    (O U V : Opens X) (hU : U ≤ O) (hV : V ≤ O)
    (u : Sections F U) (v : Sections F V)
    (hc : ∀ (W : Opens X) (hWU : W ≤ U) (hWV : W ≤ V),
      res F hWU u = res F hWV v) :
    ∃ t : Sections F O, res F hU t = u ∧ res F hV t = v := by
  obtain ⟨g, hg, -⟩ := existsUnique_pair F (U ⊔ V) U V le_sup_left le_sup_right
    le_rfl u v hc
  obtain ⟨t, ht⟩ := injective_restriction_surjective F (sup_le hU hV) g
  refine ⟨t, ?_, ?_⟩
  · have hh := congrArg (res F (show U ≤ U ⊔ V from le_sup_left)) ht
    rw [res_comp] at hh
    exact hh.trans hg.1
  · have hh := congrArg (res F (show V ≤ U ⊔ V from le_sup_right)) ht
    rw [res_comp] at hh
    exact hh.trans hg.2

theorem extend_three (F : AbSheaf X) [Injective F]
    (O U V W : Opens X) (hU : U ≤ O) (hV : V ≤ O) (hW : W ≤ O)
    (u : Sections F U) (v : Sections F V) (w : Sections F W)
    (hUV : ∀ (P : Opens X) (hPU : P ≤ U) (hPV : P ≤ V),
      res F hPU u = res F hPV v)
    (hUW : ∀ (P : Opens X) (hPU : P ≤ U) (hPW : P ≤ W),
      res F hPU u = res F hPW w)
    (hVW : ∀ (P : Opens X) (hPV : P ≤ V) (hPW : P ≤ W),
      res F hPV v = res F hPW w) :
    ∃ t : Sections F O, res F hU t = u ∧ res F hV t = v ∧ res F hW t = w := by
  let A : Fin 3 → Opens X := ![U, V, W]
  let a : ∀ i, Sections F (A i) :=
    Fin.cases u (Fin.cases v (Fin.cases w (fun i => Fin.elim0 i)))
  have hA : ∀ i, A i ≤ O := by
    intro i
    fin_cases i
    · exact hU
    · exact hV
    · exact hW
  obtain ⟨t, ht⟩ := extend_family F A O hA a (by
    intro i j P hi hj
    fin_cases i <;> fin_cases j
    · rfl
    · exact hUV P hi hj
    · exact hUW P hi hj
    · exact (hUV P hj hi).symm
    · rfl
    · exact hVW P hi hj
    · exact (hUW P hj hi).symm
    · exact (hVW P hj hi).symm
    · rfl)
  exact ⟨t, ht 0, ht 1, ht 2⟩

/-- An injective additive sheaf has no degree-one Cech obstruction on four
opens. The vertex-zero primitive can be chosen to be zero. -/
theorem four_one_cocycle_has_primitive (F : AbSheaf X) [Injective F]
    (U₀ U₁ U₂ U₃ : Opens X)
    (c01 : Sections F (U₀ ⊓ U₁)) (c02 : Sections F (U₀ ⊓ U₂))
    (c03 : Sections F (U₀ ⊓ U₃)) (c12 : Sections F (U₁ ⊓ U₂))
    (c13 : Sections F (U₁ ⊓ U₃)) (c23 : Sections F (U₂ ⊓ U₃))
    (h012 : ∀ (W : Opens X) (h₀ : W ≤ U₀) (h₁ : W ≤ U₁) (h₂ : W ≤ U₂),
      res F (le_inf h₀ h₂) c02 =
        res F (le_inf h₀ h₁) c01 + res F (le_inf h₁ h₂) c12)
    (h013 : ∀ (W : Opens X) (h₀ : W ≤ U₀) (h₁ : W ≤ U₁) (h₃ : W ≤ U₃),
      res F (le_inf h₀ h₃) c03 =
        res F (le_inf h₀ h₁) c01 + res F (le_inf h₁ h₃) c13)
    (h023 : ∀ (W : Opens X) (h₀ : W ≤ U₀) (h₂ : W ≤ U₂) (h₃ : W ≤ U₃),
      res F (le_inf h₀ h₃) c03 =
        res F (le_inf h₀ h₂) c02 + res F (le_inf h₂ h₃) c23)
    (h123 : ∀ (W : Opens X) (h₁ : W ≤ U₁) (h₂ : W ≤ U₂) (h₃ : W ≤ U₃),
      res F (le_inf h₁ h₃) c13 =
        res F (le_inf h₁ h₂) c12 + res F (le_inf h₂ h₃) c23) :
    ∃ (q1 : Sections F U₁) (q2 : Sections F U₂) (q3 : Sections F U₃),
      res F inf_le_right q1 = c01 ∧ res F inf_le_right q2 = c02 ∧
      res F inf_le_right q3 = c03 ∧
      res F inf_le_right q2 - res F inf_le_left q1 = c12 ∧
      res F inf_le_right q3 - res F inf_le_left q1 = c13 ∧
      res F inf_le_right q3 - res F inf_le_left q2 = c23 := by
  obtain ⟨q1, hq1⟩ := injective_restriction_surjective F
    (show U₀ ⊓ U₁ ≤ U₁ from inf_le_right) c01
  obtain ⟨q2, hq20, hq21⟩ := extend_pair F U₂ (U₀ ⊓ U₂) (U₁ ⊓ U₂)
    inf_le_right inf_le_right c02 (c12 + res F inf_le_left q1) (by
      intro W hW0 hW1
      have h₀ : W ≤ U₀ := hW0.trans inf_le_left
      have h₁ : W ≤ U₁ := hW1.trans inf_le_left
      have h₂ : W ≤ U₂ := hW0.trans inf_le_right
      have hq1' : res F h₁ q1 = res F (le_inf h₀ h₁) c01 := by
        rw [← hq1, res_comp]
      rw [map_add, res_comp, hq1', add_comm]
      exact h012 W h₀ h₁ h₂)
  obtain ⟨q3, hq30, hq31, hq32⟩ := extend_three F U₃
    (U₀ ⊓ U₃) (U₁ ⊓ U₃) (U₂ ⊓ U₃) inf_le_right inf_le_right inf_le_right
    c03 (c13 + res F inf_le_left q1) (c23 + res F inf_le_left q2)
    (by
      intro W hW0 hW1
      have h₀ : W ≤ U₀ := hW0.trans inf_le_left
      have h₁ : W ≤ U₁ := hW1.trans inf_le_left
      have h₃ : W ≤ U₃ := hW0.trans inf_le_right
      have hq1' : res F h₁ q1 = res F (le_inf h₀ h₁) c01 := by
        rw [← hq1, res_comp]
      rw [map_add, res_comp, hq1', add_comm]
      exact h013 W h₀ h₁ h₃)
    (by
      intro W hW0 hW2
      have h₀ : W ≤ U₀ := hW0.trans inf_le_left
      have h₂ : W ≤ U₂ := hW2.trans inf_le_left
      have h₃ : W ≤ U₃ := hW0.trans inf_le_right
      have hq2' : res F h₂ q2 = res F (le_inf h₀ h₂) c02 := by
        rw [← hq20, res_comp]
      rw [map_add, res_comp, hq2', add_comm]
      exact h023 W h₀ h₂ h₃)
    (by
      intro W hW1 hW2
      have h₁ : W ≤ U₁ := hW1.trans inf_le_left
      have h₂ : W ≤ U₂ := hW2.trans inf_le_left
      have h₃ : W ≤ U₃ := hW1.trans inf_le_right
      have hq2' : res F h₂ q2 =
          res F (le_inf h₁ h₂) c12 + res F h₁ q1 := by
        have hh := congrArg (res F (le_inf h₁ h₂)) hq21
        simpa only [res_comp, map_add] using hh
      rw [map_add, map_add, res_comp, res_comp, hq2', h123 W h₁ h₂ h₃]
      abel)
  refine ⟨q1, q2, q3, hq1, hq20, hq30, ?_, ?_, ?_⟩
  · rw [hq21, add_sub_cancel_right]
  · rw [hq31, add_sub_cancel_right]
  · rw [hq32, add_sub_cancel_right]

/-- An injective additive sheaf has no degree-two Cech obstruction on four
opens. The three edges out of vertex zero can all be chosen to be zero;
the returned three sections are the remaining edges. -/
theorem four_two_cocycle_has_primitive (F : AbSheaf X) [Injective F]
    (U₀ U₁ U₂ U₃ : Opens X)
    (c012 : Sections F ((U₀ ⊓ U₁) ⊓ U₂))
    (c013 : Sections F ((U₀ ⊓ U₁) ⊓ U₃))
    (c023 : Sections F ((U₀ ⊓ U₂) ⊓ U₃))
    (c123 : Sections F ((U₁ ⊓ U₂) ⊓ U₃))
    (hc : ∀ (W : Opens X) (h₀ : W ≤ U₀) (h₁ : W ≤ U₁)
      (h₂ : W ≤ U₂) (h₃ : W ≤ U₃),
      res F (le_inf (le_inf h₁ h₂) h₃) c123 -
        res F (le_inf (le_inf h₀ h₂) h₃) c023 +
        res F (le_inf (le_inf h₀ h₁) h₃) c013 -
        res F (le_inf (le_inf h₀ h₁) h₂) c012 = 0) :
    ∃ (b12 : Sections F (U₁ ⊓ U₂))
      (b13 : Sections F (U₁ ⊓ U₃)) (b23 : Sections F (U₂ ⊓ U₃)),
      res F (inf_le_inf inf_le_right le_rfl) b12 = c012 ∧
      res F (inf_le_inf inf_le_right le_rfl) b13 = c013 ∧
      res F (inf_le_inf inf_le_right le_rfl) b23 = c023 ∧
      res F (inf_le_inf inf_le_right le_rfl) b23 -
        res F (inf_le_inf inf_le_left le_rfl) b13 +
        res F inf_le_left b12 = c123 := by
  obtain ⟨b12, h12⟩ := injective_restriction_surjective F
    (show (U₀ ⊓ U₁) ⊓ U₂ ≤ U₁ ⊓ U₂ from inf_le_inf inf_le_right le_rfl) c012
  obtain ⟨b13, h13⟩ := injective_restriction_surjective F
    (show (U₀ ⊓ U₁) ⊓ U₃ ≤ U₁ ⊓ U₃ from inf_le_inf inf_le_right le_rfl) c013
  obtain ⟨b23, h23⟩ := injective_restriction_surjective F
    (show (U₀ ⊓ U₂) ⊓ U₃ ≤ U₂ ⊓ U₃ from inf_le_inf inf_le_right le_rfl) c023
  let r123 : Sections F ((U₁ ⊓ U₂) ⊓ U₃) :=
    c123 - res F (inf_le_inf inf_le_right le_rfl) b23 +
      res F (inf_le_inf inf_le_left le_rfl) b13 - res F inf_le_left b12
  obtain ⟨t23, ht0, ht1⟩ := extend_pair F (U₂ ⊓ U₃)
    ((U₀ ⊓ U₂) ⊓ U₃) ((U₁ ⊓ U₂) ⊓ U₃)
    (inf_le_inf inf_le_right le_rfl) (inf_le_inf inf_le_right le_rfl)
    0 r123 (by
      intro W hW0 hW1
      have h₀ : W ≤ U₀ := hW0.trans (inf_le_left.trans inf_le_left)
      have h₁ : W ≤ U₁ := hW1.trans (inf_le_left.trans inf_le_left)
      have h₂ : W ≤ U₂ := hW0.trans (inf_le_left.trans inf_le_right)
      have h₃ : W ≤ U₃ := hW0.trans inf_le_right
      have h12' : res F (le_inf h₁ h₂) b12 =
          res F (le_inf (le_inf h₀ h₁) h₂) c012 := by
        rw [← h12, res_comp]
      have h13' : res F (le_inf h₁ h₃) b13 =
          res F (le_inf (le_inf h₀ h₁) h₃) c013 := by
        rw [← h13, res_comp]
      have h23' : res F (le_inf h₂ h₃) b23 =
          res F (le_inf (le_inf h₀ h₂) h₃) c023 := by
        rw [← h23, res_comp]
      simp only [map_zero, r123, map_sub, map_add, res_comp]
      rw [h12', h13', h23']
      exact (hc W h₀ h₁ h₂ h₃).symm)
  refine ⟨b12, b13, b23 + t23, h12, h13, ?_, ?_⟩
  · rw [map_add, h23, ht0, add_zero]
  · rw [map_add, ht1]
    dsimp only [r123]
    abel

#print axioms injective_restriction_surjective
#print axioms extend_family
#print axioms extend_pair
#print axioms extend_three
#print axioms four_one_cocycle_has_primitive
#print axioms four_two_cocycle_has_primitive

end CycleQ2InjectiveCech
end

end


section

/-!
# Degree-two four-open Cech classes in actual derived cohomology

Two injective presentations and the proved finite contractions define a
class in the actual Ext-based sheaf cohomology group. Local degree-one
vanishing is used only to lift the four vertex sections in the zero-class
criterion.
-/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2CechTwoToDerived
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite TopologicalSpace
open CycleQ2InjectiveCech CycleQ2GeometricSheafLocalIso
open CycleQ2GeometricConeCech.HZero

variable {X : TopCat.{0}}
local instance sheafHasExt : HasExt.{1} (AbSheaf X) := HasExt.standard _

abbrev Zero (F : AbSheaf X) (U : Fin 4 → Opens X) := ∀ i, Sections F (U i)
abbrev One (F : AbSheaf X) (U : Fin 4 → Opens X) :=
  Sections F (U 0 ⊓ U 1) × Sections F (U 0 ⊓ U 2) × Sections F (U 0 ⊓ U 3) ×
    Sections F (U 1 ⊓ U 2) × Sections F (U 1 ⊓ U 3) × Sections F (U 2 ⊓ U 3)
abbrev Two (F : AbSheaf X) (U : Fin 4 → Opens X) :=
  Sections F ((U 0 ⊓ U 1) ⊓ U 2) × Sections F ((U 0 ⊓ U 1) ⊓ U 3) ×
    Sections F ((U 0 ⊓ U 2) ⊓ U 3) × Sections F ((U 1 ⊓ U 2) ⊓ U 3)
abbrev Three (F : AbSheaf X) (U : Fin 4 → Opens X) :=
  Sections F (((U 0 ⊓ U 1) ⊓ U 2) ⊓ U 3)

variable (F : AbSheaf X) (U : Fin 4 → Opens X)

def d0 (q : Zero F U) : One F U :=
  ⟨res F inf_le_right (q 1) - res F inf_le_left (q 0),
   res F inf_le_right (q 2) - res F inf_le_left (q 0),
   res F inf_le_right (q 3) - res F inf_le_left (q 0),
   res F inf_le_right (q 2) - res F inf_le_left (q 1),
   res F inf_le_right (q 3) - res F inf_le_left (q 1),
   res F inf_le_right (q 3) - res F inf_le_left (q 2)⟩

def d1 (c : One F U) : Two F U :=
  ⟨res F (inf_le_inf inf_le_right le_rfl) c.2.2.2.1 -
      res F (inf_le_inf inf_le_left le_rfl) c.2.1 + res F inf_le_left c.1,
   res F (inf_le_inf inf_le_right le_rfl) c.2.2.2.2.1 -
      res F (inf_le_inf inf_le_left le_rfl) c.2.2.1 + res F inf_le_left c.1,
   res F (inf_le_inf inf_le_right le_rfl) c.2.2.2.2.2 -
      res F (inf_le_inf inf_le_left le_rfl) c.2.2.1 + res F inf_le_left c.2.1,
   res F (inf_le_inf inf_le_right le_rfl) c.2.2.2.2.2 -
      res F (inf_le_inf inf_le_left le_rfl) c.2.2.2.2.1 + res F inf_le_left c.2.2.2.1⟩

def d2 (c : Two F U) : Three F U :=
  res F (inf_le_inf (inf_le_inf inf_le_right le_rfl) le_rfl) c.2.2.2 -
    res F (inf_le_inf (inf_le_inf inf_le_left le_rfl) le_rfl) c.2.2.1 +
    res F (inf_le_inf inf_le_left le_rfl) c.2.1 - res F inf_le_left c.1

@[simp] theorem d1_d0 (q : Zero F U) : d1 F U (d0 F U q) = 0 := by
  apply Prod.ext <;> try apply Prod.ext <;> try apply Prod.ext
  all_goals simp only [d1, d0, map_sub, res_comp, Prod.fst_zero, Prod.snd_zero]
  all_goals abel

@[simp] theorem d2_d1 (c : One F U) : d2 F U (d1 F U c) = 0 := by
  simp only [d2, d1, map_sub, map_add, res_comp]
  abel

theorem d0_sub (a b : Zero F U) : d0 F U (a - b) = d0 F U a - d0 F U b := by
  apply Prod.ext <;> try apply Prod.ext <;> try apply Prod.ext <;> try apply Prod.ext <;>
    try apply Prod.ext
  all_goals simp only [d0, Pi.sub_apply, map_sub, Prod.fst_sub, Prod.snd_sub]
  all_goals abel

theorem d1_sub (a b : One F U) : d1 F U (a - b) = d1 F U a - d1 F U b := by
  apply Prod.ext <;> try apply Prod.ext <;> try apply Prod.ext
  all_goals simp only [d1, map_sub, Prod.fst_sub, Prod.snd_sub]
  all_goals abel

variable {F} {G H : AbSheaf X}

def app (f : F ⟶ G) (V : Opens X) : Sections F V →+ Sections G V :=
  (f.hom.app (op V)).hom

theorem app_res (f : F ⟶ G) {V W : Opens X} (h : W ≤ V) (x : Sections F V) :
    app f W (res F h x) = res G h (app f V x) := by
  change (F.obj.map (homOfLE h).op ≫ f.hom.app (op W)) x = _
  rw [f.hom.naturality]
  rfl

@[simp] theorem app_comp (f : F ⟶ G) (g : G ⟶ H) (V : Opens X) (x : Sections F V) :
    app g V (app f V x) = app (f ≫ g) V x := rfl

@[simp] theorem app_zero (V : Opens X) (x : Sections F V) :
    app (0 : F ⟶ G) V x = 0 := rfl

theorem app_injective (f : F ⟶ G) [Mono f] (V : Opens X) :
    Function.Injective (app f V) := by
  exact (AddCommGrpCat.mono_iff_injective (f.hom.app (op V))).mp inferInstance

def mapZero (f : F ⟶ G) (q : Zero F U) : Zero G U := fun i => app f (U i) (q i)
def mapOne (f : F ⟶ G) (c : One F U) : One G U :=
  ⟨app f _ c.1, app f _ c.2.1, app f _ c.2.2.1,
   app f _ c.2.2.2.1, app f _ c.2.2.2.2.1, app f _ c.2.2.2.2.2⟩
def mapTwo (f : F ⟶ G) (c : Two F U) : Two G U :=
  ⟨app f _ c.1, app f _ c.2.1, app f _ c.2.2.1, app f _ c.2.2.2⟩

theorem mapOne_d0 (f : F ⟶ G) (q : Zero F U) :
    mapOne U f (d0 F U q) = d0 G U (mapZero U f q) := by
  simp only [mapOne, mapZero, d0, map_sub, app_res]

theorem mapTwo_d1 (f : F ⟶ G) (c : One F U) :
    mapTwo U f (d1 F U c) = d1 G U (mapOne U f c) := by
  simp only [mapTwo, mapOne, d1, map_sub, map_add, app_res]

theorem mapThree_d2 (f : F ⟶ G) (c : Two F U) :
    app f _ (d2 F U c) = d2 G U (mapTwo U f c) := by
  simp only [mapTwo, d2, map_sub, map_add, app_res]

theorem mapOne_sub (f : F ⟶ G) (a b : One F U) :
    mapOne U f (a - b) = mapOne U f a - mapOne U f b := by
  simp only [mapOne, Prod.fst_sub, Prod.snd_sub, map_sub]
  rfl

theorem mapTwo_sub (f : F ⟶ G) (a b : Two F U) :
    mapTwo U f (a - b) = mapTwo U f a - mapTwo U f b := by
  simp only [mapTwo, Prod.fst_sub, Prod.snd_sub, map_sub]
  rfl

@[simp] theorem mapOne_zero (f : F ⟶ G) : mapOne U f 0 = 0 := by
  simp only [mapOne, Prod.fst_zero, Prod.snd_zero, map_zero, Prod.mk_zero_zero]
@[simp] theorem mapTwo_zero (f : F ⟶ G) : mapTwo U f 0 = 0 := by
  simp only [mapTwo, Prod.fst_zero, Prod.snd_zero, map_zero, Prod.mk_zero_zero]

@[simp] theorem mapOne_comp (f : F ⟶ G) (g : G ⟶ H) (c : One F U) :
    mapOne U g (mapOne U f c) = mapOne U (f ≫ g) c := rfl
@[simp] theorem mapTwo_comp (f : F ⟶ G) (g : G ⟶ H) (c : Two F U) :
    mapTwo U g (mapTwo U f c) = mapTwo U (f ≫ g) c := rfl

@[simp] theorem mapOne_zeroHom (c : One F U) : mapOne U (0 : F ⟶ G) c = 0 := rfl
@[simp] theorem mapTwo_zeroHom (c : Two F U) : mapTwo U (0 : F ⟶ G) c = 0 := rfl

theorem mapTwo_injective (f : F ⟶ G) [Mono f] : Function.Injective (mapTwo U f) := by
  rintro ⟨a,b,c,d⟩ ⟨a',b',c',d'⟩ h
  simp only [mapTwo, Prod.mk.injEq] at h ⊢
  exact ⟨app_injective f _ h.1, app_injective f _ h.2.1,
    app_injective f _ h.2.2.1, app_injective f _ h.2.2.2⟩

private theorem cocycle_rearrange {A : Type*} [AddCommGroup A] (a b c : A)
    (h : c - b + a = 0) : b = a + c := by
  calc
    b = (c - b + a) + b := by rw [h, zero_add]
    _ = a + c := by abel

/-- The proved injective contraction, in the six-edge cochain convention. -/
theorem one_exact_of_injective [Injective F] (c : One F U) (hc : d1 F U c = 0) :
    ∃ q : Zero F U, d0 F U q = c := by
  obtain ⟨q1,q2,q3,h01,h02,h03,h12,h13,h23⟩ :=
    four_one_cocycle_has_primitive F (U 0) (U 1) (U 2) (U 3)
      c.1 c.2.1 c.2.2.1 c.2.2.2.1 c.2.2.2.2.1 c.2.2.2.2.2
      (by
        intro W h0 h1 h2
        have hh := congrArg (res F (le_inf (le_inf h0 h1) h2))
          (congrArg (Prod.fst) hc)
        simp only [d1, Prod.fst_zero, map_zero, map_sub, map_add,
          res_comp] at hh
        exact cocycle_rearrange _ _ _ hh)
      (by
        intro W h0 h1 h3
        have hh := congrArg (res F (le_inf (le_inf h0 h1) h3))
          (congrArg (fun x => x.2.1) hc)
        simp only [d1, Prod.fst_zero, Prod.snd_zero, map_zero, map_sub, map_add,
          res_comp] at hh
        exact cocycle_rearrange _ _ _ hh)
      (by
        intro W h0 h2 h3
        have hh := congrArg (res F (le_inf (le_inf h0 h2) h3))
          (congrArg (fun x => x.2.2.1) hc)
        simp only [d1, Prod.fst_zero, Prod.snd_zero, map_zero, map_sub, map_add,
          res_comp] at hh
        exact cocycle_rearrange _ _ _ hh)
      (by
        intro W h1 h2 h3
        have hh := congrArg (res F (le_inf (le_inf h1 h2) h3))
          (congrArg (fun x => x.2.2.2) hc)
        simp only [d1, Prod.snd_zero, map_zero, map_sub, map_add,
          res_comp] at hh
        exact cocycle_rearrange _ _ _ hh)
  let q : Zero F U := Fin.cases 0 (Fin.cases q1
    (Fin.cases q2 (Fin.cases q3 (fun i => Fin.elim0 i))))
  refine ⟨q, ?_⟩
  apply Prod.ext <;> try apply Prod.ext <;> try apply Prod.ext <;> try apply Prod.ext <;>
    try apply Prod.ext
  all_goals simp only [d0, q, Fin.cases_zero, map_zero, sub_zero]
  · exact h01
  · exact h02
  · exact h03
  · exact h12
  · exact h13
  · exact h23

/-- The proved injective contraction, in the four-face cochain convention. -/
theorem two_exact_of_injective [Injective F] (c : Two F U) (hc : d2 F U c = 0) :
    ∃ b : One F U, d1 F U b = c := by
  obtain ⟨b12,b13,b23,h012,h013,h023,h123⟩ :=
    four_two_cocycle_has_primitive F (U 0) (U 1) (U 2) (U 3)
      c.1 c.2.1 c.2.2.1 c.2.2.2 (by
        intro W h0 h1 h2 h3
        have hh := congrArg (res F (le_inf (le_inf (le_inf h0 h1) h2) h3)) hc
        simpa only [d2, map_zero, map_sub, map_add, res_comp] using hh)
  refine ⟨⟨0,0,0,b12,b13,b23⟩, ?_⟩
  apply Prod.ext <;> try apply Prod.ext <;> try apply Prod.ext
  all_goals simp only [d1, map_zero, sub_zero, add_zero]
  · exact h012
  · exact h013
  · exact h023
  · exact h123

/-- A left exact sequence of sheaves is exact on sections at its middle term. -/
theorem sections_exact {S : ShortComplex (AbSheaf X)} (hS : S.ShortExact)
    (V : Opens X) (x : Sections S.X₂ V) (hx : app S.g V x = 0) :
    ∃ y : Sections S.X₁ V, app S.f V y = x := by
  let E : AbSheaf X ⥤ AddCommGrpCat :=
    sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat ⋙
      (evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj (op V)
  have hex : (S.map E).Exact :=
    (((Functor.preservesFiniteLimits_tfae E).out 1 3 rfl rfl).mpr
      inferInstance S ⟨hS.exact, hS.mono_f⟩).left
  exact (ShortComplex.ab_exact_iff (S.map E)).mp hex x hx

theorem mapZero_exact {S : ShortComplex (AbSheaf X)} (hS : S.ShortExact)
    (q : Zero S.X₂ U) (hq : mapZero U S.g q = 0) :
    ∃ p : Zero S.X₁ U, mapZero U S.f p = q := by
  have hl : ∀ i, ∃ p : Sections S.X₁ (U i), app S.f (U i) p = q i := by
    intro i
    exact sections_exact hS (U i) (q i) (congrFun hq i)
  choose p hp using hl
  exact ⟨p, funext hp⟩

theorem mapOne_exact {S : ShortComplex (AbSheaf X)} (hS : S.ShortExact)
    (c : One S.X₂ U) (hc : mapOne U S.g c = 0) :
    ∃ b : One S.X₁ U, mapOne U S.f b = c := by
  obtain ⟨b01,h01⟩ := sections_exact hS (U 0 ⊓ U 1) c.1
    (congrArg (Prod.fst) hc)
  obtain ⟨b02,h02⟩ := sections_exact hS (U 0 ⊓ U 2) c.2.1
    (congrArg (fun x => x.2.1) hc)
  obtain ⟨b03,h03⟩ := sections_exact hS (U 0 ⊓ U 3) c.2.2.1
    (congrArg (fun x => x.2.2.1) hc)
  obtain ⟨b12,h12⟩ := sections_exact hS (U 1 ⊓ U 2) c.2.2.2.1
    (congrArg (fun x => x.2.2.2.1) hc)
  obtain ⟨b13,h13⟩ := sections_exact hS (U 1 ⊓ U 3) c.2.2.2.2.1
    (congrArg (fun x => x.2.2.2.2.1) hc)
  obtain ⟨b23,h23⟩ := sections_exact hS (U 2 ⊓ U 3) c.2.2.2.2.2
    (congrArg (fun x => x.2.2.2.2.2) hc)
  refine ⟨⟨b01,b02,b03,b12,b13,b23⟩, ?_⟩
  apply Prod.ext <;> try apply Prod.ext <;> try apply Prod.ext <;> try apply Prod.ext <;>
    try apply Prod.ext
  · exact h01
  · exact h02
  · exact h03
  · exact h12
  · exact h13
  · exact h23

#print axioms one_exact_of_injective
#print axioms two_exact_of_injective
#print axioms sections_exact

theorem mapOne_injective (f : F ⟶ G) [Mono f] : Function.Injective (mapOne U f) := by
  rintro ⟨a,b,c,d,e,f₀⟩ ⟨a',b',c',d',e',f₀'⟩ h
  simp only [mapOne, Prod.mk.injEq] at h ⊢
  exact ⟨app_injective f _ h.1, app_injective f _ h.2.1,
    app_injective f _ h.2.2.1, app_injective f _ h.2.2.2.1,
    app_injective f _ h.2.2.2.2.1, app_injective f _ h.2.2.2.2.2⟩

def globalZero (x : Sections F ⊤) : Zero F U := fun _ => res F le_top x

@[simp] theorem d0_globalZero (x : Sections F ⊤) : d0 F U (globalZero U x) = 0 := by
  simp only [d0, globalZero, res_comp, sub_self, Prod.mk_zero_zero]

private theorem edge_compatible {V₁ V₂ W : Opens X}
    (q₁ : Sections F V₁) (q₂ : Sections F V₂)
    (h : res F inf_le_right q₂ - res F inf_le_left q₁ = (0 : Sections F (V₁ ⊓ V₂)))
    (h₁ : W ≤ V₁) (h₂ : W ≤ V₂) : res F h₁ q₁ = res F h₂ q₂ := by
  have hh := congrArg (res F (le_inf h₁ h₂)) (sub_eq_zero.mp h)
  exact ((res_comp F inf_le_left (le_inf h₁ h₂) q₁).symm.trans hh.symm).trans
    (res_comp F inf_le_right (le_inf h₁ h₂) q₂)

theorem compatible_of_d0_eq_zero (q : Zero F U) (hq : d0 F U q = 0)
    (i j : Fin 4) (W : Opens X) (hi : W ≤ U i) (hj : W ≤ U j) :
    res F hi (q i) = res F hj (q j) := by
  fin_cases i <;> fin_cases j
  · rfl
  · exact edge_compatible (q 0) (q 1) (congrArg Prod.fst hq) hi hj
  · exact edge_compatible (q 0) (q 2) (congrArg (fun x => x.2.1) hq) hi hj
  · exact edge_compatible (q 0) (q 3) (congrArg (fun x => x.2.2.1) hq) hi hj
  · exact (edge_compatible (q 0) (q 1) (congrArg Prod.fst hq) hj hi).symm
  · rfl
  · exact edge_compatible (q 1) (q 2) (congrArg (fun x => x.2.2.2.1) hq) hi hj
  · exact edge_compatible (q 1) (q 3) (congrArg (fun x => x.2.2.2.2.1) hq) hi hj
  · exact (edge_compatible (q 0) (q 2) (congrArg (fun x => x.2.1) hq) hj hi).symm
  · exact (edge_compatible (q 1) (q 2) (congrArg (fun x => x.2.2.2.1) hq) hj hi).symm
  · rfl
  · exact edge_compatible (q 2) (q 3) (congrArg (fun x => x.2.2.2.2.2) hq) hi hj
  · exact (edge_compatible (q 0) (q 3) (congrArg (fun x => x.2.2.1) hq) hj hi).symm
  · exact (edge_compatible (q 1) (q 3) (congrArg (fun x => x.2.2.2.2.1) hq) hj hi).symm
  · exact (edge_compatible (q 2) (q 3) (congrArg (fun x => x.2.2.2.2.2) hq) hj hi).symm
  · rfl

theorem globalZero_exists (hcover : (⨆ i, U i) = ⊤)
    (q : Zero F U) (hq : d0 F U q = 0) :
    ∃ x : Sections F ⊤, globalZero U x = q := by
  obtain ⟨x,hx,-⟩ := (show TopCat.Sheaf AddCommGrpCat X from F).existsUnique_gluing'
    U ⊤ (fun _ => homOfLE le_top) (by rw [hcover]) q (by
      intro i j
      exact compatible_of_d0_eq_zero U q hq i j _ inf_le_left inf_le_right)
  exact ⟨x, funext hx⟩

theorem freeOpenSections_postcomp (V : Opens X) (f : freeOpen V ⟶ F) (g : F ⟶ G) :
    app g V (freeOpenSections F V f) = freeOpenSections G V (f ≫ g) := by
  change _ = freeYonedaSections G.obj V
    (((sheafificationAdjunction (Opens.grothendieckTopology X) AddCommGrpCat).homEquiv
      _ G) (f ≫ g))
  rw [(sheafificationAdjunction (Opens.grothendieckTopology X)
    AddCommGrpCat).homEquiv_naturality_right]
  rfl

def sectionExtZero (V : Opens X) (x : Sections F V) : Ext (freeOpen V) F 0 :=
  Ext.mk₀ ((freeOpenSections F V).symm x)

/-- Exactness of the actual Ext connecting map gives an actual section lift. -/
theorem section_lift_of_boundary_zero {S : ShortComplex (AbSheaf X)}
    (hS : S.ShortExact) (V : Opens X) (x : Sections S.X₃ V)
    (hx : (sectionExtZero V x).comp hS.extClass rfl = 0) :
    ∃ y : Sections S.X₂ V, app S.g V y = x := by
  obtain ⟨z,hz⟩ := Ext.covariant_sequence_exact₃ (freeOpen V) hS
    (sectionExtZero V x) rfl hx
  obtain ⟨f,rfl⟩ := (Ext.mk₀_bijective _ _).surjective z
  have hf : f ≫ S.g = (freeOpenSections S.X₃ V).symm x := by
    apply (Ext.mk₀_bijective _ _).injective
    simpa only [Ext.mk₀_comp_mk₀, sectionExtZero] using hz
  refine ⟨freeOpenSections S.X₂ V f, ?_⟩
  rw [freeOpenSections_postcomp, hf, AddEquiv.apply_symm_apply]

theorem sections_surjective_of_H_one_subsingleton {S : ShortComplex (AbSheaf X)}
    (hS : S.ShortExact) (V : Opens X) (hV : Subsingleton (S.X₁.H' 1 V)) :
    Function.Surjective (app S.g V) := by
  intro x
  apply section_lift_of_boundary_zero hS V x
  exact @Subsingleton.elim (S.X₁.H' 1 V) hV _ _

abbrev presentation (F : AbSheaf X) : ShortComplex (AbSheaf X) :=
  ShortComplex.mk (Injective.ι F) (cokernel.π (Injective.ι F))
    (cokernel.condition (Injective.ι F))

theorem presentation_shortExact (F : AbSheaf X) : (presentation F).ShortExact :=
  { exact := ShortComplex.exact_cokernel (Injective.ι F)
    mono_f := by change Mono (Injective.ι F); infer_instance
    epi_g := by change Epi (cokernel.π (Injective.ι F)); infer_instance }

instance presentation_middle_injective (F : AbSheaf X) :
    Injective (presentation F).X₂ := by
  change Injective (Injective.under F)
  infer_instance

instance presentation_left_mono (F : AbSheaf X) : Mono (presentation F).f :=
  (presentation_shortExact F).mono_f

/-- Injectivity of dimension shifting in degree one when the middle sheaf is injective. -/
theorem connecting_one_zero {S : ShortComplex (AbSheaf X)} (hS : S.ShortExact)
    [Injective S.X₂] (V : Opens X) (x : Ext (freeOpen V) S.X₃ 1)
    (hx : x.comp hS.extClass rfl = 0) : x = 0 := by
  obtain ⟨y,hy⟩ := Ext.covariant_sequence_exact₃ (freeOpen V) hS x rfl hx
  have hy0 : y = 0 := Ext.eq_zero_of_injective y
  simpa only [hy0, Ext.zero_comp] using hy.symm

#print axioms globalZero_exists
#print axioms section_lift_of_boundary_zero
#print axioms connecting_one_zero

/-- The two actual injective presentations lift a given two-cocycle to a global
section of the second quotient. The fields retain all comparison equalities. -/
structure TwoDescent (c : Two F U) where
  first : One (presentation F).X₂ U
  first_differential : d1 (presentation F).X₂ U first = mapTwo U (presentation F).f c
  second : Zero (presentation (presentation F).X₃).X₂ U
  second_differential : d0 (presentation (presentation F).X₃).X₂ U second =
    mapOne U (presentation (presentation F).X₃).f (mapOne U (presentation F).g first)
  globalSection : Sections (presentation (presentation F).X₃).X₃ ⊤
  global_restriction : globalZero U globalSection =
    mapZero U (presentation (presentation F).X₃).g second

/-- Existence uses actual injective contractions and the sheaf gluing axiom. -/
theorem twoDescent_nonempty (hcover : (⨆ i, U i) = ⊤)
    (c : Two F U) (hc : d2 F U c = 0) : Nonempty (TwoDescent U c) := by
  obtain ⟨b,hb⟩ := two_exact_of_injective U (mapTwo U (presentation F).f c) (by
    rw [← mapThree_d2, hc, map_zero])
  have hpb : d1 (presentation F).X₃ U (mapOne U (presentation F).g b) = 0 := by
    rw [← mapTwo_d1, hb, mapTwo_comp, (presentation F).zero, mapTwo_zeroHom]
  obtain ⟨v,hv⟩ := one_exact_of_injective U
    (mapOne U (presentation (presentation F).X₃).f (mapOne U (presentation F).g b)) (by
      rw [← mapTwo_d1, hpb, mapTwo_zero])
  have hd : d0 (presentation (presentation F).X₃).X₃ U
      (mapZero U (presentation (presentation F).X₃).g v) = 0 := by
    rw [← mapOne_d0, hv, mapOne_comp, (presentation (presentation F).X₃).zero,
      mapOne_zeroHom]
  obtain ⟨t,ht⟩ := globalZero_exists U hcover _ hd
  exact ⟨⟨b,hb,v,hv,t,ht⟩⟩

/-- The actual degree-two Ext class attached to the retained two-stage descent. -/
def descentClass {c : Two F U} (d : TwoDescent U c) : F.H' 2 ⊤ :=
  ((sectionExtZero ⊤ d.globalSection).comp
    (presentation_shortExact (presentation F).X₃).extClass rfl).comp
      (presentation_shortExact F).extClass rfl

/-- A four-open two-cocycle defines an actual derived sheaf-cohomology class. -/
def cechTwoClass (hcover : (⨆ i, U i) = ⊤)
    (c : Two F U) (hc : d2 F U c = 0) : F.H' 2 ⊤ :=
  descentClass U (Classical.choice (twoDescent_nonempty U hcover c hc))

#print axioms twoDescent_nonempty
#print axioms cechTwoClass

theorem mapZero_sub (f : F ⟶ G) (q r : Zero F U) :
    mapZero U f (q - r) = mapZero U f q - mapZero U f r := by
  funext i
  exact (app f (U i)).map_sub _ _

theorem mapZero_globalZero (f : F ⟶ G) (x : Sections F ⊤) :
    mapZero U f (globalZero U x) = globalZero U (app f ⊤ x) := by
  funext i
  exact app_res f le_top x

/-- Zero in the actual derived group forces a concrete six-edge primitive.
Only the degree-one cohomology of the four opens is used. -/
theorem descentClass_eq_zero_implies_boundary
    (hlocal : ∀ i, Subsingleton (F.H' 1 (U i)))
    {c : Two F U} (d : TwoDescent U c) (hz : descentClass U d = 0) :
    ∃ a : One F U, d1 F U a = c := by
  have hfirst := presentation_shortExact F
  have hsecond := presentation_shortExact (presentation F).X₃
  have hzero : (sectionExtZero ⊤ d.globalSection).comp hsecond.extClass rfl = 0 :=
    connecting_one_zero hfirst ⊤ _ hz
  obtain ⟨g,hg⟩ := section_lift_of_boundary_zero hsecond ⊤ d.globalSection hzero
  have hvzero : mapZero U (presentation (presentation F).X₃).g
      (d.second - globalZero U g) = 0 := by
    rw [mapZero_sub, mapZero_globalZero, hg, ← d.global_restriction, sub_self]
  obtain ⟨q,hq⟩ := mapZero_exact U hsecond _ hvzero
  have hqdiff : d0 (presentation F).X₃ U q = mapOne U (presentation F).g d.first := by
    apply mapOne_injective U (presentation (presentation F).X₃).f
    rw [mapOne_d0, hq, d0_sub, d0_globalZero, sub_zero, d.second_differential]
  have hlift : ∀ i, ∃ w : Sections (presentation F).X₂ (U i),
      app (presentation F).g (U i) w = q i := by
    intro i
    exact sections_surjective_of_H_one_subsingleton hfirst (U i) (hlocal i) (q i)
  choose w hw using hlift
  have hw' : mapZero U (presentation F).g w = q := funext hw
  have hbzero : mapOne U (presentation F).g
      (d.first - d0 (presentation F).X₂ U w) = 0 := by
    rw [mapOne_sub, mapOne_d0, hw', hqdiff, sub_self]
  obtain ⟨a,ha⟩ := mapOne_exact U hfirst _ hbzero
  refine ⟨a, ?_⟩
  apply mapTwo_injective U (presentation F).f
  rw [mapTwo_d1, ha, d1_sub, d1_d0, sub_zero, d.first_differential]

/-- The constructed comparison detects nonzero two-cocycles modulo boundaries. -/
theorem cechTwoClass_eq_zero_implies_boundary (hcover : (⨆ i, U i) = ⊤)
    (c : Two F U) (hc : d2 F U c = 0)
    (hlocal : ∀ i, Subsingleton (F.H' 1 (U i)))
    (hz : cechTwoClass U hcover c hc = 0) :
    ∃ a : One F U, d1 F U a = c :=
  descentClass_eq_zero_implies_boundary U hlocal
    (Classical.choice (twoDescent_nonempty U hcover c hc)) hz

/-- A concrete nonboundary gives a concrete nonzero class in actual derived H′². -/
theorem cechTwoClass_ne_zero (hcover : (⨆ i, U i) = ⊤)
    (c : Two F U) (hc : d2 F U c = 0)
    (hlocal : ∀ i, Subsingleton (F.H' 1 (U i)))
    (hnot : ¬ ∃ a : One F U, d1 F U a = c) : cechTwoClass U hcover c hc ≠ 0 := by
  intro hz
  exact hnot (cechTwoClass_eq_zero_implies_boundary U hcover c hc hlocal hz)

#print axioms descentClass_eq_zero_implies_boundary
#print axioms cechTwoClass_eq_zero_implies_boundary
#print axioms cechTwoClass_ne_zero

end CycleQ2CechTwoToDerived
end

end


section

/-!
# Independence and additivity of the actual four-open comparison

The two-stage descent construction is independent of its auxiliary choices.
A boundary maps to zero, and the resulting additive comparison factors through
the genuine second Cech cohomology group.
-/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2CechTwoComparison
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite TopologicalSpace
open CycleQ2InjectiveCech CycleQ2GeometricSheafLocalIso CycleQ2CechTwoToDerived

variable {X : TopCat.{0}}
local instance sheafHasExt : HasExt.{1} (AbSheaf X) := HasExt.standard _
variable {F G H : AbSheaf X} (U : Fin 4 → Opens X)

theorem globalZero_injective (hcover : (⨆ i, U i) = ⊤) :
    Function.Injective (globalZero (F := F) U) := by
  intro x y hxy
  obtain ⟨t,_,ht⟩ := (show TopCat.Sheaf AddCommGrpCat X from F).existsUnique_gluing'
    U ⊤ (fun _ => homOfLE le_top) (by rw [hcover]) (globalZero U x) (by
      intro i j
      exact compatible_of_d0_eq_zero U _ (d0_globalZero U x) i j _
        inf_le_left inf_le_right)
  exact (ht x (fun _ => rfl)).trans (ht y (fun i => congrFun hxy.symm i)).symm

@[simp] theorem mapZero_comp (f : F ⟶ G) (g : G ⟶ H) (q : Zero F U) :
    mapZero U g (mapZero U f q) = mapZero U (f ≫ g) q := rfl
@[simp] theorem mapZero_zeroHom (q : Zero F U) : mapZero U (0 : F ⟶ G) q = 0 := rfl
@[simp] theorem mapZero_zero (f : F ⟶ G) : mapZero U f 0 = 0 := by
  funext i
  exact (app f (U i)).map_zero

theorem globalZero_sub (x y : Sections F ⊤) :
    globalZero U (x-y) = globalZero U x - globalZero U y := by
  funext i
  exact (res F le_top).map_sub _ _

theorem sectionExtZero_app (f : F ⟶ G) (V : Opens X) (x : Sections F V) :
    sectionExtZero V (app f V x) = (sectionExtZero V x).comp (Ext.mk₀ f) rfl := by
  unfold sectionExtZero
  rw [Ext.mk₀_comp_mk₀]
  congr 1
  apply (freeOpenSections G V).injective
  rw [AddEquiv.apply_symm_apply, ← freeOpenSections_postcomp,
    AddEquiv.apply_symm_apply]

theorem sectionExtZero_sub (V : Opens X) (x y : Sections F V) :
    sectionExtZero V (x-y) = sectionExtZero V x - sectionExtZero V y := by
  unfold sectionExtZero
  rw [map_sub]
  simp only [sub_eq_add_neg, Ext.mk₀_add, Ext.mk₀_neg]

/-- A descent of the zero cocycle represents zero, without any local vanishing
assumption. This is the gauge calculation that removes every choice. -/
theorem descentClass_zero_cocycle (hcover : (⨆ i, U i) = ⊤)
    (d : TwoDescent U (0 : Two F U)) : descentClass U d = 0 := by
  have hb : d1 (presentation F).X₂ U d.first = 0 :=
    d.first_differential.trans (mapTwo_zero U (presentation F).f)
  obtain ⟨q,hq⟩ := one_exact_of_injective U d.first hb
  have hquot : mapOne U (presentation F).g d.first =
      d0 (presentation F).X₃ U (mapZero U (presentation F).g q) := by
    rw [← hq, mapOne_d0]
  have hv : d0 (presentation (presentation F).X₃).X₂ U
      (d.second - mapZero U (presentation (presentation F).X₃).f
        (mapZero U (presentation F).g q)) = 0 := by
    rw [d0_sub, d.second_differential, ← mapOne_d0, hquot, sub_self]
  obtain ⟨g,hg⟩ := globalZero_exists U hcover _ hv
  have hglobal : app (presentation (presentation F).X₃).g ⊤ g = d.globalSection := by
    apply globalZero_injective U hcover
    rw [← mapZero_globalZero, hg, mapZero_sub, mapZero_comp,
      (presentation (presentation F).X₃).zero, mapZero_zeroHom, sub_zero,
      ← d.global_restriction]
  have hδ : (sectionExtZero ⊤ d.globalSection).comp
      (presentation_shortExact (presentation F).X₃).extClass rfl = 0 := by
    rw [← hglobal, sectionExtZero_app, Ext.comp_assoc_of_second_deg_zero,
      ShortComplex.ShortExact.comp_extClass, Ext.comp_zero]
  simp only [descentClass, hδ, Ext.zero_comp]

/-- Difference of actual descent data retains the literal cochain differences. -/
def subtractDescents {c c' : Two F U} (d : TwoDescent U c) (e : TwoDescent U c') :
    TwoDescent U (c-c') where
  first := d.first-e.first
  first_differential := by
    rw [d1_sub, d.first_differential, e.first_differential, mapTwo_sub]
  second := d.second-e.second
  second_differential := by
    simp only [d0_sub, d.second_differential, e.second_differential, mapOne_sub]
  globalSection := d.globalSection-e.globalSection
  global_restriction := by
    rw [globalZero_sub, d.global_restriction, e.global_restriction, mapZero_sub]

theorem descentClass_sub {c c' : Two F U} (d : TwoDescent U c) (e : TwoDescent U c') :
    descentClass U (subtractDescents U d e) = descentClass U d - descentClass U e := by
  simp only [descentClass, subtractDescents]
  rw [sectionExtZero_sub]
  simp only [sub_eq_add_neg, Ext.add_comp, Ext.neg_comp]

theorem descentClass_zero_of_underlying_zero (hcover : (⨆ i, U i) = ⊤)
    {c : Two F U} (d : TwoDescent U c) (hc : c=0) : descentClass U d = 0 := by
  subst c
  exact descentClass_zero_cocycle U hcover d

/-- Every choice of injective primitives and glued section gives the same actual
Ext class for a fixed two-cocycle. -/
theorem descentClass_independent (hcover : (⨆ i, U i) = ⊤)
    {c : Two F U} (d e : TwoDescent U c) : descentClass U d = descentClass U e := by
  have h := descentClass_zero_of_underlying_zero U hcover
    (subtractDescents U d e) (sub_self c)
  rw [descentClass_sub] at h
  exact sub_eq_zero.mp h

#print axioms globalZero_injective
#print axioms descentClass_zero_cocycle
#print axioms descentClass_independent

@[simp] theorem d0_zero : d0 F U 0 = 0 := by
  simp only [d0, Pi.zero_apply, map_zero, sub_self, Prod.mk_zero_zero]
@[simp] theorem d1_zero : d1 F U 0 = 0 := by
  simp only [d1, Prod.fst_zero, Prod.snd_zero, map_zero, sub_self, add_zero,
    Prod.mk_zero_zero]
@[simp] theorem d2_zero : d2 F U 0 = 0 := by
  simp only [d2, Prod.fst_zero, Prod.snd_zero, map_zero, sub_self, add_zero]
@[simp] theorem globalZero_zero : globalZero (F := F) U 0 = 0 := by
  funext i
  exact (res F le_top).map_zero

theorem d0_add (q r : Zero F U) : d0 F U (q+r) = d0 F U q + d0 F U r := by
  apply Prod.ext <;> try apply Prod.ext <;> try apply Prod.ext <;> try apply Prod.ext <;>
    try apply Prod.ext
  all_goals simp only [d0, Pi.add_apply, map_add, Prod.fst_add, Prod.snd_add]
  all_goals abel

theorem d1_add (a b : One F U) : d1 F U (a+b) = d1 F U a + d1 F U b := by
  apply Prod.ext <;> try apply Prod.ext <;> try apply Prod.ext
  all_goals simp only [d1, Prod.fst_add, Prod.snd_add, map_add]
  all_goals abel

theorem d2_add (c c' : Two F U) : d2 F U (c+c') = d2 F U c + d2 F U c' := by
  simp only [d2, Prod.fst_add, Prod.snd_add, map_add]
  abel

theorem mapZero_add (f : F ⟶ G) (q r : Zero F U) :
    mapZero U f (q+r) = mapZero U f q + mapZero U f r := by
  funext i
  exact (app f (U i)).map_add _ _

theorem mapOne_add (f : F ⟶ G) (a b : One F U) :
    mapOne U f (a+b) = mapOne U f a + mapOne U f b := by
  simp only [mapOne, Prod.fst_add, Prod.snd_add, map_add]
  rfl

theorem mapTwo_add (f : F ⟶ G) (c c' : Two F U) :
    mapTwo U f (c+c') = mapTwo U f c + mapTwo U f c' := by
  simp only [mapTwo, Prod.fst_add, Prod.snd_add, map_add]
  rfl

theorem globalZero_add (x y : Sections F ⊤) :
    globalZero U (x+y) = globalZero U x + globalZero U y := by
  funext i
  exact (res F le_top).map_add _ _

theorem sectionExtZero_add (V : Opens X) (x y : Sections F V) :
    sectionExtZero V (x+y) = sectionExtZero V x + sectionExtZero V y := by
  unfold sectionExtZero
  rw [map_add, Ext.mk₀_add]

/-- Addition of descent data retains the literal sums of all cochains. -/
def addDescents {c c' : Two F U} (d : TwoDescent U c) (e : TwoDescent U c') :
    TwoDescent U (c+c') where
  first := d.first+e.first
  first_differential := by
    rw [d1_add, d.first_differential, e.first_differential, mapTwo_add]
  second := d.second+e.second
  second_differential := by
    simp only [d0_add, d.second_differential, e.second_differential, mapOne_add]
  globalSection := d.globalSection+e.globalSection
  global_restriction := by
    rw [globalZero_add, d.global_restriction, e.global_restriction, mapZero_add]

theorem descentClass_add {c c' : Two F U} (d : TwoDescent U c) (e : TwoDescent U c') :
    descentClass U (addDescents U d e) = descentClass U d + descentClass U e := by
  simp only [descentClass, addDescents]
  rw [sectionExtZero_add, Ext.add_comp, Ext.add_comp]

/-- A boundary has explicit descent data with zero global section. -/
def boundaryDescent (a : One F U) : TwoDescent U (d1 F U a) where
  first := mapOne U (presentation F).f a
  first_differential := (mapTwo_d1 U (presentation F).f a).symm
  second := 0
  second_differential := by
    have h : mapOne U (presentation F).g (mapOne U (presentation F).f a) = 0 := by
      rw [mapOne_comp, (presentation F).zero, mapOne_zeroHom]
    rw [d0_zero, h, mapOne_zero]
  globalSection := 0
  global_restriction := by rw [globalZero_zero, mapZero_zero]

theorem boundaryDescent_class (a : One F U) :
    descentClass U (boundaryDescent U a) = 0 := by
  simp only [descentClass, boundaryDescent, sectionExtZero, map_zero,
    Ext.mk₀_zero, Ext.zero_comp]

theorem cechTwoClass_eq_descentClass (hcover : (⨆ i, U i) = ⊤)
    (c : Two F U) (hc : d2 F U c=0) (d : TwoDescent U c) :
    cechTwoClass U hcover c hc = descentClass U d :=
  descentClass_independent U hcover _ d

theorem cechTwoClass_boundary (hcover : (⨆ i, U i) = ⊤)
    (a : One F U) (hc : d2 F U (d1 F U a)=0) :
    cechTwoClass U hcover (d1 F U a) hc = 0 :=
  (cechTwoClass_eq_descentClass U hcover _ hc (boundaryDescent U a)).trans
    (boundaryDescent_class U a)

/-- Under exactly the four local H′¹ vanishings, zero in the actual derived group
is equivalent to being a boundary in the displayed six-edge complex. -/
theorem cechTwoClass_eq_zero_iff (hcover : (⨆ i, U i) = ⊤)
    (c : Two F U) (hc : d2 F U c=0)
    (hlocal : ∀ i, Subsingleton (F.H' 1 (U i))) :
    cechTwoClass U hcover c hc=0 ↔ ∃ a : One F U, d1 F U a=c := by
  constructor
  · exact cechTwoClass_eq_zero_implies_boundary U hcover c hc hlocal
  · rintro ⟨a,ha⟩
    subst c
    exact cechTwoClass_boundary U hcover a hc

/-- Additivity follows from arbitrary descent data. -/
theorem cechTwoClass_add (hcover : (⨆ i, U i) = ⊤)
    (c c' : Two F U) (hc : d2 F U c=0) (hc' : d2 F U c'=0)
    (hcc' : d2 F U (c+c')=0) :
    cechTwoClass U hcover (c+c') hcc' =
      cechTwoClass U hcover c hc + cechTwoClass U hcover c' hc' := by
  let d := Classical.choice (twoDescent_nonempty U hcover c hc)
  let e := Classical.choice (twoDescent_nonempty U hcover c' hc')
  exact (cechTwoClass_eq_descentClass U hcover _ hcc' (addDescents U d e)).trans
    (descentClass_add U d e)

#print axioms cechTwoClass_boundary
#print axioms cechTwoClass_eq_zero_iff
#print axioms cechTwoClass_add

/-- The literal differential from six edges to four faces, as an additive map. -/
def oneDifferentialHom : One F U →+ Two F U where
  toFun := d1 F U
  map_zero' := d1_zero U
  map_add' := d1_add U

/-- The literal differential from four faces to the quadruple intersection. -/
def twoDifferentialHom : Two F U →+ Three F U where
  toFun := d2 F U
  map_zero' := d2_zero U
  map_add' := d2_add U

/-- The actual subgroup of two-cocycles for the four given opens. -/
def twoCycles : AddSubgroup (Two F U) := (twoDifferentialHom (F := F) U).ker

/-- The image of every actual six-edge cochain inside the two-cocycles. -/
def oneBoundaryHom : One F U →+ twoCycles (F := F) U where
  toFun a := ⟨d1 F U a, d2_d1 F U a⟩
  map_zero' := Subtype.ext (d1_zero U)
  map_add' a b := Subtype.ext (d1_add U a b)

/-- Actual coboundaries, as a subgroup of actual cocycles. -/
def twoBoundaries : AddSubgroup (twoCycles (F := F) U) := (oneBoundaryHom U).range

/-- The genuine second cohomology group of the displayed four-open complex. -/
abbrev CechTwo := twoCycles (F := F) U ⧸ twoBoundaries U

theorem twoBoundaries_mem_iff (c : twoCycles (F := F) U) :
    c ∈ twoBoundaries U ↔ ∃ a : One F U, d1 F U a=c.val := by
  change (∃ a, oneBoundaryHom U a=c) ↔ _
  constructor
  · rintro ⟨a,ha⟩
    exact ⟨a, congrArg Subtype.val ha⟩
  · rintro ⟨a,ha⟩
    exact ⟨a, Subtype.ext ha⟩

/-- The canonical additive map on cocycles supplied by the explicit descent. -/
def cyclesClass (hcover : (⨆ i, U i) = ⊤) : twoCycles (F := F) U →+ F.H' 2 ⊤ where
  toFun c := cechTwoClass U hcover c.val c.property
  map_zero' := by
    change cechTwoClass U hcover (0 : Two F U) (d2_zero U)=0
    have h := cechTwoClass_boundary U hcover (0 : One F U) (d2_d1 F U 0)
    simpa only [d1_zero] using h
  map_add' c c' := cechTwoClass_add U hcover c.val c'.val c.property c'.property
    (c+c').property

theorem boundaries_le_kernel (hcover : (⨆ i, U i) = ⊤) :
    twoBoundaries (F := F) U ≤ (cyclesClass U hcover).ker := by
  intro c hc
  obtain ⟨a,rfl⟩ := hc
  exact cechTwoClass_boundary U hcover a (d2_d1 F U a)

theorem boundaries_eq_kernel (hcover : (⨆ i, U i) = ⊤)
    (hlocal : ∀ i, Subsingleton (F.H' 1 (U i))) :
    twoBoundaries (F := F) U = (cyclesClass U hcover).ker := by
  apply le_antisymm (boundaries_le_kernel U hcover)
  intro c hc
  apply (twoBoundaries_mem_iff U c).mpr
  exact (cechTwoClass_eq_zero_iff U hcover c.val c.property hlocal).mp hc

/-- The actual additive four-open Cech-to-derived comparison in degree two. -/
def comparison (hcover : (⨆ i, U i) = ⊤) : CechTwo (F := F) U →+ F.H' 2 ⊤ :=
  QuotientAddGroup.lift (twoBoundaries U) (cyclesClass U hcover)
    (boundaries_le_kernel U hcover)

/-- The quotient comparison sends the literal representative to the earlier
cocycle-specific Ext class, with no change of normalization. -/
theorem comparison_apply (hcover : (⨆ i, U i) = ⊤) (c : twoCycles (F := F) U) :
    comparison U hcover (QuotientAddGroup.mk c) = cechTwoClass U hcover c.val c.property :=
  rfl

/-- Local H′¹ vanishing on the four opens makes the actual comparison injective. -/
theorem comparison_injective (hcover : (⨆ i, U i) = ⊤)
    (hlocal : ∀ i, Subsingleton (F.H' 1 (U i))) :
    Function.Injective (comparison (F := F) U hcover) :=
  (QuotientAddGroup.injective_lift_iff _ _ _).mpr
    (boundaries_eq_kernel U hcover hlocal)

#print axioms boundaries_eq_kernel
#print axioms comparison_apply
#print axioms comparison_injective

end CycleQ2CechTwoComparison
end

end


section

/-!
# Naturality of the actual four-open Cech comparison

An actual sheaf morphism extends across each of the two injective
presentations. The induced quotient maps transport all descent data;
naturality of the actual Ext connecting morphisms then identifies the
resulting derived classes.
-/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2CechTwoNaturality
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite TopologicalSpace
open CycleQ2InjectiveCech CycleQ2GeometricSheafLocalIso CycleQ2CechTwoToDerived
  CycleQ2CechTwoComparison

variable {X : TopCat.{0}}
local instance sheafHasExt : HasExt.{1} (AbSheaf X) := HasExt.standard _
variable {F G H : AbSheaf X}

/-- The genuine extension into the target injective sheaf. -/
def middleMap (f : F ⟶ G) : (presentation F).X₂ ⟶ (presentation G).X₂ :=
  Injective.factorThru (f ≫ (presentation G).f) (presentation F).f

theorem first_middleMap (f : F ⟶ G) :
    (presentation F).f ≫ middleMap f = f ≫ (presentation G).f :=
  Injective.comp_factorThru _ _

/-- An actual map between the chosen short exact injective presentations. -/
abbrev presentationMap (f : F ⟶ G) : presentation F ⟶ presentation G where
  τ₁ := f
  τ₂ := middleMap f
  τ₃ := cokernel.map (presentation F).f (presentation G).f f (middleMap f)
    (first_middleMap f)
  comm₁₂ := (first_middleMap f).symm
  comm₂₃ := by
    exact (cokernel.π_desc (presentation F).f
      (middleMap f ≫ (presentation G).g) _).symm

abbrev secondPresentationMap (f : F ⟶ G) :
    presentation (presentation F).X₃ ⟶ presentation (presentation G).X₃ :=
  presentationMap (presentationMap f).τ₃

variable (U : Fin 4 → Opens X)

/-- Transport of the literal injective primitives and glued quotient section. -/
def transportDescent (f : F ⟶ G) {c : Two F U} (d : TwoDescent U c) :
    TwoDescent U (mapTwo U f c) where
  first := mapOne U (presentationMap f).τ₂ d.first
  first_differential := by
    rw [← mapTwo_d1, d.first_differential, mapTwo_comp,
      ← (presentationMap f).comm₁₂, ← mapTwo_comp]
  second := mapZero U (secondPresentationMap f).τ₂ d.second
  second_differential := by
    have hmap : (presentation F).g ≫ (presentation (presentation F).X₃).f ≫
        (secondPresentationMap f).τ₂ =
        (presentationMap f).τ₂ ≫ (presentation G).g ≫
          (presentation (presentation G).X₃).f := by
      rw [← (secondPresentationMap f).comm₁₂]
      change (presentation F).g ≫ (presentationMap f).τ₃ ≫ _ = _
      rw [← Category.assoc, ← (presentationMap f).comm₂₃, Category.assoc]
    simp only [← mapOne_d0, d.second_differential, mapOne_comp, Category.assoc]
    exact congrArg (fun φ => mapOne U φ d.first) hmap
  globalSection := app (secondPresentationMap f).τ₃ ⊤ d.globalSection
  global_restriction := by
    rw [← mapZero_globalZero, d.global_restriction, mapZero_comp,
      ← (secondPresentationMap f).comm₂₃, ← mapZero_comp]

/-- Naturality of a connecting operation, in the exact composition convention
used by the two-stage descent. -/
theorem connecting_naturality {S T : ShortComplex (AbSheaf X)}
    (hS : S.ShortExact) (hT : T.ShortExact) (m : S ⟶ T)
    {K : AbSheaf X} (n : ℕ) (x : Ext K S.X₃ n) :
    (x.comp hS.extClass (rfl : n+1=n+1)).comp (Ext.mk₀ m.τ₁) (Nat.add_zero (n+1)) =
      (x.comp (Ext.mk₀ m.τ₃) (Nat.add_zero n)).comp hT.extClass rfl := by
  rw [Ext.comp_assoc_of_third_deg_zero, hS.extClass_naturality hT m,
    ← Ext.comp_assoc_of_second_deg_zero]

/-- The intrinsic map of the actual cohomology presheaf, evaluated at top. -/
def derivedMap (f : F ⟶ G) : F.H' 2 ⊤ →+ G.H' 2 ⊤ :=
  (((Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology X) 2).map f).app
    (op ⊤)).hom

@[simp] theorem derivedMap_apply (f : F ⟶ G) (x : F.H' 2 ⊤) :
    derivedMap f x = x.comp (Ext.mk₀ f) (Nat.add_zero 2) := rfl

/-- Transported descent maps to precisely the intrinsic derived image. -/
theorem descentClass_naturality (f : F ⟶ G) {c : Two F U} (d : TwoDescent U c) :
    derivedMap f (descentClass U d) = descentClass U (transportDescent U f d) := by
  simp only [derivedMap_apply, descentClass, transportDescent]
  rw [connecting_naturality (presentation_shortExact F) (presentation_shortExact G)
      (presentationMap f),
    connecting_naturality (presentation_shortExact (presentation F).X₃)
      (presentation_shortExact (presentation G).X₃) (secondPresentationMap f),
    ← sectionExtZero_app]

/-- Naturality of the canonical cocycle-specific class requires no local
cohomology vanishing assumption. -/
theorem cechTwoClass_naturality (hcover : (⨆ i, U i) = ⊤) (f : F ⟶ G)
    (c : Two F U) (hc : d2 F U c=0) (hmap : d2 G U (mapTwo U f c)=0) :
    derivedMap f (cechTwoClass U hcover c hc) =
      cechTwoClass U hcover (mapTwo U f c) hmap := by
  let d := Classical.choice (twoDescent_nonempty U hcover c hc)
  change derivedMap f (descentClass U d) = _
  rw [descentClass_naturality]
  exact (cechTwoClass_eq_descentClass U hcover _ hmap (transportDescent U f d)).symm

#print axioms presentationMap
#print axioms transportDescent
#print axioms connecting_naturality
#print axioms derivedMap_apply
#print axioms descentClass_naturality
#print axioms cechTwoClass_naturality

/-- The actual morphism on four-face cochains restricts to two-cocycles. -/
def cyclesMap (f : F ⟶ G) : twoCycles (F := F) U →+ twoCycles (F := G) U where
  toFun c := ⟨mapTwo U f c.val, by
    change d2 G U (mapTwo U f c.val)=0
    have hc : d2 F U c.val=0 := c.property
    rw [← mapThree_d2, hc, map_zero]⟩
  map_zero' := Subtype.ext (mapTwo_zero U f)
  map_add' c c' := Subtype.ext (mapTwo_add U f c.val c'.val)

theorem cyclesMap_boundaries (f : F ⟶ G) :
    twoBoundaries (F := F) U ≤ (twoBoundaries (F := G) U).comap (cyclesMap U f) := by
  intro c hc
  obtain ⟨a,rfl⟩ := hc
  apply (twoBoundaries_mem_iff U _).mpr
  exact ⟨mapOne U f a, (mapTwo_d1 U f a).symm⟩

/-- The induced map on the actual four-open cycle/boundary quotient. -/
def quotientMap (f : F ⟶ G) : CechTwo (F := F) U →+ CechTwo (F := G) U :=
  QuotientAddGroup.map (twoBoundaries U) (twoBoundaries U) (cyclesMap U f)
    (cyclesMap_boundaries U f)

@[simp] theorem quotientMap_mk (f : F ⟶ G) (c : twoCycles (F := F) U) :
    quotientMap U f (QuotientAddGroup.mk c) = QuotientAddGroup.mk (cyclesMap U f c) :=
  rfl

/-- The actual quotient comparison is natural for every actual additive-sheaf
morphism, with the intrinsic cohomology-presheaf map on the derived side. -/
theorem comparison_naturality (hcover : (⨆ i, U i) = ⊤) (f : F ⟶ G) :
    (comparison (F := G) U hcover).comp (quotientMap U f) =
      (derivedMap f).comp (comparison (F := F) U hcover) := by
  apply AddMonoidHom.ext
  intro x
  refine Quotient.inductionOn' x ?_
  intro c
  exact (cechTwoClass_naturality U hcover f c.val c.property
    (cyclesMap U f c).property).symm

#print axioms cyclesMap_boundaries
#print axioms quotientMap_mk
#print axioms comparison_naturality

end CycleQ2CechTwoNaturality
end

end


section

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2ProjectiveCartierIntersections

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
  CycleQ2GeometricCartierNormalLift CycleQ2CartierSurfaceGrading
  CycleQ2CartierProjectiveCover CycleQ2GeometricProjectiveHOne
  CycleQ2GeometricSheafLocalIso

/-- The product-defined actual projective patch is exactly the finite
intersection of the actual four-open cover. -/
theorem coverPatch_finsetInf (r θ : ℂ) (s : Finset (Fin 4)) :
    coverPatch r θ s = s.inf (coverFamily r θ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [coverPatch, coverProduct]
  | @insert i s hi ih =>
      simp only [coverPatch, coverProduct, Finset.prod_insert hi,
        Proj.basicOpen_mul, Finset.inf_insert]
      exact congrArg (fun V => coverFamily r θ i ⊓ V) ih

theorem coverPatch_triple (r θ : ℂ) (i j k : Fin 4) :
    coverPatch r θ {i,j,k} =
      (coverFamily r θ i ⊓ coverFamily r θ j) ⊓ coverFamily r θ k := by
  simp only [coverPatch_finsetInf, Finset.inf_insert, Finset.inf_singleton, inf_assoc]

theorem coverPatch_quadruple (r θ : ℂ) :
    coverPatch r θ Finset.univ =
      ((coverFamily r θ 0 ⊓ coverFamily r θ 1) ⊓ coverFamily r θ 2) ⊓
        coverFamily r θ 3 := by
  have hu : (Finset.univ : Finset (Fin 4)) = {0,1,2,3} := by decide
  rw [hu]
  simp only [coverPatch_finsetInf, Finset.inf_insert, Finset.inf_singleton, inf_assoc]

section Sheaf
variable {X : TopCat.{0}}
  (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0})

/-- Canonical transport of actual sections along equality of opens, implemented
by restriction in both directions. -/
def sectionEquivOfOpenEq {O P : Opens X} (h : O = P) :
    F.obj.obj (op O) ≃+ F.obj.obj (op P) where
  toFun := res F h.ge
  invFun := res F h.le
  left_inv x := (res_comp F h.ge h.le x).trans (res_self F O x)
  right_inv x := (res_comp F h.le h.ge x).trans (res_self F P x)
  map_add' := (res F h.ge).map_add

@[simp] theorem sectionEquivOfOpenEq_apply {O P : Opens X} (h : O = P)
    (x : F.obj.obj (op O)) : sectionEquivOfOpenEq F h x = res F h.ge x := rfl

/-- Equality-of-open transports preserve the actual sheaf restrictions. -/
theorem sectionEquivOfOpenEq_restrict {O P V W : Opens X}
    (hOV : O = V) (hPW : P = W) (hPO : P ≤ O) (hWV : W ≤ V)
    (x : F.obj.obj (op O)) :
    sectionEquivOfOpenEq F hPW (res F hPO x) =
      res F hWV (sectionEquivOfOpenEq F hOV x) :=
  (res_comp F hPO hPW.ge x).trans (res_comp F hOV.ge hWV x).symm

end Sheaf

abbrev additiveSheaf (r θ : ℂ) := structureAdditiveSheaf (projectiveSurface r θ)

def pairSectionsEquiv (r θ : ℂ) (i j : Fin 4) :
    CycleQ2ProjectiveCartierCochain.Sections r θ {i,j} ≃+
      (additiveSheaf r θ).obj.obj (op (coverFamily r θ i ⊓ coverFamily r θ j)) :=
  sectionEquivOfOpenEq (additiveSheaf r θ) (coverPatch_pair r θ i j)

def tripleSectionsEquiv (r θ : ℂ) (i j k : Fin 4) :
    CycleQ2ProjectiveCartierCochain.Sections r θ {i,j,k} ≃+
      (additiveSheaf r θ).obj.obj
        (op ((coverFamily r θ i ⊓ coverFamily r θ j) ⊓ coverFamily r θ k)) :=
  sectionEquivOfOpenEq (additiveSheaf r θ) (coverPatch_triple r θ i j k)

def quadrupleSectionsEquiv (r θ : ℂ) :
    CycleQ2ProjectiveCartierCochain.Sections r θ Finset.univ ≃+
      (additiveSheaf r θ).obj.obj
        (op (((coverFamily r θ 0 ⊓ coverFamily r θ 1) ⊓ coverFamily r θ 2) ⊓
          coverFamily r θ 3)) :=
  sectionEquivOfOpenEq (additiveSheaf r θ) (coverPatch_quadruple r θ)

/-- The coefficient category and Ext universe are those of actual sheaf cohomology. -/
local instance schemeSheavesHasExt (X : Scheme.{0}) :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}) :=
  HasExt.standard _

theorem singleton_H_one_subsingleton (r θ : ℂ) (i : Fin 4) :
    Subsingleton ((additiveSheaf r θ).H' 1 (coverFamily r θ i)) := by
  have h := coverPatch_H_one_subsingleton r θ {i} (by simp)
  simpa only [coverPatch_singleton] using h

theorem literal_cover : (⨆ i : Fin 4, coverFamily 57 1 i) = ⊤ :=
  projective_four_cover 57 1 (by norm_num)

end CycleQ2ProjectiveCartierIntersections
end

end


section

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2ProjectiveCartierDerived

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
  CycleQ2GeometricCartierNormalLift CycleQ2CartierProjectiveCover
  CycleQ2ProjectiveCartierIntersections CycleQ2GeometricSheafLocalIso

abbrev CechOne (r θ : ℂ) :=
  CycleQ2CechTwoToDerived.One (additiveSheaf r θ) (coverFamily r θ)
abbrev CechTwo (r θ : ℂ) :=
  CycleQ2CechTwoToDerived.Two (additiveSheaf r θ) (coverFamily r θ)

/-- The six actual projective section values in the generic intersection convention. -/
def toOne (r θ : ℂ) (c : CycleQ2ProjectiveCartierCochain.One r θ) : CechOne r θ :=
  ⟨pairSectionsEquiv r θ 0 1 c.1, pairSectionsEquiv r θ 0 2 c.2.1,
   pairSectionsEquiv r θ 0 3 c.2.2.1, pairSectionsEquiv r θ 1 2 c.2.2.2.1,
   pairSectionsEquiv r θ 1 3 c.2.2.2.2.1, pairSectionsEquiv r θ 2 3 c.2.2.2.2.2⟩

def fromOne (r θ : ℂ) (c : CechOne r θ) : CycleQ2ProjectiveCartierCochain.One r θ :=
  ⟨(pairSectionsEquiv r θ 0 1).symm c.1, (pairSectionsEquiv r θ 0 2).symm c.2.1,
   (pairSectionsEquiv r θ 0 3).symm c.2.2.1, (pairSectionsEquiv r θ 1 2).symm c.2.2.2.1,
   (pairSectionsEquiv r θ 1 3).symm c.2.2.2.2.1,
   (pairSectionsEquiv r θ 2 3).symm c.2.2.2.2.2⟩

@[simp] theorem toOne_fromOne (r θ : ℂ) (c : CechOne r θ) : toOne r θ (fromOne r θ c) = c := by
  simp only [toOne, fromOne, AddEquiv.apply_symm_apply]

/-- The four actual projective section faces in the generic intersection convention. -/
def toTwo (r θ : ℂ) (c : CycleQ2ProjectiveCartierCochain.Two r θ) : CechTwo r θ :=
  ⟨tripleSectionsEquiv r θ 0 1 2 c.face012, tripleSectionsEquiv r θ 0 1 3 c.face013,
   tripleSectionsEquiv r θ 0 2 3 c.face023, tripleSectionsEquiv r θ 1 2 3 c.face123⟩

theorem toTwo_injective (r θ : ℂ) : Function.Injective (toTwo r θ) := by
  rintro ⟨a,b,c,d⟩ ⟨a',b',c',d'⟩ h
  have ha := (tripleSectionsEquiv r θ 0 1 2).injective (congrArg Prod.fst h)
  have hb := (tripleSectionsEquiv r θ 0 1 3).injective (congrArg (fun x => x.2.1) h)
  have hc := (tripleSectionsEquiv r θ 0 2 3).injective (congrArg (fun x => x.2.2.1) h)
  have hd := (tripleSectionsEquiv r θ 1 2 3).injective (congrArg (fun x => x.2.2.2) h)
  cases ha
  cases hb
  cases hc
  cases hd
  rfl

@[simp] theorem tripleSectionsEquiv_restrict_ij (r θ : ℂ) (i j k : Fin 4)
    (x : CycleQ2ProjectiveCartierCochain.Sections r θ {i,j}) :
    tripleSectionsEquiv r θ i j k
      (CycleQ2ProjectiveCartierCochain.restriction r θ
        (show ({i,j}:Finset (Fin 4)) ⊆ {i,j,k} by simp) x) =
      res (additiveSheaf r θ) inf_le_left (pairSectionsEquiv r θ i j x) :=
  sectionEquivOfOpenEq_restrict (additiveSheaf r θ)
    (coverPatch_pair r θ i j) (coverPatch_triple r θ i j k)
    (coverPatch_mono r θ (by simp)) inf_le_left x

@[simp] theorem tripleSectionsEquiv_restrict_ik (r θ : ℂ) (i j k : Fin 4)
    (x : CycleQ2ProjectiveCartierCochain.Sections r θ {i,k}) :
    tripleSectionsEquiv r θ i j k
      (CycleQ2ProjectiveCartierCochain.restriction r θ
        (show ({i,k}:Finset (Fin 4)) ⊆ {i,j,k} by simp) x) =
      res (additiveSheaf r θ) (inf_le_inf inf_le_left le_rfl) (pairSectionsEquiv r θ i k x) :=
  sectionEquivOfOpenEq_restrict (additiveSheaf r θ)
    (coverPatch_pair r θ i k) (coverPatch_triple r θ i j k)
    (coverPatch_mono r θ (by simp)) (inf_le_inf inf_le_left le_rfl) x

@[simp] theorem tripleSectionsEquiv_restrict_jk (r θ : ℂ) (i j k : Fin 4)
    (x : CycleQ2ProjectiveCartierCochain.Sections r θ {j,k}) :
    tripleSectionsEquiv r θ i j k
      (CycleQ2ProjectiveCartierCochain.restriction r θ
        (show ({j,k}:Finset (Fin 4)) ⊆ {i,j,k} by simp) x) =
      res (additiveSheaf r θ) (inf_le_inf inf_le_right le_rfl) (pairSectionsEquiv r θ j k x) :=
  sectionEquivOfOpenEq_restrict (additiveSheaf r θ)
    (coverPatch_pair r θ j k) (coverPatch_triple r θ i j k)
    (coverPatch_mono r θ (by simp)) (inf_le_inf inf_le_right le_rfl) x

theorem toTwo_oneDifferential (r θ : ℂ) (c : CycleQ2ProjectiveCartierCochain.One r θ) :
    toTwo r θ (CycleQ2ProjectiveCartierCochain.oneDifferential r θ c) =
      CycleQ2CechTwoToDerived.d1 (additiveSheaf r θ) (coverFamily r θ) (toOne r θ c) := by
  simp only [toTwo, toOne, CycleQ2ProjectiveCartierCochain.oneDifferential,
    CycleQ2CechTwoToDerived.d1, map_add, map_sub, tripleSectionsEquiv_restrict_ij,
    tripleSectionsEquiv_restrict_ik, tripleSectionsEquiv_restrict_jk]

@[simp] theorem quadrupleSectionsEquiv_restrict_012 (r θ : ℂ)
    (x : CycleQ2ProjectiveCartierCochain.Sections r θ {0,1,2}) :
    quadrupleSectionsEquiv r θ
      (CycleQ2ProjectiveCartierCochain.restriction r θ (Finset.subset_univ {0,1,2}) x) =
      res (additiveSheaf r θ) inf_le_left (tripleSectionsEquiv r θ 0 1 2 x) :=
  sectionEquivOfOpenEq_restrict (additiveSheaf r θ)
    (coverPatch_triple r θ 0 1 2) (coverPatch_quadruple r θ)
    (coverPatch_mono r θ (Finset.subset_univ {0,1,2})) inf_le_left x

@[simp] theorem quadrupleSectionsEquiv_restrict_013 (r θ : ℂ)
    (x : CycleQ2ProjectiveCartierCochain.Sections r θ {0,1,3}) :
    quadrupleSectionsEquiv r θ
      (CycleQ2ProjectiveCartierCochain.restriction r θ (Finset.subset_univ {0,1,3}) x) =
      res (additiveSheaf r θ) (inf_le_inf inf_le_left le_rfl)
        (tripleSectionsEquiv r θ 0 1 3 x) :=
  sectionEquivOfOpenEq_restrict (additiveSheaf r θ)
    (coverPatch_triple r θ 0 1 3) (coverPatch_quadruple r θ)
    (coverPatch_mono r θ (Finset.subset_univ {0,1,3})) (inf_le_inf inf_le_left le_rfl) x

@[simp] theorem quadrupleSectionsEquiv_restrict_023 (r θ : ℂ)
    (x : CycleQ2ProjectiveCartierCochain.Sections r θ {0,2,3}) :
    quadrupleSectionsEquiv r θ
      (CycleQ2ProjectiveCartierCochain.restriction r θ (Finset.subset_univ {0,2,3}) x) =
      res (additiveSheaf r θ) (inf_le_inf (inf_le_inf inf_le_left le_rfl) le_rfl)
        (tripleSectionsEquiv r θ 0 2 3 x) :=
  sectionEquivOfOpenEq_restrict (additiveSheaf r θ)
    (coverPatch_triple r θ 0 2 3) (coverPatch_quadruple r θ)
    (coverPatch_mono r θ (Finset.subset_univ {0,2,3}))
      (inf_le_inf (inf_le_inf inf_le_left le_rfl) le_rfl) x

@[simp] theorem quadrupleSectionsEquiv_restrict_123 (r θ : ℂ)
    (x : CycleQ2ProjectiveCartierCochain.Sections r θ {1,2,3}) :
    quadrupleSectionsEquiv r θ
      (CycleQ2ProjectiveCartierCochain.restriction r θ (Finset.subset_univ {1,2,3}) x) =
      res (additiveSheaf r θ) (inf_le_inf (inf_le_inf inf_le_right le_rfl) le_rfl)
        (tripleSectionsEquiv r θ 1 2 3 x) :=
  sectionEquivOfOpenEq_restrict (additiveSheaf r θ)
    (coverPatch_triple r θ 1 2 3) (coverPatch_quadruple r θ)
    (coverPatch_mono r θ (Finset.subset_univ {1,2,3}))
      (inf_le_inf (inf_le_inf inf_le_right le_rfl) le_rfl) x

theorem quadrupleSectionsEquiv_twoDifferential (r θ : ℂ)
    (c : CycleQ2ProjectiveCartierCochain.Two r θ) :
    quadrupleSectionsEquiv r θ (CycleQ2ProjectiveCartierCochain.twoDifferential r θ c) =
      CycleQ2CechTwoToDerived.d2 (additiveSheaf r θ) (coverFamily r θ) (toTwo r θ c) := by
  simp only [CycleQ2ProjectiveCartierCochain.twoDifferential, CycleQ2CechTwoToDerived.d2,
    toTwo, map_add, map_sub, quadrupleSectionsEquiv_restrict_012,
    quadrupleSectionsEquiv_restrict_013, quadrupleSectionsEquiv_restrict_023,
    quadrupleSectionsEquiv_restrict_123]

/-- The actual literal Cartier cocycle in the convention used by the
checked degree-two comparison, with its original normalization. -/
def literalCocycle : CechTwo 57 1 :=
  toTwo 57 1 CycleQ2ProjectiveCartierCochain.literalProjectiveCartierCochain

theorem literalCocycle_closed :
    CycleQ2CechTwoToDerived.d2 (additiveSheaf 57 1) (coverFamily 57 1) literalCocycle = 0 := by
  rw [literalCocycle, ← quadrupleSectionsEquiv_twoDifferential,
    CycleQ2ProjectiveCartierCochain.literalProjectiveCartierCochain_cocycle, map_zero]

theorem literalCocycle_not_boundary :
    ¬ ∃ c : CechOne 57 1,
      CycleQ2CechTwoToDerived.d1 (additiveSheaf 57 1) (coverFamily 57 1) c = literalCocycle := by
  rintro ⟨c,hc⟩
  apply CycleQ2ActualCartierNonboundary.literal_projective_cartier_not_boundary
  refine ⟨fromOne 57 1 c, ?_⟩
  apply toTwo_injective 57 1
  rw [toTwo_oneDifferential, toOne_fromOne]
  exact hc

local instance schemeSheavesHasExt (X : Scheme.{0}) :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}) :=
  HasExt.standard _

/-- The derived class of the actual literal projective Cartier cocycle,
constructed by the checked two-stage injective descent. -/
def literalDerivedClassAtTop : (additiveSheaf 57 1).H' 2 ⊤ :=
  CycleQ2CechTwoToDerived.cechTwoClass (coverFamily 57 1) literal_cover
    literalCocycle literalCocycle_closed

theorem literalDerivedClassAtTop_ne_zero : literalDerivedClassAtTop ≠ 0 :=
  CycleQ2CechTwoToDerived.cechTwoClass_ne_zero (coverFamily 57 1) literal_cover
    literalCocycle literalCocycle_closed (singleton_H_one_subsingleton 57 1)
      literalCocycle_not_boundary

/-- At the terminal open, the free representable source is the actual
constant integer sheaf, so this is ordinary derived sheaf cohomology. -/
def literalTerminalCohomologyEquiv :
    (additiveSheaf 57 1).H' 2 ⊤ ≃+ (additiveSheaf 57 1).H 2 :=
  CycleQ2GeometricSheafCohomologyRestriction.terminalCohomologyEquiv
    (Opens.grothendieckTopology (projectiveSurface 57 1))
    (additiveSheaf 57 1) ⊤ isTerminalTop 2

/-- The actual literal Cartier class in ordinary degree-two sheaf cohomology. -/
def literalDerivedClass : (additiveSheaf 57 1).H 2 :=
  literalTerminalCohomologyEquiv literalDerivedClassAtTop

theorem literalDerivedClass_ne_zero : literalDerivedClass ≠ 0 := by
  intro h
  apply literalDerivedClassAtTop_ne_zero
  apply literalTerminalCohomologyEquiv.injective
  exact h.trans (map_zero literalTerminalCohomologyEquiv).symm

theorem literal_H_two_nontrivial : Nontrivial ((additiveSheaf 57 1).H 2) :=
  ⟨⟨literalDerivedClass, 0, literalDerivedClass_ne_zero⟩⟩

end CycleQ2ProjectiveCartierDerived
end

end


section

/-! The canonical quotient comparison carries the actual literal projective
Cartier cocycle to the same nonzero derived class already constructed. -/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace CycleQ2LiteralCartierComparison

open AlgebraicGeometry CategoryTheory TopologicalSpace
  CycleQ2CartierProjectiveCover CycleQ2ProjectiveCartierIntersections
  CycleQ2ProjectiveCartierDerived CycleQ2CechTwoComparison

local instance schemeSheavesHasExt (X : Scheme.{0}) :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}) :=
  HasExt.standard _

def literalTwoCycle : twoCycles (F := additiveSheaf 57 1) (coverFamily 57 1) :=
  ⟨literalCocycle, literalCocycle_closed⟩

abbrev LiteralCechH2 :=
  CycleQ2CechTwoComparison.CechTwo (F := additiveSheaf 57 1) (coverFamily 57 1)

def literalCechClass : LiteralCechH2 := QuotientAddGroup.mk literalTwoCycle

def literalComparison : LiteralCechH2 →+ (additiveSheaf 57 1).H' 2 ⊤ :=
  comparison (coverFamily 57 1) literal_cover

theorem literalComparison_injective : Function.Injective literalComparison :=
  comparison_injective (coverFamily 57 1) literal_cover
    (singleton_H_one_subsingleton 57 1)

theorem literalComparison_class :
    literalComparison literalCechClass = literalDerivedClassAtTop := rfl

theorem literalCechClass_ne_zero : literalCechClass ≠ 0 := by
  intro h
  apply literalDerivedClassAtTop_ne_zero
  rw [← literalComparison_class, h, map_zero]

def literalOrdinaryComparison : LiteralCechH2 →+ (additiveSheaf 57 1).H 2 :=
  literalTerminalCohomologyEquiv.toAddMonoidHom.comp literalComparison

theorem literalOrdinaryComparison_injective :
    Function.Injective literalOrdinaryComparison :=
  literalTerminalCohomologyEquiv.injective.comp literalComparison_injective

theorem literalOrdinaryComparison_class :
    literalOrdinaryComparison literalCechClass = literalDerivedClass := rfl

end CycleQ2LiteralCartierComparison
end

end


section

/-!
# The same literal class in the actual scalar Čech quotient

The two independently developed four-open complexes differ only by product
parenthesization. Their restriction maps and signs are the same. This bridge
therefore puts the proved nonboundary into the shared branch's actual
second Čech cohomology quotient without changing its representative.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace CycleQ2CartierCechClass

open CycleQ2GeometricCartierNormalLift CycleQ2CartierInverseIdealCech
  CycleQ2GeometricFourOpenCech CycleQ2GeometricCartierCech

def flattenOne (r θ : ℂ) (p : OneCochain (CoverLocal r θ)) : ScalarOne r θ :=
  ⟨p.1.1, p.1.2.1, p.1.2.2, p.2.1, p.2.2.1, p.2.2.2⟩

def flattenTwo (r θ : ℂ) (p : TwoCochain (CoverLocal r θ)) : SurfaceCechTwo r θ :=
  ⟨p.1.1, p.1.2, p.2.1, p.2.2⟩

theorem flattenOne_differential (r θ : ℂ) (p : OneCochain (CoverLocal r θ)) :
    scalarOneDifferential r θ (flattenOne r θ p) =
      flattenTwo r θ (d1 (surfaceSystem r θ) p) := rfl

theorem flatten_cartierCycle (r θ : ℂ) (A L : CycleQ2SeedTrace.WeightedPoly) :
    flattenTwo r θ (cartierCycle r θ A L).val =
      cartierBoundaryTwoCochain r θ A L := rfl

/-- The original scalar Cartier class is nonzero in its actual quotient of
two-cocycles by one-cochain boundaries, at the fixed literal parameter. -/
theorem literal_cartierClass_ne_zero :
    cartierClass 57 1 CycleQ2NormalConnecting.derivativeA 0 ≠ 0 := by
  intro hz
  obtain ⟨p,hp⟩ :=
    (cartierClass_eq_zero_iff 57 1 CycleQ2NormalConnecting.derivativeA 0).mp hz
  apply CycleQ2ActualCartierNonboundary.literal_cartier_not_boundary
  refine ⟨flattenOne 57 1 p, ?_⟩
  exact congrArg (flattenTwo 57 1) hp

theorem literal_actualSecondCech_nontrivial : Nontrivial (ActualSecondCech 57 1) :=
  ⟨⟨cartierClass 57 1 CycleQ2NormalConnecting.derivativeA 0, 0,
    literal_cartierClass_ne_zero⟩⟩

end CycleQ2CartierCechClass
end

end


section

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace CycleQ2ProjectiveCurveSurface

open AlgebraicGeometry CategoryTheory MvPolynomial
  CycleQ2SeedTrace CycleQ2NormalConnecting CycleQ2ConormalJacobian
  CycleQ2GeometricSeedNormalIdeals CycleQ2GeometricCartierNormalLift
  CycleQ2CartierSurfaceGrading CycleQ2GeometricProjectiveCurve
  CycleQ2CartierProjectiveCover

/-- Weighted evaluation is homogeneous when each substituted variable has its assigned degree. -/
theorem aeval_weighted_homogeneous {n : ℕ} {p : WeightedPoly}
    (hp : p.IsWeightedHomogeneous weight n) (g : Fin 5 → Poly)
    (hg : ∀ i, (g i).IsHomogeneous (weight i)) :
    (MvPolynomial.aeval g p).IsHomogeneous n := by
  induction hp using MvPolynomial.IsWeightedHomogeneous.induction_on with
  | zero => simpa only [map_zero] using isHomogeneous_zero (Fin 4) ℂ n
  | add p q hp hq ihp ihq => simpa only [map_add] using ihp.add ihq
  | monomial d c hd =>
    rw [MvPolynomial.aeval_monomial]
    change (C c * ∏ i ∈ d.support, g i ^ d i).IsHomogeneous n
    have hprod := (MvPolynomial.IsHomogeneous.prod d.support
      (fun i => g i ^ d i) (fun i => weight i * d i)
      (fun i _ => (hg i).pow (d i))).C_mul c
    have hdegree : (∑ i ∈ d.support, weight i * d i) = n := by
      simpa only [Finsupp.weight_apply, Finsupp.sum, smul_eq_mul, Nat.mul_comm] using hd
    exact hdegree ▸ hprod

/-- The literal elimination of the weight-two coordinate preserves weighted degree. -/
theorem substitute_homogeneous {n : ℕ} {p : WeightedPoly}
    (hp : p.IsWeightedHomogeneous weight n) : (substitute p).IsHomogeneous n := by
  apply aeval_weighted_homogeneous hp
  intro i
  fin_cases i
  · exact isHomogeneous_X ℂ 0
  · exact isHomogeneous_X ℂ 1
  · exact isHomogeneous_X ℂ 2
  · exact isHomogeneous_X ℂ 3
  · exact (isHomogeneous_X_pow (2 : Fin 4) 2).neg

@[simp] theorem substitute_rename (p : Poly) :
    substitute (MvPolynomial.rename (fun j : Fin 4 => j.castSucc) p) = p := by
  have h : substitute.comp (MvPolynomial.rename (fun j : Fin 4 => j.castSucc)) =
      AlgHom.id ℂ Poly := by
    ext j
    fin_cases j <;> simp [substitute]
  exact DFunLike.congr_fun h p

/-- The actual quotient map from the containing surface cone to the curve cone. -/
def surfaceToCurve (r θ : ℂ) : SurfaceRing r θ →+* CurveRing r θ :=
  Ideal.Quotient.lift (surfaceIdeal r θ) (ambientCurveMap r θ)
    (fun p hp => CycleQ2ActualNormalCech.ambientCurveMap_kills r θ p
      (surfaceIdeal_le_curveIdeal r θ hp))

@[simp] theorem surfaceToCurve_quotient (r θ : ℂ) (p : WeightedPoly) :
    surfaceToCurve r θ (surfaceQuotient r θ p) = ambientCurveMap r θ p := rfl

theorem surfaceToCurve_surjective (r θ : ℂ) : Function.Surjective (surfaceToCurve r θ) := by
  intro q
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective q
  refine ⟨surfaceQuotient r θ (MvPolynomial.rename (fun j : Fin 4 => j.castSucc) p), ?_⟩
  change curveMap r θ (substitute (MvPolynomial.rename (fun j : Fin 4 => j.castSucc) p)) =
    curveMap r θ p
  rw [substitute_rename]

/-- The quotient map respects the actual weighted surface and ordinary curve gradings. -/
def surfaceToCurveGraded (r θ : ℂ) : surfaceGrade r θ →+*ᵍ curveGrade r θ where
  __ := surfaceToCurve r θ
  map_mem := by
    intro n q hq
    obtain ⟨p, hp, rfl⟩ := hq
    exact curveMap_mem_grade r θ (substitute_homogeneous hp)

@[simp] theorem surfaceToCurveGraded_quotient (r θ : ℂ) (p : WeightedPoly) :
    surfaceToCurveGraded r θ (surfaceQuotient r θ p) = ambientCurveMap r θ p := rfl

@[simp] theorem ambientCurveMap_X_castSucc (r θ : ℂ) (j : Fin 4) :
    ambientCurveMap r θ (X j.castSucc) = curveMap r θ (X j) := by
  fin_cases j <;> simp [ambientCurveMap, substitute]

theorem surface_coordinate_mem_grade_one (r θ : ℂ) (j : Fin 4) :
    surfaceQuotient r θ (X j.castSucc) ∈ surfaceGrade r θ 1 := by
  apply surfaceQuotient_mem_grade
  have hx := MvPolynomial.isWeightedHomogeneous_X ℂ weight j.castSucc
  fin_cases j <;> simpa [weight] using hx

/-- The positive-degree curve ideal is contained in the image of the positive-degree surface ideal. -/
theorem irrelevant_le_map (r θ : ℂ) :
    HomogeneousIdeal.irrelevant (curveGrade r θ) ≤
      (HomogeneousIdeal.irrelevant (surfaceGrade r θ)).map (surfaceToCurveGraded r θ) := by
  intro q hq
  change q ∈ Ideal.map (surfaceToCurveGraded r θ).toRingHom
    (HomogeneousIdeal.irrelevant (surfaceGrade r θ)).toIdeal
  have hspan : Ideal.span (Set.range (fun j : Fin 4 => curveMap r θ (X j))) ≤
      Ideal.map (surfaceToCurveGraded r θ).toRingHom
        (HomogeneousIdeal.irrelevant (surfaceGrade r θ)).toIdeal := by
    apply Ideal.span_le.mpr
    rintro _ ⟨j, rfl⟩
    have hj := HomogeneousIdeal.mem_irrelevant_of_mem (surfaceGrade r θ)
      (show 0 < (1 : ℕ) by decide) (surface_coordinate_mem_grade_one r θ j)
    change curveMap r θ (X j) ∈
      Ideal.map (surfaceToCurveGraded r θ).toRingHom
        (HomogeneousIdeal.irrelevant (surfaceGrade r θ)).toIdeal
    rw [← ambientCurveMap_X_castSucc r θ j]
    exact Ideal.mem_map_of_mem (surfaceToCurveGraded r θ).toRingHom hj
  exact hspan (CycleQ2GeometricProjectiveCurve.irrelevant_le_coordinateIdeal r θ hq)

/-- The actual projective curve-to-surface morphism induced by the literal equations. -/
def curveToSurface (r θ : ℂ) : projectiveCurve r θ ⟶ projectiveSurface r θ :=
  Proj.map (surfaceToCurveGraded r θ) (irrelevant_le_map r θ)

@[simp] theorem curveToSurface_preimage_basicOpen (r θ : ℂ) (a : SurfaceRing r θ) :
    curveToSurface r θ ⁻¹ᵁ Proj.basicOpen (surfaceGrade r θ) a =
      Proj.basicOpen (curveGrade r θ) (surfaceToCurve r θ a) := rfl

@[simp] theorem curveToSurface_preimage_cover_zero (r θ : ℂ) :
    curveToSurface r θ ⁻¹ᵁ coverFamily r θ 0 = firstProjectivePatch r θ := by
  change Proj.basicOpen (curveGrade r θ)
    (surfaceToCurve r θ (surfaceQuotient r θ (originalG1 r))) = _
  rfl

@[simp] theorem curveToSurface_preimage_cover_one (r θ : ℂ) :
    curveToSurface r θ ⁻¹ᵁ coverFamily r θ 1 = secondProjectivePatch r θ := by
  change Proj.basicOpen (curveGrade r θ)
    (surfaceToCurve r θ (surfaceQuotient r θ originalG2)) = _
  rfl

@[simp] theorem curveToSurface_preimage_cover_two (r θ : ℂ) :
    curveToSurface r θ ⁻¹ᵁ coverFamily r θ 2 = ⊥ := by
  change Proj.basicOpen (curveGrade r θ)
    (surfaceToCurve r θ (surfaceQuotient r θ (originalF1 r))) = _
  rw [surfaceToCurve_quotient, ambientCurveMap_f1, Proj.basicOpen_zero]
  rfl

@[simp] theorem curveToSurface_preimage_cover_three (r θ : ℂ) :
    curveToSurface r θ ⁻¹ᵁ coverFamily r θ 3 = ⊥ := by
  change Proj.basicOpen (curveGrade r θ)
    (surfaceToCurve r θ (surfaceQuotient r θ originalF2)) = _
  rw [surfaceToCurve_quotient, ambientCurveMap_f2, Proj.basicOpen_zero]
  rfl

/-- The ring map on a homogeneous affine chart is induced by the same graded quotient map. -/
def chartMap (r θ : ℂ) (a : SurfaceRing r θ) :
    HomogeneousLocalization.Away (surfaceGrade r θ) a →+*
      HomogeneousLocalization.Away (curveGrade r θ) (surfaceToCurve r θ a) :=
  HomogeneousLocalization.Away.map (surfaceToCurveGraded r θ) a

theorem chartMap_section_square (r θ : ℂ) {n : ℕ} {a : SurfaceRing r θ}
    (ha : a ∈ surfaceGrade r θ n) :
    Proj.awayToSection (surfaceGrade r θ) a ≫
      Scheme.Hom.appLE (curveToSurface r θ)
        (Proj.basicOpen (surfaceGrade r θ) a)
        (Proj.basicOpen (curveGrade r θ) (surfaceToCurve r θ a)) (by rfl) =
      CommRingCat.ofHom (chartMap r θ a) ≫
        Proj.awayToSection (curveGrade r θ) (surfaceToCurve r θ a) :=
  Proj.awayToSection_comp_appLE (surfaceToCurveGraded r θ) (irrelevant_le_map r θ) ha

theorem chartMap_scheme_square (r θ : ℂ) {n : ℕ} (hn : 0 < n)
    (a : SurfaceRing r θ) (ha : a ∈ surfaceGrade r θ n) :
    Proj.awayι (curveGrade r θ) (surfaceToCurve r θ a)
      ((surfaceToCurveGraded r θ).map_mem ha) hn ≫ curveToSurface r θ =
    Spec.map (CommRingCat.ofHom (chartMap r θ a)) ≫
      Proj.awayι (surfaceGrade r θ) a ha hn :=
  Proj.awayι_comp_map (surfaceToCurveGraded r θ) (irrelevant_le_map r θ) hn a ha

end CycleQ2ProjectiveCurveSurface
end

end


section

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace CycleQ2ProjectiveClosedImmersion

open AlgebraicGeometry CategoryTheory Opposite HomogeneousLocalization

section GradedSurjection

variable {A B : Type} [CommRing A] [CommRing B] [Algebra ℂ A] [Algebra ℂ B]
variable (𝒜 : ℕ → Submodule ℂ A) (ℬ : ℕ → Submodule ℂ B)
variable [GradedRing 𝒜] [GradedRing ℬ]
variable (f : 𝒜 →+*ᵍ ℬ) (hf : HomogeneousIdeal.irrelevant ℬ ≤
  (HomogeneousIdeal.irrelevant 𝒜).map f) (hfs : Function.Surjective f)

include hfs

/-- Surjectivity of a graded map provides a lift in the same homogeneous degree. -/
theorem homogeneous_lift (n : ℕ) (b : B) (hb : b ∈ ℬ n) :
    ∃ a : A, a ∈ 𝒜 n ∧ f a = b := by
  obtain ⟨a, ha⟩ := hfs b
  refine ⟨DirectSum.decompose 𝒜 a n, Subtype.property _, ?_⟩
  rw [GradedRingHom.map_directSumDecompose, ha, DirectSum.decompose_of_mem_same ℬ hb]

/-- A surjective graded quotient induces surjections on its degree-zero affine chart rings. -/
theorem awayMap_surjective {n : ℕ} (a : A) (ha : a ∈ 𝒜 n) :
    Function.Surjective (HomogeneousLocalization.Away.map f a) := by
  intro z
  obtain ⟨m, b, hb, rfl⟩ := HomogeneousLocalization.Away.mk_surjective ℬ (f.map_mem ha) z
  obtain ⟨c, hc, hfc⟩ := homogeneous_lift 𝒜 ℬ f hfs (m • n) b hb
  refine ⟨HomogeneousLocalization.Away.mk 𝒜 ha m c hc, ?_⟩
  rw [HomogeneousLocalization.Away.map_mk]
  subst b
  rfl

/-- The actual structure-sheaf map is surjective on every positive homogeneous basic open. -/
theorem basicOpen_app_surjective {n : ℕ} (hn : 0 < n) (a : A) (ha : a ∈ 𝒜 n) :
    Function.Surjective ((Proj.map f hf).app (Proj.basicOpen 𝒜 a)) := by
  intro z
  let eB := Proj.basicOpenIsoAway ℬ (f a) (f.map_mem ha) hn
  obtain ⟨x, hx⟩ := awayMap_surjective 𝒜 ℬ f hfs a ha (eB.inv z)
  refine ⟨Proj.awayToSection 𝒜 a x, ?_⟩
  have hs := Proj.awayToSection_comp_appLE f hf ha
  have he : (Proj.map f hf).appLE (Proj.basicOpen 𝒜 a)
      (Proj.basicOpen ℬ (f a)) (by rfl) =
      (Proj.map f hf).app (Proj.basicOpen 𝒜 a) :=
    Scheme.Hom.appLE_eq_app (Proj.map f hf)
  rw [he] at hs
  have hsx := ConcreteCategory.congr_hom hs x
  change (Proj.map f hf).app (Proj.basicOpen 𝒜 a) (Proj.awayToSection 𝒜 a x) =
    Proj.awayToSection ℬ (f a) (HomogeneousLocalization.Away.map f a x) at hsx
  have hz : Proj.awayToSection ℬ (f a) (eB.inv z) = z :=
    ConcreteCategory.congr_hom eB.inv_hom_id z
  exact hsx.trans ((congrArg (fun b : Away ℬ (f a) =>
    Proj.awayToSection ℬ (f a) b) hx).trans hz)

/-- A positive homogeneous basic-open restriction is a genuine closed immersion. -/
theorem basicOpen_closedImmersion {n : ℕ} (hn : 0 < n) (a : A) (ha : a ∈ 𝒜 n) :
    IsClosedImmersion ((Proj.map f hf) ∣_ Proj.basicOpen 𝒜 a) := by
  let : IsAffine (Proj.basicOpen 𝒜 a).toScheme :=
    Proj.isAffineOpen_basicOpen 𝒜 a ha hn
  let : IsAffine ((Proj.map f hf) ⁻¹ᵁ Proj.basicOpen 𝒜 a).toScheme :=
    Proj.isAffineOpen_basicOpen ℬ (f a) (f.map_mem ha) hn
  apply IsClosedImmersion.of_surjective_of_isAffine
  rw [morphismRestrict_appTop]
  apply Function.Surjective.comp
    (ConcreteCategory.bijective_of_isIso
      ((Proj ℬ).presheaf.map
        (eqToHom (image_morphismRestrict_preimage (Proj.map f hf)
          (Proj.basicOpen 𝒜 a) ⊤)).op)).2
  have hsurj : Function.Surjective
      ((Proj.map f hf).app ((Proj.basicOpen 𝒜 a).ι ''ᵁ ⊤)) := by
    rw [Scheme.Opens.ι_image_top]
    exact basicOpen_app_surjective 𝒜 ℬ f hf hfs hn a ha
  exact hsurj

/-- A surjective graded map satisfying the Proj relevance condition induces a closed immersion. -/
theorem projMap_closedImmersion : IsClosedImmersion (Proj.map f hf) := by
  let ι := Σ n : {n : ℕ // 0 < n}, 𝒜 n.1
  let U : ι → (Proj 𝒜).Opens := fun s => Proj.basicOpen 𝒜 s.2.1
  have hcover : (⨆ s, U s) = ⊤ := by
    apply Proj.iSup_basicOpen_eq_top
    apply (HomogeneousIdeal.toIdeal_irrelevant_le 𝒜).mpr
    intro n hn a ha
    exact Ideal.subset_span ⟨⟨⟨n, hn⟩, ⟨a, ha⟩⟩, rfl⟩
  apply (IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @IsClosedImmersion) U hcover).mpr
  intro s
  exact basicOpen_closedImmersion 𝒜 ℬ f hf hfs s.1.2 s.2.1 s.2.2

end GradedSurjection

open CycleQ2NormalConnecting CycleQ2GeometricSeedNormalIdeals
  CycleQ2CartierSurfaceGrading CycleQ2GeometricProjectiveCurve
  CycleQ2ProjectiveCurveSurface

/-- The actual curve defined by the literal equations is a closed subscheme of the actual surface. -/
theorem curveToSurface_isClosedImmersion (r θ : ℂ) : IsClosedImmersion (curveToSurface r θ) :=
  projMap_closedImmersion (surfaceGrade r θ) (curveGrade r θ)
    (surfaceToCurveGraded r θ) (irrelevant_le_map r θ) (surfaceToCurve_surjective r θ)

end CycleQ2ProjectiveClosedImmersion
end

end


section

/-! The actual ordinary curve ring is the quotient by the three literal
weighted curve equations. This identifies the kernel of the actual surface
quotient map with the existing ideal used by the conormal calculations. -/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace CycleQ2ActualCurveQuotient

open MvPolynomial CycleQ2SeedTrace CycleQ2SeedCechTheta CycleQ2NormalConnecting
  CycleQ2ConormalJacobian CycleQ2GeometricSeedNormalIdeals
  CycleQ2GeometricCartierNormalLift CycleQ2ProjectiveCurveSurface

abbrev AmbientCurveRing (r θ : ℂ) := WeightedPoly ⧸ ambientCurveIdeal r θ

def ambientQuotient (r θ : ℂ) : WeightedPoly →ₐ[ℂ] AmbientCurveRing r θ :=
  Ideal.Quotient.mkₐ ℂ (ambientCurveIdeal r θ)

def inclusion : Poly →ₐ[ℂ] WeightedPoly :=
  MvPolynomial.rename (fun j : Fin 4 => j.castSucc)

@[simp] theorem inclusion_relation (r : ℂ) :
    inclusion (relation r 0) = originalF1 r := by
  simp [inclusion, relation, originalF1]

@[simp] theorem inclusion_curveH (θ : ℂ) : inclusion (curveH θ) = thetaH θ := by
  simp [inclusion, curveH, h, b, thetaH, originalH, originalB]

theorem inclusion_mem (r θ : ℂ) {p : Poly} (hp : p ∈ curveIdeal r θ) :
    inclusion p ∈ ambientCurveIdeal r θ := by
  have hI : curveIdeal r θ ≤ (ambientCurveIdeal r θ).comap inclusion.toRingHom := by
    rw [curveIdeal, Ideal.span_le]
    intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl
    · change inclusion (relation r 0) ∈ ambientCurveIdeal r θ
      rw [inclusion_relation]
      exact curveEquation_mem r θ 0
    · change inclusion (curveH θ) ∈ ambientCurveIdeal r θ
      rw [inclusion_curveH]
      exact curveEquation_mem r θ 2
  exact hI hp

def forward (r θ : ℂ) : AmbientCurveRing r θ →ₐ[ℂ] CurveRing r θ :=
  Ideal.Quotient.liftₐ (ambientCurveIdeal r θ)
    (CycleQ2ActualNormalCech.ambientCurveAlg r θ)
    (CycleQ2ActualNormalCech.ambientCurveMap_kills r θ)

def backward (r θ : ℂ) : CurveRing r θ →ₐ[ℂ] AmbientCurveRing r θ :=
  Ideal.Quotient.liftₐ (curveIdeal r θ) ((ambientQuotient r θ).comp inclusion)
    (fun _p hp => Ideal.Quotient.eq_zero_iff_mem.mpr (inclusion_mem r θ hp))

@[simp] theorem forward_quotient (r θ : ℂ) (p : WeightedPoly) :
    forward r θ (ambientQuotient r θ p) = ambientCurveMap r θ p := rfl

@[simp] theorem backward_curveMap (r θ : ℂ) (p : Poly) :
    backward r θ (curveMap r θ p) = ambientQuotient r θ (inclusion p) := rfl

theorem quotient_X_four (r θ : ℂ) :
    ambientQuotient r θ (X 4) = -(ambientQuotient r θ (X 2)) ^ 2 := by
  have hf : ambientQuotient r θ originalF2 = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (curveEquation_mem r θ 1)
  simpa only [originalF2, map_add, map_pow, eq_neg_iff_add_eq_zero] using hf

theorem backward_ambientCurveMap (r θ : ℂ) (p : WeightedPoly) :
    backward r θ (ambientCurveMap r θ p) = ambientQuotient r θ p := by
  have he : (backward r θ).comp (CycleQ2ActualNormalCech.ambientCurveAlg r θ) =
      ambientQuotient r θ := by
    ext j
    change backward r θ (ambientCurveMap r θ (X j)) = ambientQuotient r θ (X j)
    fin_cases j <;> simp [ambientCurveMap, substitute, inclusion, quotient_X_four]
  exact DFunLike.congr_fun he p

theorem forward_backward (r θ : ℂ) (q : CurveRing r θ) :
    forward r θ (backward r θ q) = q := by
  obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective q
  change ambientCurveMap r θ (inclusion p) = curveMap r θ p
  change curveMap r θ (substitute (inclusion p)) = curveMap r θ p
  rw [inclusion, substitute_rename]

theorem backward_forward (r θ : ℂ) (q : AmbientCurveRing r θ) :
    backward r θ (forward r θ q) = q := by
  obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective q
  exact backward_ambientCurveMap r θ p

def curveQuotientEquiv (r θ : ℂ) : AmbientCurveRing r θ ≃ₐ[ℂ] CurveRing r θ :=
  AlgEquiv.ofAlgHom (forward r θ) (backward r θ)
    (AlgHom.ext (forward_backward r θ)) (AlgHom.ext (backward_forward r θ))

theorem ambientCurveMap_kernel (r θ : ℂ) :
    RingHom.ker (ambientCurveMap r θ) = ambientCurveIdeal r θ := by
  have he : ambientCurveMap r θ =
      (forward r θ).toRingHom.comp (ambientQuotient r θ).toRingHom := rfl
  rw [he, RingHom.ker_comp_of_injective _ (curveQuotientEquiv r θ).injective]
  exact Ideal.Quotient.mkₐ_ker ℂ (ambientCurveIdeal r θ)

/-- The kernel of the actual graded surface-to-curve map is the actual ideal
already used by the relative conormal and inverse-ideal constructions. -/
theorem surfaceToCurve_kernel (r θ : ℂ) :
    RingHom.ker (surfaceToCurve r θ) = curveIdealOnSurface r θ := by
  calc
    RingHom.ker (surfaceToCurve r θ) =
        (RingHom.ker (ambientCurveMap r θ)).map (Ideal.Quotient.mk (surfaceIdeal r θ)) :=
      Ideal.ker_quotient_lift (ambientCurveMap r θ) _
    _ = curveIdealOnSurface r θ := by
      rw [ambientCurveMap_kernel]
      rfl

end CycleQ2ActualCurveQuotient
end

end
