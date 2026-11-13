import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Proposal.GeometricProjectiveCurve

/-!
# The actual degree-one sheaf as a sheaf of structure-ring modules

This continuation equips the *existing* additive kernel sheaf with its
structure-sheaf action. It does not replace its sections or its Cech classes.

On an open `O`, a section is the compatible pair `(p₁,p₂)` already constructed
in `GeometricProjectiveCurve`. A scalar `a` in `R(O)` acts by
`(a|_(O ∩ U) * p₁, a|_(O ∩ V) * p₂)`. Compatibility follows from the
commutative-ring identity `a * (t * b) = t * (a * b)` and functoriality of
restriction. The action is transported to the existing categorical kernel
through its proved `sectionPairsEquiv`.

The file then bundles the result in mathlib's `SheafOfModules`, proves that
forgetting the action recovers the original additive sheaf, and upgrades
both existing local frames to linear equivalences, natural on all subopens.
The actual transition unit remains `x₂/x₁`.

This is not an adjunction or Serre-duality theorem. In particular, it does
not identify this module sheaf with the canonical sheaf, produce the moving
cycle, or discharge `Submission.missing_geometric_existence`.

Validation status of this continuation: source implementation; not compiled
or kernel-replayed in the delivery sandbox. Its parent projective-sheaf
module also retains its separately documented validation limitations.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2GeometricProjectiveCurve

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

namespace TwistedModule

open Twisted

variable {X : TopCat.{0}}
variable (R : X.Sheaf CommRingCat.{0})
variable (U V W : Opens X) (hW : W = U ⊓ V)
variable (t : (R.obj.obj (op W))ˣ)

/-- Scalar multiplication on the existing compatible-pair group. Both
restrictions of the scalar are retained. -/
def pairSMul (O : Opens X) (a : R.obj.obj (op O))
    (p : Pairs R U V W hW t O) : Pairs R U V W hW t O :=
  ⟨(res R (show O ⊓ U ≤ O from inf_le_left) a * p.val.1,
    res R (show O ⊓ V ≤ O from inf_le_left) a * p.val.2), by
    have hp :
        res R (inf_le_inf_left O (hW.le.trans inf_le_left)) p.val.1 =
          res R (show O ⊓ W ≤ W from inf_le_right) (t : _) *
            res R (inf_le_inf_left O (hW.le.trans inf_le_right)) p.val.2 :=
      sub_eq_zero.mp p.property
    change
      res R (inf_le_inf_left O (hW.le.trans inf_le_left))
          (res R (show O ⊓ U ≤ O from inf_le_left) a * p.val.1) -
        res R (show O ⊓ W ≤ W from inf_le_right) (t : _) *
          res R (inf_le_inf_left O (hW.le.trans inf_le_right))
            (res R (show O ⊓ V ≤ O from inf_le_left) a * p.val.2) = 0
    rw [map_mul, map_mul, res_comp, res_comp, hp]
    ring⟩

/-- The scalar laws are proved on the literal compatible pairs. -/
instance pairsModule (O : Opens X) :
    Module (R.obj.obj (op O)) (Pairs R U V W hW t O) where
  smul := pairSMul R U V W hW t O
  one_smul p := by
    apply Subtype.ext
    apply Prod.ext <;> simp only [pairSMul, map_one, one_mul]
  mul_smul a b p := by
    apply Subtype.ext
    apply Prod.ext <;> simp only [pairSMul, map_mul, mul_assoc]
  smul_zero a := by
    apply Subtype.ext
    apply Prod.ext <;> simp only [pairSMul, mul_zero]
  smul_add a p q := by
    apply Subtype.ext
    apply Prod.ext <;> simp only [pairSMul, mul_add]
  add_smul a b p := by
    apply Subtype.ext
    apply Prod.ext <;> simp only [pairSMul, map_add, add_mul]
  zero_smul p := by
    apply Subtype.ext
    apply Prod.ext <;> simp only [pairSMul, map_zero, zero_mul]

@[simp] theorem pair_smul_fst (O : Opens X) (a : R.obj.obj (op O))
    (p : Pairs R U V W hW t O) :
    (a • p).val.1 = res R (show O ⊓ U ≤ O from inf_le_left) a * p.val.1 := rfl

@[simp] theorem pair_smul_snd (O : Opens X) (a : R.obj.obj (op O))
    (p : Pairs R U V W hW t O) :
    (a • p).val.2 = res R (show O ⊓ V ≤ O from inf_le_left) a * p.val.2 := rfl

/-- The action on the original kernel sections, not on a replacement sheaf. -/
def sectionSMul (O : Opens X) (a : R.obj.obj (op O))
    (s : (sheaf R U V W hW t).obj.obj (op O)) :
    (sheaf R U V W hW t).obj.obj (op O) :=
  (sectionPairsEquiv R U V W hW t O).symm
    (a • sectionPairsEquiv R U V W hW t O s)

instance sectionsModule (O : Opens X) :
    Module (R.obj.obj (op O)) ((sheaf R U V W hW t).obj.obj (op O)) := by
  letI : SMul (R.obj.obj (op O)) ((sheaf R U V W hW t).obj.obj (op O)) :=
    ⟨sectionSMul R U V W hW t O⟩
  exact Function.Injective.module (R.obj.obj (op O))
    (sectionPairsEquiv R U V W hW t O).toAddMonoidHom
    (sectionPairsEquiv R U V W hW t O).injective
    (fun _ _ => (sectionPairsEquiv R U V W hW t O).apply_symm_apply _)

@[simp] theorem sectionPairs_smul (O : Opens X) (a : R.obj.obj (op O))
    (s : (sheaf R U V W hW t).obj.obj (op O)) :
    sectionPairsEquiv R U V W hW t O (a • s) =
      a • sectionPairsEquiv R U V W hW t O s :=
  (sectionPairsEquiv R U V W hW t O).apply_symm_apply _

@[simp] theorem sectionPairs_fst_smul (O : Opens X) (a : R.obj.obj (op O))
    (s : (sheaf R U V W hW t).obj.obj (op O)) :
    (sectionPairsEquiv R U V W hW t O (a • s)).val.1 =
      res R (show O ⊓ U ≤ O from inf_le_left) a *
        (sectionPairsEquiv R U V W hW t O s).val.1 := by
  rw [sectionPairs_smul, pair_smul_fst]

@[simp] theorem sectionPairs_snd_smul (O : Opens X) (a : R.obj.obj (op O))
    (s : (sheaf R U V W hW t).obj.obj (op O)) :
    (sectionPairsEquiv R U V W hW t O (a • s)).val.2 =
      res R (show O ⊓ V ≤ O from inf_le_left) a *
        (sectionPairsEquiv R U V W hW t O s).val.2 := by
  rw [sectionPairs_smul, pair_smul_snd]

/-- Every existing additive restriction is semilinear over the actual
structure-sheaf restriction. No constant-scalar simplification is made. -/
theorem restriction_smul {O P : Opens X} (h : P ≤ O)
    (a : R.obj.obj (op O)) (s : (sheaf R U V W hW t).obj.obj (op O)) :
    (sheaf R U V W hW t).obj.map (homOfLE h).op (a • s) =
      res R h a • (sheaf R U V W hW t).obj.map (homOfLE h).op s := by
  apply (sectionPairsEquiv R U V W hW t P).injective
  apply Subtype.ext
  apply Prod.ext
  · simp only [sectionPairs_fst_naturality, sectionPairs_fst_smul, map_mul, res_comp]
  · simp only [sectionPairs_snd_naturality, sectionPairs_snd_smul, map_mul, res_comp]

/-- Forget commutativity only to use mathlib's ring-valued module-sheaf API. -/
def ringSheaf : X.Sheaf RingCat.{0} :=
  (sheafCompose _ (forget₂ CommRingCat RingCat)).obj R

/-- Bundle the existing sections and restrictions as a presheaf of modules. -/
def modulePresheaf : PresheafOfModules.{0} (ringSheaf R).obj :=
  PresheafOfModules.ofPresheaf (sheaf R U V W hW t).obj (by
    intro O P f a s
    have hf : f = (homOfLE (leOfHom f.unop)).op := Subsingleton.elim _ _
    have hs := restriction_smul R U V W hW t (leOfHom f.unop) a s
    change
      (sheaf R U V W hW t).obj.map (homOfLE (leOfHom f.unop)).op (a • s) =
        R.obj.map (homOfLE (leOfHom f.unop)).op a •
          (sheaf R U V W hW t).obj.map (homOfLE (leOfHom f.unop)).op s at hs
    rw [← hf] at hs
    exact hs)

/-- The sheaf condition is inherited from the existing additive sheaf,
not introduced as an additional assumption. -/
def moduleSheaf : SheafOfModules.{0} (ringSheaf R) where
  val := modulePresheaf R U V W hW t
  isSheaf := (sheaf R U V W hW t).property

/-- Forgetting the module structure gives exactly the original additive
sheaf, so earlier section and cohomology constructions retain their objects. -/
theorem moduleSheaf_toSheaf :
    (SheafOfModules.toSheaf (ringSheaf R)).obj (moduleSheaf R U V W hW t) =
      sheaf R U V W hW t := rfl

/-- The original compatible-pair equivalence is now linear. -/
def sectionPairsLinearEquiv (O : Opens X) :
    (sheaf R U V W hW t).obj.obj (op O) ≃ₗ[R.obj.obj (op O)]
      Pairs R U V W hW t O where
  toAddEquiv := sectionPairsEquiv R U V W hW t O
  map_smul' := sectionPairs_smul R U V W hW t O

/-- The original first frame is linear on every subopen of the first chart. -/
theorem firstLocalSections_smul (O : Opens X) (hO : O ≤ U)
    (a : R.obj.obj (op O)) (s : (sheaf R U V W hW t).obj.obj (op O)) :
    firstLocalSectionsEquiv R U V W hW t O hO (a • s) =
      a * firstLocalSectionsEquiv R U V W hW t O hO s := by
  simp only [firstLocalSectionsEquiv_apply, sectionPairs_fst_smul,
    map_mul, res_comp, res_self]

/-- The original second frame is linear on every subopen of the second chart. -/
theorem secondLocalSections_smul (O : Opens X) (hO : O ≤ V)
    (a : R.obj.obj (op O)) (s : (sheaf R U V W hW t).obj.obj (op O)) :
    secondLocalSectionsEquiv R U V W hW t O hO (a • s) =
      a * secondLocalSectionsEquiv R U V W hW t O hO s := by
  simp only [secondLocalSectionsEquiv_apply, sectionPairs_snd_smul,
    map_mul, res_comp, res_self]

def firstLocalSectionsLinearEquiv (O : Opens X) (hO : O ≤ U) :
    (sheaf R U V W hW t).obj.obj (op O) ≃ₗ[R.obj.obj (op O)]
      R.obj.obj (op O) where
  toAddEquiv := firstLocalSectionsEquiv R U V W hW t O hO
  map_smul' := firstLocalSections_smul R U V W hW t O hO

def secondLocalSectionsLinearEquiv (O : Opens X) (hO : O ≤ V) :
    (sheaf R U V W hW t).obj.obj (op O) ≃ₗ[R.obj.obj (op O)]
      R.obj.obj (op O) where
  toAddEquiv := secondLocalSectionsEquiv R U V W hW t O hO
  map_smul' := secondLocalSections_smul R U V W hW t O hO

/-- Linear frames retain the original restriction maps on all subopens. -/
theorem firstLinearFrame_naturality {O P : Opens X} (h : P ≤ O) (hO : O ≤ U)
    (s : (sheaf R U V W hW t).obj.obj (op O)) :
    firstLocalSectionsLinearEquiv R U V W hW t P (h.trans hO)
        ((sheaf R U V W hW t).obj.map (homOfLE h).op s) =
      res R h (firstLocalSectionsLinearEquiv R U V W hW t O hO s) :=
  firstLocalSectionsEquiv_naturality R U V W hW t h hO s

theorem secondLinearFrame_naturality {O P : Opens X} (h : P ≤ O) (hO : O ≤ V)
    (s : (sheaf R U V W hW t).obj.obj (op O)) :
    secondLocalSectionsLinearEquiv R U V W hW t P (h.trans hO)
        ((sheaf R U V W hW t).obj.map (homOfLE h).op s) =
      res R h (secondLocalSectionsLinearEquiv R U V W hW t O hO s) :=
  secondLocalSectionsEquiv_naturality R U V W hW t h hO s

/-- The newly linear frames have the very same transition unit. -/
theorem linearFrame_transition (O : Opens X) (hO : O ≤ W)
    (s : (sheaf R U V W hW t).obj.obj (op O)) :
    firstLocalSectionsLinearEquiv R U V W hW t O
        (hO.trans (hW.le.trans inf_le_left)) s =
      res R hO (t : _) * secondLocalSectionsLinearEquiv R U V W hW t O
        (hO.trans (hW.le.trans inf_le_right)) s :=
  localSections_transition R U V W hW t O hO s

end TwistedModule

/-- The actual degree-one sheaf on the actual projective curve, now with
its structure-sheaf module structure. -/
def degreeOneModuleSheaf (r θ : ℂ) :
    SheafOfModules.{0} (TwistedModule.ringSheaf (projectiveCurve r θ).sheaf) :=
  TwistedModule.moduleSheaf (projectiveCurve r θ).sheaf
    (firstProjectivePatch r θ) (secondProjectivePatch r θ) (overlapProjectivePatch r θ)
    (overlapProjectivePatch_eq r θ) (projectiveTransitionUnit r θ)

theorem degreeOneModuleSheaf_toSheaf (r θ : ℂ) :
    (SheafOfModules.toSheaf (TwistedModule.ringSheaf (projectiveCurve r θ).sheaf)).obj
        (degreeOneModuleSheaf r θ) = degreeOneSheaf r θ := rfl

/-- A specialized instance makes the scalar structure explicit at the
existing public `degreeOneSheaf` interface. It is the same transported action. -/
instance degreeOneSectionsModule (r θ : ℂ) (O : (projectiveCurve r θ).Opens) :
    Module Γ(projectiveCurve r θ, O) ((degreeOneSheaf r θ).obj.obj (op O)) :=
  TwistedModule.sectionsModule (projectiveCurve r θ).sheaf
    (firstProjectivePatch r θ) (secondProjectivePatch r θ) (overlapProjectivePatch r θ)
    (overlapProjectivePatch_eq r θ) (projectiveTransitionUnit r θ) O

/-- On each actual covering chart, and every subopen of it, the original
section group is a free rank-one module, exhibited by a linear frame.
The naturality theorems above retain the full local trivialization data. -/
theorem degreeOne_linear_frames (r θ : ℂ) :
    (∀ (O : (projectiveCurve r θ).Opens) (hO : O ≤ firstProjectivePatch r θ),
      Nonempty ((degreeOneSheaf r θ).obj.obj (op O) ≃ₗ[Γ(projectiveCurve r θ, O)]
        Γ(projectiveCurve r θ, O))) ∧
    (∀ (O : (projectiveCurve r θ).Opens) (hO : O ≤ secondProjectivePatch r θ),
      Nonempty ((degreeOneSheaf r θ).obj.obj (op O) ≃ₗ[Γ(projectiveCurve r θ, O)]
        Γ(projectiveCurve r θ, O))) := by
  constructor
  · intro O hO
    exact ⟨TwistedModule.firstLocalSectionsLinearEquiv (projectiveCurve r θ).sheaf
      (firstProjectivePatch r θ) (secondProjectivePatch r θ) (overlapProjectivePatch r θ)
      (overlapProjectivePatch_eq r θ) (projectiveTransitionUnit r θ) O hO⟩
  · intro O hO
    exact ⟨TwistedModule.secondLocalSectionsLinearEquiv (projectiveCurve r θ).sheaf
      (firstProjectivePatch r θ) (secondProjectivePatch r θ) (overlapProjectivePatch r θ)
      (overlapProjectivePatch_eq r θ) (projectiveTransitionUnit r θ) O hO⟩

/-- The proved two-open cover makes the linear frames genuinely local at
every point of the actual projective curve. This does not assume a cover or
an unidentified line bundle as extra geometric input. -/
theorem degreeOne_local_frames_cover (r θ : ℂ) (hr : r ≠ 0)
    (x : projectiveCurve r θ) :
    ∃ O : (projectiveCurve r θ).Opens, x ∈ O ∧
      ∀ (P : (projectiveCurve r θ).Opens), P ≤ O →
        Nonempty ((degreeOneSheaf r θ).obj.obj (op P) ≃ₗ[Γ(projectiveCurve r θ, P)]
          Γ(projectiveCurve r θ, P)) := by
  have hx : x ∈ firstProjectivePatch r θ ⊔ secondProjectivePatch r θ := by
    rw [projective_twoOpen_cover r θ hr]
    trivial
  rcases (show x ∈ firstProjectivePatch r θ ∨ x ∈ secondProjectivePatch r θ from hx) with
    hx | hx
  · exact ⟨firstProjectivePatch r θ, hx, (degreeOne_linear_frames r θ).1⟩
  · exact ⟨secondProjectivePatch r θ, hx, (degreeOne_linear_frames r θ).2⟩

end CycleQ2GeometricProjectiveCurve

end
