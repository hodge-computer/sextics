import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Proposal.GeometricTwistedSheaf

/-!
# The scalar action on the actual twisted kernel sheaf

The structure ring acts componentwise on compatible pairs. Transport through
the proved section-pair equivalence equips the original additive kernel with
a module structure, whose restrictions are semilinear over ring restrictions.
The resulting sheaf of modules forgets to exactly that additive kernel. Both
existing local frames are linear and retain their transition unit.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2GeometricProjectiveCurve

open CategoryTheory Opposite TopologicalSpace

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
    change pairSMul R U V W hW t O 1 p = p
    apply Subtype.ext
    apply Prod.ext <;> simp only [pairSMul, map_one, one_mul]
  mul_smul a b p := by
    change pairSMul R U V W hW t O (a * b) p =
      pairSMul R U V W hW t O a (pairSMul R U V W hW t O b p)
    apply Subtype.ext
    apply Prod.ext <;> simp only [pairSMul, map_mul, mul_assoc]
  smul_zero a := by
    change pairSMul R U V W hW t O a 0 = 0
    apply Subtype.ext
    apply Prod.ext <;> simp [pairSMul]
  smul_add a p q := by
    change pairSMul R U V W hW t O a (p + q) =
      pairSMul R U V W hW t O a p + pairSMul R U V W hW t O a q
    apply Subtype.ext
    apply Prod.ext <;> simp [pairSMul, mul_add]
  add_smul a b p := by
    change pairSMul R U V W hW t O (a + b) p =
      pairSMul R U V W hW t O a p + pairSMul R U V W hW t O b p
    apply Subtype.ext
    apply Prod.ext <;> simp [pairSMul, add_mul]
  zero_smul p := by
    change pairSMul R U V W hW t O 0 p = 0
    apply Subtype.ext
    apply Prod.ext <;> simp [pairSMul]

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
def modulePresheaf : PresheafOfModules.{0} (ringSheaf R).obj := by
  letI (O : (Opens X)ᵒᵖ) : Module ((ringSheaf R).obj.obj O)
      ((sheaf R U V W hW t).obj.obj O) :=
    sectionsModule R U V W hW t O.unop
  exact PresheafOfModules.ofPresheaf (sheaf R U V W hW t).obj (by
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

end CycleQ2GeometricProjectiveCurve

end
