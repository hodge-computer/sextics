import Proposal.GeometricSheafHZero
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.Topology.Sheaves.Functors

/-!
# The sheaf obtained by gluing two frames with a transition unit

This is the original additive kernel sheaf from `GeometricProjectiveCurve`,
independent of the projective-coordinate construction. Its actual sections
are compatible pairs. Restricting to either chart gives an additive frame,
and the two frames have the prescribed transition on every overlap open.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

noncomputable section

namespace CycleQ2GeometricProjectiveCurve

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace Twisted

variable {X : TopCat.{0}}

local instance : Abelian (X.Sheaf AddCommGrpCat.{0}) :=
  inferInstanceAs (Abelian (CategoryTheory.Sheaf (Opens.grothendieckTopology X)
    AddCommGrpCat.{0}))

/-- Intersecting every test open with a fixed open, with strict objects. -/
def intersectFunctor (U : Opens X) : Opens X ⥤ Opens X where
  obj O := O ⊓ U
  map f := homOfLE (inf_le_inf_right U (leOfHom f))

def intersectFunctorIso (U : Opens X) :
    Opens.map U.inclusion' ⋙ U.isOpenEmbedding.functor ≅ intersectFunctor U :=
  NatIso.ofComponents
    (fun O => eqToIso (TopologicalSpace.Opens.functor_map_eq_inf U O))
    (fun {_ _} _ => Subsingleton.elim _ _)

variable (R : X.Sheaf CommRingCat.{0})

/-- The genuine restriction followed by direct image, presented with
sections over O equal to sections of R over O intersect U. -/
def patchRing (U : Opens X) : X.Sheaf CommRingCat.{0} := by
  let F := (TopCat.Sheaf.pushforward CommRingCat U.inclusion').obj
    ((U.sheafRestrict).obj R)
  have e : F.obj ≅ (intersectFunctor U).op ⋙ R.obj :=
    Functor.isoWhiskerRight (NatIso.op (intersectFunctorIso U).symm) R.obj
  exact ⟨(intersectFunctor U).op ⋙ R.obj,
    (CategoryTheory.Presheaf.isSheaf_of_iso_iff e).mp F.property⟩

def patchAdd (U : Opens X) : X.Sheaf AddCommGrpCat.{0} :=
  (sheafCompose _ (forget₂ CommRingCat RingCat ⋙
    forget₂ RingCat AddCommGrpCat)).obj (patchRing R U)

def res {U V : Opens X} (h : V ≤ U) :
    R.obj.obj (op U) →+* R.obj.obj (op V) :=
  (R.obj.map (homOfLE h).op).hom

@[simp] theorem res_self (U : Opens X) (a : R.obj.obj (op U)) :
    res R (le_refl U) a = a := by
  change (R.obj.map (𝟙 (op U))) a = a
  simp

theorem res_comp {U V W : Opens X} (hVU : V ≤ U) (hWV : W ≤ V)
    (a : R.obj.obj (op U)) :
    res R hWV (res R hVU a) = res R (hWV.trans hVU) a := by
  change (R.obj.map (homOfLE hVU).op ≫ R.obj.map (homOfLE hWV).op) a =
    (R.obj.map (homOfLE (hWV.trans hVU)).op) a
  rw [← R.obj.map_comp] <;>
    exact congrArg (fun k : op U ⟶ op W => R.obj.map k a) (Subsingleton.elim _ _)

def resEquiv {U V : Opens X} (hVU : V ≤ U) (hUV : U ≤ V) :
    R.obj.obj (op U) ≃+* R.obj.obj (op V) where
  toFun := res R hVU
  invFun := res R hUV
  left_inv a := by rw [res_comp]; exact res_self R U a
  right_inv a := by rw [res_comp]; exact res_self R V a
  map_add' := map_add (res R hVU)
  map_mul' := map_mul (res R hVU)

def patchRestriction {U V : Opens X} (h : V ≤ U) :
    patchRing R U ⟶ patchRing R V where
  hom :=
    { app := fun O => R.obj.map (homOfLE (inf_le_inf_left O.unop h)).op
      naturality := by
        intro O P f
        change R.obj.map _ ≫ R.obj.map _ = R.obj.map _ ≫ R.obj.map _
        rw [← R.obj.map_comp, ← R.obj.map_comp] <;>
          congr 1 <;> apply Subsingleton.elim }

def patchAddRestriction {U V : Opens X} (h : V ≤ U) :
    patchAdd R U ⟶ patchAdd R V :=
  (sheafCompose _ (forget₂ CommRingCat RingCat ⋙
    forget₂ RingCat AddCommGrpCat)).map (patchRestriction R h)

/-- Multiplication uses the restriction of one actual overlap section. -/
def patchMul (W : Opens X) (t : R.obj.obj (op W)) :
    patchAdd R W ⟶ patchAdd R W where
  hom :=
    { app := fun O => AddCommGrpCat.ofHom
        (AddMonoidHom.mulLeft (res R (show O.unop ⊓ W ≤ W from inf_le_right) t))
      naturality := by
        intro O P f
        apply AddCommGrpCat.ext
        intro a
        change R.obj.obj (op (O.unop ⊓ W)) at a
        change res R (show P.unop ⊓ W ≤ W from inf_le_right) t *
            res R (inf_le_inf_right W (leOfHom f.unop)) a =
          res R (inf_le_inf_right W (leOfHom f.unop))
            (res R (show O.unop ⊓ W ≤ W from inf_le_right) t * a)
        rw [map_mul, res_comp] }

variable (U V W : Opens X) (hW : W = U ⊓ V)
  (t : (R.obj.obj (op W))ˣ)

def difference : patchAdd R U ⊞ patchAdd R V ⟶ patchAdd R W :=
  biprod.desc (patchAddRestriction R (hW.le.trans inf_le_left))
    (-(patchAddRestriction R (hW.le.trans inf_le_right) ≫ patchMul R W (t : _)))

/-- An actual sheaf kernel, with gluing equation a = t*b on the overlap. -/
def sheaf : X.Sheaf AddCommGrpCat.{0} :=
  kernel (difference R U V W hW t)

def firstProjection : sheaf R U V W hW t ⟶ patchAdd R U :=
  kernel.ι (difference R U V W hW t) ≫ biprod.fst

def secondProjection : sheaf R U V W hW t ⟶ patchAdd R V :=
  kernel.ι (difference R U V W hW t) ≫ biprod.snd

theorem projections_compatible :
    firstProjection R U V W hW t ≫
        patchAddRestriction R (hW.le.trans inf_le_left) =
      secondProjection R U V W hW t ≫
        patchAddRestriction R (hW.le.trans inf_le_right) ≫ patchMul R W (t : _) := by
  apply sub_eq_zero.mp
  simpa only [firstProjection, secondProjection, difference, biprod.desc_eq,
    Preadditive.comp_add, Preadditive.comp_neg, Category.assoc, sub_eq_add_neg]
    using kernel.condition (difference R U V W hW t)

def pairDifference (O : Opens X) :
    R.obj.obj (op (O ⊓ U)) × R.obj.obj (op (O ⊓ V)) →+
      R.obj.obj (op (O ⊓ W)) :=
  (res R (inf_le_inf_left O (hW.le.trans inf_le_left))).toAddMonoidHom.comp
      (AddMonoidHom.fst _ _) -
    (AddMonoidHom.mulLeft (res R (show O ⊓ W ≤ W from inf_le_right) (t : _))).comp
      ((res R (inf_le_inf_left O (hW.le.trans inf_le_right))).toAddMonoidHom.comp
        (AddMonoidHom.snd _ _))

abbrev Pairs (O : Opens X) :=
  (pairDifference R U V W hW t O).ker

theorem section_pair_mem (O : Opens X) (s : (sheaf R U V W hW t).obj.obj (op O)) :
    ((firstProjection R U V W hW t).hom.app (op O) s,
      (secondProjection R U V W hW t).hom.app (op O) s) ∈
        Pairs R U V W hW t O := by
  have hs := congrArg
    (fun k : sheaf R U V W hW t ⟶ patchAdd R W => k.hom.app (op O) s)
    (projections_compatible R U V W hW t)
  change res R (inf_le_inf_left O (hW.le.trans inf_le_left))
      ((firstProjection R U V W hW t).hom.app (op O) s) =
    res R (show O ⊓ W ≤ W from inf_le_right) (t : _) *
      res R (inf_le_inf_left O (hW.le.trans inf_le_right))
        ((secondProjection R U V W hW t).hom.app (op O) s) at hs
  exact sub_eq_zero.mpr hs

def sectionPairMap (O : Opens X) :
    (sheaf R U V W hW t).obj.obj (op O) →+ Pairs R U V W hW t O :=
  (((firstProjection R U V W hW t).hom.app (op O)).hom.prod
    ((secondProjection R U V W hW t).hom.app (op O)).hom).codRestrict _
      (section_pair_mem R U V W hW t O)

/-! Evaluation of the actual kernel uses the free sheaf representing
sections. This makes the comparison independent of chosen categorical
models for kernels and biproducts. -/

def sectionsHomEquiv (F : X.Sheaf AddCommGrpCat.{0}) (O : Opens X) :
    ((presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat).obj
      (yoneda.obj O ⋙ AddCommGrpCat.free) ⟶ F) ≃+ F.obj.obj (op O) :=
  ((sheafificationAdjunction (Opens.grothendieckTopology X) AddCommGrpCat).homAddEquiv
    (yoneda.obj O ⋙ AddCommGrpCat.free) F).trans
      (CycleQ2GeometricConeCech.HZero.freeYonedaSections F.obj O)

theorem sectionsHomEquiv_comp {F G : X.Sheaf AddCommGrpCat.{0}} (O : Opens X)
    (a : (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat).obj
      (yoneda.obj O ⋙ AddCommGrpCat.free) ⟶ F) (f : F ⟶ G) :
    sectionsHomEquiv G O (a ≫ f) =
      f.hom.app (op O) (sectionsHomEquiv F O a) := by
  exact congrArg (CycleQ2GeometricConeCech.HZero.freeYonedaSections G.obj O)
    ((sheafificationAdjunction (Opens.grothendieckTopology X)
      AddCommGrpCat).homEquiv_naturality_right a f)

theorem sectionPairMap_injective (O : Opens X) :
    Function.Injective (sectionPairMap R U V W hW t O) := by
  intro s s' h
  apply (sectionsHomEquiv (sheaf R U V W hW t) O).symm.injective
  apply (cancel_mono (kernel.ι (difference R U V W hW t))).mp
  apply biprod.hom_ext
  · apply (sectionsHomEquiv (patchAdd R U) O).injective
    simp only [Category.assoc]
    change sectionsHomEquiv (patchAdd R U) O
        ((sectionsHomEquiv (sheaf R U V W hW t) O).symm s ≫
          firstProjection R U V W hW t) =
      sectionsHomEquiv (patchAdd R U) O
        ((sectionsHomEquiv (sheaf R U V W hW t) O).symm s' ≫
          firstProjection R U V W hW t)
    rw [sectionsHomEquiv_comp, sectionsHomEquiv_comp,
      AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
    exact congrArg (fun p : Pairs R U V W hW t O => p.val.1) h
  · apply (sectionsHomEquiv (patchAdd R V) O).injective
    simp only [Category.assoc]
    change sectionsHomEquiv (patchAdd R V) O
        ((sectionsHomEquiv (sheaf R U V W hW t) O).symm s ≫
          secondProjection R U V W hW t) =
      sectionsHomEquiv (patchAdd R V) O
        ((sectionsHomEquiv (sheaf R U V W hW t) O).symm s' ≫
          secondProjection R U V W hW t)
    rw [sectionsHomEquiv_comp, sectionsHomEquiv_comp,
      AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
    exact congrArg (fun p : Pairs R U V W hW t O => p.val.2) h

theorem sectionPairMap_surjective (O : Opens X) :
    Function.Surjective (sectionPairMap R U V W hW t O) := by
  intro p
  let a := (sectionsHomEquiv (patchAdd R U) O).symm p.val.1
  let b := (sectionsHomEquiv (patchAdd R V) O).symm p.val.2
  have hab : biprod.lift a b ≫ difference R U V W hW t = 0 := by
    apply (sectionsHomEquiv (patchAdd R W) O).injective
    have hc : sectionsHomEquiv (patchAdd R W) O
        (biprod.lift a b ≫ difference R U V W hW t) =
          pairDifference R U V W hW t O p.val := by
      simp only [difference, biprod.lift_desc, Preadditive.comp_neg, map_add, map_neg,
        sectionsHomEquiv_comp, a, b, AddEquiv.apply_symm_apply]
      dsimp [pairDifference, patchAddRestriction, patchRestriction, patchMul,
        res, patchAdd, patchRing, intersectFunctor]
      rw [sub_eq_add_neg]
      rfl
    rw [hc, map_zero]
    exact p.property
  refine ⟨sectionsHomEquiv (sheaf R U V W hW t) O
    (kernel.lift (difference R U V W hW t) (biprod.lift a b) hab), ?_⟩
  apply Subtype.ext
  apply Prod.ext
  · change (firstProjection R U V W hW t).hom.app (op O)
      (sectionsHomEquiv _ O (kernel.lift _ _ hab)) = p.val.1
    rw [← sectionsHomEquiv_comp, firstProjection, ← Category.assoc,
      kernel.lift_ι, biprod.lift_fst]
    exact (sectionsHomEquiv (patchAdd R U) O).apply_symm_apply p.val.1
  · change (secondProjection R U V W hW t).hom.app (op O)
      (sectionsHomEquiv _ O (kernel.lift _ _ hab)) = p.val.2
    rw [← sectionsHomEquiv_comp, secondProjection, ← Category.assoc,
      kernel.lift_ι, biprod.lift_snd]
    exact (sectionsHomEquiv (patchAdd R V) O).apply_symm_apply p.val.2

/-- Actual sections of the sheaf kernel are exactly the compatible pairs
of actual structure-sheaf sections, with no comparison premise. -/
def sectionPairsEquiv (O : Opens X) :
    (sheaf R U V W hW t).obj.obj (op O) ≃+ Pairs R U V W hW t O :=
  AddEquiv.ofBijective (sectionPairMap R U V W hW t O)
    ⟨sectionPairMap_injective R U V W hW t O,
      sectionPairMap_surjective R U V W hW t O⟩

theorem sectionPairs_fst_naturality {O P : Opens X} (h : P ≤ O)
    (s : (sheaf R U V W hW t).obj.obj (op O)) :
    (sectionPairsEquiv R U V W hW t P
      ((sheaf R U V W hW t).obj.map (homOfLE h).op s)).val.1 =
      res R (inf_le_inf_right U h) (sectionPairsEquiv R U V W hW t O s).val.1 := by
  have hh := congrArg (fun k => k s)
    ((firstProjection R U V W hW t).hom.naturality (homOfLE h).op)
  exact hh

theorem sectionPairs_snd_naturality {O P : Opens X} (h : P ≤ O)
    (s : (sheaf R U V W hW t).obj.obj (op O)) :
    (sectionPairsEquiv R U V W hW t P
      ((sheaf R U V W hW t).obj.map (homOfLE h).op s)).val.2 =
      res R (inf_le_inf_right V h) (sectionPairsEquiv R U V W hW t O s).val.2 := by
  have hh := congrArg (fun k => k s)
    ((secondProjection R U V W hW t).hom.naturality (homOfLE h).op)
  exact hh

/-! ## Actual sections in each local frame -/

def unitMulEquiv {A : Type} [CommRing A] (u : Aˣ) : A ≃+ A where
  toFun a := (u : A) * a
  invFun a := (↑(u⁻¹) : A) * a
  left_inv a := by dsimp only; rw [← mul_assoc, u.inv_mul, one_mul]
  right_inv a := by dsimp only; rw [← mul_assoc, u.mul_inv, one_mul]
  map_add' := mul_add (u : A)

def pairFirstEquiv (O : Opens X) (hO : O ≤ U) :
    Pairs R U V W hW t O ≃+ R.obj.obj (op (O ⊓ U)) := by
  let e : R.obj.obj (op (O ⊓ V)) ≃+ R.obj.obj (op (O ⊓ W)) :=
    (resEquiv R (inf_le_inf_left O (hW.le.trans inf_le_right)) (by
      rw [hW, ← inf_assoc, inf_eq_left.mpr hO] <;> exact le_rfl)).toAddEquiv.trans
        (unitMulEquiv (Units.map
          (res R (show O ⊓ W ≤ W from inf_le_right)).toMonoidHom t))
  let f := res R (inf_le_inf_left O (hW.le.trans inf_le_left))
  exact
    { toFun := fun p => p.val.1
      invFun := fun a => ⟨(a, e.symm (f a)), by
        change f a - e (e.symm (f a)) = 0
        rw [AddEquiv.apply_symm_apply, sub_self]⟩
      left_inv := by
        intro p
        apply Subtype.ext
        apply Prod.ext
        · rfl
        · change e.symm (f p.val.1) = p.val.2
          apply e.injective
          rw [AddEquiv.apply_symm_apply]
          exact sub_eq_zero.mp p.property
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl }

def pairSecondEquiv (O : Opens X) (hO : O ≤ V) :
    Pairs R U V W hW t O ≃+ R.obj.obj (op (O ⊓ V)) := by
  let e : R.obj.obj (op (O ⊓ U)) ≃+ R.obj.obj (op (O ⊓ W)) :=
    (resEquiv R (inf_le_inf_left O (hW.le.trans inf_le_left)) (by
      rw [hW]
      exact le_inf inf_le_left (le_inf inf_le_right (inf_le_left.trans hO)))).toAddEquiv
  let g : R.obj.obj (op (O ⊓ V)) → R.obj.obj (op (O ⊓ W)) := fun b =>
    res R (show O ⊓ W ≤ W from inf_le_right) (t : _) *
      res R (inf_le_inf_left O (hW.le.trans inf_le_right)) b
  exact
    { toFun := fun p => p.val.2
      invFun := fun b => ⟨(e.symm (g b), b), by
        change e (e.symm (g b)) - g b = 0
        rw [AddEquiv.apply_symm_apply, sub_self]⟩
      left_inv := by
        intro p
        apply Subtype.ext
        apply Prod.ext
        · change e.symm (g p.val.2) = p.val.1
          apply e.injective
          rw [AddEquiv.apply_symm_apply]
          exact (sub_eq_zero.mp p.property).symm
        · rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl }

/-- On every open contained in the first chart, the actual sheaf kernel
is additively identified with the actual structure-sheaf sections. -/
def firstLocalSectionsEquiv (O : Opens X) (hO : O ≤ U) :
    (sheaf R U V W hW t).obj.obj (op O) ≃+ R.obj.obj (op O) :=
  (sectionPairsEquiv R U V W hW t O).trans
    ((pairFirstEquiv R U V W hW t O hO).trans
      (resEquiv R (le_inf le_rfl hO) inf_le_left).toAddEquiv)

def secondLocalSectionsEquiv (O : Opens X) (hO : O ≤ V) :
    (sheaf R U V W hW t).obj.obj (op O) ≃+ R.obj.obj (op O) :=
  (sectionPairsEquiv R U V W hW t O).trans
    ((pairSecondEquiv R U V W hW t O hO).trans
      (resEquiv R (le_inf le_rfl hO) inf_le_left).toAddEquiv)

theorem firstLocalSectionsEquiv_apply (O : Opens X) (hO : O ≤ U)
    (s : (sheaf R U V W hW t).obj.obj (op O)) :
    firstLocalSectionsEquiv R U V W hW t O hO s =
      res R (le_inf le_rfl hO) (sectionPairsEquiv R U V W hW t O s).val.1 := rfl

theorem secondLocalSectionsEquiv_apply (O : Opens X) (hO : O ≤ V)
    (s : (sheaf R U V W hW t).obj.obj (op O)) :
    secondLocalSectionsEquiv R U V W hW t O hO s =
      res R (le_inf le_rfl hO) (sectionPairsEquiv R U V W hW t O s).val.2 := rfl

theorem firstLocalSectionsEquiv_naturality {O P : Opens X} (h : P ≤ O) (hO : O ≤ U)
    (s : (sheaf R U V W hW t).obj.obj (op O)) :
    firstLocalSectionsEquiv R U V W hW t P (h.trans hO)
        ((sheaf R U V W hW t).obj.map (homOfLE h).op s) =
      res R h (firstLocalSectionsEquiv R U V W hW t O hO s) := by
  simp only [firstLocalSectionsEquiv_apply, sectionPairs_fst_naturality, res_comp]

theorem secondLocalSectionsEquiv_naturality {O P : Opens X} (h : P ≤ O) (hO : O ≤ V)
    (s : (sheaf R U V W hW t).obj.obj (op O)) :
    secondLocalSectionsEquiv R U V W hW t P (h.trans hO)
        ((sheaf R U V W hW t).obj.map (homOfLE h).op s) =
      res R h (secondLocalSectionsEquiv R U V W hW t O hO s) := by
  simp only [secondLocalSectionsEquiv_apply, sectionPairs_snd_naturality, res_comp]

/-- The two actual section coordinates have the prescribed transition on
every open contained in the overlap. -/
theorem localSections_transition (O : Opens X) (hO : O ≤ W)
    (s : (sheaf R U V W hW t).obj.obj (op O)) :
    firstLocalSectionsEquiv R U V W hW t O (hO.trans (hW.le.trans inf_le_left)) s =
      res R hO (t : _) *
        secondLocalSectionsEquiv R U V W hW t O
          (hO.trans (hW.le.trans inf_le_right)) s := by
  let p := sectionPairsEquiv R U V W hW t O s
  have hp : res R (inf_le_inf_left O (hW.le.trans inf_le_left)) p.val.1 =
      res R (show O ⊓ W ≤ W from inf_le_right) (t : _) *
        res R (inf_le_inf_left O (hW.le.trans inf_le_right)) p.val.2 :=
    sub_eq_zero.mp p.property
  have hh := congrArg (res R (show O ≤ O ⊓ W from le_inf le_rfl hO)) hp
  simpa only [firstLocalSectionsEquiv_apply, secondLocalSectionsEquiv_apply,
    map_mul, res_comp] using hh

end Twisted

end CycleQ2GeometricProjectiveCurve

end
