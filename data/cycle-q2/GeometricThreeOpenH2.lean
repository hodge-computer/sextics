import Mathlib.CategoryTheory.Sites.SheafCohomology.MayerVietoris
import Mathlib.Topology.Sheaves.MayerVietoris
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.GroupTheory.QuotientGroup.Basic
import Proposal.GeometricSheafHZero

section SourceMayerVietorisRestriction

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2MayerVietorisRestriction

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
  TopologicalSpace Opposite

universe u w
variable {X : Type u} [TopologicalSpace X]

def freeOpenSheaf : Opens X ⥤
    Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
  yoneda ⋙ (Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free ⋙
    presheafToSheaf _ _

/-- The actual Mayer--Vietoris short complexes are covariant in a pair of
open inclusions. No cohomological comparison is supplied as a premise. -/
def shortComplexMap {U' V' U V : Opens X} (hU : U' ≤ U) (hV : V' ≤ V) :
    (Opens.mayerVietorisSquare U' V').shortComplex ⟶
      (Opens.mayerVietorisSquare U V).shortComplex where
  τ₁ := (freeOpenSheaf (X := X)).map (homOfLE (inf_le_inf hU hV))
  τ₂ := biprod.map ((freeOpenSheaf (X := X)).map (homOfLE hU))
    ((freeOpenSheaf (X := X)).map (homOfLE hV))
  τ₃ := (freeOpenSheaf (X := X)).map (homOfLE (sup_le_sup hU hV))
  comm₁₂ := by
    let K := freeOpenSheaf (X := X)
    change K.map _ ≫ biprod.lift (K.map _) (-(K.map _)) =
      biprod.lift (K.map _) (-(K.map _)) ≫ biprod.map (K.map _) (K.map _)
    apply biprod.hom_ext
    · simp only [Category.assoc, biprod.lift_fst, biprod.map_fst,
        biprod.lift_fst_assoc, ← Functor.map_comp]
      congr 1
    · simp only [Category.assoc, biprod.lift_snd, biprod.map_snd,
        biprod.lift_snd_assoc, Preadditive.comp_neg,
        Preadditive.neg_comp, ← Functor.map_comp]
      congr 2
  comm₂₃ := by
    let K := freeOpenSheaf (X := X)
    change biprod.map (K.map _) (K.map _) ≫ biprod.desc (K.map _) (K.map _) =
      biprod.desc (K.map _) (K.map _) ≫ K.map _
    apply biprod.hom_ext'
    · simp only [Category.assoc, biprod.inl_map_assoc, biprod.inl_desc,
        biprod.inl_desc_assoc, ← Functor.map_comp]
      congr 1
    · simp only [Category.assoc, biprod.inr_map_assoc, biprod.inr_desc,
        biprod.inr_desc_assoc, ← Functor.map_comp]
      congr 1

variable [HasExt.{w} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]
variable (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})

theorem restriction_apply (n : ℕ) {U V : Opens X} (h : U ≤ V)
    (x : F.H' n V) :
    (F.cohomologyPresheaf n).map (homOfLE h).op x =
      (Ext.mk₀ ((freeOpenSheaf (X := X)).map (homOfLE h))).comp x (zero_add n) := rfl

/-- Restricting an actual Mayer--Vietoris boundary to smaller opens is the
boundary of the restricted class. This follows from naturality of the
extension class of the actual short exact Mayer--Vietoris sequence. -/
theorem delta_restriction {U' V' U V : Opens X} (hU : U' ≤ U) (hV : V' ≤ V)
    (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) (x : F.H' n₀ (U ⊓ V)) :
    (F.cohomologyPresheaf n₁).map (homOfLE (sup_le_sup hU hV)).op
        ((Opens.mayerVietorisSquare U V).δ F n₀ n₁ h x) =
      (Opens.mayerVietorisSquare U' V').δ F n₀ n₁ h
        ((F.cohomologyPresheaf n₀).map (homOfLE (inf_le_inf hU hV)).op x) := by
  let S := Opens.mayerVietorisSquare U V
  let S' := Opens.mayerVietorisSquare U' V'
  let f := shortComplexMap hU hV
  let h' : 1 + n₀ = n₁ := (Nat.add_comm 1 n₀).trans h
  change (Ext.mk₀ f.τ₃).comp (S.shortComplex_shortExact.extClass.comp x h')
      (zero_add n₁) =
    S'.shortComplex_shortExact.extClass.comp
      ((Ext.mk₀ f.τ₁).comp x (zero_add n₀)) h'
  rw [← Ext.comp_assoc_of_second_deg_zero]
  rw [ShortComplex.ShortExact.extClass_naturality S'.shortComplex_shortExact
    S.shortComplex_shortExact f]
  exact (Ext.comp_assoc (Ext.mk₀ f.τ₃) S.shortComplex_shortExact.extClass x
    (zero_add 1) h' (by omega)).symm

end CycleQ2MayerVietorisRestriction

end
end SourceMayerVietorisRestriction

section SourceThreeOpenCechH2

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2ThreeOpenCechH2

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
  TopologicalSpace Opposite
open CycleQ2MayerVietorisRestriction

universe u w
variable {X : Type u} [TopologicalSpace X]
variable [HasExt.{w} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]
variable (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})

theorem delta_pair_zero (S : (Opens.grothendieckTopology X).MayerVietorisSquare)
    (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁)
    (a : F.H' n₀ S.X₂) (b : F.H' n₀ S.X₃) :
    S.δ F n₀ n₁ h
      ((F.cohomologyPresheaf n₀).map S.f₁₂.op a -
        (F.cohomologyPresheaf n₀).map S.f₁₃.op b) = 0 := by
  rw [← S.fromBiprod_biprodIsoProd_inv_apply F a b]
  exact congrArg
    (fun k : (F.H' n₀ S.X₂ ⊞ F.H' n₀ S.X₃) ⟶ F.H' n₁ S.X₄ =>
      k ((AddCommGrpCat.biprodIsoProd _ _).inv (a, b)))
    (S.fromBiprod_δ F n₀ n₁ h)

theorem delta_left_zero (S : (Opens.grothendieckTopology X).MayerVietorisSquare)
    (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) (a : F.H' n₀ S.X₂) :
    S.δ F n₀ n₁ h ((F.cohomologyPresheaf n₀).map S.f₁₂.op a) = 0 := by
  simpa only [map_zero, sub_zero] using delta_pair_zero F S n₀ n₁ h a 0

theorem delta_right_zero (S : (Opens.grothendieckTopology X).MayerVietorisSquare)
    (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) (a : F.H' n₀ S.X₃) :
    S.δ F n₀ n₁ h ((F.cohomologyPresheaf n₀).map S.f₁₃.op a) = 0 := by
  simpa only [map_zero, map_neg, zero_sub, neg_neg] using
    delta_pair_zero F S n₀ n₁ h 0 (-a)

theorem delta_eq_zero_iff (S : (Opens.grothendieckTopology X).MayerVietorisSquare)
    (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) (x : F.H' n₀ S.X₁) :
    S.δ F n₀ n₁ h x = 0 ↔
      ∃ (a : F.H' n₀ S.X₂) (b : F.H' n₀ S.X₃),
        (F.cohomologyPresheaf n₀).map S.f₁₂.op a -
          (F.cohomologyPresheaf n₀).map S.f₁₃.op b = x := by
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := (ShortComplex.ab_exact_iff _).mp
      ((S.sequence_exact F n₀ n₁ h).exact 1) x hx
    have hy' : S.fromBiprod F n₀ y = x := hy
    obtain ⟨⟨a, b⟩, rfl⟩ :=
      (AddCommGrpCat.biprodIsoProd _ _).addCommGroupIsoToAddEquiv.symm.surjective y
    exact ⟨a, b, (S.fromBiprod_biprodIsoProd_inv_apply F a b).symm.trans hy'⟩
  · rintro ⟨a, b, rfl⟩
    exact delta_pair_zero F S n₀ n₁ h a b

theorem delta_surjective (S : (Opens.grothendieckTopology X).MayerVietorisSquare)
    [Subsingleton (F.H' 1 S.X₂)] [Subsingleton (F.H' 1 S.X₃)] :
    Function.Surjective (S.δ F 0 1 rfl) := by
  intro y
  have hnext : S.toBiprod F 1 y = 0 := by
    rw [S.toBiprod_apply]
    have hp :
        (((F.cohomologyPresheaf 1).map S.f₂₄.op y),
          ((F.cohomologyPresheaf 1).map S.f₃₄.op y)) = (0, 0) :=
      Prod.ext (Subsingleton.elim _ _) (Subsingleton.elim _ _)
    rw [hp]
    exact map_zero _
  obtain ⟨x, hx⟩ := (ShortComplex.ab_exact_iff _).mp
    ((S.sequence_exact F 0 1 rfl).exact 2) y hnext
  exact ⟨x, hx⟩

/-- The outer union square uses the union of the two intersections as
its intersection object. This keeps both genuine connecting maps on the
same actual cohomology group without an arbitrary comparison map. -/
def outerSquare (U V W : Opens X) :
    (Opens.grothendieckTopology X).MayerVietorisSquare :=
  Opens.mayerVietorisSquare'
    { X₁ := (U ⊓ W) ⊔ (V ⊓ W)
      X₂ := U ⊔ V
      X₃ := W
      X₄ := (U ⊔ V) ⊔ W
      f₁₂ := homOfLE (sup_le_sup inf_le_left inf_le_left)
      f₁₃ := homOfLE (sup_le inf_le_right inf_le_right)
      f₂₄ := homOfLE le_sup_left
      f₃₄ := homOfLE le_sup_right
      fac := Subsingleton.elim _ _ }
    rfl (by rw [inf_sup_right])

abbrev TripleOpen (U V W : Opens X) := (U ⊓ W) ⊓ (V ⊓ W)

def restrict01 (U V W : Opens X) : F.H' 0 (U ⊓ V) →+ F.H' 0 (TripleOpen U V W) :=
  ((F.cohomologyPresheaf 0).map
    (homOfLE (inf_le_inf (inf_le_left : U ⊓ W ≤ U) (inf_le_left : V ⊓ W ≤ V))).op).hom

def restrict02 (U V W : Opens X) : F.H' 0 (U ⊓ W) →+ F.H' 0 (TripleOpen U V W) :=
  ((F.cohomologyPresheaf 0).map (homOfLE inf_le_left).op).hom

def restrict12 (U V W : Opens X) : F.H' 0 (V ⊓ W) →+ F.H' 0 (TripleOpen U V W) :=
  ((F.cohomologyPresheaf 0).map (homOfLE inf_le_right).op).hom

/-- The usual alternating degree-one Čech differential on a three-open
cover, expressed in actual H⁰ groups. -/
def boundary (U V W : Opens X) :
    (F.H' 0 (U ⊓ V) × F.H' 0 (U ⊓ W) × F.H' 0 (V ⊓ W)) →+
      F.H' 0 (TripleOpen U V W) where
  toFun p := restrict12 F U V W p.2.2 - restrict02 F U V W p.2.1 +
    restrict01 F U V W p.1
  map_zero' := by simp
  map_add' := by
    intro p q
    simp only [Prod.fst_add, Prod.snd_add, map_add]
    abel

/-- Two genuine Mayer--Vietoris connecting homomorphisms send a triple
overlap section to actual derived H² of the union. -/
def connecting (U V W : Opens X) :
    F.H' 0 (TripleOpen U V W) →+ F.H' 2 ((U ⊔ V) ⊔ W) :=
  ((outerSquare U V W).δ F 1 2 rfl).hom.comp
    ((Opens.mayerVietorisSquare (U ⊓ W) (V ⊓ W)).δ F 0 1 rfl).hom

theorem connecting_restrict01 (U V W : Opens X) (a : F.H' 0 (U ⊓ V)) :
    connecting F U V W (restrict01 F U V W a) = 0 := by
  let T := outerSquare U V W
  let S := Opens.mayerVietorisSquare (U ⊓ W) (V ⊓ W)
  have hn : S.δ F 0 1 rfl (restrict01 F U V W a) =
      (F.cohomologyPresheaf 1).map T.f₁₂.op
        ((Opens.mayerVietorisSquare U V).δ F 0 1 rfl a) :=
    (delta_restriction F (inf_le_left : U ⊓ W ≤ U)
      (inf_le_left : V ⊓ W ≤ V) 0 1 rfl a).symm
  exact (congrArg (fun z : F.H' 1 T.X₁ => T.δ F 1 2 rfl z) hn).trans
    (delta_left_zero F T 1 2 rfl
      ((Opens.mayerVietorisSquare U V).δ F 0 1 rfl a))

theorem connecting_restrict02 (U V W : Opens X) (a : F.H' 0 (U ⊓ W)) :
    connecting F U V W (restrict02 F U V W a) = 0 := by
  let T := outerSquare U V W
  let S := Opens.mayerVietorisSquare (U ⊓ W) (V ⊓ W)
  have hz : S.δ F 0 1 rfl (restrict02 F U V W a) = 0 :=
    delta_left_zero F S 0 1 rfl a
  exact (congrArg (fun z : F.H' 1 T.X₁ => T.δ F 1 2 rfl z) hz).trans (map_zero _)

theorem connecting_restrict12 (U V W : Opens X) (a : F.H' 0 (V ⊓ W)) :
    connecting F U V W (restrict12 F U V W a) = 0 := by
  let T := outerSquare U V W
  let S := Opens.mayerVietorisSquare (U ⊓ W) (V ⊓ W)
  have hz : S.δ F 0 1 rfl (restrict12 F U V W a) = 0 :=
    delta_right_zero F S 0 1 rfl a
  exact (congrArg (fun z : F.H' 1 T.X₁ => T.δ F 1 2 rfl z) hz).trans (map_zero _)

theorem connecting_boundary (U V W : Opens X)
    (p : F.H' 0 (U ⊓ V) × F.H' 0 (U ⊓ W) × F.H' 0 (V ⊓ W)) :
    connecting F U V W (boundary F U V W p) = 0 := by
  change connecting F U V W
    (restrict12 F U V W p.2.2 - restrict02 F U V W p.2.1 +
      restrict01 F U V W p.1) = 0
  rw [map_add, map_sub, connecting_restrict12, connecting_restrict02,
    connecting_restrict01, sub_self, zero_add]

/-- Vanishing of H¹ on the three opens identifies the complete kernel of
the two genuine connecting maps with the actual Čech boundaries. -/
theorem connecting_eq_zero_iff (U V W : Opens X)
    [Subsingleton (F.H' 1 U)] [Subsingleton (F.H' 1 V)] [Subsingleton (F.H' 1 W)]
    (x : F.H' 0 (TripleOpen U V W)) :
    connecting F U V W x = 0 ↔
      ∃ (a : F.H' 0 (U ⊓ V)) (b : F.H' 0 (U ⊓ W)) (c : F.H' 0 (V ⊓ W)),
        boundary F U V W (a, b, c) = x := by
  constructor
  · intro hx
    let S := Opens.mayerVietorisSquare (U ⊓ W) (V ⊓ W)
    let T := outerSquare U V W
    letI : Subsingleton (F.H' 1 T.X₃) :=
      (inferInstance : Subsingleton (F.H' 1 W))
    letI : Subsingleton (F.H' 1 (Opens.mayerVietorisSquare U V).X₂) :=
      (inferInstance : Subsingleton (F.H' 1 U))
    letI : Subsingleton (F.H' 1 (Opens.mayerVietorisSquare U V).X₃) :=
      (inferInstance : Subsingleton (F.H' 1 V))
    change T.δ F 1 2 rfl (S.δ F 0 1 rfl x) = 0 at hx
    obtain ⟨a₁, b₁, hab⟩ := (delta_eq_zero_iff F T 1 2 rfl _).mp hx
    have hb : b₁ = 0 := Subsingleton.elim _ _
    have ha : (F.cohomologyPresheaf 1).map T.f₁₂.op a₁ = S.δ F 0 1 rfl x := by
      simpa only [hb, map_zero, sub_zero] using hab
    obtain ⟨a, ha₀⟩ := delta_surjective F (Opens.mayerVietorisSquare U V) a₁
    have hn : S.δ F 0 1 rfl (restrict01 F U V W a) =
        (F.cohomologyPresheaf 1).map T.f₁₂.op
          ((Opens.mayerVietorisSquare U V).δ F 0 1 rfl a) :=
      (delta_restriction F (inf_le_left : U ⊓ W ≤ U)
        (inf_le_left : V ⊓ W ≤ V) 0 1 rfl a).symm
    have he : S.δ F 0 1 rfl (restrict01 F U V W a) = S.δ F 0 1 rfl x := by
      exact hn.trans ((congrArg ((F.cohomologyPresheaf 1).map T.f₁₂.op) ha₀).trans ha)
    have hz : S.δ F 0 1 rfl (x - restrict01 F U V W a) = 0 := by
      calc
        _ = S.δ F 0 1 rfl x - S.δ F 0 1 rfl (restrict01 F U V W a) := map_sub _ _ _
        _ = 0 := sub_eq_zero.mpr he.symm
    obtain ⟨b, c, hbc⟩ := (delta_eq_zero_iff F S 0 1 rfl _).mp hz
    have hbc' : restrict02 F U V W b - restrict12 F U V W c =
        x - restrict01 F U V W a := hbc
    refine ⟨a, -b, -c, ?_⟩
    change restrict12 F U V W (-c) - restrict02 F U V W (-b) +
      restrict01 F U V W a = x
    rw [map_neg, map_neg]
    calc
      _ = (restrict02 F U V W b - restrict12 F U V W c) +
          restrict01 F U V W a := by abel
      _ = x := by rw [hbc']; abel
  · rintro ⟨a, b, c, rfl⟩
    exact connecting_boundary F U V W (a, b, c)

theorem connecting_ker (U V W : Opens X)
    [Subsingleton (F.H' 1 U)] [Subsingleton (F.H' 1 V)] [Subsingleton (F.H' 1 W)] :
    (connecting F U V W).ker = (boundary F U V W).range := by
  ext x
  constructor
  · intro hx
    obtain ⟨a, b, c, habc⟩ := (connecting_eq_zero_iff F U V W x).mp hx
    exact ⟨(a, b, c), habc⟩
  · rintro ⟨p, rfl⟩
    exact connecting_boundary F U V W p

abbrev CechH2 (U V W : Opens X) :=
  F.H' 0 (TripleOpen U V W) ⧸ (boundary F U V W).range

/-- The actual triple Čech quotient injects into actual derived H². -/
def toSheafH2 (U V W : Opens X)
    [Subsingleton (F.H' 1 U)] [Subsingleton (F.H' 1 V)] [Subsingleton (F.H' 1 W)] :
    CechH2 F U V W →+ F.H' 2 ((U ⊔ V) ⊔ W) :=
  QuotientAddGroup.lift (boundary F U V W).range (connecting F U V W)
    (connecting_ker F U V W).symm.le

theorem toSheafH2_injective (U V W : Opens X)
    [Subsingleton (F.H' 1 U)] [Subsingleton (F.H' 1 V)] [Subsingleton (F.H' 1 W)] :
    Function.Injective (toSheafH2 F U V W) :=
  (QuotientAddGroup.injective_lift_iff _ _ _).2 (connecting_ker F U V W).symm

end CycleQ2ThreeOpenCechH2

end
end SourceThreeOpenCechH2

section SourceThreeOpenSectionH2

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2ThreeOpenSectionH2

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
  TopologicalSpace Opposite
open CycleQ2GeometricConeCech.HZero
open CycleQ2ThreeOpenCechH2

universe u w
variable {X : Type u} [TopologicalSpace X]
variable [HasExt.{w} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]
variable (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})

abbrev Sections (U : Opens X) := F.obj.obj (op U)

/-- The actual restriction differential, with the usual three-open signs. -/
def boundary (U V W : Opens X) :
    (Sections F (U ⊓ V) × Sections F (U ⊓ W) × Sections F (V ⊓ W)) →+
      Sections F (TripleOpen U V W) where
  toFun p := F.obj.map (homOfLE inf_le_right).op p.2.2 -
    F.obj.map (homOfLE inf_le_left).op p.2.1 +
    F.obj.map (homOfLE
      (inf_le_inf (inf_le_left : U ⊓ W ≤ U) (inf_le_left : V ⊓ W ≤ V))).op p.1
  map_zero' := by simp
  map_add' := by
    intro p q
    simp only [Prod.fst_add, Prod.snd_add, map_add]
    abel

/-- The construction uses actual sections through the canonical H⁰
comparison, then the two actual Mayer--Vietoris connecting homomorphisms. -/
def connecting (U V W : Opens X) :
    Sections F (TripleOpen U V W) →+ F.H' 2 ((U ⊔ V) ⊔ W) :=
  (CycleQ2ThreeOpenCechH2.connecting F U V W).comp
    (sectionsEquiv F (TripleOpen U V W)).symm.toAddMonoidHom

theorem boundary_hzero (U V W : Opens X)
    (a : F.H' 0 (U ⊓ V)) (b : F.H' 0 (U ⊓ W)) (c : F.H' 0 (V ⊓ W)) :
    sectionsEquiv F (TripleOpen U V W)
      (CycleQ2ThreeOpenCechH2.boundary F U V W (a, b, c)) =
        boundary F U V W
          (sectionsEquiv F (U ⊓ V) a, sectionsEquiv F (U ⊓ W) b,
            sectionsEquiv F (V ⊓ W) c) := by
  change sectionsEquiv F (TripleOpen U V W)
    (restrict12 F U V W c - restrict02 F U V W b + restrict01 F U V W a) = _
  rw [map_add, map_sub]
  exact congrArg₂ (· + ·)
    (congrArg₂ (· - ·)
      (sectionsEquiv_naturality F (homOfLE inf_le_right) c)
      (sectionsEquiv_naturality F (homOfLE inf_le_left) b))
    (sectionsEquiv_naturality F (homOfLE (inf_le_inf
      (inf_le_left : U ⊓ W ≤ U) (inf_le_left : V ⊓ W ≤ V))) a)

theorem boundary_preimage (U V W : Opens X)
    (a : Sections F (U ⊓ V)) (b : Sections F (U ⊓ W)) (c : Sections F (V ⊓ W)) :
    (sectionsEquiv F (TripleOpen U V W)).symm (boundary F U V W (a, b, c)) =
      CycleQ2ThreeOpenCechH2.boundary F U V W
        ((sectionsEquiv F (U ⊓ V)).symm a, (sectionsEquiv F (U ⊓ W)).symm b,
          (sectionsEquiv F (V ⊓ W)).symm c) := by
  apply (sectionsEquiv F (TripleOpen U V W)).injective
  rw [AddEquiv.apply_symm_apply, boundary_hzero]
  simp only [AddEquiv.apply_symm_apply]

theorem connecting_boundary (U V W : Opens X)
    (p : Sections F (U ⊓ V) × Sections F (U ⊓ W) × Sections F (V ⊓ W)) :
    connecting F U V W (boundary F U V W p) = 0 := by
  rcases p with ⟨a, b, c⟩
  change CycleQ2ThreeOpenCechH2.connecting F U V W
    ((sectionsEquiv F (TripleOpen U V W)).symm (boundary F U V W (a, b, c))) = 0
  rw [boundary_preimage]
  exact CycleQ2ThreeOpenCechH2.connecting_boundary F U V W _

theorem connecting_eq_zero_iff (U V W : Opens X)
    [Subsingleton (F.H' 1 U)] [Subsingleton (F.H' 1 V)] [Subsingleton (F.H' 1 W)]
    (x : Sections F (TripleOpen U V W)) :
    connecting F U V W x = 0 ↔
      ∃ (a : Sections F (U ⊓ V)) (b : Sections F (U ⊓ W))
        (c : Sections F (V ⊓ W)), boundary F U V W (a, b, c) = x := by
  constructor
  · intro hx
    obtain ⟨a, b, c, h⟩ := (CycleQ2ThreeOpenCechH2.connecting_eq_zero_iff F U V W
      ((sectionsEquiv F (TripleOpen U V W)).symm x)).mp hx
    refine ⟨sectionsEquiv F (U ⊓ V) a, sectionsEquiv F (U ⊓ W) b,
      sectionsEquiv F (V ⊓ W) c, ?_⟩
    have hh := congrArg (sectionsEquiv F (TripleOpen U V W)) h
    simpa only [boundary_hzero, AddEquiv.apply_symm_apply] using hh
  · rintro ⟨a, b, c, rfl⟩
    exact connecting_boundary F U V W (a, b, c)

theorem connecting_ker (U V W : Opens X)
    [Subsingleton (F.H' 1 U)] [Subsingleton (F.H' 1 V)] [Subsingleton (F.H' 1 W)] :
    (connecting F U V W).ker = (boundary F U V W).range := by
  ext x
  constructor
  · intro hx
    obtain ⟨a, b, c, h⟩ := (connecting_eq_zero_iff F U V W x).mp hx
    exact ⟨(a, b, c), h⟩
  · rintro ⟨p, rfl⟩
    exact connecting_boundary F U V W p

abbrev CechH2 (U V W : Opens X) :=
  Sections F (TripleOpen U V W) ⧸ (boundary F U V W).range

def toSheafH2 (U V W : Opens X)
    [Subsingleton (F.H' 1 U)] [Subsingleton (F.H' 1 V)] [Subsingleton (F.H' 1 W)] :
    CechH2 F U V W →+ F.H' 2 ((U ⊔ V) ⊔ W) :=
  QuotientAddGroup.lift (boundary F U V W).range (connecting F U V W)
    (connecting_ker F U V W).symm.le

theorem toSheafH2_injective (U V W : Opens X)
    [Subsingleton (F.H' 1 U)] [Subsingleton (F.H' 1 V)] [Subsingleton (F.H' 1 W)] :
    Function.Injective (toSheafH2 F U V W) :=
  (QuotientAddGroup.injective_lift_iff _ _ _).2 (connecting_ker F U V W).symm

end CycleQ2ThreeOpenSectionH2

end
end SourceThreeOpenSectionH2
