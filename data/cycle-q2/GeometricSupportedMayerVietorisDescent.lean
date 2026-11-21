import Proposal.GeometricMonicGenericSupport
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.Topology.NoetherianSpace
import Mathlib.Order.Minimal
import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle

/-! Mayer–Vietoris descent for the support quotient. Local vanishing below degree four gives global gluing of degree-four classes.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false

noncomputable section

namespace CycleQ2DeRhamNegative

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open CycleQ2IntrinsicDeRhamSheaves (relativeDeRhamInt)
open CycleQ2InjectiveCech (AbSheaf)

variable {k : Type} [Field k] [CharZero k] {X : Scheme.{0}}
    (p : X ⟶ Spec (CommRingCat.of k)) (r : ℕ) [SmoothOfRelativeDimension r p]
    [HasDerivedCategory.{1} (AbSheaf (show TopCat from X))]
private abbrev E := DerivedCategory.singleFunctor (AbSheaf (show TopCat from X)) 0

/-- The native relative de Rham complex has no negative hypercohomology
with coefficients in any source sheaf placed in degree zero. -/
theorem eq_zero (A : AbSheaf (show TopCat from X)) (q : ℤ) (hq : q < 0)
    (f : E.obj A ⟶ (DerivedCategory.Q.obj (relativeDeRhamInt p r))⟦q⟧) :
    f = 0 := by
  let K : CochainComplex (AbSheaf (show TopCat from X)) ℤ := relativeDeRhamInt p r
  let e := ComplexShape.embeddingUpIntGE 0
  let : K.IsStrictlyGE 0 := by
    change ((CycleQ2IntrinsicDeRhamSheaves.relativeDeRham p r).extend e).IsStrictlySupported e
    infer_instance
  let D : DerivedCategory.{1} (AbSheaf (show TopCat from X)) :=
    DerivedCategory.Q.obj K
  let : D.IsGE 0 :=
    (DerivedCategory.isGE_Q_obj_iff.{1} K 0).mpr inferInstance
  apply DerivedCategory.TStructure.t.zero_of_isLE_of_isGE f 0 (-q) (by omega)
  · infer_instance
  · exact DerivedCategory.TStructure.t.isGE_shift D 0 q (-q) (by omega)

end CycleQ2DeRhamNegative

namespace CycleQ2LocalDescent

open TopologicalSpace
universe u v w
variable {X : Type u} [TopologicalSpace X] [NoetherianSpace X]
  {F : Opens X → Type v}
  (r : ∀ {V W : Opens X}, V ≤ W → F W → F V)
  (comp : ∀ {D V W : Opens X} (h : D ≤ V) (j : V ≤ W) (a : F W),
    r h (r j a) = r (h.trans j) a)
  (ident : ∀ {W : Opens X} (a : F W), r le_rfl a = a)

def BinarySeparated : Prop :=
  ∀ (U V : Opens X) (a b : F (U ⊔ V)),
    r (le_sup_left : U ≤ U ⊔ V) a = r le_sup_left b →
    r (le_sup_right : V ≤ U ⊔ V) a = r le_sup_right b → a = b

def BinaryGluing : Prop :=
  ∀ (U V : Opens X) (a : F U) (b : F V),
    r (inf_le_left : U ⊓ V ≤ U) a = r inf_le_right b →
    ∃ c : F (U ⊔ V), r le_sup_left c = a ∧ r le_sup_right c = b

omit [NoetherianSpace X] in
private theorem separated_cover (sep : BinarySeparated r)
    {W U V : Opens X} (u : U ≤ W) (v : V ≤ W) (h : W ≤ U ⊔ V)
    (a b : F W) (hu : r u a = r u b) (hv : r v a = r v b) : a = b := by
  obtain rfl := le_antisymm h (sup_le u v)
  exact sep U V a b hu hv

include comp ident

/-- On a Noetherian space binary separatedness detects equality on arbitrary neighborhoods. -/
theorem eq_of_local (sep : BinarySeparated r) [Subsingleton (F ⊥)]
    {W : Opens X} {a b : F W}
    (h : ∀ x ∈ W, ∃ (V : Opens X) (v : V ≤ W), x ∈ V ∧ r v a = r v b) : a = b := by
  let P (V : Opens X) := ∃ v : V ≤ W, r v a = r v b
  obtain ⟨V,hV⟩ := exists_maximal_of_wellFoundedGT P
    ⟨⊥,bot_le,Subsingleton.elim _ _⟩
  obtain ⟨v,hv⟩ := hV.prop
  have hw : W ≤ V := by
    intro x hx
    obtain ⟨D,d,hdx,hd⟩ := h x hx
    have hD : P (V ⊔ D) := by
      refine ⟨sup_le v d,sep V D _ _ ?_ ?_⟩
      · simpa only [comp] using hv
      · simpa only [comp] using hd
    exact (le_sup_right.trans (hV.le_of_ge hD le_sup_left)) hdx
  obtain rfl := le_antisymm v hw
  simpa only [ident] using hv

/-- Pointwise agreement on the overlaps suffices for a global section once
the two-open Mayer–Vietoris maps are jointly injective. -/
theorem exists_global (sep : BinarySeparated r) (glue : BinaryGluing r)
    [Subsingleton (F ⊥)] [Nonempty (F ⊥)]
    {ι : Type w} (U : ι → Opens X) (a : ∀ n, F (U n))
    (cover : ∀ x : X, ∃ n, x ∈ U n)
    (agree : ∀ n m (x : X), x ∈ U n → x ∈ U m →
      ∃ (D : Opens X) (d : D ≤ U n) (e : D ≤ U m), x ∈ D ∧ r d (a n) = r e (a m)) :
    ∃ s : F ⊤, ∀ n, r (le_top : U n ≤ ⊤) s = a n := by
  classical
  have compatible (n m) (Z : Opens X) (z : Z ≤ U n) (w : Z ≤ U m) :
      r z (a n) = r w (a m) := by
    apply eq_of_local r comp ident sep
    intro x hx
    obtain ⟨D,d,e,xd,he⟩ := agree n m x (z hx) (w hx)
    refine ⟨Z ⊓ D,inf_le_left,⟨hx,xd⟩,?_⟩
    simpa only [comp] using congrArg (r (inf_le_right : Z ⊓ D ≤ D)) he
  let P (V : Opens X) := ∃ b : F V, ∀ n (Z : Opens X) (z : Z ≤ V) (w : Z ≤ U n),
    r z b = r w (a n)
  have start : P ⊥ := by
    refine ⟨Classical.choice inferInstance, fun n Z z w => ?_⟩
    obtain rfl := bot_unique z
    exact Subsingleton.elim _ _
  obtain ⟨V,hV⟩ := exists_maximal_of_wellFoundedGT P ⟨⊥,start⟩
  obtain ⟨b,hb⟩ := hV.prop
  have extend (n) : P (V ⊔ U n) := by
    obtain ⟨c,cv,cu⟩ := glue V (U n) b (a n) (hb n _ inf_le_left inf_le_right)
    refine ⟨c,fun m Z z w => ?_⟩
    apply separated_cover r sep (U := Z ⊓ V) (V := Z ⊓ U n) inf_le_left inf_le_left
    · rw [← inf_sup_left]
      exact le_inf le_rfl z
    · calc
        _ = r (inf_le_right : Z ⊓ V ≤ V) (r le_sup_left c) := by rw [comp,comp]
        _ = r (inf_le_right : Z ⊓ V ≤ V) b := congrArg _ cv
        _ = _ := (hb m _ inf_le_right (inf_le_left.trans w)).trans (comp _ _ _).symm
    · calc
        _ = r (inf_le_right : Z ⊓ U n ≤ U n) (r le_sup_right c) := by rw [comp,comp]
        _ = r (inf_le_right : Z ⊓ U n ≤ U n) (a n) := congrArg _ cu
        _ = _ := (compatible n m _ inf_le_right (inf_le_left.trans w)).trans (comp _ _ _).symm
  have eq : V = ⊤ := top_unique (by
    intro x _
    obtain ⟨n,hn⟩ := cover x
    exact (le_sup_right.trans (hV.le_of_ge (extend n) le_sup_left)) hn)
  subst V
  exact ⟨b,fun n => (hb n _ le_top le_rfl).trans (ident _)⟩

end CycleQ2LocalDescent

namespace CycleQ2BinaryDerivedUnique

open CategoryTheory CategoryTheory.Limits

universe w v u
variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

private abbrev E := DerivedCategory.singleFunctor C 0

/-- Two classes on the union agreeing on both opens coincide if the
overlap group in the preceding degree vanishes. -/
theorem ext {I U V W : C} (iu : I ⟶ U) (iv : I ⟶ V) (uw : U ⟶ W) (vw : V ⟶ W)
    (hz : biprod.lift iu (-iv) ≫ biprod.desc uw vw = 0)
    (hS : (ShortComplex.mk (biprod.lift iu (-iv)) (biprod.desc uw vw) hz).ShortExact)
    {T : DerivedCategory C} (hvan : ∀ f : ((E (C := C)).obj I)⟦(1 : ℤ)⟧ ⟶ T, f = 0)
    {c c' : (E (C := C)).obj W ⟶ T}
    (hu : (E (C := C)).map uw ≫ c = (E (C := C)).map uw ≫ c')
    (hv : (E (C := C)).map vw ≫ c = (E (C := C)).map vw ≫ c') :
    c = c' := by
  let F := E (C := C)
  change F.map uw ≫ c = F.map uw ≫ c' at hu
  change F.map vw ≫ c = F.map vw ≫ c' at hv
  have hk : F.map (biprod.desc uw vw) ≫ (c - c') = 0 := by
    simp only [Preadditive.comp_sub, biprod.desc_eq, F.map_add, F.map_comp,
      Preadditive.add_comp, Category.assoc, hu, hv, sub_self]
  obtain ⟨f, hf⟩ := hS.singleTriangle.yoneda_exact₃ hS.singleTriangle_distinguished (c - c') hk
  have hf₀ : f = 0 := hvan f
  exact sub_eq_zero.mp (hf.trans (by rw [hf₀]; exact comp_zero))

end CycleQ2BinaryDerivedUnique

namespace CycleQ2BinaryDerivedLift

open CategoryTheory CategoryTheory.Limits

universe w v u
variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

private abbrev E := DerivedCategory.singleFunctor C 0

/-- A pair of derived classes agreeing on the intersection extends to the union
when its Mayer–Vietoris sequence of source objects is short exact. -/
theorem glue {I U V W : C} (iu : I ⟶ U) (iv : I ⟶ V) (uw : U ⟶ W) (vw : V ⟶ W)
    (hz : biprod.lift iu (-iv) ≫ biprod.desc uw vw = 0)
    (hS : (ShortComplex.mk (biprod.lift iu (-iv)) (biprod.desc uw vw) hz).ShortExact)
    {T : DerivedCategory C} (a : (E (C := C)).obj U ⟶ T) (b : (E (C := C)).obj V ⟶ T)
    (agree : (E (C := C)).map iu ≫ a = (E (C := C)).map iv ≫ b) :
    ∃ c : (E (C := C)).obj W ⟶ T,
      (E (C := C)).map uw ≫ c = a ∧ (E (C := C)).map vw ≫ c = b := by
  let F := E (C := C)
  let p : F.obj (U ⊞ V) ⟶ T :=
    F.map biprod.fst ≫ a + F.map biprod.snd ≫ b
  change F.map iu ≫ a = F.map iv ≫ b at agree
  have hp : F.map (biprod.lift iu (-iv)) ≫ p = 0 := by
    simp only [p, Preadditive.comp_add, ← Category.assoc, ← F.map_comp,
      biprod.lift_fst, biprod.lift_snd, F.map_neg, Preadditive.neg_comp, agree, add_neg_cancel]
  obtain ⟨c, hc⟩ := hS.singleTriangle.yoneda_exact₂ hS.singleTriangle_distinguished p hp
  change F.obj W ⟶ T at c
  change p = F.map (biprod.desc uw vw) ≫ c at hc
  refine ⟨c, ?_, ?_⟩
  · change F.map uw ≫ c = a
    calc
      _ = F.map (biprod.inl : U ⟶ U ⊞ V) ≫ (F.map (biprod.desc uw vw) ≫ c) := by
        rw [← Category.assoc, ← F.map_comp, biprod.inl_desc]
      _ = F.map biprod.inl ≫ p := by rw [← hc]
      _ = a := by simp [p, Preadditive.comp_add, ← Category.assoc, ← F.map_comp]
  · change F.map vw ≫ c = b
    calc
      _ = F.map (biprod.inr : V ⟶ U ⊞ V) ≫ (F.map (biprod.desc uw vw) ≫ c) := by
        rw [← Category.assoc, ← F.map_comp, biprod.inr_desc]
      _ = F.map biprod.inr ≫ p := by rw [← hc]
      _ = b := by simp [p, Preadditive.comp_add, ← Category.assoc, ← F.map_comp]

end CycleQ2BinaryDerivedLift

namespace CycleQ2SupportMV

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open CycleQ2InjectiveCech (AbSheaf freeOpen freeOpenMap)
open CycleQ2RelativeOpenSupport (quotient sequence shortExact stalk_zero)
open CycleQ2RelativeSupportRefinement (supportMap)
open CycleQ2FreeOpenStalk (St)

attribute [local instance] preservesBinaryBiproducts_of_preservesBiproducts

variable {X : TopCat.{0}} (C : Opens X)

private abbrev sx (x : X) : AbSheaf X ⥤ AddCommGrpCat.{0} := St x

local instance stalk_additive (x : X) : (sx x).Additive := by
  change (St x).Additive
  dsimp [St]
  infer_instance

local instance stalk_zero_maps (x : X) : (sx x).PreservesZeroMorphisms := by
  exact @Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _ _ (stalk_additive x)

local instance stalk_limits (x : X) : PreservesFiniteLimits (sx x) := by
  change PreservesFiniteLimits (St x)
  dsimp [St]
  infer_instance

local instance stalk_colimits (x : X) : PreservesFiniteColimits (sx x) := by
  change PreservesFiniteColimits (St x)
  dsimp [St]
  infer_instance

abbrev M (W : Opens X) := quotient (show W ⊓ C ≤ W from inf_le_left)

abbrev π (W : Opens X) : freeOpen W ⟶ M C W :=
  (sequence (show W ⊓ C ≤ W from inf_le_left)).g

instance projection_epi (W : Opens X) : Epi (π C W) :=
  (shortExact (show W ⊓ C ≤ W from inf_le_left)).epi_g

abbrev inc {W V : Opens X} (h : W ≤ V) : M C W ⟶ M C V :=
  (supportMap (show W ⊓ C ≤ W from inf_le_left) (show V ⊓ C ≤ V from inf_le_left)
    (inf_le_inf_right _ h) h).τ₃

@[reassoc] theorem natural {W V : Opens X} (h : W ≤ V) :
    π C W ≫ inc C h = freeOpenMap h ≫ π C V :=
  (supportMap (show W ⊓ C ≤ W from inf_le_left) (show V ⊓ C ≤ V from inf_le_left)
    (inf_le_inf_right _ h) h).comm₂₃.symm

theorem inc_comp {W V T : Opens X} (h : W ≤ V) (j : V ≤ T) :
    inc C h ≫ inc C j = inc C (h.trans j) := by
  apply (cancel_epi (π C W)).mp
  rw [natural_assoc,natural,natural,← Category.assoc]
  exact congrArg (fun t => t ≫ π C T)
    (CycleQ2MayerVietorisRestriction.freeOpenSheaf.map_comp (homOfLE h) (homOfLE j)).symm

def mv (U V : Opens X) : ShortComplex (AbSheaf X) :=
  ShortComplex.mk
    (biprod.lift (inc C (inf_le_left : U ⊓ V ≤ U)) (-(inc C (inf_le_right : U ⊓ V ≤ V))))
    (biprod.desc (inc C (le_sup_left : U ≤ U ⊔ V)) (inc C (le_sup_right : V ≤ U ⊔ V)))
    (by rw [biprod.lift_desc,Preadditive.neg_comp,inc_comp,inc_comp,add_neg_cancel])

def project (U V : Opens X) : (Opens.mayerVietorisSquare U V).shortComplex ⟶ mv C U V where
  τ₁ := π C (U ⊓ V)
  τ₂ := biprod.map (π C U) (π C V)
  τ₃ := π C (U ⊔ V)
  comm₁₂ := by
    change π C (U ⊓ V) ≫ biprod.lift (inc C inf_le_left) (-(inc C inf_le_right)) =
      biprod.lift (freeOpenMap (inf_le_left : U ⊓ V ≤ U)) (-(freeOpenMap (inf_le_right : U ⊓ V ≤ V))) ≫
        biprod.map (π C U) (π C V)
    apply biprod.hom_ext <;> simp only [Category.assoc,biprod.lift_fst,biprod.lift_snd,
      biprod.map_fst,biprod.map_snd,biprod.lift_fst_assoc,biprod.lift_snd_assoc,
      Preadditive.neg_comp,Preadditive.comp_neg,natural]
  comm₂₃ := by
    change biprod.map (π C U) (π C V) ≫ biprod.desc (inc C le_sup_left) (inc C le_sup_right) =
      biprod.desc (freeOpenMap (le_sup_left : U ≤ U ⊔ V)) (freeOpenMap (le_sup_right : V ≤ U ⊔ V)) ≫ π C (U ⊔ V)
    apply biprod.hom_ext' <;> simp only [biprod.inl_map_assoc,biprod.inr_map_assoc,
      biprod.inl_desc,biprod.inr_desc,biprod.inl_desc_assoc,biprod.inr_desc_assoc,
      natural]

theorem outside_iso (W : Opens X) (x : X) (hx : x ∉ C) : IsIso ((sx x).map (π C W)) := by
  let : Mono (sequence (show W ⊓ C ≤ W from inf_le_left)).f := (shortExact _).mono_f
  apply ((shortExact (show W ⊓ C ≤ W from inf_le_left)).map (sx x)).isIso_g_iff.mpr
  exact CycleQ2FreeOpenAtPoint.zero_outside x (U := W ⊓ C) (fun h ↦ hx h.2)

theorem inside_zero (W : Opens X) (x : X) (hx : x ∈ C) : IsZero ((sx x).obj (M C W)) := by
  apply stalk_zero
  by_cases h : x ∈ W
  · exact Or.inl ⟨h,hx⟩
  · exact Or.inr h

theorem stalk_biprod_iso (U V : Opens X) (x : X) (hx : x ∉ C) :
    IsIso ((sx x).map (biprod.map (π C U) (π C V))) := by
  let F := sx x
  let : F.Additive := stalk_additive x
  let m := biprod.map (F.map (π C U)) (F.map (π C V))
  let e := F.mapBiprod (freeOpen U) (freeOpen V)
  let e' := F.mapBiprod (M C U) (M C V)
  have he : F.map (biprod.map (π C U) (π C V)) ≫ e'.hom = e.hom ≫ m := by
    apply biprod.hom_ext
    · simp only [Category.assoc, e', e, m, Functor.mapBiprod_hom,
        biprod.lift_fst, biprod.map_fst, biprod.lift_fst_assoc, ← F.map_comp]
    · simp only [Category.assoc, e', e, m, Functor.mapBiprod_hom,
        biprod.lift_snd, biprod.map_snd, biprod.lift_snd_assoc, ← F.map_comp]
  have hU : IsIso (F.map (π C U)) := outside_iso C U x hx
  have hV : IsIso (F.map (π C V)) := outside_iso C V x hx
  have : IsIso m := (biprod.mapIso (asIso (F.map (π C U))) (asIso (F.map (π C V)))).isIso_hom
  have : IsIso (F.map (biprod.map (π C U) (π C V)) ≫ e'.hom) := by rw [he]; infer_instance
  exact IsIso.of_isIso_comp_right _ e'.hom

theorem stalk_shortExact (U V : Opens X) (x : X) : ((mv C U V).map (sx x)).ShortExact := by
  let F := sx x
  let : F.Additive := stalk_additive x
  by_cases h : x ∈ C
  · have hm : IsZero (F.obj (M C U ⊞ M C V)) := (F.mapBiprod _ _).isZero_iff.mpr <|
      (biprod_isZero_iff _ _).mpr ⟨inside_zero C U x h, inside_zero C V x h⟩
    exact ShortComplex.ShortExact.mk' (ShortComplex.exact_of_isZero_X₂ ((mv C U V).map (sx x)) hm)
      ⟨fun _ _ _ ↦ (inside_zero C (U ⊓ V) x h).eq_of_tgt _ _⟩
      ⟨fun _ _ _ ↦ (inside_zero C (U ⊔ V) x h).eq_of_src _ _⟩
  · let f := F.mapShortComplex.map (project C U V)
    have : IsIso f.τ₁ := outside_iso C _ x h
    have : IsIso f.τ₂ := stalk_biprod_iso C U V x h
    have : IsIso f.τ₃ := outside_iso C _ x h
    let e := @asIso _ _ _ _ f (ShortComplex.isIso_of_isIso f)
    exact ShortComplex.shortExact_of_iso e ((Opens.mayerVietorisSquare U V).shortComplex_shortExact.map F)

theorem mv_shortExact (U V : Opens X) : (mv C U V).ShortExact where
  exact := (TopCat.Sheaf.exact_iff_stalkFunctor_map_exact _).mpr fun x ↦ (stalk_shortExact C U V x).exact
  mono_f := (TopCat.Presheaf.mono_iff_stalk_mono _).mpr fun x ↦ (stalk_shortExact C U V x).mono_f
  epi_g := by
    let f := project C U V
    have : Epi ((Opens.mayerVietorisSquare U V).shortComplex.g ≫ π C (U ⊔ V)) :=
      epi_comp' (Opens.mayerVietorisSquare U V).shortComplex_shortExact.epi_g (projection_epi C _)
    have : Epi (f.τ₂ ≫ (mv C U V).g) := by rw [f.comm₂₃]; assumption
    exact epi_of_epi f.τ₂ _

theorem glue [HasDerivedCategory.{1} (AbSheaf X)] (U V : Opens X) {T : DerivedCategory (AbSheaf X)}
    (a : (DerivedCategory.singleFunctor _ 0).obj (M C U) ⟶ T)
    (b : (DerivedCategory.singleFunctor _ 0).obj (M C V) ⟶ T)
    (agree : (DerivedCategory.singleFunctor _ 0).map (inc C (inf_le_left : U ⊓ V ≤ U)) ≫ a =
      (DerivedCategory.singleFunctor _ 0).map (inc C (inf_le_right : U ⊓ V ≤ V)) ≫ b) :
    ∃ c : (DerivedCategory.singleFunctor _ 0).obj (M C (U ⊔ V)) ⟶ T,
      (DerivedCategory.singleFunctor _ 0).map (inc C le_sup_left) ≫ c = a ∧
      (DerivedCategory.singleFunctor _ 0).map (inc C le_sup_right) ≫ c = b :=
  CycleQ2BinaryDerivedLift.glue _ _ _ _ (mv C U V).zero (mv_shortExact C U V) a b agree

end CycleQ2SupportMV

namespace CycleQ2SupportSeparated

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open CycleQ2InjectiveCech (AbSheaf)
open CycleQ2SupportMV (M inc mv mv_shortExact)

variable {X : TopCat.{0}} [HasDerivedCategory.{1} (AbSheaf X)] (C U V : Opens X)
private abbrev E := DerivedCategory.singleFunctor (AbSheaf X) 0

theorem eq_of_restrict {T : DerivedCategory (AbSheaf X)}
    (hvan : ∀ g : (E.obj (M C (U ⊓ V)))⟦(1:ℤ)⟧ ⟶ T, g = 0)
    (a b : E.obj (M C (U ⊔ V)) ⟶ T)
    (hu : E.map (inc C (le_sup_left : U ≤ U ⊔ V)) ≫ a = E.map (inc C le_sup_left) ≫ b)
    (hv : E.map (inc C (le_sup_right : V ≤ U ⊔ V)) ≫ a = E.map (inc C le_sup_right) ≫ b) :
    a = b :=
  CycleQ2BinaryDerivedUnique.ext _ _ _ _ (mv C U V).zero (mv_shortExact C U V) hvan hu hv

theorem eq_of_previous_degree (K : DerivedCategory (AbSheaf X)) (q : ℤ)
    (hvan : ∀ g : E.obj (M C (U ⊓ V)) ⟶ K⟦q-1⟧, g = 0)
    (a b : E.obj (M C (U ⊔ V)) ⟶ K⟦q⟧)
    (hu : E.map (inc C (le_sup_left : U ≤ U ⊔ V)) ≫ a = E.map (inc C le_sup_left) ≫ b)
    (hv : E.map (inc C (le_sup_right : V ≤ U ⊔ V)) ≫ a = E.map (inc C le_sup_right) ≫ b) :
    a = b :=
  by
    apply eq_of_restrict C U V _ a b hu hv
    intro g
    let F := shiftFunctor (DerivedCategory (AbSheaf X)) (1:ℤ)
    let e := (shiftFunctorAdd' (DerivedCategory (AbSheaf X)) (q-1) 1 q (by omega)).app K
    let p : E.obj (M C (U ⊓ V)) ⟶ K⟦q-1⟧ := F.preimage (g ≫ e.hom)
    have hp : F.map p = g ≫ e.hom := F.map_preimage _
    apply (cancel_mono e.hom).1
    rw [← hp, hvan p, F.map_zero, zero_comp]

end CycleQ2SupportSeparated

namespace CycleQ2NoetherianSupport

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open CycleQ2InjectiveCech (AbSheaf freeOpenMap)
open CycleQ2MayerVietorisRestriction (freeOpenSheaf)
open CycleQ2SupportMV (M inc inc_comp π natural)

variable {X : TopCat.{0}} [HasDerivedCategory.{1} (AbSheaf X)] (C : Opens X)
private abbrev E := DerivedCategory.singleFunctor (AbSheaf X) 0

omit [HasDerivedCategory.{1} (AbSheaf X)] in
private theorem inc_self (W : Opens X) : inc C (le_rfl : W ≤ W) = 𝟙 _ := by
  apply (cancel_epi (π C W)).mp
  rw [natural,Category.comp_id]
  have e : freeOpenMap (le_rfl : W ≤ W) = 𝟙 _ := freeOpenSheaf.map_id W
  rw [e,Category.id_comp]

omit [HasDerivedCategory.{1} (AbSheaf X)] in
private theorem bot_zero : IsZero (M C ⊥) := by
  let h : (⊥ : Opens X) ⊓ C ≤ ⊥ := inf_le_left
  have : IsIso (homOfLE h) := homOfLE_isIso_of_eq h (by simp)
  have : IsIso (freeOpenMap h) := inferInstanceAs (IsIso (freeOpenSheaf.map (homOfLE h)))
  exact isZero_cokernel_of_epi (freeOpenMap h)

abbrev res {V W : Opens X} (h : V ≤ W) {T : DerivedCategory (AbSheaf X)}
    (a : E.obj (M C W) ⟶ T) : E.obj (M C V) ⟶ T :=
  E.map (inc C h) ≫ a

private theorem res_comp {V W D : Opens X} (h : D ≤ V) (j : V ≤ W)
    {T : DerivedCategory (AbSheaf X)} (a : E.obj (M C W) ⟶ T) :
    res C h (res C j a) = res C (h.trans j) a := by
  simp only [res,← Category.assoc,← CategoryTheory.Functor.map_comp,inc_comp]

private theorem res_self (W : Opens X) {T : DerivedCategory (AbSheaf X)}
    (a : E.obj (M C W) ⟶ T) : res C le_rfl a = a := by
  simp only [res,inc_self,CategoryTheory.Functor.map_id,Category.id_comp]

private instance bot_subsingleton (T : DerivedCategory (AbSheaf X)) :
    Subsingleton (E.obj (M C ⊥) ⟶ T) :=
  ⟨(E.map_isZero (bot_zero C)).eq_of_src⟩

theorem eq_of_local [NoetherianSpace X] (K : DerivedCategory (AbSheaf X)) (q : ℤ)
    (hvan : ∀ V (g : E.obj (M C V) ⟶ K⟦q-1⟧), g = 0)
    {W : Opens X} {a b : E.obj (M C W) ⟶ K⟦q⟧}
    (h : ∀ x ∈ W, ∃ (V : Opens X) (v : V ≤ W), x ∈ V ∧ res C v a = res C v b) : a = b :=
  CycleQ2LocalDescent.eq_of_local (fun j z => res C j z)
    (fun i j z => res_comp C i j z) (fun z => res_self C _ z)
    (fun U V => CycleQ2SupportSeparated.eq_of_previous_degree C U V K q (hvan _)) h

/-- Local compatible supported degree-q classes on a Noetherian space glue when
the supported maps in the preceding degree vanish on opens. -/
theorem global [NoetherianSpace X] (K : DerivedCategory (AbSheaf X)) (q : ℤ)
    (hvan : ∀ W (g : E.obj (M C W) ⟶ K⟦q-1⟧), g = 0)
    {ι : Type*} (U : ι → Opens X) (a : ∀ n, E.obj (M C (U n)) ⟶ K⟦q⟧)
    (cover : ∀ x : X, ∃ n, x ∈ U n)
    (agree : ∀ n m (x : X), x ∈ U n → x ∈ U m →
      ∃ (D : Opens X) (d : D ≤ U n) (e : D ≤ U m), x ∈ D ∧ res C d (a n) = res C e (a m)) :
    ∃ s : E.obj (M C ⊤) ⟶ K⟦q⟧, ∀ n, res C le_top s = a n := by
  letI : Nonempty (E.obj (M C ⊥) ⟶ K⟦q⟧) := ⟨0⟩
  exact CycleQ2LocalDescent.exists_global (fun j z => res C j z)
    (fun i j z => res_comp C i j z) (fun z => res_self C _ z)
    (fun V W => CycleQ2SupportSeparated.eq_of_previous_degree C V W K q (hvan _))
    (fun V W => CycleQ2SupportMV.glue C V W) U a cover agree

end CycleQ2NoetherianSupport

namespace CycleQ2SupportPurityDescent

open CategoryTheory AlgebraicGeometry TopologicalSpace
open CycleQ2IntrinsicDeRhamSheaves (relativeDeRhamInt)
open CycleQ2InjectiveCech (AbSheaf)
open CycleQ2SupportMV (M)
open CycleQ2NoetherianSupport (res)

variable {k : Type} [Field k] [CharZero k] {X : Scheme.{0}}
    (p : X ⟶ Spec (CommRingCat.of k)) (r : ℕ) [SmoothOfRelativeDimension r p]
    [HasDerivedCategory.{1} (AbSheaf (show TopCat from X))]
    [NoetherianSpace X] (C : X.Opens)
private abbrev E := DerivedCategory.singleFunctor (AbSheaf (show TopCat from X)) 0
private abbrev K : DerivedCategory.{1} (AbSheaf (show TopCat from X)) :=
  DerivedCategory.Q.obj (relativeDeRhamInt p r)

/-- Local annihilation of every class through degree n implies its
vanishing on every open. The negative base case follows from the actual
relative complex being concentrated in nonnegative degrees. -/
theorem vanish (n : ℕ)
    (loc : ∀ (j : ℕ), j ≤ n → ∀ (W : X.Opens) (a : E.obj (M C W) ⟶ (K p r)⟦(j:ℤ)⟧),
      ∀ x ∈ W, ∃ (V : X.Opens) (h : V ≤ W), x ∈ V ∧ res C h a = 0)
    (W : X.Opens) (a : E.obj (M C W) ⟶ (K p r)⟦(n:ℤ)⟧) : a = 0 := by
  induction n generalizing W with
  | zero =>
    refine CycleQ2NoetherianSupport.eq_of_local C (K p r) 0 ?_ (W := W) ?_
    · intro D f
      exact CycleQ2DeRhamNegative.eq_zero p r (M C D) (0-1) (by decide) f
    · intro x hx
      obtain ⟨V,h,hxV,he⟩ := loc 0 le_rfl W a x hx
      exact ⟨V,h,hxV,by simpa only [res,CategoryTheory.Limits.comp_zero] using he⟩
  | succ n ih =>
    refine CycleQ2NoetherianSupport.eq_of_local C (K p r) ((n+1:ℕ):ℤ) ?_ (W := W) ?_
    · intro D
      have he : ((n+1:ℕ):ℤ) - 1 = (n:ℤ) := by omega
      rw [he]
      exact ih (fun j hj => loc j (Nat.le_succ_of_le hj)) D
    · intro x hx
      obtain ⟨V,h,hxV,he⟩ := loc (n+1) le_rfl W a x hx
      exact ⟨V,h,hxV,by simpa only [res,CategoryTheory.Limits.comp_zero] using he⟩

/-- A locally compatible family of graph classes in degree four has a global
representative when the supported de Rham groups vanish locally below four. -/
theorem glue_four
    (loc : ∀ (j : ℕ), j ≤ 3 → ∀ (W : X.Opens) (a : E.obj (M C W) ⟶ (K p r)⟦(j:ℤ)⟧),
      ∀ x ∈ W, ∃ (V : X.Opens) (h : V ≤ W), x ∈ V ∧ res C h a = 0)
    {ι : Type*} (U : ι → X.Opens) (a : ∀ n, E.obj (M C (U n)) ⟶ (K p r)⟦(4:ℤ)⟧)
    (cover : ∀ x : X, ∃ n, x ∈ U n)
    (agree : ∀ n m (x : X), x ∈ U n → x ∈ U m →
      ∃ (D : X.Opens) (d : D ≤ U n) (e : D ≤ U m), x ∈ D ∧ res C d (a n) = res C e (a m)) :
    ∃ s : E.obj (M C ⊤) ⟶ (K p r)⟦(4:ℤ)⟧, ∀ n, res C le_top s = a n :=
  CycleQ2NoetherianSupport.global C (K p r) 4 (vanish p r C 3 loc) U a cover agree

end CycleQ2SupportPurityDescent
