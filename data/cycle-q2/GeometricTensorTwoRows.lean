import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.Algebra.Homology.Monoidal
import Mathlib.Algebra.Homology.Embedding.Extend

/-! The two rows of the ordinary total tensor complex with a complex in
curve degrees zero and one.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md. -/

noncomputable section
set_option autoImplicit false
namespace CycleQ2TensorTwoRows

open CategoryTheory CategoryTheory.Limits MonoidalCategory HomologicalComplex
variable {k : Type} [Field k]
private abbrev M := ModuleCat.{0} k
private abbrev C := CochainComplex (M (k := k)) ℤ
private abbrev F := curriedTensor (M (k := k))

variable (P L : C (k := k))
private abbrev T := tensorObj P L
private abbrev W (a b : ℤ) := (F.obj (P.X a)).obj (L.X b)
abbrev terms (n : ℤ) := W P L 0 (n+1) ⊞ W P L 1 n

private def pick (n a b : ℤ) (h : a+b=n+1) : W P L a b ⟶ terms P L n :=
  if h₀ : a=0 then by
    subst a
    have hb : b=n+1 := by omega
    subst b
    exact biprod.inl
  else if h₁ : a=1 then by
    subst a
    have hb : b=n := by omega
    subst b
    exact biprod.inr
  else 0

private def project (n : ℤ) : (T P L).X (n+1) ⟶ terms P L n :=
  mapBifunctorDesc (K₁ := P) (K₂ := L) (F := F (k := k)) (c := .up ℤ) (pick P L n)

def inclZero (n : ℤ) := ιTensorObj P L 0 (n+1) (n+1) (zero_add _)
def inclOne (n : ℤ) := ιTensorObj P L 1 n (n+1) (by omega)
private def assemble (n : ℤ) : terms P L n ⟶ (T P L).X (n+1) :=
  biprod.desc (inclZero P L n) (inclOne P L n)

private theorem zero_project (n : ℤ) : inclZero P L n ≫ project P L n = biprod.inl := by
  unfold inclZero project
  erw [ι_mapBifunctorDesc]
  rfl

private theorem one_project (n : ℤ) : inclOne P L n ≫ project P L n = biprod.inr := by
  unfold inclOne project
  erw [ι_mapBifunctorDesc]
  rfl

variable (hP : ∀ a : ℤ, a≠0 → a≠1 → IsZero (P.X a))

/-- The ordinary coproduct over all bidegrees is exactly its curve-zero and
curve-one summands when all other curve coefficients vanish. -/
def components (n : ℤ) : (T P L).X (n+1) ≅ terms P L n where
  hom := project P L n
  inv := assemble P L n
  hom_inv_id := by
    apply mapBifunctor.hom_ext
    intro a b h
    change a+b=n+1 at h
    by_cases h₀ : a=0
    · subst a
      have h' : b=n+1 := by omega
      subst b
      erw [← Category.assoc,zero_project,Category.comp_id,biprod.inl_desc]
      rfl
    by_cases h₁ : a=1
    · subst a
      have h' : b=n := by omega
      subst b
      erw [← Category.assoc,one_project,Category.comp_id,biprod.inr_desc]
      rfl
    exact (((F (k := k)).flip.obj (L.X b)).map_isZero (hP a h₀ h₁)).eq_of_src _ _
  inv_hom_id := by
    apply biprod.hom_ext'
    · erw [← Category.assoc,biprod.inl_desc,zero_project,Category.comp_id]
      rfl
    · erw [← Category.assoc,biprod.inr_desc,one_project,Category.comp_id]
      rfl

private theorem summand_d (a b n : ℤ) (h : a+b=n) :
    ιTensorObj P L a b n h ≫ (T P L).d n (n+1) =
      (F.map (P.d a (a+1))).app (L.X b) ≫ ιTensorObj P L (a+1) b (n+1) (by omega) +
      a.negOnePow • ((F.obj (P.X a)).map (L.d b (b+1)) ≫
        ιTensorObj P L a (b+1) (n+1) (by omega)) := by
  erw [mapBifunctor.d_eq,Preadditive.comp_add,mapBifunctor.ι_D₁,mapBifunctor.ι_D₂,
    mapBifunctor.d₁_eq P L F (.up ℤ) (show (ComplexShape.up ℤ).Rel a (a+1) from rfl) b (n+1)
      (by change a+1+b=n+1; omega),
    mapBifunctor.d₂_eq P L F (.up ℤ) a (show (ComplexShape.up ℤ).Rel b (b+1) from rfl) (n+1)
      (by change a+(b+1)=n+1; omega)]
  have hε : ComplexShape.ε₁ (.up ℤ) (.up ℤ) (.up ℤ) (a,b) = 1 := rfl
  rw [hε,one_smul]
  rfl

/-- The matrix differential of the two-row total complex. -/
def next (n : ℤ) : terms P L n ⟶ terms P L (n+1) :=
  biprod.desc
    ((F.map (P.d 0 1)).app (L.X (n+1)) ≫ biprod.inr +
      (F.obj (P.X 0)).map (L.d (n+1) (n+1+1)) ≫ biprod.inl)
    (-((F.obj (P.X 1)).map (L.d n (n+1)) ≫ biprod.inr))

theorem components_d (n : ℤ) :
    (components P L hP n).inv ≫ (T P L).d (n+1) (n+1+1) ≫ (components P L hP (n+1)).hom =
      next P L n := by
  apply biprod.hom_ext'
  · change biprod.inl ≫ assemble P L n ≫ _ ≫ project P L (n+1) = biprod.inl ≫ _
    erw [← Category.assoc,biprod.inl_desc,← Category.assoc]
    unfold inclZero
    erw [summand_d,Preadditive.add_comp,biprod.inl_desc]
    simp only [Int.negOnePow_zero,one_smul,Category.assoc]
    erw [zero_project,one_project]
    rfl
  · change biprod.inr ≫ assemble P L n ≫ _ ≫ project P L (n+1) = biprod.inr ≫ _
    erw [← Category.assoc,biprod.inr_desc,← Category.assoc]
    unfold inclOne
    erw [summand_d,Preadditive.add_comp,biprod.inr_desc]
    have hd : P.d 1 2 = 0 := (hP 2 (by decide) (by decide)).eq_of_tgt _ _
    erw [hd,Functor.map_zero]
    simp only [zero_app,zero_comp,zero_add,Int.negOnePow_one,Units.neg_smul,one_smul,Preadditive.neg_comp,
      Category.assoc]
    erw [one_project]
    rfl


namespace Extension
open scoped MonoidalCategory

variable (V H : CochainComplex (M (k := k)) ℕ)
private abbrev E := ComplexShape.embeddingUpNat
private abbrev PV := V.extend E
private abbrev LH := H.extend E
private abbrev H0 (n : ℕ) := V.X 0 ⊗ H.X n
private abbrev H1 (n : ℕ) := V.X 1 ⊗ H.X n

variable (hV : ∀ n, 2 ≤ n → IsZero (V.X n))

include hV in
theorem supported (a : ℤ) (ha : a≠0) (ha' : a≠1) : IsZero ((PV V).X a) := by
  cases a with
  | ofNat n =>
    change (n:ℤ) ≠ 0 at ha
    change (n:ℤ) ≠ 1 at ha'
    apply (hV n (by omega)).of_iso (V.extendXIso E (i := n) rfl)
  | negSucc n => exact V.isZero_extend_X E _ (fun i hi => by change (i:ℤ) = Int.negSucc n at hi; omega)

private abbrev χ (p q : ℕ) :
    ((PV V).X (p:ℤ) ⊗ (LH H).X (q:ℤ)) ≅ (V.X p ⊗ H.X q) :=
  V.extendXIso E (i := p) rfl ⊗ᵢ H.extendXIso E (i := q) rfl

include hV in
/-- The positive-degree coefficients after the two nonnegative complexes are
extended to the integer indices of the actual tensor complex. -/
def positive (n : ℕ) :
    (tensorObj (PV V) (LH H)).X ((n:ℤ)+1) ≅ H0 V H (n+1) ⊞ H1 V H n :=
  components (PV V) (LH H) (supported V hV) (n:ℤ) ≪≫
    biprod.mapIso (χ V H 0 (n+1)) (χ V H 1 n)

@[reassoc]
private theorem χ_left (p q : ℕ) :
    (χ V H p q).inv ≫ (F.map ((PV V).d (p:ℤ) ((p:ℤ)+1))).app ((LH H).X (q:ℤ)) ≫
      (χ V H (p+1) q).hom = (F.map (V.d p (p+1))).app (H.X q) := by
  let ep := V.extendXIso E (i := p) rfl
  let ep' := V.extendXIso E (i := p+1) rfl
  let eq := H.extendXIso E (i := q) rfl
  change (ep.inv ⊗ₘ eq.inv) ≫ ((PV V).d (p:ℤ) ((p:ℤ)+1) ▷ (LH H).X (q:ℤ)) ≫
    (ep'.hom ⊗ₘ eq.hom) = V.d p (p+1) ▷ H.X q
  erw [← tensorHom_id,← tensorHom_id,tensorHom_comp_tensorHom,tensorHom_comp_tensorHom]
  have hd : (PV V).d (p:ℤ) ((p:ℤ)+1) = ep.hom ≫ V.d p (p+1) ≫ ep'.inv :=
    V.extend_d_eq E (i := p) (j := p+1) rfl rfl
  erw [hd,Category.assoc,ep.inv_hom_id_assoc,Category.assoc,ep'.inv_hom_id,Category.comp_id,
    Category.id_comp,eq.inv_hom_id]

@[reassoc]
private theorem χ_right (p q : ℕ) :
    (χ V H p q).inv ≫ (F.obj ((PV V).X (p:ℤ))).map ((LH H).d (q:ℤ) ((q:ℤ)+1)) ≫
      (χ V H p (q+1)).hom = (F.obj (V.X p)).map (H.d q (q+1)) := by
  let ep := V.extendXIso E (i := p) rfl
  let eq := H.extendXIso E (i := q) rfl
  let eq' := H.extendXIso E (i := q+1) rfl
  change (ep.inv ⊗ₘ eq.inv) ≫ ((PV V).X (p:ℤ) ◁ (LH H).d (q:ℤ) ((q:ℤ)+1)) ≫
    (ep.hom ⊗ₘ eq'.hom) = V.X p ◁ H.d q (q+1)
  erw [← id_tensorHom,← id_tensorHom,tensorHom_comp_tensorHom,tensorHom_comp_tensorHom]
  have hd : (LH H).d (q:ℤ) ((q:ℤ)+1) = eq.hom ≫ H.d q (q+1) ≫ eq'.inv :=
    H.extend_d_eq E (i := q) (j := q+1) rfl rfl
  erw [hd,Category.assoc,eq.inv_hom_id_assoc,Category.assoc,eq'.inv_hom_id,Category.comp_id,
    Category.id_comp,ep.inv_hom_id]

def positiveNext (n : ℕ) : H0 V H (n+1) ⊞ H1 V H n ⟶ H0 V H (n+2) ⊞ H1 V H (n+1) :=
  biprod.desc
    ((F.map (V.d 0 1)).app (H.X (n+1)) ≫ biprod.inr +
      (F.obj (V.X 0)).map (H.d (n+1) (n+2)) ≫ biprod.inl)
    (-((F.obj (V.X 1)).map (H.d n (n+1)) ≫ biprod.inr))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem positive_d (n : ℕ) :
    (positive V H hV n).inv ≫ (tensorObj (PV V) (LH H)).d ((n:ℤ)+1) ((n:ℤ)+1+1) ≫
      (positive V H hV (n+1)).hom = positiveNext V H n := by
  let e := components (PV V) (LH H) (supported V hV) (n:ℤ)
  let e' := components (PV V) (LH H) (supported V hV) ((n:ℤ)+1)
  let b := biprod.mapIso (χ V H 0 (n+1)) (χ V H 1 n)
  let b' := biprod.mapIso (χ V H 0 (n+2)) (χ V H 1 (n+1))
  have hc := components_d (PV V) (LH H) (supported V hV) (n:ℤ)
  change (b.inv ≫ e.inv) ≫ _ ≫ e'.hom ≫ b'.hom = _
  erw [Category.assoc,←Category.assoc _ e'.hom,←Category.assoc e.inv,hc]
  apply biprod.hom_ext'
  · dsimp only [b,b',biprod.mapIso,positiveNext,next]
    simp only [biprod.inl_map_assoc,biprod.inl_desc,biprod.inl_desc_assoc,Category.assoc,Preadditive.comp_add,Preadditive.add_comp,
      biprod.inl_map,biprod.inr_map]
    erw [χ_left_assoc V H 0 (n+1),χ_right_assoc V H 0 (n+1)]
    rfl
  · dsimp only [b,b',biprod.mapIso,positiveNext,next]
    simp only [biprod.inr_map_assoc,biprod.inr_desc,biprod.inr_desc_assoc,Category.assoc,Preadditive.comp_neg,Preadditive.neg_comp,
      biprod.inr_map]
    erw [χ_right_assoc V H 1 n]
    rfl

private theorem lowerZero (n : ℤ) (hn : n<0) : IsZero ((LH H).X n) :=
  H.isZero_extend_X E n (fun i hi => by change (i:ℤ)=n at hi; omega)

private def bottomDrop : terms (PV V) (LH H) (-1) ≅ W (PV V) (LH H) 0 0 :=
  (isoBiprodZero (((F (k := k)).obj ((PV V).X 1)).map_isZero (lowerZero H (-1) (by decide)))).symm

include hV in
/-- Only the horizontal zeroth coefficient survives in total degree zero. -/
def bottom :
    (tensorObj (PV V) (LH H)).X 0 ≅ H0 V H 0 :=
  show (tensorObj (PV V) (LH H)).X ((-1:ℤ)+1) ≅ _ from
    components (PV V) (LH H) (supported V hV) (-1) ≪≫ bottomDrop V H ≪≫ χ V H 0 0

def bottomNext : H0 V H 0 ⟶ H0 V H 1 ⊞ H1 V H 0 :=
  (F.map (V.d 0 1)).app (H.X 0) ≫ biprod.inr + (F.obj (V.X 0)).map (H.d 0 1) ≫ biprod.inl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem bottom_d :
    (bottom V H hV).inv ≫ (tensorObj (PV V) (LH H)).d 0 1 ≫ (positive V H hV 0).hom =
      bottomNext V H := by
  let e := components (PV V) (LH H) (supported V hV) (-1)
  let e' := components (PV V) (LH H) (supported V hV) 0
  let b' := biprod.mapIso (χ V H 0 1) (χ V H 1 0)
  have hc := components_d (PV V) (LH H) (supported V hV) (-1)
  change (((χ V H 0 0).inv ≫ biprod.inl) ≫ e.inv) ≫ _ ≫ e'.hom ≫ b'.hom = _
  erw [Category.assoc,← Category.assoc _ e'.hom,← Category.assoc e.inv,hc,Category.assoc]
  dsimp only [b',biprod.mapIso,next,bottomNext]
  simp only [biprod.inl_desc_assoc,Preadditive.add_comp,Category.assoc,biprod.inr_map,biprod.inl_map,
    Preadditive.comp_add]
  erw [χ_left_assoc V H 0 0,χ_right_assoc V H 0 0]
  rfl

include hV in
/-- Negative tensor degrees vanish because both original rows are nonnegative. -/
theorem negative (n : ℤ) (hn : n<0) :
    IsZero ((tensorObj (PV V) (LH H)).X n) := by
  obtain ⟨a, rfl⟩ : ∃ a, n=a+1 := ⟨n-1,by omega⟩
  let e := components (PV V) (LH H) (supported V hV) a
  have hz : IsZero (terms (PV V) (LH H) a) := (biprod_isZero_iff _ _).2
    ⟨((F (k := k)).obj ((PV V).X 0)).map_isZero (lowerZero H _ hn),
      ((F (k := k)).obj ((PV V).X 1)).map_isZero (lowerZero H a (by omega))⟩
  exact hz.of_iso e

end Extension

section Maps
open scoped MonoidalCategory
variable {P' L' : C (k := k)} (f : P ⟶ P') (g : L ⟶ L')
  (hP' : ∀ a : ℤ, a≠0 → a≠1 → IsZero (P'.X a))

@[reassoc]
private theorem inclusion_map (a b n : ℤ) (h : a+b=n) :
    ιTensorObj P L a b n h ≫ (HomologicalComplex.tensorHom f g).f n =
      (f.f a ⊗ₘ g.f b) ≫ ιTensorObj P' L' a b n h := by
  erw [ι_mapBifunctorMap,tensorHom_def,Category.assoc]
  rfl

/-- Each of the two surviving tensor rows carries the corresponding component
of the two given chain maps. -/
theorem components_map (n : ℤ) :
    (components P L hP n).inv ≫ (HomologicalComplex.tensorHom f g).f (n+1) ≫
      (components P' L' hP' n).hom =
      biprod.map (f.f 0 ⊗ₘ g.f (n+1)) (f.f 1 ⊗ₘ g.f n) := by
  apply biprod.hom_ext'
  · change biprod.inl ≫ assemble P L n ≫ _ ≫ project P' L' n = _
    erw [← Category.assoc,biprod.inl_desc,inclusion_map_assoc P L f g 0 (n+1) (n+1) (zero_add _),
      zero_project,biprod.inl_map]
    rfl
  · change biprod.inr ≫ assemble P L n ≫ _ ≫ project P' L' n = _
    erw [← Category.assoc,biprod.inr_desc,inclusion_map_assoc P L f g 1 n (n+1) (by omega),
      one_project,biprod.inr_map]
    rfl
end Maps

namespace Extension
open scoped MonoidalCategory
variable (V H : CochainComplex (M (k := k)) ℕ) {V' H' : CochainComplex (M (k := k)) ℕ}
  (f : V ⟶ V') (g : H ⟶ H')
  (hV : ∀ n, 2 ≤ n → IsZero (V.X n)) (hV' : ∀ n, 2 ≤ n → IsZero (V'.X n))

@[reassoc]
private theorem χ_map (p q : ℕ) :
    (χ V H p q).inv ≫ ((extendMap f E).f (p:ℤ) ⊗ₘ (extendMap g E).f (q:ℤ)) ≫
      (χ V' H' p q).hom = (f.f p ⊗ₘ g.f q) := by
  let ep := V.extendXIso E (i := p) rfl
  let eq := H.extendXIso E (i := q) rfl
  let ep' := V'.extendXIso E (i := p) rfl
  let eq' := H'.extendXIso E (i := q) rfl
  have hf : (extendMap f E).f (p:ℤ) = ep.hom ≫ f.f p ≫ ep'.inv := extendMap_f f E rfl
  have hg : (extendMap g E).f (q:ℤ) = eq.hom ≫ g.f q ≫ eq'.inv := extendMap_f g E rfl
  change (ep.inv ⊗ₘ eq.inv) ≫ _ ≫ (ep'.hom ⊗ₘ eq'.hom) = _
  erw [hf,hg,tensorHom_comp_tensorHom,tensorHom_comp_tensorHom]
  erw [Category.assoc ep.hom,ep.inv_hom_id_assoc,Category.assoc (f.f p),ep'.inv_hom_id,
    Category.comp_id,Category.assoc eq.hom,eq.inv_hom_id_assoc,Category.assoc (g.f q),eq'.inv_hom_id,
    Category.comp_id]

/-- Vertical and horizontal restriction on the original nonnegative modules
gives the two component maps in every positive total degree. -/
theorem positive_map (n : ℕ) :
    (positive V H hV n).inv ≫
      (HomologicalComplex.tensorHom (extendMap f E) (extendMap g E)).f ((n:ℤ)+1) ≫
      (positive V' H' hV' n).hom =
      biprod.map (f.f 0 ⊗ₘ g.f (n+1)) (f.f 1 ⊗ₘ g.f n) := by
  let e := components (PV V) (LH H) (supported V hV) (n:ℤ)
  let e' := components (PV V') (LH H') (supported V' hV') (n:ℤ)
  let b := biprod.mapIso (χ V H 0 (n+1)) (χ V H 1 n)
  let b' := biprod.mapIso (χ V' H' 0 (n+1)) (χ V' H' 1 n)
  have h := components_map (PV V) (LH H) (supported V hV)
    (extendMap f E) (extendMap g E) (supported V' hV') (n:ℤ)
  change (b.inv ≫ e.inv) ≫ _ ≫ e'.hom ≫ b'.hom = _
  erw [Category.assoc,← Category.assoc _ e'.hom,← Category.assoc e.inv,h]
  apply biprod.hom_ext'
  · dsimp only [b,b',biprod.mapIso]
    simp only [biprod.inl_map_assoc,biprod.inl_map]
    erw [χ_map_assoc V H f g 0 (n+1)]
  · dsimp only [b,b',biprod.mapIso]
    simp only [biprod.inr_map_assoc,biprod.inr_map]
    erw [χ_map_assoc V H f g 1 n]

/-- In degree zero there is only the tensor of the two degree-zero maps. -/
theorem bottom_map :
    (bottom V H hV).inv ≫
      (HomologicalComplex.tensorHom (extendMap f E) (extendMap g E)).f 0 ≫
      (bottom V' H' hV').hom = (f.f 0 ⊗ₘ g.f 0) := by
  let e := components (PV V) (LH H) (supported V hV) (-1)
  let e' := components (PV V') (LH H') (supported V' hV') (-1)
  have h := components_map (PV V) (LH H) (supported V hV)
    (extendMap f E) (extendMap g E) (supported V' hV') (-1)
  change (((χ V H 0 0).inv ≫ biprod.inl) ≫ e.inv) ≫ _ ≫ e'.hom ≫ biprod.fst ≫ (χ V' H' 0 0).hom = _
  erw [Category.assoc,← Category.assoc _ e'.hom,← Category.assoc e.inv,h,
    Category.assoc,biprod.inl_map_assoc,biprod.inl_fst_assoc,χ_map V H f g 0 0]

end Extension

end CycleQ2TensorTwoRows

#print axioms CycleQ2TensorTwoRows.components_d
#print axioms CycleQ2TensorTwoRows.Extension.positive_d
#print axioms CycleQ2TensorTwoRows.Extension.bottom_d
#print axioms CycleQ2TensorTwoRows.Extension.negative

#print axioms CycleQ2TensorTwoRows.Extension.positive_map
#print axioms CycleQ2TensorTwoRows.Extension.bottom_map
