import Proposal.GeometricMonicGenericSupport
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone
import Mathlib.Algebra.Homology.Embedding.ExtendHomotopy
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Homology.Monoidal
import Mathlib.Algebra.Homology.BifunctorHomotopy
import Mathlib.Algebra.Homology.BifunctorShift

/-! The signed mapping fiber of the two affine curve restrictions computes
the curve tensor complex used in the proper trace. Its restrictions on both
functions and differentials are induced by the original scheme charts.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md. -/

noncomputable section
set_option autoImplicit false

namespace CycleQ2TensorMappingCone


open CategoryTheory CategoryTheory.Limits MonoidalCategory HomologicalComplex CochainComplex
open HomologicalComplex.homotopyCofiber

variable {k : Type} [Field k]
private abbrev M := ModuleCat.{0} k
private abbrev C := CochainComplex (M (k := k)) ℤ
variable {X Y : C (k := k)} (φ : X ⟶ Y) (L : C (k := k))

private abbrev F := curriedTensor (M (k := k))
private abbrev T := tensorHom φ (𝟙 L)
private abbrev G (j : ℤ) := (curriedTensor (M (k := k))).flip.obj (L.X j)
private abbrev Z := mappingCone φ
private abbrev E := mappingCone (T φ L)
private theorem prev (i : ℤ) : ∃ j, (ComplexShape.up ℤ).Rel j i :=
  ⟨i-1,by change i-1+1=i; omega⟩

private def changeEndpoints {P R : C (k := k)} {a b a' b' : P ⟶ R}
    (H : Homotopy a b) (e : a' = a) (f : b' = b) : Homotopy a' b' where
  hom := H.hom
  zero := H.zero
  comm i := by rw [e,f]; exact H.comm i

private def lifted : Homotopy (T φ L ≫ tensorHom (inr φ) (𝟙 L)) 0 := by
  let H := mapBifunctorMapHomotopy₁ (inrCompHomotopy φ prev) (𝟙 L)
    (F (k := k)) (.up ℤ)
  refine changeEndpoints H ?_ ?_
  · let B := (F (k := k)).map₂CochainComplex.flip.obj L
    change B.map φ ≫ B.map (inr φ) = B.map (φ ≫ inr φ)
    rw [Functor.map_comp]
  · apply HomologicalComplex.Hom.ext
    funext i
    apply mapBifunctor.hom_ext
    intro a b h
    simp [F]

/-- The canonical tensor-cone comparison is induced by the actual nullhomotopy
of the composite into the cone, tensored in its first variable. -/
def compare : E φ L ⟶ tensorObj (Z φ) L :=
  homotopyCofiber.desc (T φ L) (tensorHom (inr φ) (𝟙 L)) (lifted φ L)

@[reassoc]
private theorem inr_component (a b n : ℤ) (h : a+b=n) :
    ιTensorObj Y L a b n h ≫ inrX (T φ L) n ≫ (compare φ L).f n =
      (G L b).map (inrX φ a) ≫ ιTensorObj (Z φ) L a b n h := by
  unfold compare
  erw [homotopyCofiber.inrX_desc_f]
  change _ ≫ (mapBifunctorMap (inr φ) (𝟙 L) _ _).f n = _
  erw [ι_mapBifunctorMap]
  simp only [HomologicalComplex.id_f]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  rfl

@[reassoc]
private theorem inl_component (a b n : ℤ) (h : a+1+b=n+1) :
    ιTensorObj X L (a+1) b (n+1) h ≫ inlX (T φ L) (n+1) n rfl ≫ (compare φ L).f n =
      (G L b).map (inlX φ (a+1) a rfl) ≫
        ιTensorObj (Z φ) L a b n (by omega) := by
  unfold compare
  erw [homotopyCofiber.inlX_desc_f]
  let H := inrCompHomotopy φ prev
  change _ ≫ mapBifunctorMapHomotopy.hom₁ H (𝟙 L) (F (k := k)) (.up ℤ) (n+1) n = _
  have ha : (ComplexShape.up ℤ).prev (a+1) = a := (ComplexShape.up ℤ).prev_eq' (show (ComplexShape.up ℤ).Rel a (a+1) from rfl)
  erw [mapBifunctorMapHomotopy.ιMapBifunctor_hom₁ H (𝟙 L) (F (k := k)) (.up ℤ)
    a (a+1) b (n+1) n h ha, ιMapBifunctorOrZero_eq _ _ _ _ a b n (by change a+b=n; omega)]
  have hε : ComplexShape.ε₁ (.up ℤ) (.up ℤ) (.up ℤ) (a,b) = 1 := rfl
  rw [hε,one_smul]
  simp only [HomologicalComplex.id_f,H,inrCompHomotopy_hom _ _ _ _ (show (ComplexShape.up ℤ).Rel a (a+1) from rfl)]
  erw [CategoryTheory.Functor.map_id,Category.id_comp]
  rfl

/-- The inverse in degree n recovers the source and target summands of the
underlying cone before tensoring. The source uses curve degree a+1. -/
private def inverseAt (n : ℤ) : (tensorObj (Z φ) L).X n ⟶ (E φ L).X n :=
  mapBifunctorDesc (K₁ := Z φ) (K₂ := L) (F := F (k := k)) (c := .up ℤ)
    fun a b h =>
      (G L b).map (fstX φ a (a+1) rfl) ≫
        ιTensorObj X L (a+1) b (n+1) (by change a+b=n at h; omega) ≫
        inlX (T φ L) (n+1) n rfl +
      (G L b).map (sndX φ a) ≫ ιTensorObj Y L a b n h ≫ inrX (T φ L) n

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem compare_inverse (n : ℤ) :
    (compare φ L).f n ≫ inverseAt φ L n = 𝟙 _ := by
  apply homotopyCofiber.ext_from_X (T φ L) (n+1) n rfl
  · apply mapBifunctor.hom_ext
    intro a b h
    change a+b=n+1 at h
    obtain ⟨a,rfl⟩ : ∃ a', a=a'+1 := ⟨a-1,by omega⟩
    erw [inl_component_assoc φ L a b n h,Category.assoc]
    simp only [inverseAt,ι_mapBifunctorDesc,Preadditive.comp_add,
      ← Functor.map_comp_assoc,inlX_fstX,inlX_sndX,Functor.map_zero,zero_comp,add_zero]
    erw [CategoryTheory.Functor.map_id, Category.id_comp]
  · apply mapBifunctor.hom_ext
    intro a b h
    change a+b=n at h
    erw [inr_component_assoc φ L a b n h,Category.assoc]
    simp only [inverseAt,ι_mapBifunctorDesc,Preadditive.comp_add,
      ← Functor.map_comp_assoc,inrX_fstX,inrX_sndX,Functor.map_zero,zero_comp,zero_add]
    erw [CategoryTheory.Functor.map_id, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem inverse_compare (n : ℤ) :
    inverseAt φ L n ≫ (compare φ L).f n = 𝟙 _ := by
  apply mapBifunctor.hom_ext
  intro a b h
  change a+b=n at h
  unfold inverseAt
  erw [ι_mapBifunctorDesc_assoc,Preadditive.add_comp]
  simp only [Category.assoc,inl_component φ L a b n (by omega),inr_component φ L a b n h]
  erw [← Functor.map_comp_assoc,← Functor.map_comp_assoc,← Preadditive.add_comp,← Functor.map_add]
  have hi : fstX φ a (a+1) rfl ≫ inlX φ (a+1) a rfl +
      sndX φ a ≫ inrX φ a = 𝟙 _ := mappingCone.id_X φ a (a+1) rfl
  erw [hi,CategoryTheory.Functor.map_id,Category.id_comp]

/-- Tensoring in the first variable commutes with the Čech cone. -/
def coneIso : E φ L ≅ tensorObj (Z φ) L := by
  letI : ∀ n, IsIso ((compare φ L).f n) := fun n =>
    ⟨⟨inverseAt φ L n,compare_inverse φ L n,inverse_compare φ L n⟩⟩
  letI := HomologicalComplex.Hom.isIso_of_components (compare φ L)
  exact asIso (compare φ L)

/-- The same statement for the mapping fiber with its actual negative-one shift. -/
def coconeIso : tensorObj (mappingCocone φ) L ≅ mappingCocone (T φ L) :=
  mapBifunctorShift₁Iso (Z φ) L (F (k := k)) (-1) ≪≫
    (CategoryTheory.shiftFunctor _ (-1:ℤ)).mapIso (coneIso φ L).symm

section Naturality
variable {L'} (r : L ⟶ L')

private theorem square : T φ L ≫ tensorHom (𝟙 Y) r = tensorHom (𝟙 X) r ≫ T φ L' :=
  (((F (k := k)).map₂CochainComplex.map φ).naturality r).symm

/-- The map of the two Čech cones induced by horizontal restriction. -/
def restrictCone : E φ L ⟶ E φ L' :=
  mappingCone.map (T φ L) (T φ L') (tensorHom (𝟙 X) r) (tensorHom (𝟙 Y) r) (square φ L r)

private theorem leftRestrict (n : ℤ) :
    inlX (T φ L) (n+1) n rfl ≫ (restrictCone φ L r).f n =
      (tensorHom (𝟙 X) r).f (n+1) ≫ inlX (T φ L') (n+1) n rfl := by
  change (mappingCone.inl (T φ L)).v (n+1) n (by omega) ≫ _ = _
  unfold restrictCone mappingCone.map
  erw [mappingCone.inl_v_desc_f,HomComplex.Cochain.zero_cochain_comp_v,HomComplex.Cochain.ofHom_v]
  rfl

private theorem rightRestrict (n : ℤ) :
    inrX (T φ L) n ≫ (restrictCone φ L r).f n =
      (tensorHom (𝟙 Y) r).f n ≫ inrX (T φ L') n := by
  change (mappingCone.inr (T φ L)).f n ≫ _ = _
  unfold restrictCone mappingCone.map
  erw [mappingCone.inr_f_desc_f]
  rfl

private theorem tensor_restrict (P : C (k := k)) (a b n : ℤ) (h : a+b=n) :
    ιTensorObj P L a b n h ≫ (tensorHom (𝟙 P) r).f n =
      (F.obj (P.X a)).map (r.f b) ≫ ιTensorObj P L' a b n h := by
  erw [ι_mapBifunctorMap]
  simp only [HomologicalComplex.id_f,CategoryTheory.Functor.map_id,NatTrans.id_app,Category.id_comp]

private theorem action {A B : M (k := k)} (f : A ⟶ B) (b : ℤ) :
    (G L b).map f ≫ (F.obj B).map (r.f b) =
      (F.obj A).map (r.f b) ≫ (G L' b).map f :=
  ((F.map f).naturality (r.f b)).symm

/-- The cone interchange commutes with every horizontal chain map. -/
theorem compare_restriction :
    compare φ L ≫ tensorHom (𝟙 (Z φ)) r = restrictCone φ L r ≫ compare φ L' := by
  apply HomologicalComplex.Hom.ext
  funext n
  change (compare φ L).f n ≫ (tensorHom (𝟙 (Z φ)) r).f n =
    (restrictCone φ L r).f n ≫ (compare φ L').f n
  apply homotopyCofiber.ext_from_X (T φ L) (n+1) n rfl
  · apply mapBifunctor.hom_ext
    intro a b h
    change a+b=n+1 at h
    obtain ⟨a,rfl⟩ : ∃ p, a=p+1 := ⟨a-1,by omega⟩
    erw [inl_component_assoc φ L a b n h,← Category.assoc (inlX _ _ _ _),leftRestrict φ L r n,
      Category.assoc (tensorHom (𝟙 X) r |>.f (n+1)),← Category.assoc, tensor_restrict L r X (a+1) b (n+1) h]
    erw [Category.assoc ((G L b).map (inlX φ (a+1) a rfl)),tensor_restrict L r (Z φ) a b n (by omega),
      Category.assoc ((F.obj (X.X (a+1))).map (r.f b)),inl_component φ L' a b n h,
      ← Category.assoc ((G L b).map (inlX φ (a+1) a rfl)),action L r (inlX φ (a+1) a rfl) b,Category.assoc]
  · apply mapBifunctor.hom_ext
    intro a b h
    change a+b=n at h
    erw [inr_component_assoc φ L a b n h,← Category.assoc (inrX _ _),rightRestrict φ L r n,
      Category.assoc (tensorHom (𝟙 Y) r |>.f n),← Category.assoc,tensor_restrict L r Y a b n h]
    erw [Category.assoc ((G L b).map (inrX φ a)),tensor_restrict L r (Z φ) a b n h,
      Category.assoc ((F.obj (Y.X a)).map (r.f b)),inr_component φ L' a b n h,
      ← Category.assoc ((G L b).map (inrX φ a)),action L r (inrX φ a) b,Category.assoc]

private theorem tensorShift (P : C (k := k)) (d : ℤ) :
    tensorHom (𝟙 (P⟦d⟧)) r ≫ (mapBifunctorShift₁Iso P L' F d).hom =
      (mapBifunctorShift₁Iso P L F d).hom ≫ (tensorHom (𝟙 P) r)⟦d⟧' := by
  have h := NatTrans.shift_app_comm ((F (k := k)).map₂CochainComplex.flip.map r) d P
  rw [CategoryTheory.Functor.commShiftIso_map₂CochainComplex_flip_hom_app,
    CategoryTheory.Functor.commShiftIso_map₂CochainComplex_flip_hom_app] at h
  exact h.symm

/-- Horizontal restriction on the shifted cone agrees with horizontal
restriction on the tensor of the mapping fiber. -/
theorem cocone_restriction :
    tensorHom (𝟙 (mappingCocone φ)) r ≫ (coconeIso φ L').hom =
      (coconeIso φ L).hom ≫ (restrictCone φ L r)⟦(-1:ℤ)⟧' := by
  let e := coneIso φ L
  let e' := coneIso φ L'
  let S := CategoryTheory.shiftFunctor (C (k := k)) (-1:ℤ)
  have h : e.hom ≫ tensorHom (𝟙 (Z φ)) r = restrictCone φ L r ≫ e'.hom :=
    compare_restriction φ L r
  have he : tensorHom (𝟙 (Z φ)) r ≫ e'.inv = e.inv ≫ restrictCone φ L r := by
    rw [← cancel_epi e.hom,← Category.assoc,h,Category.assoc,e'.hom_inv_id,Category.comp_id,
      e.hom_inv_id_assoc]
  have hs : tensorHom (𝟙 ((Z φ)⟦(-1:ℤ)⟧)) r ≫
      (mapBifunctorShift₁Iso (Z φ) L' F (-1)).hom =
    (mapBifunctorShift₁Iso (Z φ) L F (-1)).hom ≫ S.map (tensorHom (𝟙 (Z φ)) r) :=
    tensorShift L r (Z φ) (-1)
  change tensorHom (𝟙 ((Z φ)⟦(-1:ℤ)⟧)) r ≫ (mapBifunctorShift₁Iso (Z φ) L' F (-1)).hom ≫ S.map e'.inv =
    ((mapBifunctorShift₁Iso (Z φ) L F (-1)).hom ≫ S.map e.inv) ≫ S.map (restrictCone φ L r)
  erw [← Category.assoc,hs,Category.assoc,Category.assoc,← S.map_comp,he,S.map_comp]
  exact (Category.assoc _ _ _).symm

end Naturality

end CycleQ2TensorMappingCone


namespace CycleQ2CurveCechFiber
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex HomComplex
open CycleQ2TwoChartTraceComplex

variable {k : Type} [Field k]
variable {A₀ A₁ B₀ B₁ M₀ M₁ : Type}
  [AddCommGroup A₀] [Module k A₀] [AddCommGroup A₁] [Module k A₁]
  [AddCommGroup B₀] [Module k B₀] [AddCommGroup B₁] [Module k B₁]
  [AddCommGroup M₀] [Module k M₀] [AddCommGroup M₁] [Module k M₁]
  (dA : A₀ →ₗ[k] A₁) (dB : B₀ →ₗ[k] B₁) (dM : M₀ →ₗ[k] M₁)
  (u : A₀ →ₗ[k] M₀) (v : B₀ →ₗ[k] M₀)
  (du : A₁ →ₗ[k] M₁) (dv : B₁ →ₗ[k] M₁)
  (hu : ∀ a, du (dA a) = dM (u a)) (hv : ∀ b, dv (dB b) = dM (v b))

private abbrev term (P Q : ModuleCat.{0} k) : ℕ → ModuleCat.{0} k
  | 0 => P
  | 1 => Q
  | _ + 2 => ModuleCat.of k (Fin 0 → k)

private def diff {P Q : ModuleCat.{0} k} (d : P ⟶ Q) : ∀ n, term P Q n ⟶ term P Q (n+1)
  | 0 => d
  | _ + 1 => 0

def row {P Q : ModuleCat.{0} k} (d : P ⟶ Q) : CochainComplex (ModuleCat k) ℕ :=
  CochainComplex.of (term P Q) (diff d) (fun n => by cases n <;> exact comp_zero)

private abbrev charts := row (ModuleCat.ofHom (dA.prodMap dB))
private abbrev overlap := row (ModuleCat.ofHom dM)

local notation "T" => complex dA dB dM u v du dv hu hv
local notation "F" => charts dA dB
local notation "G" => overlap dM
local notation "E" => ComplexShape.embeddingUpNat

private def components (u : A₀ →ₗ[k] M₀) (v : B₀ →ₗ[k] M₀) : (A₀ × B₀) →ₗ[k] M₀ :=
  u.comp (LinearMap.fst k A₀ B₀) - v.comp (LinearMap.snd k A₀ B₀)

def rowMap (e : A₀ →ₗ[k] B₀) (f : A₁ →ₗ[k] B₁) (h : ∀ x, f (dA x) = dB (e x)) : row (ModuleCat.ofHom dA) ⟶ row (ModuleCat.ofHom dB) where
  f n := match n with
    | 0 => ModuleCat.ofHom e
    | 1 => ModuleCat.ofHom f
    | _ + 2 => 0
  comm' i j hij := by
    obtain rfl : j = i+1 := hij.symm
    cases i with
    | zero => exact ModuleCat.hom_ext (LinearMap.ext fun x => (h x).symm)
    | succ n => exact ModuleCat.hom_ext (LinearMap.ext fun _ => @Subsingleton.elim (Fin 0 → k) _ _ _)

def restriction : F ⟶ G :=
  rowMap (dA.prodMap dB) dM (components u v) (components du dv) (fun x => by
    change du (dA x.1) - dv (dB x.2) = dM (u x.1 - v x.2)
    rw [map_sub,hu,hv])

private def pf : ∀ n, (T).X n ⟶ (F).X n
  | 0 => 𝟙 _
  | 1 => ModuleCat.ofHom (LinearMap.snd k M₀ (A₁ × B₁))
  | _+2 => 0

def projection : T ⟶ F where
  f := pf dA dB dM u v du dv hu hv
  comm' i j hij := by
    obtain rfl : j = i+1 := hij.symm
    cases i with
    | zero => rfl
    | succ n =>
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      exact @Subsingleton.elim (Fin 0 → k) _ _ _

private def sf : ∀ i j, (T).X i ⟶ (G).X j
  | 1,0 => ModuleCat.ofHom (LinearMap.fst k M₀ _)
  | 2,1 => 𝟙 _
  | _,_ => 0

local notation "p" => projection dA dB dM u v du dv hu hv
local notation "ρ" => restriction dA dB dM u v du dv hu hv

def overlapHomotopy : Homotopy (p ≫ ρ) 0 where
  hom := sf dA dB dM u v du dv hu hv
  zero i j h := by
    cases i with
    | zero => rfl
    | succ i =>
      cases i with
      | zero => cases j <;> first | exact (h rfl).elim | rfl
      | succ i =>
        cases i with
        | zero => cases j with
          | zero => rfl
          | succ j => cases j <;> first | exact (h rfl).elim | rfl
        | succ i => cases j <;> rfl
  comm i := by
    rw [dNext_eq _ (show (ComplexShape.up ℕ).Rel i (i+1) from rfl)]
    cases i with
    | zero =>
      rw [prevD_eq_zero _ _ (by
        rintro h
        exact Nat.noConfusion h)]
      rw [HomologicalComplex.zero_f,add_zero,add_zero]
      rfl
    | succ i =>
      rw [prevD_eq _ (show (ComplexShape.up ℕ).Rel i (i+1) from rfl)]
      cases i with
      | zero =>
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        change du x.2.1 - dv x.2.2 = (du x.2.1 - dv x.2.2 - dM x.1) + dM x.1 + 0
        abel
      | succ i =>
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        exact @Subsingleton.elim (Fin 0 → k) _ _ _

local notation "H" => overlapHomotopy dA dB dM u v du dv hu hv

private def vertical : Cochain ((T).extend E) ((G).extend E) (-1) :=
  -(Cochain.ofHomotopy ((H).extend E))

def toFiber : (T).extend E ⟶ mappingCocone (extendMap ρ E) :=
  mappingCocone.lift (extendMap ρ E) (extendMap p E)
    (vertical dA dB dM u v du dv hu hv) (by
      simp only [vertical,δ_neg,δ_ofHomotopy,extendMap_zero,Cochain.ofHom_zero,
        sub_zero,extendMap_comp,neg_add_cancel])

section FiberParts
variable {K L : CochainComplex (ModuleCat.{0} k) ℤ} (φ : K ⟶ L)

private def parts (i j : ℤ) (h : i + -1 = j) :
    (mappingCocone φ).X i ≃ₗ[k] (K.X i × L.X j) where
  toLinearMap := ((mappingCocone.fst φ).f i).hom.prod ((mappingCocone.snd φ).v i j h).hom
  invFun x := (mappingCocone.inl φ).v i i (add_zero i) x.1 +
    (mappingCocone.inr φ).1.v j i (by omega) x.2
  left_inv x := by
    exact congrArg (fun f : (mappingCocone φ).X i ⟶ _ => f x) (mappingCocone.id_X φ i j h)
  right_inv x := by
    rcases x with ⟨a,b⟩
    apply Prod.ext
    · change (mappingCocone.fst φ).f i (_+_) = a
      rw [map_add]
      have h₁ := congrArg (fun f : K.X i ⟶ _ => f a) (mappingCocone.inl_v_fst_f φ i)
      have h₂ := congrArg (fun f : L.X j ⟶ _ => f b) (mappingCocone.inr_v_fst_f φ j i (by omega))
      change _ + _ = _
      rw [show (mappingCocone.fst φ).f i ((mappingCocone.inl φ).v i i _ a) = a from h₁,
        show (mappingCocone.fst φ).f i ((mappingCocone.inr φ).1.v j i _ b) = 0 from h₂,add_zero]
    · change (mappingCocone.snd φ).v i j h (_+_) = b
      rw [map_add]
      have h₁ := congrArg (fun f : K.X i ⟶ _ => f a) (mappingCocone.inl_v_snd_v φ i j h)
      have h₂ := congrArg (fun f : L.X j ⟶ _ => f b) (mappingCocone.inr_v_snd_v φ j i (by omega))
      rw [show (mappingCocone.snd φ).v i j _ ((mappingCocone.inl φ).v i i _ a) = 0 from h₁,
        show (mappingCocone.snd φ).v i j _ ((mappingCocone.inr φ).1.v j i _ b) = b from h₂,zero_add]
end FiberParts

local notation "κ" => toFiber dA dB dM u v du dv hu hv

private theorem small_positive (n : ℕ) :
    Function.Bijective (fun x : (T).X (n+1) => ((p).f (n+1) x, -(H).hom (n+1) n x)) := by
  cases n with
  | zero =>
    change Function.Bijective (fun x : M₀ × A₁ × B₁ => (x.2,-x.1))
    exact (show (M₀ × A₁ × B₁) ≃ ((A₁ × B₁) × M₀) from
      { toFun := fun x => (x.2,-x.1)
        invFun := fun x => (-x.2,x.1)
        left_inv := fun x => by simp
        right_inv := fun x => by simp }).bijective
  | succ n =>
    cases n with
    | zero =>
      change Function.Bijective (fun x : M₁ => ((0 : Fin 0 → k), -x))
      refine ⟨fun x y h => neg_injective (congrArg Prod.snd h),?_⟩
      rintro ⟨f,x⟩
      exact ⟨-x,Prod.ext (Subsingleton.elim _ _) (neg_neg _)⟩
    | succ n =>
      refine ⟨fun _ _ _ => @Subsingleton.elim (Fin 0 → k) _ _ _,?_⟩
      intro y
      exact ⟨0,@Subsingleton.elim ((Fin 0 → k) × (Fin 0 → k)) _ _ _⟩

private theorem extended_positive (n : ℕ) :
    Function.Bijective ((κ).f ((n:ℤ)+1)) := by
  let i : ℤ := (n:ℤ)+1
  let j : ℤ := n
  have hi : (E).f (n+1) = i := by rfl
  have hj : (E).f n = j := rfl
  let s := ((T).extendXIso E hi).toLinearEquiv
  let a := ((F).extendXIso E hi).toLinearEquiv
  let b := ((G).extendXIso E hj).toLinearEquiv
  let target := (parts (extendMap ρ E) i j (by dsimp [i,j]; omega)).trans (a.prodCongr b)
  apply (Function.Bijective.of_comp_iff' target.bijective ((κ).f i)).mp
  have eq : (fun x => target ((κ).f i x)) =
      (fun x : (T).X (n+1) => ((p).f (n+1) x, -(H).hom (n+1) n x)) ∘ s := by
    funext x
    apply Prod.ext
    · change a (((κ).f i ≫ (mappingCocone.fst _).f i) x) = _
      rw [toFiber,mappingCocone.lift_f_fst_f, extendMap_f _ E hi]
      change (((F).extendXIso E hi).inv ≫ ((F).extendXIso E hi).hom) _ = _
      simp [s]
      rfl
    · change b (((κ).f i ≫ (mappingCocone.snd _).v i j (by dsimp [i,j]; omega)) x) = _
      rw [toFiber,mappingCocone.lift_f_snd_v]
      change b (-((H).extend E).hom i j x) = _
      rw [map_neg]
      change -b ((Homotopy.extend.hom E (H).hom i j) x) = _
      rw [Homotopy.extend.hom_eq E (H).hom hi hj]
      change -((((G).extendXIso E hj).inv ≫ ((G).extendXIso E hj).hom) _) = _
      simp [s]
      rfl
  rw [show (⇑target ∘ ⇑((κ).f i)) = _ from eq]
  exact (small_positive dA dB dM u v du dv hu hv n).comp s.bijective


private theorem extended_nonpos (i : ℤ) (hi : i ≤ 0) : Function.Bijective ((κ).f i) := by
  let j := i - 1
  have negative (a : ℤ) (ha : a < 0) (n : ℕ) : (E).f n ≠ a := by
    change (n:ℤ) ≠ a
    omega
  let : Subsingleton (((G).extend E).X j) :=
    ModuleCat.isZero_iff_subsingleton.mp ((G).isZero_extend_X E j (negative j (by dsimp [j]; omega)))
  let : Unique (((G).extend E).X j) := uniqueOfSubsingleton 0
  let target := (parts (extendMap ρ E) i j rfl).toEquiv.trans (Equiv.prodUnique _ _)
  apply (Function.Bijective.of_comp_iff' target.bijective ((κ).f i)).mp
  have eq : (⇑target ∘ ⇑((κ).f i)) = ⇑((extendMap p E).f i) := by
    funext x
    change (((κ).f i ≫ (mappingCocone.fst _).f i) x) = _
    rw [toFiber,mappingCocone.lift_f_fst_f]
  rw [eq]
  obtain hn | rfl := lt_or_eq_of_le hi
  · let : Subsingleton (((F).extend E).X i) :=
      ModuleCat.isZero_iff_subsingleton.mp ((F).isZero_extend_X E i (negative i hn))
    let : Subsingleton (((T).extend E).X i) :=
      ModuleCat.isZero_iff_subsingleton.mp ((T).isZero_extend_X E i (negative i hn))
    exact ⟨fun _ _ _ => Subsingleton.elim _ _,fun _ => ⟨0,Subsingleton.elim _ _⟩⟩
  · rw [extendMap_f p E (show (E).f 0 = 0 from rfl)]
    let : IsIso ((p).f 0) := inferInstanceAs (IsIso (𝟙 ((T).X 0)))
    exact ConcreteCategory.bijective_of_isIso _

def curveFiberIso : (T).extend E ≅ mappingCocone (extendMap ρ E) := by
  let (i : ℤ) : IsIso ((κ).f i) := (ConcreteCategory.isIso_iff_bijective _).mpr (by
    by_cases h : i ≤ 0
    · exact extended_nonpos dA dB dM u v du dv hu hv i h
    · obtain ⟨n,hn⟩ : ∃ n : ℕ, i = (n:ℤ) + 1 := ⟨(i-1).toNat,by omega⟩
      subst i
      exact extended_positive dA dB dM u v du dv hu hv n)
  let : IsIso κ := Hom.isIso_of_components κ
  exact asIso κ

local notation "A" => row (ModuleCat.ofHom dA)
local notation "B" => row (ModuleCat.ofHom dB)
local notation "D" => row (ModuleCat.ofHom (dA.prodMap dB))

private theorem row_ext {a b : A ⟶ B} (h₀ : a.f 0 = b.f 0) (h₁ : a.f 1 = b.f 1) : a = b := by
  apply Hom.ext
  funext n
  cases n with
  | zero => exact h₀
  | succ n =>
    cases n with
    | zero => exact h₁
    | succ n => exact ModuleCat.hom_ext (LinearMap.ext fun _ => @Subsingleton.elim (Fin 0 → k) _ _ _)

private def pairBicone : BinaryBicone A B where
  pt := D
  fst := rowMap _ _ (LinearMap.fst k A₀ B₀) (LinearMap.fst k A₁ B₁) (fun _ => rfl)
  snd := rowMap _ _ (LinearMap.snd k A₀ B₀) (LinearMap.snd k A₁ B₁) (fun _ => rfl)
  inl := rowMap _ _ (LinearMap.inl k A₀ B₀) (LinearMap.inl k A₁ B₁) (fun x => by
    change (dA x,0) = (dA x,dB 0)
    rw [map_zero])
  inr := rowMap _ _ (LinearMap.inr k A₀ B₀) (LinearMap.inr k A₁ B₁) (fun x => by
    change (0,dB x) = (dA 0,dB x)
    rw [map_zero])
  inl_fst := row_ext _ _ rfl rfl
  inl_snd := row_ext _ _ rfl rfl
  inr_fst := row_ext _ _ rfl rfl
  inr_snd := row_ext _ _ rfl rfl

private def pairBilimit : (pairBicone dA dB).IsBilimit := by
  apply isBinaryBilimitOfTotal
  apply row_ext
  all_goals
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    rintro ⟨x,y⟩
    apply Prod.ext
    · exact add_zero x
    · exact zero_add y

def pairIso : D ≅ A ⊞ B := biprod.uniqueUpToIso _ _ (pairBilimit dA dB)

/-- The two actual restrictions occur with opposite signs under the chart splitting. -/
theorem pairIso_difference :
    (pairIso dA dB).hom ≫ biprod.desc (rowMap dA dM u du hu) (-(rowMap dB dM v dv hv)) =
      restriction dA dB dM u v du dv hu hv := by
  change biprod.lift _ _ ≫ biprod.desc _ _ = _
  erw [biprod.lift_desc]
  apply row_ext
  all_goals
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact (sub_eq_add_neg _ _).symm

end CycleQ2CurveCechFiber

namespace CycleQ2NativeCurveFiber

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry TopologicalSpace
open CycleQ2LaurentProjectiveLine CycleQ2ProjectiveLineStructure
open CycleQ2RelativeAffineOverlap (restrict)
open CycleQ2SmoothRelativeFrames (sectionCoefficients)
open CycleQ2NativeCurveTraceComplex (pullLinear)
open CycleQ2ExactFrameThreeDeRham (onePullback_d)
open CycleQ2CurveCechFiber HomologicalComplex CochainComplex
open scoped KaehlerDifferential

variable {k : Type} [Field k]
private abbrev C := CochainComplex (ModuleCat.{0} k) ℤ
abbrev horizontal (L : C (k := k)) :=
  (curriedTensor (ModuleCat.{0} k)).map₂CochainComplex.flip.obj L

private instance (L : C (k := k)) : (horizontal L).Additive where
  map_add {X Y} f g := by
    apply Hom.ext
    funext n
    apply mapBifunctor.hom_ext
    intro a b h
    change ιTensorObj X L a b n h ≫ (tensorHom (f+g) (𝟙 L)).f n = _
    erw [ι_mapBifunctorMap]
    change _ = ιTensorObj X L a b n h ≫ ((tensorHom f (𝟙 L)).f n + (tensorHom g (𝟙 L)).f n)
    erw [Preadditive.comp_add,ι_mapBifunctorMap,ι_mapBifunctorMap]
    simp only [HomologicalComplex.add_f_apply,Functor.map_add,NatTrans.app_add,Preadditive.add_comp]

variable (k : Type) [Field k] [CharZero k] {X : Scheme.{0}} [IsIntegral X]
  (q : X ⟶ line k) [IsFinite q] [IsDominant q]

local notation "S" => CycleQ2FiniteCurveCover.square k q
local notation "p" => q ≫ structureMap k
local notation "E" => ComplexShape.embeddingUpNat
private abbrev derivative (V : X.Opens) :
    letI := (sectionCoefficients p V).toAlgebra
    Γ(X,V) →ₗ[k] Ω[Γ(X,V)⁄k] :=
  letI := (sectionCoefficients p V).toAlgebra
  (KaehlerDifferential.D k Γ(X,V)).toLinearMap

def chartPair : CochainComplex (ModuleCat.{0} k) ℤ :=
  letI (V : X.Opens) := (sectionCoefficients p V).toAlgebra
  (row (ModuleCat.ofHom ((derivative k q (S).X₂).prodMap (derivative k q (S).X₃)))).extend E

def intersectionRow : CochainComplex (ModuleCat.{0} k) ℤ :=
  letI (V : X.Opens) := (sectionCoefficients p V).toAlgebra
  (row (ModuleCat.ofHom (derivative k q (S).X₁))).extend E

/-- Difference of the actual restrictions on functions and one-forms to the overlap. -/
def chartDifference : chartPair k q ⟶ intersectionRow k q := by
  letI (V : X.Opens) := (sectionCoefficients p V).toAlgebra
  let u := restrict p (S).f₁₂.le
  let v := restrict p (S).f₁₃.le
  exact extendMap (CycleQ2CurveCechFiber.restriction (derivative k q (S).X₂) (derivative k q (S).X₃)
    (derivative k q (S).X₁) u.toLinearMap v.toLinearMap (pullLinear u) (pullLinear v)
    (onePullback_d u) (onePullback_d v)) E

/-- Identification of the signed two-open complex used by the proper curve trace. -/
def nativeIso : CycleQ2CurveTensorTrace.curve k q ≅ mappingCocone (chartDifference k q) := by
  letI (V : X.Opens) := (sectionCoefficients p V).toAlgebra
  let u := restrict p (S).f₁₂.le
  let v := restrict p (S).f₁₃.le
  exact curveFiberIso (derivative k q (S).X₂) (derivative k q (S).X₃)
    (derivative k q (S).X₁) u.toLinearMap v.toLinearMap (pullLinear u) (pullLinear v)
    (onePullback_d u) (onePullback_d v)

def affineRow (V : X.Opens) : C (k := k) :=
  letI := (sectionCoefficients p V).toAlgebra
  (row (ModuleCat.ofHom (derivative k q V))).extend E

def affineRestriction {U V : X.Opens} (h : U ≤ V) : affineRow k q V ⟶ affineRow k q U := by
  letI (W : X.Opens) := (sectionCoefficients p W).toAlgebra
  let u := restrict p h
  exact extendMap (rowMap (derivative k q V) (derivative k q U) u.toLinearMap (pullLinear u)
    (onePullback_d u)) E

private abbrev integrateRows (L : C (k := k)) := (E).extendFunctor (ModuleCat.{0} k) ⋙ horizontal L

/-- Splitting the pair before and after forming the horizontal tensor. -/
def tensorPair (L : C (k := k)) :
    tensorObj (chartPair k q) L ≅
      tensorObj (affineRow k q (S).X₂) L ⊞ tensorObj (affineRow k q (S).X₃) L := by
  letI (W : X.Opens) := (sectionCoefficients p W).toAlgebra
  let F := integrateRows k L
  let : F.Additive := inferInstanceAs (((E).extendFunctor (ModuleCat.{0} k) ⋙ horizontal L).Additive)
  let : PreservesBinaryBiproducts F := preservesBinaryBiproducts_of_preservesBiproducts F
  exact F.mapIso (pairIso (derivative k q (S).X₂) (derivative k q (S).X₃)) ≪≫ F.mapBiprod _ _

omit [CharZero k] in
private theorem map_difference {A B P Z : CochainComplex (ModuleCat.{0} k) ℕ}
    (F : CochainComplex (ModuleCat.{0} k) ℕ ⥤ C (k := k)) [F.Additive]
    [PreservesBinaryBiproduct A B F] (e : P ≅ A ⊞ B) (a : A ⟶ Z) (b : B ⟶ Z) (f : P ⟶ Z)
    (h : e.hom ≫ biprod.desc a (-b) = f) :
    (F.mapIso e ≪≫ F.mapBiprod A B).hom ≫ biprod.desc (F.map a) (-F.map b) = F.map f := by
  change (F.map e.hom ≫ (F.mapBiprod A B).hom) ≫ _ = _
  rw [Category.assoc,← F.map_neg,biprod.mapBiprod_hom_desc,← F.map_comp,h]

omit [CharZero k] [IsFinite q] [IsDominant q] in
/-- Both overlap maps after tensoring are given by the original scheme restrictions. -/
theorem tensorPair_difference (L : C (k := k)) :
    (tensorPair k q L).hom ≫
      biprod.desc (tensorHom (affineRestriction k q (S).f₁₂.le) (𝟙 L))
        (-tensorHom (affineRestriction k q (S).f₁₃.le) (𝟙 L)) =
      tensorHom (chartDifference k q) (𝟙 L) := by
  let (W : X.Opens) := (sectionCoefficients p W).toAlgebra
  let F := integrateRows k L
  let : F.Additive := inferInstanceAs (((E).extendFunctor (ModuleCat.{0} k) ⋙ horizontal L).Additive)
  let : PreservesBinaryBiproducts F := preservesBinaryBiproducts_of_preservesBiproducts F
  let u := restrict p (S).f₁₂.le
  let v := restrict p (S).f₁₃.le
  let dA := derivative k q (S).X₂
  let dB := derivative k q (S).X₃
  let dM := derivative k q (S).X₁
  let ru := rowMap dA dM u.toLinearMap (pullLinear u) (onePullback_d u)
  let rv := rowMap dB dM v.toLinearMap (pullLinear v) (onePullback_d v)
  let ρ := CycleQ2CurveCechFiber.restriction dA dB dM u.toLinearMap v.toLinearMap
    (pullLinear u) (pullLinear v) (onePullback_d u) (onePullback_d v)
  exact map_difference k F (pairIso dA dB) ru rv ρ
    (pairIso_difference dA dB dM u.toLinearMap v.toLinearMap (pullLinear u) (pullLinear v)
      (onePullback_d u) (onePullback_d v))


end CycleQ2NativeCurveFiber

namespace CycleQ2NativeCurveFiber
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry TopologicalSpace
open CycleQ2LaurentProjectiveLine
open HomologicalComplex CochainComplex

variable {k : Type} [Field k]

private def reindexFiber {A B Z : C (k := k)} (f : A ⟶ Z) (g : B ⟶ Z)
    (e : A ≅ B) (h : e.hom ≫ g = f) : mappingCocone f ≅ mappingCocone g := by
  have h₁ : f ≫ 𝟙 Z = e.hom ≫ g := by simp [h]
  have h₂ : g ≫ 𝟙 Z = e.inv ≫ f := by rw [← h]; simp
  apply (CategoryTheory.shiftFunctor _ (-1:ℤ)).mapIso
  exact
    { hom := mappingCone.map f g e.hom (𝟙 _) h₁
      inv := mappingCone.map g f e.inv (𝟙 _) h₂
      hom_inv_id := by rw [← mappingCone.map_comp]; simp [mappingCone.map_id]
      inv_hom_id := by rw [← mappingCone.map_comp]; simp [mappingCone.map_id] }

variable (k) [CharZero k] {X : Scheme.{0}} [IsIntegral X]
  (q : X ⟶ line k) [IsFinite q] [IsDominant q] (L : C (k := k))
local notation "S" => CycleQ2FiniteCurveCover.square k q

/-- The cylinder tensor complex is the mapping fiber of the signed restrictions
of the two genuine affine curve de Rham rows tensored with the horizontal complex. -/
def tensorRectangle :
    tensorObj (CycleQ2CurveTensorTrace.curve k q) L ≅ mappingCocone
      (biprod.desc (tensorHom (affineRestriction k q (S).f₁₂.le) (𝟙 L))
        (-tensorHom (affineRestriction k q (S).f₁₃.le) (𝟙 L))) :=
  (horizontal L).mapIso (nativeIso k q) ≪≫
    CycleQ2TensorMappingCone.coconeIso (chartDifference k q) L ≪≫
    reindexFiber _ _ (tensorPair k q L) (tensorPair_difference k q L)

/-- The ordinary (unshifted) restriction cone has Čech degree one less.
In particular its degree three is the tensor complex's degree four. -/
def rectangleCohomology (n : ℤ) :
    (tensorObj (CycleQ2CurveTensorTrace.curve k q) L).homology n ≅
    (mappingCone (biprod.desc (tensorHom (affineRestriction k q (S).f₁₂.le) (𝟙 L))
      (-tensorHom (affineRestriction k q (S).f₁₃.le) (𝟙 L)))).homology (n-1) :=
  (homologyFunctor (ModuleCat.{0} k) (.up ℤ) n).mapIso (tensorRectangle k q L) ≪≫
    ((homologyFunctor (ModuleCat.{0} k) (.up ℤ) 0).shiftIso (-1:ℤ) n (n-1) (by omega)).app _

end CycleQ2NativeCurveFiber
#print axioms CycleQ2NativeCurveFiber.tensorRectangle
#print axioms CycleQ2NativeCurveFiber.rectangleCohomology
