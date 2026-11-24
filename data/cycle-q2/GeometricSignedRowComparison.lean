import Proposal.GeometricTensorTwoRows
import Proposal.GeometricCurveTensorFiber
import Proposal.GeometricUnframedTensorAssembly

/-! Identifying the tensor of the affine curve de Rham row and the horizontal
de Rham row with their explicit exterior coefficient complex.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md. -/

noncomputable section
set_option autoImplicit false
namespace CycleQ2SignedRowComparison
open CategoryTheory CategoryTheory.Limits MonoidalCategory HomologicalComplex CochainComplex
open Module KaehlerDifferential
open scoped MonoidalCategory TensorProduct KaehlerDifferential
open CycleQ2CurveCechFiber (row)
open CycleQ2WeightedCoordinateExterior (Form)
open CycleQ2ArbitraryFrameDifferential (d)
open CycleQ2TensorTwoRows.Extension (bottom positive bottomNext positiveNext bottom_d positive_d negative)

variable {k A B : Type} [Field k] [CharZero k] [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
  {m : ℕ} (c : Basis (Fin m) B Ω[B⁄k]) (v : Fin m → B) (hv : ∀ i, c i = D k B (v i))
private abbrev M := ModuleCat.{0} k
abbrev vertical := row (ModuleCat.ofHom (D k A).toLinearMap)
def horizontal : CochainComplex (M (k := k)) ℕ :=
  CochainComplex.of (fun n => ModuleCat.of k (Form k B n)) (fun n => ModuleCat.ofHom (d c n)) (by
    intro n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact CycleQ2ExactFrameComplex.exterior_square c v hv n x)
private abbrev V := vertical (k := k) (A := A)
private abbrev H := horizontal c v hv
private abbrev S := CycleQ2UnframedSignedTensor.complex (A := A) c v hv
private abbrev E := ComplexShape.embeddingUpNat
private abbrev T := tensorObj ((V (k := k) (A := A)).extend E) ((H c v hv).extend E)
omit [CharZero k] in
private theorem vanish (n : ℕ) (hn : 2 ≤ n) : IsZero ((V (k := k) (A := A)).X n) := by
  obtain ⟨i, rfl⟩ : ∃ i, n=i+2 := ⟨n-2,by omega⟩
  exact ModuleCat.isZero_iff_subsingleton.mpr (inferInstanceAs (Subsingleton (Fin 0 → k)))

private def coefficients : (n : ℕ) → (T (A := A) c v hv).X (n:ℤ) ≅ (S (A := A) c v hv).X n
  | 0 => bottom V (H c v hv) vanish
  | n+1 => positive V (H c v hv) vanish n ≪≫ ModuleCat.biprodIsoProd _ _

section Matrix

variable {k : Type} [Field k]
private theorem prod_inl (U W : ModuleCat.{0} k) :
    biprod.inl ≫ (ModuleCat.biprodIsoProd U W).hom = ModuleCat.ofHom (LinearMap.inl k U W) := by
  let e := ModuleCat.biprodIsoProd U W
  rw [← cancel_mono e.inv, Category.assoc]
  change biprod.inl ≫ e.hom ≫ e.inv = _
  rw [e.hom_inv_id,Category.comp_id]
  apply biprod.hom_ext
  · erw [biprod.inl_fst,Category.assoc,ModuleCat.biprodIsoProd_inv_comp_fst]
    rfl
  · erw [biprod.inl_snd,Category.assoc,ModuleCat.biprodIsoProd_inv_comp_snd]
    rfl

private theorem prod_inr (U W : ModuleCat.{0} k) :
    biprod.inr ≫ (ModuleCat.biprodIsoProd U W).hom = ModuleCat.ofHom (LinearMap.inr k U W) := by
  let e := ModuleCat.biprodIsoProd U W
  rw [← cancel_mono e.inv, Category.assoc]
  change biprod.inr ≫ e.hom ≫ e.inv = _
  rw [e.hom_inv_id,Category.comp_id]
  apply biprod.hom_ext
  · erw [biprod.inr_fst,Category.assoc,ModuleCat.biprodIsoProd_inv_comp_fst]
    rfl
  · erw [biprod.inr_snd,Category.assoc,ModuleCat.biprodIsoProd_inv_comp_snd]
    rfl

end Matrix


private theorem signed_d (n : ℕ) :
    (S (A := A) c v hv).d n (n+1) = ModuleCat.ofHom (CycleQ2AffineKunnethDifferential.next (A := A) c n) :=
  by simp only [S,CycleQ2UnframedSignedTensor.complex,CochainComplex.of_d]
private theorem horizontal_d (n : ℕ) :
    (H c v hv).d n (n+1) = ModuleCat.ofHom (d c n) :=
  CochainComplex.of_d (fun i => ModuleCat.of k (CycleQ2WeightedCoordinateExterior.Form k B i)) (fun i => ModuleCat.ofHom (d c i)) n
omit [CharZero k] in
private theorem vertical_d : (V (k := k) (A := A)).d 0 1 = ModuleCat.ofHom (D k A).toLinearMap :=
  rfl
private theorem rawZero : bottomNext V (H c v hv) ≫ (ModuleCat.biprodIsoProd _ _).hom =
    (S (A := A) c v hv).d 0 1 := by
  erw [signed_d c v hv]
  unfold bottomNext
  erw [vertical_d,horizontal_d c v hv]
  erw [Preadditive.add_comp,Category.assoc,Category.assoc,prod_inl,prod_inr]
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro a ω
  change (0,D k A a ⊗ₜ[k] ω) + (a ⊗ₜ[k] d c 0 ω,0) = _
  change _ = (TensorProduct.map LinearMap.id (d c 0) (a ⊗ₜ[k] ω),
    TensorProduct.map (D k A).toLinearMap LinearMap.id (a ⊗ₜ[k] ω))
  erw [TensorProduct.map_tmul,TensorProduct.map_tmul]
  simp

private theorem rawPositive (n : ℕ) :
    positiveNext V (H c v hv) n ≫ (ModuleCat.biprodIsoProd _ _).hom =
      (ModuleCat.biprodIsoProd _ _).hom ≫ (S (A := A) c v hv).d (n+1) (n+2) := by
  erw [signed_d c v hv]
  unfold positiveNext
  erw [vertical_d,horizontal_d c v hv,horizontal_d c v hv]
  apply biprod.hom_ext'
  · erw [← Category.assoc,biprod.inl_desc,Preadditive.add_comp,Category.assoc,Category.assoc,prod_inr,prod_inl,
      ← Category.assoc,prod_inl]
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro a ω
    change A at a
    change CycleQ2WeightedCoordinateExterior.Form k B (n+1) at ω
    change (0,D k A a ⊗ₜ[k] ω) + (a ⊗ₜ[k] d c (n+1) ω,0) =
      (TensorProduct.map LinearMap.id (d c (n+1)) (a ⊗ₜ[k] ω),
        TensorProduct.map (D k A).toLinearMap LinearMap.id (a ⊗ₜ[k] ω) - TensorProduct.map LinearMap.id (d c n) 0)
    erw [TensorProduct.map_tmul,TensorProduct.map_tmul]
    simp
  · erw [← Category.assoc,biprod.inr_desc,Preadditive.neg_comp,Category.assoc,prod_inr,
      ← Category.assoc,prod_inr]
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro α ω
    change Ω[A⁄k] at α
    change CycleQ2WeightedCoordinateExterior.Form k B n at ω
    change -(0,α ⊗ₜ[k] d c n ω) =
      (TensorProduct.map LinearMap.id (d c (n+1)) (0 : A ⊗[k] CycleQ2WeightedCoordinateExterior.Form k B (n+1)),
        TensorProduct.map (D k A).toLinearMap LinearMap.id (0 : A ⊗[k] CycleQ2WeightedCoordinateExterior.Form k B (n+1)) - TensorProduct.map LinearMap.id (d c n) (α ⊗ₜ[k] ω))
    erw [TensorProduct.map_tmul]
    simp

private theorem coefficients_d (n : ℕ) :
    (coefficients (A := A) c v hv n).inv ≫ (T (A := A) c v hv).d (n:ℤ) ((n:ℤ)+1) ≫
      (coefficients (A := A) c v hv (n+1)).hom = (S (A := A) c v hv).d n (n+1) := by
  cases n with
  | zero =>
    change (bottom V (H c v hv) vanish).inv ≫ _ ≫ (positive (V (k := k) (A := A)) (H c v hv) vanish 0).hom ≫
      (ModuleCat.biprodIsoProd _ _).hom = _
    erw [← Category.assoc _ (positive (V (k := k) (A := A)) (H c v hv) vanish 0).hom,← Category.assoc,bottom_d,rawZero]
  | succ n =>
    let e := positive (V (k := k) (A := A)) (H c v hv) vanish n
    let e' := positive (V (k := k) (A := A)) (H c v hv) vanish (n+1)
    let b := ModuleCat.biprodIsoProd ((V (k := k) (A := A)).X 0 ⊗ (H c v hv).X (n+1)) ((V (k := k) (A := A)).X 1 ⊗ (H c v hv).X n)
    let b' := ModuleCat.biprodIsoProd ((V (k := k) (A := A)).X 0 ⊗ (H c v hv).X (n+2)) ((V (k := k) (A := A)).X 1 ⊗ (H c v hv).X (n+1))
    change (b.inv ≫ e.inv) ≫ _ ≫ e'.hom ≫ b'.hom = _
    erw [Category.assoc,←Category.assoc _ e'.hom,← Category.assoc e.inv,positive_d,
      rawPositive c v hv n,b.inv_hom_id_assoc]

private def allCoefficients : (a : ℤ) → (T (A := A) c v hv).X a ≅
    ((S (A := A) c v hv).extend E).X a
  | .ofNat n => coefficients c v hv n ≪≫ ((S (A := A) c v hv).extendXIso E (i := n) rfl).symm
  | .negSucc n =>
    (negative V (H c v hv) vanish _ (by omega)).iso
      ((S (A := A) c v hv).isZero_extend_X E _ (fun i hi => by change (i:ℤ)=Int.negSucc n at hi; omega))

/-- On every affine curve coordinate algebra, the integer-indexed tensor of
the two-term Kähler complex with the exact-framed horizontal de Rham complex
is isomorphic to the extension of the explicit signed term complex. -/
def signedIso : T (A := A) c v hv ≅ (S (A := A) c v hv).extend E := by
  refine HomologicalComplex.Hom.isoOfComponents (allCoefficients c v hv) ?_
  intro a b hab
  have hab' : a+1=b := hab
  subst b
  cases a with
  | negSucc n => exact (negative V (H c v hv) vanish _ (by omega)).eq_of_src _ _
  | ofNat n =>
    let e := coefficients (A := A) c v hv n
    let e' := coefficients (A := A) c v hv (n+1)
    let s := (S (A := A) c v hv).extendXIso E (i := n) rfl
    let s' := (S (A := A) c v hv).extendXIso E (i := n+1) rfl
    have h : e.inv ≫ (T (A := A) c v hv).d (n:ℤ) ((n:ℤ)+1) ≫ e'.hom = (S (A := A) c v hv).d n (n+1) :=
      coefficients_d c v hv n
    have hd : ((S (A := A) c v hv).extend E).d (n:ℤ) ((n:ℤ)+1) = s.hom ≫ (S (A := A) c v hv).d n (n+1) ≫ s'.inv :=
      (S (A := A) c v hv).extend_d_eq E (i := n) (j := n+1) rfl rfl
    change (e.hom ≫ s.inv) ≫ _ = _ ≫ e'.hom ≫ s'.inv
    erw [hd,Category.assoc,s.inv_hom_id_assoc,← h]
    simp only [Category.assoc,e.hom_inv_id_assoc]
    rfl

section Restriction
variable {A' B' : Type} [CommRing A'] [CommRing B'] [Algebra k A'] [Algebra k B']
  {m' : ℕ} (c' : Basis (Fin m') B' Ω[B'⁄k]) (v' : Fin m' → B') (hv' : ∀ i, c' i = D k B' (v' i))
  (f : A →ₐ[k] A') (g : B →ₐ[k] B')
open CycleQ2NativeCurveTraceComplex (pullLinear)
open CycleQ2UnframedTensorNaturality (formLinear restrictTerm)
open CycleQ2ExactFrameThreeDeRham (onePullback_d)
open CycleQ2TensorTwoRows.Extension (positive_map bottom_map)
open scoped MonoidalCategory

/-- Pullback of functions and of Kähler differentials on the two-term curve row. -/
abbrev vMap := CycleQ2CurveCechFiber.rowMap (D k A).toLinearMap (D k A').toLinearMap
  f.toLinearMap (pullLinear f) (onePullback_d f)

/-- Pullback of horizontal exterior forms on the exact-framed de Rham complex. -/
def hMap : H c v hv ⟶ H c' v' hv' :=
  CochainComplex.ofHom (fun n => ModuleCat.ofHom (formLinear g n)) (by
    intro n
    erw [horizontal_d c v hv,horizontal_d c' v' hv']
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact (CycleQ2FrameDifferentialNaturality.differential_natural c v hv c' v' hv' g n x).symm)

/-- Restriction along the identity algebra map fixes the framed horizontal row. -/
@[simp] theorem hMap_id :
    hMap c v hv c v hv (AlgHom.id k B) = 𝟙 (horizontal c v hv) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact CycleQ2AffineDeRhamFunctorial.exteriorPullback_id n x

private abbrev tm := HomologicalComplex.tensorHom (extendMap (vMap f) E) (extendMap (hMap c v hv c' v' hv' g) E)
private abbrev sm := CycleQ2UnframedSignedTensor.restriction c v hv c' v' hv' f g

private theorem rawMap (n : ℕ) :
    biprod.map ((vMap f).f 0 ⊗ₘ (hMap c v hv c' v' hv' g).f (n+1))
      ((vMap f).f 1 ⊗ₘ (hMap c v hv c' v' hv' g).f n) ≫ (ModuleCat.biprodIsoProd _ _).hom =
        (ModuleCat.biprodIsoProd _ _).hom ≫ (sm c v hv c' v' hv' f g).f (n+1) := by
  apply biprod.hom_ext'
  · erw [← Category.assoc,biprod.inl_map,Category.assoc,prod_inl,← Category.assoc,prod_inl]
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro a x
    change A at a
    change Form k B (n+1) at x
    change (f a ⊗ₜ[k] formLinear g (n+1) x,0) =
      (TensorProduct.map f.toLinearMap (formLinear g (n+1)) (a ⊗ₜ[k] x),
        TensorProduct.map (pullLinear f) (formLinear g n) 0)
    erw [TensorProduct.map_tmul]
    simp
  · erw [← Category.assoc,biprod.inr_map,Category.assoc,prod_inr,← Category.assoc,prod_inr]
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro w x
    change Ω[A⁄k] at w
    change Form k B n at x
    change (0,pullLinear f w ⊗ₜ[k] formLinear g n x) =
      (TensorProduct.map f.toLinearMap (formLinear g (n+1)) 0,
        TensorProduct.map (pullLinear f) (formLinear g n) (w ⊗ₜ[k] x))
    erw [TensorProduct.map_tmul]
    simp

private theorem coefficients_map (n : ℕ) :
    (coefficients (A := A) c v hv n).inv ≫ (tm c v hv c' v' hv' f g).f (n:ℤ) ≫
      (coefficients (A := A') c' v' hv' n).hom = (sm c v hv c' v' hv' f g).f n := by
  cases n with
  | zero =>
    erw [bottom_map V (H c v hv) (vMap f) (hMap c v hv c' v' hv' g) vanish vanish]
    rfl
  | succ n =>
    let e := positive (V (k := k) (A := A)) (H c v hv) vanish n
    let e' := positive (V (k := k) (A := A')) (H c' v' hv') vanish n
    let b := ModuleCat.biprodIsoProd ((V (k := k) (A := A)).X 0 ⊗ (H c v hv).X (n+1)) ((V (k := k) (A := A)).X 1 ⊗ (H c v hv).X n)
    let b' := ModuleCat.biprodIsoProd ((V (k := k) (A := A')).X 0 ⊗ (H c' v' hv').X (n+1)) ((V (k := k) (A := A')).X 1 ⊗ (H c' v' hv').X n)
    change (b.inv ≫ e.inv) ≫ _ ≫ e'.hom ≫ b'.hom = _
    erw [Category.assoc,← Category.assoc _ e'.hom,← Category.assoc e.inv,
      positive_map V (H c v hv) (vMap f) (hMap c v hv c' v' hv' g) vanish vanish n,rawMap,
      b.inv_hom_id_assoc]

/-- Pullback along any pair of algebra maps, including a change of horizontal
frame, commutes with the two-row tensor comparison. -/
theorem signedIso_restriction :
    tm c v hv c' v' hv' f g ≫ (signedIso (A := A') c' v' hv').hom =
      (signedIso (A := A) c v hv).hom ≫ extendMap (sm c v hv c' v' hv' f g) E := by
  apply HomologicalComplex.Hom.ext
  funext j
  cases j with
  | negSucc n => exact (negative V (H c v hv) vanish _ (by omega)).eq_of_src _ _
  | ofNat n =>
    let e := coefficients (A := A) c v hv n
    let e' := coefficients (A := A') c' v' hv' n
    let s := (S (A := A) c v hv).extendXIso E (i := n) rfl
    let s' := (S (A := A') c' v' hv').extendXIso E (i := n) rfl
    let r := sm c v hv c' v' hv' f g
    let m := tm c v hv c' v' hv' f g
    have h : e.inv ≫ m.f (n:ℤ) ≫ e'.hom = r.f n := coefficients_map c v hv c' v' hv' f g n
    have hm : (extendMap r E).f (n:ℤ) = s.hom ≫ r.f n ≫ s'.inv := extendMap_f r E rfl
    change m.f _ ≫ e'.hom ≫ s'.inv = (e.hom ≫ s.inv) ≫ _
    erw [hm,Category.assoc,s.inv_hom_id_assoc,← h]
    simp only [Category.assoc,e.hom_inv_id_assoc]
end Restriction

section Geometric
open AlgebraicGeometry TopologicalSpace
open CycleQ2LaurentProjectiveLine CycleQ2ProjectiveLineStructure
open CycleQ2SmoothRelativeFrames (sectionCoefficients)
variable {X : Scheme.{0}} [IsIntegral X] (q : X ⟶ line k) [IsFinite q] [IsDominant q]

/-- The actual curve factor used in the proper two-open trace has the signed
affine coefficient model on each of the two opens and on their overlap. -/
def affineSignedIso (U : X.Opens) :
    letI := (sectionCoefficients (q ≫ structureMap k) U).toAlgebra
    tensorObj (CycleQ2NativeCurveFiber.affineRow k q U) ((H c v hv).extend E) ≅
      (CycleQ2UnframedSignedTensor.complex (A := Γ(X,U)) c v hv).extend E := by
  letI := (sectionCoefficients (q ≫ structureMap k) U).toAlgebra
  exact signedIso (A := Γ(X,U)) c v hv

end Geometric

end CycleQ2SignedRowComparison

#print axioms CycleQ2SignedRowComparison.signedIso
#print axioms CycleQ2SignedRowComparison.signedIso_restriction
#print axioms CycleQ2SignedRowComparison.affineSignedIso
