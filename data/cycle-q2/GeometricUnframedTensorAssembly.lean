import Proposal.GeometricMonicGenericSupport

/-! The signed tensor complex of a curve and an exactly framed smooth target assembles
on arbitrary open curve rectangles. On a framed curve patch it is the ordinary tensor
product chart, even after a change of frame. Sheaf gluing makes the assembly a natural
map of the actual de Rham section complexes. Matching-family descent of the two
ordinary tensor summands is sufficient for this map to be invertible.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md. -/

noncomputable section


namespace CycleQ2UnframedTensorNaturality
open Module TensorProduct KaehlerDifferential
open scoped TensorProduct KaehlerDifferential
open CycleQ2ExactFrameThreeDeRham (onePullback exteriorPullback)
open CycleQ2AffineDeRhamFunctorial (onePullback_comp exteriorPullback_comp)
open CycleQ2ArbitraryFrameDifferential (front front_wedge)
open CycleQ2GeometricExteriorSheaf (exteriorMap_wedge)
open CycleQ2WeightedCoordinateExterior (Form)
open CycleQ2ProductDifferentialSigns (horizontal mixed)
open CycleQ2AffineKunnethDifferential (compare term)
open CycleQ2AffineKunnethComponents (positive_horizontal positive_mixed)
open CycleQ2NativeCurveTraceComplex (pullLinear)
variable {k A B A' B' : Type} [Field k] [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
  [Algebra k A] [Algebra k B] [Algebra k A'] [Algebra k B']

/-- Inserting a one-form in the first slot respects every scalar-changing algebra map. -/
theorem pull_front (f : A →ₐ[k] B) (n : ℕ) (α : Ω[A⁄k]) (ω : Form k A n) :
    exteriorPullback f (n+1) (front n α ω) = front n (onePullback f α) (exteriorPullback f n ω) := by
  have h : ω ∈ Submodule.span A (Set.range (exteriorPower.ιMulti A n)) := by
    rw [exteriorPower.ιMulti_span]; trivial
  induction h using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w,rfl⟩ := hx
    rw [front_wedge,exteriorPullback,exteriorMap_wedge,exteriorPullback,exteriorMap_wedge,front_wedge]
    apply congrArg (exteriorPower.ιMulti B (n+1))
    funext i
    cases i using Fin.cases <;> rfl
  | zero => simp only [map_zero]
  | add x y hx hy ex ey => simp only [map_add,ex,ey]
  | smul a x hx ex => rw [map_smul,map_smulₛₗ,ex,map_smulₛₗ,map_smul]

def formLinear (f : A →ₐ[k] B) (n : ℕ) : Form k A n →ₗ[k] Form k B n where
  toFun := exteriorPullback f n
  map_add' := map_add _
  map_smul' c ω := by
    rw [← IsScalarTower.algebraMap_smul A c ω,map_smulₛₗ]
    change f (algebraMap k A c) • exteriorPullback f n ω = _
    rw [f.commutes,IsScalarTower.algebraMap_smul]; rfl

variable (f : A →ₐ[k] A') (g : B →ₐ[k] B')
local notation "F" => Algebra.TensorProduct.map f g

theorem horizontal_map (n : ℕ) (a : A) (ω : Form k B n) :
    exteriorPullback F n (horizontal n a ω) = horizontal n (f a) (exteriorPullback g n ω) := by
  unfold horizontal
  rw [map_smulₛₗ,← exteriorPullback_comp,Algebra.TensorProduct.map_comp_includeRight,exteriorPullback_comp]
  congr 1
  exact DFunLike.congr_fun (Algebra.TensorProduct.map_comp_includeLeft f g) a

theorem mixed_map (n : ℕ) (α : Ω[A⁄k]) (ω : Form k B n) :
    exteriorPullback F (n+1) (mixed n α ω) = mixed n (onePullback f α) (exteriorPullback g n ω) := by
  unfold mixed
  rw [pull_front,← onePullback_comp,← exteriorPullback_comp,Algebra.TensorProduct.map_comp_includeRight,
      Algebra.TensorProduct.map_comp_includeLeft,onePullback_comp,exteriorPullback_comp]

abbrev horizontalMap (n : ℕ) := TensorProduct.map f.toLinearMap (formLinear g n)
abbrev mixedMap (n : ℕ) := TensorProduct.map (pullLinear f) (formLinear g n)

def restrictTerm : (n : ℕ) → term (k := k) (A := A) (B := B) n →ₗ[k] term (k := k) (A := A') (B := B') n
  | 0 => horizontalMap f g 0
  | n+1 => (horizontalMap f g (n+1)).prodMap (mixedMap f g n)

private theorem pair_ext {U V M N Z : Type} [AddCommGroup U] [Module k U]
    [AddCommGroup V] [Module k V] [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]
    [AddCommGroup Z] [Module k Z] (l r : ((U ⊗[k] V) × (M ⊗[k] N)) →ₗ[k] Z)
    (hl : ∀ u v, l (u ⊗ₜ[k] v,0) = r (u ⊗ₜ[k] v,0))
    (hr : ∀ x y, l (0,x ⊗ₜ[k] y) = r (0,x ⊗ₜ[k] y)) : l = r := by
  have left : l.comp (LinearMap.inl k _ _) = r.comp (LinearMap.inl k _ _) := TensorProduct.ext' hl
  have right : l.comp (LinearMap.inr k _ _) = r.comp (LinearMap.inr k _ _) := TensorProduct.ext' hr
  apply LinearMap.ext
  rintro ⟨x,y⟩
  have hx : l (x,0) = r (x,0) := LinearMap.congr_fun left x
  have hy : l (0,y) = r (0,y) := LinearMap.congr_fun right y
  rw [show (x,y) = (x,0)+(0,y) by simp,l.map_add,r.map_add,hx,hy]

section Compare
variable {m m' : ℕ} (b : Basis (Fin 1) A Ω[A⁄k]) (c : Basis (Fin m) B Ω[B⁄k])
  (b' : Basis (Fin 1) A' Ω[A'⁄k]) (c' : Basis (Fin m') B' Ω[B'⁄k])
  (a : A) (a' : A') (ha : b 0 = D k A a) (ha' : b' 0 = D k A' a')

include ha ha' in
/-- Framed product comparison is natural under both algebra maps even when frames vary. -/
theorem compare_map (n : ℕ) (z : term (k := k) (A := A) (B := B) n) :
    exteriorPullback F n (compare b c n z) = compare b' c' n (restrictTerm f g n z) := by
  have he : (formLinear F n).comp (compare b c n).toLinearMap =
      (compare b' c' n).toLinearMap.comp (restrictTerm f g n) := by
    cases n with
    | zero =>
      apply TensorProduct.ext'
      intro x y
      change exteriorPullback F 0 (CycleQ2ProductDegreeZero.comparison (x ⊗ₜ[k] y)) =
        CycleQ2ProductDegreeZero.comparison (horizontalMap f g 0 (x ⊗ₜ[k] y))
      rw [horizontalMap,TensorProduct.map_tmul,CycleQ2ProductDegreeZero.comparison_tmul,
        CycleQ2ProductDegreeZero.comparison_tmul,horizontal_map]; rfl
    | succ n =>
      apply pair_ext
      · intro x y
        change exteriorPullback F (n+1) (CycleQ2AffineKunnethComponents.positive b c n (x ⊗ₜ[k] y,0)) =
          CycleQ2AffineKunnethComponents.positive b' c' n (horizontalMap f g (n+1) (x ⊗ₜ[k] y),mixedMap f g n 0)
        rw [(mixedMap f g n).map_zero,horizontalMap,TensorProduct.map_tmul,positive_horizontal,positive_horizontal,horizontal_map]; rfl
      · intro x y
        change exteriorPullback F (n+1) (CycleQ2AffineKunnethComponents.positive b c n (0,x ⊗ₜ[k] y)) =
          CycleQ2AffineKunnethComponents.positive b' c' n (horizontalMap f g (n+1) 0,mixedMap f g n (x ⊗ₜ[k] y))
        rw [(horizontalMap f g (n+1)).map_zero,mixedMap,TensorProduct.map_tmul,positive_mixed b c n a ha,
          positive_mixed b' c' n a' ha',mixed_map]; rfl
  exact LinearMap.congr_fun he z
end Compare
end CycleQ2UnframedTensorNaturality

namespace CycleQ2UnframedTensorNaturality
open Module TensorProduct KaehlerDifferential
open scoped TensorProduct KaehlerDifferential
open CycleQ2WeightedCoordinateExterior (Form)
open CycleQ2AffineKunnethDifferential (term)
open CycleQ2AffineDeRhamFunctorial (onePullback_comp exteriorPullback_comp onePullback_id exteriorPullback_id)
open CycleQ2NativeCurveTraceComplex (pullLinear)
variable {k A A' A'' B B' B'' : Type} [Field k] [CommRing A] [CommRing A'] [CommRing A'']
  [CommRing B] [CommRing B'] [CommRing B''] [Algebra k A] [Algebra k A'] [Algebra k A'']
  [Algebra k B] [Algebra k B'] [Algebra k B'']

private theorem maps_comp {P Q R S T W : Type} [AddCommGroup P] [Module k P] [AddCommGroup Q] [Module k Q]
    [AddCommGroup R] [Module k R] [AddCommGroup S] [Module k S] [AddCommGroup T] [Module k T]
    [AddCommGroup W] [Module k W] (f : P →ₗ[k] Q) (f' : Q →ₗ[k] R) (fo : P →ₗ[k] R)
    (g : S →ₗ[k] T) (g' : T →ₗ[k] W) (go : S →ₗ[k] W) (h : ∀ x, fo x = f' (f x)) (h' : ∀ y, go y = g' (g y))
    (x : P ⊗[k] S) : TensorProduct.map f' g' (TensorProduct.map f g x) = TensorProduct.map fo go x := by
  have he : (TensorProduct.map f' g').comp (TensorProduct.map f g) = TensorProduct.map fo go := TensorProduct.ext' (fun p s => by
    change TensorProduct.map f' g' (TensorProduct.map f g (p ⊗ₜ[k] s)) = TensorProduct.map fo go (p ⊗ₜ[k] s)
    simp only [TensorProduct.map_tmul,h,h'])
  exact LinearMap.congr_fun he x

private theorem maps_id {P Q : Type} [AddCommGroup P] [Module k P] [AddCommGroup Q] [Module k Q]
    (f : P →ₗ[k] P) (g : Q →ₗ[k] Q) (h : ∀ x, f x = x) (h' : ∀ y, g y = y) (x : P ⊗[k] Q) :
    TensorProduct.map f g x = x := by
  have hx : TensorProduct.map f g = LinearMap.id := TensorProduct.ext' (fun p q => by
    simp only [TensorProduct.map_tmul,h,h',LinearMap.id_apply])
  exact LinearMap.congr_fun hx x

theorem term_comp (f : A →ₐ[k] A') (f' : A' →ₐ[k] A'') (g : B →ₐ[k] B') (g' : B' →ₐ[k] B'')
    (n : ℕ) (x : term (k := k) (A := A) (B := B) n) :
    restrictTerm f' g' n (restrictTerm f g n x) = restrictTerm (f'.comp f) (g'.comp g) n x := by
  have hh (j : ℕ) (z : A ⊗[k] Form k B j) : horizontalMap f' g' j (horizontalMap f g j z) =
      horizontalMap (f'.comp f) (g'.comp g) j z :=
    maps_comp f.toLinearMap f'.toLinearMap (f'.comp f).toLinearMap (formLinear g j) (formLinear g' j) (formLinear (g'.comp g) j)
      (AlgHom.comp_apply f' f) (exteriorPullback_comp g g' j) z
  have mm (j : ℕ) (z : Ω[A⁄k] ⊗[k] Form k B j) : mixedMap f' g' j (mixedMap f g j z) =
      mixedMap (f'.comp f) (g'.comp g) j z :=
    maps_comp (pullLinear f) (pullLinear f') (pullLinear (f'.comp f)) (formLinear g j) (formLinear g' j) (formLinear (g'.comp g) j)
      (onePullback_comp f f') (exteriorPullback_comp g g' j) z
  cases n with
  | zero => exact hh 0 x
  | succ n => exact Prod.ext (hh (n+1) x.1) (mm n x.2)

theorem term_id (n : ℕ) (x : term (k := k) (A := A) (B := B) n) :
    restrictTerm (AlgHom.id k A) (AlgHom.id k B) n x = x := by
  have hh (j : ℕ) (z : A ⊗[k] Form k B j) : horizontalMap (AlgHom.id k A) (AlgHom.id k B) j z = z :=
    maps_id (AlgHom.id k A).toLinearMap (formLinear (AlgHom.id k B) j) (fun _ => rfl) (exteriorPullback_id j) z
  have mm (j : ℕ) (z : Ω[A⁄k] ⊗[k] Form k B j) : mixedMap (AlgHom.id k A) (AlgHom.id k B) j z = z :=
    maps_id (pullLinear (AlgHom.id k A)) (formLinear (AlgHom.id k B) j) onePullback_id (exteriorPullback_id j) z
  cases n with
  | zero => exact hh 0 x
  | succ n => exact Prod.ext (hh (n+1) x.1) (mm n x.2)
end CycleQ2UnframedTensorNaturality

namespace CycleQ2UnframedSignedTensor
open CategoryTheory Module TensorProduct KaehlerDifferential
open scoped TensorProduct KaehlerDifferential
open CycleQ2WeightedCoordinateExterior (Form)
open CycleQ2ArbitraryFrameDifferential (d)
open CycleQ2AffineKunnethDifferential (term next)
open CycleQ2UnframedTensorNaturality (restrictTerm formLinear horizontalMap mixedMap)
open CycleQ2ExactFrameComplex (exterior_square)
open CycleQ2ExactFrameThreeDeRham (onePullback_d exteriorPullback)
open CycleQ2NativeCurveTraceComplex (pullLinear)
variable {k A B : Type} [Field k] [CharZero k] [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
  {m : ℕ} (c : Basis (Fin m) B Ω[B⁄k]) (v : Fin m → B) (hv : ∀ i, c i = D k B (v i))

private abbrev H (n : ℕ) := A ⊗[k] Form k B n
private abbrev M (n : ℕ) := Ω[A⁄k] ⊗[k] Form k B n
private abbrev hd (P : Type) [AddCommGroup P] [Module k P] (n : ℕ) :=
  TensorProduct.map (LinearMap.id (R := k) (M := P)) (d c n)
private abbrev vd (n : ℕ) : H (k := k) (A := A) (B := B) n →ₗ[k] M (k := k) (A := A) (B := B) n :=
  TensorProduct.map (D k A).toLinearMap LinearMap.id

include hv in
private theorem horizontal_square (P : Type) [AddCommGroup P] [Module k P] (n : ℕ) (x : P ⊗[k] Form k B n) :
    hd c P (n+1) (hd c P n x) = 0 := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul p ω => simp only [hd,TensorProduct.map_tmul,LinearMap.id_apply,exterior_square c v hv,tmul_zero]
  | add a b ha hb => simp only [map_add,ha,hb,add_zero]

omit [CharZero k] in
private theorem commute (n : ℕ) (x : H (k := k) (A := A) (B := B) n) :
    vd (n+1) (hd c A n x) = hd c Ω[A⁄k] n (vd n x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul p ω => simp only [vd,hd,TensorProduct.map_tmul,LinearMap.id_apply]
  | add a b ha hb => simp only [map_add,ha,hb]

include hv in
theorem signed_square (n : ℕ) (x : term (k := k) (A := A) (B := B) n) :
    next c (n+1) (next c n x) = 0 := by
  cases n with
  | zero =>
    change (hd c A 1 (hd c A 0 x), vd 1 (hd c A 0 x) - hd c Ω[A⁄k] 0 (vd 0 x)) = (0,0)
    rw [horizontal_square c v hv,commute,sub_self]
  | succ n =>
    obtain ⟨x,y⟩ := x
    change (hd c A (n+2) (hd c A (n+1) x), vd (n+2) (hd c A (n+1) x) -
      hd c Ω[A⁄k] (n+1) (vd (n+1) x - hd c Ω[A⁄k] n y)) = (0,0)
    rw [horizontal_square c v hv,commute,map_sub,horizontal_square c v hv,sub_zero,sub_self]

/-- The actual signed tensor differential only needs an exact frame on the target. -/
def complex : CochainComplex (ModuleCat.{0} k) ℕ :=
  CochainComplex.of (term (k := k) (A := A) (B := B)) (fun n => ModuleCat.ofHom (next c n)) (by
    intro n
    exact ModuleCat.hom_ext (LinearMap.ext (signed_square (A := A) c v hv n)))

variable {A' B' : Type} [CommRing A'] [CommRing B'] [Algebra k A'] [Algebra k B']
  {m' : ℕ} (c' : Basis (Fin m') B' Ω[B'⁄k]) (v' : Fin m' → B') (hv' : ∀ i, c' i = D k B' (v' i))
  (f : A →ₐ[k] A') (g : B →ₐ[k] B')

include hv hv' in
private theorem hd_natural {P Q : Type} [AddCommGroup P] [Module k P] [AddCommGroup Q] [Module k Q]
    (l : P →ₗ[k] Q) (n : ℕ) (x : P ⊗[k] Form k B n) :
    TensorProduct.map l (formLinear g (n+1)) (hd c P n x) = hd c' Q n (TensorProduct.map l (formLinear g n) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add a b ha hb => simp only [map_add,ha,hb]
  | tmul p ω =>
    simp only [hd,TensorProduct.map_tmul,LinearMap.id_apply]
    exact congrArg (fun z => l p ⊗ₜ[k] z) (CycleQ2FrameDifferentialNaturality.differential_natural c v hv c' v' hv' g n ω)

omit [CharZero k] in
private theorem vd_natural (n : ℕ) (x : H (k := k) (A := A) (B := B) n) :
    mixedMap f g n (vd n x) = vd n (horizontalMap f g n x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add a b ha hb => simp only [map_add,ha,hb]
  | tmul p ω =>
    simp only [mixedMap,horizontalMap,vd,TensorProduct.map_tmul,LinearMap.id_apply]
    exact congrArg (fun z => z ⊗ₜ[k] formLinear g n ω) (onePullback_d f p)

include hv hv' in
theorem next_natural (n : ℕ) (x : term (k := k) (A := A) (B := B) n) :
    restrictTerm f g (n+1) (next c n x) = next c' n (restrictTerm f g n x) := by
  cases n with
  | zero => exact Prod.ext (hd_natural c v hv c' v' hv' g f.toLinearMap 0 x) (vd_natural f g 0 x)
  | succ n =>
    obtain ⟨x,y⟩ := x
    apply Prod.ext (hd_natural c v hv c' v' hv' g f.toLinearMap (n+1) x)
    change mixedMap f g (n+1) (vd (n+1) x - hd c Ω[A⁄k] n y) = _
    rw [map_sub,vd_natural,hd_natural c v hv c' v' hv' g (pullLinear f)]
    rfl

/-- Simultaneous restriction in both factors with the signed differential. -/
def restriction : complex (A := A) c v hv ⟶ complex (A := A') c' v' hv' :=
  CochainComplex.ofHom (fun n => ModuleCat.ofHom (restrictTerm f g n)) (by
    intro n
    simp only [complex,CochainComplex.of_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact (next_natural c v hv c' v' hv' f g n x).symm)

end CycleQ2UnframedSignedTensor

namespace CycleQ2OrdinaryTensorRows
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite TensorProduct
open CycleQ2SmoothRelativeFrames (sectionCoefficients)
open CycleQ2RelativeAffineOverlap (restrict)
open CycleQ2IntrinsicFramedAffineSite (FramedOpen frame functions frame_apply)
open CycleQ2AffineKunnethDifferential (term next)
open CycleQ2UnframedTensorNaturality (restrictTerm term_comp term_id)
open scoped TensorProduct KaehlerDifferential
variable {k : Type} [Field k] [CharZero k] {C X : Scheme.{0}}
  (p : C ⟶ Spec (CommRingCat.of k)) (q : X ⟶ Spec (CommRingCat.of k))
private abbrev coefficients {Y : Scheme.{0}} (s : Y ⟶ Spec (CommRingCat.of k)) (O : Y.Opens) : Algebra k Γ(Y,O) :=
  (sectionCoefficients s O).toAlgebra

abbrev ordinary (U : C.Opens) (V : X.Opens) (n : ℕ) : ModuleCat.{0} k :=
  letI := coefficients p U
  letI := coefficients q V
  term (k := k) (A := Γ(C,U)) (B := Γ(X,V)) n

variable {U U' U'' : C.Opens} {V V' V'' : X.Opens}

def map (h : U' ≤ U) (g : V' ≤ V) (n : ℕ) : ordinary p q U V n ⟶ ordinary p q U' V' n :=
  letI := coefficients p U
  letI := coefficients p U'
  letI := coefficients q V
  letI := coefficients q V'
  ModuleCat.ofHom (restrictTerm (restrict p h) (restrict q g) n)

omit [CharZero k] in
theorem map_comp (h : U' ≤ U) (h' : U'' ≤ U') (g : V' ≤ V) (g' : V'' ≤ V') (n : ℕ)
    (x : ordinary p q U V n) : map p q h' g' n (map p q h g n x) = map p q (h'.trans h) (g'.trans g) n x := by
  let := coefficients p U
  let := coefficients p U'
  let := coefficients p U''
  let := coefficients q V
  let := coefficients q V'
  let := coefficients q V''
  have e := term_comp (restrict p h) (restrict p h') (restrict q g) (restrict q g') n x
  rw [← CycleQ2FramedAffineSite.restrict_comp p h h',← CycleQ2FramedAffineSite.restrict_comp q g g'] at e
  exact e

omit [CharZero k] in
theorem map_id (n : ℕ) (x : ordinary p q U V n) : map p q (le_refl U) (le_refl V) n x = x := by
  let := coefficients p U
  let := coefficients q V
  change restrictTerm (restrict p (le_refl U)) (restrict q (le_refl V)) n x = x
  rw [CycleQ2FramedAffineSite.restrict_id p U,CycleQ2FramedAffineSite.restrict_id q V]
  exact term_id n x

variable (m : ℕ) (W : FramedOpen q m)

abbrev complex (U : C.Opens) : CochainComplex (ModuleCat.{0} k) ℕ :=
  letI := coefficients p U
  letI := coefficients q W.1
  CycleQ2UnframedSignedTensor.complex (A := Γ(C,U)) (frame q m W) (functions q m W) (frame_apply q m W)

abbrev restrictComplex {W' : FramedOpen q m} (h : U' ≤ U) (g : W'.1 ≤ W.1) : complex p q m W U ⟶ complex p q m W' U' :=
  letI := coefficients p U
  letI := coefficients p U'
  letI := coefficients q W.1
  letI := coefficients q W'.1
  CycleQ2UnframedSignedTensor.restriction (frame q m W) (functions q m W) (frame_apply q m W)
    (frame q m W') (functions q m W') (frame_apply q m W') (restrict p h) (restrict q g)

end CycleQ2OrdinaryTensorRows

namespace CycleQ2RectangleBasisGluing
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open CycleQ2IntrinsicFramedAffineSite (FramedOpen)
open CycleQ2ProductAffineOpen (productOpen)
open CycleQ2ProductOpenRestrictions (productOpen_mono)
variable {k : Type} [Field k] [CharZero k] {C X : Scheme.{0}}
  (p : C ⟶ Spec (CommRingCat.of k)) (q : X ⟶ Spec (CommRingCat.of k))
  [SmoothOfRelativeDimension 1 p]

abbrev Index (U : C.Opens) := {W : FramedOpen p 1 // W.1 ≤ U}
abbrev part {U : C.Opens} (V : X.Opens) (i : Index p U) := productOpen p q i.1.1 V

omit [CharZero k] in
theorem covers (U : C.Opens) (V : X.Opens) : productOpen p q U V ≤ ⨆ i : Index p U, part p q V i := by
  intro x hx
  change pullback.fst p q x ∈ U ∧ pullback.snd p q x ∈ V at hx
  obtain ⟨W,hW,hxW,hWU⟩ := (Opens.isBasis_iff_nbhd.mp (CycleQ2FiniteExactAffineAtlas.isBasis p 1)) hx.1
  exact Opens.mem_iSup.mpr ⟨⟨⟨W,hW⟩,hWU⟩,hxW,hx.2⟩

variable (D : TopCat.Sheaf AddCommGrpCat.{0} (show Scheme from pullback p q))
abbrev res {U V : (pullback p q).Opens} (h : U ≤ V) := D.obj.map (homOfLE h).op

omit [CharZero k] [SmoothOfRelativeDimension 1 p] in
private theorem res_res {U V W : (pullback p q).Opens} (h : U ≤ V) (g : V ≤ W)
    (x : D.obj.obj (op W)) : res p q D h (res p q D g x) = res p q D (h.trans g) x := by
  change D.obj.map (homOfLE h).op (D.obj.map (homOfLE g).op x) = _
  rw [← ConcreteCategory.comp_apply,← D.obj.map_comp]
  rfl

omit [CharZero k] in
/-- A section on any rectangle is determined by restriction to the framed curve patches. -/
theorem ext {U : C.Opens} {V : X.Opens} {s t : D.obj.obj (op (productOpen p q U V))}
    (h : ∀ i : Index p U, res p q D (productOpen_mono p q i.2 (le_refl V)) s =
      res p q D (productOpen_mono p q i.2 (le_refl V)) t) : s = t :=
  D.eq_of_locally_eq' (part p q V) (productOpen p q U V)
    (fun i : Index p U => homOfLE (productOpen_mono p q i.2 (le_refl V))) (covers p q U V) s t h

omit [CharZero k] in
/-- Compatibility on smaller framed curve opens suffices for actual sheaf gluing. -/
theorem existsUnique {U : C.Opens} {V : X.Opens}
    (y : (i : Index p U) → D.obj.obj (op (part p q V i)))
    (hy : ∀ (i j : Index p U) (h : i.1.1 ≤ j.1.1), res p q D (productOpen_mono p q h (le_refl V)) (y j) = y i) :
    ∃! s : D.obj.obj (op (productOpen p q U V)), ∀ i : Index p U,
      res p q D (productOpen_mono p q i.2 (le_refl V)) s = y i := by
  apply D.existsUnique_gluing' (part p q V) (productOpen p q U V) _ (covers p q U V) y
  intro i j
  let L := part p q V i ⊓ part p q V j
  let O := i.1.1 ⊓ j.1.1
  let ks (t : Index p O) : part p q V t ≤ L := le_inf
    (productOpen_mono p q (t.2.trans inf_le_left) (le_refl V)) (productOpen_mono p q (t.2.trans inf_le_right) (le_refl V))
  have cov : L ≤ ⨆ t : Index p O, part p q V t := by
    apply le_trans _ (covers p q O V)
    intro x hx
    exact ⟨⟨hx.1.1,hx.2.1⟩,hx.1.2⟩
  apply D.eq_of_locally_eq' (fun t : Index p O => part p q V t) L (fun t => homOfLE (ks t)) cov
  intro t
  let o : Index p U := ⟨t.1,(t.2.trans inf_le_left).trans i.2⟩
  change res p q D (ks t) (res p q D (inf_le_left : L ≤ part p q V i) (y i)) =
    res p q D (ks t) (res p q D (inf_le_right : L ≤ part p q V j) (y j))
  rw [res_res,res_res]
  exact (hy o i (t.2.trans inf_le_left)).trans (hy o j (t.2.trans inf_le_right)).symm

end CycleQ2RectangleBasisGluing

namespace CycleQ2UnframedFramedChain
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
set_option maxRecDepth 4000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite TensorProduct
open CycleQ2IntrinsicFramedAffineSite (FramedOpen frame functions frame_apply forms)
open CycleQ2IntrinsicDeRhamSheaves (sheafForms onBasisIso)
open CycleQ2ProductFramedOpen (framedOpen smooth_product)
open CycleQ2ProductAffineOpen (productOpen)
open CycleQ2ProductCoefficients (productBase)
open CycleQ2ProductOpenRestrictions (productOpen_mono)
open CycleQ2SmoothRelativeFrames (sectionCoefficients)
open CycleQ2RelativeAffineOverlap (restrict)
open CycleQ2ExactFrameThreeDeRham (exteriorPullback)
open CycleQ2WeightedCoordinateExterior (Form)
open CycleQ2AffineKunnethDifferential (term compare)
open CycleQ2UnframedTensorNaturality (restrictTerm compare_map)
open CycleQ2LiteralProductTensorChart (tensorSectionIso)
open scoped TensorProduct KaehlerDifferential
variable {k : Type} [Field k] [CharZero k] {C X : Scheme.{0}}
  (p : C ⟶ Spec (CommRingCat.of k)) (q : X ⟶ Spec (CommRingCat.of k)) (m : ℕ)
  [SmoothOfRelativeDimension 1 p] [SmoothOfRelativeDimension m q]
local instance smoothFramedChain : SmoothOfRelativeDimension (1+m) (productBase p q) := smooth_product p q m

variable (U : FramedOpen p 1) (V : FramedOpen q m)
private abbrev W := framedOpen p q m U V
private abbrev Z := pullback p q
private abbrev A := Γ(C,U.1)
private abbrev B := Γ(X,V.1)
private abbrev R := Γ(Z p q,(W p q m U V).1)
local instance algA : Algebra k (A p U) := (sectionCoefficients p U.1).toAlgebra
local instance algB : Algebra k (B q m V) := (sectionCoefficients q V.1).toAlgebra
local instance algR (U : C.Opens) (V : X.Opens) : Algebra k Γ(pullback p q,productOpen p q U V) :=
  (sectionCoefficients (productBase p q) (productOpen p q U V)).toAlgebra

private abbrev F (n : ℕ) := sheafForms (productBase p q) (1+m) n
abbrev sections (U : C.Opens) (V : X.Opens) (n : ℕ) := (F p q m n).obj.obj (op (productOpen p q U V))

private def readChart (n : ℕ) : sections p q m U.1 V.1 n ≃+ Form k (A p U ⊗[k] B q m V) n := by
  letI : Algebra k Γ(pullback p q,productOpen p q U.1 V.1) := algR p q U.1 V.1
  exact (((onBasisIso (productBase p q) (1+m) n).app (op (W p q m U V))).addCommGroupIsoToAddEquiv).trans
    (CycleQ2ProductOpenForms.formsEquiv p q U.2.1 V.2.1 n).toAddEquiv

abbrev localMap (n : ℕ) := (tensorSectionIso p q m U V).hom.f n

private theorem read_local (n : ℕ) (x : term (k := k) (A := A p U) (B := B q m V) n) :
    readChart p q m U V n (localMap p q m U V n x) = compare (frame p 1 U) (frame q m V) n x := by
  let e := CycleQ2ProductCoefficients.sectionsAlgEquiv p q U.2.1 V.2.1
  let I := (onBasisIso (productBase p q) (1+m) n).app (op (W p q m U V))
  let w := compare (frame p 1 U) (frame q m V) n x
  change exteriorPullback e.toAlgHom n (I.hom (I.inv (exteriorPullback e.symm.toAlgHom n w))) = w
  refine (congrArg (exteriorPullback e.toAlgHom n) (I.inv_hom_id_apply (exteriorPullback e.symm.toAlgHom n w))).trans ?_
  rw [← CycleQ2AffineDeRhamFunctorial.exteriorPullback_comp,AlgEquiv.comp_symm,
    CycleQ2AffineDeRhamFunctorial.exteriorPullback_id]

variable {U' : FramedOpen p 1} {V' : FramedOpen q m} (hf : U'.1 ≤ U.1) (hg : V'.1 ≤ V.1)

private theorem read_restrict (n : ℕ) (x : sections p q m U.1 V.1 n) :
    readChart p q m U' V' n ((F p q m n).obj.map (homOfLE (productOpen_mono p q hf hg)).op x) =
      exteriorPullback (Algebra.TensorProduct.map (restrict p hf) (restrict q hg)) n (readChart p q m U V n x) := by
  let E := onBasisIso (productBase p q) (1+m) n
  let h : W p q m U' V' ⟶ W p q m U V := homOfLE (productOpen_mono p q hf hg)
  have en := NatTrans.naturality_apply E.hom h.op x
  let f := restrict (productBase p q) (productOpen_mono p q hf hg)
  change (E.hom.app (op (W p q m U' V'))) ((F p q m n).obj.map (homOfLE (productOpen_mono p q hf hg)).op x) =
    exteriorPullback f n (E.hom.app (op (W p q m U V)) x) at en
  let e := CycleQ2ProductOpenForms.formsEquiv p q U'.2.1 V'.2.1 n
  exact (congrArg (fun z : Form k Γ(pullback p q,productOpen p q U'.1 V'.1) n => e z) en).trans
    (CycleQ2ProductOpenForms.forms_restrict p q U.2.1 V.2.1 U'.2.1 V'.2.1 hf hg n
      (E.hom.app (op (W p q m U V)) x))

/-- The actual product section is compatible with simultaneous restriction in both affine charts. -/
theorem local_natural (n : ℕ) (x : term (k := k) (A := A p U) (B := B q m V) n) :
    (F p q m n).obj.map (homOfLE (productOpen_mono p q hf hg)).op (localMap p q m U V n x) =
      localMap p q m U' V' n (restrictTerm (restrict p hf) (restrict q hg) n x) := by
  apply (readChart p q m U' V' n).injective
  refine (read_restrict p q m U V hf hg n (localMap p q m U V n x)).trans ?_
  refine (congrArg (exteriorPullback (Algebra.TensorProduct.map (restrict p hf) (restrict q hg)) n)
    (read_local p q m U V n x)).trans ?_
  refine Eq.trans ?_ (read_local p q m U' V' n _).symm
  exact compare_map _ _ (frame p 1 U) (frame q m V) (frame p 1 U') (frame q m V')
    (functions p 1 U 0) (functions p 1 U' 0) (frame_apply p 1 U 0) (frame_apply p 1 U' 0) n x

end CycleQ2UnframedFramedChain

namespace CycleQ2UnframedProductChain
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite TensorProduct
open CycleQ2IntrinsicFramedAffineSite (FramedOpen)
open CycleQ2IntrinsicDeRhamSheaves (sheafForms differential relativeDeRham)
open CycleQ2ProductFramedOpen (smooth_product)
open CycleQ2ProductCoefficients (productBase)
open CycleQ2ProductAffineOpen (productOpen)
open CycleQ2ProductOpenRestrictions (productOpen_mono)
open CycleQ2RectangleBasisGluing (Index part res)
open CycleQ2OrdinaryTensorRows (ordinary map map_comp complex restrictComplex)
open CycleQ2UnframedFramedChain (localMap local_natural)

variable {k : Type} [Field k] [CharZero k] {C X : Scheme.{0}}
  (p : C ⟶ Spec (CommRingCat.of k)) (q : X ⟶ Spec (CommRingCat.of k)) (m : ℕ)
  [SmoothOfRelativeDimension 1 p] [SmoothOfRelativeDimension m q]
local instance smoothDescent : SmoothOfRelativeDimension (1+m) (productBase p q) := smooth_product p q m

abbrev sheaf (n : ℕ) := sheafForms (productBase p q) (1+m) n
abbrev Section (U : C.Opens) (V : X.Opens) (n : ℕ) := (sheaf p q m n).obj.obj (op (productOpen p q U V))

abbrev geoRes {U U' : C.Opens} {V V' : X.Opens} (h : U' ≤ U) (g : V' ≤ V) (n : ℕ) :
    Section p q m U V n ⟶ Section p q m U' V' n :=
  res p q (sheaf p q m n) (productOpen_mono p q h g)

private theorem geo_comp {U U' U'' : C.Opens} {V V' V'' : X.Opens} (h : U' ≤ U) (h' : U'' ≤ U')
    (g : V' ≤ V) (g' : V'' ≤ V') (n : ℕ) (x : Section p q m U V n) :
    geoRes p q m h' g' n (geoRes p q m h g n x) = geoRes p q m (h'.trans h) (g'.trans g) n x := by
  change (sheaf p q m n).obj.map _ ((sheaf p q m n).obj.map _ x) = _
  rw [← ConcreteCategory.comp_apply,← Functor.map_comp]
  rfl

variable (U : C.Opens) (V : FramedOpen q m) (n : ℕ)
private abbrev patch (i : Index p U) : ordinary p q U V.1 n →+ Section p q m i.1.1 V.1 n :=
  (localMap p q m i.1 V n).hom.comp (map p q i.2 (le_refl V.1) n).hom.toAddMonoidHom

private theorem patch_compatible (x : ordinary p q U V.1 n) (i j : Index p U) (h : i.1.1 ≤ j.1.1) :
    geoRes p q m h (le_refl V.1) n (patch p q m U V n j x) = patch p q m U V n i x :=
  (local_natural p q m j.1 V h (le_refl V.1) n (map p q j.2 (le_refl V.1) n x)).trans
    (congrArg (fun z : ordinary p q i.1.1 V.1 n => localMap p q m i.1 V n z)
      (map_comp p q j.2 h (le_refl V.1) (le_refl V.1) n x))

private theorem unique (x : ordinary p q U V.1 n) :
    ∃! s : Section p q m U V.1 n, ∀ i : Index p U,
      geoRes p q m i.2 (le_refl V.1) n s = patch p q m U V n i x :=
  CycleQ2RectangleBasisGluing.existsUnique p q (sheaf p q m n) (fun i => patch p q m U V n i x)
    (patch_compatible p q m U V n x)

private def glued (x : ordinary p q U V.1 n) := (unique p q m U V n x).choose
private theorem glued_spec (x : ordinary p q U V.1 n) (i : Index p U) :
    geoRes p q m i.2 (le_refl V.1) n (glued p q m U V n x) = patch p q m U V n i x :=
  (unique p q m U V n x).choose_spec.1 i

/-- The canonical assembly on all sections, glued from ordinary tensor products on framed patches. -/
def assemble : ordinary p q U V.1 n →+ Section p q m U V.1 n :=
  AddMonoidHom.mk' (glued p q m U V n) (by
    intro x y
    apply CycleQ2RectangleBasisGluing.ext p q (sheaf p q m n)
    intro i
    change geoRes p q m i.2 (le_refl V.1) n (glued p q m U V n (x+y)) =
      geoRes p q m i.2 (le_refl V.1) n (glued p q m U V n x + glued p q m U V n y)
    rw [map_add,glued_spec,glued_spec,glued_spec,map_add])

/-- On every framed subopen the assembly is the previously checked product tensor isomorphism. -/
theorem on_patch (x : ordinary p q U V.1 n) (W : FramedOpen p 1) (h : W.1 ≤ U) :
    geoRes p q m h (le_refl V.1) n (assemble p q m U V n x) =
      localMap p q m W V n (map p q h (le_refl V.1) n x) :=
  glued_spec p q m U V n x ⟨W,h⟩

variable {U U' : C.Opens} {V V' : FramedOpen q m}
/-- Simultaneous time and target restrictions commute on the unframed rectangle. -/
theorem assemble_natural (h : U' ≤ U) (g : V'.1 ≤ V.1) (x : ordinary p q U V.1 n) :
    geoRes p q m h g n (assemble p q m U V n x) = assemble p q m U' V' n (map p q h g n x) := by
  apply CycleQ2RectangleBasisGluing.ext p q (sheaf p q m n)
  intro i
  let W := i.1
  have hw := i.2.trans h
  change geoRes p q m i.2 (le_refl V'.1) n (geoRes p q m h g n _) = geoRes p q m i.2 (le_refl V'.1) n _
  rw [geo_comp,on_patch p q m U' V' n _ W i.2]
  have he := geo_comp p q m hw (le_refl W.1) (le_refl V.1) g n (assemble p q m U V n x)
  refine he.symm.trans ?_
  rw [on_patch p q m U V n x W hw]
  refine (local_natural p q m W V (le_refl W.1) g n _).trans ?_
  apply congrArg (fun z : ordinary p q W.1 V'.1 n => localMap p q m W V' n z)
  exact (map_comp p q hw (le_refl W.1) (le_refl V.1) g n x).trans
    (map_comp p q h i.2 g (le_refl V'.1) n x).symm

end CycleQ2UnframedProductChain

namespace CycleQ2UnframedProductChain
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
set_option maxRecDepth 4000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open CycleQ2IntrinsicFramedAffineSite (FramedOpen)
open CycleQ2IntrinsicDeRhamSheaves (relativeDeRham)
open CycleQ2ProductFramedOpen (smooth_product)
open CycleQ2ProductCoefficients (productBase)
open CycleQ2ProductAffineOpen (productOpen)
open CycleQ2ProductOpenRestrictions (productOpen_mono)
open CycleQ2RectangleBasisGluing (Index)
open CycleQ2OrdinaryTensorRows (ordinary map complex restrictComplex)
open CycleQ2UnframedFramedChain (localMap)
open CycleQ2LiteralProductTensorChart (tensorSectionIso)

variable {k : Type} [Field k] [CharZero k] {C X : Scheme.{0}}
  (p : C ⟶ Spec (CommRingCat.of k)) (q : X ⟶ Spec (CommRingCat.of k)) (m : ℕ)
  [SmoothOfRelativeDimension 1 p] [SmoothOfRelativeDimension m q]
local instance smoothActualChain : SmoothOfRelativeDimension (1+m) (productBase p q) := smooth_product p q m

private abbrev ev (U : C.Opens) (V : X.Opens) :=
  sheafToPresheaf (Opens.grothendieckTopology (show Scheme from pullback p q)) AddCommGrpCat.{0} ⋙
    (evaluation (Opens (show Scheme from pullback p q))ᵒᵖ AddCommGrpCat.{0}).obj (op (productOpen p q U V))

abbrev native (U : C.Opens) (V : X.Opens) :=
  ((ev p q U V).mapHomologicalComplex (ComplexShape.up ℕ)).obj (relativeDeRham (productBase p q) (1+m))

abbrev nativeRestriction {U U' : C.Opens} {V V' : X.Opens} (h : U' ≤ U) (g : V' ≤ V) :
    native p q m U V ⟶ native p q m U' V' :=
  ((Functor.whiskerLeft (sheafToPresheaf (Opens.grothendieckTopology (show Scheme from pullback p q)) AddCommGrpCat.{0})
    ((evaluation (Opens (show Scheme from pullback p q))ᵒᵖ AddCommGrpCat.{0}).map
      (homOfLE (productOpen_mono p q h g)).op)).mapHomologicalComplex (ComplexShape.up ℕ)).app _

private abbrev forgetComplex := (forget₂ (ModuleCat.{0} k) AddCommGrpCat.{0}).mapHomologicalComplex (ComplexShape.up ℕ)
abbrev source (U : C.Opens) (V : FramedOpen q m) := (forgetComplex (k := k)).obj (complex p q m V U)

abbrev sourceRestriction {U U' : C.Opens} {V V' : FramedOpen q m} (h : U' ≤ U) (g : V'.1 ≤ V.1) :
    source p q m U V ⟶ source p q m U' V' := (forgetComplex (k := k)).map (restrictComplex p q m V h g)

/-- The native sheaf differential equals the differential on the two tensor rows after assembly. -/
theorem assemble_d (U : C.Opens) (V : FramedOpen q m) (i j : ℕ) (x : ordinary p q U V.1 i) :
    (native p q m U V.1).d i j (assemble p q m U V i x) = assemble p q m U V j ((source p q m U V).d i j x) := by
  apply CycleQ2RectangleBasisGluing.ext p q (sheaf p q m j)
  intro t
  let W := t.1
  let r := nativeRestriction p q m t.2 (le_refl V.1)
  let s := sourceRestriction p q m (V' := V) t.2 (le_refl V.1)
  let l := (tensorSectionIso p q m W V).hom
  let y := map p q t.2 (le_refl V.1) i x
  calc
    _ = (native p q m W.1 V.1).d i j (geoRes p q m t.2 (le_refl V.1) i (assemble p q m U V i x)) :=
      (ConcreteCategory.congr_hom (r.comm i j) (assemble p q m U V i x)).symm
    _ = (native p q m W.1 V.1).d i j (localMap p q m W V i y) :=
      congrArg (fun a : Section p q m W.1 V.1 i => (native p q m W.1 V.1).d i j a) (on_patch p q m U V i x W t.2)
    _ = localMap p q m W V j ((source p q m W.1 V).d i j y) := ConcreteCategory.congr_hom (l.comm i j) y
    _ = localMap p q m W V j (map p q t.2 (le_refl V.1) j ((source p q m U V).d i j x)) :=
      congrArg (fun z : ordinary p q W.1 V.1 j => localMap p q m W V j z) (ConcreteCategory.congr_hom (s.comm i j) x)
    _ = _ := (on_patch p q m U V j _ W t.2).symm

/-- Cochain map from the exact signed two-row tensor complex to the intrinsic de Rham complex on an arbitrary curve rectangle. -/
def chainMap (U : C.Opens) (V : FramedOpen q m) : source p q m U V ⟶ native p q m U V.1 where
  f n := AddCommGrpCat.ofHom (assemble p q m U V n)
  comm' i j _ := AddCommGrpCat.hom_ext (AddMonoidHom.ext (assemble_d p q m U V i j))

/-- The chart-square identity holds as an equality of actual cochain maps. -/
theorem chainMap_natural {U U' : C.Opens} {V V' : FramedOpen q m} (h : U' ≤ U) (g : V'.1 ≤ V.1) :
    chainMap p q m U V ≫ nativeRestriction p q m h g = sourceRestriction p q m h g ≫ chainMap p q m U' V' := by
  apply HomologicalComplex.hom_ext
  intro n
  exact AddCommGrpCat.hom_ext (AddMonoidHom.ext (assemble_natural p q m n h g))

end CycleQ2UnframedProductChain

namespace CycleQ2UnframedProductChain
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open CycleQ2IntrinsicFramedAffineSite (FramedOpen)
open CycleQ2ProductOpenRestrictions (productOpen_mono)
open CycleQ2RectangleBasisGluing (Index)
open CycleQ2OrdinaryTensorRows (ordinary map map_comp)
open CycleQ2UnframedFramedChain (local_natural)
open CycleQ2LiteralProductTensorChart (tensorSectionIso)
variable {k : Type} [Field k] [CharZero k] {C X : Scheme.{0}}
  (p : C ⟶ Spec (CommRingCat.of k)) (q : X ⟶ Spec (CommRingCat.of k)) (m : ℕ)
  [SmoothOfRelativeDimension 1 p] [SmoothOfRelativeDimension m q]

/-- Gluing for the two ordinary tensor summands, formulated on the framed curve basis. -/
def RowDescent (U : C.Opens) (V : X.Opens) (n : ℕ) : Prop :=
  ∀ (w : (i : Index p U) → ordinary p q i.1.1 V n),
    (∀ (i j : Index p U) (h : i.1.1 ≤ j.1.1), map p q h (le_refl V) n (w j) = w i) →
    ∃! x : ordinary p q U V n, ∀ i : Index p U, map p q i.2 (le_refl V) n x = w i

private def localEquiv (W : FramedOpen p 1) (V : FramedOpen q m) (n : ℕ) :
    ordinary p q W.1 V.1 n ≃+ Section p q m W.1 V.1 n :=
  ((HomologicalComplex.eval _ _ n).mapIso (tensorSectionIso p q m W V)).addCommGroupIsoToAddEquiv

variable (U : C.Opens) (V : FramedOpen q m) (n : ℕ)

theorem assemble_bijective (H : RowDescent p q U V.1 n) : Function.Bijective (assemble p q m U V n) := by
  constructor
  · intro x y hxy
    let w (i : Index p U) := map p q i.2 (le_refl V.1) n x
    have hw := H w (fun i j h => map_comp p q j.2 h (le_refl V.1) (le_refl V.1) n x)
    apply hw.unique (fun _ => rfl)
    intro i
    apply (localEquiv p q m i.1 V n).injective
    exact (on_patch p q m U V n y i.1 i.2).symm.trans
      ((congrArg (fun z : Section p q m U V.1 n => geoRes p q m i.2 (le_refl V.1) n z) hxy.symm).trans
        (on_patch p q m U V n x i.1 i.2))
  · intro s
    let w (i : Index p U) := (localEquiv p q m i.1 V n).symm (geoRes p q m i.2 (le_refl V.1) n s)
    have norm (i : Index p U) : localEquiv p q m i.1 V n (w i) = geoRes p q m i.2 (le_refl V.1) n s :=
      (localEquiv p q m i.1 V n).apply_symm_apply _
    have compat (i j : Index p U) (h : i.1.1 ≤ j.1.1) : map p q h (le_refl V.1) n (w j) = w i := by
      apply (localEquiv p q m i.1 V n).injective
      refine (local_natural p q m j.1 V h (le_refl V.1) n (w j)).symm.trans ?_
      refine (congrArg (fun z : Section p q m j.1.1 V.1 n => geoRes p q m h (le_refl V.1) n z) (norm j)).trans ?_
      exact (geo_comp p q m j.2 h (le_refl V.1) (le_refl V.1) n s).trans (norm i).symm
    obtain ⟨x,hx,_⟩ := H w compat
    refine ⟨x,?_⟩
    apply CycleQ2RectangleBasisGluing.ext p q (sheaf p q m n)
    intro i
    exact (on_patch p q m U V n x i.1 i.2).trans ((congrArg (localEquiv p q m i.1 V n) (hx i)).trans (norm i))

/-- Once the ordinary tensor terms satisfy descent, the actual global assembly map is a cochain equivalence. -/
def isoOfDescent (H : ∀ n, RowDescent p q U V.1 n) : source p q m U V ≅ native p q m U V.1 := by
  let e (n : ℕ) : (source p q m U V).X n ≅ (native p q m U V.1).X n :=
    (AddEquiv.ofBijective (assemble p q m U V n) (assemble_bijective p q m U V n (H n))).toAddCommGrpIso
  refine HomologicalComplex.Hom.isoOfComponents e ?_
  intro i j _
  exact (chainMap p q m U V).comm i j

@[simp] theorem isoOfDescent_hom (H : ∀ n, RowDescent p q U V.1 n) :
    (isoOfDescent p q m U V H).hom = chainMap p q m U V := by
  apply HomologicalComplex.hom_ext
  intro i
  rfl

end CycleQ2UnframedProductChain

end

#print axioms CycleQ2UnframedProductChain.chainMap
#print axioms CycleQ2UnframedProductChain.chainMap_natural
#print axioms CycleQ2UnframedProductChain.isoOfDescent
