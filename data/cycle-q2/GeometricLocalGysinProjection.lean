import Proposal.GeometricSmoothSurfaceGysin
import Proposal.GeometricLiteralThreefoldResidueContraction
import Proposal.GeometricAffineExteriorAcyclicity

/-! On an adapted affine chart for a smooth closed surface in a smooth fourfold, the
double logarithmic form multiplied by any regular two-form has a unique regular
numerator after clearing both poles. Its ordered normal residue is the restriction
of the two-form to the surface. The refinement preserves both prescribed chart equations and represents the
normalized supported degree-four class at the chosen point.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
noncomputable section
namespace CycleQ2LocalGysinProjection
open Module KaehlerDifferential CycleQ2WeightedCoordinateExterior
  CycleQ2ArbitraryFrameDifferential CycleQ2LiteralThreefoldResidueContraction
  CycleQ2GeometricExteriorSheaf CycleQ2ExactFrameThreeDeRham

section

variable {R S M N : Type} [CommRing R] [CommRing S] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module S N]

omit [AddCommGroup M] in
private theorem remove_succ (n : ℕ) (j : Fin (n+1)) (c : M) (v : Fin (n+1) → M) :
    j.succ.removeNth (Matrix.vecCons c v) = Matrix.vecCons c (j.removeNth v) := by
  funext k
  refine Fin.cases ?_ (fun l => ?_) k
  · simp [Fin.removeNth_apply]
  · simp [Fin.removeNth_apply, Fin.succ_succAbove_succ]

theorem interior_front (n : ℕ) (δ : M →ₗ[R] R) (c : M) (ω : ⋀[R]^(n+1) M) :
    interior (n+1) δ (front (n+1) c ω) = δ c • ω - front n c (interior n δ ω) := by
  have hω : ω ∈ Submodule.span R (Set.range (exteriorPower.ιMulti R (n+1))) := by
    rw [exteriorPower.ιMulti_span]; trivial
  induction hω using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨v, rfl⟩ := hw
    rw [front_wedge, interior_wedge, Fin.sum_univ_succ, interior_wedge, map_sum]
    simp only [Fin.val_zero, pow_zero, one_smul, Matrix.cons_val_zero,
      Fin.removeNth_zero, show Fin.tail (Matrix.vecCons c v) = v from rfl, Fin.val_succ, pow_succ, mul_neg, mul_one,
      neg_smul, Matrix.cons_val_succ, remove_succ, map_zsmul, map_smul, front_wedge,
      Finset.sum_neg_distrib, sub_eq_add_neg]
  | zero => simp
  | add x y _ _ hx hy => simp only [map_add, smul_add, hx, hy]; abel
  | smul a x _ hx => simp [hx, smul_sub, smul_comm a (δ c)]

theorem exteriorMap_front (φ : R →+* S) (f : M →ₛₗ[φ] N) (n : ℕ)
    (c : M) (ω : ⋀[R]^n M) :
    exteriorMap φ f (n+1) (front n c ω) = front n (f c) (exteriorMap φ f n ω) := by
  have hω : ω ∈ Submodule.span R (Set.range (exteriorPower.ιMulti R n)) := by
    rw [exteriorPower.ιMulti_span]; trivial
  induction hω using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨v, rfl⟩ := hw
    rw [front_wedge, exteriorMap_wedge, exteriorMap_wedge, front_wedge]
    apply congrArg (exteriorPower.ιMulti S (n+1))
    funext j; exact Fin.cases rfl (fun k => rfl) j
  | zero => simp
  | add x y _ _ hx hy => simp [hx, hy]
  | smul a x _ hx => simp [hx]

/-- Exterior multiplication in the graded exterior algebra. -/
def cup22 (α β : ⋀[R]^2 M) : ⋀[R]^4 M :=
  ⟨α.val * β.val, SetLike.mul_mem_graded α.property β.property⟩

private theorem front_coe (n : ℕ) (v : M) (ω : ⋀[R]^n M) :
    (front n v ω).val = ExteriorAlgebra.ι R v * ω.val := by
  have hω : ω ∈ Submodule.span R (Set.range (exteriorPower.ιMulti R n)) := by
    rw [exteriorPower.ιMulti_span]; trivial
  induction hω using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨a, rfl⟩ := hw
    rw [front_wedge]
    simp only [exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.ιMulti_apply,
      List.ofFn_succ, Matrix.cons_val_zero, List.prod_cons]
    rfl
  | zero => simp
  | add x y _ _ hx hy => simp only [map_add, Submodule.coe_add, hx, hy, mul_add]
  | smul a x _ hx => simp only [map_smul, Submodule.coe_smul, hx, mul_smul_comm]

theorem cup_wedge (u v : M) (ω : ⋀[R]^2 M) :
    cup22 (exteriorPower.ιMulti R 2 ![u,v]) ω = front 3 u (front 2 v ω) := by
  apply Subtype.ext
  change (exteriorPower.ιMulti R 2 ![u,v]).val * ω.val = _
  rw [front_coe, front_coe]
  simp [exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.ιMulti_apply, mul_assoc]

end

variable {k R B : Type} [Field k] [CommRing R] [CommRing B] [Algebra k R] [Algebra k B]
    (b : Basis (Fin 4) R Ω[R⁄k]) (φ : R →ₐ[k] B)

/-- Ordered normal residue of a regular four-form numerator, by contraction
with the two normal vectors and cotangent pullback to the closed surface. -/
def residue (ν : Form k R 4) : Form k B 2 :=
  exteriorPullback φ 2 (interior 2 (b.coord 1) (interior 3 (b.coord 0) ν))

theorem residue_projection (f g : R) (h₀ : b 0 = D k R f) (h₁ : b 1 = D k R g)
    (hf : φ f = 0) (hg : φ g = 0) (ω : Form k R 2) :
    residue b φ (front 3 (D k R f) (front 2 (D k R g) ω)) = exteriorPullback φ 2 ω := by
  have zero₀ : onePullback φ (b 0) = 0 := by rw [h₀, onePullback_d, hf, map_zero]
  have zero₁ : onePullback φ (b 1) = 0 := by rw [h₁, onePullback_d, hg, map_zero]
  rw [← h₀, ← h₁, residue, interior_front, map_sub, map_smul, interior_front, interior_front]
  have pull (n : ℕ) (v : Ω[R⁄k]) (α : Form k R n) :
      exteriorPullback φ (n+1) (front n v α) = front n (onePullback φ v) (exteriorPullback φ n α) :=
    exteriorMap_front φ.toRingHom (onePullback φ) n v α
  simp [Basis.coord_apply]
  erw [map_add (exteriorPullback φ 2), map_sub (exteriorPullback φ 2), pull 1, pull 1, zero₀, zero₁]
  simp

section Local
open CycleQ2DoubleLogarithmicClass CycleQ2PrincipalGysinFunctions
variable {T : Type} [CommRing T] [Algebra k T] [Algebra R T] [IsScalarTower k R T]

/-- Clearing the simple poles recovers the ordered conormal numerator of the actual
double logarithmic class multiplied by an arbitrary ambient two-form. -/
theorem clears_poles (f g : R) (F G : Tˣ) (hF : (F : T) = algebraMap R T f)
    (hG : (G : T) = algebraMap R T g) (ω : Form k R 2) :
    let l := IsScalarTower.toAlgHom k R T
    (F * G : T) • cup22 (twoLog (K := k) F G) (exteriorPullback l 2 ω) =
      exteriorPullback l 4 (front 3 (D k R f) (front 2 (D k R g) ω)) := by
  dsimp only
  rw [twoLog, wedge, cup_wedge]
  let l := IsScalarTower.toAlgHom k R T
  have pull (n : ℕ) (v : Ω[R⁄k]) (α : Form k R n) :
      exteriorPullback l (n+1) (front n v α) = front n (onePullback l v) (exteriorPullback l n α) :=
    exteriorMap_front l.toRingHom (onePullback l) n v α
  rw [pull 3, pull 2]
  rw [onePullback_d, onePullback_d]
  rw [show l f = (F : T) from hF.symm, show l g = (G : T) from hG.symm]
  simp only [logarithm, map_smul, LinearMap.smul_apply, smul_smul]
  have cancel : ((F : T) * G) * (↑G⁻¹ * ↑F⁻¹) = 1 := by
    calc
      _ = ((F : T) * ↑F⁻¹) * ((G : T) * ↑G⁻¹) := by ac_rfl
      _ = 1 := by simp
  rw [cancel, one_smul]

open CycleQ2NormalExteriorCech CycleQ2RelativeAffineOverlap

/-- The frame makes both normal parameters regular, so clearing the two poles
determines a unique numerator before taking the ordered residue. -/
theorem unique_normal_residue [CharZero k] [IsNoetherianRing R] (u : Fin 4 → R)
    (hu : ∀ i, b i = D k R (u i)) (h₀ : φ (u 0) = 0) (h₁ : φ (u 1) = 0)
    [IsLocalization.Away (u 0 * u 1) T] (F G : Tˣ)
    (hF : (F : T) = algebraMap R T (u 0)) (hG : (G : T) = algebraMap R T (u 1))
    (ω : Form k R 2) :
    let l := IsScalarTower.toAlgHom k R T
    let pole := cup22 (twoLog (K := k) F G) (exteriorPullback l 2 ω)
    ∃ ν : Form k R 4,
      (∀ v, exteriorPullback l 4 v = ((F : T) * G) • pole ↔ v = ν) ∧
      residue b φ ν = exteriorPullback φ 2 ω := by
  dsimp only
  let l := IsScalarTower.toAlgHom k R T
  have hreg₀ := (exact_frame_regular b u hu 0 1 (by decide)).1
  have hreg₁ := (exact_frame_regular b u hu 1 0 (by decide)).1
  have hd := (hreg₀.mul hreg₁)
  have hden : u 0 * u 1 ∈ nonZeroDivisors R :=
    ((Commute.isRegular_iff (fun a => Commute.all _ a)).mpr hd).mem_nonZeroDivisors
  have hinj : Function.Injective (algebraMap R T) :=
    IsLocalization.injective T ((Submonoid.powers_le).mpr hden)
  have : Algebra.FormallyEtale R T := Algebra.FormallyEtale.of_isLocalization (.powers (u 0 * u 1))
  let c : Basis (Fin 4) T Ω[T⁄k] := baseChangeFrame b
  have hc (i : Fin 4) : onePullback l (b i) = c i := by
    rw [hu, onePullback_d]
    exact (baseChangeFrame_apply b u hu i).symm
  have inj : Function.Injective (exteriorPullback l 4) := by
    intro x y he
    apply (b.exteriorPower 4).equivFun.injective
    funext j
    apply hinj
    exact ((pull_coordinates b c l hc 4 x j).symm.trans
      (congrArg (fun v => (c.exteriorPower 4).equivFun v j) he)).trans
      (pull_coordinates b c l hc 4 y j)
  refine ⟨_, ?_, residue_projection b φ _ _ (hu 0) (hu 1) h₀ h₁ ω⟩
  intro v
  rw [clears_poles (u 0) (u 1) F G hF hG ω]
  exact inj.eq_iff

end Local

end CycleQ2LocalGysinProjection

namespace CycleQ2LocalGysinProjection
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite Module KaehlerDifferential
open CycleQ2SmoothRelativeFrames (sectionCoefficients)
open CycleQ2RelativeAffineOverlap (restrict)
open CycleQ2FramedCechFormRow (intersection first)
open CycleQ2IntrinsicFramedAffineSite (FramedOpen)
open CycleQ2WeightedCoordinateExterior (Form)
open CycleQ2ExactFrameThreeDeRham (exteriorPullback)
open CycleQ2PrincipalLogSupportClass (restrictionUnit restrictionUnit_val)
open CycleQ2IntrinsicLogSupportClass (logForm)
open CycleQ2SmoothSurfaceGysin
open CycleQ2ClosedGraphSupport (support complement)
open CycleQ2IntrinsicDeRhamSheaves (relativeDeRhamInt)
open CycleQ2InjectiveCech (AbSheaf)

variable {k : Type} [Field k] {X Y : Scheme.{0}}
    (q : Y ⟶ Spec (CommRingCat.of k)) (i : X ⟶ Y)

/-- The algebra map on ordinary functions induced by the surface morphism. -/
def surfaceRestriction (U : Y.Opens) :
    letI := (sectionCoefficients q U).toAlgebra
    letI := (sectionCoefficients (i ≫ q) (i ⁻¹ᵁ U)).toAlgebra
    Γ(Y,U) →ₐ[k] Γ(X,i ⁻¹ᵁ U) :=
  letI := (sectionCoefficients q U).toAlgebra
  letI := (sectionCoefficients (i ≫ q) (i ⁻¹ᵁ U)).toAlgebra
  { (i.app U).hom with
    commutes' c := congrArg
      (fun h => h (((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ q.appTop) c))
      (i.naturality (homOfLE (show U ≤ ⊤ from le_top)).op) }

variable [CharZero k] [SmoothOfRelativeDimension 4 q]
variable (W : FramedOpen q 4) (u : Fin 4 → Γ(Y,W.1))

/-- The residue formula on the actual double intersection and the actual closed surface.
The four-form numerator is uniquely determined by the four-form on the intersection. -/
def HasNativeProjection : Prop :=
  let Z := intersection q 4 W (u 0) (u 1)
  let hZ : Z.1 ≤ W.1 := (first q 4 W (u 0) (u 1)).le.trans (Y.basicOpen_le _)
  letI := (sectionCoefficients q W.1).toAlgebra
  letI := (sectionCoefficients q Z.1).toAlgebra
  letI := (sectionCoefficients (i ≫ q) (i ⁻¹ᵁ W.1)).toAlgebra
  let φ := surfaceRestriction q i W.1
  let l := restrict q hZ
  let F := restrictionUnit (u 0) (show Z.1 ≤ Y.basicOpen (u 0) from inf_le_left)
  let G := restrictionUnit (u 1) (show Z.1 ≤ Y.basicOpen (u 1) from inf_le_right)
  ∃ b : Basis (Fin 4) Γ(Y,W.1) Ω[Γ(Y,W.1)⁄k], (∀ j, b j = D k Γ(Y,W.1) (u j)) ∧
    ∀ ω : Form k Γ(Y,W.1) 2, ∃ ν : Form k Γ(Y,W.1) 4,
      (∀ v, exteriorPullback l 4 v = ((F : Γ(Y,Z.1)) * G) •
        cup22 (logForm q 4 Z F G) (exteriorPullback l 2 ω) ↔ v = ν) ∧
        residue b φ ν = exteriorPullback φ 2 ω

/-- The section-ring normal residue on the double basic open of an adapted chart. -/
theorem native_projection (hu : CycleQ2AdaptedAffineFrame.ExactOnOpen q u)
    (heq : Ideal.span {u 0,u 1} = i.ker.ideal ⟨W.1,W.2.1⟩) :
    HasNativeProjection q i W u := by
  let A := Γ(Y,W.1)
  let Z := intersection q 4 W (u 0) (u 1)
  let T := Γ(Y,Z.1)
  let hZ : Z.1 ≤ W.1 := (first q 4 W (u 0) (u 1)).le.trans (Y.basicOpen_le _)
  let : Algebra k A := (sectionCoefficients q W.1).toAlgebra
  let : Algebra k T := (sectionCoefficients q Z.1).toAlgebra
  let : Algebra A T := (restrict q hZ).toRingHom.toAlgebra
  let : IsScalarTower k A T := IsScalarTower.of_algHom (restrict q hZ)
  let : Algebra k Γ(X,i ⁻¹ᵁ W.1) := (sectionCoefficients (i ≫ q) (i ⁻¹ᵁ W.1)).toAlgebra
  let : IsLocalization.Away (u 0 * u 1) T :=
    W.2.1.isLocalization_of_eq_basicOpen _ (homOfLE hZ) (Y.basicOpen_mul _ _).symm
  have : Smooth q := SmoothOfRelativeDimension.smooth 4 _
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian q
  have : IsNoetherianRing A := IsLocallyNoetherian.component_noetherian ⟨W.1, W.2.1⟩
  let φ := surfaceRestriction q i W.1
  have kill {s : A} (hs : s ∈ ({u 0,u 1} : Set A)) : φ s = 0 :=
    i.ideal_ker_le ⟨W.1,W.2.1⟩ (heq ▸ Ideal.subset_span hs)
  obtain ⟨b, hb⟩ := hu
  refine ⟨b,hb,fun ω => ?_⟩
  exact unique_normal_residue b φ u hb (kill (by simp)) (kill (by simp))
    (T := T) _ _ (restrictionUnit_val _ _) (restrictionUnit_val _ _) ω

section
variable (p : X ⟶ Spec (CommRingCat.of k)) [IsClosedImmersion i] (hi : i ≫ q = p)
    [SmoothOfRelativeDimension 2 p]
set_option quotPrecheck false
local notation "Ω" => (DerivedCategory.Q.obj (relativeDeRhamInt q 4) : DerivedCategory.{1} (AbSheaf (show TopCat from Y)))
local notation "E" => DerivedCategory.singleFunctor (AbSheaf (show TopCat from Y)) 0
local instance derived (Z : TopCat.{0}) : HasDerivedCategory.{1} (AbSheaf Z) :=
  HasDerivedCategory.standard _

include hi in
/-- Refine a prescribed equation chart at a point. Both equations restrict to the new
chart, which represents the normalized supported class and computes its ordered residue. -/
theorem normalized_chart_projection (A : Chart q i) (x : X) (hx : i x ∈ A.U.1)
    (z : (E).obj (support i ⊤) ⟶ Ω⟦(4:ℤ)⟧)
    (hz : ∀ n, CycleQ2NoetherianSupport.res (complement i)
      (show atlasOpen q i n ≤ ⊤ from le_top) z = atlasClass q i n) :
    ∃ (B : Chart q i) (e : B.U.1 ≤ A.U.1), i x ∈ B.U.1 ∧
      B.f = Y.presheaf.map (homOfLE e).op A.f ∧ B.g = Y.presheaf.map (homOfLE e).op A.g ∧
      CycleQ2NoetherianSupport.res (complement i) (show B.U.1 ≤ ⊤ from le_top) z = chartClass q i B ∧
      ∃ u : Fin 4 → Γ(Y,B.U.1), u 0 = B.f ∧ u 1 = B.g ∧
        HasNativeProjection q i ⟨B.U.1,B.U.2,B.frame⟩ u := by
  obtain ⟨T,e,hxT,w,hw,hf,hg⟩ := adapted_chart p q i hi A x hx
  have span : Ideal.span {w 0,w 1} = i.ker.ideal T := by
    rw [hf,hg,← i.ker.map_ideal (U := T) (V := A.U) e,← A.equations,Ideal.map_span]
    simp only [Set.image_insert_eq,Set.image_singleton]
    rfl
  let B : Chart q i := ⟨T,w 0,w 1,⟨w,hw⟩,span⟩
  have hc : CycleQ2NoetherianSupport.res (complement i) (show B.U.1 ≤ ⊤ from le_top) z =
      chartClass q i B := hz (some B)
  let W : FramedOpen q 4 := ⟨T.1, T.2, ⟨w,hw⟩⟩
  have hP : HasNativeProjection q i W w := native_projection q i W w hw span
  exact ⟨B,e,hxT,hf,hg,hc,w,rfl,rfl,hP⟩
end

end CycleQ2LocalGysinProjection
#print axioms CycleQ2LocalGysinProjection.normalized_chart_projection

/-! The top-form Gysin lift has the ordinary two-forms of the literal
two-equation quotient as its source. Its target is the original double
localization modulo the two single-localization images. In particular,
the descent below does not identify a chosen vector space with surface
forms or replace the logarithmic numerator. -/

namespace CycleQ2DoubleGysinTwoForms

open Algebra Module KaehlerDifferential
open CycleQ2WeightedCoordinateExterior (Form)
open CycleQ2NativeDoubleLocalization
open CycleQ2DoubleGysinOneForms (singleU singleV singleImages poleForms)
open CycleQ2DoubleGysinCotangent (ideal intersectionRing)
open CycleQ2IdealCotangentQuotient (conormal cotangentEquiv cotangentEquiv_mk)
open CycleQ2ExactFrameThreeDeRham
open CycleQ2AffineDeRhamFunctorial (onePullback_comp exteriorPullback_comp)
open CycleQ2ArbitraryFrameDifferential (front front_wedge)
open CycleQ2PrincipalGysinFunctions (logarithm)
open CycleQ2DoubleLogarithmicClass (onePullback_log)
open CycleQ2GeometricExteriorSheaf (exteriorMap_wedge)
open CycleQ2LocalGysinProjection (cup22 cup_wedge exteriorMap_front)

variable {k A : Type} [CommRing k] [CommRing A] [Algebra k A] (f g : A)

private abbrev baseMap (S : Type) [CommRing S] [Algebra k S] [Algebra A S]
    [IsScalarTower k A S] : A →ₐ[k] S := IsScalarTower.toAlgHom k A S

private abbrev logF : Ω[T f g⁄k] := logarithm (K := k) (localizedF (K := k) f g)
private abbrev logG : Ω[T f g⁄k] := logarithm (K := k) (localizedG (K := k) f g)
private abbrev quotientFour := (singleImages (K := k) f g 4).mkQ

private def regularTwo : Form k A 2 →ₗ[A] Form k (T f g) 2 where
  toFun := exteriorPullback (baseMap (T f g)) 2
  map_add' := (exteriorPullback (baseMap (T f g)) 2).map_add
  map_smul' a ω := by
    rw [map_smulₛₗ]
    exact IsScalarTower.algebraMap_smul (T f g) a _

/-- The original ordered two-log form wedged with an ambient two-form. -/
def liftTwo : Form k A 2 →ₗ[A] Form k (T f g) 4 :=
  ((front 3 (logF (k := k) f g)).restrictScalars A).comp
    (((front 2 (logG (k := k) f g)).restrictScalars A).comp (regularTwo f g))

def classTwo : Form k A 2 →ₗ[A] poleForms (K := k) f g 4 :=
  (quotientFour f g).comp (liftTwo f g)

theorem liftTwo_eq_cup (ω : Form k A 2) :
    liftTwo (k := k) f g ω =
      cup22 (cochain (K := k) f g) (exteriorPullback (baseMap (T f g)) 2 ω) := by
  rw [cochain,CycleQ2DoubleLogarithmicClass.twoLog,wedge,cup_wedge]
  rfl

private theorem pull_wedge {B C : Type} [CommRing B] [CommRing C]
    [Algebra k B] [Algebra k C] (φ : B →ₐ[k] C) (α β : Ω[B⁄k]) :
    exteriorPullback φ 2 (wedge α β) = wedge (onePullback φ α) (onePullback φ β) := by
  unfold wedge exteriorPullback
  rw [exteriorMap_wedge]
  apply congrArg (exteriorPower.ιMulti C 2)
  funext i
  fin_cases i <;> rfl

private theorem liftTwo_wedge (α β : Ω[A⁄k]) :
    liftTwo (k := k) f g (wedge α β) =
      exteriorPower.ιMulti (T f g) 4
        ![logF (k := k) f g,logG (k := k) f g,
          onePullback (baseMap (T f g)) α,onePullback (baseMap (T f g)) β] := by
  change front 3 _ (front 2 _ (exteriorPullback (baseMap (T f g)) 2 (wedge α β))) = _
  rw [pull_wedge,wedge,front_wedge,front_wedge]

private theorem fromU_coeff (a : A) :
    fromU (K := k) f g (algebraMap A (U f) a) = algebraMap A (T f g) a := by
  unfold fromU
  exact IsLocalization.Away.lift_eq (S := U f) (g := algebraMap A (T f g)) f
    (IsLocalization.Away.isUnit_of_dvd (f*g) (dvd_mul_right f g)) a

private theorem fromV_coeff (a : A) :
    fromV (K := k) f g (algebraMap A (V g) a) = algebraMap A (T f g) a := by
  unfold fromV
  exact IsLocalization.Away.lift_eq (S := V g) (g := algebraMap A (T f g)) g
    (IsLocalization.Away.isUnit_of_dvd (f*g) (dvd_mul_left g f)) a

private theorem pull_fromU (p : ℕ) (ω : Form k A p) :
    exteriorPullback (fromU (K := k) f g) p (exteriorPullback (baseMap (U f)) p ω) =
      exteriorPullback (baseMap (T f g)) p ω := by
  have he : (fromU (K := k) f g).comp (baseMap (U f)) = baseMap (T f g) :=
    AlgHom.ext (fromU_coeff f g)
  rw [← exteriorPullback_comp,he]

private theorem pull_fromV (p : ℕ) (ω : Form k A p) :
    exteriorPullback (fromV (K := k) f g) p (exteriorPullback (baseMap (V g)) p ω) =
      exteriorPullback (baseMap (T f g)) p ω := by
  have he : (fromV (K := k) f g).comp (baseMap (V g)) = baseMap (T f g) :=
    AlgHom.ext (fromV_coeff f g)
  rw [← exteriorPullback_comp,he]

private def unitU : (U f)ˣ := (IsLocalization.Away.algebraMap_isUnit f).unit
private def unitV : (V g)ˣ := (IsLocalization.Away.algebraMap_isUnit g).unit

private theorem pull_logF :
    onePullback (fromU (K := k) f g) (logarithm (K := k) (unitU f)) = logF (k := k) f g :=
  onePullback_log _ _

private theorem pull_logG :
    onePullback (fromV (K := k) f g) (logarithm (K := k) (unitV g)) = logG (k := k) f g :=
  onePullback_log _ _

private theorem times_logF :
    f • logF (k := k) f g = D k (T f g) (algebraMap A (T f g) f) := by
  let u := localizedF (K := k) f g
  change f • ((↑u⁻¹ : T f g) • D k (T f g) (u : T f g)) = _
  rw [← IsScalarTower.algebraMap_smul (T f g),← localizedF_val (K := k) f g,
    smul_smul,Units.mul_inv,one_smul]

private theorem times_logG :
    g • logG (k := k) f g = D k (T f g) (algebraMap A (T f g) g) := by
  let u := localizedG (K := k) f g
  change g • ((↑u⁻¹ : T f g) • D k (T f g) (u : T f g)) = _
  rw [← IsScalarTower.algebraMap_smul (T f g),← localizedG_val (K := k) f g,
    smul_smul,Units.mul_inv,one_smul]

private theorem front_smul_first (n : ℕ) (a : A) (α : Ω[T f g⁄k])
    (ω : Form k (T f g) n) : front n (a • α) ω = a • front n α ω := by
  rw [← IsScalarTower.algebraMap_smul (T f g) a α,map_smul,LinearMap.smul_apply,
    IsScalarTower.algebraMap_smul]

private theorem front_smul_second (n : ℕ) (a : A) (α : Ω[T f g⁄k])
    (ω : Form k (T f g) n) : front n α (a • ω) = a • front n α ω := by
  rw [← IsScalarTower.algebraMap_smul (T f g) a ω,map_smul,
    IsScalarTower.algebraMap_smul]

/-- Multiplication by the first equation comes from the second single open. -/
theorem classTwo_f_smul (ω : Form k A 2) : classTwo (k := k) f g (f • ω) = 0 := by
  let z : Form k (V g) 4 := front 3 (D k (V g) (algebraMap A (V g) f))
    (front 2 (logarithm (K := k) (unitV g)) (exteriorPullback (baseMap (V g)) 2 ω))
  have hz : singleV (K := k) f g 4 z = liftTwo (k := k) f g (f • ω) := by
    change exteriorPullback (fromV (K := k) f g) 4 z = _
    dsimp only [z]
    rw [exteriorMap_front,exteriorMap_front,onePullback_d,fromV_coeff,
      pull_logG,pull_fromV,← times_logF (k := k) f g]
    change front 3 (f • logF (k := k) f g)
        (front 2 (logG (k := k) f g) (regularTwo f g ω)) =
      front 3 (logF (k := k) f g) (front 2 (logG (k := k) f g) (regularTwo f g (f • ω)))
    simp only [(regularTwo f g).map_smul,front_smul_first,front_smul_second]
  change quotientFour f g (liftTwo f g (f • ω)) = 0
  rw [← hz]
  exact (Submodule.Quotient.mk_eq_zero _).mpr
    (Submodule.mem_sup_right (LinearMap.mem_range_self _ _))

/-- Multiplication by the second equation comes from the first single open. -/
theorem classTwo_g_smul (ω : Form k A 2) : classTwo (k := k) f g (g • ω) = 0 := by
  let z : Form k (U f) 4 := front 3 (logarithm (K := k) (unitU f))
    (front 2 (D k (U f) (algebraMap A (U f) g)) (exteriorPullback (baseMap (U f)) 2 ω))
  have hz : singleU (K := k) f g 4 z = liftTwo (k := k) f g (g • ω) := by
    change exteriorPullback (fromU (K := k) f g) 4 z = _
    dsimp only [z]
    rw [exteriorMap_front,exteriorMap_front,onePullback_d,fromU_coeff,
      pull_logF,pull_fromU,← times_logG (k := k) f g]
    change front 3 (logF (k := k) f g)
        (front 2 (g • logG (k := k) f g) (regularTwo f g ω)) =
      front 3 (logF (k := k) f g) (front 2 (logG (k := k) f g) (regularTwo f g (g • ω)))
    simp only [(regularTwo f g).map_smul,front_smul_first,front_smul_second]
  change quotientFour f g (liftTwo f g (g • ω)) = 0
  rw [← hz]
  exact (Submodule.Quotient.mk_eq_zero _).mpr
    (Submodule.mem_sup_left (LinearMap.mem_range_self _ _))

theorem classTwo_kills_ideal (a : A) (ha : a ∈ ideal f g) (ω : Form k A 2) :
    classTwo (k := k) f g (a • ω) = 0 := by
  obtain ⟨r,s,rfl⟩ := Ideal.mem_span_pair.mp ha
  rw [add_smul,← smul_smul,← smul_smul,map_add,
    (classTwo (k := k) f g).map_smul r (f • ω),
    (classTwo (k := k) f g).map_smul s (g • ω),
    classTwo_f_smul,classTwo_g_smul,smul_zero,smul_zero,zero_add]

private theorem classTwo_df (β : Ω[A⁄k]) :
    classTwo (k := k) f g (wedge (D k A f) β) = 0 := by
  change quotientFour f g (liftTwo f g (wedge (D k A f) β)) = 0
  rw [liftTwo_wedge,onePullback_d,← times_logF (k := k) f g]
  let α := logF (k := k) f g
  let β' := logG (k := k) f g
  let γ := onePullback (baseMap (T f g)) β
  have he : exteriorPower.ιMulti (T f g) 4 ![α,β',f • α,γ] = 0 := by
    rw [← IsScalarTower.algebraMap_smul (T f g) f α]
    change ((exteriorPower.ιMulti (T f g) 4).curryLeft α).curryLeft β'
      ![algebraMap A (T f g) f • α,γ] = 0
    rw [AlternatingMap.map_vecCons_smul]
    have hz : exteriorPower.ιMulti (T f g) 4 ![α,β',α,γ] = 0 :=
      (exteriorPower.ιMulti (T f g) 4).map_eq_zero_of_eq _
        (by rfl : ![α,β',α,γ] (0 : Fin 4) = ![α,β',α,γ] 2) (by decide)
    change algebraMap A (T f g) f • exteriorPower.ιMulti (T f g) 4 ![α,β',α,γ] = 0
    rw [hz,smul_zero]
  rw [he,map_zero]

private theorem classTwo_dg (β : Ω[A⁄k]) :
    classTwo (k := k) f g (wedge (D k A g) β) = 0 := by
  change quotientFour f g (liftTwo f g (wedge (D k A g) β)) = 0
  rw [liftTwo_wedge,onePullback_d,← times_logG (k := k) f g]
  let α := logF (k := k) f g
  let β' := logG (k := k) f g
  let γ := onePullback (baseMap (T f g)) β
  have he : exteriorPower.ιMulti (T f g) 4 ![α,β',g • β',γ] = 0 := by
    rw [← IsScalarTower.algebraMap_smul (T f g) g β']
    change ((exteriorPower.ιMulti (T f g) 4).curryLeft α).curryLeft β'
      ![algebraMap A (T f g) g • β',γ] = 0
    rw [AlternatingMap.map_vecCons_smul]
    have hz : exteriorPower.ιMulti (T f g) 4 ![α,β',β',γ] = 0 :=
      (exteriorPower.ιMulti (T f g) 4).map_eq_zero_of_eq _
        (by rfl : ![α,β',β',γ] (1 : Fin 4) = ![α,β',β',γ] 2) (by decide)
    change algebraMap A (T f g) g • exteriorPower.ιMulti (T f g) 4 ![α,β',β',γ] = 0
    rw [hz,smul_zero]
  rw [he,map_zero]

private theorem classTwo_exact_ideal (a : A) (ha : a ∈ ideal f g) (β : Ω[A⁄k]) :
    classTwo (k := k) f g (wedge (D k A a) β) = 0 := by
  obtain ⟨r,s,rfl⟩ := Ideal.mem_span_pair.mp ha
  change ((classTwo f g).comp (wedgeLeft β)) (D k A (r*f+s*g)) = 0
  rw [map_add,Derivation.leibniz,Derivation.leibniz,map_add,map_add,map_add]
  have hf : ((classTwo (k := k) f g).comp (wedgeLeft β)) (f • D k A r) = 0 := by
    change classTwo f g (wedgeLeft β (f • D k A r)) = 0
    rw [map_smul,classTwo_f_smul]
  have hg : ((classTwo (k := k) f g).comp (wedgeLeft β)) (g • D k A s) = 0 := by
    change classTwo f g (wedgeLeft β (g • D k A s)) = 0
    rw [map_smul,classTwo_g_smul]
  rw [hf,hg,map_smul,map_smul]
  change (r • classTwo f g (wedge (D k A f) β) + 0) +
    (s • classTwo f g (wedge (D k A g) β) + 0) = 0
  rw [classTwo_df,classTwo_dg,smul_zero,smul_zero,zero_add,zero_add,add_zero]

private theorem conormal_left (α β : Ω[A⁄k]) (hα : α ∈ conormal (k := k) (ideal f g)) :
    classTwo (k := k) f g (wedge α β) = 0 := by
  have hk : conormal (k := k) (ideal f g) ≤
      LinearMap.ker ((classTwo f g).comp (wedgeLeft β)) := by
    rw [conormal,sup_le_iff,Submodule.span_le]
    constructor
    · intro x hx
      refine Submodule.smul_induction_on hx ?_ ?_
      · intro a ha ω _
        apply LinearMap.mem_ker.mpr
        change classTwo f g (wedgeLeft β (a • ω)) = 0
        rw [map_smul,classTwo_kills_ideal f g a ha]
      · exact fun _ _ => Submodule.add_mem _
    · rintro _ ⟨a,ha,rfl⟩
      exact LinearMap.mem_ker.mpr (classTwo_exact_ideal f g a ha β)
  exact LinearMap.mem_ker.mp (hk hα)

private theorem conormal_right (α β : Ω[A⁄k]) (hβ : β ∈ conormal (k := k) (ideal f g)) :
    classTwo (k := k) f g (wedge α β) = 0 := by
  rw [wedge_swap β α,map_neg,conormal_left f g β α hβ,neg_zero]

private abbrev cotangentMap : Ω[A⁄k] →ₗ[A] Ω[intersectionRing f g⁄k] :=
  KaehlerDifferential.map k k A (intersectionRing f g)

private theorem cotangent_surjective : Function.Surjective (cotangentMap (k := k) f g) :=
  KaehlerDifferential.map_surjective_of_surjective k k A (intersectionRing f g)
    Ideal.Quotient.mk_surjective

private theorem conormal_of_map_eq {α β : Ω[A⁄k]}
    (h : cotangentMap f g α = cotangentMap f g β) :
    α - β ∈ conormal (k := k) (ideal f g) := by
  apply (Submodule.Quotient.eq (conormal (k := k) (ideal f g))).mp
  apply (cotangentEquiv (k := k) (ideal f g)).injective
  simpa only [cotangentEquiv_mk] using h

private theorem classTwo_wedge_congr {α α' β β' : Ω[A⁄k]}
    (hα : cotangentMap f g α = cotangentMap f g α')
    (hβ : cotangentMap f g β = cotangentMap f g β') :
    classTwo (k := k) f g (wedge α β) = classTwo f g (wedge α' β') := by
  have h₁ := conormal_left f g (α-α') β (conormal_of_map_eq f g hα)
  change classTwo f g (wedgeLeft β (α-α')) = 0 at h₁
  rw [map_sub,map_sub] at h₁
  have h₂ := conormal_right f g α' (β-β') (conormal_of_map_eq f g hβ)
  change classTwo f g (wedgeRight α' (β-β')) = 0 at h₂
  rw [map_sub,map_sub] at h₂
  exact (sub_eq_zero.mp h₁).trans (sub_eq_zero.mp h₂)

private def cotangentLift (α : Ω[intersectionRing f g⁄k]) : Ω[A⁄k] :=
  (cotangent_surjective (k := k) f g α).choose

private theorem cotangentLift_spec (α : Ω[intersectionRing f g⁄k]) :
    cotangentMap f g (cotangentLift f g α) = α :=
  (cotangent_surjective (k := k) f g α).choose_spec

/-- Only the image of the lift is given the quotient-ring module
structure. It remains a submodule of the original pole quotient. -/
private abbrev killed :=
  Submodule.torsionBySet A (poleForms (K := k) f g 4) (ideal f g)

private def surfacePair (α β : Ω[intersectionRing f g⁄k]) : killed (k := k) f g :=
  ⟨classTwo f g (wedge (cotangentLift f g α) (cotangentLift f g β)),by
    apply (Submodule.mem_torsionBySet_iff _ _).mpr
    rintro ⟨a,ha⟩
    rw [← map_smul]
    exact classTwo_kills_ideal f g a ha _⟩

private theorem surfacePair_pullback (α β : Ω[A⁄k]) :
    (surfacePair f g (cotangentMap f g α) (cotangentMap f g β) :
      poleForms (K := k) f g 4) = classTwo f g (wedge α β) :=
  classTwo_wedge_congr f g (cotangentLift_spec f g _) (cotangentLift_spec f g _)

private theorem surfacePair_add_left (α β γ : Ω[intersectionRing f g⁄k]) :
    surfacePair f g (α+β) γ = surfacePair f g α γ + surfacePair f g β γ := by
  obtain ⟨a,rfl⟩ := cotangent_surjective f g α
  obtain ⟨b,rfl⟩ := cotangent_surjective f g β
  obtain ⟨c,rfl⟩ := cotangent_surjective f g γ
  apply Subtype.ext
  change (surfacePair f g (cotangentMap f g a + cotangentMap f g b) (cotangentMap f g c) :
      poleForms (K := k) f g 4) = _
  rw [← map_add,surfacePair_pullback,surfacePair_pullback,surfacePair_pullback]
  change classTwo f g (wedgeLeft c (a+b)) = _
  rw [map_add,map_add]

private theorem surfacePair_add_right (α β γ : Ω[intersectionRing f g⁄k]) :
    surfacePair f g α (β+γ) = surfacePair f g α β + surfacePair f g α γ := by
  obtain ⟨a,rfl⟩ := cotangent_surjective f g α
  obtain ⟨b,rfl⟩ := cotangent_surjective f g β
  obtain ⟨c,rfl⟩ := cotangent_surjective f g γ
  apply Subtype.ext
  change (surfacePair f g (cotangentMap f g a) (cotangentMap f g b + cotangentMap f g c) :
      poleForms (K := k) f g 4) = _
  rw [← map_add,surfacePair_pullback,surfacePair_pullback,surfacePair_pullback]
  change classTwo f g (wedgeRight a (b+c)) = _
  rw [map_add,map_add]

private theorem cotangentMap_smul (a : A) (α : Ω[A⁄k]) :
    Ideal.Quotient.mk (ideal f g) a • cotangentMap f g α = cotangentMap f g (a • α) := by
  rw [map_smul]
  exact IsScalarTower.algebraMap_smul (intersectionRing f g) a _

private theorem surfacePair_smul_left (c : intersectionRing f g) (α β : Ω[intersectionRing f g⁄k]) :
    surfacePair f g (c • α) β = c • surfacePair f g α β := by
  obtain ⟨a,rfl⟩ := Ideal.Quotient.mk_surjective c
  obtain ⟨u,rfl⟩ := cotangent_surjective f g α
  obtain ⟨v,rfl⟩ := cotangent_surjective f g β
  rw [cotangentMap_smul]
  apply Subtype.ext
  change (surfacePair f g (cotangentMap f g (a • u)) (cotangentMap f g v) :
      poleForms (K := k) f g 4) =
    a • (surfacePair f g (cotangentMap f g u) (cotangentMap f g v) : poleForms (K := k) f g 4)
  rw [surfacePair_pullback,surfacePair_pullback]
  change classTwo f g (wedgeLeft v (a • u)) = _
  rw [map_smul,map_smul]

private theorem surfacePair_smul_right (c : intersectionRing f g) (α β : Ω[intersectionRing f g⁄k]) :
    surfacePair f g α (c • β) = c • surfacePair f g α β := by
  obtain ⟨a,rfl⟩ := Ideal.Quotient.mk_surjective c
  obtain ⟨u,rfl⟩ := cotangent_surjective f g α
  obtain ⟨v,rfl⟩ := cotangent_surjective f g β
  rw [cotangentMap_smul]
  apply Subtype.ext
  change (surfacePair f g (cotangentMap f g u) (cotangentMap f g (a • v)) :
      poleForms (K := k) f g 4) =
    a • (surfacePair f g (cotangentMap f g u) (cotangentMap f g v) : poleForms (K := k) f g 4)
  rw [surfacePair_pullback,surfacePair_pullback]
  change classTwo f g (wedgeRight u (a • v)) = _
  rw [map_smul,map_smul]

private theorem surfacePair_self (α : Ω[intersectionRing f g⁄k]) : surfacePair f g α α = 0 := by
  obtain ⟨a,rfl⟩ := cotangent_surjective f g α
  apply Subtype.ext
  change (surfacePair f g (cotangentMap f g a) (cotangentMap f g a) :
    poleForms (K := k) f g 4) = 0
  rw [surfacePair_pullback,wedge_self,map_zero]

private def surfaceAlternating :
    Ω[intersectionRing f g⁄k] [⋀^Fin 2]→ₗ[intersectionRing f g] killed (k := k) f g where
  toFun v := surfacePair f g (v 0) (v 1)
  map_update_add' v i α β := by
    classical
    fin_cases i <;>
      simp only [Function.update_same,Function.update_noteq (by decide : (0 : Fin 2) ≠ 1),
        Function.update_noteq (by decide : (1 : Fin 2) ≠ 0),
        surfacePair_add_left,surfacePair_add_right]
  map_update_smul' v i a α := by
    classical
    fin_cases i <;>
      simp only [Function.update_same,Function.update_noteq (by decide : (0 : Fin 2) ≠ 1),
        Function.update_noteq (by decide : (1 : Fin 2) ≠ 0),
        surfacePair_smul_left,surfacePair_smul_right]
  map_eq_zero_of_eq' v i j h hij := by
    have he : v 0 = v 1 := by
      fin_cases i <;> fin_cases j <;> simp_all
    change surfacePair f g (v 0) (v 1) = 0
    rw [he,surfacePair_self]

/-- The logarithmic Gysin lift on actual intrinsic two-forms of
`A/(f,g)`. The ordering is `dlog f ∧ dlog g`, with coefficient +1. -/
def gysinTwo : Form k (intersectionRing f g) 2 →ₗ[A] poleForms (K := k) f g 4 :=
  (killed (k := k) f g).subtype.comp
    ((exteriorPower.alternatingMapLinearEquiv (surfaceAlternating f g)).restrictScalars A)

private theorem gysinTwo_wedge (α β : Ω[intersectionRing f g⁄k]) :
    gysinTwo (k := k) f g (wedge α β) = (surfacePair f g α β : poleForms (K := k) f g 4) := by
  change ((exteriorPower.alternatingMapLinearEquiv (surfaceAlternating f g))
    (exteriorPower.ιMulti (intersectionRing f g) 2 ![α,β]) : poleForms (K := k) f g 4) = _
  rw [exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  rfl

private theorem quotient_onePullback (α : Ω[A⁄k]) :
    onePullback (Ideal.Quotient.mkₐ k (ideal f g)) α = cotangentMap f g α :=
  CycleQ2CotangentLocalizationTower.pullback_algebraMap α

/-- Pulling an ambient two-form to the literal quotient and applying
Gysin is exactly its original two-log product in the double-open quotient. -/
theorem gysinTwo_pullback (ω : Form k A 2) :
    gysinTwo (k := k) f g (exteriorPullback (Ideal.Quotient.mkₐ k (ideal f g)) 2 ω) =
      classTwo f g ω := by
  have hω : ω ∈ Submodule.span A (Set.range (exteriorPower.ιMulti A 2)) := by
    rw [exteriorPower.ιMulti_span]
    trivial
  induction hω using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨v,rfl⟩ := hz
    have hv : v = ![v 0,v 1] := by funext i; fin_cases i <;> rfl
    rw [hv]
    change gysinTwo f g (exteriorPullback (Ideal.Quotient.mkₐ k (ideal f g)) 2
      (wedge (v 0) (v 1))) = _
    rw [pull_wedge,quotient_onePullback,quotient_onePullback,gysinTwo_wedge,surfacePair_pullback]
  | zero => simp only [map_zero]
  | add a b _ _ ha hb => simp only [map_add,ha,hb]
  | smul a z _ hz =>
    have hs : exteriorPullback (Ideal.Quotient.mkₐ k (ideal f g)) 2 (a • z) =
        a • exteriorPullback (Ideal.Quotient.mkₐ k (ideal f g)) 2 z := by
      rw [map_smulₛₗ]
      exact IsScalarTower.algebraMap_smul (intersectionRing f g) a _
    rw [hs,map_smul,hz,map_smul]

theorem gysinTwo_projection (ω : Form k A 2) :
    gysinTwo (k := k) f g (exteriorPullback (Ideal.Quotient.mkₐ k (ideal f g)) 2 ω) =
      (singleImages (K := k) f g 4).mkQ
        (cup22 (cochain (K := k) f g) (exteriorPullback (baseMap (T f g)) 2 ω)) := by
  rw [gysinTwo_pullback]
  change quotientFour f g (liftTwo f g ω) = _
  rw [liftTwo_eq_cup]

end CycleQ2DoubleGysinTwoForms

#print axioms CycleQ2DoubleGysinTwoForms.gysinTwo_projection

/-! The same quotient now maps to the second Ext group of the actual
supported source on a framed affine chart. All three localization maps
are induced by the original scheme restrictions, and the Čech boundary
is the existing first-minus-second boundary. -/

namespace CycleQ2DoubleGysinTwoSupported

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
  AlgebraicGeometry TopologicalSpace Opposite
open CycleQ2InjectiveCech (AbSheaf Sections)
open CycleQ2IntrinsicFramedAffineSite (FramedOpen)
open CycleQ2FramedCechFormRow (term coordinates coordinates_restrict singleOpen intersection first second)
open CycleQ2SmoothRelativeFrames (sectionCoefficients)
open CycleQ2RelativeAffineOverlap (restrict)
open CycleQ2FramedAffineSite (restrict_comp)
open CycleQ2WeightedCoordinateExterior (Form)
open CycleQ2ExactFrameThreeDeRham (exteriorPullback onePullback wedge)
open CycleQ2AffineDeRhamFunctorial (exteriorPullback_comp)
open CycleQ2NativeDoubleLocalization
open CycleQ2DoubleGysinOneForms (singleU singleV singleImages poleForms)
open CycleQ2DoubleGysinCotangent (ideal intersectionRing)
open CycleQ2DoubleGysinTwoForms (gysinTwo gysinTwo_projection liftTwo liftTwo_eq_cup)
open CycleQ2LocalPrincipalGysin (cover union_le)
open CycleQ2PrincipalLogSupportClass (restrictionUnit restrictionUnit_val)
open CycleQ2SupportedCechExt (doubleConnecting overlapBoundary ker_connecting)
open CycleQ2LocalGysinProjection (cup22 cup_wedge exteriorMap_front)

variable {k : Type} [Field k] [CharZero k] {X : Scheme.{0}}
  (p : X ⟶ Spec (CommRingCat.of k)) [SmoothOfRelativeDimension 4 p]
  (W : FramedOpen p 4) (f g : Γ(X,W.1))

local instance (O : X.Opens) : Algebra k Γ(X,O) := (sectionCoefficients p O).toAlgebra
local instance : HasExt.{1} (AbSheaf (show TopCat from X)) := HasExt.standard _

private def localizationMap (a : Γ(X,W.1)) (B : FramedOpen p 4)
    (h : B.1 ≤ X.basicOpen a) : Localization.Away a →ₐ[k] Γ(X,B.1) :=
  IsLocalization.Away.liftAlgHom
    (f := restrict p (h.trans (X.basicOpen_le a))) a (by
      change IsUnit (X.presheaf.map (homOfLE (h.trans (X.basicOpen_le a))).op a)
      rw [← restrictionUnit_val a h]
      exact (restrictionUnit a h).isUnit)

private theorem localizationMap_coeff (a : Γ(X,W.1)) (B : FramedOpen p 4)
    (h : B.1 ≤ X.basicOpen a) (b : Γ(X,W.1)) :
    localizationMap p W a B h (algebraMap Γ(X,W.1) (Localization.Away a) b) =
      restrict p (h.trans (X.basicOpen_le a)) b := by
  unfold localizationMap
  exact IsLocalization.Away.lift_eq (S := Localization.Away a)
    (g := (restrict p (h.trans (X.basicOpen_le a))).toRingHom) a _ b

private abbrev singleMap (a : Γ(X,W.1)) := localizationMap p W a (singleOpen p 4 W a) le_rfl

private theorem top_le_product : (intersection p 4 W f g).1 ≤ X.basicOpen (f*g) := by
  rw [X.basicOpen_mul]
  exact le_rfl

private abbrev topMap :=
  localizationMap p W (f*g) (intersection p 4 W f g) (top_le_product p W f g)

private abbrev top_le : (intersection p 4 W f g).1 ≤ W.1 :=
  (first p 4 W f g).le.trans (X.basicOpen_le f)

private theorem topMap_base :
    (topMap p W f g).comp (IsScalarTower.toAlgHom k Γ(X,W.1) (T f g)) =
      restrict p (top_le p W f g) :=
  AlgHom.ext (localizationMap_coeff p W (f*g) (intersection p 4 W f g)
    (top_le_product p W f g))

private theorem topMap_fromU :
    (topMap p W f g).comp (fromU (K := k) f g) =
      (restrict p (first p 4 W f g).le).comp (singleMap p W f) := by
  apply AlgHom.coe_ringHom_injective
  apply IsLocalization.ringHom_ext (Submonoid.powers f)
  ext a
  change topMap p W f g (fromU (K := k) f g (algebraMap Γ(X,W.1) (U f) a)) =
    restrict p (first p 4 W f g).le
      (singleMap p W f (algebraMap Γ(X,W.1) (U f) a))
  rw [CycleQ2DoubleGysinTwoForms.fromU_coeff,localizationMap_coeff,localizationMap_coeff]
  exact AlgHom.congr_fun (restrict_comp p (X.basicOpen_le f) (first p 4 W f g).le) a

private theorem topMap_fromV :
    (topMap p W f g).comp (fromV (K := k) f g) =
      (restrict p (second p 4 W f g).le).comp (singleMap p W g) := by
  apply AlgHom.coe_ringHom_injective
  apply IsLocalization.ringHom_ext (Submonoid.powers g)
  ext a
  change topMap p W f g (fromV (K := k) f g (algebraMap Γ(X,W.1) (V g) a)) =
    restrict p (second p 4 W f g).le
      (singleMap p W g (algebraMap Γ(X,W.1) (V g) a))
  rw [CycleQ2DoubleGysinTwoForms.fromV_coeff,localizationMap_coeff,localizationMap_coeff]
  exact AlgHom.congr_fun (restrict_comp p (X.basicOpen_le g) (second p 4 W f g).le) a

private abbrev actualF : Γ(X,(intersection p 4 W f g).1)ˣ :=
  restrictionUnit f (first p 4 W f g).le

private abbrev actualG : Γ(X,(intersection p 4 W f g).1)ˣ :=
  restrictionUnit g (second p 4 W f g).le

private theorem topMap_F :
    Units.map (topMap p W f g).toRingHom (localizedF (K := k) f g) = actualF p W f g := by
  apply Units.ext
  change topMap p W f g (localizedF (K := k) f g : T f g) = (actualF p W f g : Γ(X,_))
  rw [localizedF_val,localizationMap_coeff,restrictionUnit_val]
  rfl

private theorem topMap_G :
    Units.map (topMap p W f g).toRingHom (localizedG (K := k) f g) = actualG p W f g := by
  apply Units.ext
  change topMap p W f g (localizedG (K := k) f g : T f g) = (actualG p W f g : Γ(X,_))
  rw [localizedG_val,localizationMap_coeff,restrictionUnit_val]
  rfl

/-- The literal two-log numerator is preserved by the actual chart map. -/
theorem topMap_liftTwo (ω : Form k Γ(X,W.1) 2) :
    exteriorPullback (topMap p W f g) 4 (liftTwo f g ω) =
      cup22
        (CycleQ2IntrinsicLogSupportClass.logForm p 4 (intersection p 4 W f g)
          (actualF p W f g) (actualG p W f g))
        (exteriorPullback (restrict p (top_le p W f g)) 2 ω) := by
  change exteriorPullback (topMap p W f g) 4
    (CycleQ2ArbitraryFrameDifferential.front 3
      (CycleQ2PrincipalGysinFunctions.logarithm (localizedF (K := k) f g))
      (CycleQ2ArbitraryFrameDifferential.front 2
        (CycleQ2PrincipalGysinFunctions.logarithm (localizedG (K := k) f g))
        (exteriorPullback (IsScalarTower.toAlgHom k Γ(X,W.1) (T f g)) 2 ω))) = _
  rw [exteriorMap_front,exteriorMap_front,CycleQ2DoubleLogarithmicClass.onePullback_log,
    CycleQ2DoubleLogarithmicClass.onePullback_log,topMap_F,topMap_G,
    ← exteriorPullback_comp,topMap_base]
  rw [CycleQ2IntrinsicLogSupportClass.logForm,CycleQ2DoubleLogarithmicClass.twoLog,wedge,cup_wedge]

private def nativeSection : Form k (T f g) 4 →+ Sections (term p 4 4) (cover f g).X₁ :=
  (coordinates p 4 (intersection p 4 W f g) 4).symm.toAddMonoidHom.comp
    (exteriorPullback (topMap p W f g) 4).toAddMonoidHom

private def singleSection (a : Γ(X,W.1)) :
    Form k (Localization.Away a) 4 →+ Sections (term p 4 4) (singleOpen p 4 W a).1 :=
  (coordinates p 4 (singleOpen p 4 W a) 4).symm.toAddMonoidHom.comp
    (exteriorPullback (singleMap p W a) 4).toAddMonoidHom

private theorem nativeSection_singleU (ω : Form k (U f) 4) :
    nativeSection p W f g (singleU (K := k) f g 4 ω) =
      (term p 4 4).obj.map (homOfLE (first p 4 W f g).le).op (singleSection p W f ω) := by
  apply (coordinates p 4 (intersection p 4 W f g) 4).injective
  rw [coordinates_restrict (h := first p 4 W f g)]
  change (coordinates p 4 (intersection p 4 W f g) 4)
      ((coordinates p 4 (intersection p 4 W f g) 4).symm
        (exteriorPullback (topMap p W f g) 4 (singleU (K := k) f g 4 ω))) =
    CycleQ2FramedCechFormRow.pull p 4 (first p 4 W f g) 4
      ((coordinates p 4 (singleOpen p 4 W f) 4)
        ((coordinates p 4 (singleOpen p 4 W f) 4).symm
          (exteriorPullback (singleMap p W f) 4 ω)))
  rw [AddEquiv.apply_symm_apply,AddEquiv.apply_symm_apply]
  change exteriorPullback (topMap p W f g) 4 (exteriorPullback (fromU (K := k) f g) 4 ω) =
    exteriorPullback (restrict p (first p 4 W f g).le) 4 (exteriorPullback (singleMap p W f) 4 ω)
  rw [← exteriorPullback_comp,← exteriorPullback_comp,topMap_fromU]

private theorem nativeSection_singleV (ω : Form k (V g) 4) :
    nativeSection p W f g (singleV (K := k) f g 4 ω) =
      (term p 4 4).obj.map (homOfLE (second p 4 W f g).le).op (singleSection p W g ω) := by
  apply (coordinates p 4 (intersection p 4 W f g) 4).injective
  rw [coordinates_restrict (h := second p 4 W f g)]
  change (coordinates p 4 (intersection p 4 W f g) 4)
      ((coordinates p 4 (intersection p 4 W f g) 4).symm
        (exteriorPullback (topMap p W f g) 4 (singleV (K := k) f g 4 ω))) =
    CycleQ2FramedCechFormRow.pull p 4 (second p 4 W f g) 4
      ((coordinates p 4 (singleOpen p 4 W g) 4)
        ((coordinates p 4 (singleOpen p 4 W g) 4).symm
          (exteriorPullback (singleMap p W g) 4 ω)))
  rw [AddEquiv.apply_symm_apply,AddEquiv.apply_symm_apply]
  change exteriorPullback (topMap p W f g) 4 (exteriorPullback (fromV (K := k) f g) 4 ω) =
    exteriorPullback (restrict p (second p 4 W f g).le) 4 (exteriorPullback (singleMap p W g) 4 ω)
  rw [← exteriorPullback_comp,← exteriorPullback_comp,topMap_fromV]

private def nativeConnecting :
    Form k (T f g) 4 →+ Ext (CycleQ2RelativeOpenSupport.quotient (union_le f g)) (term p 4 4) 2 :=
  (doubleConnecting (cover f g) (union_le f g) (term p 4 4)).comp (nativeSection p W f g)

private theorem nativeConnecting_zero (ω : Form k (T f g) 4)
    (hω : ω ∈ singleImages (K := k) f g 4) : nativeConnecting p W f g ω = 0 := by
  obtain ⟨u,hu,v,hv,rfl⟩ := Submodule.mem_sup.mp hω
  obtain ⟨a,rfl⟩ := hu
  obtain ⟨b,rfl⟩ := hv
  change nativeSection p W f g (singleU (K := k) f g 4 a + singleV (K := k) f g 4 b) ∈
    (doubleConnecting (cover f g) (union_le f g) (term p 4 4)).ker
  rw [ker_connecting (cover f g) (union_le f g) (term p 4 4)
    (CycleQ2FramedOpenFormCoefficients.term_acyclic p 4 W 4 0)]
  refine ⟨(singleSection p W f a,-singleSection p W g b),?_⟩
  change (term p 4 4).obj.map _ (singleSection p W f a) -
    (term p 4 4).obj.map _ (-singleSection p W g b) = _
  rw [map_neg,sub_neg_eq_add,map_add,nativeSection_singleU,nativeSection_singleV]

/-- The actual support connecting map, descended from the original
double-localization quotient by its two original single-open images. -/
def toSupported : poleForms (K := k) f g 4 →+
    Ext (CycleQ2RelativeOpenSupport.quotient (union_le f g)) (term p 4 4) 2 :=
  QuotientAddGroup.lift (singleImages (K := k) f g 4).toAddSubgroup
    (nativeConnecting p W f g) (nativeConnecting_zero p W f g)

theorem toSupported_mk (ω : Form k (T f g) 4) :
    toSupported p W f g ((singleImages (K := k) f g 4).mkQ ω) =
      doubleConnecting (cover f g) (union_le f g) (term p 4 4)
        ((coordinates p 4 (intersection p 4 W f g) 4).symm
          (exteriorPullback (topMap p W f g) 4 ω)) := rfl

def supportedGysinTwo : Form k (intersectionRing f g) 2 →+
    Ext (CycleQ2RelativeOpenSupport.quotient (union_le f g)) (term p 4 4) 2 :=
  (toSupported p W f g).comp (gysinTwo (k := k) f g).toAddMonoidHom

/-- On every ambient two-form the intrinsic surface Gysin map is the
actual double connecting of its ordered logarithmic product. This is
a coefficient-class comparison on the original scheme chart. -/
theorem supportedGysinTwo_projection (ω : Form k Γ(X,W.1) 2) :
    supportedGysinTwo p W f g (exteriorPullback (Ideal.Quotient.mkₐ k (ideal f g)) 2 ω) =
      doubleConnecting (cover f g) (union_le f g) (term p 4 4)
        ((coordinates p 4 (intersection p 4 W f g) 4).symm
          (cup22
            (CycleQ2IntrinsicLogSupportClass.logForm p 4 (intersection p 4 W f g)
              (actualF p W f g) (actualG p W f g))
            (exteriorPullback (restrict p (top_le p W f g)) 2 ω))) := by
  change toSupported p W f g (gysinTwo f g (exteriorPullback (Ideal.Quotient.mkₐ k (ideal f g)) 2 ω)) = _
  rw [gysinTwo_projection,← liftTwo_eq_cup,toSupported_mk,topMap_liftTwo]

end CycleQ2DoubleGysinTwoSupported

#print axioms CycleQ2DoubleGysinTwoSupported.supportedGysinTwo_projection

/-! The coefficient Gysin class has a canonical image in the full intrinsic
de Rham complex of the same fourfold. The two source connecting maps and
their shifts are exactly those in the original relative supported class. -/

namespace CycleQ2FourfoldTopSupport

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
  AlgebraicGeometry TopologicalSpace Opposite HomologicalComplex
open CycleQ2InjectiveCech (AbSheaf Sections freeOpen freeOpenSections)
open CycleQ2IntrinsicFramedAffineSite (frame)
open CycleQ2IntrinsicDeRhamSheaves
  (relativeDeRham relativeDeRhamInt basisDifferential differential compare topology)
open CycleQ2FramedCechFormRow (term)
open CycleQ2SmoothRelativeFrames (sectionCoefficients)
open CycleQ2WeightedCoordinateExterior (Form)
open CycleQ2SupportedCechExt (doubleConnecting)
open CycleQ2RelativeOpenSupport (quotient shortExact relativeOfSection)
open CycleQ2DerivedOverlapClass (sectionClass)

variable {k : Type} [Field k] [CharZero k] {X : Scheme.{0}}
  (p : X ⟶ Spec (CommRingCat.of k)) [SmoothOfRelativeDimension 4 p]

local instance : HasExt.{1} (AbSheaf (show TopCat from X)) := HasExt.standard _
local instance : HasDerivedCategory.{1} (AbSheaf (show TopCat from X)) :=
  HasDerivedCategory.standard _

private abbrev E := DerivedCategory.singleFunctor (AbSheaf (show TopCat from X)) 0
abbrev complex := relativeDeRhamInt p 4
abbrev target := DerivedCategory.Q.obj (complex p)

/-- The top differential vanishes on the original intrinsic fourfold
complex, since every exact affine cotangent frame has rank four. -/
theorem top_differential_zero : (complex p).d 4 5 = 0 := by
  have hb : basisDifferential p 4 4 = 0 := by
    apply (sheafToPresheaf (topology p 4) AddCommGrpCat).map_injective
    apply NatTrans.ext
    intro B
    letI : Algebra k Γ(X,B.unop.1) := (sectionCoefficients p B.unop.1).toAlgebra
    letI : Subsingleton (Form k Γ(X,B.unop.1) 5) :=
      CycleQ2SurfaceDeRhamChart.exterior_subsingleton (frame p 4 B.unop) (by decide)
    apply ConcreteCategory.hom_ext
    intro ω
    exact Subsingleton.elim _ _
  have hd : differential p 4 4 = 0 := by
    unfold differential
    rw [hb]
    letI : (compare p 4).functor.Full := (compare p 4).fullyFaithfulFunctor.full
    simp only [CategoryTheory.Functor.map_zero]
  have hn : (relativeDeRham p 4).d 4 5 = differential p 4 4 := by
    simp only [relativeDeRham,CochainComplex.of_d]
  change ((relativeDeRham p 4).extend (ComplexShape.embeddingUpIntGE 0)).d 4 5 = 0
  rw [(relativeDeRham p 4).extend_d_eq (ComplexShape.embeddingUpIntGE 0)
    (Int.zero_add 4) (Int.zero_add 5)]
  simp only [hn,hd,comp_zero,zero_comp]

/-- Inclusion of the actual fourth term, with no choice of a cohomology
class or a scalar normalization. -/
def topInclusion : E.obj (term p 4 4) ⟶ (target p)⟦(4 : ℤ)⟧ :=
  CycleQ2KInjectiveSections.closedClass (term p 4 4) (complex p) 4 (𝟙 _) (by
    rw [Category.id_comp,top_differential_zero])

private def topPostAt (P : AbSheaf (show TopCat from X)) (n : ℕ) (m : ℤ)
    (h : 4 + (n : ℤ) = m) :
    Ext P (term p 4 4) n →+ (E.obj P ⟶ (target p)⟦m⟧) where
  toFun a := a.hom.comp (topInclusion p) h
  map_zero' := by simp only [Ext.zero_hom,ShiftedHom.zero_comp]
  map_add' a b := by simp only [Ext.add_hom,ShiftedHom.add_comp]

/-- Actual shifted postcomposition from top-form Ext to full de Rham
cohomology, retaining the original source object. -/
def topPost (P : AbSheaf (show TopCat from X)) (n : ℕ) :
    Ext P (term p 4 4) n →+ (E.obj P ⟶ (target p)⟦4 + (n : ℤ)⟧) :=
  topPostAt p P n (4 + (n : ℤ)) rfl

/-- In particular, replacing a principal-equation support source by
the actual closed-graph source uses its original source map. -/
theorem topPost_precomp {P Q : AbSheaf (show TopCat from X)}
    (f : Q ⟶ P) (n : ℕ) (a : Ext P (term p 4 4) n) :
    topPost p Q n ((Ext.mk₀ f).comp a (zero_add n)) =
      E.map f ≫ topPost p P n a := by
  change ((Ext.mk₀ f).comp a (zero_add n)).hom.comp (topInclusion p) rfl = _
  rw [Ext.comp_hom,Ext.mk₀_hom]
  simpa only [ShiftedHom.mk₀_comp] using
    (ShiftedHom.comp_assoc (ShiftedHom.mk₀ (0 : ℤ) rfl (E.map f)) a.hom (topInclusion p)
      (add_zero _) rfl (by simp only [add_zero]))

theorem shifted_closed (O : X.Opens) (s : Sections (term p 4 4) O) :
    (((complex p)⟦(4 : ℤ)⟧).d 0 1).hom.app (op O) s = 0 := by
  rw [CochainComplex.shiftFunctor_obj_d',Int.negOnePow_even 4 ⟨2,rfl⟩,
    one_smul,top_differential_zero] <;> rfl

private theorem sectionClass_four {P : AbSheaf (show TopCat from X)}
    {L : CochainComplex (AbSheaf (show TopCat from X)) ℤ}
    (a : P ⟶ L.X 4) (ha : a ≫ L.d 4 5 = 0) :
    sectionClass (4 : ℤ) (show P ⟶ (L⟦(4 : ℤ)⟧).X 0 from a) (by
      rw [CochainComplex.shiftFunctor_obj_d',Int.negOnePow_even 4 ⟨2,rfl⟩,one_smul]
      exact ha) = CycleQ2KInjectiveSections.closedClass P L 4 a ha := by
  have he : a ≫ (L.shiftFunctorObjXIso 4 0 4 (by decide)).inv =
      (show P ⟶ (L⟦(4 : ℤ)⟧).X 0 from a) := by
    change a ≫ 𝟙 (L.X 4) = a
    exact Category.comp_id a
  have hs : (a ≫ (L.shiftFunctorObjXIso 4 0 4 (by decide)).inv) ≫
      (L⟦(4 : ℤ)⟧).d 0 1 = 0 := by
    rw [he,CochainComplex.shiftFunctor_obj_d',Int.negOnePow_even 4 ⟨2,rfl⟩,one_smul]
    exact ha
  simpa only [he] using CycleQ2AffineOverlapRepresentatives.sectionClass_eq 4 a ha hs

private theorem topPost_section (O : X.Opens) (s : Sections (term p 4 4) O) :
    topPostAt p (freeOpen O) 0 4 rfl (Ext.mk₀ ((freeOpenSections (term p 4 4) O).symm s)) =
      sectionClass (K := complex p) 4
        (show freeOpen O ⟶ ((complex p)⟦(4 : ℤ)⟧).X 0 from
          (freeOpenSections (term p 4 4) O).symm s) (by
          rw [CochainComplex.shiftFunctor_obj_d',Int.negOnePow_even 4 ⟨2,rfl⟩,
            one_smul,top_differential_zero,comp_zero]) := by
  change (Ext.mk₀ ((freeOpenSections (term p 4 4) O).symm s)).hom.comp (topInclusion p) rfl = _
  rw [Ext.mk₀_hom,ShiftedHom.mk₀_comp,sectionClass_four]
  symm
  simpa only [topInclusion,Category.comp_id] using
    (CycleQ2KInjectiveSections.closedClass_precomp (term p 4 4) (complex p)
      ((freeOpenSections (term p 4 4) O).symm s) 4 (𝟙 _) (by
        rw [Category.id_comp,top_differential_zero]))

private theorem topPostAt_boundary {S : ShortComplex (AbSheaf (show TopCat from X))}
    (hS : S.ShortExact) {n n' : ℕ} (hn : 1+n=n')
    (m : ℤ) (hm : 4 + (n : ℤ) = m) (a : Ext S.X₁ (term p 4 4) n) :
    topPostAt p S.X₃ n' (m+1) (by omega) (hS.extClass.comp a hn) =
      CycleQ2DerivedSourceBoundary.connecting hS (target p) m (topPostAt p S.X₁ n m hm a) := by
  change (hS.extClass.comp a hn).hom.comp (topInclusion p) _ = _
  rw [Ext.comp_hom,hS.extClass_hom]
  calc
    (hS.singleδ.comp a.hom _).comp (topInclusion p) _ =
        hS.singleδ.comp (a.hom.comp (topInclusion p) hm) rfl :=
      ShiftedHom.comp_assoc hS.singleδ a.hom (topInclusion p) (by omega) hm (by omega)
    _ = _ := by
      rw [ShiftedHom.comp,shiftFunctorAdd'_eq_shiftFunctorAdd] <;> rfl

/-- The coefficient double boundary followed by the top-term inclusion
is the original relative supported de Rham construction, with its
original two source boundaries and its original shift convention. -/
theorem topPost_doubleConnecting
    (S : (Opens.grothendieckTopology X).MayerVietorisSquare)
    {O : X.Opens} (h : S.X₄ ≤ O) (s : Sections (term p 4 4) S.X₁) :
    topPost p (quotient h) 2 (doubleConnecting S h (term p 4 4) s) =
      relativeOfSection (K := complex p) 4 S h
        (show Sections (((complex p)⟦(4 : ℤ)⟧).X 0) S.X₁ from s)
        (shifted_closed p S.X₁ s) := by
  change topPostAt p (quotient h) 2 6 rfl
    ((shortExact h).extClass.comp
      (S.shortComplex_shortExact.extClass.comp
        (Ext.mk₀ ((freeOpenSections (term p 4 4) S.X₁).symm s)) rfl) rfl) = _
  rw [topPostAt_boundary p (shortExact h) rfl 5 rfl,
    topPostAt_boundary p S.shortComplex_shortExact rfl 4 rfl,topPost_section]
  unfold CycleQ2DerivedSourceBoundary.connecting
    CycleQ2RelativeOpenSupport.relativeOfSection CycleQ2RelativeOpenSupport.relativeClass
    CycleQ2DerivedOverlapClass.overlapClass
  rw [(shortExact h).extClass_hom,S.shortComplex_shortExact.extClass_hom]

end CycleQ2FourfoldTopSupport

namespace CycleQ2DoubleGysinTwoDeRham

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open CycleQ2InjectiveCech (AbSheaf Sections)
open CycleQ2IntrinsicFramedAffineSite (FramedOpen)
open CycleQ2FramedCechFormRow (term coordinates intersection first second)
open CycleQ2SmoothRelativeFrames (sectionCoefficients)
open CycleQ2RelativeAffineOverlap (restrict)
open CycleQ2WeightedCoordinateExterior (Form)
open CycleQ2ExactFrameThreeDeRham (exteriorPullback)
open CycleQ2DoubleGysinCotangent (ideal intersectionRing)
open CycleQ2LocalPrincipalGysin (cover union_le)
open CycleQ2PrincipalLogSupportClass (restrictionUnit)
open CycleQ2LocalGysinProjection (cup22)
open CycleQ2FourfoldTopSupport (complex target topPost shifted_closed topPost_doubleConnecting)

variable {k : Type} [Field k] [CharZero k] {X : Scheme.{0}}
  (p : X ⟶ Spec (CommRingCat.of k)) [SmoothOfRelativeDimension 4 p]
  (W : FramedOpen p 4) (f g : Γ(X,W.1))

local instance (O : X.Opens) : Algebra k Γ(X,O) := (sectionCoefficients p O).toAlgebra
local instance : HasExt.{1} (AbSheaf (show TopCat from X)) := HasExt.standard _
local instance : HasDerivedCategory.{1} (AbSheaf (show TopCat from X)) :=
  HasDerivedCategory.standard _

private abbrev E := DerivedCategory.singleFunctor (AbSheaf (show TopCat from X)) 0

/-- The ordered logarithmic product on the original intersection of
the two principal chart opens. -/
def productSection (ω : Form k Γ(X,W.1) 2) : Sections (term p 4 4) (cover f g).X₁ :=
  (coordinates p 4 (intersection p 4 W f g) 4).symm
    (cup22
      (CycleQ2IntrinsicLogSupportClass.logForm p 4 (intersection p 4 W f g)
        (restrictionUnit f (first p 4 W f g).le)
        (restrictionUnit g (second p 4 W f g).le))
      (exteriorPullback (restrict p ((first p 4 W f g).le.trans (X.basicOpen_le f))) 2 ω))

/-- The original intrinsic two-form Gysin class, now with its genuine
degree-six de Rham target and its unchanged relative support source. -/
def gysinTwo : Form k (intersectionRing f g) 2 →+
    (E.obj (CycleQ2RelativeOpenSupport.quotient (union_le f g)) ⟶ (target p)⟦(6 : ℤ)⟧) :=
  (topPost p (CycleQ2RelativeOpenSupport.quotient (union_le f g)) 2).comp
    (CycleQ2DoubleGysinTwoSupported.supportedGysinTwo p W f g)

/-- The comparison has coefficient +1: the same ordered two-log
product represents both the descended surface form and the original
relative supported de Rham class. No closure condition on the ambient
two-form is needed for this top-degree local calculation. -/
theorem gysinTwo_projection (ω : Form k Γ(X,W.1) 2) :
    gysinTwo p W f g (exteriorPullback (Ideal.Quotient.mkₐ k (ideal f g)) 2 ω) =
      CycleQ2RelativeOpenSupport.relativeOfSection (K := complex p) 4 (cover f g) (union_le f g)
        (show Sections (((complex p)⟦(4 : ℤ)⟧).X 0) (cover f g).X₁ from productSection p W f g ω)
        (shifted_closed p (cover f g).X₁ (productSection p W f g ω)) := by
  change topPost p (CycleQ2RelativeOpenSupport.quotient (union_le f g)) 2
    (CycleQ2DoubleGysinTwoSupported.supportedGysinTwo p W f g
      (exteriorPullback (Ideal.Quotient.mkₐ k (ideal f g)) 2 ω)) = _
  rw [CycleQ2DoubleGysinTwoSupported.supportedGysinTwo_projection]
  exact topPost_doubleConnecting p (cover f g) (union_le f g) (productSection p W f g ω)

variable {Z : Scheme.{0}} (i : Z ⟶ X) [IsClosedImmersion i]
  (he : CycleQ2LocalPrincipalGysin.locus f g = (W.1 : Set X) ∩ Set.range i)

/-- This is the same source refinement as in
`CycleQ2ClosedGraphSupport.classOf`, for the same closed immersion. -/
def graphSourceMap : CycleQ2ClosedGraphSupport.support i W.1 ⟶
    CycleQ2RelativeOpenSupport.quotient (union_le f g) :=
  (CycleQ2RelativeSupportRefinement.supportMap
    (show W.1 ⊓ CycleQ2ClosedGraphSupport.complement i ≤ W.1 from inf_le_left)
    (union_le f g) (CycleQ2ClosedGraphSupport.union_eq_complement i f g he).ge le_rfl).τ₃

/-- The coefficient Gysin class on the unchanged closed-graph support,
followed by the intrinsic fourth-term inclusion. -/
def graphGysinTwo : Form k (intersectionRing f g) 2 →+
    (E.obj (CycleQ2ClosedGraphSupport.support i W.1) ⟶ (target p)⟦(6 : ℤ)⟧) :=
  (topPost p (CycleQ2ClosedGraphSupport.support i W.1) 2).comp
    (((Ext.mk₀ (graphSourceMap p W f g i he)).precomp (term p 4 4) (zero_add 2)).comp
      (CycleQ2DoubleGysinTwoSupported.supportedGysinTwo p W f g))

theorem graphGysinTwo_eq_precomp (η : Form k (intersectionRing f g) 2) :
    graphGysinTwo p W f g i he η = E.map (graphSourceMap p W f g i he) ≫ gysinTwo p W f g η :=
  CycleQ2FourfoldTopSupport.topPost_precomp p (graphSourceMap p W f g i he) 2
    (CycleQ2DoubleGysinTwoSupported.supportedGysinTwo p W f g η)

/-- The local supported product retains exactly the source map and
ordered logarithmic representative of the original graph class. -/
theorem graphGysinTwo_projection (ω : Form k Γ(X,W.1) 2) :
    graphGysinTwo p W f g i he (exteriorPullback (Ideal.Quotient.mkₐ k (ideal f g)) 2 ω) =
      E.map (graphSourceMap p W f g i he) ≫
        CycleQ2RelativeOpenSupport.relativeOfSection (K := complex p) 4 (cover f g) (union_le f g)
          (show Sections (((complex p)⟦(4 : ℤ)⟧).X 0) (cover f g).X₁ from productSection p W f g ω)
          (shifted_closed p (cover f g).X₁ (productSection p W f g ω)) := by
  rw [graphGysinTwo_eq_precomp,gysinTwo_projection]

end CycleQ2DoubleGysinTwoDeRham

#print axioms CycleQ2FourfoldTopSupport.top_differential_zero
#print axioms CycleQ2FourfoldTopSupport.topPost_doubleConnecting
#print axioms CycleQ2DoubleGysinTwoDeRham.gysinTwo_projection
#print axioms CycleQ2DoubleGysinTwoDeRham.graphGysinTwo_projection
