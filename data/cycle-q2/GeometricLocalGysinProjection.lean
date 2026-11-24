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

/-!
# Intrinsic de Rham transport along the actual open immersion

All exterior degrees use the original map on section rings. On the
dense exact affine basis this map is an algebra isomorphism, and its
ordinary Kähler pullback commutes with the intrinsic differential.
The resulting comparison is therefore an isomorphism of the actual
sheaf complexes, including their extension to integer degrees.
-/

namespace CycleQ2IntrinsicOpenTransport

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite Module
open HomologicalComplex
open CycleQ2IntrinsicFramedAffineSite (FramedOpen inclusion frame functions frame_apply cover_dense)
open CycleQ2IntrinsicDeRhamSheaves
  (sheafForms differential relativeDeRham relativeDeRhamInt onBasisIso onBasisIso_d)
open CycleQ2RankOneOpenRestriction (onImage)
open CycleQ2RelativeOpenKahler (sectionIso affine_image)
open CycleQ2RelativeAffineOverlap (restrict baseChangeFrame baseChangeFrame_apply)
open CycleQ2SmoothRelativeFrames (sectionCoefficients)
open CycleQ2ExactFrameThreeDeRham (exteriorPullback)
open CycleQ2AffineDeRhamFunctorial (exteriorPullback_id exteriorPullback_comp)
open CycleQ2IntrinsicOrdinaryExterior (forms toSheaf toSheaf_onBasis)
open scoped KaehlerDifferential

variable {k : Type} [Field k] [CharZero k] {X Y : Scheme.{0}}
  (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
  (j : Y ⟶ X) [IsOpenImmersion j] (hj : j ≫ f = g) (r : ℕ)
  [SmoothOfRelativeDimension r f] [SmoothOfRelativeDimension r g]

local instance : (inclusion g r).IsCoverDense (Opens.grothendieckTopology Y) :=
  cover_dense g r

local instance : (onImage j).Additive where

/-- The image has an exact frame obtained by the actual section-ring
isomorphism; it is not assigned a new unrelated cotangent basis. -/
def imageFramed (V : FramedOpen g r) : FramedOpen f r := by
  letI : Algebra k Γ(X,j ''ᵁ V.1) := (sectionCoefficients f (j ''ᵁ V.1)).toAlgebra
  letI : Algebra k Γ(Y,V.1) := (sectionCoefficients g V.1).toAlgebra
  let e := (sectionIso f g j hj V.1).symm
  letI : Algebra Γ(Y,V.1) Γ(X,j ''ᵁ V.1) := e.toRingHom.toAlgebra
  letI : IsScalarTower k Γ(Y,V.1) Γ(X,j ''ᵁ V.1) := IsScalarTower.of_algHom e.toAlgHom
  letI : Algebra.Etale Γ(Y,V.1) Γ(X,j ''ᵁ V.1) :=
    (RingHom.Etale.of_bijective e.bijective).toAlgebra
  refine ⟨j ''ᵁ V.1,affine_image (j := j) V.2.1,?_⟩
  obtain ⟨u,b,hb⟩ := V.2.2
  exact ⟨fun i => e (u i),baseChangeFrame b,baseChangeFrame_apply b u hb⟩

/-- Ordinary forms in every degree, via the genuine Kähler map. -/
def formIso (n : ℕ) (V : Y.Opens) :
    (forms f n).obj (op (j ''ᵁ V)) ≃+ (forms g n).obj (op V) := by
  letI : Algebra k Γ(X,j ''ᵁ V) := (sectionCoefficients f (j ''ᵁ V)).toAlgebra
  letI : Algebra k Γ(Y,V) := (sectionCoefficients g V).toAlgebra
  let e := sectionIso f g j hj V
  exact {
    toFun := exteriorPullback e.toAlgHom n
    invFun := exteriorPullback e.symm.toAlgHom n
    left_inv := fun ω => by
      rw [← exteriorPullback_comp,AlgEquiv.symm_comp,exteriorPullback_id]
    right_inv := fun ω => by
      rw [← exteriorPullback_comp,AlgEquiv.comp_symm,exteriorPullback_id]
    map_add' := map_add _ }

theorem formIso_restrict (n : ℕ) {V W : Y.Opens} (h : W ≤ V)
    (ω : (forms f n).obj (op (j ''ᵁ V))) :
    formIso f g j hj n W ((forms f n).map (homOfLE (j.image_mono h)).op ω) =
      (forms g n).map (homOfLE h).op (formIso f g j hj n V ω) := by
  letI : Algebra k Γ(X,j ''ᵁ V) := (sectionCoefficients f (j ''ᵁ V)).toAlgebra
  letI : Algebra k Γ(X,j ''ᵁ W) := (sectionCoefficients f (j ''ᵁ W)).toAlgebra
  letI : Algebra k Γ(Y,V) := (sectionCoefficients g V).toAlgebra
  letI : Algebra k Γ(Y,W) := (sectionCoefficients g W).toAlgebra
  change exteriorPullback (sectionIso f g j hj W).toAlgHom n
      (exteriorPullback (restrict f (j.image_mono h)) n ω) =
    exteriorPullback (restrict g h) n
      (exteriorPullback (sectionIso f g j hj V).toAlgHom n ω)
  rw [← exteriorPullback_comp,← exteriorPullback_comp]
  have he : (sectionIso f g j hj W).toAlgHom.comp (restrict f (j.image_mono h)) =
      (restrict g h).comp (sectionIso f g j hj V).toAlgHom := by
    ext a
    exact ConcreteCategory.congr_hom (j.appIso_hom_naturality (homOfLE h).op) a
  rw [he]

private abbrev F (n : ℕ) := (onImage j).obj (sheafForms f r n)

def component (n : ℕ) (V : FramedOpen g r) :
    (F f j r n).obj.obj (op V.1) ≃+ (sheafForms g r n).obj.obj (op V.1) :=
  (((onBasisIso f r n).app (op (imageFramed f g j hj r V))).addCommGroupIsoToAddEquiv.trans
    (formIso f g j hj n V.1)).trans
    ((onBasisIso g r n).app (op V)).symm.addCommGroupIsoToAddEquiv

theorem component_coordinates (n : ℕ) (V : FramedOpen g r)
    (ω : (F f j r n).obj.obj (op V.1)) :
    (onBasisIso g r n).hom.app (op V) (component f g j hj r n V ω) =
      formIso f g j hj n V.1
        ((onBasisIso f r n).hom.app (op (imageFramed f g j hj r V)) ω) := by
  change ((onBasisIso g r n).app (op V)).hom
    (((onBasisIso g r n).app (op V)).inv _) = _
  exact Iso.inv_hom_id_apply _ _

private theorem component_natural (n : ℕ) {V W : FramedOpen g r} (a : W ⟶ V)
    (ω : (F f j r n).obj.obj (op V.1)) :
    component f g j hj r n W ((F f j r n).obj.map (homOfLE a.le).op ω) =
      (sheafForms g r n).obj.map (homOfLE a.le).op (component f g j hj r n V ω) := by
  let e := (onBasisIso f r n).hom
  let m := (onBasisIso g r n).inv
  let a' : imageFramed f g j hj r W ⟶ imageFramed f g j hj r V :=
    homOfLE (j.image_mono a.le)
  have he := NatTrans.naturality_apply e a'.op ω
  change e.app (op (imageFramed f g j hj r W))
      ((F f j r n).obj.map (homOfLE a.le).op ω) =
    (forms f n).map (homOfLE (j.image_mono a.le)).op
      (e.app (op (imageFramed f g j hj r V)) ω) at he
  change m.app (op W) (formIso f g j hj n W.1
      (e.app (op (imageFramed f g j hj r W))
        ((F f j r n).obj.map (homOfLE a.le).op ω))) =
    (sheafForms g r n).obj.map (homOfLE a.le).op
      (m.app (op V) (formIso f g j hj n V.1
        (e.app (op (imageFramed f g j hj r V)) ω)))
  rw [he,formIso_restrict f g j hj n a.le]
  exact NatTrans.naturality_apply m a.op _

def basisIso (n : ℕ) :
    (inclusion g r).op ⋙ (F f j r n).obj ≅
      (inclusion g r).op ⋙ (sheafForms g r n).obj :=
  NatIso.ofComponents (fun V => (component f g j hj r n V.unop).toAddCommGrpIso)
    (fun a => by ext ω; exact component_natural f g j hj r n a.unop ω)

/-- Intrinsic exterior sheaves commute with the actual open immersion. -/
def comparison (n : ℕ) : F f j r n ≅ sheafForms g r n :=
  Functor.IsCoverDense.sheafIso (G := inclusion g r)
    (K := Opens.grothendieckTopology Y) (basisIso f g j hj r n)

theorem comparison_onBasis (n : ℕ) (V : FramedOpen g r)
    (ω : (F f j r n).obj.obj (op V.1)) :
    (comparison f g j hj r n).hom.hom.app (op V.1) ω = component f g j hj r n V ω := by
  have h := Functor.IsCoverDense.sheafHom_restrict_eq (G := inclusion g r)
    (K := Opens.grothendieckTopology Y) (ℱ' := sheafForms g r n) (basisIso f g j hj r n).hom
  exact ConcreteCategory.congr_hom (NatTrans.congr_app h (op V)) ω

/-- This comparison preserves the original differential in every
exterior degree. It is not merely a termwise sheaf equivalence. -/
theorem comparison_d (n : ℕ) :
    (onImage j).map (differential f r n) ≫ (comparison f g j hj r (n+1)).hom =
      (comparison f g j hj r n).hom ≫ differential g r n := by
  apply (Functor.IsCoverDense.restrictHomEquivHom (G := inclusion g r)
    (K := Opens.grothendieckTopology Y) (ℱ' := sheafForms g r (n+1))).symm.injective
  ext V ω
  let W := imageFramed f g j hj r V.unop
  letI : Algebra k Γ(X,W.1) := (sectionCoefficients f W.1).toAlgebra
  letI : Algebra k Γ(Y,V.unop.1) := (sectionCoefficients g V.unop.1).toAlgebra
  change (comparison f g j hj r (n+1)).hom.hom.app (op V.unop.1)
      ((differential f r n).hom.app (op W.1) ω) =
    (differential g r n).hom.app (op V.unop.1)
      ((comparison f g j hj r n).hom.hom.app (op V.unop.1) ω)
  rw [comparison_onBasis,comparison_onBasis]
  let e := (onBasisIso g r (n+1)).app V
  apply (ConcreteCategory.bijective_of_isIso e.hom).injective
  rw [component_coordinates]
  have hf := ConcreteCategory.congr_hom (onBasisIso_d f r n W) ω
  have hg := ConcreteCategory.congr_hom (onBasisIso_d g r n V.unop)
    (component f g j hj r n V.unop ω)
  change (onBasisIso f r (n+1)).hom.app (op W)
      ((differential f r n).hom.app (op W.1) ω) =
    CycleQ2ArbitraryFrameDifferential.d (frame f r W) n
      ((onBasisIso f r n).hom.app (op W) ω) at hf
  change e.hom ((differential g r n).hom.app (op V.unop.1)
      (component f g j hj r n V.unop ω)) =
    CycleQ2ArbitraryFrameDifferential.d (frame g r V.unop) n
      ((onBasisIso g r n).hom.app V (component f g j hj r n V.unop ω)) at hg
  rw [hf,hg,component_coordinates]
  exact CycleQ2FrameDifferentialNaturality.differential_natural
    (frame f r W) (functions f r W) (frame_apply f r W)
    (frame g r V.unop) (functions g r V.unop) (frame_apply g r V.unop)
    (sectionIso f g j hj V.unop.1).toAlgHom n _

def complexIso :
    ((onImage j).mapHomologicalComplex (.up ℕ)).obj (relativeDeRham f r) ≅
      relativeDeRham g r := by
  refine HomologicalComplex.Hom.isoOfComponents (fun n => comparison f g j hj r n) ?_
  intro i l hil
  have hl : i+1=l := hil
  subst l
  simpa only [Functor.mapHomologicalComplex_obj_d,relativeDeRham,CochainComplex.of_d] using
    (comparison_d f g j hj r i).symm

private def intTerm : (a : Option ℕ) →
    (onImage j).obj (extend.X (relativeDeRham f r) a) ≅ extend.X (relativeDeRham g r) a
  | some n => comparison f g j hj r n
  | none => ((onImage j).map_isZero (isZero_zero _)).iso (isZero_zero _)

private theorem intTerm_d (a b : Option ℕ) :
    (intTerm f g j hj r a).hom ≫ extend.d (relativeDeRham g r) a b =
      (onImage j).map (extend.d (relativeDeRham f r) a b) ≫ (intTerm f g j hj r b).hom := by
  cases a with
  | none => exact ((onImage j).map_isZero (isZero_zero _)).eq_of_src _ _
  | some a => cases b with
    | none => exact (isZero_zero _).eq_of_tgt _ _
    | some b => exact (complexIso f g j hj r).hom.comm a b

/-- The same actual de Rham transport in integer degrees, including
the zero terms used by the derived support constructions. -/
def complexIsoInt :
    ((onImage j).mapHomologicalComplex (.up ℤ)).obj (relativeDeRhamInt f r) ≅
      relativeDeRhamInt g r :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => intTerm f g j hj r ((ComplexShape.embeddingUpIntGE 0).r n))
    (fun i l _ => intTerm_d f g j hj r _ _)

end CycleQ2IntrinsicOpenTransport

#print axioms CycleQ2IntrinsicOpenTransport.comparison_d
#print axioms CycleQ2IntrinsicOpenTransport.complexIsoInt

namespace CycleQ2GenericHodgeDeRham

open CategoryTheory AlgebraicGeometry
open CycleQ2NativeWeightedCover (ambientToField)
open CycleQ2GenericHodgeModel (genericHodgeIso genericHodgeIso_over)
open CycleQ2GeometricHodgeThreefold (toBase)
open CycleQ2MonicGenericSmooth (coeff)
open CycleQ2IntrinsicDeRhamSheaves (sheafForms relativeDeRhamInt)
open CycleQ2RankOneOpenRestriction (onImage)

local instance : SmoothOfRelativeDimension 3 ambientToField := CycleQ2NativeGenericSmooth.ambient_smooth
local instance : SmoothOfRelativeDimension 3 (toBase coeff) :=
  CycleQ2MonicGenericSmooth.explicit_projective_smooth

/-- The intrinsic generic forms are transported to the explicit Hodge
model by the actual coefficient-preserving scheme isomorphism. -/
def formsIso (n : ℕ) :
    (onImage genericHodgeIso.hom).obj (sheafForms ambientToField 3 n) ≅
      sheafForms (toBase coeff) 3 n :=
  CycleQ2IntrinsicOpenTransport.comparison ambientToField (toBase coeff)
    genericHodgeIso.hom genericHodgeIso_over 3 n

local instance : (onImage genericHodgeIso.hom).Additive where

/-- The actual relative de Rham complexes, not only their canonical
terms, agree on the two already identified generic schemes. -/
def deRhamIso :
    ((onImage genericHodgeIso.hom).mapHomologicalComplex (.up ℤ)).obj
      (relativeDeRhamInt ambientToField 3) ≅ relativeDeRhamInt (toBase coeff) 3 :=
  CycleQ2IntrinsicOpenTransport.complexIsoInt ambientToField (toBase coeff)
    genericHodgeIso.hom genericHodgeIso_over 3

end CycleQ2GenericHodgeDeRham

#print axioms CycleQ2GenericHodgeDeRham.deRhamIso

/-!
# Cohomology transport through the original generic scheme isomorphism

The functor on sheaves is the same open-image functor used above.  Its
inverse comes from the inverse scheme morphism.  Consequently its exact
derived functor is an equivalence, and the comparison preserves the
actual free source at the whole scheme and every de Rham degree.
-/

namespace CycleQ2ExactEquivalenceDerived

open CategoryTheory CategoryTheory.Limits HomologicalComplex

universe u v u' v' w w'
variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasDerivedCategory.{w'} D]
  (E : C ≌ D) [E.functor.Additive]

/-- An actual additive equivalence induces an equivalence of the
localized categories.  Quasi-isomorphisms are both preserved and
reflected by the same functor on complexes. -/
def derivedEquiv : DerivedCategory C ≌ DerivedCategory D := by
  let Φ := E.functor.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism (.up ℤ)
  letI : Φ.functor.IsEquivalence := (E.mapHomologicalComplex (.up ℤ)).isEquivalence_functor
  letI : Φ.IsInduced := ⟨by
    ext K L a
    exact HomologicalComplex.quasiIso_map_iff_of_preservesHomology a E.functor⟩
  letI : Φ.IsLocalizedEquivalence := Φ.isLocalizedEquivalence_of_isInduced
  letI : E.functor.mapDerivedCategory.IsEquivalence := by
    change (Φ.localizedFunctor DerivedCategory.Q DerivedCategory.Q).IsEquivalence
    infer_instance
  exact E.functor.mapDerivedCategory.asEquivalence

theorem derived_faithful : E.functor.mapDerivedCategory.Faithful :=
  (derivedEquiv E).fullyFaithfulFunctor.faithful

theorem derived_full : E.functor.mapDerivedCategory.Full :=
  (derivedEquiv E).fullyFaithfulFunctor.full

end CycleQ2ExactEquivalenceDerived

namespace CycleQ2SchemeIsoCohomology

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open CycleQ2InjectiveCech (AbSheaf freeOpen)
open CycleQ2GeometricSheafCohomologyRestriction
  (continuousSheafEquiv constantSourceIso terminalFreeSheafIso mapExt_bijective_of_fixedSource)
open CycleQ2RankOneOpenRestriction (onImage)

variable {X Y : Scheme.{0}} (e : Y ≅ X)

/-- The inverse maps on opens are induced by the two original scheme
morphisms, with their actual images as objects. -/
def opensEquiv : Y.Opens ≌ X.Opens where
  functor := e.hom.opensFunctor
  inverse := e.inv.opensFunctor
  unitIso := NatIso.ofComponents (fun U => eqToIso (by
    change U = e.inv ''ᵁ (e.hom ''ᵁ U)
    rw [← Scheme.Hom.comp_image,e.hom_inv_id,Scheme.Hom.id_image]))
    (fun _ => Subsingleton.elim _ _)
  counitIso := NatIso.ofComponents (fun U => eqToIso (by
    change e.hom ''ᵁ (e.inv ''ᵁ U) = U
    rw [← Scheme.Hom.comp_image,e.inv_hom_id,Scheme.Hom.id_image]))
    (fun _ => Subsingleton.elim _ _)
  functor_unitIso_comp _ := Subsingleton.elim _ _

/-- The forward functor is definitionally the already used
`onImage e.hom`, rather than a separately chosen equivalence. -/
def sheafEquiv : AbSheaf (show TopCat from X) ≌ AbSheaf (show TopCat from Y) :=
  continuousSheafEquiv (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)
    (opensEquiv e.symm)

local instance : (sheafEquiv e).functor.Additive where
local instance : (onImage e.hom).Additive where
local instance : HasExt.{1} (AbSheaf (show TopCat from X)) := HasExt.standard _
local instance : HasExt.{1} (AbSheaf (show TopCat from Y)) := HasExt.standard _
local instance : HasDerivedCategory.{1} (AbSheaf (show TopCat from X)) :=
  HasDerivedCategory.standard _
local instance : HasDerivedCategory.{1} (AbSheaf (show TopCat from Y)) :=
  HasDerivedCategory.standard _

def constantIso : (sheafEquiv e).functor.obj
      ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat).obj
        (AddCommGrpCat.of (ULift.{0} ℤ))) ≅
    (constantSheaf (Opens.grothendieckTopology Y) AddCommGrpCat).obj
      (AddCommGrpCat.of (ULift.{0} ℤ)) :=
  constantSourceIso (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)
    (opensEquiv e.symm) ⊤ isTerminalTop

/-- The actual integer source at the whole scheme is preserved. -/
def freeTopIso : (sheafEquiv e).functor.obj (freeOpen (⊤ : X.Opens)) ≅
    freeOpen (⊤ : Y.Opens) :=
  (sheafEquiv e).functor.mapIso
    (terminalFreeSheafIso (Opens.grothendieckTopology X) ⊤ isTerminalTop) ≪≫
      constantIso e ≪≫
        (terminalFreeSheafIso (Opens.grothendieckTopology Y) ⊤ isTerminalTop).symm

/-- Cohomology of the transported sheaf in every degree, through the
actual exact equivalence and its actual constant-source isomorphism. -/
def sheafCohomologyEquiv (F : AbSheaf (show TopCat from X)) (n : ℕ) :
    F.H n ≃+ ((sheafEquiv e).functor.obj F).H n :=
  (AddEquiv.ofBijective ((sheafEquiv e).functor.mapExtAddHom _ F n)
    (mapExt_bijective_of_fixedSource (sheafEquiv e).functor _
      (fun _ => ⟨(sheafEquiv e).functor.map_injective,
        (sheafEquiv e).functor.map_surjective⟩) F n)).trans
      ((((extFunctor n).mapIso (constantIso e).op).app
        ((sheafEquiv e).functor.obj F)).addCommGroupIsoToAddEquiv.symm)

def derivedEquiv : DerivedCategory (AbSheaf (show TopCat from X)) ≌
    DerivedCategory (AbSheaf (show TopCat from Y)) :=
  CycleQ2ExactEquivalenceDerived.derivedEquiv (sheafEquiv e)

private abbrev SX := DerivedCategory.singleFunctor (AbSheaf (show TopCat from X)) 0
private abbrev SY := DerivedCategory.singleFunctor (AbSheaf (show TopCat from Y)) 0

def derivedSourceIso : (derivedEquiv e).functor.obj (SX.obj (freeOpen (⊤ : X.Opens))) ≅
    SY.obj (freeOpen (⊤ : Y.Opens)) :=
  ((sheafEquiv e).functor.mapDerivedCategorySingleFunctor 0).app _ ≪≫
    SY.mapIso (freeTopIso e)

/-- A specified isomorphism of the actual transported complexes induces
the corresponding target isomorphism in the actual derived category. -/
def derivedTargetIso (K : CochainComplex (AbSheaf (show TopCat from X)) ℤ)
    (L : CochainComplex (AbSheaf (show TopCat from Y)) ℤ)
    (i : ((onImage e.hom).mapHomologicalComplex (.up ℤ)).obj K ≅ L) :
    (derivedEquiv e).functor.obj (DerivedCategory.Q.obj K) ≅ DerivedCategory.Q.obj L :=
  (sheafEquiv e).functor.mapDerivedCategoryFactors.app K ≪≫ DerivedCategory.Q.mapIso i

def derivedShiftedTargetIso (K : CochainComplex (AbSheaf (show TopCat from X)) ℤ)
    (L : CochainComplex (AbSheaf (show TopCat from Y)) ℤ)
    (i : ((onImage e.hom).mapHomologicalComplex (.up ℤ)).obj K ≅ L) (n : ℤ) :
    (derivedEquiv e).functor.obj ((DerivedCategory.Q.obj K)⟦n⟧) ≅
      (DerivedCategory.Q.obj L)⟦n⟧ :=
  ((sheafEquiv e).functor.mapDerivedCategory.commShiftIso n).app _ ≪≫
    (shiftFunctor _ n).mapIso (derivedTargetIso e K L i)

/-- Global hypercohomology transport, preserving the original source,
the original complex, and the original integer degree. -/
def globalCohomologyEquiv (K : CochainComplex (AbSheaf (show TopCat from X)) ℤ)
    (L : CochainComplex (AbSheaf (show TopCat from Y)) ℤ)
    (i : ((onImage e.hom).mapHomologicalComplex (.up ℤ)).obj K ≅ L) (n : ℤ) :
    CycleQ2DerivedCoverTop.H (DerivedCategory.Q.obj K) n (⊤ : X.Opens) ≃+
      CycleQ2DerivedCoverTop.H (DerivedCategory.Q.obj L) n (⊤ : Y.Opens) := by
  let F := (derivedEquiv e).functor
  let a := derivedSourceIso e
  let b := derivedShiftedTargetIso e K L i n
  let h : (F.obj (SX.obj (freeOpen (⊤ : X.Opens))) ⟶
        F.obj ((DerivedCategory.Q.obj K)⟦n⟧)) ≃+
      (SY.obj (freeOpen (⊤ : Y.Opens)) ⟶ (DerivedCategory.Q.obj L)⟦n⟧) :=
    { Iso.homCongr a b with
      map_add' x y := by
        change a.inv ≫ (x+y) ≫ b.hom = (a.inv ≫ x ≫ b.hom) + (a.inv ≫ y ≫ b.hom)
        simp only [Preadditive.comp_add,Preadditive.add_comp] }
  exact (AddEquiv.ofBijective F.mapAddHom ⟨F.map_injective,F.map_surjective⟩).trans h

end CycleQ2SchemeIsoCohomology

namespace CycleQ2GenericHodgeDeRham

open CategoryTheory AlgebraicGeometry TopologicalSpace
open CycleQ2NativeWeightedCover (ambientToField)
open CycleQ2GenericHodgeModel (genericHodgeIso genericHodgeIso_over)
open CycleQ2GeometricHodgeThreefold (toBase)
open CycleQ2MonicGenericSmooth (coeff)
open CycleQ2IntrinsicDeRhamSheaves (sheafForms relativeDeRhamInt)
open CycleQ2InjectiveCech (AbSheaf)

local instance : SmoothOfRelativeDimension 3 ambientToField := CycleQ2NativeGenericSmooth.ambient_smooth
local instance : SmoothOfRelativeDimension 3 (toBase coeff) :=
  CycleQ2MonicGenericSmooth.explicit_projective_smooth
local instance (Z : Scheme.{0}) : HasExt.{1} (AbSheaf (show TopCat from Z)) := HasExt.standard _
local instance (Z : Scheme.{0}) : HasDerivedCategory.{1} (AbSheaf (show TopCat from Z)) :=
  HasDerivedCategory.standard _

/-- Actual Hodge sheaf cohomology agrees on the two generic models. -/
def hodgeCohomologyEquiv (p q : ℕ) :
    (sheafForms ambientToField 3 p).H q ≃+ (sheafForms (toBase coeff) 3 p).H q :=
  (CycleQ2SchemeIsoCohomology.sheafCohomologyEquiv genericHodgeIso
    (sheafForms ambientToField 3 p) q).trans
      (((Sheaf.functorH _ q).mapIso (formsIso p)).addCommGroupIsoToAddEquiv)

/-- The original generic derived de Rham classes, including the marked
class, can be transported without changing whether they vanish. -/
def globalDeRhamEquiv (n : ℤ) :
    CycleQ2DerivedCoverTop.H (DerivedCategory.Q.obj (relativeDeRhamInt ambientToField 3)) n ⊤ ≃+
      CycleQ2DerivedCoverTop.H (DerivedCategory.Q.obj (relativeDeRhamInt (toBase coeff) 3)) n ⊤ :=
  CycleQ2SchemeIsoCohomology.globalCohomologyEquiv genericHodgeIso _ _ deRhamIso n

theorem globalDeRhamEquiv_eq_zero_iff (n : ℤ)
    (a : CycleQ2DerivedCoverTop.H
      (DerivedCategory.Q.obj (relativeDeRhamInt ambientToField 3)) n ⊤) :
    globalDeRhamEquiv n a = 0 ↔ a = 0 :=
  (globalDeRhamEquiv n).map_eq_zero_iff

end CycleQ2GenericHodgeDeRham

#print axioms CycleQ2ExactEquivalenceDerived.derivedEquiv
#print axioms CycleQ2GenericHodgeDeRham.hodgeCohomologyEquiv
#print axioms CycleQ2GenericHodgeDeRham.globalDeRhamEquiv_eq_zero_iff

/-!
# The intrinsic top-form class on a smooth threefold

This construction is over an arbitrary characteristic-zero field and
uses the actual intrinsic relative de Rham complex.  In particular it
does not specialize the coefficient field or substitute the fixed
threefold's canonical sheaf for the generic one.
-/

namespace CycleQ2IntrinsicThreefoldTop

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
  AlgebraicGeometry TopologicalSpace Opposite HomologicalComplex
open CycleQ2InjectiveCech
  (AbSheaf Sections freeOpen freeOpenMap freeOpenSections freeOpenSections_naturality)
open CycleQ2CechTwoToDerived (freeOpenSections_postcomp sectionExtZero)
open CycleQ2GeometricSheafLocalIso (res)
open CycleQ2IntrinsicDeRhamSheaves
  (relativeDeRham relativeDeRhamInt sheafForms differential basisForms compare topology)
open CycleQ2IntrinsicFramedAffineSite (frame)
open CycleQ2SmoothRelativeFrames (sectionCoefficients)
open CycleQ2WeightedCoordinateExterior (Form)
open CycleQ2DerivedCoverTop (H)

variable {k : Type} [Field k] [CharZero k] {X : Scheme.{0}}
  (p : X ⟶ Spec (CommRingCat.of k)) [SmoothOfRelativeDimension 3 p]

local instance : HasExt.{1} (AbSheaf (show TopCat from X)) := HasExt.standard _
local instance : HasDerivedCategory.{1} (AbSheaf (show TopCat from X)) :=
  HasDerivedCategory.standard _

abbrev deRham := relativeDeRhamInt p 3
abbrev target := DerivedCategory.Q.obj (deRham p)

variable {p}

local notation "DR" => deRham p
local notation "T" => target p
local notation "F" => sheafForms p 3

local instance : DR.IsStrictlyGE 0 := by
  change ((relativeDeRham p 3).extend (ComplexShape.embeddingUpIntGE 0)).IsStrictlySupported
    (ComplexShape.embeddingUpIntGE 0)
  infer_instance

def termIso (n : ℕ) : DR.X (n : ℤ) ≅ F n :=
  (relativeDeRham p 3).extendXIso (ComplexShape.embeddingUpIntGE 0) (Int.zero_add n)

def coefficients (W : X.Opens) (n : ℕ) : Sections (DR.X (n : ℤ)) W ≃+ Sections (F n) W :=
  (((sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat).mapIso
    (termIso n)).app (op W)).addCommGroupIsoToAddEquiv

theorem coefficients_restrict {U V : X.Opens} (h : U ≤ V) (n : ℕ)
    (s : Sections (DR.X (n : ℤ)) V) :
    coefficients U n (res _ h s) = res _ h (coefficients V n s) :=
  NatTrans.naturality_apply (termIso n).hom.hom (homOfLE h).op s

/-- Exterior degrees above three vanish on the actual sheaf, as they
vanish on every exact affine cotangent frame. -/
theorem forms_above (W : X.Opens) (n : ℕ) (hn : 3 < n) (s : Sections (F n) W) : s = 0 := by
  have hb : (𝟙 (basisForms p 3 n)) = 0 := by
    apply (sheafToPresheaf (topology p 3) AddCommGrpCat).map_injective
    apply NatTrans.ext
    intro V
    letI : Algebra k Γ(X,V.unop.1) := (sectionCoefficients p V.unop.1).toAlgebra
    letI : Subsingleton (Form k Γ(X,V.unop.1) n) :=
      CycleQ2SurfaceDeRhamChart.exterior_subsingleton (frame p 3 V.unop) hn
    apply ConcreteCategory.hom_ext
    intro ω
    exact Subsingleton.elim _ _
  letI : (compare p 3).functor.Full := (compare p 3).fullyFaithfulFunctor.full
  have hf : (𝟙 (F n)) = 0 := by
    simpa only [Functor.map_id,Functor.map_zero] using
      congrArg (fun a => (compare p 3).functor.map a) hb
  have hs := ConcreteCategory.congr_hom (congrArg (fun a => a.hom.app (op W)) hf) s
  exact hs

theorem term_above (W : X.Opens) (n : ℕ) (hn : 3 < n)
    (s : Sections (DR.X (n : ℤ)) W) : s = 0 := by
  apply (coefficients W n).injective
  rw [map_zero]
  exact forms_above W n hn _

theorem affine_above {W : X.Opens} (hW : IsAffineOpen W) (n : ℕ) (hn : 3 < n) :
    Subsingleton (H T (n : ℤ) W) := by
  have terms := CycleQ2AffineExteriorComparison.term_acyclic p 3 hW
  apply subsingleton_of_forall_eq 0
  intro y
  obtain ⟨a,ha,rfl⟩ := CycleQ2AcyclicSectionRepresentatives.surjective
    (freeOpen W) DR 0 terms (n : ℤ) y
  have ha₀ : a = 0 := by
    apply (freeOpenSections _ W).injective
    rw [map_zero]
    exact term_above W n hn _
  apply (CycleQ2AcyclicSectionRepresentatives.zero_iff (freeOpen W) DR 0 terms (n : ℤ) a ha).mpr
  exact ⟨0,by rw [zero_comp,ha₀]⟩

def representative (W : X.Opens) : Sections (F 3) W →+ (freeOpen W ⟶ DR.X 3) :=
  (freeOpenSections _ W).symm.toAddMonoidHom.comp (coefficients W 3).symm.toAddMonoidHom

theorem representative_sections (W : X.Opens) (s : Sections (F 3) W) :
    freeOpenSections _ W (representative W s) = (coefficients W 3).symm s :=
  (freeOpenSections _ W).apply_symm_apply _

theorem representative_closed (W : X.Opens) (s : Sections (F 3) W) :
    representative W s ≫ DR.d 3 4 = 0 := by
  apply (freeOpenSections _ W).injective
  rw [map_zero]
  exact term_above W 4 (by decide) _

private def rawClass (W : X.Opens) (s : Sections (F 3) W) : H T 3 W :=
  CycleQ2KInjectiveSections.closedClass (freeOpen W) DR 3
    (representative W s) (representative_closed W s)

private theorem rawClass_sub (W : X.Opens) (s t : Sections (F 3) W) :
    rawClass W (s-t) = rawClass W s - rawClass W t := by
  unfold rawClass
  rw [map_sub]
  exact CycleQ2AcyclicSectionRepresentatives.closedClass_sub (K := DR) (freeOpen W) 3
    (representative W s) (representative W t) (representative_closed W s) (representative_closed W t)

def localTop (W : X.Opens) : Sections (F 3) W →+ H T 3 W :=
  AddMonoidHom.mk' (rawClass W) (by
    intro s t
    have h := rawClass_sub W (s+t) t
    rw [add_sub_cancel_right] at h
    exact eq_add_of_sub_eq h.symm)

theorem localTop_surjective {W : X.Opens} (hW : IsAffineOpen W) :
    Function.Surjective (localTop (p := p) W) := by
  intro y
  have terms := CycleQ2AffineExteriorComparison.term_acyclic p 3 hW
  obtain ⟨a,ha,hy⟩ := CycleQ2AcyclicSectionRepresentatives.surjective
    (freeOpen W) DR 0 terms 3 y
  refine ⟨coefficients W 3 (freeOpenSections _ W a),?_⟩
  have hr : representative W (coefficients W 3 (freeOpenSections _ W a)) = a := by
    change (freeOpenSections _ W).symm
      ((coefficients W 3).symm (coefficients W 3 (freeOpenSections _ W a))) = a
    rw [AddEquiv.symm_apply_apply,AddEquiv.symm_apply_apply]
  change CycleQ2KInjectiveSections.closedClass _ DR 3 _ _ = y
  simpa only [hr] using hy

theorem differential_two : DR.d 2 3 =
    (termIso 2).hom ≫ differential p 3 2 ≫ (termIso 3).inv := by
  simpa only [relativeDeRham,CochainComplex.of_d] using
    (relativeDeRham p 3).extend_d_eq (ComplexShape.embeddingUpIntGE 0)
      (Int.zero_add 2) (Int.zero_add 3)

theorem coefficients_differential_two (W : X.Opens) (s : Sections (DR.X 2) W) :
    coefficients W 3 ((DR.d 2 3).hom.app (op W) s) =
      (differential p 3 2).hom.app (op W) (coefficients W 2 s) := by
  have hd : DR.d 2 3 ≫ (termIso 3).hom = (termIso 2).hom ≫ differential p 3 2 := by
    rw [differential_two]
    simp only [Category.assoc,Iso.inv_hom_id_assoc]
  exact ConcreteCategory.congr_hom (congrArg (fun a => a.hom.app (op W)) hd) s

theorem localTop_eq_zero_iff {W : X.Opens} (hW : IsAffineOpen W)
    (s : Sections (F 3) W) : localTop W s = 0 ↔
      ∃ t : Sections (F 2) W, (differential p 3 2).hom.app (op W) t = s := by
  have terms := CycleQ2AffineExteriorComparison.term_acyclic p 3 hW
  change CycleQ2KInjectiveSections.closedClass _ DR 3 _ _ = 0 ↔ _
  rw [CycleQ2AcyclicSectionRepresentatives.zero_iff (freeOpen W) DR 0 terms]
  constructor
  · rintro ⟨a,ha⟩
    refine ⟨coefficients W 2 (freeOpenSections _ W a),?_⟩
    rw [← coefficients_differential_two,freeOpenSections_postcomp,ha,representative_sections]
    exact (coefficients W 3).apply_symm_apply s
  · rintro ⟨t,ht⟩
    refine ⟨(freeOpenSections _ W).symm ((coefficients W 2).symm t),?_⟩
    apply (freeOpenSections _ W).injective
    apply (coefficients W 3).injective
    rw [representative_sections,← freeOpenSections_postcomp,coefficients_differential_two]
    simpa only [AddEquiv.apply_symm_apply] using ht

theorem representative_restrict {U V : X.Opens} (h : U ≤ V)
    (s : Sections (F 3) V) : representative U (res _ h s) = freeOpenMap h ≫ representative V s := by
  apply (freeOpenSections _ U).injective
  rw [representative_sections,freeOpenSections_naturality,representative_sections]
  apply (coefficients U 3).injective
  rw [AddEquiv.apply_symm_apply,coefficients_restrict,AddEquiv.apply_symm_apply]

theorem localTop_restrict {U V : X.Opens} (h : U ≤ V) (s : Sections (F 3) V) :
    CycleQ2DerivedCoverTop.restriction T 3 h (localTop V s) = localTop U (res _ h s) := by
  change _ = CycleQ2KInjectiveSections.closedClass _ DR 3 (representative U (res _ h s)) _
  rw [representative_restrict]
  exact (CycleQ2KInjectiveSections.closedClass_precomp (freeOpen V) DR (freeOpenMap h) 3
    (representative V s) (representative_closed V s)).symm

private abbrev E := DerivedCategory.singleFunctor (AbSheaf (show TopCat from X)) 0

private theorem top_closed : (termIso (p := p) 3).inv ≫ DR.d 3 4 = 0 := by
  apply CategoryTheory.Sheaf.hom_ext
  apply NatTrans.ext
  intro W
  apply ConcreteCategory.hom_ext
  intro s
  change _ = 0
  exact term_above W.unop 4 (by decide) _

/-- Inclusion of the intrinsic top sheaf, with its original differential. -/
def topInclusion : E.obj (F 3) ⟶ T⟦(3 : ℤ)⟧ :=
  CycleQ2KInjectiveSections.closedClass (F 3) DR 3 (termIso 3).inv top_closed

private def topPostAt (P : AbSheaf (show TopCat from X)) (n : ℕ) (m : ℤ)
    (h : 3 + (n : ℤ) = m) : Ext P (F 3) n →+ (E.obj P ⟶ T⟦m⟧) where
  toFun a := a.hom.comp topInclusion h
  map_zero' := by simp only [Ext.zero_hom,ShiftedHom.zero_comp]
  map_add' a b := by simp only [Ext.add_hom,ShiftedHom.add_comp]

def topPost (n : ℕ) (W : X.Opens) : (F 3).H' n W →+ H T (3 + (n : ℤ)) W :=
  topPostAt (freeOpen W) n (3 + (n : ℤ)) rfl

private theorem representative_eq_post (W : X.Opens) (s : Sections (F 3) W) :
    representative W s = (freeOpenSections (F 3) W).symm s ≫ (termIso 3).inv := by
  apply (freeOpenSections _ W).injective
  rw [representative_sections,← freeOpenSections_postcomp,AddEquiv.apply_symm_apply]
  rfl

theorem topPost_section (W : X.Opens) (s : Sections (F 3) W) :
    topPost 0 W (sectionExtZero W s) = localTop W s := by
  change (Ext.mk₀ ((freeOpenSections (F 3) W).symm s)).hom.comp topInclusion _ = _
  rw [Ext.mk₀_hom,ShiftedHom.mk₀_comp]
  symm
  change CycleQ2KInjectiveSections.closedClass (freeOpen W) DR 3 (representative W s) _ = _
  rw [representative_eq_post]
  exact CycleQ2KInjectiveSections.closedClass_precomp (F 3) DR
    ((freeOpenSections (F 3) W).symm s) 3 (termIso 3).inv top_closed

private theorem topPostAt_precomp {P Q : AbSheaf (show TopCat from X)}
    (f : Q ⟶ P) (n : ℕ) (m : ℤ) (h : 3 + (n : ℤ) = m)
    (a : Ext P (F 3) n) :
    topPostAt Q n m h ((Ext.mk₀ f).comp a (zero_add n)) = E.map f ≫ topPostAt P n m h a := by
  change ((Ext.mk₀ f).comp a (zero_add n)).hom.comp topInclusion h = _
  rw [Ext.comp_hom,Ext.mk₀_hom]
  simpa only [ShiftedHom.mk₀_comp] using
    (ShiftedHom.comp_assoc (ShiftedHom.mk₀ (0 : ℤ) rfl (E.map f)) a.hom topInclusion
      (add_zero _) h (by simpa only [add_zero] using h))

theorem topPost_restrict (n : ℕ) {U V : X.Opens} (h : U ≤ V) (a : (F 3).H' n V) :
    topPost n U (((F 3).cohomologyPresheaf n).map (homOfLE h).op a) =
      CycleQ2DerivedCoverTop.restriction T (3 + (n : ℤ)) h (topPost n V a) :=
  topPostAt_precomp (freeOpenMap h) n (3 + (n : ℤ)) rfl a

private theorem topPostAt_boundary {S : ShortComplex (AbSheaf (show TopCat from X))}
    (hS : S.ShortExact) {n n' : ℕ} (hn : 1 + n = n')
    (m : ℤ) (hm : 3 + (n : ℤ) = m) (a : Ext S.X₁ (F 3) n) :
    topPostAt S.X₃ n' (m+1) (by omega) (hS.extClass.comp a hn) =
      CycleQ2DerivedSourceBoundary.connecting hS T m (topPostAt S.X₁ n m hm a) := by
  change (hS.extClass.comp a hn).hom.comp topInclusion _ = _
  rw [Ext.comp_hom,hS.extClass_hom]
  calc
    (hS.singleδ.comp a.hom _).comp topInclusion _ =
        hS.singleδ.comp (a.hom.comp topInclusion hm) rfl :=
      ShiftedHom.comp_assoc hS.singleδ a.hom topInclusion (by omega) hm (by omega)
    _ = _ := by
      rw [ShiftedHom.comp,shiftFunctorAdd'_eq_shiftFunctorAdd]
      rfl

private theorem topPost_delta_zero
    (S : (Opens.grothendieckTopology X).MayerVietorisSquare) (a : (F 3).H' 0 S.X₁) :
    topPost 1 S.X₄ (S.δ (F 3) 0 1 rfl a) =
      CycleQ2DerivedCoverTop.delta T S 3 (topPost 0 S.X₁ a) :=
  topPostAt_boundary S.shortComplex_shortExact rfl 3 rfl a

private theorem topPost_delta_one
    (S : (Opens.grothendieckTopology X).MayerVietorisSquare) (a : (F 3).H' 1 S.X₁) :
    topPost 2 S.X₄ (S.δ (F 3) 1 2 rfl a) =
      CycleQ2DerivedCoverTop.delta T S 4 (topPost 1 S.X₁ a) :=
  topPostAt_boundary S.shortComplex_shortExact rfl 4 rfl a

private theorem topPost_delta_two
    (S : (Opens.grothendieckTopology X).MayerVietorisSquare) (a : (F 3).H' 2 S.X₁) :
    topPost 3 S.X₄ (S.δ (F 3) 2 3 rfl a) =
      CycleQ2DerivedCoverTop.delta T S 5 (topPost 2 S.X₁ a) :=
  topPostAt_boundary S.shortComplex_shortExact rfl 5 rfl a

/-- The top edge map commutes with the original three source
Mayer--Vietoris boundaries, without a chosen scalar normalization. -/
theorem topPost_four (U V W Z : X.Opens)
    (s : Sections (F 3) (CycleQ2FourOpenH3.QuadOpen U V W Z)) :
    topPost 3 (((U ⊔ V) ⊔ W) ⊔ Z) (CycleQ2FourOpenH3.connecting (F 3) U V W Z s) =
      CycleQ2DerivedCoverTop.fourConnecting T 3 U V W Z
        (localTop (CycleQ2FourOpenH3.QuadOpen U V W Z) s) := by
  let S := CycleQ2FourOpenH3.outerSquare U V W Z
  let R := CycleQ2ThreeOpenCechH2.outerSquare (U ⊓ Z) (V ⊓ Z) (W ⊓ Z)
  let Q := Opens.mayerVietorisSquare ((U ⊓ Z) ⊓ (W ⊓ Z)) ((V ⊓ Z) ⊓ (W ⊓ Z))
  change topPost 3 S.X₄
    (S.δ (F 3) 2 3 rfl (R.δ (F 3) 1 2 rfl (Q.δ (F 3) 0 1 rfl
      ((CycleQ2GeometricConeCech.HZero.sectionsEquiv (F 3) Q.X₁).symm s)))) = _
  rw [topPost_delta_two,topPost_delta_one,topPost_delta_zero,
    ← CycleQ2ThreeOpenInjectiveComparison.sectionExtZero_eq_hzero,topPost_section]
  rfl

end CycleQ2IntrinsicThreefoldTop

#print axioms CycleQ2IntrinsicThreefoldTop.localTop_eq_zero_iff
#print axioms CycleQ2IntrinsicThreefoldTop.topPost_four

namespace CycleQ2IntrinsicFourOpenTop

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open CycleQ2InjectiveCech (AbSheaf Sections)
open CycleQ2IntrinsicDeRhamSheaves (sheafForms differential)
open CycleQ2IntrinsicThreefoldTop
  (target localTop localTop_restrict localTop_surjective localTop_eq_zero_iff affine_above topPost)
open CycleQ2HodgeTwistCoordinates (NativeTopFaces nativeTopBoundary)
open CycleQ2HodgeTwistTopDerived
  (FaceAcyclic full_quad nativeQuadEquiv nativeTripleEquiv nativeQuad_boundary
    union_cover nativeTopConnecting nativeTopConnecting_boundary nativeTopConnecting_surjective)
open CycleQ2DerivedCoverTop (H)
open CycleQ2CechTwoToDerived (app app_res)
open CycleQ2ThreeOpenCechH2 (TripleOpen)
open CycleQ2FourOpenH3 (QuadOpen)
open CycleQ2GeometricSheafLocalIso (res)

variable {k : Type} [Field k] [CharZero k] {X : Scheme.{0}}
  {p : X ⟶ Spec (CommRingCat.of k)} [SmoothOfRelativeDimension 3 p]
  {U : Fin 4 → X.Opens} (hcover : (⨆ i, U i) = ⊤)

local instance : HasExt.{1} (AbSheaf (show TopCat from X)) := HasExt.standard _
local instance : HasDerivedCategory.{1} (AbSheaf (show TopCat from X)) :=
  HasDerivedCategory.standard _

local notation "F" => sheafForms p 3
local notation "T" => target p
private abbrev Quad := QuadOpen (U 0) (U 1) (U 2) (U 3)
private abbrev Torus := Finset.univ.inf U

/-- The actual canonical class followed by the actual intrinsic
top-term inclusion, with the original ordered source boundaries. -/
def connectingNative : Sections (F 3) (Torus (U := U)) →+ H T 6 ⊤ :=
  (topPost 3 ⊤).comp (nativeTopConnecting (F 3) U hcover)

theorem connectingNative_eq_four (s : Sections (F 3) (Torus (U := U))) :
    connectingNative hcover s =
      (CycleQ2DerivedCoverTop.restrictionEquiv T 6 (union_cover U hcover))
        (CycleQ2DerivedCoverTop.fourConnecting T 3 (U 0) (U 1) (U 2) (U 3)
          (localTop (Quad (U := U)) (nativeQuadEquiv (F 3) U s))) := by
  have he : (eqToHom (union_cover U hcover).symm :
      (⊤ : X.Opens) ⟶ ((U 0 ⊔ U 1) ⊔ U 2) ⊔ U 3) =
        homOfLE (union_cover U hcover).ge := Subsingleton.elim _ _
  change topPost 3 ⊤ (((F 3).cohomologyPresheaf 3).map
    (eqToHom (union_cover U hcover).symm).op
      (CycleQ2FourOpenH3.connecting (F 3) (U 0) (U 1) (U 2) (U 3)
        (nativeQuadEquiv (F 3) U s))) = _
  rw [he,CycleQ2IntrinsicThreefoldTop.topPost_restrict,CycleQ2IntrinsicThreefoldTop.topPost_four]
  rfl

theorem connectingNative_boundary (c : NativeTopFaces (F := F 3) (U := U)) :
    connectingNative hcover (nativeTopBoundary c) = 0 := by
  change topPost 3 ⊤ (nativeTopConnecting (F 3) U hcover (nativeTopBoundary c)) = 0
  rw [nativeTopConnecting_boundary,map_zero]

variable (hface : ∀ (S : Finset (Fin 4)), S.Nonempty → IsAffineOpen (S.inf U))

include hface in
private theorem vertex_affine (i : Fin 4) : IsAffineOpen (U i) := by
  simpa only [Finset.inf_singleton] using hface {i} (by simp)

include hface in
private theorem pair_affine (i j : Fin 4) : IsAffineOpen (U i ⊓ U j) := by
  simpa only [Finset.inf_insert,Finset.inf_singleton] using hface {i,j} (by simp)

include hface in
private theorem triple_affine (i j l : Fin 4) : IsAffineOpen (TripleOpen (U i) (U j) (U l)) := by
  simpa only [TripleOpen,Finset.inf_insert,Finset.inf_singleton,
    inf_assoc,inf_left_comm,inf_comm,inf_idem] using hface {i,j,l} (by simp)

include hface in
private theorem quad_affine : IsAffineOpen (Quad (U := U)) := by
  rw [← full_quad U]
  exact hface _ (by simp)

include hface in
theorem forms_face_acyclic (n : ℕ) : FaceAcyclic (F n) U := fun S hS m =>
  CycleQ2AffineExteriorComparison.forms_acyclic p 3 (hface S hS) n m

include hface in
private theorem four_surjective : Function.Surjective
    (CycleQ2DerivedCoverTop.fourConnecting T 3 (U 0) (U 1) (U 2) (U 3)) :=
  CycleQ2DerivedCoverTop.four_surjective T 3 _ _ _ _
    (affine_above (vertex_affine hface 0) 6 (by decide))
    (affine_above (vertex_affine hface 1) 6 (by decide))
    (affine_above (vertex_affine hface 2) 6 (by decide))
    (affine_above (vertex_affine hface 3) 6 (by decide))
    (affine_above (pair_affine hface 0 1) 5 (by decide))
    (affine_above (pair_affine hface 0 2) 5 (by decide))
    (affine_above (pair_affine hface 1 2) 5 (by decide))
    (affine_above (pair_affine hface 0 3) 5 (by decide))
    (affine_above (pair_affine hface 1 3) 5 (by decide))
    (affine_above (pair_affine hface 2 3) 5 (by decide))
    (affine_above (triple_affine hface 0 1 2) 4 (by decide))
    (affine_above (triple_affine hface 0 1 3) 4 (by decide))
    (affine_above (triple_affine hface 0 2 3) 4 (by decide))
    (affine_above (triple_affine hface 1 2 3) 4 (by decide))

include hface in
theorem connectingNative_surjective : Function.Surjective (connectingNative (p := p) hcover) := by
  intro y
  obtain ⟨z,hz⟩ := (CycleQ2DerivedCoverTop.restrictionEquiv T 6 (union_cover U hcover)).surjective y
  obtain ⟨a,ha⟩ := four_surjective (p := p) hface z
  obtain ⟨s,hs⟩ := localTop_surjective (p := p) (quad_affine hface) a
  refine ⟨(nativeQuadEquiv (F 3) U).symm s,?_⟩
  rw [connectingNative_eq_four,AddEquiv.apply_symm_apply,hs,ha,hz]

include hcover hface in
theorem topPost_surjective : Function.Surjective (topPost (p := p) 3 (⊤ : X.Opens)) := by
  intro y
  obtain ⟨s,hs⟩ := connectingNative_surjective hcover hface y
  exact ⟨nativeTopConnecting (F 3) U hcover s,hs⟩

include hface in
private theorem four_eq_zero_iff (s : H T 3 (Quad (U := U))) :
    CycleQ2DerivedCoverTop.fourConnecting T 3 (U 0) (U 1) (U 2) (U 3) s = 0 ↔
    ∃ a, CycleQ2DerivedCoverTop.fourBoundary T 3 (U 0) (U 1) (U 2) (U 3) a = s :=
  CycleQ2DerivedCoverTop.four_eq_zero_iff T 3 _ _ _ _
    (affine_above (vertex_affine hface 0) 5 (by decide))
    (affine_above (vertex_affine hface 1) 5 (by decide))
    (affine_above (vertex_affine hface 2) 5 (by decide))
    (affine_above (vertex_affine hface 3) 5 (by decide))
    (affine_above (pair_affine hface 0 1) 4 (by decide))
    (affine_above (pair_affine hface 0 2) 4 (by decide))
    (affine_above (pair_affine hface 1 2) 4 (by decide))
    (affine_above (pair_affine hface 0 3) 4 (by decide))
    (affine_above (pair_affine hface 1 3) 4 (by decide))
    (affine_above (pair_affine hface 2 3) 4 (by decide)) s

private def faceClasses (c : NativeTopFaces (F := F 3) (U := U)) :
    CycleQ2DerivedCoverTop.TripleClasses T 3 (U 0) (U 1) (U 2) (U 3) :=
  (localTop _ (nativeTripleEquiv (F 3) U c).1,
    localTop _ (nativeTripleEquiv (F 3) U c).2.1,
    localTop _ (nativeTripleEquiv (F 3) U c).2.2.1,
    localTop _ (nativeTripleEquiv (F 3) U c).2.2.2)

include hface in
private theorem faceClasses_surjective : Function.Surjective (faceClasses (p := p) (U := U)) := by
  rintro ⟨a,b,c,d⟩
  obtain ⟨a,rfl⟩ := localTop_surjective (triple_affine hface 0 1 2) a
  obtain ⟨b,rfl⟩ := localTop_surjective (triple_affine hface 0 1 3) b
  obtain ⟨c,rfl⟩ := localTop_surjective (triple_affine hface 0 2 3) c
  obtain ⟨d,rfl⟩ := localTop_surjective (triple_affine hface 1 2 3) d
  refine ⟨(nativeTripleEquiv (F 3) U).symm (a,b,c,d),?_⟩
  simp only [faceClasses,AddEquiv.apply_symm_apply]

private theorem localTop_native_boundary (c : NativeTopFaces (F := F 3) (U := U)) :
    localTop (Quad (U := U)) (nativeQuadEquiv (F 3) U (nativeTopBoundary c)) =
      CycleQ2DerivedCoverTop.fourBoundary T 3 (U 0) (U 1) (U 2) (U 3) (faceClasses c) := by
  rw [nativeQuad_boundary]
  change localTop (Quad (U := U))
      (res _ _ (nativeTripleEquiv (F 3) U c).2.2.2 -
        res _ _ (nativeTripleEquiv (F 3) U c).2.2.1 +
        res _ _ (nativeTripleEquiv (F 3) U c).2.1 -
        res _ _ (nativeTripleEquiv (F 3) U c).1) = _
  simp only [map_sub,map_add,← localTop_restrict] <;> rfl

theorem nativeQuad_differential (s : Sections (F 2) (Torus (U := U))) :
    nativeQuadEquiv (F 3) U (app (differential p 3 2) _ s) =
      app (differential p 3 2) (Quad (U := U)) (nativeQuadEquiv (F 2) U s) :=
  (app_res (differential p 3 2) (full_quad U).ge s).symm

include hface in
theorem connectingNative_differential (s : Sections (F 2) (Torus (U := U))) :
    connectingNative hcover (app (differential p 3 2) _ s) = 0 := by
  rw [connectingNative_eq_four,nativeQuad_differential]
  have hz := (localTop_eq_zero_iff (quad_affine hface)
    (app (differential p 3 2) _ (nativeQuadEquiv (F 2) U s))).mpr
      ⟨nativeQuadEquiv (F 2) U s,rfl⟩
  rw [hz,map_zero,map_zero]

/-- The kernel uses only the original four-face boundary and the
actual intrinsic two-form differential on the original torus. -/
include hface in
theorem connectingNative_eq_zero_iff (s : Sections (F 3) (Torus (U := U))) :
    connectingNative hcover s = 0 ↔
      ∃ c : NativeTopFaces (F := F 3) (U := U),
        ∃ η : Sections (F 2) (Torus (U := U)),
          nativeTopBoundary c - app (differential p 3 2) _ η = s := by
  constructor
  · intro hs
    rw [connectingNative_eq_four] at hs
    have hfour : CycleQ2DerivedCoverTop.fourConnecting T 3 (U 0) (U 1) (U 2) (U 3)
        (localTop (Quad (U := U)) (nativeQuadEquiv (F 3) U s)) = 0 := by
      apply (CycleQ2DerivedCoverTop.restrictionEquiv T 6 (union_cover U hcover)).injective
      simpa only [map_zero] using hs
    obtain ⟨a,ha⟩ := (four_eq_zero_iff hface _).mp hfour
    obtain ⟨c,hc⟩ := faceClasses_surjective hface a
    have he : localTop (Quad (U := U))
        (nativeQuadEquiv (F 3) U (s - nativeTopBoundary c)) = 0 := by
      rw [map_sub,map_sub,localTop_native_boundary,hc,ha,sub_self]
    obtain ⟨η,hη⟩ := (localTop_eq_zero_iff (quad_affine hface) _).mp he
    let t := (nativeQuadEquiv (F 2) U).symm η
    have ht : app (differential p 3 2) _ t = s - nativeTopBoundary c := by
      apply (nativeQuadEquiv (F 3) U).injective
      rw [nativeQuad_differential]
      change app (differential p 3 2) _
        (nativeQuadEquiv (F 2) U ((nativeQuadEquiv (F 2) U).symm η)) = _
      rw [AddEquiv.apply_symm_apply]
      exact hη
    refine ⟨c,-t,?_⟩
    rw [map_neg,ht]
    abel
  · rintro ⟨c,η,rfl⟩
    rw [map_sub,connectingNative_boundary,connectingNative_differential hcover hface,sub_self]

section SectionTrace

variable {A : Type*} [AddCommGroup A] (τ : Sections (F 3) (Torus (U := U)) →+ A)
  (hδ : ∀ c : NativeTopFaces (F := F 3) (U := U), τ (nativeTopBoundary c) = 0)
  (hd : ∀ s : Sections (F 2) (Torus (U := U)), τ (app (differential p 3 2) _ s) = 0)

/-- The native torus functional descends once it kills the two
explicit kinds of boundary; no global volume frame is presumed. -/
def traceOfSections : H T 6 ⊤ →+ A :=
  AddMonoidHom.liftOfSurjective (connectingNative hcover)
    (connectingNative_surjective hcover hface)
    ⟨τ,fun s hs => by
      obtain ⟨c,η,rfl⟩ := (connectingNative_eq_zero_iff hcover hface s).mp hs
      rw [map_sub,hδ,hd,sub_self]⟩

theorem traceOfSections_connecting (s : Sections (F 3) (Torus (U := U))) :
    traceOfSections hcover hface τ hδ hd (connectingNative hcover s) = τ s := by
  simp [traceOfSections]

include hcover hface hδ hd in
theorem connectingNative_ne_zero (s : Sections (F 3) (Torus (U := U))) (hs : τ s ≠ 0) :
    connectingNative hcover s ≠ 0 := by
  intro hz
  apply hs
  rw [← traceOfSections_connecting hcover hface τ hδ hd,hz,map_zero]

/-- The same local functional also gives the canonical H³ trace,
through the original native four-open cohomology map. -/
def canonicalTraceOfSections : (F 3).H' 3 ⊤ →+ A :=
  AddMonoidHom.liftOfSurjective (nativeTopConnecting (F 3) U hcover)
    (nativeTopConnecting_surjective (F 3) U hcover (forms_face_acyclic hface 3))
    ⟨τ,fun s hs => by
      obtain ⟨c,rfl⟩ := (CycleQ2HodgeTwistTopDerived.nativeTopConnecting_eq_zero_iff
        (F 3) U hcover (forms_face_acyclic hface 3) s).mp hs
      exact hδ c⟩

theorem canonicalTraceOfSections_connecting (s : Sections (F 3) (Torus (U := U))) :
    canonicalTraceOfSections hcover hface τ hδ (nativeTopConnecting (F 3) U hcover s) = τ s := by
  simp [canonicalTraceOfSections]

theorem traceOfSections_topPost (a : (F 3).H' 3 ⊤) :
    traceOfSections hcover hface τ hδ hd (topPost 3 ⊤ a) =
      canonicalTraceOfSections hcover hface τ hδ a := by
  obtain ⟨s,rfl⟩ := nativeTopConnecting_surjective (F 3) U hcover (forms_face_acyclic hface 3) a
  rw [canonicalTraceOfSections_connecting]
  exact traceOfSections_connecting hcover hface τ hδ hd s

end SectionTrace

section Trace

variable {A : Type*} [AddCommGroup A] (τ : (F 3).H' 3 ⊤ →+ A)
  (hτ : ∀ s : Sections (F 2) (Torus (U := U)),
    τ (nativeTopConnecting (F 3) U hcover (app (differential p 3 2) _ s)) = 0)

/-- A canonical trace that kills the genuine exterior differential
descends to actual global derived de Rham cohomology. -/
def derivedTrace : H T 6 ⊤ →+ A :=
  AddMonoidHom.liftOfSurjective (connectingNative hcover)
    (connectingNative_surjective hcover hface)
    ⟨τ.comp (nativeTopConnecting (F 3) U hcover),fun s hs => by
      obtain ⟨c,η,rfl⟩ := (connectingNative_eq_zero_iff hcover hface s).mp hs
      change τ (nativeTopConnecting (F 3) U hcover
        (nativeTopBoundary c - app (differential p 3 2) _ η)) = 0
      rw [map_sub,nativeTopConnecting_boundary,map_sub,map_zero,hτ,sub_self]⟩

theorem derivedTrace_connecting (s : Sections (F 3) (Torus (U := U))) :
    derivedTrace hcover hface τ hτ (connectingNative hcover s) =
      τ (nativeTopConnecting (F 3) U hcover s) := by
  simp [derivedTrace]

/-- The descended trace agrees with the given canonical trace on every
actual H³ class, under the actual top-term inclusion. -/
theorem derivedTrace_topPost (a : (F 3).H' 3 ⊤) :
    derivedTrace hcover hface τ hτ (topPost 3 ⊤ a) = τ a := by
  obtain ⟨s,rfl⟩ := nativeTopConnecting_surjective (F 3) U hcover (forms_face_acyclic hface 3) a
  exact derivedTrace_connecting hcover hface τ hτ s

include hcover hface hτ in
theorem topPost_injective (hτi : Function.Injective τ) :
    Function.Injective (topPost (p := p) 3 (⊤ : X.Opens)) := by
  intro a b hab
  apply hτi
  rw [← derivedTrace_topPost hcover hface τ hτ,← derivedTrace_topPost hcover hface τ hτ,hab]

end Trace

end CycleQ2IntrinsicFourOpenTop

#print axioms CycleQ2IntrinsicFourOpenTop.connectingNative_surjective
#print axioms CycleQ2IntrinsicFourOpenTop.connectingNative_eq_zero_iff
#print axioms CycleQ2IntrinsicFourOpenTop.derivedTrace_topPost

/-!
# The actual generic top trace on both coefficient models

The coefficient-one homogeneous section is the same section used in
the explicit torus calculation.  Both of its boundary cancellations
are now applied to the intrinsic four-open comparison, and the result
is carried back through the original generic scheme isomorphism.
-/

namespace CycleQ2GenericHodgeCanonicalTrace

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open CycleQ2MonicGenericAmbientChart (K genericCoeff_vertex)
open CycleQ2MonicGenericSmooth (coeff explicit_projective_smooth)
open CycleQ2GeometricHodgeThreefold (threefold toBase coordinateOpen coordinateOpens_cover)
open CycleQ2IntrinsicDeRhamSheaves (sheafForms relativeDeRhamInt)
open CycleQ2IntrinsicThreefoldTop (target topPost)
open CycleQ2IntrinsicFourOpenTop
  (connectingNative traceOfSections traceOfSections_connecting
    canonicalTraceOfSections canonicalTraceOfSections_connecting traceOfSections_topPost)
open CycleQ2InjectiveCech (AbSheaf Sections)
open CycleQ2DerivedCoverTop (H)
open CycleQ2NativeWeightedCover (ambientToField)
open CycleQ2GenericHodgeDeRham (globalDeRhamEquiv)

local instance : SmoothOfRelativeDimension 3 (toBase coeff) := explicit_projective_smooth
local instance : SmoothOfRelativeDimension 3 ambientToField := CycleQ2NativeGenericSmooth.ambient_smooth
local instance (Z : Scheme.{0}) : HasExt.{1} (AbSheaf (show TopCat from Z)) := HasExt.standard _
local instance (Z : Scheme.{0}) : HasDerivedCategory.{1} (AbSheaf (show TopCat from Z)) :=
  HasDerivedCategory.standard _

private theorem cover : (⨆ i : Fin 4, coordinateOpen coeff i) = ⊤ :=
  coordinateOpens_cover coeff (by rw [genericCoeff_vertex]; exact isUnit_one)

private theorem affine_faces (S : Finset (Fin 4)) (hS : S.Nonempty) :
    IsAffineOpen (S.inf (coordinateOpen coeff)) := by
  obtain ⟨i,hi⟩ := hS
  exact CycleQ2HodgeCubicIntrinsicForms.face_affine coeff i S hi

/-- The generic torus functional on actual global degree-six intrinsic
de Rham cohomology, with both original differentials accounted for. -/
def deRhamTrace : H (target (toBase coeff)) 6 ⊤ →+ K :=
  traceOfSections cover affine_faces torusSectionTrace
    torusSectionTrace_boundary torusSectionTrace_differential

/-- The same coefficient functional on actual canonical cohomology. -/
def canonicalTrace : (sheafForms (toBase coeff) 3 3).H' 3 ⊤ →+ K :=
  canonicalTraceOfSections cover affine_faces torusSectionTrace torusSectionTrace_boundary

theorem deRhamTrace_connecting
    (s : Sections (sheafForms (toBase coeff) 3 3)
      (Finset.univ.inf (coordinateOpen coeff))) :
    deRhamTrace (connectingNative cover s) = torusSectionTrace s :=
  traceOfSections_connecting cover affine_faces torusSectionTrace
    torusSectionTrace_boundary torusSectionTrace_differential s

theorem canonicalTrace_connecting
    (s : Sections (sheafForms (toBase coeff) 3 3)
      (Finset.univ.inf (coordinateOpen coeff))) :
    canonicalTrace (CycleQ2HodgeTwistTopDerived.nativeTopConnecting
      (sheafForms (toBase coeff) 3 3) (coordinateOpen coeff) cover s) = torusSectionTrace s :=
  canonicalTraceOfSections_connecting cover affine_faces torusSectionTrace
    torusSectionTrace_boundary s

theorem deRhamTrace_topPost (a : (sheafForms (toBase coeff) 3 3).H' 3 ⊤) :
    deRhamTrace (topPost 3 ⊤ a) = canonicalTrace a :=
  traceOfSections_topPost cover affine_faces torusSectionTrace
    torusSectionTrace_boundary torusSectionTrace_differential a

/-- The actual normalized homogeneous section followed by the actual
ordered connecting maps and the intrinsic top-term inclusion. -/
def normalizedDeRhamClass (a : K) : H (target (toBase coeff)) 6 ⊤ :=
  connectingNative cover (normalizedSection a)

theorem deRhamTrace_normalizedDeRhamClass (a : K) :
    deRhamTrace (normalizedDeRhamClass a) = a := by
  rw [normalizedDeRhamClass,deRhamTrace_connecting,torusSectionTrace_normalizedSection]

theorem normalizedDeRhamClass_ne_zero {a : K} (ha : a ≠ 0) :
    normalizedDeRhamClass a ≠ 0 := by
  intro hz
  apply ha
  rw [← deRhamTrace_normalizedDeRhamClass a,hz,map_zero]

theorem deRhamTrace_eq_zero_iff (a : H (target (toBase coeff)) 6 ⊤) :
    deRhamTrace a = 0 ↔ a = 0 := by
  constructor
  · obtain ⟨s,rfl⟩ := CycleQ2IntrinsicFourOpenTop.connectingNative_surjective cover affine_faces a
    intro hs
    rw [deRhamTrace_connecting] at hs
    obtain ⟨c,rfl⟩ := (torusSectionTrace_eq_zero_iff s).mp hs
    exact CycleQ2IntrinsicFourOpenTop.connectingNative_boundary cover c
  · rintro rfl
    exact map_zero deRhamTrace

theorem deRhamTrace_bijective : Function.Bijective deRhamTrace := by
  constructor
  · intro a b hab
    apply sub_eq_zero.mp
    apply (deRhamTrace_eq_zero_iff (a-b)).mp
    rw [map_sub,hab,sub_self]
  · intro a
    exact ⟨normalizedDeRhamClass a,deRhamTrace_normalizedDeRhamClass a⟩

/-- The actual top de Rham group is identified by the original
homogeneous trace, with no abstractly chosen nonzero generator. -/
def deRhamTraceEquiv : H (target (toBase coeff)) 6 ⊤ ≃+ K :=
  AddEquiv.ofBijective deRhamTrace deRhamTrace_bijective

theorem canonicalTrace_eq_zero_iff (a : (sheafForms (toBase coeff) 3 3).H' 3 ⊤) :
    canonicalTrace a = 0 ↔ a = 0 := by
  constructor
  · obtain ⟨s,rfl⟩ := CycleQ2HodgeTwistTopDerived.nativeTopConnecting_surjective
      (sheafForms (toBase coeff) 3 3) (coordinateOpen coeff) cover
      (CycleQ2IntrinsicFourOpenTop.forms_face_acyclic affine_faces 3) a
    intro hs
    rw [canonicalTrace_connecting] at hs
    obtain ⟨c,rfl⟩ := (torusSectionTrace_eq_zero_iff s).mp hs
    exact CycleQ2HodgeTwistTopDerived.nativeTopConnecting_boundary
      (sheafForms (toBase coeff) 3 3) (coordinateOpen coeff) cover c
  · rintro rfl
    exact map_zero canonicalTrace

theorem canonicalTrace_injective : Function.Injective canonicalTrace := by
  intro a b hab
  apply sub_eq_zero.mp
  apply (canonicalTrace_eq_zero_iff (a-b)).mp
  rw [map_sub,hab,sub_self]

theorem topPost_bijective : Function.Bijective
    (topPost (p := toBase coeff) 3 (⊤ : (threefold coeff).Opens)) := by
  refine ⟨?_,CycleQ2IntrinsicFourOpenTop.topPost_surjective cover affine_faces⟩
  intro a b hab
  apply canonicalTrace_injective
  rw [← deRhamTrace_topPost,← deRhamTrace_topPost,hab]

/-- The canonical class maps to de Rham cohomology by the actual
top-term inclusion, and that very map is an isomorphism in top degree. -/
def topPostEquiv : (sheafForms (toBase coeff) 3 3).H' 3 ⊤ ≃+
    H (target (toBase coeff)) 6 ⊤ :=
  AddEquiv.ofBijective (topPost 3 ⊤) topPost_bijective

/-- The trace on the original generic ambient scheme is transported
through its coefficient-preserving isomorphism, in every de Rham degree. -/
def originalDeRhamTrace : H (target ambientToField) 6 ⊤ →+ K :=
  deRhamTrace.comp (globalDeRhamEquiv 6).toAddMonoidHom

def normalizedOriginalDeRhamClass (a : K) : H (target ambientToField) 6 ⊤ :=
  (globalDeRhamEquiv 6).symm (normalizedDeRhamClass a)

theorem originalDeRhamTrace_normalized (a : K) :
    originalDeRhamTrace (normalizedOriginalDeRhamClass a) = a := by
  change deRhamTrace ((globalDeRhamEquiv 6)
    ((globalDeRhamEquiv 6).symm (normalizedDeRhamClass a))) = a
  rw [AddEquiv.apply_symm_apply,deRhamTrace_normalizedDeRhamClass]

theorem normalizedOriginalDeRhamClass_ne_zero {a : K} (ha : a ≠ 0) :
    normalizedOriginalDeRhamClass a ≠ 0 := by
  intro hz
  apply ha
  rw [← originalDeRhamTrace_normalized a,hz,map_zero]

theorem normalizedOriginalDeRhamClass_one_ne_zero : normalizedOriginalDeRhamClass 1 ≠ 0 :=
  normalizedOriginalDeRhamClass_ne_zero one_ne_zero

/-- The same normalized trace identifies the original generic
ambient top de Rham group through its actual scheme isomorphism. -/
def originalDeRhamTraceEquiv : H (target ambientToField) 6 ⊤ ≃+ K :=
  (globalDeRhamEquiv 6).trans deRhamTraceEquiv

theorem originalDeRhamTrace_eq_zero_iff (a : H (target ambientToField) 6 ⊤) :
    originalDeRhamTrace a = 0 ↔ a = 0 :=
  originalDeRhamTraceEquiv.map_eq_zero_iff

end CycleQ2GenericHodgeCanonicalTrace

#print axioms CycleQ2GenericHodgeCanonicalTrace.deRhamTrace_topPost
#print axioms CycleQ2GenericHodgeCanonicalTrace.topPost_bijective
#print axioms CycleQ2GenericHodgeCanonicalTrace.originalDeRhamTrace_eq_zero_iff
#print axioms CycleQ2GenericHodgeCanonicalTrace.originalDeRhamTrace_normalized
#print axioms CycleQ2GenericHodgeCanonicalTrace.normalizedOriginalDeRhamClass_one_ne_zero
