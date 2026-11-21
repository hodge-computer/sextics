import Proposal.GeometricSmoothSurfaceGysin
import Proposal.GeometricLiteralThreefoldResidueContraction

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
