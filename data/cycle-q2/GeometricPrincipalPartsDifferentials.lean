import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Algebra.Regular.Basic
import Mathlib.Tactic.Ring
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Tactic.LinearCombination
import Proposal.GeometricUniversalWeightedDeRham
import Proposal.GeometricMonicGenericSupport
import Proposal.GeometricLocalizedDerivations
import Mathlib.RingTheory.Derivation.Lie
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Module
import Mathlib.Tactic.Positivity

/-! The normal de Rham calculation on the quotient of the double localization by its two single localizations.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false

noncomputable section

section
namespace CycleQ2CechDenominatorTorsion

variable {R A B T : Type*} [CommRing R] [CommRing A] [CommRing B] [CommRing T]
    [Algebra R A] [Algebra R B] [Algebra R T]

noncomputable def fromFirst (x y : R) [IsLocalization.Away x A]
    [IsLocalization.Away (x*y) T] : A →ₐ[R] T :=
  ⟨IsLocalization.Away.awayToAwayRight x y, IsLocalization.Away.awayToAwayRight_eq x y⟩

noncomputable def fromSecond (x y : R) [IsLocalization.Away y B]
    [IsLocalization.Away (x*y) T] : B →ₐ[R] T :=
  ⟨IsLocalization.Away.awayToAwayLeft y x, IsLocalization.Away.awayToAwayLeft_eq y x⟩

/-- Boundaries on the intersection of the two principal opens are sums
of restrictions of the two singly localized rings. -/
noncomputable def boundaries (A B T : Type*) [CommRing A] [CommRing B] [CommRing T]
    [Algebra R A] [Algebra R B] [Algebra R T] (x y : R) [IsLocalization.Away x A]
    [IsLocalization.Away y B] [IsLocalization.Away (x*y) T] : Submodule R T :=
  LinearMap.range (fromFirst (A := A) x y).toLinearMap ⊔
  LinearMap.range (fromSecond (B := B) x y).toLinearMap

private theorem clears_other {a t : R} [IsLocalization.Away t B] (j : B →ₐ[R] T)
    (z : T) (n : ℕ) (c : R) (hz : z * ((algebraMap R T a) * (algebraMap R T t)) ^ n = algebraMap R T c) :
    a ^ n • z ∈ LinearMap.range j.toLinearMap := by
  apply LinearMap.mem_range.mpr
  refine ⟨algebraMap R B c * (IsLocalization.Away.invSelf t)^n, ?_⟩
  have hu : IsUnit (algebraMap R T t ^ n) := by
    simpa only [AlgHom.commutes, map_pow] using (IsLocalization.Away.algebraMap_pow_isUnit (S := B) t n).map j
  apply hu.mul_right_cancel
  have hi := congrArg j (IsLocalization.Away.mul_invSelf (S := B) t)
  simp only [map_mul, AlgHom.commutes, map_one] at hi
  change j _ * _ = _ * _
  rw [map_mul, map_pow, j.commutes, Algebra.smul_def, map_pow]
  calc
    algebraMap R T c * j (IsLocalization.Away.invSelf t) ^ n * algebraMap R T t ^ n =
        algebraMap R T c * (algebraMap R T t * j (IsLocalization.Away.invSelf t)) ^ n := by rw [mul_pow]; ac_rfl
    _ = algebraMap R T c := by rw [hi, one_pow, mul_one]
    _ = algebraMap R T a ^ n * z * algebraMap R T t ^ n := by rw [← hz, mul_pow]; ac_rfl

/-- Every class in `R[1/(xy)] / (R[1/x] + R[1/y])` is killed by a power
of `x` and by the same power of `y`. No regularity assumption is needed. -/
theorem powers_kill (x y : R) [IsLocalization.Away x A] [IsLocalization.Away y B]
    [IsLocalization.Away (x*y) T] (v : T ⧸ boundaries A B T x y) :
    ∃ n : ℕ, x ^ n • v = 0 ∧ y ^ n • v = 0 := by
  obtain ⟨z,rfl⟩ := (boundaries A B T x y).mkQ_surjective v
  obtain ⟨n,c,h⟩ := IsLocalization.Away.surj (x*y) z
  rw [map_mul] at h
  refine ⟨n, ?_, ?_⟩
  · rw [← LinearMap.map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact le_sup_right (a := LinearMap.range (fromFirst (A := A) x y).toLinearMap)
      (clears_other (fromSecond (B := B) x y) z n c h)
  · rw [← LinearMap.map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact le_sup_left (b := LinearMap.range (fromSecond (B := B) x y).toLinearMap)
      (clears_other (fromFirst (A := A) x y) z n c (by rwa [mul_comm (algebraMap R T y) _]))

end CycleQ2CechDenominatorTorsion
end

section
namespace CycleQ2RegularPairCech
open CycleQ2CechDenominatorTorsion
variable {R A B T : Type*} [CommRing R] [CommRing A] [CommRing B] [CommRing T]
    [Algebra R A] [Algebra R B] [Algebra R T]

/-- Injectivity at the initial term of the two-principal-open Čech row. -/
theorem first_injective {x : R} [IsLocalization.Away x A] (hx : IsLeftRegular x) :
    Function.Injective (algebraMap R A) := by
  intro a b hab
  obtain ⟨n,hn⟩ := IsLocalization.Away.exists_of_eq x hab
  exact (hx.pow n) hn

private theorem restriction_injective (x y : R) [IsLocalization.Away y B]
    [IsLocalization.Away (x*y) T] (hx : IsLeftRegular x) :
    Function.Injective (fromSecond (B := B) (T := T) x y) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro b hb
  obtain ⟨m,a,ha⟩ := IsLocalization.Away.surj y b
  have hm := congrArg (fromSecond (B := B) (T := T) x y) ha
  simp only [map_mul, map_pow, AlgHom.commutes, hb, zero_mul] at hm
  obtain ⟨k,hk⟩ := IsLocalization.Away.exists_of_eq (x*y) (hm.symm.trans (map_zero _).symm)
  have hya : y ^ k * a = 0 := (hx.pow k) (by simpa [mul_pow, mul_assoc] using hk)
  have hab : algebraMap R B a = 0 := by
    apply (IsLocalization.Away.algebraMap_pow_isUnit (S := B) y k).mul_left_cancel
    simpa [map_pow, map_mul] using congrArg (algebraMap R B) hya
  apply (IsLocalization.Away.algebraMap_pow_isUnit (S := B) y m).mul_right_cancel
  simp [ha, hab]

/-- Descent of two compatible fractions. `sat` is saturation of all powers
 of `(x)` by `y`, as follows from regularity of `y` modulo `(x)`. -/
theorem glue (x y : R) [IsLocalization.Away x A] [IsLocalization.Away y B]
    [IsLocalization.Away (x*y) T] (hx : IsLeftRegular x)
    (sat : ∀ n m : ℕ, ∀ a : R, x^n ∣ y^m*a → x^n ∣ a)
    (u : A) (v : B) (huv : fromFirst (T := T) x y u = fromSecond x y v) :
    ∃ a : R, algebraMap R A a = u ∧ algebraMap R B a = v := by
  obtain ⟨n,a,ha⟩ := IsLocalization.Away.surj x u
  obtain ⟨m,b,hb⟩ := IsLocalization.Away.surj y v
  have hat := congrArg (fromFirst (A := A) (T := T) x y) ha
  have hbt := congrArg (fromSecond (B := B) (T := T) x y) hb
  simp only [map_mul, map_pow, AlgHom.commutes, huv] at hat hbt
  have hc : algebraMap R T (y^m*a) = algebraMap R T (x^n*b) := by
    rw [map_mul, map_mul, map_pow, map_pow, ← hat, ← hbt]; ring
  obtain ⟨k,hk⟩ := IsLocalization.Away.exists_of_eq (x*y) hc
  have hh : y^(k+m)*a = x^n*(y^k*b) := (hx.pow k) (by
    rw [mul_pow] at hk
    simpa only [pow_add] using (show x^k*(y^k*y^m*a) = x^k*(x^n*(y^k*b)) from by
      convert hk using 1 <;> ring))
  obtain ⟨c,hc⟩ := sat n (k+m) a ⟨_,hh⟩
  have hc₁ : algebraMap R A c = u := by
    apply (IsLocalization.Away.algebraMap_pow_isUnit (S := A) x n).mul_right_cancel
    rw [ha,hc,map_mul,map_pow,mul_comm]
  exact ⟨c,hc₁,restriction_injective x y (T := T) hx (by rw [AlgHom.commutes, ← huv, ← hc₁, AlgHom.commutes])⟩

end CycleQ2RegularPairCech
end

section
namespace CycleQ2RegularPairDivisibility

variable {R : Type*} [CommRing R] {x y : R}

private theorem dvd_of_pow_mul (hy : ∀ a : R, x ∣ y * a → x ∣ a)
    (m : ℕ) (a : R) (ha : x ∣ y ^ m * a) : x ∣ a := by
  induction m with
  | zero => simpa using ha
  | succ m ih =>
    apply ih
    apply hy
    simpa only [pow_succ', mul_assoc] using ha

/-- All powers of the second element of a regular pair are nonzerodivisors
modulo every power of the first element. -/
theorem pow_dvd_of_dvd_pow_mul (hx : IsLeftRegular x) (hy : ∀ a : R, x ∣ y * a → x ∣ a)
    (n m : ℕ) (a : R) (ha : x ^ n ∣ y ^ m * a) : x ^ n ∣ a := by
  induction n generalizing a with
  | zero => simp
  | succ n ih =>
    obtain ⟨b, hb⟩ := ha
    obtain ⟨c, rfl⟩ := dvd_of_pow_mul hy m a ⟨x^n * b, by simpa [pow_succ', mul_assoc] using hb⟩
    have hc : y ^ m * c = x ^ n * b := by
      apply hx
      calc x * (y^m * c) = y^m * (x*c) := by ac_rfl
           _ = x * (x^n * b) := by simpa [pow_succ', mul_assoc] using hb
    obtain ⟨d, rfl⟩ := ih c ⟨b, hc⟩
    exact ⟨d, by simp only [pow_succ', mul_assoc]⟩

/-- Convert regularity in the usual principal quotient to the divisibility criterion. -/
theorem dvd_of_regular_mod (hy : IsLeftRegular (Ideal.Quotient.mk (Ideal.span {x}) y))
    (a : R) (ha : x ∣ y * a) : x ∣ a := by
  apply Ideal.mem_span_singleton.mp
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  apply hy
  dsimp only
  rw [mul_zero, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mem_span_singleton.mpr ha

end CycleQ2RegularPairDivisibility
end

section
namespace CycleQ2RegularPairDifferentiation
variable {k A : Type*} [Field k] [CharZero k] [CommRing A] [Algebra k A]

private theorem reduce_kernel (D : Derivation k A A) {x : A} (hx : D x = 1) (n : ℕ)
    (hs : ∀ a : A, x ^ (n+1) * a = 0 → x^n*a = 0) (a : A) (ha : x*a = 0) : a = 0 := by
  induction n with
  | zero => simpa using hs a (by simpa using ha)
  | succ n ih =>
    apply ih
    intro b hb
    have hd := congrArg D hb
    simp only [map_zero, D.leibniz, D.leibniz_pow, hx, smul_eq_mul, mul_one,
      Nat.add_sub_cancel, nsmul_eq_mul, Nat.cast_succ] at hd
    have hk : x^(n+2)*D b = 0 := by
      linear_combination x * hd - (n+1 : A) * hb
    have hz := hs (D b) hk
    have hu : IsUnit (n+1 : A) := by
      have h : IsUnit ((n+1 : ℕ) : k) := isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr n.succ_ne_zero)
      simpa using h.map (algebraMap k A)
    apply hu.mul_left_cancel
    linear_combination hd - hz

/-- A function admitting a coordinate derivation on a Noetherian algebra in
characteristic zero is a nonzerodivisor. -/
theorem isLeftRegular_of_derivative_one [IsNoetherianRing A]
    (D : Derivation k A A) {x : A} (hx : D x = 1) : IsLeftRegular x := by
  let T : ℕ →o Submodule A A :=
    { toFun := fun n => LinearMap.ker (LinearMap.mulLeft A (x^n))
      monotone' := fun n m h a ha => by
        change x^n*a = 0 at ha
        change x^m*a = 0
        obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le h
        rw [pow_add, mul_right_comm, ha, zero_mul] }
  obtain ⟨n,hn⟩ := monotone_stabilizes_iff_noetherian.mpr (inferInstance : IsNoetherian A A) T
  have hs (a : A) (ha : x^(n+1)*a = 0) : x^n*a = 0 := by
    change a ∈ T n
    rw [hn (n+1) (Nat.le_succ _)]
    exact ha
  intro a b hab
  apply sub_eq_zero.mp
  apply reduce_kernel D hx n hs
  rw [mul_sub, sub_eq_zero]
  exact hab

end CycleQ2RegularPairDifferentiation
end

namespace CycleQ2NormalExteriorCech
open Module KaehlerDifferential CycleQ2WeightedCoordinateExterior CycleQ2ExactFrameThreeDeRham
open CycleQ2RelativeAffineOverlap CycleQ2CechDenominatorTorsion
open CycleQ2RegularPairCech CycleQ2RegularPairDivisibility

section Coordinates
variable {K A B : Type} [CommRing K] [CommRing A] [CommRing B] [Algebra K A] [Algebra K B]
  {n : ℕ} (b : Basis (Fin n) A Ω[A⁄K]) (c : Basis (Fin n) B Ω[B⁄K])

/-- Coefficients of an exterior form restrict by the ring map whenever
 the two coordinate frames are related by ordinary Kähler pullback. -/
theorem pull_coordinates (φ : A →ₐ[K] B) (h : ∀ i, onePullback φ (b i) = c i)
    (p : ℕ) (ω : Form K A p) (s : Set.powersetCard (Fin n) p) :
    (c.exteriorPower p).equivFun (exteriorPullback φ p ω) s =
      φ ((b.exteriorPower p).equivFun ω s) := by
  classical
  have hb (t : Set.powersetCard (Fin n) p) :
      exteriorPullback φ p ((b.exteriorPower p) t) = (c.exteriorPower p) t := by
    simp only [exteriorPower.basis_apply, exteriorPower.ιMulti_family, exteriorPullback,
      CycleQ2GeometricExteriorSheaf.exteriorMap_wedge]
    congr 1
    funext j; exact h _
  let a := (b.exteriorPower p).equivFun ω
  have he : ω = (b.exteriorPower p).equivFun.symm a :=
    ((b.exteriorPower p).equivFun.symm_apply_apply ω).symm
  change (c.exteriorPower p).equivFun (exteriorPullback φ p ω) s = φ (a s)
  have hr : exteriorPullback φ p ω = (c.exteriorPower p).equivFun.symm (fun t => φ (a t)) := by
    rw [he, (b.exteriorPower p).equivFun_symm_apply, (c.exteriorPower p).equivFun_symm_apply]
    simp only [map_sum, map_smulₛₗ, hb]; rfl
  rw [hr, LinearEquiv.apply_symm_apply]
end Coordinates

variable {K R U V T : Type} [CommRing K] [CommRing R] [CommRing U] [CommRing V] [CommRing T]
    [Algebra K R] [Algebra K U] [Algebra K V] [Algebra K T]
    [Algebra R U] [Algebra R V] [Algebra R T]
    [IsScalarTower K R U] [IsScalarTower K R V] [IsScalarTower K R T]
    (x y : R) [IsLocalization.Away x U] [IsLocalization.Away y V]
    [IsLocalization.Away (x*y) T]

/-- Every compatible pair of exterior forms on the two principal opens is
 the restriction of a unique form on the original exact affine chart. -/
theorem exterior_row {n : ℕ} (b : Basis (Fin n) R Ω[R⁄K]) (u : Fin n → R)
    (hu : ∀ i, b i = D K R (u i)) (hx : IsLeftRegular x)
    (hy : IsLeftRegular (Ideal.Quotient.mk (Ideal.span {x}) y)) (p : ℕ) :
    Function.Injective (exteriorPullback (IsScalarTower.toAlgHom K R U) p) ∧
      ∀ (α : Form K U p) (β : Form K V p),
        exteriorPullback ((fromFirst (A := U) (T := T) x y).restrictScalars K) p α =
          exteriorPullback ((fromSecond (B := V) (T := T) x y).restrictScalars K) p β →
        ∃ ω : Form K R p, exteriorPullback (IsScalarTower.toAlgHom K R U) p ω = α ∧
          exteriorPullback (IsScalarTower.toAlgHom K R V) p ω = β := by
  classical
  let : Algebra.FormallyEtale R U := Algebra.FormallyEtale.of_isLocalization (.powers x)
  let : Algebra.FormallyEtale R V := Algebra.FormallyEtale.of_isLocalization (.powers y)
  let : Algebra.FormallyEtale R T := Algebra.FormallyEtale.of_isLocalization (.powers (x*y))
  let bu : Basis (Fin n) U Ω[U⁄K] := baseChangeFrame b
  let bv : Basis (Fin n) V Ω[V⁄K] := baseChangeFrame b
  let bt : Basis (Fin n) T Ω[T⁄K] := baseChangeFrame b
  let ru := IsScalarTower.toAlgHom K R U
  let rv := IsScalarTower.toAlgHom K R V
  let ut := (fromFirst (A := U) (T := T) x y).restrictScalars K
  let vt := (fromSecond (B := V) (T := T) x y).restrictScalars K
  have hru (i : Fin n) : onePullback ru (b i) = bu i := by
    rw [hu,onePullback_d]; exact (baseChangeFrame_apply b u hu i).symm
  have hrv (i : Fin n) : onePullback rv (b i) = bv i := by
    rw [hu,onePullback_d]; exact (baseChangeFrame_apply b u hu i).symm
  have hut (i : Fin n) : onePullback ut (bu i) = bt i := by
    rw [show bu i = D K U (algebraMap R U (u i)) from baseChangeFrame_apply b u hu i,
      onePullback_d,show ut (algebraMap R U (u i)) = algebraMap R T (u i) from
        (fromFirst (A := U) (T := T) x y).commutes (u i)]
    exact (baseChangeFrame_apply b u hu i).symm
  have hvt (i : Fin n) : onePullback vt (bv i) = bt i := by
    rw [show bv i = D K V (algebraMap R V (u i)) from baseChangeFrame_apply b u hu i,
      onePullback_d,show vt (algebraMap R V (u i)) = algebraMap R T (u i) from
        (fromSecond (B := V) (T := T) x y).commutes (u i)]
    exact (baseChangeFrame_apply b u hu i).symm
  constructor
  · intro a c h
    apply (b.exteriorPower p).equivFun.injective
    funext s
    apply first_injective (A := U) hx
    exact (pull_coordinates b bu ru hru p a s).symm.trans
      ((congrArg (fun t => (bu.exteriorPower p).equivFun t s) h).trans
        (pull_coordinates b bu ru hru p c s))
  · intro α β h
    have hc (s : Set.powersetCard (Fin n) p) :
        ut ((bu.exteriorPower p).equivFun α s) = vt ((bv.exteriorPower p).equivFun β s) :=
      (pull_coordinates bu bt ut hut p α s).symm.trans
        ((congrArg (fun t => (bt.exteriorPower p).equivFun t s) h).trans
          (pull_coordinates bv bt vt hvt p β s))
    choose c hc₁ hc₂ using fun s => glue x y hx (pow_dvd_of_dvd_pow_mul hx (dvd_of_regular_mod hy))
      ((bu.exteriorPower p).equivFun α s) ((bv.exteriorPower p).equivFun β s) (hc s)
    refine ⟨(b.exteriorPower p).equivFun.symm c, ?_, ?_⟩
    · apply (bu.exteriorPower p).equivFun.injective; funext s
      rw [pull_coordinates b bu ru hru, LinearEquiv.apply_symm_apply]; exact hc₁ s
    · apply (bv.exteriorPower p).equivFun.injective; funext s
      rw [pull_coordinates b bv rv hrv, LinearEquiv.apply_symm_apply]; exact hc₂ s

section Adapted
variable {k S : Type} [Field k] [CharZero k] [CommRing S] [Algebra k S] [IsNoetherianRing S]

/-- Any two distinct coordinates of an exact affine frame are a weak
 regular sequence, including after passage to the first coordinate quotient. -/
theorem exact_frame_regular {n : ℕ} (b : Basis (Fin n) S Ω[S⁄k]) (u : Fin n → S)
    (hu : ∀ i, b i = D k S (u i)) (i j : Fin n) (hij : i ≠ j) :
    IsLeftRegular (u i) ∧ IsLeftRegular (Ideal.Quotient.mk (Ideal.span {u i}) (u j)) := by
  let δ (t : Fin n) := (b.coord t).compDer (D k S)
  have hδ (t s : Fin n) : δ t (u s) = if s=t then 1 else 0 := by
    change b.repr (D k S (u s)) t = _
    rw [← hu]; exact b.repr_self_apply s t
  refine ⟨CycleQ2RegularPairDifferentiation.isLeftRegular_of_derivative_one (δ i) (by simp [hδ]), ?_⟩
  let I : Ideal S := Ideal.span {u i}
  let π := Ideal.Quotient.mkₐ k I
  have hstable (s : S) (hs : π s = 0) : π (δ j s) = 0 := by
    obtain ⟨t,rfl⟩ := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hs)
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    apply Ideal.mem_span_singleton.mpr
    exact ⟨δ j t, by simp [Derivation.leibniz, hδ, hij, smul_eq_mul]⟩
  let δ' := Derivation.liftOfSurjective (Ideal.Quotient.mkₐ_surjective k I) hstable
  apply CycleQ2RegularPairDifferentiation.isLeftRegular_of_derivative_one δ'
  change Derivation.liftOfSurjective _ hstable (π (u j)) = 1
  rw [Derivation.liftOfSurjective_apply]; simp [hδ]

variable {A B C : Type} [CommRing A] [CommRing B] [CommRing C]
    [Algebra k A] [Algebra k B] [Algebra k C] [Algebra S A] [Algebra S B] [Algebra S C]
    [IsScalarTower k S A] [IsScalarTower k S B] [IsScalarTower k S C]

end Adapted
end CycleQ2NormalExteriorCech

namespace CycleQ2FrameCurl
open Module KaehlerDifferential CycleQ2ArbitraryFrameDifferential
open CycleQ2ExactFrameFirstDifferential CycleQ2WeightedCoordinateExterior
open CycleQ2ExactFrameThreeDeRham (wedge)
open CycleQ2FrameExteriorIdentities CycleQ2CartanContraction
variable {K A : Type} [Field K] [CommRing A] [Algebra K A]
    {n : ℕ} (b : Basis (Fin n) A Ω[A⁄K])

/-- Evaluate a two-form in an ordered pair of coordinate directions. -/
def pair (i j : Fin n) : Form K A 2 →ₗ[A] A :=
  (b.coord j).comp (two (spatialDerivative b i))

private theorem contractions (i : Fin n) :
    one (spatialDerivative b i) = b.coord i :=
  (linearMapEquivDerivation K A).symm_apply_apply _

theorem pair_wedge (i j : Fin n) (a c : Ω[A⁄K]) :
    pair b i j (wedge a c) = b.coord i a * b.coord j c - b.coord i c * b.coord j a := by
  simp only [pair, LinearMap.comp_apply, two_wedge, contractions, map_sub, map_smul, smul_eq_mul]

/-- The mixed coefficient `i,j` of a first exterior derivative is the
 difference of the two cross-partials of the actual one-form coefficients. -/
theorem pair_onOne [CharZero K] (i j : Fin n) (ω : Ω[A⁄K]) :
    pair b i j (onOne b ω) =
      spatialDerivative b i (b.coord j ω) - spatialDerivative b j (b.coord i ω) := by
  rw [onOne_apply, map_sum]
  simp [pair_wedge, Finset.sum_sub_distrib, Finsupp.single_apply, mul_ite, ite_mul, partial_apply]

private abbrev oneIso := exteriorPower.oneEquiv A Ω[A⁄K]

private theorem oneIso_symm (v : Ω[A⁄K]) : oneIso.symm v = exteriorPower.ιMulti A 1 (fun _ => v) := by
  apply oneIso.injective
  rw [LinearEquiv.apply_symm_apply, exteriorPower.oneEquiv_ιMulti]

/-- Identify the Kähler first derivative with the map in the full, intrinsic
 de Rham complex of the framed chart. -/
theorem first_eq [CharZero K] (v : Ω[A⁄K]) : d b 1 (oneIso.symm v) = onOne b v := by
  nth_rw 1 [← b.sum_repr v]
  rw [map_sum, map_sum, onOne_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul, d_smul, oneIso_symm]
  have hb : d b 1 (exteriorPower.ιMulti A 1 (fun _ => b i)) = 0 :=
    d_coordinate_wedge b 1 (fun _ => i)
  rw [hb, smul_zero, add_zero, front_wedge]
  unfold wedge
  rfl

end CycleQ2FrameCurl

namespace CycleQ2NormalCechDerivation
open CycleQ2GeometricLocalizedDerivations

variable {A B C : Type} [CommRing A] [Algebra ℂ A]
  [CommRing B] [Algebra ℂ B] [Algebra A B] [IsScalarTower ℂ A B]
  [CommRing C] [Algebra ℂ C] [Algebra A C] [IsScalarTower ℂ A C]

omit [Algebra ℂ A] [IsScalarTower ℂ A B] in
/-- Uniqueness of the localized derivation, proved by differentiating
 a cleared denominator in an arbitrary localization. -/
theorem eq_zero_of_vanishes (M : Submonoid A) [IsLocalization M B]
    (D : Derivation ℂ B B) (h : ∀ a : A, D (algebraMap A B a) = 0) : D = 0 := by
  ext b
  obtain ⟨⟨a,s⟩,hs⟩ := IsLocalization.surj M b
  have he := congrArg D hs
  simp only [Derivation.leibniz, smul_eq_mul, h, mul_zero, zero_add] at he
  simpa using (IsLocalization.map_units B s).mul_left_cancel (he.trans (mul_zero _).symm)

/-- The canonical extensions of commuting coordinate derivatives commute. -/
theorem localizations_commute (M : Submonoid A) (B : Type) [CommRing B]
    [Algebra ℂ B] [Algebra A B] [IsScalarTower ℂ A B] [IsLocalization M B]
    (d e : Derivation ℂ A A) (h : ∀ a, d (e a) = e (d a)) (b : B) :
    localizedDerivation M B d (localizedDerivation M B e b) =
      localizedDerivation M B e (localizedDerivation M B d b) := by
  let δ := localizedDerivation M B d
  let ε := localizedDerivation M B e
  have hbr : ⁅δ,ε⁆ = 0 := by
    apply eq_zero_of_vanishes M
    intro a
    simp [Derivation.commutator_apply, δ, ε, localizedDerivation_algebraMap, h]
  exact sub_eq_zero.mp (show ⁅δ,ε⁆ b = 0 by rw [hbr]; rfl)

/-- Restriction between charts commutes with the quotient-rule extensions. -/
theorem localization_natural (M N : Submonoid A) [IsLocalization M B] [IsLocalization N C]
    (g : B →ₐ[A] C) (d : Derivation ℂ A A) (b : B) :
    localizedDerivation N C d (g b) = g (localizedDerivation M B d b) := by
  obtain ⟨⟨a,s⟩,hs⟩ := IsLocalization.surj M b
  have hgs := congrArg g hs
  simp only [map_mul, AlgHom.commutes] at hgs
  have h₁ := congrArg (localizedDerivation N C d) hgs
  have h₂ := congrArg (fun t => g (localizedDerivation M B d t)) hs
  simp only [Derivation.leibniz, smul_eq_mul, localizedDerivation_algebraMap,
    map_add, map_mul, AlgHom.commutes] at h₁ h₂
  have hu : IsUnit (algebraMap A C (s:A)) := by
    simpa only [AlgHom.commutes] using (IsLocalization.map_units B s).map g
  exact hu.mul_left_cancel (add_left_cancel (h₁.trans h₂.symm))

section Cech
open CycleQ2CechDenominatorTorsion
variable {R U V T : Type} [CommRing R] [CommRing U] [CommRing V] [CommRing T]
    [Algebra ℂ R] [Algebra ℂ U] [Algebra ℂ V] [Algebra ℂ T]
    [Algebra R U] [Algebra R V] [Algebra R T]
    [IsScalarTower ℂ R U] [IsScalarTower ℂ R V] [IsScalarTower ℂ R T]
    (x y : R) [IsLocalization.Away x U] [IsLocalization.Away y V]
    [IsLocalization.Away (x*y) T]

include x y in
private theorem preserves (d : Derivation ℂ R R) {t : T}
    (ht : t ∈ boundaries U V T x y) :
    localizedDerivation (.powers (x*y)) T d t ∈ boundaries U V T x y := by
  obtain ⟨a, ⟨u,rfl⟩, b, ⟨v,rfl⟩, rfl⟩ := Submodule.mem_sup.mp ht
  rw [map_add]
  apply Submodule.add_mem_sup
  · exact ⟨localizedDerivation (.powers x) U d u,
      (localization_natural (.powers x) (.powers (x*y)) (fromFirst x y) d u).symm⟩
  · exact ⟨localizedDerivation (.powers y) V d v,
      (localization_natural (.powers y) (.powers (x*y)) (fromSecond x y) d v).symm⟩

/-- The derivative on the actual top Čech quotient of the two principal opens. -/
def onParts (d : Derivation ℂ R R) : Module.End ℂ (T ⧸ boundaries U V T x y) :=
  let Q := (boundaries U V T x y).restrictScalars ℂ
  Q.mapQ Q (localizedDerivation (.powers (x*y)) T d).toLinearMap
    (by intro t ht; exact preserves x y d ht)

@[simp] theorem onParts_mk (d : Derivation ℂ R R) (t : T) :
    onParts (U := U) (V := V) x y d (Submodule.Quotient.mk t) =
      Submodule.Quotient.mk (localizedDerivation (.powers (x*y)) T d t) := rfl

/-- The commutator of a derivative with multiplication on the quotient
 is multiplication by the derivative of the scalar. -/
theorem onParts_smul (d : Derivation ℂ R R) (r : R) (z : T ⧸ boundaries U V T x y) :
    onParts x y d (r • z) = r • onParts x y d z + d r • z := by
  obtain ⟨t,rfl⟩ := (boundaries U V T x y).mkQ_surjective z
  change Submodule.Quotient.mk (localizedDerivation (.powers (x*y)) T d (r • t)) =
    (Submodule.Quotient.mk (r • localizedDerivation (.powers (x*y)) T d t + d r • t) : T ⧸ _)
  congr 1
  simp [Algebra.smul_def, Derivation.leibniz, localizedDerivation_algebraMap, mul_comm, add_comm]

/-- Commuting vector fields on the affine chart induce commuting operators
 on its actual top Čech quotient. -/
theorem onParts_commute (d e : Derivation ℂ R R) (h : ∀ r, d (e r) = e (d r))
    (z : T ⧸ boundaries U V T x y) :
    onParts x y d (onParts x y e z) = onParts x y e (onParts x y d z) := by
  obtain ⟨t,rfl⟩ := (boundaries U V T x y).mkQ_surjective z
  exact congrArg Submodule.Quotient.mk (localizations_commute (.powers (x*y)) T d e h t)

end Cech
end CycleQ2NormalCechDerivation

namespace CycleQ2SupportedWeyl
variable {V : Type*} [AddCommGroup V] [Module ℚ V]

theorem power_rule (X D : Module.End ℚ V) (h : ∀ m, D (X m) = m + X (D m))
    (m : V) (n : ℕ) : D ((X ^ (n+1)) m) = ((n+1 : ℕ) : ℚ) • (X ^ n) m + (X ^ (n+1)) (D m) := by
  induction n with
  | zero => simp [h]
  | succ n ih =>
    rw [pow_succ' X (n+1), Module.End.mul_apply, h, ih, map_add, map_smul,
      pow_succ' X n, Module.End.mul_apply, Module.End.mul_apply, Nat.cast_add_one]
    module

/-- For an invariant subspace, differentiation is injective on the quotient
 whenever the coordinate multiplier is locally nilpotent there. -/
theorem derivative_injective_mod (X D : Module.End ℚ V) (S : Submodule ℚ V)
    (h : ∀ m, D (X m) = m + X (D m))
    (hX : ∀ m ∈ S, X m ∈ S) (hD : ∀ m ∈ S, D m ∈ S)
    (m : V) (hm : D m ∈ S) {n : ℕ} (hn : (X ^ n) m ∈ S) : m ∈ S := by
  have hDm (k : ℕ) : (X ^ k) (D m) ∈ S := by
    induction k with
    | zero => simpa using hm
    | succ k ih => rw [pow_succ', Module.End.mul_apply]; exact hX _ ih
  induction n with
  | zero => simpa using hn
  | succ n ih =>
    have hstep := S.sub_mem (hD _ hn) (hDm (n+1))
    rw [power_rule X D h m n, add_sub_cancel_right] at hstep
    exact ih ((S.smul_mem_iff (by positivity : ((n+1 : ℕ) : ℚ) ≠ 0)).mp hstep)

/-- In particular no horizontal section can be supported on the coordinate. -/
theorem derivative_injective (X D : Module.End ℚ V) (h : ∀ m, D (X m) = m + X (D m))
    (hX : ∀ m, ∃ n : ℕ, (X ^ n) m = 0) : Function.Injective D := by
  rw [← LinearMap.ker_eq_bot]; apply le_antisymm _ bot_le
  intro m hm
  obtain ⟨n,hn⟩ := hX m
  apply derivative_injective_mod X D ⊥ h (by simp) (by simp) m hm (n := n)
  exact hn

/-- The degree-one normal de Rham complex of a module supported where both
 coordinates vanish is exact for commuting coordinate derivatives. -/
theorem closed_one_form_exact (X Y Dx Dy : Module.End ℚ V)
    (hxx : ∀ m, Dx (X m) = m + X (Dx m))
    (hyy : ∀ m, Dy (Y m) = m + Y (Dy m))
    (hxy : ∀ m, Y (Dx m) = Dx (Y m)) (hdd : ∀ m, Dy (Dx m) = Dx (Dy m))
    (hnx : ∀ m, ∃ n : ℕ, (X ^ n) m = 0) (hny : ∀ m, ∃ n : ℕ, (Y ^ n) m = 0)
    (p q : V) (hc : Dy p = Dx q) : ∃ f, Dx f = p ∧ Dy f = q := by
  obtain ⟨n,hn⟩ := hny p
  have hy : ∀ m ∈ LinearMap.range Dx, Y m ∈ LinearMap.range Dx := by
    rintro _ ⟨a,rfl⟩; exact ⟨Y a, (hxy a).symm⟩
  have hd : ∀ m ∈ LinearMap.range Dx, Dy m ∈ LinearMap.range Dx := by
    rintro _ ⟨a,rfl⟩; exact ⟨Dy a, (hdd a).symm⟩
  obtain ⟨f,hf⟩ := derivative_injective_mod Y Dy (LinearMap.range Dx) hyy hy hd p
    ⟨q,hc.symm⟩ (hn ▸ (LinearMap.range Dx).zero_mem)
  refine ⟨f,hf,derivative_injective X Dx hxx hnx ?_⟩
  rw [← hdd, hf, hc]

/-- Include all tangential components of an ambient one-form. Commuting
 any further coordinate derivative with the first one determines its
 component from closedness and the normal primitive. -/
theorem ambient_one_form_exact {ι : Type*} (x y : ι) (X Y : Module.End ℚ V)
    (D : ι → Module.End ℚ V) (hxx : ∀ m, D x (X m) = m + X (D x m))
    (hyy : ∀ m, D y (Y m) = m + Y (D y m))
    (hxy : ∀ m, Y (D x m) = D x (Y m))
    (hdd : ∀ i m, D i (D x m) = D x (D i m))
    (hnx : ∀ m, ∃ n : ℕ, (X ^ n) m = 0) (hny : ∀ m, ∃ n : ℕ, (Y ^ n) m = 0)
    (p : ι → V) (hc : ∀ i, D i (p x) = D x (p i)) : ∃ f, ∀ i, D i f = p i := by
  obtain ⟨f,hf,_⟩ := closed_one_form_exact X Y (D x) (D y) hxx hyy hxy (hdd y)
    hnx hny (p x) (p y) (hc y)
  exact ⟨f, fun i => derivative_injective X (D x) hxx hnx
    (by rw [← hdd, hf, hc])⟩

end CycleQ2SupportedWeyl

namespace CycleQ2NormalCechExact
open CycleQ2CechDenominatorTorsion CycleQ2NormalCechDerivation CycleQ2SupportedWeyl

variable {R U V T : Type} [CommRing R] [CommRing U] [CommRing V] [CommRing T]
    [Algebra ℂ R] [Algebra ℂ U] [Algebra ℂ V] [Algebra ℂ T]
    [Algebra R U] [Algebra R V] [Algebra R T]
    [IsScalarTower ℂ R U] [IsScalarTower ℂ R V] [IsScalarTower ℂ R T]
    (x y : R) [IsLocalization.Away x U] [IsLocalization.Away y V]
    [IsLocalization.Away (x*y) T]

/-- On the top Čech row, a horizontal function vanishes and every closed
 tuple of one-form coefficients has a primitive. The derivations and their
 three coordinate values are taken in the original algebra, before localization. -/
theorem actual_chart_low_degrees {ι : Type*} (a b : ι) (D : ι → Derivation ℂ R R)
    (hxx : D a x = 1) (hyy : D b y = 1) (hxy : D a y = 0)
    (hcomm : ∀ i r, D i (D a r) = D a (D i r)) :
    Function.Injective (onParts (U := U) (V := V) (T := T) x y (D a)) ∧
    ∀ p : ι → T ⧸ boundaries U V T x y,
      (∀ i, onParts x y (D i) (p a) = onParts x y (D a) (p i)) →
        ∃ f, ∀ i, onParts x y (D i) f = p i := by
  let Q := T ⧸ boundaries U V T x y
  let : Module ℚ Q := Module.compHom Q (algebraMap ℚ ℂ)
  let : IsScalarTower ℚ ℂ Q := IsScalarTower.of_compHom ℚ ℂ Q
  let d (i : ι) : Module.End ℚ Q := (onParts x y (D i)).restrictScalars ℚ
  let s (r : R) : Module.End ℚ Q := (Algebra.lsmul ℂ ℂ Q r).restrictScalars ℚ
  have spow (r : R) (z : Q) (n : ℕ) : (s r ^ n) z = r^n • z := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', Module.End.mul_apply, ih, pow_succ' r]
      change r • (r ^ n • z) = (r * r ^ n) • z
      exact (mul_smul r (r ^ n) z).symm
  have nx (z : Q) : ∃ n : ℕ, (s x ^ n) z = 0 := by
    obtain ⟨n,h,_⟩ := powers_kill x y z; exact ⟨n,(spow x z n).trans h⟩
  have ny (z : Q) : ∃ n : ℕ, (s y ^ n) z = 0 := by
    obtain ⟨n,_,h⟩ := powers_kill x y z; exact ⟨n,(spow y z n).trans h⟩
  have hx (z : Q) : d a (s x z) = z + s x (d a z) := by
    change onParts x y (D a) (x • z) = z + x • onParts x y (D a) z
    rw [onParts_smul, hxx, one_smul, add_comm]
  have hy (z : Q) : d b (s y z) = z + s y (d b z) := by
    change onParts x y (D b) (y • z) = z + y • onParts x y (D b) z
    rw [onParts_smul, hyy, one_smul, add_comm]
  have hcross (z : Q) : s y (d a z) = d a (s y z) := by
    change y • onParts x y (D a) z = onParts x y (D a) (y • z)
    rw [onParts_smul, hxy, zero_smul, add_zero]
  exact ⟨derivative_injective _ _ hx nx, fun p hc =>
    ambient_one_form_exact a b (s x) (s y) d hx hy hcross
      (fun i z => onParts_commute x y (D i) (D a) (hcomm i) z) nx ny p hc⟩

end CycleQ2NormalCechExact

namespace CycleQ2NormalCechKahler
open Module KaehlerDifferential CycleQ2FrameCurl CycleQ2ExactFrameFirstDifferential
open CycleQ2CechDenominatorTorsion CycleQ2NormalCechDerivation CycleQ2NormalCechExact
open CycleQ2ArbitraryFrameDifferential CycleQ2GeometricLocalizedDerivations
variable {k R U V T : Type} [Field k] [CharZero k] [Algebra ℂ k]
    [CommRing R] [CommRing U] [CommRing V] [CommRing T]
    [Algebra ℂ R] [Algebra ℂ U] [Algebra ℂ V] [Algebra ℂ T]
    [Algebra R U] [Algebra R V] [Algebra R T] [Algebra k R] [Algebra k T]
    [IsScalarTower ℂ k R] [IsScalarTower ℂ k T] [IsScalarTower k R T]
    [IsScalarTower ℂ R U] [IsScalarTower ℂ R V] [IsScalarTower ℂ R T]
    {n : ℕ} (b : Basis (Fin n) R Ω[R⁄k])

/-- The original cotangent basis transported to a principal localization. -/
def localFrame (M : Submonoid R) [IsLocalization M T] : Basis (Fin n) T Ω[T⁄k] :=
  letI := Algebra.FormallyEtale.of_isLocalization (Rₘ := T) M
  (b.baseChange T).map (tensorKaehlerEquivOfFormallyEtale k R T)

omit [CharZero k] in
theorem direction_extends (M : Submonoid R) [IsLocalization M T] (i : Fin n) :
    (spatialDerivative (localFrame (T := T) b M) i).restrictScalars ℂ =
      localizedDerivation M T ((spatialDerivative b i).restrictScalars ℂ) := by
  apply sub_eq_zero.mp
  apply eq_zero_of_vanishes M
  intro r
  rw [Derivation.sub_apply, localizedDerivation_algebraMap, sub_eq_zero]
  let := Algebra.FormallyEtale.of_isLocalization (Rₘ := T) M
  change (b.baseChange T).repr ((tensorKaehlerEquivOfFormallyEtale k R T).symm
    (D k T (algebraMap R T r))) i = algebraMap R T (b.repr (D k R r) i)
  rw [tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap, Basis.baseChange_repr_tmul,
    Algebra.smul_def, mul_one]

/-- A one-form whose mixed coefficients of the genuine local exterior
 derivative come from the single opens has a primitive modulo those opens.
The primitive is a function in the actual doubly localized algebra. -/
theorem one_form_exact (u : Fin n → R) (hu : ∀ i, b i = D k R (u i))
    (a c : Fin n) (hac : a ≠ c)
    [IsLocalization.Away (u a) U] [IsLocalization.Away (u c) V]
    [IsLocalization.Away (u a * u c) T] (ω : Ω[T⁄k])
    (hω : let t := localFrame (T := T) b (Submonoid.powers (u a * u c));
      ∀ i, pair t i a (d t 1 ((exteriorPower.oneEquiv T Ω[T⁄k]).symm ω)) ∈ boundaries U V T (u a) (u c)) :
    ∃ f : T, ∀ i, (localFrame b (Submonoid.powers (u a * u c))).coord i (D k T f - ω) ∈
      boundaries U V T (u a) (u c) := by
  let M := Submonoid.powers (u a * u c)
  let t := localFrame (T := T) b M
  let δ (i : Fin n) := (spatialDerivative b i).restrictScalars ℂ
  let S := boundaries U V T (u a) (u c)
  have hδ (i : Fin n) (z : T) : localizedDerivation M T (δ i) z = spatialDerivative t i z :=
    DFunLike.congr_fun (direction_extends b M i).symm z
  have xx : δ a (u a) = 1 := by change spatialDerivative b a _ = 1; simp [partial_coordinate b u hu]
  have yy : δ c (u c) = 1 := by change spatialDerivative b c _ = 1; simp [partial_coordinate b u hu]
  have xy : δ a (u c) = 0 := by change spatialDerivative b a _ = 0; simp [partial_coordinate b u hu,hac.symm]
  have comm (i : Fin n) (r : R) : δ i (δ a r) = δ a (δ i r) := partials_commute b u hu i a r
  have closed (i : Fin n) := hω i
  change ∀ i, pair t i a (d t 1 ((exteriorPower.oneEquiv T Ω[T⁄k]).symm ω)) ∈ S at closed
  simp_rw [first_eq, pair_onOne] at closed
  let p (i : Fin n) : T ⧸ S := Submodule.Quotient.mk (t.coord i ω)
  obtain ⟨z,hz⟩ := (actual_chart_low_degrees (U := U) (V := V) (T := T) (u a) (u c) a c δ xx yy xy comm).2 p (by
    intro i
    apply (Submodule.Quotient.eq S).mpr
    change localizedDerivation M T (δ i) (t.coord a ω) - localizedDerivation M T (δ a) (t.coord i ω) ∈ S
    rw [hδ, hδ]; exact closed i)
  obtain ⟨f,rfl⟩ := Submodule.Quotient.mk_surjective S z
  refine ⟨f,fun i => ?_⟩
  have hz' := (Submodule.Quotient.eq S).mp (hz i)
  change localizedDerivation M T (δ i) f - t.coord i ω ∈ S at hz'
  rw [hδ] at hz'
  change t.coord i (D k T f - ω) ∈ S
  rw [map_sub]; exact hz'

/-- If the normal derivative of an actual function on the intersection is
 a boundary then that function already comes from the two single opens. -/
theorem function_is_boundary (u : Fin n → R) (hu : ∀ i, b i = D k R (u i))
    (a c : Fin n) (hac : a ≠ c)
    [IsLocalization.Away (u a) U] [IsLocalization.Away (u c) V]
    [IsLocalization.Away (u a * u c) T] (f : T)
    (hf : (localFrame b (Submonoid.powers (u a * u c))).coord a (D k T f) ∈ boundaries U V T (u a) (u c)) :
    f ∈ boundaries U V T (u a) (u c) := by
  let M := Submonoid.powers (u a * u c)
  let δ (i : Fin n) := (spatialDerivative b i).restrictScalars ℂ
  let S := boundaries U V T (u a) (u c)
  have xx : δ a (u a) = 1 := by change spatialDerivative b a _ = 1; simp [partial_coordinate b u hu]
  have yy : δ c (u c) = 1 := by change spatialDerivative b c _ = 1; simp [partial_coordinate b u hu]
  have xy : δ a (u c) = 0 := by change spatialDerivative b a _ = 0; simp [partial_coordinate b u hu,hac.symm]
  have comm (i : Fin n) (r : R) : δ i (δ a r) = δ a (δ i r) := partials_commute b u hu i a r
  apply (Submodule.Quotient.mk_eq_zero S).mp
  apply (actual_chart_low_degrees (U := U) (V := V) (T := T) (u a) (u c) a c δ xx yy xy comm).1
  rw [map_zero, onParts_mk, Submodule.Quotient.mk_eq_zero]
  have eq := DFunLike.congr_fun (direction_extends (T := T) b M a) f
  exact eq ▸ hf

end CycleQ2NormalCechKahler

namespace CycleQ2AffineZeroOneForms
open Module KaehlerDifferential CycleQ2ArbitraryFrameDifferential CycleQ2WeightedCoordinateExterior
open CycleQ2ExactFrameThreeDeRham CycleQ2AffineDeRhamFunctorial
variable {k A B : Type} [Field k] [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]

abbrev scalar := (exteriorPower.zeroEquiv A Ω[A⁄k]).symm
abbrev one := (exteriorPower.oneEquiv A Ω[A⁄k]).symm

theorem scalar_eq (a : A) : scalar (k := k) a = a • exteriorPower.ιMulti A 0 (fun j => Fin.elim0 j) := by
  apply (exteriorPower.zeroEquiv A Ω[A⁄k]).injective
  rw [LinearEquiv.apply_symm_apply, map_smul, exteriorPower.zeroEquiv_ιMulti, smul_eq_mul, mul_one]

theorem one_eq (α : Ω[A⁄k]) : one α = exteriorPower.ιMulti A 1 (fun _ => α) := by
  apply (exteriorPower.oneEquiv A Ω[A⁄k]).injective
  rw [LinearEquiv.apply_symm_apply, exteriorPower.oneEquiv_ιMulti]

theorem pull_scalar (φ : A →ₐ[k] B) (a : A) :
    exteriorPullback φ 0 (scalar a) = scalar (φ a) := by
  rw [scalar_eq, scalar_eq, (exteriorPullback φ 0).map_smulₛₗ,
    exteriorPullback, CycleQ2GeometricExteriorSheaf.exteriorMap_wedge]
  congr 2
  funext i; exact i.elim0

theorem pull_one (φ : A →ₐ[k] B) (α : Ω[A⁄k]) :
    exteriorPullback φ 1 (one α) = one (onePullback φ α) := by
  rw [one_eq, one_eq, exteriorPullback, CycleQ2GeometricExteriorSheaf.exteriorMap_wedge]

variable {n : ℕ} (b : Basis (Fin n) A Ω[A⁄k])

/-- In the actual affine exterior complex the degree-zero map is the
 universal derivation, with the canonical degree-zero and one identifications. -/
theorem d_scalar (a : A) : d b 0 (scalar a) = one (D k A a) := by
  let e : Fin 0 → Fin n := Fin.elim0
  have hz : d b 0 (exteriorPower.ιMulti A 0 (fun j => Fin.elim0 j)) = 0 := by
    convert CycleQ2FrameExteriorIdentities.d_coordinate_wedge b 0 e using 3
  rw [scalar_eq,d_smul,hz,smul_zero,add_zero,front_wedge,one_eq]
  congr 1
  funext j; fin_cases j; rfl

/-- Every choice of exact frame gives the same local affine differential. -/
theorem change_frame [CharZero k] (u : Fin n → A) (hu : ∀ i, b i = D k A (u i))
    (c : Basis (Fin n) A Ω[A⁄k]) (v : Fin n → A) (hv : ∀ i, c i = D k A (v i))
    (q : ℕ) (w : Form k A q) : d b q w = d c q w := by
  simpa only [exteriorPullback_id, LinearMap.id_apply] using
    CycleQ2FrameDifferentialNaturality.differential_natural b u hu c v hv (AlgHom.id k A) q w

end CycleQ2AffineZeroOneForms

namespace CycleQ2NormalCechFormBoundary
open Module KaehlerDifferential CycleQ2FrameCurl CycleQ2CechDenominatorTorsion
open CycleQ2WeightedCoordinateExterior CycleQ2ExactFrameThreeDeRham
open CycleQ2NormalCechKahler CycleQ2ArbitraryFrameDifferential
section Pull
variable {k A B : Type} [Field k] [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
    {n : ℕ} (b : Basis (Fin n) A Ω[A⁄k]) (t : Basis (Fin n) B Ω[B⁄k]) (φ : A →ₐ[k] B)
    (hb : ∀ i, onePullback φ (b i) = t i)
include hb

theorem coord_pull (i : Fin n) (ω : Ω[A⁄k]) : t.coord i (onePullback φ ω) = φ (b.coord i ω) := by
  nth_rw 1 [← b.sum_repr ω]
  simp only [map_sum, (onePullback φ).map_smulₛₗ, hb, map_smul, smul_eq_mul, Basis.coord_apply, Basis.repr_self_apply]
  simp [mul_ite]

theorem pair_pull (i j : Fin n) (ω : Form k A 2) :
    pair t i j (exteriorPullback φ 2 ω) = φ (pair b i j ω) := by
  have hspan : ω ∈ Submodule.span A (Set.range (exteriorPower.ιMulti A 2 (M := Ω[A⁄k]))) := by
    rw [exteriorPower.ιMulti_span]; trivial
  induction hspan using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨v,rfl⟩ := hz
    have hv : v = ![v 0,v 1] := by funext j; fin_cases j <;> rfl
    rw [hv, exteriorPullback, CycleQ2GeometricExteriorSheaf.exteriorMap_wedge]
    change pair t i j (wedge (onePullback φ (v 0)) (onePullback φ (v 1))) = φ (pair b i j (wedge _ _))
    simp only [pair_wedge, coord_pull b t φ hb, map_sub, map_mul]
  | zero => rw [(exteriorPullback φ 2).map_zero, map_zero, map_zero, map_zero]
  | add x y hx hy hx' hy' => simp only [map_add,hx',hy']
  | smul r x hx hx' => rw [(exteriorPullback φ 2).map_smulₛₗ, (pair t i j).map_smul, (pair b i j).map_smul, smul_eq_mul, smul_eq_mul, map_mul, hx']; rfl
end Pull

section Local
variable {k R U V T : Type} [Field k] [CharZero k] [Algebra ℂ k]
    [CommRing R] [CommRing U] [CommRing V] [CommRing T]
    [Algebra ℂ R] [Algebra ℂ U] [Algebra ℂ V] [Algebra ℂ T]
    [Algebra R U] [Algebra R V] [Algebra R T]
    [Algebra k R] [Algebra k T] [Algebra k U] [Algebra k V]
    [IsScalarTower ℂ k R] [IsScalarTower ℂ k T] [IsScalarTower k R T]
    [IsScalarTower k R U] [IsScalarTower k R V]
    [IsScalarTower ℂ R U] [IsScalarTower ℂ R V] [IsScalarTower ℂ R T]
    {n : ℕ} (b : Basis (Fin n) R Ω[R⁄k]) (u : Fin n → R) (hu : ∀ i, b i = D k R (u i))

include hu
omit [CharZero k] [Algebra ℂ k] [Algebra ℂ R] [Algebra ℂ T] [IsScalarTower ℂ k R] [IsScalarTower ℂ k T] [IsScalarTower ℂ R T] in
theorem frame_exact (M : Submonoid R) [IsLocalization M T] (i : Fin n) :
    localFrame (T := T) b M i = D k T (algebraMap R T (u i)) := by
  let := Algebra.FormallyEtale.of_isLocalization (Rₘ := T) M
  let e := tensorKaehlerEquivOfFormallyEtale k R T
  apply e.symm.injective
  change e.symm (e ((b.baseChange T) i)) = _
  rw [LinearEquiv.symm_apply_apply, Basis.baseChange_apply, hu]
  exact (tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap k R T _).symm

/-- If the genuine exterior derivative of an intersection one-form is a
 difference of two restrictions, the one-form differs from an exact form by
 a difference of restrictions of ordinary one-forms on those same opens. -/
theorem exact_mod_boundary (a c : Fin n) (hac : a ≠ c)
    [IsLocalization.Away (u a) U] [IsLocalization.Away (u c) V]
    [IsLocalization.Away (u a * u c) T] (ω : Ω[T⁄k])
    (ρ : U →ₐ[k] T := (fromFirst (A := U) (T := T) (u a) (u c)).restrictScalars k)
    (σ : V →ₐ[k] T := (fromSecond (B := V) (T := T) (u a) (u c)).restrictScalars k)
    (hρ : ρ = (fromFirst (u a) (u c)).restrictScalars k := by rfl)
    (hσ : σ = (fromSecond (u a) (u c)).restrictScalars k := by rfl)
    (t := localFrame (T := T) b (Submonoid.powers (u a * u c)))
    (ht : t = localFrame b (Submonoid.powers (u a * u c)) := by rfl)
    (hω : ∃ α : Form k U 2, ∃ β : Form k V 2,
      d t 1 ((exteriorPower.oneEquiv T Ω[T⁄k]).symm ω) = exteriorPullback ρ 2 α - exteriorPullback σ 2 β) :
    ∃ f : T, ∃ α : Ω[U⁄k], ∃ β : Ω[V⁄k], D k T f - ω = onePullback ρ α - onePullback σ β := by
  subst t; subst ρ; subst σ
  let r := fromFirst (A := U) (T := T) (u a) (u c)
  let s := fromSecond (B := V) (T := T) (u a) (u c)
  let bU := localFrame (T := U) b (Submonoid.powers (u a))
  let bV := localFrame (T := V) b (Submonoid.powers (u c))
  let bT := localFrame (T := T) b (Submonoid.powers (u a * u c))
  have hr (i : Fin n) : onePullback (r.restrictScalars k) (bU i) = bT i := by
    rw [frame_exact b u hu _ i, onePullback_d, frame_exact b u hu _ i]; exact congrArg (D k T) (r.commutes (u i))
  have hs (i : Fin n) : onePullback (s.restrictScalars k) (bV i) = bT i := by
    rw [frame_exact b u hu _ i, onePullback_d, frame_exact b u hu _ i]; exact congrArg (D k T) (s.commutes (u i))
  obtain ⟨α,β,h⟩ := hω
  obtain ⟨f,hf⟩ := one_form_exact (U := U) (V := V) b u hu a c hac ω (by
    dsimp only; intro i; rw [h, map_sub, pair_pull bU bT _ hr, pair_pull bV bT _ hs]
    apply Submodule.sub_mem
    · exact le_sup_left (b := LinearMap.range s.toLinearMap) ⟨_,rfl⟩
    · exact le_sup_right (a := LinearMap.range r.toLinearMap) ⟨_,rfl⟩)
  have coeff (i : Fin n) : ∃ l : U, ∃ m : V, r l + s m = bT.coord i (D k T f - ω) := by
    obtain ⟨_,⟨l,rfl⟩,_,⟨m,rfl⟩,hm⟩ := Submodule.mem_sup.mp (hf i)
    exact ⟨l,m,hm⟩
  choose l m hm using coeff
  refine ⟨f,bU.equivFun.symm l,-bV.equivFun.symm m,bT.equivFun.injective ?_⟩
  funext i
  change bT.coord i (D k T f - ω) = bT.coord i (_ - _)
  rw [← hm, map_sub, coord_pull bU bT _ hr, map_neg, map_neg, coord_pull bV bT _ hs, sub_neg_eq_add]
  rw [Basis.coord_equivFun_symm, Basis.coord_equivFun_symm]
  rfl

open CycleQ2AffineZeroOneForms (scalar one d_scalar pull_one pull_scalar change_frame)

/-- Membership in the signed image of the actual two restriction maps. -/
def IsBoundary {A B C : Type} [CommRing A] [CommRing B] [CommRing C]
    [Algebra k A] [Algebra k B] [Algebra k C] (ρ : A →ₐ[k] C) (σ : B →ₐ[k] C)
    (q : ℕ) (ω : Form k C q) : Prop :=
  ∃ α : Form k A q, ∃ β : Form k B q, ω = exteriorPullback ρ q α - exteriorPullback σ q β

variable (a c : Fin n) (hac : a ≠ c) [IsLocalization.Away (u a) U] [IsLocalization.Away (u c) V]
    [IsLocalization.Away (u a * u c) T]

private abbrev resX := (fromFirst (A := U) (T := T) (u a) (u c)).restrictScalars k
private abbrev resY := (fromSecond (B := V) (T := T) (u a) (u c)).restrictScalars k

include hac

/-- Vanishing of degree zero of the quotient de Rham complex of actual
 exterior forms. The intersection chart may use any exact frame. -/
theorem row_zero (t : Basis (Fin n) T Ω[T⁄k])
    (w : Form k T 0)
    (hw : IsBoundary (resX (U := U) (T := T) u a c) (resY (V := V) (T := T) u a c) 1 (d t 0 w)) :
    IsBoundary (resX (U := U) (T := T) u a c) (resY (V := V) (T := T) u a c) 0 w := by
  obtain ⟨f,rfl⟩ := (scalar (k := k) (A := T)).surjective w
  obtain ⟨α,β,h⟩ := hw
  obtain ⟨α,rfl⟩ := (one (k := k) (A := U)).surjective α
  obtain ⟨β,rfl⟩ := (one (k := k) (A := V)).surjective β
  rw [d_scalar, pull_one, pull_one, ← map_sub] at h
  have hform := (one (k := k) (A := T)).injective h
  let r := fromFirst (A := U) (T := T) (u a) (u c)
  let s := fromSecond (B := V) (T := T) (u a) (u c)
  let bU := localFrame (T := U) b (Submonoid.powers (u a))
  let bV := localFrame (T := V) b (Submonoid.powers (u c))
  let bT := localFrame (T := T) b (Submonoid.powers (u a * u c))
  have hr (i : Fin n) : onePullback (r.restrictScalars k) (bU i) = bT i := by
    rw [frame_exact b u hu _ i, onePullback_d, frame_exact b u hu _ i]; exact congrArg (D k T) (r.commutes (u i))
  have hs (i : Fin n) : onePullback (s.restrictScalars k) (bV i) = bT i := by
    rw [frame_exact b u hu _ i, onePullback_d, frame_exact b u hu _ i]; exact congrArg (D k T) (s.commutes (u i))
  have hf := function_is_boundary (U := U) (V := V) b u hu a c hac f (by
    rw [hform, map_sub, coord_pull bU bT _ hr, coord_pull bV bT _ hs]
    exact Submodule.sub_mem _ (le_sup_left (b := LinearMap.range s.toLinearMap) ⟨_,rfl⟩)
      (le_sup_right (a := LinearMap.range r.toLinearMap) ⟨_,rfl⟩))
  obtain ⟨_,⟨l,rfl⟩,_,⟨m,rfl⟩,hm⟩ := Submodule.mem_sup.mp hf
  refine ⟨scalar l, scalar (-m), ?_⟩
  rw [pull_scalar, pull_scalar, ← map_sub, map_neg, sub_neg_eq_add]
  exact congrArg (scalar (k := k) (A := T)) hm.symm

/-- Vanishing in degree one of the actual quotient de Rham complex for
 any choice of exact intersection chart frame. -/
theorem row_one (t : Basis (Fin n) T Ω[T⁄k]) (v : Fin n → T) (ht : ∀ i, t i = D k T (v i))
    (w : Form k T 1)
    (hw : IsBoundary (resX (U := U) (T := T) u a c) (resY (V := V) (T := T) u a c) 2 (d t 1 w)) :
    ∃ z : Form k T 0, IsBoundary (resX (U := U) (T := T) u a c) (resY (V := V) (T := T) u a c) 1 (w - d t 0 z) := by
  obtain ⟨ω,rfl⟩ := (one (k := k) (A := T)).surjective w
  let B := localFrame (T := T) b (Submonoid.powers (u a * u c))
  have hB (i : Fin n) : B i = D k T (algebraMap R T (u i)) := frame_exact b u hu _ i
  rw [change_frame t v ht B _ hB] at hw
  obtain ⟨f,α,β,h⟩ := exact_mod_boundary (U := U) (V := V) b u hu a c hac ω (hω := hw)
  refine ⟨scalar f, one (-α), one (-β), ?_⟩
  rw [d_scalar, pull_one, pull_one, ← map_sub, ← map_sub]
  apply congrArg (one (k := k) (A := T))
  rw [map_neg, map_neg, neg_sub_neg]
  simpa only [neg_sub] using congrArg Neg.neg h

end Local
end CycleQ2NormalCechFormBoundary


namespace CycleQ2NormalChartForms
open Module KaehlerDifferential CycleQ2WeightedCoordinateExterior
open CycleQ2ArbitraryFrameDifferential CycleQ2NormalCechFormBoundary
open CycleQ2CechDenominatorTorsion
variable {k R U V T : Type} [Field k] [CharZero k] [Algebra ℂ k]
    [CommRing R] [CommRing U] [CommRing V] [CommRing T]
    [Algebra k R] [Algebra k U] [Algebra k V] [Algebra k T]
    [Algebra R U] [Algebra R V] [Algebra R T]
    [IsScalarTower k R U] [IsScalarTower k R V] [IsScalarTower k R T]
    {n : ℕ} (B : Basis (Fin n) R Ω[R⁄k]) (u : Fin n → R) (hu : ∀ i, B i = D k R (u i))
    (a c : Fin n) (hac : a ≠ c) [IsLocalization.Away (u a) U] [IsLocalization.Away (u c) V]
    [IsLocalization.Away (u a * u c) T]

include hu hac

/-- Quotient de Rham exactness in degrees zero and one, for the actual
restriction maps of the three specified algebra localizations. -/
theorem low_degrees (t : Basis (Fin n) T Ω[T⁄k]) (v : Fin n → T) (ht : ∀ i, t i = D k T (v i)) :
    let ρ := (fromFirst (A := U) (T := T) (u a) (u c)).restrictScalars k
    let σ := (fromSecond (B := V) (T := T) (u a) (u c)).restrictScalars k
    (∀ s : Form k T 0, IsBoundary ρ σ 1 (d t 0 s) → IsBoundary ρ σ 0 s) ∧
    (∀ s : Form k T 1, IsBoundary ρ σ 2 (d t 1 s) → ∃ z : Form k T 0, IsBoundary ρ σ 1 (s - d t 0 z)) := by
  let _ : Algebra ℂ R := ((algebraMap k R).comp (algebraMap ℂ k)).toAlgebra
  let _ : Algebra ℂ U := ((algebraMap k U).comp (algebraMap ℂ k)).toAlgebra
  let _ : Algebra ℂ V := ((algebraMap k V).comp (algebraMap ℂ k)).toAlgebra
  let _ : Algebra ℂ T := ((algebraMap k T).comp (algebraMap ℂ k)).toAlgebra
  let _ : IsScalarTower ℂ k R := IsScalarTower.of_algebraMap_eq' rfl
  let _ : IsScalarTower ℂ k T := IsScalarTower.of_algebraMap_eq' rfl
  let _ : IsScalarTower ℂ R U := IsScalarTower.of_algebraMap_eq fun x => IsScalarTower.algebraMap_apply k R U (algebraMap ℂ k x)
  let _ : IsScalarTower ℂ R V := IsScalarTower.of_algebraMap_eq fun x => IsScalarTower.algebraMap_apply k R V (algebraMap ℂ k x)
  let _ : IsScalarTower ℂ R T := IsScalarTower.of_algebraMap_eq fun x => IsScalarTower.algebraMap_apply k R T (algebraMap ℂ k x)
  exact ⟨row_zero B u hu a c hac t, row_one B u hu a c hac t v ht⟩

end CycleQ2NormalChartForms

namespace CycleQ2SupportedWeyl

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

/-- With three normal coordinates, the degree-two normal de Rham complex is
exact, including every tangential coefficient. The proof first solves the
degree-one problem modulo the image of the first derivative, then uses its
injectivity to recover all the remaining coefficient identities. -/
theorem ambient_two_form_exact {ι : Type*} (a b c : ι)
    (X Y Z : Module.End ℚ V) (D : ι → Module.End ℚ V)
    (hxx : ∀ m, D a (X m) = m + X (D a m))
    (hyy : ∀ m, D b (Y m) = m + Y (D b m))
    (hzz : ∀ m, D c (Z m) = m + Z (D c m))
    (hyx : ∀ m, Y (D a m) = D a (Y m))
    (hzx : ∀ m, Z (D a m) = D a (Z m))
    (hzy : ∀ m, Z (D b m) = D b (Z m))
    (hdd : ∀ i j m, D i (D j m) = D j (D i m))
    (hnx : ∀ m, ∃ n : ℕ, (X ^ n) m = 0)
    (hny : ∀ m, ∃ n : ℕ, (Y ^ n) m = 0)
    (hnz : ∀ m, ∃ n : ℕ, (Z ^ n) m = 0)
    (p : ι → ι → V)
    (hc : ∀ i j, D a (p i j) = D i (p a j) - D j (p a i)) :
    ∃ f : ι → V, ∀ i j, D i (f j) - D j (f i) = p i j := by
  classical
  let S := LinearMap.range (D a)
  have stableD (i : ι) : ∀ m ∈ S, D i m ∈ S := by
    rintro _ ⟨m,rfl⟩
    exact ⟨D i m,(hdd i a m).symm⟩
  have stableY : ∀ m ∈ S, Y m ∈ S := by
    rintro _ ⟨m,rfl⟩
    exact ⟨Y m,(hyx m).symm⟩
  have stableZ : ∀ m ∈ S, Z m ∈ S := by
    rintro _ ⟨m,rfl⟩
    exact ⟨Z m,(hzx m).symm⟩
  let E (i : ι) : Module.End ℚ (V ⧸ S) := S.mapQ S (D i) (stableD i)
  let y : Module.End ℚ (V ⧸ S) := S.mapQ S Y stableY
  let z : Module.End ℚ (V ⧸ S) := S.mapQ S Z stableZ
  have yy (v : V ⧸ S) : E b (y v) = v + y (E b v) := by
    obtain ⟨m,rfl⟩ := S.mkQ_surjective v
    change S.mkQ (D b (Y m)) = S.mkQ m + S.mkQ (Y (D b m))
    rw [hyy,map_add]
  have zz (v : V ⧸ S) : E c (z v) = v + z (E c v) := by
    obtain ⟨m,rfl⟩ := S.mkQ_surjective v
    change S.mkQ (D c (Z m)) = S.mkQ m + S.mkQ (Z (D c m))
    rw [hzz,map_add]
  have zy (v : V ⧸ S) : z (E b v) = E b (z v) := by
    obtain ⟨m,rfl⟩ := S.mkQ_surjective v
    exact congrArg S.mkQ (hzy m)
  have dd (i : ι) (v : V ⧸ S) : E i (E b v) = E b (E i v) := by
    obtain ⟨m,rfl⟩ := S.mkQ_surjective v
    exact congrArg S.mkQ (hdd i b m)
  have powY (n : ℕ) (m : V) : (y ^ n) (S.mkQ m) = S.mkQ ((Y ^ n) m) := by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [pow_succ' y,pow_succ' Y,Module.End.mul_apply,Module.End.mul_apply,ih]
      rfl
  have powZ (n : ℕ) (m : V) : (z ^ n) (S.mkQ m) = S.mkQ ((Z ^ n) m) := by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [pow_succ' z,pow_succ' Z,Module.End.mul_apply,Module.End.mul_apply,ih]
      rfl
  have ny (v : V ⧸ S) : ∃ n : ℕ, (y ^ n) v = 0 := by
    obtain ⟨m,rfl⟩ := S.mkQ_surjective v
    obtain ⟨n,hn⟩ := hny m
    exact ⟨n,by rw [powY,hn,map_zero]⟩
  have nz (v : V ⧸ S) : ∃ n : ℕ, (z ^ n) v = 0 := by
    obtain ⟨m,rfl⟩ := S.mkQ_surjective v
    obtain ⟨n,hn⟩ := hnz m
    exact ⟨n,by rw [powZ,hn,map_zero]⟩
  let q (i : ι) : V ⧸ S := S.mkQ (p a i)
  have closed (i : ι) : E i (q b) = E b (q i) := by
    apply (Submodule.Quotient.eq S).mpr
    change D i (p a b) - D b (p a i) ∈ S
    have he : D i (p a b) - D b (p a i) = D a (-p b i) := by
      rw [map_neg,hc]
      abel
    rw [he]
    exact ⟨-p b i,rfl⟩
  obtain ⟨v,hv⟩ := ambient_one_form_exact b c y z E yy zz zy dd ny nz q closed
  obtain ⟨v,rfl⟩ := S.mkQ_surjective v
  have lifts (i : ι) : ∃ f : V, D a f = p a i - D i v := by
    have hi := S.neg_mem ((Submodule.Quotient.eq S).mp (hv i))
    change -(D i v - p a i) ∈ S at hi
    apply LinearMap.mem_range.mp
    simpa only [neg_sub] using hi
  choose f hf using lifts
  refine ⟨f,fun i j => derivative_injective X (D a) hxx hnx ?_⟩
  rw [map_sub,hdd a i,hdd a j,hf,hf,map_sub,map_sub,hc,hdd i j]
  abel

end CycleQ2SupportedWeyl

namespace CycleQ2FinitePrincipalParts

open CycleQ2GeometricLocalizedDerivations CycleQ2NormalCechDerivation

variable {ι : Type} [Fintype ι] [DecidableEq ι]
    {R T : Type} [CommRing R] [CommRing T] [Algebra R T]
    (U : ι → Type) [∀ i, CommRing (U i)] [∀ i, Algebra R (U i)] (x : ι → R)

def denominator : R := ∏ i, x i

def faceDenominator (i : ι) : R := ∏ j ∈ Finset.univ.erase i, x j

theorem mul_faceDenominator (i : ι) : x i * faceDenominator x i = denominator x :=
  Finset.mul_prod_erase Finset.univ x (Finset.mem_univ i)

variable [∀ i, IsLocalization.Away (faceDenominator x i) (U i)]
    [IsLocalization.Away (denominator x) T]

/-- The actual restriction from the face omitting one normal coordinate
to the full intersection of the principal opens. -/
def faceToTop (i : ι) : U i →ₐ[R] T :=
  IsLocalization.Away.liftAlgHom (faceDenominator x i) (f := Algebra.ofId R T)
    (IsLocalization.Away.isUnit_of_dvd (denominator x)
      ⟨x i,by rw [← mul_faceDenominator x i]; exact mul_comm _ _⟩)

/-- The top Čech boundary submodule: sums of the actual restrictions from
the faces omitting one coordinate. For three equations these are the three
double principal opens, not the three single principal opens. -/
def boundaries : Submodule R T :=
  Submodule.span R {z | ∃ i, ∃ a : U i, faceToTop U x i a = z}

theorem face_mem (i : ι) (a : U i) : faceToTop U x i a ∈ boundaries U x :=
  Submodule.subset_span ⟨i,a,rfl⟩

def sumFaces : (∀ i, U i) →ₗ[R] T where
  toFun a := ∑ i, faceToTop U x i (a i)
  map_add' a b := by simp only [Pi.add_apply,map_add,Finset.sum_add_distrib]
  map_smul' r a := by simp only [Pi.smul_apply,map_smul,Finset.smul_sum]

/-- The span description retains actual representatives on each omitted
face; no infinite family of denominators is introduced by taking the span. -/
theorem boundaries_eq_range : boundaries U x = LinearMap.range (sumFaces U x) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i,a,rfl⟩
    refine ⟨Pi.single i a,?_⟩
    change (∑ j, faceToTop U x j (Pi.single i a j)) = faceToTop U x i a
    rw [Finset.sum_eq_single i]
    · simp only [Pi.single_eq_same]
    · intro j _ hji
      rw [Pi.single_eq_of_ne hji,map_zero]
    · intro hi
      exact (hi (Finset.mem_univ i)).elim
  · rintro a ⟨v,rfl⟩
    exact Submodule.sum_mem _ (fun i _ => face_mem U x i (v i))

theorem mem_boundaries_iff (a : T) :
    a ∈ boundaries U x ↔ ∃ v : ∀ i, U i, (∑ i, faceToTop U x i (v i)) = a := by
  rw [boundaries_eq_range]
  rfl

abbrev Parts := T ⧸ boundaries U x

/-- Every normal coordinate acts locally nilpotently on the actual top
Čech quotient, by clearing the denominator into its omitted face. -/
theorem powers_kill (i : ι) (v : Parts U x) : ∃ n : ℕ, x i ^ n • v = 0 := by
  obtain ⟨a,rfl⟩ := (boundaries U x).mkQ_surjective v
  obtain ⟨n,c,hc⟩ := IsLocalization.Away.surj (denominator x) a
  have hfactor : algebraMap R T (denominator x) =
      algebraMap R T (x i) * algebraMap R T (faceDenominator x i) := by
    rw [← mul_faceDenominator x i,map_mul]
  rw [hfactor] at hc
  have hclear := CycleQ2CechDenominatorTorsion.clears_other
    (faceToTop U x i) a n c hc
  obtain ⟨b,hb⟩ := hclear
  refine ⟨n,?_⟩
  rw [← LinearMap.map_smul,Submodule.mkQ_apply,Submodule.Quotient.mk_eq_zero]
  exact hb ▸ face_mem U x i b

section Derivatives

variable [Algebra ℂ R] [Algebra ℂ T] [IsScalarTower ℂ R T]
    [∀ i, Algebra ℂ (U i)] [∀ i, IsScalarTower ℂ R (U i)]

private theorem preserves (d : Derivation ℂ R R) {a : T}
    (ha : a ∈ boundaries U x) :
    localizedDerivation (.powers (denominator x)) T d a ∈ boundaries U x := by
  induction ha using Submodule.span_induction with
  | mem a ha =>
      obtain ⟨i,b,rfl⟩ := ha
      rw [localization_natural (.powers (faceDenominator x i))
        (.powers (denominator x)) (faceToTop U x i)]
      exact face_mem U x i _
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
  | smul r a ha hd =>
      change localizedDerivation (.powers (denominator x)) T d
        (algebraMap R T r * a) ∈ boundaries U x
      rw [Derivation.leibniz,localizedDerivation_algebraMap]
      change r • localizedDerivation (.powers (denominator x)) T d a + d r • a ∈ boundaries U x
      exact Submodule.add_mem _ (Submodule.smul_mem _ r hd) (Submodule.smul_mem _ (d r) ha)

/-- Coordinate differentiation on the literal top Čech quotient. -/
def onParts (d : Derivation ℂ R R) : Module.End ℂ (Parts U x) :=
  let S := (boundaries U x).restrictScalars ℂ
  S.mapQ S (localizedDerivation (.powers (denominator x)) T d).toLinearMap
    (by intro a ha; exact preserves U x d ha)

@[simp] theorem onParts_mk (d : Derivation ℂ R R) (a : T) :
    onParts U x d (Submodule.Quotient.mk a) =
      Submodule.Quotient.mk (localizedDerivation (.powers (denominator x)) T d a) := rfl

theorem onParts_smul (d : Derivation ℂ R R) (r : R) (v : Parts U x) :
    onParts U x d (r • v) = r • onParts U x d v + d r • v := by
  obtain ⟨a,rfl⟩ := (boundaries U x).mkQ_surjective v
  change Submodule.Quotient.mk (localizedDerivation (.powers (denominator x)) T d (r • a)) =
    (Submodule.Quotient.mk (r • localizedDerivation (.powers (denominator x)) T d a + d r • a) : Parts U x)
  congr 1
  simp [Algebra.smul_def,Derivation.leibniz,localizedDerivation_algebraMap,mul_comm,add_comm]

theorem onParts_commute (d e : Derivation ℂ R R) (h : ∀ r, d (e r) = e (d r))
    (v : Parts U x) : onParts U x d (onParts U x e v) = onParts U x e (onParts U x d v) := by
  obtain ⟨a,rfl⟩ := (boundaries U x).mkQ_surjective v
  exact congrArg Submodule.Quotient.mk
    (localizations_commute (.powers (denominator x)) T d e h a)

local instance ratModule : Module ℚ (Parts U x) :=
  Module.compHom (Parts U x) (algebraMap ℚ ℂ)

local instance ratTower : IsScalarTower ℚ ℂ (Parts U x) :=
  IsScalarTower.of_compHom ℚ ℂ (Parts U x)

private def derivativeOperator (d : Derivation ℂ R R) : Module.End ℚ (Parts U x) :=
  (onParts U x d).restrictScalars ℚ

private def coordinateOperator (r : R) : Module.End ℚ (Parts U x) :=
  ((LinearMap.lsmul R (Parts U x) r).restrictScalars ℂ).restrictScalars ℚ

private theorem coordinateOperator_pow (r : R) (v : Parts U x) (n : ℕ) :
    (coordinateOperator U x r ^ n) v = r ^ n • v := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ',Module.End.mul_apply,ih,pow_succ' r]
      exact (mul_smul r (r ^ n) v).symm

private theorem coordinateOperator_nilpotent (i : ι) (v : Parts U x) :
    ∃ n : ℕ, (coordinateOperator U x (x i) ^ n) v = 0 := by
  obtain ⟨n,hn⟩ := powers_kill U x i v
  exact ⟨n,(coordinateOperator_pow U x (x i) v n).trans hn⟩

private theorem operator_Weyl (d : Derivation ℂ R R) (r : R) (hr : d r = 1)
    (v : Parts U x) :
    derivativeOperator U x d (coordinateOperator U x r v) =
      v + coordinateOperator U x r (derivativeOperator U x d v) := by
  change onParts U x d (r • v) = v + r • onParts U x d v
  rw [onParts_smul,hr,one_smul,add_comm]

private theorem operator_cross (d : Derivation ℂ R R) (r : R) (hr : d r = 0)
    (v : Parts U x) :
    coordinateOperator U x r (derivativeOperator U x d v) =
      derivativeOperator U x d (coordinateOperator U x r v) := by
  change r • onParts U x d v = onParts U x d (r • v)
  rw [onParts_smul,hr,zero_smul,add_zero]

/-- A normal coordinate derivative is injective on this actual top Čech
quotient. In particular a horizontal degree-zero representative is zero. -/
theorem derivative_injective (a : ι) (d : Derivation ℂ R R) (hd : d (x a) = 1) :
    Function.Injective (onParts U x d) :=
  CycleQ2SupportedWeyl.derivative_injective (coordinateOperator U x (x a))
    (derivativeOperator U x d) (operator_Weyl U x d (x a) hd)
    (coordinateOperator_nilpotent U x a)

/-- Exactness of all one-form coefficients on the top Čech row. The two
specified normal derivatives are genuine derivations of the unlocalized
chart, and every other coefficient is recovered from closedness. -/
theorem closed_one_exact {η : Type} (a b : ι) (i j : η)
    (D : η → Derivation ℂ R R)
    (hxx : D i (x a) = 1) (hyy : D j (x b) = 1) (hxy : D i (x b) = 0)
    (hcomm : ∀ q r, D q (D i r) = D i (D q r))
    (p : η → Parts U x)
    (hp : ∀ q, onParts U x (D q) (p i) = onParts U x (D i) (p q)) :
    ∃ f : Parts U x, ∀ q, onParts U x (D q) f = p q :=
  CycleQ2SupportedWeyl.ambient_one_form_exact i j
    (coordinateOperator U x (x a)) (coordinateOperator U x (x b))
    (fun q => derivativeOperator U x (D q))
    (operator_Weyl U x (D i) (x a) hxx)
    (operator_Weyl U x (D j) (x b) hyy)
    (operator_cross U x (D i) (x b) hxy)
    (fun q v => onParts_commute U x (D q) (D i) (hcomm q) v)
    (coordinateOperator_nilpotent U x a) (coordinateOperator_nilpotent U x b) p hp

/-- Exactness in degree two on the actual triple (or higher) principal-open
Čech quotient. Only three normal coordinates are needed; the result includes
all tangential pairs as well. Its closedness equation has the ordinary
exterior-differential signs, ∂ᵢpᵤᵥ − ∂ᵤpᵢᵥ + ∂ᵥpᵢᵤ = 0. -/
theorem closed_two_exact {η : Type} (a b c : ι) (i j l : η)
    (D : η → Derivation ℂ R R)
    (hxx : D i (x a) = 1) (hyy : D j (x b) = 1) (hzz : D l (x c) = 1)
    (hyx : D i (x b) = 0) (hzx : D i (x c) = 0) (hzy : D j (x c) = 0)
    (hcomm : ∀ u v r, D u (D v r) = D v (D u r))
    (p : η → η → Parts U x)
    (hp : ∀ u v, onParts U x (D i) (p u v) =
      onParts U x (D u) (p i v) - onParts U x (D v) (p i u)) :
    ∃ f : η → Parts U x, ∀ u v,
      onParts U x (D u) (f v) - onParts U x (D v) (f u) = p u v :=
  CycleQ2SupportedWeyl.ambient_two_form_exact i j l
    (coordinateOperator U x (x a)) (coordinateOperator U x (x b))
    (coordinateOperator U x (x c)) (fun q => derivativeOperator U x (D q))
    (operator_Weyl U x (D i) (x a) hxx) (operator_Weyl U x (D j) (x b) hyy)
    (operator_Weyl U x (D l) (x c) hzz)
    (operator_cross U x (D i) (x b) hyx) (operator_cross U x (D i) (x c) hzx)
    (operator_cross U x (D j) (x c) hzy)
    (fun u v z => onParts_commute U x (D u) (D v) (hcomm u v) z)
    (coordinateOperator_nilpotent U x a) (coordinateOperator_nilpotent U x b)
    (coordinateOperator_nilpotent U x c) p hp

end Derivatives
end CycleQ2FinitePrincipalParts

namespace CycleQ2FrameCurl

open Module KaehlerDifferential CycleQ2ArbitraryFrameDifferential
open CycleQ2WeightedCoordinateExterior CycleQ2ExactFrameThreeDeRham
open CycleQ2CartanContraction CycleQ2ExactFrameFirstDifferential

variable {k A : Type} [Field k] [CommRing A] [Algebra k A]
    {n : ℕ} (b : Basis (Fin n) A Ω[A⁄k])

/-- An ordered triple coefficient, using the same contraction order as
the ordered pair coefficient above. -/
def triple (i j l : Fin n) : Form k A 3 →ₗ[A] A :=
  (pair b j l).comp (three (spatialDerivative b i))

theorem triple_wedge (i j l : Fin n) (α β γ : Ω[A⁄k]) :
    triple b i j l (exteriorPower.ιMulti A 3 ![α,β,γ]) =
      b.coord i α * (b.coord j β * b.coord l γ - b.coord j γ * b.coord l β) -
      b.coord i β * (b.coord j α * b.coord l γ - b.coord j γ * b.coord l α) +
      b.coord i γ * (b.coord j α * b.coord l β - b.coord j β * b.coord l α) := by
  simp only [triple,LinearMap.comp_apply,three_wedge,map_add,map_sub,map_smul,
    smul_eq_mul,pair_wedge,contractions]

theorem triple_front (i j l : Fin n) (α : Ω[A⁄k]) (ω : Form k A 2) :
    triple b i j l (front 2 α ω) =
      b.coord i α * pair b j l ω - b.coord j α * pair b i l ω +
        b.coord l α * pair b i j ω := by
  have hω : ω ∈ Submodule.span A (Set.range (exteriorPower.ιMulti A 2)) := by
    rw [exteriorPower.ιMulti_span]
    trivial
  induction hω using Submodule.span_induction with
  | mem ω hω =>
      obtain ⟨v,rfl⟩ := hω
      have hv : v = ![v 0,v 1] := by funext i; fin_cases i <;> rfl
      rw [hv,front_wedge]
      change triple b i j l (exteriorPower.ιMulti A 3 ![α,v 0,v 1]) = _
      rw [triple_wedge]
      change _ = b.coord i α * pair b j l (wedge (v 0) (v 1)) -
        b.coord j α * pair b i l (wedge (v 0) (v 1)) +
        b.coord l α * pair b i j (wedge (v 0) (v 1))
      simp only [pair_wedge]
      ring
  | zero => simp only [map_zero,mul_zero,sub_zero,add_zero]
  | add ω ν _ _ hω hν => simp only [map_add,hω,hν]; ring
  | smul r ω _ hω => simp only [map_smul,smul_eq_mul,hω]; ring

/-- The sorted exterior coordinate is precisely the corresponding ordered
pair coefficient. This fixes the coefficient normalization without a factor
of two or a choice of a different exterior basis. -/
theorem exterior_coord_pair (s : Set.powersetCard (Fin n) 2) :
    (b.exteriorPower 2).coord s =
      pair b (Set.powersetCard.ofFinEmbEquiv.symm s 0)
        (Set.powersetCard.ofFinEmbEquiv.symm s 1) := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro v
  change (b.exteriorPower 2).coord s (exteriorPower.ιMulti A 2 v) = _
  rw [exteriorPower.basis_coord,exteriorPower.ιMultiDual_apply_ιMulti,Matrix.det_fin_two]
  have hv : v = ![v 0,v 1] := by funext i; fin_cases i <;> rfl
  conv_rhs => rw [hv]
  change _ = pair b _ _ (wedge (v 0) (v 1))
  rw [pair_wedge]
  simp only [Matrix.of_apply]
  ring

private theorem pair_basis_derivative (δ : Derivation k A A)
    (i j : Fin n) (s : Set.powersetCard (Fin n) 2) :
    δ (pair b i j (b.exteriorPower 2 s)) = 0 := by
  rw [exteriorPower.basis_apply,exteriorPower.ιMulti_family]
  let v := Set.powersetCard.ofFinEmbEquiv.symm s
  have hv : b ∘ v = ![b (v 0),b (v 1)] := by funext i; fin_cases i <;> rfl
  rw [hv]
  change δ (pair b i j (wedge (b (v 0)) (b (v 1)))) = 0
  simp [pair_wedge,Basis.coord_apply,Basis.repr_self,Finsupp.single_apply,
    mul_ite,ite_mul,apply_ite]

/-- The three-component curl of a two-form is the ordered triple
coefficient of its genuine exterior differential. -/
theorem triple_d_two (i j l : Fin n) (ω : Form k A 2) :
    triple b i j l (d b 2 ω) =
      spatialDerivative b i (pair b j l ω) -
      spatialDerivative b j (pair b i l ω) +
      spatialDerivative b l (pair b i j ω) := by
  classical
  have basisCase (s : Set.powersetCard (Fin n) 2) (a : A) :
      triple b i j l (d b 2 (a • b.exteriorPower 2 s)) =
        spatialDerivative b i (pair b j l (a • b.exteriorPower 2 s)) -
        spatialDerivative b j (pair b i l (a • b.exteriorPower 2 s)) +
        spatialDerivative b l (pair b i j (a • b.exteriorPower 2 s)) := by
    rw [d_smul_basis,triple_front]
    simp only [map_smul,smul_eq_mul,Derivation.leibniz,
      pair_basis_derivative,mul_zero,zero_add,partial_apply]
    ring
  nth_rw 1 [← (b.exteriorPower 2).sum_repr ω]
  rw [map_sum,map_sum]
  simp_rw [basisCase]
  simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,← map_sum,
    (b.exteriorPower 2).sum_repr]

end CycleQ2FrameCurl

namespace CycleQ2NormalCechFormBoundary

open Module KaehlerDifferential CycleQ2FrameCurl
open CycleQ2WeightedCoordinateExterior CycleQ2ExactFrameThreeDeRham

variable {k A B : Type} [Field k] [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
    {n : ℕ} (b : Basis (Fin n) A Ω[A⁄k]) (t : Basis (Fin n) B Ω[B⁄k]) (φ : A →ₐ[k] B)
    (hb : ∀ i, onePullback φ (b i) = t i)

/-- Ordered triple coefficients commute with the original Kähler
pullback whenever the exact frames do. -/
include hb in
theorem triple_pull (i j l : Fin n) (ω : Form k A 3) :
    triple t i j l (exteriorPullback φ 3 ω) = φ (triple b i j l ω) := by
  have hω : ω ∈ Submodule.span A (Set.range (exteriorPower.ιMulti A 3)) := by
    rw [exteriorPower.ιMulti_span]
    trivial
  induction hω using Submodule.span_induction with
  | mem ω hω =>
      obtain ⟨v,rfl⟩ := hω
      have hv : v = ![v 0,v 1,v 2] := by funext i; fin_cases i <;> rfl
      rw [hv,exteriorPullback,CycleQ2GeometricExteriorSheaf.exteriorMap_wedge]
      change triple t i j l (exteriorPower.ιMulti B 3
        ![onePullback φ (v 0),onePullback φ (v 1),onePullback φ (v 2)]) = _
      simp only [triple_wedge,coord_pull b t φ hb,map_add,map_sub,map_mul]
  | zero => simp only [map_zero]
  | add ω ν _ _ hω hν => simp only [map_add,hω,hν]
  | smul r ω _ hω => simp only [map_smulₛₗ,map_smul,smul_eq_mul,map_mul,hω]

end CycleQ2NormalCechFormBoundary

namespace CycleQ2FinitePrincipalFormBoundary

open Module KaehlerDifferential CycleQ2WeightedCoordinateExterior
open CycleQ2ExactFrameThreeDeRham CycleQ2FrameCurl
open CycleQ2FinitePrincipalParts CycleQ2NormalCechFormBoundary
open CycleQ2AffineZeroOneForms (scalar one pull_scalar pull_one)

variable {ι : Type} [Fintype ι] [DecidableEq ι]
    {k R T : Type} [Field k] [CommRing R] [CommRing T]
    [Algebra k R] [Algebra k T] [Algebra R T] [IsScalarTower k R T]
    (U : ι → Type) [∀ i, CommRing (U i)] [∀ i, Algebra R (U i)]
    [∀ i, Algebra k (U i)] [∀ i, IsScalarTower k R (U i)] (x : ι → R)
    [∀ i, IsLocalization.Away (faceDenominator x i) (U i)]
    [IsLocalization.Away (denominator x) T]

abbrev restriction (i : ι) : U i →ₐ[k] T := (faceToTop U x i).restrictScalars k

/-- The unsigned top Čech image on the actual exterior forms. Alternating
Čech signs give the same subgroup by negating the corresponding face. -/
def IsBoundary (q : ℕ) (ω : Form k T q) : Prop :=
  ∃ α : ∀ i, Form k (U i) q, ω = ∑ i, exteriorPullback (restriction U x i) q (α i)

variable {n : ℕ} (b : Basis (Fin n) T Ω[T⁄k])
    (c : ∀ i, Basis (Fin n) (U i) Ω[U i⁄k])
    (hc : ∀ i j, onePullback (restriction U x i) (c i j) = b j)

/-- The literal face-image condition is equivalent to its scalar coordinate
conditions in the transported exterior bases. Both implications retain
actual forms on the omitted-coordinate faces. -/
include hc in
theorem iff_coordinates (q : ℕ) (ω : Form k T q) :
    IsBoundary U x q ω ↔
      ∀ s, (b.exteriorPower q).equivFun ω s ∈ boundaries U x := by
  classical
  constructor
  · rintro ⟨α,rfl⟩ s
    rw [map_sum,Finset.sum_apply]
    apply Submodule.sum_mem
    intro i _
    rw [CycleQ2NormalExteriorCech.pull_coordinates (c i) b (restriction U x i) (hc i)]
    exact face_mem U x i _
  · intro h
    choose a ha using fun s => (mem_boundaries_iff U x _).mp (h s)
    refine ⟨fun i => ((c i).exteriorPower q).equivFun.symm (fun s => a s i),?_⟩
    apply (b.exteriorPower q).equivFun.injective
    funext s
    rw [map_sum,Finset.sum_apply]
    simp_rw [CycleQ2NormalExteriorCech.pull_coordinates (c _) b (restriction U x _) (hc _)]
    simp only [LinearEquiv.apply_symm_apply]
    exact (ha s).symm

include hc in
theorem pair_mem (i j : Fin n) (ω : Form k T 2) (hω : IsBoundary U x 2 ω) :
    pair b i j ω ∈ boundaries U x := by
  obtain ⟨α,rfl⟩ := hω
  rw [map_sum]
  apply Submodule.sum_mem
  intro a _
  rw [pair_pull (c a) b (restriction U x a) (hc a)]
  exact face_mem U x a _

include hc in
theorem triple_mem (i j l : Fin n) (ω : Form k T 3) (hω : IsBoundary U x 3 ω) :
    triple b i j l ω ∈ boundaries U x := by
  obtain ⟨α,rfl⟩ := hω
  rw [map_sum]
  apply Submodule.sum_mem
  intro a _
  rw [triple_pull (c a) b (restriction U x a) (hc a)]
  exact face_mem U x a _

include hc in
theorem of_pair_mem (ω : Form k T 2)
    (hω : ∀ i j, pair b i j ω ∈ boundaries U x) : IsBoundary U x 2 ω := by
  apply (iff_coordinates U x b c hc 2 ω).mpr
  intro s
  change (b.exteriorPower 2).coord s ω ∈ boundaries U x
  rw [exterior_coord_pair]
  exact hω _ _

/-- The degree-zero exterior equivalence identifies this boundary image
with the original top scalar Čech image. -/
theorem scalar_iff (a : T) : IsBoundary U x 0 (scalar a) ↔ a ∈ boundaries U x := by
  constructor
  · rintro ⟨α,hα⟩
    choose v hv using fun i => (scalar (k := k) (A := U i)).surjective (α i)
    have he : a = ∑ i, faceToTop U x i (v i) := by
      apply (scalar (k := k) (A := T)).injective
      rw [hα,map_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [← hv i,pull_scalar]
      rfl
    rw [he]
    exact Submodule.sum_mem _ (fun i _ => face_mem U x i (v i))
  · intro ha
    obtain ⟨v,hv⟩ := (mem_boundaries_iff U x a).mp ha
    refine ⟨fun i => scalar (v i),?_⟩
    simp_rw [pull_scalar]
    rw [← map_sum]
    exact congrArg (scalar (k := k) (A := T)) hv.symm

/-- Degree-one boundaries retain the actual Kähler coefficients and the
original face pullbacks. -/
include hc in
theorem one_iff (ω : Ω[T⁄k]) :
    IsBoundary U x 1 (one ω) ↔ ∀ j, b.coord j ω ∈ boundaries U x := by
  classical
  constructor
  · rintro ⟨α,hα⟩ j
    choose β hβ using fun i => (one (k := k) (A := U i)).surjective (α i)
    have he : ω = ∑ i, onePullback (restriction U x i) (β i) := by
      apply (one (k := k) (A := T)).injective
      rw [hα,map_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [← hβ i,pull_one]
    rw [he,map_sum]
    apply Submodule.sum_mem
    intro i _
    rw [coord_pull (c i) b (restriction U x i) (hc i)]
    exact face_mem U x i _
  · intro hω
    choose a ha using fun j => (mem_boundaries_iff U x _).mp (hω j)
    let β (i : ι) : Ω[U i⁄k] := (c i).equivFun.symm (fun j => a j i)
    have he : ω = ∑ i, onePullback (restriction U x i) (β i) := by
      apply b.equivFun.injective
      funext j
      change b.coord j ω = b.coord j _
      rw [map_sum]
      simp_rw [coord_pull (c _) b (restriction U x _) (hc _)]
      simp only [β,Basis.coord_equivFun_symm]
      exact (ha j).symm
    refine ⟨fun i => one (β i),?_⟩
    simp_rw [pull_one]
    rw [← map_sum,← he]

end CycleQ2FinitePrincipalFormBoundary

namespace CycleQ2FiniteNormalChartForms

open Module KaehlerDifferential CycleQ2WeightedCoordinateExterior
open CycleQ2ExactFrameThreeDeRham CycleQ2FrameCurl
open CycleQ2ExactFrameFirstDifferential CycleQ2ArbitraryFrameDifferential
open CycleQ2NormalCechKahler CycleQ2NormalCechFormBoundary
open CycleQ2FinitePrincipalParts CycleQ2FinitePrincipalFormBoundary
open CycleQ2GeometricLocalizedDerivations
open CycleQ2AffineZeroOneForms (scalar one d_scalar)

variable {ι : Type} [Fintype ι] [DecidableEq ι]
    {k R T : Type} [Field k] [CharZero k] [Algebra ℂ k]
    [CommRing R] [CommRing T] [Algebra R T]
    [Algebra k R] [Algebra k T] [IsScalarTower k R T]
    [Algebra ℂ R] [Algebra ℂ T] [IsScalarTower ℂ k R] [IsScalarTower ℂ k T]
    [IsScalarTower ℂ R T]
    (U : ι → Type) [∀ i, CommRing (U i)] [∀ i, Algebra R (U i)]
    [∀ i, Algebra k (U i)] [∀ i, IsScalarTower k R (U i)]
    [∀ i, Algebra ℂ (U i)] [∀ i, IsScalarTower ℂ R (U i)]
    {n : ℕ} (b : Basis (Fin n) R Ω[R⁄k]) (u : Fin n → R)
    (hu : ∀ i, b i = D k R (u i)) (normal : ι → Fin n)

abbrev equations : ι → R := u ∘ normal

variable [∀ i, IsLocalization.Away (faceDenominator (equations u normal) i) (U i)]
    [IsLocalization.Away (denominator (equations u normal)) T]

abbrev topFrame : Basis (Fin n) T Ω[T⁄k] :=
  localFrame (T := T) b (.powers (denominator (equations u normal)))

abbrev faceFrame (i : ι) : Basis (Fin n) (U i) Ω[U i⁄k] :=
  localFrame (T := U i) b (.powers (faceDenominator (equations u normal) i))

include hu in
theorem frame_restrict (i : ι) (j : Fin n) :
    onePullback (restriction U (equations u normal) i) (faceFrame U b u normal i j) =
      topFrame (T := T) b u normal j := by
  rw [frame_exact b u hu _ j,onePullback_d,frame_exact b u hu _ j]
  exact congrArg (D k T) ((faceToTop U (equations u normal) i).commutes (u j))

private abbrev δ (i : Fin n) := (spatialDerivative b i).restrictScalars ℂ

private theorem derivative_extends (i : Fin n) (a : T) :
    localizedDerivation (.powers (denominator (equations u normal))) T (δ b i) a =
      spatialDerivative (topFrame (T := T) b u normal) i a :=
  DFunLike.congr_fun (direction_extends (T := T) b
    (.powers (denominator (equations u normal))) i).symm a

include hu in
private theorem normal_value (i : Fin n) (j : ι) :
    δ b i (equations u normal j) = if normal j = i then 1 else 0 :=
  partial_coordinate b u hu i (normal j)

/-- The actual degree-zero top Čech row has no closed supported function. -/
include hu in
theorem row_zero (s : ι) (ω : Form k T 0)
    (hω : IsBoundary U (equations u normal) 1
      (d (topFrame (T := T) b u normal) 0 ω)) :
    IsBoundary U (equations u normal) 0 ω := by
  let x := equations u normal
  let B := topFrame (T := T) b u normal
  let C := faceFrame U b u normal
  have hC := frame_restrict (T := T) U b u hu normal
  obtain ⟨f,rfl⟩ := (scalar (k := k) (A := T)).surjective ω
  rw [d_scalar] at hω
  have hf := ((one_iff U x B C hC (D k T f)).mp hω) (normal s)
  apply (scalar_iff U x f).mpr
  apply (Submodule.Quotient.mk_eq_zero (boundaries U x)).mp
  apply derivative_injective U x s (δ b (normal s))
    (by simp [x,normal_value b u hu normal])
  rw [map_zero,onParts_mk,Submodule.Quotient.mk_eq_zero]
  rw [derivative_extends]
  exact hf

/-- Closed ordinary one-forms on the full intersection have actual
function primitives modulo the sum of the omitted-face restrictions. -/
include hu in
theorem row_one (s t : ι) (hst : normal s ≠ normal t) (ω : Form k T 1)
    (hω : IsBoundary U (equations u normal) 2
      (d (topFrame (T := T) b u normal) 1 ω)) :
    ∃ f : Form k T 0, IsBoundary U (equations u normal) 1
      (ω - d (topFrame (T := T) b u normal) 0 f) := by
  let x := equations u normal
  let B := topFrame (T := T) b u normal
  let C := faceFrame U b u normal
  let S := boundaries (T := T) U x
  have hC := frame_restrict (T := T) U b u hu normal
  obtain ⟨ω,rfl⟩ := (one (k := k) (A := T)).surjective ω
  let p (i : Fin n) : Parts (T := T) U x := Submodule.Quotient.mk (B.coord i ω)
  have hp (i : Fin n) : onParts U x (δ b i) (p (normal s)) =
      onParts U x (δ b (normal s)) (p i) := by
    have hh := pair_mem U x B C hC i (normal s) _ hω
    rw [first_eq,pair_onOne] at hh
    apply (Submodule.Quotient.eq S).mpr
    change localizedDerivation (.powers (denominator x)) T (δ b i) (B.coord (normal s) ω) -
      localizedDerivation (.powers (denominator x)) T (δ b (normal s)) (B.coord i ω) ∈ S
    rw [derivative_extends,derivative_extends]
    exact hh
  obtain ⟨f,hf⟩ := closed_one_exact U x s t (normal s) (normal t) (δ b)
    (by simp [x,normal_value b u hu normal])
    (by simp [x,normal_value b u hu normal])
    (by simp [x,normal_value b u hu normal,hst,hst.symm])
    (fun i r => partials_commute b u hu i (normal s) r) p hp
  obtain ⟨f,rfl⟩ := Submodule.Quotient.mk_surjective S f
  refine ⟨scalar f,?_⟩
  rw [d_scalar,← map_sub]
  apply (one_iff U x B C hC (ω - D k T f)).mpr
  intro i
  have hi := S.neg_mem ((Submodule.Quotient.eq S).mp (hf i))
  change -(localizedDerivation (.powers (denominator x)) T (δ b i) f - B.coord i ω) ∈ S at hi
  rw [neg_sub,derivative_extends] at hi
  rw [map_sub]
  exact hi

/-- The degree-two exactness needed for codimension-three purity. The
primitive is an ordinary one-form on the actual full intersection, and its
error is a sum of actual two-forms restricted from the double principal opens. -/
include hu in
theorem row_two (s t r : ι)
    (hst : normal s ≠ normal t) (hsr : normal s ≠ normal r) (htr : normal t ≠ normal r)
    (ω : Form k T 2)
    (hω : IsBoundary U (equations u normal) 3
      (d (topFrame (T := T) b u normal) 2 ω)) :
    ∃ α : Form k T 1, IsBoundary U (equations u normal) 2
      (ω - d (topFrame (T := T) b u normal) 1 α) := by
  classical
  let x := equations u normal
  let B := topFrame (T := T) b u normal
  let C := faceFrame U b u normal
  let S := boundaries (T := T) U x
  have hC := frame_restrict (T := T) U b u hu normal
  let p (i j : Fin n) : Parts (T := T) U x := Submodule.Quotient.mk (pair B i j ω)
  have hp (i j : Fin n) : onParts U x (δ b (normal s)) (p i j) =
      onParts U x (δ b i) (p (normal s) j) - onParts U x (δ b j) (p (normal s) i) := by
    have hh := triple_mem U x B C hC (normal s) i j _ hω
    rw [triple_d_two] at hh
    apply (Submodule.Quotient.eq S).mpr
    change localizedDerivation (.powers (denominator x)) T (δ b (normal s)) (pair B i j ω) -
      (localizedDerivation (.powers (denominator x)) T (δ b i) (pair B (normal s) j ω) -
        localizedDerivation (.powers (denominator x)) T (δ b j) (pair B (normal s) i ω)) ∈ S
    rw [derivative_extends,derivative_extends,derivative_extends]
    convert hh using 1 <;> abel
  obtain ⟨f,hf⟩ := closed_two_exact U x s t r (normal s) (normal t) (normal r) (δ b)
    (by simp [x,normal_value b u hu normal])
    (by simp [x,normal_value b u hu normal])
    (by simp [x,normal_value b u hu normal])
    (by simp [x,normal_value b u hu normal,hst,hst.symm])
    (by simp [x,normal_value b u hu normal,hsr,hsr.symm])
    (by simp [x,normal_value b u hu normal,htr,htr.symm])
    (fun i j a => partials_commute b u hu i j a) p hp
  choose v hv using fun i => Submodule.Quotient.mk_surjective S (f i)
  let α := B.equivFun.symm v
  refine ⟨one α,of_pair_mem U x B C hC _ ?_⟩
  intro i j
  have hij := hf i j
  rw [← hv i,← hv j,onParts_mk,onParts_mk] at hij
  change S.mkQ (localizedDerivation (.powers (denominator x)) T (δ b i) (v j)) -
    S.mkQ (localizedDerivation (.powers (denominator x)) T (δ b j) (v i)) =
      S.mkQ (pair B i j ω) at hij
  rw [← map_sub] at hij
  have hh := S.neg_mem ((Submodule.Quotient.eq S).mp hij)
  rw [neg_sub,derivative_extends,derivative_extends] at hh
  rw [map_sub,first_eq,pair_onOne]
  simpa only [α,Basis.coord_equivFun_symm] using hh

/-- The three low rows in any exact frame on the intersection. This is
the ordinary-form input for the genuine supported Ext³ row calculation. -/
include hu in
theorem low_degrees (s t r : ι)
    (hst : normal s ≠ normal t) (hsr : normal s ≠ normal r) (htr : normal t ≠ normal r)
    (B : Basis (Fin n) T Ω[T⁄k]) (v : Fin n → T) (hB : ∀ i, B i = D k T (v i)) :
    (∀ ω : Form k T 0, IsBoundary U (equations u normal) 1 (d B 0 ω) →
      IsBoundary U (equations u normal) 0 ω) ∧
    (∀ ω : Form k T 1, IsBoundary U (equations u normal) 2 (d B 1 ω) →
      ∃ f : Form k T 0, IsBoundary U (equations u normal) 1 (ω - d B 0 f)) ∧
    (∀ ω : Form k T 2, IsBoundary U (equations u normal) 3 (d B 2 ω) →
      ∃ α : Form k T 1, IsBoundary U (equations u normal) 2 (ω - d B 1 α)) := by
  let C := topFrame (T := T) b u normal
  have hC (i : Fin n) : C i = D k T (algebraMap R T (u i)) := frame_exact b u hu _ i
  have he (q : ℕ) (ω : Form k T q) : d B q ω = d C q ω := by
    simpa only [CycleQ2AffineDeRhamFunctorial.exteriorPullback_id] using
      CycleQ2FrameDifferentialNaturality.differential_natural B v hB C
        (fun i => algebraMap R T (u i)) hC (AlgHom.id k T) q ω
  constructor
  · intro ω hω
    rw [he] at hω
    exact row_zero U b u hu normal s ω hω
  constructor
  · intro ω hω
    rw [he] at hω
    obtain ⟨f,hf⟩ := row_one U b u hu normal s t hst ω hω
    exact ⟨f,by rwa [he]⟩
  · intro ω hω
    rw [he] at hω
    obtain ⟨α,hα⟩ := row_two U b u hu normal s t r hst hsr htr ω hω
    exact ⟨α,by rwa [he]⟩

end CycleQ2FiniteNormalChartForms

namespace CycleQ2ThirdCoordinateSaturation

open CycleQ2CechDenominatorTorsion

section Quotient

variable {k R : Type} [Field k] [CharZero k] [CommRing R] [Algebra k R]
    [IsNoetherianRing R] (d : Derivation k R R) (f g h : R)
    (hf : d f = 0) (hg : d g = 0) (hh : d h = 1)

/-- A third exact coordinate is a nonzerodivisor modulo every pair of
powers of the first two equations. The third coordinate derivation descends
to the actual quotient, so no regular-sequence power theorem is assumed. -/
include hf hg hh in
theorem regular_mod_powers (m n : ℕ) :
    IsLeftRegular (Ideal.Quotient.mk (Ideal.span {f ^ m,g ^ n}) h) := by
  let I : Ideal R := Ideal.span {f ^ m,g ^ n}
  let π := Ideal.Quotient.mkₐ k I
  have hfm : π (f ^ m) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr
    (Ideal.subset_span (by simp))
  have hgn : π (g ^ n) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr
    (Ideal.subset_span (by simp))
  have stable (a : R) (ha : π a = 0) : π (d a) = 0 := by
    obtain ⟨u,v,huv⟩ := Ideal.mem_span_pair.mp (Ideal.Quotient.eq_zero_iff_mem.mp ha)
    rw [← huv]
    simp only [map_add,Derivation.leibniz,Derivation.leibniz_pow,hf,hg,
      smul_zero,smul_eq_mul,zero_add,map_mul,hfm,hgn,mul_zero,zero_mul,add_zero,map_zero]
  let d' := Derivation.liftOfSurjective (Ideal.Quotient.mkₐ_surjective k I) stable
  apply CycleQ2RegularPairDifferentiation.isLeftRegular_of_derivative_one d'
  change Derivation.liftOfSurjective _ stable (π h) = 1
  rw [Derivation.liftOfSurjective_apply,hh,map_one]

include hf hg hh in
theorem powers_saturated (m n r : ℕ) (a : R)
    (ha : h ^ r * a ∈ Ideal.span {f ^ m,g ^ n}) :
    a ∈ Ideal.span {f ^ m,g ^ n} := by
  let I : Ideal R := Ideal.span {f ^ m,g ^ n}
  let π := Ideal.Quotient.mk I
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  apply (regular_mod_powers d f g h hf hg hh m n).pow r
  rw [mul_zero,← map_pow,← map_mul,Ideal.Quotient.eq_zero_iff_mem]
  exact ha

end Quotient

section Fractions

variable {R U V T : Type} [CommRing R] [CommRing U] [CommRing V] [CommRing T]
    [Algebra R U] [Algebra R V] [Algebra R T]
    (f g : R) [IsLocalization.Away f U] [IsLocalization.Away g V]
    [IsLocalization.Away (f*g) T]

/-- A genuine pair Čech boundary has a common denominator whose numerator
belongs to the corresponding ideal generated by the two denominator powers. -/
theorem boundary_clears (a : T) (ha : a ∈ boundaries U V T f g) :
    ∃ n : ℕ, ∃ c : R,
      a * algebraMap R T (f*g) ^ n = algebraMap R T c ∧ c ∈ Ideal.span {f ^ n,g ^ n} := by
  obtain ⟨_,⟨u,rfl⟩,_,⟨v,rfl⟩,rfl⟩ := Submodule.mem_sup.mp ha
  obtain ⟨m,c,hc⟩ := IsLocalization.Away.surj f u
  obtain ⟨n,e,he⟩ := IsLocalization.Away.surj g v
  have hc' := congrArg (fromFirst (A := U) (T := T) f g) hc
  have he' := congrArg (fromSecond (B := V) (T := T) f g) he
  simp only [map_mul,map_pow,AlgHom.commutes] at hc' he'
  refine ⟨m+n,c*f^n*g^(m+n)+e*f^(m+n)*g^m,?_,?_⟩
  · calc
      (fromFirst f g u + fromSecond f g v) * algebraMap R T (f*g) ^ (m+n) =
          (fromFirst f g u * algebraMap R T f ^ m) * algebraMap R T f ^ n *
              algebraMap R T g ^ (m+n) +
            (fromSecond f g v * algebraMap R T g ^ n) * algebraMap R T f ^ (m+n) *
              algebraMap R T g ^ m := by
        rw [map_mul,mul_pow]
        simp only [pow_add]
        ring
      _ = algebraMap R T (c*f^n*g^(m+n)+e*f^(m+n)*g^m) := by
        rw [hc',he']
        simp only [map_add,map_mul,map_pow]
  · exact Ideal.mem_span_pair.mpr ⟨e*g^m,c*f^n,by ring⟩

private theorem inverse_fraction {L : Type} [CommRing L] [Algebra R L]
    (x : R) [IsLocalization.Away x L] (a : R) (n : ℕ) :
    (algebraMap R L a * IsLocalization.Away.invSelf x ^ n) * algebraMap R L x ^ n =
      algebraMap R L a := by
  calc
    _ = algebraMap R L a * (algebraMap R L x * IsLocalization.Away.invSelf x) ^ n := by
      rw [mul_pow]
      ring
    _ = algebraMap R L a := by rw [IsLocalization.Away.mul_invSelf,one_pow,mul_one]

/-- The converse denominator calculation supplies literal forms on the
two single opens, rather than merely a formal numerator criterion. -/
theorem boundary_of_clears (a : T) (n : ℕ) (c : R)
    (ha : a * algebraMap R T (f*g) ^ n = algebraMap R T c)
    (hc : c ∈ Ideal.span {f ^ n,g ^ n}) : a ∈ boundaries U V T f g := by
  obtain ⟨b,e,hbe⟩ := Ideal.mem_span_pair.mp hc
  let u : U := algebraMap R U e * IsLocalization.Away.invSelf f ^ n
  let v : V := algebraMap R V b * IsLocalization.Away.invSelf g ^ n
  have hu : fromFirst (A := U) (T := T) f g u * algebraMap R T f ^ n = algebraMap R T e := by
    simpa only [u,map_mul,map_pow,AlgHom.commutes] using
      congrArg (fromFirst (A := U) (T := T) f g) (inverse_fraction (L := U) f e n)
  have hv : fromSecond (B := V) (T := T) f g v * algebraMap R T g ^ n = algebraMap R T b := by
    simpa only [v,map_mul,map_pow,AlgHom.commutes] using
      congrArg (fromSecond (B := V) (T := T) f g) (inverse_fraction (L := V) g b n)
  have he : (fromFirst f g u + fromSecond f g v) * algebraMap R T (f*g) ^ n =
      algebraMap R T c := by
    calc
      _ = (fromFirst f g u * algebraMap R T f ^ n) * algebraMap R T g ^ n +
          (fromSecond f g v * algebraMap R T g ^ n) * algebraMap R T f ^ n := by
        rw [map_mul,mul_pow]
        ring
      _ = algebraMap R T e * algebraMap R T g ^ n +
          algebraMap R T b * algebraMap R T f ^ n := by rw [hu,hv]
      _ = algebraMap R T c := by
        rw [← map_pow,← map_mul,← map_pow,← map_mul,← map_add]
        exact congrArg (algebraMap R T) ((add_comm _ _).trans hbe)
  have hea : a = fromFirst f g u + fromSecond f g v :=
    (IsLocalization.Away.algebraMap_pow_isUnit (S := T) (f*g) n).mul_right_cancel (ha.trans he.symm)
  rw [hea]
  exact Submodule.add_mem_sup ⟨u,rfl⟩ ⟨v,rfl⟩

/-- If a prescribed cleared numerator represents a pair Čech boundary,
it lies in the appropriate ideal after multiplying by a further power of
the original denominator. This retains possible denominator torsion. -/
theorem shifted_numerator_mem (a : T) (n : ℕ) (c : R)
    (ha : a * algebraMap R T (f*g) ^ n = algebraMap R T c)
    (hb : a ∈ boundaries U V T f g) :
    ∃ m : ℕ, (f*g) ^ m * c ∈ Ideal.span {f ^ (n+m),g ^ (n+m)} := by
  obtain ⟨l,e,he,heI⟩ := boundary_clears f g a hb
  have heq : algebraMap R T ((f*g)^l*c) = algebraMap R T ((f*g)^n*e) := by
    rw [map_mul,map_pow,map_mul,map_pow,← ha,← he]
    ring
  obtain ⟨r,hr⟩ := IsLocalization.Away.exists_of_eq (f*g) heq
  obtain ⟨b,d,hbd⟩ := Ideal.mem_span_pair.mp heI
  refine ⟨l+r,Ideal.mem_span_pair.mpr ⟨b*g^(n+r),d*f^(n+r),?_⟩⟩
  calc
    b*g^(n+r)*f^(n+(l+r)) + d*f^(n+r)*g^(n+(l+r)) = (f*g)^r*((f*g)^n*e) := by
      rw [← hbd]
      simp only [pow_add,mul_pow]
      ring
    _ = (f*g)^r*((f*g)^l*c) := hr.symm
    _ = (f*g)^(l+r)*c := by rw [pow_add]; ring

end Fractions

section Saturation

variable {k R U V T : Type} [Field k] [CharZero k]
    [CommRing R] [Algebra k R] [IsNoetherianRing R]
    [CommRing U] [CommRing V] [CommRing T]
    [Algebra R U] [Algebra R V] [Algebra R T]
    (f g h : R) [IsLocalization.Away f U] [IsLocalization.Away g V]
    [IsLocalization.Away (f*g) T]
    (d : Derivation k R R) (hf : d f = 0) (hg : d g = 0) (hh : d h = 1)

/-- The third coordinate has no torsion on the actual top Čech module
of the first two principal opens. This is the scalar injectivity input
for the augmented three-open Čech row. -/
include hf hg hh in
theorem pair_boundary_saturated (a : T) (r : ℕ)
    (ha : h ^ r • a ∈ boundaries U V T f g) : a ∈ boundaries U V T f g := by
  obtain ⟨n,c,hc⟩ := IsLocalization.Away.surj (f*g) a
  have hclear : (h^r • a) * algebraMap R T (f*g)^n = algebraMap R T (h^r*c) := by
    rw [Algebra.smul_def,mul_assoc,hc,map_mul]
  obtain ⟨m,hm⟩ := shifted_numerator_mem f g (h^r • a) n (h^r*c) hclear ha
  have hm' : h^r*((f*g)^m*c) ∈ Ideal.span {f^(n+m),g^(n+m)} := by
    convert hm using 1 <;> ring
  have hnum := powers_saturated d f g h hf hg hh (n+m) (n+m) r ((f*g)^m*c) hm'
  apply boundary_of_clears f g a (n+m) ((f*g)^m*c) _ hnum
  calc
    a * algebraMap R T (f*g) ^ (n+m) =
        (a * algebraMap R T (f*g)^n) * algebraMap R T (f*g)^m := by rw [pow_add]; ring
    _ = algebraMap R T ((f*g)^m*c) := by rw [hc,map_mul,map_pow]; ring

end Saturation
end CycleQ2ThirdCoordinateSaturation

namespace CycleQ2ThirdCoordinateRestriction

open CycleQ2CechDenominatorTorsion CycleQ2ThirdCoordinateSaturation

section Refinement

variable {R A B : Type} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (x h : R)
    [IsLocalization.Away x A] [IsLocalization.Away (x*h) B]

/-- A section on a twice localized open clears a power of the added
coordinate into an actual section of the original principal open. -/
theorem clears_refinement (b : B) :
    ∃ n : ℕ, ∃ a : A, fromFirst x h a = h ^ n • b := by
  obtain ⟨n,c,hc⟩ := IsLocalization.Away.surj (x*h) b
  rw [map_mul] at hc
  have he := CycleQ2CechDenominatorTorsion.clears_other (a := h) (t := x)
    (fromFirst (A := A) (T := B) x h) b n c (by
      simpa only [mul_comm (algebraMap R B h) (algebraMap R B x)] using hc)
  obtain ⟨a,ha⟩ := he
  exact ⟨n,a,ha⟩

/-- The actual map from `R[1/x]` to `R[1/(xh)]` has exactly the
expected added-coordinate torsion kernel, even when the original ring
has zero divisors. -/
theorem kernel_clears (φ : A →ₐ[R] B) (a : A) (ha : φ a = 0) :
    ∃ n : ℕ, h ^ n • a = 0 := by
  obtain ⟨m,c,hc⟩ := IsLocalization.Away.surj x a
  have hc' := congrArg φ hc
  simp only [map_mul,map_pow,AlgHom.commutes,ha,zero_mul] at hc'
  obtain ⟨n,hn⟩ := IsLocalization.Away.exists_of_eq (x*h)
    (hc'.symm.trans (map_zero (algebraMap R B)).symm)
  rw [mul_zero] at hn
  have hz : algebraMap R A h ^ n * algebraMap R A c = 0 := by
    apply (IsLocalization.Away.algebraMap_pow_isUnit (S := A) x n).mul_left_cancel
    rw [mul_zero]
    simpa only [map_mul,map_pow,mul_pow,map_zero,mul_assoc] using
      congrArg (algebraMap R A) hn
  refine ⟨n,?_⟩
  rw [Algebra.smul_def,map_pow]
  apply (IsLocalization.Away.algebraMap_pow_isUnit (S := A) x m).mul_right_cancel
  rw [zero_mul,mul_assoc,hc]
  exact hz

end Refinement

section Pair

variable {k R U V A P Q Z : Type} [Field k] [CharZero k]
    [CommRing R] [Algebra k R] [IsNoetherianRing R]
    [CommRing U] [CommRing V] [CommRing A] [CommRing P] [CommRing Q] [CommRing Z]
    [Algebra R U] [Algebra R V] [Algebra R A]
    [Algebra R P] [Algebra R Q] [Algebra R Z]
    (f g h : R)
    [IsLocalization.Away f U] [IsLocalization.Away g V]
    [IsLocalization.Away (f*g) A]
    [IsLocalization.Away (f*h) P] [IsLocalization.Away (g*h) Q]
    [IsLocalization.Away ((f*g)*h) Z]
    (d : Derivation k R R) (hf : d f = 0) (hg : d g = 0) (hh : d h = 1)

private theorem localization_algHom_unique {S L : Type} [CommRing S] [CommRing L]
    [Algebra R S] [Algebra R L] (a : R) [IsLocalization.Away a S]
    (φ ψ : S →ₐ[R] L) : φ = ψ := by
  apply IsLocalization.algHom_ext (R := R) (A := R) (.powers a)
  ext r
  simp only [AlgHom.comp_apply,IsScalarTower.coe_toAlgHom,AlgHom.commutes]

/-- Restriction from the two-equation Čech cokernel to the complement
where the third coordinate is invertible is injective. The three maps
in the statement are the actual ring restrictions; their compatibility
is proved from their original localization universal properties. -/
include hf hg hh in
theorem pair_boundary_of_refinement (α : A →ₐ[R] Z) (β : P →ₐ[R] Z) (γ : Q →ₐ[R] Z)
    (a : A) (p : P) (q : Q) (ha : α a = β p + γ q) :
    a ∈ boundaries U V A f g := by
  obtain ⟨m,u,hu⟩ := clears_refinement (A := U) f h p
  obtain ⟨n,v,hv⟩ := clears_refinement (A := V) g h q
  let u' : U := h^n • u
  let v' : V := h^m • v
  have hu' : fromFirst (A := U) (T := P) f h u' = h^(m+n) • p := by
    change fromFirst f h (h^n • u) = _
    rw [map_smul,hu,smul_smul,pow_add]
    congr 1
    exact mul_comm _ _
  have hv' : fromFirst (A := V) (T := Q) g h v' = h^(m+n) • q := by
    change fromFirst g h (h^m • v) = _
    rw [map_smul,hv,smul_smul,pow_add]
  have ku (b : U) : α (fromFirst f g b) = β (fromFirst f h b) :=
    AlgHom.congr_fun (localization_algHom_unique f
      (α.comp (fromFirst (A := U) f g)) (β.comp (fromFirst (A := U) f h))) b
  have kv (b : V) : α (fromSecond f g b) = γ (fromFirst g h b) :=
    AlgHom.congr_fun (localization_algHom_unique g
      (α.comp (fromSecond (B := V) f g)) (γ.comp (fromFirst (A := V) g h))) b
  let b : A := fromFirst f g u' + fromSecond f g v'
  have hb : b ∈ boundaries U V A f g := Submodule.add_mem_sup ⟨u',rfl⟩ ⟨v',rfl⟩
  have hz : α (h^(m+n) • a - b) = 0 := by
    change α (h^(m+n) • a - (fromFirst f g u' + fromSecond f g v')) = 0
    rw [map_sub,map_smul,ha,smul_add,map_add,ku,kv,hu',hv',map_smul,map_smul,sub_self]
  obtain ⟨r,hr⟩ := kernel_clears (f*g) h α (h^(m+n) • a - b) hz
  have he : h^r • (h^(m+n) • a) = h^r • b := by
    apply sub_eq_zero.mp
    simpa only [smul_sub] using hr
  have hs : h^(r+(m+n)) • a ∈ boundaries U V A f g := by
    rw [pow_add,mul_smul,he]
    exact Submodule.smul_mem _ (h^r) hb
  exact pair_boundary_saturated f g h d hf hg hh a (r+(m+n)) hs

end Pair
end CycleQ2ThirdCoordinateRestriction

namespace CycleQ2ExactFrameThirdCoordinate

open Module KaehlerDifferential CycleQ2ExactFrameFirstDifferential
open CycleQ2CechDenominatorTorsion
open CycleQ2NormalCechKahler CycleQ2NormalCechFormBoundary
open CycleQ2WeightedCoordinateExterior CycleQ2ExactFrameThreeDeRham

variable {k R : Type} [Field k] [CharZero k] [CommRing R] [Algebra k R]
    [IsNoetherianRing R] {n : ℕ}
    (b : Basis (Fin n) R Ω[R⁄k]) (u : Fin n → R)
    (hu : ∀ i, b i = D k R (u i)) (i j l : Fin n) (hil : i ≠ l) (hjl : j ≠ l)

/-- The saturation uses the original derivative dual to the third exact
coordinate, which annihilates both earlier normal coordinates. -/
include hu hil hjl in
theorem regular_mod_powers (a c : ℕ) :
    IsLeftRegular (Ideal.Quotient.mk (Ideal.span {(u i)^a,(u j)^c}) (u l)) :=
  CycleQ2ThirdCoordinateSaturation.regular_mod_powers (spatialDerivative b l)
    (u i) (u j) (u l)
    (by simp [partial_coordinate b u hu,hil])
    (by simp [partial_coordinate b u hu,hjl])
    (by simp [partial_coordinate b u hu]) a c

include hu in
private theorem local_frame_pull {S T : Type} [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra k S] [Algebra k T]
    [IsScalarTower k R S] [IsScalarTower k R T]
    (M N : Submonoid R) [IsLocalization M S] [IsLocalization N T]
    (φ : S →ₐ[R] T) (a : Fin n) :
    onePullback (φ.restrictScalars k) (localFrame (T := S) b M a) =
      localFrame (T := T) b N a := by
  rw [frame_exact b u hu M a,onePullback_d,frame_exact b u hu N a]
  exact congrArg (D k T) (φ.commutes (u a))

section Pair

variable {U V A : Type} [CommRing U] [CommRing V] [CommRing A]
    [Algebra R U] [Algebra R V] [Algebra R A]
    [IsLocalization.Away (u i) U] [IsLocalization.Away (u j) V]
    [IsLocalization.Away (u i*u j) A]

include hu hil hjl in
theorem pair_boundary_saturated (a : A) (r : ℕ)
    (ha : (u l)^r • a ∈ boundaries U V A (u i) (u j)) :
    a ∈ boundaries U V A (u i) (u j) :=
  CycleQ2ThirdCoordinateSaturation.pair_boundary_saturated (u i) (u j) (u l)
    (spatialDerivative b l)
    (by simp [partial_coordinate b u hu,hil])
    (by simp [partial_coordinate b u hu,hjl])
    (by simp [partial_coordinate b u hu]) a r ha

variable {P Q Z : Type} [CommRing P] [CommRing Q] [CommRing Z]
    [Algebra R P] [Algebra R Q] [Algebra R Z]
    [IsLocalization.Away (u i*u l) P] [IsLocalization.Away (u j*u l) Q]
    [IsLocalization.Away ((u i*u j)*u l) Z]

/-- Actual restriction injectivity on the first pair Čech cokernel in
an adapted triple chart. This is the lower-row input for the outer
Mayer–Vietoris square of the three principal opens. -/
include hu hil hjl in
theorem pair_boundary_of_refinement
    (α : A →ₐ[R] Z) (β : P →ₐ[R] Z) (γ : Q →ₐ[R] Z)
    (a : A) (p : P) (q : Q) (ha : α a = β p + γ q) :
    a ∈ boundaries U V A (u i) (u j) :=
  CycleQ2ThirdCoordinateRestriction.pair_boundary_of_refinement (u i) (u j) (u l)
    (spatialDerivative b l)
    (by simp [partial_coordinate b u hu,hil])
    (by simp [partial_coordinate b u hu,hjl])
    (by simp [partial_coordinate b u hu]) α β γ a p q ha

variable [Algebra k U] [Algebra k V] [Algebra k A]
    [Algebra k P] [Algebra k Q] [Algebra k Z]
    [IsScalarTower k R U] [IsScalarTower k R V] [IsScalarTower k R A]
    [IsScalarTower k R P] [IsScalarTower k R Q] [IsScalarTower k R Z]

/-- The same restriction injectivity for the original ordinary exterior
forms in every degree. It returns actual forms on the two original single
opens, with the signed Čech boundary used by the supported Ext row. -/
include hu hil hjl in
theorem forms_boundary_of_refinement
    (α : A →ₐ[R] Z) (β : P →ₐ[R] Z) (γ : Q →ₐ[R] Z)
    (q : ℕ) (ω : Form k A q) (η : Form k P q) (ν : Form k Q q)
    (hω : exteriorPullback (α.restrictScalars k) q ω =
      exteriorPullback (β.restrictScalars k) q η + exteriorPullback (γ.restrictScalars k) q ν) :
    CycleQ2NormalCechFormBoundary.IsBoundary
      ((fromFirst (A := U) (T := A) (u i) (u j)).restrictScalars k)
      ((fromSecond (B := V) (T := A) (u i) (u j)).restrictScalars k) q ω := by
  classical
  let bU := localFrame (T := U) b (.powers (u i))
  let bV := localFrame (T := V) b (.powers (u j))
  let bA := localFrame (T := A) b (.powers (u i*u j))
  let bP := localFrame (T := P) b (.powers (u i*u l))
  let bQ := localFrame (T := Q) b (.powers (u j*u l))
  let bZ := localFrame (T := Z) b (.powers ((u i*u j)*u l))
  have hα := local_frame_pull b u hu (.powers (u i*u j)) (.powers ((u i*u j)*u l)) α
  have hβ := local_frame_pull b u hu (.powers (u i*u l)) (.powers ((u i*u j)*u l)) β
  have hγ := local_frame_pull b u hu (.powers (u j*u l)) (.powers ((u i*u j)*u l)) γ
  have hU := local_frame_pull b u hu (.powers (u i)) (.powers (u i*u j))
    (fromFirst (A := U) (T := A) (u i) (u j))
  have hV := local_frame_pull b u hu (.powers (u j)) (.powers (u i*u j))
    (fromSecond (B := V) (T := A) (u i) (u j))
  have coeff (s : Set.powersetCard (Fin n) q) :
      (bA.exteriorPower q).equivFun ω s ∈ boundaries U V A (u i) (u j) := by
    have hs := congrArg (fun z => (bZ.exteriorPower q).equivFun z s) hω
    rw [CycleQ2NormalExteriorCech.pull_coordinates bA bZ _ hα,
      map_add,Pi.add_apply,CycleQ2NormalExteriorCech.pull_coordinates bP bZ _ hβ,
      CycleQ2NormalExteriorCech.pull_coordinates bQ bZ _ hγ] at hs
    exact pair_boundary_of_refinement b u hu i j l hil hjl α β γ
      ((bA.exteriorPower q).equivFun ω s) ((bP.exteriorPower q).equivFun η s)
      ((bQ.exteriorPower q).equivFun ν s) hs
  have reps (s : Set.powersetCard (Fin n) q) : ∃ a : U, ∃ c : V,
      fromFirst (u i) (u j) a + fromSecond (u i) (u j) c = (bA.exteriorPower q).equivFun ω s := by
    obtain ⟨_,⟨a,rfl⟩,_,⟨c,rfl⟩,hc⟩ := Submodule.mem_sup.mp (coeff s)
    exact ⟨a,c,hc⟩
  choose a c hc using reps
  refine ⟨(bU.exteriorPower q).equivFun.symm a,-(bV.exteriorPower q).equivFun.symm c,?_⟩
  apply (bA.exteriorPower q).equivFun.injective
  funext s
  rw [map_sub,Pi.sub_apply,CycleQ2NormalExteriorCech.pull_coordinates bU bA _ hU,
    CycleQ2NormalExteriorCech.pull_coordinates bV bA _ hV,
    map_neg,Pi.neg_apply,LinearEquiv.apply_symm_apply,LinearEquiv.apply_symm_apply,
    map_neg,sub_neg_eq_add]
  exact (hc s).symm

end Pair
end CycleQ2ExactFrameThirdCoordinate
