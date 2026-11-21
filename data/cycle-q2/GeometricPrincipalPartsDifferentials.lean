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
