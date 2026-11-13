import HodgeComputer.Constructions.EllipticCompanions.CompanionAlgebra
import HodgeComputer.Constructions.HoldoutCover.FiniteDifferentials
import HodgeComputer.Constructions.HoldoutCover.FiniteTrace
import HodgeComputer.Constructions.HoldoutCover.Piola
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.PartialFractions
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.Tactic

/-!
Target-independent algebra extracted from the accepted crossed-ternary proof
by GitHub contributor `1337isnot1337`. Original declarations and namespaces
are retained. The accepted application imports the maintained shared modules.

The source explanation credits fqlx's moving-conic/Fermat-cover construction,
Benjamin Diamond's maintained library extraction, the project contributors,
classical elliptic-curve/residue methods, Lean/mathlib, and OpenAI Codex.
This extraction was prepared with Codex assistance for fqlx.

This module supplies reusable steps; it asserts no new instance certificate.
-/

/- Source component: RationalResidue. -/
section

/- Rational one-form residues for the proposed elliptic contraction.
   No certificate is asserted by these intermediate lemmas. -/
noncomputable section
open scoped LaurentSeries PowerSeries
namespace CrossedRationalResidue
open Polynomial
variable {K : Type*} [Field K]

local instance : Algebra ℤ (RatFunc K) := Ring.toIntAlgebra _

local instance : Algebra (RatFunc K) (LaurentSeries K) :=
  RatFunc.liftAlgebra K (LaurentSeries K)
local instance : IsScalarTower K[X] (RatFunc K) (LaurentSeries K) :=
  RatFunc.isScalarTower_liftAlgebra K (LaurentSeries K)

def shift (a : K) : RatFunc K ≃ₐ[K] RatFunc K :=
  IsFractionRing.algEquivOfAlgEquiv (Polynomial.algEquivAevalXAddC a)

def expansion (a : K) : RatFunc K →+* LaurentSeries K :=
  (algebraMap (RatFunc K) (LaurentSeries K)).comp (shift a).toRingHom

lemma shift_polynomial (a : K) (P : K[X]) :
    shift a (algebraMap K[X] (RatFunc K) P) =
      algebraMap K[X] (RatFunc K) (P.comp (X+C a)) := by
  change IsFractionRing.algEquivOfAlgEquiv _ _ = _
  rw [IsFractionRing.algEquivOfAlgEquiv_algebraMap]
  rfl

lemma expansion_polynomial (a : K) (P : K[X]) :
    expansion a (algebraMap K[X] (RatFunc K) P) =
      (((P.comp (X+C a) : K[X]) : PowerSeries K) : LaurentSeries K) := by
  change algebraMap (RatFunc K) (LaurentSeries K)
    (shift a (algebraMap K[X] (RatFunc K) P)) = _
  rw [shift_polynomial]
  exact (RatFunc.coe_coe (P.comp (X+C a))).symm

lemma expansion_C (a c : K) :
    expansion a (RatFunc.C c) = HahnSeries.C c := by
  change expansion a (algebraMap K[X] (RatFunc K) (C c)) = _
  rw [expansion_polynomial]
  simp

def residue (a : K) : RatFunc K →ₗ[K] K where
  toFun f := (expansion a f).coeff (-1)
  map_add' f g := by simp
  map_smul' c f := by
    rw [RatFunc.smul_eq_C_mul, map_mul, expansion_C]
    simp [smul_eq_mul]

def uniformizer (a : K) : RatFunc K :=
  algebraMap K[X] (RatFunc K) (X-C a)

lemma expansion_uniformizer (a : K) :
    expansion a (uniformizer a) = HahnSeries.single 1 1 := by
  rw [uniformizer, expansion_polynomial]
  simp

lemma residue_inverse_power (a : K) (n : ℕ) :
    residue a ((uniformizer a)^n)⁻¹ = if n=1 then 1 else 0 := by
  change (expansion a ((uniformizer a)^n)⁻¹).coeff (-1) = _
  rw [map_inv₀, map_pow, expansion_uniformizer, HahnSeries.single_pow,
    HahnSeries.inv_single]
  simp only [one_pow, inv_one, nsmul_eq_mul, mul_one, HahnSeries.coeff_single]
  have h : ((-1 : ℤ) = -(n : ℤ)) ↔ n=1 := by omega
  simp only [h]

lemma residue_polynomial (a : K) (P : K[X]) :
    residue a (algebraMap K[X] (RatFunc K) P)=0 := by
  change (expansion a (algebraMap K[X] (RatFunc K) P)).coeff (-1)=0
  rw [expansion_polynomial]
  simp [PowerSeries.coeff_coe]

lemma residue_div_polynomials (a : K) (P Q : K[X]) (hQ : Q.eval a ≠ 0) :
    residue a (algebraMap K[X] (RatFunc K) P /
      algebraMap K[X] (RatFunc K) Q) = 0 := by
  let P0 : PowerSeries K := (P.comp (X+C a) : K[X])
  let Q0 : PowerSeries K := (Q.comp (X+C a) : K[X])
  have hq0 : PowerSeries.constantCoeff Q0 = Q.eval a := by
    simp [Q0, Polynomial.coeff_zero_eq_eval_zero]
  have hu : IsUnit Q0 := PowerSeries.isUnit_iff_constantCoeff.mpr (by
    rw [hq0]
    exact isUnit_iff_ne_zero.mpr hQ)
  have hqn : (Q0 : LaurentSeries K) ≠ 0 :=
    (hu.map (HahnSeries.ofPowerSeries ℤ K)).ne_zero
  obtain ⟨U, hU⟩ := hu
  have hi : (((↑(U⁻¹) : PowerSeries K)) : LaurentSeries K) =
      (Q0 : LaurentSeries K)⁻¹ := by
    apply mul_right_cancel₀ hqn
    rw [inv_mul_cancel₀ hqn, ← PowerSeries.coe_mul, ← hU]
    simp
  change (expansion a (algebraMap K[X] (RatFunc K) P /
    algebraMap K[X] (RatFunc K) Q)).coeff (-1) = 0
  rw [map_div₀, expansion_polynomial, expansion_polynomial]
  change ((P0 : LaurentSeries K)/(Q0 : LaurentSeries K)).coeff (-1)=0
  rw [div_eq_mul_inv, ← hi, ← PowerSeries.coe_mul]
  rw [PowerSeries.coeff_coe]
  norm_num

/-- A rational function is regular at `a` when it has a denominator nonzero there. -/
def RegularAt (a : K) (f : RatFunc K) : Prop :=
  ∃ P Q : K[X], Q.eval a ≠ 0 ∧
    f = algebraMap K[X] (RatFunc K) P / algebraMap K[X] (RatFunc K) Q

lemma RegularAt.residue_eq_zero {a : K} {f : RatFunc K} (h : RegularAt a f) :
    residue a f = 0 := by
  obtain ⟨P,Q,hQ,rfl⟩ := h
  exact residue_div_polynomials a P Q hQ

lemma RegularAt.polynomial (a : K) (P : K[X]) :
    RegularAt a (algebraMap K[X] (RatFunc K) P) := by
  exact ⟨P,1,by simp,by simp⟩

lemma polynomialMap_ne_zero {P : K[X]} (hP : P ≠ 0) :
    algebraMap K[X] (RatFunc K) P ≠ 0 := by
  intro h
  apply hP
  apply IsFractionRing.injective K[X] (RatFunc K)
  simpa using h

lemma RegularAt.add {a : K} {f g : RatFunc K}
    (hf : RegularAt a f) (hg : RegularAt a g) : RegularAt a (f+g) := by
  obtain ⟨P,Q,hQ,rfl⟩ := hf
  obtain ⟨R,S,hS,rfl⟩ := hg
  refine ⟨P*S+R*Q,Q*S,by simpa using mul_ne_zero hQ hS,?_⟩
  have hq : algebraMap K[X] (RatFunc K) Q ≠ 0 := by
    apply polynomialMap_ne_zero
    intro h; apply hQ; simp [h]
  have hs : algebraMap K[X] (RatFunc K) S ≠ 0 := by
    apply polynomialMap_ne_zero
    intro h; apply hS; simp [h]
  simp only [map_add,map_mul]
  field_simp

lemma uniformizer_ne_zero (a : K) : uniformizer a ≠ 0 := by
  apply polynomialMap_ne_zero
  exact (monic_X_sub_C a).ne_zero

/-- Finite lists of principal terms; exponent `n` means a pole of order `n+1`. -/
def poleSum (a : K) : List (K × ℕ) → RatFunc K
  | [] => 0
  | (c,n)::terms => RatFunc.C c * ((uniformizer a)^(n+1))⁻¹ + poleSum a terms

lemma div_uniformizer_power_decomposition (a : K) (n : ℕ) (P : K[X]) :
    ∃ g : RatFunc K, ∃ terms : List (K × ℕ), RegularAt a g ∧
      algebraMap K[X] (RatFunc K) P / (uniformizer a)^n = g + poleSum a terms := by
  induction n generalizing P with
  | zero => exact ⟨_,[],RegularAt.polynomial a P,by simp [poleSum]⟩
  | succ n ih =>
    obtain ⟨g,terms,hg,he⟩ := ih (P /ₘ (X-C a))
    refine ⟨g,(P.eval a,n)::terms,hg,?_⟩
    have hp := congrArg (algebraMap K[X] (RatFunc K))
      (modByMonic_add_div P (X-C a))
    rw [modByMonic_X_sub_C_eq_C_eval] at hp
    simp only [map_add,map_mul] at hp
    change RatFunc.C (P.eval a) + uniformizer a *
      algebraMap K[X] (RatFunc K) (P /ₘ (X-C a)) =
      algebraMap K[X] (RatFunc K) P at hp
    simp only [poleSum]
    rw [add_left_comm g,← he]
    rw [← hp]
    have hu := uniformizer_ne_zero a
    field_simp
    ring

/-- Every rational function has a finite principal part at any given rational point. -/
lemma exists_regular_add_poleSum (a : K) (f : RatFunc K) :
    ∃ g : RatFunc K, ∃ terms : List (K × ℕ), RegularAt a g ∧
      f = g + poleSum a terms := by
  induction f using RatFunc.induction_on with
  | f P Q hQ =>
    obtain ⟨R,hR,hnd⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd Q hQ a
    have hr : R.eval a ≠ 0 := by
      simpa only [dvd_iff_isRoot,IsRoot] using hnd
    have hcop : IsCoprime (X-C a : K[X]) R := by
      exact ((irreducible_X_sub_C a).isCoprime_or_dvd R).resolve_right hnd
    obtain ⟨U,V,hUV⟩ := hcop.pow_left (m := Q.rootMultiplicity a)
    obtain ⟨g,terms,hg,he⟩ :=
      div_uniformizer_power_decomposition a (Q.rootMultiplicity a) (P*V)
    let r : RatFunc K := algebraMap K[X] (RatFunc K) (P*U) /
      algebraMap K[X] (RatFunc K) R
    have hreg : RegularAt a r := ⟨P*U,R,hr,rfl⟩
    refine ⟨r+g,terms,hreg.add hg,?_⟩
    rw [add_assoc,← he]
    have hR0 : algebraMap K[X] (RatFunc K) R ≠ 0 := by
      apply polynomialMap_ne_zero
      intro h; apply hr; simp [h]
    have hu := uniformizer_ne_zero a
    have huv := congrArg (algebraMap K[X] (RatFunc K)) hUV
    simp only [map_add,map_mul,map_pow,map_one] at huv
    change _ * (uniformizer a)^_ + _ * _ = 1 at huv
    conv_lhs => rw [hR,map_mul,map_pow]
    change _ / ((uniformizer a)^_ * _) = _
    dsimp [r]
    simp only [map_mul]
    field_simp [hu,hR0]
    linear_combination -(algebraMap K[X] (RatFunc K) P)*huv

lemma RegularAt.derivation {a : K} {f : RatFunc K}
    (hf : RegularAt a f) (D : Derivation ℤ (RatFunc K) (RatFunc K))
    (hpoly : ∀ P : K[X], ∃ Q : K[X],
      D (algebraMap K[X] (RatFunc K) P) = algebraMap K[X] (RatFunc K) Q) :
    RegularAt a (D f) := by
  obtain ⟨P,Q,hQ,rfl⟩ := hf
  obtain ⟨P',hP'⟩ := hpoly P
  obtain ⟨Q',hQ'⟩ := hpoly Q
  refine ⟨Q*P'-P*Q',Q^2,by simpa using pow_ne_zero 2 hQ,?_⟩
  rw [D.leibniz_div,hP',hQ']
  simp only [map_sub,map_mul,map_pow,smul_eq_mul,div_eq_mul_inv]
  ring

lemma residue_term (a c : K) (n : ℕ) :
    residue a (RatFunc.C c * ((uniformizer a)^(n+1))⁻¹) =
      if n=0 then c else 0 := by
  rw [← RatFunc.smul_eq_C_mul,map_smul,residue_inverse_power]
  by_cases hn : n=0 <;> simp [hn]

lemma derivation_inverse_power (D : Derivation ℤ (RatFunc K) (RatFunc K))
    (z : RatFunc K) (hz : z ≠ 0) (n : ℕ) :
    D ((z^(n+1))⁻¹) = -(n+1 : RatFunc K) * D z * (z^(n+2))⁻¹ := by
  rw [D.leibniz_inv,D.leibniz_pow]
  simp only [smul_eq_mul,nsmul_eq_mul,Nat.cast_add,Nat.cast_one,Nat.add_sub_cancel]
  field_simp
  simp only [pow_succ]
  ring

lemma residue_derivation_term (a c k : K) (n : ℕ)
    (D : Derivation ℤ (RatFunc K) (RatFunc K)) (δ : Derivation ℤ K K)
    (hC : ∀ c, D (RatFunc.C c) = RatFunc.C (δ c))
    (hU : D (uniformizer a) = RatFunc.C k) :
    residue a (D (RatFunc.C c * ((uniformizer a)^(n+1))⁻¹)) =
      δ (residue a (RatFunc.C c * ((uniformizer a)^(n+1))⁻¹)) := by
  have he : D (RatFunc.C c * ((uniformizer a)^(n+1))⁻¹) =
      RatFunc.C (δ c) * ((uniformizer a)^(n+1))⁻¹ -
      RatFunc.C (c*(n+1)*k) * ((uniformizer a)^(n+2))⁻¹ := by
    rw [D.leibniz,derivation_inverse_power D _ (uniformizer_ne_zero a),hC,hU]
    simp only [map_mul,map_add,map_natCast,map_one,smul_eq_mul]
    ring
  rw [he,map_sub,residue_term]
  have hzero := residue_term a (c*(n+1)*k) (n+1)
  rw [show n+1+1=n+2 by omega] at hzero
  rw [hzero,if_neg (by omega : n+1 ≠ 0),sub_zero,residue_term]
  by_cases hn : n=0 <;> simp [hn]

/-- Residues commute with a base derivation even when the pole moves.
The hypothesis on the uniformizer allows its derivative to be any constant. -/
lemma residue_derivation (a k : K)
    (D : Derivation ℤ (RatFunc K) (RatFunc K)) (δ : Derivation ℤ K K)
    (hC : ∀ c, D (RatFunc.C c) = RatFunc.C (δ c))
    (hU : D (uniformizer a) = RatFunc.C k)
    (hpoly : ∀ P : K[X], ∃ Q : K[X],
      D (algebraMap K[X] (RatFunc K) P) = algebraMap K[X] (RatFunc K) Q)
    (f : RatFunc K) : residue a (D f) = δ (residue a f) := by
  obtain ⟨g,terms,hg,rfl⟩ := exists_regular_add_poleSum a f
  rw [map_add,map_add,map_add,(hg.derivation D hpoly).residue_eq_zero,
    hg.residue_eq_zero,zero_add,zero_add]
  induction terms with
  | nil => simp [poleSum]
  | cons t terms ih =>
    rcases t with ⟨c,n⟩
    simp only [poleSum,map_add]
    rw [residue_derivation_term a c k n D δ hC hU,ih]

end CrossedRationalResidue
end
end

/- Source component: RationalDerivation. -/
section

noncomputable section
namespace CrossedRationalResidue
open Polynomial
variable {K : Type*} [Field K]

local instance : Algebra ℤ (RatFunc K) := Ring.toIntAlgebra _

lemma derivation_polynomial_closed
    (D : Derivation ℤ (RatFunc K) (RatFunc K)) (δ : Derivation ℤ K K) (s : K)
    (hC : ∀ c, D (RatFunc.C c) = RatFunc.C (δ c))
    (hX : D RatFunc.X = RatFunc.C s) (P : K[X]) :
    ∃ Q : K[X], D (algebraMap K[X] (RatFunc K) P) =
      algebraMap K[X] (RatFunc K) Q := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    obtain ⟨P',hP'⟩ := hP
    obtain ⟨Q',hQ'⟩ := hQ
    exact ⟨P'+Q',by rw [map_add,map_add,hP',hQ',map_add]⟩
  | monomial n c =>
    refine ⟨C (δ c)*X^n + C (c*n*s)*X^(n-1),?_⟩
    rw [← C_mul_X_pow_eq_monomial]
    simp only [map_add,map_mul,map_pow,RatFunc.algebraMap_C,RatFunc.algebraMap_X,
      D.leibniz,D.leibniz_pow,hC,hX,smul_eq_mul,nsmul_eq_mul,map_natCast]
    ring

lemma residue_derivation_of_constants (a s : K)
    (D : Derivation ℤ (RatFunc K) (RatFunc K)) (δ : Derivation ℤ K K)
    (hC : ∀ c, D (RatFunc.C c) = RatFunc.C (δ c))
    (hX : D RatFunc.X = RatFunc.C s) (f : RatFunc K) :
    residue a (D f) = δ (residue a f) := by
  apply residue_derivation a (s-δ a) D δ hC
  · simp only [uniformizer,map_sub,RatFunc.algebraMap_X,RatFunc.algebraMap_C,hX,hC]
  · exact derivation_polynomial_closed D δ s hC hX

lemma residue_exact_derivative (a : K)
    (D : Derivation ℤ (RatFunc K) (RatFunc K))
    (hC : ∀ c, D (RatFunc.C c) = 0)
    (hX : D RatFunc.X = 1) (f : RatFunc K) : residue a (D f) = 0 := by
  have hc : ∀ c, D (RatFunc.C c) = RatFunc.C ((0 : Derivation ℤ K K) c) := by
    simpa using hC
  have hx : D RatFunc.X = RatFunc.C (1 : K) := by simpa using hX
  simpa using residue_derivation_of_constants a 1 D 0 hc hx f

end CrossedRationalResidue
end
end

/- Source component: RationalGlobalResidue. -/
section

noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
namespace CrossedRationalResidue
open Polynomial
variable {K : Type*} [Field K]

lemma transcendental_inverse_X : Transcendental K (RatFunc.X⁻¹ : RatFunc K) := by
  intro h
  exact RatFunc.transcendental_X (IsAlgebraic.inv_iff.mp h)

def reciprocal : RatFunc K →ₐ[K] RatFunc K :=
  IsFractionRing.liftAlgHom (transcendental_iff_injective.mp
    (transcendental_inverse_X (K := K)))

lemma reciprocal_polynomial (P : K[X]) :
    reciprocal (algebraMap K[X] (RatFunc K) P) =
      aeval (RatFunc.X⁻¹ : RatFunc K) P := by
  exact IsFractionRing.lift_algebraMap
    (transcendental_iff_injective.mp (transcendental_inverse_X (K := K))) P

lemma reciprocal_C (c : K) : reciprocal (RatFunc.C c) = RatFunc.C c := by
  change reciprocal (algebraMap K (RatFunc K) c) = _
  exact (reciprocal (K := K)).commutes c

lemma reciprocal_X : reciprocal (RatFunc.X : RatFunc K) = RatFunc.X⁻¹ := by
  rw [← RatFunc.algebraMap_X,reciprocal_polynomial]
  exact aeval_X _

lemma uniformizer_zero : uniformizer (0 : K) = RatFunc.X := by
  simp [uniformizer,RatFunc.algebraMap_X]

lemma X_ne_zero : (RatFunc.X : RatFunc K) ≠ 0 := by
  simpa only [uniformizer_zero] using uniformizer_ne_zero (0 : K)

/-- The coefficient of `X⁻¹` at infinity. Its negative is the residue at infinity. -/
def infinityCoefficient : RatFunc K →ₗ[K] K where
  toFun f := residue 0 ((RatFunc.X^2)⁻¹ * reciprocal f)
  map_add' f g := by simp [mul_add]
  map_smul' c f := by
    simp only [map_smul]
    rw [mul_smul_comm,map_smul]
    rfl

lemma infinityCoefficient_polynomial (P : K[X]) :
    infinityCoefficient (algebraMap K[X] (RatFunc K) P) = 0 := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ => simp only [map_add,hP,hQ,add_zero]
  | monomial n c =>
    have he : (RatFunc.X^2)⁻¹ *
        reciprocal (algebraMap K[X] (RatFunc K) (monomial n c)) =
        RatFunc.C c * (RatFunc.X^(n+2))⁻¹ := by
      rw [← C_mul_X_pow_eq_monomial,map_mul,map_pow,RatFunc.algebraMap_C,
        RatFunc.algebraMap_X,map_mul,map_pow,reciprocal_C,reciprocal_X]
      simp only [pow_add,mul_inv_rev,inv_pow]
      ring
    change residue (K := K) 0 _ = 0
    rw [he]
    have h := residue_term (0 : K) c (n+1)
    rw [show n+1+1=n+2 by omega] at h
    simpa only [uniformizer_zero,if_neg (by omega : n+1 ≠ 0)] using h

lemma reciprocal_uniformizer (a : K) :
    reciprocal (uniformizer a) =
      (1-RatFunc.C a*RatFunc.X)/RatFunc.X := by
  simp only [uniformizer,map_sub,RatFunc.algebraMap_X,RatFunc.algebraMap_C,
    reciprocal_X,reciprocal_C]
  field_simp [X_ne_zero]

lemma one_sub_C_mul_X_ne_zero (a : K) :
    (1-RatFunc.C a*RatFunc.X : RatFunc K) ≠ 0 := by
  have hp : (1-C a*X : K[X]).eval 0 ≠ 0 := by simp
  have : (1-C a*X : K[X]) ≠ 0 := by intro h; simp [h] at hp
  simpa using polynomialMap_ne_zero this

lemma infinityCoefficient_term (a c : K) (n : ℕ) :
    infinityCoefficient (RatFunc.C c*((uniformizer a)^(n+1))⁻¹) =
      if n=0 then c else 0 := by
  cases n with
  | zero =>
    have he : (RatFunc.X^2)⁻¹ *
        reciprocal (RatFunc.C c*((uniformizer a)^(0+1))⁻¹) =
        RatFunc.C c*(RatFunc.X)⁻¹ +
        RatFunc.C (c*a)/(1-RatFunc.C a*RatFunc.X) := by
      simp only [map_mul,map_inv₀,map_pow,reciprocal_C,reciprocal_uniformizer]
      simp only [div_pow,inv_div]
      have hL : (1-RatFunc.X*RatFunc.C a : RatFunc K) ≠ 0 := by
        simpa only [mul_comm] using one_sub_C_mul_X_ne_zero a
      field_simp [X_ne_zero,one_sub_C_mul_X_ne_zero,hL]
      ring
    change residue (K := K) 0 _ = _
    rw [he,map_add]
    have hr : RegularAt (0 : K)
        (RatFunc.C (c*a)/(1-RatFunc.C a*RatFunc.X)) := by
      exact ⟨C (c*a),1-C a*X,by simp,by simp⟩
    rw [hr.residue_eq_zero,add_zero]
    simpa only [uniformizer_zero,zero_add,pow_one,if_pos rfl] using residue_term (0 : K) c 0
  | succ n =>
    have he : (RatFunc.X^2)⁻¹ *
        reciprocal (RatFunc.C c*((uniformizer a)^(n+1+1))⁻¹) =
        algebraMap K[X] (RatFunc K) (C c*X^n) /
        algebraMap K[X] (RatFunc K) ((1-C a*X)^(n+2)) := by
      simp only [map_mul,map_pow,map_sub,map_one,RatFunc.algebraMap_C,
        RatFunc.algebraMap_X,map_inv₀,reciprocal_C,reciprocal_uniformizer]
      rw [show n+1+1=n+2 by omega]
      simp only [div_pow,inv_div]
      field_simp [X_ne_zero,one_sub_C_mul_X_ne_zero]
      simp only [pow_succ]
      ring
    change residue (K := K) 0 _ = _
    rw [he,residue_div_polynomials (hQ := by simp)]
    simp

end CrossedRationalResidue
end
end

/- Source component: EllipticFunctionField. -/
section

noncomputable section
set_option maxHeartbeats 400000
namespace CrossedElliptic
open Polynomial
variable (K : Type*) [Field K]

def W : WeierstrassCurve.Affine K := ⟨0,0,0,0,-432⟩
def equation : (RatFunc K)[X] :=
  (W K).polynomial.map (algebraMap K[X] (RatFunc K))

lemma equation_irreducible : Irreducible (equation K) := by
  exact ((WeierstrassCurve.Affine.monic_polynomial (W := W K)).irreducible_iff_irreducible_map_fraction_map (K := RatFunc K)).mp
      (WeierstrassCurve.Affine.irreducible_polynomial (W := W K))

instance : Fact (Irreducible (equation K)) := ⟨equation_irreducible K⟩
abbrev E := AdjoinRoot (equation K)

lemma equation_eq : equation K = X^2-C ((RatFunc.X : RatFunc K)^3-432) := by
  norm_num [equation,W,WeierstrassCurve.Affine.polynomial,RatFunc.C,-RatFunc.algebraMap_eq_C]
  rw [show (algebraMap K (RatFunc K)) (432 : K) = (432 : RatFunc K) from
    map_natCast _ 432]
  ring

lemma equation_monic : (equation K).Monic := by
  exact (WeierstrassCurve.Affine.monic_polynomial (W := W K)).map _

instance : FiniteDimensional (RatFunc K) (E K) :=
  Module.Finite.of_basis (AdjoinRoot.powerBasis' (equation_monic K)).basis

instance : Algebra K (E K) := inferInstance
instance : IsScalarTower K (RatFunc K) (E K) := inferInstance

def x : E K := algebraMap (RatFunc K) (E K) RatFunc.X
def y : E K := AdjoinRoot.root (equation K)

lemma relation : (y K)^2 = (x K)^3-432 := by
  have he := AdjoinRoot.eval₂_root (equation K)
  change (equation K).eval₂ (algebraMap (RatFunc K) (E K)) (y K) = 0 at he
  conv_lhs at he => arg 3; rw [equation_eq]
  simp only [Polynomial.eval₂_sub,Polynomial.eval₂_pow,Polynomial.eval₂_X,
    Polynomial.eval₂_C,Polynomial.eval₂_ofNat,map_sub,map_pow,map_ofNat] at he
  exact sub_eq_zero.mp he

lemma x_ne_zero : x K ≠ 0 := by
  simpa only [x,map_zero] using
    (algebraMap (RatFunc K) (E K)).injective.ne
      (CrossedRationalResidue.X_ne_zero (K := K))

end CrossedElliptic
end
end

/- Source component: EllipticDifferentials. -/
section

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace CrossedElliptic
open Polynomial HoldoutConstruction
variable {K : Type*} [Field K] [CharZero K]

local instance : Algebra ℤ (RatFunc K) := Ring.toIntAlgebra _

instance : CharZero (E K) :=
  charZero_of_injective_ringHom (f := algebraMap K (E K))
    (algebraMap K (E K)).injective

local instance : Algebra ℤ (E K) := Ring.toIntAlgebra _

def baseTime : Derivation ℤ (RatFunc K) (RatFunc K) :=
  extendRingDerivation (L := RatFunc K) (timePolynomialDerivation (E := K))

def baseCoefficient (D : Derivation ℤ K K) : Derivation ℤ (RatFunc K) (RatFunc K) :=
  extendRingDerivation (L := RatFunc K) (coefficientPolynomialDerivation D)

omit [CharZero K] in
lemma baseTime_C (c : K) : baseTime (RatFunc.C c) = 0 := by
  change baseTime (algebraMap K[X] (RatFunc K) (C c)) = 0
  rw [baseTime,extendRingDerivation_apply]
  simp [timePolynomialDerivation_apply]
omit [CharZero K] in
lemma baseTime_X : baseTime (RatFunc.X : RatFunc K) = 1 := by
  change baseTime (algebraMap K[X] (RatFunc K) X) = 1
  rw [baseTime,extendRingDerivation_apply]
  simp [timePolynomialDerivation_apply]
omit [CharZero K] in
lemma baseCoefficient_C (D : Derivation ℤ K K) (c : K) :
    baseCoefficient D (RatFunc.C c) = RatFunc.C (D c) := by
  change baseCoefficient D (algebraMap K[X] (RatFunc K) (C c)) = _
  rw [baseCoefficient,extendRingDerivation_apply]
  simp
omit [CharZero K] in
lemma baseCoefficient_X (D : Derivation ℤ K K) :
    baseCoefficient D (RatFunc.X : RatFunc K) = 0 := by
  change baseCoefficient D (algebraMap K[X] (RatFunc K) X) = 0
  rw [baseCoefficient,extendRingDerivation_apply]
  simp

def time : Derivation ℤ (E K) (E K) := extendFiniteDerivation (K := RatFunc K) (L := E K) (baseTime (K := K))
def coefficient (D : Derivation ℤ K K) : Derivation ℤ (E K) (E K) :=
  extendFiniteDerivation (K := RatFunc K) (L := E K) (baseCoefficient D)

lemma time_base (f : RatFunc K) :
    time (K := K) (algebraMap (RatFunc K) (E K) f) =
      algebraMap (RatFunc K) (E K) (baseTime (K := K) f) :=
  extendFiniteDerivation_apply _ _
lemma coefficient_base (D : Derivation ℤ K K) (f : RatFunc K) :
    coefficient D (algebraMap (RatFunc K) (E K) f) =
      algebraMap (RatFunc K) (E K) (baseCoefficient D f) :=
  extendFiniteDerivation_apply _ _

lemma time_x : time (K := K) (x K) = 1 := by
  change time (K := K) (algebraMap (RatFunc K) (E K) RatFunc.X) = 1
  rw [time_base,baseTime_X,map_one]
lemma coefficient_x (D : Derivation ℤ K K) : coefficient D (x K) = 0 := by
  change coefficient D (algebraMap (RatFunc K) (E K) RatFunc.X) = 0
  rw [coefficient_base,baseCoefficient_X,map_zero]

lemma y_ne_zero : y K ≠ 0 := by
  have hp : (X^3-C (432 : K) : K[X]) ≠ 0 := by
    intro h
    have hc := congrArg (fun P : K[X] => P.coeff 3) h
    norm_num at hc
  have hn := CrossedRationalResidue.polynomialMap_ne_zero hp
  have hnon := (algebraMap (RatFunc K) (E K)).injective.ne hn
  have he : algebraMap (RatFunc K) (E K)
      (algebraMap K[X] (RatFunc K) (X^3-C (432 : K))) = (x K)^3-432 := by
    simp only [map_sub,map_pow,RatFunc.algebraMap_X,RatFunc.algebraMap_C]
    rw [map_ofNat,map_ofNat]
    rfl
  rw [he,map_zero] at hnon
  intro hy
  apply hnon
  rw [← relation K,hy,zero_pow (by decide)]

lemma time_y : time (K := K) (y K) = 3*(x K)^2/(2*y K) := by
  have h := congrArg (time (K := K)) (relation K)
  simp only [Derivation.leibniz_pow,map_sub,time_x,
    smul_eq_mul,nsmul_eq_mul] at h
  have hc : time (K := K) (432 : E K) = 0 := (time (K := K)).map_natCast 432
  rw [hc] at h
  norm_num at h
  apply (eq_div_iff (mul_ne_zero (by norm_num) (y_ne_zero (K := K)))).mpr
  linear_combination h

lemma coefficient_y (D : Derivation ℤ K K) : coefficient D (y K) = 0 := by
  have h := congrArg (coefficient D) (relation K)
  simp only [Derivation.leibniz_pow,map_sub,coefficient_x,
    smul_eq_mul,nsmul_eq_mul] at h
  have hc : coefficient D (432 : E K) = 0 := (coefficient D).map_natCast 432
  rw [hc] at h
  norm_num at h
  exact h.resolve_left (y_ne_zero (K := K))

lemma residue_time (a : K) (f : RatFunc K) :
    CrossedRationalResidue.residue a (baseTime (K := K) f) = 0 :=
  CrossedRationalResidue.residue_exact_derivative a baseTime baseTime_C baseTime_X f
lemma residue_coefficient (a : K) (D : Derivation ℤ K K) (f : RatFunc K) :
    CrossedRationalResidue.residue a (baseCoefficient D f) =
      D (CrossedRationalResidue.residue a f) :=
  CrossedRationalResidue.residue_derivation_of_constants a 0 (baseCoefficient D) D
    (baseCoefficient_C D) (by simpa using baseCoefficient_X D) f

end CrossedElliptic
end
end

/- Source component: RationalPartialFractions. -/
section

noncomputable section
open scoped BigOperators
namespace CrossedRationalResidue
open Polynomial
variable {K : Type*} [Field K]

lemma eq_constant_of_degree_lt_linear (a : K) (P : K[X])
    (hP : P.degree < (X-C a).degree) : P = C (P.coeff 0) := by
  by_cases hz : P=0
  · simp [hz]
  have hn : P.natDegree < 1 :=
    (natDegree_lt_iff_degree_lt hz).mpr (by simpa using hP)
  exact eq_C_of_natDegree_eq_zero (by omega)

/-- Finite partial fractions with constant principal coefficients.
The splitting hypothesis can be obtained in a finite splitting field. -/
lemma exists_global_principal_parts (f : RatFunc K)
    (hsplit : f.denom.Splits) :
    ∃ (s : Finset K) (n : K → ℕ) (c : (a : K) → Fin (n a) → K) (P : K[X]),
      f = algebraMap K[X] (RatFunc K) P + ∑ a ∈ s, ∑ j : Fin (n a),
        RatFunc.C (c a j) * ((uniformizer a)^(j.val+1))⁻¹ := by
  classical
  let Q := f.denom
  let lc := Q.leadingCoeff
  have hlc : lc ≠ 0 := leadingCoeff_ne_zero.mpr f.denom_ne_zero
  let s := Q.roots.toFinset
  let n : K → ℕ := fun a => Q.rootMultiplicity a
  have hq : Q = C lc * ∏ a ∈ s, (X-C a)^n a := by
    calc Q = C lc * (Q.roots.map (fun a => X-C a)).prod := hsplit.eq_prod_roots
         _ = _ := by rw [prod_multiset_root_eq_finset_root]
  have hpair : Set.Pairwise (↑s : Set K) (fun a b => IsCoprime (X-C a) (X-C b)) := by
    intro a ha b hb hab
    exact pairwise_coprime_X_sub_C (fun x y h => h) hab
  have hinv (a : K) (ha : a ∈ s) :
      ((uniformizer a)⁻¹) * algebraMap K[X] (RatFunc K) (X-C a) = 1 := by
    exact inv_mul_cancel₀ (uniformizer_ne_zero a)
  obtain ⟨P,r,hr,he⟩ :=
    mul_prod_pow_inverse_eq_quo_add_sum_rem_mul_pow_inverse
      (K := RatFunc K) (C lc⁻¹*f.num)
      (fun a (_ : a ∈ s) => monic_X_sub_C a) hpair n hinv
  refine ⟨s,n,fun a j => (r a j).coeff 0,P,?_⟩
  have heleft : algebraMap K[X] (RatFunc K) (C lc⁻¹*f.num) *
      ∏ a ∈ s, ((uniformizer a)⁻¹)^n a = f := by
    conv_rhs => rw [← f.num_div_denom]
    conv_rhs => rw [show f.denom = Q from rfl,hq]
    simp only [map_mul,map_prod,map_pow,RatFunc.algebraMap_C]
    change _ = _ / (RatFunc.C lc * ∏ a ∈ s, (uniformizer a)^n a)
    simp only [inv_pow,← Finset.prod_inv_distrib,div_eq_mul_inv,mul_inv_rev,
      map_inv₀]
    ring
  rw [heleft] at he
  rw [he]
  congr 1
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro j hj
  rw [eq_constant_of_degree_lt_linear a _ (hr a ha j)]
  simp only [RatFunc.algebraMap_C,inv_pow]

end CrossedRationalResidue
end
end

/- Source component: RationalResidueSum. -/
section

noncomputable section
open scoped BigOperators
namespace CrossedRationalResidue
open Polynomial
variable {K : Type*} [Field K]

lemma residue_term_other (a b c : K) (n : ℕ) (hab : a ≠ b) :
    residue a (RatFunc.C c*((uniformizer b)^(n+1))⁻¹) = 0 := by
  apply RegularAt.residue_eq_zero
  refine ⟨C c,(X-C b)^(n+1),?_,?_⟩
  · simpa using pow_ne_zero (n+1) (sub_ne_zero.mpr hab)
  · simp [div_eq_mul_inv,uniformizer]

lemma sum_residue_term (s : Finset K) (b c : K) (n : ℕ) (hb : b ∈ s) :
    (∑ a ∈ s, residue a (RatFunc.C c*((uniformizer b)^(n+1))⁻¹)) =
      infinityCoefficient (RatFunc.C c*((uniformizer b)^(n+1))⁻¹) := by
  classical
  rw [Finset.sum_eq_single b,residue_term,infinityCoefficient_term]
  · intro a ha hab
    exact residue_term_other a b c n hab
  · exact fun h => (h hb).elim

/-- The sum of all finite residues is the coefficient of `X⁻¹` at infinity. -/
lemma exists_finite_residue_sum (f : RatFunc K) (hsplit : f.denom.Splits) :
    ∃ s : Finset K, (∀ a ∉ s, residue a f = 0) ∧
      ∑ a ∈ s, residue a f = infinityCoefficient f := by
  classical
  obtain ⟨s,n,c,P,hf⟩ := exists_global_principal_parts f hsplit
  refine ⟨s,?_,?_⟩
  · intro a ha
    rw [hf,map_add,residue_polynomial,zero_add]
    simp only [map_sum]
    apply Finset.sum_eq_zero
    intro b hb
    apply Finset.sum_eq_zero
    intro j hj
    apply residue_term_other
    intro h
    exact ha (h ▸ hb)
  · rw [hf,map_add,infinityCoefficient_polynomial,zero_add]
    simp only [map_add,map_sum,residue_polynomial,zero_add]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b hb
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    exact sum_residue_term s b (c b j) j.val hb

/-- A finite set containing every pole can be enlarged without changing the sum. -/
lemma residue_sum_eq_infinity (f : RatFunc K) (hsplit : f.denom.Splits)
    (s : Finset K) (houtside : ∀ a ∉ s, residue a f = 0) :
    ∑ a ∈ s, residue a f = infinityCoefficient f := by
  classical
  obtain ⟨t,ht,he⟩ := exists_finite_residue_sum f hsplit
  rw [← he]
  calc
    ∑ a ∈ s, residue a f = ∑ a ∈ s ∪ t, residue a f := by
      exact Finset.sum_subset Finset.subset_union_left
        (fun a ha has => houtside a has)
    _ = ∑ a ∈ t, residue a f := by
      exact (Finset.sum_subset Finset.subset_union_right
        (fun a ha hat => ht a hat)).symm

end CrossedRationalResidue
end
end

/- Source component: EllipticResidues. -/
section

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace CrossedElliptic
open Polynomial HoldoutConstruction
open scoped BigOperators
variable {K : Type*} [Field K] [CharZero K]
local instance : Algebra ℤ (RatFunc K) := Ring.toIntAlgebra _
local instance : Algebra ℤ (E K) := Ring.toIntAlgebra _

/-- Unnormalized finite trace also commutes with compatible derivations. -/
lemma trace_derivation_finite
    {F L : Type*} [Field F] [Field L] [CharZero F] [Algebra F L]
    [FiniteDimensional F L]
    (D : Derivation ℤ F F) (D' : Derivation ℤ L L)
    (h : ∀ a, D' (algebraMap F L a) = algebraMap F L (D a)) (f : L) :
    Algebra.trace F L (D' f) = D (Algebra.trace F L f) := by
  have hn : (Module.finrank F L : F) ≠ 0 :=
    Nat.cast_ne_zero.mpr (ne_of_gt (Module.finrank_pos (R := F) (M := L)))
  have ht := finiteNormalizedTrace_derivation D D' h f
  simp only [Algebra.normalizedTrace_eq_of_finiteDimensional_apply,smul_eq_mul] at ht
  rw [D.leibniz,D.leibniz_inv,D.map_natCast,smul_zero] at ht
  simp only [smul_eq_mul,mul_zero,add_zero] at ht
  exact mul_left_cancel₀ (inv_ne_zero hn) ht

/-- The invariant elliptic vector field corresponding to omega=da/b^2. -/
def delta : Derivation ℤ (E K) (E K) := (-y K/3) • time (K := K)

/-- Trace of a rational elliptic one-form to the x-line: omega=-3 dx/y. -/
def differentialTrace : E K →ₗ[K] RatFunc K :=
  ((Algebra.trace (RatFunc K) (E K)).restrictScalars K).comp
    (LinearMap.mulLeft K (-3/y K))

omit [CharZero K] in
lemma differentialTrace_apply (f : E K) :
    differentialTrace f = Algebra.trace (RatFunc K) (E K) ((-3/y K)*f) := rfl

lemma differentialTrace_delta (f : E K) :
    differentialTrace (delta f) = baseTime (K := K)
      (Algebra.trace (RatFunc K) (E K) f) := by
  rw [differentialTrace_apply]
  have he : (-3/y K)*delta (K := K) f = time (K := K) f := by
    simp only [delta,Derivation.smul_apply,smul_eq_mul]
    field_simp [y_ne_zero (K := K)]
  rw [he]
  exact trace_derivation_finite (baseTime (K := K)) (time (K := K)) time_base f

lemma coefficient_density (D : Derivation ℤ K K) :
    coefficient D (-3/y K) = 0 := by
  rw [Derivation.leibniz_div,coefficient_y]
  have hc : coefficient D (-3 : E K) = 0 := by
    rw [map_neg]
    exact neg_eq_zero.mpr ((coefficient D).map_natCast 3)
  rw [hc,smul_zero,smul_zero,sub_self,smul_zero]

lemma differentialTrace_coefficient (D : Derivation ℤ K K) (f : E K) :
    differentialTrace (coefficient D f) =
      baseCoefficient D (differentialTrace f) := by
  simp only [differentialTrace_apply]
  rw [← trace_derivation_finite (baseCoefficient D) (coefficient D)
    (coefficient_base D)]
  rw [Derivation.leibniz,coefficient_density,smul_zero,add_zero,smul_eq_mul]

/-- Residues above a finite set of x-coordinates, including all conjugate branches. -/
def residueAt (a : K) : E K →ₗ[K] K :=
  (CrossedRationalResidue.residue a).comp differentialTrace

def residueOn (s : Finset K) : E K →ₗ[K] K := ∑ a ∈ s, residueAt a

lemma residueAt_delta (a : K) (f : E K) : residueAt a (delta f) = 0 := by
  change CrossedRationalResidue.residue a (differentialTrace (delta (K := K) f)) = 0
  rw [differentialTrace_delta,residue_time]

lemma residueAt_coefficient (a : K) (D : Derivation ℤ K K) (f : E K) :
    residueAt a (coefficient D f) = D (residueAt a f) := by
  change CrossedRationalResidue.residue a (differentialTrace (coefficient D f)) = _
  rw [differentialTrace_coefficient,residue_coefficient]
  rfl

lemma residueOn_delta (s : Finset K) (f : E K) : residueOn s (delta f) = 0 := by
  simp only [residueOn,LinearMap.sum_apply,residueAt_delta,Finset.sum_const_zero]

lemma residueOn_coefficient (s : Finset K) (D : Derivation ℤ K K) (f : E K) :
    residueOn s (coefficient D f) = D (residueOn s f) := by
  simp only [residueOn,LinearMap.sum_apply,map_sum,residueAt_coefficient]

end CrossedElliptic
end
end

/- Source component: RationalLocalValue. -/
section

noncomputable section
open scoped LaurentSeries PowerSeries
namespace CrossedRationalResidue
open Polynomial
variable {K : Type*} [Field K]
local instance : Algebra ℤ (RatFunc K) := Ring.toIntAlgebra _
local instance : Algebra (RatFunc K) (LaurentSeries K) :=
  RatFunc.liftAlgebra K (LaurentSeries K)
local instance : IsScalarTower K[X] (RatFunc K) (LaurentSeries K) :=
  RatFunc.isScalarTower_liftAlgebra K (LaurentSeries K)

def valueAt (a : K) : RatFunc K →ₗ[K] K where
  toFun f := (expansion a f).coeff 0
  map_add' f g := by simp
  map_smul' c f := by
    rw [RatFunc.smul_eq_C_mul,map_mul,expansion_C]
    simp [smul_eq_mul]

lemma valueAt_div_polynomials (a : K) (P Q : K[X]) (hQ : Q.eval a ≠ 0) :
    valueAt a (algebraMap K[X] (RatFunc K) P /
      algebraMap K[X] (RatFunc K) Q) = P.eval a / Q.eval a := by
  let P0 : PowerSeries K := (P.comp (X+C a) : K[X])
  let Q0 : PowerSeries K := (Q.comp (X+C a) : K[X])
  have hp0 : PowerSeries.constantCoeff P0 = P.eval a := by
    simp [P0,Polynomial.coeff_zero_eq_eval_zero]
  have hq0 : PowerSeries.constantCoeff Q0 = Q.eval a := by
    simp [Q0,Polynomial.coeff_zero_eq_eval_zero]
  have hu : IsUnit Q0 := PowerSeries.isUnit_iff_constantCoeff.mpr (by
    rw [hq0]
    exact isUnit_iff_ne_zero.mpr hQ)
  have hqn : (Q0 : LaurentSeries K) ≠ 0 :=
    (hu.map (HahnSeries.ofPowerSeries ℤ K)).ne_zero
  obtain ⟨U,hU⟩ := hu
  have hi : (((↑(U⁻¹) : PowerSeries K)) : LaurentSeries K) =
      (Q0 : LaurentSeries K)⁻¹ := by
    apply mul_right_cancel₀ hqn
    rw [inv_mul_cancel₀ hqn,← PowerSeries.coe_mul,← hU]
    simp
  have hic : PowerSeries.constantCoeff (↑(U⁻¹) : PowerSeries K) = (Q.eval a)⁻¹ := by
    apply mul_right_cancel₀ hQ
    rw [inv_mul_cancel₀ hQ,← hq0,← map_mul,← hU]
    simp
  change (expansion a (algebraMap K[X] (RatFunc K) P /
    algebraMap K[X] (RatFunc K) Q)).coeff 0 = _
  rw [map_div₀,expansion_polynomial,expansion_polynomial]
  change ((P0 : LaurentSeries K)/(Q0 : LaurentSeries K)).coeff 0 = _
  rw [div_eq_mul_inv,← hi,← PowerSeries.coe_mul,PowerSeries.coeff_coe]
  norm_num only
  simp only [ite_false]
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]
  rw [map_mul,hp0,hic,div_eq_mul_inv]

lemma residue_div_uniformizer (a : K) (f : RatFunc K) :
    residue a (f/uniformizer a) = valueAt a f := by
  change (expansion a (f/uniformizer a)).coeff (-1) = (expansion a f).coeff 0
  rw [map_div₀,expansion_uniformizer,div_eq_mul_inv,HahnSeries.inv_single,
    HahnSeries.coeff_mul_single]
  simp

lemma residue_div_uniformizer_sq (a : K) (D : Derivation ℤ (RatFunc K) (RatFunc K))
    (hC : ∀ c, D (RatFunc.C c) = 0) (hX : D RatFunc.X = 1) (f : RatFunc K) :
    residue a (f/(uniformizer a)^2) = valueAt a (D f) := by
  have hu : D (uniformizer a) = 1 := by
    simp only [uniformizer,map_sub,RatFunc.algebraMap_X,RatFunc.algebraMap_C,hX,hC,sub_zero]
  have he : D (f/uniformizer a) = D f/uniformizer a-f/(uniformizer a)^2 := by
    rw [D.leibniz_div,hu]
    simp only [smul_eq_mul,mul_one]
    field_simp [uniformizer_ne_zero a]
  have hr := residue_exact_derivative a D hC hX (f/uniformizer a)
  rw [he,map_sub,residue_div_uniformizer] at hr
  exact (sub_eq_zero.mp hr).symm

end CrossedRationalResidue
end
end

/- Source component: EllipticLinearDescent. -/
section

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace CrossedElliptic
open HoldoutConstruction CrossedRationalResidue Polynomial
open scoped BigOperators
variable {K : Type*} [Field K] [CharZero K]
local instance : Algebra ℤ (RatFunc K) := Ring.toIntAlgebra _
local instance : Algebra ℤ (E K) := Ring.toIntAlgebra _

/-- Constant Laurent coefficient is a linear retraction of the constant field.
No regularity at the expansion point is required. -/
def rationalConstantTerm : RatFunc K →ₗ[K] K :=
  (residue (K:=K) 0).comp (LinearMap.mulRight K (RatFunc.X)⁻¹)

omit [CharZero K] in
lemma rationalConstantTerm_apply (f : RatFunc K) :
    rationalConstantTerm f=residue (K:=K) 0 (f/RatFunc.X) := by
  simp only [rationalConstantTerm,LinearMap.comp_apply,LinearMap.mulRight_apply,div_eq_mul_inv]

lemma rationalConstantTerm_C (c : K) : rationalConstantTerm (RatFunc.C c)=c := by
  rw [rationalConstantTerm_apply]
  have hu : uniformizer (0 : K)=RatFunc.X := by simp [uniformizer]
  rw [← hu,div_eq_mul_inv]
  rw [← RatFunc.smul_eq_C_mul]
  rw [map_smul]
  have hr := residue_inverse_power (0 : K) 1
  simp only [pow_one,ite_true] at hr
  rw [hr,smul_eq_mul,mul_one]

lemma rationalConstantTerm_derivation (D : Derivation ℤ K K) (f : RatFunc K) :
    rationalConstantTerm (baseCoefficient D f)=D (rationalConstantTerm f) := by
  rw [rationalConstantTerm_apply,rationalConstantTerm_apply]
  have hx : baseCoefficient D (RatFunc.X : RatFunc K)=0 := baseCoefficient_X D
  have he : baseCoefficient D (f/RatFunc.X)=(baseCoefficient D f)/RatFunc.X := by
    rw [Derivation.leibniz_div,hx,smul_zero,sub_zero,smul_eq_mul]
    simp only [Algebra.smul_def,Algebra.algebraMap_self,RingHom.id_apply]
    field_simp [RatFunc.X_ne_zero]
  rw [← he,residue_coefficient]

/-- Linear descent through an independent generic elliptic constant.
This is not a field homomorphism and does not require specialization. -/
def ellipticConstantTerm : E K →ₗ[K] K :=
  rationalConstantTerm.comp ((Algebra.normalizedTrace (RatFunc K) (E K)).restrictScalars K)

lemma ellipticConstantTerm_base (c : K) :
    ellipticConstantTerm (algebraMap K (E K) c)=c := by
  change rationalConstantTerm (Algebra.normalizedTrace (RatFunc K) (E K)
    (algebraMap (RatFunc K) (E K) (RatFunc.C c)))=c
  rw [Algebra.normalizedTrace_algebraMap_apply_eq_self,rationalConstantTerm_C]

lemma ellipticConstantTerm_derivation (D : Derivation ℤ K K) (f : E K) :
    ellipticConstantTerm (coefficient D f)=D (ellipticConstantTerm f) := by
  change rationalConstantTerm (Algebra.normalizedTrace (RatFunc K) (E K)
    (coefficient D f))=D _
  rw [finiteNormalizedTrace_derivation (baseCoefficient D) (coefficient D) (coefficient_base D),
    rationalConstantTerm_derivation]
  rfl

theorem firstOrder_descends_generic_elliptic {ι : Type*} [Fintype ι]
    (D : ι → Derivation ℤ K K) (c : ι → K) (r : K) (w : ι → E K)
    (h : (∑ i,(coefficient (D i) (w i)+algebraMap K (E K) (c i)*w i))=
      algebraMap K (E K) r) :
    ∃ v : ι → K,(∑ i,(D i (v i)+c i*v i))=r := by
  refine ⟨fun i => ellipticConstantTerm (w i),?_⟩
  have he := congrArg ellipticConstantTerm h
  simp only [map_sum,map_add,ellipticConstantTerm_derivation,ellipticConstantTerm_base] at he
  have hm (i : ι) : ellipticConstantTerm (algebraMap K (E K) (c i)*w i)=
      c i*ellipticConstantTerm (w i) := by
    simpa only [Algebra.smul_def,smul_eq_mul,Algebra.algebraMap_self,RingHom.id_apply] using
      (ellipticConstantTerm (K:=K)).map_smul (c i) (w i)
  simp only [hm] at he
  exact he

end CrossedElliptic
end
end

/- Source component: RadialResidueDescent. -/
section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000
namespace CrossedRadialResidue
open CrossedElliptic HoldoutConstruction CrossedRationalResidue
open scoped BigOperators
variable {K : Type*} [Field K] [CharZero K]
local instance : Algebra ℤ (RatFunc K) := Ring.toIntAlgebra _

def coneDerivations (D : Fin 3 → Derivation ℤ K K) (c : Fin 3 → K) :
    Fin 4 → Derivation ℤ (RatFunc K) (RatFunc K) :=
  ![(RatFunc.X : RatFunc K)⁻¹ • baseCoefficient (D 0),
    (baseTime (K:=K))-(RatFunc.C (c 0)/RatFunc.X) • baseCoefficient (D 0)-
      (2*RatFunc.C (c 1)/RatFunc.X) • baseCoefficient (D 1)-
      (2*RatFunc.C (c 2)/RatFunc.X) • baseCoefficient (D 2),
    ((RatFunc.X : RatFunc K)^2)⁻¹ • baseCoefficient (D 1),
    ((RatFunc.X : RatFunc K)^2)⁻¹ • baseCoefficient (D 2)]

def projectedField (c : Fin 3 → K) (w : Fin 4 → RatFunc K) : Fin 3 → RatFunc K :=
  ![w 0/RatFunc.X-RatFunc.C (c 0)*w 1/RatFunc.X,
    w 2/RatFunc.X^2-2*RatFunc.C (c 1)*w 1/RatFunc.X,
    w 3/RatFunc.X^2-2*RatFunc.C (c 2)*w 1/RatFunc.X]

def independentCoordinates (c : Fin 3 → K) : Fin 4 → RatFunc K :=
  ![RatFunc.X*RatFunc.C (c 0),RatFunc.X,
    RatFunc.X^2*RatFunc.C (c 1),RatFunc.X^2*RatFunc.C (c 2)]

lemma coneDerivations_coordinate (D : Fin 3 → Derivation ℤ K K) (c : Fin 3 → K)
    (hc : ∀ i j,D i (c j)=if j=i then 1 else 0) (i j : Fin 4) :
    coneDerivations D c i (independentCoordinates c j)=if j=i then 1 else 0 := by
  have hX : (RatFunc.X : RatFunc K)≠0 := CrossedRationalResidue.X_ne_zero
  have h2 (i : Fin 3) : baseCoefficient (D i) (2 : RatFunc K)=0 :=
    (baseCoefficient (D i)).map_natCast 2
  fin_cases i <;> fin_cases j <;>
    simp [coneDerivations,independentCoordinates,Derivation.sub_apply,Derivation.smul_apply,
      Derivation.leibniz,Derivation.leibniz_pow,smul_eq_mul,
      baseTime_X,baseTime_C,baseCoefficient_X,baseCoefficient_C,hc] <;>
    field_simp <;> ring

lemma coneDerivations_constant (D : Fin 3 → Derivation ℤ K K) (c : Fin 3 → K)
    (a : K) (ha : ∀ i,D i a=0) (i : Fin 4) :
    coneDerivations D c i (RatFunc.C a)=0 := by
  fin_cases i <;> simp [coneDerivations,Derivation.sub_apply,Derivation.smul_apply,
    baseTime_C,baseCoefficient_C,ha]

lemma radial_divergence_identity (D : Fin 3 → Derivation ℤ K K) (c : Fin 3 → K)
    (hc : ∀ i,D i (c i)=1) (g : K) (hg : g≠0) (w : Fin 4 → RatFunc K) :
    residueDivergence (coneDerivations D c) (RatFunc.X^5*RatFunc.C g) w=
      baseTime (w 1)+residueDivergence (fun i => baseCoefficient (D i))
        (RatFunc.C g) (projectedField c w) := by
  have hX : (RatFunc.X : RatFunc K)≠0 := CrossedRationalResidue.X_ne_zero
  have hg' : (RatFunc.C g : RatFunc K)≠0 := (RatFunc.C_injective.ne hg).trans_eq (map_zero RatFunc.C)
  have h2 (i : Fin 3) : baseCoefficient (D i) (2 : RatFunc K)=0 :=
    (baseCoefficient (D i)).map_natCast 2
  simp [residueDivergence,fieldDivergence,coneDerivations,projectedField,
    Fin.sum_univ_succ,Derivation.sub_apply,Derivation.smul_apply,Derivation.leibniz,
    Derivation.leibniz_div,Derivation.leibniz_pow,
    smul_eq_mul,
    baseTime_X,baseTime_C,baseCoefficient_X,baseCoefficient_C,hc,h2]
  field_simp
  ring

lemma residue_weighted_divergence (D : Fin 3 → Derivation ℤ K K)
    (g : K) (hg : g≠0) (v : Fin 3 → RatFunc K) :
    residue (K:=K) 0 (residueDivergence (fun i => baseCoefficient (D i)) (RatFunc.C g) v)=
      residueDivergence D g (fun i => residue (K:=K) 0 (v i)) := by
  have hg' : (RatFunc.C g : RatFunc K)≠0 := (RatFunc.C_injective.ne hg).trans_eq (map_zero RatFunc.C)
  simp only [residueDivergence,fieldDivergence,map_sub,map_sum,residue_coefficient,
    baseCoefficient_C]
  have hm (i : Fin 3) : residue (K:=K) 0 (v i*RatFunc.C (D i g)/RatFunc.C g)=
      residue (K:=K) 0 (v i)*D i g/g := by
    rw [div_eq_mul_inv,← map_inv₀,mul_assoc,← map_mul]
    rw [mul_comm,← RatFunc.smul_eq_C_mul,map_smul,smul_eq_mul]
    ring
  rw [Finset.sum_div,Finset.sum_div]
  simp only [map_sum,hm]

theorem residue_solution_descends_radial (D : Fin 3 → Derivation ℤ K K)
    (c : Fin 3 → K) (hc : ∀ i,D i (c i)=1) (g : K) (hg : g≠0)
    (s : K) (w : Fin 4 → RatFunc K)
    (hw : residueDivergence (coneDerivations D c) (RatFunc.X^5*RatFunc.C g) w=
      RatFunc.C s/RatFunc.X) :
    ∃ v : Fin 3 → K,residueDivergence D g v=s := by
  refine ⟨fun i => residue (K:=K) 0 (projectedField c w i),?_⟩
  rw [radial_divergence_identity D c hc g hg w] at hw
  have hr := congrArg (residue (K:=K) 0) hw
  rw [map_add,residue_time,residue_weighted_divergence D g hg,zero_add] at hr
  have hs : residue (K:=K) 0 (RatFunc.C s/RatFunc.X)=s := by
    simpa only [rationalConstantTerm_apply] using rationalConstantTerm_C s
  exact hr.trans hs

end CrossedRadialResidue
end
end
