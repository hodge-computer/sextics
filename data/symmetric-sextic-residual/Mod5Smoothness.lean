import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
An algebraic smoothness-lifting argument for sextics in six variables.
It uses a symbolic degree-25 Macaulay matrix. No matrix of size 142506
is materialized: its reduction is a scalar identity by a uniform proof.
-/

noncomputable section
namespace SexticModFive
open MvPolynomial Matrix
open scoped BigOperators

abbrev Vars := Fin 6
abbrev Exponents := Vars →₀ ℕ
abbrev Degree25 := {d : Exponents // d.degree = 25}

instance : Fact (Nat.Prime 5) := ⟨by decide⟩
instance : Fintype Degree25 := (Finsupp.finite_of_degree_eq (σ := Vars) 25).fintype

theorem exists_large_exponent (d : Degree25) : ∃ i, 5 ≤ d.val i := by
  by_contra h
  push Not at h
  have hb : (∑ i : Vars, d.val i) ≤ ∑ _i : Vars, 4 :=
    Finset.sum_le_sum (fun i _ => by have hi := h i; omega)
  have hd := d.property
  rw [Finsupp.degree_eq_sum] at hd
  norm_num [Vars] at hb
  omega

def pivot (d : Degree25) : Vars := Classical.choose (exists_large_exponent d)

theorem pivot_large (d : Degree25) : 5 ≤ d.val (pivot d) :=
  Classical.choose_spec (exists_large_exponent d)

def remainder (d : Degree25) : Exponents := d.val - Finsupp.single (pivot d) 5

theorem remainder_add_pivot (d : Degree25) :
    remainder d + Finsupp.single (pivot d) 5 = d.val :=
  tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr (pivot_large d))

theorem remainder_degree (d : Degree25) : (remainder d).degree = 20 := by
  have h := congrArg Finsupp.degree (remainder_add_pivot d)
  simp only [map_add, Finsupp.degree_single, d.property] at h
  omega

theorem homogeneous_expansion {R : Type*} [CommRing R]
    (p : MvPolynomial Vars R) (hp : p.IsHomogeneous 25) :
    p = ∑ d : Degree25, monomial d.val (coeff d.val p) := by
  classical
  ext e
  rw [coeff_sum]
  by_cases he : e.degree = 25
  · let a : Degree25 := ⟨e, he⟩
    rw [Finset.sum_eq_single a]
    · simp [a]
    · intro b _ hba
      have hbe : b.val ≠ e := by
        intro h
        apply hba
        exact Subtype.ext h
      simp [hbe]
    · simp
  · have hc : coeff e p = 0 := by
      by_contra hn
      apply he
      rw [Finsupp.degree_eq_weight_one]
      exact hp hn
    rw [hc]
    symm
    apply Finset.sum_eq_zero
    intro b _
    have hbe : b.val ≠ e := by
      intro h
      exact he (h ▸ b.property)
    simp [hbe]

def columnPolynomial (g : Vars → MvPolynomial Vars ℤ) (d : Degree25) :
    MvPolynomial Vars ℤ := monomial (remainder d) 1 * g (pivot d)

def macaulay (g : Vars → MvPolynomial Vars ℤ) : Matrix Degree25 Degree25 ℤ :=
  fun a b => coeff a.val (columnPolynomial g b)

theorem column_homogeneous (g : Vars → MvPolynomial Vars ℤ)
    (hg : ∀ i, (g i).IsHomogeneous 5) (d : Degree25) :
    (columnPolynomial g d).IsHomogeneous 25 := by
  exact (isHomogeneous_monomial 1 (remainder_degree d)).mul (hg (pivot d))

theorem column_mod_five (g : Vars → MvPolynomial Vars ℤ)
    (hmod : ∀ i, map (Int.castRingHom (ZMod 5)) (g i) = C 2 * X i ^ 5)
    (d : Degree25) :
    map (Int.castRingHom (ZMod 5)) (columnPolynomial g d) = monomial d.val 2 := by
  rw [columnPolynomial, map_mul, map_monomial, map_one, hmod]
  rw [C_mul_X_pow_eq_monomial, monomial_mul, one_mul, remainder_add_pivot]

theorem macaulay_mod_five (g : Vars → MvPolynomial Vars ℤ)
    (hmod : ∀ i, map (Int.castRingHom (ZMod 5)) (g i) = C 2 * X i ^ 5) :
    (macaulay g).map (Int.castRingHom (ZMod 5)) =
      (2 : ZMod 5) • (1 : Matrix Degree25 Degree25 (ZMod 5)) := by
  classical
  ext a b
  change (Int.castRingHom (ZMod 5)) (coeff a.val (columnPolynomial g b)) = _
  rw [← coeff_map, column_mod_five g hmod]
  simp only [coeff_monomial, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  by_cases h : a = b
  · subst b
    simp
  · have hab : b.val ≠ a.val := fun he => h (Subtype.ext he.symm)
    simp [h, hab]

theorem macaulay_det_ne_zero (g : Vars → MvPolynomial Vars ℤ)
    (hmod : ∀ i, map (Int.castRingHom (ZMod 5)) (g i) = C 2 * X i ^ 5) :
    (macaulay g).det ≠ 0 := by
  intro hz
  have he := (Int.castRingHom (ZMod 5)).map_det (macaulay g)
  change ((macaulay g).det : ZMod 5) =
    ((macaulay g).map (Int.castRingHom (ZMod 5))).det at he
  rw [hz, Int.cast_zero, macaulay_mod_five g hmod, Matrix.det_smul, Matrix.det_one,
    mul_one] at he
  have htwo : (2 : ZMod 5) ≠ 0 := by decide
  exact (pow_ne_zero _ htwo) he.symm

theorem common_zero_is_origin {K : Type*} [Field K] [CharZero K]
    (g : Vars → MvPolynomial Vars ℤ)
    (hg : ∀ i, (g i).IsHomogeneous 5)
    (hmod : ∀ i, map (Int.castRingHom (ZMod 5)) (g i) = C 2 * X i ^ 5)
    (x : Vars → K) (hx : ∀ i, eval₂ (Int.castRingHom K) x (g i) = 0) :
    x = 0 := by
  classical
  let M : Matrix Degree25 Degree25 K := (macaulay g).map (Int.castRingHom K)
  have hd : M.det ≠ 0 := by
    rw [show M.det = ((macaulay g).det : K) from
      ((Int.castRingHom K).map_det (macaulay g)).symm]
    exact_mod_cast macaulay_det_ne_zero g hmod
  let v : Degree25 → K := fun d => eval₂ (Int.castRingHom K) x (monomial d.val 1)
  have hz : Matrix.vecMul v M = 0 := by
    funext b
    have he := congrArg (eval₂ (Int.castRingHom K) x)
      (homogeneous_expansion (columnPolynomial g b) (column_homogeneous g hg b))
    have hleft : eval₂ (Int.castRingHom K) x (columnPolynomial g b) = 0 := by
      simp [columnPolynomial, hx]
    rw [hleft] at he
    simp only [eval₂_sum, eval₂_monomial] at he
    change (∑ a : Degree25, v a * M a b) = 0
    simpa [v, M, macaulay, mul_comm] using he.symm
  have hv : v = 0 := by
    apply (Matrix.vecMul_injective_iff_isUnit.mpr
      ((Matrix.isUnit_iff_isUnit_det M).mpr (isUnit_iff_ne_zero.mpr hd)))
    simpa using hz
  funext i
  let a : Degree25 := ⟨Finsupp.single i 25, Finsupp.degree_single i 25⟩
  have ha := congrFun hv a
  have hp : x i ^ 25 = 0 := by
    change eval₂ (Int.castRingHom K) x (monomial (Finsupp.single i 25) 1) = 0 at ha
    rw [← X_pow_eq_monomial, eval₂_X_pow] at ha
    exact ha
  exact eq_zero_of_pow_eq_zero hp

#print axioms common_zero_is_origin
end SexticModFive
