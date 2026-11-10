import Proposal.ContactBanachExistence
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! Quantitative estimates for the sparse monomial lists in the contact system. -/

noncomputable section

namespace ContactPolynomialBounds

open Metric Set
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false

abbrev Space (n : ℕ) := Fin n → ℂ
abbrev Polynomial (n : ℕ) := List (ℂ × List (Fin n))

def monomial {n : ℕ} (m : List (Fin n)) (x : Space n) : ℂ :=
  (m.map x).prod

def monomialDeriv {n : ℕ} : List (Fin n) → Space n → Space n →L[ℂ] ℂ
  | [], _ => 0
  | i :: m, x => x i • monomialDeriv m x + monomial m x • ContinuousLinearMap.proj i

def firstMass (M : ℝ) : ℕ → ℝ
  | 0 => 0
  | k + 1 => M * firstMass M k + M ^ k

def secondMass (M : ℝ) : ℕ → ℝ
  | 0 => 0
  | k + 1 => 2 * firstMass M k + M * secondMass M k

theorem firstMass_nonneg {M : ℝ} (hM : 0 ≤ M) (k : ℕ) : 0 ≤ firstMass M k := by
  induction k with
  | zero => simp [firstMass]
  | succ k ih => exact add_nonneg (mul_nonneg hM ih) (pow_nonneg hM _)

theorem secondMass_nonneg {M : ℝ} (hM : 0 ≤ M) (k : ℕ) : 0 ≤ secondMass M k := by
  induction k with
  | zero => simp [secondMass]
  | succ k ih =>
      exact add_nonneg (mul_nonneg (by norm_num) (firstMass_nonneg hM _))
        (mul_nonneg hM ih)

theorem monomial_hasFDerivAt {n : ℕ} (m : List (Fin n)) (x : Space n) :
    HasFDerivAt (monomial m) (monomialDeriv m x) x := by
  induction m with
  | nil =>
    change HasFDerivAt (fun _ : Space n => (1 : ℂ)) 0 x
    exact hasFDerivAt_const (𝕜 := ℂ) (1 : ℂ) x
  | cons i m ih =>
    change HasFDerivAt (fun y : Space n => y i * monomial m y)
      (x i • monomialDeriv m x + monomial m x • ContinuousLinearMap.proj i) x
    exact (hasFDerivAt_apply (𝕜 := ℂ) i x).fun_mul ih

theorem norm_proj_le {n : ℕ} (i : Fin n) :
    ‖ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) i‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simpa using norm_le_pi_norm x i

theorem norm_monomial_le {n : ℕ} (m : List (Fin n)) (x : Space n)
    {M : ℝ} (hM : 0 ≤ M) (hx : ‖x‖ ≤ M) :
    ‖monomial m x‖ ≤ M ^ m.length := by
  induction m with
  | nil => simp [monomial]
  | cons i m ih =>
    simp only [monomial, List.map_cons, List.prod_cons, norm_mul, List.length_cons]
    calc
      ‖x i‖ * ‖(List.map x m).prod‖ ≤ M * M ^ m.length :=
        mul_le_mul ((norm_le_pi_norm x i).trans hx) ih (norm_nonneg _) hM
      _ = M ^ (m.length + 1) := by rw [pow_succ, mul_comm]

theorem norm_monomialDeriv_le {n : ℕ} (m : List (Fin n)) (x : Space n)
    {M : ℝ} (hM : 0 ≤ M) (hx : ‖x‖ ≤ M) :
    ‖monomialDeriv m x‖ ≤ firstMass M m.length := by
  induction m with
  | nil => simp [monomialDeriv, firstMass]
  | cons i m ih =>
    simp only [monomialDeriv, List.length_cons, firstMass]
    calc
      ‖x i • monomialDeriv m x + monomial m x • ContinuousLinearMap.proj i‖
          ≤ ‖x i • monomialDeriv m x‖ + ‖monomial m x • ContinuousLinearMap.proj i‖ :=
        norm_add_le _ _
      _ ≤ M * firstMass M m.length + M ^ m.length := by
        rw [norm_smul, norm_smul]
        apply add_le_add
        · exact mul_le_mul ((norm_le_pi_norm x i).trans hx) ih (norm_nonneg _) hM
        · calc
            ‖monomial m x‖ * ‖ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) i‖
                ≤ M ^ m.length * 1 := mul_le_mul (norm_monomial_le m x hM hx)
                  (norm_proj_le i) (norm_nonneg _) (pow_nonneg hM _)
            _ = M ^ m.length := mul_one _

theorem monomial_lipschitz {n : ℕ} (m : List (Fin n)) (x y : Space n)
    {M : ℝ} (hM : 0 ≤ M) (hx : ‖x‖ ≤ M) (hy : ‖y‖ ≤ M) :
    ‖monomial m x - monomial m y‖ ≤ firstMass M m.length * ‖x - y‖ := by
  apply (convex_closedBall (0 : Space n) M).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun z _ => (monomial_hasFDerivAt m z).hasFDerivWithinAt)
    (fun z hz => norm_monomialDeriv_le m z hM (by simpa using hz))
    (by simpa using hy) (by simpa using hx)

theorem monomialDeriv_lipschitz {n : ℕ} (m : List (Fin n)) (x y : Space n)
    {M : ℝ} (hM : 0 ≤ M) (hx : ‖x‖ ≤ M) (hy : ‖y‖ ≤ M) :
    ‖monomialDeriv m x - monomialDeriv m y‖ ≤
      secondMass M m.length * ‖x - y‖ := by
  induction m with
  | nil => simp [monomialDeriv, secondMass]
  | cons i m ih =>
    have hdecomp : monomialDeriv (i :: m) x - monomialDeriv (i :: m) y =
        (x i - y i) • monomialDeriv m x +
        y i • (monomialDeriv m x - monomialDeriv m y) +
        (monomial m x - monomial m y) • ContinuousLinearMap.proj i := by
      ext v
      simp only [monomialDeriv, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
      ring
    rw [hdecomp]
    calc
      _ ≤ ‖(x i - y i) • monomialDeriv m x‖ +
          ‖y i • (monomialDeriv m x - monomialDeriv m y)‖ +
          ‖(monomial m x - monomial m y) • ContinuousLinearMap.proj i‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ ‖x - y‖ * firstMass M m.length +
          M * (secondMass M m.length * ‖x - y‖) +
          firstMass M m.length * ‖x - y‖ := by
        simp only [norm_smul]
        apply add_le_add
        · apply add_le_add
          · exact mul_le_mul (norm_le_pi_norm (x - y) i)
              (norm_monomialDeriv_le m x hM hx) (norm_nonneg _) (norm_nonneg _)
          · exact mul_le_mul ((norm_le_pi_norm y i).trans hy) ih (norm_nonneg _)
              (by positivity)
        · calc
            _ ≤ (firstMass M m.length * ‖x - y‖) * 1 :=
              mul_le_mul (monomial_lipschitz m x y hM hx hy)
                (norm_proj_le i) (norm_nonneg _)
                (mul_nonneg (firstMass_nonneg hM _) (norm_nonneg _))
            _ = _ := mul_one _
      _ = secondMass M (i :: m).length * ‖x - y‖ := by
        simp only [List.length_cons, secondMass]
        ring

def poly {n : ℕ} : Polynomial n → Space n → ℂ
  | [], _ => 0
  | (a, m) :: p, x => a * monomial m x + poly p x

def polyDeriv {n : ℕ} : Polynomial n → Space n → Space n →L[ℂ] ℂ
  | [], _ => 0
  | (a, m) :: p, x => a • monomialDeriv m x + polyDeriv p x

def complexMass (a : ℂ) : ℝ := |a.re| + |a.im|

theorem complexMass_nonneg (a : ℂ) : 0 ≤ complexMass a :=
  add_nonneg (abs_nonneg _) (abs_nonneg _)

theorem norm_le_complexMass (a : ℂ) : ‖a‖ ≤ complexMass a :=
  Complex.norm_le_abs_re_add_abs_im a

def hessianMass {n : ℕ} : Polynomial n → ℝ → ℝ
  | [], _ => 0
  | (a, m) :: p, M => complexMass a * secondMass M m.length + hessianMass p M

theorem hessianMass_nonneg {n : ℕ} (p : Polynomial n) {M : ℝ} (hM : 0 ≤ M) :
    0 ≤ hessianMass p M := by
  induction p with
  | nil => simp [hessianMass]
  | cons a p ih =>
    exact add_nonneg (mul_nonneg (complexMass_nonneg _) (secondMass_nonneg hM _)) ih

theorem poly_hasFDerivAt {n : ℕ} (p : Polynomial n) (x : Space n) :
    HasFDerivAt (poly p) (polyDeriv p x) x := by
  induction p with
  | nil => exact hasFDerivAt_const (𝕜 := ℂ) (0 : ℂ) x
  | cons a p ih =>
    change HasFDerivAt (fun y : Space n => a.1 * monomial a.2 y + poly p y)
      (a.1 • monomialDeriv a.2 x + polyDeriv p x) x
    exact ((monomial_hasFDerivAt a.2 x).const_mul a.1).add ih

theorem polyDeriv_lipschitz {n : ℕ} (p : Polynomial n) (x y : Space n)
    {M : ℝ} (hM : 0 ≤ M) (hx : ‖x‖ ≤ M) (hy : ‖y‖ ≤ M) :
    ‖polyDeriv p x - polyDeriv p y‖ ≤ hessianMass p M * ‖x - y‖ := by
  induction p with
  | nil => simp [polyDeriv, hessianMass]
  | cons a p ih =>
    have heq : polyDeriv (a :: p) x - polyDeriv (a :: p) y =
        a.1 • (monomialDeriv a.2 x - monomialDeriv a.2 y) +
        (polyDeriv p x - polyDeriv p y) := by
      simp only [polyDeriv, smul_sub]
      abel
    rw [heq]
    calc
      _ ≤ ‖a.1 • (monomialDeriv a.2 x - monomialDeriv a.2 y)‖ +
          ‖polyDeriv p x - polyDeriv p y‖ := norm_add_le _ _
      _ ≤ complexMass a.1 * (secondMass M a.2.length * ‖x - y‖) +
          hessianMass p M * ‖x - y‖ := by
        rw [norm_smul]
        exact add_le_add (mul_le_mul (norm_le_complexMass _) (monomialDeriv_lipschitz
          a.2 x y hM hx hy) (norm_nonneg _) (complexMass_nonneg _)) ih
      _ = hessianMass (a :: p) M * ‖x - y‖ := by simp only [hessianMass]; ring

def system {n : ℕ} (p : Fin n → Polynomial n) (x : Space n) : Space n :=
  fun i => poly (p i) x

def systemDeriv {n : ℕ} (p : Fin n → Polynomial n) (x : Space n) :
    Space n →L[ℂ] Space n := ContinuousLinearMap.pi (fun i => polyDeriv (p i) x)

theorem system_hasFDerivAt {n : ℕ} (p : Fin n → Polynomial n) (x : Space n) :
    HasFDerivAt (system p) (systemDeriv p x) x :=
  hasFDerivAt_pi.mpr (fun i => poly_hasFDerivAt (p i) x)

theorem systemDeriv_lipschitz {n : ℕ} (p : Fin n → Polynomial n) (x y : Space n)
    {M H : ℝ} (hM : 0 ≤ M) (hH : 0 ≤ H)
    (hp : ∀ i, hessianMass (p i) M ≤ H) (hx : ‖x‖ ≤ M) (hy : ‖y‖ ≤ M) :
    ‖systemDeriv p x - systemDeriv p y‖ ≤ H * ‖x - y‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hH (norm_nonneg _))
  intro v
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  have hpoly : ‖polyDeriv (p i) x - polyDeriv (p i) y‖ ≤ H * ‖x - y‖ :=
    (polyDeriv_lipschitz (p i) x y hM hx hy).trans
      (mul_le_mul_of_nonneg_right (hp i) (norm_nonneg _))
  exact (polyDeriv (p i) x - polyDeriv (p i) y).le_of_opNorm_le hpoly v

end ContactPolynomialBounds
