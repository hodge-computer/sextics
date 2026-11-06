import HodgeComputer.Constructions.FiniteAlgebra.RegularSpecialization
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.Localization.Integer
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Choose
import Mathlib.Tactic.NormNum

noncomputable section
namespace HoldoutQ2.Clearing
open MvPolynomial
abbrev Parameters := MvPolynomial (Fin 2) ℂ
abbrev BasePoly := MvPolynomial (Fin 6) ℂ

def xa : BasePoly := X 0 * X 1

def goodParameters (k : ℂ) : Parameters →+* ℂ := eval₂Hom (RingHom.id ℂ) ![k^2,k]
def goodBase (k : ℂ) : BasePoly →+* ℂ := eval₂Hom (RingHom.id ℂ) ![1,1,0,k^2,k,0]

variable {k : ℂ}

/-- An encoding of (xa)^n p(b/a,d/c), including its full evaluation law. -/
structure HomogeneousDatum (p : Parameters) (n : ℕ) (H : BasePoly) : Prop where
  homogeneous : H.IsHomogeneous (2 * n)
  evaluation : ∀ {K : Type} [Field K] [Algebra ℂ K] (v : Fin 6 → K),
    v 0 ≠ 0 → v 1 ≠ 0 →
    eval₂ (algebraMap ℂ K) v H = (v 0 * v 1)^n *
      eval₂ (algebraMap ℂ K) ![v 3 / v 0, v 4 / v 1] p

theorem ac_homogeneous : xa.IsHomogeneous 2 :=
  (isHomogeneous_X ℂ 0).mul (isHomogeneous_X ℂ 1)

theorem homogeneousDatum_C (r : ℂ) : HomogeneousDatum (C r) 0 (C r) where
  homogeneous := isHomogeneous_C _ r
  evaluation := by intros; simp

theorem HomogeneousDatum.add {p q : Parameters} {n m : ℕ} {H J : BasePoly}
    (hp : HomogeneousDatum p n H) (hq : HomogeneousDatum q m J) :
    HomogeneousDatum (p + q) (n + m) (H * xa^m + J * xa^n) where
  homogeneous := by
    have h1 := hp.homogeneous.mul (ac_homogeneous.pow m)
    have h2 := hq.homogeneous.mul (ac_homogeneous.pow n)
    convert h1.add (by simpa only [Nat.add_comm] using h2) using 1 <;> omega
  evaluation := by
    intro K _ _ v ha hc
    simp only [eval₂_add, eval₂_mul, eval₂_pow, xa, eval₂_X]
    rw [hp.evaluation v ha hc, hq.evaluation v ha hc]
    simp only [pow_add]
    ring

theorem HomogeneousDatum.mul_X {p : Parameters} {n : ℕ} {H : BasePoly}
    (hp : HomogeneousDatum p n H) (j : Fin 2) :
    ∃ J, HomogeneousDatum (p * X j) (n + 1) J := by
  fin_cases j
  · refine ⟨H * (X 3 * X 1), ?_⟩
    constructor
    · have hh := hp.homogeneous.mul ((isHomogeneous_X ℂ 3).mul (isHomogeneous_X ℂ 1))
      convert hh using 1 <;> omega
    · intro K _ _ v ha hc
      simp only [eval₂_mul, eval₂_X, Matrix.cons_val, hp.evaluation v ha hc, pow_succ]
      norm_num [Matrix.cons_val, Fin.isValue]
      field_simp [ha, hc]
      <;> ring
  · refine ⟨H * (X 4 * X 0), ?_⟩
    constructor
    · have hh := hp.homogeneous.mul ((isHomogeneous_X ℂ 4).mul (isHomogeneous_X ℂ 0))
      convert hh using 1 <;> omega
    · intro K _ _ v ha hc
      simp only [eval₂_mul, eval₂_X, Matrix.cons_val, hp.evaluation v ha hc, pow_succ]
      norm_num [Matrix.cons_val, Fin.isValue]
      field_simp [ha, hc]
      <;> ring

theorem exists_homogeneousDatum (p : Parameters) : ∃ n H, HomogeneousDatum p n H := by
  induction p using MvPolynomial.induction_on with
  | C r => exact ⟨0, C r, homogeneousDatum_C r⟩
  | add p q hp hq =>
      obtain ⟨n, H, hH⟩ := hp
      obtain ⟨m, J, hJ⟩ := hq
      exact ⟨n + m, H * xa^m + J * xa^n, hH.add hJ⟩
  | mul_X p j hp =>
      obtain ⟨n, H, hH⟩ := hp
      obtain ⟨J, hJ⟩ := hH.mul_X j
      exact ⟨n + 1, J, hJ⟩

theorem HomogeneousDatum.raise {p : Parameters} {n : ℕ} {H : BasePoly}
    (hp : HomogeneousDatum p n H) (k : ℕ) :
    HomogeneousDatum p (n + k) (H * xa^k) where
  homogeneous := by
    convert hp.homogeneous.mul (ac_homogeneous.pow k) using 1 <;> omega
  evaluation := by
    intro K _ _ v ha hc
    simp only [eval₂_mul, eval₂_pow, xa, eval₂_X, hp.evaluation v ha hc, pow_add]
    ring

theorem HomogeneousDatum.goodBase {p : Parameters} {n : ℕ} {H : BasePoly}
    (hp : HomogeneousDatum p n H) : goodBase k H = goodParameters k p := by
  have he := hp.evaluation (K := ℂ) ![1,1,0,k^2,k,0] (by change (1:ℂ) ≠ 0; norm_num) (by change (1:ℂ) ≠ 0; norm_num)
  simpa [HoldoutQ2.Clearing.goodBase, goodParameters] using he

theorem exists_uniform_homogeneousDatum {ι : Type*} [Fintype ι]
    (p : ι → Parameters) : ∃ (n : ℕ) (H : ι → BasePoly), ∀ i, HomogeneousDatum (p i) n (H i) := by
  classical
  choose n H hh using fun i => exists_homogeneousDatum (p i)
  let N := ∑ i, n i
  refine ⟨N, fun i => H i * xa ^ (N - n i), ?_⟩
  intro i
  have hi : n i ≤ N := Finset.single_le_sum (fun j _ => Nat.zero_le (n j)) (Finset.mem_univ i)
  simpa only [Nat.add_sub_of_le hi] using (hh i).raise (N - n i)

/-- A finite family of regular coefficients has a good common denominator. -/
theorem regular_common_denominator {ι : Type*} [Finite ι]
    (z : ι → RegularSpecialization.Coefficients (goodParameters k)) :
    ∃ q : Parameters, goodParameters k q ≠ 0 ∧ ∃ p : ι → Parameters,
      ∀ i, algebraMap Parameters (RegularSpecialization.Coefficients (goodParameters k)) (p i) =
        algebraMap Parameters (RegularSpecialization.Coefficients (goodParameters k)) q * z i := by
  obtain ⟨q, hq⟩ := IsLocalization.exist_integer_multiples_of_finite
    (RegularSpecialization.denominators (goodParameters k)) z
  choose p hp using hq
  refine ⟨q, q.property, p, ?_⟩
  intro i
  simpa [Algebra.smul_def] using hp i

/-- Matching-degree numerator/denominator encodings preserving good specialization. -/
theorem regular_uniform_homogeneous_clearing {ι : Type*} [Fintype ι]
    (z : ι → RegularSpecialization.Coefficients (goodParameters k)) :
    ∃ (n : ℕ) (q : Parameters) (p : ι → Parameters) (D : BasePoly) (N : ι → BasePoly),
      HomogeneousDatum q n D ∧ goodBase k D ≠ 0 ∧
      (∀ i, HomogeneousDatum (p i) n (N i)) ∧
      (∀ i, algebraMap Parameters (RegularSpecialization.Coefficients (goodParameters k)) (p i) =
        algebraMap Parameters (RegularSpecialization.Coefficients (goodParameters k)) q * z i) := by
  classical
  obtain ⟨q, hq, p, hp⟩ := regular_common_denominator z
  obtain ⟨n, H, hh⟩ := exists_uniform_homogeneousDatum (fun i : Option ι => i.elim q p)
  refine ⟨n, q, p, H none, fun i => H (some i), hh none, ?_, fun i => hh (some i), hp⟩
  rw [(hh none).goodBase (k := k)]
  exact hq

end HoldoutQ2.Clearing

#print axioms HoldoutQ2.Clearing.regular_uniform_homogeneous_clearing
