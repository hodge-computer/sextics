import HodgeComputer.Constructions.RationalFields.CommonDenominatorSubstitution
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

/-- The two rational coordinates share the homogeneous quadratic denominator. -/
def clearingCoordinates : Fin 2 → BasePoly := ![X 3 * X 1, X 4 * X 0]

/-- Any total-degree bound supplies a literal homogeneous clearing. -/
theorem homogeneousDatum_of_degree (p : Parameters) (n : ℕ) (hp : p.totalDegree ≤ n) :
    HomogeneousDatum p n
      (CommonDenominatorSubstitution.cleared p xa clearingCoordinates n) where
  homogeneous := by
    apply CommonDenominatorSubstitution.cleared_homogeneous p xa clearingCoordinates n 2 hp
      ac_homogeneous
    intro i
    fin_cases i
    · exact (isHomogeneous_X ℂ 3).mul (isHomogeneous_X ℂ 1)
    · exact (isHomogeneous_X ℂ 4).mul (isHomogeneous_X ℂ 0)
  evaluation := by
    intro K _ _ v ha hc
    let φ : BasePoly →+* K := eval₂Hom (algebraMap ℂ K) v
    have hB : φ xa = v 0 * v 1 := by simp [φ, xa]
    have hG (i : Fin 2) :
        φ (clearingCoordinates i) = (v 0 * v 1) * ![v 3/v 0,v 4/v 1] i := by
      fin_cases i <;> simp [φ, clearingCoordinates] <;> field_simp [ha, hc] <;> ring
    have hC : φ.comp C = algebraMap ℂ K := by ext r; simp [φ]
    have h := CommonDenominatorSubstitution.map_cleared p xa clearingCoordinates n hp
      φ (v 0 * v 1) ![v 3/v 0,v 4/v 1] hB hG
    simpa only [hC, φ, coe_eval₂Hom] using h

theorem exists_homogeneousDatum (p : Parameters) : ∃ n H, HomogeneousDatum p n H := by
  exact ⟨p.totalDegree, _, homogeneousDatum_of_degree p p.totalDegree le_rfl⟩

theorem HomogeneousDatum.goodBase {p : Parameters} {n : ℕ} {H : BasePoly}
    (hp : HomogeneousDatum p n H) : goodBase k H = goodParameters k p := by
  have he := hp.evaluation (K := ℂ) ![1,1,0,k^2,k,0] (by change (1:ℂ) ≠ 0; norm_num) (by change (1:ℂ) ≠ 0; norm_num)
  simpa [HoldoutQ2.Clearing.goodBase, goodParameters] using he

theorem exists_uniform_homogeneousDatum {ι : Type*} [Fintype ι]
    (p : ι → Parameters) : ∃ (n : ℕ) (H : ι → BasePoly), ∀ i, HomogeneousDatum (p i) n (H i) := by
  classical
  let n := ∑ i, (p i).totalDegree
  refine ⟨n, fun i => CommonDenominatorSubstitution.cleared (p i) xa clearingCoordinates n, ?_⟩
  intro i
  apply homogeneousDatum_of_degree
  exact Finset.single_le_sum (fun j _ => Nat.zero_le (p j).totalDegree) (Finset.mem_univ i)

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
