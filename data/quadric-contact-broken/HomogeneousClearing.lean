import HodgeComputer.Constructions.RationalFields.CommonDenominatorSubstitution
import Proposal.ParameterSpecialization
import Mathlib.RingTheory.Localization.Integer
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Choose
import Mathlib.Tactic.NormNum

noncomputable section
namespace QuadricContactClearing
open MvPolynomial
abbrev Parameters := MvPolynomial (Fin 2) ℚ
abbrev BasePoly := MvPolynomial (Fin 6) ℚ

def ac : BasePoly := X 1 * X 2

abbrev goodParameters : Parameters →+* ℚ := ParameterSpecialization.point
def goodBase : BasePoly →+* ℚ := eval₂Hom (RingHom.id ℚ) ![0, 1, 1, 0, 1, 2]

/-- An encoding of (ac)^n p(b/a,d/c), including its full evaluation law. -/
structure HomogeneousDatum (p : Parameters) (n : ℕ) (H : BasePoly) : Prop where
  homogeneous : H.IsHomogeneous (2 * n)
  evaluation : ∀ {K : Type} [Field K] [Algebra ℚ K] (v : Fin 6 → K),
    v 1 ≠ 0 → v 2 ≠ 0 →
    eval₂ (algebraMap ℚ K) v H = (v 1 * v 2)^n *
      eval₂ (algebraMap ℚ K) ![v 4 / v 1, v 5 / v 2] p

theorem ac_homogeneous : ac.IsHomogeneous 2 :=
  (isHomogeneous_X ℚ 1).mul (isHomogeneous_X ℚ 2)

/-- The two rational coordinates share the homogeneous quadratic denominator. -/
def clearingCoordinates : Fin 2 → BasePoly := ![X 4 * X 2, X 5 * X 1]

/-- Any total-degree bound supplies a literal homogeneous clearing. -/
theorem homogeneousDatum_of_degree (p : Parameters) (n : ℕ) (hp : p.totalDegree ≤ n) :
    HomogeneousDatum p n
      (CommonDenominatorSubstitution.cleared p ac clearingCoordinates n) where
  homogeneous := by
    apply CommonDenominatorSubstitution.cleared_homogeneous p ac clearingCoordinates n 2 hp
      ac_homogeneous
    intro i
    fin_cases i
    · exact (isHomogeneous_X ℚ 4).mul (isHomogeneous_X ℚ 2)
    · exact (isHomogeneous_X ℚ 5).mul (isHomogeneous_X ℚ 1)
  evaluation := by
    intro K _ _ v ha hc
    let φ : BasePoly →+* K := eval₂Hom (algebraMap ℚ K) v
    have hB : φ ac = v 1 * v 2 := by simp [φ, ac]
    have hG (i : Fin 2) :
        φ (clearingCoordinates i) = (v 1 * v 2) * ![v 4/v 1,v 5/v 2] i := by
      fin_cases i <;> simp [φ, clearingCoordinates] <;> field_simp [ha, hc] <;> ring
    have hC : φ.comp C = algebraMap ℚ K := by ext r; simp [φ]
    have h := CommonDenominatorSubstitution.map_cleared p ac clearingCoordinates n hp
      φ (v 1 * v 2) ![v 4/v 1,v 5/v 2] hB hG
    simpa only [hC, φ, coe_eval₂Hom] using h

theorem exists_homogeneousDatum (p : Parameters) : ∃ n H, HomogeneousDatum p n H := by
  exact ⟨p.totalDegree, _, homogeneousDatum_of_degree p p.totalDegree le_rfl⟩

theorem HomogeneousDatum.goodBase {p : Parameters} {n : ℕ} {H : BasePoly}
    (hp : HomogeneousDatum p n H) : goodBase H = goodParameters p := by
  have he := hp.evaluation (K := ℚ) ![0,1,1,0,1,2] (by change (1:ℚ) ≠ 0; norm_num) (by change (1:ℚ) ≠ 0; norm_num)
  simpa [QuadricContactClearing.goodBase, goodParameters, ParameterSpecialization.point] using he

theorem exists_uniform_homogeneousDatum {ι : Type*} [Fintype ι]
    (p : ι → Parameters) : ∃ (n : ℕ) (H : ι → BasePoly), ∀ i, HomogeneousDatum (p i) n (H i) := by
  classical
  let n := ∑ i, (p i).totalDegree
  refine ⟨n, fun i => CommonDenominatorSubstitution.cleared (p i) ac clearingCoordinates n, ?_⟩
  intro i
  apply homogeneousDatum_of_degree
  exact Finset.single_le_sum (fun j _ => Nat.zero_le (p j).totalDegree) (Finset.mem_univ i)

/-- A finite family of regular coefficients has a good common denominator. -/
theorem regular_common_denominator {ι : Type*} [Finite ι]
    (z : ι → RegularSpecialization.Coefficients goodParameters) :
    ∃ q : Parameters, goodParameters q ≠ 0 ∧ ∃ p : ι → Parameters,
      ∀ i, algebraMap Parameters (RegularSpecialization.Coefficients goodParameters) (p i) =
        algebraMap Parameters (RegularSpecialization.Coefficients goodParameters) q * z i := by
  obtain ⟨q, hq⟩ := IsLocalization.exist_integer_multiples_of_finite
    (RegularSpecialization.denominators goodParameters) z
  choose p hp using hq
  refine ⟨q, q.property, p, ?_⟩
  intro i
  simpa [Algebra.smul_def] using hp i

/-- Matching-degree numerator/denominator encodings preserving good specialization. -/
theorem regular_uniform_homogeneous_clearing {ι : Type*} [Fintype ι]
    (z : ι → RegularSpecialization.Coefficients goodParameters) :
    ∃ (n : ℕ) (q : Parameters) (p : ι → Parameters) (D : BasePoly) (N : ι → BasePoly),
      HomogeneousDatum q n D ∧ goodBase D ≠ 0 ∧
      (∀ i, HomogeneousDatum (p i) n (N i)) ∧
      (∀ i, algebraMap Parameters (RegularSpecialization.Coefficients goodParameters) (p i) =
        algebraMap Parameters (RegularSpecialization.Coefficients goodParameters) q * z i) := by
  classical
  obtain ⟨q, hq, p, hp⟩ := regular_common_denominator z
  obtain ⟨n, H, hh⟩ := exists_uniform_homogeneousDatum (fun i : Option ι => i.elim q p)
  refine ⟨n, q, p, H none, fun i => H (some i), hh none, ?_, fun i => hh (some i), hp⟩
  rw [(hh none).goodBase]
  exact hq

end QuadricContactClearing

#print axioms QuadricContactClearing.regular_uniform_homogeneous_clearing
