import ProjectorCore
import Mathlib.Tactic.Module
import Mathlib.Tactic

/-!
The character decomposition used in the two-reflection support theorem.
This proves its linear-algebra step. It does not assert the geometric support
or cohomology hypotheses for a variety.
-/

noncomputable section
namespace TwoReflectionSectors

variable {K V : Type*} [Field K] [CharZero K]
  [AddCommGroup V] [Module K V]

def positive (r : V →ₗ[K] V) : V →ₗ[K] V :=
  (1 / 2 : K) • (LinearMap.id + r)

def negative (r : V →ₗ[K] V) : V →ₗ[K] V :=
  (1 / 2 : K) • (LinearMap.id - r)

theorem positive_apply (r : V →ₗ[K] V) (v : V) :
    positive r v = (1 / 2 : K) • (v + r v) := rfl

theorem negative_apply (r : V →ₗ[K] V) (v : V) :
    negative r v = (1 / 2 : K) • (v - r v) := rfl

theorem positive_add_negative (r : V →ₗ[K] V) (v : V) :
    positive r v + negative r v = v := by
  rw [positive_apply, negative_apply]
  module

theorem positive_fixed (r : V →ₗ[K] V) (hr : Function.Involutive r) (v : V) :
    r (positive r v) = positive r v := by
  simp only [positive_apply, map_smul, map_add, hr v]
  module

theorem negative_negated (r : V →ₗ[K] V) (hr : Function.Involutive r) (v : V) :
    r (negative r v) = -negative r v := by
  simp only [negative_apply, map_smul, map_sub, hr v]
  module

theorem commute_positive (a r : V →ₗ[K] V) (h : Function.Commute a r) (v : V) :
    a (positive r v) = positive r (a v) := by
  simp only [positive_apply, map_smul, map_add, h v]

theorem commute_negative (a r : V →ₗ[K] V) (h : Function.Commute a r) (v : V) :
    a (negative r v) = negative r (a v) := by
  simp only [negative_apply, map_smul, map_sub, h v]

/-- Every vector splits into a first-positive, second-positive and simultaneous
negative part. The third part has exactly the beta/sigma characters required
by the weighted-threefold argument when the original vector is tau-invariant. -/
theorem three_sector_decomposition
    (τ r s : V →ₗ[K] V)
    (hr : Function.Involutive r) (hs : Function.Involutive s)
    (hτr : Function.Commute τ r) (hτs : Function.Commute τ s)
    (hrs : Function.Commute r s)
    (v : V) (hτv : τ v = v) :
    ∃ p q z : V,
      v = p + q + z ∧
      τ p = p ∧ r p = p ∧
      τ q = q ∧ s q = q ∧
      τ z = z ∧ r z = -z ∧ s z = -z ∧
      r (s z) = z ∧ τ (s z) = -z := by
  let p := positive r v
  let n := negative r v
  let q := positive s n
  let z := negative s n
  have hv : v = p + n := (positive_add_negative r v).symm
  have hn : n = q + z := (positive_add_negative s n).symm
  have hτn : τ n = n := by
    dsimp [n]
    rw [commute_negative τ r hτr, hτv]
  have hrn : r n = -n := negative_negated r hr v
  have hτz : τ z = z := by
    dsimp [z]
    rw [commute_negative τ s hτs, hτn]
  have hrz : r z = -z := by
    dsimp [z]
    rw [commute_negative r s hrs, hrn, map_neg]
  have hsz : s z = -z := negative_negated s hs n
  refine ⟨p, q, z, ?_, ?_, positive_fixed r hr v, ?_,
    positive_fixed s hs n, hτz, hrz, hsz, ?_, ?_⟩
  · rw [hv, hn, add_assoc]
  · dsimp [p]
    rw [commute_positive τ r hτr, hτv]
  · dsimp [q]
    rw [commute_positive τ s hτs, hτn]
  · rw [hsz, map_neg, hrz, neg_neg]
  · rw [hsz, map_neg, hτz]

/-- If a linear subspace contains both reflection-positive sectors and the
remaining beta-positive/sigma-negative sector, it contains every tau-fixed
vector. The hypothesis does not assert that any geometric support has this
property; it isolates the final linear step of the paper's proof. -/
theorem invariant_supported_of_three_sectors
    (τ r s : V →ₗ[K] V)
    (hr : Function.Involutive r) (hs : Function.Involutive s)
    (hτr : Function.Commute τ r) (hτs : Function.Commute τ s)
    (hrs : Function.Commute r s)
    (N : Submodule K V)
    (hfirst : ∀ v, τ v = v → r v = v → v ∈ N)
    (hsecond : ∀ v, τ v = v → s v = v → v ∈ N)
    (hresidual : ∀ v, τ v = v → r (s v) = v → τ (s v) = -v → v ∈ N)
    (v : V) (hv : τ v = v) : v ∈ N := by
  obtain ⟨p, q, z, hsplit, hτp, hrp, hτq, hsq, hτz, _, _, hβz, hσz⟩ :=
    three_sector_decomposition τ r s hr hs hτr hτs hrs v hv
  rw [hsplit]
  exact N.add_mem (N.add_mem (hfirst p hτp hrp) (hsecond q hτq hsq))
    (hresidual z hτz hβz hσz)

#print axioms three_sector_decomposition
#print axioms invariant_supported_of_three_sectors

end TwoReflectionSectors
