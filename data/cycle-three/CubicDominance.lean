import Proposal.CyclicCubic
import HodgeComputer.Constructions.CyclicCubic.Map
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.Algebraic.Defs
import Mathlib.RingTheory.Derivation.Basic

/-! A nonzero relative differential proves transcendence, hence nonconstancy
of the cubic-to-Jacobian coordinate. This is a characteristic-zero statement:
the minimal polynomial is separable and its derivative cannot vanish at its
root. The hypotheses about the base field and the differential are explicit;
constructing the physical-field embedding remains a separate obligation.
Prepared with OpenAI Codex assistance for hodgepodgeconjecture. -/
noncomputable section
namespace CycleCubicDominance
variable {B K : Type*} [Field B] [CharZero B] [Field K] [Algebra B K]

lemma transcendental_of_derivative (D : Derivation B K K) (x : K)
    (hx : D x ≠ 0) : Transcendental B x := by
  intro halg
  have hi : IsIntegral B x := halg.isIntegral
  have hp := (minpoly.irreducible hi).separable
  have hn : Polynomial.aeval x (minpoly B x).derivative ≠ 0 :=
    hp.aeval_derivative_ne_zero (minpoly.aeval B x)
  have hd := D.map_aeval (minpoly B x) x
  rw [minpoly.aeval,D.map_zero,smul_eq_mul] at hd
  exact hx ((mul_eq_zero.mp hd.symm).resolve_left hn)

lemma transcendental_of_differential [CharZero K]
    (D : Derivation B K K) (x y g : K) (hg : g ≠ 0)
    (hd : D x/(2*y)=3/g) : Transcendental B x := by
  apply transcendental_of_derivative D x
  intro hx
  rw [hx,zero_div] at hd
  exact (div_ne_zero (by norm_num : (3:K) ≠ 0) hg) hd.symm

end CycleCubicDominance
#print axioms CycleCubicDominance.transcendental_of_differential
