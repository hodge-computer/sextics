import Proposal.GeometricHodgeTwistRatios
import Proposal.GeometricHodgeTwistCech

/-!
# Change of weight-one frame for Laurent monomials

On the common coordinate torus, all four weight-one coordinate ratios
are units. The weight-two coordinate is regular there. Their monomial
of integral degree t transforms by precisely the t-th power of the
transition unit, including for negative twists and Laurent exponents.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace CycleQ2HodgeTwistMonomials
open AlgebraicGeometry CycleQ2HodgeTwistRatios CycleQ2HodgeTwistCech
open CycleQ2GeometricHodgeThreefold
open CycleQ2GenericSexticGradient (CoeffRing)

variable {R : Type} [CommRing R] (φ : CoeffRing →+* R) (V : (threefold φ).Opens)
variable (hV : ∀ i, V ≤ U φ i)

def units (i : Vertex) (e : Exp) : Γ(threefold φ,V)ˣ :=
  ∏ a, transition φ i a V (hV i) (hV a) ^ e a

theorem units_change (i k : Vertex) (e : Exp) :
    units φ V hV i e = transition φ i k V (hV i) (hV k) ^ (∑ a, e a) * units φ V hV k e := by
  unfold units
  let u := transition φ i k V (hV i) (hV k)
  have hpow (S : Finset Vertex) : u ^ (∑ a ∈ S, e a) = ∏ a ∈ S, u ^ e a := by
    induction S using Finset.induction_on with
    | empty => simp
    | insert a S ha ih => simp [ha, zpow_add, ih]
  rw [show transition φ i k V (hV i) (hV k) ^ (∑ a, e a) = _ from hpow Finset.univ,
    ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro a _
  rw [← mul_zpow, show u * transition φ k a V (hV k) (hV a) =
    transition φ i a V (hV i) (hV a) from transition_comp φ i k a V _ _ _]

def weightTwo (i : Vertex) : Γ(threefold φ,V) :=
  normalized φ i (coord φ (Fin.last 4)) (show coord φ (Fin.last 4) ∈ grade φ 2 from
    coord_mem_grade φ (Fin.last 4)) V (hV i)

theorem weightTwo_change (i k : Vertex) :
    weightTwo φ V hV i = (transition φ i k V (hV i) (hV k) : Γ(threefold φ,V)) ^ 2 * weightTwo φ V hV k :=
  normalized_change φ i k _ _ _ (hV i) (hV k)

def monomial (i : Vertex) (j : Fin 3) (e : Exp) : Γ(threefold φ,V) :=
  (units φ V hV i e : Γ(threefold φ,V)) * weightTwo φ V hV i ^ j.val

/-- The literal homogeneous fraction transforms by the degree-t line-bundle cocycle. -/
theorem monomial_change (i k : Vertex) (j : Fin 3) (e : Exp) {t : ℤ}
    (ht : (∑ a, e a) + 2 * (j.val : ℤ) = t) :
    monomial φ V hV i j e =
      (transition φ i k V (hV i) (hV k) ^ t : Γ(threefold φ,V)ˣ).val * monomial φ V hV k j e := by
  let u := transition φ i k V (hV i) (hV k)
  have hw : (u.val ^ 2) ^ j.val = (u ^ (2 * (j.val : ℤ))).val := by
    rw [zpow_mul, zpow_natCast]
    rfl
  rw [monomial, units_change φ V hV i k, weightTwo_change φ V hV i k, mul_pow]
  change ((u ^ (∑ a, e a)) * units φ V hV k e).val *
    ((u.val ^ 2) ^ j.val * weightTwo φ V hV k ^ j.val) =
    (u ^ t).val * ((units φ V hV k e).val * weightTwo φ V hV k ^ j.val)
  rw [hw, ← ht, zpow_add, Units.val_mul, Units.val_mul]
  ring

/-- Evaluation of a finite Laurent expansion in a single frame of the common torus. -/
def evaluate (ρ : R →+* Γ(threefold φ,V)) (i : Vertex) (p : NormalForm R) : Γ(threefold φ,V) :=
  ∑ j, (p j).sum fun e c => ρ c * monomial φ V hV i j e

theorem evaluate_change (ρ : R →+* Γ(threefold φ,V)) (i k : Vertex) {t : ℤ}
    {S : Finset Vertex} (p : sections R t S) :
    evaluate φ V hV ρ i p.val = (transition φ i k V (hV i) (hV k) ^ t : Γ(threefold φ,V)ˣ).val *
      evaluate φ V hV ρ k p.val := by
  rw [evaluate, evaluate, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finsupp.sum, Finsupp.sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  have hallowed : Allowed t S j e := by
    by_contra hf
    exact (Finsupp.mem_support_iff.mp he) (p.property j e hf)
  rw [monomial_change φ V hV i k j e hallowed.1]
  ring

end CycleQ2HodgeTwistMonomials
end

#print axioms CycleQ2HodgeTwistMonomials.monomial_change

#print axioms CycleQ2HodgeTwistMonomials.evaluate_change
