import Proposal.SymmetricNegativeJacobianQuotient
import Proposal.SymmetricSmallBidegrees

/-! Every multiplier in the complementary bidegree produces one of the
twelve actual negative Jacobian directions, or a linear combination thereof.
The low-degree monomial classification is tied to the actual weights. -/

noncomputable section

namespace SymmetricNegativeJacobian

open MvPolynomial SymmetricNegativeSource
open scoped BigOperators

set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

def ambientDirectionSpan : Submodule ℂ Poly :=
  Submodule.span ℂ (Set.range direction)

def complementaryBidegree (i : Fin 5) : ℕ × ZMod 2 :=
  ((bidegreeWeight i).1, 1 + (bidegreeWeight i).2)

@[simp] theorem complementaryBidegree_zero : complementaryBidegree 0 = (1,1) := by decide
@[simp] theorem complementaryBidegree_one : complementaryBidegree 1 = (1,1) := by decide
@[simp] theorem complementaryBidegree_two : complementaryBidegree 2 = (1,0) := by decide
@[simp] theorem complementaryBidegree_three : complementaryBidegree 3 = (1,0) := by decide
@[simp] theorem complementaryBidegree_four : complementaryBidegree 4 = (2,1) := by decide

theorem complementary_add_derivative (i : Fin 5) :
    complementaryBidegree i + derivativeBidegree i = (6,1) := by
  fin_cases i <;> decide

theorem bidegree_exponent_conditions (e : Fin 5 →₀ ℕ) (n : ℕ) (b : ZMod 2)
    (h : Finsupp.weight bidegreeWeight e = (n,b)) :
    weightedDegree e = n ∧ (e 2 + e 3) % 2 = b.val := by
  rw [bidegree_formula] at h
  refine ⟨congrArg Prod.fst h, ?_⟩
  have hs := congrArg Prod.snd h
  simpa only [ZMod.val_natCast] using congrArg ZMod.val hs

/-- Each allowed monomial multiplier is literally one of the twelve listed ones. -/
theorem complementary_monomial (i : Fin 5) (e : Fin 5 →₀ ℕ)
    (h : Finsupp.weight bidegreeWeight e = complementaryBidegree i) :
    ∃ j : Fin 12, partialIndex j = i ∧
      map (Int.castRingHom ℂ) (multiplier j) = monomial e 1 := by
  fin_cases i
  · change Finsupp.weight bidegreeWeight e = complementaryBidegree (0 : Fin 5) at h
    rw [complementaryBidegree_zero] at h
    obtain ⟨hd,hp⟩ := bidegree_exponent_conditions e 1 1 h
    norm_num at hp
    rcases odd_linear_exponent hd hp with rfl | rfl
    · exact ⟨0, rfl, by simp [multiplier, X]⟩
    · exact ⟨1, rfl, by simp [multiplier, X]⟩
  · change Finsupp.weight bidegreeWeight e = complementaryBidegree (1 : Fin 5) at h
    rw [complementaryBidegree_one] at h
    obtain ⟨hd,hp⟩ := bidegree_exponent_conditions e 1 1 h
    norm_num at hp
    rcases odd_linear_exponent hd hp with rfl | rfl
    · exact ⟨2, rfl, by simp [multiplier, X, Matrix.cons_val_two]⟩
    · exact ⟨3, rfl, by simp [multiplier, X, Matrix.cons_val_three]⟩
  · change Finsupp.weight bidegreeWeight e = complementaryBidegree (2 : Fin 5) at h
    rw [complementaryBidegree_two] at h
    obtain ⟨hd,hp⟩ := bidegree_exponent_conditions e 1 0 h
    norm_num at hp
    rcases even_linear_exponent hd hp with rfl | rfl
    · exact ⟨4, rfl, by simp [multiplier, X, Matrix.cons_val_four]⟩
    · exact ⟨5, rfl, by
        change map (Int.castRingHom ℂ) (X 1) = _
        rw [map_X]; rfl⟩
  · change Finsupp.weight bidegreeWeight e = complementaryBidegree (3 : Fin 5) at h
    rw [complementaryBidegree_three] at h
    obtain ⟨hd,hp⟩ := bidegree_exponent_conditions e 1 0 h
    norm_num at hp
    rcases even_linear_exponent hd hp with rfl | rfl
    · exact ⟨6, rfl, by
        change map (Int.castRingHom ℂ) (X 0) = _
        rw [map_X]; rfl⟩
    · exact ⟨7, rfl, by
        change map (Int.castRingHom ℂ) (X 1) = _
        rw [map_X]; rfl⟩
  · change Finsupp.weight bidegreeWeight e = complementaryBidegree (4 : Fin 5) at h
    rw [complementaryBidegree_four] at h
    obtain ⟨hd,hp⟩ := bidegree_exponent_conditions e 2 1 h
    norm_num at hp
    rcases odd_quadratic_exponent hd hp with rfl | rfl | rfl | rfl
    · exact ⟨8, rfl, by
        change map (Int.castRingHom ℂ) (X 0 * X 2) = _
        simp [monomial_add_single, ← C_mul_X_pow_eq_monomial]⟩
    · exact ⟨9, rfl, by
        change map (Int.castRingHom ℂ) (X 0 * X 3) = _
        simp [monomial_add_single, ← C_mul_X_pow_eq_monomial]⟩
    · exact ⟨10, rfl, by
        change map (Int.castRingHom ℂ) (X 1 * X 2) = _
        simp [monomial_add_single, ← C_mul_X_pow_eq_monomial]⟩
    · exact ⟨11, rfl, by
        change map (Int.castRingHom ℂ) (X 1 * X 3) = _
        simp [monomial_add_single, ← C_mul_X_pow_eq_monomial]⟩

theorem homogeneous_mul_partial_mem_directionSpan (i : Fin 5) (p : Poly)
    (hp : p.IsWeightedHomogeneous bidegreeWeight (complementaryBidegree i)) :
    p * pderiv i WeightedFiberSmoothness.weightedG ∈ ambientDirectionSpan := by
  rw [p.as_sum, Finset.sum_mul]
  apply Submodule.sum_mem
  intro e he
  obtain ⟨j,hji,hm⟩ := complementary_monomial i e (hp (mem_support_iff.mp he))
  have hj : direction j ∈ ambientDirectionSpan := Submodule.subset_span ⟨j,rfl⟩
  have hs := ambientDirectionSpan.smul_mem (coeff e p) hj
  convert hs using 1
  rw [smul_eq_C_mul, direction, hji, hm, ← mul_assoc, C_mul_monomial, mul_one]

#print axioms complementary_monomial
#print axioms homogeneous_mul_partial_mem_directionSpan

end SymmetricNegativeJacobian
