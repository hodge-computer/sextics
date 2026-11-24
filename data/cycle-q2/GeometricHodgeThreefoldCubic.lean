import Proposal.GeometricHodgeThreefold
import Mathlib.RingTheory.AdjoinRoot

/-!
# The cubic equation in each weight-one chart

Set a weight-one variable to one, take the other three weight-one variables
as affine base coordinates and leave the weight-two variable as the
univariate indeterminate. Every tail monomial has degree at most two in
that indeterminate. Inverting the original leading parameter makes the
equation monic, with power basis of length three.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 3000
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2GeometricHodgeThreefoldCubic

open MvPolynomial CycleQ2IncidenceNormalForm
open CycleQ2GenericSexticGradient (CoeffRing universalF)
open CycleQ2GeometricHodgeThreefold (equation vertexCoefficient)

variable {R : Type} [CommRing R]
abbrev Base (R : Type) [CommRing R] := MvPolynomial (Fin 3) R

def baseValue (i : Fin 4) : Fin 4 → Base R :=
  i.insertNth 1 X

def expand (i : Fin 4) : MvPolynomial (Fin 5) R →ₐ[R] Polynomial (Base R) :=
  aeval (Fin.snoc (fun j : Fin 4 => Polynomial.C (baseValue i j)) Polynomial.X)

def baseMonomial (i : Fin 4) (d : Fin 5 →₀ ℕ) (a : R) : Base R :=
  C a * ∏ j : Fin 4, baseValue i j ^ d j.castSucc

theorem expand_monomial (i : Fin 4) (d : Fin 5 →₀ ℕ) (a : R) :
    expand i (monomial d a) = Polynomial.monomial (d 4) (baseMonomial i d a) := by
  classical
  rw [expand, aeval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
    Fin.prod_univ_castSucc, ← Polynomial.C_mul_X_pow_eq_monomial]
  simp only [Fin.snoc_castSucc, Fin.snoc_last, baseMonomial, map_mul, map_prod, map_pow]
  change Polynomial.C (C a) * (_ * _) = (Polynomial.C (C a) * _) * _
  rw [mul_assoc]
  rfl

def tail (φ : CoeffRing →+* R) (i : Fin 4) (b : R) : Polynomial (Base R) :=
  ∑ e : FullSexticTailIndex, Polynomial.monomial (e.val.val 4).val
    (C b * baseMonomial i (fullExponentOf e.val.val) (φ (X e.val)))

theorem tail_degree (φ : CoeffRing →+* R) (i : Fin 4) (b : R) :
    (tail φ i b).degree < 3 := by
  apply (Polynomial.degree_sum_le _ _).trans_lt
  refine (Finset.sup_lt_iff (show (⊥ : WithBot ℕ) < 3 by decide)).mpr ?_
  intro e _
  exact (Polynomial.degree_monomial_le _ _).trans_lt (WithBot.coe_lt_coe.mpr e.property)

def cubic (φ : CoeffRing →+* R) (i : Fin 4) (h : IsUnit (φ vertexCoefficient)) :
    Polynomial (Base R) := Polynomial.X ^ 3 + tail φ i (↑h.unit⁻¹)

theorem cubic_monic (φ : CoeffRing →+* R) (i : Fin 4) (h : IsUnit (φ vertexCoefficient)) :
    (cubic φ i h).Monic := by
  unfold cubic
  apply Polynomial.monic_X_pow_add
  exact tail_degree φ i _

theorem cubic_natDegree [Nontrivial R] (φ : CoeffRing →+* R) (i : Fin 4)
    (h : IsUnit (φ vertexCoefficient)) : (cubic φ i h).natDegree = 3 := by
  apply Polynomial.natDegree_eq_of_degree_eq_some
  rw [cubic, Polynomial.degree_add_eq_left_of_degree_lt, Polynomial.degree_X_pow]
  rw [Polynomial.degree_X_pow]
  exact (tail_degree φ i (↑h.unit⁻¹)).trans_le (by norm_num)

theorem expand_equation (φ : CoeffRing →+* R) (i : Fin 4) (h : IsUnit (φ vertexCoefficient)) :
    expand i (equation φ) = Polynomial.C (C (φ vertexCoefficient)) * cubic φ i h := by
  classical
  rw [CycleQ2GeometricHodgeThreefold.equation_raw]
  change expand i (monomial (Finsupp.single 4 3) (φ vertexCoefficient) +
    ∑ e : FullSexticTailIndex, monomial (fullExponentOf e.val.val) (φ (X e.val))) = _
  simp only [map_add, map_sum, expand_monomial, cubic, mul_add, tail, Finset.mul_sum]
  apply congrArg₂ (· + ·)
  · rw [Polynomial.C_mul_X_pow_eq_monomial, Finsupp.single_eq_same]
    apply congrArg (Polynomial.monomial 3)
    have hz (j : Fin 4) : (Finsupp.single (4 : Fin 5) (3 : ℕ)) j.castSucc = 0 :=
      Finsupp.single_eq_of_ne (Fin.castSucc_ne_last j)
    simp [baseMonomial, hz]
  · apply Finset.sum_congr rfl
    intro e _
    have hu : φ vertexCoefficient * (↑h.unit⁻¹ : R) = 1 :=
      (congrArg (· * (↑h.unit⁻¹ : R)) h.unit_spec.symm).trans h.unit.mul_inv
    rw [Polynomial.C_mul_monomial, ← mul_assoc, ← map_mul, hu,
      map_one, one_mul, fullExponentOf_apply]

/-- The powers 1, w and w² in the literal monic quotient. -/
def basis [Nontrivial R] (φ : CoeffRing →+* R) (i : Fin 4)
    (h : IsUnit (φ vertexCoefficient)) :
    Module.Basis (Fin 3) (Base R) (AdjoinRoot (cubic φ i h)) :=
  (AdjoinRoot.powerBasisAux' (cubic_monic φ i h)).reindex (finCongr (cubic_natDegree φ i h))

theorem basis_apply [Nontrivial R] (φ : CoeffRing →+* R) (i : Fin 4)
    (h : IsUnit (φ vertexCoefficient)) (j : Fin 3) :
    basis φ i h j = (AdjoinRoot.root (cubic φ i h)) ^ j.val := by
  rw [basis, Module.Basis.reindex_apply]
  exact (AdjoinRoot.powerBasis' (cubic_monic φ i h)).basis_eq_pow _

end CycleQ2GeometricHodgeThreefoldCubic
end

#print axioms CycleQ2GeometricHodgeThreefoldCubic.expand_equation
#print axioms CycleQ2GeometricHodgeThreefoldCubic.basis_apply
