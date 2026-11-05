import HodgeComputer.Constructions.HoldoutCover.PolynomialFamilyBridge
import HodgeComputer.Constructions.HoldoutCover.FiniteResidueClearing
import HodgeComputer.Constructions.HoldoutCover.HomogeneousCertificate

/-!
Extracted from fqlx's accepted PR #150. The original declaration namespace
is retained for compatibility; the hypotheses are independent of its target.

Algebraic closure of a polynomial curve family on a six-variable hypersurface. This file assembles the existing polynomial integration,
finite trace, and denominator clearing theorems. It assumes actual curve-family
data and makes no assertion that such data have already been constructed.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace ReflectionCoupledFano
open HoldoutConstruction MvPolynomial
open scoped BigOperators

variable {B K L T : Type*} [CommRing B] [IsDomain B]
variable [Field K] [CharZero K] [Algebra B K] [IsFractionRing B K]
variable [Field L] [CharZero L] [Algebra K L] [FiniteDimensional K L]
variable [CommRing T]

/-- A verified polynomial family yields unrestricted normalized polynomial
data. The application imposes homogeneity after its coordinate transport. -/
theorem normalized_data_from_polynomial_family
    (π : HodgeComputer.Poly →+* B) (hπ : Function.Surjective π)
    (f A : HodgeComputer.Poly)
    (hirr : Irreducible f) (hker : ∀ p, π p = 0 ↔ f ∣ p)
    (hg0 : algebraMap B K (π (pderiv 0 f)) ≠ 0)
    (D : Fin 5 → Derivation ℤ L L)
    (M : Matrix (Fin 6) (Fin 6) L) (ψ : Fin 6 → L)
    (χ : T →+* L) (t : L) (timeIndex : Fin 5)
    (hconst : ∀ a, D timeIndex (χ a) = 0)
    (htime : D timeIndex t = 1)
    (hdet : M.det ≠ 0)
    (hM0 : ∀ j, M j 0 = ψ j)
    (hMX : ∀ k i, M k i.succ =
      D i (finiteQuotientEvaluation (K := K) π (MvPolynomial.X k)))
    (hψ : (∑ j, finiteQuotientEvaluation (K := K) π (pderiv j f) * ψ j) = 1)
    (hDC : ∀ i r, D i (finiteQuotientEvaluation (K := K) π (MvPolynomial.C r)) = 0)
    (hcommute : ∀ i j, Function.Commute (D i) (D j))
    (hpolyC : ∀ r, finiteQuotientEvaluation (K := K) π (MvPolynomial.C r) ∈
      (Polynomial.eval₂RingHom χ t).range)
    (hpolyX : ∀ i, finiteQuotientEvaluation (K := K) π (MvPolynomial.X i) ∈
      (Polynomial.eval₂RingHom χ t).range)
    (hpolyψ : ∀ i, ψ i ∈ (Polynomial.eval₂RingHom χ t).range)
    (hDpoly : ∀ i x, x ∈ (Polynomial.eval₂RingHom χ t).range →
      D i x ∈ (Polynomial.eval₂RingHom χ t).range) :
    ∃ d : HodgeComputer.Poly, ∃ N : Fin 6 → HodgeComputer.Poly,
      ∃ Q : HodgeComputer.Poly,
        d ≠ 0 ∧ IsRelPrime f d ∧
        HodgeTestbed.directional f N = A * d ∧
        HodgeTestbed.divergenceNumerator d N = f * Q := by
  let E : Fin 5 → Derivation ℤ K K := fun i =>
    residueTangent π hπ (integerPartial 0) (integerPartial i.succ) f hker hg0
  let E' : Fin 5 → Derivation ℤ L L := fun i => extendFiniteDerivation (L := L) (E i)
  let ρ := finiteQuotientEvaluation (K := K) (L := L) π
  have hf : ρ f = 0 := by
    change algebraMap K L (algebraMap B K (π f)) = 0
    rw [(hker f).mpr (dvd_refl _), map_zero, map_zero]
  have hg : ρ (pderiv 0 f) ≠ 0 :=
    (map_ne_zero (algebraMap K L)).2 hg0
  have hE (i : Fin 5) (p : HodgeComputer.Poly) :
      E' i (ρ p) = ρ (pderiv i.succ p) -
        ρ (pderiv i.succ f) / ρ (pderiv 0 f) * ρ (pderiv 0 p) := by
    change extendFiniteDerivation (L := L) (E i)
      (algebraMap K L (algebraMap B K (π p))) = _
    rw [extendFiniteDerivation_apply]
    dsimp only [E]
    rw [residueTangent_apply]
    simp only [map_sub, map_mul, map_div₀, integerPartial_apply]
    rfl
  obtain ⟨w, hw⟩ := residue_solution_from_polynomial_curve (K := K)
    π hπ f A D E' M ψ χ t timeIndex hconst htime hf hg hdet hM0 hMX hψ
    hDC hcommute hE hpolyC hpolyX hpolyψ hDpoly
  have heq :
      algebraMap K L
        ((algebraMap B K (π (integerPartial 0 A)) *
            algebraMap B K (π (integerPartial 0 f)) -
          algebraMap B K (π A) *
            algebraMap B K (π (integerPartial 0 (integerPartial 0 f)))) /
          (algebraMap B K (π (integerPartial 0 f)))^2) +
        ∑ i, (E' i (w i) -
          w i * E' i (algebraMap K L (algebraMap B K (π (integerPartial 0 f)))) /
            algebraMap K L (algebraMap B K (π (integerPartial 0 f)))) = 0 := by
    have hs : ρ (pderiv 0 A) / ρ (pderiv 0 f) -
        ρ A * ρ (pderiv 0 (pderiv 0 f)) / (ρ (pderiv 0 f))^2 =
        (ρ (pderiv 0 A) * ρ (pderiv 0 f) -
          ρ A * ρ (pderiv 0 (pderiv 0 f))) / (ρ (pderiv 0 f))^2 := by
      field_simp
      <;> ring
    have hw' :
        (ρ (pderiv 0 A) * ρ (pderiv 0 f) -
          ρ A * ρ (pderiv 0 (pderiv 0 f))) / (ρ (pderiv 0 f))^2 +
          residueDivergence E' (ρ (pderiv 0 f)) w = 0 := by
      rw [hw, hs]
      ring
    convert hw' using 1 <;>
      simp only [ρ, finiteQuotientEvaluation, RingHom.comp_apply,
        map_div₀, map_sub, map_mul, map_pow, integerPartial_apply,
        residueDivergence, fieldDivergence, Finset.sum_sub_distrib,
        div_eq_mul_inv, map_inv₀, Finset.sum_mul] <;> ring
  obtain ⟨d, N0, N, Q, hd, hlegal, hnormal, hdiv, _⟩ :=
    finite_residue_solution_clearing_canonical (K := K) (L := L)
      π hπ (integerPartial 0) (fun i : Fin 5 => integerPartial i.succ) f A w
      hirr hker hg0 (fun i => integerPartial_commute i.succ 0 f) heq
  refine ⟨d, Fin.cases N0 N, Q, hd, hlegal, ?_, ?_⟩
  · simpa only [HodgeTestbed.directional, Fin.sum_univ_succ,
      Fin.cases_zero, Fin.cases_succ, integerPartial, Derivation.restrictScalars_apply,
      Derivation.coeFn_coe, mul_comm] using hnormal
  · simpa only [HodgeTestbed.divergenceNumerator, HodgeTestbed.divergence,
      HodgeTestbed.directional, residueDivNum, Fin.sum_univ_succ,
      Fin.cases_zero, Fin.cases_succ, integerPartial, Derivation.restrictScalars_apply,
      Derivation.coeFn_coe, mul_comm] using hdiv

end ReflectionCoupledFano

#print axioms ReflectionCoupledFano.normalized_data_from_polynomial_family
