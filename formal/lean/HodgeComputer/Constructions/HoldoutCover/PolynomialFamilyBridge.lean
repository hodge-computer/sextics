import HodgeComputer.Constructions.HoldoutCover.FiniteDifferentials
import HodgeComputer.Constructions.HoldoutCover.PolynomialCalculus
import HodgeComputer.Constructions.HoldoutCover.PolynomialFamily

/- Source component: PolynomialFamilyBridge -/
section
/-!
Bridge from an actual polynomial curve in a finite extension of a
hypersurface function field to the generic polynomial-family residue
primitive. The chain rule, inverse coordinate matrix, Hessian identities,
and polynomiality requirements are derived here from concrete algebraic
inputs. No certificate or geometric existence premise is introduced.
-/

noncomputable section

namespace HoldoutConstruction

open scoped BigOperators

section PolynomialImages

variable {R L σ : Type*} [CommRing R] [Field L]

theorem polynomial_image_mem_subring (ρ : MvPolynomial σ R →+* L)
    (S : Subring L) (hC : ∀ r, ρ (MvPolynomial.C r) ∈ S)
    (hX : ∀ i, ρ (MvPolynomial.X i) ∈ S) (p : MvPolynomial σ R) : ρ p ∈ S := by
  induction p using MvPolynomial.induction_on with
  | C r => exact hC r
  | add p q hp hq => rw [map_add]; exact S.add_mem hp hq
  | mul_X p i hp => rw [map_mul]; exact S.mul_mem hp (hX i)

theorem derivation_polynomial_ringHom_chain [Fintype σ] [DecidableEq σ]
    (D : Derivation ℤ L L) (ρ : MvPolynomial σ R →+* L)
    (hC : ∀ r, D (ρ (MvPolynomial.C r)) = 0) (p : MvPolynomial σ R) :
    D (ρ p) = ∑ i, ρ (MvPolynomial.pderiv i p)*D (ρ (MvPolynomial.X i)) := by
  have heval : MvPolynomial.eval₂Hom (ρ.comp MvPolynomial.C)
      (fun i => ρ (MvPolynomial.X i)) = ρ := by
    ext i <;> simp
  have h := derivation_eval₂_chain D (ρ.comp MvPolynomial.C)
    (fun i => ρ (MvPolynomial.X i)) hC p
  simpa only [heval] using h

end PolynomialImages

section DerivationCombination

variable {L ι : Type*} [Field L] [Fintype ι]

def derivationLinearCombination (D : ι → Derivation ℤ L L) (a : ι → L) :
    Derivation ℤ L L := ∑ i, a i • D i

theorem derivationLinearCombination_apply (D : ι → Derivation ℤ L L)
    (a : ι → L) (x : L) :
    derivationLinearCombination D a x = ∑ i, a i*D i x := by
  change Derivation.coeFnAddMonoidHom (∑ i, a i • D i) x = _
  rw [map_sum]
  simp only [Finset.sum_apply, Derivation.coeFnAddMonoidHom_apply,
    Derivation.smul_apply, smul_eq_mul]

end DerivationCombination

section FullTangentMatrix

variable {L : Type*} [Field L] {n : ℕ}

/-- The inverse tangent matrix gives the full implicit-coordinate
derivative, including the eliminated coordinate X0. -/
theorem tangentInverse_full_coordinate
    (M N : Matrix (Fin (n+1)) (Fin (n+1)) L)
    (g ψ : Fin (n+1) → L) (hg0 : g 0 ≠ 0) (hMN : M*N = 1)
    (hN : ∀ j, N 0 j = g j) (hM : ∀ j, M j 0 = ψ j)
    (k : Fin (n+1)) (j : Fin n) :
    (∑ i : Fin n, M k i.succ*tangentInverse N g i j) =
      (if k=j.succ then 1 else 0) -
        (g j.succ/g 0)*(if k=0 then 1 else 0) := by
  have h1 := congrArg
    (fun A : Matrix (Fin (n+1)) (Fin (n+1)) L => A k j.succ) hMN
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, hN, hM, Matrix.one_apply] at h1
  have htail : (∑ i : Fin n, M k i.succ*N i.succ j.succ) =
      (if k=j.succ then 1 else 0) - ψ k*g j.succ := by
    linear_combination h1
  have hzero := normal_inverse_tail_product M N g ψ hMN hN hM k
  have hsum : (∑ i : Fin n, M k i.succ*(N i.succ 0/g 0*g j.succ)) =
      (∑ i : Fin n, M k i.succ*N i.succ 0)*(g j.succ/g 0) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  simp only [tangentInverse, mul_sub, Finset.sum_sub_distrib]
  rw [hsum, htail, hzero]
  field_simp
  ring

end FullTangentMatrix

section FiniteQuotient

variable {R Q K L : Type*} [CommRing R] [CommRing Q] [IsDomain Q]
variable [Field K] [CharZero K] [Algebra Q K] [IsFractionRing Q K]
variable [Field L] [Algebra K L] [FiniteDimensional K L]
variable {n : ℕ}

def finiteQuotientEvaluation (π : MvPolynomial (Fin (n+1)) R →+* Q) :
    MvPolynomial (Fin (n+1)) R →+* L :=
  (algebraMap K L).comp ((algebraMap Q K).comp π)

omit [IsDomain Q] in
/-- The full tangent-coordinate identities determine the derivation on
the entire finite function-field extension, not just on coordinate images. -/
theorem finite_quotient_tangent_chain
    (π : MvPolynomial (Fin (n+1)) R →+* Q) (hπ : Function.Surjective π)
    (f : MvPolynomial (Fin (n+1)) R)
    (D E : Fin n → Derivation ℤ L L)
    (M N : Matrix (Fin (n+1)) (Fin (n+1)) L)
    (ψ : Fin (n+1) → L)
    (hMN : M*N = 1)
    (hN : ∀ j, N 0 j = finiteQuotientEvaluation (K := K) π (MvPolynomial.pderiv j f))
    (hM0 : ∀ j, M j 0 = ψ j)
    (hMX : ∀ k i, M k i.succ =
      D i (finiteQuotientEvaluation (K := K) π (MvPolynomial.X k)))
    (hg0 : finiteQuotientEvaluation (K := K) (L := L) π (MvPolynomial.pderiv 0 f) ≠ 0)
    (hDC : ∀ i r, D i (finiteQuotientEvaluation (K := K) π (MvPolynomial.C r)) = 0)
    (hE : ∀ j p, E j (finiteQuotientEvaluation (K := K) π p) =
      finiteQuotientEvaluation (K := K) π (MvPolynomial.pderiv j.succ p) -
        finiteQuotientEvaluation (K := K) π (MvPolynomial.pderiv j.succ f) /
          finiteQuotientEvaluation (K := K) π (MvPolynomial.pderiv 0 f) *
            finiteQuotientEvaluation (K := K) π (MvPolynomial.pderiv 0 p)) :
    ∀ j x, E j x = ∑ i, tangentInverse N
      (fun k => finiteQuotientEvaluation (K := K) π (MvPolynomial.pderiv k f)) i j * D i x := by
  let ρ := finiteQuotientEvaluation (K := K) (L := L) π
  let g : Fin (n+1) → L := fun k => ρ (MvPolynomial.pderiv k f)
  intro j
  let V := derivationLinearCombination D (fun i => tangentInverse N g i j)
  have hconstant (r : R) : E j (ρ (MvPolynomial.C r)) = V (ρ (MvPolynomial.C r)) := by
    rw [hE j, derivationLinearCombination_apply]
    simp only [ρ, MvPolynomial.pderiv_C, map_zero, hDC, mul_zero, sub_self,
      Finset.sum_const_zero]
  have hcoordinate (k : Fin (n+1)) : E j (ρ (MvPolynomial.X k)) = V (ρ (MvPolynomial.X k)) := by
    have hfield : E j (ρ (MvPolynomial.X k)) =
        (if k=j.succ then 1 else 0) - (g j.succ/g 0)*(if k=0 then 1 else 0) := by
      simpa only [MvPolynomial.pderiv_X, Pi.single_apply, apply_ite, map_one, map_zero]
        using hE j (MvPolynomial.X k)
    rw [hfield, derivationLinearCombination_apply]
    rw [← tangentInverse_full_coordinate M N g ψ hg0 hMN hN hM0 k j]
    apply Finset.sum_congr rfl
    intro i _
    rw [hMX]
    ring
  have hsame : E j = V :=
    derivations_ext_finite_quotient_fraction (K := K) π hπ (E j) V hconstant hcoordinate
  intro x
  rw [hsame, derivationLinearCombination_apply]

end FiniteQuotient

section ConcretePolynomialFamily

variable {R Q K L T : Type*} [CommRing R] [CommRing Q] [IsDomain Q]
variable [Field K] [CharZero K] [Algebra Q K] [IsFractionRing Q K]
variable [Field L] [CharZero L] [Algebra K L] [FiniteDimensional K L]
variable [CommRing T] {n : ℕ}

omit [IsDomain Q] in
/-- An actual polynomial family on the hypersurface produces the residue
equation needed by legal denominator clearing. All remaining matrix,
Hessian, and polynomiality hypotheses are derived from the stated data. -/
theorem residue_solution_from_polynomial_curve
    (π : MvPolynomial (Fin (n+1)) R →+* Q) (hπ : Function.Surjective π)
    (f A : MvPolynomial (Fin (n+1)) R)
    (D E : Fin n → Derivation ℤ L L)
    (M : Matrix (Fin (n+1)) (Fin (n+1)) L) (ψ : Fin (n+1) → L)
    (χ : T →+* L) (t : L) (timeIndex : Fin n)
    (hconst : ∀ a, D timeIndex (χ a) = 0) (htime : D timeIndex t = 1)
    (hf : finiteQuotientEvaluation (K := K) (L := L) π f = 0)
    (hg0 : finiteQuotientEvaluation (K := K) (L := L) π (MvPolynomial.pderiv 0 f) ≠ 0)
    (hdet : M.det ≠ 0)
    (hM0 : ∀ j, M j 0 = ψ j)
    (hMX : ∀ k i, M k i.succ =
      D i (finiteQuotientEvaluation (K := K) π (MvPolynomial.X k)))
    (hψ : (∑ j, finiteQuotientEvaluation (K := K) π (MvPolynomial.pderiv j f)*ψ j) = 1)
    (hDC : ∀ i r, D i (finiteQuotientEvaluation (K := K) π (MvPolynomial.C r)) = 0)
    (hcommute : ∀ i j, Function.Commute (D i) (D j))
    (hE : ∀ j p, E j (finiteQuotientEvaluation (K := K) π p) =
      finiteQuotientEvaluation (K := K) π (MvPolynomial.pderiv j.succ p) -
        finiteQuotientEvaluation (K := K) π (MvPolynomial.pderiv j.succ f) /
          finiteQuotientEvaluation (K := K) π (MvPolynomial.pderiv 0 f) *
            finiteQuotientEvaluation (K := K) π (MvPolynomial.pderiv 0 p))
    (hpolyC : ∀ r, finiteQuotientEvaluation (K := K) π (MvPolynomial.C r) ∈
      (Polynomial.eval₂RingHom χ t).range)
    (hpolyX : ∀ i, finiteQuotientEvaluation (K := K) π (MvPolynomial.X i) ∈
      (Polynomial.eval₂RingHom χ t).range)
    (hpolyψ : ∀ i, ψ i ∈ (Polynomial.eval₂RingHom χ t).range)
    (hDpoly : ∀ i x, x ∈ (Polynomial.eval₂RingHom χ t).range →
      D i x ∈ (Polynomial.eval₂RingHom χ t).range) :
    ∃ w : Fin n → L,
      residueDivergence E (finiteQuotientEvaluation (K := K) π (MvPolynomial.pderiv 0 f)) w =
        -(finiteQuotientEvaluation (K := K) π (MvPolynomial.pderiv 0 A) /
            finiteQuotientEvaluation (K := K) π (MvPolynomial.pderiv 0 f) -
          finiteQuotientEvaluation (K := K) π A *
            finiteQuotientEvaluation (K := K) π (MvPolynomial.pderiv 0 (MvPolynomial.pderiv 0 f)) /
              (finiteQuotientEvaluation (K := K) π (MvPolynomial.pderiv 0 f))^2) := by
  let ρ := finiteQuotientEvaluation (K := K) (L := L) π
  let g : Fin (n+1) → L := fun j => ρ (MvPolynomial.pderiv j f)
  let b : Fin (n+1) → L := fun j => ρ (MvPolynomial.pderiv j A)
  let H : Matrix (Fin (n+1)) (Fin (n+1)) L :=
    fun j k => ρ (MvPolynomial.pderiv k (MvPolynomial.pderiv j f))
  let N : Matrix (Fin (n+1)) (Fin (n+1)) L := M⁻¹
  have hunit : IsUnit M.det := isUnit_iff_ne_zero.mpr hdet
  have hMN : M*N = 1 := Matrix.mul_nonsing_inv M hunit
  have hNM : N*M = 1 := Matrix.nonsing_inv_mul M hunit
  have hchain (i : Fin n) (p : MvPolynomial (Fin (n+1)) R) :
      D i (ρ p) = ∑ j, ρ (MvPolynomial.pderiv j p)*D i (ρ (MvPolynomial.X j)) :=
    derivation_polynomial_ringHom_chain (D i) ρ (hDC i) p
  have hgM : ∀ j, (∑ k, g k*M k j) = if j=0 then 1 else 0 := by
    intro j
    induction j using Fin.cases with
    | zero => simpa only [hM0, ↓reduceIte] using hψ
    | succ i =>
      have h := hchain i f
      rw [hf, map_zero] at h
      simpa only [Fin.succ_ne_zero, ↓reduceIte, hMX] using h.symm
  have hN : ∀ j, N 0 j = g j := inverse_normal_row M N g hMN hgM
  have hg : ∀ i j, D i (g j) = ∑ k, H j k*M k i.succ := by
    intro i j
    simpa only [g, H, hMX] using hchain i (MvPolynomial.pderiv j f)
  have chain : ∀ j x, E j x = ∑ i, tangentInverse N g i j*D i x :=
    finite_quotient_tangent_chain π hπ f D E M N ψ hMN hN hM0 hMX hg0 hDC hE
  have mixed : ∀ (i j k : Fin n), D k (M j.succ i.succ) = D i (M j.succ k.succ) := by
    intro i j k
    rw [hMX, hMX]
    exact hcommute k i (ρ (MvPolynomial.X j.succ))
  have hb : ∀ j, E j (ρ A) = b j.succ - (g j.succ/g 0)*b 0 := fun j => hE j A
  have hH : ∀ j, E j (g 0) = H j.succ 0 - (g j.succ/g 0)*H 0 0 := by
    intro j
    dsimp only [g, H]
    rw [hE j]
    rw [pderiv_commute j.succ 0 f]
  have hpoly (p : MvPolynomial (Fin (n+1)) R) :
      ρ p ∈ (Polynomial.eval₂RingHom χ t).range :=
    polynomial_image_mem_subring ρ _ hpolyC hpolyX p
  have hpolyM : ∀ i j, M i j ∈ (Polynomial.eval₂RingHom χ t).range := by
    intro i j
    induction j using Fin.cases with
    | zero => rw [hM0]; exact hpolyψ i
    | succ j => rw [hMX]; exact hDpoly j _ (hpolyX i)
  exact residue_solution_of_polynomial_family D E M N H g ψ b (ρ A) χ t timeIndex
    hconst htime hg0 hdet hMN hNM hN hM0 hψ hg chain mixed hb hH hpolyM
    (fun i j => hpoly _) hpolyψ (fun j => hpoly _) (hpoly A)
    (fun i j => hDpoly i _ (hpolyψ j))

end ConcretePolynomialFamily

end HoldoutConstruction

#print axioms HoldoutConstruction.tangentInverse_full_coordinate
#print axioms HoldoutConstruction.finite_quotient_tangent_chain
#print axioms HoldoutConstruction.residue_solution_from_polynomial_curve
end
end
