import Proposal.Workspace
import HodgeComputer.CertificateOperations
import HodgeComputer.Constructions.HoldoutCover.HypersurfaceDomain
import HodgeComputer.Constructions.RationalFields.Calculus
import HodgeComputer.Constructions.FiniteAlgebra.FractionDerivation
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Topology
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fin.VecNotation
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Topology.Irreducible
import Mathlib.Tactic

/-! # Certificates and support equations for the protected hypersurface -/

set_option Elab.async false

/- Component: geometry/ExactTargetNonsingular.lean -/
section
/-!
# The protected cycle-q2 equation has no nonzero affine critical point

This discharges a concrete premise of the geometric proof. It does not assert
divisor support or certificate existence. There are no admissions or new axioms.

The main theorem is `protected_F_gradient_nonzero`: for every nonzero affine
representative, at least one evaluated formal partial derivative of the actual
protected polynomial is nonzero. No equation-value hypothesis is needed.
-/

noncomputable section

namespace CycleQ2ExactNonsingular

open MvPolynomial

abbrev Poly := HodgeComputer.AmbientPoly 5
abbrev F : Poly := HodgeSubmission.F

/-- The six formal derivatives, in the protected coordinate order. -/
def gradientValue (z : Fin 6 → ℂ) : Fin 6 → ℂ := ![
  6 * z 0 ^ 5 + (3 * (z 0 ^ 2 * z 1 * z 3 * z 4) +
    z 2 ^ 3 * z 5 * z 3) / 2,
  6 * z 1 ^ 5 + (3 * (z 1 ^ 2 * z 2 * z 4 * z 5) +
    z 0 ^ 3 * z 3 * z 4) / 2,
  6 * z 2 ^ 5 + (3 * (z 2 ^ 2 * z 0 * z 5 * z 3) +
    z 1 ^ 3 * z 4 * z 5) / 2,
  6 * z 3 ^ 5 + (1 * (z 0 ^ 3 * z 1 * z 4) +
    z 2 ^ 3 * z 0 * z 5) / 2,
  6 * z 4 ^ 5 + (1 * (z 0 ^ 3 * z 1 * z 3) +
    z 1 ^ 3 * z 2 * z 5) / 2,
  6 * z 5 ^ 5 + (1 * (z 1 ^ 3 * z 2 * z 4) +
    z 2 ^ 3 * z 0 * z 3) / 2]

lemma quadratic_monomial_bound (z : Fin 6 → ℂ) (M : ℝ)
    (hM : 0 ≤ M) (h : ∀ j, ‖z j‖ ≤ M) (i j k l : Fin 6) :
    ‖z i ^ 2 * z j * z k * z l‖ ≤ M ^ 5 := by
  calc
    ‖z i ^ 2 * z j * z k * z l‖ =
        ‖z i‖ ^ 2 * ‖z j‖ * ‖z k‖ * ‖z l‖ := by
      simp only [norm_mul, norm_pow]
    _ ≤ M ^ 2 * M * M * M := by gcongr <;> apply h
    _ = M ^ 5 := by ring

lemma cubic_monomial_bound (z : Fin 6 → ℂ) (M : ℝ)
    (hM : 0 ≤ M) (h : ∀ j, ‖z j‖ ≤ M) (i j k : Fin 6) :
    ‖z i ^ 3 * z j * z k‖ ≤ M ^ 5 := by
  calc
    ‖z i ^ 3 * z j * z k‖ = ‖z i‖ ^ 3 * ‖z j‖ * ‖z k‖ := by
      simp only [norm_mul, norm_pow]
    _ ≤ M ^ 3 * M * M := by gcongr <;> apply h
    _ = M ^ 5 := by ring

/-- A pure sixth-power derivative dominates both mixed terms. -/
lemma dominant_derivative_ne_zero (a b c k : ℂ)
    (ha : 0 < ‖a‖) (hb : ‖b‖ ≤ ‖a‖ ^ 5) (hc : ‖c‖ ≤ ‖a‖ ^ 5)
    (hk : ‖k‖ ≤ 3) :
    6 * a ^ 5 + (k * b + c) / 2 ≠ 0 := by
  intro hz
  have hpert : ‖(k * b + c) / 2‖ ≤ 2 * ‖a‖ ^ 5 := by
    calc
      ‖(k * b + c) / 2‖ = ‖k * b + c‖ / 2 := by
        norm_num [norm_div]
      _ ≤ (‖k * b‖ + ‖c‖) / 2 := by
        gcongr
        exact norm_add_le _ _
      _ = (‖k‖ * ‖b‖ + ‖c‖) / 2 := by rw [norm_mul]
      _ ≤ (3 * ‖a‖ ^ 5 + ‖a‖ ^ 5) / 2 := by gcongr
      _ = 2 * ‖a‖ ^ 5 := by ring
  have heq : (6 : ℂ) * a ^ 5 = -((k * b + c) / 2) :=
    eq_neg_of_add_eq_zero_left hz
  have hn : 6 * ‖a‖ ^ 5 = ‖(k * b + c) / 2‖ := by
    have hn' := congrArg norm heq
    simpa only [norm_mul, norm_pow, norm_neg, Complex.norm_ofNat] using hn'
  have hp : 0 < ‖a‖ ^ 5 := pow_pos ha 5
  linarith

theorem gradientValue_nonzero (z : Fin 6 → ℂ) (hz : z ≠ 0) :
    ∃ i, gradientValue z i ≠ 0 := by
  obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ
    (fun j : Fin 6 => ‖z j‖) (by simp)
  have hmax : ∀ j, ‖z j‖ ≤ ‖z i‖ := fun j => hi j (Finset.mem_univ j)
  have hpos : 0 < ‖z i‖ := by
    by_contra hnot
    have hi0 : ‖z i‖ ≤ 0 := le_of_not_gt hnot
    apply hz
    funext j
    apply norm_eq_zero.mp
    exact le_antisymm ((hmax j).trans hi0) (norm_nonneg _)
  have hnonneg : 0 ≤ ‖z i‖ := norm_nonneg _
  refine ⟨i, ?_⟩
  fin_cases i
  · exact dominant_derivative_ne_zero _ _ _ _ hpos
      (quadratic_monomial_bound z _ hnonneg hmax 0 1 3 4)
      (cubic_monomial_bound z _ hnonneg hmax 2 5 3) (by norm_num)
  · exact dominant_derivative_ne_zero _ _ _ _ hpos
      (quadratic_monomial_bound z _ hnonneg hmax 1 2 4 5)
      (cubic_monomial_bound z _ hnonneg hmax 0 3 4) (by norm_num)
  · exact dominant_derivative_ne_zero _ _ _ _ hpos
      (quadratic_monomial_bound z _ hnonneg hmax 2 0 5 3)
      (cubic_monomial_bound z _ hnonneg hmax 1 4 5) (by norm_num)
  · exact dominant_derivative_ne_zero _ _ _ _ hpos
      (cubic_monomial_bound z _ hnonneg hmax 0 1 4)
      (cubic_monomial_bound z _ hnonneg hmax 2 0 5) (by norm_num)
  · exact dominant_derivative_ne_zero _ _ _ _ hpos
      (cubic_monomial_bound z _ hnonneg hmax 0 1 3)
      (cubic_monomial_bound z _ hnonneg hmax 1 2 5) (by norm_num)
  · exact dominant_derivative_ne_zero _ _ _ _ hpos
      (cubic_monomial_bound z _ hnonneg hmax 1 2 4)
      (cubic_monomial_bound z _ hnonneg hmax 2 0 3) (by norm_num)

/-- Binding the elementary norm argument to the actual protected polynomial. -/
theorem eval_pderiv_F (z : Fin 6 → ℂ) (i : Fin 6) :
    eval z (pderiv i F) = gradientValue z i := by
  fin_cases i <;>
    norm_num [F, HodgeSubmission.F, gradientValue, map_add, pderiv_mul,
      pderiv_pow, pderiv_C, Pi.single_apply, Fin.ext_iff] <;> ring

/-- The needed nonsingularity condition, for the protected `HodgeSubmission.F`. -/
theorem protected_F_gradient_nonzero (z : Fin 6 → ℂ) (hz : z ≠ 0) :
    ∃ i, eval z (pderiv i HodgeSubmission.F) ≠ 0 := by
  obtain ⟨i, hi⟩ := gradientValue_nonzero z hz
  exact ⟨i, by simpa only [← eval_pderiv_F] using hi⟩

#print axioms protected_F_gradient_nonzero

end CycleQ2ExactNonsingular
end
end


/- Component: geometry/ExactTargetIrreducible.lean -/
section
/-!
# Absolute irreducibility of the protected cycle-q2 equation

The coefficient field is already `ℂ`. We view the exact protected polynomial as
monic in X0, then specialize the other variables by
`(X1,X2,Y0,Y1,Y2) = (0,0,t+1,0,I)`. The image is
`X0^6 + (t+1)^6 - 1`, Eisenstein at `t`. Monic specialization reflects
irreducibility. The Eisenstein helper is the existing proved project theorem
`HoldoutConstruction.irreducible_power_add_constant`.

This supplies a genuine premise for coprimality and polynomial divisibility in
the certificate bridge. It does not assert certificate existence.
-/

noncomputable section

namespace CycleQ2ExactIrreducible

open Polynomial

abbrev Coeff := MvPolynomial (Fin 5) ℂ

/-- Coefficients are ordered `(X1,X2,Y0,Y1,Y2)`. -/
def cubicCoeff : Coeff :=
  MvPolynomial.C (1 / 2 : ℂ) * MvPolynomial.X 0 *
    MvPolynomial.X 2 * MvPolynomial.X 3

def linearCoeff : Coeff :=
  MvPolynomial.C (1 / 2 : ℂ) * MvPolynomial.X 1 ^ 3 *
    MvPolynomial.X 4 * MvPolynomial.X 2

def constantCoeff : Coeff :=
  MvPolynomial.X 0 ^ 6 + MvPolynomial.X 1 ^ 6 + MvPolynomial.X 2 ^ 6 +
    MvPolynomial.X 3 ^ 6 + MvPolynomial.X 4 ^ 6 +
    MvPolynomial.C (1 / 2 : ℂ) * MvPolynomial.X 0 ^ 3 *
      MvPolynomial.X 1 * MvPolynomial.X 3 * MvPolynomial.X 4

def univariateF : Coeff[X] :=
  X ^ 6 + (C cubicCoeff * X ^ 3 + (C linearCoeff * X ^ 1 + C constantCoeff))

theorem univariateF_monic : univariateF.Monic := by
  unfold univariateF
  apply monic_X_pow_add
  apply lt_of_le_of_lt (degree_add_le _ _)
  apply max_lt
  · exact lt_of_le_of_lt (degree_C_mul_X_pow_le 3 _) (by decide)
  · apply lt_of_le_of_lt (degree_add_le _ _)
    apply max_lt
    · exact lt_of_le_of_lt (degree_C_mul_X_pow_le 1 _) (by decide)
    · exact lt_of_le_of_lt degree_C_le (by decide)

def coefficientSpecialization : Coeff →+* ℂ[X] :=
  MvPolynomial.eval₂Hom C ![0, 0, X + 1, 0, C Complex.I]

lemma I_pow_six : Complex.I ^ 6 = -1 := by
  calc
    Complex.I ^ 6 = (Complex.I ^ 2) ^ 3 := by ring
    _ = -1 := by rw [Complex.I_sq]; norm_num

theorem univariateF_specialization :
    univariateF.map coefficientSpecialization =
      (X : (ℂ[X])[X]) ^ 6 + C ((X + 1) ^ 6 - 1) := by
  simp [univariateF, cubicCoeff, linearCoeff, constantCoeff,
    coefficientSpecialization, ← map_pow, I_pow_six, sub_eq_add_neg]

theorem univariateF_irreducible : Irreducible univariateF := by
  apply univariateF_monic.irreducible_of_irreducible_map coefficientSpecialization
  rw [univariateF_specialization]
  exact HoldoutConstruction.irreducible_power_add_constant ((X + 1) ^ 6 - 1 : ℂ[X])
    (by simp [coeff_X_add_one_pow])
    (by norm_num [coeff_X_add_one_pow, coeff_one]) 6 (by decide)

/-- Exact binding to the protected polynomial, including all three half-weight
mixed terms. -/
theorem protected_F_univariate :
    MvPolynomial.finSuccEquiv ℂ 5 HodgeSubmission.F = univariateF := by
  have he : (Fin.cases (X : Coeff[X]) (fun j => C (MvPolynomial.X j))) =
      ![X, C (MvPolynomial.X 0), C (MvPolynomial.X 1),
        C (MvPolynomial.X 2), C (MvPolynomial.X 3), C (MvPolynomial.X 4)] := by
    funext i
    fin_cases i <;> rfl
  simp [HodgeSubmission.F, univariateF, cubicCoeff, linearCoeff, constantCoeff,
    MvPolynomial.finSuccEquiv_apply, he]
  ring

theorem protected_F_irreducible : Irreducible HodgeSubmission.F := by
  apply (MulEquiv.irreducible_iff (MvPolynomial.finSuccEquiv ℂ 5)).mp
  rw [protected_F_univariate]
  exact univariateF_irreducible

theorem protected_F_prime : Prime HodgeSubmission.F :=
  protected_F_irreducible.prime

theorem protected_F_quotient_isDomain :
    IsDomain (HodgeComputer.AmbientPoly 5 ⧸ Ideal.span {HodgeSubmission.F}) :=
  (Ideal.Quotient.isDomain_iff_prime _).mpr
    ((Ideal.span_singleton_prime protected_F_irreducible.ne_zero).mpr protected_F_prime)

#print axioms protected_F_irreducible
#print axioms protected_F_prime
#print axioms protected_F_quotient_isDomain

end CycleQ2ExactIrreducible
end
end


/- Component: algebra/FiniteAveraging.lean -/
section
/-!+# Finite linear combinations with an explicit legal denominator

The denominator is the product of the supplied denominators. The numerator
and quotient are finite sums with the corresponding complementary products.
No denominator-degree bound, strictness condition, or coefficient search is
introduced. The final averaging theorem retains the original source whenever
the scalar weights sum to one.
-/

noncomputable section

namespace HodgeComputer

open HodgeTestbed MvPolynomial
open scoped BigOperators

theorem divergenceNumerator_C_mul {n : ℕ} (D : AmbientPoly n)
    (N : Fin (n + 1) → AmbientPoly n) (c : ℂ) :
    divergenceNumerator D (fun i => C c * N i) =
      C c * divergenceNumerator D N := by
  have hc : directional (C c : AmbientPoly n) N = 0 := by
    simp [directional]
  unfold divergenceNumerator
  rw [divergence_mul, hc, zero_add, directional_mul]
  ring

theorem defect_C_mul {n : ℕ} (F A D : AmbientPoly n) (q : ℕ)
    (N : Fin (n + 1) → AmbientPoly n) (c : ℂ) :
    defect F (C c * A) D q (fun i => C c * N i) =
      C c * defect F A D q N := by
  unfold defect
  rw [directional_mul, divergenceNumerator_C_mul]
  ring

theorem Verify.C_mul {n : ℕ} {F A D Q : AmbientPoly n} {d q : ℕ}
    {N : Fin (n + 1) → AmbientPoly n}
    (h : Verify F A d q D N Q) (c : ℂ) :
    Verify F (C c * A) d q D (fun i => C c * N i) (C c * Q) where
  hypersurface_ne_zero := h.hypersurface_ne_zero
  hypersurface_homogeneous := h.hypersurface_homogeneous
  source_homogeneous := h.source_homogeneous.C_mul c
  denominator_ne_zero := h.denominator_ne_zero
  denominator_homogeneous := h.denominator_homogeneous
  numerator_homogeneous := fun i => (h.numerator_homogeneous i).C_mul c
  denominator_legal := h.denominator_legal
  identity := by
    rw [defect_C_mul, h.identity]
    ring

/-- Adding a legal homogeneous factor to the denominator preserves the
certificate, with the same factor in every numerator and its square in Q. -/
theorem Verify.scale_denominator {n : ℕ} {F A D Q : AmbientPoly n} {d q : ℕ}
    {N : Fin (n + 1) → AmbientPoly n}
    (h : Verify F A d q D N Q) (H : AmbientPoly n)
    (hH : H ≠ 0) (hHhom : H.IsHomogeneous H.totalDegree)
    (hHlegal : IsRelPrime F H) :
    Verify F A d q (H * D) (fun i => H * N i) (H ^ 2 * Q) where
  hypersurface_ne_zero := h.hypersurface_ne_zero
  hypersurface_homogeneous := h.hypersurface_homogeneous
  source_homogeneous := h.source_homogeneous
  denominator_ne_zero := mul_ne_zero hH h.denominator_ne_zero
  denominator_homogeneous := by
    rw [MvPolynomial.totalDegree_mul_of_isDomain hH h.denominator_ne_zero]
    exact hHhom.mul h.denominator_homogeneous
  numerator_homogeneous := by
    intro i
    have hn := (Homogeneous.of_isHomogeneous hHhom).mul (h.numerator_homogeneous i)
    rw [MvPolynomial.totalDegree_mul_of_isDomain hH h.denominator_ne_zero,
      Nat.cast_add]
    convert hn using 1 <;> ring
  denominator_legal := hHlegal.mul_right h.denominator_legal
  identity := by
    rw [defect_scale_denominator, h.identity]
    ring

/-- Zero source with any already legal homogeneous denominator. -/
theorem Verify.zero_denominator {n : ℕ} (F D : AmbientPoly n) (d q : ℕ)
    (hF : F ≠ 0) (hFhom : F.IsHomogeneous d)
    (hD : D ≠ 0) (hDhom : D.IsHomogeneous D.totalDegree)
    (hDlegal : IsRelPrime F D) :
    Verify F 0 d q D (fun _ => 0) 0 where
  hypersurface_ne_zero := hF
  hypersurface_homogeneous := hFhom
  source_homogeneous := homogeneous_zero _
  denominator_ne_zero := hD
  denominator_homogeneous := hDhom
  numerator_homogeneous := fun _ => homogeneous_zero _
  denominator_legal := hDlegal
  identity := by simp [defect, directional, divergenceNumerator, divergence]

theorem Verify.add_same_denominator {n : ℕ}
    {F A B D Q R : AmbientPoly n} {d q : ℕ}
    {N M : Fin (n + 1) → AmbientPoly n}
    (h : Verify F A d q D N Q) (k : Verify F B d q D M R) :
    Verify F (A + B) d q D (fun i => N i + M i) (Q + R) where
  hypersurface_ne_zero := h.hypersurface_ne_zero
  hypersurface_homogeneous := h.hypersurface_homogeneous
  source_homogeneous := h.source_homogeneous.add k.source_homogeneous
  denominator_ne_zero := h.denominator_ne_zero
  denominator_homogeneous := h.denominator_homogeneous
  numerator_homogeneous := fun i =>
    (h.numerator_homogeneous i).add (k.numerator_homogeneous i)
  denominator_legal := h.denominator_legal
  identity := by
    rw [defect_add_same_denominator, h.identity, k.identity]
    ring

/-- Finite addition at one denominator does not raise its degree. -/
theorem Verify.sum_same_denominator {n : ℕ} {ι : Type*}
    (s : Finset ι) (F D : AmbientPoly n) (d q : ℕ)
    (A Q : ι → AmbientPoly n) (N : ι → Fin (n + 1) → AmbientPoly n)
    (hF : F ≠ 0) (hFhom : F.IsHomogeneous d)
    (hD : D ≠ 0) (hDhom : D.IsHomogeneous D.totalDegree)
    (hDlegal : IsRelPrime F D)
    (h : ∀ j ∈ s, Verify F (A j) d q D (N j) (Q j)) :
    Verify F (∑ j ∈ s, A j) d q D
      (fun i => ∑ j ∈ s, N j i) (∑ j ∈ s, Q j) := by
  classical
  revert h
  induction s using Finset.induction_on with
  | empty =>
      intro _
      simpa using Verify.zero_denominator F D d q hF hFhom hD hDhom hDlegal
  | @insert a s ha ih =>
      intro h
      have hs := ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
      have hsum := (h a (Finset.mem_insert_self a s)).add_same_denominator hs
      simpa only [Finset.sum_insert ha] using hsum

/-- Finite products retain all three denominator side conditions. -/
theorem homogeneous_legal_product {n : ℕ} {ι : Type*}
    (s : Finset ι) (F : AmbientPoly n) (D : ι → AmbientPoly n)
    (h : ∀ j ∈ s, D j ≠ 0 ∧ (D j).IsHomogeneous (D j).totalDegree ∧
      IsRelPrime F (D j)) :
    (∏ j ∈ s, D j) ≠ 0 ∧
      (∏ j ∈ s, D j).IsHomogeneous (∏ j ∈ s, D j).totalDegree ∧
      IsRelPrime F (∏ j ∈ s, D j) := by
  classical
  revert h
  induction s using Finset.induction_on with
  | empty =>
      intro _
      simp only [Finset.prod_empty]
      exact ⟨one_ne_zero, by simpa using isHomogeneous_one (Fin (n + 1)) ℂ,
        isRelPrime_one_right⟩
  | @insert a s ha ih =>
      intro h
      rcases ih (fun j hj => h j (Finset.mem_insert_of_mem hj)) with
        ⟨hs, hshom, hslegal⟩
      rcases h a (Finset.mem_insert_self a s) with ⟨ha0, hahom, halegal⟩
      rw [Finset.prod_insert ha]
      refine ⟨mul_ne_zero ha0 hs, ?_, halegal.mul_right hslegal⟩
      rw [MvPolynomial.totalDegree_mul_of_isDomain ha0 hs]
      exact hahom.mul hshom

/-- The product denominator has exactly the sum of the input degrees. -/
theorem totalDegree_product_of_nonzero {n : ℕ} {ι : Type*}
    (s : Finset ι) (D : ι → AmbientPoly n)
    (h : ∀ j ∈ s, D j ≠ 0) :
    (∏ j ∈ s, D j).totalDegree = ∑ j ∈ s, (D j).totalDegree := by
  classical
  revert h
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      intro h
      have hs : (∏ j ∈ s, D j) ≠ 0 :=
        Finset.prod_ne_zero_iff.mpr (fun j hj => h j (Finset.mem_insert_of_mem hj))
      rw [Finset.prod_insert ha, Finset.sum_insert ha,
        MvPolynomial.totalDegree_mul_of_isDomain (h a (Finset.mem_insert_self a s)) hs,
        ih (fun j hj => h j (Finset.mem_insert_of_mem hj))]

/-- Explicit finite linear combination. Each complementary product clears
one summand; the product of all denominators is homogeneous and relatively
prime to F. The quotient is retained even when it is nonzero. -/
theorem Verify.linearCombination {n : ℕ} {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (F : AmbientPoly n) (d q : ℕ)
    (A D Q : ι → AmbientPoly n) (N : ι → Fin (n + 1) → AmbientPoly n)
    (c : ι → ℂ) (hF : F ≠ 0) (hFhom : F.IsHomogeneous d)
    (h : ∀ j ∈ s, Verify F (A j) d q (D j) (N j) (Q j)) :
    Verify F (∑ j ∈ s, C (c j) * A j) d q (∏ j ∈ s, D j)
      (fun i => ∑ j ∈ s, (∏ k ∈ s.erase j, D k) * (C (c j) * N j i))
      (∑ j ∈ s, (∏ k ∈ s.erase j, D k) ^ 2 * (C (c j) * Q j)) := by
  have hden := homogeneous_legal_product s F D (fun j hj =>
    ⟨(h j hj).denominator_ne_zero, (h j hj).denominator_homogeneous,
      (h j hj).denominator_legal⟩)
  apply Verify.sum_same_denominator s F (∏ j ∈ s, D j) d q
    (fun j => C (c j) * A j)
    (fun j => (∏ k ∈ s.erase j, D k) ^ 2 * (C (c j) * Q j))
    (fun j i => (∏ k ∈ s.erase j, D k) * (C (c j) * N j i))
    hF hFhom hden.1 hden.2.1 hden.2.2
  intro j hj
  have hrest := homogeneous_legal_product (s.erase j) F D (fun k hk =>
    ⟨(h k (Finset.mem_of_mem_erase hk)).denominator_ne_zero,
      (h k (Finset.mem_of_mem_erase hk)).denominator_homogeneous,
      (h k (Finset.mem_of_mem_erase hk)).denominator_legal⟩)
  have hscaled := ((h j hj).C_mul (c j)).scale_denominator
    (∏ k ∈ s.erase j, D k) hrest.1 hrest.2.1 hrest.2.2
  have hprod : (∏ k ∈ s.erase j, D k) * D j = ∏ k ∈ s, D k := by
    calc
      (∏ k ∈ s.erase j, D k) * D j =
          D j * (∏ k ∈ s.erase j, D k) := mul_comm _ _
      _ = ∏ k ∈ insert j (s.erase j), D k :=
        (Finset.prod_insert (Finset.notMem_erase j s)).symm
      _ = ∏ k ∈ s, D k := by rw [Finset.insert_erase hj]
  simpa only [hprod] using hscaled

/-- Weighted averaging preserves a common source. This is the algebraic
certificate step needed after a finite family of conjugate witnesses has
been supplied; the resulting denominator is their product. -/
theorem Verify.average {n : ℕ} {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (F A : AmbientPoly n) (d q : ℕ)
    (D Q : ι → AmbientPoly n) (N : ι → Fin (n + 1) → AmbientPoly n)
    (c : ι → ℂ) (hc : ∑ j ∈ s, c j = 1)
    (hF : F ≠ 0) (hFhom : F.IsHomogeneous d)
    (h : ∀ j ∈ s, Verify F A d q (D j) (N j) (Q j)) :
    Verify F A d q (∏ j ∈ s, D j)
      (fun i => ∑ j ∈ s, (∏ k ∈ s.erase j, D k) * (C (c j) * N j i))
      (∑ j ∈ s, (∏ k ∈ s.erase j, D k) ^ 2 * (C (c j) * Q j)) := by
  have hsource : (∑ j ∈ s, C (c j) * A) = A := by
    calc
      (∑ j ∈ s, C (c j) * A) = (∑ j ∈ s, C (c j)) * A :=
        (Finset.sum_mul s (fun j => C (c j)) A).symm
      _ = C (∑ j ∈ s, c j) * A := by rw [map_sum]
      _ = A := by rw [hc]; simp
  simpa only [hsource] using
    Verify.linearCombination s F d q (fun _ => A) D Q N c hF hFhom h

/-- Equal-weight averaging over a nonempty finite family. -/
theorem Verify.uniformAverage {n : ℕ} {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (hs : s.Nonempty) (F A : AmbientPoly n) (d q : ℕ)
    (D Q : ι → AmbientPoly n) (N : ι → Fin (n + 1) → AmbientPoly n)
    (hF : F ≠ 0) (hFhom : F.IsHomogeneous d)
    (h : ∀ j ∈ s, Verify F A d q (D j) (N j) (Q j)) :
    Verify F A d q (∏ j ∈ s, D j)
      (fun i => ∑ j ∈ s,
        (∏ k ∈ s.erase j, D k) * (C ((s.card : ℂ)⁻¹) * N j i))
      (∑ j ∈ s,
        (∏ k ∈ s.erase j, D k) ^ 2 * (C ((s.card : ℂ)⁻¹) * Q j)) := by
  have hcard : (s.card : ℂ) ≠ 0 := by exact_mod_cast hs.card_pos.ne'
  have hc : (∑ _j ∈ s, (s.card : ℂ)⁻¹) = 1 := by
    simp [nsmul_eq_mul, hcard]
  exact Verify.average s F A d q D Q N (fun _ => (s.card : ℂ)⁻¹) hc hF hFhom h

end HodgeComputer

#print axioms HodgeComputer.Verify.scale_denominator
#print axioms HodgeComputer.Verify.linearCombination
#print axioms HodgeComputer.Verify.average
#print axioms HodgeComputer.Verify.uniformAverage
end
end


/- Component: bridge/LocalizedCertificate.lean -/
section
/-!
# Rational differential equations and the protected certificate

This module supplies the algebraic end of the nonconstructive support argument.
It uses actual derivations on the fraction field of the ambient polynomial ring.
The quotient rule is proved by the existing fraction-derivation construction;
the divergence and the cleared defect are then identified without additional
differential hypotheses.

The key equivalence allows the residual term to have an arbitrary denominator
coprime to the hypersurface. Euclid's lemma removes that residual denominator,
so geometry need only prove regularity along the hypersurface. It need not
predict the polynomial quotient accepted by `Verify`.

The prescribed-power constructor proves nonvanishing, homogeneity, the exact
numerator degree, and coprimality for D = S^q. For a sextic at q = 2, its
denominator is S^2 and numerator degree is 2 * degree(S) + 7.

No support theorem or geometric existence assertion is assumed as an axiom.
The geometric input remains an explicit hypothesis of the final constructor.
The fraction derivations and vector-field calculus are reused with their
original attribution from the repository's accepted constructions.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace CycleQ2Bridge

open MvPolynomial HodgeComputer HodgeTestbed HodgeTestbed.Conic
open scoped BigOperators

variable {n : ℕ}

/-- The actual rational-function field in the homogeneous coordinates. -/
abbrev RationalFunction (n : ℕ) := FractionRing (AmbientPoly n)

-- Choose the algebra-induced rational scalar action consistently. The
-- concrete localization also carries a transported module instance.
local instance rationalFunctionRatAlgebra (n : ℕ) : Algebra ℚ (RationalFunction n) :=
  DivisionRing.toRatAlgebra

local instance rationalFunctionRatModule (n : ℕ) : Module ℚ (RationalFunction n) :=
  Algebra.toModule

/-- The injective polynomial-to-rational-function map. -/
abbrev polynomialMap (n : ℕ) : AmbientPoly n →+* RationalFunction n :=
  algebraMap (AmbientPoly n) (RationalFunction n)

theorem polynomialMap_injective : Function.Injective (polynomialMap n) :=
  IsFractionRing.injective (AmbientPoly n) (RationalFunction n)

theorem polynomialMap_ne_zero {P : AmbientPoly n} (hP : P ≠ 0) :
    polynomialMap n P ≠ 0 := by
  intro h
  apply hP
  apply polynomialMap_injective
  simpa only [map_zero] using h

/-- Coordinate partial derivatives extended by the proved quotient rule. -/
def rationalPartial (n : ℕ) (i : Fin (n + 1)) :
    Derivation ℚ (RationalFunction n) (RationalFunction n) :=
  QuadricContactFraction.extend (F := RationalFunction n)
    ((MvPolynomial.pderiv i : Derivation ℂ (AmbientPoly n) (AmbientPoly n)).restrictScalars ℚ)

@[simp] theorem rationalPartial_map (i : Fin (n + 1)) (P : AmbientPoly n) :
    rationalPartial n i (polynomialMap n P) = polynomialMap n (pderiv i P) := by
  unfold rationalPartial polynomialMap
  rw [QuadricContactFraction.extend_map]
  rfl

/-- The rational field represented by a common polynomial denominator. -/
def rationalField (D : AmbientPoly n) (N : Fin (n + 1) → AmbientPoly n) :
    Fin (n + 1) → RationalFunction n :=
  fun i => polynomialMap n (N i) / polynomialMap n D

/-- The actual first-order rational differential expression. -/
def rationalDefect (F A : AmbientPoly n) (q : ℕ)
    (v : Fin (n + 1) → RationalFunction n) : RationalFunction n :=
  polynomialMap n A - (q : RationalFunction n) *
      fieldAction (k := ℚ) (rationalPartial n) v (polynomialMap n F) +
    polynomialMap n F * fieldDivergence (k := ℚ) (rationalPartial n) v

theorem rationalField_action (F D : AmbientPoly n)
    (N : Fin (n + 1) → AmbientPoly n) :
    fieldAction (k := ℚ) (rationalPartial n) (rationalField D N) (polynomialMap n F) =
      polynomialMap n (directional F N) / polynomialMap n D := by
  simp only [fieldAction_apply, rationalField, rationalPartial_map,
    directional, map_sum, map_mul, div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The quotient-rule numerator really is the divergence of N / D. -/
theorem rationalField_divergence (D : AmbientPoly n)
    (N : Fin (n + 1) → AmbientPoly n) :
    fieldDivergence (k := ℚ) (rationalPartial n) (rationalField D N) =
      polynomialMap n (divergenceNumerator D N) / (polynomialMap n D)^2 := by
  have hdirection :
      (∑ i, polynomialMap n (N i) * polynomialMap n (pderiv i D)) =
        polynomialMap n (directional D N) := by
    simp only [directional, map_sum, map_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  simp only [fieldDivergence, rationalField, Derivation.leibniz_div,
    smul_eq_mul, rationalPartial_map]
  rw [← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.mul_sum, hdirection]
  simp only [divergenceNumerator, divergence, map_sub, map_mul, map_sum,
    div_eq_mul_inv, inv_pow]
  ring

/-- Clearing the common denominator identifies the rational and polynomial defects. -/
theorem rationalDefect_eq (F A D : AmbientPoly n) (q : ℕ)
    (N : Fin (n + 1) → AmbientPoly n) (hD : D ≠ 0) :
    rationalDefect F A q (rationalField D N) =
      polynomialMap n (defect F A D q N) / (polynomialMap n D)^2 := by
  have hD' := polynomialMap_ne_zero hD
  unfold rationalDefect
  rw [rationalField_action, rationalField_divergence]
  simp only [defect, map_add, map_sub, map_mul, map_pow, map_natCast]
  field_simp

/-- Exact polynomial equality is equivalent to its actual rational differential equation. -/
theorem identity_iff_rationalDefect (F A D Q : AmbientPoly n) (q : ℕ)
    (N : Fin (n + 1) → AmbientPoly n) (hD : D ≠ 0) :
    defect F A D q N = F^(q+1) * Q ↔
      rationalDefect F A q (rationalField D N) =
        (polynomialMap n F)^(q+1) *
          (polynomialMap n Q / (polynomialMap n D)^2) := by
  rw [rationalDefect_eq F A D q N hD]
  constructor
  · intro h
    rw [h, map_mul, map_pow]
    ring
  · intro h
    apply polynomialMap_injective
    have hD' := polynomialMap_ne_zero hD
    have hh := congrArg (fun z : RationalFunction n => z * (polynomialMap n D)^2) h
    simpa only [map_mul, map_pow] using (by
      field_simp at hh
      linear_combination hh : polynomialMap n (defect F A D q N) =
        (polynomialMap n F)^(q+1) * polynomialMap n Q)

/-- Divisibility of the residual expression by F^(q+1) in the ring of
rational functions with denominators coprime to F.

This is the precise algebraic meaning needed from regularity of the rational
top form along the hypersurface. The residual denominator T is unrestricted.
-/
def LocalizedEquation (F A : AmbientPoly n) (q : ℕ) (D : AmbientPoly n)
    (N : Fin (n + 1) → AmbientPoly n) : Prop :=
  ∃ P T : AmbientPoly n, T ≠ 0 ∧ IsRelPrime F T ∧
    rationalDefect F A q (rationalField D N) =
      (polynomialMap n F)^(q+1) * (polynomialMap n P / polynomialMap n T)

/-- An auxiliary residual denominator cancels by coprimality, not by an
unjustified assertion that the residual function was a polynomial. -/
theorem quotient_exists_of_localizedEquation
    (F A D : AmbientPoly n) (q : ℕ) (N : Fin (n + 1) → AmbientPoly n)
    (hD : D ≠ 0) (h : LocalizedEquation F A q D N) :
    ∃ Q : AmbientPoly n, defect F A D q N = F^(q+1) * Q := by
  obtain ⟨P, T, hT, hlegal, heq⟩ := h
  have hD' := polynomialMap_ne_zero hD
  have hT' := polynomialMap_ne_zero hT
  rw [rationalDefect_eq F A D q N hD] at heq
  have hcleared : T * defect F A D q N = F^(q+1) * (P * D^2) := by
    apply polynomialMap_injective
    simp only [map_mul, map_pow]
    field_simp at heq
    linear_combination heq
  have hdiv : F^(q+1) ∣ T * defect F A D q N := ⟨P * D^2, hcleared⟩
  exact (hlegal.pow_left : IsRelPrime (F^(q+1)) T).dvd_of_dvd_mul_left hdiv

/-- The polynomial quotient gives a legal localized residual with
denominator D^2, yielding an equivalence for a legal field. -/
theorem localizedEquation_iff_quotient
    (F A D : AmbientPoly n) (q : ℕ) (N : Fin (n + 1) → AmbientPoly n)
    (hD : D ≠ 0) (hlegal : IsRelPrime F D) :
    LocalizedEquation F A q D N ↔
      ∃ Q : AmbientPoly n, defect F A D q N = F^(q+1) * Q := by
  constructor
  · exact quotient_exists_of_localizedEquation F A D q N hD
  · rintro ⟨Q, hQ⟩
    refine ⟨Q, D^2, pow_ne_zero 2 hD, hlegal.pow_right, ?_⟩
    simpa only [map_pow] using
      (identity_iff_rationalDefect F A D Q q N hD).mp hQ

/-- The actual first-order equation supplies exactly the quotient required
by Verify, retaining the stated homogeneous and legal field. -/
theorem exists_verify_iff_localizedEquation
    (F A D : AmbientPoly n) (d q : ℕ) (N : Fin (n + 1) → AmbientPoly n)
    (hF : F ≠ 0) (hFhom : F.IsHomogeneous d)
    (hA : Homogeneous A ((d : ℤ) * (q + 1) - (n + 1)))
    (hD : D ≠ 0) (hDhom : D.IsHomogeneous D.totalDegree)
    (hN : ∀ i, Homogeneous (N i) ((D.totalDegree : ℤ) + d*q - n))
    (hlegal : IsRelPrime F D) :
    (∃ Q : AmbientPoly n, Verify F A d q D N Q) ↔
      LocalizedEquation F A q D N := by
  constructor
  · rintro ⟨Q, hQ⟩
    exact (localizedEquation_iff_quotient F A D q N hD hlegal).mpr ⟨Q, hQ.identity⟩
  · intro h
    obtain ⟨Q, hQ⟩ := quotient_exists_of_localizedEquation F A D q N hD h
    exact ⟨Q, {
      hypersurface_ne_zero := hF
      hypersurface_homogeneous := hFhom
      source_homogeneous := hA
      denominator_ne_zero := hD
      denominator_homogeneous := hDhom
      numerator_homogeneous := hN
      denominator_legal := hlegal
      identity := hQ }⟩

/-- A nonconstructively chosen support equation with a bounded primitive
finishes every algebraic clause of the protected certificate. -/
theorem hasCertificate_of_prescribed_power
    (F A S : AmbientPoly n) (d q e : ℕ)
    (N : Fin (n + 1) → AmbientPoly n)
    (hF : F ≠ 0) (hFhom : F.IsHomogeneous d)
    (hA : Homogeneous A ((d : ℤ) * (q + 1) - (n + 1)))
    (hS : S ≠ 0) (hShom : S.IsHomogeneous e)
    (hlegal : IsRelPrime F S)
    (hN : ∀ i, Homogeneous (N i) ((e : ℤ)*q + d*q - n))
    (hlocal : LocalizedEquation F A q (S^q) N) :
    HasCertificate F q A := by
  have hD : S^q ≠ 0 := pow_ne_zero q hS
  have hDhom : (S^q).IsHomogeneous (e*q) := hShom.pow q
  have hdegree : (S^q).totalDegree = e*q := hDhom.totalDegree hD
  obtain ⟨Q, hQ⟩ := (exists_verify_iff_localizedEquation F A (S^q) d q N
    hF hFhom hA hD (by simpa only [hdegree] using hDhom)
    (by
      intro i
      simpa only [hdegree, Nat.cast_mul] using hN i)
    hlegal.pow_right).mpr hlocal
  exact hQ.hasCertificate

/-- The degree bookkeeping from the filtered double-pole primitive for a
sextic fourfold, without an explicit support equation or degree bound. -/
theorem sextic_q2_hasCertificate_of_square_primitive
    (F A S : AmbientPoly 5) (e : ℕ) (N : Fin 6 → AmbientPoly 5)
    (hF : F ≠ 0) (hFhom : F.IsHomogeneous 6)
    (hA : Homogeneous A 12)
    (hS : S ≠ 0) (hShom : S.IsHomogeneous e)
    (hlegal : IsRelPrime F S)
    (hN : ∀ i, Homogeneous (N i) (2*(e : ℤ)+7))
    (hlocal : LocalizedEquation F A 2 (S^2) N) :
    HasCertificate F 2 A := by
  apply hasCertificate_of_prescribed_power F A S 6 2 e N hF hFhom
  · simpa using hA
  · exact hS
  · exact hShom
  · exact hlegal
  · intro i
    convert hN i using 1
    ring
  · exact hlocal

/-- For an irreducible hypersurface, the geometric choice S outside (F)
already proves both denominator nonvanishing and coprimality. -/
theorem sextic_q2_hasCertificate_of_irreducible_square_primitive
    (F A S : AmbientPoly 5) (e : ℕ) (N : Fin 6 → AmbientPoly 5)
    (hF : Irreducible F) (hFhom : F.IsHomogeneous 6)
    (hA : Homogeneous A 12) (hShom : S.IsHomogeneous e)
    (hS : ¬ F ∣ S)
    (hN : ∀ i, Homogeneous (N i) (2*(e : ℤ)+7))
    (hlocal : LocalizedEquation F A 2 (S^2) N) :
    HasCertificate F 2 A := by
  have hS0 : S ≠ 0 := by
    intro hs
    apply hS
    rw [hs]
    exact dvd_zero F
  exact sextic_q2_hasCertificate_of_square_primitive F A S e N
    hF.ne_zero hFhom hA hS0 hShom
    (hF.isRelPrime_iff_not_dvd.mpr hS) hN hlocal

/-- Any nonzero denominator can be squared without changing the actual field. -/
theorem rationalField_square (D : AmbientPoly n)
    (N : Fin (n + 1) → AmbientPoly n) (hD : D ≠ 0) :
    rationalField (D^2) (fun i => D * N i) = rationalField D N := by
  have hD' := polynomialMap_ne_zero hD
  funext i
  simp only [rationalField, map_mul, map_pow]
  field_simp

/-- The square-support formulation is exactly the original existential
problem. It is not an extra denominator ansatz, and this equivalence does
not assert that either side has been proved for a particular source. -/
theorem sextic_q2_hasCertificate_iff_square_primitive
    (F A : AmbientPoly 5)
    (hF : Irreducible F) (hFhom : F.IsHomogeneous 6)
    (hA : Homogeneous A 12) :
    HasCertificate F 2 A ↔
      ∃ (e : ℕ) (S : AmbientPoly 5) (N : Fin 6 → AmbientPoly 5),
        S.IsHomogeneous e ∧ ¬ F ∣ S ∧
        (∀ i, Homogeneous (N i) (2*(e : ℤ)+7)) ∧
        LocalizedEquation F A 2 (S^2) N := by
  constructor
  · rintro ⟨D, N, Q, h⟩
    have hdegree : F.totalDegree = 6 := hFhom.totalDegree hF.ne_zero
    rw [hdegree] at h
    refine ⟨D.totalDegree, D, (fun i => D * N i), h.denominator_homogeneous,
      hF.isRelPrime_iff_not_dvd.mp h.denominator_legal, ?_, ?_⟩
    · intro i
      have hn := (Homogeneous.of_isHomogeneous h.denominator_homogeneous).mul
        (h.numerator_homogeneous i)
      convert hn using 1
      ring
    · have hlocal := (localizedEquation_iff_quotient F A D 2 N
        h.denominator_ne_zero h.denominator_legal).mpr ⟨Q, h.identity⟩
      simpa only [LocalizedEquation, rationalField_square D N h.denominator_ne_zero]
        using hlocal
  · rintro ⟨e, S, N, hShom, hS, hN, hlocal⟩
    exact sextic_q2_hasCertificate_of_irreducible_square_primitive
      F A S e N hF hFhom hA hShom hS hN hlocal

end CycleQ2Bridge

#print axioms CycleQ2Bridge.rationalField_divergence
#print axioms CycleQ2Bridge.quotient_exists_of_localizedEquation
#print axioms CycleQ2Bridge.exists_verify_iff_localizedEquation
#print axioms CycleQ2Bridge.sextic_q2_hasCertificate_of_square_primitive
#print axioms CycleQ2Bridge.sextic_q2_hasCertificate_of_irreducible_square_primitive
#print axioms CycleQ2Bridge.sextic_q2_hasCertificate_iff_square_primitive
end
end


/- Component: support_choice/ProjectiveSupportEquation.lean -/
section
/-!
# Choosing an ambient equation for an actual proper projective support

This file proves the support-equation choice using mathlib's actual projective
spectrum, homogeneous vanishing ideals, and homogeneous components. No
cohomology or residue support is postulated or constructed here.

For every closed strict subset Z of the protected hypersurface, the theorem
chooses a positive-degree homogeneous S that vanishes on Z and is not divisible
by F. Its square is therefore a nonzero homogeneous legal denominator.

The remaining geometric assertion is that the specified residue vanishes off
some such Z. The theorem below does not assert that support exists.
-/

noncomputable section

namespace CycleQ2SupportEquation

open MvPolynomial HodgeComputer

attribute [local instance] MvPolynomial.gradedAlgebra

/-- A homogeneous ideal not contained in another ideal has a homogeneous
element outside the latter ideal. The proof selects an actual homogeneous
component of an actual ideal-membership witness. -/
theorem exists_homogeneous_mem_not_mem
    {σ R : Type*} [CommRing R]
    (I J : Ideal (MvPolynomial σ R))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ R))
    (hIJ : ¬ I ≤ J) :
    ∃ (e : ℕ) (S : MvPolynomial σ R),
      S ∈ I ∧ S.IsHomogeneous e ∧ S ∉ J := by
  classical
  obtain ⟨P, hPI, hPJ⟩ := SetLike.not_le_iff_exists.mp hIJ
  have hex : ∃ e : ℕ, homogeneousComponent e P ∉ J := by
    by_contra! h
    apply hPJ
    rw [← sum_homogeneousComponent P]
    exact J.sum_mem fun e _ => h e
  obtain ⟨e, he⟩ := hex
  exact ⟨e, homogeneousComponent e P,
    homogeneousComponent_mem_of_mem hI hPI e,
    homogeneousComponent_isHomogeneous e P, he⟩

/-- The special case used when the hypersurface ideal is properly contained
in the ideal of a support. -/
theorem homogeneous_equation_of_strict_ideal_inclusion
    {σ R : Type*} [CommRing R]
    (F : MvPolynomial σ R) (I : Ideal (MvPolynomial σ R))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ R))
    (hFI : Ideal.span ({F} : Set (MvPolynomial σ R)) < I) :
    ∃ (e : ℕ) (S : MvPolynomial σ R),
      S ∈ I ∧ S.IsHomogeneous e ∧ ¬ F ∣ S := by
  obtain ⟨e, S, hSI, hShom, hSF⟩ :=
    exists_homogeneous_mem_not_mem I (Ideal.span {F}) hI (not_le_of_gt hFI)
  exact ⟨e, S, hSI, hShom, by simpa only [Ideal.mem_span_singleton] using hSF⟩

abbrev ambientGrading (n : ℕ) := homogeneousSubmodule (Fin (n + 1)) ℂ

/-- The actual topological projective spectrum of the ambient polynomial ring. -/
abbrev AmbientProjectiveSpace (n : ℕ) := ProjectiveSpectrum (ambientGrading n)

/-- A proper closed subset of an actual projective hypersurface has a
homogeneous ambient equation that is not divisible by its defining equation.
No projective Nullstellensatz or saturation hypothesis is needed: otherwise
zero-locus antitonicity would force the entire hypersurface into the support. -/
theorem homogeneous_equation_of_closed_proper_subset
    {n : ℕ} (F : AmbientPoly n) (Z : Set (AmbientProjectiveSpace n))
    (hZ : IsClosed Z)
    (hproper : Z ⊂ ProjectiveSpectrum.zeroLocus (ambientGrading n) {F}) :
    ∃ (e : ℕ) (S : AmbientPoly n),
      S.IsHomogeneous e ∧ ¬ F ∣ S ∧
      Z ⊆ ProjectiveSpectrum.zeroLocus (ambientGrading n) {S} := by
  classical
  let I := ProjectiveSpectrum.vanishingIdeal Z
  have hnot : ¬ I.toIdeal ≤ Ideal.span ({F} : Set (AmbientPoly n)) := by
    intro h
    have hreverse := ProjectiveSpectrum.zeroLocus_anti_mono_ideal
      (ambientGrading n) h
    change ProjectiveSpectrum.zeroLocus (ambientGrading n) (Ideal.span {F}) ⊆
      ProjectiveSpectrum.zeroLocus (ambientGrading n)
        (ProjectiveSpectrum.vanishingIdeal Z) at hreverse
    rw [ProjectiveSpectrum.zeroLocus_span,
      ProjectiveSpectrum.zeroLocus_vanishingIdeal_eq_closure, hZ.closure_eq] at hreverse
    exact hproper.2 hreverse
  obtain ⟨e, S, hSI, hShom, hSF⟩ :=
    exists_homogeneous_mem_not_mem I.toIdeal (Ideal.span {F}) I.isHomogeneous hnot
  refine ⟨e, S, hShom, ?_, ?_⟩
  · simpa only [Ideal.mem_span_singleton] using hSF
  · apply (ProjectiveSpectrum.subset_zeroLocus_iff_subset_vanishingIdeal
      (ambientGrading n) Z {S}).mpr
    exact Set.singleton_subset_iff.mpr hSI

theorem not_dvd_coordinate_of_degree_gt_one
    {n : ℕ} (F : AmbientPoly n) (hdegree : 1 < F.totalDegree)
    (i : Fin (n + 1)) : ¬ F ∣ X i := by
  intro h
  have hh := totalDegree_le_of_dvd_of_isDomain h (X_ne_zero i)
  rw [totalDegree_X] at hh
  exact (not_le_of_gt hdegree) hh

/-- A positive-degree support equation and its square denominator, with
legality derived from irreducibility. This is the exact equation-selection
step used before filtered de Rham theory is invoked. -/
theorem legal_square_of_closed_proper_subset
    {n : ℕ} (F : AmbientPoly n) (Z : Set (AmbientProjectiveSpace n))
    (hF : Irreducible F) (hdegree : 1 < F.totalDegree)
    (hZ : IsClosed Z)
    (hproper : Z ⊂ ProjectiveSpectrum.zeroLocus (ambientGrading n) {F}) :
    ∃ (e : ℕ) (S : AmbientPoly n),
      0 < e ∧ S.IsHomogeneous e ∧ S ≠ 0 ∧ ¬ F ∣ S ∧
      Z ⊆ ProjectiveSpectrum.zeroLocus (ambientGrading n) {S} ∧
      (S ^ 2).IsHomogeneous (2 * e) ∧ S ^ 2 ≠ 0 ∧ IsRelPrime F (S ^ 2) := by
  obtain ⟨e, S, hShom, hnot, hcover⟩ :=
    homogeneous_equation_of_closed_proper_subset F Z hZ hproper
  have hS : S ≠ 0 := by
    intro h
    apply hnot
    rw [h]
    exact dvd_zero F
  have hlegal : IsRelPrime F S := hF.isRelPrime_iff_not_dvd.mpr hnot
  have hXlegal : IsRelPrime F (X (0 : Fin (n + 1))) :=
    hF.isRelPrime_iff_not_dvd.mpr (not_dvd_coordinate_of_degree_gt_one F hdegree 0)
  have hprodlegal : IsRelPrime F (S * X (0 : Fin (n + 1))) :=
    hlegal.mul_right hXlegal
  have hprod : S * X (0 : Fin (n + 1)) ≠ 0 := mul_ne_zero hS (X_ne_zero 0)
  have hprodhom : (S * X (0 : Fin (n + 1))).IsHomogeneous (e + 1) :=
    hShom.mul (isHomogeneous_X ℂ 0)
  refine ⟨e + 1, S * X 0, Nat.succ_pos e, hprodhom, hprod,
    hF.isRelPrime_iff_not_dvd.mp hprodlegal, ?_, ?_, pow_ne_zero 2 hprod,
    hprodlegal.pow_right⟩
  · rw [ProjectiveSpectrum.zeroLocus_singleton_mul]
    exact hcover.trans Set.subset_union_left
  · simpa only [Nat.mul_comm] using hprodhom.pow 2

/-- Exact target specialization: every actual proper projective closed
support admits a legal homogeneous square denominator, existentially. -/
theorem protected_support_has_legal_square
    (Z : Set (AmbientProjectiveSpace 5))
    (hZ : IsClosed Z)
    (hproper : Z ⊂ ProjectiveSpectrum.zeroLocus (ambientGrading 5) {HodgeSubmission.F}) :
    ∃ (e : ℕ) (S : AmbientPoly 5),
      0 < e ∧ S.IsHomogeneous e ∧ S ≠ 0 ∧ ¬ HodgeSubmission.F ∣ S ∧
      Z ⊆ ProjectiveSpectrum.zeroLocus (ambientGrading 5) {S} ∧
      (S ^ 2).IsHomogeneous (2 * e) ∧ S ^ 2 ≠ 0 ∧
      IsRelPrime HodgeSubmission.F (S ^ 2) := by
  apply legal_square_of_closed_proper_subset HodgeSubmission.F Z
    CycleQ2ExactIrreducible.protected_F_irreducible
  · rw [CycleQ2Workspace.originalF_totalDegree]
    decide
  · exact hZ
  · exact hproper

/-- The actual protected hypersurface as a closed subspace of projective
spectrum, with its induced topology. -/
abbrev ProtectedHypersurface :=
  {x : AmbientProjectiveSpace 5 //
    x ∈ ProjectiveSpectrum.zeroLocus (ambientGrading 5) {HodgeSubmission.F}}

/-- The geometric support statement normally provides a proper closed subset
inside X. Closedness of the hypersurface promotes that relative support to an
ambient closed set, so the preceding theorem applies without an added
ambient-closedness assumption. -/
theorem protected_relative_support_has_legal_square
    (Z : Set ProtectedHypersurface) (hZ : IsClosed Z) (hproper : Z ≠ Set.univ) :
    ∃ (e : ℕ) (S : AmbientPoly 5),
      0 < e ∧ S.IsHomogeneous e ∧ S ≠ 0 ∧ ¬ HodgeSubmission.F ∣ S ∧
      (∀ x ∈ Z, x.val ∈ ProjectiveSpectrum.zeroLocus (ambientGrading 5) {S}) ∧
      (S ^ 2).IsHomogeneous (2 * e) ∧ S ^ 2 ≠ 0 ∧
      IsRelPrime HodgeSubmission.F (S ^ 2) := by
  let Y : Set (AmbientProjectiveSpace 5) := Subtype.val '' Z
  have hY : IsClosed Y :=
    (ProjectiveSpectrum.isClosed_zeroLocus (ambientGrading 5)
      {HodgeSubmission.F}).isClosedMap_subtype_val Z hZ
  have hYproper : Y ⊂ ProjectiveSpectrum.zeroLocus (ambientGrading 5)
      {HodgeSubmission.F} := by
    refine ⟨?_, ?_⟩
    · rintro x ⟨y, hy, rfl⟩
      exact y.property
    · intro h
      apply hproper
      apply Set.eq_univ_of_forall
      intro x
      obtain ⟨y, hy, hxy⟩ := h x.property
      have he : y = x := Subtype.ext hxy
      simpa only [he] using hy
  obtain ⟨e, S, he, hShom, hS, hnot, hcover, hDhom, hD, hlegal⟩ :=
    protected_support_has_legal_square Y hY hYproper
  refine ⟨e, S, he, hShom, hS, hnot, ?_, hDhom, hD, hlegal⟩
  intro x hx
  exact hcover ⟨x, hx, rfl⟩


/-- The homogeneous prime ideal `(F)` is an actual generic point of the
projective hypersurface. The degree assumption excludes the irrelevant ideal.
Its singleton closure gives irreducibility of the actual projective zero set. -/
theorem hypersurface_isIrreducible
    {n d : ℕ} (F : AmbientPoly n)
    (hF : Irreducible F) (hhom : F.IsHomogeneous d)
    (hdegree : 1 < F.totalDegree) :
    IsIrreducible (ProjectiveSpectrum.zeroLocus (ambientGrading n) {F}) := by
  let I : HomogeneousIdeal (ambientGrading n) :=
    ⟨Ideal.span {F}, Ideal.homogeneous_span (ambientGrading n) {F} (by
      intro x hx
      rcases Set.mem_singleton_iff.mp hx with rfl
      exact ⟨d, hhom⟩)⟩
  let η : AmbientProjectiveSpace n :=
    { asHomogeneousIdeal := I
      isPrime := (Ideal.span_singleton_prime hF.ne_zero).mpr hF.prime
      not_irrelevant_le := by
        intro h
        have hX : (X (0 : Fin (n + 1)) : AmbientPoly n) ∈
            HomogeneousIdeal.irrelevant (ambientGrading n) :=
          HomogeneousIdeal.mem_irrelevant_of_mem (ambientGrading n)
            (by decide : 0 < 1) (isHomogeneous_X ℂ 0)
        exact not_dvd_coordinate_of_degree_gt_one F hdegree 0
          (Ideal.mem_span_singleton.mp (h hX)) }
  have hclosure : closure ({η} : Set (AmbientProjectiveSpace n)) =
      ProjectiveSpectrum.zeroLocus (ambientGrading n) {F} := by
    rw [← ProjectiveSpectrum.zeroLocus_vanishingIdeal_eq_closure,
      ProjectiveSpectrum.vanishingIdeal_singleton]
    change ProjectiveSpectrum.zeroLocus (ambientGrading n) (Ideal.span {F}) = _
    exact ProjectiveSpectrum.zeroLocus_span (ambientGrading n) {F}
  rw [← hclosure]
  exact isIrreducible_singleton.closure

/-- Irreducibility of the exact protected hypersurface as an actual space. -/
theorem protected_hypersurface_irreducible :
    IrreducibleSpace ProtectedHypersurface := by
  apply Subtype.irreducibleSpace
  apply hypersurface_isIrreducible HodgeSubmission.F
    CycleQ2ExactIrreducible.protected_F_irreducible
    CycleQ2Workspace.originalF_homogeneous
  rw [CycleQ2Workspace.originalF_totalDegree]
  decide

/-- A finite collection of genuine proper closed supports inside the
protected hypersurface still has proper union. -/
theorem protected_finite_union_proper
    (T : Finset (Set ProtectedHypersurface))
    (hclosed : ∀ Z ∈ T, IsClosed Z)
    (hproper : ∀ Z ∈ T, Z ≠ Set.univ) :
    ⋃₀ (T : Set (Set ProtectedHypersurface)) ≠ Set.univ := by
  letI := protected_hypersurface_irreducible
  intro h
  obtain ⟨Z, hZT, hcover⟩ := isIrreducible_iff_sUnion_isClosed.mp
    (IrreducibleSpace.isIrreducible_univ ProtectedHypersurface) T hclosed
    (by rw [h])
  exact hproper Z hZT (Set.eq_univ_of_univ_subset hcover)

/-- A finite family of proper closed supports has one positive-degree
homogeneous ambient equation whose square is a legal denominator. -/
theorem protected_finite_supports_have_legal_square
    (T : Finset (Set ProtectedHypersurface))
    (hclosed : ∀ Z ∈ T, IsClosed Z)
    (hproper : ∀ Z ∈ T, Z ≠ Set.univ) :
    ∃ (e : ℕ) (S : AmbientPoly 5),
      0 < e ∧ S.IsHomogeneous e ∧ S ≠ 0 ∧ ¬ HodgeSubmission.F ∣ S ∧
      (∀ Z ∈ T, ∀ x ∈ Z,
        x.val ∈ ProjectiveSpectrum.zeroLocus (ambientGrading 5) {S}) ∧
      (S ^ 2).IsHomogeneous (2 * e) ∧ S ^ 2 ≠ 0 ∧
      IsRelPrime HodgeSubmission.F (S ^ 2) := by
  have hc : IsClosed (⋃₀ (T : Set (Set ProtectedHypersurface))) := by
    rw [Set.sUnion_eq_biUnion]
    exact isClosed_biUnion_finset hclosed
  obtain ⟨e, S, he, hShom, hS, hnot, hcover, hDhom, hD, hlegal⟩ :=
    protected_relative_support_has_legal_square _ hc
      (protected_finite_union_proper T hclosed hproper)
  refine ⟨e, S, he, hShom, hS, hnot, ?_, hDhom, hD, hlegal⟩
  intro Z hZT x hx
  exact hcover x ⟨Z, hZT, hx⟩

end CycleQ2SupportEquation

#print axioms CycleQ2SupportEquation.homogeneous_equation_of_closed_proper_subset
#print axioms CycleQ2SupportEquation.protected_support_has_legal_square
#print axioms CycleQ2SupportEquation.protected_relative_support_has_legal_square

#print axioms CycleQ2SupportEquation.protected_hypersurface_irreducible
#print axioms CycleQ2SupportEquation.protected_finite_supports_have_legal_square
end
end


namespace CycleQ2FormalInputs

/-- A precise equivalent form of the unchanged protected goal. This theorem
does not prove the existential on either side. In particular, it makes no
assumption that a supporting equation or primitive has already been found. -/
theorem protected_certificate_iff_square_primitive :
    HodgeComputer.HasCertificate
        HodgeSubmission.F HodgeSubmission.q HodgeSubmission.A ↔
      ∃ (e : ℕ) (S : HodgeComputer.AmbientPoly 5)
          (N : Fin 6 → HodgeComputer.AmbientPoly 5),
        S.IsHomogeneous e ∧ ¬ HodgeSubmission.F ∣ S ∧
        (∀ i, HodgeComputer.Homogeneous (N i) (2 * (e : ℤ) + 7)) ∧
        CycleQ2Bridge.LocalizedEquation
          HodgeSubmission.F HodgeSubmission.A 2 (S ^ 2) N := by
  exact CycleQ2Bridge.sextic_q2_hasCertificate_iff_square_primitive
    HodgeSubmission.F HodgeSubmission.A
    CycleQ2ExactIrreducible.protected_F_irreducible
    CycleQ2Workspace.originalF_homogeneous
    (HodgeComputer.Homogeneous.of_isHomogeneous
      CycleQ2Workspace.originalA_homogeneous)

end CycleQ2FormalInputs

#print axioms CycleQ2FormalInputs.protected_certificate_iff_square_primitive
