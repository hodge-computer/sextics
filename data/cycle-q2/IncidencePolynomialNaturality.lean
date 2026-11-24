import Proposal.GeometricSeedCoordinateCover
import Proposal.GeometricSurfaceCoordinates
import Proposal.CurveRestrictionRightInverse

/-!
# Incidence polynomials and specialization

The equations, Jacobian and their relations respect coefficient specialization.
-/

set_option Elab.async false

/- Component: continuation_3/IncidenceJacobianNaturality.lean -/
section
/-! The literal first-order incidence system commutes with coefficient maps.
This supplies a single integral matrix whose modular and complex versions
are obtained by applying ring homomorphisms, rather than comparing unrelated
numerical matrices. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

namespace CycleQ2IncidenceJacobianNaturality

open MvPolynomial CycleQ2IncidenceNormalForm CycleQ2IncidenceMonomials
  CycleQ2IncidenceEquations CycleQ2IncidenceFirstOrder CycleQ2IncidenceJacobian
  CycleQ2IncidenceUniversalChart
  CycleQ2IncidenceCoefficientRelations

variable {R S : Type*} [CommRing R] [CommRing S]

theorem map_smoothH (φ : R →+* S) (ι : R) :
    map φ (smoothH ι) = smoothH (φ ι) := by
  simp [smoothH, smoothA, smoothB]

theorem map_smoothK (φ : R →+* S) (ι : R) :
    map φ (smoothK ι) = smoothK (φ ι) := by
  simp [smoothK, smoothA, smoothB]

theorem map_seedG (φ : R →+* S) (r : R) :
    map φ (seedG r) = seedG (φ r) := by
  simp [seedG, CycleQ2SegreSeed.seedG_expanded]

theorem map_smoothF (φ : R →+* S) (r ι : R) :
    map φ (smoothF r ι) = smoothF (φ r) (φ ι) := by
  simp only [smoothF, map_add, map_mul, map_seedG, map_smoothH, map_smoothK]

theorem map_seedCubicCoefficients (φ : R →+* S) (ι : R) :
    φ ∘ seedCubicCoefficients ι = seedCubicCoefficients (φ ι) := by
  funext e
  simp only [Function.comp_apply, seedCubicCoefficients, ← coeff_map, map_smoothH]

theorem map_seedSexticCoefficients (φ : R →+* S) (r ι : R) :
    φ ∘ seedSexticCoefficients r ι = seedSexticCoefficients (φ r) (φ ι) := by
  funext e
  simp only [Function.comp_apply, seedSexticCoefficients, ← coeff_map, map_smoothF]

theorem seedG_ne_zero [Nontrivial R] (r : R) : seedG r ≠ 0 := by
  intro hz
  have h := congrArg (eval (fun j : Fin 5 => if j = 4 then (1 : R) else 0)) hz
  norm_num [seedG, CycleQ2SegreSeed.seedG_expanded] at h
  norm_num [Fin.ext_iff] at h

theorem map_rawCofactorQuotient [IsDomain S] (φ : R →+* S) (r : R) (i j : Fin 3) :
    map φ (rawCofactorQuotient r i j) = rawCofactorQuotient (φ r) i j := by
  apply mul_left_cancel₀ (seedG_ne_zero (φ r))
  have h := congrArg (map φ) (rawSeedMatrix_cofactor r i j)
  rw [map_cofactors, map_rawSeedMatrix, map_mul, map_seedG,
    rawSeedMatrix_cofactor] at h
  exact h.symm

theorem map_cofactorDifferential (φ : R →+* S)
    (M N : Matrix (Fin 3) (Fin 3) (Poly R)) (i j : Fin 3) :
    map φ (cofactorDifferential M N i j) =
      cofactorDifferential ((map φ).mapMatrix M) ((map φ).mapMatrix N) i j := by
  simp only [cofactorDifferential, Matrix.sub_apply, map_sub, map_cofactors, map_add]

theorem map_fullFirstOrderResidual [IsDomain S] (φ : R →+* S) (r ι : R)
    (H J : Poly R) (N : Matrix (Fin 3) (Fin 3) (Poly R)) (i j : Fin 3) :
    map φ (fullFirstOrderResidual r ι H J N i j) =
      fullFirstOrderResidual (φ r) (φ ι) (map φ H) (map φ J)
        ((map φ).mapMatrix N) i j := by
  simp only [fullFirstOrderResidual, firstOrderResidual, map_sub, map_add, map_mul,
    map_cofactorDifferential, map_rawSeedMatrix, map_smoothK, map_rawCofactorQuotient]

theorem linearizedEquations_map [Nontrivial R] [IsDomain S]
    (φ : R →+* S) (r ι : R)
    (η : FullInvariantIndex 3 → R) (ζ : FullInvariantIndex 6 → R)
    (δ : Fin 3 → Fin 3 → StandardIndex 14 → R) (q : EquationIndex) :
    φ (linearizedEquations r ι η ζ δ q) =
      linearizedEquations (φ r) (φ ι) (φ ∘ η) (φ ∘ ζ)
        (fun i j e => φ (δ i j e)) q := by
  unfold linearizedEquations
  rw [← coeff_map, fullRemainder_map, map_fullFirstOrderResidual,
    map_fullInvariantPolynomial, map_fullInvariantPolynomial, map_perturbation]
  simp only [map_seedCubicCoefficients, map_seedSexticCoefficients]

def linearizedMatrix [Nontrivial R] (r ι : R) : Matrix EquationIndex ParameterIndex R := by
  classical
  exact fun q j => linearizedEquations r ι
    (fun e => if j = Sum.inl e then 1 else 0)
    (fun e => if j = Sum.inr (Sum.inl e) then 1 else 0)
    (fun i k e => if j = Sum.inr (Sum.inr ((i, k), e)) then 1 else 0) q

theorem linearizedMatrix_map [Nontrivial R] [IsDomain S]
    (φ : R →+* S) (r ι : R) :
    (linearizedMatrix r ι).map φ = linearizedMatrix (φ r) (φ ι) := by
  classical
  ext q j
  simp only [Matrix.map_apply, linearizedMatrix, linearizedEquations_map]
  congr 1 <;> funext <;> split_ifs <;> simp_all

theorem segreRelations_map (φ : R →+* S) (M : Matrix (Fin 3) (Fin 3) R)
    (k : Fin 16) (j : Fin 9) :
    φ (CycleQ2SegreRelations.relations M k j) =
      CycleQ2SegreRelations.relations (φ.mapMatrix M) k j := by
  fin_cases k <;> fin_cases j <;>
    simp [CycleQ2SegreRelations.relations, RingHom.mapMatrix_apply]

theorem coefficientRelations_map [Nontrivial R] [Nontrivial S] (φ : R →+* S)
    (hc : FullInvariantIndex 3 → R) (Fc : FullInvariantIndex 6 → R)
    (hu : IsUnit (hc fullCubicLeadingIndex)) (Fu : IsUnit (Fc fullSexticLeadingIndex))
    (M : Matrix (Fin 3) (Fin 3) (Poly R)) (row : RelationIndex) (col : ColumnIndex) :
    φ (coefficientRelations hc Fc hu Fu M row col) =
      coefficientRelations (φ ∘ hc) (φ ∘ Fc) (hu.map φ) (Fu.map φ)
        ((map φ).mapMatrix M) row col := by
  unfold coefficientRelations
  rw [← coeff_map, fullRemainder_map, map_mul, segreRelations_map, map_monomial, map_one]

def seedCoefficientRelations [Nontrivial R] (r ι : R) : Matrix RelationIndex ColumnIndex R :=
  coefficientRelations (seedCubicCoefficients ι) (seedSexticCoefficients r ι)
    (seedCubicCoefficients_unit ι) (seedSexticCoefficients_unit r ι) (rawSeedMatrix r)

theorem seedCoefficientRelations_map [Nontrivial R] [Nontrivial S]
    (φ : R →+* S) (r ι : R) :
    (seedCoefficientRelations r ι).map φ = seedCoefficientRelations (φ r) (φ ι) := by
  ext row col
  simp only [Matrix.map_apply, seedCoefficientRelations, coefficientRelations_map,
    map_rawSeedMatrix, map_seedCubicCoefficients, map_seedSexticCoefficients]

end CycleQ2IncidenceJacobianNaturality

#print axioms CycleQ2IncidenceJacobianNaturality.linearizedEquations_map
#print axioms CycleQ2IncidenceJacobianNaturality.linearizedMatrix_map
#print axioms CycleQ2IncidenceJacobianNaturality.seedCoefficientRelations_map
end
end

/- Component: continuation_3/IncidencePolynomialRelations.lean -/
section
/-!
# Polynomial equations and relations for the actual incidence family

A single power of the two leading coefficients clears both the entire
equation vector and the entire coefficient-relation matrix.  Injectivity
of the actual localization then proves the polynomial relation identity
before evaluation.  Thus no relation is inferred from a pointwise seed
calculation.  At the literal seed the clearing factor is one.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

namespace CycleQ2UniformDenominators

open scoped BigOperators
open Matrix

variable {P L : Type*} [CommRing P] [CommRing L] [Algebra P L]
variable (a : P) [IsLocalization.Away a L]

theorem exists_uniform_numerators {ι : Type*} [Finite ι] (v : ι → L) :
    ∃ n : ℕ, ∃ p : ι → P, ∀ i,
      algebraMap P L (p i) = algebraMap P L (a ^ n) * v i := by
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (Submonoid.powers a) v
  obtain ⟨n, hn⟩ := d.property
  have hd' : ∀ i, ∃ p : P, algebraMap P L p = (d.val : P) • v i := hd
  choose p hp using hd'
  refine ⟨n, p, fun i => ?_⟩
  simpa only [Algebra.smul_def, hn] using hp i

/-- Equations and all their linear relations can be cleared simultaneously
without losing the relation identity in the original polynomial ring. -/
theorem exists_polynomial_relations [IsDomain P] (ha : a ≠ 0)
    {ι κ : Type*} [Fintype ι] [Finite κ]
    (e : ι → L) (B : Matrix κ ι L) (hB : B *ᵥ e = 0) :
    ∃ n : ℕ, ∃ p : ι → P, ∃ A : Matrix κ ι P,
      (∀ i, algebraMap P L (p i) = algebraMap P L (a ^ n) * e i) ∧
      (∀ k i, algebraMap P L (A k i) = algebraMap P L (a ^ n) * B k i) ∧
      A *ᵥ p = 0 := by
  classical
  obtain ⟨n, v, hv⟩ := exists_uniform_numerators a
    (Sum.elim e (fun q : κ × ι => B q.1 q.2))
  let p : ι → P := fun i => v (Sum.inl i)
  let A : Matrix κ ι P := fun k i => v (Sum.inr (k, i))
  have hp (i : ι) : algebraMap P L (p i) = algebraMap P L (a ^ n) * e i := hv (.inl i)
  have hA (k : κ) (i : ι) :
      algebraMap P L (A k i) = algebraMap P L (a ^ n) * B k i := hv (.inr (k, i))
  refine ⟨n, p, A, hp, hA, ?_⟩
  funext k
  apply IsLocalization.injective L (powers_le_nonZeroDivisors_of_noZeroDivisors ha)
  change algebraMap P L (∑ i, A k i * p i) = algebraMap P L 0
  simp only [map_sum, map_mul, map_zero, hp, hA]
  have hk : (∑ i, B k i * e i) = 0 := congrFun hB k
  calc
    (∑ i, (algebraMap P L (a ^ n) * B k i) *
        (algebraMap P L (a ^ n) * e i)) =
      (algebraMap P L (a ^ n)) ^ 2 * ∑ i, B k i * e i := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
    _ = 0 := by rw [hk, mul_zero]

end CycleQ2UniformDenominators

namespace CycleQ2IncidencePolynomialRelations

open Matrix MvPolynomial CycleQ2IncidenceNormalForm CycleQ2IncidenceMonomials
  CycleQ2IncidenceEquations CycleQ2IncidenceUniversalChart
  CycleQ2IncidenceCoefficientRelations

variable (R : Type*) [CommRing R] [IsDomain R]

def universalRelations (r : R) : Matrix RelationIndex ColumnIndex (ParameterRing R) :=
  coefficientRelations (cubicCoefficient R) (sexticCoefficient R)
    (leading_coefficients_units R).1 (leading_coefficients_units R).2
    (incidenceMatrix (algebraMap R (ParameterRing R) r) (matrixCoefficient R))

def orderedEquations (r : R) : ColumnIndex → ParameterRing R :=
  fun q => equations R r (columnEquiv q)

theorem universal_relation_identity (r : R) :
    universalRelations R r *ᵥ orderedEquations R r = 0 :=
  coefficientRelations_incidenceEquations (cubicCoefficient R) (sexticCoefficient R)
    (leading_coefficients_units R).1 (leading_coefficients_units R).2
    (algebraMap R (ParameterRing R) r) (matrixCoefficient R)

structure Presentation (r : R) where
  exponent : ℕ
  equation : ColumnIndex → ParameterPolynomial R
  relation : Matrix RelationIndex ColumnIndex (ParameterPolynomial R)
  equation_spec : ∀ q,
    algebraMap (ParameterPolynomial R) (ParameterRing R) (equation q) =
      algebraMap (ParameterPolynomial R) (ParameterRing R) (leadingProduct R ^ exponent) *
        orderedEquations R r q
  relation_spec : ∀ k q,
    algebraMap (ParameterPolynomial R) (ParameterRing R) (relation k q) =
      algebraMap (ParameterPolynomial R) (ParameterRing R) (leadingProduct R ^ exponent) *
        universalRelations R r k q
  relation_identity : relation *ᵥ equation = 0

theorem presentation_nonempty (r : R) : Nonempty (Presentation R r) := by
  obtain ⟨n, p, A, hp, hA, hrel⟩ :=
    CycleQ2UniformDenominators.exists_polynomial_relations (leadingProduct R)
      (leadingProduct_ne_zero R) (orderedEquations R r) (universalRelations R r)
      (universal_relation_identity R r)
  exact ⟨⟨n, p, A, hp, hA, hrel⟩⟩

def presentation (r : R) : Presentation R r := (presentation_nonempty R r).some

section Specialization

variable {R} {S : Type*} [CommRing S] [Nontrivial S] [Algebra R S]

theorem equation_specialization
    (hcoeff : FullInvariantIndex 3 → S) (Fcoeff : FullInvariantIndex 6 → S)
    (hu : IsUnit (hcoeff fullCubicLeadingIndex))
    (Fu : IsUnit (Fcoeff fullSexticLeadingIndex))
    (δ : Fin 3 → Fin 3 → StandardIndex 14 → S) (r : R) (q : ColumnIndex) :
    polynomialSpecialization hcoeff Fcoeff δ ((presentation R r).equation q) =
      (hcoeff fullCubicLeadingIndex * Fcoeff fullSexticLeadingIndex) ^
          (presentation R r).exponent *
        incidenceEquations hcoeff Fcoeff hu Fu (algebraMap R S r) δ (columnEquiv q) := by
  have h := congrArg (specialization hcoeff Fcoeff hu Fu δ)
    ((presentation R r).equation_spec q)
  simpa only [orderedEquations, map_mul, specialization_polynomial, map_pow,
    polynomialSpecialization_leadingProduct, specialization_equations] using h

theorem equations_zero_iff
    (hcoeff : FullInvariantIndex 3 → S) (Fcoeff : FullInvariantIndex 6 → S)
    (hu : IsUnit (hcoeff fullCubicLeadingIndex))
    (Fu : IsUnit (Fcoeff fullSexticLeadingIndex))
    (δ : Fin 3 → Fin 3 → StandardIndex 14 → S) (r : R) :
    (∀ q, polynomialSpecialization hcoeff Fcoeff δ ((presentation R r).equation q) = 0) ↔
      ∀ i j, CycleQ2SegreLocal.cofactors (incidenceMatrix (algebraMap R S r) δ) i j ∈
        equationsIdeal (fullInvariantPolynomial 3 hcoeff) (fullInvariantPolynomial 6 Fcoeff) := by
  rw [← incidenceEquations_zero_iff hcoeff Fcoeff hu Fu (algebraMap R S r) δ]
  have hz (q : ColumnIndex) :
      polynomialSpecialization hcoeff Fcoeff δ ((presentation R r).equation q) = 0 ↔
        incidenceEquations hcoeff Fcoeff hu Fu (algebraMap R S r) δ (columnEquiv q) = 0 := by
    rw [equation_specialization hcoeff Fcoeff hu Fu δ r q]
    exact ((hu.mul Fu).pow _).mul_right_eq_zero
  simp only [hz]
  exact columnEquiv.forall_congr (fun _ => Iff.rfl)

end Specialization

theorem seed_equations_zero (r ι : R) (q : ColumnIndex) :
    polynomialSpecialization (seedCubicCoefficients ι) (seedSexticCoefficients r ι)
      (fun _ _ _ => 0) ((presentation R r).equation q) = 0 := by
  rw [equation_specialization _ _ (seedCubicCoefficients_unit ι)
    (seedSexticCoefficients_unit r ι)]
  simp only [Algebra.algebraMap_self, RingHom.id_apply, smoothSeed_equations_zero, mul_zero]

theorem seed_leadingProduct (r ι : R) :
    seedSpecialization R r ι
      (algebraMap (ParameterPolynomial R) (ParameterRing R) (leadingProduct R)) = 1 := by
  rw [seedSpecialization, specialization_polynomial,
    polynomialSpecialization_leadingProduct]
  simp only [seedCubicCoefficients, seedSexticCoefficients,
    fullCubicLeadingIndex_exponent, fullSexticLeadingIndex_exponent,
    smoothH_leading_coefficient, smoothF_leading_coefficient, one_mul]

/-- Every cleared relation has exactly the original localized value at the
literal seed, because both of its leading coefficients are one. -/
theorem seed_relation_value (r ι : R) (k : RelationIndex) (q : ColumnIndex) :
    polynomialSpecialization (seedCubicCoefficients ι) (seedSexticCoefficients r ι)
      (fun _ _ _ => 0) ((presentation R r).relation k q) =
        seedSpecialization R r ι (universalRelations R r k q) := by
  have h := congrArg (seedSpecialization R r ι) ((presentation R r).relation_spec k q)
  rw [map_mul, map_pow, map_pow, seed_leadingProduct, one_pow, one_mul] at h
  simpa only [seedSpecialization, specialization_polynomial] using h

section Derivative

variable {S : Type*} [CommRing S] [Algebra (ParameterRing R) S]

theorem differential_at_solution (r : R) (q : ColumnIndex)
    (D : Derivation ℤ (ParameterRing R) S)
    (hzero : algebraMap (ParameterRing R) S (orderedEquations R r q) = 0) :
    D (algebraMap (ParameterPolynomial R) (ParameterRing R)
        ((presentation R r).equation q)) =
      algebraMap (ParameterRing R) S
        (algebraMap (ParameterPolynomial R) (ParameterRing R)
          (leadingProduct R ^ (presentation R r).exponent)) *
        D (orderedEquations R r q) := by
  rw [(presentation R r).equation_spec, Derivation.leibniz]
  simp only [Algebra.smul_def, hzero, zero_mul, add_zero]

end Derivative

def seedRelationMatrix (r ι : R) : Matrix RelationIndex ColumnIndex R :=
  fun k q => polynomialSpecialization (seedCubicCoefficients ι)
    (seedSexticCoefficients r ι) (fun _ _ _ => 0) ((presentation R r).relation k q)

def seedJacobian (r ι : R) : Matrix ColumnIndex ParameterIndex R :=
  fun q j => polynomialSpecialization (seedCubicCoefficients ι)
    (seedSexticCoefficients r ι) (fun _ _ _ => 0)
      (pderiv j ((presentation R r).equation q))

/-- Differentiating the actual polynomial relation identity at the literal
smooth seed yields the genuine relation matrix times the genuine parameter
Jacobian.  No numerical rank calculation is used for this identity. -/
theorem seed_relations_jacobian (r ι : R) :
    seedRelationMatrix R r ι * seedJacobian R r ι = 0 := by
  classical
  ext k j
  let ev : ParameterPolynomial R →ₐ[R] R := polynomialSpecialization (seedCubicCoefficients ι)
    (seedSexticCoefficients r ι) (fun _ _ _ => 0)
  have h := congrArg (fun p : ParameterPolynomial R => ev (pderiv j p))
    (congrFun (presentation R r).relation_identity k)
  change ev (pderiv j (∑ q, (presentation R r).relation k q *
    (presentation R r).equation q)) = ev (pderiv j 0) at h
  have he (q : ColumnIndex) : ev ((presentation R r).equation q) = 0 :=
    seed_equations_zero R r ι q
  simpa only [seedRelationMatrix, seedJacobian, Matrix.mul_apply, Matrix.zero_apply,
    map_sum, pderiv_mul, map_add, map_mul, he, mul_zero, zero_add, map_zero] using h

end CycleQ2IncidencePolynomialRelations

#print axioms CycleQ2UniformDenominators.exists_polynomial_relations
#print axioms CycleQ2IncidencePolynomialRelations.presentation_nonempty
#print axioms CycleQ2IncidencePolynomialRelations.equations_zero_iff
#print axioms CycleQ2IncidencePolynomialRelations.seed_relation_value
#print axioms CycleQ2IncidencePolynomialRelations.differential_at_solution
#print axioms CycleQ2IncidencePolynomialRelations.seed_relations_jacobian
end
end
