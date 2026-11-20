import Proposal.SegreFlatActionThirdRow
import Proposal.SegreBasepointSOne
import Proposal.SegreBasepointSThree
import Proposal.SegreBasepointSTwo
import Proposal.SegreBasepointSZero
import Proposal.SegreBasepointW

/-!
# The modular Segre basepoint

The literal basepoint data used in the modular pairing.
-/

set_option Elab.async false

/- Component: continuation_3/SegreModularBasepoint.lean -/
section
/-!
# Actual projective basepoint witnesses for the modular Segre seed

Five checked polynomial identities place powers of every weighted coordinate
in the actual raw-entry ideal modulo h and F. They exclude every relevant
prime as a common zero and make the raw entries generate the unit ideal on
each coordinate localization. No characteristic-zero basepoint assertion
or unverified rank is used.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option maxRecDepth 20000

namespace CycleQ2SegreModularBasepoint

open MvPolynomial CycleQ2SparseModularPolynomial CycleQ2SegreModularBasepointData
  CycleQ2SegreModularTangent CycleQ2IncidenceEquations CycleQ2IncidenceFirstOrder
  CycleQ2IncidenceNormalForm CycleQ2SegreTangentLocal
open scoped BigOperators

variable {R : Type*} [CommRing R] [CharP R 109]

def generators : Fin 11 → P R :=
  ![rawSeedMatrix (57 : R) 0 0, rawSeedMatrix (57 : R) 0 1, rawSeedMatrix (57 : R) 0 2,
    rawSeedMatrix (57 : R) 1 0, rawSeedMatrix (57 : R) 1 1, rawSeedMatrix (57 : R) 1 2,
    rawSeedMatrix (57 : R) 2 0, rawSeedMatrix (57 : R) 2 1, rawSeedMatrix (57 : R) 2 2,
    smoothH (33 : R), seedG (57 : R)]

def generatorBlocks : Fin 11 → Blocks :=
  ![CycleQ2SegreModularTangentData.m00, CycleQ2SegreModularTangentData.m01,
    CycleQ2SegreModularTangentData.m02, CycleQ2SegreModularTangentData.m10,
    CycleQ2SegreModularTangentData.m11, CycleQ2SegreModularTangentData.m12,
    CycleQ2SegreModularTangentData.m20, CycleQ2SegreModularTangentData.m21,
    CycleQ2SegreModularTangentData.m22, CycleQ2SegreModularTangentData.h,
    CycleQ2SegreModularTangentData.g]

theorem value_generators (j : Fin 11) :
    value (R := R) (generatorBlocks j) = generators j := by
  fin_cases j
  · exact value_rawMatrix 0 0
  · exact value_rawMatrix 0 1
  · exact value_rawMatrix 0 2
  · exact value_rawMatrix 1 0
  · exact value_rawMatrix 1 1
  · exact value_rawMatrix 1 2
  · exact value_rawMatrix 2 0
  · exact value_rawMatrix 2 1
  · exact value_rawMatrix 2 2
  · exact value_h
  · exact value_g

def witnesses : Fin 5 → Fin 11 → Blocks :=
  ![![witness0_00,witness0_01,witness0_02,witness0_10,witness0_11,witness0_12,
      witness0_20,witness0_21,witness0_22,hWitness0,gWitness0],
    ![witness1_00,witness1_01,witness1_02,witness1_10,witness1_11,witness1_12,
      witness1_20,witness1_21,witness1_22,hWitness1,gWitness1],
    ![witness2_00,witness2_01,witness2_02,witness2_10,witness2_11,witness2_12,
      witness2_20,witness2_21,witness2_22,hWitness2,gWitness2],
    ![witness3_00,witness3_01,witness3_02,witness3_10,witness3_11,witness3_12,
      witness3_20,witness3_21,witness3_22,hWitness3,gWitness3],
    ![witness4_00,witness4_01,witness4_02,witness4_10,witness4_11,witness4_12,
      witness4_20,witness4_21,witness4_22,hWitness4,gWitness4]]

def targets : Fin 5 → Blocks := ![target0,target1,target2,target3,target4]
def degrees : Fin 5 → ℕ := ![24,24,24,24,12]
def residuals : Fin 5 → Blocks :=
  ![residualExpression0,residualExpression1,residualExpression2,residualExpression3,residualExpression4]

theorem value_targets (i : Fin 5) : value (R := R) (targets i) = X i ^ degrees i := by
  fin_cases i <;>
    simp [targets, degrees, target0, target1, target2, target3, target4, value,
      evalBlocks, evalLayers, CycleQ2SparseModularPolynomial.eval,
      termValue, CycleQ2SparseModularPolynomial.monomial] <;> ring

theorem value_empty : value (R := R) [] = 0 := rfl

theorem value_residuals (i : Fin 5) :
    value (R := R) (residuals i) = value (targets i) -
      ∑ j : Fin 11, value (generatorBlocks j) * value (witnesses i j) := by
  fin_cases i <;>
    simp only [residuals, residualExpression0, residualExpression1, residualExpression2,
      residualExpression3, residualExpression4, targets, witnesses, generatorBlocks,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_succ, Matrix.cons_val_zero', Matrix.cons_val_succ',
      Fin.sum_univ_succ, Fin.sum_univ_zero, value_add, value_mul, value_neg,
      value_empty, add_zero, sub_eq_add_neg]

theorem residuals_zero (i : Fin 5) : value (R := R) (residuals i) = 0 := by
  fin_cases i
  · exact identity0 X (X 0) (X 4)
  · exact identity1 X (X 0) (X 4)
  · exact identity2 X (X 0) (X 4)
  · exact identity3 X (X 0) (X 4)
  · exact identity4 X (X 0) (X 4)

/-- The literal powers and polynomial multipliers are all present in the
certificate; this is an identity of actual weighted-coordinate polynomials. -/
theorem coordinate_power_identity (i : Fin 5) :
    (X i : P R) ^ degrees i = ∑ j : Fin 11, generators j * value (witnesses i j) := by
  have h := residuals_zero (R := R) i
  rw [value_residuals, value_targets] at h
  simpa only [value_generators] using sub_eq_zero.mp h

def generatorIdeal : Ideal (P R) := Ideal.span (Set.range (generators (R := R)))

theorem coordinate_power_mem (i : Fin 5) :
    (X i : P R) ^ degrees i ∈ generatorIdeal (R := R) := by
  rw [coordinate_power_identity]
  apply Ideal.sum_mem
  intro j _
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_range_self j))

abbrev ActualSeedRing := SeedRing (57 : R) (33 : R)

def coordinate (i : Fin 5) : ActualSeedRing (R := R) :=
  Ideal.Quotient.mk _ (X i)

def matrix : Matrix (Fin 3) (Fin 3) (ActualSeedRing (R := R)) :=
  seedQuotientMatrix (57 : R) (33 : R)

def entryIdeal : Ideal (ActualSeedRing (R := R)) :=
  Ideal.span (Set.range (fun p : Fin 3 × Fin 3 => matrix (R := R) p.1 p.2))

theorem quotient_h :
    Ideal.Quotient.mk (equationsIdeal (smoothH (33 : R)) (smoothF (57 : R) 33))
      (smoothH (33 : R)) = 0 := by
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact Ideal.subset_span (by simp)

theorem quotient_g :
    Ideal.Quotient.mk (equationsIdeal (smoothH (33 : R)) (smoothF (57 : R) 33))
      (seedG (57 : R)) = 0 := by
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  apply (smoothSeed_mem_iff_linkage (57 : R) 33).mpr
  exact ⟨0, 1, by simp⟩

theorem generator_quotient_mem (j : Fin 11) :
    Ideal.Quotient.mk (equationsIdeal (smoothH (33 : R)) (smoothF (57 : R) 33))
      (generators j) ∈ entryIdeal (R := R) := by
  have hm (i j : Fin 3) : matrix (R := R) i j ∈ entryIdeal (R := R) :=
    Ideal.subset_span (Set.mem_range_self (i, j))
  fin_cases j
  · exact hm 0 0
  · exact hm 0 1
  · exact hm 0 2
  · exact hm 1 0
  · exact hm 1 1
  · exact hm 1 2
  · exact hm 2 0
  · exact hm 2 1
  · exact hm 2 2
  · change Ideal.Quotient.mk _ (smoothH (33 : R)) ∈ _
    rw [quotient_h]
    exact Ideal.zero_mem _
  · change Ideal.Quotient.mk _ (seedG (57 : R)) ∈ _
    rw [quotient_g]
    exact Ideal.zero_mem _

theorem seed_coordinate_power_mem (i : Fin 5) :
    coordinate (R := R) i ^ degrees i ∈ entryIdeal (R := R) := by
  let φ := Ideal.Quotient.mk (equationsIdeal (smoothH (33 : R)) (smoothF (57 : R) 33))
  have hle : generatorIdeal (R := R) ≤ (entryIdeal (R := R)).comap φ := by
    apply Ideal.span_le.mpr
    rintro _ ⟨j, rfl⟩
    exact generator_quotient_mem j
  have h := hle (coordinate_power_mem (R := R) i)
  change φ ((X i : P R) ^ degrees i) ∈ entryIdeal (R := R) at h
  simpa only [map_pow, φ, coordinate] using h

/-- Every relevant prime of the actual modular seed has a raw-matrix pivot.
This includes nonclosed points, not only the enumerated finite-field points. -/
theorem prime_pivot_cover (P : Ideal (ActualSeedRing (R := R))) [P.IsPrime]
    (hx : ∃ i, coordinate (R := R) i ∉ P) :
    ∃ i j, matrix (R := R) i j ∉ P := by
  classical
  by_contra! hzero
  have hle : entryIdeal (R := R) ≤ P := by
    apply Ideal.span_le.mpr
    rintro _ ⟨ij, rfl⟩
    exact hzero ij.1 ij.2
  obtain ⟨i, hi⟩ := hx
  exact hi ((inferInstance : P.IsPrime).mem_of_pow_mem _ (hle (seed_coordinate_power_mem i)))

theorem field_pivot_cover {K : Type*} [Field K]
    (φ : ActualSeedRing (R := R) →+* K) (hx : ∃ i, φ (coordinate i) ≠ 0) :
    ∃ i j, IsUnit (φ (matrix i j)) :=
  CycleQ2SegreImage.exists_unit_entry_of_coordinate_powers
    (matrix (R := R)) coordinate degrees seed_coordinate_power_mem φ hx

/-- Once any coordinate is a unit, the actual raw matrix entries generate
the unit ideal. This is the algebraic cover needed to glue the pivot-chart
exactness theorems on each of the coordinate Čech opens. -/
theorem entries_generate_if_coordinate_unit {S : Type*} [CommRing S]
    (φ : ActualSeedRing (R := R) →+* S) (i : Fin 5)
    (hu : IsUnit (φ (coordinate i))) :
    Ideal.span (Set.range (fun ij : Fin 3 × Fin 3 => φ (matrix ij.1 ij.2))) = ⊤ := by
  have hm := Ideal.mem_map_of_mem φ (seed_coordinate_power_mem (R := R) i)
  have hunit : IsUnit (φ (coordinate i ^ degrees i)) := by
    rw [map_pow]
    exact hu.pow _
  have ht := Ideal.eq_top_of_isUnit_mem _ hm hunit
  simpa only [entryIdeal, Ideal.map_span, ← Set.range_comp, Function.comp_def] using ht

theorem coordinate_localization_entries_generate (i : Fin 5) :
    Ideal.span (Set.range (fun ij : Fin 3 × Fin 3 =>
      algebraMap (ActualSeedRing (R := R)) (Localization.Away (coordinate (R := R) i))
        (matrix (R := R) ij.1 ij.2))) = ⊤ :=
  entries_generate_if_coordinate_unit
    (algebraMap (ActualSeedRing (R := R)) (Localization.Away (coordinate (R := R) i))) i
    (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (coordinate (R := R) i)) _)

end CycleQ2SegreModularBasepoint

#print axioms CycleQ2SegreModularBasepoint.coordinate_power_identity
#print axioms CycleQ2SegreModularBasepoint.seed_coordinate_power_mem
#print axioms CycleQ2SegreModularBasepoint.prime_pivot_cover
#print axioms CycleQ2SegreModularBasepoint.field_pivot_cover
#print axioms CycleQ2SegreModularBasepoint.coordinate_localization_entries_generate
end
end
