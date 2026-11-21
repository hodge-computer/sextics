import Proposal.SparseSeedQuotientTrace

/-! # The degree-nine seed quotient and uniqueness of its normalized trace -/

set_option Elab.async false

/- Component: seed_trace/SparseSeedDegreeNineReduction.lean -/
section
/-!
# Monomial reductions for the actual degree-nine seed component

These reductions use the concrete ideal relations. They will be combined
with finite polynomial certificates for the surviving normal monomials.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace CycleQ2SeedTrace
open MvPolynomial

def normalizationClass (r : ℂ) : ReducedAlgebra r := reducedQuotient r (mon 1 8 0 0)
def degreeNineLine (r : ℂ) : Submodule ℂ (ReducedAlgebra r) :=
  Submodule.span ℂ {normalizationClass r}
def degreeNinePiece (r : ℂ) : Submodule ℂ (ReducedAlgebra r) :=
  Submodule.map (reducedQuotient r).toLinearMap (homogeneousSubmodule (Fin 4) ℂ 9)

theorem normalizationClass_mem_line (r : ℂ) : normalizationClass r ∈ degreeNineLine r :=
  Submodule.subset_span (Set.mem_singleton _)

theorem normalizationClass_mem_piece (r : ℂ) : normalizationClass r ∈ degreeNinePiece r := by
  exact ⟨mon 1 8 0 0, mon_homogeneous 1 8 0 0, rfl⟩

theorem normalizationClass_ne_zero (r : ℂ) (hr : r ^ 3 = 2) :
    normalizationClass r ≠ 0 := by
  intro hz
  have h := trace_normalized r hr
  change reducedTrace r hr (normalizationClass r) = 1 at h
  rw [hz, map_zero] at h
  exact zero_ne_one h

theorem fourRelationSum_mem (r : ℂ) (a b c d : Poly) :
    relation r 0 * a + relation r 1 * b + relation r 2 * c + relation r 3 * d ∈
      reducedIdeal r := by
  have hg (i : Fin 4) : relation r i ∈ reducedIdeal r := Ideal.subset_span ⟨i, rfl⟩
  exact Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _
    (Ideal.mul_mem_right a _ (hg 0)) (Ideal.mul_mem_right b _ (hg 1)))
    (Ideal.mul_mem_right c _ (hg 2))) (Ideal.mul_mem_right d _ (hg 3))

theorem quotient_eq_smul_of_relation (r z : ℂ) (p q : Poly)
    (hp : p - C z * q ∈ reducedIdeal r) :
    reducedQuotient r p = z • reducedQuotient r q := by
  have hz : reducedQuotient r (p - C z * q) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hp
  rw [map_sub, ← smul_eq_C_mul, map_smul, sub_eq_zero] at hz
  exact hz

theorem class_mem_line_of_scaled_relation (r scale z : ℂ) (p : Poly)
    (hscale : scale ≠ 0)
    (hp : C scale * p - C z * mon 1 8 0 0 ∈ reducedIdeal r) :
    reducedQuotient r p ∈ degreeNineLine r := by
  have heq := quotient_eq_smul_of_relation r z (C scale * p) (mon 1 8 0 0) hp
  have hsmul : scale • reducedQuotient r p = z • normalizationClass r := by
    simpa only [← smul_eq_C_mul, map_smul, normalizationClass] using heq
  apply ((degreeNineLine r).smul_mem_iff hscale).mp
  rw [hsmul]
  exact Submodule.smul_mem _ _ (normalizationClass_mem_line r)

theorem quotient_mon_add_two (r : ℂ) (a b c d : ℕ) :
    reducedQuotient r (mon (a + 2) b c d) =
      r • reducedQuotient r (mon a (b + 1) c (d + 1)) := by
  apply quotient_eq_smul_of_relation
  have hpoly : mon (a + 2) b c d - C r * mon a (b + 1) c (d + 1) =
      relation r 0 * mon a b c d := by
    simp only [mon, relation, Matrix.cons_val_zero, pow_add, pow_one]
    ring
  rw [hpoly]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨0, rfl⟩)

theorem quotient_mon_c_add_four_zero (r : ℂ) (a b c d : ℕ) :
    reducedQuotient r (mon a b (c + 4) d) = 0 := by
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  have hpoly : mon a b (c + 4) d = relation r 2 * mon a b c d := by
    norm_num [mon, relation, pow_add, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    ring
  rw [hpoly]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨2, rfl⟩)

theorem quotient_mon_bd_add_two_zero (r : ℂ) (a b c d : ℕ) :
    reducedQuotient r (mon a (b + 2) c (d + 2)) = 0 := by
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  have hpoly : mon a (b + 2) c (d + 2) = relation r 1 * mon a b c d := by
    norm_num [mon, relation, pow_add]
    ring
  rw [hpoly]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨1, rfl⟩)

end CycleQ2SeedTrace
end
end


/- Component: seed_trace/SparseSeedDegreeNineData.lean -/
section
/-!
# Concrete degree-nine relations in the actual sparse seed ideal

The31-by-32 homogeneous relation matrix is used only to discover polynomial
witnesses. The identities below are proved directly in the original reduced
polynomial ring, with no matrix rank or trace value assumed.

This still concerns the sparse seed; no smoothness conclusion is asserted.
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
noncomputable section
namespace CycleQ2SeedTrace
open MvPolynomial

def degreeNineExponent : Fin 32 → Fin 4 → ℕ := ![
  ![0, 0, 0, 9],
  ![0, 0, 1, 8],
  ![0, 0, 2, 7],
  ![0, 0, 3, 6],
  ![0, 1, 0, 8],
  ![0, 1, 1, 7],
  ![0, 1, 2, 6],
  ![0, 1, 3, 5],
  ![0, 5, 3, 1],
  ![0, 6, 2, 1],
  ![0, 6, 3, 0],
  ![0, 7, 1, 1],
  ![0, 7, 2, 0],
  ![0, 8, 0, 1],
  ![0, 8, 1, 0],
  ![0, 9, 0, 0],
  ![1, 0, 0, 8],
  ![1, 0, 1, 7],
  ![1, 0, 2, 6],
  ![1, 0, 3, 5],
  ![1, 1, 0, 7],
  ![1, 1, 1, 6],
  ![1, 1, 2, 5],
  ![1, 1, 3, 4],
  ![1, 4, 3, 1],
  ![1, 5, 2, 1],
  ![1, 5, 3, 0],
  ![1, 6, 1, 1],
  ![1, 6, 2, 0],
  ![1, 7, 0, 1],
  ![1, 7, 1, 0],
  ![1, 8, 0, 0]]

def degreeNineMonomial (i : Fin 32) : Poly :=
  mon (degreeNineExponent i 0) (degreeNineExponent i 1)
    (degreeNineExponent i 2) (degreeNineExponent i 3)

def degreeNineWitness0_0 (r : ℂ) : Poly :=
    C ((1 : ℂ) * Complex.I) * mon 0 7 0 0 +
    C ((-1 : ℂ) * r * Complex.I) * mon 0 6 0 1 +
    C ((1 : ℂ) * Complex.I + (1 : ℂ)) * mon 0 5 1 1 +
    C ((1 : ℂ)) * mon 0 4 3 0 +
    C ((-1 : ℂ) * r * Complex.I) * mon 0 4 1 2 +
    C ((-3 : ℂ) * r) * mon 0 3 3 1 +
    C ((-6 : ℂ) * Complex.I + (7 : ℂ)) * mon 0 3 2 2 +
    C ((1 : ℂ)) * mon 0 2 4 1 +
    C ((6 : ℂ) * Complex.I) * mon 0 2 1 4 +
    C ((-3 : ℂ) * r) * mon 0 1 4 2 +
    C ((-6 : ℂ) * Complex.I + (6 : ℂ)) * mon 0 1 3 3 +
    C ((6 : ℂ) * Complex.I) * mon 0 0 2 5

def degreeNineWitness0_1 (r : ℂ) : Poly :=
    C ((-1 : ℂ) * r * Complex.I + (1 : ℂ) * r) * mon 1 3 1 0 +
    C ((1 : ℂ) * Complex.I + (1 : ℂ)) * mon 1 3 0 1 +
    C ((-6 : ℂ) * Complex.I + (-5 : ℂ)) * mon 1 2 2 0 +
    C ((-1 : ℂ) * r * Complex.I + (-1 : ℂ) * r) * mon 1 2 0 2 +
    C ((-3 : ℂ) * r * Complex.I + (3 : ℂ) * r) * mon 1 1 2 1 +
    C ((5 : ℂ) * Complex.I + (7 : ℂ)) * mon 1 1 1 2 +
    C ((-2 : ℂ) * r * Complex.I + (-3 : ℂ) * r) * mon 1 0 4 0 +
    C ((-1 : ℂ) * Complex.I + (7 : ℂ)) * mon 1 0 3 1 +
    C ((-6 : ℂ) * Complex.I + (-6 : ℂ)) * mon 1 0 0 4 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I) * mon 0 5 0 0 +
    C ((1 : ℂ) * r * Complex.I + (2 : ℂ) * r) * mon 0 4 1 0 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I) * mon 0 3 1 1 +
    C ((-1 : ℂ) * r * Complex.I + (1 : ℂ) * r) * mon 0 3 0 2 +
    C ((-3 : ℂ) * r ^ 2) * mon 0 2 3 0 +
    C ((-9 : ℂ) * r * Complex.I + (4 : ℂ) * r) * mon 0 2 2 1 +
    C ((6 : ℂ)) * mon 0 2 1 2 +
    C ((-2 : ℂ) * r * Complex.I + (1 : ℂ) * r) * mon 0 1 4 0 +
    C ((6 : ℂ)) * mon 0 1 3 1 +
    C ((6 : ℂ) * r * Complex.I) * mon 0 1 1 3 +
    C ((6 : ℂ) * Complex.I + (-6 : ℂ)) * mon 0 1 0 4 +
    C ((-3 : ℂ) * r ^ 2) * mon 0 0 4 1 +
    C ((-11 : ℂ) * r * Complex.I + (7 : ℂ) * r) * mon 0 0 3 2 +
    C ((6 : ℂ) * Complex.I) * mon 0 0 2 3

def degreeNineWitness0_2 (r : ℂ) : Poly :=
    C ((2 : ℂ)) * mon 1 3 0 1 +
    C ((1 : ℂ)) * mon 1 2 2 0 +
    C ((-3 : ℂ) * r) * mon 1 1 2 1 +
    C ((-6 : ℂ) * Complex.I + (6 : ℂ)) * mon 1 1 1 2 +
    C ((12 : ℂ) * Complex.I) * mon 1 0 0 4 +
    C ((-2 : ℂ) * r * Complex.I) * mon 0 2 2 1 +
    C ((-3 : ℂ) * r * Complex.I + (3 : ℂ) * r) * mon 0 1 1 3 +
    C ((12 : ℂ) * Complex.I) * mon 0 1 0 4 +
    C ((6 : ℂ) * Complex.I) * mon 0 0 2 3

def degreeNineWitness0_3 (r : ℂ) : Poly :=
    C ((-1 : ℂ) * Complex.I) * mon 1 5 0 0 +
    C ((1 : ℂ) * r * Complex.I) * mon 1 4 0 1 +
    C ((-1 : ℂ)) * mon 1 3 1 1 +
    C ((-1 : ℂ)) * mon 1 2 3 0 +
    C ((3 : ℂ) * r) * mon 1 1 3 1 +
    C ((6 : ℂ) * Complex.I + (-6 : ℂ)) * mon 1 1 2 2 +
    C ((-6 : ℂ) * Complex.I) * mon 1 0 1 4 +
    C ((-1 : ℂ) * r) * mon 0 5 0 1 +
    C ((2 : ℂ) * r * Complex.I) * mon 0 2 3 1 +
    C ((3 : ℂ) * r * Complex.I + (-3 : ℂ) * r) * mon 0 1 2 3 +
    C ((-6 : ℂ) * Complex.I) * mon 0 1 1 4 +
    C ((-6 : ℂ) * Complex.I) * mon 0 0 3 3 +
    C ((6 : ℂ) * Complex.I + (6 : ℂ)) * mon 0 0 0 6

theorem degreeNineCertificate0 (r : ℂ) (hr : r ^ 3 = 2) :
    (12 : Poly) * mon 0 0 0 9 - C ((1 : ℂ)) * mon 1 8 0 0 =
      relation r 0 * degreeNineWitness0_0 r +
      relation r 1 * degreeNineWitness0_1 r +
      relation r 2 * degreeNineWitness0_2 r +
      relation r 3 * degreeNineWitness0_3 r := by
  have hr' : (C r : Poly) ^ 3 = 2 := by rw [← map_pow, hr, map_ofNat]
  have hi' : (C Complex.I : Poly) ^ 2 = -1 := by
    rw [← map_pow, Complex.I_sq, map_neg, map_one]
  norm_num only [degreeNineWitness0_0, degreeNineWitness0_1,
    degreeNineWitness0_2, degreeNineWitness0_3, relation, b, h, mon,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
    map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_zero, map_one] <;>
    ring_nf <;> (try simp only [hr', hi']) <;> ring

def degreeNineWitness1_0 (r : ℂ) : Poly :=
    C ((-1 : ℂ) * r ^ 2 * Complex.I + (-1 : ℂ) * r ^ 2) * mon 0 7 0 0 +
    C ((2 : ℂ) * Complex.I + (2 : ℂ)) * mon 0 6 0 1 +
    C ((-2 : ℂ) * r ^ 2) * mon 0 5 1 1 +
    C ((1 : ℂ) * r ^ 2 * Complex.I + (-1 : ℂ) * r ^ 2) * mon 0 4 3 0 +
    C ((2 : ℂ) * Complex.I + (2 : ℂ)) * mon 0 4 1 2 +
    C ((-6 : ℂ) * Complex.I + (6 : ℂ)) * mon 0 3 3 1 +
    C ((1 : ℂ) * r ^ 2 * Complex.I + (-1 : ℂ) * r ^ 2) * mon 0 3 2 2 +
    C ((1 : ℂ) * r ^ 2 * Complex.I + (-1 : ℂ) * r ^ 2) * mon 0 2 4 1 +
    C ((6 : ℂ) * Complex.I) * mon 0 2 2 3 +
    C ((-6 : ℂ) * Complex.I + (6 : ℂ)) * mon 0 1 4 2 +
    C ((6 : ℂ) * Complex.I) * mon 0 0 3 4

def degreeNineWitness1_1 (r : ℂ) : Poly :=
    C ((4 : ℂ) * Complex.I) * mon 1 3 1 0 +
    C ((-2 : ℂ) * r ^ 2) * mon 1 3 0 1 +
    C ((1 : ℂ) * r ^ 2 * Complex.I + (-1 : ℂ) * r ^ 2) * mon 1 2 2 0 +
    C ((4 : ℂ)) * mon 1 2 0 2 +
    C ((-3 : ℂ) * r * Complex.I + (3 : ℂ) * r) * mon 1 1 3 0 +
    C ((6 : ℂ) * Complex.I + (6 : ℂ)) * mon 1 1 2 1 +
    C ((2 : ℂ) * r ^ 2 * Complex.I) * mon 1 1 1 2 +
    C ((-2 : ℂ) * Complex.I + (10 : ℂ)) * mon 1 0 4 0 +
    C ((2 : ℂ) * r ^ 2 * Complex.I) * mon 1 0 3 1 +
    C ((-6 : ℂ) * Complex.I + (-6 : ℂ)) * mon 1 0 1 3 +
    C ((2 : ℂ) * r * Complex.I + (2 : ℂ) * r) * mon 0 5 0 0 +
    C ((2 : ℂ) * Complex.I + (-6 : ℂ)) * mon 0 4 1 0 +
    C ((2 : ℂ) * r * Complex.I + (2 : ℂ) * r) * mon 0 3 1 1 +
    C ((4 : ℂ) * Complex.I) * mon 0 3 0 2 +
    C ((-9 : ℂ) * r * Complex.I + (3 : ℂ) * r) * mon 0 2 3 0 +
    C ((2 : ℂ) * Complex.I + (4 : ℂ)) * mon 0 2 2 1 +
    C ((6 : ℂ) * Complex.I + (2 : ℂ)) * mon 0 1 4 0 +
    C ((6 : ℂ) * r * Complex.I) * mon 0 1 2 2 +
    C ((6 : ℂ) * Complex.I + (-6 : ℂ)) * mon 0 1 1 3 +
    C ((-9 : ℂ) * r * Complex.I + (9 : ℂ) * r) * mon 0 0 4 1 +
    C ((6 : ℂ) * Complex.I + (8 : ℂ)) * mon 0 0 3 2

def degreeNineWitness1_2 (r : ℂ) : Poly :=
    C ((2 : ℂ) * r ^ 2 * Complex.I + (-2 : ℂ) * r ^ 2) * mon 1 3 0 1 +
    C ((1 : ℂ) * r ^ 2 * Complex.I + (-1 : ℂ) * r ^ 2) * mon 1 2 2 0 +
    C ((-6 : ℂ) * Complex.I + (6 : ℂ)) * mon 1 1 2 1 +
    C ((-3 : ℂ) * r * Complex.I + (3 : ℂ) * r) * mon 1 1 0 3 +
    C ((6 : ℂ) * Complex.I) * mon 1 0 1 3 +
    C ((4 : ℂ) * Complex.I + (4 : ℂ)) * mon 0 2 2 1 +
    C ((-3 : ℂ) * r * Complex.I + (3 : ℂ) * r) * mon 0 1 2 2 +
    C ((6 : ℂ) * Complex.I) * mon 0 1 1 3 +
    C ((-6 : ℂ) * Complex.I + (-6 : ℂ)) * mon 0 0 0 5

def degreeNineWitness1_3 (r : ℂ) : Poly :=
    C ((1 : ℂ) * r ^ 2 * Complex.I + (1 : ℂ) * r ^ 2) * mon 1 5 0 0 +
    C ((-2 : ℂ) * Complex.I + (-2 : ℂ)) * mon 1 4 0 1 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I + (1 : ℂ) * r ^ 2) * mon 1 3 1 1 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I + (1 : ℂ) * r ^ 2) * mon 1 2 3 0 +
    C ((6 : ℂ) * Complex.I + (-6 : ℂ)) * mon 1 1 3 1 +
    C ((-6 : ℂ) * Complex.I) * mon 1 0 2 3 +
    C ((-2 : ℂ) * Complex.I + (2 : ℂ)) * mon 0 5 0 1 +
    C ((-4 : ℂ) * Complex.I + (-4 : ℂ)) * mon 0 2 3 1 +
    C ((3 : ℂ) * r * Complex.I + (-3 : ℂ) * r) * mon 0 1 3 2 +
    C ((-6 : ℂ) * Complex.I) * mon 0 1 2 3 +
    C ((6 : ℂ) * Complex.I + (6 : ℂ)) * mon 0 0 1 5

theorem degreeNineCertificate1 (r : ℂ) (hr : r ^ 3 = 2) :
    (12 : Poly) * mon 0 0 1 8 - C ((1 : ℂ) * r ^ 2 * Complex.I + (-1 : ℂ) * r ^ 2) * mon 1 8 0 0 =
      relation r 0 * degreeNineWitness1_0 r +
      relation r 1 * degreeNineWitness1_1 r +
      relation r 2 * degreeNineWitness1_2 r +
      relation r 3 * degreeNineWitness1_3 r := by
  have hr' : (C r : Poly) ^ 3 = 2 := by rw [← map_pow, hr, map_ofNat]
  have hi' : (C Complex.I : Poly) ^ 2 = -1 := by
    rw [← map_pow, Complex.I_sq, map_neg, map_one]
  norm_num only [degreeNineWitness1_0, degreeNineWitness1_1,
    degreeNineWitness1_2, degreeNineWitness1_3, relation, b, h, mon,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
    map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_zero, map_one] <;>
    ring_nf <;> (try simp only [hr', hi']) <;> ring

def degreeNineWitness2_0 (r : ℂ) : Poly :=
    C ((1 : ℂ) * Complex.I) * mon 0 2 3 2 +
    C ((1 : ℂ) * Complex.I) * mon 0 0 4 3

def degreeNineWitness2_1 (r : ℂ) : Poly :=
    C ((1 : ℂ) * Complex.I + (1 : ℂ)) * mon 1 1 3 0 +
    C ((-1 : ℂ) * Complex.I + (-1 : ℂ)) * mon 1 0 2 2 +
    C ((1 : ℂ)) * mon 0 2 3 0 +
    C ((1 : ℂ) * r * Complex.I) * mon 0 1 3 1 +
    C ((1 : ℂ) * Complex.I + (-1 : ℂ)) * mon 0 1 2 2 +
    C ((1 : ℂ) * Complex.I) * mon 0 0 4 1

def degreeNineWitness2_2 (r : ℂ) : Poly :=
    C ((2 : ℂ) * Complex.I) * mon 1 1 0 3 +
    C ((1 : ℂ) * Complex.I) * mon 1 0 2 2 +
    C ((1 : ℂ) * Complex.I) * mon 0 1 2 2 +
    C ((1 : ℂ) * r * Complex.I) * mon 0 1 0 4 +
    C ((-1 : ℂ) * Complex.I + (-1 : ℂ)) * mon 0 0 1 4

def degreeNineWitness2_3 (r : ℂ) : Poly :=
    C ((-1 : ℂ) * Complex.I) * mon 1 0 3 2 +
    C ((-1 : ℂ) * Complex.I) * mon 0 1 3 2 +
    C ((1 : ℂ) * Complex.I + (1 : ℂ)) * mon 0 0 2 4

theorem degreeNineCertificate2 (r : ℂ) (hr : r ^ 3 = 2) :
    (2 : Poly) * mon 0 0 2 7 - C ((0 : ℂ)) * mon 1 8 0 0 =
      relation r 0 * degreeNineWitness2_0 r +
      relation r 1 * degreeNineWitness2_1 r +
      relation r 2 * degreeNineWitness2_2 r +
      relation r 3 * degreeNineWitness2_3 r := by
  have hr' : (C r : Poly) ^ 3 = 2 := by rw [← map_pow, hr, map_ofNat]
  have hi' : (C Complex.I : Poly) ^ 2 = -1 := by
    rw [← map_pow, Complex.I_sq, map_neg, map_one]
  norm_num only [degreeNineWitness2_0, degreeNineWitness2_1,
    degreeNineWitness2_2, degreeNineWitness2_3, relation, b, h, mon,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
    map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_zero, map_one] <;>
    ring_nf <;> (try simp only [hr', hi']) <;> ring

def degreeNineWitness3_0 (r : ℂ) : Poly :=
    0

def degreeNineWitness3_1 (r : ℂ) : Poly :=
    C ((-1 : ℂ) * Complex.I + (-1 : ℂ)) * mon 1 0 3 1 +
    C ((1 : ℂ) * Complex.I + (-1 : ℂ)) * mon 0 1 3 1

def degreeNineWitness3_2 (r : ℂ) : Poly :=
    C ((-1 : ℂ) * Complex.I + (-1 : ℂ)) * mon 1 0 0 4 +
    C ((-1 : ℂ) * Complex.I + (-1 : ℂ)) * mon 0 1 0 4 +
    C ((-1 : ℂ) * Complex.I + (-1 : ℂ)) * mon 0 0 2 3

def degreeNineWitness3_3 (r : ℂ) : Poly :=
    C ((1 : ℂ) * Complex.I + (1 : ℂ)) * mon 0 0 3 3

theorem degreeNineCertificate3 (r : ℂ) (hr : r ^ 3 = 2) :
    (2 : Poly) * mon 0 0 3 6 - C ((0 : ℂ)) * mon 1 8 0 0 =
      relation r 0 * degreeNineWitness3_0 r +
      relation r 1 * degreeNineWitness3_1 r +
      relation r 2 * degreeNineWitness3_2 r +
      relation r 3 * degreeNineWitness3_3 r := by
  have hr' : (C r : Poly) ^ 3 = 2 := by rw [← map_pow, hr, map_ofNat]
  have hi' : (C Complex.I : Poly) ^ 2 = -1 := by
    rw [← map_pow, Complex.I_sq, map_neg, map_one]
  norm_num only [degreeNineWitness3_0, degreeNineWitness3_1,
    degreeNineWitness3_2, degreeNineWitness3_3, relation, b, h, mon,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
    map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_zero, map_one] <;>
    ring_nf <;> (try simp only [hr', hi']) <;> ring

def degreeNineWitness4_0 (r : ℂ) : Poly :=
    C ((1 : ℂ) * Complex.I) * mon 0 3 1 3 +
    C ((1 : ℂ) * Complex.I) * mon 0 1 2 4

def degreeNineWitness4_1 (r : ℂ) : Poly :=
    C ((1 : ℂ)) * mon 1 2 1 1 +
    C ((1 : ℂ) * Complex.I) * mon 1 1 3 0 +
    C ((-1 : ℂ) * Complex.I + (-1 : ℂ)) * mon 1 1 0 3 +
    C ((1 : ℂ) * Complex.I) * mon 1 0 2 2 +
    C ((1 : ℂ)) * mon 0 2 3 0 +
    C ((1 : ℂ) * r * Complex.I) * mon 0 2 1 2 +
    C ((1 : ℂ) * Complex.I + (-1 : ℂ)) * mon 0 2 0 3 +
    C ((1 : ℂ) * Complex.I) * mon 0 0 4 1 +
    C ((1 : ℂ) * r * Complex.I) * mon 0 0 2 3 +
    C ((-1 : ℂ) * Complex.I + (-1 : ℂ)) * mon 0 0 1 4

def degreeNineWitness4_2 (r : ℂ) : Poly :=
    C ((2 : ℂ) * Complex.I) * mon 1 1 0 3 +
    C ((1 : ℂ) * Complex.I) * mon 0 1 2 2

def degreeNineWitness4_3 (r : ℂ) : Poly :=
    C ((-1 : ℂ) * Complex.I) * mon 1 1 1 3 +
    C ((-1 : ℂ) * Complex.I) * mon 0 1 3 2 +
    C ((1 : ℂ) * Complex.I + (1 : ℂ)) * mon 0 1 0 5

theorem degreeNineCertificate4 (r : ℂ) (hr : r ^ 3 = 2) :
    (2 : Poly) * mon 0 1 0 8 - C ((0 : ℂ)) * mon 1 8 0 0 =
      relation r 0 * degreeNineWitness4_0 r +
      relation r 1 * degreeNineWitness4_1 r +
      relation r 2 * degreeNineWitness4_2 r +
      relation r 3 * degreeNineWitness4_3 r := by
  have hr' : (C r : Poly) ^ 3 = 2 := by rw [← map_pow, hr, map_ofNat]
  have hi' : (C Complex.I : Poly) ^ 2 = -1 := by
    rw [← map_pow, Complex.I_sq, map_neg, map_one]
  norm_num only [degreeNineWitness4_0, degreeNineWitness4_1,
    degreeNineWitness4_2, degreeNineWitness4_3, relation, b, h, mon,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
    map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_zero, map_one] <;>
    ring_nf <;> (try simp only [hr', hi']) <;> ring

def degreeNineWitness5_0 (r : ℂ) : Poly :=
    C ((1 : ℂ) * Complex.I) * mon 0 3 2 2 +
    C ((1 : ℂ) * Complex.I) * mon 0 1 3 3

def degreeNineWitness5_1 (r : ℂ) : Poly :=
    C ((1 : ℂ)) * mon 1 2 2 0 +
    C ((-1 : ℂ) * Complex.I + (-1 : ℂ)) * mon 1 1 1 2 +
    C ((1 : ℂ) * Complex.I) * mon 1 0 3 1 +
    C ((1 : ℂ) * r * Complex.I) * mon 0 2 2 1 +
    C ((1 : ℂ) * Complex.I + (-1 : ℂ)) * mon 0 2 1 2 +
    C ((1 : ℂ) * r * Complex.I) * mon 0 0 3 2 +
    C ((-1 : ℂ) * Complex.I + (-1 : ℂ)) * mon 0 0 2 3

def degreeNineWitness5_2 (r : ℂ) : Poly :=
    C ((1 : ℂ) * Complex.I) * mon 1 1 1 2 +
    C ((-1 : ℂ) * Complex.I + (-1 : ℂ)) * mon 0 1 0 4

def degreeNineWitness5_3 (r : ℂ) : Poly :=
    C ((-1 : ℂ) * Complex.I) * mon 1 1 2 2 +
    C ((1 : ℂ) * Complex.I + (1 : ℂ)) * mon 0 1 1 4

theorem degreeNineCertificate5 (r : ℂ) (hr : r ^ 3 = 2) :
    (2 : Poly) * mon 0 1 1 7 - C ((0 : ℂ)) * mon 1 8 0 0 =
      relation r 0 * degreeNineWitness5_0 r +
      relation r 1 * degreeNineWitness5_1 r +
      relation r 2 * degreeNineWitness5_2 r +
      relation r 3 * degreeNineWitness5_3 r := by
  have hr' : (C r : Poly) ^ 3 = 2 := by rw [← map_pow, hr, map_ofNat]
  have hi' : (C Complex.I : Poly) ^ 2 = -1 := by
    rw [← map_pow, Complex.I_sq, map_neg, map_one]
  norm_num only [degreeNineWitness5_0, degreeNineWitness5_1,
    degreeNineWitness5_2, degreeNineWitness5_3, relation, b, h, mon,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
    map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_zero, map_one] <;>
    ring_nf <;> (try simp only [hr', hi']) <;> ring

def degreeNineWitness6_0 (r : ℂ) : Poly :=
    C ((1 : ℂ) * r ^ 2) * mon 0 7 0 0 +
    C ((-2 : ℂ)) * mon 0 6 0 1 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I + (1 : ℂ) * r ^ 2) * mon 0 5 1 1 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I) * mon 0 4 3 0 +
    C ((-2 : ℂ)) * mon 0 4 1 2 +
    C ((6 : ℂ) * Complex.I) * mon 0 3 3 1 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I) * mon 0 3 2 2 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I) * mon 0 2 4 1 +
    C ((6 : ℂ) * Complex.I) * mon 0 1 4 2

def degreeNineWitness6_1 (r : ℂ) : Poly :=
    C ((-2 : ℂ) * Complex.I + (-2 : ℂ)) * mon 1 3 1 0 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I + (1 : ℂ) * r ^ 2) * mon 1 3 0 1 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I) * mon 1 2 2 0 +
    C ((2 : ℂ) * Complex.I + (-2 : ℂ)) * mon 1 2 0 2 +
    C ((-6 : ℂ) * Complex.I + (-6 : ℂ)) * mon 1 1 2 1 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I + (-1 : ℂ) * r ^ 2) * mon 1 1 1 2 +
    C ((6 : ℂ) * Complex.I + (-4 : ℂ)) * mon 1 0 4 0 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I + (-1 : ℂ) * r ^ 2) * mon 1 0 3 1 +
    C ((-2 : ℂ) * r) * mon 0 5 0 0 +
    C ((-4 : ℂ) * Complex.I + (2 : ℂ)) * mon 0 4 1 0 +
    C ((-2 : ℂ) * r) * mon 0 3 1 1 +
    C ((-2 : ℂ) * Complex.I + (-2 : ℂ)) * mon 0 3 0 2 +
    C ((6 : ℂ) * r * Complex.I) * mon 0 2 3 0 +
    C ((4 : ℂ) * Complex.I + (-6 : ℂ)) * mon 0 2 2 1 +
    C ((-2 : ℂ) * Complex.I + (-4 : ℂ)) * mon 0 1 4 0 +
    C ((6 : ℂ) * r * Complex.I) * mon 0 0 4 1 +
    C ((-2 : ℂ) * Complex.I + (-10 : ℂ)) * mon 0 0 3 2

def degreeNineWitness6_2 (r : ℂ) : Poly :=
    C ((-2 : ℂ) * r ^ 2 * Complex.I) * mon 1 3 0 1 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I) * mon 1 2 2 0 +
    C ((6 : ℂ) * Complex.I) * mon 1 1 2 1 +
    C ((-4 : ℂ)) * mon 0 2 2 1 +
    C ((-6 : ℂ) * Complex.I + (-6 : ℂ)) * mon 0 1 1 3

def degreeNineWitness6_3 (r : ℂ) : Poly :=
    C ((-1 : ℂ) * r ^ 2) * mon 1 5 0 0 +
    C ((2 : ℂ)) * mon 1 4 0 1 +
    C ((1 : ℂ) * r ^ 2 * Complex.I) * mon 1 3 1 1 +
    C ((1 : ℂ) * r ^ 2 * Complex.I) * mon 1 2 3 0 +
    C ((-6 : ℂ) * Complex.I) * mon 1 1 3 1 +
    C ((2 : ℂ) * Complex.I) * mon 0 5 0 1 +
    C ((4 : ℂ)) * mon 0 2 3 1 +
    C ((6 : ℂ) * Complex.I + (6 : ℂ)) * mon 0 1 2 3

theorem degreeNineCertificate6 (r : ℂ) (hr : r ^ 3 = 2) :
    (12 : Poly) * mon 0 1 2 6 - C ((-1 : ℂ) * r ^ 2 * Complex.I) * mon 1 8 0 0 =
      relation r 0 * degreeNineWitness6_0 r +
      relation r 1 * degreeNineWitness6_1 r +
      relation r 2 * degreeNineWitness6_2 r +
      relation r 3 * degreeNineWitness6_3 r := by
  have hr' : (C r : Poly) ^ 3 = 2 := by rw [← map_pow, hr, map_ofNat]
  have hi' : (C Complex.I : Poly) ^ 2 = -1 := by
    rw [← map_pow, Complex.I_sq, map_neg, map_one]
  norm_num only [degreeNineWitness6_0, degreeNineWitness6_1,
    degreeNineWitness6_2, degreeNineWitness6_3, relation, b, h, mon,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
    map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_zero, map_one] <;>
    ring_nf <;> (try simp only [hr', hi']) <;> ring

def degreeNineWitness7_0 (r : ℂ) : Poly :=
    0

def degreeNineWitness7_1 (r : ℂ) : Poly :=
    C ((-1 : ℂ) * Complex.I + (-1 : ℂ)) * mon 1 1 3 0 +
    C ((1 : ℂ) * Complex.I + (-1 : ℂ)) * mon 0 2 3 0 +
    C ((-1 : ℂ) * Complex.I + (-1 : ℂ)) * mon 0 0 4 1

def degreeNineWitness7_2 (r : ℂ) : Poly :=
    C ((-1 : ℂ) * Complex.I + (-1 : ℂ)) * mon 1 1 0 3 +
    C ((-1 : ℂ) * Complex.I + (-1 : ℂ)) * mon 0 1 2 2

def degreeNineWitness7_3 (r : ℂ) : Poly :=
    C ((1 : ℂ) * Complex.I + (1 : ℂ)) * mon 0 1 3 2

theorem degreeNineCertificate7 (r : ℂ) (hr : r ^ 3 = 2) :
    (2 : Poly) * mon 0 1 3 5 - C ((0 : ℂ)) * mon 1 8 0 0 =
      relation r 0 * degreeNineWitness7_0 r +
      relation r 1 * degreeNineWitness7_1 r +
      relation r 2 * degreeNineWitness7_2 r +
      relation r 3 * degreeNineWitness7_3 r := by
  have hr' : (C r : Poly) ^ 3 = 2 := by rw [← map_pow, hr, map_ofNat]
  have hi' : (C Complex.I : Poly) ^ 2 = -1 := by
    rw [← map_pow, Complex.I_sq, map_neg, map_one]
  norm_num only [degreeNineWitness7_0, degreeNineWitness7_1,
    degreeNineWitness7_2, degreeNineWitness7_3, relation, b, h, mon,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
    map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_zero, map_one] <;>
    ring_nf <;> (try simp only [hr', hi']) <;> ring

def degreeNineWitness8_0 (r : ℂ) : Poly :=
    C ((-1 : ℂ) * r ^ 2 * Complex.I) * mon 0 7 0 0 +
    C ((2 : ℂ) * Complex.I) * mon 0 6 0 1 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I + (-1 : ℂ) * r ^ 2) * mon 0 5 1 1 +
    C ((-1 : ℂ) * r ^ 2) * mon 0 4 3 0 +
    C ((2 : ℂ) * Complex.I) * mon 0 4 1 2 +
    C ((-1 : ℂ) * r ^ 2) * mon 0 3 2 2 +
    C ((-1 : ℂ) * r ^ 2) * mon 0 2 4 1

def degreeNineWitness8_1 (r : ℂ) : Poly :=
    C ((2 : ℂ) * Complex.I + (-2 : ℂ)) * mon 1 3 1 0 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I + (-1 : ℂ) * r ^ 2) * mon 1 3 0 1 +
    C ((-1 : ℂ) * r ^ 2) * mon 1 2 2 0 +
    C ((2 : ℂ) * Complex.I + (2 : ℂ)) * mon 1 2 0 2 +
    C ((1 : ℂ) * r ^ 2 * Complex.I + (-1 : ℂ) * r ^ 2) * mon 1 1 1 2 +
    C ((-2 : ℂ) * Complex.I) * mon 1 0 4 0 +
    C ((1 : ℂ) * r ^ 2 * Complex.I + (-1 : ℂ) * r ^ 2) * mon 1 0 3 1 +
    C ((2 : ℂ) * r * Complex.I) * mon 0 5 0 0 +
    C ((-2 : ℂ) * Complex.I + (-4 : ℂ)) * mon 0 4 1 0 +
    C ((2 : ℂ) * r * Complex.I) * mon 0 3 1 1 +
    C ((2 : ℂ) * Complex.I + (-2 : ℂ)) * mon 0 3 0 2 +
    C ((-2 : ℂ)) * mon 0 2 2 1 +
    C ((-2 : ℂ) * Complex.I + (-2 : ℂ)) * mon 0 1 4 0 +
    C ((-2 : ℂ) * Complex.I + (-2 : ℂ)) * mon 0 0 3 2

def degreeNineWitness8_2 (r : ℂ) : Poly :=
    C ((-2 : ℂ) * r ^ 2) * mon 1 3 0 1 +
    C ((-1 : ℂ) * r ^ 2) * mon 1 2 2 0 +
    C ((-2 : ℂ) * Complex.I) * mon 0 2 2 1

def degreeNineWitness8_3 (r : ℂ) : Poly :=
    C ((1 : ℂ) * r ^ 2 * Complex.I) * mon 1 5 0 0 +
    C ((-2 : ℂ) * Complex.I) * mon 1 4 0 1 +
    C ((1 : ℂ) * r ^ 2) * mon 1 3 1 1 +
    C ((1 : ℂ) * r ^ 2) * mon 1 2 3 0 +
    C ((2 : ℂ)) * mon 0 5 0 1 +
    C ((2 : ℂ) * Complex.I) * mon 0 2 3 1

theorem degreeNineCertificate8 (r : ℂ) (hr : r ^ 3 = 2) :
    (6 : Poly) * mon 0 5 3 1 - C ((-1 : ℂ) * r ^ 2) * mon 1 8 0 0 =
      relation r 0 * degreeNineWitness8_0 r +
      relation r 1 * degreeNineWitness8_1 r +
      relation r 2 * degreeNineWitness8_2 r +
      relation r 3 * degreeNineWitness8_3 r := by
  have hr' : (C r : Poly) ^ 3 = 2 := by rw [← map_pow, hr, map_ofNat]
  have hi' : (C Complex.I : Poly) ^ 2 = -1 := by
    rw [← map_pow, Complex.I_sq, map_neg, map_one]
  norm_num only [degreeNineWitness8_0, degreeNineWitness8_1,
    degreeNineWitness8_2, degreeNineWitness8_3, relation, b, h, mon,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
    map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_zero, map_one] <;>
    ring_nf <;> (try simp only [hr', hi']) <;> ring

def degreeNineWitness9_0 (r : ℂ) : Poly :=
    C ((-1 : ℂ)) * mon 0 4 2 1 +
    C ((-1 : ℂ)) * mon 0 2 3 2

def degreeNineWitness9_1 (r : ℂ) : Poly :=
    C ((-1 : ℂ) * Complex.I + (-1 : ℂ)) * mon 1 1 3 0 +
    C ((1 : ℂ) * Complex.I + (-1 : ℂ)) * mon 1 0 2 2 +
    C ((-1 : ℂ) * r) * mon 0 3 2 0 +
    C ((-1 : ℂ) * Complex.I) * mon 0 2 3 0 +
    C ((-1 : ℂ) * r) * mon 0 1 3 1 +
    C ((-1 : ℂ) * Complex.I + (-1 : ℂ)) * mon 0 1 2 2

def degreeNineWitness9_2 (r : ℂ) : Poly :=
    C ((-1 : ℂ)) * mon 1 2 1 1 +
    C ((-1 : ℂ) * Complex.I) * mon 0 3 1 1

def degreeNineWitness9_3 (r : ℂ) : Poly :=
    C ((1 : ℂ)) * mon 1 2 2 1 +
    C ((1 : ℂ) * Complex.I) * mon 0 3 2 1

theorem degreeNineCertificate9 (r : ℂ) (hr : r ^ 3 = 2) :
    (1 : Poly) * mon 0 6 2 1 - C ((0 : ℂ)) * mon 1 8 0 0 =
      relation r 0 * degreeNineWitness9_0 r +
      relation r 1 * degreeNineWitness9_1 r +
      relation r 2 * degreeNineWitness9_2 r +
      relation r 3 * degreeNineWitness9_3 r := by
  have hr' : (C r : Poly) ^ 3 = 2 := by rw [← map_pow, hr, map_ofNat]
  have hi' : (C Complex.I : Poly) ^ 2 = -1 := by
    rw [← map_pow, Complex.I_sq, map_neg, map_one]
  norm_num only [degreeNineWitness9_0, degreeNineWitness9_1,
    degreeNineWitness9_2, degreeNineWitness9_3, relation, b, h, mon,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
    map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_zero, map_one] <;>
    ring_nf <;> (try simp only [hr', hi']) <;> ring

def degreeNineWitness10_0 (r : ℂ) : Poly :=
    C ((1 : ℂ) * Complex.I) * mon 0 7 0 0 +
    C ((-1 : ℂ) * r * Complex.I) * mon 0 6 0 1 +
    C ((1 : ℂ) * Complex.I + (1 : ℂ)) * mon 0 5 1 1 +
    C ((-2 : ℂ)) * mon 0 4 3 0 +
    C ((-1 : ℂ) * r * Complex.I) * mon 0 4 1 2 +
    C ((1 : ℂ)) * mon 0 3 2 2 +
    C ((-2 : ℂ)) * mon 0 2 4 1

def degreeNineWitness10_1 (r : ℂ) : Poly :=
    C ((-1 : ℂ) * r * Complex.I + (1 : ℂ) * r) * mon 1 3 1 0 +
    C ((1 : ℂ) * Complex.I + (1 : ℂ)) * mon 1 3 0 1 +
    C ((1 : ℂ)) * mon 1 2 2 0 +
    C ((-1 : ℂ) * r * Complex.I + (-1 : ℂ) * r) * mon 1 2 0 2 +
    C ((-1 : ℂ) * Complex.I + (1 : ℂ)) * mon 1 1 1 2 +
    C ((1 : ℂ) * r * Complex.I) * mon 1 0 4 0 +
    C ((2 : ℂ) * Complex.I + (-2 : ℂ)) * mon 1 0 3 1 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I) * mon 0 5 0 0 +
    C ((1 : ℂ) * r * Complex.I + (2 : ℂ) * r) * mon 0 4 1 0 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I) * mon 0 3 1 1 +
    C ((-1 : ℂ) * r * Complex.I + (1 : ℂ) * r) * mon 0 3 0 2 +
    C ((1 : ℂ) * r) * mon 0 2 2 1 +
    C ((1 : ℂ) * r * Complex.I + (-2 : ℂ) * r) * mon 0 1 4 0 +
    C ((-3 : ℂ) * Complex.I + (-3 : ℂ)) * mon 0 1 3 1 +
    C ((1 : ℂ) * r * Complex.I + (1 : ℂ) * r) * mon 0 0 3 2

def degreeNineWitness10_2 (r : ℂ) : Poly :=
    C ((-3 : ℂ) * Complex.I + (-1 : ℂ)) * mon 1 3 0 1 +
    C ((-2 : ℂ)) * mon 1 2 2 0 +
    C ((-3 : ℂ) * Complex.I) * mon 0 4 0 1 +
    C ((-3 : ℂ) * Complex.I) * mon 0 3 2 0 +
    C ((1 : ℂ) * r * Complex.I) * mon 0 2 2 1

def degreeNineWitness10_3 (r : ℂ) : Poly :=
    C ((-1 : ℂ) * Complex.I) * mon 1 5 0 0 +
    C ((1 : ℂ) * r * Complex.I) * mon 1 4 0 1 +
    C ((-1 : ℂ)) * mon 1 3 1 1 +
    C ((2 : ℂ)) * mon 1 2 3 0 +
    C ((-1 : ℂ) * r) * mon 0 5 0 1 +
    C ((3 : ℂ) * Complex.I) * mon 0 3 3 0 +
    C ((-1 : ℂ) * r * Complex.I) * mon 0 2 3 1

theorem degreeNineCertificate10 (r : ℂ) (hr : r ^ 3 = 2) :
    (3 : Poly) * mon 0 6 3 0 - C ((1 : ℂ)) * mon 1 8 0 0 =
      relation r 0 * degreeNineWitness10_0 r +
      relation r 1 * degreeNineWitness10_1 r +
      relation r 2 * degreeNineWitness10_2 r +
      relation r 3 * degreeNineWitness10_3 r := by
  have hr' : (C r : Poly) ^ 3 = 2 := by rw [← map_pow, hr, map_ofNat]
  have hi' : (C Complex.I : Poly) ^ 2 = -1 := by
    rw [← map_pow, Complex.I_sq, map_neg, map_one]
  norm_num only [degreeNineWitness10_0, degreeNineWitness10_1,
    degreeNineWitness10_2, degreeNineWitness10_3, relation, b, h, mon,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
    map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_zero, map_one] <;>
    ring_nf <;> (try simp only [hr', hi']) <;> ring

def degreeNineWitness11_0 (r : ℂ) : Poly :=
    C ((-1 : ℂ)) * mon 0 5 1 1 +
    C ((-1 : ℂ)) * mon 0 3 2 2

def degreeNineWitness11_1 (r : ℂ) : Poly :=
    C ((-1 : ℂ) * Complex.I + (-1 : ℂ)) * mon 1 2 2 0 +
    C ((1 : ℂ) * Complex.I + (-1 : ℂ)) * mon 1 1 1 2 +
    C ((-1 : ℂ) * r) * mon 0 4 1 0 +
    C ((-1 : ℂ) * Complex.I) * mon 0 3 2 0 +
    C ((-1 : ℂ) * r) * mon 0 2 2 1 +
    C ((-1 : ℂ) * Complex.I + (-1 : ℂ)) * mon 0 2 1 2

def degreeNineWitness11_2 (r : ℂ) : Poly :=
    C ((-1 : ℂ)) * mon 1 3 0 1 +
    C ((-1 : ℂ) * Complex.I) * mon 0 4 0 1

def degreeNineWitness11_3 (r : ℂ) : Poly :=
    C ((1 : ℂ)) * mon 1 3 1 1 +
    C ((1 : ℂ) * Complex.I) * mon 0 4 1 1

theorem degreeNineCertificate11 (r : ℂ) (hr : r ^ 3 = 2) :
    (1 : Poly) * mon 0 7 1 1 - C ((0 : ℂ)) * mon 1 8 0 0 =
      relation r 0 * degreeNineWitness11_0 r +
      relation r 1 * degreeNineWitness11_1 r +
      relation r 2 * degreeNineWitness11_2 r +
      relation r 3 * degreeNineWitness11_3 r := by
  have hr' : (C r : Poly) ^ 3 = 2 := by rw [← map_pow, hr, map_ofNat]
  have hi' : (C Complex.I : Poly) ^ 2 = -1 := by
    rw [← map_pow, Complex.I_sq, map_neg, map_one]
  norm_num only [degreeNineWitness11_0, degreeNineWitness11_1,
    degreeNineWitness11_2, degreeNineWitness11_3, relation, b, h, mon,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
    map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_zero, map_one] <;>
    ring_nf <;> (try simp only [hr', hi']) <;> ring

def degreeNineWitness12_0 (r : ℂ) : Poly :=
    C ((-1 : ℂ) * r ^ 2 * Complex.I + (-2 : ℂ) * r ^ 2) * mon 0 7 0 0 +
    C ((2 : ℂ) * Complex.I + (4 : ℂ)) * mon 0 6 0 1 +
    C ((-6 : ℂ)) * mon 0 5 2 0 +
    C ((1 : ℂ) * r ^ 2 * Complex.I + (-3 : ℂ) * r ^ 2) * mon 0 5 1 1 +
    C ((2 : ℂ) * r ^ 2 * Complex.I + (-1 : ℂ) * r ^ 2) * mon 0 4 3 0 +
    C ((6 : ℂ) * r) * mon 0 4 2 1 +
    C ((2 : ℂ) * Complex.I + (4 : ℂ)) * mon 0 4 1 2 +
    C ((-6 : ℂ)) * mon 0 3 3 1 +
    C ((2 : ℂ) * r ^ 2 * Complex.I + (-1 : ℂ) * r ^ 2) * mon 0 3 2 2 +
    C ((2 : ℂ) * r ^ 2 * Complex.I + (-1 : ℂ) * r ^ 2) * mon 0 2 4 1 +
    C ((6 : ℂ) * r) * mon 0 2 3 2

def degreeNineWitness12_1 (r : ℂ) : Poly :=
    C ((6 : ℂ) * Complex.I + (2 : ℂ)) * mon 1 3 1 0 +
    C ((1 : ℂ) * r ^ 2 * Complex.I + (-3 : ℂ) * r ^ 2) * mon 1 3 0 1 +
    C ((2 : ℂ) * r ^ 2 * Complex.I + (-1 : ℂ) * r ^ 2) * mon 1 2 2 0 +
    C ((-2 : ℂ) * Complex.I + (6 : ℂ)) * mon 1 2 0 2 +
    C ((6 : ℂ) * r * Complex.I + (6 : ℂ) * r) * mon 1 1 3 0 +
    C ((6 : ℂ) * Complex.I + (-6 : ℂ)) * mon 1 1 2 1 +
    C ((3 : ℂ) * r ^ 2 * Complex.I + (1 : ℂ) * r ^ 2) * mon 1 1 1 2 +
    C ((4 : ℂ) * Complex.I + (2 : ℂ)) * mon 1 0 4 0 +
    C ((3 : ℂ) * r ^ 2 * Complex.I + (1 : ℂ) * r ^ 2) * mon 1 0 3 1 +
    C ((-6 : ℂ) * r * Complex.I + (6 : ℂ) * r) * mon 1 0 2 2 +
    C ((2 : ℂ) * r * Complex.I + (4 : ℂ) * r) * mon 0 5 0 0 +
    C ((6 : ℂ) * Complex.I + (-8 : ℂ)) * mon 0 4 1 0 +
    C ((6 : ℂ) * r ^ 2) * mon 0 3 2 0 +
    C ((2 : ℂ) * r * Complex.I + (4 : ℂ) * r) * mon 0 3 1 1 +
    C ((6 : ℂ) * Complex.I + (2 : ℂ)) * mon 0 3 0 2 +
    C ((6 : ℂ) * r * Complex.I + (-6 : ℂ) * r) * mon 0 2 3 0 +
    C ((-2 : ℂ) * Complex.I + (-8 : ℂ)) * mon 0 2 2 1 +
    C ((8 : ℂ) * Complex.I) * mon 0 1 4 0 +
    C ((6 : ℂ) * r ^ 2) * mon 0 1 3 1 +
    C ((6 : ℂ) * r * Complex.I + (6 : ℂ) * r) * mon 0 1 2 2 +
    C ((2 : ℂ) * Complex.I + (6 : ℂ)) * mon 0 0 3 2

def degreeNineWitness12_2 (r : ℂ) : Poly :=
    C ((-6 : ℂ)) * mon 1 3 1 0 +
    C ((4 : ℂ) * r ^ 2 * Complex.I + (-2 : ℂ) * r ^ 2) * mon 1 3 0 1 +
    C ((2 : ℂ) * r ^ 2 * Complex.I + (-1 : ℂ) * r ^ 2) * mon 1 2 2 0 +
    C ((6 : ℂ) * r) * mon 1 2 1 1 +
    C ((-6 : ℂ) * Complex.I) * mon 0 4 1 0 +
    C ((6 : ℂ) * r * Complex.I) * mon 0 3 1 1 +
    C ((4 : ℂ) * Complex.I + (2 : ℂ)) * mon 0 2 2 1

def degreeNineWitness12_3 (r : ℂ) : Poly :=
    C ((1 : ℂ) * r ^ 2 * Complex.I + (2 : ℂ) * r ^ 2) * mon 1 5 0 0 +
    C ((-2 : ℂ) * Complex.I + (-4 : ℂ)) * mon 1 4 0 1 +
    C ((6 : ℂ)) * mon 1 3 2 0 +
    C ((-2 : ℂ) * r ^ 2 * Complex.I + (1 : ℂ) * r ^ 2) * mon 1 3 1 1 +
    C ((-2 : ℂ) * r ^ 2 * Complex.I + (1 : ℂ) * r ^ 2) * mon 1 2 3 0 +
    C ((-6 : ℂ) * r) * mon 1 2 2 1 +
    C ((-4 : ℂ) * Complex.I + (2 : ℂ)) * mon 0 5 0 1 +
    C ((6 : ℂ) * Complex.I) * mon 0 4 2 0 +
    C ((-6 : ℂ) * r * Complex.I) * mon 0 3 2 1 +
    C ((-4 : ℂ) * Complex.I + (-2 : ℂ)) * mon 0 2 3 1

theorem degreeNineCertificate12 (r : ℂ) (hr : r ^ 3 = 2) :
    (6 : Poly) * mon 0 7 2 0 - C ((2 : ℂ) * r ^ 2 * Complex.I + (-1 : ℂ) * r ^ 2) * mon 1 8 0 0 =
      relation r 0 * degreeNineWitness12_0 r +
      relation r 1 * degreeNineWitness12_1 r +
      relation r 2 * degreeNineWitness12_2 r +
      relation r 3 * degreeNineWitness12_3 r := by
  have hr' : (C r : Poly) ^ 3 = 2 := by rw [← map_pow, hr, map_ofNat]
  have hi' : (C Complex.I : Poly) ^ 2 = -1 := by
    rw [← map_pow, Complex.I_sq, map_neg, map_one]
  norm_num only [degreeNineWitness12_0, degreeNineWitness12_1,
    degreeNineWitness12_2, degreeNineWitness12_3, relation, b, h, mon,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
    map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_zero, map_one] <;>
    ring_nf <;> (try simp only [hr', hi']) <;> ring

def degreeNineWitness13_0 (r : ℂ) : Poly :=
    C ((-1 : ℂ) * r ^ 2) * mon 0 7 0 0 +
    C ((-1 : ℂ)) * mon 0 6 0 1 +
    C ((1 : ℂ) * r ^ 2 * Complex.I + (-1 : ℂ) * r ^ 2) * mon 0 5 1 1 +
    C ((1 : ℂ) * r ^ 2 * Complex.I) * mon 0 4 3 0 +
    C ((-1 : ℂ)) * mon 0 4 1 2 +
    C ((1 : ℂ) * r ^ 2 * Complex.I) * mon 0 3 2 2 +
    C ((1 : ℂ) * r ^ 2 * Complex.I) * mon 0 2 4 1

def degreeNineWitness13_1 (r : ℂ) : Poly :=
    C ((-1 : ℂ) * Complex.I + (-1 : ℂ)) * mon 1 3 1 0 +
    C ((1 : ℂ) * r ^ 2 * Complex.I + (-1 : ℂ) * r ^ 2) * mon 1 3 0 1 +
    C ((1 : ℂ) * r ^ 2 * Complex.I) * mon 1 2 2 0 +
    C ((1 : ℂ) * Complex.I + (-1 : ℂ)) * mon 1 2 0 2 +
    C ((1 : ℂ) * r ^ 2 * Complex.I + (1 : ℂ) * r ^ 2) * mon 1 1 1 2 +
    C ((1 : ℂ)) * mon 1 0 4 0 +
    C ((1 : ℂ) * r ^ 2 * Complex.I + (1 : ℂ) * r ^ 2) * mon 1 0 3 1 +
    C ((-1 : ℂ) * r) * mon 0 5 0 0 +
    C ((1 : ℂ) * Complex.I + (-2 : ℂ)) * mon 0 4 1 0 +
    C ((-1 : ℂ) * r) * mon 0 3 1 1 +
    C ((-1 : ℂ) * Complex.I + (-1 : ℂ)) * mon 0 3 0 2 +
    C ((2 : ℂ) * Complex.I) * mon 0 2 2 1 +
    C ((2 : ℂ) * Complex.I + (1 : ℂ)) * mon 0 1 4 0 +
    C ((-1 : ℂ) * Complex.I + (1 : ℂ)) * mon 0 0 3 2

def degreeNineWitness13_2 (r : ℂ) : Poly :=
    C ((2 : ℂ) * r ^ 2 * Complex.I) * mon 1 3 0 1 +
    C ((1 : ℂ) * r ^ 2 * Complex.I) * mon 1 2 2 0 +
    C ((1 : ℂ)) * mon 0 2 2 1

def degreeNineWitness13_3 (r : ℂ) : Poly :=
    C ((1 : ℂ) * r ^ 2) * mon 1 5 0 0 +
    C ((1 : ℂ)) * mon 1 4 0 1 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I) * mon 1 3 1 1 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I) * mon 1 2 3 0 +
    C ((1 : ℂ) * Complex.I) * mon 0 5 0 1 +
    C ((-1 : ℂ)) * mon 0 2 3 1

theorem degreeNineCertificate13 (r : ℂ) (hr : r ^ 3 = 2) :
    (3 : Poly) * mon 0 8 0 1 - C ((1 : ℂ) * r ^ 2 * Complex.I) * mon 1 8 0 0 =
      relation r 0 * degreeNineWitness13_0 r +
      relation r 1 * degreeNineWitness13_1 r +
      relation r 2 * degreeNineWitness13_2 r +
      relation r 3 * degreeNineWitness13_3 r := by
  have hr' : (C r : Poly) ^ 3 = 2 := by rw [← map_pow, hr, map_ofNat]
  have hi' : (C Complex.I : Poly) ^ 2 = -1 := by
    rw [← map_pow, Complex.I_sq, map_neg, map_one]
  norm_num only [degreeNineWitness13_0, degreeNineWitness13_1,
    degreeNineWitness13_2, degreeNineWitness13_3, relation, b, h, mon,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
    map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_zero, map_one] <;>
    ring_nf <;> (try simp only [hr', hi']) <;> ring

def degreeNineWitness14_0 (r : ℂ) : Poly :=
    C ((-1 : ℂ)) * mon 0 6 1 0 +
    C ((1 : ℂ) * r) * mon 0 5 1 1 +
    C ((2 : ℂ) * Complex.I + (-2 : ℂ)) * mon 0 4 2 1 +
    C ((1 : ℂ) * r) * mon 0 3 2 2 +
    C ((2 : ℂ) * Complex.I + (-1 : ℂ)) * mon 0 2 3 2

def degreeNineWitness14_1 (r : ℂ) : Poly :=
    C ((1 : ℂ) * r * Complex.I + (1 : ℂ) * r) * mon 1 2 2 0 +
    C ((1 : ℂ) * Complex.I + (-1 : ℂ)) * mon 1 2 1 1 +
    C ((2 : ℂ) * Complex.I + (-2 : ℂ)) * mon 1 1 3 0 +
    C ((-1 : ℂ) * r * Complex.I + (1 : ℂ) * r) * mon 1 1 1 2 +
    C ((3 : ℂ) * Complex.I + (1 : ℂ)) * mon 1 0 2 2 +
    C ((1 : ℂ) * r ^ 2) * mon 0 4 1 0 +
    C ((3 : ℂ) * r * Complex.I + (-2 : ℂ) * r) * mon 0 3 2 0 +
    C ((-1 : ℂ) * Complex.I + (-1 : ℂ)) * mon 0 3 1 1 +
    C ((-1 : ℂ)) * mon 0 2 3 0 +
    C ((1 : ℂ) * r ^ 2) * mon 0 2 2 1 +
    C ((1 : ℂ) * r * Complex.I + (1 : ℂ) * r) * mon 0 2 1 2 +
    C ((2 : ℂ) * r * Complex.I + (-1 : ℂ) * r) * mon 0 1 3 1 +
    C ((1 : ℂ) * Complex.I + (-1 : ℂ)) * mon 0 1 2 2

def degreeNineWitness14_2 (r : ℂ) : Poly :=
    C ((-1 : ℂ)) * mon 1 4 0 0 +
    C ((1 : ℂ) * r) * mon 1 3 0 1 +
    C ((2 : ℂ) * Complex.I + (-1 : ℂ)) * mon 1 2 1 1 +
    C ((-1 : ℂ) * Complex.I) * mon 0 5 0 0 +
    C ((1 : ℂ) * r * Complex.I) * mon 0 4 0 1 +
    C ((-1 : ℂ)) * mon 0 3 1 1

def degreeNineWitness14_3 (r : ℂ) : Poly :=
    C ((1 : ℂ)) * mon 1 4 1 0 +
    C ((-1 : ℂ) * r) * mon 1 3 1 1 +
    C ((-2 : ℂ) * Complex.I + (1 : ℂ)) * mon 1 2 2 1 +
    C ((1 : ℂ) * Complex.I) * mon 0 5 1 0 +
    C ((-1 : ℂ) * r * Complex.I) * mon 0 4 1 1 +
    C ((1 : ℂ)) * mon 0 3 2 1

theorem degreeNineCertificate14 (r : ℂ) (hr : r ^ 3 = 2) :
    (1 : Poly) * mon 0 8 1 0 - C ((0 : ℂ)) * mon 1 8 0 0 =
      relation r 0 * degreeNineWitness14_0 r +
      relation r 1 * degreeNineWitness14_1 r +
      relation r 2 * degreeNineWitness14_2 r +
      relation r 3 * degreeNineWitness14_3 r := by
  have hr' : (C r : Poly) ^ 3 = 2 := by rw [← map_pow, hr, map_ofNat]
  have hi' : (C Complex.I : Poly) ^ 2 = -1 := by
    rw [← map_pow, Complex.I_sq, map_neg, map_one]
  norm_num only [degreeNineWitness14_0, degreeNineWitness14_1,
    degreeNineWitness14_2, degreeNineWitness14_3, relation, b, h, mon,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
    map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_zero, map_one] <;>
    ring_nf <;> (try simp only [hr', hi']) <;> ring

def degreeNineWitness15_0 (r : ℂ) : Poly :=
    C ((1 : ℂ)) * mon 0 7 0 0 +
    C ((-1 : ℂ) * r) * mon 0 6 0 1 +
    C ((2 : ℂ) * Complex.I + (-2 : ℂ)) * mon 0 5 1 1 +
    C ((2 : ℂ) * Complex.I) * mon 0 4 3 0 +
    C ((-1 : ℂ) * r) * mon 0 4 1 2 +
    C ((2 : ℂ) * Complex.I + (-3 : ℂ)) * mon 0 3 2 2 +
    C ((2 : ℂ) * Complex.I) * mon 0 2 4 1

def degreeNineWitness15_1 (r : ℂ) : Poly :=
    C ((-1 : ℂ) * r * Complex.I + (-1 : ℂ) * r) * mon 1 3 1 0 +
    C ((-1 : ℂ) * Complex.I + (1 : ℂ)) * mon 1 3 0 1 +
    C ((2 : ℂ) * Complex.I + (-6 : ℂ)) * mon 1 2 2 0 +
    C ((1 : ℂ) * r * Complex.I + (-1 : ℂ) * r) * mon 1 2 0 2 +
    C ((5 : ℂ) * Complex.I + (-1 : ℂ)) * mon 1 1 1 2 +
    C ((1 : ℂ) * r) * mon 1 0 4 0 +
    C ((2 : ℂ) * Complex.I + (2 : ℂ)) * mon 1 0 3 1 +
    C ((-1 : ℂ) * r ^ 2) * mon 0 5 0 0 +
    C ((1 : ℂ) * r * Complex.I + (-2 : ℂ) * r) * mon 0 4 1 0 +
    C ((-3 : ℂ) * Complex.I + (-3 : ℂ)) * mon 0 4 0 1 +
    C ((-3 : ℂ)) * mon 0 3 2 0 +
    C ((-1 : ℂ) * r ^ 2) * mon 0 3 1 1 +
    C ((-1 : ℂ) * r * Complex.I + (-1 : ℂ) * r) * mon 0 3 0 2 +
    C ((2 : ℂ) * r * Complex.I + (-3 : ℂ) * r) * mon 0 2 2 1 +
    C ((3 : ℂ) * Complex.I + (-3 : ℂ)) * mon 0 2 1 2 +
    C ((2 : ℂ) * r * Complex.I + (1 : ℂ) * r) * mon 0 1 4 0 +
    C ((3 : ℂ) * Complex.I + (-3 : ℂ)) * mon 0 1 3 1 +
    C ((-1 : ℂ) * r * Complex.I + (1 : ℂ) * r) * mon 0 0 3 2

def degreeNineWitness15_2 (r : ℂ) : Poly :=
    C ((4 : ℂ) * Complex.I + (-6 : ℂ)) * mon 1 3 0 1 +
    C ((2 : ℂ) * Complex.I) * mon 1 2 2 0 +
    C ((-6 : ℂ)) * mon 0 4 0 1 +
    C ((-3 : ℂ)) * mon 0 3 2 0 +
    C ((1 : ℂ) * r) * mon 0 2 2 1

def degreeNineWitness15_3 (r : ℂ) : Poly :=
    C ((-1 : ℂ)) * mon 1 5 0 0 +
    C ((1 : ℂ) * r) * mon 1 4 0 1 +
    C ((-2 : ℂ) * Complex.I + (3 : ℂ)) * mon 1 3 1 1 +
    C ((-2 : ℂ) * Complex.I) * mon 1 2 3 0 +
    C ((3 : ℂ) * Complex.I) * mon 0 6 0 0 +
    C ((1 : ℂ) * r * Complex.I) * mon 0 5 0 1 +
    C ((3 : ℂ)) * mon 0 4 1 1 +
    C ((3 : ℂ)) * mon 0 3 3 0 +
    C ((-1 : ℂ) * r) * mon 0 2 3 1

theorem degreeNineCertificate15 (r : ℂ) (hr : r ^ 3 = 2) :
    (3 : Poly) * mon 0 9 0 0 - C ((-4 : ℂ) * Complex.I) * mon 1 8 0 0 =
      relation r 0 * degreeNineWitness15_0 r +
      relation r 1 * degreeNineWitness15_1 r +
      relation r 2 * degreeNineWitness15_2 r +
      relation r 3 * degreeNineWitness15_3 r := by
  have hr' : (C r : Poly) ^ 3 = 2 := by rw [← map_pow, hr, map_ofNat]
  have hi' : (C Complex.I : Poly) ^ 2 = -1 := by
    rw [← map_pow, Complex.I_sq, map_neg, map_one]
  norm_num only [degreeNineWitness15_0, degreeNineWitness15_1,
    degreeNineWitness15_2, degreeNineWitness15_3, relation, b, h, mon,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
    map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_zero, map_one] <;>
    ring_nf <;> (try simp only [hr', hi']) <;> ring

def degreeNineWitness16_0 (r : ℂ) : Poly :=
    C ((-1 : ℂ) * r * Complex.I + (1 : ℂ) * r) * mon 0 3 2 2 +
    C ((2 : ℂ) * Complex.I) * mon 0 3 1 3 +
    C ((2 : ℂ) * Complex.I) * mon 0 2 3 2 +
    C ((-2 : ℂ) * Complex.I + (-2 : ℂ)) * mon 0 2 0 5 +
    C ((-1 : ℂ) * r * Complex.I + (1 : ℂ) * r) * mon 0 1 3 3 +
    C ((2 : ℂ) * Complex.I) * mon 0 1 2 4 +
    C ((2 : ℂ) * Complex.I) * mon 0 0 4 3 +
    C ((-2 : ℂ) * Complex.I + (-2 : ℂ)) * mon 0 0 1 6

def degreeNineWitness16_1 (r : ℂ) : Poly :=
    C ((-1 : ℂ) * r * Complex.I + (-1 : ℂ) * r) * mon 1 2 2 0 +
    C ((2 : ℂ)) * mon 1 2 1 1 +
    C ((2 : ℂ)) * mon 1 1 3 0 +
    C ((2 : ℂ) * r * Complex.I) * mon 1 1 1 2 +
    C ((2 : ℂ) * Complex.I + (-2 : ℂ)) * mon 1 1 0 3 +
    C ((-1 : ℂ) * r * Complex.I + (1 : ℂ) * r) * mon 1 0 3 1 +
    C ((2 : ℂ) * Complex.I) * mon 1 0 2 2 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I + (1 : ℂ) * r ^ 2) * mon 0 2 2 1 +
    C ((2 : ℂ) * r * Complex.I + (2 : ℂ) * r) * mon 0 2 1 2 +
    C ((2 : ℂ) * r * Complex.I) * mon 0 1 3 1 +
    C ((-2 : ℂ) * r * Complex.I + (-2 : ℂ) * r) * mon 0 1 0 4 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I + (1 : ℂ) * r ^ 2) * mon 0 0 3 2 +
    C ((4 : ℂ) * r * Complex.I) * mon 0 0 2 3

def degreeNineWitness16_2 (r : ℂ) : Poly :=
    C ((-1 : ℂ) * r * Complex.I + (1 : ℂ) * r) * mon 1 1 1 2 +
    C ((4 : ℂ) * Complex.I) * mon 1 1 0 3 +
    C ((2 : ℂ) * Complex.I) * mon 1 0 2 2 +
    C ((4 : ℂ) * r * Complex.I) * mon 0 1 0 4

def degreeNineWitness16_3 (r : ℂ) : Poly :=
    C ((1 : ℂ) * r * Complex.I + (-1 : ℂ) * r) * mon 1 1 2 2 +
    C ((-2 : ℂ) * Complex.I) * mon 1 1 1 3 +
    C ((-2 : ℂ) * Complex.I) * mon 1 0 3 2 +
    C ((2 : ℂ) * Complex.I + (2 : ℂ)) * mon 1 0 0 5 +
    C ((-2 : ℂ) * r * Complex.I) * mon 0 1 1 4

theorem degreeNineCertificate16 (r : ℂ) (hr : r ^ 3 = 2) :
    (4 : Poly) * mon 1 0 0 8 - C ((0 : ℂ)) * mon 1 8 0 0 =
      relation r 0 * degreeNineWitness16_0 r +
      relation r 1 * degreeNineWitness16_1 r +
      relation r 2 * degreeNineWitness16_2 r +
      relation r 3 * degreeNineWitness16_3 r := by
  have hr' : (C r : Poly) ^ 3 = 2 := by rw [← map_pow, hr, map_ofNat]
  have hi' : (C Complex.I : Poly) ^ 2 = -1 := by
    rw [← map_pow, Complex.I_sq, map_neg, map_one]
  norm_num only [degreeNineWitness16_0, degreeNineWitness16_1,
    degreeNineWitness16_2, degreeNineWitness16_3, relation, b, h, mon,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
    map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_zero, map_one] <;>
    ring_nf <;> (try simp only [hr', hi']) <;> ring

def degreeNineWitness17_0 (r : ℂ) : Poly :=
    C ((-1 : ℂ) * Complex.I + (-1 : ℂ)) * mon 0 7 0 0 +
    C ((1 : ℂ) * r * Complex.I + (1 : ℂ) * r) * mon 0 6 0 1 +
    C ((-2 : ℂ)) * mon 0 5 1 1 +
    C ((1 : ℂ) * Complex.I + (-1 : ℂ)) * mon 0 4 3 0 +
    C ((1 : ℂ) * r * Complex.I + (1 : ℂ) * r) * mon 0 4 1 2 +
    C ((-3 : ℂ) * r * Complex.I + (3 : ℂ) * r) * mon 0 3 3 1 +
    C ((7 : ℂ) * Complex.I + (-1 : ℂ)) * mon 0 3 2 2 +
    C ((1 : ℂ) * Complex.I + (-1 : ℂ)) * mon 0 2 4 1 +
    C ((-6 : ℂ) * Complex.I + (-6 : ℂ)) * mon 0 2 1 4 +
    C ((-3 : ℂ) * r * Complex.I + (3 : ℂ) * r) * mon 0 1 4 2 +
    C ((6 : ℂ) * Complex.I) * mon 0 1 3 3 +
    C ((-6 : ℂ) * Complex.I + (-6 : ℂ)) * mon 0 0 2 5

def degreeNineWitness17_1 (r : ℂ) : Poly :=
    C ((2 : ℂ) * r * Complex.I) * mon 1 3 1 0 +
    C ((-2 : ℂ)) * mon 1 3 0 1 +
    C ((1 : ℂ) * Complex.I + (5 : ℂ)) * mon 1 2 2 0 +
    C ((2 : ℂ) * r) * mon 1 2 0 2 +
    C ((6 : ℂ) * r * Complex.I) * mon 1 1 2 1 +
    C ((8 : ℂ) * Complex.I + (-6 : ℂ)) * mon 1 1 1 2 +
    C ((-1 : ℂ) * r * Complex.I + (5 : ℂ) * r) * mon 1 0 4 0 +
    C ((8 : ℂ) * Complex.I) * mon 1 0 3 1 +
    C ((1 : ℂ) * r ^ 2 * Complex.I + (1 : ℂ) * r ^ 2) * mon 0 5 0 0 +
    C ((1 : ℂ) * r * Complex.I + (-3 : ℂ) * r) * mon 0 4 1 0 +
    C ((1 : ℂ) * r ^ 2 * Complex.I + (1 : ℂ) * r ^ 2) * mon 0 3 1 1 +
    C ((2 : ℂ) * r * Complex.I) * mon 0 3 0 2 +
    C ((-3 : ℂ) * r ^ 2 * Complex.I + (3 : ℂ) * r ^ 2) * mon 0 2 3 0 +
    C ((7 : ℂ) * r * Complex.I + (5 : ℂ) * r) * mon 0 2 2 1 +
    C ((3 : ℂ) * r * Complex.I + (1 : ℂ) * r) * mon 0 1 4 0 +
    C ((-6 : ℂ) * r * Complex.I + (-6 : ℂ) * r) * mon 0 1 1 3 +
    C ((-3 : ℂ) * r ^ 2 * Complex.I + (3 : ℂ) * r ^ 2) * mon 0 0 4 1 +
    C ((12 : ℂ) * r * Complex.I + (4 : ℂ) * r) * mon 0 0 3 2

def degreeNineWitness17_2 (r : ℂ) : Poly :=
    C ((2 : ℂ) * Complex.I + (-2 : ℂ)) * mon 1 3 0 1 +
    C ((1 : ℂ) * Complex.I + (-1 : ℂ)) * mon 1 2 2 0 +
    C ((-3 : ℂ) * r * Complex.I + (3 : ℂ) * r) * mon 1 1 2 1 +
    C ((6 : ℂ) * Complex.I) * mon 1 1 1 2 +
    C ((-6 : ℂ) * Complex.I + (-6 : ℂ)) * mon 1 0 0 4 +
    C ((2 : ℂ) * r * Complex.I + (2 : ℂ) * r) * mon 0 2 2 1 +
    C ((6 : ℂ) * r * Complex.I) * mon 0 1 1 3

def degreeNineWitness17_3 (r : ℂ) : Poly :=
    C ((1 : ℂ) * Complex.I + (1 : ℂ)) * mon 1 5 0 0 +
    C ((-1 : ℂ) * r * Complex.I + (-1 : ℂ) * r) * mon 1 4 0 1 +
    C ((-1 : ℂ) * Complex.I + (1 : ℂ)) * mon 1 3 1 1 +
    C ((-1 : ℂ) * Complex.I + (1 : ℂ)) * mon 1 2 3 0 +
    C ((3 : ℂ) * r * Complex.I + (-3 : ℂ) * r) * mon 1 1 3 1 +
    C ((-6 : ℂ) * Complex.I) * mon 1 1 2 2 +
    C ((6 : ℂ) * Complex.I + (6 : ℂ)) * mon 1 0 1 4 +
    C ((-1 : ℂ) * r * Complex.I + (1 : ℂ) * r) * mon 0 5 0 1 +
    C ((-2 : ℂ) * r * Complex.I + (-2 : ℂ) * r) * mon 0 2 3 1 +
    C ((-6 : ℂ) * r * Complex.I) * mon 0 1 2 3

theorem degreeNineCertificate17 (r : ℂ) (hr : r ^ 3 = 2) :
    (12 : Poly) * mon 1 0 1 7 - C ((1 : ℂ) * Complex.I + (-1 : ℂ)) * mon 1 8 0 0 =
      relation r 0 * degreeNineWitness17_0 r +
      relation r 1 * degreeNineWitness17_1 r +
      relation r 2 * degreeNineWitness17_2 r +
      relation r 3 * degreeNineWitness17_3 r := by
  have hr' : (C r : Poly) ^ 3 = 2 := by rw [← map_pow, hr, map_ofNat]
  have hi' : (C Complex.I : Poly) ^ 2 = -1 := by
    rw [← map_pow, Complex.I_sq, map_neg, map_one]
  norm_num only [degreeNineWitness17_0, degreeNineWitness17_1,
    degreeNineWitness17_2, degreeNineWitness17_3, relation, b, h, mon,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
    map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_zero, map_one] <;>
    ring_nf <;> (try simp only [hr', hi']) <;> ring

def degreeNineWitness18_0 (r : ℂ) : Poly :=
    C ((1 : ℂ) * r ^ 2) * mon 0 7 0 0 +
    C ((-2 : ℂ)) * mon 0 6 0 1 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I + (1 : ℂ) * r ^ 2) * mon 0 5 1 1 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I) * mon 0 4 3 0 +
    C ((-2 : ℂ)) * mon 0 4 1 2 +
    C ((6 : ℂ) * Complex.I) * mon 0 3 3 1 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I) * mon 0 3 2 2 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I) * mon 0 2 4 1 +
    C ((-6 : ℂ) * Complex.I + (-6 : ℂ)) * mon 0 2 2 3 +
    C ((6 : ℂ) * Complex.I) * mon 0 1 4 2 +
    C ((-6 : ℂ) * Complex.I + (-6 : ℂ)) * mon 0 0 3 4

def degreeNineWitness18_1 (r : ℂ) : Poly :=
    C ((-2 : ℂ) * Complex.I + (-2 : ℂ)) * mon 1 3 1 0 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I + (1 : ℂ) * r ^ 2) * mon 1 3 0 1 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I) * mon 1 2 2 0 +
    C ((2 : ℂ) * Complex.I + (-2 : ℂ)) * mon 1 2 0 2 +
    C ((6 : ℂ) * r * Complex.I) * mon 1 1 3 0 +
    C ((6 : ℂ) * Complex.I + (-6 : ℂ)) * mon 1 1 2 1 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I + (-1 : ℂ) * r ^ 2) * mon 1 1 1 2 +
    C ((6 : ℂ) * Complex.I + (-4 : ℂ)) * mon 1 0 4 0 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I + (-1 : ℂ) * r ^ 2) * mon 1 0 3 1 +
    C ((-2 : ℂ) * r) * mon 0 5 0 0 +
    C ((-4 : ℂ) * Complex.I + (2 : ℂ)) * mon 0 4 1 0 +
    C ((-2 : ℂ) * r) * mon 0 3 1 1 +
    C ((-2 : ℂ) * Complex.I + (-2 : ℂ)) * mon 0 3 0 2 +
    C ((6 : ℂ) * r * Complex.I + (6 : ℂ) * r) * mon 0 2 3 0 +
    C ((-2 : ℂ) * Complex.I) * mon 0 2 2 1 +
    C ((-2 : ℂ) * Complex.I + (-4 : ℂ)) * mon 0 1 4 0 +
    C ((-6 : ℂ) * r * Complex.I + (-6 : ℂ) * r) * mon 0 1 2 2 +
    C ((12 : ℂ) * r * Complex.I) * mon 0 0 4 1 +
    C ((4 : ℂ) * Complex.I + (-4 : ℂ)) * mon 0 0 3 2

def degreeNineWitness18_2 (r : ℂ) : Poly :=
    C ((-2 : ℂ) * r ^ 2 * Complex.I) * mon 1 3 0 1 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I) * mon 1 2 2 0 +
    C ((6 : ℂ) * Complex.I) * mon 1 1 2 1 +
    C ((6 : ℂ) * r * Complex.I) * mon 1 1 0 3 +
    C ((-6 : ℂ) * Complex.I + (-6 : ℂ)) * mon 1 0 1 3 +
    C ((-4 : ℂ)) * mon 0 2 2 1 +
    C ((6 : ℂ) * r * Complex.I) * mon 0 1 2 2

def degreeNineWitness18_3 (r : ℂ) : Poly :=
    C ((-1 : ℂ) * r ^ 2) * mon 1 5 0 0 +
    C ((2 : ℂ)) * mon 1 4 0 1 +
    C ((1 : ℂ) * r ^ 2 * Complex.I) * mon 1 3 1 1 +
    C ((1 : ℂ) * r ^ 2 * Complex.I) * mon 1 2 3 0 +
    C ((-6 : ℂ) * Complex.I) * mon 1 1 3 1 +
    C ((6 : ℂ) * Complex.I + (6 : ℂ)) * mon 1 0 2 3 +
    C ((2 : ℂ) * Complex.I) * mon 0 5 0 1 +
    C ((4 : ℂ)) * mon 0 2 3 1 +
    C ((-6 : ℂ) * r * Complex.I) * mon 0 1 3 2

theorem degreeNineCertificate18 (r : ℂ) (hr : r ^ 3 = 2) :
    (12 : Poly) * mon 1 0 2 6 - C ((-1 : ℂ) * r ^ 2 * Complex.I) * mon 1 8 0 0 =
      relation r 0 * degreeNineWitness18_0 r +
      relation r 1 * degreeNineWitness18_1 r +
      relation r 2 * degreeNineWitness18_2 r +
      relation r 3 * degreeNineWitness18_3 r := by
  have hr' : (C r : Poly) ^ 3 = 2 := by rw [← map_pow, hr, map_ofNat]
  have hi' : (C Complex.I : Poly) ^ 2 = -1 := by
    rw [← map_pow, Complex.I_sq, map_neg, map_one]
  norm_num only [degreeNineWitness18_0, degreeNineWitness18_1,
    degreeNineWitness18_2, degreeNineWitness18_3, relation, b, h, mon,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
    map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_zero, map_one] <;>
    ring_nf <;> (try simp only [hr', hi']) <;> ring

def degreeNineWitness19_0 (r : ℂ) : Poly :=
    C ((-1 : ℂ) * Complex.I + (-1 : ℂ)) * mon 0 2 3 2 +
    C ((-1 : ℂ) * Complex.I + (-1 : ℂ)) * mon 0 0 4 3

def degreeNineWitness19_1 (r : ℂ) : Poly :=
    C ((1 : ℂ) * Complex.I + (-1 : ℂ)) * mon 1 1 3 0 +
    C ((-1 : ℂ) * r * Complex.I + (-1 : ℂ) * r) * mon 0 1 3 1

def degreeNineWitness19_2 (r : ℂ) : Poly :=
    C ((-1 : ℂ) * Complex.I + (-1 : ℂ)) * mon 1 1 0 3 +
    C ((-1 : ℂ) * Complex.I + (-1 : ℂ)) * mon 1 0 2 2 +
    C ((-1 : ℂ) * r * Complex.I + (-1 : ℂ) * r) * mon 0 1 0 4

def degreeNineWitness19_3 (r : ℂ) : Poly :=
    C ((1 : ℂ) * Complex.I + (1 : ℂ)) * mon 1 0 3 2

theorem degreeNineCertificate19 (r : ℂ) (hr : r ^ 3 = 2) :
    (2 : Poly) * mon 1 0 3 5 - C ((0 : ℂ)) * mon 1 8 0 0 =
      relation r 0 * degreeNineWitness19_0 r +
      relation r 1 * degreeNineWitness19_1 r +
      relation r 2 * degreeNineWitness19_2 r +
      relation r 3 * degreeNineWitness19_3 r := by
  have hr' : (C r : Poly) ^ 3 = 2 := by rw [← map_pow, hr, map_ofNat]
  have hi' : (C Complex.I : Poly) ^ 2 = -1 := by
    rw [← map_pow, Complex.I_sq, map_neg, map_one]
  norm_num only [degreeNineWitness19_0, degreeNineWitness19_1,
    degreeNineWitness19_2, degreeNineWitness19_3, relation, b, h, mon,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
    map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_zero, map_one] <;>
    ring_nf <;> (try simp only [hr', hi']) <;> ring

def degreeNineWitness20_0 (r : ℂ) : Poly :=
    C ((1 : ℂ) * r ^ 2) * mon 0 7 0 0 +
    C ((-2 : ℂ)) * mon 0 6 0 1 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I + (1 : ℂ) * r ^ 2) * mon 0 5 1 1 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I) * mon 0 4 3 0 +
    C ((-2 : ℂ)) * mon 0 4 1 2 +
    C ((6 : ℂ) * Complex.I) * mon 0 3 3 1 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I) * mon 0 3 2 2 +
    C ((-6 : ℂ) * Complex.I + (-6 : ℂ)) * mon 0 3 0 4 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I) * mon 0 2 4 1 +
    C ((6 : ℂ) * Complex.I) * mon 0 1 4 2 +
    C ((-6 : ℂ) * Complex.I + (-6 : ℂ)) * mon 0 1 1 5

def degreeNineWitness20_1 (r : ℂ) : Poly :=
    C ((-2 : ℂ) * Complex.I + (-2 : ℂ)) * mon 1 3 1 0 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I + (1 : ℂ) * r ^ 2) * mon 1 3 0 1 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I) * mon 1 2 2 0 +
    C ((8 : ℂ) * Complex.I + (-8 : ℂ)) * mon 1 2 0 2 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I + (-1 : ℂ) * r ^ 2) * mon 1 1 1 2 +
    C ((6 : ℂ) * Complex.I + (-4 : ℂ)) * mon 1 0 4 0 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I + (-1 : ℂ) * r ^ 2) * mon 1 0 3 1 +
    C ((-6 : ℂ) * Complex.I + (-6 : ℂ)) * mon 1 0 1 3 +
    C ((-2 : ℂ) * r) * mon 0 5 0 0 +
    C ((-4 : ℂ) * Complex.I + (2 : ℂ)) * mon 0 4 1 0 +
    C ((-2 : ℂ) * r) * mon 0 3 1 1 +
    C ((-2 : ℂ) * Complex.I + (-2 : ℂ)) * mon 0 3 0 2 +
    C ((6 : ℂ) * r * Complex.I) * mon 0 2 3 0 +
    C ((-2 : ℂ) * Complex.I) * mon 0 2 2 1 +
    C ((-6 : ℂ) * r * Complex.I + (-6 : ℂ) * r) * mon 0 2 0 3 +
    C ((-2 : ℂ) * Complex.I + (-4 : ℂ)) * mon 0 1 4 0 +
    C ((6 : ℂ) * r * Complex.I) * mon 0 0 4 1 +
    C ((4 : ℂ) * Complex.I + (-4 : ℂ)) * mon 0 0 3 2 +
    C ((-6 : ℂ) * r * Complex.I + (-6 : ℂ) * r) * mon 0 0 1 4

def degreeNineWitness20_2 (r : ℂ) : Poly :=
    C ((-2 : ℂ) * r ^ 2 * Complex.I) * mon 1 3 0 1 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I) * mon 1 2 2 0 +
    C ((6 : ℂ) * Complex.I) * mon 1 1 2 1 +
    C ((-4 : ℂ)) * mon 0 2 2 1

def degreeNineWitness20_3 (r : ℂ) : Poly :=
    C ((-1 : ℂ) * r ^ 2) * mon 1 5 0 0 +
    C ((2 : ℂ)) * mon 1 4 0 1 +
    C ((1 : ℂ) * r ^ 2 * Complex.I) * mon 1 3 1 1 +
    C ((1 : ℂ) * r ^ 2 * Complex.I) * mon 1 2 3 0 +
    C ((-6 : ℂ) * Complex.I) * mon 1 1 3 1 +
    C ((6 : ℂ) * Complex.I + (6 : ℂ)) * mon 1 1 0 4 +
    C ((2 : ℂ) * Complex.I) * mon 0 5 0 1 +
    C ((4 : ℂ)) * mon 0 2 3 1

theorem degreeNineCertificate20 (r : ℂ) (hr : r ^ 3 = 2) :
    (12 : Poly) * mon 1 1 0 7 - C ((-1 : ℂ) * r ^ 2 * Complex.I) * mon 1 8 0 0 =
      relation r 0 * degreeNineWitness20_0 r +
      relation r 1 * degreeNineWitness20_1 r +
      relation r 2 * degreeNineWitness20_2 r +
      relation r 3 * degreeNineWitness20_3 r := by
  have hr' : (C r : Poly) ^ 3 = 2 := by rw [← map_pow, hr, map_ofNat]
  have hi' : (C Complex.I : Poly) ^ 2 = -1 := by
    rw [← map_pow, Complex.I_sq, map_neg, map_one]
  norm_num only [degreeNineWitness20_0, degreeNineWitness20_1,
    degreeNineWitness20_2, degreeNineWitness20_3, relation, b, h, mon,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
    map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_zero, map_one] <;>
    ring_nf <;> (try simp only [hr', hi']) <;> ring

def degreeNineWitness21_0 (r : ℂ) : Poly :=
    C ((-1 : ℂ) * Complex.I + (-1 : ℂ)) * mon 0 3 1 3 +
    C ((-1 : ℂ) * Complex.I + (-1 : ℂ)) * mon 0 1 2 4

def degreeNineWitness21_1 (r : ℂ) : Poly :=
    C ((1 : ℂ) * Complex.I + (-1 : ℂ)) * mon 1 2 1 1 +
    C ((-1 : ℂ) * Complex.I + (-1 : ℂ)) * mon 1 0 2 2 +
    C ((-1 : ℂ) * r * Complex.I + (-1 : ℂ) * r) * mon 0 2 1 2 +
    C ((-1 : ℂ) * r * Complex.I + (-1 : ℂ) * r) * mon 0 0 2 3

def degreeNineWitness21_2 (r : ℂ) : Poly :=
    C ((-1 : ℂ) * Complex.I + (-1 : ℂ)) * mon 1 1 0 3

def degreeNineWitness21_3 (r : ℂ) : Poly :=
    C ((1 : ℂ) * Complex.I + (1 : ℂ)) * mon 1 1 1 3

theorem degreeNineCertificate21 (r : ℂ) (hr : r ^ 3 = 2) :
    (2 : Poly) * mon 1 1 1 6 - C ((0 : ℂ)) * mon 1 8 0 0 =
      relation r 0 * degreeNineWitness21_0 r +
      relation r 1 * degreeNineWitness21_1 r +
      relation r 2 * degreeNineWitness21_2 r +
      relation r 3 * degreeNineWitness21_3 r := by
  have hr' : (C r : Poly) ^ 3 = 2 := by rw [← map_pow, hr, map_ofNat]
  have hi' : (C Complex.I : Poly) ^ 2 = -1 := by
    rw [← map_pow, Complex.I_sq, map_neg, map_one]
  norm_num only [degreeNineWitness21_0, degreeNineWitness21_1,
    degreeNineWitness21_2, degreeNineWitness21_3, relation, b, h, mon,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
    map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_zero, map_one] <;>
    ring_nf <;> (try simp only [hr', hi']) <;> ring

def degreeNineWitness22_0 (r : ℂ) : Poly :=
    C ((-1 : ℂ) * Complex.I + (-1 : ℂ)) * mon 0 3 2 2 +
    C ((-1 : ℂ) * Complex.I + (-1 : ℂ)) * mon 0 1 3 3

def degreeNineWitness22_1 (r : ℂ) : Poly :=
    C ((1 : ℂ) * Complex.I + (-1 : ℂ)) * mon 1 2 2 0 +
    C ((-1 : ℂ) * Complex.I + (-1 : ℂ)) * mon 1 0 3 1 +
    C ((-1 : ℂ) * r * Complex.I + (-1 : ℂ) * r) * mon 0 2 2 1 +
    C ((-1 : ℂ) * r * Complex.I + (-1 : ℂ) * r) * mon 0 0 3 2

def degreeNineWitness22_2 (r : ℂ) : Poly :=
    C ((-1 : ℂ) * Complex.I + (-1 : ℂ)) * mon 1 1 1 2

def degreeNineWitness22_3 (r : ℂ) : Poly :=
    C ((1 : ℂ) * Complex.I + (1 : ℂ)) * mon 1 1 2 2

theorem degreeNineCertificate22 (r : ℂ) (hr : r ^ 3 = 2) :
    (2 : Poly) * mon 1 1 2 5 - C ((0 : ℂ)) * mon 1 8 0 0 =
      relation r 0 * degreeNineWitness22_0 r +
      relation r 1 * degreeNineWitness22_1 r +
      relation r 2 * degreeNineWitness22_2 r +
      relation r 3 * degreeNineWitness22_3 r := by
  have hr' : (C r : Poly) ^ 3 = 2 := by rw [← map_pow, hr, map_ofNat]
  have hi' : (C Complex.I : Poly) ^ 2 = -1 := by
    rw [← map_pow, Complex.I_sq, map_neg, map_one]
  norm_num only [degreeNineWitness22_0, degreeNineWitness22_1,
    degreeNineWitness22_2, degreeNineWitness22_3, relation, b, h, mon,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
    map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_zero, map_one] <;>
    ring_nf <;> (try simp only [hr', hi']) <;> ring

def degreeNineWitness23_0 (r : ℂ) : Poly :=
    C ((1 : ℂ) * r ^ 2 * Complex.I + (-1 : ℂ) * r ^ 2) * mon 0 7 0 0 +
    C ((-2 : ℂ) * Complex.I + (2 : ℂ)) * mon 0 6 0 1 +
    C ((2 : ℂ) * r ^ 2 * Complex.I) * mon 0 5 1 1 +
    C ((1 : ℂ) * r ^ 2 * Complex.I + (1 : ℂ) * r ^ 2) * mon 0 4 3 0 +
    C ((-2 : ℂ) * Complex.I + (2 : ℂ)) * mon 0 4 1 2 +
    C ((-6 : ℂ) * Complex.I + (-6 : ℂ)) * mon 0 3 3 1 +
    C ((1 : ℂ) * r ^ 2 * Complex.I + (1 : ℂ) * r ^ 2) * mon 0 3 2 2 +
    C ((1 : ℂ) * r ^ 2 * Complex.I + (1 : ℂ) * r ^ 2) * mon 0 2 4 1 +
    C ((-6 : ℂ) * Complex.I + (-6 : ℂ)) * mon 0 1 4 2

def degreeNineWitness23_1 (r : ℂ) : Poly :=
    C ((4 : ℂ)) * mon 1 3 1 0 +
    C ((2 : ℂ) * r ^ 2 * Complex.I) * mon 1 3 0 1 +
    C ((1 : ℂ) * r ^ 2 * Complex.I + (1 : ℂ) * r ^ 2) * mon 1 2 2 0 +
    C ((-4 : ℂ) * Complex.I) * mon 1 2 0 2 +
    C ((2 : ℂ) * r ^ 2) * mon 1 1 1 2 +
    C ((-10 : ℂ) * Complex.I + (-2 : ℂ)) * mon 1 0 4 0 +
    C ((2 : ℂ) * r ^ 2) * mon 1 0 3 1 +
    C ((-2 : ℂ) * r * Complex.I + (2 : ℂ) * r) * mon 0 5 0 0 +
    C ((6 : ℂ) * Complex.I + (2 : ℂ)) * mon 0 4 1 0 +
    C ((-2 : ℂ) * r * Complex.I + (2 : ℂ) * r) * mon 0 3 1 1 +
    C ((4 : ℂ)) * mon 0 3 0 2 +
    C ((-6 : ℂ) * r * Complex.I + (-6 : ℂ) * r) * mon 0 2 3 0 +
    C ((2 : ℂ) * Complex.I + (2 : ℂ)) * mon 0 2 2 1 +
    C ((-2 : ℂ) * Complex.I + (6 : ℂ)) * mon 0 1 4 0 +
    C ((-6 : ℂ) * r * Complex.I + (-6 : ℂ) * r) * mon 0 0 4 1 +
    C ((-8 : ℂ) * Complex.I) * mon 0 0 3 2

def degreeNineWitness23_2 (r : ℂ) : Poly :=
    C ((2 : ℂ) * r ^ 2 * Complex.I + (2 : ℂ) * r ^ 2) * mon 1 3 0 1 +
    C ((1 : ℂ) * r ^ 2 * Complex.I + (1 : ℂ) * r ^ 2) * mon 1 2 2 0 +
    C ((-6 : ℂ) * Complex.I + (-6 : ℂ)) * mon 1 1 2 1 +
    C ((-4 : ℂ) * Complex.I + (4 : ℂ)) * mon 0 2 2 1

def degreeNineWitness23_3 (r : ℂ) : Poly :=
    C ((-1 : ℂ) * r ^ 2 * Complex.I + (1 : ℂ) * r ^ 2) * mon 1 5 0 0 +
    C ((2 : ℂ) * Complex.I + (-2 : ℂ)) * mon 1 4 0 1 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I + (-1 : ℂ) * r ^ 2) * mon 1 3 1 1 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I + (-1 : ℂ) * r ^ 2) * mon 1 2 3 0 +
    C ((6 : ℂ) * Complex.I + (6 : ℂ)) * mon 1 1 3 1 +
    C ((-2 : ℂ) * Complex.I + (-2 : ℂ)) * mon 0 5 0 1 +
    C ((4 : ℂ) * Complex.I + (-4 : ℂ)) * mon 0 2 3 1

theorem degreeNineCertificate23 (r : ℂ) (hr : r ^ 3 = 2) :
    (12 : Poly) * mon 1 1 3 4 - C ((1 : ℂ) * r ^ 2 * Complex.I + (1 : ℂ) * r ^ 2) * mon 1 8 0 0 =
      relation r 0 * degreeNineWitness23_0 r +
      relation r 1 * degreeNineWitness23_1 r +
      relation r 2 * degreeNineWitness23_2 r +
      relation r 3 * degreeNineWitness23_3 r := by
  have hr' : (C r : Poly) ^ 3 = 2 := by rw [← map_pow, hr, map_ofNat]
  have hi' : (C Complex.I : Poly) ^ 2 = -1 := by
    rw [← map_pow, Complex.I_sq, map_neg, map_one]
  norm_num only [degreeNineWitness23_0, degreeNineWitness23_1,
    degreeNineWitness23_2, degreeNineWitness23_3, relation, b, h, mon,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
    map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_zero, map_one] <;>
    ring_nf <;> (try simp only [hr', hi']) <;> ring

def degreeNineWitness24_0 (r : ℂ) : Poly :=
    C ((1 : ℂ) * r ^ 2) * mon 0 7 0 0 +
    C ((-2 : ℂ)) * mon 0 6 0 1 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I + (1 : ℂ) * r ^ 2) * mon 0 5 1 1 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I) * mon 0 4 3 0 +
    C ((-2 : ℂ)) * mon 0 4 1 2 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I) * mon 0 3 2 2 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I) * mon 0 2 4 1

def degreeNineWitness24_1 (r : ℂ) : Poly :=
    C ((-2 : ℂ) * Complex.I + (-2 : ℂ)) * mon 1 3 1 0 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I + (1 : ℂ) * r ^ 2) * mon 1 3 0 1 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I) * mon 1 2 2 0 +
    C ((2 : ℂ) * Complex.I + (-2 : ℂ)) * mon 1 2 0 2 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I + (-1 : ℂ) * r ^ 2) * mon 1 1 1 2 +
    C ((-4 : ℂ)) * mon 1 0 4 0 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I + (-1 : ℂ) * r ^ 2) * mon 1 0 3 1 +
    C ((-2 : ℂ) * r) * mon 0 5 0 0 +
    C ((-4 : ℂ) * Complex.I + (2 : ℂ)) * mon 0 4 1 0 +
    C ((-2 : ℂ) * r) * mon 0 3 1 1 +
    C ((-2 : ℂ) * Complex.I + (-2 : ℂ)) * mon 0 3 0 2 +
    C ((-2 : ℂ) * Complex.I) * mon 0 2 2 1 +
    C ((-2 : ℂ) * Complex.I + (-4 : ℂ)) * mon 0 1 4 0 +
    C ((4 : ℂ) * Complex.I + (-4 : ℂ)) * mon 0 0 3 2

def degreeNineWitness24_2 (r : ℂ) : Poly :=
    C ((-2 : ℂ) * r ^ 2 * Complex.I) * mon 1 3 0 1 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I) * mon 1 2 2 0 +
    C ((-4 : ℂ)) * mon 0 2 2 1

def degreeNineWitness24_3 (r : ℂ) : Poly :=
    C ((-1 : ℂ) * r ^ 2) * mon 1 5 0 0 +
    C ((2 : ℂ)) * mon 1 4 0 1 +
    C ((1 : ℂ) * r ^ 2 * Complex.I) * mon 1 3 1 1 +
    C ((1 : ℂ) * r ^ 2 * Complex.I) * mon 1 2 3 0 +
    C ((2 : ℂ) * Complex.I) * mon 0 5 0 1 +
    C ((4 : ℂ)) * mon 0 2 3 1

theorem degreeNineCertificate24 (r : ℂ) (hr : r ^ 3 = 2) :
    (6 : Poly) * mon 1 4 3 1 - C ((-1 : ℂ) * r ^ 2 * Complex.I) * mon 1 8 0 0 =
      relation r 0 * degreeNineWitness24_0 r +
      relation r 1 * degreeNineWitness24_1 r +
      relation r 2 * degreeNineWitness24_2 r +
      relation r 3 * degreeNineWitness24_3 r := by
  have hr' : (C r : Poly) ^ 3 = 2 := by rw [← map_pow, hr, map_ofNat]
  have hi' : (C Complex.I : Poly) ^ 2 = -1 := by
    rw [← map_pow, Complex.I_sq, map_neg, map_one]
  norm_num only [degreeNineWitness24_0, degreeNineWitness24_1,
    degreeNineWitness24_2, degreeNineWitness24_3, relation, b, h, mon,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
    map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_zero, map_one] <;>
    ring_nf <;> (try simp only [hr', hi']) <;> ring

def degreeNineWitness25_0 (r : ℂ) : Poly :=
    C ((-1 : ℂ) * Complex.I) * mon 0 4 2 1 +
    C ((-1 : ℂ) * Complex.I) * mon 0 2 3 2

def degreeNineWitness25_1 (r : ℂ) : Poly :=
    C ((-1 : ℂ) * Complex.I) * mon 1 1 3 0 +
    C ((-1 : ℂ) * Complex.I + (-1 : ℂ)) * mon 1 0 2 2 +
    C ((-1 : ℂ) * r * Complex.I) * mon 0 3 2 0 +
    C ((-1 : ℂ) * r * Complex.I) * mon 0 1 3 1

def degreeNineWitness25_2 (r : ℂ) : Poly :=
    C ((-1 : ℂ) * Complex.I) * mon 1 2 1 1

def degreeNineWitness25_3 (r : ℂ) : Poly :=
    C ((1 : ℂ) * Complex.I) * mon 1 2 2 1

theorem degreeNineCertificate25 (r : ℂ) (hr : r ^ 3 = 2) :
    (1 : Poly) * mon 1 5 2 1 - C ((0 : ℂ)) * mon 1 8 0 0 =
      relation r 0 * degreeNineWitness25_0 r +
      relation r 1 * degreeNineWitness25_1 r +
      relation r 2 * degreeNineWitness25_2 r +
      relation r 3 * degreeNineWitness25_3 r := by
  have hr' : (C r : Poly) ^ 3 = 2 := by rw [← map_pow, hr, map_ofNat]
  have hi' : (C Complex.I : Poly) ^ 2 = -1 := by
    rw [← map_pow, Complex.I_sq, map_neg, map_one]
  norm_num only [degreeNineWitness25_0, degreeNineWitness25_1,
    degreeNineWitness25_2, degreeNineWitness25_3, relation, b, h, mon,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
    map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_zero, map_one] <;>
    ring_nf <;> (try simp only [hr', hi']) <;> ring

def degreeNineWitness26_0 (r : ℂ) : Poly :=
    C ((-1 : ℂ)) * mon 0 7 0 0 +
    C ((1 : ℂ) * r) * mon 0 6 0 1 +
    C ((1 : ℂ) * Complex.I + (-1 : ℂ)) * mon 0 5 1 1 +
    C ((-2 : ℂ) * Complex.I) * mon 0 4 3 0 +
    C ((1 : ℂ) * r) * mon 0 4 1 2 +
    C ((1 : ℂ) * Complex.I) * mon 0 3 2 2 +
    C ((-2 : ℂ) * Complex.I) * mon 0 2 4 1

def degreeNineWitness26_1 (r : ℂ) : Poly :=
    C ((1 : ℂ) * r * Complex.I + (1 : ℂ) * r) * mon 1 3 1 0 +
    C ((1 : ℂ) * Complex.I + (-1 : ℂ)) * mon 1 3 0 1 +
    C ((1 : ℂ) * Complex.I) * mon 1 2 2 0 +
    C ((-1 : ℂ) * r * Complex.I + (1 : ℂ) * r) * mon 1 2 0 2 +
    C ((1 : ℂ) * Complex.I + (1 : ℂ)) * mon 1 1 1 2 +
    C ((-1 : ℂ) * r) * mon 1 0 4 0 +
    C ((-2 : ℂ) * Complex.I + (-2 : ℂ)) * mon 1 0 3 1 +
    C ((1 : ℂ) * r ^ 2) * mon 0 5 0 0 +
    C ((2 : ℂ) * r * Complex.I + (-1 : ℂ) * r) * mon 0 4 1 0 +
    C ((1 : ℂ) * r ^ 2) * mon 0 3 1 1 +
    C ((1 : ℂ) * r * Complex.I + (1 : ℂ) * r) * mon 0 3 0 2 +
    C ((1 : ℂ) * r * Complex.I) * mon 0 2 2 1 +
    C ((-2 : ℂ) * r * Complex.I + (-1 : ℂ) * r) * mon 0 1 4 0 +
    C ((1 : ℂ) * r * Complex.I + (-1 : ℂ) * r) * mon 0 0 3 2

def degreeNineWitness26_2 (r : ℂ) : Poly :=
    C ((-1 : ℂ) * Complex.I) * mon 1 3 0 1 +
    C ((-2 : ℂ) * Complex.I) * mon 1 2 2 0 +
    C ((-1 : ℂ) * r) * mon 0 2 2 1

def degreeNineWitness26_3 (r : ℂ) : Poly :=
    C ((1 : ℂ)) * mon 1 5 0 0 +
    C ((-1 : ℂ) * r) * mon 1 4 0 1 +
    C ((-1 : ℂ) * Complex.I) * mon 1 3 1 1 +
    C ((2 : ℂ) * Complex.I) * mon 1 2 3 0 +
    C ((-1 : ℂ) * r * Complex.I) * mon 0 5 0 1 +
    C ((1 : ℂ) * r) * mon 0 2 3 1

theorem degreeNineCertificate26 (r : ℂ) (hr : r ^ 3 = 2) :
    (3 : Poly) * mon 1 5 3 0 - C ((1 : ℂ) * Complex.I) * mon 1 8 0 0 =
      relation r 0 * degreeNineWitness26_0 r +
      relation r 1 * degreeNineWitness26_1 r +
      relation r 2 * degreeNineWitness26_2 r +
      relation r 3 * degreeNineWitness26_3 r := by
  have hr' : (C r : Poly) ^ 3 = 2 := by rw [← map_pow, hr, map_ofNat]
  have hi' : (C Complex.I : Poly) ^ 2 = -1 := by
    rw [← map_pow, Complex.I_sq, map_neg, map_one]
  norm_num only [degreeNineWitness26_0, degreeNineWitness26_1,
    degreeNineWitness26_2, degreeNineWitness26_3, relation, b, h, mon,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
    map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_zero, map_one] <;>
    ring_nf <;> (try simp only [hr', hi']) <;> ring

def degreeNineWitness27_0 (r : ℂ) : Poly :=
    C ((-1 : ℂ) * Complex.I) * mon 0 5 1 1 +
    C ((-1 : ℂ) * Complex.I) * mon 0 3 2 2

def degreeNineWitness27_1 (r : ℂ) : Poly :=
    C ((-1 : ℂ) * Complex.I) * mon 1 2 2 0 +
    C ((-1 : ℂ) * Complex.I + (-1 : ℂ)) * mon 1 1 1 2 +
    C ((-1 : ℂ) * r * Complex.I) * mon 0 4 1 0 +
    C ((-1 : ℂ) * r * Complex.I) * mon 0 2 2 1

def degreeNineWitness27_2 (r : ℂ) : Poly :=
    C ((-1 : ℂ) * Complex.I) * mon 1 3 0 1

def degreeNineWitness27_3 (r : ℂ) : Poly :=
    C ((1 : ℂ) * Complex.I) * mon 1 3 1 1

theorem degreeNineCertificate27 (r : ℂ) (hr : r ^ 3 = 2) :
    (1 : Poly) * mon 1 6 1 1 - C ((0 : ℂ)) * mon 1 8 0 0 =
      relation r 0 * degreeNineWitness27_0 r +
      relation r 1 * degreeNineWitness27_1 r +
      relation r 2 * degreeNineWitness27_2 r +
      relation r 3 * degreeNineWitness27_3 r := by
  have hr' : (C r : Poly) ^ 3 = 2 := by rw [← map_pow, hr, map_ofNat]
  have hi' : (C Complex.I : Poly) ^ 2 = -1 := by
    rw [← map_pow, Complex.I_sq, map_neg, map_one]
  norm_num only [degreeNineWitness27_0, degreeNineWitness27_1,
    degreeNineWitness27_2, degreeNineWitness27_3, relation, b, h, mon,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
    map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_zero, map_one] <;>
    ring_nf <;> (try simp only [hr', hi']) <;> ring

def degreeNineWitness28_0 (r : ℂ) : Poly :=
    C ((-1 : ℂ) * r ^ 2 * Complex.I) * mon 0 7 0 0 +
    C ((2 : ℂ) * Complex.I) * mon 0 6 0 1 +
    C ((-6 : ℂ) * Complex.I) * mon 0 5 2 0 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I + (-1 : ℂ) * r ^ 2) * mon 0 5 1 1 +
    C ((-1 : ℂ) * r ^ 2) * mon 0 4 3 0 +
    C ((6 : ℂ) * r * Complex.I) * mon 0 4 2 1 +
    C ((2 : ℂ) * Complex.I) * mon 0 4 1 2 +
    C ((-6 : ℂ) * Complex.I) * mon 0 3 3 1 +
    C ((-1 : ℂ) * r ^ 2) * mon 0 3 2 2 +
    C ((-1 : ℂ) * r ^ 2) * mon 0 2 4 1 +
    C ((6 : ℂ) * r * Complex.I) * mon 0 2 3 2

def degreeNineWitness28_1 (r : ℂ) : Poly :=
    C ((2 : ℂ) * Complex.I + (-2 : ℂ)) * mon 1 3 1 0 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I + (-1 : ℂ) * r ^ 2) * mon 1 3 0 1 +
    C ((-1 : ℂ) * r ^ 2) * mon 1 2 2 0 +
    C ((2 : ℂ) * Complex.I + (2 : ℂ)) * mon 1 2 0 2 +
    C ((6 : ℂ) * r * Complex.I + (-6 : ℂ) * r) * mon 1 1 3 0 +
    C ((-6 : ℂ) * Complex.I + (-6 : ℂ)) * mon 1 1 2 1 +
    C ((1 : ℂ) * r ^ 2 * Complex.I + (-1 : ℂ) * r ^ 2) * mon 1 1 1 2 +
    C ((4 : ℂ) * Complex.I) * mon 1 0 4 0 +
    C ((1 : ℂ) * r ^ 2 * Complex.I + (-1 : ℂ) * r ^ 2) * mon 1 0 3 1 +
    C ((6 : ℂ) * r * Complex.I + (6 : ℂ) * r) * mon 1 0 2 2 +
    C ((2 : ℂ) * r * Complex.I) * mon 0 5 0 0 +
    C ((-2 : ℂ) * Complex.I + (-4 : ℂ)) * mon 0 4 1 0 +
    C ((6 : ℂ) * r ^ 2 * Complex.I) * mon 0 3 2 0 +
    C ((2 : ℂ) * r * Complex.I) * mon 0 3 1 1 +
    C ((2 : ℂ) * Complex.I + (-2 : ℂ)) * mon 0 3 0 2 +
    C ((-6 : ℂ) * r * Complex.I + (-6 : ℂ) * r) * mon 0 2 3 0 +
    C ((-2 : ℂ)) * mon 0 2 2 1 +
    C ((4 : ℂ) * Complex.I + (-2 : ℂ)) * mon 0 1 4 0 +
    C ((6 : ℂ) * r ^ 2 * Complex.I) * mon 0 1 3 1 +
    C ((6 : ℂ) * r * Complex.I + (-6 : ℂ) * r) * mon 0 1 2 2 +
    C ((4 : ℂ) * Complex.I + (4 : ℂ)) * mon 0 0 3 2

def degreeNineWitness28_2 (r : ℂ) : Poly :=
    C ((-6 : ℂ) * Complex.I) * mon 1 3 1 0 +
    C ((-2 : ℂ) * r ^ 2) * mon 1 3 0 1 +
    C ((-1 : ℂ) * r ^ 2) * mon 1 2 2 0 +
    C ((6 : ℂ) * r * Complex.I) * mon 1 2 1 1 +
    C ((-6 : ℂ) * r) * mon 0 3 1 1 +
    C ((4 : ℂ) * Complex.I) * mon 0 2 2 1

def degreeNineWitness28_3 (r : ℂ) : Poly :=
    C ((1 : ℂ) * r ^ 2 * Complex.I) * mon 1 5 0 0 +
    C ((-2 : ℂ) * Complex.I) * mon 1 4 0 1 +
    C ((6 : ℂ) * Complex.I) * mon 1 3 2 0 +
    C ((1 : ℂ) * r ^ 2) * mon 1 3 1 1 +
    C ((1 : ℂ) * r ^ 2) * mon 1 2 3 0 +
    C ((-6 : ℂ) * r * Complex.I) * mon 1 2 2 1 +
    C ((2 : ℂ)) * mon 0 5 0 1 +
    C ((6 : ℂ) * r) * mon 0 3 2 1 +
    C ((-4 : ℂ) * Complex.I) * mon 0 2 3 1

theorem degreeNineCertificate28 (r : ℂ) (hr : r ^ 3 = 2) :
    (6 : Poly) * mon 1 6 2 0 - C ((-1 : ℂ) * r ^ 2) * mon 1 8 0 0 =
      relation r 0 * degreeNineWitness28_0 r +
      relation r 1 * degreeNineWitness28_1 r +
      relation r 2 * degreeNineWitness28_2 r +
      relation r 3 * degreeNineWitness28_3 r := by
  have hr' : (C r : Poly) ^ 3 = 2 := by rw [← map_pow, hr, map_ofNat]
  have hi' : (C Complex.I : Poly) ^ 2 = -1 := by
    rw [← map_pow, Complex.I_sq, map_neg, map_one]
  norm_num only [degreeNineWitness28_0, degreeNineWitness28_1,
    degreeNineWitness28_2, degreeNineWitness28_3, relation, b, h, mon,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
    map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_zero, map_one] <;>
    ring_nf <;> (try simp only [hr', hi']) <;> ring

def degreeNineWitness29_0 (r : ℂ) : Poly :=
    C ((-1 : ℂ) * r ^ 2 * Complex.I) * mon 0 7 0 0 +
    C ((-4 : ℂ) * Complex.I) * mon 0 6 0 1 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I + (-1 : ℂ) * r ^ 2) * mon 0 5 1 1 +
    C ((-1 : ℂ) * r ^ 2) * mon 0 4 3 0 +
    C ((-4 : ℂ) * Complex.I) * mon 0 4 1 2 +
    C ((-1 : ℂ) * r ^ 2) * mon 0 3 2 2 +
    C ((-1 : ℂ) * r ^ 2) * mon 0 2 4 1

def degreeNineWitness29_1 (r : ℂ) : Poly :=
    C ((-4 : ℂ) * Complex.I + (-2 : ℂ)) * mon 1 3 1 0 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I + (-1 : ℂ) * r ^ 2) * mon 1 3 0 1 +
    C ((-1 : ℂ) * r ^ 2) * mon 1 2 2 0 +
    C ((-4 : ℂ) * Complex.I + (-4 : ℂ)) * mon 1 2 0 2 +
    C ((1 : ℂ) * r ^ 2 * Complex.I + (-1 : ℂ) * r ^ 2) * mon 1 1 1 2 +
    C ((4 : ℂ) * Complex.I) * mon 1 0 4 0 +
    C ((1 : ℂ) * r ^ 2 * Complex.I + (-1 : ℂ) * r ^ 2) * mon 1 0 3 1 +
    C ((-4 : ℂ) * r * Complex.I) * mon 0 5 0 0 +
    C ((-2 : ℂ) * Complex.I + (-4 : ℂ)) * mon 0 4 1 0 +
    C ((-4 : ℂ) * r * Complex.I) * mon 0 3 1 1 +
    C ((2 : ℂ) * Complex.I + (-2 : ℂ)) * mon 0 3 0 2 +
    C ((-2 : ℂ)) * mon 0 2 2 1 +
    C ((4 : ℂ) * Complex.I + (-2 : ℂ)) * mon 0 1 4 0 +
    C ((4 : ℂ) * Complex.I + (4 : ℂ)) * mon 0 0 3 2

def degreeNineWitness29_2 (r : ℂ) : Poly :=
    C ((-2 : ℂ) * r ^ 2) * mon 1 3 0 1 +
    C ((-1 : ℂ) * r ^ 2) * mon 1 2 2 0 +
    C ((4 : ℂ) * Complex.I) * mon 0 2 2 1

def degreeNineWitness29_3 (r : ℂ) : Poly :=
    C ((1 : ℂ) * r ^ 2 * Complex.I) * mon 1 5 0 0 +
    C ((4 : ℂ) * Complex.I) * mon 1 4 0 1 +
    C ((1 : ℂ) * r ^ 2) * mon 1 3 1 1 +
    C ((1 : ℂ) * r ^ 2) * mon 1 2 3 0 +
    C ((2 : ℂ)) * mon 0 5 0 1 +
    C ((-4 : ℂ) * Complex.I) * mon 0 2 3 1

theorem degreeNineCertificate29 (r : ℂ) (hr : r ^ 3 = 2) :
    (6 : Poly) * mon 1 7 0 1 - C ((-1 : ℂ) * r ^ 2) * mon 1 8 0 0 =
      relation r 0 * degreeNineWitness29_0 r +
      relation r 1 * degreeNineWitness29_1 r +
      relation r 2 * degreeNineWitness29_2 r +
      relation r 3 * degreeNineWitness29_3 r := by
  have hr' : (C r : Poly) ^ 3 = 2 := by rw [← map_pow, hr, map_ofNat]
  have hi' : (C Complex.I : Poly) ^ 2 = -1 := by
    rw [← map_pow, Complex.I_sq, map_neg, map_one]
  norm_num only [degreeNineWitness29_0, degreeNineWitness29_1,
    degreeNineWitness29_2, degreeNineWitness29_3, relation, b, h, mon,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
    map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_zero, map_one] <;>
    ring_nf <;> (try simp only [hr', hi']) <;> ring

def degreeNineWitness30_0 (r : ℂ) : Poly :=
    C ((-1 : ℂ) * Complex.I) * mon 0 6 1 0 +
    C ((1 : ℂ) * r * Complex.I) * mon 0 5 1 1 +
    C ((-1 : ℂ) * Complex.I + (-1 : ℂ)) * mon 0 4 2 1 +
    C ((1 : ℂ) * r * Complex.I) * mon 0 3 2 2 +
    C ((-1 : ℂ)) * mon 0 2 3 2

def degreeNineWitness30_1 (r : ℂ) : Poly :=
    C ((1 : ℂ) * r * Complex.I + (-1 : ℂ) * r) * mon 1 2 2 0 +
    C ((-1 : ℂ) * Complex.I + (-1 : ℂ)) * mon 1 2 1 1 +
    C ((-1 : ℂ)) * mon 1 1 3 0 +
    C ((1 : ℂ) * r * Complex.I + (1 : ℂ) * r) * mon 1 1 1 2 +
    C ((1 : ℂ) * Complex.I + (-1 : ℂ)) * mon 1 0 2 2 +
    C ((1 : ℂ) * r ^ 2 * Complex.I) * mon 0 4 1 0 +
    C ((-1 : ℂ) * r * Complex.I + (-2 : ℂ) * r) * mon 0 3 2 0 +
    C ((1 : ℂ) * r ^ 2 * Complex.I) * mon 0 2 2 1 +
    C ((1 : ℂ) * r * Complex.I + (-1 : ℂ) * r) * mon 0 2 1 2 +
    C ((-1 : ℂ) * r) * mon 0 1 3 1

def degreeNineWitness30_2 (r : ℂ) : Poly :=
    C ((-1 : ℂ) * Complex.I) * mon 1 4 0 0 +
    C ((1 : ℂ) * r * Complex.I) * mon 1 3 0 1 +
    C ((-1 : ℂ)) * mon 1 2 1 1 +
    C ((-1 : ℂ) * r) * mon 0 4 0 1

def degreeNineWitness30_3 (r : ℂ) : Poly :=
    C ((1 : ℂ) * Complex.I) * mon 1 4 1 0 +
    C ((-1 : ℂ) * r * Complex.I) * mon 1 3 1 1 +
    C ((1 : ℂ)) * mon 1 2 2 1 +
    C ((1 : ℂ) * r) * mon 0 4 1 1

theorem degreeNineCertificate30 (r : ℂ) (hr : r ^ 3 = 2) :
    (1 : Poly) * mon 1 7 1 0 - C ((0 : ℂ)) * mon 1 8 0 0 =
      relation r 0 * degreeNineWitness30_0 r +
      relation r 1 * degreeNineWitness30_1 r +
      relation r 2 * degreeNineWitness30_2 r +
      relation r 3 * degreeNineWitness30_3 r := by
  have hr' : (C r : Poly) ^ 3 = 2 := by rw [← map_pow, hr, map_ofNat]
  have hi' : (C Complex.I : Poly) ^ 2 = -1 := by
    rw [← map_pow, Complex.I_sq, map_neg, map_one]
  norm_num only [degreeNineWitness30_0, degreeNineWitness30_1,
    degreeNineWitness30_2, degreeNineWitness30_3, relation, b, h, mon,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
    map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_zero, map_one] <;>
    ring_nf <;> (try simp only [hr', hi']) <;> ring

def degreeNineWitness31_0 (r : ℂ) : Poly :=
    0

def degreeNineWitness31_1 (r : ℂ) : Poly :=
    0

def degreeNineWitness31_2 (r : ℂ) : Poly :=
    0

def degreeNineWitness31_3 (r : ℂ) : Poly :=
    0

theorem degreeNineCertificate31 (r : ℂ) (hr : r ^ 3 = 2) :
    (1 : Poly) * mon 1 8 0 0 - C ((1 : ℂ)) * mon 1 8 0 0 =
      relation r 0 * degreeNineWitness31_0 r +
      relation r 1 * degreeNineWitness31_1 r +
      relation r 2 * degreeNineWitness31_2 r +
      relation r 3 * degreeNineWitness31_3 r := by
  have hr' : (C r : Poly) ^ 3 = 2 := by rw [← map_pow, hr, map_ofNat]
  have hi' : (C Complex.I : Poly) ^ 2 = -1 := by
    rw [← map_pow, Complex.I_sq, map_neg, map_one]
  norm_num only [degreeNineWitness31_0, degreeNineWitness31_1,
    degreeNineWitness31_2, degreeNineWitness31_3, relation, b, h, mon,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
    map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_zero, map_one] <;>
    ring_nf <;> (try simp only [hr', hi']) <;> ring

end CycleQ2SeedTrace

#print axioms CycleQ2SeedTrace.degreeNineCertificate0
#print axioms CycleQ2SeedTrace.degreeNineCertificate1
#print axioms CycleQ2SeedTrace.degreeNineCertificate2
#print axioms CycleQ2SeedTrace.degreeNineCertificate3
#print axioms CycleQ2SeedTrace.degreeNineCertificate4
#print axioms CycleQ2SeedTrace.degreeNineCertificate5
#print axioms CycleQ2SeedTrace.degreeNineCertificate6
#print axioms CycleQ2SeedTrace.degreeNineCertificate7
#print axioms CycleQ2SeedTrace.degreeNineCertificate8
#print axioms CycleQ2SeedTrace.degreeNineCertificate9
#print axioms CycleQ2SeedTrace.degreeNineCertificate10
#print axioms CycleQ2SeedTrace.degreeNineCertificate11
#print axioms CycleQ2SeedTrace.degreeNineCertificate12
#print axioms CycleQ2SeedTrace.degreeNineCertificate13
#print axioms CycleQ2SeedTrace.degreeNineCertificate14
#print axioms CycleQ2SeedTrace.degreeNineCertificate15
#print axioms CycleQ2SeedTrace.degreeNineCertificate16
#print axioms CycleQ2SeedTrace.degreeNineCertificate17
#print axioms CycleQ2SeedTrace.degreeNineCertificate18
#print axioms CycleQ2SeedTrace.degreeNineCertificate19
#print axioms CycleQ2SeedTrace.degreeNineCertificate20
#print axioms CycleQ2SeedTrace.degreeNineCertificate21
#print axioms CycleQ2SeedTrace.degreeNineCertificate22
#print axioms CycleQ2SeedTrace.degreeNineCertificate23
#print axioms CycleQ2SeedTrace.degreeNineCertificate24
#print axioms CycleQ2SeedTrace.degreeNineCertificate25
#print axioms CycleQ2SeedTrace.degreeNineCertificate26
#print axioms CycleQ2SeedTrace.degreeNineCertificate27
#print axioms CycleQ2SeedTrace.degreeNineCertificate28
#print axioms CycleQ2SeedTrace.degreeNineCertificate29
#print axioms CycleQ2SeedTrace.degreeNineCertificate30
#print axioms CycleQ2SeedTrace.degreeNineCertificate31
end
end


/- Component: seed_trace/SparseSeedDegreeNineCertificates.lean -/
section
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace CycleQ2SeedTrace
open MvPolynomial

/-- Every displayed normal monomial is proved to lie on the normalization line. -/
theorem degreeNineMonomial_mem_line (r : ℂ) (hr : r ^ 3 = 2) (i : Fin 32) :
    reducedQuotient r (degreeNineMonomial i) ∈ degreeNineLine r := by
  fin_cases i
  · change reducedQuotient r (mon 0 0 0 9) ∈ degreeNineLine r
    have hmem := fourRelationSum_mem r
      (degreeNineWitness0_0 r) (degreeNineWitness0_1 r)
      (degreeNineWitness0_2 r) (degreeNineWitness0_3 r)
    rw [← degreeNineCertificate0 r hr] at hmem
    exact class_mem_line_of_scaled_relation r (12 : ℂ) ((1 : ℂ)) _ (by norm_num)
      (by simpa only [map_ofNat, map_one] using hmem)
  · change reducedQuotient r (mon 0 0 1 8) ∈ degreeNineLine r
    have hmem := fourRelationSum_mem r
      (degreeNineWitness1_0 r) (degreeNineWitness1_1 r)
      (degreeNineWitness1_2 r) (degreeNineWitness1_3 r)
    rw [← degreeNineCertificate1 r hr] at hmem
    exact class_mem_line_of_scaled_relation r (12 : ℂ) ((1 : ℂ) * r ^ 2 * Complex.I + (-1 : ℂ) * r ^ 2) _ (by norm_num)
      (by simpa only [map_ofNat, map_one] using hmem)
  · change reducedQuotient r (mon 0 0 2 7) ∈ degreeNineLine r
    have hmem := fourRelationSum_mem r
      (degreeNineWitness2_0 r) (degreeNineWitness2_1 r)
      (degreeNineWitness2_2 r) (degreeNineWitness2_3 r)
    rw [← degreeNineCertificate2 r hr] at hmem
    exact class_mem_line_of_scaled_relation r (2 : ℂ) ((0 : ℂ)) _ (by norm_num)
      (by simpa only [map_ofNat, map_one] using hmem)
  · change reducedQuotient r (mon 0 0 3 6) ∈ degreeNineLine r
    have hmem := fourRelationSum_mem r
      (degreeNineWitness3_0 r) (degreeNineWitness3_1 r)
      (degreeNineWitness3_2 r) (degreeNineWitness3_3 r)
    rw [← degreeNineCertificate3 r hr] at hmem
    exact class_mem_line_of_scaled_relation r (2 : ℂ) ((0 : ℂ)) _ (by norm_num)
      (by simpa only [map_ofNat, map_one] using hmem)
  · change reducedQuotient r (mon 0 1 0 8) ∈ degreeNineLine r
    have hmem := fourRelationSum_mem r
      (degreeNineWitness4_0 r) (degreeNineWitness4_1 r)
      (degreeNineWitness4_2 r) (degreeNineWitness4_3 r)
    rw [← degreeNineCertificate4 r hr] at hmem
    exact class_mem_line_of_scaled_relation r (2 : ℂ) ((0 : ℂ)) _ (by norm_num)
      (by simpa only [map_ofNat, map_one] using hmem)
  · change reducedQuotient r (mon 0 1 1 7) ∈ degreeNineLine r
    have hmem := fourRelationSum_mem r
      (degreeNineWitness5_0 r) (degreeNineWitness5_1 r)
      (degreeNineWitness5_2 r) (degreeNineWitness5_3 r)
    rw [← degreeNineCertificate5 r hr] at hmem
    exact class_mem_line_of_scaled_relation r (2 : ℂ) ((0 : ℂ)) _ (by norm_num)
      (by simpa only [map_ofNat, map_one] using hmem)
  · change reducedQuotient r (mon 0 1 2 6) ∈ degreeNineLine r
    have hmem := fourRelationSum_mem r
      (degreeNineWitness6_0 r) (degreeNineWitness6_1 r)
      (degreeNineWitness6_2 r) (degreeNineWitness6_3 r)
    rw [← degreeNineCertificate6 r hr] at hmem
    exact class_mem_line_of_scaled_relation r (12 : ℂ) ((-1 : ℂ) * r ^ 2 * Complex.I) _ (by norm_num)
      (by simpa only [map_ofNat, map_one] using hmem)
  · change reducedQuotient r (mon 0 1 3 5) ∈ degreeNineLine r
    have hmem := fourRelationSum_mem r
      (degreeNineWitness7_0 r) (degreeNineWitness7_1 r)
      (degreeNineWitness7_2 r) (degreeNineWitness7_3 r)
    rw [← degreeNineCertificate7 r hr] at hmem
    exact class_mem_line_of_scaled_relation r (2 : ℂ) ((0 : ℂ)) _ (by norm_num)
      (by simpa only [map_ofNat, map_one] using hmem)
  · change reducedQuotient r (mon 0 5 3 1) ∈ degreeNineLine r
    have hmem := fourRelationSum_mem r
      (degreeNineWitness8_0 r) (degreeNineWitness8_1 r)
      (degreeNineWitness8_2 r) (degreeNineWitness8_3 r)
    rw [← degreeNineCertificate8 r hr] at hmem
    exact class_mem_line_of_scaled_relation r (6 : ℂ) ((-1 : ℂ) * r ^ 2) _ (by norm_num)
      (by simpa only [map_ofNat, map_one] using hmem)
  · change reducedQuotient r (mon 0 6 2 1) ∈ degreeNineLine r
    have hmem := fourRelationSum_mem r
      (degreeNineWitness9_0 r) (degreeNineWitness9_1 r)
      (degreeNineWitness9_2 r) (degreeNineWitness9_3 r)
    rw [← degreeNineCertificate9 r hr] at hmem
    exact class_mem_line_of_scaled_relation r (1 : ℂ) ((0 : ℂ)) _ (by norm_num)
      (by simpa only [map_ofNat, map_one] using hmem)
  · change reducedQuotient r (mon 0 6 3 0) ∈ degreeNineLine r
    have hmem := fourRelationSum_mem r
      (degreeNineWitness10_0 r) (degreeNineWitness10_1 r)
      (degreeNineWitness10_2 r) (degreeNineWitness10_3 r)
    rw [← degreeNineCertificate10 r hr] at hmem
    exact class_mem_line_of_scaled_relation r (3 : ℂ) ((1 : ℂ)) _ (by norm_num)
      (by simpa only [map_ofNat, map_one] using hmem)
  · change reducedQuotient r (mon 0 7 1 1) ∈ degreeNineLine r
    have hmem := fourRelationSum_mem r
      (degreeNineWitness11_0 r) (degreeNineWitness11_1 r)
      (degreeNineWitness11_2 r) (degreeNineWitness11_3 r)
    rw [← degreeNineCertificate11 r hr] at hmem
    exact class_mem_line_of_scaled_relation r (1 : ℂ) ((0 : ℂ)) _ (by norm_num)
      (by simpa only [map_ofNat, map_one] using hmem)
  · change reducedQuotient r (mon 0 7 2 0) ∈ degreeNineLine r
    have hmem := fourRelationSum_mem r
      (degreeNineWitness12_0 r) (degreeNineWitness12_1 r)
      (degreeNineWitness12_2 r) (degreeNineWitness12_3 r)
    rw [← degreeNineCertificate12 r hr] at hmem
    exact class_mem_line_of_scaled_relation r (6 : ℂ) ((2 : ℂ) * r ^ 2 * Complex.I + (-1 : ℂ) * r ^ 2) _ (by norm_num)
      (by simpa only [map_ofNat, map_one] using hmem)
  · change reducedQuotient r (mon 0 8 0 1) ∈ degreeNineLine r
    have hmem := fourRelationSum_mem r
      (degreeNineWitness13_0 r) (degreeNineWitness13_1 r)
      (degreeNineWitness13_2 r) (degreeNineWitness13_3 r)
    rw [← degreeNineCertificate13 r hr] at hmem
    exact class_mem_line_of_scaled_relation r (3 : ℂ) ((1 : ℂ) * r ^ 2 * Complex.I) _ (by norm_num)
      (by simpa only [map_ofNat, map_one] using hmem)
  · change reducedQuotient r (mon 0 8 1 0) ∈ degreeNineLine r
    have hmem := fourRelationSum_mem r
      (degreeNineWitness14_0 r) (degreeNineWitness14_1 r)
      (degreeNineWitness14_2 r) (degreeNineWitness14_3 r)
    rw [← degreeNineCertificate14 r hr] at hmem
    exact class_mem_line_of_scaled_relation r (1 : ℂ) ((0 : ℂ)) _ (by norm_num)
      (by simpa only [map_ofNat, map_one] using hmem)
  · change reducedQuotient r (mon 0 9 0 0) ∈ degreeNineLine r
    have hmem := fourRelationSum_mem r
      (degreeNineWitness15_0 r) (degreeNineWitness15_1 r)
      (degreeNineWitness15_2 r) (degreeNineWitness15_3 r)
    rw [← degreeNineCertificate15 r hr] at hmem
    exact class_mem_line_of_scaled_relation r (3 : ℂ) ((-4 : ℂ) * Complex.I) _ (by norm_num)
      (by simpa only [map_ofNat, map_one] using hmem)
  · change reducedQuotient r (mon 1 0 0 8) ∈ degreeNineLine r
    have hmem := fourRelationSum_mem r
      (degreeNineWitness16_0 r) (degreeNineWitness16_1 r)
      (degreeNineWitness16_2 r) (degreeNineWitness16_3 r)
    rw [← degreeNineCertificate16 r hr] at hmem
    exact class_mem_line_of_scaled_relation r (4 : ℂ) ((0 : ℂ)) _ (by norm_num)
      (by simpa only [map_ofNat, map_one] using hmem)
  · change reducedQuotient r (mon 1 0 1 7) ∈ degreeNineLine r
    have hmem := fourRelationSum_mem r
      (degreeNineWitness17_0 r) (degreeNineWitness17_1 r)
      (degreeNineWitness17_2 r) (degreeNineWitness17_3 r)
    rw [← degreeNineCertificate17 r hr] at hmem
    exact class_mem_line_of_scaled_relation r (12 : ℂ) ((1 : ℂ) * Complex.I + (-1 : ℂ)) _ (by norm_num)
      (by simpa only [map_ofNat, map_one] using hmem)
  · change reducedQuotient r (mon 1 0 2 6) ∈ degreeNineLine r
    have hmem := fourRelationSum_mem r
      (degreeNineWitness18_0 r) (degreeNineWitness18_1 r)
      (degreeNineWitness18_2 r) (degreeNineWitness18_3 r)
    rw [← degreeNineCertificate18 r hr] at hmem
    exact class_mem_line_of_scaled_relation r (12 : ℂ) ((-1 : ℂ) * r ^ 2 * Complex.I) _ (by norm_num)
      (by simpa only [map_ofNat, map_one] using hmem)
  · change reducedQuotient r (mon 1 0 3 5) ∈ degreeNineLine r
    have hmem := fourRelationSum_mem r
      (degreeNineWitness19_0 r) (degreeNineWitness19_1 r)
      (degreeNineWitness19_2 r) (degreeNineWitness19_3 r)
    rw [← degreeNineCertificate19 r hr] at hmem
    exact class_mem_line_of_scaled_relation r (2 : ℂ) ((0 : ℂ)) _ (by norm_num)
      (by simpa only [map_ofNat, map_one] using hmem)
  · change reducedQuotient r (mon 1 1 0 7) ∈ degreeNineLine r
    have hmem := fourRelationSum_mem r
      (degreeNineWitness20_0 r) (degreeNineWitness20_1 r)
      (degreeNineWitness20_2 r) (degreeNineWitness20_3 r)
    rw [← degreeNineCertificate20 r hr] at hmem
    exact class_mem_line_of_scaled_relation r (12 : ℂ) ((-1 : ℂ) * r ^ 2 * Complex.I) _ (by norm_num)
      (by simpa only [map_ofNat, map_one] using hmem)
  · change reducedQuotient r (mon 1 1 1 6) ∈ degreeNineLine r
    have hmem := fourRelationSum_mem r
      (degreeNineWitness21_0 r) (degreeNineWitness21_1 r)
      (degreeNineWitness21_2 r) (degreeNineWitness21_3 r)
    rw [← degreeNineCertificate21 r hr] at hmem
    exact class_mem_line_of_scaled_relation r (2 : ℂ) ((0 : ℂ)) _ (by norm_num)
      (by simpa only [map_ofNat, map_one] using hmem)
  · change reducedQuotient r (mon 1 1 2 5) ∈ degreeNineLine r
    have hmem := fourRelationSum_mem r
      (degreeNineWitness22_0 r) (degreeNineWitness22_1 r)
      (degreeNineWitness22_2 r) (degreeNineWitness22_3 r)
    rw [← degreeNineCertificate22 r hr] at hmem
    exact class_mem_line_of_scaled_relation r (2 : ℂ) ((0 : ℂ)) _ (by norm_num)
      (by simpa only [map_ofNat, map_one] using hmem)
  · change reducedQuotient r (mon 1 1 3 4) ∈ degreeNineLine r
    have hmem := fourRelationSum_mem r
      (degreeNineWitness23_0 r) (degreeNineWitness23_1 r)
      (degreeNineWitness23_2 r) (degreeNineWitness23_3 r)
    rw [← degreeNineCertificate23 r hr] at hmem
    exact class_mem_line_of_scaled_relation r (12 : ℂ) ((1 : ℂ) * r ^ 2 * Complex.I + (1 : ℂ) * r ^ 2) _ (by norm_num)
      (by simpa only [map_ofNat, map_one] using hmem)
  · change reducedQuotient r (mon 1 4 3 1) ∈ degreeNineLine r
    have hmem := fourRelationSum_mem r
      (degreeNineWitness24_0 r) (degreeNineWitness24_1 r)
      (degreeNineWitness24_2 r) (degreeNineWitness24_3 r)
    rw [← degreeNineCertificate24 r hr] at hmem
    exact class_mem_line_of_scaled_relation r (6 : ℂ) ((-1 : ℂ) * r ^ 2 * Complex.I) _ (by norm_num)
      (by simpa only [map_ofNat, map_one] using hmem)
  · change reducedQuotient r (mon 1 5 2 1) ∈ degreeNineLine r
    have hmem := fourRelationSum_mem r
      (degreeNineWitness25_0 r) (degreeNineWitness25_1 r)
      (degreeNineWitness25_2 r) (degreeNineWitness25_3 r)
    rw [← degreeNineCertificate25 r hr] at hmem
    exact class_mem_line_of_scaled_relation r (1 : ℂ) ((0 : ℂ)) _ (by norm_num)
      (by simpa only [map_ofNat, map_one] using hmem)
  · change reducedQuotient r (mon 1 5 3 0) ∈ degreeNineLine r
    have hmem := fourRelationSum_mem r
      (degreeNineWitness26_0 r) (degreeNineWitness26_1 r)
      (degreeNineWitness26_2 r) (degreeNineWitness26_3 r)
    rw [← degreeNineCertificate26 r hr] at hmem
    exact class_mem_line_of_scaled_relation r (3 : ℂ) ((1 : ℂ) * Complex.I) _ (by norm_num)
      (by simpa only [map_ofNat, map_one] using hmem)
  · change reducedQuotient r (mon 1 6 1 1) ∈ degreeNineLine r
    have hmem := fourRelationSum_mem r
      (degreeNineWitness27_0 r) (degreeNineWitness27_1 r)
      (degreeNineWitness27_2 r) (degreeNineWitness27_3 r)
    rw [← degreeNineCertificate27 r hr] at hmem
    exact class_mem_line_of_scaled_relation r (1 : ℂ) ((0 : ℂ)) _ (by norm_num)
      (by simpa only [map_ofNat, map_one] using hmem)
  · change reducedQuotient r (mon 1 6 2 0) ∈ degreeNineLine r
    have hmem := fourRelationSum_mem r
      (degreeNineWitness28_0 r) (degreeNineWitness28_1 r)
      (degreeNineWitness28_2 r) (degreeNineWitness28_3 r)
    rw [← degreeNineCertificate28 r hr] at hmem
    exact class_mem_line_of_scaled_relation r (6 : ℂ) ((-1 : ℂ) * r ^ 2) _ (by norm_num)
      (by simpa only [map_ofNat, map_one] using hmem)
  · change reducedQuotient r (mon 1 7 0 1) ∈ degreeNineLine r
    have hmem := fourRelationSum_mem r
      (degreeNineWitness29_0 r) (degreeNineWitness29_1 r)
      (degreeNineWitness29_2 r) (degreeNineWitness29_3 r)
    rw [← degreeNineCertificate29 r hr] at hmem
    exact class_mem_line_of_scaled_relation r (6 : ℂ) ((-1 : ℂ) * r ^ 2) _ (by norm_num)
      (by simpa only [map_ofNat, map_one] using hmem)
  · change reducedQuotient r (mon 1 7 1 0) ∈ degreeNineLine r
    have hmem := fourRelationSum_mem r
      (degreeNineWitness30_0 r) (degreeNineWitness30_1 r)
      (degreeNineWitness30_2 r) (degreeNineWitness30_3 r)
    rw [← degreeNineCertificate30 r hr] at hmem
    exact class_mem_line_of_scaled_relation r (1 : ℂ) ((0 : ℂ)) _ (by norm_num)
      (by simpa only [map_ofNat, map_one] using hmem)
  · change reducedQuotient r (mon 1 8 0 0) ∈ degreeNineLine r
    have hmem := fourRelationSum_mem r
      (degreeNineWitness31_0 r) (degreeNineWitness31_1 r)
      (degreeNineWitness31_2 r) (degreeNineWitness31_3 r)
    rw [← degreeNineCertificate31 r hr] at hmem
    exact class_mem_line_of_scaled_relation r (1 : ℂ) ((1 : ℂ)) _ (by norm_num)
      (by simpa only [map_ofNat, map_one] using hmem)

end CycleQ2SeedTrace

#print axioms CycleQ2SeedTrace.degreeNineMonomial_mem_line
end
end


/- Component: seed_trace/SparseSeedDegreeNine.lean -/
section
/-!
# The actual degree-nine quotient component has a unique normalized trace

Every degree-nine polynomial class is reduced using the concrete ideal
relations and finite polynomial membership certificates. The component is
then proved to be a nonzero line, and the previously constructed normalized
trace is proved unique on it.

This is a finite algebra theorem for the sparse seed. No smoothness or
geometric residue comparison is asserted.
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
noncomputable section
namespace CycleQ2SeedTrace
open MvPolynomial

theorem degreeNine_normal_complete_fin :
    ∀ a : Fin 2, ∀ b : Fin 10, ∀ c : Fin 4, ∀ d : Fin 10,
      a.val + b.val + c.val + d.val = 9 → (b.val < 2 ∨ d.val < 2) →
      ∃ i : Fin 32, degreeNineExponent i = ![a.val, b.val, c.val, d.val] := by
  intro a b c d
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> decide +kernel

theorem degreeNine_normal_complete (a b c d : ℕ)
    (ha : a < 2) (hc : c < 4) (hbd : b < 2 ∨ d < 2)
    (hdegree : a + b + c + d = 9) :
    ∃ i : Fin 32, degreeNineMonomial i = mon a b c d := by
  have hb : b < 10 := by omega
  have hd : d < 10 := by omega
  obtain ⟨i, hi⟩ := degreeNine_normal_complete_fin
    ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩ ⟨d, hd⟩ hdegree hbd
  exact ⟨i, by simp [degreeNineMonomial, hi]⟩

theorem degreeNine_mon_class_mem_line (r : ℂ) (hr : r ^ 3 = 2)
    (a b c d : ℕ) (hdegree : a + b + c + d = 9) :
    reducedQuotient r (mon a b c d) ∈ degreeNineLine r := by
  induction a using Nat.strong_induction_on generalizing b c d with
  | h a ih =>
      by_cases ha : a < 2
      · by_cases hc : c < 4
        · by_cases hbd : b < 2 ∨ d < 2
          · obtain ⟨i, hi⟩ := degreeNine_normal_complete a b c d ha hc hbd hdegree
            rw [← hi]
            exact degreeNineMonomial_mem_line r hr i
          · have hb : b = (b - 2) + 2 := by omega
            have hd : d = (d - 2) + 2 := by omega
            rw [hb, hd, quotient_mon_bd_add_two_zero]
            exact Submodule.zero_mem _
        · have hc' : c = (c - 4) + 4 := by omega
          rw [hc', quotient_mon_c_add_four_zero]
          exact Submodule.zero_mem _
      · have ha' : a = (a - 2) + 2 := by omega
        rw [ha', quotient_mon_add_two]
        apply Submodule.smul_mem
        exact ih (a - 2) (by omega) (b + 1) c (d + 1) (by omega)

theorem monomial_eq_C_mul_mon (d : Exp) (z : ℂ) :
    monomial d z = C z * mon (d 0) (d 1) (d 2) (d 3) := by
  rw [mon_eq_monomial, C_mul_monomial, mul_one]
  apply congrArg (fun e : Exp => monomial e z)
  ext i
  fin_cases i <;> rfl

theorem homogeneous_degreeNine_class_mem_line (r : ℂ) (hr : r ^ 3 = 2)
    {p : Poly} (hp : p.IsHomogeneous 9) :
    reducedQuotient r p ∈ degreeNineLine r := by
  induction hp using IsWeightedHomogeneous.induction_on with
  | zero => simpa only [map_zero] using (degreeNineLine r).zero_mem
  | add p q _ _ hp hq =>
      simpa only [map_add] using (degreeNineLine r).add_mem hp hq
  | monomial d z hd =>
      rw [monomial_eq_C_mul_mon, ← smul_eq_C_mul, map_smul]
      apply Submodule.smul_mem
      apply degreeNine_mon_class_mem_line r hr
      have hdegree : d.degree = 9 := by
        simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using hd
      rw [Finsupp.degree_eq_sum] at hdegree
      norm_num [Fin.sum_univ_succ] at hdegree
      rw [show (Fin.succ (2 : Fin 3) : Fin 4) = 3 from rfl] at hdegree
      omega

theorem degreeNinePiece_eq_line (r : ℂ) (hr : r ^ 3 = 2) :
    degreeNinePiece r = degreeNineLine r := by
  apply le_antisymm
  · rintro x ⟨p, hp, rfl⟩
    exact homogeneous_degreeNine_class_mem_line r hr hp
  · unfold degreeNineLine
    apply Submodule.span_le.mpr
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx]
    exact normalizationClass_mem_piece r

/-- The actual homogeneous degree-nine component of the ideal quotient is
one-dimensional. -/
theorem degreeNinePiece_finrank (r : ℂ) (hr : r ^ 3 = 2) :
    Module.finrank ℂ (degreeNinePiece r) = 1 := by
  rw [degreeNinePiece_eq_line r hr]
  exact finrank_span_singleton (normalizationClass_ne_zero r hr)

@[simp] theorem reducedTrace_normalizationClass (r : ℂ) (hr : r ^ 3 = 2) :
    reducedTrace r hr (normalizationClass r) = 1 := trace_normalized r hr

theorem degreeNine_class_eq_trace_smul (r : ℂ) (hr : r ^ 3 = 2)
    {x : ReducedAlgebra r} (hx : x ∈ degreeNinePiece r) :
    x = reducedTrace r hr x • normalizationClass r := by
  rw [degreeNinePiece_eq_line r hr] at hx
  obtain ⟨z, rfl⟩ := Submodule.mem_span_singleton.mp hx
  rw [map_smul, reducedTrace_normalizationClass, smul_eq_mul, mul_one]

/-- Uniform polynomial ideal-membership statement, beyond the finite list. -/
theorem homogeneous_degreeNine_mod_trace (r : ℂ) (hr : r ^ 3 = 2)
    {p : Poly} (hp : p.IsHomogeneous 9) :
    p - C (traceLinear r p) * mon 1 8 0 0 ∈ reducedIdeal r := by
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  change reducedQuotient r (p - C (traceLinear r p) * mon 1 8 0 0) = 0
  rw [map_sub, ← smul_eq_C_mul, map_smul, sub_eq_zero]
  exact degreeNine_class_eq_trace_smul r hr ⟨p, hp, rfl⟩

def degreeNineTrace (r : ℂ) (hr : r ^ 3 = 2) : degreeNinePiece r →ₗ[ℂ] ℂ :=
  (reducedTrace r hr).comp (degreeNinePiece r).subtype

def degreeNineNormalization (r : ℂ) : degreeNinePiece r :=
  ⟨normalizationClass r, normalizationClass_mem_piece r⟩

@[simp] theorem degreeNineTrace_normalized (r : ℂ) (hr : r ^ 3 = 2) :
    degreeNineTrace r hr (degreeNineNormalization r) = 1 := trace_normalized r hr

/-- Any complex-linear trace on this component with the stated normalization
is the constructed trace. No trace values remain as free input data. -/
theorem degreeNineTrace_unique (r : ℂ) (hr : r ^ 3 = 2)
    (τ : degreeNinePiece r →ₗ[ℂ] ℂ)
    (hτ : τ (degreeNineNormalization r) = 1) : τ = degreeNineTrace r hr := by
  ext x
  let c : ℂ := reducedTrace r hr (x : ReducedAlgebra r)
  have hx : x = c • degreeNineNormalization r := by
    apply Subtype.ext
    exact degreeNine_class_eq_trace_smul r hr x.property
  calc
    τ x = τ (c • degreeNineNormalization r) := congrArg τ hx
    _ = c := by rw [map_smul, hτ, smul_eq_mul, mul_one]
    _ = degreeNineTrace r hr x := rfl

end CycleQ2SeedTrace

#print axioms CycleQ2SeedTrace.degreeNinePiece_finrank
#print axioms CycleQ2SeedTrace.homogeneous_degreeNine_mod_trace
#print axioms CycleQ2SeedTrace.degreeNineTrace_unique
end
end
