import Proposal.GeometricFormalInputs02Part01

/-! Continuation of GeometricFormalInputs02.lean; complete source components and declarations. -/

set_option Elab.async false

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


