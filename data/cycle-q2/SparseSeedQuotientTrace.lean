import Proposal.GeometricSeed
import Proposal.GeometricSeedNormalIdeals
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.Tactic

/-! # Construction and evaluation of the sparse seed quotient trace -/

set_option Elab.async false

/- Component: seed_trace/SparseSeedTraceData.lean -/
section
/-!
# An actual quotient trace for the sparse seed

The finite trace is constructed as a coefficient of multiplication by an
explicit polynomial. Four polynomial annihilator identities prove that it
vanishes on the defining ideal, so it descends to the actual quotient.

This file concerns the sparse seed algebra. Its associated geometric surface
is singular; no smoothness or geometric trace comparison is asserted here.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

noncomputable section
namespace CycleQ2SeedTrace
open MvPolynomial

abbrev Exp := Fin 4 →₀ ℕ

def exponent (a : Fin 4 → ℕ) : Exp := Finsupp.equivFunOnFinite.symm a

@[simp] theorem exponent_apply (a : Fin 4 → ℕ) (i : Fin 4) : exponent a i = a i := rfl

def mon (a b c d : ℕ) : Poly := X 0 ^ a * X 1 ^ b * X 2 ^ c * X 3 ^ d

def topExponent : Exp := exponent ![3, 9, 3, 9]
def cutoff (i : Fin 4) : ℕ := topExponent i + 1
def truncationIdeal : Ideal Poly := Ideal.span (Set.range fun i : Fin 4 => X i ^ cutoff i)

def k : Poly := b + C Complex.I * (X 1 ^ 3 + X 3 ^ 3)


def traceNumerator (r : ℂ) : Poly :=
    C ((1 : ℂ)) * mon 3 9 3 0 +
    C ((1 : ℂ) * r ^ 2 * Complex.I + (-1 : ℂ) * r ^ 2) * mon 3 9 2 1 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I) * mon 3 8 1 3 +
    C ((-2 : ℂ) * r ^ 2) * mon 3 4 0 8 +
    C ((4 : ℂ)) * mon 3 3 0 9 +
    C ((4 : ℂ) * r ^ 2 * Complex.I + (-2 : ℂ) * r ^ 2) * mon 3 2 1 9 +
    C ((4 : ℂ) * r ^ 2 * Complex.I) * mon 3 1 3 8 +
    C ((-16 : ℂ) * Complex.I) * mon 3 0 3 9 +
    C ((1 : ℂ) * Complex.I + (-1 : ℂ)) * mon 2 9 2 2 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I) * mon 2 9 1 3 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I) * mon 2 8 3 2 +
    C ((1 : ℂ) * r ^ 2 * Complex.I + (1 : ℂ) * r ^ 2) * mon 2 8 0 5 +
    C ((-2 : ℂ) * r ^ 2 * Complex.I) * mon 2 5 0 8 +
    C ((4 : ℂ) * Complex.I) * mon 2 4 0 9 +
    C ((-2 : ℂ) * r ^ 2) * mon 2 3 1 9 +
    C ((-2 : ℂ) * r ^ 2) * mon 2 2 3 8 +
    C ((12 : ℂ)) * mon 2 1 3 9 +
    C ((-2 : ℂ) * Complex.I) * mon 1 9 1 4 +
    C ((-4 : ℂ)) * mon 1 5 0 9 +
    C ((8 : ℂ) * Complex.I) * mon 1 2 3 9 +
    C ((-2 : ℂ) * Complex.I) * mon 0 9 3 3 +
    C ((2 : ℂ) * Complex.I + (2 : ℂ)) * mon 0 9 0 6 +
    C ((-4 : ℂ) * Complex.I) * mon 0 6 0 9 +
    C ((-4 : ℂ)) * mon 0 3 3 9

def witness00 (r : ℂ) : Poly :=
    C ((1 : ℂ)) * mon 1 9 3 0 +
    C ((1 : ℂ) * r ^ 2 * Complex.I + (-1 : ℂ) * r ^ 2) * mon 1 9 2 1 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I) * mon 1 8 1 3 +
    C ((-2 : ℂ) * r ^ 2) * mon 1 4 0 8 +
    C ((4 : ℂ)) * mon 1 3 0 9 +
    C ((4 : ℂ) * r ^ 2 * Complex.I + (-2 : ℂ) * r ^ 2) * mon 1 2 1 9 +
    C ((4 : ℂ) * r ^ 2 * Complex.I) * mon 1 1 3 8 +
    C ((-16 : ℂ) * Complex.I) * mon 1 0 3 9 +
    C ((1 : ℂ) * Complex.I + (-1 : ℂ)) * mon 0 9 2 2 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I) * mon 0 9 1 3 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I) * mon 0 8 3 2 +
    C ((1 : ℂ) * r ^ 2 * Complex.I + (1 : ℂ) * r ^ 2) * mon 0 8 0 5 +
    C ((-2 : ℂ) * r ^ 2 * Complex.I) * mon 0 5 0 8 +
    C ((4 : ℂ) * Complex.I) * mon 0 4 0 9 +
    C ((-2 : ℂ) * r ^ 2) * mon 0 3 1 9 +
    C ((-2 : ℂ) * r ^ 2) * mon 0 2 3 8 +
    C ((12 : ℂ)) * mon 0 1 3 9

def witness01 (r : ℂ) : Poly :=
    C ((-1 : ℂ) * r) * mon 3 0 3 1 +
    C ((-2 : ℂ) * Complex.I + (2 : ℂ)) * mon 3 0 2 2 +
    C ((-1 : ℂ) * r * Complex.I + (1 : ℂ) * r) * mon 2 0 2 3 +
    C ((2 : ℂ) * Complex.I) * mon 2 0 1 4 +
    C ((2 : ℂ) * r * Complex.I) * mon 1 0 1 5 +
    C ((2 : ℂ) * r * Complex.I) * mon 0 0 3 4 +
    C ((-2 : ℂ) * r * Complex.I + (-2 : ℂ) * r) * mon 0 0 0 7

def witness02 (r : ℂ) : Poly :=
    0

def witness03 (r : ℂ) : Poly :=
    C ((-4 : ℂ) * r) * mon 3 4 0 0 +
    C ((-8 : ℂ) * Complex.I + (4 : ℂ)) * mon 3 3 1 0 +
    C ((16 : ℂ) * r * Complex.I) * mon 3 1 3 0 +
    C ((-4 : ℂ) * r * Complex.I) * mon 2 5 0 0 +
    C ((4 : ℂ)) * mon 2 4 1 0 +
    C ((-12 : ℂ) * r) * mon 2 2 3 0 +
    C ((4 : ℂ) * r) * mon 1 6 0 0 +
    C ((-8 : ℂ) * r * Complex.I) * mon 1 3 3 0 +
    C ((4 : ℂ) * r * Complex.I) * mon 0 7 0 0 +
    C ((4 : ℂ) * r) * mon 0 4 3 0

theorem annihilator0 (r : ℂ) (hr : r ^ 3 = 2) :
    traceNumerator r * relation r 0 =
      X 0 ^ 4 * witness00 r +
      X 1 ^ 10 * witness01 r +
      X 2 ^ 4 * witness02 r +
      X 3 ^ 10 * witness03 r := by
  have hr' : (C r : Poly) ^ 3 = 2 := by rw [← map_pow, hr, map_ofNat]
  have hi' : (C Complex.I : Poly) ^ 2 = -1 := by
    rw [← map_pow, Complex.I_sq, map_neg, map_one]
  norm_num only [traceNumerator, relation, b, h, mon,
    witness00, witness01, witness02, witness03,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
    map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_zero, map_one]
  ring_nf <;> (try simp only [hr', hi']) <;> ring

def witness10 (r : ℂ) : Poly :=
    0

def witness11 (r : ℂ) : Poly :=
    C ((1 : ℂ)) * mon 3 1 3 2 +
    C ((1 : ℂ) * r ^ 2 * Complex.I + (-1 : ℂ) * r ^ 2) * mon 3 1 2 3 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I) * mon 3 0 1 5 +
    C ((1 : ℂ) * Complex.I + (-1 : ℂ)) * mon 2 1 2 4 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I) * mon 2 1 1 5 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I) * mon 2 0 3 4 +
    C ((1 : ℂ) * r ^ 2 * Complex.I + (1 : ℂ) * r ^ 2) * mon 2 0 0 7 +
    C ((-2 : ℂ) * Complex.I) * mon 1 1 1 6 +
    C ((-2 : ℂ) * Complex.I) * mon 0 1 3 5 +
    C ((2 : ℂ) * Complex.I + (2 : ℂ)) * mon 0 1 0 8

def witness12 (r : ℂ) : Poly :=
    0

def witness13 (r : ℂ) : Poly :=
    C ((-2 : ℂ) * r ^ 2) * mon 3 6 0 0 +
    C ((4 : ℂ)) * mon 3 5 0 1 +
    C ((4 : ℂ) * r ^ 2 * Complex.I + (-2 : ℂ) * r ^ 2) * mon 3 4 1 1 +
    C ((4 : ℂ) * r ^ 2 * Complex.I) * mon 3 3 3 0 +
    C ((-16 : ℂ) * Complex.I) * mon 3 2 3 1 +
    C ((-2 : ℂ) * r ^ 2 * Complex.I) * mon 2 7 0 0 +
    C ((4 : ℂ) * Complex.I) * mon 2 6 0 1 +
    C ((-2 : ℂ) * r ^ 2) * mon 2 5 1 1 +
    C ((-2 : ℂ) * r ^ 2) * mon 2 4 3 0 +
    C ((12 : ℂ)) * mon 2 3 3 1 +
    C ((-4 : ℂ)) * mon 1 7 0 1 +
    C ((8 : ℂ) * Complex.I) * mon 1 4 3 1 +
    C ((-4 : ℂ) * Complex.I) * mon 0 8 0 1 +
    C ((-4 : ℂ)) * mon 0 5 3 1

theorem annihilator1 (r : ℂ) (hr : r ^ 3 = 2) :
    traceNumerator r * relation r 1 =
      X 0 ^ 4 * witness10 r +
      X 1 ^ 10 * witness11 r +
      X 2 ^ 4 * witness12 r +
      X 3 ^ 10 * witness13 r := by
  have hr' : (C r : Poly) ^ 3 = 2 := by rw [← map_pow, hr, map_ofNat]
  have hi' : (C Complex.I : Poly) ^ 2 = -1 := by
    rw [← map_pow, Complex.I_sq, map_neg, map_one]
  norm_num only [traceNumerator, relation, b, h, mon,
    witness10, witness11, witness12, witness13,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
    map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_zero, map_one]
  ring_nf <;> (try simp only [hr', hi']) <;> ring

def witness20 (r : ℂ) : Poly :=
    0

def witness21 (r : ℂ) : Poly :=
    0

def witness22 (r : ℂ) : Poly :=
    C ((1 : ℂ)) * mon 3 9 3 0 +
    C ((1 : ℂ) * r ^ 2 * Complex.I + (-1 : ℂ) * r ^ 2) * mon 3 9 2 1 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I) * mon 3 8 1 3 +
    C ((-2 : ℂ) * r ^ 2) * mon 3 4 0 8 +
    C ((4 : ℂ)) * mon 3 3 0 9 +
    C ((4 : ℂ) * r ^ 2 * Complex.I + (-2 : ℂ) * r ^ 2) * mon 3 2 1 9 +
    C ((4 : ℂ) * r ^ 2 * Complex.I) * mon 3 1 3 8 +
    C ((-16 : ℂ) * Complex.I) * mon 3 0 3 9 +
    C ((1 : ℂ) * Complex.I + (-1 : ℂ)) * mon 2 9 2 2 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I) * mon 2 9 1 3 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I) * mon 2 8 3 2 +
    C ((1 : ℂ) * r ^ 2 * Complex.I + (1 : ℂ) * r ^ 2) * mon 2 8 0 5 +
    C ((-2 : ℂ) * r ^ 2 * Complex.I) * mon 2 5 0 8 +
    C ((4 : ℂ) * Complex.I) * mon 2 4 0 9 +
    C ((-2 : ℂ) * r ^ 2) * mon 2 3 1 9 +
    C ((-2 : ℂ) * r ^ 2) * mon 2 2 3 8 +
    C ((12 : ℂ)) * mon 2 1 3 9 +
    C ((-2 : ℂ) * Complex.I) * mon 1 9 1 4 +
    C ((-4 : ℂ)) * mon 1 5 0 9 +
    C ((8 : ℂ) * Complex.I) * mon 1 2 3 9 +
    C ((-2 : ℂ) * Complex.I) * mon 0 9 3 3 +
    C ((2 : ℂ) * Complex.I + (2 : ℂ)) * mon 0 9 0 6 +
    C ((-4 : ℂ) * Complex.I) * mon 0 6 0 9 +
    C ((-4 : ℂ)) * mon 0 3 3 9

def witness23 (r : ℂ) : Poly :=
    0

theorem annihilator2 (r : ℂ) (hr : r ^ 3 = 2) :
    traceNumerator r * relation r 2 =
      X 0 ^ 4 * witness20 r +
      X 1 ^ 10 * witness21 r +
      X 2 ^ 4 * witness22 r +
      X 3 ^ 10 * witness23 r := by
  have hr' : (C r : Poly) ^ 3 = 2 := by rw [← map_pow, hr, map_ofNat]
  have hi' : (C Complex.I : Poly) ^ 2 = -1 := by
    rw [← map_pow, Complex.I_sq, map_neg, map_one]
  norm_num only [traceNumerator, relation, b, h, mon,
    witness20, witness21, witness22, witness23,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
    map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_zero, map_one]
  ring_nf <;> (try simp only [hr', hi']) <;> ring

def witness30 (r : ℂ) : Poly :=
    C ((1 : ℂ)) * mon 0 11 3 0 +
    C ((1 : ℂ) * r ^ 2 * Complex.I + (-1 : ℂ) * r ^ 2) * mon 0 11 2 1 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I) * mon 0 10 1 3 +
    C ((1 : ℂ)) * mon 0 9 4 1 +
    C ((1 : ℂ) * r ^ 2 * Complex.I + (-1 : ℂ) * r ^ 2) * mon 0 9 3 2 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I) * mon 0 8 2 4 +
    C ((-2 : ℂ) * r ^ 2) * mon 0 6 0 8 +
    C ((4 : ℂ)) * mon 0 5 0 9 +
    C ((4 : ℂ) * r ^ 2 * Complex.I + (-4 : ℂ) * r ^ 2) * mon 0 4 1 9 +
    C ((4 : ℂ) * r ^ 2 * Complex.I) * mon 0 3 3 8 +
    C ((4 : ℂ)) * mon 0 3 1 10 +
    C ((-16 : ℂ) * Complex.I) * mon 0 2 3 9 +
    C ((4 : ℂ) * r ^ 2 * Complex.I + (-2 : ℂ) * r ^ 2) * mon 0 2 2 10 +
    C ((4 : ℂ) * r ^ 2 * Complex.I) * mon 0 1 4 9 +
    C ((-16 : ℂ) * Complex.I) * mon 0 0 4 10

def witness31 (r : ℂ) : Poly :=
    C ((-1 : ℂ) * Complex.I) * mon 3 2 3 0 +
    C ((1 : ℂ) * r ^ 2 * Complex.I + (1 : ℂ) * r ^ 2) * mon 3 2 2 1 +
    C ((1 : ℂ) * Complex.I + (-1 : ℂ)) * mon 3 1 2 2 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I + (-1 : ℂ) * r ^ 2) * mon 3 1 1 3 +
    C ((1 : ℂ)) * mon 3 0 4 1 +
    C ((-1 : ℂ) * r ^ 2) * mon 3 0 3 2 +
    C ((1 : ℂ) * r ^ 2 * Complex.I + (1 : ℂ) * r ^ 2) * mon 3 0 0 5 +
    C ((1 : ℂ) * Complex.I + (1 : ℂ)) * mon 2 2 2 2 +
    C ((-1 : ℂ) * r ^ 2) * mon 2 2 1 3 +
    C ((-1 : ℂ) * r ^ 2) * mon 2 1 3 2 +
    C ((-2 : ℂ) * Complex.I) * mon 2 1 1 4 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I + (1 : ℂ) * r ^ 2) * mon 2 1 0 5 +
    C ((1 : ℂ) * Complex.I + (-1 : ℂ)) * mon 2 0 3 3 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I) * mon 2 0 2 4 +
    C ((-2 : ℂ)) * mon 1 2 1 4 +
    C ((-2 : ℂ) * Complex.I) * mon 1 1 3 3 +
    C ((2 : ℂ) * Complex.I + (2 : ℂ)) * mon 1 1 0 6 +
    C ((-2 : ℂ) * Complex.I) * mon 1 0 2 5 +
    C ((-2 : ℂ)) * mon 0 2 3 3 +
    C ((-2 : ℂ) * Complex.I + (2 : ℂ)) * mon 0 2 0 6 +
    C ((-2 : ℂ) * Complex.I) * mon 0 0 4 4 +
    C ((2 : ℂ) * Complex.I + (2 : ℂ)) * mon 0 0 1 7

def witness32 (r : ℂ) : Poly :=
    C ((1 : ℂ)) * mon 3 9 2 0 +
    C ((1 : ℂ) * r ^ 2 * Complex.I + (-1 : ℂ) * r ^ 2) * mon 3 9 1 1 +
    C ((-2 : ℂ) * r ^ 2 * Complex.I) * mon 3 8 0 3 +
    C ((8 : ℂ) * r ^ 2 * Complex.I + (-4 : ℂ) * r ^ 2) * mon 3 2 0 9 +
    C ((4 : ℂ) * r ^ 2 * Complex.I) * mon 3 1 2 8 +
    C ((-16 : ℂ) * Complex.I + (12 : ℂ)) * mon 3 1 0 10 +
    C ((-16 : ℂ) * Complex.I) * mon 3 0 2 9 +
    C ((1 : ℂ) * Complex.I + (-1 : ℂ)) * mon 2 9 1 2 +
    C ((-2 : ℂ) * r ^ 2 * Complex.I) * mon 2 9 0 3 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I) * mon 2 8 2 2 +
    C ((-4 : ℂ) * r ^ 2) * mon 2 3 0 9 +
    C ((-2 : ℂ) * r ^ 2) * mon 2 2 2 8 +
    C ((8 : ℂ) * Complex.I + (12 : ℂ)) * mon 2 2 0 10 +
    C ((12 : ℂ)) * mon 2 1 2 9 +
    C ((-4 : ℂ) * Complex.I) * mon 1 9 0 4 +
    C ((8 : ℂ) * Complex.I + (-4 : ℂ)) * mon 1 3 0 10 +
    C ((8 : ℂ) * Complex.I) * mon 1 2 2 9 +
    C ((-2 : ℂ) * Complex.I) * mon 0 9 2 3 +
    C ((-4 : ℂ)) * mon 0 4 0 10 +
    C ((-4 : ℂ)) * mon 0 3 2 9

def witness33 (r : ℂ) : Poly :=
    C ((4 : ℂ) * Complex.I + (4 : ℂ)) * mon 3 4 1 0 +
    C ((2 : ℂ) * r ^ 2 * Complex.I + (-2 : ℂ) * r ^ 2) * mon 3 4 0 1 +
    C ((4 : ℂ) * r ^ 2 * Complex.I + (-4 : ℂ) * r ^ 2) * mon 3 3 2 0 +
    C ((-4 : ℂ) * Complex.I + (4 : ℂ)) * mon 3 3 0 2 +
    C ((6 : ℂ) * r ^ 2 * Complex.I + (2 : ℂ) * r ^ 2) * mon 3 2 1 2 +
    C ((4 : ℂ) * r ^ 2 * Complex.I + (4 : ℂ) * r ^ 2) * mon 3 1 3 1 +
    C ((-16 : ℂ) * Complex.I + (-16 : ℂ)) * mon 3 0 3 2 +
    C ((4 : ℂ) * Complex.I + (-4 : ℂ)) * mon 2 5 1 0 +
    C ((-2 : ℂ) * r ^ 2 * Complex.I + (-2 : ℂ) * r ^ 2) * mon 2 5 0 1 +
    C ((-2 : ℂ) * r ^ 2) * mon 2 4 2 0 +
    C ((4 : ℂ) * Complex.I + (4 : ℂ)) * mon 2 4 0 2 +
    C ((2 : ℂ) * r ^ 2 * Complex.I + (-2 : ℂ) * r ^ 2) * mon 2 3 1 2 +
    C ((2 : ℂ) * r ^ 2 * Complex.I + (-2 : ℂ) * r ^ 2) * mon 2 2 3 1 +
    C ((-12 : ℂ) * Complex.I + (12 : ℂ)) * mon 2 1 3 2 +
    C ((-4 : ℂ) * Complex.I + (-4 : ℂ)) * mon 1 6 1 0 +
    C ((4 : ℂ) * Complex.I + (-4 : ℂ)) * mon 1 5 0 2 +
    C ((8 : ℂ) * Complex.I + (8 : ℂ)) * mon 1 2 3 2 +
    C ((-4 : ℂ) * Complex.I) * mon 0 7 1 0 +
    C ((-4 : ℂ) * Complex.I + (-4 : ℂ)) * mon 0 6 0 2 +
    C ((4 : ℂ) * Complex.I + (-4 : ℂ)) * mon 0 3 3 2

theorem annihilator3 (r : ℂ) (hr : r ^ 3 = 2) :
    traceNumerator r * relation r 3 =
      X 0 ^ 4 * witness30 r +
      X 1 ^ 10 * witness31 r +
      X 2 ^ 4 * witness32 r +
      X 3 ^ 10 * witness33 r := by
  have hr' : (C r : Poly) ^ 3 = 2 := by rw [← map_pow, hr, map_ofNat]
  have hi' : (C Complex.I : Poly) ^ 2 = -1 := by
    rw [← map_pow, Complex.I_sq, map_neg, map_one]
  norm_num only [traceNumerator, relation, b, h, mon,
    witness30, witness31, witness32, witness33,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
    map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_zero, map_one]
  ring_nf <;> (try simp only [hr', hi']) <;> ring

end CycleQ2SeedTrace

#print axioms CycleQ2SeedTrace.annihilator0
#print axioms CycleQ2SeedTrace.annihilator1
#print axioms CycleQ2SeedTrace.annihilator2
#print axioms CycleQ2SeedTrace.annihilator3
end
end


/- Component: seed_trace/SparseSeedTrace.lean -/
section
/-!
# Descent of the constructed sparse trace to the actual ideal quotient

The polynomial annihilator certificates prove the trace vanishes on every
multiple of every defining relation, not just on selected finite products.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

noncomputable section
namespace CycleQ2SeedTrace
open MvPolynomial

theorem truncationIdeal_eq_monomials : truncationIdeal =
    Ideal.span ((fun d : Exp => monomial d (1 : ℂ)) ''
      Set.range (fun i : Fin 4 => Finsupp.single i (cutoff i))) := by
  unfold truncationIdeal
  congr 1
  ext p
  simp only [Set.mem_range, Set.mem_image, X_pow_eq_monomial]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨_, ⟨i, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, rfl⟩

theorem top_coeff_zero_of_mem {p : Poly} (hp : p ∈ truncationIdeal) :
    coeff topExponent p = 0 := by
  rw [truncationIdeal_eq_monomials, mem_ideal_span_monomial_image] at hp
  by_contra hc
  obtain ⟨_, ⟨i, rfl⟩, hi⟩ := hp topExponent (mem_support_iff.mpr hc)
  have h := Finsupp.single_le_iff.mp hi
  change topExponent i + 1 ≤ topExponent i at h
  omega

theorem fourTerm_mem_truncation (a b c d : Poly) :
    X 0 ^ 4 * a + X 1 ^ 10 * b + X 2 ^ 4 * c + X 3 ^ 10 * d ∈
      truncationIdeal := by
  have hg (i : Fin 4) : X i ^ cutoff i ∈ truncationIdeal :=
    Ideal.subset_span ⟨i, rfl⟩
  exact Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _
    (Ideal.mul_mem_right a _ (hg 0)) (Ideal.mul_mem_right b _ (hg 1)))
    (Ideal.mul_mem_right c _ (hg 2))) (Ideal.mul_mem_right d _ (hg 3))

theorem annihilator_generators_mem (r : ℂ) (hr : r ^ 3 = 2) (i : Fin 4) :
    traceNumerator r * relation r i ∈ truncationIdeal := by
  fin_cases i
  · change traceNumerator r * relation r 0 ∈ truncationIdeal
    rw [annihilator0 r hr]
    exact fourTerm_mem_truncation _ _ _ _
  · change traceNumerator r * relation r 1 ∈ truncationIdeal
    rw [annihilator1 r hr]
    exact fourTerm_mem_truncation _ _ _ _
  · change traceNumerator r * relation r 2 ∈ truncationIdeal
    rw [annihilator2 r hr]
    exact fourTerm_mem_truncation _ _ _ _
  · change traceNumerator r * relation r 3 ∈ truncationIdeal
    rw [annihilator3 r hr]
    exact fourTerm_mem_truncation _ _ _ _

theorem traceNumerator_mul_mem (r : ℂ) (hr : r ^ 3 = 2)
    {p : Poly} (hp : p ∈ reducedIdeal r) :
    traceNumerator r * p ∈ truncationIdeal := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
      obtain ⟨i, rfl⟩ := hp
      exact annihilator_generators_mem r hr i
  | zero => simp
  | add p q _ _ hp hq =>
      simpa only [mul_add] using Ideal.add_mem truncationIdeal hp hq
  | smul a p _ hp =>
      simpa only [smul_eq_mul, mul_left_comm] using
        Ideal.mul_mem_left truncationIdeal a hp

def traceLinear (r : ℂ) : Poly →ₗ[ℂ] ℂ :=
  ((1 / 12 : ℂ) • lcoeff ℂ topExponent).comp
    (LinearMap.mul ℂ Poly (traceNumerator r))

@[simp] theorem traceLinear_apply (r : ℂ) (p : Poly) :
    traceLinear r p = (1 / 12 : ℂ) * coeff topExponent (traceNumerator r * p) := rfl

theorem traceLinear_zero_of_mem (r : ℂ) (hr : r ^ 3 = 2)
    {p : Poly} (hp : p ∈ reducedIdeal r) : traceLinear r p = 0 := by
  rw [traceLinear_apply, top_coeff_zero_of_mem (traceNumerator_mul_mem r hr hp), mul_zero]

abbrev ReducedAlgebra (r : ℂ) := Poly ⧸ reducedIdeal r

def reducedQuotient (r : ℂ) : Poly →ₐ[ℂ] ReducedAlgebra r :=
  Ideal.Quotient.mkₐ ℂ (reducedIdeal r)

/-- The normalized coefficient functional genuinely descends to the quotient. -/
def reducedTrace (r : ℂ) (hr : r ^ 3 = 2) : ReducedAlgebra r →ₗ[ℂ] ℂ :=
  ((reducedIdeal r).restrictScalars ℂ).liftQ (traceLinear r) (by
    intro p hp
    exact traceLinear_zero_of_mem r hr hp)

@[simp] theorem reducedTrace_mk (r : ℂ) (hr : r ^ 3 = 2) (p : Poly) :
    reducedTrace r hr (reducedQuotient r p) = traceLinear r p := rfl

theorem mon_eq_monomial (a b c d : ℕ) :
    mon a b c d = monomial (exponent ![a, b, c, d]) 1 := by
  simp only [mon, X_pow_eq_monomial, monomial_mul, one_mul]
  apply congrArg (fun e : Exp => monomial e (1 : ℂ))
  ext i
  fin_cases i <;> simp [exponent, Finsupp.single_apply, Fin.ext_iff]

theorem mon_mul (a b c d e f g h : ℕ) :
    mon a b c d * mon e f g h = mon (a+e) (b+f) (c+g) (d+h) := by
  simp only [mon, pow_add]
  ring

theorem coeff_top_mon (a b c d : ℕ) :
    coeff topExponent (mon a b c d) =
      if a = 3 ∧ b = 9 ∧ c = 3 ∧ d = 9 then 1 else 0 := by
  rw [mon_eq_monomial, coeff_monomial]
  congr 1
  apply propext
  constructor
  · intro h
    exact ⟨congrArg (fun e : Exp => e 0) h, congrArg (fun e : Exp => e 1) h,
      congrArg (fun e : Exp => e 2) h, congrArg (fun e : Exp => e 3) h⟩
  · rintro ⟨rfl, rfl, rfl, rfl⟩
    rfl

theorem trace_normalized (r : ℂ) (hr : r ^ 3 = 2) :
    reducedTrace r hr (reducedQuotient r (mon 1 8 0 0)) = 1 := by
  rw [reducedTrace_mk, traceLinear_apply]
  simp only [traceNumerator, add_mul, mul_assoc, mon_mul, coeff_add, coeff_C_mul,
    coeff_top_mon]
  norm_num

end CycleQ2SeedTrace

#print axioms CycleQ2SeedTrace.traceLinear_zero_of_mem
#print axioms CycleQ2SeedTrace.reducedTrace
#print axioms CycleQ2SeedTrace.trace_normalized
end
end


/- Component: seed_trace/SparseSeedOriginal.lean -/
section
/-!
# The trace on the original five-variable seed algebra

This uses the actual five relations f1,g1,f2,g2,h from the sparse seed.
Substitution w=-x2^2 sends their ideal into the four-variable ideal on which
the coefficient functional has already been proved to vanish.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

noncomputable section
namespace CycleQ2SeedTrace
open MvPolynomial


def seedEquation : WeightedPoly :=
  X 0 ^ 6 + X 1 ^ 6 + X 2 ^ 6 + X 3 ^ 6 + X 4 ^ 3 + originalB ^ 2

theorem seedEquation_decomposition (r : ℂ) (hr : r ^ 3 = 2) :
    seedEquation = originalF1 r * originalG1 r + originalF2 * originalG2 +
      originalH * originalK := by
  have hr' : (C r : WeightedPoly) ^ 3 = 2 := by rw [← map_pow, hr, map_ofNat]
  have hi' : (C Complex.I : WeightedPoly) ^ 2 = -1 := by
    rw [← map_pow, Complex.I_sq, map_neg, map_one]
  simp only [seedEquation, originalF1, originalG1, originalF2, originalG2,
    originalH, originalK, map_pow]
  ring_nf
  rw [hr', hi']
  ring

def originalRelations (r : ℂ) : Fin 5 → WeightedPoly :=
  ![originalF1 r, originalG1 r, originalF2, originalG2, originalH]

def originalIdeal (r : ℂ) : Ideal WeightedPoly := Ideal.span (Set.range (originalRelations r))


theorem substitute_relations (r : ℂ) (i : Fin 5) :
    substitute (originalRelations r i) =
      ![relation r 0,
        relation r 0 * (X 0 ^ 2 + C (2 * r) * X 1 * X 3) +
          C (3 * r ^ 2) * relation r 1,
        0,
        3 * relation r 2,
        relation r 3] i := by
  fin_cases i <;>
    norm_num [substitute, originalRelations, originalF1, originalG1, originalF2,
      originalG2, originalH, originalB, relation, b, h, map_pow, map_mul, map_ofNat,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons] <;> ring

theorem substitute_relations_mem (r : ℂ) (i : Fin 5) :
    substitute (originalRelations r i) ∈ reducedIdeal r := by
  have hg (j : Fin 4) : relation r j ∈ reducedIdeal r := Ideal.subset_span ⟨j, rfl⟩
  rw [substitute_relations]
  fin_cases i
  · exact hg 0
  · exact Ideal.add_mem _
      (Ideal.mul_mem_right _ _ (hg 0)) (Ideal.mul_mem_left _ _ (hg 1))
  · exact Ideal.zero_mem _
  · exact Ideal.mul_mem_left _ _ (hg 2)
  · exact hg 3

theorem substitute_mem_reduced (r : ℂ) {p : WeightedPoly} (hp : p ∈ originalIdeal r) :
    substitute p ∈ reducedIdeal r := by
  have hle : originalIdeal r ≤ Ideal.comap substitute.toRingHom (reducedIdeal r) := by
    rw [originalIdeal, Ideal.span_le]
    rintro p ⟨i, rfl⟩
    exact substitute_relations_mem r i
  exact hle hp

def originalTraceLinear (r : ℂ) : WeightedPoly →ₗ[ℂ] ℂ :=
  (traceLinear r).comp substitute.toLinearMap

theorem originalTraceLinear_zero_of_mem (r : ℂ) (hr : r ^ 3 = 2)
    {p : WeightedPoly} (hp : p ∈ originalIdeal r) : originalTraceLinear r p = 0 :=
  traceLinear_zero_of_mem r hr (substitute_mem_reduced r hp)

abbrev SeedAlgebra (r : ℂ) := WeightedPoly ⧸ originalIdeal r

def seedQuotient (r : ℂ) : WeightedPoly →ₐ[ℂ] SeedAlgebra r :=
  Ideal.Quotient.mkₐ ℂ (originalIdeal r)

/-- The constructed functional on the actual original seed ideal quotient. -/
def seedTrace (r : ℂ) (hr : r ^ 3 = 2) : SeedAlgebra r →ₗ[ℂ] ℂ :=
  ((originalIdeal r).restrictScalars ℂ).liftQ (originalTraceLinear r) (by
    intro p hp
    exact originalTraceLinear_zero_of_mem r hr hp)

@[simp] theorem seedTrace_mk (r : ℂ) (hr : r ^ 3 = 2) (p : WeightedPoly) :
    seedTrace r hr (seedQuotient r p) = traceLinear r (substitute p) := rfl

theorem seedTrace_normalized (r : ℂ) (hr : r ^ 3 = 2) :
    seedTrace r hr (seedQuotient r (X 0 * X 1 ^ 8)) = 1 := by
  rw [seedTrace_mk]
  have heq : substitute (X 0 * X 1 ^ 8) = mon 1 8 0 0 := by
    simp [substitute, mon]
  rw [heq]
  exact trace_normalized r hr

end CycleQ2SeedTrace

#print axioms CycleQ2SeedTrace.seedEquation_decomposition
#print axioms CycleQ2SeedTrace.seedTrace
#print axioms CycleQ2SeedTrace.seedTrace_normalized
end
end


/- Component: seed_trace/SparseSeedEvaluation.lean -/
section
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace CycleQ2SeedTrace
open MvPolynomial

private theorem shiftTest0 (a b c d : ℕ) :
    (3 + a = 3 ∧ 9 + b = 9 ∧ 3 + c = 3 ∧ 0 + d = 9) ↔ (a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 9) := by omega

private theorem shiftTest1 (a b c d : ℕ) :
    (3 + a = 3 ∧ 9 + b = 9 ∧ 2 + c = 3 ∧ 1 + d = 9) ↔ (a = 0 ∧ b = 0 ∧ c = 1 ∧ d = 8) := by omega

private theorem shiftTest2 (a b c d : ℕ) :
    (3 + a = 3 ∧ 8 + b = 9 ∧ 1 + c = 3 ∧ 3 + d = 9) ↔ (a = 0 ∧ b = 1 ∧ c = 2 ∧ d = 6) := by omega

private theorem shiftTest3 (a b c d : ℕ) :
    (3 + a = 3 ∧ 4 + b = 9 ∧ 0 + c = 3 ∧ 8 + d = 9) ↔ (a = 0 ∧ b = 5 ∧ c = 3 ∧ d = 1) := by omega

private theorem shiftTest4 (a b c d : ℕ) :
    (3 + a = 3 ∧ 3 + b = 9 ∧ 0 + c = 3 ∧ 9 + d = 9) ↔ (a = 0 ∧ b = 6 ∧ c = 3 ∧ d = 0) := by omega

private theorem shiftTest5 (a b c d : ℕ) :
    (3 + a = 3 ∧ 2 + b = 9 ∧ 1 + c = 3 ∧ 9 + d = 9) ↔ (a = 0 ∧ b = 7 ∧ c = 2 ∧ d = 0) := by omega

private theorem shiftTest6 (a b c d : ℕ) :
    (3 + a = 3 ∧ 1 + b = 9 ∧ 3 + c = 3 ∧ 8 + d = 9) ↔ (a = 0 ∧ b = 8 ∧ c = 0 ∧ d = 1) := by omega

private theorem shiftTest7 (a b c d : ℕ) :
    (3 + a = 3 ∧ 0 + b = 9 ∧ 3 + c = 3 ∧ 9 + d = 9) ↔ (a = 0 ∧ b = 9 ∧ c = 0 ∧ d = 0) := by omega

private theorem shiftTest8 (a b c d : ℕ) :
    (2 + a = 3 ∧ 9 + b = 9 ∧ 2 + c = 3 ∧ 2 + d = 9) ↔ (a = 1 ∧ b = 0 ∧ c = 1 ∧ d = 7) := by omega

private theorem shiftTest9 (a b c d : ℕ) :
    (2 + a = 3 ∧ 9 + b = 9 ∧ 1 + c = 3 ∧ 3 + d = 9) ↔ (a = 1 ∧ b = 0 ∧ c = 2 ∧ d = 6) := by omega

private theorem shiftTest10 (a b c d : ℕ) :
    (2 + a = 3 ∧ 8 + b = 9 ∧ 3 + c = 3 ∧ 2 + d = 9) ↔ (a = 1 ∧ b = 1 ∧ c = 0 ∧ d = 7) := by omega

private theorem shiftTest11 (a b c d : ℕ) :
    (2 + a = 3 ∧ 8 + b = 9 ∧ 0 + c = 3 ∧ 5 + d = 9) ↔ (a = 1 ∧ b = 1 ∧ c = 3 ∧ d = 4) := by omega

private theorem shiftTest12 (a b c d : ℕ) :
    (2 + a = 3 ∧ 5 + b = 9 ∧ 0 + c = 3 ∧ 8 + d = 9) ↔ (a = 1 ∧ b = 4 ∧ c = 3 ∧ d = 1) := by omega

private theorem shiftTest13 (a b c d : ℕ) :
    (2 + a = 3 ∧ 4 + b = 9 ∧ 0 + c = 3 ∧ 9 + d = 9) ↔ (a = 1 ∧ b = 5 ∧ c = 3 ∧ d = 0) := by omega

private theorem shiftTest14 (a b c d : ℕ) :
    (2 + a = 3 ∧ 3 + b = 9 ∧ 1 + c = 3 ∧ 9 + d = 9) ↔ (a = 1 ∧ b = 6 ∧ c = 2 ∧ d = 0) := by omega

private theorem shiftTest15 (a b c d : ℕ) :
    (2 + a = 3 ∧ 2 + b = 9 ∧ 3 + c = 3 ∧ 8 + d = 9) ↔ (a = 1 ∧ b = 7 ∧ c = 0 ∧ d = 1) := by omega

private theorem shiftTest16 (a b c d : ℕ) :
    (2 + a = 3 ∧ 1 + b = 9 ∧ 3 + c = 3 ∧ 9 + d = 9) ↔ (a = 1 ∧ b = 8 ∧ c = 0 ∧ d = 0) := by omega

private theorem shiftTest17 (a b c d : ℕ) :
    (1 + a = 3 ∧ 9 + b = 9 ∧ 1 + c = 3 ∧ 4 + d = 9) ↔ (a = 2 ∧ b = 0 ∧ c = 2 ∧ d = 5) := by omega

private theorem shiftTest18 (a b c d : ℕ) :
    (1 + a = 3 ∧ 5 + b = 9 ∧ 0 + c = 3 ∧ 9 + d = 9) ↔ (a = 2 ∧ b = 4 ∧ c = 3 ∧ d = 0) := by omega

private theorem shiftTest19 (a b c d : ℕ) :
    (1 + a = 3 ∧ 2 + b = 9 ∧ 3 + c = 3 ∧ 9 + d = 9) ↔ (a = 2 ∧ b = 7 ∧ c = 0 ∧ d = 0) := by omega

private theorem shiftTest20 (a b c d : ℕ) :
    (0 + a = 3 ∧ 9 + b = 9 ∧ 3 + c = 3 ∧ 3 + d = 9) ↔ (a = 3 ∧ b = 0 ∧ c = 0 ∧ d = 6) := by omega

private theorem shiftTest21 (a b c d : ℕ) :
    (0 + a = 3 ∧ 9 + b = 9 ∧ 0 + c = 3 ∧ 6 + d = 9) ↔ (a = 3 ∧ b = 0 ∧ c = 3 ∧ d = 3) := by omega

private theorem shiftTest22 (a b c d : ℕ) :
    (0 + a = 3 ∧ 6 + b = 9 ∧ 0 + c = 3 ∧ 9 + d = 9) ↔ (a = 3 ∧ b = 3 ∧ c = 3 ∧ d = 0) := by omega

private theorem shiftTest23 (a b c d : ℕ) :
    (0 + a = 3 ∧ 3 + b = 9 ∧ 3 + c = 3 ∧ 9 + d = 9) ↔ (a = 3 ∧ b = 6 ∧ c = 0 ∧ d = 0) := by omega

def traceValue (r : ℂ) (a b c d : ℕ) : ℂ :=
  (1 / 12) * (((1 : ℂ)) * (if a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 9 then 1 else 0) +
    ((1 : ℂ) * r ^ 2 * Complex.I + (-1 : ℂ) * r ^ 2) * (if a = 0 ∧ b = 0 ∧ c = 1 ∧ d = 8 then 1 else 0) +
    ((-1 : ℂ) * r ^ 2 * Complex.I) * (if a = 0 ∧ b = 1 ∧ c = 2 ∧ d = 6 then 1 else 0) +
    ((-2 : ℂ) * r ^ 2) * (if a = 0 ∧ b = 5 ∧ c = 3 ∧ d = 1 then 1 else 0) +
    ((4 : ℂ)) * (if a = 0 ∧ b = 6 ∧ c = 3 ∧ d = 0 then 1 else 0) +
    ((4 : ℂ) * r ^ 2 * Complex.I + (-2 : ℂ) * r ^ 2) * (if a = 0 ∧ b = 7 ∧ c = 2 ∧ d = 0 then 1 else 0) +
    ((4 : ℂ) * r ^ 2 * Complex.I) * (if a = 0 ∧ b = 8 ∧ c = 0 ∧ d = 1 then 1 else 0) +
    ((-16 : ℂ) * Complex.I) * (if a = 0 ∧ b = 9 ∧ c = 0 ∧ d = 0 then 1 else 0) +
    ((1 : ℂ) * Complex.I + (-1 : ℂ)) * (if a = 1 ∧ b = 0 ∧ c = 1 ∧ d = 7 then 1 else 0) +
    ((-1 : ℂ) * r ^ 2 * Complex.I) * (if a = 1 ∧ b = 0 ∧ c = 2 ∧ d = 6 then 1 else 0) +
    ((-1 : ℂ) * r ^ 2 * Complex.I) * (if a = 1 ∧ b = 1 ∧ c = 0 ∧ d = 7 then 1 else 0) +
    ((1 : ℂ) * r ^ 2 * Complex.I + (1 : ℂ) * r ^ 2) * (if a = 1 ∧ b = 1 ∧ c = 3 ∧ d = 4 then 1 else 0) +
    ((-2 : ℂ) * r ^ 2 * Complex.I) * (if a = 1 ∧ b = 4 ∧ c = 3 ∧ d = 1 then 1 else 0) +
    ((4 : ℂ) * Complex.I) * (if a = 1 ∧ b = 5 ∧ c = 3 ∧ d = 0 then 1 else 0) +
    ((-2 : ℂ) * r ^ 2) * (if a = 1 ∧ b = 6 ∧ c = 2 ∧ d = 0 then 1 else 0) +
    ((-2 : ℂ) * r ^ 2) * (if a = 1 ∧ b = 7 ∧ c = 0 ∧ d = 1 then 1 else 0) +
    ((12 : ℂ)) * (if a = 1 ∧ b = 8 ∧ c = 0 ∧ d = 0 then 1 else 0) +
    ((-2 : ℂ) * Complex.I) * (if a = 2 ∧ b = 0 ∧ c = 2 ∧ d = 5 then 1 else 0) +
    ((-4 : ℂ)) * (if a = 2 ∧ b = 4 ∧ c = 3 ∧ d = 0 then 1 else 0) +
    ((8 : ℂ) * Complex.I) * (if a = 2 ∧ b = 7 ∧ c = 0 ∧ d = 0 then 1 else 0) +
    ((-2 : ℂ) * Complex.I) * (if a = 3 ∧ b = 0 ∧ c = 0 ∧ d = 6 then 1 else 0) +
    ((2 : ℂ) * Complex.I + (2 : ℂ)) * (if a = 3 ∧ b = 0 ∧ c = 3 ∧ d = 3 then 1 else 0) +
    ((-4 : ℂ) * Complex.I) * (if a = 3 ∧ b = 3 ∧ c = 3 ∧ d = 0 then 1 else 0) +
    ((-4 : ℂ)) * (if a = 3 ∧ b = 6 ∧ c = 0 ∧ d = 0 then 1 else 0))

theorem traceLinear_mon (r : ℂ) (a b c d : ℕ) :
    traceLinear r (mon a b c d) = traceValue r a b c d := by
  simp only [traceLinear_apply, traceNumerator, add_mul, mul_assoc, mon_mul,
    coeff_add, coeff_C_mul, coeff_top_mon, traceValue,
    shiftTest0, shiftTest1, shiftTest2, shiftTest3, shiftTest4, shiftTest5, shiftTest6, shiftTest7, shiftTest8, shiftTest9, shiftTest10, shiftTest11, shiftTest12, shiftTest13, shiftTest14, shiftTest15, shiftTest16, shiftTest17, shiftTest18, shiftTest19, shiftTest20, shiftTest21, shiftTest22, shiftTest23]

theorem traceLinear_C_mul (r z : ℂ) (p : Poly) :
    traceLinear r (C z * p) = z * traceLinear r p := by
  simpa only [smul_eq_C_mul, smul_eq_mul] using (traceLinear r).map_smul z p

end CycleQ2SeedTrace

#print axioms CycleQ2SeedTrace.traceLinear_mon
end
end


/- Component: seed_trace/SparseSeedMatrix.lean -/
section
/-!
# Binding the sparse seed matrix to the constructed quotient trace

All entries are evaluated from the coefficient functional whose descent to
the original quotient has been proved. The geometric interpretation of the
trace as a Noether--Lefschetz or Abel--Jacobi derivative remains separate.
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

noncomputable section
namespace CycleQ2SeedTrace
open MvPolynomial

attribute [local irreducible] traceLinear

def columnPolynomial : Fin 9 → Poly := ![
  mon 0 0 0 3, mon 0 0 3 0, mon 0 1 1 1, mon 0 3 0 0,
  mon 1 0 1 1, mon 1 2 0 0, mon 2 1 0 0, mon 3 0 0 0, -mon 0 0 2 1]

def rowPolynomial : Fin 8 → Poly := ![
  k * mon 0 0 1 2, k * mon 0 1 2 0, k * mon 0 2 0 1,
  k * mon 1 0 2 0, k * mon 1 1 0 1, k * mon 2 0 0 1,
  -(k * mon 0 0 3 0), -mon 0 0 3 3]

def rowScale (r : ℂ) : Fin 8 → ℂ := ![3*r, 3*r, 3*r, 3*r, 3*r, 3, 3, 6]

def polynomialTraceMatrix (r : ℂ) : Matrix (Fin 8) (Fin 9) ℂ :=
  fun i j => rowScale r i * traceLinear r (rowPolynomial i * columnPolynomial j)

theorem k_eq_monomials : k = mon 0 0 0 3 + mon 0 0 3 0 + mon 0 1 1 1 +
    mon 1 0 1 1 + mon 1 2 0 0 + C Complex.I * (mon 0 3 0 0 + mon 0 0 0 3) := by
  simp [k, b, mon]

theorem mon_mul_C_assoc (a b c d : ℕ) (q : Poly) (z : ℂ) :
    mon a b c d * (C z * q) = C z * (mon a b c d * q) := by ring

theorem polynomialTraceMatrix_eq_seedMatrix (r : ℂ) (hr : r ^ 3 = 2) :
    polynomialTraceMatrix r = CycleQ2GeometricSeed.seedMatrix := by
  ext i j
  change rowScale r i * traceLinear r (rowPolynomial i * columnPolynomial j) =
    CycleQ2GeometricSeed.seedMatrix i j
  fin_cases i <;> fin_cases j
  all_goals
    simp only [rowScale, rowPolynomial, columnPolynomial, CycleQ2GeometricSeed.seedMatrix,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons]
    simp only [k_eq_monomials,
      add_mul, mul_add, neg_mul, mul_neg, mul_assoc, mon_mul_C_assoc, mon_mul,
      map_add, map_neg, traceLinear_C_mul, traceLinear_mon]
    norm_num [traceValue] <;> ring_nf <;> norm_num [hr, Complex.I_sq] <;> ring

end CycleQ2SeedTrace

#print axioms CycleQ2SeedTrace.polynomialTraceMatrix_eq_seedMatrix
end
end


/- Component: seed_trace/SparseSeedBinding.lean -/
section
/-!
# The checked matrix is an actual quotient-trace matrix

This final binding uses the original weighted coordinates, original cubic
columns, original seven cycle rows and original derivative row. No finite
trace value is supplied as an assumption.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

noncomputable section
namespace CycleQ2SeedTrace
open MvPolynomial

def originalColumn : Fin 9 → WeightedPoly := ![
  X 3 ^ 3, X 2 ^ 3, X 1 * X 2 * X 3, X 1 ^ 3,
  X 0 * X 2 * X 3, X 0 * X 1 ^ 2, X 0 ^ 2 * X 1, X 0 ^ 3, X 3 * X 4]

def originalRow : Fin 8 → WeightedPoly := ![
  originalK * (X 2 * X 3 ^ 2), originalK * (X 1 * X 2 ^ 2),
  originalK * (X 1 ^ 2 * X 3), originalK * (X 0 * X 2 ^ 2),
  originalK * (X 0 * X 1 * X 3), originalK * (X 0 ^ 2 * X 3),
  originalK * (X 2 * X 4), X 2 * X 3 ^ 3 * X 4]

theorem substitute_originalK : substitute originalK = k := by
  norm_num [substitute, originalK, originalB, k, b,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
    Matrix.head_cons, Matrix.tail_cons]

theorem substitute_originalColumn (j : Fin 9) :
    substitute (originalColumn j) = columnPolynomial j := by
  fin_cases j <;>
    norm_num [substitute, originalColumn, columnPolynomial, mon,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons] <;> ring <;> simp

theorem substitute_originalRow (i : Fin 8) :
    substitute (originalRow i) = rowPolynomial i := by
  fin_cases i <;>
    norm_num [originalRow, rowPolynomial, map_mul, substitute, originalK, originalB, k, b,
      mon, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons] <;> ring <;> simp

/-- The exact displayed scaling, written without divisions for its computation. -/
theorem rowScale_eq_displayed (r : ℂ) (hr : r ^ 3 = 2) :
    rowScale r = ![6 / r ^ 2, 6 / r ^ 2, 6 / r ^ 2, 6 / r ^ 2,
      6 / r ^ 2, 3, 3, 6] := by
  have hr0 : r ≠ 0 := by
    intro h
    rw [h] at hr
    norm_num at hr
  have hs : 3 * r = 6 / r ^ 2 := by
    apply (eq_div_iff (pow_ne_zero 2 hr0)).mpr
    calc
      3 * r * r ^ 2 = 3 * r ^ 3 := by ring
      _ = 6 := by rw [hr]; norm_num
  funext i
  fin_cases i <;> simp [rowScale, hs]

def actualSeedTraceMatrix (r : ℂ) (hr : r ^ 3 = 2) : Matrix (Fin 8) (Fin 9) ℂ :=
  fun i j => rowScale r i * seedTrace r hr
    (seedQuotient r (originalRow i) * seedQuotient r (originalColumn j))

theorem actualSeedTraceMatrix_eq_polynomial (r : ℂ) (hr : r ^ 3 = 2) :
    actualSeedTraceMatrix r hr = polynomialTraceMatrix r := by
  ext i j
  change rowScale r i * seedTrace r hr
      (seedQuotient r (originalRow i) * seedQuotient r (originalColumn j)) = _
  rw [← map_mul, seedTrace_mk, map_mul, substitute_originalRow, substitute_originalColumn]
  rfl

/-- Every one of the 72 entries of the checked array is identified with its
trace product in the actual original seed algebra. -/
theorem actualSeedTraceMatrix_eq_seedMatrix (r : ℂ) (hr : r ^ 3 = 2) :
    actualSeedTraceMatrix r hr = CycleQ2GeometricSeed.seedMatrix := by
  rw [actualSeedTraceMatrix_eq_polynomial, polynomialTraceMatrix_eq_seedMatrix r hr]

theorem actualSeedTraceMatrix_right_inverse (r : ℂ) (hr : r ^ 3 = 2) :
    actualSeedTraceMatrix r hr * CycleQ2GeometricSeed.seedRightInverse = 1 := by
  rw [actualSeedTraceMatrix_eq_seedMatrix, CycleQ2GeometricSeed.seed_right_inverse]

theorem actualSeedTraceMatrix_tangent (r : ℂ) (hr : r ^ 3 = 2) :
    (actualSeedTraceMatrix r hr).mulVec CycleQ2GeometricSeed.seedTangent =
      CycleQ2GeometricSeed.tangentImage := by
  rw [actualSeedTraceMatrix_eq_seedMatrix, CycleQ2GeometricSeed.seed_tangent_image]

end CycleQ2SeedTrace

#print axioms CycleQ2SeedTrace.actualSeedTraceMatrix_eq_seedMatrix
#print axioms CycleQ2SeedTrace.actualSeedTraceMatrix_right_inverse
#print axioms CycleQ2SeedTrace.actualSeedTraceMatrix_tangent
end
end


/- Component: seed_trace/SparseSeedGrading.lean -/
section
set_option autoImplicit false
noncomputable section
namespace CycleQ2SeedTrace
open MvPolynomial

theorem mon_homogeneous (a b c d : ℕ) :
    (mon a b c d).IsHomogeneous (a + b + c + d) :=
  (((isHomogeneous_X_pow 0 a).mul (isHomogeneous_X_pow 1 b)).mul
    (isHomogeneous_X_pow 2 c)).mul (isHomogeneous_X_pow 3 d)

theorem traceNumerator_homogeneous (r : ℂ) :
    (traceNumerator r).IsHomogeneous 15 := by
  unfold traceNumerator
  repeat' apply IsHomogeneous.add
  all_goals exact (mon_homogeneous _ _ _ _).C_mul _

theorem topExponent_degree : topExponent.degree = 24 := by
  rw [Finsupp.degree_eq_sum]
  norm_num [topExponent, exponent_apply, Fin.sum_univ_succ]

/-- The constructed quotient functional is concentrated in degree nine. -/
theorem traceLinear_zero_other_degree (r : ℂ) {p : Poly} {d : ℕ}
    (hp : p.IsHomogeneous d) (hd : d ≠ 9) : traceLinear r p = 0 := by
  have hprod := (traceNumerator_homogeneous r).mul hp
  have hzero : coeff topExponent (traceNumerator r * p) = 0 :=
    hprod.coeff_eq_zero (by rw [topExponent_degree]; omega)
  rw [traceLinear_apply, hzero, mul_zero]

end CycleQ2SeedTrace

#print axioms CycleQ2SeedTrace.traceLinear_zero_other_degree
end
end
