import Proposal.CoverResidue

/-!
# Polymorphic Algebraic Identities for Local Residue at Infinity (`U = ∞`)

Self-contained `[Field R] [CharZero R]` polynomial/rational identities and `k5Params` leading
coefficient extractions factored out of `LocalResidueInf.lean` to keep elaboration fast and modular.
-/

namespace SymmetricSexticResidual.LocalResidueInfAlg

open Polynomial
open SymmetricSexticResidual.K5Field
open SymmetricSexticResidual.SheetCalculus
open SymmetricSexticResidual.CoverAlgebra
open SymmetricSexticResidual.CoverResidue
open QuadraticCovers

/-! ### Section 2: Polymorphic Polynomial Helpers & Exact Algebraic Identities -/

def P44_fn {R : Type*} [Field R] (S Q T : R) : R :=
    (20510415 : R) +
    (-45278190 : R) * T +
    (-135184545 : R) * T ^ 2 +
    (-13243230 : R) * T ^ 3 +
    (-496300770 : R) * Q +
    (1002263220 : R) * Q * T +
    (1619567460 : R) * Q * T ^ 2 +
    (61801740 : R) * Q * T ^ 3 +
    (1510998300 : R) * Q ^ 2 +
    (-9227925000 : R) * Q ^ 2 * T +
    (-4613962500 : R) * Q ^ 2 * T ^ 2 +
    (4883417910 : R) * Q ^ 3 +
    (25838190000 : R) * Q ^ 3 * T +
    (-20513855880 : R) * Q ^ 4 +
    (141076404 : R) * S +
    (-302433264 : R) * S * T +
    (-657628902 : R) * S * T ^ 2 +
    (-22660638 : R) * S * T ^ 3 +
    (-1013761980 : R) * S * Q +
    (6278958000 : R) * S * Q * T +
    (3978922500 : R) * S * Q * T ^ 2 +
    (-4586695470 : R) * S * Q ^ 2 +
    (-28116396000 : R) * S * Q ^ 2 * T +
    (-1389150000 : R) * S * Q ^ 2 * T ^ 2 +
    (28084223286 : R) * S * Q ^ 3 +
    (2593080000 : R) * S * Q ^ 3 * T +
    (161280315 : R) * S ^ 2 +
    (-1055687850 : R) * S ^ 2 * T +
    (-843577875 : R) * S ^ 2 * T ^ 2 +
    (1449439110 : R) * S ^ 2 * Q +
    (10141721100 : R) * S ^ 2 * Q * T +
    (1065015000 : R) * S ^ 2 * Q * T ^ 2 +
    (-14449808646 : R) * S ^ 2 * Q ^ 2 +
    (-2722734000 : R) * S ^ 2 * Q ^ 2 * T +
    (-108045000 : R) * S ^ 2 * Q ^ 2 * T ^ 2 +
    (-155306970 : R) * S ^ 3 +
    (-1212264900 : R) * S ^ 3 * T +
    (-203742000 : R) * S ^ 3 * T ^ 2 +
    (3313480842 : R) * S ^ 3 * Q +
    (950796000 : R) * S ^ 3 * Q * T +
    (79233000 : R) * S ^ 3 * Q * T ^ 2 +
    (-285894273 : R) * S ^ 4 +
    (-110397980 : R) * S ^ 4 * T +
    (-14526050 : R) * S ^ 4 * T ^ 2

def M01_q_fn {R : Type*} [Field R] (S Q T : R) : R :=
    (-2238759810 : R) * Q +
    (5237503740 : R) * Q * T +
    (-3040030980 : R) * Q * T ^ 2 +
    (525029505 : R) * Q * T ^ 3 +
    (7683624765 : R) * Q ^ 2 +
    (-372008700 : R) * Q ^ 2 * T +
    (10237067550 : R) * Q ^ 3 +
    (1928934000 : R) * Q ^ 3 * T +
    (4197469815 : R) * Q ^ 4 +
    (746253270 : R) * S +
    (-1745834580 : R) * S * T +
    (1013343660 : R) * S * T ^ 2 +
    (-175009835 : R) * S * T ^ 3 +
    (-4575240450 : R) * S * Q +
    (275562000 : R) * S * Q * T +
    (-8309917980 : R) * S * Q ^ 2 +
    (-2057529600 : R) * S * Q ^ 2 * T +
    (-7561149120 : R) * S * Q ^ 3 +
    (671344065 : R) * S ^ 2 +
    (-50519700 : R) * S ^ 2 * T +
    (2244102813 : R) * S ^ 2 * Q +
    (730851660 : R) * S ^ 2 * Q * T +
    (4310935335 : R) * S ^ 2 * Q ^ 2 +
    (-203860701 : R) * S ^ 3 +
    (-86444820 : R) * S ^ 3 * T +
    (-968078160 : R) * S ^ 3 * Q +
    (71921850 : R) * S ^ 4

def A32_2_q_fn {R : Type*} [Field R] (S Q T : R) : R :=
    (3000564 : R) * Q +
    (78318540 : R) * Q * T +
    (-197659350 : R) * Q ^ 2 +
    (-1000188 : R) * S +
    (-26106180 : R) * S * T +
    (124429830 : R) * S * Q +
    (18357675 : R) * S * Q * T +
    (-19514460 : R) * S ^ 2 +
    (-6119225 : R) * S ^ 2 * T

def A32_1_q_fn {R : Type*} [Field R] (S Q T : R) : R :=
    (482717070 : R) * Q +
    (-275562000 : R) * Q * T +
    (-1157172750 : R) * Q * T ^ 2 +
    (1567877310 : R) * Q ^ 2 +
    (-1841555250 : R) * Q ^ 2 * T +
    (-160905690 : R) * S +
    (91854000 : R) * S * T +
    (385724250 : R) * S * T ^ 2 +
    (-1036249848 : R) * S * Q +
    (1656892800 : R) * S * Q * T +
    (-783185400 : R) * S * Q * T ^ 2 +
    (-1185956100 : R) * S * Q ^ 2 +
    (1976593500 : R) * S * Q ^ 2 * T +
    (171208026 : R) * S ^ 2 +
    (-347680350 : R) * S ^ 2 * T +
    (261061800 : R) * S ^ 2 * T ^ 2 +
    (779622795 : R) * S ^ 2 * Q +
    (-1244298300 : R) * S ^ 2 * Q * T +
    (-91788375 : R) * S ^ 2 * Q * T ^ 2 +
    (-128101365 : R) * S ^ 3 +
    (195144600 : R) * S ^ 3 * T +
    (30596125 : R) * S ^ 3 * T ^ 2

def Q5_c5 {R : Type*} [Field R] (S Q : R) : R :=
    (80 / 567 : R) * Q ^ 4 +
    (-160 / 243 : R) * Q ^ 5 +
    (-320 / 1701 : R) * S * Q ^ 3 +
    (272 / 243 : R) * S * Q ^ 4 +
    (160 / 1701 : R) * S ^ 2 * Q ^ 2 +
    (-1664 / 2187 : R) * S ^ 2 * Q ^ 3 +
    (-320 / 15309 : R) * S ^ 3 * Q +
    (1696 / 6561 : R) * S ^ 3 * Q ^ 2 +
    (80 / 45927 : R) * S ^ 4 +
    (-32 / 729 : R) * S ^ 4 * Q +
    (176 / 59049 : R) * S ^ 5

def Q5_c4 {R : Type*} [Field R] (S Q : R) : R :=
    (400 / 1323 : R) * Q +
    (800 / 1323 : R) * Q ^ 2 +
    (-4400 / 3969 : R) * Q ^ 3 +
    (-320 / 63 : R) * Q ^ 4 +
    (-80 / 81 : R) * Q ^ 5 +
    (-400 / 3969 : R) * S +
    (-800 / 3969 : R) * S * Q +
    (3520 / 3969 : R) * S * Q ^ 2 +
    (4400 / 567 : R) * S * Q ^ 3 +
    (-992 / 243 : R) * S * Q ^ 4 +
    (-880 / 5103 : R) * S ^ 2 * Q +
    (-2600 / 567 : R) * S ^ 2 * Q ^ 2 +
    (15584 / 2187 : R) * S ^ 2 * Q ^ 3 +
    (18800 / 15309 : R) * S ^ 3 * Q +
    (-26656 / 6561 : R) * S ^ 3 * Q ^ 2 +
    (-5720 / 45927 : R) * S ^ 4 +
    (6556 / 6561 : R) * S ^ 4 * Q +
    (-5380 / 59049 : R) * S ^ 5

def p21_c3 {R : Type*} [Field R] (S Q : R) : R :=
    (80 / 63 : R) * Q +
    (40 / 63 : R) * Q ^ 2 +
    (-80 / 189 : R) * S +
    (-80 / 81 : R) * S * Q ^ 2 +
    (-40 / 567 : R) * S ^ 2 +
    (56 / 81 : R) * S ^ 2 * Q +
    (-88 / 729 : R) * S ^ 3

def p21_c2 {R : Type*} [Field R] (S Q : R) : R :=
    (-1040 / 63 : R) * Q +
    (-520 / 63 : R) * Q ^ 2 +
    (1840 / 189 : R) * S +
    (-560 / 81 : R) * S * Q ^ 2 +
    (1430 / 567 : R) * S ^ 2 +
    (292 / 81 : R) * S ^ 2 * Q +
    (-152 / 243 : R) * S ^ 3

def Q7_c7 {R : Type*} [Field R] (S Q : R) : R :=
    (64 / 6561 : R) * Q ^ 6 +
    (-128 / 6561 : R) * S * Q ^ 5 +
    (320 / 19683 : R) * S ^ 2 * Q ^ 4 +
    (-1280 / 177147 : R) * S ^ 3 * Q ^ 3 +
    (320 / 177147 : R) * S ^ 4 * Q ^ 2 +
    (-128 / 531441 : R) * S ^ 5 * Q +
    (64 / 4782969 : R) * S ^ 6

def Q7_c6 {R : Type*} [Field R] (S Q : R) : R :=
    (1760 / 5103 : R) * Q ^ 4 +
    (1760 / 5103 : R) * Q ^ 5 +
    (6944 / 6561 : R) * Q ^ 6 +
    (-7040 / 15309 : R) * S * Q ^ 3 +
    (-7040 / 15309 : R) * S * Q ^ 4 +
    (-1792 / 729 : R) * S * Q ^ 5 +
    (3520 / 15309 : R) * S ^ 2 * Q ^ 2 +
    (3520 / 15309 : R) * S ^ 2 * Q ^ 3 +
    (45920 / 19683 : R) * S ^ 2 * Q ^ 4 +
    (-7040 / 137781 : R) * S ^ 3 * Q +
    (-7040 / 137781 : R) * S ^ 3 * Q ^ 2 +
    (-206080 / 177147 : R) * S ^ 3 * Q ^ 3 +
    (1760 / 413343 : R) * S ^ 4 +
    (1760 / 413343 : R) * S ^ 4 * Q +
    (19040 / 59049 : R) * S ^ 4 * Q ^ 2 +
    (-25088 / 531441 : R) * S ^ 5 * Q +
    (13664 / 4782969 : R) * S ^ 6

def p32_c5 {R : Type*} [Field R] (S Q : R) : R :=
    (160 / 243 : R) * Q ^ 4 +
    (-640 / 729 : R) * S * Q ^ 3 +
    (320 / 729 : R) * S ^ 2 * Q ^ 2 +
    (-640 / 6561 : R) * S ^ 3 * Q +
    (160 / 19683 : R) * S ^ 4

def p32_c4 {R : Type*} [Field R] (S Q : R) : R :=
    (-400 / 1323 : R) +
    (-800 / 1323 : R) * Q +
    (4400 / 3969 : R) * Q ^ 2 +
    (800 / 567 : R) * Q ^ 3 +
    (80 / 81 : R) * Q ^ 4 +
    (1280 / 243 : R) * S * Q ^ 3 +
    (-880 / 5103 : R) * S ^ 2 +
    (-880 / 5103 : R) * S ^ 2 * Q +
    (-5120 / 729 : R) * S ^ 2 * Q ^ 2 +
    (18400 / 6561 : R) * S ^ 3 * Q +
    (-7124 / 19683 : R) * S ^ 4

def p31_c3 {R : Type*} [Field R] (S Q : R) : R :=
    (-40 / 63 : R) +
    (-40 / 63 : R) * Q +
    (80 / 81 : R) * S * Q +
    (-28 / 81 : R) * S ^ 2

def p31_c2 {R : Type*} [Field R] (S Q : R) : R :=
    (520 / 63 : R) +
    (520 / 63 : R) * Q +
    (560 / 81 : R) * S * Q +
    (-146 / 81 : R) * S ^ 2


lemma coeff_quadU {R : Type*} [CommRing R] (a0 a1 a2 : R) (n : ℕ) :
    (CoverParams.quadU a0 a1 a2).coeff n =
      match n with | 0 => a0 | 1 => a1 | 2 => a2 | _ => 0 := by
  unfold CoverParams.quadU
  rcases n with _ | _ | _ | n
  · simp
  · simp
  · simp
  · simp

lemma quadU_mul2_coeff3 {R : Type*} [CommRing R] (a0 a1 a2 b0 b1 b2 : R) :
    (CoverParams.quadU a0 a1 a2 * CoverParams.quadU b0 b1 b2).coeff 3 = a1 * b2 + a2 * b1 := by
  have heq : CoverParams.quadU a0 a1 a2 * CoverParams.quadU b0 b1 b2 =
      C (a0 * b0) + C (a0 * b1 + a1 * b0) * X + C (a0 * b2 + a1 * b1 + a2 * b0) * X ^ 2 +
      C (a1 * b2 + a2 * b1) * X ^ 3 + C (a2 * b2) * X ^ 4 := by
    simp only [CoverParams.quadU, map_add, map_mul]; ring
  rw [heq]
  simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
    Polynomial.coeff_X, Polynomial.coeff_C, Nat.reduceEqDiff, ↓reduceIte, mul_zero,
    zero_add, add_zero, mul_one]

lemma quadU_mul3_coeff5 {R : Type*} [CommRing R] (a0 a1 a2 b0 b1 b2 c0 c1 c2 : R) :
    (CoverParams.quadU a0 a1 a2 * CoverParams.quadU b0 b1 b2 * CoverParams.quadU c0 c1 c2).coeff 5 =
      a1 * b2 * c2 + a2 * b1 * c2 + a2 * b2 * c1 := by
  have heq : CoverParams.quadU a0 a1 a2 * CoverParams.quadU b0 b1 b2 * CoverParams.quadU c0 c1 c2 =
      C (a0 * b0 * c0) +
      C (a0 * b0 * c1 + a0 * b1 * c0 + a1 * b0 * c0) * X +
      C (a0 * b0 * c2 + a0 * b1 * c1 + a0 * b2 * c0 + a1 * b0 * c1 + a1 * b1 * c0 + a2 * b0 * c0) * X ^ 2 +
      C (a0 * b1 * c2 + a0 * b2 * c1 + a1 * b0 * c2 + a1 * b1 * c1 + a1 * b2 * c0 + a2 * b0 * c1 + a2 * b1 * c0) * X ^ 3 +
      C (a0 * b2 * c2 + a1 * b1 * c2 + a1 * b2 * c1 + a2 * b0 * c2 + a2 * b1 * c1 + a2 * b2 * c0) * X ^ 4 +
      C (a1 * b2 * c2 + a2 * b1 * c2 + a2 * b2 * c1) * X ^ 5 +
      C (a2 * b2 * c2) * X ^ 6 := by
    simp only [CoverParams.quadU, map_add, map_mul]; ring
  rw [heq]
  simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
    Polynomial.coeff_X, Polynomial.coeff_C, Nat.reduceEqDiff, ↓reduceIte, mul_zero,
    zero_add, add_zero, mul_one]

lemma quadU_mul3_coeff4 {R : Type*} [CommRing R] (a0 a1 a2 b0 b1 b2 c0 c1 c2 : R) :
    (CoverParams.quadU a0 a1 a2 * CoverParams.quadU b0 b1 b2 * CoverParams.quadU c0 c1 c2).coeff 4 =
      a0 * b2 * c2 + a1 * b1 * c2 + a1 * b2 * c1 + a2 * b0 * c2 + a2 * b1 * c1 + a2 * b2 * c0 := by
  have heq : CoverParams.quadU a0 a1 a2 * CoverParams.quadU b0 b1 b2 * CoverParams.quadU c0 c1 c2 =
      C (a0 * b0 * c0) +
      C (a0 * b0 * c1 + a0 * b1 * c0 + a1 * b0 * c0) * X +
      C (a0 * b0 * c2 + a0 * b1 * c1 + a0 * b2 * c0 + a1 * b0 * c1 + a1 * b1 * c0 + a2 * b0 * c0) * X ^ 2 +
      C (a0 * b1 * c2 + a0 * b2 * c1 + a1 * b0 * c2 + a1 * b1 * c1 + a1 * b2 * c0 + a2 * b0 * c1 + a2 * b1 * c0) * X ^ 3 +
      C (a0 * b2 * c2 + a1 * b1 * c2 + a1 * b2 * c1 + a2 * b0 * c2 + a2 * b1 * c1 + a2 * b2 * c0) * X ^ 4 +
      C (a1 * b2 * c2 + a2 * b1 * c2 + a2 * b2 * c1) * X ^ 5 +
      C (a2 * b2 * c2) * X ^ 6 := by
    simp only [CoverParams.quadU, map_add, map_mul]; ring
  rw [heq]
  simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
    Polynomial.coeff_X, Polynomial.coeff_C, Nat.reduceEqDiff, ↓reduceIte, mul_zero,
    zero_add, add_zero, mul_one]

lemma quadU_mul4_coeff7 {R : Type*} [CommRing R] (a0 a1 a2 b0 b1 b2 c0 c1 c2 d0 d1 d2 : R) :
    (CoverParams.quadU a0 a1 a2 * CoverParams.quadU b0 b1 b2 *
     CoverParams.quadU c0 c1 c2 * CoverParams.quadU d0 d1 d2).coeff 7 =
      a1 * b2 * c2 * d2 + a2 * b1 * c2 * d2 + a2 * b2 * c1 * d2 + a2 * b2 * c2 * d1 := by
  set P : R[X] := C (a0 * b0) + C (a0 * b1 + a1 * b0) * X + C (a0 * b2 + a1 * b1 + a2 * b0) * X ^ 2 +
      C (a1 * b2 + a2 * b1) * X ^ 3 + C (a2 * b2) * X ^ 4
  set Q : R[X] := C (c0 * d0) + C (c0 * d1 + c1 * d0) * X + C (c0 * d2 + c1 * d1 + c2 * d0) * X ^ 2 +
      C (c1 * d2 + c2 * d1) * X ^ 3 + C (c2 * d2) * X ^ 4
  have hp : CoverParams.quadU a0 a1 a2 * CoverParams.quadU b0 b1 b2 = P := by
    simp only [P, CoverParams.quadU, map_add, map_mul]; ring
  have hq : CoverParams.quadU c0 c1 c2 * CoverParams.quadU d0 d1 d2 = Q := by
    simp only [Q, CoverParams.quadU, map_add, map_mul]; ring
  rw [mul_assoc, hp, hq, Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => P.coeff i * Q.coeff j) 7]
  simp only [P, Q, Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.reduceSub,
    Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
    Polynomial.coeff_X, Polynomial.coeff_C, Nat.reduceEqDiff, ↓reduceIte,
    mul_zero, zero_mul, zero_add, add_zero, mul_one]
  ring

lemma quadU_mul4_coeff6 {R : Type*} [CommRing R] (a0 a1 a2 b0 b1 b2 c0 c1 c2 d0 d1 d2 : R) :
    (CoverParams.quadU a0 a1 a2 * CoverParams.quadU b0 b1 b2 *
     CoverParams.quadU c0 c1 c2 * CoverParams.quadU d0 d1 d2).coeff 6 =
      a0 * b2 * c2 * d2 + a1 * b1 * c2 * d2 + a1 * b2 * c1 * d2 + a1 * b2 * c2 * d1 +
      a2 * b0 * c2 * d2 + a2 * b1 * c1 * d2 + a2 * b1 * c2 * d1 +
      a2 * b2 * c0 * d2 + a2 * b2 * c1 * d1 + a2 * b2 * c2 * d0 := by
  set P : R[X] := C (a0 * b0) + C (a0 * b1 + a1 * b0) * X + C (a0 * b2 + a1 * b1 + a2 * b0) * X ^ 2 +
      C (a1 * b2 + a2 * b1) * X ^ 3 + C (a2 * b2) * X ^ 4
  set Q : R[X] := C (c0 * d0) + C (c0 * d1 + c1 * d0) * X + C (c0 * d2 + c1 * d1 + c2 * d0) * X ^ 2 +
      C (c1 * d2 + c2 * d1) * X ^ 3 + C (c2 * d2) * X ^ 4
  have hp : CoverParams.quadU a0 a1 a2 * CoverParams.quadU b0 b1 b2 = P := by
    simp only [P, CoverParams.quadU, map_add, map_mul]; ring
  have hq : CoverParams.quadU c0 c1 c2 * CoverParams.quadU d0 d1 d2 = Q := by
    simp only [Q, CoverParams.quadU, map_add, map_mul]; ring
  rw [mul_assoc, hp, hq, Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => P.coeff i * Q.coeff j) 6]
  simp only [P, Q, Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.reduceSub,
    Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
    Polynomial.coeff_X, Polynomial.coeff_C, Nat.reduceEqDiff, ↓reduceIte,
    mul_zero, zero_mul, zero_add, add_zero, mul_one]
  ring

lemma k5Params_Q5_c5_eq : k5Params.Q5_z.coeff 5 = Q5_c5 S_K Q_K := by
  have h : k5Params.Q5_z =
      k5Params.q20 * k5Params.cb_h * k5Params.cb_h -
      k5Params.q11 * k5Params.ca_h * k5Params.cb_h +
      k5Params.q02 * k5Params.ca_h * k5Params.ca_h := by
    unfold CoverParams.Q5_z; ring
  rw [h, Polynomial.coeff_add, Polynomial.coeff_sub]
  simp only [CoverParams.q20, CoverParams.q11, CoverParams.q02, CoverParams.ca_h, CoverParams.cb_h,
    quadU_mul3_coeff5, CoverParams.inv9, CoverParams.inv27, CoverParams.inv81, k5Params_inv3,
    k5Params_inv7, k5Params_S, k5Params_Q, Q5_c5]
  ring

lemma k5Params_Q5_c4_eq : k5Params.Q5_z.coeff 4 = Q5_c4 S_K Q_K := by
  have h : k5Params.Q5_z =
      k5Params.q20 * k5Params.cb_h * k5Params.cb_h -
      k5Params.q11 * k5Params.ca_h * k5Params.cb_h +
      k5Params.q02 * k5Params.ca_h * k5Params.ca_h := by
    unfold CoverParams.Q5_z; ring
  rw [h, Polynomial.coeff_add, Polynomial.coeff_sub]
  simp only [CoverParams.q20, CoverParams.q11, CoverParams.q02, CoverParams.ca_h, CoverParams.cb_h,
    quadU_mul3_coeff4, CoverParams.inv9, CoverParams.inv27, CoverParams.inv81, k5Params_inv3,
    k5Params_inv7, k5Params_S, k5Params_Q, Q5_c4]
  ring

lemma k5Params_Q7_c7_eq : k5Params.Q7_z.coeff 7 = Q7_c7 S_K Q_K := by
  have h : k5Params.Q7_z =
      k5Params.c30 * k5Params.cb_h * k5Params.cb_h * k5Params.cb_h -
      k5Params.c21 * k5Params.ca_h * k5Params.cb_h * k5Params.cb_h +
      k5Params.c12 * k5Params.ca_h * k5Params.ca_h * k5Params.cb_h -
      k5Params.c03 * k5Params.ca_h * k5Params.ca_h * k5Params.ca_h := by
    unfold CoverParams.Q7_z; ring
  rw [h, Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_sub]
  simp only [CoverParams.c30, CoverParams.c21, CoverParams.c12, CoverParams.c03,
    CoverParams.ca_h, CoverParams.cb_h, quadU_mul4_coeff7, CoverParams.inv9, CoverParams.inv27,
    CoverParams.inv81, CoverParams.inv243, k5Params_inv3, k5Params_inv7, k5Params_S, k5Params_Q, Q7_c7]
  ring

lemma k5Params_Q7_c6_eq : k5Params.Q7_z.coeff 6 = Q7_c6 S_K Q_K := by
  have h : k5Params.Q7_z =
      k5Params.c30 * k5Params.cb_h * k5Params.cb_h * k5Params.cb_h -
      k5Params.c21 * k5Params.ca_h * k5Params.cb_h * k5Params.cb_h +
      k5Params.c12 * k5Params.ca_h * k5Params.ca_h * k5Params.cb_h -
      k5Params.c03 * k5Params.ca_h * k5Params.ca_h * k5Params.ca_h := by
    unfold CoverParams.Q7_z; ring
  rw [h, Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_sub]
  simp only [CoverParams.c30, CoverParams.c21, CoverParams.c12, CoverParams.c03,
    CoverParams.ca_h, CoverParams.cb_h, quadU_mul4_coeff6, CoverParams.inv9, CoverParams.inv27,
    CoverParams.inv81, CoverParams.inv243, k5Params_inv3, k5Params_inv7, k5Params_S, k5Params_Q, Q7_c6]
  ring

lemma k5Params_p21_c3_eq :
    (-k5Params.q11 * k5Params.cb_h + 2 * k5Params.q02 * k5Params.ca_h).coeff 3 = p21_c3 S_K Q_K := by
  have h : -k5Params.q11 * k5Params.cb_h + 2 * k5Params.q02 * k5Params.ca_h =
      -(k5Params.q11 * k5Params.cb_h) + C 2 * (k5Params.q02 * k5Params.ca_h) := by
    rw [map_ofNat]; ring
  rw [h, Polynomial.coeff_add, Polynomial.coeff_neg, Polynomial.coeff_C_mul]
  simp only [CoverParams.q11, CoverParams.q02, CoverParams.ca_h, CoverParams.cb_h,
    quadU_mul2_coeff3, CoverParams.inv9, CoverParams.inv27, CoverParams.inv81, k5Params_inv3,
    k5Params_inv7, k5Params_S, k5Params_Q, p21_c3]
  ring

lemma k5Params_p32_c5_eq :
    (-k5Params.c21 * k5Params.cb_h ^ 2 + 2 * k5Params.c12 * k5Params.ca_h * k5Params.cb_h -
      3 * k5Params.c03 * k5Params.ca_h ^ 2).coeff 5 = p32_c5 S_K Q_K := by
  have h : -k5Params.c21 * k5Params.cb_h ^ 2 + 2 * k5Params.c12 * k5Params.ca_h * k5Params.cb_h -
      3 * k5Params.c03 * k5Params.ca_h ^ 2 =
      -(k5Params.c21 * k5Params.cb_h * k5Params.cb_h) +
      C 2 * (k5Params.c12 * k5Params.ca_h * k5Params.cb_h) -
      C 3 * (k5Params.c03 * k5Params.ca_h * k5Params.ca_h) := by
    rw [map_ofNat, map_ofNat]; ring
  rw [h, Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_neg,
    Polynomial.coeff_C_mul, Polynomial.coeff_C_mul]
  simp only [CoverParams.c21, CoverParams.c12, CoverParams.c03, CoverParams.ca_h, CoverParams.cb_h,
    quadU_mul3_coeff5, CoverParams.inv9, CoverParams.inv27, CoverParams.inv81, k5Params_inv3,
    k5Params_inv7, k5Params_S, k5Params_Q, p32_c5]
  ring

lemma k5Params_p31_c3_eq :
    (k5Params.c12 * k5Params.cb_h - 3 * k5Params.c03 * k5Params.ca_h).coeff 3 = p31_c3 S_K Q_K := by
  have h : k5Params.c12 * k5Params.cb_h - 3 * k5Params.c03 * k5Params.ca_h =
      k5Params.c12 * k5Params.cb_h - C 3 * (k5Params.c03 * k5Params.ca_h) := by
    rw [map_ofNat]; ring
  rw [h, Polynomial.coeff_sub, Polynomial.coeff_C_mul]
  simp only [CoverParams.c12, CoverParams.c03, CoverParams.ca_h, CoverParams.cb_h,
    quadU_mul2_coeff3, CoverParams.inv9, CoverParams.inv27, CoverParams.inv81, k5Params_inv3,
    k5Params_inv7, k5Params_S, k5Params_Q, p31_c3]
  ring

-- Universal `minor_split_UV` & `numM_split_UV`:
def dHS_2 {R : Type*} [Field R] (s q : R) : R := -(4 / 81 : R) * (s - 3 * q) ^ 2
def dHS_1 {R : Type*} [Field R] (s q : R) : R := (143 / 81 : R) * s ^ 2 - (184 / 27) * s * q + (52 / 9) * q ^ 2
def dHS_0 {R : Type*} [Field R] (s q : R) : R := -(25 / 243 : R) * (5 * s - 9 * q) * (15 * s - 9 * q)
def dHQ_1 {R : Type*} [Field R] (s q v : R) : R :=
  -(92 / 27 : R) * s ^ 2 + (104 / 9) * s * q - (22 / 3) * q ^ 2 + (10 / 7) * q * v + (10 / 7) * v ^ 2
def dHQ_0 {R : Type*} [Field R] (s q : R) : R := (50 / 27 : R) * s * (5 * s - 9 * q)

def minor_U3 {R : Type*} [Field R] (s1 q1 v1 s2 q2 v2 : R) : R :=
  dHS_2 s1 q1 * (dHQ_1 s2 q2 v2 + 3 * dHS_1 s2 q2) - dHS_2 s2 q2 * (dHQ_1 s1 q1 v1 + 3 * dHS_1 s1 q1)

def minor_U2 {R : Type*} [Field R] (s1 q1 v1 s2 q2 v2 : R) : R :=
  dHS_2 s1 q1 * (dHQ_0 s2 q2 + 3 * dHS_0 s2 q2) - dHS_2 s2 q2 * (dHQ_0 s1 q1 + 3 * dHS_0 s1 q1) +
  dHS_1 s1 q1 * dHQ_1 s2 q2 v2 - dHS_1 s2 q2 * dHQ_1 s1 q1 v1

def minor_U1 {R : Type*} [Field R] (s1 q1 v1 s2 q2 v2 : R) : R :=
  dHS_1 s1 q1 * dHQ_0 s2 q2 - dHS_1 s2 q2 * dHQ_0 s1 q1 +
  dHS_0 s1 q1 * dHQ_1 s2 q2 v2 - dHS_0 s2 q2 * dHQ_1 s1 q1 v1

def minor_U0 {R : Type*} [Field R] (s1 q1 s2 q2 : R) : R :=
  dHS_0 s1 q1 * dHQ_0 s2 q2 - dHS_0 s2 q2 * dHQ_0 s1 q1

lemma minor_split_UV {R : Type*} [Field R] [CharZero R] (s1 q1 v1 s2 q2 v2 U V : R) :
    dH_dS s1 q1 U V * dH_dQ s2 q2 v2 U V - dH_dS s2 q2 U V * dH_dQ s1 q1 v1 U V =
      V ^ 2 * (U ^ 3 * minor_U3 s1 q1 v1 s2 q2 v2 + U ^ 2 * minor_U2 s1 q1 v1 s2 q2 v2 +
               U * minor_U1 s1 q1 v1 s2 q2 v2 + minor_U0 s1 q1 s2 q2) := by
  simp only [dH_dS, dH_dQ, minor_U3, minor_U2, minor_U1, minor_U0,
    dHS_2, dHS_1, dHS_0, dHQ_1, dHQ_0]; ring

def d20_U3 {R : Type*} [Field R] (a b xS xQ : R) : R := minor_U3 a b 0 xS xQ 1
def d20_U2 {R : Type*} [Field R] (a b xS xQ : R) : R := minor_U2 a b 0 xS xQ 1
def d20_U1 {R : Type*} [Field R] (a b xS xQ : R) : R := minor_U1 a b 0 xS xQ 1
def d20_U0 {R : Type*} [Field R] (a b xS xQ : R) : R := minor_U0 a b xS xQ

def d21_U3 {R : Type*} [Field R] (a b xS xQ : R) : R :=
  minor_U3 a b 0 (a + xS) (b + xQ) 0 - minor_U3 a b 0 xS xQ 0 + (10 / 7 : R) * b * dHS_2 a b
def d21_U2 {R : Type*} [Field R] (a b xS xQ : R) : R :=
  minor_U2 a b 0 (a + xS) (b + xQ) 0 - minor_U2 a b 0 xS xQ 0 + (10 / 7 : R) * b * dHS_1 a b
def d21_U1 {R : Type*} [Field R] (a b xS xQ : R) : R :=
  minor_U1 a b 0 (a + xS) (b + xQ) 0 - minor_U1 a b 0 xS xQ 0 + (10 / 7 : R) * b * dHS_0 a b
def d21_U0 {R : Type*} [Field R] (a b xS xQ : R) : R :=
  minor_U0 a b (a + xS) (b + xQ) - minor_U0 a b xS xQ

def d10_U3 {R : Type*} [Field R] (a b xS xQ : R) : R :=
  minor_U3 (a + xS) (b + xQ) 0 xS xQ 1 - minor_U3 a b 0 xS xQ 1 - minor_U3 xS xQ 0 xS xQ 1 -
    (10 / 7 : R) * b * dHS_2 xS xQ
def d10_U2 {R : Type*} [Field R] (a b xS xQ : R) : R :=
  minor_U2 (a + xS) (b + xQ) 0 xS xQ 1 - minor_U2 a b 0 xS xQ 1 - minor_U2 xS xQ 0 xS xQ 1 -
    (10 / 7 : R) * b * dHS_1 xS xQ
def d10_U1 {R : Type*} [Field R] (a b xS xQ : R) : R :=
  minor_U1 (a + xS) (b + xQ) 0 xS xQ 1 - minor_U1 a b 0 xS xQ 1 - minor_U1 xS xQ 0 xS xQ 1 -
    (10 / 7 : R) * b * dHS_0 xS xQ
def d10_U0 {R : Type*} [Field R] (a b xS xQ : R) : R :=
  minor_U0 (a + xS) (b + xQ) xS xQ - minor_U0 a b xS xQ - minor_U0 xS xQ xS xQ

def numM_Uk {R : Type*} [Field R] (k : Fin 4) (mi : Fin 10) (a b xS xQ : R) : R :=
  let (d10, d20, d21) : R × R × R := match k with
    | 0 => (d10_U0 a b xS xQ, d20_U0 a b xS xQ, d21_U0 a b xS xQ)
    | 1 => (d10_U1 a b xS xQ, d20_U1 a b xS xQ, d21_U1 a b xS xQ)
    | 2 => (d10_U2 a b xS xQ, d20_U2 a b xS xQ, d21_U2 a b xS xQ)
    | 3 => (d10_U3 a b xS xQ, d20_U3 a b xS xQ, d21_U3 a b xS xQ)
  let (m2, m1, m0) : R × R × R := match mi with
    | 0 => (a ^ 2, 2 * a * xS, xS ^ 2)
    | 1 => (a * b, a * xQ + b * xS, xS * xQ)
    | 2 => (b ^ 2, 2 * b * xQ, xQ ^ 2)
    | 3 => (a, xS, 0)
    | 4 => (0, a, xS)
    | 5 => (b, xQ, 0)
    | 6 => (0, b, xQ)
    | 7 => (1, 0, 0)
    | 8 => (0, 1, 0)
    | 9 => (0, 0, 1)
  (1 / 16 : R) * (m2 * d10 - m1 * d20 + m0 * d21)

lemma numM_split_UV {R : Type*} [Field R] [CharZero R] (mi : Fin 10) (a b xS xQ U V : R) :
    numM mi a b xS xQ U V =
      V ^ 2 * (U ^ 3 * numM_Uk 3 mi a b xS xQ + U ^ 2 * numM_Uk 2 mi a b xS xQ +
               U * numM_Uk 1 mi a b xS xQ + numM_Uk 0 mi a b xS xQ) := by
  have hd20 : q1_a2 a b U V * q2_b0 xS xQ U V - q1_a0 xS xQ U V * q2_b2 a b U V =
      V ^ 2 * (U ^ 3 * d20_U3 a b xS xQ + U ^ 2 * d20_U2 a b xS xQ +
               U * d20_U1 a b xS xQ + d20_U0 a b xS xQ) :=
    minor_split_UV a b 0 xS xQ 1 U V
  have hd21 : q1_a2 a b U V * q2_b1 a b xS xQ U V - q1_a1 a b xS xQ U V * q2_b2 a b U V =
      V ^ 2 * (U ^ 3 * d21_U3 a b xS xQ + U ^ 2 * d21_U2 a b xS xQ +
               U * d21_U1 a b xS xQ + d21_U0 a b xS xQ) := by
    have hm1 := minor_split_UV a b 0 (a + xS) (b + xQ) 0 U V
    have hm2 := minor_split_UV a b 0 xS xQ 0 U V
    have hre : q1_a2 a b U V * q2_b1 a b xS xQ U V - q1_a1 a b xS xQ U V * q2_b2 a b U V =
        (dH_dS a b U V * dH_dQ (a + xS) (b + xQ) 0 U V - dH_dS (a + xS) (b + xQ) U V * dH_dQ a b 0 U V) -
        (dH_dS a b U V * dH_dQ xS xQ 0 U V - dH_dS xS xQ U V * dH_dQ a b 0 U V) +
        (10 / 7 : R) * b * U * V * dH_dS a b U V := by
      simp only [q1_a2, q1_a1, q2_b2, q2_b1]; ring
    rw [hre, hm1, hm2]
    simp only [d21_U3, d21_U2, d21_U1, d21_U0, dH_dS, dHS_2, dHS_1, dHS_0]; ring
  have hd10 : q1_a1 a b xS xQ U V * q2_b0 xS xQ U V - q1_a0 xS xQ U V * q2_b1 a b xS xQ U V =
      V ^ 2 * (U ^ 3 * d10_U3 a b xS xQ + U ^ 2 * d10_U2 a b xS xQ +
               U * d10_U1 a b xS xQ + d10_U0 a b xS xQ) := by
    have hm1 := minor_split_UV (a + xS) (b + xQ) 0 xS xQ 1 U V
    have hm2 := minor_split_UV a b 0 xS xQ 1 U V
    have hm3 := minor_split_UV xS xQ 0 xS xQ 1 U V
    have hre : q1_a1 a b xS xQ U V * q2_b0 xS xQ U V - q1_a0 xS xQ U V * q2_b1 a b xS xQ U V =
        (dH_dS (a + xS) (b + xQ) U V * dH_dQ xS xQ 1 U V - dH_dS xS xQ U V * dH_dQ (a + xS) (b + xQ) 0 U V) -
        (dH_dS a b U V * dH_dQ xS xQ 1 U V - dH_dS xS xQ U V * dH_dQ a b 0 U V) -
        (dH_dS xS xQ U V * dH_dQ xS xQ 1 U V - dH_dS xS xQ U V * dH_dQ xS xQ 0 U V) -
        (10 / 7 : R) * b * U * V * dH_dS xS xQ U V := by
      simp only [q1_a1, q1_a0, q2_b1, q2_b0]; ring
    rw [hre, hm1, hm2, hm3]
    simp only [d10_U3, d10_U2, d10_U1, d10_U0, dH_dS, dHS_2, dHS_1, dHS_0]; ring
  fin_cases mi <;> (simp only [numM, numM_Uk]; rw [hd20, hd21, hd10]; ring)

lemma AY_t3_U3_eq_zero {R : Type*} [Field R] [CharZero R] (a b xS xQ : R) :
    -(123236 / 24249375 : R) * (numM_Uk 3 0 a b xS xQ + (2790 / 77) * numM_Uk 3 6 a b xS xQ +
      28 * numM_Uk 3 8 a b xS xQ - (5904 / 77) * numM_Uk 3 9 a b xS xQ) +
    (492944 / 33949125) * (numM_Uk 3 1 a b xS xQ + (927 / 77) * numM_Uk 3 6 a b xS xQ +
      (49 / 5) * numM_Uk 3 8 a b xS xQ - (21159 / 770) * numM_Uk 3 9 a b xS xQ) = 0 := by
  simp only [numM_Uk, d10_U3, d20_U3, d21_U3, minor_U3, dHS_2, dHS_1, dHQ_1]; ring

def A0V_Uk {R : Type*} [Field R] (k : Fin 4) (a b xS xQ : R) : R :=
  -(892 / 3645 : R) * (5 * numM_Uk k 3 a b xS xQ - 9 * numM_Uk k 4 a b xS xQ) +
   (40 / 81) * (5 * numM_Uk k 5 a b xS xQ - 9 * numM_Uk k 6 a b xS xQ) -
   (112 / 2395) * (5 * numM_Uk k 7 a b xS xQ - 9 * numM_Uk k 8 a b xS xQ) +
   (392 / 11975) * (5 * numM_Uk k 8 a b xS xQ - 9 * numM_Uk k 9 a b xS xQ)

def AX_Uk {R : Type*} [Field R] (k : Fin 4) (a b xS xQ : R) : R :=
  -(8 / 405 : R) * (5 * numM_Uk k 3 a b xS xQ - 9 * numM_Uk k 4 a b xS xQ) -
   (476 / 7185) * (5 * numM_Uk k 7 a b xS xQ - 9 * numM_Uk k 8 a b xS xQ) +
   (6916 / 35925) * (5 * numM_Uk k 8 a b xS xQ - 9 * numM_Uk k 9 a b xS xQ)

lemma A_0V_split_UV {R : Type*} [Field R] [CharZero R] (a b xS xQ U V : R) :
    A_0V a b xS xQ U V =
      V ^ 2 * (U ^ 3 * A0V_Uk 3 a b xS xQ + U ^ 2 * A0V_Uk 2 a b xS xQ +
               U * A0V_Uk 1 a b xS xQ + A0V_Uk 0 a b xS xQ) := by
  simp only [A_0V, A0V_Uk, numM_split_UV]; ring

lemma A_X_split_UV {R : Type*} [Field R] [CharZero R] (a b xS xQ U V : R) :
    A_X a b xS xQ U V =
      U * V ^ 2 * (U ^ 3 * AX_Uk 3 a b xS xQ + U ^ 2 * AX_Uk 2 a b xS xQ +
                   U * AX_Uk 1 a b xS xQ + AX_Uk 0 a b xS xQ) := by
  simp only [A_X, AX_Uk, numM_split_UV]; ring

-- Compact factored forms for `d20/d21/d10` at `U3` and `U2`, and linear decomposition of `A0V_Uk`/`AX_Uk`:
lemma d20_U3_eq {R : Type*} [Field R] [CharZero R] (a b xS xQ : R) :
    d20_U3 a b xS xQ =
      (4 / 5103 : R) * (441 * a ^ 2 * xQ ^ 2 - 154 * a ^ 2 * xQ * xS - 90 * a ^ 2 * xQ - 90 * a ^ 2 -
        1260 * a * b * xQ ^ 2 + 540 * a * b * xQ + 154 * a * b * xS ^ 2 + 540 * a * b +
        1260 * b ^ 2 * xQ * xS - 810 * b ^ 2 * xQ - 441 * b ^ 2 * xS ^ 2 - 810 * b ^ 2) := by
  simp only [d20_U3, minor_U3, dHS_2, dHS_1, dHQ_1]; ring

lemma d21_U3_eq {R : Type*} [Field R] [CharZero R] (a b xS xQ : R) :
    d21_U3 a b xS xQ =
      -(8 / 5103 : R) * (a - 3 * b) *
        (77 * a ^ 2 * xQ - 210 * a * b * xQ - 77 * a * b * xS + 45 * a * b + 210 * b ^ 2 * xS - 135 * b ^ 2) := by
  simp only [d21_U3, minor_U3, dHS_2, dHS_1, dHQ_1]; ring

lemma d10_U3_eq {R : Type*} [Field R] [CharZero R] (a b xS xQ : R) :
    d10_U3 a b xS xQ =
      -(8 / 5103 : R) * (3 * xQ - xS) *
        (210 * a * xQ ^ 2 - 77 * a * xQ * xS - 90 * a * xQ - 90 * a -
         210 * b * xQ * xS + 135 * b * xQ + 77 * b * xS ^ 2 + 45 * b * xS + 270 * b) := by
  simp only [d10_U3, minor_U3, dHS_2, dHS_1, dHQ_1]; ring

lemma d20_U2_eq {R : Type*} [Field R] [CharZero R] (a b xS xQ : R) :
    d20_U2 a b xS xQ =
      (2 / 1701 : R) * (1533 * a ^ 2 * xQ ^ 2 - 532 * a ^ 2 * xQ * xS + 2145 * a ^ 2 * xQ + 2145 * a ^ 2 -
        5880 * a * b * xQ ^ 2 - 8280 * a * b * xQ + 532 * a * b * xS ^ 2 - 8280 * a * b +
        5880 * b ^ 2 * xQ * xS + 7020 * b ^ 2 * xQ - 1533 * b ^ 2 * xS ^ 2 + 7020 * b ^ 2) := by
  simp only [d20_U2, minor_U2, dHS_2, dHS_1, dHS_0, dHQ_1, dHQ_0]; ring

lemma d21_U2_eq {R : Type*} [Field R] [CharZero R] (a b xS xQ : R) :
    d21_U2 a b xS xQ =
      -(2 / 1701 : R) * (532 * a ^ 3 * xQ - 3066 * a ^ 2 * b * xQ - 532 * a ^ 2 * b * xS - 2145 * a ^ 2 * b +
        5880 * a * b ^ 2 * xQ + 3066 * a * b ^ 2 * xS + 8280 * a * b ^ 2 - 5880 * b ^ 3 * xS - 7020 * b ^ 3) := by
  simp only [d21_U2, minor_U2, dHS_2, dHS_1, dHS_0, dHQ_1, dHQ_0]; ring

lemma d10_U2_eq {R : Type*} [Field R] [CharZero R] (a b xS xQ : R) :
    d10_U2 a b xS xQ =
      -(2 / 1701 : R) * (5880 * a * xQ ^ 3 - 3066 * a * xQ ^ 2 * xS + 8280 * a * xQ ^ 2 +
        532 * a * xQ * xS ^ 2 - 4290 * a * xQ * xS + 8280 * a * xQ - 4290 * a * xS -
        5880 * b * xQ ^ 2 * xS - 7020 * b * xQ ^ 2 + 3066 * b * xQ * xS ^ 2 - 14040 * b * xQ -
        532 * b * xS ^ 3 + 2145 * b * xS ^ 2 + 8280 * b * xS) := by
  simp only [d10_U2, minor_U2, dHS_2, dHS_1, dHS_0, dHQ_1, dHQ_0]; ring

lemma A0V_Uk_eq {R : Type*} [Field R] [CharZero R] (k : Fin 4) (a b xS xQ : R) :
    let (d10, d20, d21) : R × R × R := match k with
      | 0 => (d10_U0 a b xS xQ, d20_U0 a b xS xQ, d21_U0 a b xS xQ)
      | 1 => (d10_U1 a b xS xQ, d20_U1 a b xS xQ, d21_U1 a b xS xQ)
      | 2 => (d10_U2 a b xS xQ, d20_U2 a b xS xQ, d21_U2 a b xS xQ)
      | 3 => (d10_U3 a b xS xQ, d20_U3 a b xS xQ, d21_U3 a b xS xQ)
    A0V_Uk k a b xS xQ =
      (-(223 / 2916 : R) * a + (25 / 162) * b - (7 / 479)) * d10 +
      (-(223 / 1620 : R) * a + (5 / 18) * b - (25 / 162) * xQ + (223 / 2916) * xS - (35 / 958)) * d20 +
      (-(5 / 18 : R) * xQ + (223 / 1620) * xS - (441 / 23950)) * d21 := by
  fin_cases k <;> (simp only [A0V_Uk, numM_Uk]; ring)

lemma AX_Uk_eq {R : Type*} [Field R] [CharZero R] (k : Fin 4) (a b xS xQ : R) :
    let (d10, d20, d21) : R × R × R := match k with
      | 0 => (d10_U0 a b xS xQ, d20_U0 a b xS xQ, d21_U0 a b xS xQ)
      | 1 => (d10_U1 a b xS xQ, d20_U1 a b xS xQ, d21_U1 a b xS xQ)
      | 2 => (d10_U2 a b xS xQ, d20_U2 a b xS xQ, d21_U2 a b xS xQ)
      | 3 => (d10_U3 a b xS xQ, d20_U3 a b xS xQ, d21_U3 a b xS xQ)
    AX_Uk k a b xS xQ =
      (-(1 / 162 : R) * a - (119 / 5748)) * d10 +
      (-(1 / 90 : R) * a + (1 / 162) * xS - (140 / 1437)) * d20 +
      ((1 / 90 : R) * xS - (5187 / 47900)) * d21 := by
  fin_cases k <;> (simp only [AX_Uk, numM_Uk]; ring)

lemma diff3_lin_mul {R : Type*} [Field R] [CharZero R] (p1 p0 : R) (D : R → R) :
    let g := fun z : R => (p1 * z + p0) * D z
    (g 2 - 3 * g 1 + 3 * g 0 - g (-1)) / 6 =
      p1 * ((2 * D 2 - 3 * D 1 + D (-1)) / 6) +
      p0 * ((D 2 - 3 * D 1 + 3 * D 0 - D (-1)) / 6) := by
  dsimp only; ring

-- Exact cubic expansion of `A0V_Uk 3` at `(a, b) = (u, u / 3 + β)` for free `β`, then specializing `β`:
lemma A0V_U3_poly_beta {R : Type*} [Field R] [CharZero R] (S Q T u β : R) :
    A0V_Uk 3 u (u / 3 + β) (S - u * T) (Q - (u / 3 + β) * T) =
      ((73 / 7971615 : R) * (5 * T - 9) * (S - 3 * Q) ^ 2) * u ^ 3 +
      ((3 * Q - S) * (329432250 * Q ^ 2 - 225740725 * Q * S - 329432250 * Q * T * β + 7144200 * Q * T +
        592978050 * Q * β - 87606000 * Q + 38643325 * S ^ 2 + 97572300 * S * T * β - 2381400 * S * T -
        175630140 * S * β + 29202000 * S - 7144200 * T ^ 2 * β + 17860500 * T * β - 9001692 * β) / 44548041825) * u ^ 2 +
      ((214326000 * Q ^ 3 - 658864500 * Q ^ 2 * S * β - 221470200 * Q ^ 2 * S - 428652000 * Q ^ 2 * T * β +
        1256829750 * Q ^ 2 * β - 45927000 * Q ^ 2 + 451481450 * Q * S ^ 2 * β + 76204800 * Q * S ^ 2 +
        658864500 * Q * S * T * β ^ 2 + 285768000 * Q * S * T * β - 1185956100 * Q * S * β ^ 2 -
        680535000 * Q * S * β + 30618000 * Q * S + 214326000 * Q * T ^ 2 * β ^ 2 - 1256829750 * Q * T * β ^ 2 +
        1567877310 * Q * β ^ 2 + 472054500 * Q * β - 77286650 * S ^ 3 * β - 8731800 * S ^ 3 -
        213502275 * S ^ 2 * T * β ^ 2 - 47628000 * S ^ 2 * T * β + 384304095 * S ^ 2 * β ^ 2 +
        87197250 * S ^ 2 * β - 5103000 * S ^ 2 - 64297800 * S * T ^ 2 * β ^ 2 + 401082750 * S * T * β ^ 2 -
        513624078 * S * β ^ 2 - 157351500 * S * β + 45927000 * T ^ 2 * β ^ 2 - 350844750 * T * β ^ 2 +
        482717070 * β ^ 2) / 14849347275) * u +
      A0V_Uk 3 0 β S (Q - β * T) := by
  rw [A0V_Uk_eq 3 u (u / 3 + β) (S - u * T) (Q - (u / 3 + β) * T),
      A0V_Uk_eq 3 0 β S (Q - β * T)]
  have hd10 : d10_U3 u (u / 3 + β) (S - u * T) (Q - (u / 3 + β) * T) =
      (-(8 / 2187 : R) * T * (3 * Q - S) * (3 * Q - S - 3 * T * β)) * u ^ 2 +
      (-(8 / 15309 : R) * (3 * Q - S - 3 * T * β) * (630 * Q ^ 2 - 441 * Q * S - 630 * Q * T * β - 135 * Q +
        77 * S ^ 2 + 189 * S * T * β + 45 * S - 135 * T * β)) * u +
      d10_U3 0 β S (Q - β * T) := by
    rw [d10_U3_eq, d10_U3_eq]; ring
  have hd20 : d20_U3 u (u / 3 + β) (S - u * T) (Q - (u / 3 + β) * T) =
      ((4 / 2187 : R) * (3 * Q - S) * (3 * Q - S - 6 * T * β)) * u ^ 2 +
      (-(8 / 5103 : R) * β * (630 * Q ^ 2 - 420 * Q * S - 630 * Q * T * β + 70 * S ^ 2 + 189 * S * T * β - 135 * T * β)) * u +
      d20_U3 0 β S (Q - β * T) := by
    rw [d20_U3_eq, d20_U3_eq]; ring
  have hd21 : d21_U3 u (u / 3 + β) (S - u * T) (Q - (u / 3 + β) * T) =
      ((8 / 729 : R) * β * (3 * Q - S)) * u ^ 2 +
      (-(8 / 567 : R) * β ^ 2 * (70 * Q - 21 * S + 15)) * u +
      d21_U3 0 β S (Q - β * T) := by
    rw [d21_U3_eq, d21_U3_eq]; ring
  rw [hd10, hd20, hd21]
  have hd10_0 : d10_U3 0 β S (Q - β * T) =
      (8 / 5103 : R) * β * (3 * Q - S - 3 * T * β) * (210 * Q * S - 135 * Q - 77 * S ^ 2 - 210 * S * T * β - 45 * S + 135 * T * β - 270) := by
    rw [d10_U3_eq]; ring
  have hd20_0 : d20_U3 0 β S (Q - β * T) =
      (4 / 567 : R) * β ^ 2 * (140 * Q * S - 90 * Q - 49 * S ^ 2 - 140 * S * T * β + 90 * T * β - 90) := by
    rw [d20_U3_eq]; ring
  have hd21_0 : d21_U3 0 β S (Q - β * T) = (40 / 567 : R) * β ^ 3 * (14 * S - 9) := by
    rw [d21_U3_eq]; ring
  rw [hd10_0, hd20_0, hd21_0]
  ring

lemma A0V_U3_poly {R : Type*} [Field R] [CharZero R] (S Q T u : R)
    (hT : T ≠ 0) (hT59 : 5 * T - 9 ≠ 0) :
    let β : R := -(S - 3 * Q) * (5 * T - 3) / (3 * T * (5 * T - 9))
    A0V_Uk 3 u (u / 3 + β) (S - u * T) (Q - (u / 3 + β) * T) =
      ((73 / 7971615 : R) * (5 * T - 9) * (S - 3 * Q) ^ 2) * u ^ 3 +
      (A32_2_q_fn S Q T * (5 * T - 9) * (S - 3 * Q) / (14849347275 * (3 * T * (5 * T - 9)))) * u ^ 2 +
      (A32_1_q_fn S Q T * (5 * T - 9) * (S - 3 * Q) / (4949782425 * (3 * T * (5 * T - 9)) ^ 2)) * u +
      A0V_Uk 3 0 β S (Q - β * T) := by
  intro β
  rw [A0V_U3_poly_beta S Q T u β]
  have h3T : (3 : R) * T * (5 * T - 9) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by exact_mod_cast (by decide : (3 : ℕ) ≠ 0)) hT) hT59
  have h14849_ne : (14849347275 : R) ≠ 0 := by exact_mod_cast (by decide : (14849347275 : ℕ) ≠ 0)
  have h4949_ne : (4949782425 : R) ≠ 0 := by exact_mod_cast (by decide : (4949782425 : ℕ) ≠ 0)
  have hc2 :
      ((3 * Q - S) * (329432250 * Q ^ 2 - 225740725 * Q * S - 329432250 * Q * T * β + 7144200 * Q * T +
        592978050 * Q * β - 87606000 * Q + 38643325 * S ^ 2 + 97572300 * S * T * β - 2381400 * S * T -
        175630140 * S * β + 29202000 * S - 7144200 * T ^ 2 * β + 17860500 * T * β - 9001692 * β) / 44548041825) =
      A32_2_q_fn S Q T * (5 * T - 9) * (S - 3 * Q) / (14849347275 * (3 * T * (5 * T - 9))) := by
    have h445 : (44548041825 : R) = 3 * 14849347275 := by norm_num
    rw [h445, div_eq_div_iff (mul_ne_zero (by exact_mod_cast (by decide : (3 : ℕ) ≠ 0)) h14849_ne)
      (mul_ne_zero h14849_ne h3T)]
    have hβ : β * (3 * T * (5 * T - 9)) = -(S - 3 * Q) * (5 * T - 3) := div_mul_cancel₀ _ h3T
    have hmul :
        ((3 * Q - S) * (329432250 * Q ^ 2 - 225740725 * Q * S - 329432250 * Q * T * β + 7144200 * Q * T +
          592978050 * Q * β - 87606000 * Q + 38643325 * S ^ 2 + 97572300 * S * T * β - 2381400 * S * T -
          175630140 * S * β + 29202000 * S - 7144200 * T ^ 2 * β + 17860500 * T * β - 9001692 * β)) *
        (3 * T * (5 * T - 9)) =
        3 * (A32_2_q_fn S Q T * (5 * T - 9) * (S - 3 * Q)) := by
      have hpoly :
          (3 * Q - S) * ((329432250 * Q ^ 2 - 225740725 * Q * S + 7144200 * Q * T - 87606000 * Q +
            38643325 * S ^ 2 - 2381400 * S * T + 29202000 * S) * (3 * T * (5 * T - 9)) +
            (-329432250 * Q * T + 592978050 * Q + 97572300 * S * T - 175630140 * S -
              7144200 * T ^ 2 + 17860500 * T - 9001692) * (-(S - 3 * Q) * (5 * T - 3))) =
          3 * (A32_2_q_fn S Q T * (5 * T - 9) * (S - 3 * Q)) := by
        dsimp only [A32_2_q_fn]; ring
      linear_combination hpoly +
        (3 * Q - S) * (-329432250 * Q * T + 592978050 * Q + 97572300 * S * T - 175630140 * S -
          7144200 * T ^ 2 + 17860500 * T - 9001692) * hβ
    linear_combination (14849347275 : R) * hmul
  have hc1 :
      ((214326000 * Q ^ 3 - 658864500 * Q ^ 2 * S * β - 221470200 * Q ^ 2 * S - 428652000 * Q ^ 2 * T * β +
        1256829750 * Q ^ 2 * β - 45927000 * Q ^ 2 + 451481450 * Q * S ^ 2 * β + 76204800 * Q * S ^ 2 +
        658864500 * Q * S * T * β ^ 2 + 285768000 * Q * S * T * β - 1185956100 * Q * S * β ^ 2 -
        680535000 * Q * S * β + 30618000 * Q * S + 214326000 * Q * T ^ 2 * β ^ 2 - 1256829750 * Q * T * β ^ 2 +
        1567877310 * Q * β ^ 2 + 472054500 * Q * β - 77286650 * S ^ 3 * β - 8731800 * S ^ 3 -
        213502275 * S ^ 2 * T * β ^ 2 - 47628000 * S ^ 2 * T * β + 384304095 * S ^ 2 * β ^ 2 +
        87197250 * S ^ 2 * β - 5103000 * S ^ 2 - 64297800 * S * T ^ 2 * β ^ 2 + 401082750 * S * T * β ^ 2 -
        513624078 * S * β ^ 2 - 157351500 * S * β + 45927000 * T ^ 2 * β ^ 2 - 350844750 * T * β ^ 2 +
        482717070 * β ^ 2) / 14849347275) =
      A32_1_q_fn S Q T * (5 * T - 9) * (S - 3 * Q) / (4949782425 * (3 * T * (5 * T - 9)) ^ 2) := by
    have h148 : (14849347275 : R) = 3 * 4949782425 := by norm_num
    rw [h148, div_eq_div_iff (mul_ne_zero (by exact_mod_cast (by decide : (3 : ℕ) ≠ 0)) h4949_ne)
      (mul_ne_zero h4949_ne (pow_ne_zero 2 h3T))]
    have hβ : β * (3 * T * (5 * T - 9)) = -(S - 3 * Q) * (5 * T - 3) := div_mul_cancel₀ _ h3T
    have hβ2 : β ^ 2 * (3 * T * (5 * T - 9)) ^ 2 = (-(S - 3 * Q) * (5 * T - 3)) ^ 2 := by
      rw [← mul_pow, hβ]
    have hmul :
        (214326000 * Q ^ 3 - 658864500 * Q ^ 2 * S * β - 221470200 * Q ^ 2 * S - 428652000 * Q ^ 2 * T * β +
          1256829750 * Q ^ 2 * β - 45927000 * Q ^ 2 + 451481450 * Q * S ^ 2 * β + 76204800 * Q * S ^ 2 +
          658864500 * Q * S * T * β ^ 2 + 285768000 * Q * S * T * β - 1185956100 * Q * S * β ^ 2 -
          680535000 * Q * S * β + 30618000 * Q * S + 214326000 * Q * T ^ 2 * β ^ 2 - 1256829750 * Q * T * β ^ 2 +
          1567877310 * Q * β ^ 2 + 472054500 * Q * β - 77286650 * S ^ 3 * β - 8731800 * S ^ 3 -
          213502275 * S ^ 2 * T * β ^ 2 - 47628000 * S ^ 2 * T * β + 384304095 * S ^ 2 * β ^ 2 +
          87197250 * S ^ 2 * β - 5103000 * S ^ 2 - 64297800 * S * T ^ 2 * β ^ 2 + 401082750 * S * T * β ^ 2 -
          513624078 * S * β ^ 2 - 157351500 * S * β + 45927000 * T ^ 2 * β ^ 2 - 350844750 * T * β ^ 2 +
          482717070 * β ^ 2) * (3 * T * (5 * T - 9)) ^ 2 =
        3 * (A32_1_q_fn S Q T * (5 * T - 9) * (S - 3 * Q)) := by
      have hpoly :
          (214326000 * Q ^ 3 - 221470200 * Q ^ 2 * S - 45927000 * Q ^ 2 + 76204800 * Q * S ^ 2 +
            30618000 * Q * S - 8731800 * S ^ 3 - 5103000 * S ^ 2) * (3 * T * (5 * T - 9)) ^ 2 +
          (-658864500 * Q ^ 2 * S - 428652000 * Q ^ 2 * T + 1256829750 * Q ^ 2 + 451481450 * Q * S ^ 2 +
            285768000 * Q * S * T - 680535000 * Q * S + 472054500 * Q - 77286650 * S ^ 3 -
            47628000 * S ^ 2 * T + 87197250 * S ^ 2 - 157351500 * S) * (-(S - 3 * Q) * (5 * T - 3)) * (3 * T * (5 * T - 9)) +
          (658864500 * Q * S * T - 1185956100 * Q * S + 214326000 * Q * T ^ 2 - 1256829750 * Q * T +
            1567877310 * Q - 213502275 * S ^ 2 * T + 384304095 * S ^ 2 - 64297800 * S * T ^ 2 +
            401082750 * S * T - 513624078 * S + 45927000 * T ^ 2 - 350844750 * T + 482717070) *
            (-(S - 3 * Q) * (5 * T - 3)) ^ 2 =
          3 * (A32_1_q_fn S Q T * (5 * T - 9) * (S - 3 * Q)) := by
        dsimp only [A32_1_q_fn]; ring
      linear_combination hpoly +
        (-658864500 * Q ^ 2 * S - 428652000 * Q ^ 2 * T + 1256829750 * Q ^ 2 + 451481450 * Q * S ^ 2 +
          285768000 * Q * S * T - 680535000 * Q * S + 472054500 * Q - 77286650 * S ^ 3 -
          47628000 * S ^ 2 * T + 87197250 * S ^ 2 - 157351500 * S) * (3 * T * (5 * T - 9)) * hβ +
        (658864500 * Q * S * T - 1185956100 * Q * S + 214326000 * Q * T ^ 2 - 1256829750 * Q * T +
          1567877310 * Q - 213502275 * S ^ 2 * T + 384304095 * S ^ 2 - 64297800 * S * T ^ 2 +
          401082750 * S * T - 513624078 * S + 45927000 * T ^ 2 - 350844750 * T + 482717070) * hβ2
    linear_combination (4949782425 : R) * hmul
  rw [hc2, hc1]

def A0V_U3_lead3_fn {R : Type*} [Field R] (S Q T aa ab : R) : R :=
  -(1 / 4949782425 : R) * (5 * T - 9) *
    (-7728665 * Q ^ 2 * aa ^ 3 - 1746360 * Q * T * aa ^ 3 + 15457330 * S * Q * aa ^ 2 * ab +
     21962150 * Q ^ 2 * aa ^ 2 * ab + 1746360 * S * T * aa ^ 2 * ab + 10001880 * Q * T * aa ^ 2 * ab -
     7728665 * S ^ 2 * aa * ab ^ 2 - 43924300 * S * Q * aa * ab ^ 2 - 10001880 * S * T * aa * ab ^ 2 -
     14288400 * Q * T * aa * ab ^ 2 + 21962150 * S ^ 2 * ab ^ 3 + 14288400 * S * T * ab ^ 3 +
     6563302 * Q * aa ^ 3 - 6563302 * S * aa ^ 2 * ab - 39046416 * Q * aa ^ 2 * ab -
     1020600 * T * aa ^ 2 * ab + 39046416 * S * aa * ab ^ 2 + 58069530 * Q * aa * ab ^ 2 +
     6123600 * T * aa * ab ^ 2 - 58069530 * S * ab ^ 3 - 9185400 * T * ab ^ 3 +
     5340850 * aa ^ 3 - 42108180 * aa ^ 2 * ab + 108446130 * aa * ab ^ 2 - 90567720 * ab ^ 3)

lemma A0V_U3_lead3_eq {R : Type*} [Field R] [CharZero R] (S Q T aa ab b0 : R) :
    let f := fun z : R => A0V_Uk 3 (aa * z) (ab * z + b0) (S - aa * z * T) (Q - (ab * z + b0) * T)
    (f 2 - 3 * f 1 + 3 * f 0 - f (-1)) / 6 = A0V_U3_lead3_fn S Q T aa ab := by
  intro f
  let D10 : R → R := fun z => d10_U3 (aa * z) (ab * z + b0) (S - aa * z * T) (Q - (ab * z + b0) * T)
  let D20 : R → R := fun z => d20_U3 (aa * z) (ab * z + b0) (S - aa * z * T) (Q - (ab * z + b0) * T)
  let D21 : R → R := fun z => d21_U3 (aa * z) (ab * z + b0) (S - aa * z * T) (Q - (ab * z + b0) * T)
  let p10_1 : R := -(223 * aa - 450 * ab) / 2916
  let p10_0 : R := (11975 * b0 - 1134) / 77598
  let p20_1 : R := -(5 * T + 9) * (223 * aa - 450 * ab) / 14580
  let p20_0 : R := (-215550 * Q + 106817 * S + 215550 * T * b0 + 387990 * b0 - 51030) / 1396764
  let p21_1 : R := -T * (223 * aa - 450 * ab) / 1620
  let p21_0 : R := (-1077750 * Q + 534085 * S + 1077750 * T * b0 - 71442) / 3879900
  have hf_eq : ∀ z, f z = (p10_1 * z + p10_0) * D10 z + (p20_1 * z + p20_0) * D20 z + (p21_1 * z + p21_0) * D21 z := by
    intro z
    change A0V_Uk 3 (aa * z) (ab * z + b0) (S - aa * z * T) (Q - (ab * z + b0) * T) = _
    rw [A0V_Uk_eq 3]
    dsimp only [p10_1, p10_0, p20_1, p20_0, p21_1, p21_0, D10, D20, D21]
    ring
  have hsplit : (f 2 - 3 * f 1 + 3 * f 0 - f (-1)) / 6 =
      p10_1 * ((2 * D10 2 - 3 * D10 1 + D10 (-1)) / 6) + p10_0 * ((D10 2 - 3 * D10 1 + 3 * D10 0 - D10 (-1)) / 6) +
      p20_1 * ((2 * D20 2 - 3 * D20 1 + D20 (-1)) / 6) + p20_0 * ((D20 2 - 3 * D20 1 + 3 * D20 0 - D20 (-1)) / 6) +
      p21_1 * ((2 * D21 2 - 3 * D21 1 + D21 (-1)) / 6) + p21_0 * ((D21 2 - 3 * D21 1 + 3 * D21 0 - D21 (-1)) / 6) := by
    rw [hf_eq 2, hf_eq 1, hf_eq 0, hf_eq (-1)]
    have h1 := diff3_lin_mul p10_1 p10_0 D10
    have h2 := diff3_lin_mul p20_1 p20_0 D20
    have h3 := diff3_lin_mul p21_1 p21_0 D21
    dsimp only at h1 h2 h3
    linear_combination h1 + h2 + h3
  have hd10_d : (D10 2 - 3 * D10 1 + 3 * D10 0 - D10 (-1)) / 6 =
      -(8 / 5103 : R) * T ^ 2 * (aa - 3 * ab) *
        (77 * Q * aa ^ 2 - 210 * Q * aa * ab - 77 * S * aa * ab + 210 * S * ab ^ 2 + 45 * aa * ab - 135 * ab ^ 2) := by
    dsimp only [D10]; simp only [d10_U3_eq]; ring
  have hd10_w : (2 * D10 2 - 3 * D10 1 + D10 (-1)) / 6 =
      (8 / 5103 : R) * T * (-441 * Q ^ 2 * aa ^ 2 + 1260 * Q ^ 2 * aa * ab + 154 * Q * S * aa ^ 2 - 1260 * Q * S * ab ^ 2 -
        154 * Q * T * aa ^ 3 + 882 * Q * T * aa ^ 2 * ab + 441 * Q * T * aa ^ 2 * b0 - 1260 * Q * T * aa * ab ^ 2 -
        1260 * Q * T * aa * ab * b0 + 90 * Q * aa ^ 2 - 540 * Q * aa * ab + 810 * Q * ab ^ 2 - 154 * S ^ 2 * aa * ab +
        441 * S ^ 2 * ab ^ 2 + 154 * S * T * aa ^ 2 * ab + 77 * S * T * aa ^ 2 * b0 - 882 * S * T * aa * ab ^ 2 -
        882 * S * T * aa * ab * b0 + 1260 * S * T * ab ^ 3 + 1890 * S * T * ab ^ 2 * b0 - 90 * T * aa ^ 2 * ab -
        45 * T * aa ^ 2 * b0 + 540 * T * aa * ab ^ 2 + 540 * T * aa * ab * b0 - 810 * T * ab ^ 3 -
        1215 * T * ab ^ 2 * b0 + 90 * aa ^ 2 - 540 * aa * ab + 810 * ab ^ 2) := by
    dsimp only [D10]; simp only [d10_U3_eq]; ring
  have hd20_d : (D20 2 - 3 * D20 1 + 3 * D20 0 - D20 (-1)) / 6 =
      (8 / 5103 : R) * T * (aa - 3 * ab) *
        (77 * Q * aa ^ 2 - 210 * Q * aa * ab - 77 * S * aa * ab + 210 * S * ab ^ 2 + 45 * aa * ab - 135 * ab ^ 2) := by
    dsimp only [D20]; simp only [d20_U3_eq]; ring
  have hd20_w : (2 * D20 2 - 3 * D20 1 + D20 (-1)) / 6 =
      -(4 / 5103 : R) * (-441 * Q ^ 2 * aa ^ 2 + 1260 * Q ^ 2 * aa * ab + 154 * Q * S * aa ^ 2 - 1260 * Q * S * ab ^ 2 -
        308 * Q * T * aa ^ 3 + 1764 * Q * T * aa ^ 2 * ab + 882 * Q * T * aa ^ 2 * b0 - 2520 * Q * T * aa * ab ^ 2 -
        2520 * Q * T * aa * ab * b0 + 90 * Q * aa ^ 2 - 540 * Q * aa * ab + 810 * Q * ab ^ 2 - 154 * S ^ 2 * aa * ab +
        441 * S ^ 2 * ab ^ 2 + 308 * S * T * aa ^ 2 * ab + 154 * S * T * aa ^ 2 * b0 - 1764 * S * T * aa * ab ^ 2 -
        1764 * S * T * aa * ab * b0 + 2520 * S * T * ab ^ 3 + 3780 * S * T * ab ^ 2 * b0 - 180 * T * aa ^ 2 * ab -
        90 * T * aa ^ 2 * b0 + 1080 * T * aa * ab ^ 2 + 1080 * T * aa * ab * b0 - 1620 * T * ab ^ 3 -
        2430 * T * ab ^ 2 * b0 + 90 * aa ^ 2 - 540 * aa * ab + 810 * ab ^ 2) := by
    dsimp only [D20]; simp only [d20_U3_eq]; ring
  have hd21_d : (D21 2 - 3 * D21 1 + 3 * D21 0 - D21 (-1)) / 6 =
      -(8 / 5103 : R) * (aa - 3 * ab) *
        (77 * Q * aa ^ 2 - 210 * Q * aa * ab - 77 * S * aa * ab + 210 * S * ab ^ 2 + 45 * aa * ab - 135 * ab ^ 2) := by
    dsimp only [D21]; simp only [d21_U3_eq]; ring
  have hd21_w : (2 * D21 2 - 3 * D21 1 + D21 (-1)) / 6 =
      (8 / 5103 : R) * (-154 * Q * aa ^ 3 + 882 * Q * aa ^ 2 * ab + 441 * Q * aa ^ 2 * b0 - 1260 * Q * aa * ab ^ 2 -
        1260 * Q * aa * ab * b0 + 154 * S * aa ^ 2 * ab + 77 * S * aa ^ 2 * b0 - 882 * S * aa * ab ^ 2 -
        882 * S * aa * ab * b0 + 1260 * S * ab ^ 3 + 1890 * S * ab ^ 2 * b0 - 90 * aa ^ 2 * ab -
        45 * aa ^ 2 * b0 + 540 * aa * ab ^ 2 + 540 * aa * ab * b0 - 810 * ab ^ 3 - 1215 * ab ^ 2 * b0) := by
    dsimp only [D21]; simp only [d21_U3_eq]; ring
  rw [hsplit, hd10_d, hd10_w, hd20_d, hd20_w, hd21_d, hd21_w]
  dsimp only [p10_1, p10_0, p20_1, p20_0, p21_1, p21_0, A0V_U3_lead3_fn]
  ring

lemma A0V_U2_lead3_at_third {R : Type*} [Field R] [CharZero R] (S Q T aa b0 : R) :
    let f := fun z : R => A0V_Uk 2 (aa * z) ((aa / 3) * z + b0) (S - aa * z * T) (Q - ((aa / 3) * z + b0) * T)
    (f 2 - 3 * f 1 + 3 * f 0 - f (-1)) / 6 =
      aa ^ 3 * ((1 / 53457650190 : R) * (5 * T - 9) *
        (-50137409 * S ^ 2 + 300824454 * S * Q - 451236681 * Q ^ 2 - 10001880 * S * T +
         30005640 * Q * T - 45873099 * S + 137619297 * Q - 10103940 * T + 58998753)) := by
  intro f
  let D10 : R → R := fun z => d10_U2 (aa * z) ((aa / 3) * z + b0) (S - aa * z * T) (Q - ((aa / 3) * z + b0) * T)
  let D20 : R → R := fun z => d20_U2 (aa * z) ((aa / 3) * z + b0) (S - aa * z * T) (Q - ((aa / 3) * z + b0) * T)
  let D21 : R → R := fun z => d21_U2 (aa * z) ((aa / 3) * z + b0) (S - aa * z * T) (Q - ((aa / 3) * z + b0) * T)
  let p10_1 : R := -(73 / 2916 : R) * aa
  let p10_0 : R := (11975 * b0 - 1134) / 77598
  let p20_1 : R := -(73 / 14580 : R) * aa * (5 * T + 9)
  let p20_0 : R := (-215550 * Q + 106817 * S + 215550 * T * b0 + 387990 * b0 - 51030) / 1396764
  let p21_1 : R := -(73 / 1620 : R) * T * aa
  let p21_0 : R := (-1077750 * Q + 534085 * S + 1077750 * T * b0 - 71442) / 3879900
  have hf_eq : ∀ z, f z = (p10_1 * z + p10_0) * D10 z + (p20_1 * z + p20_0) * D20 z + (p21_1 * z + p21_0) * D21 z := by
    intro z
    change A0V_Uk 2 (aa * z) ((aa / 3) * z + b0) (S - aa * z * T) (Q - ((aa / 3) * z + b0) * T) = _
    rw [A0V_Uk_eq 2]
    dsimp only [p10_1, p10_0, p20_1, p20_0, p21_1, p21_0, D10, D20, D21]
    ring
  have hsplit : (f 2 - 3 * f 1 + 3 * f 0 - f (-1)) / 6 =
      p10_1 * ((2 * D10 2 - 3 * D10 1 + D10 (-1)) / 6) + p10_0 * ((D10 2 - 3 * D10 1 + 3 * D10 0 - D10 (-1)) / 6) +
      p20_1 * ((2 * D20 2 - 3 * D20 1 + D20 (-1)) / 6) + p20_0 * ((D20 2 - 3 * D20 1 + 3 * D20 0 - D20 (-1)) / 6) +
      p21_1 * ((2 * D21 2 - 3 * D21 1 + D21 (-1)) / 6) + p21_0 * ((D21 2 - 3 * D21 1 + 3 * D21 0 - D21 (-1)) / 6) := by
    rw [hf_eq 2, hf_eq 1, hf_eq 0, hf_eq (-1)]
    have h1 := diff3_lin_mul p10_1 p10_0 D10
    have h2 := diff3_lin_mul p20_1 p20_0 D20
    have h3 := diff3_lin_mul p21_1 p21_0 D21
    dsimp only at h1 h2 h3
    linear_combination h1 + h2 + h3
  have hd10_d : (D10 2 - 3 * D10 1 + 3 * D10 0 - D10 (-1)) / 6 =
      -(10 / 15309 : R) * T ^ 2 * aa ^ 3 * (294 * Q - 98 * S - 99) := by
    dsimp only [D10]; simp only [d10_U2_eq]; ring
  have hd10_w : (2 * D10 2 - 3 * D10 1 + D10 (-1)) / 6 =
      -(2 / 15309 : R) * T * aa ^ 2 * (-7686 * Q ^ 2 + 2184 * Q * S + 2940 * Q * T * aa + 7686 * Q * T * b0 +
        2970 * Q + 126 * S ^ 2 - 980 * S * T * aa - 4032 * S * T * b0 - 990 * T * aa + 9315 * T * b0 + 2970) := by
    dsimp only [D10]; simp only [d10_U2_eq]; ring
  have hd20_d : (D20 2 - 3 * D20 1 + 3 * D20 0 - D20 (-1)) / 6 =
      (10 / 15309 : R) * T * aa ^ 3 * (294 * Q - 98 * S - 99) := by
    dsimp only [D20]; simp only [d20_U2_eq]; ring
  have hd20_w : (2 * D20 2 - 3 * D20 1 + D20 (-1)) / 6 =
      (2 / 15309 : R) * aa ^ 2 * (-3843 * Q ^ 2 + 1092 * Q * S + 2940 * Q * T * aa + 7686 * Q * T * b0 +
        1485 * Q + 63 * S ^ 2 - 980 * S * T * aa - 4032 * S * T * b0 - 990 * T * aa + 9315 * T * b0 + 1485) := by
    dsimp only [D20]; simp only [d20_U2_eq]; ring
  have hd21_d : (D21 2 - 3 * D21 1 + 3 * D21 0 - D21 (-1)) / 6 =
      -(10 / 15309 : R) * aa ^ 3 * (294 * Q - 98 * S - 99) := by
    dsimp only [D21]; simp only [d21_U2_eq]; ring
  have hd21_w : (2 * D21 2 - 3 * D21 1 + D21 (-1)) / 6 =
      -(2 / 15309 : R) * aa ^ 2 * (2940 * Q * aa + 7686 * Q * b0 - 980 * S * aa - 4032 * S * b0 - 990 * aa + 9315 * b0) := by
    dsimp only [D21]; simp only [d21_U2_eq]; ring
  rw [hsplit, hd10_d, hd10_w, hd20_d, hd20_w, hd21_d, hd21_w]
  dsimp only [p10_1, p10_0, p20_1, p20_0, p21_1, p21_0]
  ring

lemma AX_U3_lead3_at_third {R : Type*} [Field R] [CharZero R] (S Q T aa b0 : R) :
    let f := fun z : R => AX_Uk 3 (aa * z) ((aa / 3) * z + b0) (S - aa * z * T) (Q - ((aa / 3) * z + b0) * T)
    (f 2 - 3 * f 1 + 3 * f 0 - f (-1)) / 6 =
      aa ^ 3 * ((2 / 885735 : R) * (5 * T - 9) * (S - 3 * Q) ^ 2) := by
  intro f
  let D10 : R → R := fun z => d10_U3 (aa * z) ((aa / 3) * z + b0) (S - aa * z * T) (Q - ((aa / 3) * z + b0) * T)
  let D20 : R → R := fun z => d20_U3 (aa * z) ((aa / 3) * z + b0) (S - aa * z * T) (Q - ((aa / 3) * z + b0) * T)
  let D21 : R → R := fun z => d21_U3 (aa * z) ((aa / 3) * z + b0) (S - aa * z * T) (Q - ((aa / 3) * z + b0) * T)
  let p10_1 : R := -(1 / 162 : R) * aa
  let p10_0 : R := -(119 / 5748 : R)
  let p20_1 : R := -(1 / 810 : R) * aa * (5 * T + 9)
  let p20_0 : R := (479 * S - 7560) / 77598
  let p21_1 : R := -(1 / 90 : R) * T * aa
  let p21_0 : R := (4790 * S - 46683) / 431100
  have hf_eq : ∀ z, f z = (p10_1 * z + p10_0) * D10 z + (p20_1 * z + p20_0) * D20 z + (p21_1 * z + p21_0) * D21 z := by
    intro z
    change AX_Uk 3 (aa * z) ((aa / 3) * z + b0) (S - aa * z * T) (Q - ((aa / 3) * z + b0) * T) = _
    rw [AX_Uk_eq 3]
    dsimp only [p10_1, p10_0, p20_1, p20_0, p21_1, p21_0, D10, D20, D21]
    ring
  have hsplit : (f 2 - 3 * f 1 + 3 * f 0 - f (-1)) / 6 =
      p10_1 * ((2 * D10 2 - 3 * D10 1 + D10 (-1)) / 6) + p10_0 * ((D10 2 - 3 * D10 1 + 3 * D10 0 - D10 (-1)) / 6) +
      p20_1 * ((2 * D20 2 - 3 * D20 1 + D20 (-1)) / 6) + p20_0 * ((D20 2 - 3 * D20 1 + 3 * D20 0 - D20 (-1)) / 6) +
      p21_1 * ((2 * D21 2 - 3 * D21 1 + D21 (-1)) / 6) + p21_0 * ((D21 2 - 3 * D21 1 + 3 * D21 0 - D21 (-1)) / 6) := by
    rw [hf_eq 2, hf_eq 1, hf_eq 0, hf_eq (-1)]
    have h1 := diff3_lin_mul p10_1 p10_0 D10
    have h2 := diff3_lin_mul p20_1 p20_0 D20
    have h3 := diff3_lin_mul p21_1 p21_0 D21
    dsimp only at h1 h2 h3
    linear_combination h1 + h2 + h3
  have hd10_d : (D10 2 - 3 * D10 1 + 3 * D10 0 - D10 (-1)) / 6 = 0 := by
    dsimp only [D10]; simp only [d10_U3_eq]; ring
  have hd10_w : (2 * D10 2 - 3 * D10 1 + D10 (-1)) / 6 =
      (8 / 2187 : R) * T * aa ^ 2 * (3 * Q - S) * (-3 * Q + S + 3 * T * b0) := by
    dsimp only [D10]; simp only [d10_U3_eq]; ring
  have hd20_d : (D20 2 - 3 * D20 1 + 3 * D20 0 - D20 (-1)) / 6 = 0 := by
    dsimp only [D20]; simp only [d20_U3_eq]; ring
  have hd20_w : (2 * D20 2 - 3 * D20 1 + D20 (-1)) / 6 =
      -(4 / 2187 : R) * aa ^ 2 * (3 * Q - S) * (-3 * Q + S + 6 * T * b0) := by
    dsimp only [D20]; simp only [d20_U3_eq]; ring
  have hd21_d : (D21 2 - 3 * D21 1 + 3 * D21 0 - D21 (-1)) / 6 = 0 := by
    dsimp only [D21]; simp only [d21_U3_eq]; ring
  have hd21_w : (2 * D21 2 - 3 * D21 1 + D21 (-1)) / 6 =
      (8 / 729 : R) * aa ^ 2 * b0 * (3 * Q - S) := by
    dsimp only [D21]; simp only [d21_U3_eq]; ring
  rw [hsplit, hd10_d, hd10_w, hd20_d, hd20_w, hd21_d, hd21_w]
  dsimp only [p10_1, p10_0, p20_1, p20_0, p21_1, p21_0]
  ring

lemma M01_dual_combine {R : Type*} [Field R] [CharZero R] (S Q T : R) :
    let Bv1 : R := (143 / 243 : R) * S ^ 3 - (92 / 27) * S ^ 2 * Q + (52 / 9) * S * Q ^ 2 - (22 / 9) * Q ^ 3 +
      (143 / 243) * T ^ 3 - (92 / 27) * T ^ 2 + (52 / 9) * T - (22 / 9) + (5 / 7) * Q ^ 2 + (10 / 7) * Q
    let w1w0_sc : R := (243 / 4 : R) * Bv1
    let rb_sc : R := -(3 / 28 : R) * (S - 3 * Q) * (119 * S ^ 2 - 560 * S * Q + 630 * Q ^ 2 + 90 * Q + 90)
    let c0 : R := (73 / 7971615 : R) * (5 * T - 9) * (S - 3 * Q) ^ 2
    let dc0 : R := -(2 / 2121335325 : R) * (5 * T - 9) * (-464630 * S + 1568725 * Q + 34020 * T - 23814) * (-S + 3 * Q)
    let c2 : R := (1 / 53457650190 : R) * (5 * T - 9) *
      (-50137409 * S ^ 2 + 300824454 * S * Q - 451236681 * Q ^ 2 - 10001880 * S * T +
       30005640 * Q * T - 45873099 * S + 137619297 * Q - 10103940 * T + 58998753);
    -2 * w1w0_sc * c0 + (rb_sc / 3) * dc0 + (S - 3 * Q) ^ 3 * c2 =
      M01_q_fn S Q T * (5 * T - 9) * (S - 3 * Q) / 267288250950 := by
  dsimp only [M01_q_fn]; ring

lemma A0V_U3_lead3_dual {R : Type*} [Field R] [CharZero R] (S Q T r1 : R) :
    let c0 : R := (73 / 7971615 : R) * (5 * T - 9) * (S - 3 * Q) ^ 2
    let dc0 : R := -(2 / 2121335325 : R) * (5 * T - 9) * (-464630 * S + 1568725 * Q + 34020 * T - 23814) * (-S + 3 * Q)
    (-(1 / 4949782425 : R) * (5 * T - 9) *
      (-7728665 * Q ^ 2 - 1746360 * Q * T + 15457330 * S * Q * (1 / 3 : R) +
       21962150 * Q ^ 2 * (1 / 3) + 1746360 * S * T * (1 / 3) + 10001880 * Q * T * (1 / 3) -
       7728665 * S ^ 2 * (1 / 3) ^ 2 - 43924300 * S * Q * (1 / 3) ^ 2 - 10001880 * S * T * (1 / 3) ^ 2 -
       14288400 * Q * T * (1 / 3) ^ 2 + 21962150 * S ^ 2 * (1 / 3) ^ 3 + 14288400 * S * T * (1 / 3) ^ 3 +
       6563302 * Q - 6563302 * S * (1 / 3) - 39046416 * Q * (1 / 3) -
       1020600 * T * (1 / 3) + 39046416 * S * (1 / 3) ^ 2 + 58069530 * Q * (1 / 3) ^ 2 +
       6123600 * T * (1 / 3) ^ 2 - 58069530 * S * (1 / 3) ^ 3 - 9185400 * T * (1 / 3) ^ 3 +
       5340850 - 42108180 * (1 / 3) + 108446130 * (1 / 3) ^ 2 - 90567720 * (1 / 3) ^ 3) = c0) ∧
    (-(1 / 4949782425 : R) * (5 * T - 9) *
      ((15457330 * S * Q + 21962150 * Q ^ 2 + 1746360 * S * T + 10001880 * Q * T -
        6563302 * S - 39046416 * Q - 1020600 * T - 42108180) +
       2 * (-7728665 * S ^ 2 - 43924300 * S * Q - 10001880 * S * T - 14288400 * Q * T +
        39046416 * S + 58069530 * Q + 6123600 * T + 108446130) * (1 / 3 : R) +
       3 * (21962150 * S ^ 2 + 14288400 * S * T - 58069530 * S - 9185400 * T - 90567720) * (1 / 3 : R) ^ 2) * r1 =
      dc0 * r1) := by
  dsimp only; constructor <;> ring

-- 1-term factored `br` and `om` identities for `(1,0), (0,0), (1,1)` UV-coefficients!
lemma br_10_eq {R : Type*} [Field R] [CharZero R] (k : Fin 5) (S Q T x y : R) :
    243 * (br_fn k S Q T x y 1 0 - br_fn k S Q T x y 0 0) =
      match k with
      | 0 => -5 * T * (5 * T - 9) * (9 * x - 25 * S + 15 * Q)
      | 1 => -150 * T * (5 * T - 9) * S
      | 2 => 5 * (5 * T - 3) * (27 * x - 25 * S + 45 * Q) * S
      | 3 => -90 * T * (5 * T - 9) * S
      | 4 => 0 := by
  fin_cases k <;> (simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, br_fn, LX_of, LY_of,
    dLX_fn, dLY_fn, u3_of, v3_of, u_of, v_of]; ring)

lemma br_00_eq {R : Type*} [Field R] [CharZero R] (k : Fin 5) (S Q T x y : R) :
    243 * br_fn k S Q T x y 0 0 =
      match k with
      | 0 => 25 * T * (5 * T - 9) * (-5 * S + 3 * Q)
      | 1 => 150 * T * (5 * T - 9) * S
      | 2 => -25 * (5 * T - 3) * (-5 * S + 9 * Q) * S
      | 3 => 0
      | 4 => 0 := by
  fin_cases k <;> (simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, br_fn, LX_of, LY_of,
    dLX_fn, dLY_fn, u3_of, v3_of, u_of, v_of]; ring)

lemma br_11_eq {R : Type*} [Field R] [CharZero R] (k : Fin 5) (S Q T x y : R) :
    243 * (br_fn k S Q T x y 1 1 - br_fn k S Q T x y 1 0 - br_fn k S Q T x y 0 1 + br_fn k S Q T x y 0 0) =
      match k with
      | 0 => -(27 * y - 25 * T + 45) * T * (9 * x - 25 * S + 15 * Q)
      | 1 => -30 * (27 * y - 25 * T + 45) * T * S
      | 2 => (9 * y - 25 * T + 15) * (27 * x - 25 * S + 45 * Q) * S
      | 3 => -18 * (27 * y - 25 * T + 45) * T * S
      | 4 => 18 * T * (27 * x - 25 * S + 45 * Q) * S := by
  fin_cases k <;> (simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, br_fn, LX_of, LY_of,
    dLX_fn, dLY_fn, u3_of, v3_of, u_of, v_of]; ring)

lemma om_10_eq {R : Type*} [Field R] [CharZero R] (i j : Fin 5) (S Q T x y : R) :
    81 * (om_fn i j S Q T x y 1 0 - om_fn i j S Q T x y 0 0) =
      let f : Fin 5 → Fin 5 → R := fun p q => match p, q with
        | 0, 2 => 5 * (5 * T - 3) * (9 * x - 25 * S + 15 * Q)
        | 1, 2 => 150 * (5 * T - 3) * S
        | 2, 3 => -90 * (5 * T - 3) * S
        | _, _ => 0
      f i j - f j i := by
  fin_cases i <;> fin_cases j <;> (simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, om_fn]; ring)

lemma om_00_eq {R : Type*} [Field R] [CharZero R] (i j : Fin 5) (S Q T x y : R) :
    81 * om_fn i j S Q T x y 0 0 =
      let f : Fin 5 → Fin 5 → R := fun p q => match p, q with
        | 0, 2 => -25 * (5 * T - 3) * (-5 * S + 3 * Q)
        | 1, 2 => -150 * (5 * T - 3) * S
        | _, _ => 0
      f i j - f j i := by
  fin_cases i <;> fin_cases j <;> (simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, om_fn]; ring)

lemma om_11_eq {R : Type*} [Field R] [CharZero R] (i j : Fin 5) (S Q T x y : R) :
    81 * (om_fn i j S Q T x y 1 1 - om_fn i j S Q T x y 1 0 - om_fn i j S Q T x y 0 1 + om_fn i j S Q T x y 0 0) =
      let f : Fin 5 → Fin 5 → R := fun p q => match p, q with
        | 0, 2 => (9 * y - 25 * T + 15) * (9 * x - 25 * S + 15 * Q)
        | 0, 4 => 18 * T * (9 * x - 25 * S + 15 * Q)
        | 1, 2 => 30 * (9 * y - 25 * T + 15) * S
        | 1, 4 => 540 * T * S
        | 2, 3 => -18 * (9 * y - 25 * T + 15) * S
        | 3, 4 => 324 * T * S
        | _, _ => 0
      f i j - f j i := by
  fin_cases i <;> fin_cases j <;> (simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, om_fn]; ring)

lemma QY_10_u1_zero {R : Type*} [Field R] [CharZero R] (S Q T x y : R) :
    3 * (QY_num S Q T x y 1 0 0 - QY_num S Q T x y 0 0 0) +
    (QY_num S Q T x y 1 0 1 - QY_num S Q T x y 0 0 1) = 0 := by
  have hb0 : br_fn 0 S Q T x y 1 0 = br_fn 0 S Q T x y 0 0 + (-5 * T * (5 * T - 9) * (9 * x - 25 * S + 15 * Q)) / 243 := by
    have h := br_10_eq 0 S Q T x y; dsimp only at h; linear_combination (1 / 243 : R) * h
  have hb1 : br_fn 1 S Q T x y 1 0 = br_fn 1 S Q T x y 0 0 + (-150 * T * (5 * T - 9) * S) / 243 := by
    have h := br_10_eq 1 S Q T x y; dsimp only at h; linear_combination (1 / 243 : R) * h
  have hb3 : br_fn 3 S Q T x y 1 0 = br_fn 3 S Q T x y 0 0 + (-90 * T * (5 * T - 9) * S) / 243 := by
    have h := br_10_eq 3 S Q T x y; dsimp only at h; linear_combination (1 / 243 : R) * h
  have hb4 : br_fn 4 S Q T x y 1 0 = br_fn 4 S Q T x y 0 0 := by
    have h := br_10_eq 4 S Q T x y; dsimp only at h; linear_combination (1 / 243 : R) * h
  have ho03 : om_fn 0 3 S Q T x y 1 0 = om_fn 0 3 S Q T x y 0 0 := by
    have h := om_10_eq 0 3 S Q T x y; dsimp only at h; linear_combination (1 / 81 : R) * h
  have ho40 : om_fn 4 0 S Q T x y 1 0 = om_fn 4 0 S Q T x y 0 0 := by
    have h := om_10_eq 4 0 S Q T x y; dsimp only at h; linear_combination (1 / 81 : R) * h
  have ho34 : om_fn 3 4 S Q T x y 1 0 = om_fn 3 4 S Q T x y 0 0 := by
    have h := om_10_eq 3 4 S Q T x y; dsimp only at h; linear_combination (1 / 81 : R) * h
  have ho13 : om_fn 1 3 S Q T x y 1 0 = om_fn 1 3 S Q T x y 0 0 := by
    have h := om_10_eq 1 3 S Q T x y; dsimp only at h; linear_combination (1 / 81 : R) * h
  have ho41 : om_fn 4 1 S Q T x y 1 0 = om_fn 4 1 S Q T x y 0 0 := by
    have h := om_10_eq 4 1 S Q T x y; dsimp only at h; linear_combination (1 / 81 : R) * h
  have hd4 : dDX2_fn 4 S Q x = 0 := rfl
  have hcore :
      3 * (dDX2_fn 0 S Q x * (-90 * T * (5 * T - 9) * S) -
           dDX2_fn 3 S Q x * (-5 * T * (5 * T - 9) * (9 * x - 25 * S + 15 * Q))) +
      (dDX2_fn 1 S Q x * (-90 * T * (5 * T - 9) * S) -
       dDX2_fn 3 S Q x * (-150 * T * (5 * T - 9) * S)) = 0 := by
    simp only [dDX2_fn, u3_of]; ring
  simp only [QY_num, Omega_F, dDX2_F, F_contract]
  rw [hb0, hb1, hb3, hb4, ho03, ho40, ho34, ho13, ho41, hd4]
  linear_combination -(DY2_of T y * dF5_fn 4 S Q T x y * S * T / 243) * hcore

-- Exact log-derivative verification of `W1_inf` weights `A4[3], A4[4], A3[4], A2[4]`!
lemma dual_div_eq_iff {R : Type*} [Field R] (a b c : Dual R) (hb : b.val ≠ 0) :
    a * ⟨b.val⁻¹, -b.eps / b.val ^ 2⟩ = c ↔ a = b * c := by
  constructor
  · intro h; rw [← h]
    ext
    · simp only [Dual.mul_val]; field_simp [hb]
    · simp only [Dual.mul_val, Dual.mul_eps]; field_simp [hb]; ring
  · intro h; rw [h]
    ext
    · simp only [Dual.mul_val]; field_simp [hb]
    · simp only [Dual.mul_val, Dual.mul_eps]; field_simp [hb]; ring

-- Purely symbolic log-derivative identity for `W1_inf_weights_alg` (no unfolding of concrete polynomials!):
lemma W1_inf_log_deriv {R : Type*} [Field R] [CharZero R]
    (Bv2 Bv1 : R) (WD cbD D22 D20 D33 : Dual R)
    (d21v d1s ress p1d0 A43 A44 ratio : R)
    (hBv2 : Bv2 ≠ 0) (hcb : cbD.val ≠ 0) (hd22 : D22.val ≠ 0) (hd20 : D20.val ≠ 0) (hd33 : D33.val ≠ 0)
    (hw_rel : WD.eps * Bv2 = -WD.val * Bv1)
    (hA4_ratio : A44 = A43 * ratio)
    (hval : (-(WD.val * cbD.val ^ 4)) * (D22.val ^ 2 * D20.val ^ 3 * D33.val) =
      (81 * Bv2 * D22.val ^ 3 * (D20.val ^ 3 * D33.val ^ 2)) * A43)
    (hsum : (-2 * Bv1 / Bv2 + 4 * cbD.eps / cbD.val - D22.eps / D22.val - D33.eps / D33.val -
      d21v ^ 2 / (D22.val * D20.val) - d1s / (D22.val * D20.val * D33.val) -
      ress / (D20.val ^ 3 * D33.val ^ 2) + p1d0 / (D22.val ^ 2 * D20.val ^ 3 * D33.val)) - ratio = 0)
    (num_pref d1_D res_D den_pref P0_4_D C4_D : Dual R)
    (hnum : num_pref = -(WD * cbD ^ 4))
    (hd1 : d1_D = ⟨(-(D22 * D20 * D33)).val, (-(D22 * D20 * D33)).eps + d1s⟩)
    (hres : res_D = ⟨(D20 ^ 3 * D33 ^ 2).val, (D20 ^ 3 * D33 ^ 2).eps + ress⟩)
    (hden : den_pref = Dual.C (81 : R) * ⟨Bv2, Bv1⟩ * D22 ^ 3 * res_D)
    (hP0 : P0_4_D = ⟨(D22 * D20 ^ 2).val, (D22 * D20 ^ 2).eps - d21v ^ 2 * D20.val⟩)
    (hC4 : C4_D = ⟨(-(P0_4_D * d1_D)).val, (-(P0_4_D * d1_D)).eps + p1d0⟩) :
    num_pref.val * C4_D.eps + num_pref.eps * C4_D.val = den_pref.val * A44 + den_pref.eps * A43 := by
  subst hnum hden hC4 hP0 hd1 hres
  rcases WD with ⟨w0, w1⟩
  rcases cbD with ⟨cbv, cbe⟩
  rcases D22 with ⟨d22v, d22e⟩
  rcases D20 with ⟨d20v, d20e⟩
  rcases D33 with ⟨d33v, d33e⟩
  have h81 : (81 : R) ≠ 0 := by exact_mod_cast (by decide : (81 : ℕ) ≠ 0)
  have hw1_eq : w1 = -w0 * Bv1 / Bv2 := by rw [eq_div_iff hBv2]; exact hw_rel
  have hA43_eq : A43 = -(w0 * cbv ^ 4) / (81 * Bv2 * d22v * d33v) := by
    have hden_ne : (81 : R) * Bv2 * d22v * d33v ≠ 0 :=
      mul_ne_zero (mul_ne_zero (mul_ne_zero h81 hBv2) hd22) hd33
    rw [eq_div_iff hden_ne]
    apply mul_right_cancel₀ (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 hd22) (pow_ne_zero 3 hd20)) hd33)
    linear_combination hval.symm
  have hdiff :
      ((-(w0 * cbv ^ 4)) * (-(d22v * d20v ^ 2 * (-(d22v * d20v * d33e + (d22v * d20e + d22e * d20v) * d33v) + d1s) +
        (d22v * (2 * d20v * d20e) + d22e * d20v ^ 2 - d21v ^ 2 * d20v) * (-(d22v * d20v * d33v))) + p1d0) +
       (-(w0 * (4 * cbv ^ 3 * cbe) + w1 * cbv ^ 4)) * (-(d22v * d20v ^ 2 * (-(d22v * d20v * d33v))))) -
      ((81 * Bv2 * d22v ^ 3 * (d20v ^ 3 * d33v ^ 2)) * A44 +
       ((81 * Bv2 * d22v ^ 3) * (d20v ^ 3 * (2 * d33v * d33e) + 3 * d20v ^ 2 * d20e * d33v ^ 2 + ress) +
        ((81 * Bv2) * (3 * d22v ^ 2 * d22e) + 81 * Bv1 * d22v ^ 3) * (d20v ^ 3 * d33v ^ 2)) * A43) =
      (81 * Bv2 * d22v ^ 3 * (d20v ^ 3 * d33v ^ 2)) * A43 *
        ((-2 * Bv1 / Bv2 + 4 * cbe / cbv - d22e / d22v - d33e / d33v -
          d21v ^ 2 / (d22v * d20v) - d1s / (d22v * d20v * d33v) -
          ress / (d20v ^ 3 * d33v ^ 2) + p1d0 / (d22v ^ 2 * d20v ^ 3 * d33v)) - ratio) := by
    rw [hA4_ratio, hw1_eq, hA43_eq]
    field_simp [hBv2, hcb, hd22, hd20, hd33, h81]
    ring
  rw [hsum, mul_zero] at hdiff
  simp only [Dual.neg_val, Dual.neg_eps, Dual.mul_val, Dual.mul_eps, Dual.C_val, Dual.C_eps,
    Dual.pow_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one]
  linear_combination hdiff

lemma W1_inf_r5678_alg {R : Type*} [Field R] [CharZero R]
    (d22 d20 d33 d21 d32 d31 d30 : R) (hd22 : d22 ≠ 0) (hd20 : d20 ≠ 0) (hd33 : d33 ≠ 0) :
    -d21 ^ 2 / (d22 * d20) - (d22 ^ 2 * d31 - d21 * (d22 * d32 - d21 * d33)) / (d22 * d20 * d33) -
      (-d21 * d20 ^ 2 * d33 * d32 + d22 * d20 ^ 2 * d32 ^ 2 - 2 * d22 * d20 ^ 2 * d33 * d31 +
       3 * d22 * d21 * d20 * d33 * d30 - 2 * d22 ^ 2 * d20 * d32 * d30 + d22 ^ 3 * d30 ^ 2) / (d20 ^ 3 * d33 ^ 2) +
      (2 * d22 * d21 * d20 * (d22 ^ 2 * d30 - d20 * (d22 * d32 - d21 * d33))) / (d22 ^ 2 * d20 ^ 3 * d33) =
    (d22 / d20) * (d31 / d33) - (d22 / d20) * (d32 / d33) ^ 2 - (d22 / d33) * (d21 / d20) * (d30 / d20) +
      2 * (d22 / d33) * (d22 / d20) * (d32 / d33) * (d30 / d20) - (d22 / d33) ^ 2 * (d22 / d20) * (d30 / d20) ^ 2 := by
  field_simp [hd22, hd20, hd33]; ring

lemma ofNat_ne_zero {R : Type*} [Field R] [CharZero R] (n : ℕ) [n.AtLeastTwo] :
    (no_index (OfNat.ofNat n) : R) ≠ 0 := by
  rw [← Nat.cast_ofNat (R := R) (n := n)]
  exact Nat.cast_ne_zero.mpr (NeZero.ne n)

lemma W1_inf_weights_consts {R : Type*} [Field R] [CharZero R] :
    ((-(2500 / 6561 : R)) ^ 3 * (64 / 4782969 : R) ^ 2 =
      -(64000000000000 / 6461081889226673298932241 : R)) ∧
    (-(-(25 / 4 : R) * (4 / 27 : R) ^ 4) =
      81 * (-(4 / 243 : R)) * (16 / 413343 : R) * (64 / 4782969 : R) * (-(279006525 / 64 : R))) ∧
    (-(-(25 / 4 : R) * (4 / 27 : R) ^ 4) /
        (81 * (-(4 / 243 : R)) * (-(2500 / 6561 : R)) * (64 / 4782969 : R)) =
      (177147 / 400 : R)) ∧
    (-(25 / 4 : R) * (4 / 27 : R) ^ 4 =
      81 * (-(4 / 243 : R)) * (-(2500 / 6561 : R)) * (64 / 4782969 : R) * (-(177147 / 400 : R))) := by
  have hd1_a : (4 : R) * 27 ^ 4 ≠ 0 := mul_ne_zero (ofNat_ne_zero 4) (pow_ne_zero 4 (ofNat_ne_zero 27))
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hZ : ((-2500 : ℤ) ^ 3 * 64 ^ 2) * 6461081889226673298932241 =
        (-64000000000000 : ℤ) * (6561 ^ 3 * 4782969 ^ 2) := by decide
    have hR := congrArg (Int.castRingHom R) hZ
    have hd1 : (6561 : R) ^ 3 * (4782969 : R) ^ 2 ≠ 0 :=
      mul_ne_zero (pow_ne_zero 3 (ofNat_ne_zero 6561)) (pow_ne_zero 2 (ofNat_ne_zero 4782969))
    have hd2 : (6461081889226673298932241 : R) ≠ 0 := ofNat_ne_zero 6461081889226673298932241
    rw [← neg_div, div_pow, div_pow, div_mul_div_comm, ← neg_div, div_eq_div_iff hd1 hd2]
    simpa only [map_mul, map_pow, map_neg, map_ofNat] using hR
  · have hZ : (25 * 4 ^ 4 : ℤ) * (243 * 413343 * 4782969 * 64) =
        (81 * 4 * 16 * 64 * 279006525 : ℤ) * (4 * 27 ^ 4) := by decide
    have hR := congrArg (Int.castRingHom R) hZ
    have hd2 : (243 : R) * 413343 * 4782969 * 64 ≠ 0 :=
      mul_ne_zero (mul_ne_zero (mul_ne_zero (ofNat_ne_zero 243) (ofNat_ne_zero 413343))
        (ofNat_ne_zero 4782969)) (ofNat_ne_zero 64)
    have h1 : -(-(25 / 4 : R) * (4 / 27 : R) ^ 4) = (25 * 4 ^ 4 : R) / (4 * 27 ^ 4) := by
      field_simp [hd1_a]
    have h2 : 81 * (-(4 / 243 : R)) * (16 / 413343 : R) * (64 / 4782969 : R) * (-(279006525 / 64 : R)) =
        (81 * 4 * 16 * 64 * 279006525 : R) / (243 * 413343 * 4782969 * 64) := by
      field_simp [hd2]
    rw [h1, h2, div_eq_div_iff hd1_a hd2]
    simpa only [map_mul, map_pow, map_ofNat] using hR
  · have hZ : (25 * 4 ^ 4 : ℤ) * (400 * (243 * 6561 * 4782969)) =
        (177147 * (81 * 4 * 2500 * 64) : ℤ) * (4 * 27 ^ 4) := by decide
    have hR := congrArg (Int.castRingHom R) hZ
    have hnz2 : (243 : R) * 6561 * 4782969 ≠ 0 :=
      mul_ne_zero (mul_ne_zero (ofNat_ne_zero 243) (ofNat_ne_zero 6561)) (ofNat_ne_zero 4782969)
    have hnz4 : (400 : R) ≠ 0 := ofNat_ne_zero 400
    have hden_ne : (81 : R) * -(4 / 243 : R) * -(2500 / 6561 : R) * (64 / 4782969 : R) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (mul_ne_zero (ofNat_ne_zero 81)
        (neg_ne_zero.mpr (div_ne_zero (ofNat_ne_zero 4) (ofNat_ne_zero 243))))
        (neg_ne_zero.mpr (div_ne_zero (ofNat_ne_zero 2500) (ofNat_ne_zero 6561))))
        (div_ne_zero (ofNat_ne_zero 64) (ofNat_ne_zero 4782969))
    rw [div_eq_iff hden_ne]
    have h1 : -(-(25 / 4 : R) * (4 / 27 : R) ^ 4) = (25 * 4 ^ 4 : R) / (4 * 27 ^ 4) := by
      field_simp [hd1_a]
    have h2 : (177147 / 400 : R) * (81 * -(4 / 243 : R) * -(2500 / 6561 : R) * (64 / 4782969 : R)) =
        (177147 * (81 * 4 * 2500 * 64) : R) / (400 * (243 * 6561 * 4782969)) := by
      field_simp [hnz2, hnz4]
    rw [h1, h2, div_eq_div_iff hd1_a (mul_ne_zero hnz4 hnz2)]
    simpa only [map_mul, map_pow, map_ofNat] using hR
  · have hZ : ((-25 : ℤ) * 4 ^ 4) * (243 * 6561 * 4782969 * 400) =
        (81 * (-4) * (-2500) * 64 * (-177147) : ℤ) * (4 * 27 ^ 4) := by decide
    have hR := congrArg (Int.castRingHom R) hZ
    have hd2 : (243 : R) * 6561 * 4782969 * 400 ≠ 0 :=
      mul_ne_zero (mul_ne_zero (mul_ne_zero (ofNat_ne_zero 243) (ofNat_ne_zero 6561))
        (ofNat_ne_zero 4782969)) (ofNat_ne_zero 400)
    have h1 : -(25 / 4 : R) * (4 / 27 : R) ^ 4 = ((-25 : R) * 4 ^ 4) / (4 * 27 ^ 4) := by
      field_simp [hd1_a]
    have h2 : 81 * (-(4 / 243 : R)) * (-(2500 / 6561 : R)) * (64 / 4782969 : R) * (-(177147 / 400 : R)) =
        (81 * (-4) * (-2500) * 64 * (-177147) : R) / (243 * 6561 * 4782969 * 400) := by
      field_simp [hd2]
    rw [h1, h2, div_eq_div_iff hd1_a hd2]
    simpa only [map_mul, map_pow, map_neg, map_ofNat] using hR

private lemma P44_fn_split {R : Type*} [Field R] (S Q T : R) :
    P44_fn S Q T =
      ((20510415 : R) + (-496300770) * Q + 1510998300 * Q ^ 2 + 4883417910 * Q ^ 3 +
        (-20513855880) * Q ^ 4 + 141076404 * S + (-1013761980) * S * Q + (-4586695470) * S * Q ^ 2 +
        28084223286 * S * Q ^ 3 + 161280315 * S ^ 2 + 1449439110 * S ^ 2 * Q +
        (-14449808646) * S ^ 2 * Q ^ 2 + (-155306970) * S ^ 3 + 3313480842 * S ^ 3 * Q + (-285894273) * S ^ 4) +
      ((-45278190 : R) + 1002263220 * Q + (-9227925000) * Q ^ 2 + 25838190000 * Q ^ 3 +
        (-302433264) * S + 6278958000 * S * Q + (-28116396000) * S * Q ^ 2 + 2593080000 * S * Q ^ 3 +
        (-1055687850) * S ^ 2 + 10141721100 * S ^ 2 * Q + (-2722734000) * S ^ 2 * Q ^ 2 +
        (-1212264900) * S ^ 3 + 950796000 * S ^ 3 * Q + (-110397980) * S ^ 4) * T +
      ((-135184545 : R) + 1619567460 * Q + (-4613962500) * Q ^ 2 + (-657628902) * S +
        3978922500 * S * Q + (-1389150000) * S * Q ^ 2 + (-843577875) * S ^ 2 +
        1065015000 * S ^ 2 * Q + (-108045000) * S ^ 2 * Q ^ 2 + (-203742000) * S ^ 3 +
        79233000 * S ^ 3 * Q + (-14526050) * S ^ 4) * T ^ 2 +
      ((-13243230 : R) + 61801740 * Q + (-22660638) * S) * T ^ 3 := by
  dsimp only [P44_fn]; ring

private lemma W1_inf_hsum8_poly {R : Type*} [CommRing R] (S Q T : R) :
    let S3Q : R := S - 3 * Q
    let L : R := 77 * S - 210 * Q + 45
    294 * L * (1001 * S ^ 3 - 5796 * S ^ 2 * Q + 9828 * S * Q ^ 2 - 4158 * Q ^ 3 +
        1001 * T ^ 3 - 5796 * T ^ 2 + 9828 * T - 4158 + 1215 * Q ^ 2 + 2430 * Q) +
      588 * S3Q * L * (-644 * S ^ 2 + 2184 * S * Q - 1386 * Q ^ 2 + 270 * Q + 270) +
      (-147) * (238140 * Q ^ 4 + 1063692 * Q ^ 3 * S + 1224720 * Q ^ 3 - 1363572 * Q ^ 2 * S ^ 2 -
        1462860 * Q ^ 2 * S + 267300 * Q ^ 2 + 525084 * Q * S ^ 3 + 618030 * Q * S ^ 2 -
        124740 * Q * S - 145800 * Q - 65905 * S ^ 4 - 90090 * S ^ 3 - 72900) +
      (-294) * S3Q * L * (13671 * Q ^ 2 - 13524 * Q * S + 4455 * Q + 2989 * S ^ 2 + 4455) +
      (-21) * L ^ 2 * (5 * T - 3) ^ 2 * (-49 * S ^ 2 + 140 * S * Q - 90 * Q - 90) +
      14700 * S3Q ^ 2 * L ^ 2 * (5 * T - 3) ^ 2 +
      14 * L ^ 2 * (5 * T - 3) * (5 * T - 1) * (-77 * S ^ 2 + 210 * S * Q - 45 * S - 135 * Q - 270) +
      (-420) * S3Q * L ^ 3 * (5 * T - 3) * (5 * T - 1) +
      3 * L ^ 4 * (5 * T - 1) ^ 2 +
      (((20510415 : R) + (-496300770) * Q + 1510998300 * Q ^ 2 + 4883417910 * Q ^ 3 +
        (-20513855880) * Q ^ 4 + 141076404 * S + (-1013761980) * S * Q + (-4586695470) * S * Q ^ 2 +
        28084223286 * S * Q ^ 3 + 161280315 * S ^ 2 + 1449439110 * S ^ 2 * Q +
        (-14449808646) * S ^ 2 * Q ^ 2 + (-155306970) * S ^ 3 + 3313480842 * S ^ 3 * Q + (-285894273) * S ^ 4) +
      ((-45278190 : R) + 1002263220 * Q + (-9227925000) * Q ^ 2 + 25838190000 * Q ^ 3 +
        (-302433264) * S + 6278958000 * S * Q + (-28116396000) * S * Q ^ 2 + 2593080000 * S * Q ^ 3 +
        (-1055687850) * S ^ 2 + 10141721100 * S ^ 2 * Q + (-2722734000) * S ^ 2 * Q ^ 2 +
        (-1212264900) * S ^ 3 + 950796000 * S ^ 3 * Q + (-110397980) * S ^ 4) * T +
      ((-135184545 : R) + 1619567460 * Q + (-4613962500) * Q ^ 2 + (-657628902) * S +
        3978922500 * S * Q + (-1389150000) * S * Q ^ 2 + (-843577875) * S ^ 2 +
        1065015000 * S ^ 2 * Q + (-108045000) * S ^ 2 * Q ^ 2 + (-203742000) * S ^ 3 +
        79233000 * S ^ 3 * Q + (-14526050) * S ^ 4) * T ^ 2 +
      ((-13243230 : R) + 61801740 * Q + (-22660638) * S) * T ^ 3) = 0 := by
  intro S3Q L
  set p5 : R := -49 * S ^ 2 + 140 * S * Q - 90 * Q - 90
  set p7 : R := -77 * S ^ 2 + 210 * S * Q - 45 * S - 135 * Q - 270
  set A : R := -21 * L ^ 2 * p5 + 14700 * S3Q ^ 2 * L ^ 2
  set B : R := 14 * L ^ 2 * p7 - 420 * S3Q * L ^ 3
  set C : R := 3 * L ^ 4
  have hc3 : 294 * L * 1001 + ((-13243230 : R) + 61801740 * Q + (-22660638) * S) = 0 := by
    dsimp only [L]; ring
  have hc2 : 294 * L * (-5796) + 25 * (A + B + C) +
      ((-135184545 : R) + 1619567460 * Q + (-4613962500) * Q ^ 2 + (-657628902) * S +
        3978922500 * S * Q + (-1389150000) * S * Q ^ 2 + (-843577875) * S ^ 2 +
        1065015000 * S ^ 2 * Q + (-108045000) * S ^ 2 * Q ^ 2 + (-203742000) * S ^ 3 +
        79233000 * S ^ 3 * Q + (-14526050) * S ^ 4) = 0 := by
    dsimp only [A, B, C, L, S3Q, p5, p7]; ring
  have hc1 : 294 * L * 9828 + (-30 * A - 20 * B - 10 * C) +
      ((-45278190 : R) + 1002263220 * Q + (-9227925000) * Q ^ 2 + 25838190000 * Q ^ 3 +
        (-302433264) * S + 6278958000 * S * Q + (-28116396000) * S * Q ^ 2 + 2593080000 * S * Q ^ 3 +
        (-1055687850) * S ^ 2 + 10141721100 * S ^ 2 * Q + (-2722734000) * S ^ 2 * Q ^ 2 +
        (-1212264900) * S ^ 3 + 950796000 * S ^ 3 * Q + (-110397980) * S ^ 4) = 0 := by
    dsimp only [A, B, C, L, S3Q, p5, p7]; ring
  have hc0 : 294 * L * (1001 * S ^ 3 - 5796 * S ^ 2 * Q + 9828 * S * Q ^ 2 - 4158 * Q ^ 3 -
        4158 + 1215 * Q ^ 2 + 2430 * Q) +
      588 * S3Q * L * (-644 * S ^ 2 + 2184 * S * Q - 1386 * Q ^ 2 + 270 * Q + 270) -
      147 * (238140 * Q ^ 4 + 1063692 * Q ^ 3 * S + 1224720 * Q ^ 3 - 1363572 * Q ^ 2 * S ^ 2 -
        1462860 * Q ^ 2 * S + 267300 * Q ^ 2 + 525084 * Q * S ^ 3 + 618030 * Q * S ^ 2 -
        124740 * Q * S - 145800 * Q - 65905 * S ^ 4 - 90090 * S ^ 3 - 72900) -
      294 * S3Q * L * (13671 * Q ^ 2 - 13524 * Q * S + 4455 * Q + 2989 * S ^ 2 + 4455) +
      (9 * A + 3 * B + C) +
      ((20510415 : R) + (-496300770) * Q + 1510998300 * Q ^ 2 + 4883417910 * Q ^ 3 +
        (-20513855880) * Q ^ 4 + 141076404 * S + (-1013761980) * S * Q + (-4586695470) * S * Q ^ 2 +
        28084223286 * S * Q ^ 3 + 161280315 * S ^ 2 + 1449439110 * S ^ 2 * Q +
        (-14449808646) * S ^ 2 * Q ^ 2 + (-155306970) * S ^ 3 + 3313480842 * S ^ 3 * Q + (-285894273) * S ^ 4) = 0 := by
    dsimp only [A, B, C, L, S3Q, p5, p7]; ring
  have hgrp :
      294 * L * (1001 * S ^ 3 - 5796 * S ^ 2 * Q + 9828 * S * Q ^ 2 - 4158 * Q ^ 3 +
          1001 * T ^ 3 - 5796 * T ^ 2 + 9828 * T - 4158 + 1215 * Q ^ 2 + 2430 * Q) +
        588 * S3Q * L * (-644 * S ^ 2 + 2184 * S * Q - 1386 * Q ^ 2 + 270 * Q + 270) +
        (-147) * (238140 * Q ^ 4 + 1063692 * Q ^ 3 * S + 1224720 * Q ^ 3 - 1363572 * Q ^ 2 * S ^ 2 -
          1462860 * Q ^ 2 * S + 267300 * Q ^ 2 + 525084 * Q * S ^ 3 + 618030 * Q * S ^ 2 -
          124740 * Q * S - 145800 * Q - 65905 * S ^ 4 - 90090 * S ^ 3 - 72900) +
        (-294) * S3Q * L * (13671 * Q ^ 2 - 13524 * Q * S + 4455 * Q + 2989 * S ^ 2 + 4455) +
        (-21) * L ^ 2 * (5 * T - 3) ^ 2 * p5 +
        14700 * S3Q ^ 2 * L ^ 2 * (5 * T - 3) ^ 2 +
        14 * L ^ 2 * (5 * T - 3) * (5 * T - 1) * p7 +
        (-420) * S3Q * L ^ 3 * (5 * T - 3) * (5 * T - 1) +
        3 * L ^ 4 * (5 * T - 1) ^ 2 =
      (294 * L * 1001) * T ^ 3 +
      (294 * L * (-5796) + 25 * (A + B + C)) * T ^ 2 +
      (294 * L * 9828 + (-30 * A - 20 * B - 10 * C)) * T +
      (294 * L * (1001 * S ^ 3 - 5796 * S ^ 2 * Q + 9828 * S * Q ^ 2 - 4158 * Q ^ 3 -
          4158 + 1215 * Q ^ 2 + 2430 * Q) +
        588 * S3Q * L * (-644 * S ^ 2 + 2184 * S * Q - 1386 * Q ^ 2 + 270 * Q + 270) -
        147 * (238140 * Q ^ 4 + 1063692 * Q ^ 3 * S + 1224720 * Q ^ 3 - 1363572 * Q ^ 2 * S ^ 2 -
          1462860 * Q ^ 2 * S + 267300 * Q ^ 2 + 525084 * Q * S ^ 3 + 618030 * Q * S ^ 2 -
          124740 * Q * S - 145800 * Q - 65905 * S ^ 4 - 90090 * S ^ 3 - 72900) -
        294 * S3Q * L * (13671 * Q ^ 2 - 13524 * Q * S + 4455 * Q + 2989 * S ^ 2 + 4455) +
        (9 * A + 3 * B + C)) := by
    dsimp only [A, B, C]
    generalize (-644 * S ^ 2 + 2184 * S * Q - 1386 * Q ^ 2 + 270 * Q + 270 : R) = gcb
    generalize (238140 * Q ^ 4 + 1063692 * Q ^ 3 * S + 1224720 * Q ^ 3 - 1363572 * Q ^ 2 * S ^ 2 -
          1462860 * Q ^ 2 * S + 267300 * Q ^ 2 + 525084 * Q * S ^ 3 + 618030 * Q * S ^ 2 -
          124740 * Q * S - 145800 * Q - 65905 * S ^ 4 - 90090 * S ^ 3 - 72900 : R) = gp3
    generalize (13671 * Q ^ 2 - 13524 * Q * S + 4455 * Q + 2989 * S ^ 2 + 4455 : R) = gp4
    ring
  change (294 * L * _ + _ + _ + _ + (-21) * L ^ 2 * (5 * T - 3) ^ 2 * p5 + _ + 14 * L ^ 2 * (5 * T - 3) * (5 * T - 1) * p7 + _ + _) + _ = 0
  rw [hgrp]
  linear_combination hc3 * T ^ 3 + hc2 * T ^ 2 + hc1 * T + hc0

private lemma mul_dist10 {R : Type*} [CommRing R] (M a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 : R) :
    M * ((a1 + a2 + a3 + a4) + (a5 - a6 - a7 + a8 - a9) - a10) =
      (M * a1) + (M * a2) + (M * a3) + (M * a4) + (M * a5) +
      (M * (-a6)) + (M * (-a7)) + (M * a8) + (M * (-a9)) + (M * (-a10)) := by ring

lemma W1_inf_weights_hsum8 {R : Type*} [Field R] [CharZero R] (S Q T : R)
    (hS3Q : S - 3 * Q ≠ 0) (hL : 77 * S - 210 * Q + 45 ≠ 0) (hT59 : 5 * T - 9 ≠ 0) :
    let S3Q := S - 3 * Q; let T59 := 5 * T - 9; let L := 77 * S - 210 * Q + 45
    let Bv2 : R := -(4 / 243 : R) * S3Q ^ 3
    let Bv1 : R := (143 / 243 : R) * S ^ 3 - (92 / 27) * S ^ 2 * Q + (52 / 9) * S * Q ^ 2 - (22 / 9) * Q ^ 3 +
      (143 / 243) * T ^ 3 - (92 / 27) * T ^ 2 + (52 / 9) * T - (22 / 9) + (5 / 7) * Q ^ 2 + (10 / 7) * Q
    let cbD_val : R := (4 / 27 : R) * S3Q ^ 2
    let cbD_eps : R := -(92 / 27 : R) * S ^ 2 + (104 / 9) * S * Q - (22 / 3) * Q ^ 2 + (10 / 7) * Q + (10 / 7)
    let r3 : R := -(238140 * Q ^ 4 + 1063692 * Q ^ 3 * S + 1224720 * Q ^ 3 - 1363572 * Q ^ 2 * S ^ 2 -
      1462860 * Q ^ 2 * S + 267300 * Q ^ 2 + 525084 * Q * S ^ 3 + 618030 * Q * S ^ 2 -
      124740 * Q * S - 145800 * Q - 65905 * S ^ 4 - 90090 * S ^ 3 - 72900) / (28 * S3Q ^ 3 * L)
    let r4 : R := -(13671 * Q ^ 2 - 13524 * Q * S + 4455 * Q + 2989 * S ^ 2 + 4455) / (14 * S3Q ^ 2)
    let q22_33 : R := (81 / 28 : R) * L / S3Q ^ 2
    let q32_33 : R := -(375 / 2 : R) * T59 * (5 * T - 3) / S3Q ^ 2
    let q31_33 : R := (5625 / 112 : R) * T59 ^ 2 * (5 * T - 3) ^ 2 *
      (-49 * S ^ 2 + 140 * S * Q - 90 * Q - 90) / S3Q ^ 6
    let q21_20 : R := (2 / 1575 : R) * (5 * T - 3) / T59 *
      (-77 * S ^ 2 + 210 * S * Q - 45 * S - 135 * Q - 270)
    let q30_20 : R := -(25 / 27 : R) * (5 * T - 1) * T59 / S3Q
    let q22_20 : R := -(4 / 39375 : R) * L * S3Q ^ 3 / T59 ^ 2
    (-2 * Bv1 / Bv2 + 4 * cbD_eps / cbD_val + r3 + r4) +
      (q22_20 * q31_33 - q22_20 * q32_33 ^ 2 - q22_33 * q21_20 * q30_20 +
       2 * q22_33 * q22_20 * q32_33 * q30_20 - q22_33 ^ 2 * q22_20 * q30_20 ^ 2) -
      (-(1 / 4116 : R) * P44_fn S Q T / (S3Q ^ 3 * L)) = 0 := by
  intro S3Q T59 L Bv2 Bv1 cbD_val cbD_eps r3 r4 q22_33 q32_33 q31_33 q21_20 q30_20 q22_20
  have hS3Q' : S3Q ≠ 0 := hS3Q; have hL' : L ≠ 0 := hL; have hT59' : T59 ≠ 0 := hT59
  have hM : (4116 : R) * S3Q ^ 3 * L ≠ 0 :=
    mul_ne_zero (mul_ne_zero (ofNat_ne_zero 4116) (pow_ne_zero 3 hS3Q')) hL'
  apply mul_left_cancel₀ hM
  rw [mul_zero, mul_dist10]
  have ht1 : (4116 : R) * S3Q ^ 3 * L * (-2 * Bv1 / Bv2) =
      294 * L * (1001 * S ^ 3 - 5796 * S ^ 2 * Q + 9828 * S * Q ^ 2 - 4158 * Q ^ 3 +
        1001 * T ^ 3 - 5796 * T ^ 2 + 9828 * T - 4158 + 1215 * Q ^ 2 + 2430 * Q) := by
    have h1 : (4116 : R) * S3Q ^ 3 * L * (-2 * Bv1 / Bv2) = 294 * L * (1701 * Bv1) := by
      dsimp only [Bv2]; field_simp [hS3Q']; ring
    rw [h1]; congr 1; dsimp only [Bv1]; ring
  have ht2 : (4116 : R) * S3Q ^ 3 * L * (4 * cbD_eps / cbD_val) =
      588 * S3Q * L * (-644 * S ^ 2 + 2184 * S * Q - 1386 * Q ^ 2 + 270 * Q + 270) := by
    have h1 : (4116 : R) * S3Q ^ 3 * L * (4 * cbD_eps / cbD_val) = 588 * S3Q * L * (189 * cbD_eps) := by
      dsimp only [cbD_val]; field_simp [hS3Q']; ring
    rw [h1]; congr 1; dsimp only [cbD_eps]; ring
  have ht3 : (4116 : R) * S3Q ^ 3 * L * r3 =
      (-147) * (238140 * Q ^ 4 + 1063692 * Q ^ 3 * S + 1224720 * Q ^ 3 - 1363572 * Q ^ 2 * S ^ 2 -
        1462860 * Q ^ 2 * S + 267300 * Q ^ 2 + 525084 * Q * S ^ 3 + 618030 * Q * S ^ 2 -
        124740 * Q * S - 145800 * Q - 65905 * S ^ 4 - 90090 * S ^ 3 - 72900) := by
    dsimp only [r3]; field_simp [hS3Q', hL']; ring
  have ht4 : (4116 : R) * S3Q ^ 3 * L * r4 =
      (-294) * S3Q * L * (13671 * Q ^ 2 - 13524 * Q * S + 4455 * Q + 2989 * S ^ 2 + 4455) := by
    dsimp only [r4]; field_simp [hS3Q']; ring
  have ht5 : (4116 : R) * S3Q ^ 3 * L * (q22_20 * q31_33) =
      (-21) * L ^ 2 * (5 * T - 3) ^ 2 * (-49 * S ^ 2 + 140 * S * Q - 90 * Q - 90) := by
    dsimp only [q22_20, q31_33]; field_simp [hS3Q', hT59']; ring
  have ht6 : (4116 : R) * S3Q ^ 3 * L * (-(q22_20 * q32_33 ^ 2)) =
      14700 * S3Q ^ 2 * L ^ 2 * (5 * T - 3) ^ 2 := by
    dsimp only [q22_20, q32_33]; field_simp [hS3Q', hT59']; ring
  have ht7 : (4116 : R) * S3Q ^ 3 * L * (-(q22_33 * q21_20 * q30_20)) =
      14 * L ^ 2 * (5 * T - 3) * (5 * T - 1) * (-77 * S ^ 2 + 210 * S * Q - 45 * S - 135 * Q - 270) := by
    dsimp only [q22_33, q21_20, q30_20]; field_simp [hS3Q', hT59']; ring
  have ht8 : (4116 : R) * S3Q ^ 3 * L * (2 * q22_33 * q22_20 * q32_33 * q30_20) =
      (-420) * S3Q * L ^ 3 * (5 * T - 3) * (5 * T - 1) := by
    dsimp only [q22_33, q22_20, q32_33, q30_20]; field_simp [hS3Q', hT59']; ring
  have ht9 : (4116 : R) * S3Q ^ 3 * L * (-(q22_33 ^ 2 * q22_20 * q30_20 ^ 2)) =
      3 * L ^ 4 * (5 * T - 1) ^ 2 := by
    dsimp only [q22_33, q22_20, q30_20]; field_simp [hS3Q', hT59']; ring
  have ht10 : (4116 : R) * S3Q ^ 3 * L * (-(-(1 / 4116 : R) * P44_fn S Q T / (S3Q ^ 3 * L))) =
      P44_fn S Q T := by
    field_simp [hS3Q', hL']
  rw [ht1, ht2, ht3, ht4, ht5, ht6, ht7, ht8, ht9, ht10, P44_fn_split]
  exact W1_inf_hsum8_poly S Q T

lemma ring_regroup8 {R : Type*} [Field R] (a b c1 c2 d1 d2 e f g h : R) :
    a + b - c1 / c2 - d1 / d2 - e - f - g + h =
      (a + b + (-c1 / c2) + (-d1 / d2)) + (-e - f - g + h) := by ring

def w1_Bv2 {R : Type*} [Field R] (S Q : R) : R := -(4 / 243 : R) * (S - 3 * Q) ^ 3
def w1_Bv1 {R : Type*} [Field R] (S Q T : R) : R :=
  (143 / 243 : R) * S ^ 3 - (92 / 27) * S ^ 2 * Q + (52 / 9) * S * Q ^ 2 - (22 / 9) * Q ^ 3 +
  (143 / 243) * T ^ 3 - (92 / 27) * T ^ 2 + (52 / 9) * T - (22 / 9) + (5 / 7) * Q ^ 2 + (10 / 7) * Q
def w1_Cv0 {R : Type*} [Field R] (T : R) : R := -(25 / 243 : R) * T * (5 * T - 9) ^ 2
def w1_w0 {R : Type*} [Field R] (S Q T : R) : R := -w1_Cv0 T / w1_Bv2 S Q
def w1_w1 {R : Type*} [Field R] (S Q T : R) : R := w1_Cv0 T * w1_Bv1 S Q T / w1_Bv2 S Q ^ 2
def w1_WD {R : Type*} [Field R] (S Q T : R) : Dual R := ⟨w1_w0 S Q T, w1_w1 S Q T⟩
def w1_cbD {R : Type*} [Field R] (S Q : R) : Dual R :=
  ⟨(4 / 27 : R) * (S - 3 * Q) ^ 2, -(92 / 27 : R) * S ^ 2 + (104 / 9) * S * Q - (22 / 3) * Q ^ 2 + (10 / 7) * Q + (10 / 7)⟩
def w1_c0_0 {R : Type*} [Field R] (T : R) : R := -(25 / 81 : R) * (5 * T - 9) * (5 * T - 3)
def w1_k2_0 {R : Type*} [Field R] (T : R) : R := -(125 / 81 : R) * (5 * T - 6)
def w1_k3_0 (R : Type*) [Field R] : R := -(625 / 243 : R)
def w1_D22 {R : Type*} [Field R] (S Q : R) : Dual R := ⟨Q5_c5 S Q, Q5_c4 S Q⟩
def w1_D21_v {R : Type*} [Field R] (S Q T : R) : R := p21_c3 S Q * w1_c0_0 T
def w1_D20_v {R : Type*} [Field R] (S Q T : R) : R :=
  (-(4 / 9 : R) * S + (4 / 3) * Q) * w1_c0_0 T ^ 2 + (w1_cbD S Q).val ^ 2 * (w1_w0 S Q T * w1_k2_0 T)
def w1_D20 {R : Type*} [Field R] (S Q T d20e : R) : Dual R := ⟨w1_D20_v S Q T, d20e⟩
def w1_D33 {R : Type*} [Field R] (S Q : R) : Dual R := ⟨Q7_c7 S Q, Q7_c6 S Q⟩
def w1_D32_v {R : Type*} [Field R] (S Q T : R) : R := p32_c5 S Q * w1_c0_0 T
def w1_D31_v {R : Type*} [Field R] (S Q T : R) : R := p31_c3 S Q * w1_c0_0 T ^ 2
def w1_D30_v {R : Type*} [Field R] (S Q T : R) : R :=
  -(4 / 9 : R) * w1_c0_0 T ^ 3 + (w1_cbD S Q).val ^ 3 * (w1_w0 S Q T ^ 2 * w1_k3_0 R)
def w1_diff12_v {R : Type*} [Field R] (S Q T : R) : R :=
  (w1_D22 S Q).val * w1_D32_v S Q T - w1_D21_v S Q T * (w1_D33 S Q).val
def w1_d1_main {R : Type*} [Field R] (S Q T d20e : R) : Dual R := -(w1_D22 S Q * w1_D20 S Q T d20e * w1_D33 S Q)
def w1_d1_sub_v {R : Type*} [Field R] (S Q T : R) : R :=
  (w1_D22 S Q).val ^ 2 * w1_D31_v S Q T - w1_D21_v S Q T * w1_diff12_v S Q T
def w1_d1_D {R : Type*} [Field R] (S Q T d20e : R) : Dual R :=
  ⟨(w1_d1_main S Q T d20e).val, (w1_d1_main S Q T d20e).eps + w1_d1_sub_v S Q T⟩
def w1_d0_v {R : Type*} [Field R] (S Q T : R) : R :=
  (w1_D22 S Q).val ^ 2 * w1_D30_v S Q T - w1_D20_v S Q T * w1_diff12_v S Q T
def w1_res_main {R : Type*} [Field R] (S Q T d20e : R) : Dual R := w1_D20 S Q T d20e ^ 3 * w1_D33 S Q ^ 2
def w1_res_sub_v {R : Type*} [Field R] (S Q T : R) : R :=
  -w1_D21_v S Q T * w1_D20_v S Q T ^ 2 * (w1_D33 S Q).val * w1_D32_v S Q T +
  (w1_D22 S Q).val * w1_D20_v S Q T ^ 2 * w1_D32_v S Q T ^ 2 -
  2 * (w1_D22 S Q).val * w1_D20_v S Q T ^ 2 * (w1_D33 S Q).val * w1_D31_v S Q T +
  3 * (w1_D22 S Q).val * w1_D21_v S Q T * w1_D20_v S Q T * (w1_D33 S Q).val * w1_D30_v S Q T -
  2 * (w1_D22 S Q).val ^ 2 * w1_D20_v S Q T * w1_D32_v S Q T * w1_D30_v S Q T +
  (w1_D22 S Q).val ^ 3 * w1_D30_v S Q T ^ 2
def w1_res_D {R : Type*} [Field R] (S Q T d20e : R) : Dual R :=
  ⟨(w1_res_main S Q T d20e).val, (w1_res_main S Q T d20e).eps + w1_res_sub_v S Q T⟩
def w1_num_pref {R : Type*} [Field R] (S Q T : R) : Dual R := -(w1_WD S Q T * w1_cbD S Q ^ 4)
def w1_den_pref {R : Type*} [Field R] (S Q T d20e : R) : Dual R :=
  Dual.C (81 : R) * ⟨w1_Bv2 S Q, w1_Bv1 S Q T⟩ * w1_D22 S Q ^ 3 * w1_res_D S Q T d20e
def w1_P0_4_D {R : Type*} [Field R] (S Q T d20e : R) : Dual R :=
  ⟨(w1_D22 S Q * w1_D20 S Q T d20e ^ 2).val,
   (w1_D22 S Q * w1_D20 S Q T d20e ^ 2).eps - w1_D21_v S Q T ^ 2 * w1_D20_v S Q T⟩
def w1_P1_4_v {R : Type*} [Field R] (S Q T : R) : R :=
  2 * (w1_D22 S Q).val * w1_D21_v S Q T * w1_D20_v S Q T
def w1_C4_D {R : Type*} [Field R] (S Q T d20e : R) : Dual R :=
  ⟨(-(w1_P0_4_D S Q T d20e * w1_d1_D S Q T d20e)).val,
   (-(w1_P0_4_D S Q T d20e * w1_d1_D S Q T d20e)).eps + w1_P1_4_v S Q T * w1_d0_v S Q T⟩
def w1_C3_v {R : Type*} [Field R] (S Q T d20e : R) : R :=
  (-(w1_D22 S Q).val ^ 2 * w1_D20_v S Q T) * w1_d0_v S Q T -
  ((w1_D22 S Q).val * w1_D21_v S Q T * w1_D20_v S Q T) * (w1_d1_main S Q T d20e).val
def w1_C2_v {R : Type*} [Field R] (S Q T d20e : R) : R :=
  ((w1_D22 S Q).val ^ 2 * w1_D20_v S Q T) * (w1_d1_main S Q T d20e).val
def w1_A4_3 {R : Type*} [Field R] (S Q T : R) : R :=
  -(279006525 / 64 : R) * T * (5 * T - 9) ^ 2 / ((S - 3 * Q) ^ 8 * (77 * S - 210 * Q + 45))
def w1_A4_4 {R : Type*} [Field R] (S Q T : R) : R :=
  (13286025 / 12544 : R) * T * (5 * T - 9) ^ 2 * P44_fn S Q T / ((S - 3 * Q) ^ 11 * (77 * S - 210 * Q + 45) ^ 2)
def w1_A3_4 {R : Type*} [Field R] (S Q T : R) : R :=
  (531441 / 448 : R) * T * (5 * T - 9) * (35 * S * T + 133 * S - 420 * Q + 225 * T - 45) / (S - 3 * Q) ^ 8
def w1_A2_4 {R : Type*} [Field R] (S Q T : R) : R :=
  -(177147 / 400 : R) * T / (S - 3 * Q) ^ 5

lemma W1_inf_weights_alg {R : Type*} [Field R] [CharZero R] (S Q T d20e : R)
    (hS3Q : S - 3 * Q ≠ 0) (hL : 77 * S - 210 * Q + 45 ≠ 0) (hT59 : 5 * T - 9 ≠ 0) :
    (w1_res_D S Q T d20e).val =
      -(64000000000000 / 6461081889226673298932241 : R) * (5 * T - 9) ^ 6 * (S - 3 * Q) ^ 15 ∧
    (w1_den_pref S Q T d20e).val ≠ 0 ∧
    w1_num_pref S Q T * w1_C4_D S Q T d20e =
      w1_den_pref S Q T d20e * ⟨w1_A4_3 S Q T, w1_A4_4 S Q T⟩ ∧
    (w1_num_pref S Q T).val * w1_C3_v S Q T d20e =
      (w1_den_pref S Q T d20e).val * w1_A3_4 S Q T ∧
    (w1_num_pref S Q T).val * w1_C2_v S Q T d20e =
      (w1_den_pref S Q T d20e).val * w1_A2_4 S Q T := by
  obtain ⟨hres_c, hsc_A4, hsc_A3, hsc_A2⟩ := W1_inf_weights_consts (R := R)
  have hBv2_ne : w1_Bv2 S Q ≠ 0 :=
    mul_ne_zero (neg_ne_zero.mpr (div_ne_zero (ofNat_ne_zero 4) (ofNat_ne_zero 243))) (pow_ne_zero 3 hS3Q)
  have hw0_s : w1_w0 S Q T = -(25 / 4 : R) * T * (5 * T - 9) ^ 2 / (S - 3 * Q) ^ 3 := by
    simp only [w1_w0, w1_Cv0, w1_Bv2]; field_simp [hS3Q]
  have hQ5_5 : (w1_D22 S Q).val = (16 / 413343 : R) * (77 * S - 210 * Q + 45) * (S - 3 * Q) ^ 4 := by
    simp only [w1_D22, Q5_c5]; ring
  have hQ7_7 : (w1_D33 S Q).val = (64 / 4782969 : R) * (S - 3 * Q) ^ 6 := by
    simp only [w1_D33, Q7_c7]; ring
  have hD20_v : w1_D20_v S Q T = -(2500 / 6561 : R) * (S - 3 * Q) * (5 * T - 9) ^ 2 := by
    simp only [w1_D20_v, w1_c0_0, w1_k2_0, w1_cbD]; rw [hw0_s]; field_simp [hS3Q]; ring
  have hD30_v : w1_D30_v S Q T = (62500 / 177147 : R) * (5 * T - 1) * (5 * T - 9) ^ 3 := by
    simp only [w1_D30_v, w1_c0_0, w1_k3_0, w1_cbD]; rw [hw0_s]
    have hcancel : ((4 / 27 : R) * (S - 3 * Q) ^ 2) ^ 3 *
        ((-(25 / 4 : R) * T * (5 * T - 9) ^ 2 / (S - 3 * Q) ^ 3) ^ 2 * -(625 / 243 : R)) =
        -(1562500 / 4782969 : R) * T ^ 2 * (5 * T - 9) ^ 4 := by
      field_simp [hS3Q]; ring
    rw [hcancel]; ring
  have hD21_v : w1_D21_v S Q T = -(200 / 413343 : R) * (5 * T - 9) * (5 * T - 3) * (S - 3 * Q) *
      (-77 * S ^ 2 + 210 * S * Q - 45 * S - 135 * Q - 270) := by
    simp only [w1_D21_v, p21_c3, w1_c0_0]; ring
  have hD32_v : w1_D32_v S Q T = -(4000 / 1594323 : R) * (5 * T - 9) * (5 * T - 3) * (S - 3 * Q) ^ 4 := by
    simp only [w1_D32_v, p32_c5, w1_c0_0]; ring
  have hD31_v : w1_D31_v S Q T = (2500 / 3720087 : R) * (5 * T - 9) ^ 2 * (5 * T - 3) ^ 2 *
      (-49 * S ^ 2 + 140 * S * Q - 90 * Q - 90) := by
    simp only [w1_D31_v, p31_c3, w1_c0_0]; ring
  have hres_fac : (w1_res_D S Q T d20e).val = w1_D20_v S Q T ^ 3 * (w1_D33 S Q).val ^ 2 := by
    simp only [w1_res_D, w1_res_main, Dual.mul_val, Dual.pow_eq, w1_D20]
  have hd1_fac : (w1_d1_main S Q T d20e).val = -((w1_D22 S Q).val * w1_D20_v S Q T * (w1_D33 S Q).val) := by
    simp only [w1_d1_main, Dual.neg_val, Dual.mul_val, w1_D20]
  have hres_v : (w1_res_D S Q T d20e).val =
      -(64000000000000 / 6461081889226673298932241 : R) * (5 * T - 9) ^ 6 * (S - 3 * Q) ^ 15 := by
    rw [hres_fac, hD20_v, hQ7_7, ← hres_c]
    generalize (-(2500 / 6561 : R)) = c1; generalize (64 / 4782969 : R) = c2; ring
  have hD22_ne : (w1_D22 S Q).val ≠ 0 := by
    rw [hQ5_5]; exact mul_ne_zero (mul_ne_zero (div_ne_zero (ofNat_ne_zero 16) (ofNat_ne_zero 413343)) hL) (pow_ne_zero 4 hS3Q)
  have hD20_ne : w1_D20_v S Q T ≠ 0 := by
    rw [hD20_v]; exact mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr (div_ne_zero (ofNat_ne_zero 2500) (ofNat_ne_zero 6561))) hS3Q) (pow_ne_zero 2 hT59)
  have hD33_ne : (w1_D33 S Q).val ≠ 0 := by
    rw [hQ7_7]; exact mul_ne_zero (div_ne_zero (ofNat_ne_zero 64) (ofNat_ne_zero 4782969)) (pow_ne_zero 6 hS3Q)
  have hden_v : (w1_den_pref S Q T d20e).val = 81 * w1_Bv2 S Q * (w1_D22 S Q).val ^ 3 * (w1_res_D S Q T d20e).val := by
    simp only [w1_den_pref, Dual.mul_val, Dual.C_val, Dual.pow_eq]
  have hden_ne : (w1_den_pref S Q T d20e).val ≠ 0 := by
    rw [hden_v, hres_fac]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (ofNat_ne_zero 81) hBv2_ne) (pow_ne_zero 3 hD22_ne))
      (mul_ne_zero (pow_ne_zero 3 hD20_ne) (pow_ne_zero 2 hD33_ne))
  have hnum_v : (w1_num_pref S Q T).val = -(w1_w0 S Q T * (w1_cbD S Q).val ^ 4) := by
    simp only [w1_num_pref, w1_WD, Dual.neg_val, Dual.mul_val, Dual.pow_eq]
  have hC4_v : (w1_C4_D S Q T d20e).val = -((w1_D22 S Q).val * w1_D20_v S Q T ^ 2 * (w1_d1_main S Q T d20e).val) := by
    simp only [w1_C4_D, w1_P0_4_D, w1_d1_D, Dual.neg_val, Dual.mul_val, Dual.pow_eq, w1_D20]
  have hq32_33 : w1_D32_v S Q T / (w1_D33 S Q).val = -(375 / 2 : R) * (5 * T - 9) * (5 * T - 3) / (S - 3 * Q) ^ 2 := by
    rw [hD32_v, hQ7_7]; field_simp [hS3Q]; ring
  have hq22_20 : (w1_D22 S Q).val / w1_D20_v S Q T = -(4 / 39375 : R) * (77 * S - 210 * Q + 45) * (S - 3 * Q) ^ 3 / (5 * T - 9) ^ 2 := by
    rw [hQ5_5, hD20_v]; field_simp [hS3Q, hT59]; ring
  have hq30_33 : w1_D30_v S Q T / (w1_D33 S Q).val = (1687500 / 64 : R) * (5 * T - 1) * (5 * T - 9) ^ 3 / (S - 3 * Q) ^ 6 := by
    rw [hD30_v, hQ7_7]; field_simp [hS3Q]; ring
  have hA4_3 : (w1_num_pref S Q T).val * (w1_C4_D S Q T d20e).val = (w1_den_pref S Q T d20e).val * w1_A4_3 S Q T := by
    have hcore : -(w1_w0 S Q T * (w1_cbD S Q).val ^ 4) =
        81 * w1_Bv2 S Q * (w1_D22 S Q).val * (w1_D33 S Q).val * w1_A4_3 S Q T := by
      rw [hw0_s, hQ5_5, hQ7_7]; simp only [w1_cbD, w1_Bv2, w1_A4_3]
      have hfac : -((-(25 / 4 : R) * T * (5 * T - 9) ^ 2 / (S - 3 * Q) ^ 3) * ((4 / 27 : R) * (S - 3 * Q) ^ 2) ^ 4) =
          (-(-(25 / 4 : R) * (4 / 27 : R) ^ 4)) * (T * (5 * T - 9) ^ 2 * (S - 3 * Q) ^ 5) := by
        field_simp [hS3Q]
      have hfac2 : 81 * (-(4 / 243 : R) * (S - 3 * Q) ^ 3) * ((16 / 413343 : R) * (77 * S - 210 * Q + 45) * (S - 3 * Q) ^ 4) *
          ((64 / 4782969 : R) * (S - 3 * Q) ^ 6) *
          (-(279006525 / 64 : R) * T * (5 * T - 9) ^ 2 / ((S - 3 * Q) ^ 8 * (77 * S - 210 * Q + 45))) =
          (81 * (-(4 / 243 : R)) * (16 / 413343 : R) * (64 / 4782969 : R) * (-(279006525 / 64 : R))) *
            (T * (5 * T - 9) ^ 2 * (S - 3 * Q) ^ 5) := by
        generalize (S - 3 * Q) = S3Q at hS3Q ⊢
        generalize (77 * S - 210 * Q + 45) = L at hL ⊢
        field_simp [hS3Q, hL]
      rw [hfac, hfac2, hsc_A4]
    rw [hnum_v, hC4_v, hden_v, hd1_fac, hres_fac]
    linear_combination ((w1_D22 S Q).val ^ 2 * w1_D20_v S Q T ^ 3 * (w1_D33 S Q).val) * hcore
  have hA3_4 : (w1_num_pref S Q T).val * w1_C3_v S Q T d20e = (w1_den_pref S Q T d20e).val * w1_A3_4 S Q T := by
    have hC3_simp : w1_C3_v S Q T d20e =
        (w1_D22 S Q).val ^ 3 * w1_D20_v S Q T * (w1_D20_v S Q T * w1_D32_v S Q T - (w1_D22 S Q).val * w1_D30_v S Q T) := by
      simp only [w1_C3_v, w1_d0_v, w1_diff12_v]; rw [hd1_fac]; ring
    have hcore : (-(w1_w0 S Q T * (w1_cbD S Q).val ^ 4)) *
        (w1_D20_v S Q T * w1_D32_v S Q T - (w1_D22 S Q).val * w1_D30_v S Q T) =
        81 * w1_Bv2 S Q * w1_D20_v S Q T ^ 2 * (w1_D33 S Q).val ^ 2 * w1_A3_4 S Q T := by
      have hbr : w1_D20_v S Q T * w1_D32_v S Q T - (w1_D22 S Q).val * w1_D30_v S Q T =
          w1_D20_v S Q T * (w1_D33 S Q).val *
            (w1_D32_v S Q T / (w1_D33 S Q).val - ((w1_D22 S Q).val / w1_D20_v S Q T) * (w1_D30_v S Q T / (w1_D33 S Q).val)) := by
        field_simp [hD20_ne, hD33_ne]
      have hsc_pref : -(w1_w0 S Q T * (w1_cbD S Q).val ^ 4) / (81 * w1_Bv2 S Q * w1_D20_v S Q T * (w1_D33 S Q).val) =
          (177147 / 400 : R) * T / (S - 3 * Q) ^ 5 := by
        rw [hw0_s, hD20_v, hQ7_7]; simp only [w1_cbD, w1_Bv2]
        have hfac : -((-(25 / 4 : R) * T * (5 * T - 9) ^ 2 / (S - 3 * Q) ^ 3) * ((4 / 27 : R) * (S - 3 * Q) ^ 2) ^ 4) /
            (81 * (-(4 / 243 : R) * (S - 3 * Q) ^ 3) * (-(2500 / 6561 : R) * (S - 3 * Q) * (5 * T - 9) ^ 2) *
              ((64 / 4782969 : R) * (S - 3 * Q) ^ 6)) =
            (-(-(25 / 4 : R) * (4 / 27 : R) ^ 4) / (81 * (-(4 / 243 : R)) * (-(2500 / 6561 : R)) * (64 / 4782969 : R))) *
              (T / (S - 3 * Q) ^ 5) := by
          generalize (S - 3 * Q) = S3Q at hS3Q ⊢
          generalize (5 * T - 9) = T59 at hT59 ⊢
          field_simp [hS3Q, hT59]
        rw [hfac, hsc_A3]; ring
      have hden0 : (81 : R) * w1_Bv2 S Q * w1_D20_v S Q T * (w1_D33 S Q).val ≠ 0 :=
        mul_ne_zero (mul_ne_zero (mul_ne_zero (ofNat_ne_zero 81) hBv2_ne) hD20_ne) hD33_ne
      rw [hbr]
      have hdiv_eq : (-(w1_w0 S Q T * (w1_cbD S Q).val ^ 4)) *
          (w1_D20_v S Q T * (w1_D33 S Q).val *
            (w1_D32_v S Q T / (w1_D33 S Q).val - (w1_D22 S Q).val / w1_D20_v S Q T * (w1_D30_v S Q T / (w1_D33 S Q).val))) =
          (81 * w1_Bv2 S Q * w1_D20_v S Q T * (w1_D33 S Q).val) * (w1_D20_v S Q T * (w1_D33 S Q).val) *
            ((-(w1_w0 S Q T * (w1_cbD S Q).val ^ 4) / (81 * w1_Bv2 S Q * w1_D20_v S Q T * (w1_D33 S Q).val)) *
              (w1_D32_v S Q T / (w1_D33 S Q).val - (w1_D22 S Q).val / w1_D20_v S Q T * (w1_D30_v S Q T / (w1_D33 S Q).val))) := by
        field_simp [hden0]
      rw [hdiv_eq, hsc_pref, hq32_33, hq22_20, hq30_33]
      have hfin : ((177147 / 400 : R) * T / (S - 3 * Q) ^ 5) *
          (-(375 / 2 : R) * (5 * T - 9) * (5 * T - 3) / (S - 3 * Q) ^ 2 -
            (-(4 / 39375 : R) * (77 * S - 210 * Q + 45) * (S - 3 * Q) ^ 3 / (5 * T - 9) ^ 2) *
              ((1687500 / 64 : R) * (5 * T - 1) * (5 * T - 9) ^ 3 / (S - 3 * Q) ^ 6)) = w1_A3_4 S Q T := by
        simp only [w1_A3_4]; field_simp [hS3Q, hT59]; ring
      rw [hfin]; ring
    rw [hnum_v, hC3_simp, hden_v, hres_fac]
    linear_combination ((w1_D22 S Q).val ^ 3 * w1_D20_v S Q T) * hcore
  have hA2_4 : (w1_num_pref S Q T).val * w1_C2_v S Q T d20e = (w1_den_pref S Q T d20e).val * w1_A2_4 S Q T := by
    have hC2_simp : w1_C2_v S Q T d20e = -((w1_D22 S Q).val ^ 3 * w1_D20_v S Q T ^ 2 * (w1_D33 S Q).val) := by
      simp only [w1_C2_v]; rw [hd1_fac]; ring
    have hcore : w1_w0 S Q T * (w1_cbD S Q).val ^ 4 =
        81 * w1_Bv2 S Q * w1_D20_v S Q T * (w1_D33 S Q).val * w1_A2_4 S Q T := by
      rw [hw0_s, hD20_v, hQ7_7]; simp only [w1_cbD, w1_Bv2, w1_A2_4]
      have hfac1 : (-(25 / 4 : R) * T * (5 * T - 9) ^ 2 / (S - 3 * Q) ^ 3) * ((4 / 27 : R) * (S - 3 * Q) ^ 2) ^ 4 =
          (-(25 / 4 : R) * (4 / 27 : R) ^ 4) * (T * (5 * T - 9) ^ 2 * (S - 3 * Q) ^ 5) := by field_simp [hS3Q]
      have hfac2 : 81 * (-(4 / 243 : R) * (S - 3 * Q) ^ 3) * (-(2500 / 6561 : R) * (S - 3 * Q) * (5 * T - 9) ^ 2) *
          ((64 / 4782969 : R) * (S - 3 * Q) ^ 6) * (-(177147 / 400 : R) * T / (S - 3 * Q) ^ 5) =
          (81 * (-(4 / 243 : R)) * (-(2500 / 6561 : R)) * (64 / 4782969 : R) * (-(177147 / 400 : R))) *
            (T * (5 * T - 9) ^ 2 * (S - 3 * Q) ^ 5) := by field_simp [hS3Q]
      rw [hfac1, hfac2, hsc_A2]
    rw [hnum_v, hC2_simp, hden_v, hres_fac]
    linear_combination ((w1_D22 S Q).val ^ 3 * w1_D20_v S Q T ^ 2 * (w1_D33 S Q).val) * hcore
  have hA4_dual : w1_num_pref S Q T * w1_C4_D S Q T d20e =
      w1_den_pref S Q T d20e * ⟨w1_A4_3 S Q T, w1_A4_4 S Q T⟩ := by
    ext
    · simp only [Dual.mul_val]; exact hA4_3
    · simp only [Dual.mul_eps]
      have hcb2_ne : (w1_cbD S Q).val ≠ 0 :=
        mul_ne_zero (div_ne_zero (ofNat_ne_zero 4) (ofNat_ne_zero 27)) (pow_ne_zero 2 hS3Q)
      have hw_rel : (w1_WD S Q T).eps * w1_Bv2 S Q = -(w1_WD S Q T).val * w1_Bv1 S Q T := by
        simp only [w1_WD, w1_w0, w1_w1]; field_simp [hBv2_ne]
      have hA4_ratio : w1_A4_4 S Q T =
          w1_A4_3 S Q T * (-(1 / 4116 : R) * P44_fn S Q T / ((S - 3 * Q) ^ 3 * (77 * S - 210 * Q + 45))) := by
        simp only [w1_A4_3, w1_A4_4]; field_simp [hS3Q, hL]; ring
      have hval_sym : (-((w1_WD S Q T).val * (w1_cbD S Q).val ^ 4)) *
            ((w1_D22 S Q).val ^ 2 * (w1_D20 S Q T d20e).val ^ 3 * (w1_D33 S Q).val) =
          (81 * w1_Bv2 S Q * (w1_D22 S Q).val ^ 3 * ((w1_D20 S Q T d20e).val ^ 3 * (w1_D33 S Q).val ^ 2)) * w1_A4_3 S Q T := by
        have h1 : (w1_C4_D S Q T d20e).val = (w1_D22 S Q).val ^ 2 * w1_D20_v S Q T ^ 3 * (w1_D33 S Q).val := by
          rw [hC4_v, hd1_fac]; ring
        have h2 : (w1_den_pref S Q T d20e).val =
            81 * w1_Bv2 S Q * (w1_D22 S Q).val ^ 3 * (w1_D20_v S Q T ^ 3 * (w1_D33 S Q).val ^ 2) := by
          rw [hden_v, hres_fac]
        change (-((w1_w0 S Q T) * (w1_cbD S Q).val ^ 4)) * ((w1_D22 S Q).val ^ 2 * w1_D20_v S Q T ^ 3 * (w1_D33 S Q).val) =
          (81 * w1_Bv2 S Q * (w1_D22 S Q).val ^ 3 * (w1_D20_v S Q T ^ 3 * (w1_D33 S Q).val ^ 2)) * w1_A4_3 S Q T
        rw [← hnum_v, ← h1, ← h2]; exact hA4_3
      have hr5678' := W1_inf_r5678_alg (w1_D22 S Q).val (w1_D20_v S Q T) (w1_D33 S Q).val
        (w1_D21_v S Q T) (w1_D32_v S Q T) (w1_D31_v S Q T) (w1_D30_v S Q T) hD22_ne hD20_ne hD33_ne
      have hq22_33 : (w1_D22 S Q).val / (w1_D33 S Q).val = (81 / 28 : R) * (77 * S - 210 * Q + 45) / (S - 3 * Q) ^ 2 := by
        rw [hQ5_5, hQ7_7]; field_simp [hS3Q]; ring
      have hq31_33 : w1_D31_v S Q T / (w1_D33 S Q).val = (5625 / 112 : R) * (5 * T - 9) ^ 2 * (5 * T - 3) ^ 2 *
          (-49 * S ^ 2 + 140 * S * Q - 90 * Q - 90) / (S - 3 * Q) ^ 6 := by
        rw [hD31_v, hQ7_7]; field_simp [hS3Q]; ring
      have hq21_20 : w1_D21_v S Q T / w1_D20_v S Q T = (2 / 1575 : R) * (5 * T - 3) / (5 * T - 9) *
          (-77 * S ^ 2 + 210 * S * Q - 45 * S - 135 * Q - 270) := by
        rw [hD21_v, hD20_v]; field_simp [hS3Q, hT59]; ring
      have hq30_20 : w1_D30_v S Q T / w1_D20_v S Q T = -(25 / 27 : R) * (5 * T - 1) * (5 * T - 9) / (S - 3 * Q) := by
        rw [hD30_v, hD20_v]; field_simp [hS3Q, hT59]; ring
      have hr3 : -(w1_D22 S Q).eps / (w1_D22 S Q).val =
          -(238140 * Q ^ 4 + 1063692 * Q ^ 3 * S + 1224720 * Q ^ 3 - 1363572 * Q ^ 2 * S ^ 2 -
            1462860 * Q ^ 2 * S + 267300 * Q ^ 2 + 525084 * Q * S ^ 3 + 618030 * Q * S ^ 2 -
            124740 * Q * S - 145800 * Q - 65905 * S ^ 4 - 90090 * S ^ 3 - 72900) /
            (28 * (S - 3 * Q) ^ 3 * (77 * S - 210 * Q + 45)) := by
        rw [div_eq_div_iff hD22_ne (mul_ne_zero (mul_ne_zero (ofNat_ne_zero 28) (pow_ne_zero 3 hS3Q)) hL)]
        rw [hQ5_5]; simp only [w1_D22, Q5_c4]; ring
      have hr4 : -(w1_D33 S Q).eps / (w1_D33 S Q).val =
          -(13671 * Q ^ 2 - 13524 * Q * S + 4455 * Q + 2989 * S ^ 2 + 4455) / (14 * (S - 3 * Q) ^ 2) := by
        rw [div_eq_div_iff hD33_ne (mul_ne_zero (ofNat_ne_zero 14) (pow_ne_zero 2 hS3Q))]
        rw [hQ7_7]; simp only [w1_D33, Q7_c6]; ring
      have hsum8 :
          (-2 * w1_Bv1 S Q T / w1_Bv2 S Q + 4 * (w1_cbD S Q).eps / (w1_cbD S Q).val -
           (w1_D22 S Q).eps / (w1_D22 S Q).val - (w1_D33 S Q).eps / (w1_D33 S Q).val -
           w1_D21_v S Q T ^ 2 / ((w1_D22 S Q).val * (w1_D20 S Q T d20e).val) -
           w1_d1_sub_v S Q T / ((w1_D22 S Q).val * (w1_D20 S Q T d20e).val * (w1_D33 S Q).val) -
           w1_res_sub_v S Q T / ((w1_D20 S Q T d20e).val ^ 3 * (w1_D33 S Q).val ^ 2) +
           (w1_P1_4_v S Q T * w1_d0_v S Q T) / ((w1_D22 S Q).val ^ 2 * (w1_D20 S Q T d20e).val ^ 3 * (w1_D33 S Q).val)) -
          (-(1 / 4116 : R) * P44_fn S Q T / ((S - 3 * Q) ^ 3 * (77 * S - 210 * Q + 45))) = 0 := by
        change (-2 * w1_Bv1 S Q T / w1_Bv2 S Q + 4 * (w1_cbD S Q).eps / (w1_cbD S Q).val -
           (w1_D22 S Q).eps / (w1_D22 S Q).val - (w1_D33 S Q).eps / (w1_D33 S Q).val -
           w1_D21_v S Q T ^ 2 / ((w1_D22 S Q).val * w1_D20_v S Q T) -
           w1_d1_sub_v S Q T / ((w1_D22 S Q).val * w1_D20_v S Q T * (w1_D33 S Q).val) -
           w1_res_sub_v S Q T / (w1_D20_v S Q T ^ 3 * (w1_D33 S Q).val ^ 2) +
           (w1_P1_4_v S Q T * w1_d0_v S Q T) / ((w1_D22 S Q).val ^ 2 * w1_D20_v S Q T ^ 3 * (w1_D33 S Q).val)) - _ = 0
        have hre := ring_regroup8 (-2 * w1_Bv1 S Q T / w1_Bv2 S Q) (4 * (w1_cbD S Q).eps / (w1_cbD S Q).val)
          (w1_D22 S Q).eps (w1_D22 S Q).val (w1_D33 S Q).eps (w1_D33 S Q).val
          (w1_D21_v S Q T ^ 2 / ((w1_D22 S Q).val * w1_D20_v S Q T))
          (w1_d1_sub_v S Q T / ((w1_D22 S Q).val * w1_D20_v S Q T * (w1_D33 S Q).val))
          (w1_res_sub_v S Q T / (w1_D20_v S Q T ^ 3 * (w1_D33 S Q).val ^ 2))
          ((w1_P1_4_v S Q T * w1_d0_v S Q T) / ((w1_D22 S Q).val ^ 2 * w1_D20_v S Q T ^ 3 * (w1_D33 S Q).val))
        rw [hre]
        simp only [w1_d1_sub_v, w1_res_sub_v, w1_P1_4_v, w1_d0_v, w1_diff12_v]
        rw [neg_div] at hr5678'
        rw [hr5678', hr3, hr4, hq22_33, hq32_33, hq31_33, hq21_20, hq30_20, hq22_20]
        simpa only [w1_Bv2, w1_Bv1, w1_cbD] using W1_inf_weights_hsum8 S Q T hS3Q hL hT59
      exact W1_inf_log_deriv (w1_Bv2 S Q) (w1_Bv1 S Q T) (w1_WD S Q T) (w1_cbD S Q)
        (w1_D22 S Q) (w1_D20 S Q T d20e) (w1_D33 S Q)
        (w1_D21_v S Q T) (w1_d1_sub_v S Q T) (w1_res_sub_v S Q T) (w1_P1_4_v S Q T * w1_d0_v S Q T)
        (w1_A4_3 S Q T) (w1_A4_4 S Q T)
        (-(1 / 4116 : R) * P44_fn S Q T / ((S - 3 * Q) ^ 3 * (77 * S - 210 * Q + 45)))
        hBv2_ne hcb2_ne hD22_ne hD20_ne hD33_ne hw_rel hA4_ratio hval_sym hsum8
        (w1_num_pref S Q T) (w1_d1_D S Q T d20e) (w1_res_D S Q T d20e)
        (w1_den_pref S Q T d20e) (w1_P0_4_D S Q T d20e) (w1_C4_D S Q T d20e)
        rfl rfl rfl rfl rfl rfl
  exact ⟨hres_v, hden_ne, hA4_dual, hA3_4, hA2_4⟩


end SymmetricSexticResidual.LocalResidueInfAlg
