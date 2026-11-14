import Proposal.SolutionSupport02Part03

/-!
# An explicit trace-one direction at the literal smooth incidence seed

This file supplies seven exact ideal-membership identities for the existing
`selectedTangent` cubic at r = 57 and theta = 1. They show that its products
with k and each of the seven character-one cubic tests vanish in the actual
five-relation Artinian quotient. No cube-root-of-two equation is assumed.

The source binds the same cubic to the already constructed all-poles Cech
functional. Three times this cubic has derivative trace one and paired
ambient normal trace -1/171. The identification of these quotient tests with
the geometric Noether-Lefschetz map and the Abel-Jacobi derivative is still
a separate theorem; this file does not assert existence of the certificate.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000

noncomputable section
namespace CycleQ2ExplicitSeedDirection

open MvPolynomial

section Arithmetic
variable {R : Type*} [CommRing R]

def sparseH (ι x0 x1 x2 x3 : R) : R :=
  x0 ^ 3 + x0 * x1 ^ 2 + x0 * x2 * x3 + x1 * x2 * x3 +
    x2 ^ 3 + x3 ^ 3 - ι * (x1 ^ 3 + x3 ^ 3)

def sparseK (ι x0 x1 x2 x3 : R) : R :=
  x0 ^ 3 + x0 * x1 ^ 2 + x0 * x2 * x3 + x1 * x2 * x3 +
    x2 ^ 3 + x3 ^ 3 + ι * (x1 ^ 3 + x3 ^ 3)

def chosenCubic (ι x0 x1 : R) : R := ι * x0 ^ 2 * x1 + (ι - 1) * x0 ^ 3

def reducedTest (x0 x1 x2 x3 : R) : Fin 7 → R :=
  ![-x2 ^ 3, x2 * x3 ^ 2, x1 * x2 ^ 2, x1 ^ 2 * x3,
    x0 * x2 ^ 2, x0 * x1 * x3, x0 ^ 2 * x3]

def reducedRelations (ι x0 x1 x2 x3 : R) : Fin 4 → R :=
  ![x1 ^ 2 * x3 ^ 2, x2 ^ 4, x0 ^ 2 - 57 * x1 * x3,
    sparseH ι x0 x1 x2 x3]

def bezout0 (ι x0 x1 x2 x3 : R) : Fin 4 → R :=
  ![-6498 * ι * x0 ^ 2 * x2 ^ 3 - 6498 * ι * x0 * x1 * x2 ^ 3 - 114 * ι * x0 * x2 ^ 4 - 6498 * ι * x1 ^
      2 * x2 ^ 3 - 57 * ι * x1 * x2 ^ 4 - 114 * ι * x2 ^ 3 * x3 ^ 2 - 57 * x0 * x2 ^ 4,
-ι * x0 ^ 4 * x3 - 2 * ι * x0 ^ 3 * x1 * x3 - ι * x0 ^ 3 * x2 ^ 2 - ι * x0 ^ 2 * x1 ^ 2 * x3 - ι *
      x0 ^ 2 * x1 * x2 ^ 2 - 57 * ι * x0 ^ 2 * x1 * x3 ^ 2 - 57 * ι * x0 * x1 * x2 ^ 2 * x3 - 57 * ι
      * x1 ^ 2 * x2 ^ 2 * x3 + x0 ^ 4 * x3 + x0 ^ 3 * x1 * x3 + x0 ^ 3 * x2 ^ 2 - 57 * x0 ^ 2 * x1 *
      x3 ^ 2 - 57 * x0 * x1 * x2 ^ 2 * x3,
-ι * x0 ^ 4 * x2 ^ 3 - ι * x0 ^ 3 * x1 * x2 ^ 3 - ι * x0 ^ 2 * x1 ^ 2 * x2 ^ 3 - 114 * ι * x0 ^ 2 *
      x1 * x2 ^ 3 * x3 - 114 * ι * x0 * x1 ^ 2 * x2 ^ 3 * x3 - 114 * ι * x1 ^ 3 * x2 ^ 3 * x3 - ι *
      x1 * x2 ^ 3 * x3 ^ 3 + x0 ^ 4 * x2 ^ 3 + x0 ^ 2 * x1 ^ 2 * x2 ^ 3 + x0 * x1 ^ 3 * x2 ^ 3 + 2 *
      x0 * x2 ^ 3 * x3 ^ 3 + x1 ^ 4 * x2 ^ 3 + x1 * x2 ^ 3 * x3 ^ 3,
57 * ι * x0 * x1 * x2 ^ 3 * x3 + 57 * ι * x1 ^ 2 * x2 ^ 3 * x3 + 57 * x0 * x1 * x2 ^ 3 * x3]

def bezout1 (ι x0 x1 x2 x3 : R) : Fin 4 → R :=
  ![ι * x0 ^ 4 * x2 + 57 * ι * x0 ^ 3 * x2 * x3 + 57 * ι * x0 ^ 2 * x1 * x2 * x3 + ι * x0 ^ 2 * x2 ^ 2 *
      x3 + 6498 * ι * x0 ^ 2 * x2 * x3 ^ 2 - 57 * ι * x0 * x1 ^ 2 * x2 * x3 + 171 * ι * x0 * x2 ^ 2
      * x3 ^ 2 + 6498 * ι * x2 ^ 2 * x3 ^ 3 + 57 * ι * x2 * x3 ^ 4 - x0 ^ 4 * x2 - x0 ^ 3 * x1 * x2
      - x0 ^ 2 * x1 ^ 2 * x2 + 57 * x0 ^ 2 * x1 * x2 * x3 + 57 * x0 * x1 ^ 2 * x2 * x3 - 57 * x2 *
      x3 ^ 4,
ι * x0 ^ 3 * x3 ^ 2 + ι * x0 ^ 2 * x1 * x3 ^ 2 + 57 * ι * x0 * x1 * x3 ^ 3 - x0 ^ 3 * x3 ^ 2 + 57 *
      x0 * x1 * x3 ^ 3,
ι * x0 ^ 4 * x2 * x3 ^ 2 + ι * x0 ^ 3 * x1 * x2 * x3 ^ 2 + 114 * ι * x0 ^ 2 * x1 * x2 * x3 ^ 3 + ι *
      x0 ^ 2 * x2 ^ 2 * x3 ^ 3 + 2 * ι * x0 * x1 * x2 ^ 2 * x3 ^ 3 + 114 * ι * x1 * x2 ^ 2 * x3 ^ 4
      + ι * x1 * x2 * x3 ^ 5 - x0 ^ 4 * x2 * x3 ^ 2 - x0 ^ 2 * x2 ^ 2 * x3 ^ 3 - x0 * x1 * x2 ^ 2 *
      x3 ^ 3 - 2 * x0 * x2 * x3 ^ 5 - x1 * x2 * x3 ^ 5,
-57 * ι * x0 * x1 * x2 * x3 ^ 3 - 57 * x0 * x1 * x2 * x3 ^ 3]

def bezout2 (ι x0 x1 x2 x3 : R) : Fin 4 → R :=
  ![6498 * ι * x0 ^ 2 * x1 * x2 ^ 2 + 114 * ι * x0 ^ 2 * x2 ^ 3 + ι * x0 ^ 2 * x2 ^ 2 * x3 + 6498 * ι *
      x0 * x1 ^ 2 * x2 ^ 2 + 228 * ι * x0 * x1 * x2 ^ 3 + 6498 * ι * x1 ^ 3 * x2 ^ 2 + 114 * ι * x1
      ^ 2 * x2 ^ 3 + 57 * ι * x1 * x2 ^ 2 * x3 ^ 2 - x0 ^ 2 * x2 ^ 2 * x3 + 57 * x1 * x2 ^ 2 * x3 ^
      2,
ι * x0 ^ 3 * x1 * x2 + ι * x0 ^ 2 * x1 ^ 2 * x2 + 57 * ι * x0 * x1 ^ 2 * x2 * x3 + 57 * ι * x1 ^ 3 *
      x2 * x3 - x0 ^ 3 * x1 * x2 + 57 * x0 * x1 ^ 2 * x2 * x3,
ι * x0 ^ 4 * x1 * x2 ^ 2 + ι * x0 ^ 3 * x1 ^ 2 * x2 ^ 2 + ι * x0 ^ 2 * x1 ^ 3 * x2 ^ 2 + 114 * ι *
      x0 ^ 2 * x1 ^ 2 * x2 ^ 2 * x3 + ι * x0 ^ 2 * x1 * x2 ^ 3 * x3 + 114 * ι * x0 * x1 ^ 3 * x2 ^ 2
      * x3 + 2 * ι * x0 * x1 ^ 2 * x2 ^ 3 * x3 + 114 * ι * x1 ^ 4 * x2 ^ 2 * x3 + ι * x1 ^ 3 * x2 ^
      3 * x3 - x0 ^ 4 * x1 * x2 ^ 2 - x0 ^ 2 * x1 ^ 3 * x2 ^ 2 - x0 ^ 2 * x1 * x2 ^ 3 * x3 - x0 * x1
      ^ 4 * x2 ^ 2 - x0 * x1 ^ 2 * x2 ^ 3 * x3 - 2 * x0 * x1 * x2 ^ 2 * x3 ^ 3 - x1 ^ 5 * x2 ^ 2,
-57 * ι * x0 * x1 ^ 2 * x2 ^ 2 * x3 - 57 * ι * x1 ^ 3 * x2 ^ 2 * x3 - 57 * x0 * x1 ^ 2 * x2 ^ 2 * x3]

def bezout3 (ι x0 x1 x2 x3 : R) : Fin 4 → R :=
  ![57 * ι * x0 ^ 4 * x1 + ι * x0 ^ 4 * x2 + 57 * ι * x0 ^ 3 * x1 ^ 2 + 2 * ι * x0 ^ 3 * x1 * x2 + 57 *
      ι * x0 ^ 2 * x1 ^ 3 + ι * x0 ^ 2 * x1 ^ 2 * x2 + ι * x0 ^ 2 * x1 * x3 ^ 2 + 57 * ι * x0 * x1 *
      x2 ^ 3 + 57 * ι * x1 ^ 2 * x2 ^ 3 - 57 * x0 ^ 4 * x1 - x0 ^ 4 * x2 - x0 ^ 3 * x1 * x2 - 2 * x0
      ^ 3 * x3 ^ 2 - 57 * x0 ^ 2 * x1 ^ 3 - x0 ^ 2 * x1 * x3 ^ 2 - 57 * x0 * x1 ^ 4 - 57 * x0 * x1 *
      x2 ^ 3 - 57 * x1 ^ 5,
0,
ι * x0 ^ 4 * x1 ^ 2 * x3 + ι * x0 ^ 3 * x1 ^ 3 * x3 + ι * x0 ^ 2 * x1 ^ 4 * x3 + ι * x0 * x1 ^ 2 *
      x2 ^ 3 * x3 + ι * x1 ^ 3 * x2 ^ 3 * x3 - x0 ^ 4 * x1 ^ 2 * x3 - x0 ^ 2 * x1 ^ 4 * x3 - x0 * x1
      ^ 5 * x3 - x0 * x1 ^ 2 * x2 ^ 3 * x3 - x1 ^ 6 * x3,
0]

def bezout4 (ι x0 x1 x2 x3 : R) : Fin 4 → R :=
  ![3249 * ι * x0 ^ 3 * x2 ^ 2 + 6498 * ι * x0 ^ 2 * x1 * x2 ^ 2 + 171 * ι * x0 ^ 2 * x2 ^ 3 + 3249 * ι
      * x0 * x1 ^ 2 * x2 ^ 2 + 114 * ι * x0 * x1 * x2 ^ 3 + 3249 * ι * x0 * x2 ^ 3 * x3 + 114 * ι *
      x0 * x2 ^ 2 * x3 ^ 2 + 3249 * ι * x1 ^ 3 * x2 ^ 2 - 3249 * x0 ^ 3 * x2 ^ 2 - 57 * x0 ^ 2 * x2
      ^ 3 - 3249 * x0 * x1 ^ 2 * x2 ^ 2 - 3249 * x0 * x2 ^ 3 * x3 - 3249 * x1 ^ 3 * x2 ^ 2 - 6498 *
      x2 ^ 2 * x3 ^ 3,
ι * x0 ^ 4 * x2 + ι * x0 ^ 3 * x1 * x2 + 57 * ι * x0 * x1 ^ 2 * x2 * x3 - x0 ^ 4 * x2,
ι * x0 ^ 5 * x2 ^ 2 + ι * x0 ^ 4 * x1 * x2 ^ 2 + ι * x0 ^ 3 * x1 ^ 2 * x2 ^ 2 + 57 * ι * x0 ^ 3 * x1
      * x2 ^ 2 * x3 + ι * x0 ^ 3 * x2 ^ 3 * x3 + 114 * ι * x0 ^ 2 * x1 ^ 2 * x2 ^ 2 * x3 + 2 * ι *
      x0 ^ 2 * x1 * x2 ^ 3 * x3 + 57 * ι * x0 * x1 ^ 3 * x2 ^ 2 * x3 + ι * x0 * x1 ^ 2 * x2 ^ 3 * x3
      + 57 * ι * x0 * x1 * x2 ^ 3 * x3 ^ 2 + ι * x0 * x1 * x2 ^ 2 * x3 ^ 3 + 57 * ι * x1 ^ 4 * x2 ^
      2 * x3 - x0 ^ 5 * x2 ^ 2 - x0 ^ 3 * x1 ^ 2 * x2 ^ 2 - 57 * x0 ^ 3 * x1 * x2 ^ 2 * x3 - x0 ^ 3
      * x2 ^ 3 * x3 - x0 ^ 2 * x1 ^ 3 * x2 ^ 2 - x0 ^ 2 * x1 * x2 ^ 3 * x3 - 2 * x0 ^ 2 * x2 ^ 2 *
      x3 ^ 3 - x0 * x1 ^ 4 * x2 ^ 2 - 57 * x0 * x1 ^ 3 * x2 ^ 2 * x3 - 57 * x0 * x1 * x2 ^ 3 * x3 ^
      2 - x0 * x1 * x2 ^ 2 * x3 ^ 3 - 57 * x1 ^ 4 * x2 ^ 2 * x3 - 114 * x1 * x2 ^ 2 * x3 ^ 4,
-57 * ι * x0 * x1 ^ 2 * x2 ^ 2 * x3]

def bezout5 (ι x0 x1 x2 x3 : R) : Fin 4 → R :=
  ![57 * ι * x0 ^ 5 + 57 * ι * x0 ^ 4 * x1 + 2 * ι * x0 ^ 4 * x2 + 57 * ι * x0 ^ 3 * x1 ^ 2 + ι * x0 ^ 3
      * x1 * x2 + 57 * ι * x0 ^ 3 * x2 * x3 + ι * x0 ^ 3 * x3 ^ 2 + 57 * ι * x0 ^ 2 * x2 ^ 3 + 57 *
      ι * x0 * x1 * x2 ^ 3 - 57 * x0 ^ 5 - x0 ^ 4 * x2 - 57 * x0 ^ 3 * x1 ^ 2 - 57 * x0 ^ 3 * x2 *
      x3 - x0 ^ 3 * x3 ^ 2 - 57 * x0 ^ 2 * x1 ^ 3 - 57 * x0 ^ 2 * x2 ^ 3 - 114 * x0 ^ 2 * x3 ^ 3 -
      57 * x0 * x1 ^ 4,
0,
ι * x0 ^ 5 * x1 * x3 + ι * x0 ^ 4 * x1 ^ 2 * x3 + ι * x0 ^ 3 * x1 ^ 3 * x3 + ι * x0 ^ 3 * x1 * x2 *
      x3 ^ 2 + ι * x0 ^ 2 * x1 * x2 ^ 3 * x3 + ι * x0 * x1 ^ 2 * x2 ^ 3 * x3 - x0 ^ 5 * x1 * x3 - x0
      ^ 3 * x1 ^ 3 * x3 - x0 ^ 3 * x1 * x2 * x3 ^ 2 - x0 ^ 2 * x1 ^ 4 * x3 - x0 ^ 2 * x1 * x2 ^ 3 *
      x3 - 2 * x0 ^ 2 * x1 * x3 ^ 4 - x0 * x1 ^ 5 * x3,
0]

def bezout6 (ι x0 x1 x2 x3 : R) : Fin 4 → R :=
  ![57 * ι * x0 ^ 5 + 57 * ι * x0 ^ 4 * x1 + ι * x0 ^ 4 * x2 + 3249 * ι * x0 ^ 4 * x3 + 114 * ι * x0 ^ 3
      * x2 * x3 + 57 * ι * x0 ^ 2 * x2 ^ 3 + 3249 * ι * x0 ^ 2 * x2 * x3 ^ 2 + 57 * ι * x0 ^ 2 * x3
      ^ 3 + 3249 * ι * x0 * x2 ^ 3 * x3 - 57 * x0 ^ 4 * x1 - 3249 * x0 ^ 4 * x3 - 57 * x0 ^ 3 * x1 ^
      2 - 57 * x0 ^ 3 * x2 * x3 - 57 * x0 ^ 2 * x1 ^ 3 - 3249 * x0 ^ 2 * x2 * x3 ^ 2 - 57 * x0 ^ 2 *
      x3 ^ 3 - 3249 * x0 * x2 ^ 3 * x3 - 6498 * x0 * x3 ^ 4,
0,
ι * x0 ^ 6 * x3 + ι * x0 ^ 5 * x1 * x3 + ι * x0 ^ 4 * x1 ^ 2 * x3 + 57 * ι * x0 ^ 4 * x1 * x3 ^ 2 +
      ι * x0 ^ 4 * x2 * x3 ^ 2 + 2 * ι * x0 ^ 3 * x1 * x2 * x3 ^ 2 + ι * x0 ^ 3 * x2 ^ 3 * x3 + ι *
      x0 ^ 2 * x1 * x2 ^ 3 * x3 + 57 * ι * x0 ^ 2 * x1 * x2 * x3 ^ 3 + ι * x0 ^ 2 * x1 * x3 ^ 4 + 57
      * ι * x0 * x1 * x2 ^ 3 * x3 ^ 2 - x0 ^ 6 * x3 - x0 ^ 4 * x1 ^ 2 * x3 - 57 * x0 ^ 4 * x1 * x3 ^
      2 - x0 ^ 4 * x2 * x3 ^ 2 - x0 ^ 3 * x1 ^ 3 * x3 - x0 ^ 3 * x1 * x2 * x3 ^ 2 - x0 ^ 3 * x2 ^ 3
      * x3 - 2 * x0 ^ 3 * x3 ^ 4 - x0 ^ 2 * x1 ^ 4 * x3 - 57 * x0 ^ 2 * x1 * x2 * x3 ^ 3 - x0 ^ 2 *
      x1 * x3 ^ 4 - 57 * x0 * x1 * x2 ^ 3 * x3 ^ 2 - 114 * x0 * x1 * x3 ^ 5,
0]

def bezout (ι x0 x1 x2 x3 : R) : Fin 7 → Fin 4 → R :=
  ![bezout0 ι x0 x1 x2 x3, bezout1 ι x0 x1 x2 x3, bezout2 ι x0 x1 x2 x3, bezout3 ι x0 x1 x2 x3, bezout4 ι x0 x1 x2 x3, bezout5 ι x0 x1 x2 x3, bezout6 ι x0 x1 x2 x3]

/-- Literal polynomial identities over any commutative ring containing
an element whose square is minus one. -/
theorem obstruction_identity (ι x0 x1 x2 x3 : R) (hι : ι ^ 2 = -1)
    (j : Fin 7) :
    sparseK ι x0 x1 x2 x3 * chosenCubic ι x0 x1 * reducedTest x0 x1 x2 x3 j =
      ∑ a : Fin 4, bezout ι x0 x1 x2 x3 j a * reducedRelations ι x0 x1 x2 x3 a := by
  fin_cases j <;>
    norm_num [bezout, bezout0, bezout1, bezout2, bezout3, bezout4, bezout5, bezout6,
      reducedRelations, sparseK, sparseH, chosenCubic, reducedTest,
      Fin.sum_univ_succ]
  · linear_combination (-x0 ^ 3 * x1 ^ 3 * x2 ^ 3 - x0 ^ 3 * x2 ^ 3 * x3 ^ 3 - x0 ^ 2 * x1 ^ 4 * x2 ^ 3 - x0 ^ 2 * x1 * x2 ^ 3 * x3 ^ 3 + 57 * x0 * x1 ^ 4 * x2 ^ 3 * x3 + 57 * x0 * x1 * x2 ^ 3 * x3 ^ 4 + 57 * x1 ^ 5 * x2 ^ 3 * x3 + 57 * x1 ^ 2 * x2 ^ 3 * x3 ^ 4) * hι
  · linear_combination (x0 ^ 3 * x1 ^ 3 * x2 * x3 ^ 2 + x0 ^ 3 * x2 * x3 ^ 5 + x0 ^ 2 * x1 ^ 4 * x2 * x3 ^ 2 + x0 ^ 2 * x1 * x2 * x3 ^ 5 - 57 * x0 * x1 ^ 4 * x2 * x3 ^ 3 - 57 * x0 * x1 * x2 * x3 ^ 6) * hι
  · linear_combination (x0 ^ 3 * x1 ^ 4 * x2 ^ 2 + x0 ^ 3 * x1 * x2 ^ 2 * x3 ^ 3 + x0 ^ 2 * x1 ^ 5 * x2 ^ 2 + x0 ^ 2 * x1 ^ 2 * x2 ^ 2 * x3 ^ 3 - 57 * x0 * x1 ^ 5 * x2 ^ 2 * x3 - 57 * x0 * x1 ^ 2 * x2 ^ 2 * x3 ^ 4 - 57 * x1 ^ 6 * x2 ^ 2 * x3 - 57 * x1 ^ 3 * x2 ^ 2 * x3 ^ 4) * hι
  · linear_combination (x0 ^ 3 * x1 ^ 5 * x3 + x0 ^ 3 * x1 ^ 2 * x3 ^ 4 + x0 ^ 2 * x1 ^ 6 * x3 + x0 ^ 2 * x1 ^ 3 * x3 ^ 4) * hι
  · linear_combination (x0 ^ 4 * x1 ^ 3 * x2 ^ 2 + x0 ^ 4 * x2 ^ 2 * x3 ^ 3 + x0 ^ 3 * x1 ^ 4 * x2 ^ 2 + x0 ^ 3 * x1 * x2 ^ 2 * x3 ^ 3 - 57 * x0 * x1 ^ 5 * x2 ^ 2 * x3 - 57 * x0 * x1 ^ 2 * x2 ^ 2 * x3 ^ 4) * hι
  · linear_combination (x0 ^ 4 * x1 ^ 4 * x3 + x0 ^ 4 * x1 * x3 ^ 4 + x0 ^ 3 * x1 ^ 5 * x3 + x0 ^ 3 * x1 ^ 2 * x3 ^ 4) * hι
  · linear_combination (x0 ^ 5 * x1 ^ 3 * x3 + x0 ^ 5 * x3 ^ 4 + x0 ^ 4 * x1 ^ 4 * x3 + x0 ^ 4 * x1 * x3 ^ 4) * hι

end Arithmetic

open CycleQ2SeedTrace CycleQ2NormalConnecting CycleQ2SeedCechTheta

/-- The five literal defining polynomials, including the smooth theta-one cubic. -/
def traceRelations : Fin 5 → WeightedPoly :=
  ![originalF1 57, originalF2, originalG1 57, originalG2, thetaH 1]

def traceIdeal : Ideal WeightedPoly := Ideal.span (Set.range traceRelations)

def selectedCubic : WeightedPoly :=
  chosenCubic (C Complex.I) (X 0) (X 1)

/-- The complete seven-dimensional character-one cubic test basis. -/
def testCubic : Fin 7 → WeightedPoly :=
  ![X 2 * X 4, X 2 * X 3 ^ 2, X 1 * X 2 ^ 2, X 1 ^ 2 * X 3,
    X 0 * X 2 ^ 2, X 0 * X 1 * X 3, X 0 ^ 2 * X 3]

private theorem scalar_i_sq : (C Complex.I : WeightedPoly) ^ 2 = -1 := by
  rw [← map_pow, Complex.I_sq, map_neg, map_one]

private theorem relation_mem (j : Fin 5) : traceRelations j ∈ traceIdeal :=
  Ideal.subset_span ⟨j, rfl⟩

private theorem first_reduced_mem : X 1 ^ 2 * X 3 ^ 2 ∈ traceIdeal := by
  have hF : originalF1 (57 : ℂ) ∈ traceIdeal := relation_mem 0
  have hG : originalG1 (57 : ℂ) ∈ traceIdeal := relation_mem 2
  have hh := traceIdeal.sub_mem hG
    (Ideal.mul_mem_right (X 0 ^ 2 + 114 * X 1 * X 3) traceIdeal hF)
  have he : originalG1 (57 : ℂ) - originalF1 57 *
      (X 0 ^ 2 + 114 * X 1 * X 3) =
      (9747 : WeightedPoly) * (X 1 ^ 2 * X 3 ^ 2) := by
    norm_num [originalF1, originalG1, map_pow, map_ofNat]
    ring
  rw [he] at hh
  have hm := Ideal.mul_mem_left traceIdeal (C ((9747 : ℂ)⁻¹)) hh
  have hid : C ((9747 : ℂ)⁻¹) * (9747 : WeightedPoly) = 1 := by
    have hh : (9747 : ℂ)⁻¹ * 9747 = 1 := by norm_num
    simpa only [map_mul, map_ofNat, map_one] using
      congrArg (C : ℂ → WeightedPoly) hh
  simpa only [← mul_assoc, hid, one_mul] using hm

private theorem second_reduced_mem : X 2 ^ 4 ∈ traceIdeal := by
  have hF : originalF2 ∈ traceIdeal := relation_mem 1
  have hG : originalG2 ∈ traceIdeal := relation_mem 3
  have hh := traceIdeal.sub_mem hG
    (Ideal.mul_mem_right (X 4 - 2 * X 2 ^ 2) traceIdeal hF)
  have he : originalG2 - originalF2 * (X 4 - 2 * X 2 ^ 2) =
      (3 : WeightedPoly) * (X 2 ^ 4) := by
    unfold originalF2 originalG2
    ring
  rw [he] at hh
  have hm := Ideal.mul_mem_left traceIdeal (C ((3 : ℂ)⁻¹)) hh
  have hid : C ((3 : ℂ)⁻¹) * (3 : WeightedPoly) = 1 := by
    have hh : (3 : ℂ)⁻¹ * 3 = 1 := by norm_num
    simpa only [map_mul, map_ofNat, map_one] using
      congrArg (C : ℂ → WeightedPoly) hh
  simpa only [← mul_assoc, hid, one_mul] using hm

private theorem sparseH_binding :
    sparseH (C Complex.I) (X 0) (X 1) (X 2) (X 3) = thetaH 1 := by
  simp [sparseH, thetaH, originalH, originalB]
  ring

private theorem sparseK_binding :
    sparseK (C Complex.I) (X 0) (X 1) (X 2) (X 3) = thetaK 1 := by
  simp [sparseK, thetaK, originalK, originalB]
  ring

private theorem reduced_relation_mem (j : Fin 4) :
    reducedRelations (C Complex.I) (X 0) (X 1) (X 2) (X 3) j ∈ traceIdeal := by
  fin_cases j
  · exact first_reduced_mem
  · exact second_reduced_mem
  · have hh : originalF1 (57 : ℂ) ∈ traceIdeal := relation_mem 0
    simpa [reducedRelations, originalF1, map_ofNat] using hh
  · change sparseH (C Complex.I) (X 0) (X 1) (X 2) (X 3) ∈ traceIdeal
    rw [sparseH_binding]
    exact relation_mem 4

/-- Every character-one test annihilates the selected actual cubic in the
literal smooth-seed trace quotient. This is an ideal-membership theorem,
not a statement about a separately defined numerical matrix. -/
theorem selected_test_mem (j : Fin 7) :
    thetaK 1 * selectedCubic * testCubic j ∈ traceIdeal := by
  have hm : thetaK 1 * selectedCubic *
      reducedTest (X 0) (X 1) (X 2) (X 3) j ∈ traceIdeal := by
    rw [← sparseK_binding, selectedCubic, obstruction_identity _ _ _ _ _ scalar_i_sq]
    apply Ideal.sum_mem
    intro a ha
    exact Ideal.mul_mem_left _ _ (reduced_relation_mem a)
  have he : testCubic j = reducedTest (X 0) (X 1) (X 2) (X 3) j +
      (if j = 0 then X 2 * originalF2 else 0) := by
    fin_cases j <;> simp [testCubic, reducedTest, originalF2] <;> ring
  rw [he, mul_add]
  apply traceIdeal.add_mem hm
  split_ifs with hj
  · exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ (relation_mem 1))
  · simp

/-- The chosen polynomial is exactly the previously defined coefficient vector. -/
theorem selectedCubic_binding :
    substitute selectedCubic = cubicDeformation selectedTangent := by
  simp [substitute, selectedCubic, chosenCubic, cubicDeformation, selectedTangent,
    CycleQ2SeedCechTheta.cubicColumn, mon, Fin.sum_univ_succ]
  ring

/-- Scale the existing direction so that its established derivative trace is one. -/
def traceOneCoefficients : Fin 9 → ℂ := fun j => 3 * selectedTangent j

theorem traceOne_trace : derivativeTrace 1 traceOneCoefficients = 1 := by
  have he : derivativeTrace 1 traceOneCoefficients =
      3 * derivativeTrace 1 selectedTangent := by
    simp only [derivativeTrace_explicit, traceOneCoefficients]
    ring
  rw [he, selectedTangent_trace]
  norm_num

theorem traceOne_cubic :
    cubicDeformation traceOneCoefficients = C (3 : ℂ) * substitute selectedCubic := by
  rw [selectedCubic_binding]
  simp only [cubicDeformation, traceOneCoefficients, map_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem traceOne_test_mem (j : Fin 7) :
    thetaK 1 * (C (3 : ℂ) * selectedCubic) * testCubic j ∈ traceIdeal := by
  convert Ideal.mul_mem_left traceIdeal (C (3 : ℂ)) (selected_test_mem j) using 1 <;> ring

theorem traceOne_not_boundary :
    ¬ CechBoundary 57 1
      (derivativeNumerator (cubicDeformation traceOneCoefficients)) 2 4 := by
  apply nonboundary_of_derivativeTrace_ne_zero 57 1 (by norm_num)
  rw [traceOne_trace]
  norm_num

theorem traceOne_paired_normal_trace :
    pairedNormalTrace 57 1 (by norm_num) (cubicDeformation traceOneCoefficients) =
      -(1 / 171 : ℂ) := by
  rw [pairedNormalTrace_deformation, traceOne_trace]
  norm_num

end CycleQ2ExplicitSeedDirection
end

#print axioms CycleQ2ExplicitSeedDirection.selected_test_mem
#print axioms CycleQ2ExplicitSeedDirection.traceOne_not_boundary
#print axioms CycleQ2ExplicitSeedDirection.traceOne_paired_normal_trace
