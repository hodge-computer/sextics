import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
Polynomial algebra for a moving-point current on a general monic cubic cover.

These are ordinary ring identities.  They do not assert a moving-point field,
a closed form, a trace identity, or the `symmetric-sextic-residual` certificate.
In particular, the actual source-matching obligation is not a hypothesis of a
theorem which concludes the project certificate.
-/

namespace GeneralCubicCurrent

section Ring

variable {K : Type*} [CommRing K]

def cubic (a b c w : K) : K := w ^ 3 + a * w ^ 2 + b * w + c
def normal (a b w : K) : K := 3 * w ^ 2 + 2 * a * w + b
def normalDeriv (a w : K) : K := 6 * w + 2 * a
def pointQuotient (d e w : K) : K := w ^ 2 + d * w + e

def sourceNumerator (a b d e da db dc dd de w : K) : K :=
  (normal a b w) ^ 2 * (dd * w + de)
  - normal a b w * pointQuotient d e w * (2 * da * w + db)
  - (normal a b w * (2 * w + d) - pointQuotient d e w * normalDeriv a w)
    * (da * w ^ 2 + db * w + dc)

def n0 (a b c d e da db dc dd de : K) : K :=
  da * (a * c * d - 2 * b * c)
  + db * (a * c - b * e)
  + dc * (2 * a * e - b * d)
  + dd * (-a ^ 2 * c + 3 * b * c)
  + de * (-3 * a * c + b ^ 2)

def n1 (a b c d e da db dc dd de : K) : K :=
  da * (a * b * d - 2 * b ^ 2 - 2 * b * e + 3 * c * d)
  + db * (a * b - 2 * b * d + 3 * c)
  + dc * (-2 * b + 6 * e)
  + dd * (-a ^ 2 * b - 3 * a * c + 4 * b ^ 2)
  + de * (a * b - 9 * c)

def n2 (a b c d e da db dc dd de : K) : K :=
  da * (a ^ 2 * d - 2 * a * b - 2 * a * e + 6 * c)
  + db * (a ^ 2 - 2 * a * d + 3 * e)
  + dc * (-2 * a + 3 * d)
  + dd * (-a ^ 3 + 4 * a * b - 9 * c)
  + de * (a ^ 2 - 3 * b)

def divisionQuotient (a b d da db dd de w : K) : K :=
  (-a * db + 3 * a * de + da * (-a * d + 2 * b) + dd * (a ^ 2 - 3 * b))
  + (3 * a * dd - 3 * da * d - 3 * db + 9 * de) * w
  + (-6 * da + 9 * dd) * w ^ 2

/-- Reduction of the differentiated current's numerator modulo the cubic. -/
theorem source_reduction (a b c d e da db dc dd de w : K) :
    sourceNumerator a b d e da db dc dd de w =
      cubic a b c w * divisionQuotient a b d da db dd de w
      + n0 a b c d e da db dc dd de
      + n1 a b c d e da db dc dd de * w
      + n2 a b c d e da db dc dd de * w ^ 2 := by
  unfold sourceNumerator normal pointQuotient normalDeriv cubic divisionQuotient n0 n1 n2
  ring

/-- The reduced source lies in the image of the second-pole normal operator. -/
theorem source_cokernel (a b c d e da db dc dd de : K) :
    3 * n0 a b c d e da db dc dd de
      - a * n1 a b c d e da db dc dd de
      + b * n2 a b c d e da db dc dd de = 0 := by
  unfold n0 n1 n2
  ring

/-- At the moving point, the point equation and its derivative make all
three reduced coefficients zero.  For polynomial coefficient functions this
is the algebraic reason that the apparent `t² - α²` denominator cancels.
Here `v` denotes the directional derivative of the chosen root. -/
theorem moving_point_remainder (a b beta da db v : K) :
    let c := -beta ^ 3 - a * beta ^ 2 - b * beta
    let d := beta + a
    let e := beta ^ 2 + a * beta + b
    let dc := -da * beta ^ 2 - db * beta - normal a b beta * v
    let dd := da + v
    let de := beta * da + db + (2 * beta + a) * v
    n0 a b c d e da db dc dd de = 0 ∧
      n1 a b c d e da db dc dd de = 0 ∧
      n2 a b c d e da db dc dd de = 0 := by
  dsimp
  refine ⟨?_, ?_, ?_⟩ <;> dsimp [n0, n1, n2, normal] <;> ring

/-- This version uses no division and is valid over every commutative ring. -/
theorem linear_normal_source_scaled (a b c d e da db dc dd de w : K) :
    normal a b w * (-2 * n2 a b c d e da db dc dd de)
      - normalDeriv a w *
        (-n1 a b c d e da db dc dd de - 2 * n2 a b c d e da db dc dd de * w) =
      6 * (n0 a b c d e da db dc dd de
        + n1 a b c d e da db dc dd de * w
        + n2 a b c d e da db dc dd de * w ^ 2) := by
  unfold normal normalDeriv n0 n1 n2
  ring

/-- Multiples of the normal derivative have zero second-pole normal source. -/
theorem normal_gauge (a b h w : K) :
    normal a b w * (h * normalDeriv a w)
      - normalDeriv a w * (h * normal a b w) = 0 := by
  ring

/-- The protected symmetric-target numerator becomes linear in `w` after
subtracting a multiple of the normal derivative.  In the application `l=λ²`
and `C=2*r*s*x/ell²`. -/
theorem target_quadratic_reduction (a b C x l w : K) :
    3 * (C * (1 - w) * (x - l * w)) - C * l * normal a b w =
      C * (3 * x - l * b) - C * (3 * (x + l) + 2 * l * a) * w := by
  unfold normal
  ring

end Ring

section Field

variable {K : Type*} [Field K] [CharZero K]

/-- The actual factor-two conversion used in the current source formula. -/
theorem linear_normal_source
    (a b M0 M1 M2 w : K) (hM : 3 * M0 - a * M1 + b * M2 = 0) :
    normal a b w * (-(2 * M2) / 3)
      - normalDeriv a w * (-M1 / 3 - (2 * M2 / 3) * w) =
      2 * (M0 + M1 * w + M2 * w ^ 2) := by
  unfold normal normalDeriv
  field_simp
  linear_combination -2 * hM

end Field

end GeneralCubicCurrent

#print axioms GeneralCubicCurrent.source_reduction
#print axioms GeneralCubicCurrent.source_cokernel
#print axioms GeneralCubicCurrent.moving_point_remainder
#print axioms GeneralCubicCurrent.linear_normal_source_scaled
#print axioms GeneralCubicCurrent.normal_gauge
#print axioms GeneralCubicCurrent.target_quadratic_reduction
#print axioms GeneralCubicCurrent.linear_normal_source
