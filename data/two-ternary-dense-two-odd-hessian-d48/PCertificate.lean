import HodgeTestbed.Algebra
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.Coprime.Lemmas

/-!
# Certificate interface for two ternary variable groups

Indices `0,1,2,3,4,5` mean `X₀,X₁,X₂,Y₀,Y₁,Y₂`. Parity means simultaneous negation
of all three Y variables, not separate evenness or oddness in each Y variable.
-/

set_option autoImplicit false

noncomputable section

namespace HodgeTestbed

open MvPolynomial

abbrev SexticPoly := MvPolynomial (Fin 6) ℚ

/-- Simultaneous reflection of the Y variables, fixing the X variables. -/
def reflectY : SexticPoly →+* SexticPoly :=
  eval₂Hom C (fun i => if i.val < 3 then X i else -X i)

/-- Global Y-evenness. -/
def YEven (P : SexticPoly) : Prop := reflectY P = P

/-- Global Y-oddness. Zero satisfies this, as required for numerator components. -/
def YOdd (P : SexticPoly) : Prop := reflectY P = -P

/-- Correct denominator legality: every common divisor is a unit.
This is `IsRelPrime`, not the stronger Bezout/comaximal condition `IsCoprime`. -/
def DenominatorLegal (F D : SexticPoly) : Prop := IsRelPrime F D

theorem denominatorLegal_iff (F D : SexticPoly) :
    DenominatorLegal F D ↔ ∀ P : SexticPoly, P ∣ F → P ∣ D → IsUnit P := Iff.rfl

theorem YEven.mul {P Q : SexticPoly} (hP : YEven P) (hQ : YEven Q) :
    YEven (P * Q) := by
  unfold YEven at *
  rw [map_mul, hP, hQ]

theorem YEven.mul_odd {P Q : SexticPoly} (hP : YEven P) (hQ : YOdd Q) :
    YOdd (P * Q) := by
  unfold YEven YOdd at *
  rw [map_mul, hP, hQ, mul_neg]

/-- A fully legal certificate, parameterized by the actual witness data.
`IsHomogeneous 0 (d+1)` holds: zero numerator components are allowed.
No strictness requirement and no bound on `d` are imposed. -/
structure Certificate (F A : SexticPoly) (d : ℕ) (D : SexticPoly)
    (N : Fin 6 → SexticPoly) (C : SexticPoly) : Prop extends Equations F A D N C where
  positive_degree : 0 < d
  denominator_ne_zero : D ≠ 0
  denominator_homogeneous : D.IsHomogeneous d
  numerator_homogeneous : ∀ i, (N i).IsHomogeneous (d + 1)
  denominator_even : YEven D
  numerator_parity : ∀ i, if i.val < 3 then YOdd (N i) else YEven (N i)
  denominator_legal : DenominatorLegal F D

/-- Witness-requiring endpoint; an actual construction supplies `d,D,N,C` and their checks. -/
def HasCertificate (F A : SexticPoly) : Prop :=
  ∃ (d : ℕ) (D : SexticPoly) (N : Fin 6 → SexticPoly) (C : SexticPoly),
    Certificate F A d D N C

/-- Scaling by a legal nonzero homogeneous even polynomial preserves all certificate fields.
The new residual may be nonzero, and scales by `H²`. -/
theorem Certificate.scale {F A D C H : SexticPoly} {d e : ℕ}
    {N : Fin 6 → SexticPoly} (h : Certificate F A d D N C)
    (hH : H ≠ 0) (hHom : H.IsHomogeneous e) (hEven : YEven H)
    (hLegal : DenominatorLegal F H) :
    Certificate F A (e + d) (H * D) (fun i => H * N i) (H ^ 2 * C) where
  toEquations := h.toEquations.scale H
  positive_degree := Nat.add_pos_right e h.positive_degree
  denominator_ne_zero := mul_ne_zero hH h.denominator_ne_zero
  denominator_homogeneous := hHom.mul h.denominator_homogeneous
  numerator_homogeneous i := by
    simpa only [Nat.add_assoc] using hHom.mul (h.numerator_homogeneous i)
  denominator_even := hEven.mul h.denominator_even
  numerator_parity i := by
    have hi := h.numerator_parity i
    split_ifs with hlt
    · rw [ite_eq_left hlt] at hi
      exact hEven.mul_odd hi
    · rw [ite_eq_right hlt] at hi
      exact hEven.mul hi
  denominator_legal := hLegal.mul_right h.denominator_legal

end HodgeTestbed
