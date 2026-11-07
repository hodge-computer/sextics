import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# Finite-section cancellation for a moving cubic selector

Write `z = t^2`, `q(u) = f(alpha,u) = (u-beta)*h(u)`, with quadratic `h`,
and `f(t,u) = q(u) + (t^2-alpha^2)*H(z,u)`. The symbols with suffix `Dot`
denote coefficient derivatives: `alphaDot = D alpha`, `betaDot = D beta`,
and the displayed definitions include both moving-root chain rules.

The cleared selector numerator is a multiple of `t^2-alpha^2` modulo `f`.
This proves cancellation at the finite moving sections. It does not prove
an infinity correction, a traced-source identity, or primitive existence.
-/

namespace CubicSelectorCancellation

section PolynomialIdentities

variable {R : Type*} [CommRing R]

set_option maxHeartbeats 2000000

/-- Differentiating the moving root and the selector normalization supplies
the factor `(u-beta)*h`. No simple-root assumption is needed after clearing. -/
theorem moving_selector_identity
    (u beta betaDot h0 h1 h2 h0Dot h1Dot h2Dot : R) :
    let h := h2*u^2+h1*u+h0
    let hU := 2*h2*u+h1
    let hDot := h2Dot*u^2+h1Dot*u+h0Dot
    let g := h2*beta^2+h1*beta+h0
    let gDot := h2Dot*beta^2+h1Dot*beta+h0Dot+(2*h2*beta+h1)*betaDot
    let q := (u-beta)*h
    let qU := h+(u-beta)*hU
    let qDot := (u-beta)*hDot-betaDot*h
    let S := (3*h2*u+h2*beta+2*h1)*gDot-
      g*((u+beta)*h2Dot+h1Dot+2*h2*betaDot)
    g*hU*qDot-qU*(g*hDot-h*gDot) = q*S := by
  dsimp
  ring

/-- An explicit polynomial quotient for the general cubic selector.

Here `HU`, `Hz`, and `HDot` denote the normal, `z`, and coefficient
derivatives of `H`; `fT` and `fDot` include the moving-alpha correction.
The selector is `h/g`, so `numerator` is `g^2/2` times the numerator in
the differentiated selector-current formula. -/
theorem moving_even_numerator_decomposition
    (t u alpha alphaDot beta betaDot h0 h1 h2 h0Dot h1Dot h2Dot
      H HU Hz HDot : R) :
    let h := h2*u^2+h1*u+h0
    let hU := 2*h2*u+h1
    let hDot := h2Dot*u^2+h1Dot*u+h0Dot
    let g := h2*beta^2+h1*beta+h0
    let gDot := h2Dot*beta^2+h1Dot*beta+h0Dot+(2*h2*beta+h1)*betaDot
    let q := (u-beta)*h
    let qU := h+(u-beta)*hU
    let qDot := (u-beta)*hDot-betaDot*h
    let S := (3*h2*u+h2*beta+2*h1)*gDot-
      g*((u+beta)*h2Dot+h1Dot+2*h2*betaDot)
    let f := q+(t^2-alpha^2)*H
    let fU := qU+(t^2-alpha^2)*HU
    let fT := 2*t*(H+(t^2-alpha^2)*Hz)
    let fDot := qDot-2*alpha*alphaDot*H+(t^2-alpha^2)*HDot
    let K := 2*alphaDot*(H+t^2*Hz)+alpha*HDot
    let quotient := g*hU*K-alpha*HU*(g*hDot-h*gDot)-alpha*H*S
    let numerator := g*hU*(t*alphaDot*fT+alpha*fDot)-
      alpha*fU*(g*hDot-h*gDot)
    numerator = alpha*f*S+(t^2-alpha^2)*quotient := by
  dsimp
  ring

end PolynomialIdentities

section RationalCancellation

variable {K : Type*} [Field K]

/-- In the hypersurface field, the explicit polynomial quotient removes
the finite-section denominator before taking any field trace. -/
theorem cancel_section_denominator
    (numerator f S quotient alpha t g fU : K)
    (hdecomposition : numerator = alpha*f*S+(t^2-alpha^2)*quotient)
    (hf : f = 0) (hg : g ≠ 0) (hsection : t^2-alpha^2 ≠ 0)
    (hfu : fU ≠ 0) :
    (2*numerator/g^2)/((t^2-alpha^2)*fU) =
      2*quotient/(g^2*fU) := by
  rw [hdecomposition, hf]
  simp only [mul_zero, zero_mul, zero_add]
  field_simp

end RationalCancellation

#print axioms moving_selector_identity
#print axioms moving_even_numerator_decomposition
#print axioms cancel_section_denominator

end CubicSelectorCancellation
