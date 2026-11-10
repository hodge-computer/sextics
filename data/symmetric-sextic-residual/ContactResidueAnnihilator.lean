import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum

/-!
Exact algebra behind the actual-target contact-jet calculation.

For a fixed cubic `G`, a contact satisfies
`G(-Q₁) = A² - B² + Q₂*g₂`. Differentiating along its parameter curve gives
`(A-B)*D(A+B) = 0` modulo `(Q₂, A+B, G_u(-Q₁), g₂)`.
Consequently the residue functional `R ↦ τ(R*D(A+B))` kills the five
generators used by the 40-by-44 obstruction matrix.

This file proves that annihilation algebraically; it does not infer exact
zeros from numerical intervals containing zero. The geometric construction
of τ, its nonvanishing, the analytic contact branch, and the correspondence
comparison are separate obligations. No target certificate is asserted here.
-/

noncomputable section
namespace ContactResidueAnnihilator

variable {K R : Type*} [Field K] [CommRing R] [Algebra K R]

def cubicAtNegative (c₂ c₄ c₆ q₁ : R) : R :=
  -q₁ ^ 3 + c₂*q₁ ^ 2 - c₄*q₁ + c₆

def normalAtNegative (c₂ c₄ q₁ : R) : R :=
  3*q₁ ^ 2 - 2*c₂*q₁ + c₄

/-- The contact-parameter derivative, with the hypersurface coefficients fixed. -/
theorem differentiated_contact
    (D : Derivation K R R) (c₂ c₄ c₆ q₁ q₂ A B g₂ : R)
    (hc₂ : D c₂ = 0) (hc₄ : D c₄ = 0) (hc₆ : D c₆ = 0)
    (hcontact : cubicAtNegative c₂ c₄ c₆ q₁ = A^2 - B^2 + q₂*g₂) :
    (A-B)*D (A+B) + (A+B)*D (A-B)
      + normalAtNegative c₂ c₄ q₁ * D q₁ + g₂*D q₂ + q₂*D g₂ = 0 := by
  have hd := congrArg D hcontact
  simp only [cubicAtNegative, map_add, map_sub, map_neg,
    Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul,
    hc₂, hc₄, hc₆, mul_zero, add_zero] at hd
  simp only [map_add, map_sub, normalAtNegative]
  linear_combination -hd

/-- A spatial derivative of the cubic reduces to the five contact generators.
Unlike the previous lemma, its coefficients are allowed to vary. -/
theorem coordinate_source_reduction
    (d : Derivation K R R) (c₂ c₄ c₆ q₁ q₂ A B g₂ : R)
    (hcontact : cubicAtNegative c₂ c₄ c₆ q₁ = A^2 - B^2 + q₂*g₂) :
    d c₂*q₁^2 - d c₄*q₁ + d c₆ =
      2*A*d A - 2*B*d B + q₂*d g₂ + g₂*d q₂
        + normalAtNegative c₂ c₄ q₁*d q₁ := by
  have hd := congrArg d hcontact
  simp only [cubicAtNegative, map_add, map_sub, map_neg,
    Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul] at hd
  unfold normalAtNegative
  linear_combination hd

variable {L : Type*} [Field L] [CharZero L] [Algebra K L]

/-- Any functional factoring through the complete-intersection quotient kills
the full five-generator contact ideal after multiplication by `D(A+B)`.
The nonzero residue functional in the computation is such a functional.
The value field `L` may contain the parameter, while `D` is only required to
be linear over the constant field `K`. -/
theorem residue_kills_contact_generators
    (D : Derivation K R R) (τ : R →ₗ[K] L)
    (c₂ c₄ c₆ q₁ q₂ A B g₂ : R)
    (hc₂ : D c₂ = 0) (hc₄ : D c₄ = 0) (hc₆ : D c₆ = 0)
    (hcontact : cubicAtNegative c₂ c₄ c₆ q₁ = A^2 - B^2 + q₂*g₂)
    (hQ : ∀ P, τ (P*q₂) = 0)
    (hH : ∀ P, τ (P*(A+B)) = 0)
    (hN : ∀ P, τ (P*normalAtNegative c₂ c₄ q₁) = 0)
    (hG : ∀ P, τ (P*g₂) = 0) :
    ∀ P, τ (P*q₂*D (A+B)) = 0 ∧
      τ (P*normalAtNegative c₂ c₄ q₁*D (A+B)) = 0 ∧
      τ (P*g₂*D (A+B)) = 0 ∧
      τ (P*A*D (A+B)) = 0 ∧ τ (P*B*D (A+B)) = 0 := by
  intro P
  have hd := differentiated_contact D c₂ c₄ c₆ q₁ q₂ A B g₂
    hc₂ hc₄ hc₆ hcontact
  have hm : τ (P*(A-B)*D (A+B)) = 0 := by
    have he : P*(A-B)*D (A+B) =
        -(P*D (A-B)*(A+B) + P*D q₁*normalAtNegative c₂ c₄ q₁
          + P*D q₂*g₂ + P*D g₂*q₂) := by
      linear_combination P * hd
    rw [he, map_neg, map_add, map_add, map_add, hH, hN, hG, hQ]
    simp
  have hp : τ (P*(A+B)*D (A+B)) = 0 := by
    convert hH (P*D (A+B)) using 1
    congr 1
    ring
  have hA : τ (P*A*D (A+B)) = 0 := by
    have he : (2:L)*τ (P*A*D (A+B)) = 0 := by
      calc
        _ = τ (P*(A+B)*D (A+B)) + τ (P*(A-B)*D (A+B)) := by
          rw [two_mul, ← map_add, ← map_add]
          congr 1
          ring
        _ = 0 := by rw [hp, hm]; simp
    exact (mul_eq_zero.mp he).resolve_left (by norm_num)
  have hB : τ (P*B*D (A+B)) = 0 := by
    have he : τ (P*A*D (A+B)) + τ (P*B*D (A+B)) = 0 := by
      rw [← map_add]
      convert hp using 1
      congr 1
      ring
    simpa only [hA, zero_add] using he
  refine ⟨?_, ?_, ?_, hA, hB⟩
  · convert hQ (P*D (A+B)) using 1
    congr 1
    ring
  · convert hN (P*D (A+B)) using 1
    congr 1
    ring
  · convert hG (P*D (A+B)) using 1
    congr 1
    ring

/-- The contact residue annihilates spatial partial derivatives of the fixed
cubic as well. Together with the normal generator, this is the Jacobian-ideal
factorization used by the 60-dimensional source matrix. -/
theorem residue_kills_coordinate_source
    (D d : Derivation K R R) (τ : R →ₗ[K] L)
    (c₂ c₄ c₆ q₁ q₂ A B g₂ P : R)
    (hc₂ : D c₂ = 0) (hc₄ : D c₄ = 0) (hc₆ : D c₆ = 0)
    (hcontact : cubicAtNegative c₂ c₄ c₆ q₁ = A^2 - B^2 + q₂*g₂)
    (hQ : ∀ R, τ (R*q₂) = 0)
    (hH : ∀ R, τ (R*(A+B)) = 0)
    (hN : ∀ R, τ (R*normalAtNegative c₂ c₄ q₁) = 0)
    (hG : ∀ R, τ (R*g₂) = 0) :
    τ (P*(d c₂*q₁^2 - d c₄*q₁ + d c₆)*D (A+B)) = 0 := by
  have kills := residue_kills_contact_generators D τ c₂ c₄ c₆ q₁ q₂ A B g₂
    hc₂ hc₄ hc₆ hcontact hQ hH hN hG
  have he : P*(d c₂*q₁^2 - d c₄*q₁ + d c₆)*D (A+B) =
      (2*P*d A)*A*D (A+B) - (2*P*d B)*B*D (A+B)
      + (P*d g₂)*q₂*D (A+B) + (P*d q₂)*g₂*D (A+B)
      + (P*d q₁)*normalAtNegative c₂ c₄ q₁*D (A+B) := by
    rw [coordinate_source_reduction d c₂ c₄ c₆ q₁ q₂ A B g₂ hcontact]
    ring
  rw [he, map_add, map_add, map_add, map_sub,
    (kills (2*P*d A)).2.2.2.1, (kills (2*P*d B)).2.2.2.2,
    (kills (P*d g₂)).1, (kills (P*d q₂)).2.2.1, (kills (P*d q₁)).2.1]
  simp

end ContactResidueAnnihilator

#print axioms ContactResidueAnnihilator.differentiated_contact
#print axioms ContactResidueAnnihilator.coordinate_source_reduction
#print axioms ContactResidueAnnihilator.residue_kills_contact_generators
#print axioms ContactResidueAnnihilator.residue_kills_coordinate_source
