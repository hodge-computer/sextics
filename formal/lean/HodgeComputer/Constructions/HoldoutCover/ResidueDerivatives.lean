import Mathlib.RingTheory.Derivation.Lie
import HodgeComputer.Constructions.HoldoutCover.FiniteDifferentials

/- Source component: ResidueDerivations -/
section
/-!
Compatible tangent derivations on the fraction field of a hypersurface.
The formulas descend through the actual quotient and are then extended by
the proved fraction-field quotient rule. Prepared with OpenAI ChatGPT
assistance for a contribution through GitHub account fqlx.
-/

noncomputable section

namespace HoldoutConstruction

section QuotientFactor

variable {R B K : Type*} [CommRing R] [CommRing B] [Field K] [Algebra B K]

private def factorAdditive (π : R →+* B) (surjective : Function.Surjective π)
    (D : R →+ K) (kernel : ∀ p, π p = 0 → D p = 0) : B →+ K where
  toFun b := D (Function.surjInv surjective b)
  map_zero' := kernel _ (Function.surjInv_eq surjective 0)
  map_add' a b := by
    have h := kernel (Function.surjInv surjective (a + b) -
      (Function.surjInv surjective a + Function.surjInv surjective b)) (by
        simp only [map_sub, map_add, Function.surjInv_eq, sub_self])
    simpa only [map_sub, map_add, sub_eq_zero] using h

omit [Algebra B K] in
private theorem factorAdditive_apply (π : R →+* B)
    (surjective : Function.Surjective π) (D : R →+ K)
    (kernel : ∀ p, π p = 0 → D p = 0) (p : R) :
    factorAdditive π surjective D kernel (π p) = D p := by
  have h := kernel (Function.surjInv surjective (π p) - p) (by
    simp only [map_sub, Function.surjInv_eq, sub_self])
  simpa only [factorAdditive, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    map_sub, sub_eq_zero] using h

/-- An additive Leibniz map into the quotient's fraction field descends
through a surjective quotient map when it kills its kernel. -/
def factorDerivation (π : R →+* B) (surjective : Function.Surjective π)
    (D : R →+ K) (kernel : ∀ p, π p = 0 → D p = 0)
    (leibniz : ∀ a b, D (a * b) =
      algebraMap B K (π a) * D b + algebraMap B K (π b) * D a) :
    Derivation ℤ B K :=
  Derivation.mk' (factorAdditive π surjective D kernel).toIntLinearMap (by
    intro a b
    obtain ⟨x, rfl⟩ := surjective a
    obtain ⟨y, rfl⟩ := surjective b
    change factorAdditive π surjective D kernel (π x * π y) =
      π x • factorAdditive π surjective D kernel (π y) +
      π y • factorAdditive π surjective D kernel (π x)
    rw [← map_mul, factorAdditive_apply, factorAdditive_apply, factorAdditive_apply]
    simpa only [Algebra.smul_def] using leibniz x y)

@[simp]
theorem factorDerivation_apply (π : R →+* B) (surjective : Function.Surjective π)
    (D : R →+ K) (kernel : ∀ p, π p = 0 → D p = 0)
    (leibniz : ∀ a b, D (a * b) =
      algebraMap B K (π a) * D b + algebraMap B K (π b) * D a) (p : R) :
    factorDerivation π surjective D kernel leibniz (π p) = D p :=
  factorAdditive_apply π surjective D kernel p

end QuotientFactor

section TangentFormula

variable {R K : Type*} [CommRing R] [Field K]

/-- The implicit-coordinate formula before passing to the quotient. -/
def tangentAdditive (ρ : R →+* K) (Δ₀ Δ : Derivation ℤ R R) (f : R) : R →+ K where
  toFun p := ρ (Δ p) - ρ (Δ f) / ρ (Δ₀ f) * ρ (Δ₀ p)
  map_zero' := by simp
  map_add' a b := by
    simp only [map_add, mul_add]
    ring

theorem tangentAdditive_mul (ρ : R →+* K) (Δ₀ Δ : Derivation ℤ R R)
    (f a b : R) :
    tangentAdditive ρ Δ₀ Δ f (a * b) =
      ρ a * tangentAdditive ρ Δ₀ Δ f b + ρ b * tangentAdditive ρ Δ₀ Δ f a := by
  simp only [tangentAdditive, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    Derivation.leibniz, smul_eq_mul, map_add, map_mul]
  ring

theorem tangentAdditive_equation (ρ : R →+* K) (Δ₀ Δ : Derivation ℤ R R)
    (f : R) (g₀_ne : ρ (Δ₀ f) ≠ 0) : tangentAdditive ρ Δ₀ Δ f f = 0 := by
  change ρ (Δ f) - ρ (Δ f) / ρ (Δ₀ f) * ρ (Δ₀ f) = 0
  rw [div_mul_cancel₀ _ g₀_ne, sub_self]

end TangentFormula

section ResidueField

variable {R B K : Type*} [CommRing R] [CommRing B] [IsDomain B]
variable [Field K] [Algebra B K] [IsFractionRing B K]

omit [IsDomain B] [IsFractionRing B K] in
private theorem tangentAdditive_kernel (π : R →+* B)
    (Δ₀ Δ : Derivation ℤ R R) (f : R)
    (kernel : ∀ p, π p = 0 ↔ f ∣ p)
    (g₀_ne : algebraMap B K (π (Δ₀ f)) ≠ 0) :
    ∀ p, π p = 0 → tangentAdditive ((algebraMap B K).comp π) Δ₀ Δ f p = 0 := by
  intro p hp
  obtain ⟨q, rfl⟩ := (kernel p).mp hp
  have hf : ((algebraMap B K).comp π) f = 0 := by
    change algebraMap B K (π f) = 0
    rw [(kernel f).mpr (dvd_refl f), map_zero]
  rw [tangentAdditive_mul, tangentAdditive_equation _ _ _ _ g₀_ne,
    hf, zero_mul, mul_zero, add_zero]

/-- The tangent derivation is an actual derivation of the residue function
field, obtained by quotient descent and the proved fraction-field extension. -/
def residueTangent (π : R →+* B) (surjective : Function.Surjective π)
    (Δ₀ Δ : Derivation ℤ R R) (f : R)
    (kernel : ∀ p, π p = 0 ↔ f ∣ p)
    (g₀_ne : algebraMap B K (π (Δ₀ f)) ≠ 0) : Derivation ℤ K K :=
  FieldValuedFraction.extend (factorDerivation π surjective
    (tangentAdditive ((algebraMap B K).comp π) Δ₀ Δ f)
    (tangentAdditive_kernel π Δ₀ Δ f kernel g₀_ne)
    (tangentAdditive_mul ((algebraMap B K).comp π) Δ₀ Δ f))

/-- Exact compatibility with the implicit-coordinate formula. -/
theorem residueTangent_apply (π : R →+* B) (surjective : Function.Surjective π)
    (Δ₀ Δ : Derivation ℤ R R) (f : R)
    (kernel : ∀ p, π p = 0 ↔ f ∣ p)
    (g₀_ne : algebraMap B K (π (Δ₀ f)) ≠ 0) (p : R) :
    residueTangent π surjective Δ₀ Δ f kernel g₀_ne (algebraMap B K (π p)) =
      algebraMap B K (π (Δ p)) -
        algebraMap B K (π (Δ f)) / algebraMap B K (π (Δ₀ f)) *
          algebraMap B K (π (Δ₀ p)) := by
  rw [residueTangent, FieldValuedFraction.extend_map, factorDerivation_apply]
  rfl

end ResidueField

end HoldoutConstruction

#print axioms HoldoutConstruction.factorDerivation_apply
#print axioms HoldoutConstruction.residueTangent_apply
end
end

/- Source component: ResidueCommutation -/
section
/-!
Commutation of the implicit-coordinate derivations on a hypersurface's
function field. Prepared with OpenAI ChatGPT assistance for a contribution
through GitHub account fqlx. This is generic algebra, not a certificate.
-/

noncomputable section

namespace HoldoutConstruction

section Formula

variable {R K : Type*} [CommRing R] [Field K]

/-- The two implicit-coordinate derivations commute on the image of the
polynomial ring. All commutation hypotheses are explicit. -/
theorem tangent_commute_on_image
    (ρ : R →+* K) (Δ₀ Δ₁ Δ₂ : Derivation ℤ R R)
    (E₁ E₂ : Derivation ℤ K K) (f : R)
    (commute₁ : ∀ p, Δ₁ (Δ₀ p) = Δ₀ (Δ₁ p))
    (commute₂ : ∀ p, Δ₂ (Δ₀ p) = Δ₀ (Δ₂ p))
    (commute₁₂ : ∀ p, Δ₁ (Δ₂ p) = Δ₂ (Δ₁ p))
    (compatible₁ : ∀ p, E₁ (ρ p) =
      ρ (Δ₁ p) - ρ (Δ₁ f) / ρ (Δ₀ f) * ρ (Δ₀ p))
    (compatible₂ : ∀ p, E₂ (ρ p) =
      ρ (Δ₂ p) - ρ (Δ₂ f) / ρ (Δ₀ f) * ρ (Δ₀ p)) (p : R) :
    E₁ (E₂ (ρ p)) = E₂ (E₁ (ρ p)) := by
  have hc : E₁ (ρ (Δ₂ f) / ρ (Δ₀ f)) =
      E₂ (ρ (Δ₁ f) / ρ (Δ₀ f)) := by
    by_cases hg : ρ (Δ₀ f) = 0
    · simp [hg]
    · rw [Derivation.leibniz_div, Derivation.leibniz_div]
      simp only [smul_eq_mul, compatible₁, compatible₂,
        commute₁, commute₂, commute₁₂]
      field_simp
      ring
  rw [compatible₂ p, compatible₁ p]
  simp only [map_sub, Derivation.leibniz, smul_eq_mul]
  rw [compatible₁ (Δ₂ p), compatible₁ (Δ₀ p), compatible₂ (Δ₁ p),
    compatible₂ (Δ₀ p), hc, commute₁₂ p, commute₁ p, commute₂ p]
  ring

end Formula

section FractionField

variable {R B K : Type*} [CommRing R] [CommRing B] [IsDomain B]
variable [Field K] [Algebra B K] [IsFractionRing B K]

omit [IsDomain B] in
/-- Compatibility on polynomial representatives and commuting ambient
partials imply commutation on the entire residue function field. -/
theorem residue_derivations_commute_of_compatible
    (π : R →+* B) (surjective : Function.Surjective π)
    (Δ₀ Δ₁ Δ₂ : Derivation ℤ R R) (E₁ E₂ : Derivation ℤ K K) (f : R)
    (commute₁ : ∀ p, Δ₁ (Δ₀ p) = Δ₀ (Δ₁ p))
    (commute₂ : ∀ p, Δ₂ (Δ₀ p) = Δ₀ (Δ₂ p))
    (commute₁₂ : ∀ p, Δ₁ (Δ₂ p) = Δ₂ (Δ₁ p))
    (compatible₁ : ∀ p, E₁ (algebraMap B K (π p)) =
      algebraMap B K (π (Δ₁ p)) -
        algebraMap B K (π (Δ₁ f)) / algebraMap B K (π (Δ₀ f)) *
          algebraMap B K (π (Δ₀ p)))
    (compatible₂ : ∀ p, E₂ (algebraMap B K (π p)) =
      algebraMap B K (π (Δ₂ p)) -
        algebraMap B K (π (Δ₂ f)) / algebraMap B K (π (Δ₀ f)) *
          algebraMap B K (π (Δ₀ p))) :
    Function.Commute E₁ E₂ := by
  have himage := tangent_commute_on_image ((algebraMap B K).comp π)
    Δ₀ Δ₁ Δ₂ E₁ E₂ f commute₁ commute₂ commute₁₂ compatible₁ compatible₂
  have hbracket : ⁅E₁, E₂⁆ = (0 : Derivation ℤ K K) := by
    apply FieldValuedFraction.derivation_ext (P := B)
    intro b
    obtain ⟨p, rfl⟩ := surjective b
    change E₁ (E₂ (((algebraMap B K).comp π) p)) -
      E₂ (E₁ (((algebraMap B K).comp π) p)) = 0
    exact sub_eq_zero.mpr (himage p)
  intro x
  have h := congrArg (fun D : Derivation ℤ K K => D x) hbracket
  simpa only [Derivation.commutator_apply, FunLike.coe_zero,
    Pi.zero_apply, sub_eq_zero] using h

/-- The tangent derivations constructed by quotient descent and fraction
extension commute whenever the corresponding ambient partials commute. -/
theorem residueTangent_commute
    (π : R →+* B) (surjective : Function.Surjective π)
    (Δ₀ Δ₁ Δ₂ : Derivation ℤ R R) (f : R)
    (kernel : ∀ p, π p = 0 ↔ f ∣ p)
    (g₀_ne : algebraMap B K (π (Δ₀ f)) ≠ 0)
    (commute₁ : ∀ p, Δ₁ (Δ₀ p) = Δ₀ (Δ₁ p))
    (commute₂ : ∀ p, Δ₂ (Δ₀ p) = Δ₀ (Δ₂ p))
    (commute₁₂ : ∀ p, Δ₁ (Δ₂ p) = Δ₂ (Δ₁ p)) :
    Function.Commute
      (residueTangent π surjective Δ₀ Δ₁ f kernel g₀_ne)
      (residueTangent π surjective Δ₀ Δ₂ f kernel g₀_ne) := by
  apply residue_derivations_commute_of_compatible π surjective Δ₀ Δ₁ Δ₂
    _ _ f commute₁ commute₂ commute₁₂
  · exact residueTangent_apply π surjective Δ₀ Δ₁ f kernel g₀_ne
  · exact residueTangent_apply π surjective Δ₀ Δ₂ f kernel g₀_ne

end FractionField

end HoldoutConstruction

#print axioms HoldoutConstruction.residue_derivations_commute_of_compatible
#print axioms HoldoutConstruction.residueTangent_commute
end
end
