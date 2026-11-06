import Proposal.CommonCoverBaseChange
import HodgeComputer.Constructions.HoldoutCover.FiniteDifferentials

/- Source component: FermatCoefficientDerivations -/
section
/-!
A derivation kills the Fermat coefficient field once it kills the base
constants and the two displayed Fermat coordinates. The proof uses the
actual polynomial generators and the quotient rule, so it makes no
assumption that the coefficient field is algebraic over the constants.
-/

noncomputable section

namespace HoldoutConstruction

section Polynomial

variable {R L : Type*} [CommRing R] [Field L]

theorem derivation_zero_polynomial_image
    (E : Derivation ℤ L L) (φ : Polynomial R →+* L)
    (hC : ∀ c : R, E (φ (Polynomial.C c)) = 0)
    (hX : E (φ Polynomial.X) = 0) (p : Polynomial R) : E (φ p) = 0 := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, hp, hq, add_zero]
  | monomial n a =>
    rw [← Polynomial.C_mul_X_pow_eq_monomial]
    simp only [map_mul, map_pow, Derivation.leibniz, Derivation.leibniz_pow,
      smul_eq_mul, hC, hX, mul_zero, smul_zero, add_zero]

theorem fermatBase_derivation_zero
    (E : Derivation ℤ L L) (φ : FermatBaseRing R →+* L)
    (hC : ∀ c : R, E (φ (algebraMap R (FermatBaseRing R) c)) = 0)
    (hα : E (φ (baseAlpha (R := R))) = 0)
    (hβ : E (φ (baseBeta (R := R))) = 0) :
    ∀ c : FermatBaseRing R, E (φ c) = 0 := by
  have hcoeff (p : Polynomial R) : E (φ (AdjoinRoot.of _ p)) = 0 := by
    apply derivation_zero_polynomial_image E (φ.comp (AdjoinRoot.of _))
    · exact hC
    · exact hβ
  intro c
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective c
  apply derivation_zero_polynomial_image E (φ.comp (AdjoinRoot.mk _))
  · intro q
    simpa only [RingHom.comp_apply, AdjoinRoot.mk_C] using hcoeff q
  · exact hα

end Polynomial

section Fraction

variable {K L : Type*} [Field K] [CharZero K] [Field L]

attribute [local instance] fermatCurve_adjoinRoot_isDomain

theorem fermatCoefficient_derivation_zero
    (E : Derivation ℤ L L) (φ : FermatCoefficientField K →+* L)
    (hC : ∀ c : K, E (φ (algebraMap K (FermatCoefficientField K) c)) = 0)
    (hα : E (φ (genericBaseAlpha K)) = 0)
    (hβ : E (φ (genericBaseBeta K)) = 0) :
    ∀ c : FermatCoefficientField K, E (φ c) = 0 := by
  have hring (c : FermatBaseRing K) :
      E (φ (algebraMap (FermatBaseRing K) (FermatCoefficientField K) c)) = 0 := by
    apply fermatBase_derivation_zero E
      (φ.comp (algebraMap (FermatBaseRing K) (FermatCoefficientField K)))
    · intro a
      simpa only [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply] using hC a
    · exact hα
    · exact hβ
  intro c
  obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective (FermatBaseRing K) c
  rw [map_div₀, Derivation.leibniz_div, hring a, hring b]
  simp

end Fraction

end HoldoutConstruction

#print axioms HoldoutConstruction.fermatCoefficient_derivation_zero
end
end
