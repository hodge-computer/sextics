import Proposal.GeometricDualNumberRegularQuotient
import Mathlib.RingTheory.Localization.Basic
import Mathlib.RingTheory.Localization.Ideal

/-!
# Exact quotient reduction on actual principal refinements

Localization of a quotient is identified with the quotient of the
localization by the mapped ideal. The equivalence is recorded on every
original numerator. Its epsilon specialization therefore preserves the
actual first-order section equation on a principal chart refinement.

Source-only draft: compilation and kernel replay are deferred.
Prepared for fqlx with OpenAI ChatGPT assistance, following the geometric
strategy credited to Ben Diamond and the project in solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2FirstOrderLocalizedReduction

open scoped DualNumber
open CycleQ2DualNumberRegularQuotient

section QuotientLocalization

variable {R R' : Type*} [CommRing R] [CommRing R']

abbrev LocalizedQuotient (I : Ideal R) (g : R) :=
  Localization.Away g ⧸ I.map (algebraMap R (Localization.Away g))

instance localizedQuotient_isLocalization (I : Ideal R) (g : R) :
    IsLocalization.Away (Ideal.Quotient.mk I g) (LocalizedQuotient I g) := by
  simpa only [Algebra.algebraMapSubmonoid, Submonoid.map_powers,
    Ideal.Quotient.algebraMap_eq] using
    (inferInstance : IsLocalization
      (Algebra.algebraMapSubmonoid (R ⧸ I) (Submonoid.powers g))
      (LocalizedQuotient I g))

/-- Both sides are the original quotient localized at the original
element, with the supplied quotient identification made explicit. -/
def quotientAwayEquiv (I : Ideal R) (g : R) (e : (R ⧸ I) ≃+* R')
    (g' : R') (hg : e (Ideal.Quotient.mk I g) = g') :
    LocalizedQuotient I g ≃+* Localization.Away g' :=
  IsLocalization.ringEquivOfRingEquiv
    (M := Submonoid.powers (Ideal.Quotient.mk I g))
    (T := Submonoid.powers g')
    (LocalizedQuotient I g) _ e (by
      rw [Submonoid.map_powers]
      change Submonoid.powers (e (Ideal.Quotient.mk I g)) = Submonoid.powers g'
      rw [hg])

@[simp] theorem quotientAwayEquiv_mk (I : Ideal R) (g a : R)
    (e : (R ⧸ I) ≃+* R') (g' : R') (hg : e (Ideal.Quotient.mk I g) = g') :
    quotientAwayEquiv I g e g' hg
        (Ideal.Quotient.mk (I.map (algebraMap R (Localization.Away g)))
          (algebraMap R (Localization.Away g) a)) =
      algebraMap R' (Localization.Away g')
        (e (Ideal.Quotient.mk I a)) := by
  change quotientAwayEquiv I g e g' hg
    (algebraMap (R ⧸ I) (LocalizedQuotient I g) (Ideal.Quotient.mk I a)) = _
  exact IsLocalization.ringEquivOfRingEquiv_eq _ _

/-- The same localization comparison preserves an original scalar
algebra whenever the supplied quotient comparison does. -/
def quotientAwayAlgEquiv {A : Type*} [CommRing A]
    [Algebra A R] [Algebra A R'] (I : Ideal R) (g : R)
    (e : (R ⧸ I) ≃ₐ[A] R') (g' : R') (hg : e (Ideal.Quotient.mk I g) = g') :
    LocalizedQuotient I g ≃ₐ[A] Localization.Away g' := by
  letI : IsScalarTower A (R ⧸ I) (LocalizedQuotient I g) :=
    IsScalarTower.of_algebraMap_eq fun a => by
      change Ideal.Quotient.mk (I.map (algebraMap R (Localization.Away g)))
          (algebraMap A (Localization.Away g) a) =
        Ideal.Quotient.mk (I.map (algebraMap R (Localization.Away g)))
          (algebraMap R (Localization.Away g) (algebraMap A R a))
      rw [IsScalarTower.algebraMap_apply A R (Localization.Away g)]
  exact IsLocalization.algEquivOfAlgEquiv
    (M := Submonoid.powers (Ideal.Quotient.mk I g))
    (T := Submonoid.powers g')
    (LocalizedQuotient I g) _ e (by
      rw [Submonoid.map_powers]
      change Submonoid.powers (e (Ideal.Quotient.mk I g)) = Submonoid.powers g'
      rw [hg])

end QuotientLocalization

section Epsilon

variable {k B B₀ : Type*} [Field k] [CommRing B] [CommRing B₀]
  [Algebra k[ε] B]

theorem epsilonIdeal_map_away (g : B) :
    (epsilonIdeal (k := k) B).map (algebraMap B (Localization.Away g)) =
      epsilonIdeal (k := k) (Localization.Away g) := by
  simp only [epsilonIdeal, Ideal.map_span, Set.image_singleton]
  rw [← IsScalarTower.algebraMap_apply k[ε] B (Localization.Away g)]

/-- The special fiber of the original principal refinement, retaining
the original numerator and the specialized localization element. -/
def localizedReductionEquiv (g : B)
    (e : (B ⧸ epsilonIdeal (k := k) B) ≃+* B₀)
    (g₀ : B₀) (hg : e (Ideal.Quotient.mk (epsilonIdeal (k := k) B) g) = g₀) :
    (Localization.Away g ⧸ epsilonIdeal (k := k) (Localization.Away g)) ≃+*
      Localization.Away g₀ :=
  (Ideal.quotientEquivAlgOfEq k[ε] (epsilonIdeal_map_away g).symm).toRingEquiv.trans
    (quotientAwayEquiv (epsilonIdeal (k := k) B) g e g₀ hg)

@[simp] theorem localizedReductionEquiv_mk (g a : B)
    (e : (B ⧸ epsilonIdeal (k := k) B) ≃+* B₀)
    (g₀ : B₀) (hg : e (Ideal.Quotient.mk (epsilonIdeal (k := k) B) g) = g₀) :
    localizedReductionEquiv g e g₀ hg
        (Ideal.Quotient.mk (epsilonIdeal (k := k) (Localization.Away g))
          (algebraMap B (Localization.Away g) a)) =
      algebraMap B₀ (Localization.Away g₀)
        (e (Ideal.Quotient.mk (epsilonIdeal (k := k) B) a)) := by
  change quotientAwayEquiv (epsilonIdeal (k := k) B) g e g₀ hg
      (Ideal.Quotient.mk ((epsilonIdeal (k := k) B).map
        (algebraMap B (Localization.Away g)))
        (algebraMap B (Localization.Away g) a)) = _
  exact quotientAwayEquiv_mk (epsilonIdeal (k := k) B) g a e g₀ hg

end Epsilon

#print axioms quotientAwayEquiv_mk
#print axioms localizedReductionEquiv_mk

end CycleQ2FirstOrderLocalizedReduction

end
