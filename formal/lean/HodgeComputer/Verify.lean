import HodgeTestbed.Algebra
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Analysis.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.Tactic

noncomputable section
namespace HodgeComputer
open MvPolynomial
abbrev Poly := MvPolynomial (Fin 6) ℂ
abbrev Coeff := MvPolynomial (Fin 5) ℂ

/-- Exact cleared defect, with the pole parameter retained. -/
def defect (F A D : Poly) (q : ℕ) (N : Fin 6 → Poly) : Poly :=
  A * D^2 - (q : Poly) * D * HodgeTestbed.directional F N +
    F * HodgeTestbed.divergenceNumerator D N

/-- Finite sufficient witness for the full existential challenge, including non-strict fields.
There is no degree bound, positivity, normalization, or field-parity restriction. -/
structure Verify (F A : Poly) (q d : ℕ) (D : Poly) (N : Fin 6 → Poly) (Q : Poly) : Prop where
  denominator_ne_zero : D ≠ 0
  denominator_homogeneous : D.IsHomogeneous d
  numerator_homogeneous : ∀ i, (N i).IsHomogeneous (d + 6*q - 5)
  denominator_legal : IsRelPrime F D
  identity : defect F A D q N = F^(q+1) * Q

def HasCertificate (F A : Poly) (q : ℕ) : Prop :=
  ∃ d D N Q, Verify F A q d D N Q

/-- Normalization is a sufficient way of supplying the general cleared identity. -/
theorem normalized_identity {F A D Q : Poly} {q : ℕ} {N : Fin 6 → Poly}
    (h1 : (q : Poly) * HodgeTestbed.directional F N = A * D)
    (h2 : HodgeTestbed.divergenceNumerator D N = F^q * Q) :
    defect F A D q N = F^(q+1) * Q := by
  unfold defect
  rw [show (q : Poly) * D * HodgeTestbed.directional F N = D * (A*D) by rw [← h1]; ring, h2]
  ring

/-- Coprimality ascends from a univariate specialization when F has unit leading coefficient.
Unlike a multivariate Bezout condition, this does not require the two hypersurfaces to be disjoint. -/
theorem relPrime_of_specialization {R S : Type*} [CommRing R] [IsDomain R]
    [CommRing S] [IsDomain S] (φ : R →+* S) (f g : Polynomial R)
    (hf : IsUnit f.leadingCoeff) (h : IsRelPrime (f.map φ) (g.map φ)) : IsRelPrime f g := by
  intro a ha hb
  have hu : IsUnit a.leadingCoeff := by
    obtain ⟨b, rfl⟩ := ha
    rw [Polynomial.leadingCoeff_mul] at hf
    exact isUnit_of_mul_isUnit_left hf
  exact Polynomial.isUnit_of_isUnit_leadingCoeff_of_isUnit_map φ hu
    (h (map_dvd (Polynomial.mapRingHom φ) ha) (map_dvd (Polynomial.mapRingHom φ) hb))

/-- Transfer along a polynomial coordinate map equipped with a left inverse. -/
theorem relPrime_of_retract {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (g : S →+* R) (hg : g.comp f = RingHom.id R) {a b : R}
    (h : IsRelPrime (f a) (f b)) : IsRelPrime a b := by
  intro p hp hq
  have hu := (h (map_dvd f hp) (map_dvd f hq)).map g
  simpa only [← RingHom.comp_apply, hg, RingHom.id_apply] using hu

/-- Clearing D² is valid in any localization in which D is a unit. -/
theorem localization_identity {S : Type*} [CommRing S] (f : Poly →+* S)
    {F A D Q : Poly} {q d : ℕ} {N : Fin 6 → Poly}
    (h : Verify F A q d D N Q) (u : S) (hu : f D * u = 1) :
    f A - (q : S) * f (HodgeTestbed.directional F N) * u +
      f F * f (HodgeTestbed.divergenceNumerator D N) * u^2 =
      (f F)^(q+1) * (f Q * u^2) := by
  have hi := congrArg (fun p => f p * u^2) h.identity
  simp only [defect, map_add, map_sub, map_mul, map_pow, map_natCast] at hi
  have hleft : (f A * f D^2 - (q:S) * f D * f (HodgeTestbed.directional F N) +
      f F * f (HodgeTestbed.divergenceNumerator D N)) * u^2 =
      f A - (q:S) * f (HodgeTestbed.directional F N) * u +
      f F * f (HodgeTestbed.divergenceNumerator D N) * u^2 := by
    calc
      _ = f A * (f D*u)^2 - (q:S) * f (HodgeTestbed.directional F N) * u * (f D*u) +
          f F * f (HodgeTestbed.divergenceNumerator D N) * u^2 := by ring
      _ = _ := by rw [hu]; ring
  rw [hleft] at hi
  exact hi.trans (by ring)
end HodgeComputer
