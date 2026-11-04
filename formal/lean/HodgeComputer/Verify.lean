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
abbrev AmbientPoly (n : ℕ) := MvPolynomial (Fin (n + 1)) ℂ

/-- Exact cleared defect, with the pole parameter retained. -/
def defect {n : ℕ} (F A D : AmbientPoly n) (q : ℕ)
    (N : Fin (n + 1) → AmbientPoly n) : AmbientPoly n :=
  A * D^2 - (q : AmbientPoly n) * D * HodgeTestbed.directional F N +
    F * HodgeTestbed.divergenceNumerator D N

/-- Homogeneity with an integer degree. Negative degrees permit only zero. -/
def Homogeneous {σ : Type*} (P : MvPolynomial σ ℂ) (k : ℤ) : Prop :=
  ∀ ⦃m : σ →₀ ℕ⦄, coeff m P ≠ 0 → (m.degree : ℤ) = k

theorem Homogeneous.of_isHomogeneous {σ : Type*} {P : MvPolynomial σ ℂ} {k : ℕ}
    (h : P.IsHomogeneous k) : Homogeneous P (k : ℤ) := by
  intro m hm
  exact_mod_cast (show m.degree = k by
    simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using h hm)

theorem Homogeneous.isHomogeneous {σ : Type*} {P : MvPolynomial σ ℂ} {k : ℤ}
    (h : Homogeneous P k) (hk : 0 ≤ k) : P.IsHomogeneous k.toNat := by
  intro m hm
  have hd := h hm
  have he : m.degree = k.toNat := by omega
  simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using he

theorem Homogeneous.eq_zero_of_neg {σ : Type*} {P : MvPolynomial σ ℂ} {k : ℤ}
    (h : Homogeneous P k) (hk : k < 0) : P = 0 := by
  ext m
  rw [coeff_zero]
  by_contra hm
  have hd := h hm
  omega

theorem homogeneous_zero {σ : Type*} (k : ℤ) : Homogeneous (0 : MvPolynomial σ ℂ) k := by
  intro m hm
  exact False.elim (hm (coeff_zero m))

theorem Homogeneous.add {σ : Type*} {P Q : MvPolynomial σ ℂ} {k : ℤ}
    (hP : Homogeneous P k) (hQ : Homogeneous Q k) : Homogeneous (P + Q) k := by
  by_cases hk : 0 ≤ k
  · have h := Homogeneous.of_isHomogeneous ((hP.isHomogeneous hk).add (hQ.isHomogeneous hk))
    simpa only [Int.toNat_of_nonneg hk] using h
  · rw [hP.eq_zero_of_neg (by omega), hQ.eq_zero_of_neg (by omega), zero_add]
    exact homogeneous_zero k

theorem Homogeneous.mul {σ : Type*} {P Q : MvPolynomial σ ℂ} {k l : ℤ}
    (hP : Homogeneous P k) (hQ : Homogeneous Q l) : Homogeneous (P * Q) (k + l) := by
  by_cases hk : 0 ≤ k
  · by_cases hl : 0 ≤ l
    · have h := Homogeneous.of_isHomogeneous ((hP.isHomogeneous hk).mul (hQ.isHomogeneous hl))
      simpa only [Nat.cast_add, Int.toNat_of_nonneg hk, Int.toNat_of_nonneg hl] using h
    · rw [hQ.eq_zero_of_neg (by omega), mul_zero]
      exact homogeneous_zero _
  · rw [hP.eq_zero_of_neg (by omega), zero_mul]
    exact homogeneous_zero _

theorem Homogeneous.C_mul {σ : Type*} {P : MvPolynomial σ ℂ} {k : ℤ}
    (h : Homogeneous P k) (c : ℂ) : Homogeneous (C c * P) k := by
  simpa using (Homogeneous.of_isHomogeneous (isHomogeneous_C (σ := σ) c)).mul h

theorem Homogeneous.rename {σ τ : Type*} {P : MvPolynomial σ ℂ} {k : ℤ}
    (h : Homogeneous P k) (f : σ → τ) : Homogeneous (MvPolynomial.rename f P) k := by
  by_cases hk : 0 ≤ k
  · simpa only [Int.toNat_of_nonneg hk] using
      Homogeneous.of_isHomogeneous ((h.isHomogeneous hk).rename_isHomogeneous (f := f))
  · rw [h.eq_zero_of_neg (by omega), map_zero]
    exact homogeneous_zero _

/-- A rational-vector-field certificate in projective dimension `n`, for a
nonzero degree-`d` hypersurface and pole parameter `q`. All subtractions in
homogeneity degrees are in the integers. The denominator degree is unrestricted. -/
structure Verify {n : ℕ} (F A : AmbientPoly n) (d q : ℕ) (D : AmbientPoly n)
    (N : Fin (n + 1) → AmbientPoly n) (Q : AmbientPoly n) : Prop where
  hypersurface_ne_zero : F ≠ 0
  hypersurface_homogeneous : F.IsHomogeneous d
  source_homogeneous : Homogeneous A ((d : ℤ) * (q + 1) - (n + 1))
  denominator_ne_zero : D ≠ 0
  denominator_homogeneous : D.IsHomogeneous D.totalDegree
  numerator_homogeneous : ∀ i, Homogeneous (N i) ((D.totalDegree : ℤ) + d*q - n)
  denominator_legal : IsRelPrime F D
  identity : defect F A D q N = F^(q+1) * Q

def HasCertificate {n : ℕ} (F A : AmbientPoly n) (d q : ℕ) : Prop :=
  ∃ D N Q, Verify F A d q D N Q

/-- Normalization is a sufficient way of supplying the general cleared identity. -/
theorem normalized_identity {n : ℕ} {F A D Q : AmbientPoly n} {q : ℕ}
    {N : Fin (n + 1) → AmbientPoly n}
    (h1 : (q : AmbientPoly n) * HodgeTestbed.directional F N = A * D)
    (h2 : HodgeTestbed.divergenceNumerator D N = F^q * Q) :
    defect F A D q N = F^(q+1) * Q := by
  unfold defect
  rw [show (q : AmbientPoly n) * D * HodgeTestbed.directional F N = D * (A*D) by rw [← h1]; ring, h2]
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
theorem localization_identity {n : ℕ} {S : Type*} [CommRing S] (f : AmbientPoly n →+* S)
    {F A D Q : AmbientPoly n} {d q : ℕ} {N : Fin (n + 1) → AmbientPoly n}
    (h : Verify F A d q D N Q) (u : S) (hu : f D * u = 1) :
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
