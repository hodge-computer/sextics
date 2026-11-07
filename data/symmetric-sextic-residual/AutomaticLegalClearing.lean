import Proposal.CurrentVerifierBridge
import HodgeComputer.Constructions.HoldoutCover.HomogeneousCertificate
import Mathlib.RingTheory.Localization.Integer
import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

/-!
# Automatic legal denominator clearing

A current regular along the hypersurface is supplied as a vector in the
localization at nonzero polynomials relatively prime to its equation. The
localization, rather than a preselected polynomial denominator, expresses
regularity. The finite-family localization theorem supplies a common legal
denominator for the vector and its regular divergence remainder.

The normalized current identities imply polynomial normalized data. The
existing finite homogeneous-normalization theorem then proves the unchanged
`HasCertificate` proposition. No denominator, polynomial numerators, cleared
quotient, or clearing equality are inputs to the endpoint.

Existence of the current and its identities remains a substantive hypothesis.
No geometric support theorem or certificate for the protected target is asserted.
-/

noncomputable section

namespace AutomaticLegalClearing

open HodgeComputer HodgeTestbed HodgeTestbed.Conic CurrentVerifierBridge
open scoped BigOperators

variable {K : Type*} [Field K] [CharZero K] [Algebra ℚ K]

/-- Precisely the nonzero polynomial denominators allowed by the verifier. -/
def legalDenominators {n : ℕ} (F : AmbientPoly n) : Submonoid (AmbientPoly n) where
  carrier := {D | D ≠ 0 ∧ IsRelPrime F D}
  one_mem' := ⟨one_ne_zero, isRelPrime_one_right⟩
  mul_mem' := fun ha hb => ⟨mul_ne_zero ha.1 hb.1, ha.2.mul_right hb.2⟩

/-- Rational functions whose denominators have no common factor with `F`. -/
abbrev RegularRing {n : ℕ} (F : AmbientPoly n) := Localization (legalDenominators F)

/-- The canonical interpretation of a regular fraction in compatible coordinates. -/
def regularMap {n : ℕ} (c : PolynomialCoordinates n K) (F : AmbientPoly n) :
    RegularRing F →+* K :=
  IsLocalization.lift (M := legalDenominators F) (S := RegularRing F)
    (g := c.embed) (fun D => by
    apply isUnit_iff_ne_zero.mpr
    intro h
    exact D.property.1 (c.injective (by simpa using h)))

@[simp] theorem regularMap_polynomial {n : ℕ} (c : PolynomialCoordinates n K)
    (F P : AmbientPoly n) :
    regularMap c F (algebraMap (AmbientPoly n) (RegularRing F) P) = c.embed P := by
  simp [regularMap]

/-- A finite regular family automatically has one legal polynomial denominator. -/
theorem common_legal_representatives {n : ℕ} {ι : Type*} [Finite ι]
    (c : PolynomialCoordinates n K) (F : AmbientPoly n) (w : ι → RegularRing F) :
    ∃ D : AmbientPoly n, ∃ N : ι → AmbientPoly n,
      D ≠ 0 ∧ IsRelPrime F D ∧
        ∀ i, c.embed (N i) = c.embed D * regularMap c F (w i) := by
  obtain ⟨D, hD⟩ := IsLocalization.exist_integer_multiples_of_finite
    (legalDenominators F) w
  choose N hN using hD
  refine ⟨D, N, D.property.1, D.property.2, ?_⟩
  intro i
  have h := congrArg (regularMap c F) (hN i)
  simpa only [Algebra.smul_def, map_mul, regularMap_polynomial] using h

/-- Clear a normalized regular current and its regular divergence remainder.
All polynomial witnesses are conclusions, including the ordinary quotient. -/
theorem normalized_data_of_regular_current
    (c : PolynomialCoordinates 5 K) (F A : AmbientPoly 5)
    (v : Fin 6 → RegularRing F) (r : RegularRing F)
    (hnormal : fieldAction c.derivative (fun i => regularMap c F (v i)) (c.embed F) =
      c.embed A)
    (hdiv : fieldDivergence c.derivative (fun i => regularMap c F (v i)) =
      c.embed F * regularMap c F r) :
    ∃ D : AmbientPoly 5, ∃ N : Fin 6 → AmbientPoly 5, ∃ Q : AmbientPoly 5,
      D ≠ 0 ∧ IsRelPrime F D ∧ directional F N = A * D ∧
        divergenceNumerator D N = F * Q := by
  let w : Option (Fin 6) → RegularRing F := fun i => Option.elim i r v
  obtain ⟨D, W, hD, hlegal, hW⟩ := common_legal_representatives c F w
  let N : Fin 6 → AmbientPoly 5 := fun i => W (some i)
  let Q : AmbientPoly 5 := D * W none
  have hd : c.embed D ≠ 0 := fun h => hD (c.injective (by simpa using h))
  have hclear : quotientField c N D = fun i => regularMap c F (v i) := by
    funext i
    apply (div_eq_iff hd).mpr
    simpa only [N, w, Option.elim_some, mul_comm] using hW (some i)
  have hQ : c.embed Q = c.embed D ^ 2 * regularMap c F r := by
    change c.embed (D * W none) = _
    rw [map_mul, hW none]
    simp only [w, Option.elim_none]
    ring
  have hfirst : directional F N = A * D := by
    apply c.injective
    rw [map_mul]
    apply (div_eq_iff hd).mp
    rw [← quotient_action, hclear]
    exact hnormal
  have hsecond : divergenceNumerator D N = F * Q := by
    apply c.injective
    have h := quotient_divergence c D N
    rw [hclear, hdiv] at h
    have h' := (div_eq_iff (pow_ne_zero 2 hd)).mp h.symm
    rw [map_mul, hQ]
    linear_combination h'
  exact ⟨D, N, Q, hD, hlegal, hfirst, hsecond⟩

/-- A nonzero homogeneous sextic has a legal normal coordinate. -/
theorem exists_normal_chart (F : AmbientPoly 5) (hF0 : F ≠ 0)
    (hF : F.IsHomogeneous 6) : ∃ i : Fin 6, ¬ F ∣ MvPolynomial.pderiv i F := by
  classical
  by_contra! h
  have hp (i : Fin 6) : MvPolynomial.pderiv i F = 0 := by
    by_contra hn
    have hle := MvPolynomial.totalDegree_le_of_dvd_of_isDomain (h i) hn
    rw [hF.totalDegree hF0,
      (HoldoutConstruction.pderiv_isHomogeneous hF i).totalDegree hn] at hle
    norm_num at hle
  have he := hF.sum_X_mul_pderiv
  simp only [hp, mul_zero, Finset.sum_const_zero] at he
  have hz : (6 : AmbientPoly 5) * F = 0 := by
    simpa only [nsmul_eq_mul, Nat.cast_ofNat] using he.symm
  exact hF0 ((mul_eq_zero.mp hz).resolve_left (by norm_num))

/-- A regular normalized current supplies a homogeneous certificate
nonconstructively, with no polynomial witness or clearing hypothesis. -/
theorem hasCertificate_of_regular_current_on_chart
    (c : PolynomialCoordinates 5 K) (F A : AmbientPoly 5)
    (hF : F.IsHomogeneous 6) (hA : A.IsHomogeneous 6) (hprime : Prime F)
    (i : Fin 6) (hchart : ¬ F ∣ MvPolynomial.pderiv i F)
    (v : Fin 6 → RegularRing F) (r : RegularRing F)
    (hnormal : fieldAction c.derivative (fun j => regularMap c F (v j)) (c.embed F) =
      c.embed A)
    (hdiv : fieldDivergence c.derivative (fun j => regularMap c F (v j)) =
      c.embed F * regularMap c F r) :
    HasCertificate F 1 A := by
  obtain ⟨D, N, Q, _, hlegal, hnormal', hdiv'⟩ :=
    normalized_data_of_regular_current c F A v r hnormal hdiv
  exact HoldoutConstruction.hasCertificate_of_normalized F A D N Q hF hA hprime
    hlegal hnormal' hdiv' i hchart

/-- The normal chart is also obtained automatically from the sextic degree. -/
theorem hasCertificate_of_regular_current
    (c : PolynomialCoordinates 5 K) (F A : AmbientPoly 5)
    (hF : F.IsHomogeneous 6) (hA : A.IsHomogeneous 6) (hprime : Prime F)
    (v : Fin 6 → RegularRing F) (r : RegularRing F)
    (hnormal : fieldAction c.derivative (fun j => regularMap c F (v j)) (c.embed F) =
      c.embed A)
    (hdiv : fieldDivergence c.derivative (fun j => regularMap c F (v j)) =
      c.embed F * regularMap c F r) :
    HasCertificate F 1 A := by
  obtain ⟨i, hchart⟩ := exists_normal_chart F hprime.ne_zero hF
  exact hasCertificate_of_regular_current_on_chart c F A hF hA hprime i hchart
    v r hnormal hdiv

/-- The zero-divergence case also needs no chosen polynomial witnesses. -/
theorem hasCertificate_of_regular_strict_current
    (c : PolynomialCoordinates 5 K) (F A : AmbientPoly 5)
    (hF : F.IsHomogeneous 6) (hA : A.IsHomogeneous 6) (hprime : Prime F)
    (v : Fin 6 → RegularRing F)
    (hnormal : fieldAction c.derivative (fun j => regularMap c F (v j)) (c.embed F) =
      c.embed A)
    (hdiv : fieldDivergence c.derivative (fun j => regularMap c F (v j)) = 0) :
    HasCertificate F 1 A := by
  apply hasCertificate_of_regular_current c F A hF hA hprime v 0 hnormal
  simpa using hdiv

#print axioms common_legal_representatives
#print axioms normalized_data_of_regular_current
#print axioms exists_normal_chart
#print axioms hasCertificate_of_regular_current
#print axioms hasCertificate_of_regular_strict_current

end AutomaticLegalClearing
