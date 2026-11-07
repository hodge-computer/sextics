import AutomaticLegalClearing
import HodgeComputer.Constructions.RationalFields.EulerCorrection

/-!
# A regular homogeneous rational game implies the actual certificate

The regular current and its regular remainder are elements of a localization,
not polynomial witnesses. Euler correction derives normalized field identities;
automatic clearing and homogeneous normalization then give `HasCertificate`.
The only current equation assumed is the ordinary rational game identity.
Existence of such a current is not asserted for any particular hypersurface.
-/

noncomputable section

namespace RegularEulerClearing

open HodgeComputer HodgeTestbed HodgeTestbed.Conic CurrentVerifierBridge
open AutomaticLegalClearing MvPolynomial
open scoped BigOperators

variable {K : Type*} [Field K] [CharZero K] [Algebra ℚ K]

theorem regularMap_fraction (c : PolynomialCoordinates 5 K) (F P : AmbientPoly 5)
    (D : legalDenominators F) :
    regularMap c F (IsLocalization.mk' (RegularRing F) P D) =
      c.embed P / c.embed (D : AmbientPoly 5) := by
  have hd : c.embed (D : AmbientPoly 5) ≠ 0 :=
    fun h => D.property.1 (c.injective (by simpa using h))
  apply (eq_div_iff hd).mpr
  have h := congrArg (regularMap c F)
    (IsLocalization.mk'_spec (S := RegularRing F) P D)
  simpa only [map_mul, regularMap_polynomial] using h

/-- Differentiation introduces only powers of already legal denominators. -/
theorem divergence_is_regular (c : PolynomialCoordinates 5 K) (F : AmbientPoly 5)
    (v : Fin 6 → RegularRing F) :
    ∃ b : RegularRing F, regularMap c F b =
      fieldDivergence c.derivative (fun i => regularMap c F (v i)) := by
  obtain ⟨D, N, hD, hlegal, hN⟩ := common_legal_representatives c F v
  have hd : c.embed D ≠ 0 := fun h => hD (c.injective (by simpa using h))
  have hclear : quotientField c N D = fun i => regularMap c F (v i) := by
    funext i
    apply (div_eq_iff hd).mpr
    simpa only [mul_comm] using hN i
  let d : legalDenominators F := ⟨D, hD, hlegal⟩
  refine ⟨IsLocalization.mk' (RegularRing F) (divergenceNumerator D N) (d^2), ?_⟩
  rw [regularMap_fraction]
  change c.embed (divergenceNumerator D N) / c.embed (D^2) = _
  rw [map_pow, ← quotient_divergence, hclear]

def regularSixth (F : AmbientPoly 5) : RegularRing F :=
  algebraMap (AmbientPoly 5) (RegularRing F) (C (1/6 : ℂ))

@[simp] theorem regularMap_sixth (c : PolynomialCoordinates 5 K) (F : AmbientPoly 5) :
    regularMap c F (regularSixth F) = (1/6 : K) := by
  rw [regularSixth, regularMap_polynomial]
  change (c.embed.comp C) (1/6 : ℂ) = _
  simp only [map_div₀, map_one, map_ofNat]

def coordinateEuler (c : PolynomialCoordinates 5 K) : Fin 6 → K :=
  fun i => c.embed (X i)

theorem action_coordinate (c : PolynomialCoordinates 5 K) (v : Fin 6 → K)
    (i : Fin 6) : fieldAction c.derivative v (c.embed (X i)) = v i := by
  simp [fieldAction_apply, c.compatible, MvPolynomial.pderiv_X, Pi.single_apply,
    apply_ite]

theorem euler_action_sextic (c : PolynomialCoordinates 5 K) (P : AmbientPoly 5)
    (hP : P.IsHomogeneous 6) :
    fieldAction c.derivative (coordinateEuler c) (c.embed P) = 6*c.embed P := by
  have h := congrArg c.embed hP.sum_X_mul_pderiv
  simpa only [fieldAction_apply, coordinateEuler, c.compatible, map_sum, map_mul,
    map_nsmul, nsmul_eq_mul, Nat.cast_ofNat, map_ofNat] using h

theorem coordinateEuler_divergence (c : PolynomialCoordinates 5 K) :
    fieldDivergence c.derivative (coordinateEuler c) = 6 := by
  simp [fieldDivergence, coordinateEuler, c.compatible]

/-- The ordinary game has an exact Euler correction, retaining its remainder. -/
theorem eulerCorrection_normalized (δ : Fin 6 → Derivation ℚ K K)
    (F A r : K) (E v : Fin 6 → K)
    (hF : fieldAction δ E F = 6*F) (hE : fieldDivergence δ E = 6)
    (hdegree : fieldAction δ E (fieldDivergence δ v - F*r) = 0)
    (hgame : A - fieldAction δ v F + F*fieldDivergence δ v = F^2*r) :
    fieldAction δ (fun i => v i - ((fieldDivergence δ v-F*r)/6)*E i) F = A ∧
      fieldDivergence δ (fun i => v i - ((fieldDivergence δ v-F*r)/6)*E i) = F*r := by
  constructor
  · rw [fieldAction_sub, fieldAction_scale, hF]
    linear_combination -hgame
  · rw [fieldDivergence_sub, fieldDivergence_scale, derivation_sixth, hdegree, hE]
    ring

/-- Euler weight one of the current supplies the correction's degree-zero
condition; the remainder's degree is not separately assumed. -/
theorem correction_degree_zero
    (c : PolynomialCoordinates 5 K) (F A : AmbientPoly 5)
    (hF0 : F ≠ 0) (hF : F.IsHomogeneous 6) (hA : A.IsHomogeneous 6)
    (v : Fin 6 → K) (r : K)
    (hcomm : ∀ i j, Function.Commute (c.derivative i) (c.derivative j))
    (hweight : ∀ i, fieldAction c.derivative (coordinateEuler c) (v i) = v i)
    (hgame : c.embed A - fieldAction c.derivative v (c.embed F) +
      c.embed F*fieldDivergence c.derivative v = c.embed F^2*r) :
    fieldAction c.derivative (coordinateEuler c)
      (fieldDivergence c.derivative v - c.embed F*r) = 0 := by
  have hf : c.embed F ≠ 0 := fun h => hF0 (c.injective (by simpa using h))
  have hEF := euler_action_sextic c F hF
  have hEA := euler_action_sextic c A hA
  have hb : fieldBracket c.derivative (coordinateEuler c) v = fun _ => 0 := by
    funext i
    simp only [fieldBracket, hweight, coordinateEuler, action_coordinate, sub_self]
  have hvF : fieldAction c.derivative (coordinateEuler c)
      (fieldAction c.derivative v (c.embed F)) =
        6*fieldAction c.derivative v (c.embed F) := by
    have h := fieldAction_bracket c.derivative hcomm (coordinateEuler c) v (c.embed F)
    have hz : fieldAction c.derivative (fun _ : Fin 6 => 0) (c.embed F) = 0 := by
      simp only [fieldAction_apply, zero_mul, Finset.sum_const_zero]
    have h6 : fieldAction c.derivative v (6 : K) = 0 :=
      (fieldAction c.derivative v).map_natCast 6
    rw [hb, hz, hEF, Derivation.leibniz, h6] at h
    simp only [mul_zero, add_zero, smul_eq_mul] at h
    linear_combination -h
  have he := congrArg (fieldAction c.derivative (coordinateEuler c)) hgame
  simp only [map_add, map_sub, Derivation.leibniz, Derivation.leibniz_pow,
    hEA, hEF, hvF, nsmul_eq_mul, smul_eq_mul, Nat.cast_ofNat, Nat.reduceSub,
    pow_one] at he
  apply mul_left_cancel₀ hf
  rw [mul_zero]
  simp only [map_sub, Derivation.leibniz, hEF, smul_eq_mul]
  linear_combination he - 6*hgame

/-- A regular homogeneous rational current satisfying the ordinary game gives
the original certificate proposition. No polynomial witnesses are inputs. -/
theorem hasCertificate_of_regular_homogeneous_game
    (c : PolynomialCoordinates 5 K) (F A : AmbientPoly 5)
    (hF : F.IsHomogeneous 6) (hA : A.IsHomogeneous 6) (hprime : Prime F)
    (v : Fin 6 → RegularRing F) (r : RegularRing F)
    (hcomm : ∀ i j, Function.Commute (c.derivative i) (c.derivative j))
    (hweight : ∀ i, fieldAction c.derivative (coordinateEuler c)
      (regularMap c F (v i)) = regularMap c F (v i))
    (hgame : c.embed A -
        fieldAction c.derivative (fun i => regularMap c F (v i)) (c.embed F) +
        c.embed F*fieldDivergence c.derivative (fun i => regularMap c F (v i)) =
      c.embed F^2*regularMap c F r) :
    HasCertificate F 1 A := by
  obtain ⟨b, hb⟩ := divergence_is_regular c F v
  let v' : Fin 6 → RegularRing F := fun i =>
    v i - ((b-algebraMap (AmbientPoly 5) (RegularRing F) F*r)*regularSixth F)*
      algebraMap (AmbientPoly 5) (RegularRing F) (X i)
  have hclear : (fun i => regularMap c F (v' i)) =
      fun i => regularMap c F (v i) -
        ((fieldDivergence c.derivative (fun j => regularMap c F (v j)) -
          c.embed F*regularMap c F r)/6)*coordinateEuler c i := by
    funext i
    simp only [v', map_sub, map_mul, regularMap_polynomial, regularMap_sixth, hb,
      coordinateEuler]
    ring
  have hdegree := correction_degree_zero c F A hprime.ne_zero hF hA
    (fun i => regularMap c F (v i)) (regularMap c F r) hcomm hweight hgame
  have hnormalized := eulerCorrection_normalized c.derivative (c.embed F) (c.embed A)
    (regularMap c F r) (coordinateEuler c) (fun i => regularMap c F (v i))
    (euler_action_sextic c F hF) (coordinateEuler_divergence c) hdegree hgame
  apply hasCertificate_of_regular_current c F A hF hA hprime v' r
  · rw [hclear]
    exact hnormalized.1
  · rw [hclear]
    exact hnormalized.2

/-- An existence proof for the regular homogeneous game is enough; it need not
compute the current, denominator, or polynomial numerators. -/
theorem hasCertificate_of_exists_regular_homogeneous_game
    (c : PolynomialCoordinates 5 K) (F A : AmbientPoly 5)
    (hF : F.IsHomogeneous 6) (hA : A.IsHomogeneous 6) (hprime : Prime F)
    (hcomm : ∀ i j, Function.Commute (c.derivative i) (c.derivative j))
    (hexists : ∃ (v : Fin 6 → RegularRing F) (r : RegularRing F),
      (∀ i, fieldAction c.derivative (coordinateEuler c)
        (regularMap c F (v i)) = regularMap c F (v i)) ∧
      c.embed A -
          fieldAction c.derivative (fun i => regularMap c F (v i)) (c.embed F) +
          c.embed F*fieldDivergence c.derivative (fun i => regularMap c F (v i)) =
        c.embed F^2*regularMap c F r) :
    HasCertificate F 1 A := by
  obtain ⟨v, r, hweight, hgame⟩ := hexists
  exact hasCertificate_of_regular_homogeneous_game c F A hF hA hprime v r
    hcomm hweight hgame

#print axioms divergence_is_regular
#print axioms correction_degree_zero
#print axioms hasCertificate_of_regular_homogeneous_game
#print axioms hasCertificate_of_exists_regular_homogeneous_game

end RegularEulerClearing
