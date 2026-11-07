import RegularEulerClearing

/-!
# Every accepted sextic certificate gives a regular homogeneous current

The current and the ordinary remainder are constructed directly from a
`Verify` record, as the fractions `Nᵢ/D` and `Q/D²` in the localization at
legal denominators. The raw rational game follows from the verifier's
cleared identity. Euler weight one follows from its prescribed homogeneous
numerator and denominator degrees, including zero numerator components.

Together with `RegularEulerClearing`, this is the reverse implication needed
to state an equivalence with the unchanged certificate proposition. No
existence of either a certificate or a current for the protected target is
asserted in this file.
-/

noncomputable section

namespace CertificateRegularCurrent

open HodgeComputer HodgeTestbed HodgeTestbed.Conic CurrentVerifierBridge
open AutomaticLegalClearing RegularEulerClearing MvPolynomial
open scoped BigOperators

variable {K : Type*} [Field K] [CharZero K] [Algebra ℚ K]

/-- The verifier's own denominator belongs to the regular localization. -/
def certificateDenominator {F A D Q : AmbientPoly 5} {N : Fin 6 → AmbientPoly 5}
    (h : Verify F A 6 1 D N Q) : legalDenominators F :=
  ⟨D, h.denominator_ne_zero, h.denominator_legal⟩

/-- The actual rational vector field represented by a certificate. -/
def certificateCurrent {F A D Q : AmbientPoly 5} {N : Fin 6 → AmbientPoly 5}
    (h : Verify F A 6 1 D N Q) : Fin 6 → RegularRing F :=
  fun i => IsLocalization.mk' (RegularRing F) (N i) (certificateDenominator h)

/-- The ordinary verifier permits a remainder, represented by `Q/D²`. -/
def certificateRemainder {F A D Q : AmbientPoly 5} {N : Fin 6 → AmbientPoly 5}
    (h : Verify F A 6 1 D N Q) : RegularRing F :=
  IsLocalization.mk' (RegularRing F) Q (certificateDenominator h ^ 2)

@[simp] theorem certificateCurrent_map (c : PolynomialCoordinates 5 K)
    {F A D Q : AmbientPoly 5} {N : Fin 6 → AmbientPoly 5}
    (h : Verify F A 6 1 D N Q) (i : Fin 6) :
    regularMap c F (certificateCurrent h i) = c.embed (N i) / c.embed D := by
  exact regularMap_fraction c F (N i) (certificateDenominator h)

@[simp] theorem certificateRemainder_map (c : PolynomialCoordinates 5 K)
    {F A D Q : AmbientPoly 5} {N : Fin 6 → AmbientPoly 5}
    (h : Verify F A 6 1 D N Q) :
    regularMap c F (certificateRemainder h) = c.embed Q / c.embed D ^ 2 := by
  rw [certificateRemainder, regularMap_fraction]
  change c.embed Q / c.embed (D ^ 2) = _
  rw [map_pow]

/-- Euler's formula in any compatible coordinate field, for any degree. -/
theorem euler_action_homogeneous (c : PolynomialCoordinates 5 K)
    (P : AmbientPoly 5) {k : ℕ} (hP : P.IsHomogeneous k) :
    fieldAction c.derivative (coordinateEuler c) (c.embed P) = (k : K) * c.embed P := by
  have h := congrArg c.embed hP.sum_X_mul_pderiv
  simpa only [fieldAction_apply, coordinateEuler, c.compatible, map_sum, map_mul,
    map_nsmul, nsmul_eq_mul, map_natCast] using h

/-- A quotient whose numerator degree exceeds the denominator degree by one
has Euler weight one. The numerator is allowed to vanish. -/
theorem homogeneous_quotient_euler_weight_one (c : PolynomialCoordinates 5 K)
    (P D : AmbientPoly 5) (e : ℕ) (hD : D ≠ 0)
    (hP : P.IsHomogeneous (e+1)) (hDe : D.IsHomogeneous e) :
    fieldAction c.derivative (coordinateEuler c) (c.embed P / c.embed D) =
      c.embed P / c.embed D := by
  have hd : c.embed D ≠ 0 := fun h => hD (c.injective (by simpa using h))
  rw [Derivation.leibniz_div, euler_action_homogeneous c P hP,
    euler_action_homogeneous c D hDe]
  simp only [Nat.cast_add, Nat.cast_one, smul_eq_mul]
  field_simp [hd]
  ring

/-- The verifier's integer-degree requirement yields precisely weight one
for each component of the constructed regular current. -/
theorem certificateCurrent_euler_weight_one (c : PolynomialCoordinates 5 K)
    {F A D Q : AmbientPoly 5} {N : Fin 6 → AmbientPoly 5}
    (h : Verify F A 6 1 D N Q) (i : Fin 6) :
    fieldAction c.derivative (coordinateEuler c)
      (regularMap c F (certificateCurrent h i)) =
        regularMap c F (certificateCurrent h i) := by
  rw [certificateCurrent_map]
  have hn : Homogeneous (N i) ((D.totalDegree + 1 : ℕ) : ℤ) := by
    convert h.numerator_homogeneous i using 1
    push_cast
    ring
  have hNi : (N i).IsHomogeneous (D.totalDegree + 1) := by
    simpa using hn.isHomogeneous (by positivity)
  exact homogeneous_quotient_euler_weight_one c (N i) D D.totalDegree
    h.denominator_ne_zero hNi h.denominator_homogeneous

/-- Clearing the verifier's exact identity gives its ordinary rational game,
with the constructed regular remainder and no extra restriction on `Q`. -/
theorem certificateCurrent_game (c : PolynomialCoordinates 5 K)
    {F A D Q : AmbientPoly 5} {N : Fin 6 → AmbientPoly 5}
    (h : Verify F A 6 1 D N Q) :
    c.embed A -
        fieldAction c.derivative (fun i => regularMap c F (certificateCurrent h i))
          (c.embed F) +
        c.embed F * fieldDivergence c.derivative
          (fun i => regularMap c F (certificateCurrent h i)) =
      c.embed F ^ 2 * regularMap c F (certificateRemainder h) := by
  have hd : c.embed D ≠ 0 :=
    fun hz => h.denominator_ne_zero (c.injective (by simpa using hz))
  have hv : (fun i => regularMap c F (certificateCurrent h i)) = quotientField c N D := by
    funext i
    exact certificateCurrent_map c h i
  rw [hv, certificateRemainder_map]
  have hi := congrArg c.embed h.identity
  rw [defect_clearing c F A D 1 N h.denominator_ne_zero] at hi
  simp only [Nat.cast_one, one_mul, Nat.reduceAdd, map_mul, map_pow] at hi
  rw [← mul_div_assoc]
  apply (eq_div_iff (pow_ne_zero 2 hd)).mpr
  linear_combination hi

/-- Every verified sextic witness supplies the exact current-existence
statement used by the forward Euler-normalization theorem. -/
theorem exists_regular_homogeneous_game_of_verify (c : PolynomialCoordinates 5 K)
    {F A D Q : AmbientPoly 5} {N : Fin 6 → AmbientPoly 5}
    (h : Verify F A 6 1 D N Q) :
    ∃ (v : Fin 6 → RegularRing F) (r : RegularRing F),
      (∀ i, fieldAction c.derivative (coordinateEuler c)
        (regularMap c F (v i)) = regularMap c F (v i)) ∧
      c.embed A -
          fieldAction c.derivative (fun i => regularMap c F (v i)) (c.embed F) +
          c.embed F * fieldDivergence c.derivative (fun i => regularMap c F (v i)) =
        c.embed F ^ 2 * regularMap c F r :=
  ⟨certificateCurrent h, certificateRemainder h,
    certificateCurrent_euler_weight_one c h, certificateCurrent_game c h⟩

/-- The reverse direction for the unchanged existential verifier proposition.
Only sextic homogeneity is required to identify its degree parameter. -/
theorem exists_regular_homogeneous_game_of_hasCertificate
    (c : PolynomialCoordinates 5 K) (F A : AmbientPoly 5)
    (hF : F.IsHomogeneous 6) (h : HasCertificate F 1 A) :
    ∃ (v : Fin 6 → RegularRing F) (r : RegularRing F),
      (∀ i, fieldAction c.derivative (coordinateEuler c)
        (regularMap c F (v i)) = regularMap c F (v i)) ∧
      c.embed A -
          fieldAction c.derivative (fun i => regularMap c F (v i)) (c.embed F) +
          c.embed F * fieldDivergence c.derivative (fun i => regularMap c F (v i)) =
        c.embed F ^ 2 * regularMap c F r := by
  obtain ⟨D, N, Q, hv⟩ := h
  have hdegree : F.totalDegree = 6 := hF.totalDegree hv.hypersurface_ne_zero
  rw [hdegree] at hv
  exact exists_regular_homogeneous_game_of_verify c hv

#print axioms euler_action_homogeneous
#print axioms homogeneous_quotient_euler_weight_one
#print axioms certificateCurrent_euler_weight_one
#print axioms certificateCurrent_game
#print axioms exists_regular_homogeneous_game_of_verify
#print axioms exists_regular_homogeneous_game_of_hasCertificate

end CertificateRegularCurrent
