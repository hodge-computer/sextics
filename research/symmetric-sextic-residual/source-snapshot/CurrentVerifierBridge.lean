import HodgeComputer.Verify
import HodgeComputer.Constructions.RationalFields.Homogenization

/-!
Positive algebraic assembly from a residue primitive to the unchanged verifier.

The primitive, normal field, chart rules, and a legal homogeneous common
denominator are explicit construction inputs. Their existence is not asserted.
The quotient rule and cleared certificate identity are proved, not hypotheses.
No theorem in this file claims a solution of the protected target.
-/

noncomputable section
namespace CurrentVerifierBridge
open MvPolynomial HodgeComputer HodgeTestbed HodgeTestbed.Conic
open scoped BigOperators

variable {K : Type*} [Field K] [CharZero K] [Algebra ℚ K]

/-- An actual polynomial embedding with compatible coordinate derivatives. -/
structure PolynomialCoordinates (n : ℕ) (K : Type*) [Field K] [Algebra ℚ K] where
  embed : AmbientPoly n →+* K
  injective : Function.Injective embed
  derivative : Fin (n+1) → Derivation ℚ K K
  compatible : ∀ i P, derivative i (embed P) = embed (pderiv i P)

def quotientField {n : ℕ} (c : PolynomialCoordinates n K)
    (N : Fin (n+1) → AmbientPoly n) (D : AmbientPoly n) : Fin (n+1) → K :=
  fun i => c.embed (N i) / c.embed D

theorem quotient_action {n : ℕ} (c : PolynomialCoordinates n K)
    (F D : AmbientPoly n) (N : Fin (n+1) → AmbientPoly n) :
    fieldAction c.derivative (quotientField c N D) (c.embed F) =
      c.embed (directional F N) / c.embed D := by
  simp only [fieldAction_apply, quotientField, c.compatible, directional, map_sum, map_mul]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem quotient_divergence {n : ℕ} (c : PolynomialCoordinates n K)
    (D : AmbientPoly n) (N : Fin (n+1) → AmbientPoly n) :
    fieldDivergence c.derivative (quotientField c N D) =
      c.embed (divergenceNumerator D N) / c.embed D ^ 2 := by
  simp only [fieldDivergence, quotientField, Derivation.leibniz_div,
    c.compatible, smul_eq_mul]
  rw [← Finset.mul_sum]
  have hs : (∑ i, (c.embed D * c.embed (pderiv i (N i)) -
      c.embed (N i) * c.embed (pderiv i D))) = c.embed (divergenceNumerator D N) := by
    simp only [divergenceNumerator, divergence, directional, map_sub, map_mul,
      map_sum, Finset.mul_sum, Finset.sum_sub_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hs]
  simp only [div_eq_mul_inv, inv_pow]
  ring

/-- The semantic bridge from the rational differential identity to the
polynomial defect used by the verifier, for arbitrary pole parameter. -/
theorem defect_clearing {n : ℕ} (c : PolynomialCoordinates n K)
    (F A D : AmbientPoly n) (q : ℕ) (N : Fin (n+1) → AmbientPoly n)
    (hD : D ≠ 0) :
    c.embed (defect F A D q N) = c.embed D ^ 2 *
      (c.embed A - (q : K) * fieldAction c.derivative (quotientField c N D) (c.embed F)
        + c.embed F * fieldDivergence c.derivative (quotientField c N D)) := by
  have hd : c.embed D ≠ 0 := fun h => hD (c.injective (by simpa using h))
  rw [quotient_action, quotient_divergence]
  simp only [defect, map_add, map_sub, map_mul, map_pow, map_natCast]
  field_simp [hd]

/-- An ordinary rational remainder is permitted. Its computed denominator
clearing is a separate polynomial identity, not a zero-remainder restriction. -/
theorem verify_of_field_residual {n d q e v : ℕ} (c : PolynomialCoordinates n K)
    (F A D Q : AmbientPoly n) (N : Fin (n+1) → AmbientPoly n) (remainder : K)
    (hF : F ≠ 0) (hFd : F.IsHomogeneous d)
    (hA : Homogeneous A ((d : ℤ)*(q+1)-(n+1)))
    (hD : D ≠ 0) (hDe : D.IsHomogeneous e)
    (hN : ∀ i, (N i).IsHomogeneous v)
    (hdegree : (v : ℤ) = e+(d : ℤ)*q-n)
    (hlegal : IsRelPrime F D)
    (hgame : c.embed A - (q : K) *
        fieldAction c.derivative (quotientField c N D) (c.embed F)
      + c.embed F * fieldDivergence c.derivative (quotientField c N D) =
        c.embed F ^ (q+1) * remainder)
    (hquotient : c.embed Q = c.embed D ^ 2 * remainder) :
    Verify F A d q D N Q where
  hypersurface_ne_zero := hF
  hypersurface_homogeneous := hFd
  source_homogeneous := hA
  denominator_ne_zero := hD
  denominator_homogeneous := by rw [hDe.totalDegree hD]; exact hDe
  numerator_homogeneous := by
    intro i
    rw [hDe.totalDegree hD, ← hdegree]
    exact Homogeneous.of_isHomogeneous (hN i)
  denominator_legal := hlegal
  identity := by
    apply c.injective
    rw [defect_clearing c F A D q N hD, hgame, map_mul, map_pow, hquotient]
    ring

def primitiveDefect {ι : Type*} [Fintype ι]
    (δ : ι → Derivation ℚ K K) (F A : K) (current : ι → K) : K :=
  F * fieldDivergence δ current - 2 * fieldAction δ current F - A*F

/-- Exact error propagation through the explicit residue bracket correction. -/
theorem residueCorrection_game_error {ι : Type*} [Fintype ι]
    (δ : ι → Derivation ℚ K K)
    (hcomm : ∀ i j, Function.Commute (δ i) (δ j))
    (F A : K) (normal current : ι → K)
    (hnormal : fieldAction δ normal F = 1) :
    A - fieldAction δ (fun i => -residueCorrection δ A normal current i) F
      + F * fieldDivergence δ (fun i => -residueCorrection δ A normal current i) =
      -(fieldAction δ normal (primitiveDefect δ F A current)
        + primitiveDefect δ F A current * fieldDivergence δ normal) / 2 := by
  have htwo : fieldAction δ normal (2 : K) = 0 := (fieldAction δ normal).map_natCast 2
  have ha : fieldAction δ (fun i => -residueCorrection δ A normal current i) F =
      -fieldAction δ (residueCorrection δ A normal current) F := by
    simp only [fieldAction_apply, neg_mul, Finset.sum_neg_distrib]
  have hv : fieldDivergence δ (fun i => -residueCorrection δ A normal current i) =
      -fieldDivergence δ (residueCorrection δ A normal current) := by
    simp only [fieldDivergence, map_neg, Finset.sum_neg_distrib]
  rw [ha, hv, residueCorrection_divergence δ hcomm]
  unfold residueCorrection
  rw [fieldAction_sub, fieldAction_add, fieldAction_bracket δ hcomm,
    fieldAction_scale, fieldAction_scale, hnormal, Derivation.map_one_eq_zero]
  simp only [primitiveDefect, residueScalar, fieldDivergence_scale,
    map_sub, Derivation.leibniz, derivation_half, htwo,
    hnormal, smul_eq_mul]
  ring

def residueRemainder {ι : Type*} [Fintype ι]
    (δ : ι → Derivation ℚ K K) (F : K) (normal : ι → K) (error : K) : K :=
  -(3*error + F*(fieldAction δ normal error + error*fieldDivergence δ normal))/2

/-- Exact propagation of a factored primitive error in the field. The
factorization alone does not assert regularity along F; the ordinary verifier
adapter additionally requires polynomial clearing of the computed remainder. -/
theorem residueCorrection_game_mod_cube {ι : Type*} [Fintype ι]
    (δ : ι → Derivation ℚ K K)
    (hcomm : ∀ i j, Function.Commute (δ i) (δ j))
    (F A error : K) (normal current : ι → K)
    (hnormal : fieldAction δ normal F = 1)
    (hprimitive : F * fieldDivergence δ current - 2 * fieldAction δ current F =
      A*F+F^3*error) :
    A - fieldAction δ (fun i => -residueCorrection δ A normal current i) F
      + F * fieldDivergence δ (fun i => -residueCorrection δ A normal current i) =
      F^2 * residueRemainder δ F normal error := by
  have he : primitiveDefect δ F A current = F^3*error := by
    unfold primitiveDefect
    linear_combination hprimitive
  rw [residueCorrection_game_error δ hcomm F A normal current hnormal, he]
  simp only [Derivation.leibniz, Derivation.leibniz_pow, hnormal,
    smul_eq_mul, residueRemainder]
  ring

/-- A rational game identity with a specified legal homogeneous common
denominator assembles an actual strict Verify record. -/
theorem verify_of_field_game {n d q e v : ℕ} (c : PolynomialCoordinates n K)
    (F A D : AmbientPoly n) (N : Fin (n+1) → AmbientPoly n)
    (hF : F ≠ 0) (hFd : F.IsHomogeneous d)
    (hA : Homogeneous A ((d : ℤ)*(q+1)-(n+1)))
    (hD : D ≠ 0) (hDe : D.IsHomogeneous e)
    (hN : ∀ i, (N i).IsHomogeneous v)
    (hdegree : (v : ℤ) = e+(d : ℤ)*q-n)
    (hlegal : IsRelPrime F D)
    (hgame : c.embed A - (q : K) *
        fieldAction c.derivative (quotientField c N D) (c.embed F)
      + c.embed F * fieldDivergence c.derivative (quotientField c N D) = 0) :
    Verify F A d q D N 0 where
  hypersurface_ne_zero := hF
  hypersurface_homogeneous := hFd
  source_homogeneous := hA
  denominator_ne_zero := hD
  denominator_homogeneous := by rw [hDe.totalDegree hD]; exact hDe
  numerator_homogeneous := by
    intro i
    rw [hDe.totalDegree hD, ← hdegree]
    exact Homogeneous.of_isHomogeneous (hN i)
  denominator_legal := hlegal
  identity := by
    have hz : defect F A D q N = 0 := by
      apply c.injective
      rw [defect_clearing c F A D q N hD, hgame, mul_zero, map_zero]
    simp only [hz, mul_zero]

/-- The residue primitive supplies the game identity through the explicit
bracket correction. No polynomial target identity is assumed. -/
theorem verify_of_residue_primitive {e : ℕ} (c : PolynomialCoordinates 5 K)
    (F A D : AmbientPoly 5) (N : Fin 6 → AmbientPoly 5)
    (hF : F ≠ 0) (hFd : F.IsHomogeneous 6) (hA : A.IsHomogeneous 6)
    (hD : D ≠ 0) (hDe : D.IsHomogeneous e)
    (hN : ∀ i, (N i).IsHomogeneous (e+1)) (hlegal : IsRelPrime F D)
    (normal current : Fin 6 → K)
    (hcomm : ∀ i j, Function.Commute (c.derivative i) (c.derivative j))
    (hnormal : fieldAction c.derivative normal (c.embed F) = 1)
    (hprimitive : c.embed F * fieldDivergence c.derivative current
      - 2 * fieldAction c.derivative current (c.embed F) = c.embed A * c.embed F)
    (hclear : quotientField c N D =
      fun i => -residueCorrection c.derivative (c.embed A) normal current i) :
    Verify F A 6 1 D N 0 := by
  apply verify_of_field_game c F A D N hF hFd
    (by simpa using Homogeneous.of_isHomogeneous hA) hD hDe hN
    (by omega) hlegal
  rw [hclear]
  simpa only [Nat.cast_one, one_mul] using
    residueCorrection_game c.derivative hcomm (c.embed F) (c.embed A)
      normal current hnormal hprimitive

/-- Ordinary certificate assembly from the factored primitive error. The
explicit polynomial clearing of the computed remainder is essential: an
arbitrary field factorization by F³ alone gives no divisibility statement. -/
theorem verify_of_residue_primitive_mod_cube {e : ℕ} (c : PolynomialCoordinates 5 K)
    (F A D Q : AmbientPoly 5) (N : Fin 6 → AmbientPoly 5)
    (hF : F ≠ 0) (hFd : F.IsHomogeneous 6) (hA : A.IsHomogeneous 6)
    (hD : D ≠ 0) (hDe : D.IsHomogeneous e)
    (hN : ∀ i, (N i).IsHomogeneous (e+1)) (hlegal : IsRelPrime F D)
    (normal current : Fin 6 → K) (error : K)
    (hcomm : ∀ i j, Function.Commute (c.derivative i) (c.derivative j))
    (hnormal : fieldAction c.derivative normal (c.embed F) = 1)
    (hprimitive : c.embed F * fieldDivergence c.derivative current
      - 2 * fieldAction c.derivative current (c.embed F) =
        c.embed A*c.embed F+c.embed F^3*error)
    (hclear : quotientField c N D =
      fun i => -residueCorrection c.derivative (c.embed A) normal current i)
    (hquotient : c.embed Q = c.embed D^2 *
      residueRemainder c.derivative (c.embed F) normal error) :
    Verify F A 6 1 D N Q := by
  apply verify_of_field_residual c F A D Q N
    (residueRemainder c.derivative (c.embed F) normal error) hF hFd
    (by simpa using Homogeneous.of_isHomogeneous hA) hD hDe hN
    (by omega) hlegal ?_ hquotient
  rw [hclear]
  simpa only [Nat.cast_one, one_mul] using
    residueCorrection_game_mod_cube c.derivative hcomm (c.embed F) (c.embed A)
      error normal current hnormal hprimitive

/-- Exact chart transport of the entire game defect, including a nonzero
remainder. The strict and ordinary adapters can both use this identity. -/
theorem homogenized_game_defect
    {R : Type*} [Field R] [Algebra ℚ R]
    (δ : Fin 5 → Derivation ℚ R R) (θ : Fin 6 → Derivation ℚ K K)
    (f : R →+* K) (a : K) (x p : Fin 5 → R)
    (chart : HomogeneousChart δ θ f a x) (H A : R) :
    a^6*f A - fieldAction θ (homogenizedField f a p) (a^6*f H)
      + (a^6*f H)*fieldDivergence θ (homogenizedField f a p) =
      a^6*f (A-fieldAction δ p H+H*fieldDivergence δ p) := by
  rw [homogenizedField_contraction δ θ f a x p chart H,
    homogenizedField_divergence δ θ f a x p chart]
  simp only [map_add, map_sub, map_mul]
  ring

/-- An affine residue primitive, an actual projective chart, and an explicit
legal homogeneous clearing produce the verifier record in six variables.
Chart source binding and the cleared corrected field are stated separately. -/
theorem verify_of_affine_residue_primitive
    {R : Type*} [Field R] [CharZero R] [Algebra ℚ R] {e : ℕ}
    (c : PolynomialCoordinates 5 K)
    (δ : Fin 5 → Derivation ℚ R R) (f : R →+* K) (a : K) (x : Fin 5 → R)
    (chart : HomogeneousChart δ c.derivative f a x)
    (H B : R) (normal current : Fin 5 → R)
    (hcomm : ∀ i j, Function.Commute (δ i) (δ j))
    (hnormal : fieldAction δ normal H = 1)
    (hprimitive : H * fieldDivergence δ current - 2 * fieldAction δ current H = B*H)
    (F A D : AmbientPoly 5) (N : Fin 6 → AmbientPoly 5)
    (hF : F ≠ 0) (hFd : F.IsHomogeneous 6) (hA : A.IsHomogeneous 6)
    (hD : D ≠ 0) (hDe : D.IsHomogeneous e)
    (hN : ∀ i, (N i).IsHomogeneous (e+1)) (hlegal : IsRelPrime F D)
    (hFbind : c.embed F = a^6*f H) (hAbind : c.embed A = a^6*f B)
    (hclear : quotientField c N D = homogenizedField f a
      (fun i => -residueCorrection δ B normal current i)) :
    Verify F A 6 1 D N 0 := by
  apply verify_of_field_game c F A D N hF hFd
    (by simpa using Homogeneous.of_isHomogeneous hA) hD hDe hN
    (by omega) hlegal
  rw [hclear, hFbind, hAbind]
  simpa only [Nat.cast_one, one_mul] using
    homogenizedField_game δ c.derivative f a x
      (fun i => -residueCorrection δ B normal current i) chart H B
      (residueCorrection_game δ hcomm H B normal current hnormal hprimitive)

#print axioms defect_clearing
#print axioms residueCorrection_game_mod_cube
#print axioms verify_of_residue_primitive
#print axioms verify_of_residue_primitive_mod_cube
#print axioms verify_of_affine_residue_primitive
end CurrentVerifierBridge
