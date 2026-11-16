/- Adapted for the instance `one-reflection-y2-sector` from the accepted holdout proof by `fqlx` (prepared with OpenAI ChatGPT assistance); the target-specific source, companion and trace data are replaced, all other modules are unchanged. Adaptation prepared with Claude Code assistance for `DiamondJM`. -/
import Proposal.CoverCoordinates
import Proposal.DeckTrace
import Proposal.FermatDeck

/- Source component: CoverDeckField -/
section
/-!
The common-cover deck transformation is an actual automorphism fixing
the exact physical function field. Its nontrivial inverse-fourth-power
character has normalized trace zero. Prepared with OpenAI ChatGPT
assistance for a contribution through GitHub account fqlx.
-/

noncomputable section

namespace HoldoutConstruction

attribute [local instance] fermatCurve_adjoinRoot_isDomain fermat_base_charZero
attribute [local instance] holdoutCoordinateRing_isDomain genericCommonCoverRing_isDomain
attribute [local instance] commonCoverFunctionField_finite

local instance coverDeckField_holdoutFunctionFieldCharZero : CharZero HoldoutFunctionField :=
  charZero_of_injective_ringHom (f := algebraMap ℂ HoldoutFunctionField)
    (algebraMap ℂ HoldoutFunctionField).injective

local instance coverDeckField_commonCoverFunctionFieldCharZero : CharZero CommonCoverFunctionField :=
  charZero_of_injective_ringHom (f := algebraMap ℂ CommonCoverFunctionField)
    (algebraMap ℂ CommonCoverFunctionField).injective

def commonDeckFieldEquiv (z : ℂ) (hz : z^6=1) (hz0 : z ≠ 0) :
    CommonCoverFunctionField ≃+* CommonCoverFunctionField :=
  IsFractionRing.ringEquivOfRingEquiv (commonDeckRingEquiv z hz hz0)

@[simp] theorem commonDeckFieldEquiv_coordinateRing
    (z : ℂ) (hz : z^6=1) (hz0 : z ≠ 0) (r : GenericCommonCoverRing ℂ) :
    commonDeckFieldEquiv z hz hz0
      (algebraMap (GenericCommonCoverRing ℂ) CommonCoverFunctionField r) =
      algebraMap (GenericCommonCoverRing ℂ) CommonCoverFunctionField
        (commonDeckRingEquiv z hz hz0 r) :=
  IsFractionRing.ringEquivOfRingEquiv_algebraMap _ _

@[simp] theorem commonDeckFieldEquiv_base
    (z : ℂ) (hz : z^6=1) (hz0 : z ≠ 0) (c : FermatCoefficientField ℂ) :
    commonDeckFieldEquiv z hz hz0
      (algebraMap (FermatCoefficientField ℂ) CommonCoverFunctionField c) =
      algebraMap (FermatCoefficientField ℂ) CommonCoverFunctionField
        (genericBaseScaleEquiv z⁻¹ (by rw [inv_pow, hz, inv_one]) (inv_ne_zero hz0) c) := by
  rw [IsScalarTower.algebraMap_apply (FermatCoefficientField ℂ)
    (GenericCommonCoverRing ℂ) CommonCoverFunctionField,
    commonDeckFieldEquiv_coordinateRing]
  change algebraMap (GenericCommonCoverRing ℂ) CommonCoverFunctionField
    (commonDeckRingEquiv z hz hz0 (AdjoinRoot.of _ (MvPolynomial.C c))) = _
  rw [commonDeckRingEquiv_of, commonDeckCoefficientEquiv_C]
  rfl

@[simp] theorem commonDeckFieldEquiv_complex
    (z : ℂ) (hz : z^6=1) (hz0 : z ≠ 0) (c : ℂ) :
    commonDeckFieldEquiv z hz hz0 (algebraMap ℂ CommonCoverFunctionField c) =
      algebraMap ℂ CommonCoverFunctionField c := by
  rw [IsScalarTower.algebraMap_apply ℂ (FermatCoefficientField ℂ)
    CommonCoverFunctionField, commonDeckFieldEquiv_base,
    genericBaseScaleEquiv_coefficient]

@[simp] theorem commonDeckFieldEquiv_alpha
    (z : ℂ) (hz : z^6=1) (hz0 : z ≠ 0) :
    commonDeckFieldEquiv z hz hz0 coverAlpha =
      algebraMap ℂ CommonCoverFunctionField z⁻¹ * coverAlpha := by
  rw [coverAlpha, commonDeckFieldEquiv_base, genericBaseScaleEquiv_alpha, map_mul,
    ← IsScalarTower.algebraMap_apply]

@[simp] theorem commonDeckFieldEquiv_beta
    (z : ℂ) (hz : z^6=1) (hz0 : z ≠ 0) :
    commonDeckFieldEquiv z hz hz0 coverBeta =
      algebraMap ℂ CommonCoverFunctionField z⁻¹ * coverBeta := by
  rw [coverBeta, commonDeckFieldEquiv_base, genericBaseScaleEquiv_beta, map_mul,
    ← IsScalarTower.algebraMap_apply]

@[simp] theorem commonDeckFieldEquiv_x0
    (z : ℂ) (hz : z^6=1) (hz0 : z ≠ 0) :
    commonDeckFieldEquiv z hz hz0 coverX0 = coverX0 := by
  simp [coverX0]

@[simp] theorem commonDeckFieldEquiv_parameter
    (z : ℂ) (hz : z^6=1) (hz0 : z ≠ 0) (i : Fin 4) :
    commonDeckFieldEquiv z hz hz0 (coverCoefficient i) =
      ![coverX1, coverX2, coverY, algebraMap ℂ CommonCoverFunctionField z*coverT] i := by
  simp only [coverCoefficient, commonDeckFieldEquiv_coordinateRing,
    commonDeckRingEquiv_of, commonDeckCoefficientEquiv_X]
  fin_cases i
  · rfl
  · rfl
  · rfl
  · change algebraMap (GenericCommonCoverRing ℂ) CommonCoverFunctionField
      (AdjoinRoot.of _
        (MvPolynomial.C (algebraMap ℂ (FermatCoefficientField ℂ) z) * MvPolynomial.X 3)) =
          algebraMap ℂ CommonCoverFunctionField z * coverT
    rw [map_mul, map_mul, cover_of_C,
      ← IsScalarTower.algebraMap_apply ℂ (FermatCoefficientField ℂ) CommonCoverFunctionField]
    rfl

@[simp] theorem commonDeckFieldEquiv_T
    (z : ℂ) (hz : z^6=1) (hz0 : z ≠ 0) :
    commonDeckFieldEquiv z hz hz0 coverT =
      algebraMap ℂ CommonCoverFunctionField z * coverT := by
  simpa only [Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] using
    commonDeckFieldEquiv_parameter z hz hz0 3

private theorem scaled_product_fixed
    {K L : Type*} [Field K] [Field L] (e : L ≃+* L) (f : K →+* L)
    (z : K) (hz : z ≠ 0) (a t : L)
    (ha : e a = f z⁻¹*a) (ht : e t = f z*t) : e (a*t) = a*t := by
  rw [map_mul, ha, ht]
  have hz' : f z⁻¹*f z = 1 := by rw [← map_mul, inv_mul_cancel₀ hz, map_one]
  calc
    (f z⁻¹*a)*(f z*t) = (f z⁻¹*f z)*(a*t) := by ring
    _ = a*t := by rw [hz', one_mul]

@[simp] theorem commonDeckFieldEquiv_Y0
    (z : ℂ) (hz : z^6=1) (hz0 : z ≠ 0) :
    commonDeckFieldEquiv z hz hz0 (coverAlpha*coverT) = coverAlpha*coverT :=
  scaled_product_fixed (commonDeckFieldEquiv z hz hz0)
    (algebraMap ℂ CommonCoverFunctionField) z hz0 coverAlpha coverT
    (commonDeckFieldEquiv_alpha z hz hz0) (commonDeckFieldEquiv_T z hz hz0)

@[simp] theorem commonDeckFieldEquiv_Y2
    (z : ℂ) (hz : z^6=1) (hz0 : z ≠ 0) :
    commonDeckFieldEquiv z hz hz0 (coverBeta*coverT) = coverBeta*coverT :=
  scaled_product_fixed (commonDeckFieldEquiv z hz hz0)
    (algebraMap ℂ CommonCoverFunctionField) z hz0 coverBeta coverT
    (commonDeckFieldEquiv_beta z hz hz0) (commonDeckFieldEquiv_T z hz hz0)

private theorem physicalCoordinateFieldMap_parameter (i : Fin 5) :
    physicalCoordinateFieldMap (physicalParameter i) =
      ![coverX1, coverX2, coverAlpha*coverT, coverY, coverBeta*coverT] i := by
  rw [← physicalCoverFieldMap_parameter, physicalCoverFieldMap_coordinateRing]
  rfl

private theorem physicalCoordinateFieldMap_root :
    physicalCoordinateFieldMap physicalRoot = coverX0 := by
  rw [← physicalCoverFieldMap_root, physicalCoverFieldMap_coordinateRing]
  rfl

private theorem physicalCoordinateFieldMap_coefficient (c : ℂ) :
    physicalCoordinateFieldMap (AdjoinRoot.of _ (MvPolynomial.C c)) =
      algebraMap ℂ CommonCoverFunctionField c := by
  change algebraMap (GenericCommonCoverRing ℂ) CommonCoverFunctionField
    (physicalGenericCoverMap ℂ (algebraMap ℂ HoldoutCoordinateRing c)) = _
  rw [physicalGenericCoverMap_coefficient, ← IsScalarTower.algebraMap_apply]

theorem commonDeckFieldEquiv_fixes_coordinateRing
    (z : ℂ) (hz : z^6=1) (hz0 : z ≠ 0) (r : HoldoutCoordinateRing) :
    commonDeckFieldEquiv z hz hz0 (physicalCoordinateFieldMap r) =
      physicalCoordinateFieldMap r := by
  have he : (commonDeckFieldEquiv z hz hz0).toRingHom.comp physicalCoordinateFieldMap =
      physicalCoordinateFieldMap := by
    apply AdjoinRoot.ringHom_ext
    · apply MvPolynomial.ringHom_ext
      · intro c
        change commonDeckFieldEquiv z hz hz0
          (physicalCoordinateFieldMap (AdjoinRoot.of _ (MvPolynomial.C c))) =
            physicalCoordinateFieldMap (AdjoinRoot.of _ (MvPolynomial.C c))
        simp only [physicalCoordinateFieldMap_coefficient, commonDeckFieldEquiv_complex]
      · intro i
        change commonDeckFieldEquiv z hz hz0
          (physicalCoordinateFieldMap (physicalParameter i)) =
            physicalCoordinateFieldMap (physicalParameter i)
        rw [physicalCoordinateFieldMap_parameter]
        fin_cases i <;>
          simp [commonDeckFieldEquiv_parameter]
    · change commonDeckFieldEquiv z hz hz0 (physicalCoordinateFieldMap physicalRoot) =
        physicalCoordinateFieldMap physicalRoot
      rw [physicalCoordinateFieldMap_root]
      exact commonDeckFieldEquiv_x0 z hz hz0
  exact RingHom.congr_fun he r

theorem commonDeckFieldEquiv_fixes_physical
    (z : ℂ) (hz : z^6=1) (hz0 : z ≠ 0) (r : HoldoutFunctionField) :
    commonDeckFieldEquiv z hz hz0 (physicalCoverFieldMap r) =
      physicalCoverFieldMap r := by
  have he : (commonDeckFieldEquiv z hz hz0).toRingHom.comp physicalCoverFieldMap =
      physicalCoverFieldMap := by
    apply IsFractionRing.ringHom_ext (A := HoldoutCoordinateRing)
    intro x
    simp only [RingHom.comp_apply, physicalCoverFieldMap_coordinateRing]
    change commonDeckFieldEquiv z hz hz0 (physicalCoordinateFieldMap x) =
      physicalCoordinateFieldMap x
    exact commonDeckFieldEquiv_fixes_coordinateRing z hz hz0 x
  exact RingHom.congr_fun he r

/-- The deck map is linear over the exact physical residue function field. -/
def physicalDeckAlgHom (z : ℂ) (hz : z^6=1) (hz0 : z ≠ 0) :
    CommonCoverFunctionField →ₐ[HoldoutFunctionField] CommonCoverFunctionField :=
  { (commonDeckFieldEquiv z hz hz0).toRingHom with
    commutes' := commonDeckFieldEquiv_fixes_physical z hz hz0 }

theorem physicalDeckAlgHom_T (z : ℂ) (hz : z^6=1) (hz0 : z ≠ 0) :
    physicalDeckAlgHom z hz hz0 coverT =
      algebraMap HoldoutFunctionField CommonCoverFunctionField
        (algebraMap ℂ HoldoutFunctionField z) * coverT := by
  change commonDeckFieldEquiv z hz hz0 coverT = _
  rw [commonDeckFieldEquiv_T, ← IsScalarTower.algebraMap_apply]

theorem exists_nontrivial_sixth_root :
    ∃ z : ℂ, z^6=1 ∧ z ≠ 0 ∧ z^4 ≠ 1 ∧ z^2 ≠ 1 := by
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (-3 : ℂ) (show 0<2 by decide)
  let z := (s-1)/2
  have hq : z^2+z+1 = 0 := by
    dsimp [z]
    linear_combination hs/4
  have h3 : z^3=1 := by linear_combination (z-1)*hq
  have h0 : z ≠ 0 := by intro hz; simp [hz] at h3
  have h1 : z ≠ 1 := by intro hz; norm_num [hz] at hq
  refine ⟨z, ?_, h0, ?_, ?_⟩
  · rw [show 6=3*2 by decide, pow_mul, h3, one_pow]
  · intro h4
    apply h1
    calc
      z = z^3*z := by rw [h3, one_mul]
      _ = z^4 := by ring
      _ = 1 := h4
  · intro h2
    have hz2 : z = -2 := by linear_combination hq - h2
    rw [hz2] at h3
    norm_num at h3

theorem commonCover_trace_inverse_fourth :
    Algebra.normalizedTrace HoldoutFunctionField CommonCoverFunctionField
      ((coverT^4)⁻¹) = 0 := by
  obtain ⟨z,hz,hz0,hz4,_⟩ := exists_nontrivial_sixth_root
  apply normalizedTrace_inv_fourth_zero (physicalDeckAlgHom z hz hz0)
    (algebraMap ℂ HoldoutFunctionField z) ?_ coverT (physicalDeckAlgHom_T z hz hz0)
  intro h
  apply hz4
  apply (algebraMap ℂ HoldoutFunctionField).injective
  simpa only [map_pow, map_one] using h

theorem commonCover_trace_inverse_square :
    Algebra.normalizedTrace HoldoutFunctionField CommonCoverFunctionField
      ((coverT^2)⁻¹) = 0 := by
  obtain ⟨z,hz,hz0,_,hz2⟩ := exists_nontrivial_sixth_root
  apply normalizedTrace_inv_pow_zero (physicalDeckAlgHom z hz hz0)
    (algebraMap ℂ HoldoutFunctionField z) 2 ?_ coverT (physicalDeckAlgHom_T z hz hz0)
  intro h
  apply hz2
  apply (algebraMap ℂ HoldoutFunctionField).injective
  simpa only [map_pow, map_one] using h

theorem commonCover_trace_square :
    Algebra.normalizedTrace HoldoutFunctionField CommonCoverFunctionField
      (coverT^2) = 0 := by
  obtain ⟨z,hz,hz0,_,hz2⟩ := exists_nontrivial_sixth_root
  apply normalizedTrace_pow_zero (physicalDeckAlgHom z hz hz0)
    (algebraMap ℂ HoldoutFunctionField z) 2 ?_ coverT (physicalDeckAlgHom_T z hz hz0)
  intro h
  apply hz2
  apply (algebraMap ℂ HoldoutFunctionField).injective
  simpa only [map_pow, map_one] using h

end HoldoutConstruction

#print axioms HoldoutConstruction.commonDeckFieldEquiv_fixes_physical
#print axioms HoldoutConstruction.physicalDeckAlgHom
#print axioms HoldoutConstruction.commonCover_trace_inverse_fourth
end
end
