import Proposal.SeedLinkageOrbitKernel

/-!
# Graded localization, restriction and gluing on the curve
-/

set_option Elab.async false

/- Component: continuation_3/CurveLocalizedRestriction.lean -/
section
/-!
# Restriction of the actual seed coordinate localizations to the curves

The target of each map is the localization of the actual curve quotient
at the image of the source denominator. The two base-coordinate charts
are compared with the previously checked six-coordinate curve complex.
-/

noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2CurveLocalizedRestriction

open MvPolynomial CycleQ2CurveRestriction CycleQ2SegreTangentLocal

variable (R : Type*) [CommRing R]

abbrev SB := CycleQ2SeedQuotientFiniteFree.Base R
abbrev CB := CycleQ2CurveQuotientFiniteFree.Base R
abbrev SL (r ι : R) (t : Finset (Fin 3)) := CycleQ2SeedCechLocalizedBasis.SeedLocal R r ι t
abbrev CL (side : Side) (r ι : R) (t : Finset (Fin 2)) :=
  CycleQ2CurveCechLocalizedBasis.CurveLocal R side r ι t

def seedProduct (r ι : R) (t : Finset (Fin 3)) : SeedRing r ι :=
  algebraMap (SB R) (SeedRing r ι) (CycleQ2SeedCechLocalization.baseProduct R t)

instance sourceAway (r ι : R) (t : Finset (Fin 3)) :
    IsLocalization.Away (seedProduct R r ι t) (SL R r ι t) :=
  CycleQ2SeedCechRestrictions.seedLocalAway R r ι t

def curveProduct (side : Side) (r ι : R) (t : Finset (Fin 3)) : CurveRing side r ι :=
  seedRestriction side r ι (seedProduct R r ι t)

abbrev RestrictedLocal (side : Side) (r ι : R) (t : Finset (Fin 3)) :=
  Localization.Away (curveProduct R side r ι t)

instance targetAway (side : Side) (r ι : R) (t : Finset (Fin 3)) :
    IsLocalization.Away ((seedRestriction side r ι).toRingHom (seedProduct R r ι t))
      (RestrictedLocal R side r ι t) :=
  inferInstanceAs (IsLocalization.Away (curveProduct R side r ι t)
    (Localization.Away (curveProduct R side r ι t)))

def localRestrictionMap (side : Side) (r ι : R) (t : Finset (Fin 3)) :
    SL R r ι t →+* RestrictedLocal R side r ι t :=
  IsLocalization.Away.map (SL R r ι t) (RestrictedLocal R side r ι t)
    (seedRestriction side r ι).toRingHom (seedProduct R r ι t)

@[simp] theorem localRestrictionMap_algebraMap (side : Side) (r ι : R)
    (t : Finset (Fin 3)) (p : SeedRing r ι) :
    localRestrictionMap R side r ι t (algebraMap (SeedRing r ι) (SL R r ι t) p)=
      algebraMap (CurveRing side r ι) (RestrictedLocal R side r ι t) (seedRestriction side r ι p) :=
  by
  unfold localRestrictionMap IsLocalization.Away.map
  exact IsLocalization.map_eq _ p

theorem curveProduct_dvd (side : Side) (r ι : R) {s t : Finset (Fin 3)} (hst : s⊆t) :
    curveProduct R side r ι s ∣ curveProduct R side r ι t := by
  exact (seedRestriction side r ι).toRingHom.map_dvd
    ((algebraMap (SB R) (SeedRing r ι)).map_dvd
      (CycleQ2SeedCechRestrictions.baseProduct_dvd R hst))

def restriction (side : Side) (r ι : R) {s t : Finset (Fin 3)} (hst : s⊆t) :
    RestrictedLocal R side r ι s →+* RestrictedLocal R side r ι t :=
  IsLocalization.Away.lift (curveProduct R side r ι s)
    (IsLocalization.Away.isUnit_of_dvd (S:=RestrictedLocal R side r ι t)
      (curveProduct R side r ι t) (curveProduct_dvd R side r ι hst))

@[simp] theorem restriction_algebraMap (side : Side) (r ι : R)
    {s t : Finset (Fin 3)} (hst : s⊆t) (p : CurveRing side r ι) :
    restriction R side r ι hst (algebraMap _ (RestrictedLocal R side r ι s) p)=
      algebraMap _ (RestrictedLocal R side r ι t) p := IsLocalization.Away.lift_eq _ _ _

theorem localRestrictionMap_natural (side : Side) (r ι : R)
    {s t : Finset (Fin 3)} (hst : s⊆t) :
    (restriction R side r ι hst).comp (localRestrictionMap R side r ι s)=
      (localRestrictionMap R side r ι t).comp (CycleQ2SeedCechRestrictions.restriction R r ι hst) := by
  apply IsLocalization.ringHom_ext (S:=SL R r ι s) (Submonoid.powers (seedProduct R r ι s))
  apply RingHom.ext
  intro p
  simp only [RingHom.comp_apply,localRestrictionMap_algebraMap,restriction_algebraMap,
    CycleQ2SeedCechRestrictions.restriction_algebraMap]

def baseIndex : Fin 2 → Fin 3 := ![0,2]

theorem baseIndex_injective : Function.Injective baseIndex := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp [baseIndex] at h ⊢

def seedOpen (t : Finset (Fin 2)) : Finset (Fin 3) := t.image baseIndex

def coordinateScale (side : Side) : R := match side with | .left => 1 | .right => 2

theorem restriction_baseCoordinate (side : Side) (r ι : R) (j : Fin 2) :
    seedRestriction side r ι
      (algebraMap (SB R) (SeedRing r ι) (X (baseIndex j)))=
      algebraMap R (CurveRing side r ι) (coordinateScale R side)*
        algebraMap (CB R) (CurveRing side r ι) (X j) := by
  change seedRestriction side r ι
    (Ideal.Quotient.mk _ (CycleQ2SeedQuotientFiniteFree.remainingInclusion R (X (baseIndex j))))=_
  rw [seedRestriction_mk]
  change Ideal.Quotient.mk _ (substitution side r
    (CycleQ2SeedQuotientFiniteFree.remainingInclusion R (X (baseIndex j))))=
      Ideal.Quotient.mk _ (C (coordinateScale R side))*
        Ideal.Quotient.mk _ (CycleQ2CurveQuotientFiniteFree.remainingInclusion R (X j))
  have hCtwo : (C (2:R):CurvePoly R)=2 := map_ofNat C 2
  cases side <;> fin_cases j <;>
    simp [hCtwo,CycleQ2SeedQuotientFiniteFree.remainingInclusion,
      CycleQ2SeedQuotientFiniteFree.remainingIndex,
      CycleQ2CurveQuotientFiniteFree.remainingInclusion,
      CycleQ2CurveQuotientFiniteFree.remainingIndex,
      baseIndex,coordinateScale,restrictionValues,Matrix.cons_val_succ,Fin.reduceSucc] <;> norm_num

theorem curveProduct_baseOpen (side : Side) (r ι : R) (t : Finset (Fin 2)) :
    curveProduct R side r ι (seedOpen t)=
      (algebraMap R (CurveRing side r ι) (coordinateScale R side))^t.card*
        algebraMap (CB R) (CurveRing side r ι) (CycleQ2CurveCechLocalization.baseProduct R t) := by
  classical
  unfold curveProduct seedProduct CycleQ2SeedCechLocalization.baseProduct seedOpen
  rw [Finset.prod_image baseIndex_injective.injOn]
  simp only [map_prod]
  simp only [restriction_baseCoordinate]
  rw [Finset.prod_mul_distrib,Finset.prod_const]
  simp [CycleQ2CurveCechLocalization.baseProduct]

theorem baseOpen_isLocalization (side : Side) (r ι : R) (t : Finset (Fin 2))
    (hscale : IsUnit (coordinateScale R side)) :
    IsLocalization.Away (curveProduct R side r ι (seedOpen t)) (CL R side r ι t) := by
  rw [curveProduct_baseOpen]
  apply IsLocalization.Away.mul_of_isUnit'
  exact ((hscale.map (algebraMap R (CurveRing side r ι))).pow t.card).map
    (algebraMap (CurveRing side r ι) (CL R side r ι t))

def baseOpenEquiv (side : Side) (r ι : R) (t : Finset (Fin 2))
    (hscale : IsUnit (coordinateScale R side)) :
    RestrictedLocal R side r ι (seedOpen t) ≃ₐ[CurveRing side r ι] CL R side r ι t := by
  letI := baseOpen_isLocalization R side r ι t hscale
  exact IsLocalization.algEquiv (Submonoid.powers (curveProduct R side r ι (seedOpen t)))
    (RestrictedLocal R side r ι (seedOpen t)) (CL R side r ι t)

def baseOpenMap (side : Side) (r ι : R) (t : Finset (Fin 2))
    (hscale : IsUnit (coordinateScale R side)) :
    SL R r ι (seedOpen t) →+* CL R side r ι t :=
  (baseOpenEquiv R side r ι t hscale).toRingHom.comp (localRestrictionMap R side r ι (seedOpen t))

@[simp] theorem baseOpenMap_algebraMap (side : Side) (r ι : R) (t : Finset (Fin 2))
    (hscale : IsUnit (coordinateScale R side)) (p : SeedRing r ι) :
    baseOpenMap R side r ι t hscale
      (algebraMap (SeedRing r ι) (SL R r ι (seedOpen t)) p)=
      algebraMap (CurveRing side r ι) (CL R side r ι t) (seedRestriction side r ι p) := by
  simp only [baseOpenMap,RingHom.comp_apply,localRestrictionMap_algebraMap]
  exact (baseOpenEquiv R side r ι t hscale).commutes _

theorem complex_scale_unit (side : Side) : IsUnit (coordinateScale ℂ side) := by
  cases side <;> simp [coordinateScale]

end CycleQ2CurveLocalizedRestriction

#print axioms CycleQ2CurveLocalizedRestriction.localRestrictionMap_natural
#print axioms CycleQ2CurveLocalizedRestriction.baseOpenEquiv
end
end

/- Component: continuation_3/cylinder_bridge/SeedLocalizedProjection.lean -/
section
/-! # Homogeneous projection and regular division in actual coordinate rings -/

noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2SeedLocalizedProjection

open MvPolynomial Matrix CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations
  CycleQ2IncidenceFirstOrder CycleQ2SegreTangentLocal CycleQ2SeedQuotientFiniteFree
  CycleQ2SeedCechThreeOpen CycleQ2SeedCechLocalization CycleQ2SeedCechLocalizedBasis
  CycleQ2SeedCechGlobalGluing CycleQ2SeedQuotientGrading CycleQ2SeedLocalizedClearing
  CycleQ2SeedHomogeneousDenominator CycleQ2WeightedComponent

variable (R : Type*) [CommRing R] [Nontrivial R]

def HasLocalGrade (r ι : R) (s : Finset (Fin 3)) (d : Grade)
    (q : SeedLocal R r ι s) : Prop :=
  ∀ ab, HasGrade ab (signedGrade d) (localizedCoordinates R r ι s q ab)

theorem signed_shift_grade (s : Finset (Fin 3)) (n : ℕ) (d : Grade) :
    signedGrade (n • openGrade s+d)=signedGrade d+baseGrade (n • openExponent s) := by
  change signedGradeHom (n • openGrade s+d)=_
  rw [map_add]
  change signedGrade (n • openGrade s)+signedGrade d=_
  rw [signed_openGrade_nsmul,add_comm]

theorem polynomial_hasLocalGrade (r ι : R) (s : Finset (Fin 3)) (p : Poly R)
    (d : Grade) (hp : HG p d) : HasLocalGrade R r ι s d (polynomialMap R r ι s p) :=
  localized_polynomial_homogeneous R r ι s p d hp

theorem hasLocalGrade_add (r ι : R) (s : Finset (Fin 3)) (d : Grade)
    (p q : SeedLocal R r ι s) (hp : HasLocalGrade R r ι s d p)
    (hq : HasLocalGrade R r ι s d q) : HasLocalGrade R r ι s d (p+q) := by
  intro ab
  change HasGrade ab (signedGrade d) (localizedCoordinates R r ι s (p+q) ab)
  rw [map_add,Pi.add_apply]
  exact hasGrade_add ab _ (hp ab) (hq ab)

/-- A polynomial whose actual localized image has one homogeneous grade is
unchanged in that localization by projecting its original polynomial grade. -/
theorem component_eq_of_homogeneous_image (r ι : R) (s : Finset (Fin 3))
    (p : Poly R) (d : Grade)
    (hp : HasLocalGrade R r ι s d (polynomialMap R r ι s p)) :
    polynomialMap R r ι s (weightedHomogeneousComponent fullGrading d p)=
      polynomialMap R r ι s p := by
  have hq (ab : ShiftIndex) : HasGrade ab (signedGrade d)
      (baseToLaurent R ((seedBasis R r ι).repr (Ideal.Quotient.mk _ p) ab)) := by
    simpa only [polynomialMap,RingHom.comp_apply,localizedCoordinates_algebraMap] using hp ab
  obtain ⟨P,_,hPg,hPq⟩ := exists_signed_homogeneous_representative R r ι
    (Ideal.Quotient.mk _ p) (signedGrade d) hq
  have hPw : HG P d := (signedHomogeneous_iff R P d).mp hPg
  have hmem : p-P ∈ equationsIdeal (smoothH ι) (smoothF r ι) := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_sub,hPq,sub_self]
  have hc := weightedHomogeneousComponent_mem_of_mem R fullGrading
    (CycleQ2SegreWeightedProjection.equationsIdeal_homogeneous r ι) hmem d
  rw [map_sub,hPw.weightedHomogeneousComponent_same] at hc
  have he : Ideal.Quotient.mk (equationsIdeal (smoothH ι) (smoothF r ι))
      (weightedHomogeneousComponent fullGrading d p)=Ideal.Quotient.mk _ P :=
    Ideal.Quotient.eq.mpr hc
  exact congrArg (algebraMap (SeedRing r ι) (SeedLocal R r ι s)) (he.trans hPq)

theorem fraction_hasLocalGrade (r ι : R) (s : Finset (Fin 3))
    (q : SeedLocal R r ι s) (d : Grade) (n : ℕ) (p : Poly R)
    (hp : HG p (n • openGrade s+d))
    (he : polynomialMap R r ι s p=polynomialMap R r ι s (openPolynomial R s^n)*q) :
    HasLocalGrade R r ι s d q := by
  apply (localized_homogeneous_iff_fraction R r ι s q (signedGrade d)).mpr
  refine ⟨n,p,?_,?_⟩
  · rw [← signed_shift_grade s n d]
    exact (signedHomogeneous_iff R p _).mpr hp
  · have hden : algebraMap (SeedRing r ι) (SeedLocal R r ι s)
        (algebraMap (Base R) (SeedRing r ι) (baseProduct R s^n))=
        polynomialMap R r ι s (openPolynomial R s^n) := by
      simp only [polynomialMap,RingHom.comp_apply,map_pow,quotient_openPolynomial]
    rw [hden]
    calc
      q*polynomialMap R r ι s (openPolynomial R s^n)=
          polynomialMap R r ι s (openPolynomial R s^n)*q :=
        mul_comm q (polynomialMap R r ι s (openPolynomial R s^n))
      _ = polynomialMap R r ι s p := he.symm

/-- Multiplication in the actual localized seed ring respects the original
degree and character. -/
theorem hasLocalGrade_mul (r ι : R) (s : Finset (Fin 3)) (d e : Grade)
    (x y : SeedLocal R r ι s) (hx : HasLocalGrade R r ι s d x)
    (hy : HasLocalGrade R r ι s e y) : HasLocalGrade R r ι s (d+e) (x*y) := by
  let z : Fin 2 → SeedLocal R r ι s := ![x,y]
  let g : Fin 2 → Grade := ![d,e]
  have hz : ∀ i ab, HasGrade ab (signedGrade (g i))
      (localizedCoordinates R r ι s (z i) ab) := by
    intro i
    fin_cases i
    · exact hx
    · exact hy
  obtain ⟨n,P,hP,hEq⟩ := exists_common_homogeneous_denominator R r ι s g z hz
  have hP0 : HG (P 0) (n • openGrade s+d) := hP 0
  have hP1 : HG (P 1) (n • openGrade s+e) := hP 1
  have hE0 : polynomialMap R r ι s (P 0)=
      polynomialMap R r ι s (openPolynomial R s^n)*x := hEq 0
  have hE1 : polynomialMap R r ι s (P 1)=
      polynomialMap R r ι s (openPolynomial R s^n)*y := hEq 1
  apply fraction_hasLocalGrade R r ι s (x*y) (d+e) (n+n) (P 0*P 1)
  · have hgrade : (n • openGrade s+d)+(n • openGrade s+e)=
        (n+n) • openGrade s+(d+e) := by rw [add_nsmul]; abel
    exact hgrade ▸ hP0.mul hP1
  · rw [map_mul,hE0,hE1,pow_add,map_mul]
    ring

/-- Division by a regular homogeneous polynomial preserves the expected
grade in the actual localization. No domain assumption is needed. -/
theorem regular_division_hasLocalGrade (r ι : R) (s : Finset (Fin 3))
    (p : Poly R) (e d : Grade) (hp : HG p e)
    (hreg : Function.Injective (fun z : SeedLocal R r ι s => polynomialMap R r ι s p*z))
    (x : SeedLocal R r ι s)
    (hx : HasLocalGrade R r ι s (d+e) (polynomialMap R r ι s p*x)) :
    HasLocalGrade R r ι s d x := by
  let f := polynomialMap R r ι s
  obtain ⟨n,P,hP⟩ := exists_common_polynomial_denominator R r ι s (fun _ _ => x)
  let Q := P 0 0
  have hQ : f Q=f (openPolynomial R s^n)*x := hP 0 0
  have hmul := hasLocalGrade_mul R r ι s (n • openGrade s) (d+e)
    (f (openPolynomial R s^n)) (f p*x)
    (polynomial_hasLocalGrade R r ι s _ _ ((openPolynomial_homogeneous R s).pow n)) hx
  have hEq : f (p*Q)=f (openPolynomial R s^n)*(f p*x) := by rw [map_mul,hQ]; ring
  rw [← hEq] at hmul
  have hc := component_eq_of_homogeneous_image R r ι s (p*Q)
    (n • openGrade s+(d+e)) hmul
  have hgrade : n • openGrade s+(d+e)=e+(n • openGrade s+d) := by abel
  rw [hgrade,component_mul_left fullGrading p Q e (n • openGrade s+d) hp,map_mul,map_mul] at hc
  have hcancel : f (weightedHomogeneousComponent fullGrading (n • openGrade s+d) Q)=f Q := hreg hc
  apply fraction_hasLocalGrade R r ι s x d n
    (weightedHomogeneousComponent fullGrading (n • openGrade s+d) Q)
    (weightedHomogeneousComponent_isWeightedHomogeneous _ _)
  exact hcancel.trans hQ

end CycleQ2SeedLocalizedProjection

#print axioms CycleQ2SeedLocalizedProjection.component_eq_of_homogeneous_image
#print axioms CycleQ2SeedLocalizedProjection.hasLocalGrade_mul
#print axioms CycleQ2SeedLocalizedProjection.regular_division_hasLocalGrade
end
end

/- Component: continuation_3/CurveOpenFaithfulness.lean -/
section
/-! # Faithfulness of the remaining curve chart comparison

The third normal base coordinate is regular in the curve quotient because
that quotient is free over its two-variable base. Thus adjoining that
coordinate to the middle seed chart loses no sections.
-/

noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2CurveOpenFaithfulness

open MvPolynomial CycleQ2CurveRestriction CycleQ2CurveLocalizedRestriction
  CycleQ2CurveQuotientFiniteFree

theorem baseCoordinate_mul_injective (R : Type*) [CommRing R] [IsDomain R]
    (side : Side) (r ι : R) (j : Fin 2) :
    Function.Injective (fun q : CurveRing side r ι =>
      algebraMap (Base R) (CurveRing side r ι) (X j)*q) := by
  intro p q hpq
  have hsm : (X j:Base R) • p=(X j:Base R) • q := by
    change algebraMap (Base R) (CurveRing side r ι) (X j)*p=
      algebraMap (Base R) (CurveRing side r ι) (X j)*q
    exact hpq
  apply (curveBasis R side r ι).repr.injective
  apply Finsupp.ext
  intro ab
  have hh := congrArg (fun z : CurveRing side r ι => (curveBasis R side r ι).repr z ab) hsm
  simp only [map_smul,Finsupp.smul_apply,smul_eq_mul] at hh
  exact mul_left_cancel₀ (X_ne_zero j) hh

theorem last_curveProduct (side : Side) (r ι : ℂ) :
    curveProduct ℂ side r ι {2}=
      algebraMap ℂ (CurveRing side r ι) (coordinateScale ℂ side)*
        algebraMap (Base ℂ) (CurveRing side r ι) (X (1:Fin 2)) := by
  have hh := restriction_baseCoordinate ℂ side r ι (1:Fin 2)
  simpa [curveProduct,seedProduct,CycleQ2SeedCechLocalization.baseProduct,
    baseIndex,CB,Matrix.cons_val_succ,Matrix.cons_val_zero,Fin.reduceSucc] using hh

theorem last_curveProduct_regular (side : Side) (r ι : ℂ) :
    Function.Injective (fun q : CurveRing side r ι => curveProduct ℂ side r ι {2}*q) := by
  rw [last_curveProduct]
  intro p q h
  apply baseCoordinate_mul_injective ℂ side r ι 1
  apply ((complex_scale_unit side).map (algebraMap ℂ (CurveRing side r ι))).mul_right_injective
  simpa only [mul_assoc] using h

theorem middle_last_product (side : Side) (r ι : ℂ) :
    curveProduct ℂ side r ι {1,2}=
      curveProduct ℂ side r ι {1}*curveProduct ℂ side r ι {2} := by
  simp [curveProduct,seedProduct,CycleQ2SeedCechLocalization.baseProduct]

/-- The exact comparison needed to recover the middle chart from its
overlap with the last base-coordinate chart. -/
theorem middle_to_overlap_injective (side : Side) (r ι : ℂ) :
    Function.Injective (CycleQ2CurveLocalizedRestriction.restriction ℂ side r ι
      (show ({1}:Finset (Fin 3))⊆{1,2} by decide)) := by
  letI : IsLocalization.Away
      (curveProduct ℂ side r ι {1}*curveProduct ℂ side r ι {2})
      (RestrictedLocal ℂ side r ι {1,2}) := by
    rw [←middle_last_product]
    infer_instance
  apply CycleQ2LocalizationRegularFactor.restriction_injective
    (curveProduct ℂ side r ι {1}) (curveProduct ℂ side r ι {2})
    (last_curveProduct_regular side r ι)
  exact fun p => restriction_algebraMap ℂ side r ι _ p

end CycleQ2CurveOpenFaithfulness

#print axioms CycleQ2CurveOpenFaithfulness.middle_to_overlap_injective
end
end

/- Component: continuation_3/CurveRestrictionGrading.lean -/
section
/-! # Grading and naturality of the actual curve restriction -/

noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2CurveLocalizedRestriction

open MvPolynomial CycleQ2CurveRestriction CycleQ2SegreTangentLocal
  CycleQ2IncidenceGradedBasis CycleQ2IncidenceNormalForm

variable (R : Type*) [CommRing R]

theorem baseOpenMap_natural (side : Side) (r ι : R) {s t : Finset (Fin 2)}
    (hst : s⊆t) (hscale : IsUnit (coordinateScale R side)) :
    (CycleQ2CurveCechRestrictions.restriction R side r ι hst).comp (baseOpenMap R side r ι s hscale)=
      (baseOpenMap R side r ι t hscale).comp
        (CycleQ2SeedCechRestrictions.restriction R r ι (Finset.image_subset_image hst)) := by
  apply IsLocalization.ringHom_ext (S:=SL R r ι (seedOpen s))
    (Submonoid.powers (seedProduct R r ι (seedOpen s)))
  apply RingHom.ext
  intro p
  change CycleQ2CurveCechRestrictions.restriction R side r ι hst
      (baseOpenMap R side r ι s hscale (algebraMap (SeedRing r ι) (SL R r ι (seedOpen s)) p))=
    baseOpenMap R side r ι t hscale
      (CycleQ2SeedCechRestrictions.restriction R r ι
        (show seedOpen s⊆seedOpen t from Finset.image_subset_image hst)
        (algebraMap (SeedRing r ι) (SL R r ι (seedOpen s)) p))
  calc
    _ = CycleQ2CurveCechRestrictions.restriction R side r ι hst
        (algebraMap (CurveRing side r ι) (CL R side r ι s) (seedRestriction side r ι p)) :=
      congrArg (CycleQ2CurveCechRestrictions.restriction R side r ι hst)
        (baseOpenMap_algebraMap R side r ι s hscale p)
    _ = algebraMap (CurveRing side r ι) (CL R side r ι t) (seedRestriction side r ι p) :=
      CycleQ2CurveCechRestrictions.restriction_algebraMap R side r ι hst _
    _ = baseOpenMap R side r ι t hscale (algebraMap (SeedRing r ι) (SL R r ι (seedOpen t)) p) :=
      (baseOpenMap_algebraMap R side r ι t hscale p).symm
    _ = _ := congrArg (baseOpenMap R side r ι t hscale)
      (CycleQ2SeedCechRestrictions.restriction_algebraMap R r ι
        (show seedOpen s⊆seedOpen t from Finset.image_subset_image hst) p).symm

theorem substitution_signedHomogeneous (side : Side) (r : R)
    (p : MvPolynomial (Fin 5) R) (g : CycleQ2SeedCechThreeOpen.LaurentGrade)
    (hp : CycleQ2SeedQuotientGrading.SignedHomogeneous R p g) :
    CycleQ2CurveQuotientGrading.SignedHomogeneous R (substitution side r p) g.1 := by
  by_cases hz : p=0
  · subst p
    intro e he
    simp at he
  · obtain ⟨e,he⟩ := exists_coeff_ne_zero hz
    have hg := hp e he
    have hh : p.IsWeightedHomogeneous fullGrading (Finsupp.weight fullGrading e) := by
      apply (CycleQ2SeedQuotientGrading.signedHomogeneous_iff R p _).mp
      exact hg.symm ▸ hp
    have hs := substitution_homogeneous side r hh
    have ho := (CycleQ2CurveQuotientGrading.signedHomogeneous_iff R
      (substitution side r p) (Finsupp.weight fullGrading e).1).mpr hs
    have hd := congrArg Prod.fst hg
    exact hd ▸ ho

end CycleQ2CurveLocalizedRestriction

#print axioms CycleQ2CurveLocalizedRestriction.baseOpenMap_natural
#print axioms CycleQ2CurveLocalizedRestriction.substitution_signedHomogeneous
end
end

/- Component: continuation_3/CurveRestrictionKernel.lean -/
section
/-! # The actual component ideals are the kernels of the curve restrictions -/

noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2CurveRestrictionKernel

open MvPolynomial CycleQ2CurveRestriction CycleQ2IncidenceNormalForm
  CycleQ2IncidenceEquations CycleQ2SegreTangentLocal

abbrev P5 := MvPolynomial (Fin 5) ℂ

def componentFirst (side : Side) (r : ℂ) : P5 := match side with
  | .left => X 0^2-C r*X 1*X 3
  | .right => X 0^2+X 2^2

def componentSecond (side : Side) (r : ℂ) : P5 := match side with
  | .left => X 4+X 2^2
  | .right => X 4-C r*X 1*X 3

def componentIdeal (side : Side) (r ι : ℂ) : Ideal (SeedRing r ι) :=
  Ideal.span {Ideal.Quotient.mk _ (componentFirst side r),
    Ideal.Quotient.mk _ (componentSecond side r)}

abbrev ComponentQuotient (side : Side) (r ι : ℂ) := SeedRing r ι ⧸ componentIdeal side r ι

def ambientToComponent (side : Side) (r ι : ℂ) : P5 →ₐ[ℂ] ComponentQuotient side r ι :=
  (Ideal.Quotient.mkₐ ℂ (componentIdeal side r ι)).comp
    (Ideal.Quotient.mkₐ ℂ (equationsIdeal (smoothH ι) (smoothF r ι)))

theorem ambient_first (side : Side) (r ι : ℂ) :
    ambientToComponent side r ι (componentFirst side r)=0 := by
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact Ideal.subset_span (by simp [componentIdeal])

theorem ambient_second (side : Side) (r ι : ℂ) :
    ambientToComponent side r ι (componentSecond side r)=0 := by
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact Ideal.subset_span (by simp [componentIdeal])

theorem ambient_h (side : Side) (r ι : ℂ) : ambientToComponent side r ι (smoothH ι)=0 := by
  have hh : Ideal.Quotient.mk (equationsIdeal (smoothH ι) (smoothF r ι)) (smoothH ι)=0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp [equationsIdeal]))
  change Ideal.Quotient.mk _ (Ideal.Quotient.mk _ (smoothH ι))=0
  rw [hh,map_zero]

def variableIndex (j : Fin 4) : Fin 5 := j.castSucc

def inclusion : CP →ₐ[ℂ] P5 := rename variableIndex

theorem inclusion_quadric (side : Side) (r : ℂ) :
    inclusion (originalQuadric side r)=componentFirst side r := by
  cases side <;> simp [inclusion,variableIndex,originalQuadric,componentFirst]

theorem inclusion_cubic (ι : ℂ) : inclusion (originalCubic ι)=smoothH ι := by
  simp [inclusion,variableIndex,originalCubic,smoothH,smoothB,smoothA]
  ring

def originalToComponent (side : Side) (r ι : ℂ) :
    CP ⧸ originalCurveIdeal side r ι →ₐ[ℂ] ComponentQuotient side r ι :=
  Ideal.Quotient.liftₐ _ ((ambientToComponent side r ι).comp inclusion) (by
    intro p hp
    obtain ⟨a,b,hab⟩ := Ideal.mem_span_pair.mp hp
    rw [←hab,map_add,map_mul,map_mul]
    change _*ambientToComponent side r ι (inclusion (originalQuadric side r))+
      _*ambientToComponent side r ι (inclusion (originalCubic ι))=0
    rw [inclusion_quadric,inclusion_cubic,ambient_first,ambient_h]
    ring)

@[simp] theorem originalToComponent_mk (side : Side) (r ι : ℂ) (p : CP) :
    originalToComponent side r ι (Ideal.Quotient.mk (originalCurveIdeal side r ι) p)=
      ambientToComponent side r ι (inclusion p) := rfl

theorem originalToComponent_substitution (side : Side) (r ι : ℂ) (p : P5) :
    originalToComponent side r ι
      (Ideal.Quotient.mk (originalCurveIdeal side r ι) (originalSubstitution side r p))=
      ambientToComponent side r ι p := by
  have h : (originalToComponent side r ι).comp
      ((Ideal.Quotient.mkₐ ℂ (originalCurveIdeal side r ι)).comp (originalSubstitution side r))=
      ambientToComponent side r ι := by
    apply MvPolynomial.algHom_ext
    intro j
    have hw := ambient_second side r ι
    cases side <;> fin_cases j <;>
      simp [AlgHom.comp_apply,originalToComponent_mk,originalSubstitution,
        originalRestrictionValues,inclusion,variableIndex,Matrix.cons_val_succ,Fin.reduceSucc]
    · simp only [componentSecond,map_add,map_pow] at hw
      linear_combination -hw
    · simp only [componentSecond,map_sub,map_mul] at hw
      have hc : ambientToComponent .right r ι (C r)=
          algebraMap ℂ (ComponentQuotient .right r ι) r :=
        (ambientToComponent .right r ι).commutes r
      rw [hc] at hw
      linear_combination -hw
  exact congrArg (fun f : P5 →ₐ[ℂ] ComponentQuotient side r ι => f p) h

theorem actualRestriction_mk_original (side : Side) (r ι : ℂ) (p : P5) :
    seedRestriction side r ι (Ideal.Quotient.mk (equationsIdeal (smoothH ι) (smoothF r ι)) p)=
      originalCurveEquiv side r ι
        (Ideal.Quotient.mk (originalCurveIdeal side r ι) (originalSubstitution side r p)) := by
  rw [seedRestriction_mk,originalCurveEquiv_mk]
  congr 1
  exact congrArg (fun f : P5 →ₐ[ℂ] CP => f p) (coordinateMap_substitution side r).symm

theorem component_le_kernel (side : Side) (r ι : ℂ) :
    componentIdeal side r ι≤RingHom.ker (seedRestriction side r ι).toRingHom := by
  apply Ideal.span_le.mpr
  intro p hp
  rcases hp with rfl | ⟨rfl⟩
  · change seedRestriction side r ι (Ideal.Quotient.mk _ (componentFirst side r))=0
    rw [actualRestriction_mk_original]
    have hq : originalSubstitution side r (componentFirst side r)=originalQuadric side r := by
      cases side <;> simp [originalSubstitution,originalRestrictionValues,componentFirst,originalQuadric]
    rw [hq]
    have hz : Ideal.Quotient.mk (originalCurveIdeal side r ι) (originalQuadric side r)=0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp [originalCurveIdeal]))
    rw [hz,map_zero]
  · change seedRestriction side r ι (Ideal.Quotient.mk _ (componentSecond side r))=0
    rw [actualRestriction_mk_original]
    have hz : originalSubstitution side r (componentSecond side r)=0 := by
      cases side <;> simp [originalSubstitution,originalRestrictionValues,componentSecond]
    rw [hz,map_zero,map_zero]

/-- The normal-form restriction has exactly the original two-generator
component ideal as its kernel, including the right coordinate change. -/
theorem kernel_eq_componentIdeal (side : Side) (r ι : ℂ) :
    RingHom.ker (seedRestriction side r ι).toRingHom=componentIdeal side r ι := by
  apply le_antisymm _ (component_le_kernel side r ι)
  intro q hq
  obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective q
  have hh : seedRestriction side r ι (Ideal.Quotient.mk _ p)=0 := hq
  rw [actualRestriction_mk_original] at hh
  have ho : Ideal.Quotient.mk (originalCurveIdeal side r ι) (originalSubstitution side r p)=0 :=
    (originalCurveEquiv side r ι).injective (hh.trans (map_zero _).symm)
  have hc := congrArg (originalToComponent side r ι) ho
  rw [originalToComponent_substitution,map_zero] at hc
  exact Ideal.Quotient.eq_zero_iff_mem.mp hc

/-- Localizing the actual restriction introduces exactly the extension of
the chosen component ideal. No saturation or kernel condition is assumed. -/
theorem localized_kernel_eq_componentIdeal (side : Side) (r ι : ℂ)
    (t : Finset (Fin 3)) :
    RingHom.ker (CycleQ2CurveLocalizedRestriction.localRestrictionMap ℂ side r ι t)=
      (componentIdeal side r ι).map
        (algebraMap (SeedRing r ι) (CycleQ2CurveLocalizedRestriction.SL ℂ r ι t)) := by
  change RingHom.ker (IsLocalization.Away.map
    (CycleQ2CurveLocalizedRestriction.SL ℂ r ι t)
    (CycleQ2CurveLocalizedRestriction.RestrictedLocal ℂ side r ι t)
    (seedRestriction side r ι).toRingHom
    (CycleQ2CurveLocalizedRestriction.seedProduct ℂ r ι t))=_
  rw [CycleQ2LocalizationKernel.kernel_away,kernel_eq_componentIdeal]

end CycleQ2CurveRestrictionKernel

#print axioms CycleQ2CurveRestrictionKernel.kernel_eq_componentIdeal
#print axioms CycleQ2CurveRestrictionKernel.localized_kernel_eq_componentIdeal
end
end

/- Component: continuation_3/ModularGlobalCurveGluing.lean -/
section
/-! Graded local linkage sections glue into the actual global curve
restriction kernels over F109. Only the forward ideal-to-curve-kernel
inclusion is used; no orbit or global linkage-ideal comparison is assumed. -/

noncomputable section
set_option maxHeartbeats 300000
set_option maxRecDepth 20000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace CycleQ2ModularGlobalCurveGluing

open MvPolynomial CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations
  CycleQ2SegreTangentLocal CycleQ2CurveRestriction CycleQ2SeedLinkageIdeals
  CycleQ2SeedCechThreeOpen CycleQ2SeedCechLocalizedBasis CycleQ2SeedCechRestrictions
  CycleQ2SeedCechGlobalGluing CycleQ2SeedQuotientGrading
  CycleQ2ModularGlobalFactorSpaces CycleQ2ModularFactorChartExact

def threeSections {P : Fin 3 → Type*} (q0 : P 0) (q1 : P 1) (q2 : P 2) :
    (i : Fin 3) → P i := Fin.cases q0 (Fin.cases q1 (Fin.cases q2 (fun i => Fin.elim0 i)))

@[simp] theorem threeSections_zero {P : Fin 3 → Type*} (q0 : P 0) (q1 : P 1) (q2 : P 2) :
    threeSections q0 q1 q2 0=q0 := rfl
@[simp] theorem threeSections_one {P : Fin 3 → Type*} (q0 : P 0) (q1 : P 1) (q2 : P 2) :
    threeSections q0 q1 q2 1=q1 := rfl
@[simp] theorem threeSections_two {P : Fin 3 → Type*} (q0 : P 0) (q1 : P 1) (q2 : P 2) :
    threeSections q0 q1 q2 2=q2 := rfl

theorem compatible_of_two_differences (q0 : Chart {0}) (q1 : Chart {1}) (q2 : Chart {2})
    (h01 : restriction K 57 33 (by decide : ({1}:Finset (Fin 3))⊆{0,1}) q1-
      restriction K 57 33 (by decide : ({0}:Finset (Fin 3))⊆{0,1}) q0=0)
    (h02 : restriction K 57 33 (by decide : ({2}:Finset (Fin 3))⊆{0,2}) q2-
      restriction K 57 33 (by decide : ({0}:Finset (Fin 3))⊆{0,2}) q0=0) :
    Compatible K 57 33 (threeSections (P:=fun i => Chart {i}) q0 q1 q2) := by
  have hc01 (ab) : localizedCoordinates K 57 33 {1} q1 ab=
      localizedCoordinates K 57 33 {0} q0 ab := by
    have hh := congrArg (fun q => localizedCoordinates K 57 33 {0,1} q ab) h01
    simp only [map_sub,Pi.sub_apply,map_zero,Pi.zero_apply,coordinates_restriction] at hh
    exact sub_eq_zero.mp hh
  have hc02 (ab) : localizedCoordinates K 57 33 {2} q2 ab=
      localizedCoordinates K 57 33 {0} q0 ab := by
    have hh := congrArg (fun q => localizedCoordinates K 57 33 {0,2} q ab) h02
    simp only [map_sub,Pi.sub_apply,map_zero,Pi.zero_apply,coordinates_restriction] at hh
    exact sub_eq_zero.mp hh
  have hcoord (i : Fin 3) (ab) :
      localizedCoordinates K 57 33 {i} (threeSections (P:=fun i => Chart {i}) q0 q1 q2 i) ab=
      localizedCoordinates K 57 33 {0} q0 ab := by
    fin_cases i
    · rfl
    · exact hc01 ab
    · exact hc02 ab
  intro i j
  apply localizedCoordinates_injective K 57 33 {i,j}
  funext ab
  simp only [pairRestriction,secondPairRestriction,coordinates_restriction]
  exact (hcoord i ab).trans (hcoord j ab).symm

theorem scale_unit (side : Side) :
    IsUnit (CycleQ2CurveLocalizedRestriction.coordinateScale K side) := by
  cases side
  · exact isUnit_one
  · exact isUnit_iff_ne_zero.mpr (by decide : (2:K)≠0)

theorem local_ideal_restriction_zero (side : Side) (t : Finset (Fin 3))
    (q : Chart t)
    (hq : q∈(linkageIdeal side (57:K) 33).map (chartMap t)) :
    CycleQ2CurveLocalizedRestriction.localRestrictionMap K side 57 33 t q=0 := by
  have hle : (linkageIdeal side (57:K) 33).map (chartMap t) ≤
      RingHom.ker (CycleQ2CurveLocalizedRestriction.localRestrictionMap K side 57 33 t) := by
    apply Ideal.map_le_iff_le_comap.mpr
    intro z hz
    change CycleQ2CurveLocalizedRestriction.localRestrictionMap K side 57 33 t (chartMap t z)=0
    have hh := linkageIdeal_le_restrictionKernel side (57:K) 33 hz
    change seedRestriction side (57:K) 33 z=0 at hh
    calc
      _ = algebraMap (CurveRing side (57:K) 33)
          (CycleQ2CurveLocalizedRestriction.RestrictedLocal K side 57 33 t)
          (seedRestriction side (57:K) 33 z) :=
        CycleQ2CurveLocalizedRestriction.localRestrictionMap_algebraMap K side 57 33 t z
      _ = 0 := by rw [hh,map_zero]
  exact hle hq

theorem seedRestriction_zero_of_first_local_zero (side : Side) (q : A)
    (hq : CycleQ2CurveLocalizedRestriction.localRestrictionMap K side 57 33 {0}
      (chartMap {0} q)=0) : seedRestriction side (57:K) 33 q=0 := by
  let e := CycleQ2CurveLocalizedRestriction.baseOpenEquiv K side 57 33 {0}
    (scale_unit side)
  have h := congrArg e hq
  have hb : CycleQ2CurveLocalizedRestriction.baseOpenMap K side 57 33 {0}
      (scale_unit side) (chartMap {0} q)=0 := by
    exact h.trans (map_zero e)
  apply CycleQ2CurveCechGlobalGluing.localization_injective K side 57 33 {0}
  rw [map_zero]
  rw [←CycleQ2CurveLocalizedRestriction.baseOpenMap_algebraMap K side 57 33 {0}
    (scale_unit side) q]
  exact hb

theorem exists_global_curve_kernel_piece (side : Side) (d ch : ℕ)
    (q0 : Chart {0}) (q1 : Chart {1}) (q2 : Chart {2})
    (hq0 : ∀ ab, HasGrade ab ((d:ℤ),(ch:ZMod 3)) (localizedCoordinates K 57 33 {0} q0 ab))
    (hi0 : q0∈(linkageIdeal side (57:K) 33).map (chartMap {0}))
    (h01 : restriction K 57 33 (by decide : ({1}:Finset (Fin 3))⊆{0,1}) q1-
      restriction K 57 33 (by decide : ({0}:Finset (Fin 3))⊆{0,1}) q0=0)
    (h02 : restriction K 57 33 (by decide : ({2}:Finset (Fin 3))⊆{0,2}) q2-
      restriction K 57 33 (by decide : ({0}:Finset (Fin 3))⊆{0,2}) q0=0) :
    ∃ q : LinearMap.ker (seedRestrictionPiece side (57:K) 33 d ch),
      chartMap {0} q.val.val=q0 ∧ chartMap {1} q.val.val=q1 ∧ chartMap {2} q.val.val=q2 := by
  let qs := threeSections (P:=fun i => Chart {i}) q0 q1 q2
  have hcomp := compatible_of_two_differences q0 q1 q2 h01 h02
  obtain ⟨p,_hstd,hp,hglue⟩ := exists_homogeneous_polynomial_gluing K 57 33 qs hcomp
    ((d:ℤ),(ch:ZMod 3)) hq0
  have hpg : HG p (d,(ch:ZMod 3)) := (signedHomogeneous_iff K p _).mp hp
  let q : SeedPiece (57:K) 33 d ch :=
    ⟨Ideal.Quotient.mk (equationsIdeal (smoothH (33:K)) (smoothF (57:K) 33)) p,
      Submodule.mem_map.mpr ⟨p,hpg,rfl⟩⟩
  have hqzero : seedRestriction side (57:K) 33 q.val=0 := by
    apply seedRestriction_zero_of_first_local_zero side q.val
    have hzero := local_ideal_restriction_zero side {0} q0 hi0
    have he : chartMap {0} q.val=q0 := hglue 0
    rw [he]
    exact hzero
  have hmem : q∈LinearMap.ker (seedRestrictionPiece side (57:K) 33 d ch) := by
    change seedRestrictionPiece side (57:K) 33 d ch q=0
    apply Subtype.ext
    exact hqzero
  exact ⟨⟨q,hmem⟩,hglue 0,hglue 1,hglue 2⟩

end CycleQ2ModularGlobalCurveGluing

#print axioms CycleQ2ModularGlobalCurveGluing.exists_global_curve_kernel_piece
end
end

/- Component: continuation_3/cylinder_bridge/SeedLocalizedGradeLinear.lean -/
section
/-! Linear closure and restriction of the actual localized homogeneous grades. -/

noncomputable section
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2SeedLocalizedProjection

open MvPolynomial CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations CycleQ2SeedCechThreeOpen
  CycleQ2SeedCechLocalizedBasis CycleQ2SeedCechRestrictions CycleQ2SeedCechLinearCoordinates
  CycleQ2SeedQuotientGrading

variable (R : Type*) [CommRing R] [Nontrivial R]

theorem hasLocalGrade_zero (r ι : R) (s : Finset (Fin 3)) (d : Grade) :
    HasLocalGrade R r ι s d 0 := by
  intro ab e he
  simp

theorem hasLocalGrade_neg (r ι : R) (s : Finset (Fin 3)) (d : Grade)
    (q : SeedLocal R r ι s) (hq : HasLocalGrade R r ι s d q) :
    HasLocalGrade R r ι s d (-q) := by
  intro ab
  rw [map_neg,Pi.neg_apply]
  intro e he
  simp [hq ab e he]

theorem hasLocalGrade_sub (r ι : R) (s : Finset (Fin 3)) (d : Grade)
    (p q : SeedLocal R r ι s) (hp : HasLocalGrade R r ι s d p)
    (hq : HasLocalGrade R r ι s d q) : HasLocalGrade R r ι s d (p-q) := by
  rw [sub_eq_add_neg]
  exact hasLocalGrade_add R r ι s d p (-q) hp (hasLocalGrade_neg R r ι s d q hq)

theorem hasLocalGrade_R_smul (r ι : R) (s : Finset (Fin 3)) (d : Grade)
    (c : R) (q : SeedLocal R r ι s) (hq : HasLocalGrade R r ι s d q) :
    HasLocalGrade R r ι s d (c • q) := by
  intro ab
  rw [localizedCoordinates_R_smul,Pi.smul_apply]
  intro e he
  simp [AddMonoidAlgebra.coeff_smul,Finsupp.smul_apply,hq ab e he]

theorem hasLocalGrade_restriction (r ι : R) {s t : Finset (Fin 3)} (hst : s⊆t)
    (d : Grade) (q : SeedLocal R r ι s) (hq : HasLocalGrade R r ι s d q) :
    HasLocalGrade R r ι t d (restriction R r ι hst q) := by
  intro ab
  rw [coordinates_restriction]
  exact hq ab

def gradeSubmodule (r ι : R) (s : Finset (Fin 3)) (d : Grade) :
    Submodule R (SeedLocal R r ι s) where
  carrier := {q | HasLocalGrade R r ι s d q}
  zero_mem' := hasLocalGrade_zero R r ι s d
  add_mem' := fun hp hq => hasLocalGrade_add R r ι s d _ _ hp hq
  smul_mem' := fun c _ hq => hasLocalGrade_R_smul R r ι s d c _ hq

end CycleQ2SeedLocalizedProjection

#print axioms CycleQ2SeedLocalizedProjection.gradeSubmodule
end
end

/- Component: continuation_3/CurveRestrictionLocalGrading.lean -/
section
/-! # The actual localized restriction preserves degree

For global curve gluing it suffices to check the first base chart. The
right coordinate change scales its denominator by two; the inverse scalar
is included explicitly in the homogeneous numerator below.
-/

noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2CurveLocalizedRestriction

open MvPolynomial CycleQ2CurveRestriction CycleQ2SegreTangentLocal
  CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations

theorem baseOpenMap_first_homogeneous (side : Side) (r ι : ℂ)
    (q : SL ℂ r ι (seedOpen {0})) (g : CycleQ2SeedCechThreeOpen.LaurentGrade)
    (hq : ∀ ab, CycleQ2SeedCechThreeOpen.HasGrade ab g
      (CycleQ2SeedCechLocalizedBasis.localizedCoordinates ℂ r ι (seedOpen {0}) q ab)) :
    ∀ ab, CycleQ2CurveCechTwoOpen.HasDegree ab g.1
      (CycleQ2CurveCechLocalizedBasis.localizedCoordinates ℂ side r ι {0}
        (baseOpenMap ℂ side r ι {0} (complex_scale_unit side) q) ab) := by
  obtain ⟨n,p,hp,hn⟩ :=
    (CycleQ2SeedQuotientGrading.localized_homogeneous_iff_fraction ℂ r ι
      (seedOpen {0}) q g).mp hq
  let β := coordinateScale ℂ side
  let c : ℂ := (β^n)⁻¹
  let π : CurvePoly ℂ →ₐ[ℂ] CL ℂ side r ι {0} :=
    (IsScalarTower.toAlgHom ℂ (CurveRing side r ι) (CL ℂ side r ι {0})).comp
      (Ideal.Quotient.mkₐ ℂ (curveIdeal side r ι))
  have hπC (a : ℂ) : π (C a)=algebraMap ℂ (CL ℂ side r ι {0}) a := π.commutes a
  have hβ : β≠0 := (isUnit_iff_ne_zero.mp (complex_scale_unit side))
  have hunit : algebraMap ℂ (CL ℂ side r ι {0}) c *
      algebraMap ℂ (CL ℂ side r ι {0}) (β^n)=1 := by
    rw [←map_mul]
    simp only [c,inv_mul_cancel₀ (pow_ne_zero n hβ),map_one]
  have hd : (g + CycleQ2SeedQuotientGrading.baseGrade
      (n • CycleQ2SeedCechLocalization.openExponent (seedOpen {0}))).1=
      g.1 + CycleQ2CurveQuotientGrading.baseDegree
        (n • CycleQ2CurveCechLocalization.openExponent {0}) := by
    simp [CycleQ2SeedQuotientGrading.baseGrade,CycleQ2CurveQuotientGrading.baseDegree,
      CycleQ2SeedCechLocalization.openExponent,CycleQ2CurveCechLocalization.openExponent,
      seedOpen,baseIndex,Fin.sum_univ_succ,Matrix.cons_val_succ,Fin.reduceSucc]
  have hp' : CycleQ2CurveQuotientGrading.SignedHomogeneous ℂ (substitution side r p)
      (g.1 + CycleQ2CurveQuotientGrading.baseDegree
        (n • CycleQ2CurveCechLocalization.openExponent {0})) :=
    hd ▸ substitution_signedHomogeneous ℂ side r p _ hp
  have hp'' : CycleQ2CurveQuotientGrading.SignedHomogeneous ℂ (C c*substitution side r p)
      (g.1 + CycleQ2CurveQuotientGrading.baseDegree
        (n • CycleQ2CurveCechLocalization.openExponent {0})) := by
    intro e he
    apply hp' e
    rw [coeff_C_mul] at he
    exact (mul_ne_zero_iff.mp he).2
  apply (CycleQ2CurveQuotientGrading.localized_homogeneous_iff_fraction ℂ side r ι {0}
    (baseOpenMap ℂ side r ι {0} (complex_scale_unit side) q) g.1).mpr
  refine ⟨n,C c*substitution side r p,hp'',?_⟩
  have hh := congrArg (baseOpenMap ℂ side r ι {0} (complex_scale_unit side)) hn
  simp only [map_mul,baseOpenMap_algebraMap,seedRestriction_mk] at hh
  have hden : seedRestriction side r ι
      (algebraMap (SB ℂ) (SeedRing r ι)
        (CycleQ2SeedCechLocalization.baseProduct ℂ (seedOpen {0}) ^ n))=
      algebraMap ℂ (CurveRing side r ι) (β^n)*
        algebraMap (CB ℂ) (CurveRing side r ι)
          (CycleQ2CurveCechLocalization.baseProduct ℂ {0} ^ n) := by
    simp only [map_pow]
    change (curveProduct ℂ side r ι (seedOpen {0}))^n=_
    rw [curveProduct_baseOpen]
    simp only [Finset.card_singleton,pow_one,mul_pow]
    rfl
  rw [hden,map_mul] at hh
  have hscalar : algebraMap (CurveRing side r ι) (CL ℂ side r ι {0})
      (algebraMap ℂ (CurveRing side r ι) (β^n))=
      algebraMap ℂ (CL ℂ side r ι {0}) (β^n) :=
    (IsScalarTower.algebraMap_apply ℂ (CurveRing side r ι) (CL ℂ side r ι {0}) (β^n)).symm
  rw [hscalar] at hh
  change _ = π (substitution side r p) at hh
  change _ = π (C c*substitution side r p)
  rw [map_mul,hπC]
  calc
    _ = (algebraMap ℂ (CL ℂ side r ι {0}) c *
        algebraMap ℂ (CL ℂ side r ι {0}) (β^n)) *
        (baseOpenMap ℂ side r ι {0} (complex_scale_unit side) q *
          algebraMap (CurveRing side r ι) (CL ℂ side r ι {0})
            (algebraMap (CB ℂ) (CurveRing side r ι)
              (CycleQ2CurveCechLocalization.baseProduct ℂ {0} ^ n))) := by rw [hunit,one_mul]
    _ = algebraMap ℂ (CL ℂ side r ι {0}) c * π (substitution side r p) := by
      rw [←hh]
      ring

end CycleQ2CurveLocalizedRestriction

#print axioms CycleQ2CurveLocalizedRestriction.baseOpenMap_first_homogeneous
end
end

/- Component: continuation_3/SeedLinkageRestrictionKernel.lean -/
section
/-! On every nonempty coordinate open, the actual fixed-character linkage
ideal is exactly the kernel of restriction to the chosen actual curve. -/

noncomputable section
set_option maxHeartbeats 100000
set_option maxRecDepth 20000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2SeedLinkageRestrictionKernel

open MvPolynomial CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations
  CycleQ2SegreTangentLocal CycleQ2CurveRestriction CycleQ2SeedLinkageIdeals
  CycleQ2SeedLinkagePrincipal CycleQ2SeedLinkageOrbitCover CycleQ2SeedLinkageComponents
  CycleQ2SeedLinkageOrbitKernel CycleQ2SeedCechThreeOpen CycleQ2SeedCechLocalizedBasis

theorem component_one_global_eq (s : Side) (r ι : ℂ) :
    CycleQ2LinkageComponentDecomposition.componentIdeal (1:SeedRing r ι)
      (linkageA r ι) (orbitB s r ι) (linkageC r ι) (orbitD s r ι)=
      CycleQ2CurveRestrictionKernel.componentIdeal s r ι := by
  cases s <;>
    simp only [CycleQ2LinkageComponentDecomposition.componentIdeal,
      CycleQ2LinkageComponentDecomposition.componentGenerator,Matrix.range_cons_cons_empty,
      orbitB,orbitD,linkageA,linkageB,linkageC,linkageD,
      CycleQ2CurveRestrictionKernel.componentIdeal,CycleQ2CurveRestrictionKernel.componentFirst,
      CycleQ2CurveRestrictionKernel.componentSecond,quotientMap,one_mul,one_pow,
      map_sub,map_add,map_mul,map_pow,map_neg,neg_neg,sub_neg_eq_add,sub_eq_add_neg]

theorem localComponent_one_eq (s : Side) (r ι : ℂ) (t : Finset (Fin 3)) :
    localComponent s r ι t 1=
      (CycleQ2CurveRestrictionKernel.componentIdeal s r ι).map
        (algebraMap (SeedRing r ι) (SeedLocal ℂ r ι t)) := by
  rw [←component_one_global_eq s r ι]
  have h := @CycleQ2LinkageComponentAlgebra.map_componentIdeal
    (SeedRing r ι) (SeedLocal ℂ r ι t)
    (inferInstance : CommRing (SeedRing r ι)) (inferInstance : CommRing (SeedLocal ℂ r ι t))
    (algebraMap (SeedRing r ι) (SeedLocal ℂ r ι t)) 1
    (linkageA r ι) (orbitB s r ι) (linkageC r ι) (orbitD s r ι)
  simpa only [localComponent,map_one (localScalar r ι t),
    map_one (algebraMap (SeedRing r ι) (SeedLocal ℂ r ι t))] using h.symm

 theorem homogeneous_mem_linkage_iff_restriction_zero (s : Side) (r ι : ℂ)
    (hr : r≠0) (hι : ι≠0) (hι1 : ι≠1) (t : Finset (Fin 3)) (ht : t.Nonempty)
    (q : SeedLocal ℂ r ι t) (g : LaurentGrade)
    (hq : ∀ ab, HasGrade ab g (localizedCoordinates ℂ r ι t q ab)) :
    q∈localLinkageIdeal s r ι t ↔
      CycleQ2CurveLocalizedRestriction.localRestrictionMap ℂ s r ι t q=0 := by
  rw [homogeneous_mem_linkage_iff_component s r ι hr hι hι1 t ht q g hq,
    localComponent_one_eq,← CycleQ2CurveRestrictionKernel.localized_kernel_eq_componentIdeal]
  rfl

end CycleQ2SeedLinkageRestrictionKernel

#print axioms CycleQ2SeedLinkageRestrictionKernel.homogeneous_mem_linkage_iff_restriction_zero
end
end

/- Component: continuation_3/CurveRestrictionGluing.lean -/
section
/-! # Gluing the actual restrictions from all three seed charts -/

noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2CurveRestrictionGluing

open CycleQ2CurveRestriction CycleQ2SegreTangentLocal
  CycleQ2CurveLocalizedRestriction

theorem natural_apply (side : Side) (r ι : ℂ)
    {s t : Finset (Fin 3)} (hst : s⊆t) (q : SL ℂ r ι s) :
    CycleQ2CurveLocalizedRestriction.restriction ℂ side r ι hst
      (localRestrictionMap ℂ side r ι s q)=
      localRestrictionMap ℂ side r ι t (CycleQ2SeedCechRestrictions.restriction ℂ r ι hst q) :=
  congrArg (fun f : SL ℂ r ι s →+* RestrictedLocal ℂ side r ι t => f q)
    (localRestrictionMap_natural ℂ side r ι hst)

theorem base_natural_apply (side : Side) (r ι : ℂ)
    {s t : Finset (Fin 2)} (hst : s⊆t) (q : SL ℂ r ι (seedOpen s)) :
    CycleQ2CurveCechRestrictions.restriction ℂ side r ι hst
      (baseOpenMap ℂ side r ι s (complex_scale_unit side) q)=
      baseOpenMap ℂ side r ι t (complex_scale_unit side)
        (CycleQ2SeedCechRestrictions.restriction ℂ r ι (Finset.image_subset_image hst) q) :=
  congrArg (fun f : SL ℂ r ι (seedOpen s) →+* CL ℂ side r ι t => f q)
    (baseOpenMap_natural ℂ side r ι hst (complex_scale_unit side))

/-- Compatibility on the two indicated overlaps produces one original
homogeneous curve polynomial agreeing with all three actual restrictions. -/
theorem exists_homogeneous_gluing (side : Side) (r ι : ℂ)
    (q0 : SL ℂ r ι {0}) (q1 : SL ℂ r ι {1}) (q2 : SL ℂ r ι {2})
    (g : CycleQ2SeedCechThreeOpen.LaurentGrade)
    (hg0 : ∀ ab,CycleQ2SeedCechThreeOpen.HasGrade ab g
      (CycleQ2SeedCechLocalizedBasis.localizedCoordinates ℂ r ι {0} q0 ab))
    (h02 : localRestrictionMap ℂ side r ι {0,2}
        (CycleQ2SeedCechRestrictions.restriction ℂ r ι
          (show ({0}:Finset (Fin 3))⊆{0,2} by decide) q0)=
      localRestrictionMap ℂ side r ι {0,2}
        (CycleQ2SeedCechRestrictions.restriction ℂ r ι
          (show ({2}:Finset (Fin 3))⊆{0,2} by decide) q2))
    (h12 : localRestrictionMap ℂ side r ι {1,2}
        (CycleQ2SeedCechRestrictions.restriction ℂ r ι
          (show ({1}:Finset (Fin 3))⊆{1,2} by decide) q1)=
      localRestrictionMap ℂ side r ι {1,2}
        (CycleQ2SeedCechRestrictions.restriction ℂ r ι
          (show ({2}:Finset (Fin 3))⊆{1,2} by decide) q2)) :
    ∃ p : CurvePoly ℂ, Standard side p ∧
      CycleQ2CurveQuotientGrading.SignedHomogeneous ℂ p g.1 ∧
      algebraMap (CurveRing side r ι) (RestrictedLocal ℂ side r ι {0})
        (Ideal.Quotient.mk (curveIdeal side r ι) p)=localRestrictionMap ℂ side r ι {0} q0 ∧
      algebraMap (CurveRing side r ι) (RestrictedLocal ℂ side r ι {1})
        (Ideal.Quotient.mk (curveIdeal side r ι) p)=localRestrictionMap ℂ side r ι {1} q1 ∧
      algebraMap (CurveRing side r ι) (RestrictedLocal ℂ side r ι {2})
        (Ideal.Quotient.mk (curveIdeal side r ι) p)=localRestrictionMap ℂ side r ι {2} q2 := by
  let c0 := baseOpenMap ℂ side r ι {0} (complex_scale_unit side) q0
  let c1 := baseOpenMap ℂ side r ι {1} (complex_scale_unit side) q2
  have hbase : CycleQ2CurveCechRestrictions.restriction ℂ side r ι
      (show ({0}:Finset (Fin 2))⊆{0,1} by decide) c0=
      CycleQ2CurveCechRestrictions.restriction ℂ side r ι
        (show ({1}:Finset (Fin 2))⊆{0,1} by decide) c1 := by
    rw [show c0=baseOpenMap ℂ side r ι {0} (complex_scale_unit side) q0 from rfl,
      show c1=baseOpenMap ℂ side r ι {1} (complex_scale_unit side) q2 from rfl,
      base_natural_apply,base_natural_apply]
    exact congrArg (baseOpenEquiv ℂ side r ι {0,1} (complex_scale_unit side)) h02
  obtain ⟨p,hp,hpg,hp0,hp2⟩ := CycleQ2CurvePairGluing.exists_homogeneous_gluing
    ℂ side r ι c0 c1 hbase g.1 (baseOpenMap_first_homogeneous side r ι q0 g hg0)
  have h0 : algebraMap (CurveRing side r ι) (RestrictedLocal ℂ side r ι {0})
      (Ideal.Quotient.mk (curveIdeal side r ι) p)=localRestrictionMap ℂ side r ι {0} q0 := by
    apply (baseOpenEquiv ℂ side r ι {0} (complex_scale_unit side)).injective
    calc
      _ = algebraMap (CurveRing side r ι) (CL ℂ side r ι {0})
          (Ideal.Quotient.mk (curveIdeal side r ι) p) :=
        (baseOpenEquiv ℂ side r ι {0} (complex_scale_unit side)).commutes _
      _ = _ := hp0
  have h2 : algebraMap (CurveRing side r ι) (RestrictedLocal ℂ side r ι {2})
      (Ideal.Quotient.mk (curveIdeal side r ι) p)=localRestrictionMap ℂ side r ι {2} q2 := by
    apply (baseOpenEquiv ℂ side r ι {1} (complex_scale_unit side)).injective
    calc
      _ = algebraMap (CurveRing side r ι) (CL ℂ side r ι {1})
          (Ideal.Quotient.mk (curveIdeal side r ι) p) :=
        (baseOpenEquiv ℂ side r ι {1} (complex_scale_unit side)).commutes _
      _ = _ := hp2
  refine ⟨p,hp,hpg,h0,?_,h2⟩
  apply CycleQ2CurveOpenFaithfulness.middle_to_overlap_injective side r ι
  rw [restriction_algebraMap]
  calc
    _ = CycleQ2CurveLocalizedRestriction.restriction ℂ side r ι
        (show ({2}:Finset (Fin 3))⊆{1,2} by decide)
        (algebraMap (CurveRing side r ι) (RestrictedLocal ℂ side r ι {2})
          (Ideal.Quotient.mk (curveIdeal side r ι) p)) :=
      (restriction_algebraMap ℂ side r ι _ _).symm
    _ = CycleQ2CurveLocalizedRestriction.restriction ℂ side r ι
        (show ({2}:Finset (Fin 3))⊆{1,2} by decide)
        (localRestrictionMap ℂ side r ι {2} q2) := congrArg _ h2
    _ = localRestrictionMap ℂ side r ι {1,2}
        (CycleQ2SeedCechRestrictions.restriction ℂ r ι
          (show ({2}:Finset (Fin 3))⊆{1,2} by decide) q2) := natural_apply _ _ _ _ _
    _ = localRestrictionMap ℂ side r ι {1,2}
        (CycleQ2SeedCechRestrictions.restriction ℂ r ι
          (show ({1}:Finset (Fin 3))⊆{1,2} by decide) q1) := h12.symm
    _ = _ := (natural_apply _ _ _ _ _).symm

end CycleQ2CurveRestrictionGluing

#print axioms CycleQ2CurveRestrictionGluing.exists_homogeneous_gluing
end
end
