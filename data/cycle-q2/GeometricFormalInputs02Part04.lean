import Proposal.GeometricFormalInputs02Part03

/-! Continuation of GeometricFormalInputs02.lean; complete source components and declarations. -/

set_option Elab.async false

/- Component: pole_reduction/ActualResidueClosure.lean -/
section
/-!
The direct q2 residue-primitive closure bound to actual polynomial fraction
fields, actual coordinate partial derivatives, and actual legal-denominator
regularity. Existence of the residue primitive is deliberately not asserted.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section

namespace CycleQ2ActualResidueClosure

open MvPolynomial HodgeComputer CycleQ2Bridge CycleQ2Regularity
open HoldoutConstruction SplitHigherResidue CycleQ2ResidueClosure
open scoped BigOperators

variable {n : ℕ}

local instance rationalFunctionRatAlgebra (n : ℕ) : Algebra ℚ (RationalFunction n) :=
  DivisionRing.toRatAlgebra

local instance rationalFunctionRatModule (n : ℕ) : Module ℚ (RationalFunction n) :=
  Algebra.toModule

local instance rationalFunctionIntAlgebra (n : ℕ) : Algebra ℤ (RationalFunction n) :=
  Ring.toIntAlgebra _

/-- The actual extended partial, in the integer-linear trusted residue API. -/
def partialZ (n : ℕ) (i : Fin (n + 1)) :
    Derivation ℤ (RationalFunction n) (RationalFunction n) :=
  Derivation.mk' (rationalPartial n i).toLinearMap.toAddMonoidHom.toIntLinearMap
    (by
      intro x y
      exact (rationalPartial n i).leibniz x y)

@[simp] theorem partialZ_apply (i : Fin (n + 1)) (z : RationalFunction n) :
    partialZ n i z = rationalPartial n i z := rfl

@[simp] theorem partialZ_map (i : Fin (n + 1)) (P : AmbientPoly n) :
    partialZ n i (polynomialMap n P) = polynomialMap n (pderiv i P) :=
  rationalPartial_map i P

theorem partialZ_commute (i j : Fin (n + 1)) :
    Function.Commute (partialZ n i) (partialZ n j) :=
  rationalPartials_commute i j

/-- The actual ambient tangent derivations, with coordinate zero eliminated. -/
def actualTangent (F : AmbientPoly n) (j : Fin n) :
    Derivation ℤ (RationalFunction n) (RationalFunction n) :=
  ambientTangent (partialZ n 0) (fun i : Fin n => partialZ n i.succ)
    (polynomialMap n F) j

@[simp] theorem actualTangent_apply (F : AmbientPoly n) (j : Fin n)
    (z : RationalFunction n) :
    actualTangent F j z = rationalPartial n j.succ z -
      polynomialMap n (pderiv j.succ F) / polynomialMap n (pderiv 0 F) *
        rationalPartial n 0 z := by
  simp only [actualTangent, ambientTangent_apply, partialZ_apply, rationalPartial_map]

/-- The actual second normal source for the polynomial numerator. -/
def actualNormalSource (F A : AmbientPoly n) : RationalFunction n :=
  normalSourceTwo (polynomialMap n A) (polynomialMap n (pderiv 0 A))
    (polynomialMap n (pderiv 0 (pderiv 0 A)))
    (polynomialMap n (pderiv 0 F))
    (polynomialMap n (pderiv 0 (pderiv 0 F)))
    (polynomialMap n (pderiv 0 (pderiv 0 (pderiv 0 F))))

def actualResidueExpression (F A : AmbientPoly n) (w : Fin n → RationalFunction n) :
    RationalFunction n :=
  actualNormalSource F A +
    residueDivergence (actualTangent F) (polynomialMap n (pderiv 0 F)) w

/-- The explicit ambient rational vector field supplied by a lifted residue primitive. -/
def actualClosureVector (F A : AmbientPoly n) (w : Fin n → RationalFunction n) :
    Fin (n + 1) → RationalFunction n :=
  Fin.cases
    (closureNormal (partialZ n 0) (fun i : Fin n => partialZ n i.succ)
      (polynomialMap n F) (polynomialMap n A) w)
    (closureTangent (polynomialMap n F) w)

theorem actualClosureVector_zero (F A : AmbientPoly n)
    (w : Fin n → RationalFunction n) :
    actualClosureVector F A w 0 =
      polynomialMap n A / (2 * polynomialMap n (pderiv 0 F)) +
      polynomialMap n F *
        (rationalPartial n 0 (polynomialMap n A / polynomialMap n (pderiv 0 F)) /
          (2 * polynomialMap n (pderiv 0 F)) -
          ∑ i, polynomialMap n (pderiv i.succ F) * w i /
            polynomialMap n (pderiv 0 F)) := by
  simp only [actualClosureVector, Fin.cases_zero, closureNormal,
    partialZ_apply, rationalPartial_map]

@[simp] theorem actualClosureVector_succ (F A : AmbientPoly n)
    (w : Fin n → RationalFunction n) (i : Fin n) :
    actualClosureVector F A w i.succ = polynomialMap n F * w i := rfl

/-- The actual protected rational defect equals f² times the actual residue expression. -/
theorem actualClosure_defect (F A : AmbientPoly n)
    (w : Fin n → RationalFunction n) (hg : pderiv 0 F ≠ 0) :
    rationalDefect F A 2 (actualClosureVector F A w) =
      polynomialMap n F ^ 2 * actualResidueExpression F A w := by
  have ht : actualTangent F = ambientTangent (partialZ n 0)
      (fun i : Fin n => partialZ n i.succ) (polynomialMap n F) := rfl
  unfold actualResidueExpression
  rw [ht]
  have h := closure_defect_of_commute (partialZ n 0)
    (fun i : Fin n => partialZ n i.succ) (polynomialMap n F) (polynomialMap n A) w
    (by simpa only [partialZ_map] using polynomialMap_ne_zero hg)
    (fun i => partialZ_commute 0 i.succ)
  simpa only [rationalDefect, HodgeTestbed.Conic.fieldAction_apply,
    HodgeTestbed.Conic.fieldDivergence, Fin.sum_univ_succ,
    actualClosureVector, Fin.cases_zero, Fin.cases_succ, partialZ_apply,
    rationalPartial_map, actualNormalSource,
    Nat.cast_ofNat] using h

theorem actualClosure_defect_of_residue (F A : AmbientPoly n)
    (w : Fin n → RationalFunction n) (t : RationalFunction n)
    (hg : pderiv 0 F ≠ 0)
    (hres : actualResidueExpression F A w = polynomialMap n F * t) :
    rationalDefect F A 2 (actualClosureVector F A w) = polynomialMap n F ^ 3 * t := by
  rw [actualClosure_defect F A w hg, hres]
  ring

private theorem regular_two_inv (F : AmbientPoly n) :
    RegularAlong F (2 : RationalFunction n)⁻¹ := by
  have hu : IsUnit (2 : AmbientPoly n) := by
    simpa only [map_ofNat] using (isUnit_iff_ne_zero.mpr (by norm_num : (2 : ℂ) ≠ 0)).map
      (C : ℂ →+* AmbientPoly n)
  simpa only [map_ofNat] using
    regular_inv_polynomial F 2 (by norm_num) hu.isRelPrime_right

private theorem regular_div_normal {F : AmbientPoly n} {z : RationalFunction n}
    (hz : RegularAlong F z) (hg : pderiv 0 F ≠ 0)
    (hlegal : IsRelPrime F (pderiv 0 F)) :
    RegularAlong F (z / polynomialMap n (pderiv 0 F)) := by
  simpa only [div_eq_mul_inv] using
    hz.mul (regular_inv_polynomial F _ hg hlegal)

private theorem regular_div_two_normal {F : AmbientPoly n} {z : RationalFunction n}
    (hz : RegularAlong F z) (hg : pderiv 0 F ≠ 0)
    (hlegal : IsRelPrime F (pderiv 0 F)) :
    RegularAlong F (z / (2 * polynomialMap n (pderiv 0 F))) := by
  simpa only [div_eq_mul_inv, mul_inv, mul_assoc] using
    (hz.mul (regular_two_inv F)).mul (regular_inv_polynomial F _ hg hlegal)

theorem regular_actualTangent {F : AmbientPoly n} {z : RationalFunction n}
    (hz : RegularAlong F z) (hg : pderiv 0 F ≠ 0)
    (hlegal : IsRelPrime F (pderiv 0 F)) (j : Fin n) :
    RegularAlong F (actualTangent F j z) := by
  rw [actualTangent_apply]
  exact (hz.rationalPartial j.succ).sub
    ((regular_div_normal (regular_polynomial F _) hg hlegal).mul
      (hz.rationalPartial 0))

theorem regular_actualNormalSource (F A : AmbientPoly n)
    (hg : pderiv 0 F ≠ 0) (hlegal : IsRelPrime F (pderiv 0 F)) :
    RegularAlong F (actualNormalSource F A) := by
  have hh := normalSourceTwo_eq_derivative (partialZ n 0)
    (polynomialMap n A) (polynomialMap n (pderiv 0 F)) (polynomialMap_ne_zero hg)
  simp only [partialZ_apply, rationalPartial_map] at hh
  unfold actualNormalSource
  rw [hh]
  exact (regular_div_two_normal
    ((regular_div_normal (regular_polynomial F A) hg hlegal).rationalPartial 0)
    hg hlegal).rationalPartial 0

theorem regular_actualResidueExpression (F A : AmbientPoly n)
    (w : Fin n → RationalFunction n) (hg : pderiv 0 F ≠ 0)
    (hlegal : IsRelPrime F (pderiv 0 F))
    (hw : ∀ j, RegularAlong F (w j)) :
    RegularAlong F (actualResidueExpression F A w) := by
  unfold actualResidueExpression
  apply (regular_actualNormalSource F A hg hlegal).add
  unfold residueDivergence HoldoutConstruction.fieldDivergence
  exact (RegularAlong.sum Finset.univ _ (fun i _ =>
    regular_actualTangent (hw i) hg hlegal i)).sub
    (regular_div_normal (RegularAlong.sum Finset.univ _ (fun i _ =>
      (hw i).mul (regular_actualTangent (regular_polynomial F _) hg hlegal i)))
      hg hlegal)

/-- Every output component has a genuine denominator relatively prime to F. -/
theorem regular_actualClosureVector (F A : AmbientPoly n)
    (w : Fin n → RationalFunction n) (hg : pderiv 0 F ≠ 0)
    (hlegal : IsRelPrime F (pderiv 0 F))
    (hw : ∀ j, RegularAlong F (w j)) (i : Fin (n + 1)) :
    RegularAlong F (actualClosureVector F A w i) := by
  induction i using Fin.cases with
  | zero =>
    rw [actualClosureVector_zero]
    exact (regular_div_two_normal (regular_polynomial F A) hg hlegal).add
      ((regular_polynomial F F).mul
        ((regular_div_two_normal
          ((regular_div_normal (regular_polynomial F A) hg hlegal).rationalPartial 0)
          hg hlegal).sub
          (RegularAlong.sum Finset.univ _ (fun j _ =>
            regular_div_normal ((regular_polynomial F _).mul (hw j)) hg hlegal))))
  | succ j =>
    rw [actualClosureVector_succ]
    exact (regular_polynomial F F).mul (hw j)

end CycleQ2ActualResidueClosure

#print axioms CycleQ2ActualResidueClosure.actualClosure_defect
#print axioms CycleQ2ActualResidueClosure.regular_actualClosureVector
end
end


/- Component: pole_reduction/HypersurfaceDerivations.lean -/
section
/-!
# Actual tangent derivations of the protected affine cone

The coordinate ring is the actual quotient C[Z0,...,Z5]/(F), and its
function field is its actual fraction field. This is the dimension-five
affine cone function field, not the dimension-four projective function field.
The trusted generic quotient/fraction derivation construction is specialized
to these rings, with all its hypotheses proved for the exact protected F.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace CycleQ2Hypersurface

open MvPolynomial HodgeComputer

abbrev ConeCoordinateRing := AmbientPoly 5 ⧸ Ideal.span {HodgeSubmission.F}

instance coneCoordinateRing_isDomain : IsDomain ConeCoordinateRing :=
  CycleQ2ExactIrreducible.protected_F_quotient_isDomain

abbrev ConeFunctionField := FractionRing ConeCoordinateRing

local instance coneFunctionFieldIntAlgebra : Algebra ℤ ConeFunctionField :=
  Ring.toIntAlgebra _

/-- Actual projection to the protected cone's coordinate ring. -/
def coneProjection : AmbientPoly 5 →+* ConeCoordinateRing := Ideal.Quotient.mk _

theorem coneProjection_surjective : Function.Surjective coneProjection :=
  Ideal.Quotient.mk_surjective

theorem coneProjection_kernel (P : AmbientPoly 5) :
    coneProjection P = 0 ↔ HodgeSubmission.F ∣ P := by
  simp only [coneProjection, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]

/-- Actual polynomial class in the protected cone's function field. -/
def coneMap : AmbientPoly 5 →+* ConeFunctionField :=
  (algebraMap ConeCoordinateRing ConeFunctionField).comp coneProjection

theorem coneMap_kernel (P : AmbientPoly 5) :
    coneMap P = 0 ↔ HodgeSubmission.F ∣ P := by
  constructor
  · intro h
    apply (coneProjection_kernel P).mp
    apply IsFractionRing.injective ConeCoordinateRing ConeFunctionField
    simpa only [coneMap, RingHom.comp_apply, map_zero] using h
  · intro h
    change algebraMap ConeCoordinateRing ConeFunctionField (coneProjection P) = 0
    rw [(coneProjection_kernel P).mpr h, map_zero]

@[simp] theorem coneMap_F : coneMap HodgeSubmission.F = 0 :=
  (coneMap_kernel _).mpr (dvd_refl _)

/-- A concrete smooth point on the protected affine cone. -/
def normalPoint : Fin 6 → ℂ := ![1, Complex.I, 0, 0, 0, 0]

@[simp] theorem normalPoint_zero : normalPoint 0 = 1 := rfl
@[simp] theorem normalPoint_one : normalPoint 1 = Complex.I := rfl
@[simp] theorem normalPoint_two : normalPoint 2 = 0 := rfl
@[simp] theorem normalPoint_three : normalPoint 3 = 0 := rfl
@[simp] theorem normalPoint_four : normalPoint 4 = 0 := rfl
@[simp] theorem normalPoint_five : normalPoint 5 = 0 := rfl

theorem eval_normalPoint_F : eval normalPoint HodgeSubmission.F = 0 := by
  have hI : Complex.I ^ 6 = (-1 : ℂ) := by
    calc
      _ = (Complex.I ^ 2) ^ 3 := by ring
      _ = -1 := by rw [Complex.I_sq]; norm_num
  norm_num [HodgeSubmission.F, hI]

theorem eval_normalPoint_partial :
    eval normalPoint (pderiv 0 HodgeSubmission.F) = 6 := by
  rw [CycleQ2ExactNonsingular.eval_pderiv_F]
  norm_num [CycleQ2ExactNonsingular.gradientValue]

theorem protected_F_not_dvd_normal :
    ¬ HodgeSubmission.F ∣ pderiv 0 HodgeSubmission.F := by
  intro h
  have hh := map_dvd (eval normalPoint) h
  rw [eval_normalPoint_F, eval_normalPoint_partial] at hh
  norm_num at hh

/-- The normal derivative is nonzero in the actual cone function field. -/
theorem normal_ne_zero : coneMap (pderiv 0 HodgeSubmission.F) ≠ 0 := by
  intro h
  exact protected_F_not_dvd_normal ((coneMap_kernel _).mp h)

/-- Polynomial coordinate partials in the integer-linear interface used by
the trusted residue derivation construction. -/
def polynomialPartial (i : Fin 6) : Derivation ℤ (AmbientPoly 5) (AmbientPoly 5) :=
  (MvPolynomial.pderiv i).restrictScalars ℤ

@[simp] theorem polynomialPartial_apply (i : Fin 6) (P : AmbientPoly 5) :
    polynomialPartial i P = pderiv i P := rfl

theorem polynomialPartials_commute (i j : Fin 6) (P : AmbientPoly 5) :
    polynomialPartial i (polynomialPartial j P) =
      polynomialPartial j (polynomialPartial i P) :=
  CycleQ2Regularity.polynomial_partials_commute i j P

/-- The five actual tangent derivations, obtained by descent through (F)
followed by fraction-field extension. Coordinate zero is the eliminated normal. -/
def coneTangent (j : Fin 5) : Derivation ℤ ConeFunctionField ConeFunctionField :=
  HoldoutConstruction.residueTangent (K := ConeFunctionField)
    coneProjection coneProjection_surjective (polynomialPartial 0)
    (polynomialPartial j.succ) HodgeSubmission.F coneProjection_kernel normal_ne_zero

/-- The actual tangent derivative has the implicit-coordinate formula on
every polynomial class. -/
theorem coneTangent_apply (j : Fin 5) (P : AmbientPoly 5) :
    coneTangent j (coneMap P) = coneMap (pderiv j.succ P) -
      coneMap (pderiv j.succ HodgeSubmission.F) /
        coneMap (pderiv 0 HodgeSubmission.F) * coneMap (pderiv 0 P) :=
  HoldoutConstruction.residueTangent_apply (K := ConeFunctionField)
    coneProjection coneProjection_surjective (polynomialPartial 0)
    (polynomialPartial j.succ) HodgeSubmission.F coneProjection_kernel normal_ne_zero P

@[simp] theorem coneTangent_F (j : Fin 5) :
    coneTangent j (coneMap HodgeSubmission.F) = 0 := by
  rw [coneMap_F, map_zero]

/-- All five constructed tangent derivations commute on the entire actual
cone function field; no derivative-compatibility assumption remains. -/
theorem coneTangents_commute (i j : Fin 5) :
    Function.Commute (coneTangent i) (coneTangent j) :=
  HoldoutConstruction.residueTangent_commute (K := ConeFunctionField)
    coneProjection coneProjection_surjective (polynomialPartial 0)
    (polynomialPartial i.succ) (polynomialPartial j.succ) HodgeSubmission.F
    coneProjection_kernel normal_ne_zero (polynomialPartials_commute i.succ 0)
    (polynomialPartials_commute j.succ 0) (polynomialPartials_commute i.succ j.succ)

@[simp] theorem coneTangent_constant (j : Fin 5) (c : ℂ) :
    coneTangent j (coneMap (C c)) = 0 := by
  rw [coneTangent_apply]
  simp

/-- The independent coordinate classes have the expected Kronecker derivatives. -/
theorem coneTangent_coordinate (i j : Fin 5) :
    coneTangent i (coneMap (X j.succ)) = if j = i then 1 else 0 := by
  rw [coneTangent_apply]
  simp [pderiv_X, Pi.single_apply, Fin.succ_ne_zero]

/-- The eliminated coordinate differentiates by the implicit equation. -/
theorem coneTangent_normalCoordinate (i : Fin 5) :
    coneTangent i (coneMap (X 0)) =
      -coneMap (pderiv i.succ HodgeSubmission.F) /
        coneMap (pderiv 0 HodgeSubmission.F) := by
  rw [coneTangent_apply]
  simp [pderiv_X, Pi.single_apply, Fin.succ_ne_zero, div_eq_mul_inv]

end CycleQ2Hypersurface

#print axioms CycleQ2Hypersurface.normal_ne_zero
#print axioms CycleQ2Hypersurface.coneTangent_apply
#print axioms CycleQ2Hypersurface.coneTangents_commute
end
end


/- Component: pole_reduction/RegularResidue.lean -/
section
/-!
# Actual residue homomorphism along the protected hypersurface

The domain is the actual subring of ambient fractions admitting a denominator
relatively prime to F. The target is the actual fraction field of C[Z]/(F).
The representative-choice map is proved independent by cross multiplication.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace CycleQ2Residue

open MvPolynomial HodgeComputer CycleQ2Bridge CycleQ2Regularity CycleQ2Hypersurface

abbrev Poly := AmbientPoly 5
abbrev RatFun := RationalFunction 5

/-- The actual ring of ambient rational functions regular along F. -/
def RegularAtF : Subring RatFun where
  carrier := {z | RegularAlong HodgeSubmission.F z}
  zero_mem' := regular_zero _
  one_mem' := regular_one _
  add_mem' := fun hx hy => hx.add hy
  mul_mem' := fun hx hy => hx.mul hy
  neg_mem' := fun hx => hx.neg

private def presentationNumerator (z : RegularAtF) : Poly :=
  Classical.choose z.property

private def presentationDenominator (z : RegularAtF) : Poly :=
  Classical.choose (Classical.choose_spec z.property)

private theorem presentation_spec (z : RegularAtF) :
    presentationDenominator z ≠ 0 ∧
    IsRelPrime HodgeSubmission.F (presentationDenominator z) ∧
    (z : RatFun) = polynomialMap 5 (presentationNumerator z) /
      polynomialMap 5 (presentationDenominator z) :=
  Classical.choose_spec (Classical.choose_spec z.property)

/-- Every legal ambient denominator maps to a nonzero cone-function-field element. -/
theorem legal_coneMap_ne_zero (T : Poly) (hT : IsRelPrime HodgeSubmission.F T) :
    coneMap T ≠ 0 := by
  intro h
  exact (CycleQ2ExactIrreducible.protected_F_irreducible.isRelPrime_iff_not_dvd.mp hT)
    ((coneMap_kernel T).mp h)

private def residueValue (z : RegularAtF) : ConeFunctionField :=
  coneMap (presentationNumerator z) / coneMap (presentationDenominator z)

/-- Representative independence uses the injective ambient fraction map and
polynomial cross multiplication, not a chosen representative axiom. -/
private theorem residueValue_eq (z : RegularAtF) (P T : Poly)
    (hT : T ≠ 0) (hFT : IsRelPrime HodgeSubmission.F T)
    (hz : (z : RatFun) = polynomialMap 5 P / polynomialMap 5 T) :
    residueValue z = coneMap P / coneMap T := by
  have hs := presentation_spec z
  have hcross : presentationNumerator z * T = P * presentationDenominator z := by
    apply polynomialMap_injective
    simpa only [map_mul] using
      (div_eq_div_iff (polynomialMap_ne_zero hs.1) (polynomialMap_ne_zero hT)).mp
        (hs.2.2.symm.trans hz)
  apply (div_eq_div_iff
    (legal_coneMap_ne_zero _ hs.2.1) (legal_coneMap_ne_zero T hFT)).mpr
  simpa only [map_mul] using congrArg coneMap hcross

private theorem residueValue_zero : residueValue 0 = 0 := by
  simpa using residueValue_eq 0 0 1 one_ne_zero isRelPrime_one_right (by simp)

private theorem residueValue_one : residueValue 1 = 1 := by
  simpa using residueValue_eq 1 1 1 one_ne_zero isRelPrime_one_right (by simp)

private theorem residueValue_add (x y : RegularAtF) :
    residueValue (x + y) = residueValue x + residueValue y := by
  obtain ⟨P, T, hT, hFT, hx⟩ := x.property
  obtain ⟨Q, U, hU, hFU, hy⟩ := y.property
  have hxy : ((x + y : RegularAtF) : RatFun) =
      polynomialMap 5 (P * U + Q * T) / polynomialMap 5 (T * U) := by
    change (x : RatFun) + (y : RatFun) = _
    rw [hx, hy]
    have hT' := polynomialMap_ne_zero hT
    have hU' := polynomialMap_ne_zero hU
    simp only [map_add, map_mul]
    field_simp
  rw [residueValue_eq _ _ _ (mul_ne_zero hT hU) (hFT.mul_right hFU) hxy,
    residueValue_eq x P T hT hFT hx, residueValue_eq y Q U hU hFU hy]
  have hT' := legal_coneMap_ne_zero T hFT
  have hU' := legal_coneMap_ne_zero U hFU
  simp only [map_add, map_mul]
  field_simp

private theorem residueValue_mul (x y : RegularAtF) :
    residueValue (x * y) = residueValue x * residueValue y := by
  obtain ⟨P, T, hT, hFT, hx⟩ := x.property
  obtain ⟨Q, U, hU, hFU, hy⟩ := y.property
  have hxy : ((x * y : RegularAtF) : RatFun) =
      polynomialMap 5 (P * Q) / polynomialMap 5 (T * U) := by
    change (x : RatFun) * (y : RatFun) = _
    rw [hx, hy]
    simp only [map_mul, mul_div_mul_comm]
  rw [residueValue_eq _ _ _ (mul_ne_zero hT hU) (hFT.mul_right hFU) hxy,
    residueValue_eq x P T hT hFT hx, residueValue_eq y Q U hU hFU hy]
  simp only [map_mul, mul_div_mul_comm]

/-- The actual residue homomorphism from the regular subring to the protected
cone function field. All ring-homomorphism laws are proved above. -/
def residue : RegularAtF →+* ConeFunctionField where
  toFun := residueValue
  map_zero' := residueValue_zero
  map_one' := residueValue_one
  map_add' := residueValue_add
  map_mul' := residueValue_mul

theorem residue_fraction (z : RegularAtF) (P T : Poly)
    (hT : T ≠ 0) (hFT : IsRelPrime HodgeSubmission.F T)
    (hz : (z : RatFun) = polynomialMap 5 P / polynomialMap 5 T) :
    residue z = coneMap P / coneMap T :=
  residueValue_eq z P T hT hFT hz

/-- A polynomial viewed in the regular ambient subring. -/
def polynomialRegular (P : Poly) : RegularAtF :=
  ⟨polynomialMap 5 P, regular_polynomial HodgeSubmission.F P⟩

@[simp] theorem residue_polynomial (P : Poly) :
    residue (polynomialRegular P) = coneMap P := by
  simpa using residue_fraction (polynomialRegular P) P 1
    one_ne_zero isRelPrime_one_right (by simp [polynomialRegular])

theorem residue_fraction_eq_zero_iff (z : RegularAtF) (P T : Poly)
    (hT : T ≠ 0) (hFT : IsRelPrime HodgeSubmission.F T)
    (hz : (z : RatFun) = polynomialMap 5 P / polynomialMap 5 T) :
    residue z = 0 ↔ HodgeSubmission.F ∣ P := by
  rw [residue_fraction z P T hT hFT hz]
  have hT' := legal_coneMap_ne_zero T hFT
  rw [div_eq_zero_iff]
  simp only [hT', or_false]
  exact coneMap_kernel P

/-- The actual residue kernel is exactly multiplication by F inside the
regular subring. The quotient coefficient is still regular along F. -/
theorem residue_eq_zero_iff_exists_F_mul (z : RegularAtF) :
    residue z = 0 ↔ ∃ t : RegularAtF,
      (z : RatFun) = polynomialMap 5 HodgeSubmission.F * (t : RatFun) := by
  constructor
  · intro hz
    obtain ⟨P, T, hT, hFT, hrepr⟩ := z.property
    obtain ⟨Q, hQ⟩ := (residue_fraction_eq_zero_iff z P T hT hFT hrepr).mp hz
    let t : RegularAtF := ⟨polynomialMap 5 Q / polynomialMap 5 T,
      ⟨Q, T, hT, hFT, rfl⟩⟩
    refine ⟨t, ?_⟩
    change (z : RatFun) = polynomialMap 5 HodgeSubmission.F *
      (polynomialMap 5 Q / polynomialMap 5 T)
    rw [hrepr, hQ, map_mul]
    ring
  · rintro ⟨t, ht⟩
    have he : z = polynomialRegular HodgeSubmission.F * t := Subtype.ext ht
    rw [he, map_mul, residue_polynomial, coneMap_F, zero_mul]

/-- Equivalent form convenient for pole reduction: vanishing residue means
one can divide by F while remaining in the actual regular subring. -/
theorem residue_eq_zero_iff_regular_div_F (z : RegularAtF) :
    residue z = 0 ↔ RegularAlong HodgeSubmission.F
      ((z : RatFun) / polynomialMap 5 HodgeSubmission.F) := by
  have hF := polynomialMap_ne_zero CycleQ2ExactIrreducible.protected_F_irreducible.ne_zero
  constructor
  · intro hz
    obtain ⟨t, ht⟩ := (residue_eq_zero_iff_exists_F_mul z).mp hz
    have he : (z : RatFun) / polynomialMap 5 HodgeSubmission.F = (t : RatFun) := by
      rw [ht]
      field_simp
    rw [he]
    exact t.property
  · intro hz
    apply (residue_eq_zero_iff_exists_F_mul z).mpr
    refine ⟨⟨(z : RatFun) / polynomialMap 5 HodgeSubmission.F, hz⟩, ?_⟩
    change (z : RatFun) = polynomialMap 5 HodgeSubmission.F *
      ((z : RatFun) / polynomialMap 5 HodgeSubmission.F)
    field_simp


open CycleQ2ActualResidueClosure

local instance rationalFunctionIntAlgebra : Algebra ℤ RatFun := Ring.toIntAlgebra _
local instance coneFunctionFieldIntAlgebra : Algebra ℤ ConeFunctionField := Ring.toIntAlgebra _
local instance regularAtFIntAlgebra : Algebra ℤ RegularAtF := Ring.toIntAlgebra _

/-- The exact normal polynomial is nonzero before quotienting as well. -/
theorem normal_polynomial_ne_zero : pderiv 0 HodgeSubmission.F ≠ 0 := by
  intro h
  apply normal_ne_zero
  rw [h, map_zero]

theorem normal_polynomial_relPrime :
    IsRelPrime HodgeSubmission.F (pderiv 0 HodgeSubmission.F) :=
  CycleQ2ExactIrreducible.protected_F_irreducible.isRelPrime_iff_not_dvd.mpr
    protected_F_not_dvd_normal

/-- Restriction of the actual ambient tangent derivation to the actual regular
subring. Closure is proved from the quotient rule and normal-denominator legality. -/
def regularTangent (j : Fin 5) : Derivation ℤ RegularAtF RegularAtF :=
  Derivation.mk'
    ({ toFun := fun z => ⟨actualTangent HodgeSubmission.F j (z : RatFun),
         regular_actualTangent z.property normal_polynomial_ne_zero
           normal_polynomial_relPrime j⟩
       map_zero' := Subtype.ext (map_zero _)
       map_add' := fun x y => Subtype.ext (map_add _ _ _)
     } : RegularAtF →+ RegularAtF).toIntLinearMap
    (by
      intro x y
      apply Subtype.ext
      change actualTangent HodgeSubmission.F j ((x : RatFun) * (y : RatFun)) =
        (x : RatFun) * actualTangent HodgeSubmission.F j (y : RatFun) +
          (y : RatFun) * actualTangent HodgeSubmission.F j (x : RatFun)
      simpa only [smul_eq_mul] using
        (actualTangent HodgeSubmission.F j).leibniz (x : RatFun) (y : RatFun))

@[simp] theorem regularTangent_apply (j : Fin 5) (z : RegularAtF) :
    ((regularTangent j z : RegularAtF) : RatFun) =
      actualTangent HodgeSubmission.F j (z : RatFun) := rfl

@[simp] theorem residue_regularTangent_polynomial (j : Fin 5) (P : Poly) :
    residue (regularTangent j (polynomialRegular P)) =
      coneTangent j (coneMap P) := by
  let Q : Poly := pderiv 0 HodgeSubmission.F * pderiv j.succ P -
    pderiv j.succ HodgeSubmission.F * pderiv 0 P
  have hrepr : ((regularTangent j (polynomialRegular P) : RegularAtF) : RatFun) =
      polynomialMap 5 Q / polynomialMap 5 (pderiv 0 HodgeSubmission.F) := by
    change actualTangent HodgeSubmission.F j (polynomialMap 5 P) = _
    rw [actualTangent_apply]
    simp only [Q, rationalPartial_map, map_sub, map_mul]
    have hg := polynomialMap_ne_zero normal_polynomial_ne_zero
    field_simp <;> ring
  rw [residue_fraction _ Q _ normal_polynomial_ne_zero normal_polynomial_relPrime hrepr,
    coneTangent_apply]
  simp only [Q, map_sub, map_mul]
  have hg := normal_ne_zero
  field_simp <;> ring

/-- Exact compatibility of the actual regular-subring residue homomorphism
with the actual constructed tangent derivations on the cone function field. -/
theorem residue_regularTangent (j : Fin 5) (z : RegularAtF) :
    residue (regularTangent j z) = coneTangent j (residue z) := by
  obtain ⟨P, T, hT, hFT, hz⟩ := z.property
  have hprod : z * polynomialRegular T = polynomialRegular P := by
    apply Subtype.ext
    change (z : RatFun) * polynomialMap 5 T = polynomialMap 5 P
    rw [hz, div_mul_cancel₀ _ (polynomialMap_ne_zero hT)]
  have h₁ := congrArg (fun u : RegularAtF => residue (regularTangent j u)) hprod
  rw [Derivation.leibniz] at h₁
  simp only [smul_eq_mul, map_add, map_mul, residue_polynomial,
    residue_regularTangent_polynomial] at h₁
  have h₂ := congrArg (fun u : RegularAtF => coneTangent j (residue u)) hprod
  simp only [map_mul, residue_polynomial, Derivation.leibniz, smul_eq_mul] at h₂
  apply mul_left_cancel₀ (legal_coneMap_ne_zero T hFT)
  linear_combination h₁ - h₂


/-- Every element of the actual cone function field lifts to an actual
ambient fraction regular along F. This does not assert any homogeneity of
that lift. -/
theorem residue_surjective : Function.Surjective residue := by
  intro w
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective ConeCoordinateRing w
  obtain ⟨P, rfl⟩ := coneProjection_surjective a
  obtain ⟨T, rfl⟩ := coneProjection_surjective b
  have hden : coneMap T ≠ 0 := by
    change algebraMap ConeCoordinateRing ConeFunctionField (coneProjection T) ≠ 0
    exact IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  have hT : T ≠ 0 := by
    intro h
    apply hden
    rw [h, map_zero]
  have hFT : IsRelPrime HodgeSubmission.F T :=
    CycleQ2ExactIrreducible.protected_F_irreducible.isRelPrime_iff_not_dvd.mpr
      (fun h => hden ((coneMap_kernel T).mpr h))
  let z : RegularAtF := ⟨polynomialMap 5 P / polynomialMap 5 T,
    ⟨P, T, hT, hFT, rfl⟩⟩
  refine ⟨z, ?_⟩
  exact residue_fraction z P T hT hFT rfl

/-- A nonconstructive lift, justified by the proved residue surjectivity. -/
def liftResidue (w : ConeFunctionField) : RegularAtF :=
  Function.surjInv residue_surjective w

@[simp] theorem residue_liftResidue (w : ConeFunctionField) :
    residue (liftResidue w) = w := Function.surjInv_eq residue_surjective w

end CycleQ2Residue

#print axioms CycleQ2Residue.residue_fraction
#print axioms CycleQ2Residue.residue_eq_zero_iff_exists_F_mul
#print axioms CycleQ2Residue.residue_eq_zero_iff_regular_div_F

#print axioms CycleQ2Residue.residue_regularTangent

#print axioms CycleQ2Residue.residue_surjective
#print axioms CycleQ2Residue.residue_liftResidue
end
end


/- Component: pole_reduction/ProtectedResidueClosure.lean -/
section
/-!
Concrete closure of an actual residue primitive on the protected affine cone.

This proves regular ambient lifts and the third-order defect identity. It does
not assert existence of the residue primitive, and it does not assert the
homogeneous degree-seven condition on the resulting ambient vector field.
Projective homogenization or a graded primitive is a further step before
the protected HasCertificate theorem follows.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section

namespace CycleQ2ProtectedResidueClosure

open MvPolynomial HodgeComputer CycleQ2Bridge CycleQ2Regularity
open CycleQ2Hypersurface CycleQ2Residue CycleQ2ActualResidueClosure
open HoldoutConstruction SplitHigherResidue
open scoped BigOperators

local instance rationalFunctionIntAlgebra : Algebra ℤ RatFun := Ring.toIntAlgebra _
local instance coneFunctionFieldIntAlgebra : Algebra ℤ ConeFunctionField := Ring.toIntAlgebra _
local instance regularAtFIntAlgebra : Algebra ℤ RegularAtF := Ring.toIntAlgebra _

private theorem two_polynomial_relPrime : IsRelPrime HodgeSubmission.F (2 : Poly) := by
  have hu : IsUnit (2 : Poly) := by
    simpa only [map_ofNat] using
      (isUnit_iff_ne_zero.mpr (by norm_num : (2 : ℂ) ≠ 0)).map (C : ℂ →+* Poly)
  exact hu.isRelPrime_right

/-- The genuine inverse of the normal polynomial in the regular subring. -/
def normalInverse : RegularAtF :=
  ⟨(polynomialMap 5 (pderiv 0 HodgeSubmission.F))⁻¹,
    regular_inv_polynomial _ _ normal_polynomial_ne_zero normal_polynomial_relPrime⟩

@[simp] theorem normalInverse_val :
    (normalInverse : RatFun) = (polynomialMap 5 (pderiv 0 HodgeSubmission.F))⁻¹ := rfl

@[simp] theorem residue_normalInverse :
    residue normalInverse = (coneMap (pderiv 0 HodgeSubmission.F))⁻¹ := by
  simpa using residue_fraction normalInverse 1 (pderiv 0 HodgeSubmission.F)
    normal_polynomial_ne_zero normal_polynomial_relPrime (by simp [normalInverse])

private def halfRegular : RegularAtF :=
  ⟨(1 / 2 : RatFun), by
    change RegularAlong HodgeSubmission.F (1 / 2 : RatFun)
    simpa only [map_ofNat, one_div] using regular_inv_polynomial HodgeSubmission.F (2 : Poly)
      (by norm_num) two_polynomial_relPrime⟩

private theorem halfRegular_val : (halfRegular : RatFun) = (1 / 2 : RatFun) := rfl

private theorem residue_halfRegular : residue halfRegular = (1 / 2 : ConeFunctionField) := by
  simpa only [map_one, map_ofNat] using residue_fraction halfRegular 1 (2 : Poly)
    (by norm_num) two_polynomial_relPrime (by
      change (1 / 2 : RatFun) = polynomialMap 5 1 / polynomialMap 5 2
      simp only [map_one, map_ofNat])

/-- The exact normal source, now evaluated in the actual cone function field. -/
def coneNormalSource (A : Poly) : ConeFunctionField :=
  normalSourceTwo (coneMap A) (coneMap (pderiv 0 A))
    (coneMap (pderiv 0 (pderiv 0 A)))
    (coneMap (pderiv 0 HodgeSubmission.F))
    (coneMap (pderiv 0 (pderiv 0 HodgeSubmission.F)))
    (coneMap (pderiv 0 (pderiv 0 (pderiv 0 HodgeSubmission.F))))

/-- The concrete function-field residue equation whose solution is required. -/
def coneResidueExpression (A : Poly) (w : Fin 5 → ConeFunctionField) : ConeFunctionField :=
  coneNormalSource A +
    residueDivergence coneTangent (coneMap (pderiv 0 HodgeSubmission.F)) w

private def normalSourceRegular (A : Poly) : RegularAtF :=
  halfRegular *
    (polynomialRegular (pderiv 0 (pderiv 0 A)) * normalInverse ^ 2 -
      (3 * polynomialRegular (pderiv 0 A) *
          polynomialRegular (pderiv 0 (pderiv 0 HodgeSubmission.F)) +
        polynomialRegular A * polynomialRegular (pderiv 0 (pderiv 0 (pderiv 0 HodgeSubmission.F)))) *
        normalInverse ^ 3 +
      3 * polynomialRegular A * polynomialRegular (pderiv 0 (pderiv 0 HodgeSubmission.F)) ^ 2 *
        normalInverse ^ 4)

private theorem normalSourceRegular_val (A : Poly) :
    ((normalSourceRegular A : RegularAtF) : RatFun) =
      actualNormalSource HodgeSubmission.F A := by
  change RegularAtF.subtype (normalSourceRegular A) = _
  simp only [normalSourceRegular, actualNormalSource, normalSourceTwo,
    map_mul, map_add, map_sub, map_pow, map_ofNat, Subring.subtype_apply,
    halfRegular_val, normalInverse_val, polynomialRegular,
    div_eq_mul_inv, inv_pow]

private theorem residue_normalSourceRegular (A : Poly) :
    residue (normalSourceRegular A) = coneNormalSource A := by
  simp only [normalSourceRegular, map_mul, map_add, map_sub, map_pow, map_ofNat,
    residue_halfRegular, residue_normalInverse, residue_polynomial,
    coneNormalSource, normalSourceTwo, div_eq_mul_inv, inv_pow]

/-- The actual regular-subring lift of the entire residue equation. -/
def residueExpressionRegular (A : Poly) (w : Fin 5 → RegularAtF) : RegularAtF :=
  normalSourceRegular A +
    (∑ j, regularTangent j (w j)) -
    (∑ j, w j * regularTangent j (polynomialRegular (pderiv 0 HodgeSubmission.F))) *
      normalInverse

theorem residueExpressionRegular_val (A : Poly) (w : Fin 5 → RegularAtF) :
    ((residueExpressionRegular A w : RegularAtF) : RatFun) =
      actualResidueExpression HodgeSubmission.F A (fun j => (w j : RatFun)) := by
  change RegularAtF.subtype (residueExpressionRegular A w) = _
  simp only [residueExpressionRegular, map_add, map_sub, map_mul,
    map_sum, Subring.subtype_apply, regularTangent_apply, normalSourceRegular_val, normalInverse_val,
    polynomialRegular, actualResidueExpression, residueDivergence,
    HoldoutConstruction.fieldDivergence, div_eq_mul_inv]
  ring

/-- The ambient source and tangent divergence transport to the actual quotient
equation through the proved residue homomorphism. -/
theorem residue_residueExpressionRegular (A : Poly) (w : Fin 5 → RegularAtF) :
    residue (residueExpressionRegular A w) =
      coneResidueExpression A (fun j => residue (w j)) := by
  simp only [residueExpressionRegular, map_add, map_sub, map_mul, map_sum,
    residue_normalSourceRegular, residue_regularTangent, residue_polynomial,
    residue_normalInverse, coneResidueExpression, residueDivergence,
    HoldoutConstruction.fieldDivergence, div_eq_mul_inv]
  ring

/-- A solved cone residue equation for actual regular lifts gives an actual
regular ambient vector with third-order defect. Homogeneity is not asserted. -/
theorem regular_cone_primitive_closure (A : Poly) (w : Fin 5 → RegularAtF)
    (hres : coneResidueExpression A (fun j => residue (w j)) = 0) :
    ∃ (v : Fin 6 → RatFun) (t : RatFun),
      (∀ i, RegularAlong HodgeSubmission.F (v i)) ∧
      RegularAlong HodgeSubmission.F t ∧
      rationalDefect HodgeSubmission.F A 2 v =
        polynomialMap 5 HodgeSubmission.F ^ 3 * t := by
  have hz : residue (residueExpressionRegular A w) = 0 := by
    rw [residue_residueExpressionRegular]
    exact hres
  obtain ⟨t, ht⟩ := (residue_eq_zero_iff_exists_F_mul (residueExpressionRegular A w)).mp hz
  refine ⟨actualClosureVector HodgeSubmission.F A (fun j => (w j : RatFun)), t,
    ?_, t.property, ?_⟩
  · exact regular_actualClosureVector HodgeSubmission.F A _ normal_polynomial_ne_zero
      normal_polynomial_relPrime (fun j => (w j).property)
  · apply actualClosure_defect_of_residue HodgeSubmission.F A _ _ normal_polynomial_ne_zero
    rw [← residueExpressionRegular_val]
    exact ht

/-- Every actual cone primitive has regular ambient lifts. This conclusion
is the rational defect equation; no homogeneous-degree conclusion is hidden. -/
theorem cone_primitive_closure (A : Poly) (w : Fin 5 → ConeFunctionField)
    (hres : coneResidueExpression A w = 0) :
    ∃ (v : Fin 6 → RatFun) (t : RatFun),
      (∀ i, RegularAlong HodgeSubmission.F (v i)) ∧
      RegularAlong HodgeSubmission.F t ∧
      rationalDefect HodgeSubmission.F A 2 v =
        polynomialMap 5 HodgeSubmission.F ^ 3 * t := by
  apply regular_cone_primitive_closure A (fun j => liftResidue (w j))
  simpa only [residue_liftResidue] using hres

/-- The exact protected numerator is bound here to the concrete cone equation.
Its remaining primitive-existence hypothesis is stated explicitly. -/
theorem protected_regular_ambient_of_cone_primitive
    (h : ∃ w : Fin 5 → ConeFunctionField,
      coneResidueExpression HodgeSubmission.A w = 0) :
    ∃ (v : Fin 6 → RatFun) (t : RatFun),
      (∀ i, RegularAlong HodgeSubmission.F (v i)) ∧
      RegularAlong HodgeSubmission.F t ∧
      rationalDefect HodgeSubmission.F HodgeSubmission.A 2 v =
        polynomialMap 5 HodgeSubmission.F ^ 3 * t := by
  obtain ⟨w, hw⟩ := h
  exact cone_primitive_closure HodgeSubmission.A w hw

end CycleQ2ProtectedResidueClosure

#print axioms CycleQ2ProtectedResidueClosure.residue_residueExpressionRegular
#print axioms CycleQ2ProtectedResidueClosure.regular_cone_primitive_closure
#print axioms CycleQ2ProtectedResidueClosure.protected_regular_ambient_of_cone_primitive
end
end


