import Proposal.GeometricLiteralGradedDeformation

/-!
# The graded quotient is the original literal deformation

The maps in both directions retain the original polynomial coordinates
and the original epsilon element. Their inverse identities prove an
actual complex-algebra equivalence with the independently constructed
quotient by F - epsilon B*. The grading is therefore attached to that
specific deformation, rather than to a replacement square-zero model.

Prepared for fqlx with OpenAI ChatGPT assistance; see solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralGradedDeformationEquiv

open MvPolynomial CycleQ2SeedTrace CycleQ2NormalConnecting
  CycleQ2LiteralCartierTransitionBinding CycleQ2GeometricSurfaceFirstOrder
  CycleQ2LiteralCartierOverlapSplittings CycleQ2LiteralGradedDeformation

attribute [local instance] CycleQ2LiteralCartierTransitionBinding.cubicSelfModule
  CycleQ2LiteralCartierTransitionBinding.cubicOppositeModule
  CycleQ2LiteralCartierTransitionBinding.cubicCentralScalar
  CycleQ2LiteralCartierTransitionBinding.cubicSmulCommClass
  CycleQ2GeometricSurfaceFirstOrder.reducedAlgebra

def polynomialInGraded : WeightedPoly →ₐ[ℂ] GradedDeformation :=
  quotientMap.comp includePolynomial

theorem polynomialInGraded_cubic : polynomialInGraded (thetaH 1) = 0 :=
  quotientMap_relations 0

theorem originalCubicIdeal_le_kernel :
    CycleQ2GeometricUniversalSurfaceFirstOrder.cubicIdeal ℂ
        (CycleQ2GeometricSeedNormalizedCoordinates.cubicCoefficients 57) ≤
      RingHom.ker polynomialInGraded.toRingHom := by
  apply Ideal.span_le.mpr
  rintro p (rfl : p = _)
  rw [CycleQ2GeometricSeedNormalizedCoordinates.normalizedCubic_eq_thetaH_one]
  exact polynomialInGraded_cubic

def cubicToGraded : CubicRing →ₐ[ℂ] GradedDeformation :=
  Ideal.Quotient.liftₐ _ polynomialInGraded (fun _ hp => originalCubicIdeal_le_kernel hp)

theorem cubicToGraded_polynomial (p : WeightedPoly) :
    cubicToGraded (cubicMap p) = polynomialInGraded p := rfl

def dualToGraded : Dual CubicRing →ₐ[ℂ] GradedDeformation :=
  TrivSqZeroExt.lift cubicToGraded (epsilonElement • cubicToGraded.toLinearMap)
    (by
      intro x y
      change (epsilonElement * cubicToGraded x) * (epsilonElement * cubicToGraded y) = 0
      calc
        _ = (epsilonElement * epsilonElement) * (cubicToGraded x * cubicToGraded y) := by ring
        _ = 0 := by rw [epsilonElement_square, zero_mul])
    (by
      intro r x
      change epsilonElement * cubicToGraded (r * x) =
        cubicToGraded r * (epsilonElement * cubicToGraded x)
      rw [map_mul]
      ring)
    (by
      intro r x
      change epsilonElement * cubicToGraded (x * r) =
        (epsilonElement * cubicToGraded x) * cubicToGraded r
      rw [map_mul]
      ring)

theorem dualToGraded_apply (z : Dual CubicRing) :
    dualToGraded z = cubicToGraded z.fst + epsilonElement * cubicToGraded z.snd := rfl

theorem dualToGraded_inl (x : CubicRing) :
    dualToGraded (TrivSqZeroExt.inl x) = cubicToGraded x := by
  rw [dualToGraded_apply]
  simp only [TrivSqZeroExt.fst_inl, TrivSqZeroExt.snd_inl, map_zero, mul_zero, add_zero]

theorem dualToGraded_inr (x : CubicRing) :
    dualToGraded (TrivSqZeroExt.inr x) = epsilonElement * cubicToGraded x := by
  rw [dualToGraded_apply]
  simp only [TrivSqZeroExt.fst_inr, TrivSqZeroExt.snd_inr, map_zero, zero_add]

theorem cubicToGraded_equation :
    cubicToGraded equation = polynomialInGraded (actualSeedEquation 57 1) := by
  rw [← cubicMap_actualSeedEquation, cubicToGraded_polynomial]

theorem dualToGraded_relation : dualToGraded (relation equation perturbation) = 0 := by
  rw [relation_eq, map_sub, dualToGraded_inl, dualToGraded_inr,
    cubicToGraded_equation]
  change quotientMap (includePolynomial (actualSeedEquation 57 1)) -
    quotientMap epsilonPolynomial * quotientMap (includePolynomial derivativeA) = 0
  rw [← map_mul, ← map_sub]
  exact quotientMap_relations 1

def fromOriginal : ThickBase →ₐ[ℂ] GradedDeformation :=
  Ideal.Quotient.liftₐ (deformationIdeal equation perturbation) dualToGraded (by
    intro z hz
    have hI : deformationIdeal equation perturbation ≤ RingHom.ker dualToGraded.toRingHom :=
      Ideal.span_le.mpr (by rintro z (rfl : z = _); exact dualToGraded_relation)
    exact hI hz)

theorem fromOriginal_polynomial (p : WeightedPoly) :
    fromOriginal (originalPolynomial p) = polynomialInGraded p := by
  change dualToGraded (TrivSqZeroExt.inl (cubicMap p)) = _
  rw [dualToGraded_inl, cubicToGraded_polynomial]

theorem fromOriginal_epsilon : fromOriginal originalEpsilon = epsilonElement := by
  change dualToGraded (TrivSqZeroExt.inr (1 : CubicRing)) = _
  rw [dualToGraded_inr, map_one, mul_one]

theorem toOriginal_polynomial (p : WeightedPoly) :
    toOriginal (polynomialInGraded p) = originalPolynomial p :=
  toOriginalRaw_include p

def originalBaseMap : CubicRing →ₐ[ℂ] ThickBase :=
  IsScalarTower.toAlgHom ℂ CubicRing ThickBase

theorem toOriginal_cubicToGraded (x : CubicRing) :
    toOriginal (cubicToGraded x) = originalBaseMap x := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact toOriginal_polynomial p

theorem toOriginal_dualToGraded (z : Dual CubicRing) :
    toOriginal (dualToGraded z) =
      Ideal.Quotient.mk (deformationIdeal equation perturbation) z := by
  rw [dualToGraded_apply, map_add, map_mul, toOriginal_cubicToGraded,
    toOriginal_cubicToGraded, toOriginal_epsilon]
  change Ideal.Quotient.mk _ (TrivSqZeroExt.inl z.fst) +
    Ideal.Quotient.mk _ (TrivSqZeroExt.inr (1 : CubicRing)) *
      Ideal.Quotient.mk _ (TrivSqZeroExt.inl z.snd) = _
  rw [← map_mul, ← map_add]
  congr 1
  apply TrivSqZeroExt.ext
  · change z.fst + 0 * z.snd = z.fst
    ring
  · change (0 : CubicRing) + (0 * 0 + 1 * z.snd) = z.snd
    ring

theorem toOriginal_fromOriginal (x : ThickBase) : toOriginal (fromOriginal x) = x := by
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact toOriginal_dualToGraded z

theorem fromOriginal_toOriginal (x : GradedDeformation) : fromOriginal (toOriginal x) = x := by
  have h : (fromOriginal.comp toOriginal).comp quotientMap = quotientMap := by
    apply MvPolynomial.algHom_ext
    intro i
    cases i with
    | none =>
      change fromOriginal (toOriginal epsilonElement) = epsilonElement
      rw [toOriginal_epsilon, fromOriginal_epsilon]
    | some i =>
      change fromOriginal (toOriginal (coordinate i)) = coordinate i
      rw [toOriginal_coordinate, fromOriginal_polynomial]
      simp only [polynomialInGraded, AlgHom.comp_apply, includePolynomial, rename_X, coordinate]
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact AlgHom.congr_fun h p

/-- The comparison of actual presentations fixes every original
coordinate and the original degree-zero epsilon, in both directions. -/
def originalAlgEquiv : GradedDeformation ≃ₐ[ℂ] ThickBase where
  __ := toOriginal
  invFun := fromOriginal
  left_inv := fromOriginal_toOriginal
  right_inv := toOriginal_fromOriginal

theorem originalAlgEquiv_coordinate (i : Fin 5) :
    originalAlgEquiv (coordinate i) = originalPolynomial (X i) :=
  toOriginal_coordinate i

theorem originalAlgEquiv_epsilon : originalAlgEquiv epsilonElement = originalEpsilon :=
  toOriginal_epsilon

theorem originalAlgEquiv_symm_polynomial (p : WeightedPoly) :
    originalAlgEquiv.symm (originalPolynomial p) = polynomialInGraded p :=
  fromOriginal_polynomial p

theorem originalAlgEquiv_symm_epsilon :
    originalAlgEquiv.symm originalEpsilon = epsilonElement :=
  fromOriginal_epsilon

end CycleQ2LiteralGradedDeformationEquiv

end

#print axioms CycleQ2LiteralGradedDeformationEquiv.originalAlgEquiv
#print axioms CycleQ2LiteralGradedDeformationEquiv.originalAlgEquiv_coordinate
#print axioms CycleQ2LiteralGradedDeformationEquiv.originalAlgEquiv_epsilon
