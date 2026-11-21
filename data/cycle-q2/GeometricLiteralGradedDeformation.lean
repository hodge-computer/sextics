import Proposal.GeometricLiteralCartierProjectedCup
import Mathlib.Algebra.MvPolynomial.Rename

/-!
# A graded presentation of the original literal ambient deformation

The extra variable is epsilon, of weight zero. The three actual
relations are the unchanged cubic, F - epsilon B*, and epsilon squared.
Their homogeneity constructs a genuine graded quotient. Its map to the
already constructed literal deformation fixes the original coordinates
and epsilon. Equivalence with that deformation is a further proof.

Prepared for fqlx with OpenAI ChatGPT assistance; see solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralGradedDeformation

open MvPolynomial CycleQ2SeedTrace CycleQ2NormalConnecting
  CycleQ2CartierSurfaceGrading CycleQ2LiteralCartierTransitionBinding
  CycleQ2GeometricSurfaceFirstOrder CycleQ2LiteralCartierOverlapSplittings

attribute [local instance] CycleQ2LiteralCartierTransitionBinding.cubicSelfModule
  CycleQ2LiteralCartierTransitionBinding.cubicOppositeModule
  CycleQ2LiteralCartierTransitionBinding.cubicCentralScalar
  CycleQ2LiteralCartierTransitionBinding.cubicSmulCommClass
  CycleQ2GeometricSurfaceFirstOrder.reducedAlgebra

abbrev AmbientPoly := MvPolynomial (Option (Fin 5)) ℂ

def ambientWeight : Option (Fin 5) → ℕ := Option.elim' 0 weight

def includePolynomial : WeightedPoly →ₐ[ℂ] AmbientPoly := rename some

abbrev AmbientGrade (n : ℕ) : Submodule ℂ AmbientPoly :=
  weightedHomogeneousSubmodule ℂ ambientWeight n

attribute [local instance] MvPolynomial.weightedGradedAlgebra

private theorem renamed_weight (d : Fin 5 →₀ ℕ) :
    Finsupp.weight ambientWeight (Finsupp.mapDomain some d) = Finsupp.weight weight d := by
  classical
  induction d using Finsupp.induction with
  | zero => simp
  | @single_add a b d h ha ih =>
    simp only [Finsupp.mapDomain_add, map_add, Finsupp.mapDomain_single,
      Finsupp.weight_single, ih]
    rfl

/-- Adding the independent weight-zero epsilon variable preserves the
actual weighted degree of every original polynomial. -/
theorem includePolynomial_homogeneous {p : WeightedPoly} {n : ℕ}
    (hp : p.IsWeightedHomogeneous weight n) :
    (includePolynomial p).IsWeightedHomogeneous ambientWeight n := by
  induction hp using MvPolynomial.IsWeightedHomogeneous.induction_on with
  | zero => exact isWeightedHomogeneous_zero ℂ ambientWeight n
  | add p q hp hq ihp ihq =>
    simpa only [map_add] using ihp.add ihq
  | monomial d c hd =>
    rw [includePolynomial, rename_monomial]
    exact isWeightedHomogeneous_monomial ambientWeight _ c ((renamed_weight d).trans hd)

def epsilonPolynomial : AmbientPoly := X none

def cubicPolynomial : AmbientPoly := includePolynomial (thetaH 1)

def equationPolynomial : AmbientPoly :=
  includePolynomial (actualSeedEquation 57 1) - epsilonPolynomial * includePolynomial derivativeA

def relations : Fin 3 → AmbientPoly :=
  ![cubicPolynomial, equationPolynomial, epsilonPolynomial ^ 2]

def relationDegree : Fin 3 → ℕ := ![3,6,0]

def ambientIdeal : Ideal AmbientPoly := Ideal.span (Set.range relations)

theorem epsilonPolynomial_homogeneous : epsilonPolynomial ∈ AmbientGrade 0 :=
  isWeightedHomogeneous_X ℂ ambientWeight none

theorem cubicPolynomial_homogeneous : cubicPolynomial ∈ AmbientGrade 3 :=
  includePolynomial_homogeneous (thetaH_homogeneous 1)

theorem equationPolynomial_homogeneous : equationPolynomial ∈ AmbientGrade 6 := by
  exact (includePolynomial_homogeneous (actualSeedEquation_homogeneous 57 1)).sub
    (by simpa using (epsilonPolynomial_homogeneous.mul
        (includePolynomial_homogeneous derivativeA_homogeneous)))

theorem relations_homogeneous (i : Fin 3) : relations i ∈ AmbientGrade (relationDegree i) := by
  fin_cases i
  · exact cubicPolynomial_homogeneous
  · exact equationPolynomial_homogeneous
  · change (epsilonPolynomial ^ 2).IsWeightedHomogeneous ambientWeight 0
    simpa using epsilonPolynomial_homogeneous.pow 2

theorem ambientIdeal_homogeneous : ambientIdeal.IsHomogeneous AmbientGrade := by
  apply Ideal.homogeneous_span
  rintro p ⟨i, rfl⟩
  exact ⟨relationDegree i, relations_homogeneous i⟩

abbrev GradedDeformation := AmbientPoly ⧸ ambientIdeal

abbrev deformationGrade (n : ℕ) : Submodule ℂ GradedDeformation :=
  CycleQ2GeometricProjectiveCurve.HomogeneousQuotient.grade AmbientGrade ambientIdeal n

instance deformationGradedRing : GradedRing deformationGrade :=
  CycleQ2GeometricProjectiveCurve.HomogeneousQuotient.gradedRing
    AmbientGrade ambientIdeal ambientIdeal_homogeneous

def quotientMap : AmbientPoly →ₐ[ℂ] GradedDeformation := Ideal.Quotient.mkₐ ℂ ambientIdeal

def coordinate (i : Fin 5) : GradedDeformation := quotientMap (X (some i))

def epsilonElement : GradedDeformation := quotientMap epsilonPolynomial

theorem quotientMap_mem_grade {n : ℕ} {p : AmbientPoly} (hp : p ∈ AmbientGrade n) :
    quotientMap p ∈ deformationGrade n := ⟨p, hp, rfl⟩

theorem coordinate_mem_grade (i : Fin 5) : coordinate i ∈ deformationGrade (weight i) :=
  quotientMap_mem_grade (isWeightedHomogeneous_X ℂ ambientWeight (some i))

theorem epsilonElement_mem_grade : epsilonElement ∈ deformationGrade 0 :=
  quotientMap_mem_grade epsilonPolynomial_homogeneous

theorem quotientMap_relations (i : Fin 3) : quotientMap (relations i) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨i, rfl⟩)

theorem epsilonElement_square : epsilonElement * epsilonElement = 0 := by
  change quotientMap epsilonPolynomial * quotientMap epsilonPolynomial = 0
  rw [← map_mul, ← pow_two]
  exact quotientMap_relations 2

/-- The original epsilon element in the already constructed deformation. -/
def originalEpsilon : ThickBase :=
  Ideal.Quotient.mk (deformationIdeal equation perturbation) (TrivSqZeroExt.inr (1 : CubicRing))

def originalPolynomial : WeightedPoly →ₐ[ℂ] ThickBase where
  toRingHom := polynomialToThick
  commutes' _c := rfl

def toOriginalRaw : AmbientPoly →ₐ[ℂ] ThickBase :=
  aeval (Option.elim' originalEpsilon (fun i => originalPolynomial (X i)))

theorem toOriginalRaw_epsilon : toOriginalRaw epsilonPolynomial = originalEpsilon := by
  simp [toOriginalRaw, epsilonPolynomial]

theorem toOriginalRaw_include (p : WeightedPoly) :
    toOriginalRaw (includePolynomial p) = originalPolynomial p := by
  have h : toOriginalRaw.comp includePolynomial = originalPolynomial := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [toOriginalRaw, includePolynomial]
  exact AlgHom.congr_fun h p

theorem originalEpsilon_square : originalEpsilon * originalEpsilon = 0 := by
  rw [originalEpsilon, ← map_mul, TrivSqZeroExt.inr_mul_inr, map_zero]

theorem originalEpsilon_mul_polynomial (p : WeightedPoly) :
    originalEpsilon * originalPolynomial p =
      Ideal.Quotient.mk (deformationIdeal equation perturbation)
        (TrivSqZeroExt.inr (cubicMap p)) := by
  change Ideal.Quotient.mk _ (TrivSqZeroExt.inr (1 : CubicRing)) *
    Ideal.Quotient.mk _ (TrivSqZeroExt.inl (cubicMap p)) = _
  rw [← map_mul]
  congr 1
  apply TrivSqZeroExt.ext
  · simp
  · change (0 : CubicRing) * 0 + 1 * cubicMap p = cubicMap p
    ring

theorem cubicMap_actualSeedEquation : cubicMap (actualSeedEquation 57 1) = equation := by
  rw [← CycleQ2GeometricSeedNormalizedCoordinates.normalizedSextic_eq_actualSeedEquation]
  rfl

theorem toOriginalRaw_relations (i : Fin 3) : toOriginalRaw (relations i) = 0 := by
  fin_cases i
  · change toOriginalRaw (includePolynomial (thetaH 1)) = 0
    rw [toOriginalRaw_include]
    change @Algebra.algebraMap CubicRing ThickBase
      (inferInstance : CommSemiring CubicRing) (inferInstance : Semiring ThickBase)
      inferInstance (cubicMap (thetaH 1)) = 0
    rw [cubicMap_cubic, map_zero]
  · change toOriginalRaw (includePolynomial (actualSeedEquation 57 1) -
      epsilonPolynomial * includePolynomial derivativeA) = 0
    rw [map_sub, map_mul, toOriginalRaw_include, toOriginalRaw_include,
      toOriginalRaw_epsilon, originalEpsilon_mul_polynomial]
    change deformationCoordinate equation perturbation (cubicMap (actualSeedEquation 57 1)) -
      Ideal.Quotient.mk (deformationIdeal equation perturbation) (TrivSqZeroExt.inr perturbation) = 0
    rw [cubicMap_actualSeedEquation, deformation_equation, epsilon_mk, sub_self]
  · change toOriginalRaw (epsilonPolynomial ^ 2) = 0
    rw [map_pow, toOriginalRaw_epsilon, pow_two, originalEpsilon_square]

/-- The canonical map fixes every original polynomial coordinate and epsilon. -/
def toOriginal : GradedDeformation →ₐ[ℂ] ThickBase :=
  Ideal.Quotient.liftₐ ambientIdeal toOriginalRaw (by
    intro p hp
    have hI : ambientIdeal ≤ RingHom.ker toOriginalRaw.toRingHom :=
      Ideal.span_le.mpr (fun _ h => by
        obtain ⟨i,rfl⟩ := h
        exact toOriginalRaw_relations i)
    exact hI hp)

theorem toOriginal_coordinate (i : Fin 5) : toOriginal (coordinate i) = originalPolynomial (X i) := by
  change toOriginalRaw (X (some i)) = _
  simp [toOriginalRaw]

theorem toOriginal_epsilon : toOriginal epsilonElement = originalEpsilon :=
  toOriginalRaw_epsilon

end CycleQ2LiteralGradedDeformation

end

#print axioms CycleQ2LiteralGradedDeformation.ambientIdeal_homogeneous
#print axioms CycleQ2LiteralGradedDeformation.deformationGradedRing
#print axioms CycleQ2LiteralGradedDeformation.toOriginal_coordinate
#print axioms CycleQ2LiteralGradedDeformation.toOriginal_epsilon
