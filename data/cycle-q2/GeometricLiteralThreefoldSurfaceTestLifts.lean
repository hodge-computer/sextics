import Proposal.GeometricLiteralThreefoldLiftDifference
import Proposal.GeometricLiteralThreefoldTriangleLifts
import Proposal.GeometricLiteralNativeCotangent
import Proposal.GeometricLiteralNativeHomogeneousFractions

/-!
# The independent test deformation restricted to the cubic surface

On a native surface overlap, normalize the original homogeneous coordinates
in the thick ring, then read their two components in the trivialization
given by a vertex splitting. They solve the same first-order sextic as the
ambient chart lifts. Differences are the original Kodaira–Spencer derivation.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option maxHeartbeats 500000
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2LiteralThreefoldSurfaceTestLifts

open MvPolynomial HomogeneousLocalization CycleQ2LiteralProjectiveIntersections
  CycleQ2LiteralProjectiveIntersectionKernel CycleQ2LiteralProjectiveIntersectionRestrictions
  CycleQ2LiteralProjectiveIntersectionSplittings CycleQ2LiteralProjectiveIntersectionComplex
  CycleQ2GeometricSquareZeroSplittings CycleQ2GeometricSquareZeroCoefficientDerivation
  CycleQ2LiteralNativeKodairaSpencer CycleQ2LiteralNativeHomogeneousFractions
  CycleQ2LiteralGradedDeformation CycleQ2LiteralProjectiveDeformation
  CycleQ2LiteralThreefoldChartLift CycleQ2LiteralThreefoldLiftDifference
  CycleQ2LiteralThreefoldKodairaSpencer CycleQ2LiteralThreefoldResidueCoordinates
  CycleQ2IncidenceDehomogenizedChart CycleQ2GeometricIncidenceProj
  CycleQ2LiteralAbelJacobiContraction CycleQ2LiteralAbelJacobiEquations
  CycleQ2GeometricLiteralDirection CycleQ2GeometricSurfaceAdjunction
  CycleQ2IncidencePolynomialJacobianBinding CycleQ2LiteralThreefoldLiftTransition
  CycleQ2LiteralThreefoldTangentCoordinates CycleQ2LiteralThreefoldTriangleLifts
  CycleQ2LiteralThreefoldResidueChartMaps

attribute [local instance] nativeReductionAlgebra thickComplexAlgebra closedComplexAlgebra
  thickComplexSMul closedComplexSMul thickComplexModule closedComplexModule complexReductionTower

abbrev chartIndex (v : Vertex) : Fin 4 := v.2.succ

def coefficient (s : Finset Vertex) (a : Fin 4) (ha : Admissible s a) :
    Derivation ℂ (ThickRing s) (ClosedRing s) :=
  coefficientDerivation (epsilonKernelEquiv s) (projectiveSplittingAlgHom s a ha)
    (projectiveSplittingAlgHom_reduction s a ha)

/-- The true first-order Taylor components of a function on the thickened surface. -/
def splitJet (s : Finset Vertex) (a : Fin 4) (ha : Admissible s a) :
    ThickRing s →ₐ[ℂ] Jet (ClosedRing s) where
  toFun b := (nativeReductionAlgHom s b, coefficient s a ha b)
  map_zero' := by apply TrivSqZeroExt.ext <;> simp
  map_one' := by apply TrivSqZeroExt.ext <;> simp
  map_add' x y := by apply TrivSqZeroExt.ext <;> simp
  map_mul' x y := by
    apply TrivSqZeroExt.ext
    · exact map_mul _ _ _
    · change coefficient s a ha (x * y) = _ * _ + _ * _
      rw [Derivation.leibniz, Algebra.smul_def, Algebra.smul_def]
      rw [mul_comm (algebraMap (ThickRing s) (ClosedRing s) y)]
      rfl
  commutes' c := by
    apply TrivSqZeroExt.ext
    · exact (nativeReductionAlgHom s).commutes c
    · exact Derivation.map_algebraMap _ c

theorem splitJet_epsilon (s : Finset Vertex) (a : Fin 4) (ha : Admissible s a) :
    splitJet s a ha (nativeEpsilon s) = TrivSqZeroExt.inr 1 := by
  apply TrivSqZeroExt.ext
  · exact nativeReduction_epsilon s
  · change coefficient s a ha (nativeEpsilon s) = 1
    rw [← CycleQ2LiteralNativeCotangent.epsilon_one, coefficient, coefficientDerivation_epsilon_one]

theorem splitJet_difference (s : Finset Vertex) (a b : Fin 4)
    (ha : Admissible s a) (hb : Admissible s b) (x : ThickRing s) :
    (splitJet s a ha x).snd - (splitJet s b hb x).snd =
      kodairaSpencer s a b ha hb (nativeReduction s x) :=
  coefficientDerivation_change (epsilonKernelEquiv s) (projectiveSplittingAlgHom s a ha) _
    (projectiveSplittingAlgHom s b hb) _ x

abbrev normalizedCoordinate (s : Finset Vertex) (v : Vertex) (hv : v ∈ s) (j : Fin 5) :=
  normalized s v hv (coordinate j) (coordinate_mem_grade j)

def inverseCoordinate (s : Finset Vertex) (v : Vertex) (hv : v ∈ s) : ThickCone s :=
  ↑((coordinateUnit s v hv)⁻¹)

theorem normalizedCoordinate_val (s : Finset Vertex) (v : Vertex) (hv : v ∈ s) (j : Fin 5) :
    (normalizedCoordinate s v hv j).val = inverseCoordinate s v hv ^ geometricWeight j *
      algebraMap GradedDeformation (ThickCone s) (coordinate j) := by
  have H := normalized_val_mul s v hv (coordinate j) (coordinate_mem_grade j)
  rw [← coordinateUnit_value s v hv] at H
  let u := coordinateUnit s v hv
  change _ * (u : ThickCone s) ^ geometricWeight j = _ at H
  rw [← H]
  change _ = (↑(u⁻¹) : ThickCone s) ^ _ * (_ * (u : ThickCone s) ^ _)
  rw [mul_left_comm, ← mul_pow, Units.inv_mul, one_pow, mul_one]

theorem chartIndex_castSucc (v : Vertex) :
    (chartIndex v).castSucc = CycleQ2SeedQuotientFiniteFree.remainingIndex v.2 := by
  rcases v with ⟨a,l⟩
  fin_cases l <;> rfl

theorem normalized_coordinate_self (s : Finset Vertex) (v : Vertex) (hv : v ∈ s) :
    normalizedCoordinate s v hv (chartIndex v).castSucc = 1 := by
  apply HomogeneousLocalization.val_injective
  rw [normalizedCoordinate_val, weight_castSucc, pow_one, HomogeneousLocalization.val_one]
  rw [chartIndex_castSucc]
  change _ * coordinateValue s v = 1
  rw [← coordinateUnit_value s v hv]
  exact Units.inv_mul _

/-- The coordinates are normalized in the actual homogeneous localization.
The extra affine variable is (w + X₂²)/Xᵢ². -/
def thickX (s : Finset Vertex) (v : Vertex) (hv : v ∈ s) : Index → ThickRing s
  | none => normalizedCoordinate s v hv (Fin.last 4) + normalizedCoordinate s v hv (2 : Fin 4).castSucc ^ 2
  | some a => normalizedCoordinate s v hv ((chartIndex v).succAbove a).castSucc

theorem thickX_linear (s : Finset Vertex) (v : Vertex) (hv : v ∈ s) (j : Fin 4) :
    aeval (thickX s v hv) (linearCoordinate (S := ℂ) (chartIndex v) j) =
      normalizedCoordinate s v hv j.castSucc := by
  obtain rfl | ⟨r,rfl⟩ := (chartIndex v).eq_self_or_eq_succAbove j
  · rw [linearCoordinate_self, map_one, normalized_coordinate_self]
  · rw [linearCoordinate_succAbove, aeval_X]
    rfl

private theorem thickX_dehomogenize (s : Finset Vertex) (v : Vertex) (hv : v ∈ s)
    (p : MvPolynomial (Fin 5) ℂ) :
    aeval (thickX s v hv) (dehomogenize (chartIndex v) p) = aeval (normalizedCoordinate s v hv) p := by
  have H : (aeval (thickX s v hv)).comp (dehomogenize (S := ℂ) (chartIndex v)) =
      aeval (normalizedCoordinate s v hv) := by
    apply MvPolynomial.algHom_ext
    intro j
    refine Fin.lastCases ?_ (fun l => ?_) j
    · rw [AlgHom.comp_apply, dehomogenize_last, map_sub, map_pow, aeval_X, thickX_linear, aeval_X]
      change _ + _ - _ = _
      abel
    · rw [AlgHom.comp_apply, dehomogenize_castSucc, thickX_linear, aeval_X]
  exact AlgHom.congr_fun H p

private def valAlg (s : Finset Vertex) : ThickRing s →ₐ[ℂ] ThickCone s where
  toRingHom := algebraMap _ _
  commutes' := thickCoefficient_val s

private def raw (s : Finset Vertex) : MvPolynomial (Fin 5) ℂ →ₐ[ℂ] ThickCone s :=
  (IsScalarTower.toAlgHom ℂ GradedDeformation (ThickCone s)).comp
    (quotientMap.comp includePolynomial)

private theorem raw_X (s : Finset Vertex) (j : Fin 5) :
    raw s (X j) = algebraMap GradedDeformation (ThickCone s) (coordinate j) := by
  change algebraMap GradedDeformation (ThickCone s) (quotientMap (rename some (X j))) = _
  rw [rename_X]
  rfl

private theorem thickX_homogeneous (s : Finset Vertex) (v : Vertex) (hv : v ∈ s)
    (p : MvPolynomial (Fin 5) ℂ) {n : ℕ} (hp : p.IsWeightedHomogeneous geometricWeight n) :
    (aeval (thickX s v hv) (dehomogenize (chartIndex v) p)).val =
      inverseCoordinate s v hv ^ n * raw s p := by
  rw [thickX_dehomogenize]
  let y := fun j : Fin 5 => raw s (X j)
  have hy : aeval y = raw s := by ext j; exact aeval_X y j
  have h : (valAlg s).comp (aeval (normalizedCoordinate s v hv)) =
      aeval (fun j => inverseCoordinate s v hv ^ geometricWeight j * y j) := by
    apply MvPolynomial.algHom_ext
    intro j
    rw [AlgHom.comp_apply, aeval_X, aeval_X]
    exact (normalizedCoordinate_val s v hv j).trans (by rw [show y j = _ from raw_X s j])
  change ((valAlg s).comp (aeval (normalizedCoordinate s v hv))) p = _
  rw [h]
  calc
    _ = inverseCoordinate s v hv ^ n * aeval y p :=
      weighted_homogeneous_eval_scale (algebraMap ℂ (ThickCone s)) y _ p n hp
    _ = _ := by rw [hy]

/-- The thick surface coordinates solve the literal sextic F − ε B*. -/
theorem thickEquation (s : Finset Vertex) (v : Vertex) (hv : v ∈ s) :
    aeval (thickX s v hv) (seedF (chartIndex v)) =
      nativeEpsilon s * aeval (thickX s v hv) (test (chartIndex v)) := by
  have he := quotientMap_relations (1 : Fin 3)
  change quotientMap (includePolynomial _ - epsilonPolynomial * includePolynomial _) = 0 at he
  rw [map_sub, map_mul, sub_eq_zero] at he
  have hraw : raw s (pointEquationF (seedPoint (57 : ℂ) Complex.I)) =
      (nativeEpsilon s).val * raw s ambientTest := by
    rw [literalPointEquationF, nativeEpsilon_val]
    change algebraMap GradedDeformation (ThickCone s) (quotientMap (includePolynomial _)) =
      algebraMap GradedDeformation (ThickCone s) epsilonElement *
        algebraMap GradedDeformation (ThickCone s) (quotientMap (includePolynomial _))
    rw [he, map_mul]
    rfl
  apply HomogeneousLocalization.val_injective
  change (aeval (thickX s v hv) (dehomogenize _ (pointEquationF _))).val = _
  rw [HomogeneousLocalization.val_mul, thickX_homogeneous _ _ _ _ (pointEquationF_homogeneous _),
    show test (chartIndex v) = dehomogenize _ ambientTest from rfl,
    thickX_homogeneous _ _ _ _ test_homogeneous, hraw, mul_left_comm]

/-- The cubic defining the surface inside the sextic is unchanged throughout
the independent test deformation. -/
theorem thickCubic (s : Finset Vertex) (v : Vertex) (hv : v ∈ s) :
    aeval (thickX s v hv) (seedH (chartIndex v)) = 0 := by
  have he := quotientMap_relations (0 : Fin 3)
  have hraw : raw s (pointEquationH (seedPoint (57 : ℂ) Complex.I)) = 0 := by
    rw [literalPointEquationH]
    change algebraMap GradedDeformation (ThickCone s) (quotientMap (includePolynomial _)) = 0
    exact (congrArg (algebraMap GradedDeformation (ThickCone s)) he).trans (map_zero _)
  apply HomogeneousLocalization.val_injective
  change (aeval (thickX s v hv) (dehomogenize _ (pointEquationH _))).val = _
  rw [thickX_homogeneous _ _ _ _ (pointEquationH_homogeneous _), hraw, mul_zero,
    HomogeneousLocalization.val_zero]

private theorem eval_splitJet (s : Finset Vertex) (v : Vertex) (hv : v ∈ s)
    (a : Fin 4) (ha : Admissible s a) (p : P) :
    aeval (fun j => splitJet s a ha (thickX s v hv j)) p = splitJet s a ha (aeval (thickX s v hv) p) := by
  have h : aeval (fun j => splitJet s a ha (thickX s v hv j)) =
      (splitJet s a ha).comp (aeval (thickX s v hv)) := by
    apply MvPolynomial.algHom_ext
    intro j
    rw [AlgHom.comp_apply, aeval_X, aeval_X]
  exact AlgHom.congr_fun h p

/-- A chosen native vertex splitting gives an actual lifted point in any
weight-one chart represented in the intersection. -/
def surfaceLift (s : Finset Vertex) (v : Vertex) (hv : v ∈ s)
    (a : Fin 4) (ha : Admissible s a) : Lift (chartIndex v) (ClosedRing s) where
  x j := splitJet s a ha (thickX s v hv j)
  equation := by
    rw [eval_splitJet, eval_splitJet, thickEquation, map_mul, splitJet_epsilon]

theorem surfaceLift_cubic (s : Finset Vertex) (v : Vertex) (hv : v ∈ s) (a : Fin 4) (ha : Admissible s a) :
    aeval (surfaceLift s v hv a ha).x (seedH (chartIndex v)) = 0 := by
  exact (eval_splitJet s v hv a ha _).trans
    ((congrArg (splitJet s a ha) (thickCubic s v hv)).trans (map_zero _))

private def reducedEval (s : Finset Vertex) (v : Vertex) (hv : v ∈ s) : P →ₐ[ℂ] ClosedRing s :=
  (nativeReductionAlgHom s).comp (aeval (thickX s v hv))

/-- The reduced surface point of the fixed threefold in this chart. -/
def fixedPoint (s : Finset Vertex) (v : Vertex) (hv : v ∈ s) :
    T (chartIndex v) →ₐ[ℂ] ClosedRing s :=
  Ideal.Quotient.liftₐ (fixedIdeal (chartIndex v)) (reducedEval s v hv) (by
    change fixedIdeal (chartIndex v) ≤ RingHom.ker (reducedEval s v hv).toRingHom
    apply (Ideal.span_singleton_le_iff_mem (RingHom.ker (reducedEval s v hv).toRingHom)).mpr
    change nativeReduction s (aeval (thickX s v hv) (seedF (chartIndex v))) = 0
    rw [thickEquation, map_mul, nativeReduction_epsilon, zero_mul])

theorem fixedPoint_q (s : Finset Vertex) (v : Vertex) (hv : v ∈ s) (p : P) :
    fixedPoint s v hv (q (chartIndex v) p) = nativeReduction s (aeval (thickX s v hv) p) := rfl

def polynomialImage : MvPolynomial (Fin 5) ℂ →ₐ[ℂ] GradedDeformation :=
  quotientMap.comp includePolynomial

theorem polynomialImage_homogeneous (p : MvPolynomial (Fin 5) ℂ) {n : ℕ}
    (hp : p.IsWeightedHomogeneous geometricWeight n) : polynomialImage p ∈ deformationGrade n :=
  quotientMap_mem_grade (includePolynomial_homogeneous hp)

/-- The chart restriction of every homogeneous numerator is its literal
projective fraction p/Xᵥⁿ in the actual native surface ring. -/
theorem fixedPoint_homogeneous (s : Finset Vertex) (v : Vertex) (hv : v ∈ s)
    (p : MvPolynomial (Fin 5) ℂ) {n : ℕ} (hp : p.IsWeightedHomogeneous geometricWeight n) :
    fixedPoint s v hv (q (chartIndex v) (dehomogenize (chartIndex v) p)) =
      nativeReduction s (normalized s v hv (polynomialImage p) (polynomialImage_homogeneous p hp)) := by
  rw [fixedPoint_q]
  apply congrArg (nativeReduction s)
  apply HomogeneousLocalization.val_injective
  apply ((coordinateValue_isUnit s v hv).pow n).mul_right_cancel
  rw [thickX_homogeneous _ _ _ _ hp, normalized_val_mul, ← coordinateUnit_value s v hv]
  change ((↑(coordinateUnit s v hv)⁻¹ : ThickCone s)^n * raw s p) *
      (coordinateUnit s v hv : ThickCone s)^n = raw s p
  rw [mul_right_comm, ← mul_pow, Units.inv_mul, one_pow, one_mul]

theorem fixedPoint_cubic (s : Finset Vertex) (v : Vertex) (hv : v ∈ s) :
    fixedPoint s v hv (cubicOnT (chartIndex v)) = 0 := by
  change fixedPoint s v hv (q (chartIndex v) (seedH (chartIndex v))) = 0
  rw [fixedPoint_q, thickCubic, map_zero]

theorem surfaceLift_liesOver (s : Finset Vertex) (v : Vertex) (hv : v ∈ s)
    (a : Fin 4) (ha : Admissible s a) : LiesOver (surfaceLift s v hv a ha) (fixedPoint s v hv) := by
  intro j
  rw [fixedPoint_q, aeval_X]
  rfl

/-- The difference of the two Taylor lifts on every fixed chart function
is the given surface Kodaira–Spencer derivation with its original sign. -/
theorem surfaceLift_difference (s : Finset Vertex) (v : Vertex) (hv : v ∈ s)
    (a b : Fin 4) (ha : Admissible s a) (hb : Admissible s b) (p : P) :
    (aeval (surfaceLift s v hv a ha).x p).snd - (aeval (surfaceLift s v hv b hb).x p).snd =
      kodairaSpencer s a b ha hb (fixedPoint s v hv (q (chartIndex v) p)) := by
  change (aeval (fun j => splitJet s a ha (thickX s v hv j)) p).snd -
    (aeval (fun j => splitJet s b hb (thickX s v hv j)) p).snd = _
  rw [eval_splitJet, eval_splitJet, splitJet_difference, fixedPoint_q]

end CycleQ2LiteralThreefoldSurfaceTestLifts
end

#print axioms CycleQ2LiteralThreefoldSurfaceTestLifts.surfaceLift_difference
#print axioms CycleQ2LiteralThreefoldSurfaceTestLifts.fixedPoint_homogeneous
#print axioms CycleQ2LiteralThreefoldSurfaceTestLifts.surfaceLift
