import Proposal.GeometricSeedFermatProjSmooth

/-!
# An explicit complex point of the actual weighted projective seed

The weighted coordinates `[1 : 0 : 0 : 0 : -1]` satisfy the zero-cubic
Fermat equation and lie in the degree-one `z₀` chart. Evaluation first
descends through the literal cone quotient, then extends to its `z₀`
localization and restricts to the native degree-zero chart ring. The
corresponding scheme morphism is a section of the original structure
morphism to `Spec ℂ`, and in particular proves nonemptiness.

Prepared for `fqlx` with OpenAI ChatGPT assistance,
following the geometric seed in Ben Diamond's surface-section argument.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2SeedFermatPoint

open CategoryTheory AlgebraicGeometry MvPolynomial
open CycleQ2GeometricSeedSmooth CycleQ2SeedFermatCone
  CycleQ2SeedFermatProj CycleQ2SeedFermatChartRetract
  CycleQ2SeedFermatProjSmooth

/-- A fixed representative of the complex point; no additional root is needed. -/
def pointCoordinates : Fin 5 → ℂ := ![1, 0, 0, 0, -1]

/-- Literal polynomial evaluation at the chosen weighted coordinates. -/
def polynomialEvaluation : SeedPolynomial →+* ℂ :=
  eval₂Hom (RingHom.id ℂ) pointCoordinates

theorem polynomialEvaluation_seedFamily (r : ℂ) (hr : r ^ 3 = 2) :
    polynomialEvaluation (seedFamily r 0) = 0 := by
  rw [seedFamily_zero_of_cube_two r hr]
  norm_num [polynomialEvaluation, pointCoordinates, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four]

theorem coneIdeal_le_evaluation_kernel (r : ℂ) (hr : r ^ 3 = 2) :
    Ideal.span {seedFamily r 0} ≤ RingHom.ker polynomialEvaluation := by
  apply Ideal.span_le.mpr
  intro p hp
  obtain rfl := Set.mem_singleton_iff.mp hp
  exact polynomialEvaluation_seedFamily r hr

/-- Evaluation on the original one-equation affine cone quotient. -/
def coneEvaluation (r : ℂ) (hr : r ^ 3 = 2) : ConeRing r →+* ℂ :=
  Ideal.Quotient.lift (Ideal.span {seedFamily r 0}) polynomialEvaluation
    (fun _ hp => coneIdeal_le_evaluation_kernel r hr hp)

@[simp] theorem coneEvaluation_coneQuotient (r : ℂ) (hr : r ^ 3 = 2)
    (p : SeedPolynomial) :
    coneEvaluation r hr (coneQuotient r p) = polynomialEvaluation p := rfl

@[simp] theorem coneEvaluation_coordinate (r : ℂ) (hr : r ^ 3 = 2)
    (j : Fin 5) :
    coneEvaluation r hr (coordinateClass r j) = pointCoordinates j := by
  change polynomialEvaluation (X j) = pointCoordinates j
  simp only [polynomialEvaluation, eval₂Hom_X']

/-- The evaluation preserves the original complex coefficient action. -/
def coneEvaluationAlgHom (r : ℂ) (hr : r ^ 3 = 2) :
    ConeRing r →ₐ[ℂ] ℂ where
  toRingHom := coneEvaluation r hr
  commutes' c := by
    change polynomialEvaluation (C c) = c
    simp only [polynomialEvaluation, eval₂Hom_C, RingHom.id_apply]

/-- The `z₀` coordinate evaluates to one, so evaluation extends to the
actual full localization at `z₀`. -/
def localizedEvaluation (r : ℂ) (hr : r ^ 3 = 2) :
    CoordinateRing r 0 →ₐ[ℂ] ℂ :=
  IsLocalization.Away.liftAlgHom (S := CoordinateRing r 0)
    (f := coneEvaluationAlgHom r hr) (coordinateClass r 0) (by
      change IsUnit (coneEvaluation r hr (coordinateClass r 0))
      rw [coneEvaluation_coordinate]
      exact isUnit_one)

@[simp] theorem localizedEvaluation_algebraMap (r : ℂ) (hr : r ^ 3 = 2)
    (a : ConeRing r) :
    localizedEvaluation r hr (algebraMap (ConeRing r) (CoordinateRing r 0) a) =
      coneEvaluation r hr a := by
  dsimp only [localizedEvaluation]
  have hunit : IsUnit (coneEvaluationAlgHom r hr (coordinateClass r 0)) := by
    change IsUnit (coneEvaluation r hr (coordinateClass r 0))
    rw [coneEvaluation_coordinate]
    exact isUnit_one
  exact IsLocalization.Away.lift_eq (coordinateClass r 0) hunit a

@[simp] theorem localizedEvaluation_invSelf (r : ℂ) (hr : r ^ 3 = 2) :
    localizedEvaluation r hr (IsLocalization.Away.invSelf (coordinateClass r 0)) = 1 := by
  have h := congrArg (localizedEvaluation r hr)
    (IsLocalization.Away.mul_invSelf (S := CoordinateRing r 0) (coordinateClass r 0))
  simpa only [map_mul, map_one, localizedEvaluation_algebraMap,
    coneEvaluation_coordinate, pointCoordinates, Matrix.cons_val_zero, one_mul] using h

/-- Restriction of the actual localized evaluation to the native Proj chart. -/
def chartEvaluation (r : ℂ) (hr : r ^ 3 = 2) : ChartRing r 0 →ₐ[ℂ] ℂ :=
  (localizedEvaluation r hr).comp (chartInclusion r 0)

theorem chartEvaluation_coordinateRatio (r : ℂ) (hr : r ^ 3 = 2) (j : Fin 5) :
    chartEvaluation r hr (coordinateRatio r 0 j) = pointCoordinates j := by
  change localizedEvaluation r hr ((coordinateRatio r 0 j).val) = pointCoordinates j
  rw [coordinateRatio_val, map_mul, map_pow]
  change localizedEvaluation r hr
      (algebraMap (ConeRing r) (CoordinateRing r 0) (coneQuotient r (X j))) *
      localizedEvaluation r hr (IsLocalization.Away.invSelf (coordinateClass r 0)) ^
        CycleQ2GeometricIncidenceProj.geometricWeight j = pointCoordinates j
  rw [localizedEvaluation_algebraMap, localizedEvaluation_invSelf, one_pow, mul_one]
  exact coneEvaluation_coordinate r hr j

/-- The complex point first lands in the native `z₀` affine chart. -/
def chartPoint (r : ℂ) (hr : r ^ 3 = 2) :
    Spec (CommRingCat.of ℂ) ⟶ (coordinateOpen r 0).toScheme :=
  Spec.map (CommRingCat.ofHom (chartEvaluation r hr).toRingHom) ≫
    (coordinateChart r 0).inv

/-- The point `[1 : 0 : 0 : 0 : -1]` on the actual weighted projective seed. -/
def seedPoint (r : ℂ) (hr : r ^ 3 = 2) :
    Spec (CommRingCat.of ℂ) ⟶ threefold r :=
  chartPoint r hr ≫ (coordinateOpen r 0).ι

/-- This is a complex-valued point for the original structure morphism. -/
theorem seedPoint_overComplex (r : ℂ) (hr : r ^ 3 = 2) :
    seedPoint r hr ≫ threefoldToComplex r = 𝟙 (Spec (CommRingCat.of ℂ)) := by
  have hc :
      CommRingCat.ofHom (algebraMap ℂ (ChartRing r 0)) ≫
        CommRingCat.ofHom (chartEvaluation r hr).toRingHom =
      𝟙 (CommRingCat.of ℂ) := by
    ext c
    exact (chartEvaluation r hr).commutes c
  simp only [seedPoint, chartPoint, Category.assoc]
  rw [coordinateChart_overComplex, ← Spec.map_comp, hc, Spec.map_id]

/-- The explicit complex point proves that the actual projective seed is nonempty. -/
theorem threefold_nonempty (r : ℂ) (hr : r ^ 3 = 2) : Nonempty (threefold r) :=
  ⟨seedPoint r hr (default : Spec (CommRingCat.of ℂ))⟩

end CycleQ2SeedFermatPoint

end

#print axioms CycleQ2SeedFermatPoint.polynomialEvaluation_seedFamily
#print axioms CycleQ2SeedFermatPoint.chartEvaluation_coordinateRatio
#print axioms CycleQ2SeedFermatPoint.seedPoint_overComplex
#print axioms CycleQ2SeedFermatPoint.threefold_nonempty
