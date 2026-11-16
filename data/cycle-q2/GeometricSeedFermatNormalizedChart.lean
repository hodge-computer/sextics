import Proposal.GeometricSeedFermatNormalized

/-!
# The normalized quotient is the actual weighted Proj chart

For each weight-one coordinate, the literal quotient by the seed equation
and `z_i - 1` is isomorphic over the original complex coefficients to the
native degree-zero homogeneous localization. In one direction, weighted
normalization kills both defining relations. In the other, the chosen
coordinate is already one, so the original cone quotient maps to the
normalized ring and the map extends across the cone localization.

The inverse identities are checked on actual quotient representatives and
actual homogeneous fractions. This identification uses homogeneity alone
and does not assume either smoothness or the relation `r ^ 3 = 2`.

Prepared for `fqlx` with OpenAI ChatGPT assistance, following
Ben Diamond's geometric seed construction.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2SeedFermatNormalizedChart

open MvPolynomial CycleQ2GeometricSeedSmooth CycleQ2SeedFermatCone
open CycleQ2GeometricIncidenceProj CycleQ2SeedFermatProj
  CycleQ2SeedFermatChartRetract CycleQ2SeedFermatNormalized

theorem normalizedIdeal_le_chart_kernel (r : ℂ) (i : Fin 4) :
    normalizedIdeal r i ≤ RingHom.ker (projectiveEvaluate r i) := by
  apply Ideal.span_le.mpr
  rintro _ ⟨j, rfl⟩
  fin_cases j
  · change projectiveEvaluate r i (seedFamily r 0) = 0
    exact projectiveEvaluate_seedFamily r i
  · change projectiveEvaluate r i (X i.castSucc - 1) = 0
    simp only [map_sub, map_one, projectiveEvaluate, eval₂Hom_X',
      coordinateRatio_self, sub_self]

/-- Weighted normalization factors through both literal chart relations. -/
def normalizedToChart (r : ℂ) (i : Fin 4) :
    NormalizedRing r i →ₐ[ℂ] ChartRing r i where
  toRingHom := Ideal.Quotient.lift (normalizedIdeal r i) (projectiveEvaluate r i)
    (fun _ hp => normalizedIdeal_le_chart_kernel r i hp)
  commutes' c := by
    change projectiveEvaluate r i (C c) = chartCoefficient r i c
    simp only [projectiveEvaluate, eval₂Hom_C]

@[simp] theorem normalizedToChart_quotient (r : ℂ) (i : Fin 4)
    (p : SeedPolynomial) :
    normalizedToChart r i (normalizedQuotient r i p) =
      projectiveEvaluate r i p := rfl

theorem coneIdeal_le_normalized_kernel (r : ℂ) (i : Fin 4) :
    Ideal.span {seedFamily r 0} ≤ RingHom.ker (normalizedQuotient r i) := by
  apply Ideal.span_le.mpr
  intro p hp
  obtain rfl := Set.mem_singleton_iff.mp hp
  exact normalizedEquation r i

/-- The original cone quotient maps to the literal normalized quotient. -/
def coneToNormalized (r : ℂ) (i : Fin 4) :
    ConeRing r →ₐ[ℂ] NormalizedRing r i where
  toRingHom := Ideal.Quotient.lift (Ideal.span {seedFamily r 0})
    (normalizedQuotient r i) (fun _ hp => coneIdeal_le_normalized_kernel r i hp)
  commutes' _ := rfl

@[simp] theorem coneToNormalized_quotient (r : ℂ) (i : Fin 4)
    (p : SeedPolynomial) :
    coneToNormalized r i (coneQuotient r p) = normalizedQuotient r i p := rfl

@[simp] theorem coneToNormalized_coordinate (r : ℂ) (i : Fin 4) (j : Fin 5) :
    coneToNormalized r i (coordinateClass r j) = normalizedCoordinate r i j := rfl

/-- Since the chosen coordinate is one, the cone map extends to the
actual localization at that coordinate. -/
def localizationToNormalized (r : ℂ) (i : Fin 4) :
    CoordinateRing r i.castSucc →ₐ[ℂ] NormalizedRing r i :=
  IsLocalization.Away.liftAlgHom (S := CoordinateRing r i.castSucc)
    (f := coneToNormalized r i) (coordinateClass r i.castSucc) (by
      change IsUnit (normalizedCoordinate r i i.castSucc)
      rw [normalizedCoordinate_self]
      exact isUnit_one)

@[simp] theorem localizationToNormalized_algebraMap (r : ℂ) (i : Fin 4)
    (a : ConeRing r) :
    localizationToNormalized r i
        (algebraMap (ConeRing r) (CoordinateRing r i.castSucc) a) =
      coneToNormalized r i a := by
  dsimp only [localizationToNormalized]
  have hunit : IsUnit (coneToNormalized r i (coordinateClass r i.castSucc)) := by
    rw [coneToNormalized_coordinate, normalizedCoordinate_self]
    exact isUnit_one
  exact IsLocalization.Away.lift_eq (coordinateClass r i.castSucc) hunit a

@[simp] theorem localizationToNormalized_invSelf (r : ℂ) (i : Fin 4) :
    localizationToNormalized r i
      (IsLocalization.Away.invSelf (coordinateClass r i.castSucc)) = 1 := by
  have h := congrArg (localizationToNormalized r i)
    (IsLocalization.Away.mul_invSelf (S := CoordinateRing r i.castSucc)
      (coordinateClass r i.castSucc))
  simpa only [map_mul, map_one, localizationToNormalized_algebraMap,
    coneToNormalized_coordinate, normalizedCoordinate_self, one_mul] using h

/-- Restrict the localized cone map to the native degree-zero chart. -/
def chartToNormalized (r : ℂ) (i : Fin 4) :
    ChartRing r i →ₐ[ℂ] NormalizedRing r i :=
  (localizationToNormalized r i).comp (chartInclusion r i)

theorem chartToNormalized_homogeneousFraction (r : ℂ) (i : Fin 4)
    (n : ℕ) (p : SeedPolynomial) (hp : p.IsWeightedHomogeneous geometricWeight n) :
    chartToNormalized r i (homogeneousFraction r i n p hp) =
      normalizedQuotient r i p := by
  change localizationToNormalized r i ((homogeneousFraction r i n p hp).val) = _
  rw [homogeneousFraction_val, map_mul, map_pow, localizationToNormalized_algebraMap,
    localizationToNormalized_invSelf, one_pow, mul_one, coneToNormalized_quotient]

@[simp] theorem chartToNormalized_coordinateRatio (r : ℂ) (i : Fin 4) (j : Fin 5) :
    chartToNormalized r i (coordinateRatio r i j) = normalizedCoordinate r i j :=
  chartToNormalized_homogeneousFraction r i (geometricWeight j) (X j)
    (isWeightedHomogeneous_X ℂ geometricWeight j)

theorem chartToNormalized_projectiveEvaluate (r : ℂ) (i : Fin 4)
    (p : SeedPolynomial) :
    chartToNormalized r i (projectiveEvaluate r i p) = normalizedQuotient r i p := by
  have h : (chartToNormalized r i).toRingHom.comp (projectiveEvaluate r i) =
      normalizedQuotient r i := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp only [RingHom.comp_apply, projectiveEvaluate, eval₂Hom_C]
      exact (chartToNormalized r i).commutes c
    · intro j
      simp only [RingHom.comp_apply, projectiveEvaluate, eval₂Hom_X']
      exact chartToNormalized_coordinateRatio r i j
  exact RingHom.congr_fun h p

theorem chartToNormalized_comp_normalizedToChart (r : ℂ) (i : Fin 4) :
    (chartToNormalized r i).comp (normalizedToChart r i) =
      AlgHom.id ℂ (NormalizedRing r i) := by
  apply AlgHom.ext
  intro a
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  change chartToNormalized r i (normalizedToChart r i (normalizedQuotient r i p)) =
    normalizedQuotient r i p
  rw [normalizedToChart_quotient, chartToNormalized_projectiveEvaluate]

theorem normalizedToChart_comp_chartToNormalized (r : ℂ) (i : Fin 4) :
    (normalizedToChart r i).comp (chartToNormalized r i) =
      AlgHom.id ℂ (ChartRing r i) := by
  apply AlgHom.ext
  intro z
  obtain ⟨n, a, ha, rfl⟩ :=
    HomogeneousLocalization.Away.mk_surjective (coneGrade r) (coordinate_mem_grade r i) z
  obtain ⟨p, hp, rfl⟩ := ha
  have hp' : p.IsWeightedHomogeneous geometricWeight n := by simpa using hp
  change normalizedToChart r i (chartToNormalized r i (homogeneousFraction r i n p hp')) =
    homogeneousFraction r i n p hp'
  rw [chartToNormalized_homogeneousFraction, normalizedToChart_quotient,
    projectiveEvaluate_homogeneousFraction r i n p hp']

/-- The actual normalized quotient and the native Proj chart are isomorphic
over the original complex coefficient field. -/
def normalizedChartEquiv (r : ℂ) (i : Fin 4) :
    NormalizedRing r i ≃ₐ[ℂ] ChartRing r i :=
  AlgEquiv.ofAlgHom (normalizedToChart r i) (chartToNormalized r i)
    (normalizedToChart_comp_chartToNormalized r i)
    (chartToNormalized_comp_normalizedToChart r i)

@[simp] theorem normalizedChartEquiv_quotient (r : ℂ) (i : Fin 4)
    (p : SeedPolynomial) :
    normalizedChartEquiv r i (normalizedQuotient r i p) =
      projectiveEvaluate r i p := rfl

@[simp] theorem normalizedChartEquiv_coordinate (r : ℂ) (i : Fin 4) (j : Fin 5) :
    normalizedChartEquiv r i (normalizedCoordinate r i j) = coordinateRatio r i j := by
  change projectiveEvaluate r i (X j) = coordinateRatio r i j
  simp only [projectiveEvaluate, eval₂Hom_X']

@[simp] theorem normalizedChartEquiv_symm_coordinateRatio
    (r : ℂ) (i : Fin 4) (j : Fin 5) :
    (normalizedChartEquiv r i).symm (coordinateRatio r i j) =
      normalizedCoordinate r i j :=
  chartToNormalized_coordinateRatio r i j

end CycleQ2SeedFermatNormalizedChart

end

#print axioms CycleQ2SeedFermatNormalizedChart.chartToNormalized_comp_normalizedToChart
#print axioms CycleQ2SeedFermatNormalizedChart.normalizedToChart_comp_chartToNormalized
#print axioms CycleQ2SeedFermatNormalizedChart.normalizedChartEquiv
