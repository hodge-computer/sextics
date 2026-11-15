import Proposal.GeometricSeedFamilyChartAlgebra
import Proposal.GeometricSeedFamilyNormalized

/-!
# Literal normalized charts of the actual full cubic family

The quotient by the universal equation and `z_i - 1` is isomorphic over
ParameterRing to the native degree-zero Proj chart. Both inverse maps
are constructed on the original quotient and homogeneous fractions.
The induced affine chart is an actual open immersion into the family,
and its structure map is the original parameter-algebra map.

Source-only draft: no Lean elaboration, compilation, or kernel replay
was run. Prepared for `fqlx` with OpenAI ChatGPT assistance, following
Ben Diamond's geometric seed construction.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2SeedFamilyChart

open CategoryTheory AlgebraicGeometry MvPolynomial
open CycleQ2SeedCubicFamily CycleQ2SeedProjectiveFamily
  CycleQ2SeedFamilyNormalized CycleQ2GeometricIncidenceProj

theorem normalizedIdeal_le_chart_kernel (r : ℂ) (i : Fin 4) :
    normalizedIdeal r i ≤ RingHom.ker (projectiveEvaluate r i) := by
  apply Ideal.span_le.mpr
  rintro _ ⟨j, rfl⟩
  fin_cases j
  · change projectiveEvaluate r i (familyEquation r) = 0
    exact projectiveEvaluate_familyEquation r i
  · change projectiveEvaluate r i (X i.castSucc - 1) = 0
    simp only [map_sub, map_one, projectiveEvaluate, eval₂Hom_X',
      coordinateRatio_self, sub_self]

def normalizedToChart (r : ℂ) (i : Fin 4) :
    NormalizedRing r i →ₐ[ParameterRing] ChartRing r i where
  toRingHom := Ideal.Quotient.lift (normalizedIdeal r i) (projectiveEvaluate r i)
    (fun _ hp => normalizedIdeal_le_chart_kernel r i hp)
  commutes' c := by
    change projectiveEvaluate r i (C c) = chartCoefficient r i c
    simp only [projectiveEvaluate, eval₂Hom_C]

@[simp] theorem normalizedToChart_quotient (r : ℂ) (i : Fin 4) (p : FamilyPolynomial) :
    normalizedToChart r i (normalizedQuotient r i p) = projectiveEvaluate r i p := rfl

theorem familyIdeal_le_normalized_kernel (r : ℂ) (i : Fin 4) :
    familyIdeal r ≤ RingHom.ker (normalizedQuotient r i) := by
  apply Ideal.span_le.mpr
  intro p hp
  obtain rfl := Set.mem_singleton_iff.mp hp
  exact normalizedEquation r i

def familyRingToNormalized (r : ℂ) (i : Fin 4) :
    FamilyRing r →ₐ[ParameterRing] NormalizedRing r i where
  toRingHom := Ideal.Quotient.lift (familyIdeal r) (normalizedQuotient r i)
    (fun _ hp => familyIdeal_le_normalized_kernel r i hp)
  commutes' _ := rfl

@[simp] theorem familyRingToNormalized_quotient (r : ℂ) (i : Fin 4)
    (p : FamilyPolynomial) :
    familyRingToNormalized r i (familyQuotient r p) = normalizedQuotient r i p := rfl

@[simp] theorem familyRingToNormalized_coordinate (r : ℂ) (i : Fin 4) (j : Fin 5) :
    familyRingToNormalized r i (familyCoordinate r j) = normalizedCoordinate r i j := rfl

def localizationToNormalized (r : ℂ) (i : Fin 4) :
    CoordinateRing r i →ₐ[ParameterRing] NormalizedRing r i :=
  IsLocalization.Away.liftAlgHom (S := CoordinateRing r i)
    (f := familyRingToNormalized r i) (familyCoordinate r i.castSucc) (by
      change IsUnit (normalizedCoordinate r i i.castSucc)
      rw [normalizedCoordinate_self]
      exact isUnit_one)

@[simp] theorem localizationToNormalized_algebraMap (r : ℂ) (i : Fin 4) (a : FamilyRing r) :
    localizationToNormalized r i (algebraMap (FamilyRing r) (CoordinateRing r i) a) =
      familyRingToNormalized r i a :=
  IsLocalization.Away.lift_eq (familyCoordinate r i.castSucc) _ a

@[simp] theorem localizationToNormalized_invSelf (r : ℂ) (i : Fin 4) :
    localizationToNormalized r i
      (IsLocalization.Away.invSelf (familyCoordinate r i.castSucc)) = 1 := by
  have h := congrArg (localizationToNormalized r i)
    (IsLocalization.Away.mul_invSelf (S := CoordinateRing r i)
      (familyCoordinate r i.castSucc))
  simpa only [map_mul, map_one, localizationToNormalized_algebraMap,
    familyRingToNormalized_coordinate, normalizedCoordinate_self, one_mul] using h

def chartToNormalized (r : ℂ) (i : Fin 4) :
    ChartRing r i →ₐ[ParameterRing] NormalizedRing r i :=
  (localizationToNormalized r i).comp (chartInclusion r i)

theorem chartToNormalized_homogeneousFraction (r : ℂ) (i : Fin 4) (n : ℕ)
    (p : FamilyPolynomial) (hp : p.IsWeightedHomogeneous geometricWeight n) :
    chartToNormalized r i (homogeneousFraction r i n p hp) = normalizedQuotient r i p := by
  change localizationToNormalized r i ((homogeneousFraction r i n p hp).val) = _
  rw [homogeneousFraction_val, map_mul, map_pow, localizationToNormalized_algebraMap,
    localizationToNormalized_invSelf, one_pow, mul_one, familyRingToNormalized_quotient]

@[simp] theorem chartToNormalized_coordinateRatio (r : ℂ) (i : Fin 4) (j : Fin 5) :
    chartToNormalized r i (coordinateRatio r i j) = normalizedCoordinate r i j :=
  chartToNormalized_homogeneousFraction r i (geometricWeight j) (X j)
    (isWeightedHomogeneous_X ParameterRing geometricWeight j)

theorem chartToNormalized_projectiveEvaluate (r : ℂ) (i : Fin 4) (p : FamilyPolynomial) :
    chartToNormalized r i (projectiveEvaluate r i p) = normalizedQuotient r i p := by
  have h : (chartToNormalized r i).toRingHom.comp (projectiveEvaluate r i) =
      normalizedQuotient r i := by
    apply MvPolynomial.ringHom_ext
    · intro c
      change chartToNormalized r i (chartCoefficient r i c) = normalizedQuotient r i (C c)
      exact (chartToNormalized r i).commutes c
    · intro j
      change chartToNormalized r i (coordinateRatio r i j) = normalizedCoordinate r i j
      exact chartToNormalized_coordinateRatio r i j
  exact RingHom.congr_fun h p

theorem chartToNormalized_comp_normalizedToChart (r : ℂ) (i : Fin 4) :
    (chartToNormalized r i).comp (normalizedToChart r i) =
      AlgHom.id ParameterRing (NormalizedRing r i) := by
  apply AlgHom.ext
  intro a
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  change chartToNormalized r i (normalizedToChart r i (normalizedQuotient r i p)) =
    normalizedQuotient r i p
  rw [normalizedToChart_quotient, chartToNormalized_projectiveEvaluate]

theorem normalizedToChart_comp_chartToNormalized (r : ℂ) (i : Fin 4) :
    (normalizedToChart r i).comp (chartToNormalized r i) =
      AlgHom.id ParameterRing (ChartRing r i) := by
  apply AlgHom.ext
  intro z
  obtain ⟨n, a, ha, rfl⟩ :=
    HomogeneousLocalization.Away.mk_surjective (familyGrade r) (coordinate_mem_grade r i) z
  obtain ⟨p, hp, rfl⟩ := ha
  have hp' : p.IsWeightedHomogeneous geometricWeight n := by simpa using hp
  change normalizedToChart r i (chartToNormalized r i (homogeneousFraction r i n p hp')) =
    homogeneousFraction r i n p hp'
  rw [chartToNormalized_homogeneousFraction, normalizedToChart_quotient,
    projectiveEvaluate_homogeneousFraction r i n p hp']

def normalizedChartEquiv (r : ℂ) (i : Fin 4) :
    NormalizedRing r i ≃ₐ[ParameterRing] ChartRing r i :=
  AlgEquiv.ofAlgHom (normalizedToChart r i) (chartToNormalized r i)
    (normalizedToChart_comp_chartToNormalized r i)
    (chartToNormalized_comp_normalizedToChart r i)

def coordinateOpen (r : ℂ) (i : Fin 4) : (family r).Opens :=
  Proj.basicOpen (familyGrade r) (familyCoordinate r i.castSucc)

def coordinateChart (r : ℂ) (i : Fin 4) :
    (coordinateOpen r i).toScheme ≅ Spec (CommRingCat.of (ChartRing r i)) :=
  Proj.basicOpenIsoSpec (familyGrade r) (familyCoordinate r i.castSucc)
    (coordinate_mem_grade r i) (by decide)

theorem coordinateChart_overParameters (r : ℂ) (i : Fin 4) :
    (coordinateChart r i).inv ≫ (coordinateOpen r i).ι ≫ familyToParameters r =
      Spec.map (CommRingCat.ofHom (algebraMap ParameterRing (ChartRing r i))) := by
  change (Proj.basicOpenIsoSpec (familyGrade r) (familyCoordinate r i.castSucc)
      (coordinate_mem_grade r i) (by decide)).inv ≫
      (Proj.basicOpen (familyGrade r) (familyCoordinate r i.castSucc)).ι ≫
      familyToParameters r = _
  rw [Proj.basicOpenIsoSpec_inv_ι_assoc, familyToParameters,
    Proj.awayι_toSpecZero_assoc, ← Spec.map_comp]
  rfl

/-- The normalized affine scheme is the actual coordinate open of the family. -/
def normalizedAffineChart (r : ℂ) (i : Fin 4) :
    normalizedScheme r i ≅ (coordinateOpen r i).toScheme :=
  (Scheme.Spec.mapIso (normalizedChartEquiv r i).symm.toRingEquiv.toCommRingCatIso.op).trans
    (coordinateChart r i).symm

theorem normalizedAffineChart_hom (r : ℂ) (i : Fin 4) :
    (normalizedAffineChart r i).hom =
      Spec.map (CommRingCat.ofHom (normalizedChartEquiv r i).symm.toRingHom) ≫
        (coordinateChart r i).inv := rfl

def normalizedChartToFamily (r : ℂ) (i : Fin 4) : normalizedScheme r i ⟶ family r :=
  (normalizedAffineChart r i).hom ≫ (coordinateOpen r i).ι

instance normalizedChartToFamily_isOpenImmersion (r : ℂ) (i : Fin 4) :
    IsOpenImmersion (normalizedChartToFamily r i) := by
  dsimp only [normalizedChartToFamily]
  infer_instance

/-- The chart uses the original parameter coefficients, with no change of base. -/
theorem normalizedChartToFamily_overParameters (r : ℂ) (i : Fin 4) :
    normalizedChartToFamily r i ≫ familyToParameters r =
      Spec.map (CommRingCat.ofHom (algebraMap ParameterRing (NormalizedRing r i))) := by
  simp only [normalizedChartToFamily, normalizedAffineChart_hom, Category.assoc]
  rw [coordinateChart_overParameters, ← Spec.map_comp]
  apply congrArg Spec.map
  ext c
  exact (normalizedChartEquiv r i).symm.commutes c

/-- Every point of the coordinate open has a point in the actual normalized chart. -/
theorem exists_normalizedChart_preimage (r : ℂ) (i : Fin 4) (x : family r)
    (hx : x ∈ coordinateOpen r i) :
    ∃ q : normalizedScheme r i, normalizedChartToFamily r i q = x := by
  let y : (coordinateOpen r i).toScheme := ⟨x, hx⟩
  refine ⟨(normalizedAffineChart r i).inv y, ?_⟩
  change (coordinateOpen r i).ι
    ((normalizedAffineChart r i).hom ((normalizedAffineChart r i).inv y)) = x
  have hy : (normalizedAffineChart r i).hom ((normalizedAffineChart r i).inv y) = y := by
    change ((normalizedAffineChart r i).inv ≫ (normalizedAffineChart r i).hom) y = y
    rw [(normalizedAffineChart r i).inv_hom_id]
    rfl
  rw [hy]
  rfl

end CycleQ2SeedFamilyChart

end

#print axioms CycleQ2SeedFamilyChart.normalizedChartEquiv
#print axioms CycleQ2SeedFamilyChart.normalizedChartToFamily_overParameters
#print axioms CycleQ2SeedFamilyChart.exists_normalizedChart_preimage
