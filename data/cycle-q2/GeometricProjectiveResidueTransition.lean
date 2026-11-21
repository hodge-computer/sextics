import Proposal.GeometricDehomogenizedCharts
import Proposal.GeometricKaehlerResidue
import Proposal.GeometricResidueFrames

/-!
# Residue transport on the actual projective coordinate overlap

The common ring is the degree-zero homogeneous localization at X1*X2.
The two affine maps are the existing homogeneous restriction maps composed
with the proved dehomogenized-chart equivalences. In particular their
coordinate change is proved in the actual intersection ring.

The complex scalar map is the canonical degree-zero constant map. Local
Jacobian-minor conditions, when used for normalized residue frames, remain
explicit; no assertion that the Jacobian opens cover the curve is made here.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2GeometricProjectiveResidueTransition

open MvPolynomial
open CycleQ2SeedTrace CycleQ2SeedCechTheta CycleQ2NormalConnecting
open CycleQ2GeometricProjectiveCurve CycleQ2GeometricAffineCurveCharts
open CycleQ2GeometricDehomogenizedCharts CycleQ2GeometricAdjunctionOverlap
open CycleQ2GeometricCofactorResidue CycleQ2GeometricResidueFrames

abbrev CoordinateOverlapRing (r θ : ℂ) :=
  HomogeneousLocalization.Away (curveGrade r θ)
    (curveMap r θ (X 1) * curveMap r θ (X 2))

abbrev CoordinateOverlapLocalization (r θ : ℂ) :=
  Localization.Away (curveMap r θ (X 1) * curveMap r θ (X 2))

def firstCoordinateRestriction (r θ : ℂ) :
    CoordinateRing r θ 1 →+* CoordinateOverlapRing r θ :=
  HomogeneousLocalization.awayMap (curveGrade r θ)
    (f := curveMap r θ (X 1)) (g := curveMap r θ (X 2))
    (x := curveMap r θ (X 1) * curveMap r θ (X 2))
    (coordinate_mem_grade r θ 2) rfl

def secondCoordinateRestriction (r θ : ℂ) :
    CoordinateRing r θ 2 →+* CoordinateOverlapRing r θ :=
  HomogeneousLocalization.awayMap (curveGrade r θ)
    (f := curveMap r θ (X 2)) (g := curveMap r θ (X 1))
    (x := curveMap r θ (X 1) * curveMap r θ (X 2))
    (coordinate_mem_grade r θ 1) (mul_comm _ _)

theorem firstCoordinateRestriction_constants (r θ : ℂ) (c : ℂ) :
    firstCoordinateRestriction r θ (constants r θ 1 c) =
      HomogeneousLocalization.fromZeroRingHom (curveGrade r θ)
        (Submonoid.powers (curveMap r θ (X 1) * curveMap r θ (X 2)))
        ⟨curveMap r θ (C c), curveMap_mem_grade r θ (isHomogeneous_C _ c)⟩ := by
  exact HomogeneousLocalization.awayMap_fromZeroRingHom (curveGrade r θ)
    (coordinate_mem_grade r θ 2) rfl
    ⟨curveMap r θ (C c), curveMap_mem_grade r θ (isHomogeneous_C _ c)⟩

theorem secondCoordinateRestriction_constants (r θ : ℂ) (c : ℂ) :
    secondCoordinateRestriction r θ (constants r θ 2 c) =
      HomogeneousLocalization.fromZeroRingHom (curveGrade r θ)
        (Submonoid.powers (curveMap r θ (X 1) * curveMap r θ (X 2)))
        ⟨curveMap r θ (C c), curveMap_mem_grade r θ (isHomogeneous_C _ c)⟩ := by
  exact HomogeneousLocalization.awayMap_fromZeroRingHom (curveGrade r θ)
    (coordinate_mem_grade r θ 1) (mul_comm _ _)
    ⟨curveMap r θ (C c), curveMap_mem_grade r θ (isHomogeneous_C _ c)⟩

/-- The canonical scalar map, with agreement of both chart restrictions proved above. -/
def overlapConstants (r θ : ℂ) : ℂ →+* CoordinateOverlapRing r θ :=
  (firstCoordinateRestriction r θ).comp (constants r θ 1)

instance overlapAlgebra (r θ : ℂ) : Algebra ℂ (CoordinateOverlapRing r θ) :=
  (overlapConstants r θ).toAlgebra

/-- The first actual affine quotient maps to the actual projective intersection. -/
def firstAffineMap (r θ : ℂ) :
    ChartRing ![firstQuadric r, firstCubic θ] →ₐ[ℂ] CoordinateOverlapRing r θ where
  __ := (firstCoordinateRestriction r θ).comp (firstChartEquiv r θ).symm.toRingHom
  commutes' c := by
    change firstCoordinateRestriction r θ
        ((firstChartEquiv r θ).symm
          (algebraMap ℂ (ChartRing ![firstQuadric r, firstCubic θ]) c)) =
      firstCoordinateRestriction r θ (constants r θ 1 c)
    congr 1
    apply (firstChartEquiv r θ).injective
    rw [RingEquiv.apply_symm_apply, firstChartEquiv_constants]

/-- The second actual affine quotient has the same complex scalar map. -/
def secondAffineMap (r θ : ℂ) :
    ChartRing ![secondQuadric r, secondCubic θ] →ₐ[ℂ] CoordinateOverlapRing r θ where
  __ := (secondCoordinateRestriction r θ).comp (secondChartEquiv r θ).symm.toRingHom
  commutes' c := by
    have hc : (secondChartEquiv r θ).symm
        (algebraMap ℂ (ChartRing ![secondQuadric r, secondCubic θ]) c) =
        constants r θ 2 c := by
      apply (secondChartEquiv r θ).injective
      rw [RingEquiv.apply_symm_apply, secondChartEquiv_constants]
    change secondCoordinateRestriction r θ
        ((secondChartEquiv r θ).symm
          (algebraMap ℂ (ChartRing ![secondQuadric r, secondCubic θ]) c)) =
      firstCoordinateRestriction r θ (constants r θ 1 c)
    rw [hc, secondCoordinateRestriction_constants, firstCoordinateRestriction_constants]

def firstCoordinates (r θ : ℂ) (j : Fin 3) : CoordinateOverlapRing r θ :=
  firstAffineMap r θ (Ideal.Quotient.mk (chartIdeal ![firstQuadric r, firstCubic θ]) (X j))

def secondCoordinates (r θ : ℂ) (j : Fin 3) : CoordinateOverlapRing r θ :=
  secondAffineMap r θ
    (Ideal.Quotient.mk (chartIdeal ![secondQuadric r, secondCubic θ]) (X j))

theorem firstCoordinates_eq_ratio (r θ : ℂ) (j : Fin 3) :
    firstCoordinates r θ j =
      firstCoordinateRestriction r θ (coordinateRatio r θ 1 ((1 : Fin 4).succAbove j)) := by
  change firstCoordinateRestriction r θ ((firstChartEquiv r θ).symm _) = _
  rw [firstChartEquiv_symm_variable]

theorem secondCoordinates_eq_ratio (r θ : ℂ) (j : Fin 3) :
    secondCoordinates r θ j =
      secondCoordinateRestriction r θ (coordinateRatio r θ 2 ((2 : Fin 4).succAbove j)) := by
  change secondCoordinateRestriction r θ ((secondChartEquiv r θ).symm _) = _
  rw [secondChartEquiv_symm_variable]

theorem firstCoordinateRestriction_ratio_val (r θ : ℂ) (j : Fin 4) :
    (firstCoordinateRestriction r θ (coordinateRatio r θ 1 j)).val =
      Localization.mk (curveMap r θ (X j) * curveMap r θ (X 2))
        ⟨curveMap r θ (X 1) * curveMap r θ (X 2), Submonoid.mem_powers _⟩ := by
  simp only [firstCoordinateRestriction, coordinateRatio, homogeneousFraction,
    HomogeneousLocalization.awayMap_mk, HomogeneousLocalization.Away.val_mk, pow_one]

theorem secondCoordinateRestriction_ratio_val (r θ : ℂ) (j : Fin 4) :
    (secondCoordinateRestriction r θ (coordinateRatio r θ 2 j)).val =
      Localization.mk (curveMap r θ (X j) * curveMap r θ (X 1))
        ⟨curveMap r θ (X 1) * curveMap r θ (X 2), Submonoid.mem_powers _⟩ := by
  simp only [secondCoordinateRestriction, coordinateRatio, homogeneousFraction,
    HomogeneousLocalization.awayMap_mk, HomogeneousLocalization.Away.val_mk, pow_one]

/-- Coordinate change proved by equality of fractions in the actual common localization. -/
theorem restriction_ratio_change (r θ : ℂ) (j : Fin 4) :
    secondCoordinateRestriction r θ (coordinateRatio r θ 2 j) =
      firstCoordinateRestriction r θ (coordinateRatio r θ 1 j) *
        secondCoordinateRestriction r θ (coordinateRatio r θ 2 1) := by
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.val_mul, secondCoordinateRestriction_ratio_val,
    firstCoordinateRestriction_ratio_val, secondCoordinateRestriction_ratio_val,
    Localization.mk_mul, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [Submonoid.coe_one, Submonoid.coe_mul, one_mul]
  ring

theorem middle_coordinates_mul (r θ : ℂ) :
    firstCoordinates r θ 1 * secondCoordinates r θ 1 = 1 := by
  rw [firstCoordinates_eq_ratio, secondCoordinates_eq_ratio]
  simp only [show (1 : Fin 4).succAbove (1 : Fin 3) = 2 from by decide,
    show (2 : Fin 4).succAbove (1 : Fin 3) = 1 from by decide]
  simpa using (restriction_ratio_change r θ 2).symm

/-- The coordinate ratio x2/x1 is an actual unit on the intersection. -/
def overlapUnit (r θ : ℂ) : (CoordinateOverlapRing r θ)ˣ where
  val := firstCoordinates r θ 1
  inv := secondCoordinates r θ 1
  val_inv := middle_coordinates_mul r θ
  inv_val := by rw [mul_comm, middle_coordinates_mul]

@[simp] theorem overlapUnit_val (r θ : ℂ) :
    (overlapUnit r θ : CoordinateOverlapRing r θ) = firstCoordinates r θ 1 := rfl

@[simp] theorem overlapUnit_inv_val (r θ : ℂ) :
    (↑((overlapUnit r θ)⁻¹) : CoordinateOverlapRing r θ) = secondCoordinates r θ 1 := rfl

theorem coordinate_change (r θ : ℂ) :
    secondCoordinates r θ =
      ![firstCoordinates r θ 0 * (↑((overlapUnit r θ)⁻¹) : CoordinateOverlapRing r θ),
        (↑((overlapUnit r θ)⁻¹) : CoordinateOverlapRing r θ),
        firstCoordinates r θ 2 * (↑((overlapUnit r θ)⁻¹) : CoordinateOverlapRing r θ)] := by
  funext j
  fin_cases j
  · change secondCoordinates r θ 0 = firstCoordinates r θ 0 *
      (↑((overlapUnit r θ)⁻¹) : CoordinateOverlapRing r θ)
    simpa only [overlapUnit_inv_val, firstCoordinates_eq_ratio, secondCoordinates_eq_ratio,
      show (1 : Fin 4).succAbove (0 : Fin 3) = 0 from by decide,
      show (2 : Fin 4).succAbove (0 : Fin 3) = 0 from by decide,
      show (2 : Fin 4).succAbove (1 : Fin 3) = 1 from by decide]
      using restriction_ratio_change r θ 0
  · rfl
  · change secondCoordinates r θ 2 = firstCoordinates r θ 2 *
      (↑((overlapUnit r θ)⁻¹) : CoordinateOverlapRing r θ)
    simpa only [overlapUnit_inv_val, firstCoordinates_eq_ratio, secondCoordinates_eq_ratio,
      show (1 : Fin 4).succAbove (2 : Fin 3) = 3 from by decide,
      show (2 : Fin 4).succAbove (2 : Fin 3) = 3 from by decide,
      show (2 : Fin 4).succAbove (1 : Fin 3) = 1 from by decide]
      using restriction_ratio_change r θ 3

/-! ## The actual equation rows on the overlap -/

def firstPolynomialMap (r θ : ℂ) : AffinePoly →ₐ[ℂ] CoordinateOverlapRing r θ :=
  (firstAffineMap r θ).comp (Ideal.Quotient.mkₐ ℂ (chartIdeal ![firstQuadric r, firstCubic θ]))

def secondPolynomialMap (r θ : ℂ) : AffinePoly →ₐ[ℂ] CoordinateOverlapRing r θ :=
  (secondAffineMap r θ).comp (Ideal.Quotient.mkₐ ℂ (chartIdeal ![secondQuadric r, secondCubic θ]))

@[simp] theorem firstPolynomialMap_X (r θ : ℂ) (j : Fin 3) :
    firstPolynomialMap r θ (X j) = firstCoordinates r θ j := rfl

@[simp] theorem secondPolynomialMap_X (r θ : ℂ) (j : Fin 3) :
    secondPolynomialMap r θ (X j) = secondCoordinates r θ j := rfl

theorem firstPolynomialMap_equation (r θ : ℂ) (i : Fin 2) :
    firstPolynomialMap r θ (![firstQuadric r, firstCubic θ] i) = 0 := by
  have hz : Ideal.Quotient.mk (chartIdeal ![firstQuadric r, firstCubic θ])
      (![firstQuadric r, firstCubic θ] i) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨i, rfl⟩)
  exact (congrArg (firstAffineMap r θ) hz).trans (map_zero _)

theorem secondPolynomialMap_equation (r θ : ℂ) (i : Fin 2) :
    secondPolynomialMap r θ (![secondQuadric r, secondCubic θ] i) = 0 := by
  have hz : Ideal.Quotient.mk (chartIdeal ![secondQuadric r, secondCubic θ])
      (![secondQuadric r, secondCubic θ] i) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨i, rfl⟩)
  exact (congrArg (secondAffineMap r θ) hz).trans (map_zero _)

def firstGradientRows (r θ : ℂ) (i : Fin 2) : Coordinates (CoordinateOverlapRing r θ) :=
  fun j => firstPolynomialMap r θ (pderiv j (![firstQuadric r, firstCubic θ] i))

def secondGradientRows (r θ : ℂ) (i : Fin 2) : Coordinates (CoordinateOverlapRing r θ) :=
  fun j => secondPolynomialMap r θ (pderiv j (![secondQuadric r, secondCubic θ] i))

theorem firstGradientRows_quadric (r θ : ℂ) :
    firstGradientRows r θ 0 =
      gradQuadricOne (algebraMap ℂ (CoordinateOverlapRing r θ) r) (firstCoordinates r θ 0) := by
  funext j
  change firstPolynomialMap r θ (pderiv j (firstQuadric r)) = _
  rw [congrFun (firstQuadric_gradient r) j]
  fin_cases j <;> simp [gradQuadricOne, map_ofNat]

theorem firstGradientRows_cubic (r θ : ℂ) :
    firstGradientRows r θ 1 =
      gradCubicOne (algebraMap ℂ (CoordinateOverlapRing r θ) Complex.I)
        (algebraMap ℂ (CoordinateOverlapRing r θ) θ)
        (firstCoordinates r θ 0) (firstCoordinates r θ 1) (firstCoordinates r θ 2) := by
  funext j
  change firstPolynomialMap r θ (pderiv j (firstCubic θ)) = _
  rw [congrFun (firstCubic_gradient θ) j]
  fin_cases j <;> simp [gradCubicOne, map_ofNat]

theorem secondGradientRows_quadric (r θ : ℂ) :
    secondGradientRows r θ 0 =
      gradQuadricTwo (algebraMap ℂ (CoordinateOverlapRing r θ) r)
        (secondCoordinates r θ 0) (secondCoordinates r θ 1) (secondCoordinates r θ 2) := by
  funext j
  change secondPolynomialMap r θ (pderiv j (secondQuadric r)) = _
  rw [congrFun (secondQuadric_gradient r) j]
  fin_cases j <;> simp [gradQuadricTwo, map_ofNat] <;> ring

theorem secondGradientRows_cubic (r θ : ℂ) :
    secondGradientRows r θ 1 =
      gradCubicTwo (algebraMap ℂ (CoordinateOverlapRing r θ) Complex.I)
        (algebraMap ℂ (CoordinateOverlapRing r θ) θ)
        (secondCoordinates r θ 0) (secondCoordinates r θ 1) (secondCoordinates r θ 2) := by
  funext j
  change secondPolynomialMap r θ (pderiv j (secondCubic θ)) = _
  rw [congrFun (secondCubic_gradient θ) j]
  fin_cases j <;> simp [gradCubicTwo, map_ofNat]

theorem first_equations_on_overlap (r θ : ℂ) :
    quadricOne (algebraMap ℂ (CoordinateOverlapRing r θ) r)
        (firstCoordinates r θ 0) (firstCoordinates r θ 1) (firstCoordinates r θ 2) = 0 ∧
      cubicOne (algebraMap ℂ (CoordinateOverlapRing r θ) Complex.I)
        (algebraMap ℂ (CoordinateOverlapRing r θ) θ)
        (firstCoordinates r θ 0) (firstCoordinates r θ 1) (firstCoordinates r θ 2) = 0 := by
  constructor
  · simpa [firstQuadric, quadricOne] using firstPolynomialMap_equation r θ 0
  · simpa [firstCubic, cubicOne] using firstPolynomialMap_equation r θ 1

theorem gradient_change_on_overlap (r θ : ℂ) :
    pullRow (firstCoordinates r θ 0) (firstCoordinates r θ 2)
        (↑((overlapUnit r θ)⁻¹) : CoordinateOverlapRing r θ) (secondGradientRows r θ 0) =
      (↑((overlapUnit r θ)⁻¹) : CoordinateOverlapRing r θ) ^ 2 • firstGradientRows r θ 0 ∧
    pullRow (firstCoordinates r θ 0) (firstCoordinates r θ 2)
        (↑((overlapUnit r θ)⁻¹) : CoordinateOverlapRing r θ) (secondGradientRows r θ 1) =
      (↑((overlapUnit r θ)⁻¹) : CoordinateOverlapRing r θ) ^ 3 • firstGradientRows r θ 1 := by
  have h := conormal_change_on_curve
    (algebraMap ℂ (CoordinateOverlapRing r θ) r)
    (algebraMap ℂ (CoordinateOverlapRing r θ) Complex.I)
    (algebraMap ℂ (CoordinateOverlapRing r θ) θ)
    (firstCoordinates r θ 0) (firstCoordinates r θ 1) (firstCoordinates r θ 2)
    (↑((overlapUnit r θ)⁻¹) : CoordinateOverlapRing r θ)
    (overlapUnit r θ).mul_inv
    (first_equations_on_overlap r θ).1 (first_equations_on_overlap r θ).2
  rw [secondGradientRows_quadric, secondGradientRows_cubic,
    firstGradientRows_quadric, firstGradientRows_cubic]
  constructor
  · funext j
    simpa only [coordinate_change, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Pi.smul_apply,
      smul_eq_mul] using congrFun h.1 j
  · funext j
    simpa only [coordinate_change, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Pi.smul_apply,
      smul_eq_mul] using congrFun h.2 j

/-! ## Coordinate pullback on the actual conormal quotients -/

section LinearAlgebra
variable {R : Type*} [CommRing R]

def coordinatePull (a c t : R) : Coordinates R →ₗ[R] Coordinates R where
  toFun := pullRow a c t
  map_add' u v := by
    funext j
    simp [pullRow, add_mul, Finset.sum_add_distrib]
  map_smul' k u := by
    funext j
    simp [pullRow, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

theorem coefficient_smul_rows (u v x : Coordinates R) (α β : R) :
    coefficient (α • u) (β • v) x = (α * β) * coefficient u v x := by
  simpa only [zero_smul, add_zero, zero_add, mul_zero, sub_zero] using
    coefficient_row_change u v x α 0 0 β

/-- The determinant calculation, proved before choosing any gradient rows. -/
theorem coefficient_pullRow (a c t : R) (u v x : Coordinates R) :
    coefficient (pullRow a c t u) (pullRow a c t v) (pullRow a c t x) =
      -(t ^ 4) * coefficient u v x := by
  simp [coefficient, cofactor, pullRow, coordinateJacobian, Fin.sum_univ_succ]
  ring

end LinearAlgebra

def overlapCoordinatePull (r θ : ℂ) :
    Coordinates (CoordinateOverlapRing r θ) →ₗ[CoordinateOverlapRing r θ]
      Coordinates (CoordinateOverlapRing r θ) :=
  coordinatePull (firstCoordinates r θ 0) (firstCoordinates r θ 2)
    (↑((overlapUnit r θ)⁻¹) : CoordinateOverlapRing r θ)

theorem overlapCoordinatePull_relations (r θ : ℂ) :
    relations (secondGradientRows r θ 0) (secondGradientRows r θ 1) ≤
      (relations (firstGradientRows r θ 0) (firstGradientRows r θ 1)).comap
        (overlapCoordinatePull r θ) := by
  apply Submodule.span_le.mpr
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  change overlapCoordinatePull r θ x ∈
    relations (firstGradientRows r θ 0) (firstGradientRows r θ 1)
  rcases hx with hx | hx
  · rw [hx]
    change pullRow _ _ _ (secondGradientRows r θ 0) ∈ _
    rw [(gradient_change_on_overlap r θ).1]
    exact (relations _ _).smul_mem _ (first_relation_mem _ _)
  · rw [hx]
    change pullRow _ _ _ (secondGradientRows r θ 1) ∈ _
    rw [(gradient_change_on_overlap r θ).2]
    exact (relations _ _).smul_mem _ (second_relation_mem _ _)

/-- Pullback by the actual coordinate-change Jacobian, descended through the actual relations. -/
def residuePullback (r θ : ℂ) :
    ResidueModule (secondGradientRows r θ 0) (secondGradientRows r θ 1) →ₗ[
      CoordinateOverlapRing r θ]
      ResidueModule (firstGradientRows r θ 0) (firstGradientRows r θ 1) :=
  (relations (secondGradientRows r θ 0) (secondGradientRows r θ 1)).mapQ
    (relations (firstGradientRows r θ 0) (firstGradientRows r θ 1))
    (overlapCoordinatePull r θ) (overlapCoordinatePull_relations r θ)

@[simp] theorem residuePullback_toResidue (r θ : ℂ)
    (x : Coordinates (CoordinateOverlapRing r θ)) :
    residuePullback r θ (toResidue (secondGradientRows r θ 0) (secondGradientRows r θ 1) x) =
      toResidue (firstGradientRows r θ 0) (firstGradientRows r θ 1)
        (overlapCoordinatePull r θ x) := rfl

theorem coefficient_change_on_overlap (r θ : ℂ)
    (x : Coordinates (CoordinateOverlapRing r θ)) :
    coefficient (firstGradientRows r θ 0) (firstGradientRows r θ 1)
        (overlapCoordinatePull r θ x) =
      -(overlapUnit r θ : CoordinateOverlapRing r θ) *
        coefficient (secondGradientRows r θ 0) (secondGradientRows r θ 1) x := by
  let t : CoordinateOverlapRing r θ := ↑((overlapUnit r θ)⁻¹)
  have h := coefficient_pullRow (firstCoordinates r θ 0) (firstCoordinates r θ 2) t
    (secondGradientRows r θ 0) (secondGradientRows r θ 1) x
  rw [(gradient_change_on_overlap r θ).1, (gradient_change_on_overlap r θ).2,
    coefficient_smul_rows] at h
  have ht : IsUnit t := ((overlapUnit r θ)⁻¹).isUnit
  apply (ht.pow 5).mul_left_cancel
  calc
    t ^ 5 * coefficient (firstGradientRows r θ 0) (firstGradientRows r θ 1)
        (overlapCoordinatePull r θ x) =
        -(t ^ 4) * coefficient (secondGradientRows r θ 0) (secondGradientRows r θ 1) x := by
      change t ^ 5 * coefficient (firstGradientRows r θ 0) (firstGradientRows r θ 1)
          (pullRow (firstCoordinates r θ 0) (firstCoordinates r θ 2) t x) =
        -(t ^ 4) * coefficient (secondGradientRows r θ 0) (secondGradientRows r θ 1) x
      simpa only [t, ← pow_add, show (2 : ℕ) + 3 = 5 from rfl] using h
    _ = t ^ 5 * (-(overlapUnit r θ : CoordinateOverlapRing r θ) *
        coefficient (secondGradientRows r θ 0) (secondGradientRows r θ 1) x) := by
      have hb : (overlapUnit r θ : CoordinateOverlapRing r θ) * t = 1 :=
        (overlapUnit r θ).mul_inv
      linear_combination t ^ 4 *
        coefficient (secondGradientRows r θ 0) (secondGradientRows r θ 1) x * hb

/-- The coefficient-transformation premise is proved for the constructed geometric map. -/
theorem residuePullback_coefficient (r θ : ℂ)
    (ξ : ResidueModule (secondGradientRows r θ 0) (secondGradientRows r θ 1)) :
    residueFunctional (firstGradientRows r θ 0) (firstGradientRows r θ 1)
        (residuePullback r θ ξ) =
      -(overlapUnit r θ : CoordinateOverlapRing r θ) *
        residueFunctional (secondGradientRows r θ 0) (secondGradientRows r θ 1) ξ := by
  refine Quotient.inductionOn' ξ (fun x => ?_)
  exact coefficient_change_on_overlap r θ x

/-! ## Binding the quotient pullback to universal differentials -/

def firstCoordinateDifferentials (r θ : ℂ) :
    Coordinates (CoordinateOverlapRing r θ) →ₗ[CoordinateOverlapRing r θ]
      KaehlerDifferential ℂ (CoordinateOverlapRing r θ) :=
  (Pi.basisFun (CoordinateOverlapRing r θ) (Fin 3)).constr (CoordinateOverlapRing r θ)
    (fun j => KaehlerDifferential.D ℂ _ (firstCoordinates r θ j))

def secondCoordinateDifferentials (r θ : ℂ) :
    Coordinates (CoordinateOverlapRing r θ) →ₗ[CoordinateOverlapRing r θ]
      KaehlerDifferential ℂ (CoordinateOverlapRing r θ) :=
  (Pi.basisFun (CoordinateOverlapRing r θ) (Fin 3)).constr (CoordinateOverlapRing r θ)
    (fun j => KaehlerDifferential.D ℂ _ (secondCoordinates r θ j))

theorem firstCoordinateDifferentials_apply (r θ : ℂ)
    (x : Coordinates (CoordinateOverlapRing r θ)) :
    firstCoordinateDifferentials r θ x =
      ∑ j : Fin 3, x j • KaehlerDifferential.D ℂ _ (firstCoordinates r θ j) := by
  rw [firstCoordinateDifferentials, Module.Basis.constr_apply_fintype]
  rfl

theorem secondCoordinateDifferentials_apply (r θ : ℂ)
    (x : Coordinates (CoordinateOverlapRing r θ)) :
    secondCoordinateDifferentials r θ x =
      ∑ j : Fin 3, x j • KaehlerDifferential.D ℂ _ (secondCoordinates r θ j) := by
  rw [secondCoordinateDifferentials, Module.Basis.constr_apply_fintype]
  rfl

@[simp] theorem firstCoordinateDifferentials_coordinateVector (r θ : ℂ) (j : Fin 3) :
    firstCoordinateDifferentials r θ (coordinateVector j) =
      KaehlerDifferential.D ℂ _ (firstCoordinates r θ j) := by
  have hvec : coordinateVector j =
      (Pi.basisFun (CoordinateOverlapRing r θ) (Fin 3)) j := by
    funext i
    simp [coordinateVector, Pi.basisFun_apply, Pi.single_apply, eq_comm]
  rw [hvec]
  exact (Pi.basisFun (CoordinateOverlapRing r θ) (Fin 3)).constr_basis
    (CoordinateOverlapRing r θ)
    (fun i => KaehlerDifferential.D ℂ _ (firstCoordinates r θ i)) j

@[simp] theorem secondCoordinateDifferentials_coordinateVector (r θ : ℂ) (j : Fin 3) :
    secondCoordinateDifferentials r θ (coordinateVector j) =
      KaehlerDifferential.D ℂ _ (secondCoordinates r θ j) := by
  have hvec : coordinateVector j =
      (Pi.basisFun (CoordinateOverlapRing r θ) (Fin 3)) j := by
    funext i
    simp [coordinateVector, Pi.basisFun_apply, Pi.single_apply, eq_comm]
  rw [hvec]
  exact (Pi.basisFun (CoordinateOverlapRing r θ) (Fin 3)).constr_basis
    (CoordinateOverlapRing r θ)
    (fun i => KaehlerDifferential.D ℂ _ (secondCoordinates r θ i)) j

theorem firstCoordinateDifferentials_gradient (r θ : ℂ) (i : Fin 2) :
    firstCoordinateDifferentials r θ (firstGradientRows r θ i) = 0 := by
  rw [firstCoordinateDifferentials_apply]
  change (∑ j : Fin 3,
    firstPolynomialMap r θ (pderiv j (![firstQuadric r, firstCubic θ] i)) •
      KaehlerDifferential.D ℂ _ (firstPolynomialMap r θ (X j))) = 0
  rw [← CycleQ2GeometricKaehlerResidue.differential_polynomial,
    firstPolynomialMap_equation, map_zero]

theorem secondCoordinateDifferentials_gradient (r θ : ℂ) (i : Fin 2) :
    secondCoordinateDifferentials r θ (secondGradientRows r θ i) = 0 := by
  rw [secondCoordinateDifferentials_apply]
  change (∑ j : Fin 3,
    secondPolynomialMap r θ (pderiv j (![secondQuadric r, secondCubic θ] i)) •
      KaehlerDifferential.D ℂ _ (secondPolynomialMap r θ (X j))) = 0
  rw [← CycleQ2GeometricKaehlerResidue.differential_polynomial,
    secondPolynomialMap_equation, map_zero]

/-- The first gradient quotient maps to the actual Kähler module of the overlap. -/
def firstDifferential (r θ : ℂ) :
    ResidueModule (firstGradientRows r θ 0) (firstGradientRows r θ 1) →ₗ[
      CoordinateOverlapRing r θ] KaehlerDifferential ℂ (CoordinateOverlapRing r θ) :=
  (relations (firstGradientRows r θ 0) (firstGradientRows r θ 1)).liftQ
    (firstCoordinateDifferentials r θ) (by
      apply Submodule.span_le.mpr
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      change firstCoordinateDifferentials r θ x = 0
      rcases hx with hx | hx
      · rw [hx, firstCoordinateDifferentials_gradient]
      · rw [hx, firstCoordinateDifferentials_gradient])

/-- The second gradient quotient maps independently to the same actual Kähler module. -/
def secondDifferential (r θ : ℂ) :
    ResidueModule (secondGradientRows r θ 0) (secondGradientRows r θ 1) →ₗ[
      CoordinateOverlapRing r θ] KaehlerDifferential ℂ (CoordinateOverlapRing r θ) :=
  (relations (secondGradientRows r θ 0) (secondGradientRows r θ 1)).liftQ
    (secondCoordinateDifferentials r θ) (by
      apply Submodule.span_le.mpr
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      change secondCoordinateDifferentials r θ x = 0
      rcases hx with hx | hx
      · rw [hx, secondCoordinateDifferentials_gradient]
      · rw [hx, secondCoordinateDifferentials_gradient])

@[simp] theorem firstDifferential_toResidue (r θ : ℂ)
    (x : Coordinates (CoordinateOverlapRing r θ)) :
    firstDifferential r θ (toResidue (firstGradientRows r θ 0) (firstGradientRows r θ 1) x) =
      firstCoordinateDifferentials r θ x := rfl

@[simp] theorem secondDifferential_toResidue (r θ : ℂ)
    (x : Coordinates (CoordinateOverlapRing r θ)) :
    secondDifferential r θ (toResidue (secondGradientRows r θ 0) (secondGradientRows r θ 1) x) =
      secondCoordinateDifferentials r θ x := rfl

theorem universal_differential_change (r θ : ℂ) (i : Fin 3) :
    KaehlerDifferential.D ℂ (CoordinateOverlapRing r θ) (secondCoordinates r θ i) =
      ∑ j : Fin 3,
        coordinateJacobian (firstCoordinates r θ 0) (firstCoordinates r θ 2)
            (↑((overlapUnit r θ)⁻¹) : CoordinateOverlapRing r θ) i j •
          KaehlerDifferential.D ℂ _ (firstCoordinates r θ j) := by
  let D := KaehlerDifferential.D ℂ (CoordinateOverlapRing r θ)
  have h := coordinate_differential_change D (firstCoordinates r θ 0)
    (firstCoordinates r θ 2) (overlapUnit r θ)
  have hfirst : ![D (firstCoordinates r θ 0), D (overlapUnit r θ : CoordinateOverlapRing r θ),
      D (firstCoordinates r θ 2)] = fun j => D (firstCoordinates r θ j) := by
    funext j
    fin_cases j <;> rfl
  have hsecond :
      ![D (firstCoordinates r θ 0 * (↑((overlapUnit r θ)⁻¹) : CoordinateOverlapRing r θ)),
        D (↑((overlapUnit r θ)⁻¹) : CoordinateOverlapRing r θ),
        D (firstCoordinates r θ 2 * (↑((overlapUnit r θ)⁻¹) : CoordinateOverlapRing r θ))] =
        fun j => D (secondCoordinates r θ j) := by
    rw [coordinate_change]
    funext j
    fin_cases j <;> rfl
  rw [hfirst, hsecond] at h
  exact congrFun h i

theorem coordinateDifferentials_change (r θ : ℂ) :
    (firstCoordinateDifferentials r θ).comp (overlapCoordinatePull r θ) =
      secondCoordinateDifferentials r θ := by
  apply (Pi.basisFun (CoordinateOverlapRing r θ) (Fin 3)).ext
  intro i
  have hvec : (Pi.basisFun (CoordinateOverlapRing r θ) (Fin 3)) i = coordinateVector i := by
    funext j
    simp [coordinateVector, Pi.basisFun_apply, Pi.single_apply, eq_comm]
  rw [hvec, LinearMap.comp_apply, secondCoordinateDifferentials_coordinateVector]
  change firstCoordinateDifferentials r θ
    (pullRow (firstCoordinates r θ 0) (firstCoordinates r θ 2)
      (↑((overlapUnit r θ)⁻¹) : CoordinateOverlapRing r θ) (coordinateVector i)) = _
  rw [firstCoordinateDifferentials_apply]
  have hrow :
      pullRow (firstCoordinates r θ 0) (firstCoordinates r θ 2)
          (↑((overlapUnit r θ)⁻¹) : CoordinateOverlapRing r θ) (coordinateVector i) =
        fun j => coordinateJacobian (firstCoordinates r θ 0) (firstCoordinates r θ 2)
          (↑((overlapUnit r θ)⁻¹) : CoordinateOverlapRing r θ) i j := by
    funext j
    simp [pullRow, coordinateVector]
  rw [hrow]
  exact (universal_differential_change r θ i).symm

/-- The descended Jacobian map commutes with the literal universal-differential maps. -/
theorem firstDifferential_residuePullback (r θ : ℂ) :
    (firstDifferential r θ).comp (residuePullback r θ) = secondDifferential r θ := by
  apply LinearMap.ext
  intro ξ
  refine Quotient.inductionOn' ξ (fun x => ?_)
  change firstCoordinateDifferentials r θ (overlapCoordinatePull r θ x) =
    secondCoordinateDifferentials r θ x
  exact LinearMap.congr_fun (coordinateDifferentials_change r θ) x

theorem normalized_residue_pullback (r θ : ℂ) (k l : Fin 3)
    (u v : (CoordinateOverlapRing r θ)ˣ)
    (hu : cofactor (firstGradientRows r θ 0) (firstGradientRows r θ 1) k = ↑u)
    (hv : cofactor (secondGradientRows r θ 0) (secondGradientRows r θ 1) l = ↑v) :
    residuePullback r θ
        (normalizedResidue (secondGradientRows r θ 0) (secondGradientRows r θ 1) l v) =
      -(overlapUnit r θ : CoordinateOverlapRing r θ) •
        normalizedResidue (firstGradientRows r θ 0) (firstGradientRows r θ 1) k u :=
  normalizedResidue_transport (secondGradientRows r θ 0) (secondGradientRows r θ 1)
    (firstGradientRows r θ 0) (firstGradientRows r θ 1) l k v u hv hu
    (residuePullback r θ) (-(overlapUnit r θ : CoordinateOverlapRing r θ))
    (residuePullback_coefficient r θ)

@[simp] theorem firstDifferential_normalizedResidue (r θ : ℂ) (k : Fin 3)
    (u : (CoordinateOverlapRing r θ)ˣ) :
    firstDifferential r θ
        (normalizedResidue (firstGradientRows r θ 0) (firstGradientRows r θ 1) k u) =
      (↑(u⁻¹) : CoordinateOverlapRing r θ) •
        KaehlerDifferential.D ℂ _ (firstCoordinates r θ k) := by
  rw [normalizedResidue, map_smul, firstDifferential_toResidue,
    firstCoordinateDifferentials_coordinateVector]

@[simp] theorem secondDifferential_normalizedResidue (r θ : ℂ) (l : Fin 3)
    (v : (CoordinateOverlapRing r θ)ˣ) :
    secondDifferential r θ
        (normalizedResidue (secondGradientRows r θ 0) (secondGradientRows r θ 1) l v) =
      (↑(v⁻¹) : CoordinateOverlapRing r θ) •
        KaehlerDifferential.D ℂ _ (secondCoordinates r θ l) := by
  rw [normalizedResidue, map_smul, secondDifferential_toResidue,
    secondCoordinateDifferentials_coordinateVector]

/-- Deleting projective coordinates 1 and 2 contributes opposite signs.
After including these signs, the genuine differential transition is +x2/x1.
The unit-minor hypotheses specify exactly where these normalized frames exist. -/
theorem oriented_kaehler_residue_transition (r θ : ℂ) (k l : Fin 3)
    (u v : (CoordinateOverlapRing r θ)ˣ)
    (hu : cofactor (firstGradientRows r θ 0) (firstGradientRows r θ 1) k = ↑u)
    (hv : cofactor (secondGradientRows r θ 0) (secondGradientRows r θ 1) l = ↑v) :
    (↑(v⁻¹) : CoordinateOverlapRing r θ) •
        KaehlerDifferential.D ℂ _ (secondCoordinates r θ l) =
      (overlapUnit r θ : CoordinateOverlapRing r θ) •
        (-((↑(u⁻¹) : CoordinateOverlapRing r θ) •
          KaehlerDifferential.D ℂ _ (firstCoordinates r θ k))) := by
  have h := LinearMap.congr_fun (firstDifferential_residuePullback r θ)
    (normalizedResidue (secondGradientRows r θ 0) (secondGradientRows r θ 1) l v)
  change firstDifferential r θ (residuePullback r θ
    (normalizedResidue (secondGradientRows r θ 0) (secondGradientRows r θ 1) l v)) =
      secondDifferential r θ
        (normalizedResidue (secondGradientRows r θ 0) (secondGradientRows r θ 1) l v) at h
  rw [normalized_residue_pullback r θ k l u v hu hv, map_smul,
    firstDifferential_normalizedResidue, secondDifferential_normalizedResidue] at h
  simpa only [neg_smul, smul_neg] using h.symm

end CycleQ2GeometricProjectiveResidueTransition

end
