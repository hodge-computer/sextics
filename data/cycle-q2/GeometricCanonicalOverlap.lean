import Proposal.GeometricChartKaehler

/-!
# Actual canonical forms on the entire overlap of the curve charts

The whole-chart differential forms are transported through the actual
localization homomorphisms and the constructed overlap algebra equivalence.
Their transition is proved on the entire coordinate overlap for arbitrary
parameters whose actual chart Jacobian ideals are the unit ideal. No Jacobian
minor is inverted. The three signed minors generate one, so their three
coordinate differential identities determine the transported form uniquely.

With the projective orientation on the first chart, the transition factor
is the actual coordinate x2/x1. This is a comparison of genuine Kähler forms
on the two literal affine rings and their full overlap. The projective sheaf
identification and the geometric Serre trace remain separate statements.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2GeometricCanonicalOverlap.At

open CycleQ2GeometricAffineCurveCharts CycleQ2GeometricAffineOverlap
  CycleQ2GeometricSparseJacobianCover
open CycleQ2GeometricChartKaehler (ChartJacobianCover)

/-- The actual localization homomorphism from an entire affine chart. -/
def localizationMap (v : Fin 2 → AffinePoly) :
    ChartRing v →ₐ[ℂ] CoordinateOverlap v :=
  IsScalarTower.toAlgHom ℂ (ChartRing v) (CoordinateOverlap v)

def firstChartMap (r θ : ℂ) : ChartRing (firstEquations r θ) →ₐ[ℂ] FirstOverlap r θ :=
  localizationMap (firstEquations r θ)

/-- The second chart maps into the same actual overlap through the proved
coordinate-change algebra equivalence. -/
def secondChartMap (r θ : ℂ) : ChartRing (secondEquations r θ) →ₐ[ℂ] FirstOverlap r θ :=
  (overlapEquiv r θ).toAlgHom.comp (localizationMap (secondEquations r θ))

@[simp] theorem localizationMap_coordinate (v : Fin 2 → AffinePoly) (j : Fin 3) :
    localizationMap v (CycleQ2GeometricChartKaehler.coordinate v j) = coordinate v j := rfl

@[simp] theorem localizationMap_minor (v : Fin 2 → AffinePoly) (j : Fin 3) :
    localizationMap v (chartMinor v j) = chartMinors v j := rfl

@[simp] theorem secondChartMap_coordinate (r θ : ℂ) (j : Fin 3) :
    secondChartMap r θ (CycleQ2GeometricChartKaehler.coordinate (secondEquations r θ) j) =
      overlapEquiv r θ (coordinate (secondEquations r θ) j) := rfl

@[simp] theorem secondChartMap_minor (r θ : ℂ) (j : Fin 3) :
    secondChartMap r θ (chartMinor (secondEquations r θ) j) =
      overlapEquiv r θ (chartMinors (secondEquations r θ) j) := rfl

/-- The first whole-chart form restricted to the actual overlap. -/
def firstForm (r θ : ℂ) (h : ChartJacobianCover r θ) : KaehlerDifferential ℂ (FirstOverlap r θ) :=
  differentialMap (firstChartMap r θ) (CycleQ2GeometricChartKaehler.At.firstChartForm r θ h)

/-- The second whole-chart form transported into the actual first overlap. -/
def secondForm (r θ : ℂ) (h : ChartJacobianCover r θ) : KaehlerDifferential ℂ (FirstOverlap r θ) :=
  differentialMap (secondChartMap r θ) (CycleQ2GeometricChartKaehler.At.secondChartForm r θ h)

/-- Universal differentiation commutes with the actual algebra maps. -/
theorem mapped_coordinate_differential (v : Fin 2 → AffinePoly) (h : jacobianIdeal v = ⊤)
    {S : Type*} [CommRing S] [Algebra ℂ S] (f : ChartRing v →ₐ[ℂ] S) (j : Fin 3) :
    KaehlerDifferential.D ℂ S (f (CycleQ2GeometricChartKaehler.coordinate v j)) =
      f (chartMinor v j) • differentialMap f (CycleQ2GeometricChartKaehler.globalForm v h) := by
  simpa only [differentialMap_D, differentialMap_smul] using
    congrArg (differentialMap f) (CycleQ2GeometricChartKaehler.differential_coordinate_eq_smul v h j)

theorem first_coordinate_differential (r θ : ℂ) (h : ChartJacobianCover r θ) (j : Fin 3) :
    KaehlerDifferential.D ℂ (FirstOverlap r θ) (coordinate (firstEquations r θ) j) =
      chartMinors (firstEquations r θ) j • firstForm r θ h :=
  mapped_coordinate_differential (firstEquations r θ)
    h.1 (firstChartMap r θ) j

theorem second_coordinate_differential (r θ : ℂ) (h : ChartJacobianCover r θ) (j : Fin 3) :
    KaehlerDifferential.D ℂ (FirstOverlap r θ)
        (overlapEquiv r θ (coordinate (secondEquations r θ) j)) =
      overlapEquiv r θ (chartMinors (secondEquations r θ) j) • secondForm r θ h :=
  mapped_coordinate_differential (secondEquations r θ)
    h.2 (secondChartMap r θ) j

section CoefficientIdentities
variable {R : Type*} [CommRing R]

private theorem outer_coefficient (a b t m n : R) (ht : b * t = 1) :
    t * m - a * t ^ 2 * n = (-t ^ 2 * m + a * t ^ 3 * n) * (-b) := by
  linear_combination (-t * m + a * t ^ 2 * n) * ht

private theorem middle_coefficient (b t n : R) (ht : b * t = 1) :
    (-t ^ 2) * n = (t ^ 3 * n) * (-b) := by
  linear_combination t ^ 2 * n * ht

end CoefficientIdentities

/-- The chain rule and all three actual cofactor transformations give the
same candidate transition for every coordinate differential. -/
theorem coordinate_transition (r θ : ℂ) (h : ChartJacobianCover r θ) (j : Fin 3) :
    overlapDifferentialEquiv r θ
      (KaehlerDifferential.D ℂ (SecondOverlap r θ) (coordinate (secondEquations r θ) j)) =
      overlapEquiv r θ (chartMinors (secondEquations r θ) j) •
        (-(coordinate (firstEquations r θ) 1) • firstForm r θ h) := by
  have hmin := congrFun (overlapEquiv_allMinors r θ) j
  fin_cases j
  · change overlapDifferentialEquiv r θ
      (KaehlerDifferential.D ℂ (SecondOverlap r θ) (coordinate (secondEquations r θ) 0)) =
        overlapEquiv r θ (chartMinors (secondEquations r θ) 0) •
          (-(coordinate (firstEquations r θ) 1) • firstForm r θ h)
    rw [overlapDifferential_coordinate0 r θ, first_coordinate_differential r θ h 0,
      first_coordinate_differential r θ h 1]
    change overlapEquiv r θ (chartMinors (secondEquations r θ) 0) =
      -inverse (firstEquations r θ) ^ 2 * chartMinors (firstEquations r θ) 0 +
        coordinate (firstEquations r θ) 0 * inverse (firstEquations r θ) ^ 3 *
          chartMinors (firstEquations r θ) 1 at hmin
    rw [hmin]
    simp only [smul_smul, ← sub_smul]
    rw [outer_coefficient _ _ _ _ _ (coordinate_mul_inverse (firstEquations r θ))]
  · change overlapDifferentialEquiv r θ
      (KaehlerDifferential.D ℂ (SecondOverlap r θ) (coordinate (secondEquations r θ) 1)) =
        overlapEquiv r θ (chartMinors (secondEquations r θ) 1) •
          (-(coordinate (firstEquations r θ) 1) • firstForm r θ h)
    rw [overlapDifferential_coordinate1 r θ, first_coordinate_differential r θ h 1]
    change overlapEquiv r θ (chartMinors (secondEquations r θ) 1) =
      inverse (firstEquations r θ) ^ 3 * chartMinors (firstEquations r θ) 1 at hmin
    rw [hmin]
    simp only [smul_smul]
    rw [middle_coefficient _ _ _ (coordinate_mul_inverse (firstEquations r θ))]
  · change overlapDifferentialEquiv r θ
      (KaehlerDifferential.D ℂ (SecondOverlap r θ) (coordinate (secondEquations r θ) 2)) =
        overlapEquiv r θ (chartMinors (secondEquations r θ) 2) •
          (-(coordinate (firstEquations r θ) 1) • firstForm r θ h)
    rw [overlapDifferential_coordinate2 r θ, first_coordinate_differential r θ h 2,
      first_coordinate_differential r θ h 1]
    change overlapEquiv r θ (chartMinors (secondEquations r θ) 2) =
      -inverse (firstEquations r θ) ^ 2 * chartMinors (firstEquations r θ) 2 +
        coordinate (firstEquations r θ) 2 * inverse (firstEquations r θ) ^ 3 *
          chartMinors (firstEquations r θ) 1 at hmin
    rw [hmin]
    simp only [smul_smul, ← sub_smul]
    rw [outer_coefficient _ _ _ _ _ (coordinate_mul_inverse (firstEquations r θ))]

/-- All three actual minors kill the difference between the two forms. -/
theorem minor_smul_transition (r θ : ℂ) (h : ChartJacobianCover r θ) (j : Fin 3) :
    secondChartMap r θ (chartMinor (secondEquations r θ) j) • secondForm r θ h =
      secondChartMap r θ (chartMinor (secondEquations r θ) j) •
        (-(coordinate (firstEquations r θ) 1) • firstForm r θ h) := by
  rw [secondChartMap_minor, ← second_coordinate_differential]
  exact (differentialEquiv_D (overlapEquiv r θ)
    (coordinate (secondEquations r θ) j)).symm.trans (coordinate_transition r θ h j)

section BezoutUniqueness
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- A finite unit-ideal family detects equality in any module. -/
theorem eq_of_bezout_smul (c w : Fin 3 → R) (hw : ∑ j, w j * c j = 1)
    (x y : M) (hxy : ∀ j, c j • x = c j • y) : x = y := by
  calc
    x = (∑ j, w j * c j) • x := by rw [hw, one_smul]
    _ = ∑ j, w j • (c j • x) := by simp only [Finset.sum_smul, smul_smul]
    _ = ∑ j, w j • (c j • y) := Finset.sum_congr rfl (fun j _ => congrArg (w j • ·) (hxy j))
    _ = (∑ j, w j * c j) • y := by simp only [Finset.sum_smul, smul_smul]
    _ = y := by rw [hw, one_smul]

end BezoutUniqueness

/-- The full affine overlap transition, without inverting a Jacobian minor. -/
theorem full_overlap_transition (r θ : ℂ) (h : ChartJacobianCover r θ) :
    secondForm r θ h = -(coordinate (firstEquations r θ) 1) • firstForm r θ h := by
  have hone : (1 : ChartRing (secondEquations r θ)) ∈
      Ideal.span (Set.range (chartMinor (secondEquations r θ))) := by
    change (1 : ChartRing (secondEquations r θ)) ∈ jacobianIdeal (secondEquations r θ)
    rw [h.2]
    trivial
  obtain ⟨w, hw⟩ := Ideal.mem_span_range_iff_exists_fun.mp hone
  have hmap : ∑ j, secondChartMap r θ (w j) *
      secondChartMap r θ (chartMinor (secondEquations r θ) j) = 1 := by
    simpa only [map_sum, map_mul, map_one] using congrArg (secondChartMap r θ) hw
  exact eq_of_bezout_smul _ _ hmap _ _ (minor_smul_transition r θ h)

/-- Projective orientation of the first chart's genuine differential. -/
def firstOrientedForm (r θ : ℂ) (h : ChartJacobianCover r θ) : KaehlerDifferential ℂ (FirstOverlap r θ) :=
  -firstForm r θ h

/-- In projective orientation, the factor is precisely the coordinate x2/x1. -/
theorem oriented_overlap_transition (r θ : ℂ) (h : ChartJacobianCover r θ) :
    secondForm r θ h = coordinate (firstEquations r θ) 1 • firstOrientedForm r θ h := by
  rw [full_overlap_transition, firstOrientedForm, smul_neg, neg_smul]

/-- The identity explicitly displays both maps out of the original chart rings. -/
theorem actual_chart_form_transition (r θ : ℂ) (h : ChartJacobianCover r θ) :
    differentialMap (secondChartMap r θ) (CycleQ2GeometricChartKaehler.At.secondChartForm r θ h) =
      coordinate (firstEquations r θ) 1 • differentialMap (firstChartMap r θ)
        (-CycleQ2GeometricChartKaehler.At.firstChartForm r θ h) := by
  simpa only [firstOrientedForm, firstForm, secondForm, map_neg] using
    oriented_overlap_transition r θ h

/-- Equivalently, restriction to the second overlap followed by the actual
Kähler equivalence gives the same oriented transition. -/
theorem overlap_equivalence_form_transition (r θ : ℂ) (h : ChartJacobianCover r θ) :
    overlapDifferentialEquiv r θ
      (differentialMap (localizationMap (secondEquations r θ))
        (CycleQ2GeometricChartKaehler.At.secondChartForm r θ h)) =
      coordinate (firstEquations r θ) 1 •
        differentialMap (localizationMap (firstEquations r θ))
          (-CycleQ2GeometricChartKaehler.At.firstChartForm r θ h) := by
  change differentialMap (overlapEquiv r θ).toAlgHom
    (differentialMap (localizationMap (secondEquations r θ)) _) = _
  rw [differentialMap_comp]
  exact actual_chart_form_transition r θ h

end CycleQ2GeometricCanonicalOverlap.At

/-! The original sparse APIs specialize the common proofs to their proved cover. -/
namespace CycleQ2GeometricCanonicalOverlap

open CycleQ2GeometricChartKaehler

abbrev localizationMap := At.localizationMap
abbrev localizationMap_coordinate := At.localizationMap_coordinate
abbrev localizationMap_minor := At.localizationMap_minor
abbrev mapped_coordinate_differential := At.mapped_coordinate_differential
abbrev eq_of_bezout_smul := @At.eq_of_bezout_smul

abbrev firstChartMap (r : ℂ) := At.firstChartMap r 0

abbrev secondChartMap (r : ℂ) := At.secondChartMap r 0

abbrev secondChartMap_coordinate (r : ℂ) := At.secondChartMap_coordinate r 0

abbrev secondChartMap_minor (r : ℂ) := At.secondChartMap_minor r 0

abbrev firstForm (r : ℂ) (hr : r ^ 3 = 2) :=
  At.firstForm r 0 (sparseChartJacobianCover r hr)

abbrev secondForm (r : ℂ) (hr : r ^ 3 = 2) :=
  At.secondForm r 0 (sparseChartJacobianCover r hr)

abbrev first_coordinate_differential (r : ℂ) (hr : r ^ 3 = 2) :=
  At.first_coordinate_differential r 0 (sparseChartJacobianCover r hr)

abbrev second_coordinate_differential (r : ℂ) (hr : r ^ 3 = 2) :=
  At.second_coordinate_differential r 0 (sparseChartJacobianCover r hr)

abbrev coordinate_transition (r : ℂ) (hr : r ^ 3 = 2) :=
  At.coordinate_transition r 0 (sparseChartJacobianCover r hr)

abbrev minor_smul_transition (r : ℂ) (hr : r ^ 3 = 2) :=
  At.minor_smul_transition r 0 (sparseChartJacobianCover r hr)

abbrev full_overlap_transition (r : ℂ) (hr : r ^ 3 = 2) :=
  At.full_overlap_transition r 0 (sparseChartJacobianCover r hr)

abbrev firstOrientedForm (r : ℂ) (hr : r ^ 3 = 2) :=
  At.firstOrientedForm r 0 (sparseChartJacobianCover r hr)

abbrev oriented_overlap_transition (r : ℂ) (hr : r ^ 3 = 2) :=
  At.oriented_overlap_transition r 0 (sparseChartJacobianCover r hr)

abbrev actual_chart_form_transition (r : ℂ) (hr : r ^ 3 = 2) :=
  At.actual_chart_form_transition r 0 (sparseChartJacobianCover r hr)

abbrev overlap_equivalence_form_transition (r : ℂ) (hr : r ^ 3 = 2) :=
  At.overlap_equivalence_form_transition r 0 (sparseChartJacobianCover r hr)

#print axioms At.full_overlap_transition
#print axioms At.actual_chart_form_transition
#print axioms actual_chart_form_transition

end CycleQ2GeometricCanonicalOverlap
end
