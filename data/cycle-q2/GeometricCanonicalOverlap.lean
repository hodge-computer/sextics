import Proposal.GeometricChartKaehler

/-!
# Actual canonical forms on the entire overlap of the sparse curve charts

The whole-chart differential forms are transported through the actual
localization homomorphisms and the constructed overlap algebra equivalence.
Their transition is proved on the entire coordinate overlap: no Jacobian
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

namespace CycleQ2GeometricCanonicalOverlap

open CycleQ2GeometricAffineCurveCharts CycleQ2GeometricAffineOverlap
  CycleQ2GeometricSparseJacobianCover

/-- The actual localization homomorphism from an entire affine chart. -/
def localizationMap (v : Fin 2 → AffinePoly) :
    ChartRing v →ₐ[ℂ] CoordinateOverlap v :=
  IsScalarTower.toAlgHom ℂ (ChartRing v) (CoordinateOverlap v)

def firstChartMap (r : ℂ) : ChartRing (firstEquations r 0) →ₐ[ℂ] FirstOverlap r 0 :=
  localizationMap (firstEquations r 0)

/-- The second chart maps into the same actual overlap through the proved
coordinate-change algebra equivalence. -/
def secondChartMap (r : ℂ) : ChartRing (secondEquations r 0) →ₐ[ℂ] FirstOverlap r 0 :=
  (overlapEquiv r 0).toAlgHom.comp (localizationMap (secondEquations r 0))

@[simp] theorem localizationMap_coordinate (v : Fin 2 → AffinePoly) (j : Fin 3) :
    localizationMap v (CycleQ2GeometricChartKaehler.coordinate v j) = coordinate v j := rfl

@[simp] theorem localizationMap_minor (v : Fin 2 → AffinePoly) (j : Fin 3) :
    localizationMap v (chartMinor v j) = chartMinors v j := rfl

@[simp] theorem secondChartMap_coordinate (r : ℂ) (j : Fin 3) :
    secondChartMap r (CycleQ2GeometricChartKaehler.coordinate (secondEquations r 0) j) =
      overlapEquiv r 0 (coordinate (secondEquations r 0) j) := rfl

@[simp] theorem secondChartMap_minor (r : ℂ) (j : Fin 3) :
    secondChartMap r (chartMinor (secondEquations r 0) j) =
      overlapEquiv r 0 (chartMinors (secondEquations r 0) j) := rfl

/-- The first whole-chart form restricted to the actual overlap. -/
def firstForm (r : ℂ) (hr : r ^ 3 = 2) : KaehlerDifferential ℂ (FirstOverlap r 0) :=
  differentialMap (firstChartMap r) (CycleQ2GeometricChartKaehler.firstChartForm r hr)

/-- The second whole-chart form transported into the actual first overlap. -/
def secondForm (r : ℂ) (hr : r ^ 3 = 2) : KaehlerDifferential ℂ (FirstOverlap r 0) :=
  differentialMap (secondChartMap r) (CycleQ2GeometricChartKaehler.secondChartForm r hr)

/-- Universal differentiation commutes with the actual algebra maps. -/
theorem mapped_coordinate_differential (v : Fin 2 → AffinePoly) (h : jacobianIdeal v = ⊤)
    {S : Type*} [CommRing S] [Algebra ℂ S] (f : ChartRing v →ₐ[ℂ] S) (j : Fin 3) :
    KaehlerDifferential.D ℂ S (f (CycleQ2GeometricChartKaehler.coordinate v j)) =
      f (chartMinor v j) • differentialMap f (CycleQ2GeometricChartKaehler.globalForm v h) := by
  simpa only [differentialMap_D, differentialMap_smul] using
    congrArg (differentialMap f) (CycleQ2GeometricChartKaehler.differential_coordinate_eq_smul v h j)

theorem first_coordinate_differential (r : ℂ) (hr : r ^ 3 = 2) (j : Fin 3) :
    KaehlerDifferential.D ℂ (FirstOverlap r 0) (coordinate (firstEquations r 0) j) =
      chartMinors (firstEquations r 0) j • firstForm r hr :=
  mapped_coordinate_differential (firstEquations r 0)
    (first_chart_jacobianIdeal_eq_top r hr) (firstChartMap r) j

theorem second_coordinate_differential (r : ℂ) (hr : r ^ 3 = 2) (j : Fin 3) :
    KaehlerDifferential.D ℂ (FirstOverlap r 0)
        (overlapEquiv r 0 (coordinate (secondEquations r 0) j)) =
      overlapEquiv r 0 (chartMinors (secondEquations r 0) j) • secondForm r hr :=
  mapped_coordinate_differential (secondEquations r 0)
    (second_chart_jacobianIdeal_eq_top r hr) (secondChartMap r) j

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
theorem coordinate_transition (r : ℂ) (hr : r ^ 3 = 2) (j : Fin 3) :
    overlapDifferentialEquiv r 0
      (KaehlerDifferential.D ℂ (SecondOverlap r 0) (coordinate (secondEquations r 0) j)) =
      overlapEquiv r 0 (chartMinors (secondEquations r 0) j) •
        (-(coordinate (firstEquations r 0) 1) • firstForm r hr) := by
  have hmin := congrFun (overlapEquiv_allMinors r 0) j
  fin_cases j
  · change overlapDifferentialEquiv r 0
      (KaehlerDifferential.D ℂ (SecondOverlap r 0) (coordinate (secondEquations r 0) 0)) =
        overlapEquiv r 0 (chartMinors (secondEquations r 0) 0) •
          (-(coordinate (firstEquations r 0) 1) • firstForm r hr)
    rw [overlapDifferential_coordinate0 r 0, first_coordinate_differential r hr 0,
      first_coordinate_differential r hr 1]
    change overlapEquiv r 0 (chartMinors (secondEquations r 0) 0) =
      -inverse (firstEquations r 0) ^ 2 * chartMinors (firstEquations r 0) 0 +
        coordinate (firstEquations r 0) 0 * inverse (firstEquations r 0) ^ 3 *
          chartMinors (firstEquations r 0) 1 at hmin
    rw [hmin]
    simp only [smul_smul, ← sub_smul]
    rw [outer_coefficient _ _ _ _ _ (coordinate_mul_inverse (firstEquations r 0))]
  · change overlapDifferentialEquiv r 0
      (KaehlerDifferential.D ℂ (SecondOverlap r 0) (coordinate (secondEquations r 0) 1)) =
        overlapEquiv r 0 (chartMinors (secondEquations r 0) 1) •
          (-(coordinate (firstEquations r 0) 1) • firstForm r hr)
    rw [overlapDifferential_coordinate1 r 0, first_coordinate_differential r hr 1]
    change overlapEquiv r 0 (chartMinors (secondEquations r 0) 1) =
      inverse (firstEquations r 0) ^ 3 * chartMinors (firstEquations r 0) 1 at hmin
    rw [hmin]
    simp only [smul_smul]
    rw [middle_coefficient _ _ _ (coordinate_mul_inverse (firstEquations r 0))]
  · change overlapDifferentialEquiv r 0
      (KaehlerDifferential.D ℂ (SecondOverlap r 0) (coordinate (secondEquations r 0) 2)) =
        overlapEquiv r 0 (chartMinors (secondEquations r 0) 2) •
          (-(coordinate (firstEquations r 0) 1) • firstForm r hr)
    rw [overlapDifferential_coordinate2 r 0, first_coordinate_differential r hr 2,
      first_coordinate_differential r hr 1]
    change overlapEquiv r 0 (chartMinors (secondEquations r 0) 2) =
      -inverse (firstEquations r 0) ^ 2 * chartMinors (firstEquations r 0) 2 +
        coordinate (firstEquations r 0) 2 * inverse (firstEquations r 0) ^ 3 *
          chartMinors (firstEquations r 0) 1 at hmin
    rw [hmin]
    simp only [smul_smul, ← sub_smul]
    rw [outer_coefficient _ _ _ _ _ (coordinate_mul_inverse (firstEquations r 0))]

/-- All three actual minors kill the difference between the two forms. -/
theorem minor_smul_transition (r : ℂ) (hr : r ^ 3 = 2) (j : Fin 3) :
    secondChartMap r (chartMinor (secondEquations r 0) j) • secondForm r hr =
      secondChartMap r (chartMinor (secondEquations r 0) j) •
        (-(coordinate (firstEquations r 0) 1) • firstForm r hr) := by
  rw [secondChartMap_minor, ← second_coordinate_differential]
  exact (differentialEquiv_D (overlapEquiv r 0)
    (coordinate (secondEquations r 0) j)).symm.trans (coordinate_transition r hr j)

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
theorem full_overlap_transition (r : ℂ) (hr : r ^ 3 = 2) :
    secondForm r hr = -(coordinate (firstEquations r 0) 1) • firstForm r hr := by
  have hone : (1 : ChartRing (secondEquations r 0)) ∈
      Ideal.span (Set.range (chartMinor (secondEquations r 0))) := by
    change (1 : ChartRing (secondEquations r 0)) ∈ jacobianIdeal (secondEquations r 0)
    rw [second_chart_jacobianIdeal_eq_top r hr]
    trivial
  obtain ⟨w, hw⟩ := Ideal.mem_span_range_iff_exists_fun.mp hone
  have hmap : ∑ j, secondChartMap r (w j) *
      secondChartMap r (chartMinor (secondEquations r 0) j) = 1 := by
    simpa only [map_sum, map_mul, map_one] using congrArg (secondChartMap r) hw
  exact eq_of_bezout_smul _ _ hmap _ _ (minor_smul_transition r hr)

/-- Projective orientation of the first chart's genuine differential. -/
def firstOrientedForm (r : ℂ) (hr : r ^ 3 = 2) : KaehlerDifferential ℂ (FirstOverlap r 0) :=
  -firstForm r hr

/-- In projective orientation, the factor is precisely the coordinate x2/x1. -/
theorem oriented_overlap_transition (r : ℂ) (hr : r ^ 3 = 2) :
    secondForm r hr = coordinate (firstEquations r 0) 1 • firstOrientedForm r hr := by
  rw [full_overlap_transition, firstOrientedForm, smul_neg, neg_smul]

/-- The identity explicitly displays both maps out of the original chart rings. -/
theorem actual_chart_form_transition (r : ℂ) (hr : r ^ 3 = 2) :
    differentialMap (secondChartMap r) (CycleQ2GeometricChartKaehler.secondChartForm r hr) =
      coordinate (firstEquations r 0) 1 • differentialMap (firstChartMap r)
        (-CycleQ2GeometricChartKaehler.firstChartForm r hr) := by
  simpa only [firstOrientedForm, firstForm, secondForm, map_neg] using
    oriented_overlap_transition r hr

/-- Equivalently, restriction to the second overlap followed by the actual
Kähler equivalence gives the same oriented transition. -/
theorem overlap_equivalence_form_transition (r : ℂ) (hr : r ^ 3 = 2) :
    overlapDifferentialEquiv r 0
      (differentialMap (localizationMap (secondEquations r 0))
        (CycleQ2GeometricChartKaehler.secondChartForm r hr)) =
      coordinate (firstEquations r 0) 1 •
        differentialMap (localizationMap (firstEquations r 0))
          (-CycleQ2GeometricChartKaehler.firstChartForm r hr) := by
  change differentialMap (overlapEquiv r 0).toAlgHom
    (differentialMap (localizationMap (secondEquations r 0)) _) = _
  rw [differentialMap_comp]
  exact actual_chart_form_transition r hr

#print axioms full_overlap_transition
#print axioms oriented_overlap_transition
#print axioms actual_chart_form_transition
#print axioms overlap_equivalence_form_transition

end CycleQ2GeometricCanonicalOverlap
end
