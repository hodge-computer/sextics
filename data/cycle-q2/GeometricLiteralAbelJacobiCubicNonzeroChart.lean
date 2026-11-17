import Proposal.GeometricLiteralAbelJacobiEquations
import Proposal.GeometricSeedProjectiveImageChart
import Proposal.GeometricSeedConeSection

/-!
# Curve chart vanishing in the seed cone row ideal

For a homogeneous polynomial, vanishing in the dehomogenized section curve
on the chart X_(j+1) ≠ 0 puts its original numerator in the homogeneous
row ideal on the corresponding seed cone. The chart denominator is
the same coordinate used in the original three-chart Čech complex.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralAbelJacobiCubicNonzeroChart

open MvPolynomial CycleQ2IncidenceImageLine CycleQ2GeometricIncidenceProj
  CycleQ2IncidenceDehomogenizedChart CycleQ2RelativeCurveChart
  CycleQ2RelativeConstantSection CycleQ2SeedConeSection CycleQ2SegreFactorChartExact
  CycleQ2LiteralAbelJacobiEquations

attribute [local instance] CycleQ2SeedProjectiveImageChart.cone_isLocalization

local instance coneCommRing (s : Finset (Fin 3)) : CommRing (Chart s) := inferInstance
local instance surfaceCommRing : CommRing (PointSurface seed) := inferInstance
local instance locCommRing (i : Fin 4) : CommRing (CoordinateLocalization seed i) := inferInstance
local instance coordCommRing (i : Fin 4) : CommRing (CoordinateRing seed i) := inferInstance

private theorem toCone_polynomial (i : Fin 3) (p : P) :
    toCone {i} (surfaceQuotient seed p) = polynomialToCone {i} p := by
  exact congrArg (algebraMap A (Chart {i})) (literalToSeed_polynomial p)

private theorem coneCoordinate_unit (i : Fin 3) :
    IsUnit (toCone {i} (surfaceQuotient seed (X i.succ.castSucc))) := by
  rw [toCone_polynomial, polynomialToCone_apply]
  have h : quotient (X i.succ.castSucc) = CycleQ2SeedProjectiveImageChart.localizingCoordinate i := by
    rw [CycleQ2SeedProjectiveImageChart.localizingCoordinate_eq]
    exact (CycleQ2GeometricSurfaceCoordinates.seedRingEquiv_quotient _ _).symm
  rw [h]
  exact IsLocalization.Away.algebraMap_isUnit _

private def toSeedCone (j : Fin 3) : CoordinateLocalization seed j.succ →+* Chart {j} :=
  IsLocalization.Away.lift (S := CoordinateLocalization seed j.succ) (g := (toCone {j}).toRingHom)
    (surfaceQuotient seed (X j.succ.castSucc)) (coneCoordinate_unit j)

private theorem toSeedCone_base (j : Fin 3) (a : PointSurface seed) :
    toSeedCone j (algebraMap (PointSurface seed) (CoordinateLocalization seed j.succ) a) = toCone {j} a :=
  IsLocalization.Away.lift_eq _ _ a

private theorem toSeedCone_comp (j : Fin 3) :
    (toSeedCone j).comp (algebraMap (PointSurface seed) (CoordinateLocalization seed j.succ)) =
      (toCone {j}).toRingHom := RingHom.ext (toSeedCone_base j)

private theorem rowIdeal_map (t : Fin 3 → ℂ) (j : Fin 3) :
    (relativeSectionIdeal seed t).map (toCone {j}).toRingHom = Ideal.span (Set.range (row t {j})) := by
  rw [relativeSectionIdeal, Ideal.map_span, ← Set.range_comp]
  apply congrArg Ideal.span
  apply congrArg Set.range
  funext a
  change toCone {j} (relativeEquation seed t a) = row t {j} a
  rw [relativeEquation_complex, toCone_equation t {j} (Finset.singleton_nonempty j)]

private theorem localized_mem (t : Fin 3 → ℂ) (i : Fin 4) (n : ℕ) (p : P)
    (hp : p.IsWeightedHomogeneous geometricWeight n)
    (hz : seedChartMap t i (dehomogenize i p) = 0) :
    algebraMap (PointSurface seed) (CoordinateLocalization seed i) (surfaceQuotient seed p) ∈
      (relativeSectionIdeal seed t).map (algebraMap (PointSurface seed) (CoordinateLocalization seed i)) := by
  have hm : homogeneousFraction seed i n p hp ∈ normalizedSectionIdeal seed t i := by
    rw [← coordinateCurveMap_ker]
    change coordinateCurveMap seed t i _ = 0
    apply (curveCoordinateChartEquiv seed t i).injective
    rw [map_zero, curveCoordinateChartEquiv_map, familyCoordinateChartEquiv_homogeneousFraction]
    exact hz
  rw [relativeSectionIdeal_localize_coordinate]
  have hn := Ideal.mem_map_of_mem (algebraMap (CoordinateRing seed i) (CoordinateLocalization seed i)) hm
  have he : (homogeneousFraction seed i n p hp).val *
      algebraMap (PointSurface seed) (CoordinateLocalization seed i) (surfaceQuotient seed (X i.castSucc)) ^ n =
        algebraMap (PointSurface seed) (CoordinateLocalization seed i) (surfaceQuotient seed p) := by
    rw [homogeneousFraction_val, mul_assoc, ← mul_pow, mul_comm (IsLocalization.Away.invSelf _),
      IsLocalization.Away.mul_invSelf, one_pow, mul_one]
  rw [← he]
  exact Ideal.mul_mem_right _ _ hn

/-- Vanishing on the original curve chart descends to membership in its
three-row ideal in the original ungraded seed localization. -/
theorem cone_row_mem (t : Fin 3 → ℂ) (j : Fin 3) (n : ℕ) (p : P)
    (hp : p.IsWeightedHomogeneous geometricWeight n)
    (hz : seedChartMap t j.succ (dehomogenize j.succ p) = 0) :
    polynomialToCone {j} p ∈ Ideal.span (Set.range (row t {j})) := by
  have hm := Ideal.mem_map_of_mem (toSeedCone j) (localized_mem t j.succ n p hp hz)
  rw [toSeedCone_base, toCone_polynomial, Ideal.map_map, toSeedCone_comp, rowIdeal_map] at hm
  exact hm

/-- The same numerator lies in the cone row ideal on every nonempty
intersection of the three original coordinate patches. -/
theorem cone_row_mem_of_all_charts (t : Fin 3 → ℂ) (s : Finset (Fin 3)) (hs : s.Nonempty)
    (n : ℕ) (p : P) (hp : p.IsWeightedHomogeneous geometricWeight n)
    (hz : ∀ i : Fin 4, seedChartMap t i (dehomogenize i p) = 0) :
    polynomialToCone s p ∈ Ideal.span (Set.range (row t s)) := by
  obtain ⟨j, hj⟩ := hs
  let h : ({j} : Finset (Fin 3)) ⊆ s := Finset.singleton_subset_iff.mpr hj
  have hm := Ideal.mem_map_of_mem (restrict h) (cone_row_mem t j n p hp (hz j.succ))
  rw [restrict_polynomial, Ideal.map_span, ← Set.range_comp] at hm
  have he : restrict h ∘ row t {j} = row t s := funext (restrict_row t h)
  rwa [he] at hm

end CycleQ2LiteralAbelJacobiCubicNonzeroChart
end

#print axioms CycleQ2LiteralAbelJacobiCubicNonzeroChart.cone_row_mem_of_all_charts
