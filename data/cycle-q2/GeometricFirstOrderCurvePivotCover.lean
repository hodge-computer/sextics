import Proposal.GeometricFirstOrderCurveChartFlat
import Proposal.GeometricRelativeCartierFamily
import Mathlib.RingTheory.Flat.Localization

/-!
# Flatness on the actual first-order curve coordinate charts

The nine original matrix pivots generate the unit ideal on every actual
first-order curve coordinate chart. For any prime of that chart, its
contraction to the original incidence surface is relevant because the
normalized coordinate maps to one. The existing basepoint certificate
then supplies an original matrix pivot outside the contracted prime.

Flatness of the actual localized curve rings therefore descends to the
entire coordinate chart. The final existence theorem retains the same
nonzero complex section vector on all four coordinate charts. No
nonempty curve or flatness over the full parameter base is asserted.

Source-only draft: no Lean elaboration or kernel replay has been run.
Prepared for `fqlx` with OpenAI ChatGPT assistance, following Ben Diamond
and the collaborators credited in solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2FirstOrderCurvePivotCover

open MvPolynomial
open scoped DualNumber TensorProduct
open CycleQ2IncidenceUniversalChart CycleQ2IncidenceEtaleParameter
  CycleQ2IncidenceImageLine CycleQ2IncidenceTraceGeometry
  CycleQ2GeometricIncidenceProj CycleQ2IncidenceDehomogenizedChart
  CycleQ2UniversalCurveCartier CycleQ2RelativeCurveChart
  CycleQ2IncidenceFirstOrder CycleQ2FirstOrderChartReduction
  CycleQ2FirstOrderCurveChartFlat

attribute [local instance] firstOrderAlgebra

/-- The original surface coordinates, followed by the actual curve
quotient and the actual first-order coefficient extension. -/
def surfaceToFirstOrderCurveChart (t : Fin 3 → ℂ) (i : Fin 4) :
    PointSurface incidencePoint →+* FirstOrderCurveChart t i :=
  (Algebra.TensorProduct.includeRight :
      AffineCurveChart incidencePoint t i →ₐ[ParameterAlgebra]
        FirstOrderCurveChart t i).toRingHom.comp
    ((Ideal.Quotient.mk (affineSectionIdeal incidencePoint t i)).comp
      (surfaceToDehomogenized incidencePoint i))

@[simp] theorem surfaceToFirstOrderCurveChart_self (t : Fin 3 → ℂ) (i : Fin 4) :
    surfaceToFirstOrderCurveChart t i
      (surfaceQuotient incidencePoint (X i.castSucc)) = 1 := by
  simp only [surfaceToFirstOrderCurveChart, RingHom.comp_apply,
    surfaceToDehomogenized_self, map_one]

/-- Every prime of the actual first-order curve chart misses an original
matrix pivot; no nonemptiness assumption is needed. -/
theorem exists_curvePivot_not_mem (t : Fin 3 → ℂ) (i : Fin 4)
    (x : PrimeSpectrum (FirstOrderCurveChart t i)) :
    ∃ p : CycleQ2SegreCech.Chart, curvePivot t i p ∉ x.asIdeal := by
  let q : Ideal (PointSurface incidencePoint) :=
    x.asIdeal.comap (surfaceToFirstOrderCurveChart t i)
  letI : x.asIdeal.IsPrime := x.isPrime
  letI : q.IsPrime := inferInstance
  have hcoordinate : ∃ j : Fin 5,
      CycleQ2IncidenceBasepointOpen.curveCoordinate (pointMap incidencePoint) j ∉ q := by
    refine ⟨i.castSucc, ?_⟩
    change surfaceToFirstOrderCurveChart t i
      (surfaceQuotient incidencePoint (X i.castSucc)) ∉ x.asIdeal
    rw [surfaceToFirstOrderCurveChart_self]
    exact x.isPrime.one_not_mem
  have hbasepoint : IsUnit
      (aeval incidencePoint CycleQ2IncidenceBasepointOpen.basepointPolynomial) :=
    tracePoint_extra_unit splitting.P splitting.B _ sliceCoordinate incidence_isTracePoint
  obtain ⟨j, k, hjk⟩ := CycleQ2IncidenceBasepointOpen.specialized_prime_pivot_cover
    (pointMap incidencePoint) hbasepoint q hcoordinate
  refine ⟨(j, k), ?_⟩
  change curvePivot t i (j, k) ∉ x.asIdeal at hjk
  exact hjk

/-- The original nine pivots generate the unit ideal on the entire
first-order curve coordinate chart, including a possibly empty chart. -/
theorem curvePivot_span (t : Fin 3 → ℂ) (i : Fin 4) :
    Ideal.span (Set.range (curvePivot t i)) = ⊤ := by
  by_contra hproper
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal
    (Ideal.span (Set.range (curvePivot t i))) hproper
  letI : m.IsMaximal := hm
  obtain ⟨p, hp⟩ := exists_curvePivot_not_mem t i ⟨m, inferInstance⟩
  exact hp (hle (Ideal.subset_span ⟨p, rfl⟩))

/-- Relative flatness descends from the actual matrix-pivot
localizations because their defining elements span the unit ideal. -/
theorem curveChart_flat_of_refined (t : Fin 3 → ℂ) (i : Fin 4)
    (hflat : ∀ p : CycleQ2SegreCech.Chart,
      Module.Flat (DualNumber ℂ) (RefinedCurveChart t i p)) :
    Module.Flat (DualNumber ℂ) (FirstOrderCurveChart t i) := by
  let S := FirstOrderCurveChart t i
  let s : Set S := Set.range (curvePivot t i)
  apply Module.flat_of_isLocalized_span (R := DualNumber ℂ) S S s
    (curvePivot_span t i)
    (fun z : s => Localization.Away z.val)
    (fun z : s => Algebra.linearMap S (Localization.Away z.val))
  rintro ⟨z, ⟨p, rfl⟩⟩
  exact hflat p

/-- One nonzero original complex section gives flat actual
first-order curve quotients on every original coordinate chart. -/
theorem exists_nonzero_firstOrderCurveCharts_flat :
    ∃ t : Fin 3 → ℂ, t ≠ 0 ∧ ∀ i : Fin 4,
      Module.Flat (DualNumber ℂ) (FirstOrderCurveChart t i) := by
  obtain ⟨t, ht, hflat⟩ := exists_nonzero_flat_refined_curves
  exact ⟨t, ht, fun i => curveChart_flat_of_refined t i (hflat i)⟩

end CycleQ2FirstOrderCurvePivotCover

end

#print axioms CycleQ2FirstOrderCurvePivotCover.exists_curvePivot_not_mem
#print axioms CycleQ2FirstOrderCurvePivotCover.curvePivot_span
#print axioms CycleQ2FirstOrderCurvePivotCover.curveChart_flat_of_refined
#print axioms CycleQ2FirstOrderCurvePivotCover.exists_nonzero_firstOrderCurveCharts_flat
