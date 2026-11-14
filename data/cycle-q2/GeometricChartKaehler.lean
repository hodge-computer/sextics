import Proposal.GeometricSparseJacobianCover
import Proposal.GeometricGlobalResidue
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.RingTheory.Extension.Cotangent.Basic

/-!
# The actual differential module on an entire affine curve chart

For the literal two-equation quotient, the presentation cotangent sequence
identifies the three-coordinate module modulo its two gradient rows with
Mathlib's Kähler differential module. This comparison is valid for every
pair of equations; no smoothness hypothesis or comparison map is assumed.

At the sparse parameters, the proved unit Jacobian ideal then gives a
residue trivialization on each entire affine chart. The image of a coordinate
class is its actual universal differential. These are affine statements;
the projective sheaf and Serre trace comparisons are separate.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2GeometricChartKaehler

open MvPolynomial Module
open CycleQ2GeometricAffineCurveCharts CycleQ2GeometricAffineOverlap
  CycleQ2GeometricCofactorResidue CycleQ2GeometricSparseJacobianCover

/-- The literal quotient presentation, before any minor is inverted. -/
def presentation (v : Fin 2 → AffinePoly) :
    Algebra.Presentation ℂ (ChartRing v) (Fin 3) (Fin 2) :=
  Algebra.Presentation.naive (v := v)

def coordinate (v : Fin 2 → AffinePoly) (j : Fin 3) : ChartRing v := chartMap v (X j)

def gradient (v : Fin 2 → AffinePoly) (i : Fin 2) : Coordinates (ChartRing v) :=
  fun j => chartMap v (pderiv j (v i))

def cotangentCoordinates (v : Fin 2 → AffinePoly) :
    (presentation v).toExtension.CotangentSpace ≃ₗ[ChartRing v] Coordinates (ChartRing v) :=
  (presentation v).cotangentSpaceBasis.repr.trans
    (Finsupp.linearEquivFunOnFinite (ChartRing v) (ChartRing v) (Fin 3))

theorem aeval_presentation (v : Fin 2 → AffinePoly) :
    aeval (presentation v).val = chartMap v := by
  ext j
  simp only [aeval_X]
  rfl

@[simp] theorem cotangentCoordinates_basis (v : Fin 2 → AffinePoly) (j : Fin 3) :
    cotangentCoordinates v ((presentation v).cotangentSpaceBasis j) = coordinateVector j := by
  ext k
  change (presentation v).cotangentSpaceBasis.repr
    ((presentation v).cotangentSpaceBasis j) k = coordinateVector j k
  rw [Basis.repr_self]
  simp [coordinateVector, Finsupp.single_apply, eq_comm]

def relationClass (v : Fin 2 → AffinePoly) (i : Fin 2) :
    (presentation v).toExtension.Cotangent :=
  Algebra.Extension.Cotangent.mk ⟨(presentation v).relation i, (presentation v).relation_mem_ker i⟩

theorem relationClass_span (v : Fin 2 → AffinePoly) :
    Submodule.span (ChartRing v) (Set.range (relationClass v)) = ⊤ :=
  Algebra.Extension.Cotangent.span_eq_top_of_span_eq_ker
    (P := (presentation v).toExtension)
    (presentation v).relation (presentation v).span_range_relation_eq_ker

def relationMap (v : Fin 2 → AffinePoly) :
    (presentation v).toExtension.Cotangent →ₗ[ChartRing v] Coordinates (ChartRing v) :=
  (cotangentCoordinates v).toLinearMap.comp (presentation v).toExtension.cotangentComplex

@[simp] theorem relationMap_relationClass (v : Fin 2 → AffinePoly) (i : Fin 2) :
    relationMap v (relationClass v i) = gradient v i := by
  ext j
  simp only [relationMap, LinearMap.comp_apply, LinearEquiv.coe_coe,
    relationClass, Algebra.Extension.cotangentComplex_mk, cotangentCoordinates,
    LinearEquiv.trans_apply, Finsupp.linearEquivFunOnFinite_apply,
    Algebra.Generators.cotangentSpaceBasis_repr_one_tmul, aeval_presentation]
  rfl

theorem gradient_range (v : Fin 2 → AffinePoly) :
    Set.range (gradient v) = {gradient v 0, gradient v 1} := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp
  · intro hx
    rcases hx with hx | hx
    · exact ⟨0, hx.symm⟩
    · exact ⟨1, hx.symm⟩

theorem relationMap_range (v : Fin 2 → AffinePoly) :
    LinearMap.range (relationMap v) = relations (gradient v 0) (gradient v 1) := by
  rw [← Submodule.map_top, ← relationClass_span v, Submodule.map_span,
    ← Set.range_comp]
  simp only [Function.comp_def, relationMap_relationClass, gradient_range, relations]

/-- The coordinate-to-differential map obtained from the genuine cotangent sequence. -/
def differential (v : Fin 2 → AffinePoly) :
    Coordinates (ChartRing v) →ₗ[ChartRing v] KaehlerDifferential ℂ (ChartRing v) :=
  (presentation v).toExtension.toKaehler.comp (cotangentCoordinates v).symm.toLinearMap

@[simp] theorem differential_coordinateVector (v : Fin 2 → AffinePoly) (j : Fin 3) :
    differential v (coordinateVector j) = KaehlerDifferential.D ℂ (ChartRing v) (coordinate v j) := by
  rw [← cotangentCoordinates_basis v j]
  simp only [differential, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply, Algebra.Generators.toKaehler_cotangentSpaceBasis]
  rfl

theorem differential_surjective (v : Fin 2 → AffinePoly) :
    Function.Surjective (differential v) :=
  (presentation v).toExtension.toKaehler_surjective.comp (cotangentCoordinates v).symm.surjective

theorem differential_kernel (v : Fin 2 → AffinePoly) :
    LinearMap.ker (differential v) = relations (gradient v 0) (gradient v 1) := by
  rw [← relationMap_range]
  ext x
  change (presentation v).toExtension.toKaehler ((cotangentCoordinates v).symm x) = 0 ↔
    ∃ y, relationMap v y = x
  rw [(presentation v).toExtension.exact_cotangentComplex_toKaehler]
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y, by
      change cotangentCoordinates v ((presentation v).toExtension.cotangentComplex y) = x
      rw [hy, LinearEquiv.apply_symm_apply]⟩
  · rintro ⟨y, hy⟩
    exact ⟨y, (cotangentCoordinates v).injective (by
      change relationMap v y = cotangentCoordinates v ((cotangentCoordinates v).symm x)
      rw [LinearEquiv.apply_symm_apply, hy])⟩

/-- The two-gradient cokernel is the actual, unlocalized differential module. -/
def residueKaehlerEquiv (v : Fin 2 → AffinePoly) :
    ResidueModule (gradient v 0) (gradient v 1) ≃ₗ[ChartRing v]
      KaehlerDifferential ℂ (ChartRing v) :=
  (Submodule.quotEquivOfEq _ _ (differential_kernel v).symm).trans
    ((differential v).quotKerEquivOfSurjective (differential_surjective v))

@[simp] theorem residueKaehlerEquiv_toResidue (v : Fin 2 → AffinePoly)
    (x : Coordinates (ChartRing v)) :
    residueKaehlerEquiv v (toResidue (gradient v 0) (gradient v 1) x) = differential v x := rfl

@[simp] theorem residueKaehlerEquiv_coordinate (v : Fin 2 → AffinePoly) (j : Fin 3) :
    residueKaehlerEquiv v
      (toResidue (gradient v 0) (gradient v 1) (coordinateVector j)) =
        KaehlerDifferential.D ℂ (ChartRing v) (coordinate v j) :=
  differential_coordinateVector v j

/-- The coordinate formula uses the same literal minors that cover the chart. -/
theorem cofactor_gradient (v : Fin 2 → AffinePoly) (j : Fin 3) :
    cofactor (gradient v 0) (gradient v 1) j = chartMinor v j := by
  fin_cases j <;>
    simp [cofactor, gradient, chartMinor, minorPolynomial,
      CycleQ2GeometricResidueFrames.jacobianMinors]

theorem minorIdeal_gradient (v : Fin 2 → AffinePoly) :
    CycleQ2GeometricGlobalResidue.minorIdeal (gradient v 0) (gradient v 1) = jacobianIdeal v := by
  unfold CycleQ2GeometricGlobalResidue.minorIdeal jacobianIdeal
  congr 1
  exact congrArg Set.range (funext (cofactor_gradient v))

/-- Residue coefficients trivialize the actual differential module over the
whole affine chart when the actual Jacobian ideal is the unit ideal. -/
def kaehlerResidueEquiv (v : Fin 2 → AffinePoly) (h : jacobianIdeal v = ⊤) :
    KaehlerDifferential ℂ (ChartRing v) ≃ₗ[ChartRing v] ChartRing v :=
  (residueKaehlerEquiv v).symm.trans
    (CycleQ2GeometricGlobalResidue.residueEquiv (gradient v 0) (gradient v 1)
      ((minorIdeal_gradient v).trans h))

@[simp] theorem kaehlerResidueEquiv_coordinate (v : Fin 2 → AffinePoly)
    (h : jacobianIdeal v = ⊤) (j : Fin 3) :
    kaehlerResidueEquiv v h (KaehlerDifferential.D ℂ (ChartRing v) (coordinate v j)) =
      chartMinor v j := by
  change residueFunctional (gradient v 0) (gradient v 1)
    ((residueKaehlerEquiv v).symm
      (KaehlerDifferential.D ℂ (ChartRing v) (coordinate v j))) = _
  rw [← residueKaehlerEquiv_coordinate v j, LinearEquiv.symm_apply_apply,
    residueFunctional_toResidue, coefficient_coordinateVector, cofactor_gradient]

/-- The genuine global differential obtained from the Bezout cofactor frame. -/
def globalForm (v : Fin 2 → AffinePoly) (h : jacobianIdeal v = ⊤) :
    KaehlerDifferential ℂ (ChartRing v) :=
  residueKaehlerEquiv v
    (CycleQ2GeometricGlobalResidue.globalResidue (gradient v 0) (gradient v 1)
      ((minorIdeal_gradient v).trans h))

@[simp] theorem kaehlerResidueEquiv_globalForm (v : Fin 2 → AffinePoly)
    (h : jacobianIdeal v = ⊤) : kaehlerResidueEquiv v h (globalForm v h) = 1 := by
  change residueFunctional (gradient v 0) (gradient v 1)
    ((residueKaehlerEquiv v).symm (residueKaehlerEquiv v _)) = 1
  rw [LinearEquiv.symm_apply_apply, CycleQ2GeometricGlobalResidue.residueFunctional_globalResidue]

/-- Every coordinate differential is its signed minor times the global form. -/
theorem differential_coordinate_eq_smul (v : Fin 2 → AffinePoly)
    (h : jacobianIdeal v = ⊤) (j : Fin 3) :
    KaehlerDifferential.D ℂ (ChartRing v) (coordinate v j) = chartMinor v j • globalForm v h := by
  apply (kaehlerResidueEquiv v h).injective
  rw [kaehlerResidueEquiv_coordinate, map_smul, kaehlerResidueEquiv_globalForm,
    smul_eq_mul, mul_one]

theorem globalForm_unique (v : Fin 2 → AffinePoly) (h : jacobianIdeal v = ⊤)
    (ω : KaehlerDifferential ℂ (ChartRing v)) (hω : kaehlerResidueEquiv v h ω = 1) :
    ω = globalForm v h := by
  apply (kaehlerResidueEquiv v h).injective
  rw [hω, kaehlerResidueEquiv_globalForm]

theorem globalForm_eq_normalized (v : Fin 2 → AffinePoly) (h : jacobianIdeal v = ⊤)
    (j : Fin 3) (u : (ChartRing v)ˣ) (hu : chartMinor v j = (u : ChartRing v)) :
    globalForm v h = (↑(u⁻¹) : ChartRing v) •
      KaehlerDifferential.D ℂ (ChartRing v) (coordinate v j) := by
  apply (kaehlerResidueEquiv v h).injective
  rw [kaehlerResidueEquiv_globalForm, map_smul, kaehlerResidueEquiv_coordinate, hu]
  exact u.inv_mul.symm

/-- The full first chart has a proved, unlocalized residue trivialization. -/
def firstChartKaehlerEquiv (r : ℂ) (hr : r ^ 3 = 2) :
    KaehlerDifferential ℂ (ChartRing (firstEquations r 0)) ≃ₗ[ChartRing (firstEquations r 0)]
      ChartRing (firstEquations r 0) :=
  kaehlerResidueEquiv (firstEquations r 0) (first_chart_jacobianIdeal_eq_top r hr)

/-- The full second chart has a proved, unlocalized residue trivialization. -/
def secondChartKaehlerEquiv (r : ℂ) (hr : r ^ 3 = 2) :
    KaehlerDifferential ℂ (ChartRing (secondEquations r 0)) ≃ₗ[ChartRing (secondEquations r 0)]
      ChartRing (secondEquations r 0) :=
  kaehlerResidueEquiv (secondEquations r 0) (second_chart_jacobianIdeal_eq_top r hr)

def firstChartForm (r : ℂ) (hr : r ^ 3 = 2) :
    KaehlerDifferential ℂ (ChartRing (firstEquations r 0)) :=
  globalForm (firstEquations r 0) (first_chart_jacobianIdeal_eq_top r hr)

def secondChartForm (r : ℂ) (hr : r ^ 3 = 2) :
    KaehlerDifferential ℂ (ChartRing (secondEquations r 0)) :=
  globalForm (secondEquations r 0) (second_chart_jacobianIdeal_eq_top r hr)

@[simp] theorem firstChartKaehlerEquiv_firstChartForm (r : ℂ) (hr : r ^ 3 = 2) :
    firstChartKaehlerEquiv r hr (firstChartForm r hr) = 1 :=
  kaehlerResidueEquiv_globalForm _ _

@[simp] theorem secondChartKaehlerEquiv_secondChartForm (r : ℂ) (hr : r ^ 3 = 2) :
    secondChartKaehlerEquiv r hr (secondChartForm r hr) = 1 :=
  kaehlerResidueEquiv_globalForm _ _

#print axioms residueKaehlerEquiv
#print axioms residueKaehlerEquiv_coordinate
#print axioms kaehlerResidueEquiv
#print axioms differential_coordinate_eq_smul
#print axioms firstChartKaehlerEquiv
#print axioms secondChartKaehlerEquiv

end CycleQ2GeometricChartKaehler
end
