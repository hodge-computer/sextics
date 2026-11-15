import Proposal.GeometricFirstOrderChartFlatness
import Proposal.GeometricFirstOrderLocalizedReduction
import Proposal.GeometricRelativeSectionIdeal
import Proposal.GeometricSimultaneousRegularSection

/-!
# Flat first-order curves on the actual coordinate and matrix-pivot refinements

The rings are localizations of the original first-order three-row curve
chart quotients. The original cofactor identities make the three rows
principal after a matrix pivot is inverted. Exact epsilon reduction
preserves the pivot and the chosen row. Finite associated-prime avoidance
chooses one nonzero complex vector regular on all 36 actual seed
refinements. The proved ambient chart flatness and the regular-quotient
criterion then give flatness of these actual curve localizations.

This is a first-order flatness assertion. It does not assert nonempty
or smooth curves, full-parameter flatness, or an Abel--Jacobi comparison.
Source-only draft: compilation and kernel replay are deferred.
Prepared for fqlx with OpenAI ChatGPT assistance, following the geometric
strategy credited to Ben Diamond and the project in solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2FirstOrderCurveChartFlat

open MvPolynomial
open scoped DualNumber TensorProduct
open CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations
  CycleQ2IncidenceUniversalChart CycleQ2IncidenceImageLine
  CycleQ2IncidencePolynomialJacobianBinding CycleQ2IncidenceEtaleParameter
  CycleQ2IncidenceTraceGeometry CycleQ2IncidencePolynomialRelations
  CycleQ2IncidenceCoefficientRelations CycleQ2GeometricIncidenceProj
  CycleQ2IncidenceDehomogenizedChart CycleQ2IncidenceChartFiberScheme
  CycleQ2IncidenceFirstOrder CycleQ2FirstOrderTensorReduction
  CycleQ2FirstOrderChartReduction CycleQ2FirstOrderChartFlatness
  CycleQ2DualNumberRegularQuotient CycleQ2FirstOrderLocalizedReduction
  CycleQ2UniversalCurveCartier CycleQ2RelativeConstantSection
  CycleQ2RelativeSectionIdeal CycleQ2RelativeCurveChart

attribute [local instance] firstOrderAlgebra CycleQ2IncidenceSeedFiber.seedAlgebra

section OriginalRows

variable {S : Type} [CommRing S] [Algebra ℂ S]

/-- The original matrix entry divided by the fourteenth power of the
chosen weight-one coordinate, in its original affine chart ring. -/
def affineMatrixEntry (y : ParameterIndex → S) (i : Fin 4)
    (p : CycleQ2SegreCech.Chart) : DehomogenizedRing y i :=
  surfaceToDehomogenized y i (basePivot y p)

theorem affineMatrixEntry_polynomial (y : ParameterIndex → S) (i : Fin 4)
    (p : CycleQ2SegreCech.Chart) :
    affineMatrixEntry y i p =
      dehomogenizedMap y i (dehomogenize i (pointMatrixPolynomial y p.1 p.2)) := by
  have hp : basePivot y p = surfaceQuotient y (pointMatrixPolynomial y p.1 p.2) := by
    rw [pointMatrixPolynomial_eq]
    rfl
  rw [affineMatrixEntry, hp, surfaceToDehomogenized_surfaceQuotient]

def dehomogenizedSurfaceMap (y : ParameterIndex → S) (i : Fin 4) :
    PointSurface y →ₐ[S] DehomogenizedRing y i where
  toRingHom := surfaceToDehomogenized y i
  commutes' a := by
    change dehomogenizedMap y i (dehomogenize i (C a)) = _
    rw [AlgHom.commutes]
    rfl

theorem affineSectionEquation_eq_sum (y : ParameterIndex → S) (t : Fin 3 → ℂ)
    (i : Fin 4) (j : Fin 3) :
    affineSectionEquation y t i j =
      ∑ k, t k • affineMatrixEntry y i (j, k) := by
  change dehomogenizedSurfaceMap y i (relativeEquation y t j) = _
  rw [relativeEquation_eq_sum]
  simp only [map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro k _
  exact IsScalarTower.algebraMap_smul S (t k) (affineMatrixEntry y i (j, k))

/-- The previously established original pivot relation remains an
equality of ideals under any further chart map with an invertible pivot. -/
theorem image_rows_principal [Nontrivial S] (y : ParameterIndex → S)
    (t : Fin 3 → ℂ)
    (he : ∀ q, aeval y ((presentation ℂ 57).equation q) = 0)
    (hu : IsUnit (aeval y (leadingProduct ℂ)))
    {T : Type} [CommRing T] (f : PointSurface y →+* T)
    (p : CycleQ2SegreCech.Chart) (hp : IsUnit (f (basePivot y p))) :
    Ideal.span (Set.range (fun j => f (relativeEquation y t j))) =
      Ideal.span {f (relativeEquation y t p.1)} := by
  let g : CoefficientPivot y p →+* T :=
    Localization.awayLift f (basePivot y p) hp
  have hcomp : g.comp (algebraMap (PointSurface y) (CoefficientPivot y p)) = f :=
    IsLocalization.Away.lift_comp (basePivot y p) hp
  have h := congrArg (Ideal.map g) (ordinaryRelativeIdeal_principal y t he hu p)
  simpa only [Ideal.map_map, hcomp, relativeSectionIdeal, Ideal.map_span,
    Set.image_range, Set.image_singleton, g, Localization.awayLift,
    IsLocalization.Away.lift_eq] using h

end OriginalRows

/-! ## Actual first-order source and curve refinements -/

def firstOrderPivot (i : Fin 4) (p : CycleQ2SegreCech.Chart) :
    FirstOrderSurfaceChart i :=
  1 ⊗ₜ[ParameterAlgebra] affineMatrixEntry incidencePoint i p

def curvePivot (t : Fin 3 → ℂ) (i : Fin 4) (p : CycleQ2SegreCech.Chart) :
    FirstOrderCurveChart t i :=
  1 ⊗ₜ[ParameterAlgebra]
    Ideal.Quotient.mk (affineSectionIdeal incidencePoint t i)
      (affineMatrixEntry incidencePoint i p)

abbrev RefinedSurfaceChart (i : Fin 4) (p : CycleQ2SegreCech.Chart) :=
  Localization.Away (firstOrderPivot i p)

/-- An actual principal localization of the already defined first-order
curve chart, retaining the original three-row quotient. -/
abbrev RefinedCurveChart (t : Fin 3 → ℂ) (i : Fin 4)
    (p : CycleQ2SegreCech.Chart) :=
  Localization.Away (curvePivot t i p)

def firstOrderRowIdeal (t : Fin 3 → ℂ) (i : Fin 4) :
    Ideal (FirstOrderSurfaceChart i) :=
  (affineSectionIdeal incidencePoint t i).map
    (Algebra.TensorProduct.includeRight (R := ParameterAlgebra) (A := ℂ[ε])
      (B := DehomogenizedRing incidencePoint i)).toRingHom

theorem firstOrderRowIdeal_eq (t : Fin 3 → ℂ) (i : Fin 4) :
    firstOrderRowIdeal t i = Ideal.span (Set.range (firstOrderSectionRow t i)) := by
  simp only [firstOrderRowIdeal, affineSectionIdeal, Ideal.map_span, Set.image_range]
  rfl

def firstOrderRefinedEquation (t : Fin 3 → ℂ) (i : Fin 4)
    (p : CycleQ2SegreCech.Chart) : RefinedSurfaceChart i p :=
  algebraMap (FirstOrderSurfaceChart i) (RefinedSurfaceChart i p)
    (firstOrderSectionRow t i p.1)

theorem refinedRowIdeal_principal (t : Fin 3 → ℂ) (i : Fin 4)
    (p : CycleQ2SegreCech.Chart) :
    (firstOrderRowIdeal t i).map
        (algebraMap (FirstOrderSurfaceChart i) (RefinedSurfaceChart i p)) =
      Ideal.span {firstOrderRefinedEquation t i p} := by
  let f : PointSurface incidencePoint →+* RefinedSurfaceChart i p :=
    (algebraMap (FirstOrderSurfaceChart i) (RefinedSurfaceChart i p)).comp
      ((Algebra.TensorProduct.includeRight (R := ParameterAlgebra) (A := ℂ[ε])
        (B := DehomogenizedRing incidencePoint i)).toRingHom.comp
          (surfaceToDehomogenized incidencePoint i))
  rw [firstOrderRowIdeal_eq, Ideal.map_span, Set.image_range]
  change Ideal.span (Set.range (fun j => f (relativeEquation incidencePoint t j))) =
    Ideal.span {f (relativeEquation incidencePoint t p.1)}
  apply image_rows_principal incidencePoint t
    (tracePoint_original_equations splitting.P splitting.B _ sliceCoordinate
      incidence_isTracePoint)
    (tracePoint_leading_unit splitting.P splitting.B _ sliceCoordinate
      incidence_isTracePoint) f p
  exact IsLocalization.Away.algebraMap_isUnit (firstOrderPivot i p)

def quotientTensorCurveEquiv (t : Fin 3 → ℂ) (i : Fin 4) :
    (FirstOrderSurfaceChart i ⧸ firstOrderRowIdeal t i) ≃ₐ[ℂ[ε]]
      FirstOrderCurveChart t i :=
  (Algebra.TensorProduct.tensorQuotientEquiv (R := ParameterAlgebra)
    ℂ[ε] (DehomogenizedRing incidencePoint i) ℂ[ε]
      (affineSectionIdeal incidencePoint t i)).symm

@[simp] theorem quotientTensorCurveEquiv_mk_tmul (t : Fin 3 → ℂ) (i : Fin 4)
    (a : ℂ[ε]) (b : DehomogenizedRing incidencePoint i) :
    quotientTensorCurveEquiv t i
      (Ideal.Quotient.mk (firstOrderRowIdeal t i) (a ⊗ₜ[ParameterAlgebra] b)) =
        a ⊗ₜ[ParameterAlgebra] Ideal.Quotient.mk (affineSectionIdeal incidencePoint t i) b :=
  Algebra.TensorProduct.tensorQuotientEquiv_symm_apply_tmul
    ℂ[ε] (DehomogenizedRing incidencePoint i) ℂ[ε]
      (affineSectionIdeal incidencePoint t i) a b

@[simp] theorem quotientTensorCurveEquiv_pivot (t : Fin 3 → ℂ) (i : Fin 4)
    (p : CycleQ2SegreCech.Chart) :
    quotientTensorCurveEquiv t i
      (Ideal.Quotient.mk (firstOrderRowIdeal t i) (firstOrderPivot i p)) =
        curvePivot t i p := by
  rw [firstOrderPivot, quotientTensorCurveEquiv_mk_tmul]
  rfl

/-- Quotienting the actual localized ambient ring gives the actual
localized curve tensor ring, with its unchanged dual-number scalars. -/
def refinedCurveEquiv (t : Fin 3 → ℂ) (i : Fin 4)
    (p : CycleQ2SegreCech.Chart) :
    LocalizedQuotient (firstOrderRowIdeal t i) (firstOrderPivot i p) ≃ₐ[ℂ[ε]]
      RefinedCurveChart t i p :=
  quotientAwayAlgEquiv (firstOrderRowIdeal t i) (firstOrderPivot i p)
    (quotientTensorCurveEquiv t i) (curvePivot t i p) (quotientTensorCurveEquiv_pivot t i p)

/-! ## Exact epsilon reduction and one regular seed vector -/

def seedPivot (i : Fin 4) (p : CycleQ2SegreCech.Chart) :
    DehomogenizedRing (seedPoint (57 : ℂ) Complex.I) i :=
  affineMatrixEntry (seedPoint (57 : ℂ) Complex.I) i p

abbrev SeedRefinement (i : Fin 4) (p : CycleQ2SegreCech.Chart) :=
  Localization.Away (seedPivot i p)

def seedRefinedCoefficient (i : Fin 4) (p : CycleQ2SegreCech.Chart) (j : Fin 3) :
    SeedRefinement i p :=
  algebraMap (DehomogenizedRing (seedPoint (57 : ℂ) Complex.I) i) (SeedRefinement i p)
    (affineMatrixEntry (seedPoint (57 : ℂ) Complex.I) i (p.1, j))

def seedRefinedEquation (t : Fin 3 → ℂ) (i : Fin 4)
    (p : CycleQ2SegreCech.Chart) : SeedRefinement i p :=
  algebraMap (DehomogenizedRing (seedPoint (57 : ℂ) Complex.I) i) (SeedRefinement i p)
    (affineSectionEquation (seedPoint (57 : ℂ) Complex.I) t i p.1)

theorem seedRefinedEquation_eq_sum (t : Fin 3 → ℂ) (i : Fin 4)
    (p : CycleQ2SegreCech.Chart) :
    seedRefinedEquation t i p = ∑ j, t j • seedRefinedCoefficient i p j := by
  unfold seedRefinedEquation
  rw [affineSectionEquation_eq_sum]
  change (IsScalarTower.toAlgHom ℂ
    (DehomogenizedRing (seedPoint (57 : ℂ) Complex.I) i) (SeedRefinement i p))
      (∑ j, t j • affineMatrixEntry (seedPoint (57 : ℂ) Complex.I) i (p.1, j)) = _
  simp only [map_sum, map_smul]
  rfl

theorem seedChartSpecialization_affineMatrixEntry (i : Fin 4)
    (p : CycleQ2SegreCech.Chart) :
    seedChartSpecialization i (affineMatrixEntry incidencePoint i p) = seedPivot i p := by
  rw [affineMatrixEntry_polynomial, seedChartSpecialization_dehomogenizedPolynomial,
    pointMatrixPolynomial_seed]
  exact (affineMatrixEntry_polynomial (seedPoint (57 : ℂ) Complex.I) i p).symm

theorem firstOrderPivot_reduction (i : Fin 4) (p : CycleQ2SegreCech.Chart) :
    surfaceChartReductionEquiv i
        (Ideal.Quotient.mk (epsilonIdeal (k := ℂ) (FirstOrderSurfaceChart i))
          (firstOrderPivot i p)) = seedPivot i p := by
  rw [firstOrderPivot, surfaceChartReductionEquiv_includeRight,
    seedChartSpecialization_affineMatrixEntry]

def refinedReductionEquiv (i : Fin 4) (p : CycleQ2SegreCech.Chart) :
    (RefinedSurfaceChart i p ⧸ epsilonIdeal (k := ℂ) (RefinedSurfaceChart i p)) ≃+*
      SeedRefinement i p :=
  localizedReductionEquiv (firstOrderPivot i p) (surfaceChartReductionEquiv i)
    (seedPivot i p) (firstOrderPivot_reduction i p)

theorem refinedReductionEquiv_equation (t : Fin 3 → ℂ) (i : Fin 4)
    (p : CycleQ2SegreCech.Chart) :
    refinedReductionEquiv i p
        (Ideal.Quotient.mk (epsilonIdeal (k := ℂ) (RefinedSurfaceChart i p))
          (firstOrderRefinedEquation t i p)) = seedRefinedEquation t i p := by
  rw [refinedReductionEquiv, firstOrderRefinedEquation, localizedReductionEquiv_mk,
    firstOrderSectionRow_reduction]
  rfl

theorem exists_nonzero_seed_refined_regular :
    ∃ t : Fin 3 → ℂ, t ≠ 0 ∧ ∀ (i : Fin 4) (p : CycleQ2SegreCech.Chart),
      IsSMulRegular (SeedRefinement i p) (seedRefinedEquation t i p) := by
  obtain ⟨t, ht, hreg⟩ :=
    CycleQ2SimultaneousRegularSection.exists_nonzero_simultaneous_regular
      (k := ℂ) (fun a : Fin 4 × CycleQ2SegreCech.Chart => SeedRefinement a.1 a.2)
      (fun a j => seedRefinedCoefficient a.1 a.2 j)
      (fun a => ⟨a.2.2, IsLocalization.Away.algebraMap_isUnit (seedPivot a.1 a.2)⟩)
  refine ⟨t, ht, fun i p => ?_⟩
  rw [seedRefinedEquation_eq_sum]
  exact hreg (i, p)

theorem refinedCurveChart_flat (t : Fin 3 → ℂ) (i : Fin 4)
    (p : CycleQ2SegreCech.Chart)
    (hreg : IsSMulRegular (SeedRefinement i p) (seedRefinedEquation t i p)) :
    Module.Flat ℂ[ε] (RefinedCurveChart t i p) := by
  letI := firstOrderSurfaceChart_flat i
  letI : Module.Flat ℂ[ε] (RefinedSurfaceChart i p) :=
    Module.Flat.trans ℂ[ε] (FirstOrderSurfaceChart i) (RefinedSurfaceChart i p)
  have hred : IsSMulRegular
      (RefinedSurfaceChart i p ⧸ epsilonIdeal (k := ℂ) (RefinedSurfaceChart i p))
      (Ideal.Quotient.mk (epsilonIdeal (k := ℂ) (RefinedSurfaceChart i p))
        (firstOrderRefinedEquation t i p)) := by
    apply IsSMulRegular.of_right_eq_zero_of_smul
    intro a ha
    apply (refinedReductionEquiv i p).injective
    rw [map_zero]
    apply hreg.right_eq_zero_of_smul
    change seedRefinedEquation t i p * refinedReductionEquiv i p a = 0
    change Ideal.Quotient.mk (epsilonIdeal (k := ℂ) (RefinedSurfaceChart i p))
      (firstOrderRefinedEquation t i p) * a = 0 at ha
    have h := congrArg (refinedReductionEquiv i p) ha
    simpa only [map_mul, map_zero, refinedReductionEquiv_equation] using h
  letI : Module.Flat ℂ[ε]
      (RefinedSurfaceChart i p ⧸ Ideal.span {firstOrderRefinedEquation t i p}) :=
    quotient_flat (firstOrderRefinedEquation t i p) hred
  letI : Module.Flat ℂ[ε]
      (LocalizedQuotient (firstOrderRowIdeal t i) (firstOrderPivot i p)) :=
    Module.Flat.of_linearEquiv
      (Ideal.quotientEquivAlgOfEq ℂ[ε] (refinedRowIdeal_principal t i p)).toLinearEquiv
  exact Module.Flat.of_linearEquiv (refinedCurveEquiv t i p).symm.toLinearEquiv

/-- One fixed nonzero complex section gives flat localizations of every
actual first-order curve chart. All regularity premises are discharged. -/
theorem exists_nonzero_flat_refined_curves :
    ∃ t : Fin 3 → ℂ, t ≠ 0 ∧ ∀ (i : Fin 4) (p : CycleQ2SegreCech.Chart),
      Module.Flat ℂ[ε] (RefinedCurveChart t i p) := by
  obtain ⟨t, ht, hreg⟩ := exists_nonzero_seed_refined_regular
  exact ⟨t, ht, fun i p => refinedCurveChart_flat t i p (hreg i p)⟩

#print axioms image_rows_principal
#print axioms refinedRowIdeal_principal
#print axioms refinedCurveEquiv
#print axioms refinedReductionEquiv_equation
#print axioms exists_nonzero_flat_refined_curves

end CycleQ2FirstOrderCurveChartFlat

end
