import Proposal.GeometricIncidenceDehomogenizedChart
import Proposal.GeometricIncidenceSeedFiber
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.RingTheory.TensorProduct.MvPolynomial

/-!
# Exact seed base change of the actual incidence-surface affine charts

Each affine ring is the shifted dehomogenized equation ring already
identified with an actual weight-one chart of the original projective
surface over its coefficient base. Tensoring that ring along seedMap
gives the corresponding affine ring at the original literal seedPoint.

The equivalence preserves all four affine variables, the shifted normal
coordinate, and the canonical coefficient maps. No scheme gluing,
global projective fiber comparison, or flatness assertion is made here.

The geometric strategy is due to Ben Diamond and the collaborators cited
in solution.md. Prepared for fqlx with OpenAI ChatGPT assistance.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2IncidenceChartSeedFiber

open MvPolynomial
open scoped TensorProduct
open CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations CycleQ2IncidenceUniversalChart
  CycleQ2IncidenceGenericPointSemantics CycleQ2IncidencePolynomialJacobianBinding
  CycleQ2IncidenceImageLine CycleQ2GeometricIncidenceProj
  CycleQ2IncidenceEtaleParameter CycleQ2IncidenceDehomogenizedChart

/- Retain the same local seed action used by the full coordinate-ring
fiber. No new global specialization instance is installed. -/
attribute [local instance] CycleQ2IncidenceSeedFiber.seedAlgebra

@[simp] theorem map_linearCoordinate {R T : Type} [CommRing R] [CommRing T]
    (f : R →+* T) (i j : Fin 4) :
    MvPolynomial.map f (linearCoordinate (S := R) i j) =
      linearCoordinate (S := T) i j := by
  rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨k, rfl⟩
  · simp [linearCoordinate]
  · simp [linearCoordinate]

/-- Coefficient maps commute with the exact shifted coordinate
substitution, including X4 ↦ X none - linearCoordinate i 2 ^ 2. -/
theorem map_dehomogenize {R T : Type} [CommRing R] [CommRing T]
    (f : R →+* T) (i : Fin 4) (p : MvPolynomial (Fin 5) R) :
    MvPolynomial.map f (dehomogenize (S := R) i p) =
      dehomogenize (S := T) i (MvPolynomial.map f p) := by
  have h :
      (MvPolynomial.map f).comp (dehomogenize (S := R) i).toRingHom =
        (dehomogenize (S := T) i).toRingHom.comp (MvPolynomial.map f) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [dehomogenize]
    · intro j
      induction j using Fin.lastCases with
      | last =>
        change MvPolynomial.map f (dehomogenize (S := R) i (X (Fin.last 4))) =
          dehomogenize (S := T) i (MvPolynomial.map f (X (Fin.last 4)))
        simp only [MvPolynomial.map_X, dehomogenize, aeval_X, Fin.lastCases_last,
          map_sub, map_pow, map_linearCoordinate]
      | cast j =>
        change MvPolynomial.map f (dehomogenize (S := R) i (X j.castSucc)) =
          dehomogenize (S := T) i (MvPolynomial.map f (X j.castSucc))
        simp only [MvPolynomial.map_X, dehomogenize, aeval_X, Fin.lastCases_castSucc,
          map_linearCoordinate]
  exact RingHom.congr_fun h p

theorem literal_pointEquationF :
    pointEquationF (seedPoint (57 : ℂ) Complex.I) = smoothF (57 : ℂ) Complex.I := by
  rw [pointEquationF, pointMap_familyF]
  change fullInvariantPolynomial 6 (seedSexticCoefficients (57 : ℂ) Complex.I) = _
  exact seedSexticCoefficients_polynomial (57 : ℂ) Complex.I

theorem literal_pointEquationH :
    pointEquationH (seedPoint (57 : ℂ) Complex.I) = smoothH Complex.I := by
  rw [pointEquationH, pointMap_familyH]
  change fullInvariantPolynomial 3 (seedCubicCoefficients Complex.I) = _
  exact seedCubicCoefficients_polynomial Complex.I

/-- The two source equations specialize to the two equations of the
actual literal seed parameter, with their F,h ordering retained. -/
theorem dehomogenizedEquations_seed (i : Fin 4) (a : Fin 2) :
    MvPolynomial.map seedMap (dehomogenizedEquations incidencePoint i a) =
      dehomogenizedEquations (seedPoint (57 : ℂ) Complex.I) i a := by
  fin_cases a
  · change MvPolynomial.map seedMap (dehomogenize i (pointEquationF incidencePoint)) =
      dehomogenize i (pointEquationF (seedPoint (57 : ℂ) Complex.I))
    rw [map_dehomogenize, CycleQ2EtaleIncidenceCurve.seed_sextic, literal_pointEquationF]
  · change MvPolynomial.map seedMap (dehomogenize i (pointEquationH incidencePoint)) =
      dehomogenize i (pointEquationH (seedPoint (57 : ℂ) Complex.I))
    rw [map_dehomogenize, CycleQ2EtaleIncidenceCurve.seed_cubic, literal_pointEquationH]

theorem chartIdeal_seed (i : Fin 4) :
    (chartIdeal (dehomogenizedEquations incidencePoint i)).map (MvPolynomial.map seedMap) =
      chartIdeal (dehomogenizedEquations (seedPoint (57 : ℂ) Complex.I) i) := by
  unfold chartIdeal
  rw [Ideal.map_span]
  apply congrArg Ideal.span
  ext p
  constructor
  · rintro ⟨q, ⟨a, rfl⟩, rfl⟩
    exact ⟨a, (dehomogenizedEquations_seed i a).symm⟩
  · rintro ⟨a, rfl⟩
    exact ⟨dehomogenizedEquations incidencePoint i a, ⟨a, rfl⟩,
      dehomogenizedEquations_seed i a⟩

abbrev IncidenceChartPolynomial := ChartPolynomial ParameterAlgebra
abbrev SeedChartPolynomial := ChartPolynomial ℂ
abbrev SeedTensorChartPolynomial := ℂ ⊗[ParameterAlgebra] IncidenceChartPolynomial

abbrev SeedChartFiber (i : Fin 4) :=
  ℂ ⊗[ParameterAlgebra] DehomogenizedRing incidencePoint i

local instance seedTensorChartCommRing : CommRing SeedTensorChartPolynomial := inferInstance
local instance seedChartCommRing : CommRing SeedChartPolynomial := inferInstance
local instance seedChartFiberCommRing (i : Fin 4) : CommRing (SeedChartFiber i) := inferInstance
local instance seedDehomogenizedCommRing (i : Fin 4) :
    CommRing (DehomogenizedRing (seedPoint (57 : ℂ) Complex.I) i) := inferInstance

def seedChartPolynomialEquiv :
    SeedTensorChartPolynomial ≃ₐ[ℂ] SeedChartPolynomial :=
  MvPolynomial.algebraTensorAlgEquiv ParameterAlgebra ℂ

@[simp] theorem seedChartPolynomialEquiv_tmul (c : ℂ) (p : IncidenceChartPolynomial) :
    seedChartPolynomialEquiv (c ⊗ₜ[ParameterAlgebra] p) =
      c • MvPolynomial.map seedMap p :=
  MvPolynomial.algebraTensorAlgEquiv_tmul ParameterAlgebra ℂ c p

def tensorChartIdeal (i : Fin 4) : Ideal SeedTensorChartPolynomial :=
  (chartIdeal (dehomogenizedEquations incidencePoint i)).map
    (Algebra.TensorProduct.includeRight (R := ParameterAlgebra) (A := ℂ))

theorem seedChartPolynomialEquiv_includeRight :
    seedChartPolynomialEquiv.toRingHom.comp
      (Algebra.TensorProduct.includeRight (R := ParameterAlgebra) (A := ℂ)
        (B := IncidenceChartPolynomial)).toRingHom = MvPolynomial.map seedMap := by
  apply RingHom.ext
  intro p
  change seedChartPolynomialEquiv (1 ⊗ₜ[ParameterAlgebra] p) = MvPolynomial.map seedMap p
  rw [seedChartPolynomialEquiv_tmul, one_smul]

theorem tensorChartIdeal_map (i : Fin 4) :
    (tensorChartIdeal i).map seedChartPolynomialEquiv.toRingHom =
      chartIdeal (dehomogenizedEquations (seedPoint (57 : ℂ) Complex.I) i) := by
  unfold tensorChartIdeal
  exact (Ideal.map_map (I := chartIdeal (dehomogenizedEquations incidencePoint i))
    (Algebra.TensorProduct.includeRight (R := ParameterAlgebra) (A := ℂ)
      (B := IncidenceChartPolynomial)).toRingHom seedChartPolynomialEquiv.toRingHom).trans
      ((congrArg (fun f : IncidenceChartPolynomial →+* SeedChartPolynomial =>
        (chartIdeal (dehomogenizedEquations incidencePoint i)).map f)
          seedChartPolynomialEquiv_includeRight).trans (chartIdeal_seed i))

/-- Exact base change between the affine rings already bound to the
actual relative chart and the actual literal seed chart. -/
def seedChartFiberEquiv (i : Fin 4) :
    SeedChartFiber i ≃ₐ[ℂ] DehomogenizedRing (seedPoint (57 : ℂ) Complex.I) i :=
  (Algebra.TensorProduct.tensorQuotientEquiv (R := ParameterAlgebra)
    ℂ IncidenceChartPolynomial ℂ (chartIdeal (dehomogenizedEquations incidencePoint i))).trans
      (Ideal.quotientEquivAlg (tensorChartIdeal i)
        (chartIdeal (dehomogenizedEquations (seedPoint (57 : ℂ) Complex.I) i))
        seedChartPolynomialEquiv (tensorChartIdeal_map i).symm)

@[simp] theorem seedChartFiberEquiv_tmul (i : Fin 4) (c : ℂ) (p : IncidenceChartPolynomial) :
    seedChartFiberEquiv i
      (c ⊗ₜ[ParameterAlgebra] dehomogenizedMap incidencePoint i p) =
        c • dehomogenizedMap (seedPoint (57 : ℂ) Complex.I) i (MvPolynomial.map seedMap p) := by
  change seedChartFiberEquiv i
      (c ⊗ₜ[ParameterAlgebra]
        Ideal.Quotient.mk (chartIdeal (dehomogenizedEquations incidencePoint i)) p) =
      c • Ideal.Quotient.mk
        (chartIdeal (dehomogenizedEquations (seedPoint (57 : ℂ) Complex.I) i))
        (MvPolynomial.map seedMap p)
  calc
    _ = Ideal.Quotient.mk
        (chartIdeal (dehomogenizedEquations (seedPoint (57 : ℂ) Complex.I) i))
        (seedChartPolynomialEquiv (c ⊗ₜ[ParameterAlgebra] p)) := rfl
    _ = Ideal.Quotient.mk
        (chartIdeal (dehomogenizedEquations (seedPoint (57 : ℂ) Complex.I) i))
        (c • MvPolynomial.map seedMap p) :=
      congrArg (Ideal.Quotient.mk
        (chartIdeal (dehomogenizedEquations (seedPoint (57 : ℂ) Complex.I) i)))
          (seedChartPolynomialEquiv_tmul c p)
    _ = _ := (Ideal.Quotient.mkₐ ℂ
      (chartIdeal (dehomogenizedEquations (seedPoint (57 : ℂ) Complex.I) i))).toLinearMap.map_smul
        c (MvPolynomial.map seedMap p)

@[simp] theorem seedChartFiberEquiv_variable (i : Fin 4) (j : Option (Fin 3)) :
    seedChartFiberEquiv i
      (1 ⊗ₜ[ParameterAlgebra] dehomogenizedMap incidencePoint i (X j)) =
        dehomogenizedMap (seedPoint (57 : ℂ) Complex.I) i (X j) := by
  rw [seedChartFiberEquiv_tmul, MvPolynomial.map_X, one_smul]

@[simp] theorem seedChartFiberEquiv_coefficient (i : Fin 4) (a : ParameterAlgebra) :
    seedChartFiberEquiv i
      (1 ⊗ₜ[ParameterAlgebra] algebraMap ParameterAlgebra (DehomogenizedRing incidencePoint i) a) =
        algebraMap ℂ (DehomogenizedRing (seedPoint (57 : ℂ) Complex.I) i) (seedMap a) := by
  change seedChartFiberEquiv i
    (1 ⊗ₜ[ParameterAlgebra] dehomogenizedMap incidencePoint i (C a)) = _
  rw [seedChartFiberEquiv_tmul, MvPolynomial.map_C, one_smul]
  rfl

@[simp] theorem seedChartFiberEquiv_complex (i : Fin 4) (c : ℂ) :
    seedChartFiberEquiv i (algebraMap ℂ (SeedChartFiber i) c) =
      algebraMap ℂ (DehomogenizedRing (seedPoint (57 : ℂ) Complex.I) i) c :=
  (seedChartFiberEquiv i).commutes c

@[simp] theorem seedChartFiberEquiv_symm_variable (i : Fin 4) (j : Option (Fin 3)) :
    (seedChartFiberEquiv i).symm
        (dehomogenizedMap (seedPoint (57 : ℂ) Complex.I) i (X j)) =
      1 ⊗ₜ[ParameterAlgebra] dehomogenizedMap incidencePoint i (X j) := by
  apply (seedChartFiberEquiv i).injective
  rw [AlgEquiv.apply_symm_apply, seedChartFiberEquiv_variable]

/-- Original geometric polynomials have the same normalized images
before and after the actual coefficient specialization. -/
theorem seedChartFiberEquiv_dehomogenizedPolynomial
    (i : Fin 4) (p : MvPolynomial (Fin 5) ParameterAlgebra) :
    seedChartFiberEquiv i
      (1 ⊗ₜ[ParameterAlgebra] dehomogenizedMap incidencePoint i (dehomogenize i p)) =
        dehomogenizedMap (seedPoint (57 : ℂ) Complex.I) i
          (dehomogenize i (MvPolynomial.map seedMap p)) := by
  rw [seedChartFiberEquiv_tmul, map_dehomogenize, one_smul]

/-- The shifted normal coordinate is the same original homogeneous
fraction on the source and target projective charts. -/
theorem seedChartFiberEquiv_normal (i : Fin 4) :
    seedChartFiberEquiv i
      (1 ⊗ₜ[ParameterAlgebra] familyCoordinateChartEquiv incidencePoint i
        (coordinateRatio incidencePoint i (Fin.last 4) +
          coordinateRatio incidencePoint i (2 : Fin 4).castSucc ^ 2)) =
      familyCoordinateChartEquiv (seedPoint (57 : ℂ) Complex.I) i
        (coordinateRatio (seedPoint (57 : ℂ) Complex.I) i (Fin.last 4) +
          coordinateRatio (seedPoint (57 : ℂ) Complex.I) i (2 : Fin 4).castSucc ^ 2) := by
  simp only [familyCoordinateChartEquiv_normal, seedChartFiberEquiv_variable]

end CycleQ2IncidenceChartSeedFiber

end

#print axioms CycleQ2IncidenceChartSeedFiber.map_dehomogenize
#print axioms CycleQ2IncidenceChartSeedFiber.chartIdeal_seed
#print axioms CycleQ2IncidenceChartSeedFiber.seedChartFiberEquiv
#print axioms CycleQ2IncidenceChartSeedFiber.seedChartFiberEquiv_normal

