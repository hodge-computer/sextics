import Proposal.GeometricRelativeCurveChart
import Proposal.GeometricIncidenceChartFiberScheme

/-!
# Exact seed base change of the relative curve's affine chart quotients

The original dehomogenized surface chart fiber equivalence preserves the
three fixed-vector rows. Its quotient therefore identifies the actual
tensor-product curve chart fiber with the same affine chart quotient at
the original literal seed, for every retained complex vector.

No flatness, nonemptiness, or global projective fiber assertion is made.
Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md for
attribution of the geometric route and the protected certificate gap.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2RelativeCurveChartFiber

open MvPolynomial
open scoped TensorProduct
open CycleQ2IncidenceUniversalChart CycleQ2IncidenceEtaleParameter
  CycleQ2IncidencePolynomialJacobianBinding CycleQ2IncidenceDehomogenizedChart
  CycleQ2IncidenceChartSeedFiber CycleQ2IncidenceChartFiberScheme
  CycleQ2RelativeConstantSection CycleQ2RelativeCurveChart

attribute [local instance] CycleQ2IncidenceSeedFiber.seedAlgebra

local instance seedScalarModule : Module ParameterAlgebra ℂ :=
  CycleQ2IncidenceSeedFiber.seedAlgebra.toModule
local instance seedScalarSMul : SMul ParameterAlgebra ℂ :=
  CycleQ2IncidenceSeedFiber.seedAlgebra.toSMul

local instance incidenceChartCommRing (i : Fin 4) :
    CommRing (DehomogenizedRing incidencePoint i) := inferInstance
local instance seedChartCommRing (i : Fin 4) :
    CommRing (DehomogenizedRing (seedPoint (57 : ℂ) Complex.I) i) := inferInstance
local instance incidenceCurveChartCommRing (t : Fin 3 → ℂ) (i : Fin 4) :
    CommRing (AffineCurveChart incidencePoint t i) := inferInstance
local instance seedCurveChartCommRing (t : Fin 3 → ℂ) (i : Fin 4) :
    CommRing (AffineCurveChart (seedPoint (57 : ℂ) Complex.I) t i) := inferInstance

local instance incidenceCurveChartAlgebra (t : Fin 3 → ℂ) (i : Fin 4) :
    Algebra ParameterAlgebra (AffineCurveChart incidencePoint t i) := inferInstance
local instance incidenceCurveChartModule (t : Fin 3 → ℂ) (i : Fin 4) :
    Module ParameterAlgebra (AffineCurveChart incidencePoint t i) :=
  (incidenceCurveChartAlgebra t i).toModule
local instance incidenceCurveChartSMul (t : Fin 3 → ℂ) (i : Fin 4) :
    SMul ParameterAlgebra (AffineCurveChart incidencePoint t i) :=
  (incidenceCurveChartAlgebra t i).toSMul

theorem seedChartSpecialization_affineSectionEquation
    (t : Fin 3 → ℂ) (i : Fin 4) (j : Fin 3) :
    seedChartSpecialization i (affineSectionEquation incidencePoint t i j) =
      affineSectionEquation (seedPoint (57 : ℂ) Complex.I) t i j := by
  rw [affineSectionEquation, seedChartSpecialization_dehomogenizedPolynomial,
    relativeSectionPolynomial_seed]
  rfl

theorem affineSectionIdeal_seed (t : Fin 3 → ℂ) (i : Fin 4) :
    (affineSectionIdeal incidencePoint t i).map (seedChartSpecialization i) =
      affineSectionIdeal (seedPoint (57 : ℂ) Complex.I) t i := by
  simp only [affineSectionIdeal, Ideal.map_span, ← Set.range_comp]
  apply congrArg (fun g : Fin 3 → DehomogenizedRing (seedPoint (57 : ℂ) Complex.I) i =>
    Ideal.span (Set.range g))
  funext j
  exact seedChartSpecialization_affineSectionEquation t i j

def tensorAffineSectionIdeal (t : Fin 3 → ℂ) (i : Fin 4) : Ideal (SeedChartFiber i) :=
  (affineSectionIdeal incidencePoint t i).map
    (Algebra.TensorProduct.includeRight (R := ParameterAlgebra) (A := ℂ)).toRingHom

theorem tensorAffineSectionIdeal_map (t : Fin 3 → ℂ) (i : Fin 4) :
    (tensorAffineSectionIdeal t i).map (seedChartFiberEquiv i).toRingHom =
      affineSectionIdeal (seedPoint (57 : ℂ) Complex.I) t i := by
  rw [tensorAffineSectionIdeal, Ideal.map_map]
  exact affineSectionIdeal_seed t i

abbrev CurveChartSeedFiber (t : Fin 3 → ℂ) (i : Fin 4) :=
  ℂ ⊗[ParameterAlgebra] AffineCurveChart incidencePoint t i

local instance curveChartSeedFiberCommRing (t : Fin 3 → ℂ) (i : Fin 4) :
    CommRing (CurveChartSeedFiber t i) := inferInstance

local instance seedChartFiberCommRing (i : Fin 4) : CommRing (SeedChartFiber i) := inferInstance

def curveChartSeedFiberEquiv (t : Fin 3 → ℂ) (i : Fin 4) :
    CurveChartSeedFiber t i ≃ₐ[ℂ]
      AffineCurveChart (seedPoint (57 : ℂ) Complex.I) t i :=
  (Algebra.TensorProduct.tensorQuotientEquiv (R := ParameterAlgebra)
    ℂ (DehomogenizedRing incidencePoint i) ℂ (affineSectionIdeal incidencePoint t i)).trans
      (Ideal.quotientEquivAlg (tensorAffineSectionIdeal t i)
        (affineSectionIdeal (seedPoint (57 : ℂ) Complex.I) t i)
        (seedChartFiberEquiv i) (tensorAffineSectionIdeal_map t i).symm)

@[simp] theorem curveChartSeedFiberEquiv_tmul (t : Fin 3 → ℂ)
    (i : Fin 4) (c : ℂ) (a : DehomogenizedRing incidencePoint i) :
    curveChartSeedFiberEquiv t i
      (c ⊗ₜ[ParameterAlgebra] (show AffineCurveChart incidencePoint t i from
        Ideal.Quotient.mk (affineSectionIdeal incidencePoint t i) a)) =
        c • (show AffineCurveChart (seedPoint (57 : ℂ) Complex.I) t i from
          Ideal.Quotient.mk (affineSectionIdeal (seedPoint (57 : ℂ) Complex.I) t i)
            (seedChartSpecialization i a)) := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective
    (I := chartIdeal (dehomogenizedEquations incidencePoint i)) a
  calc
    _ = Ideal.Quotient.mk (affineSectionIdeal (seedPoint (57 : ℂ) Complex.I) t i)
        (seedChartFiberEquiv i
          (c ⊗ₜ[ParameterAlgebra] dehomogenizedMap incidencePoint i p)) := rfl
    _ = Ideal.Quotient.mk (affineSectionIdeal (seedPoint (57 : ℂ) Complex.I) t i)
        (c • dehomogenizedMap (seedPoint (57 : ℂ) Complex.I) i
          (MvPolynomial.map seedMap p)) :=
      congrArg (Ideal.Quotient.mk
        (affineSectionIdeal (seedPoint (57 : ℂ) Complex.I) t i))
          (seedChartFiberEquiv_tmul i c p)
    _ = _ := by
      erw [seedChartSpecialization_polynomial i p]
      exact (Ideal.Quotient.mkₐ ℂ
        (affineSectionIdeal (seedPoint (57 : ℂ) Complex.I) t i)).toLinearMap.map_smul c _

def curveChartSpecialization (t : Fin 3 → ℂ) (i : Fin 4) :
    AffineCurveChart incidencePoint t i →+*
      AffineCurveChart (seedPoint (57 : ℂ) Complex.I) t i :=
  (show CurveChartSeedFiber t i →+* AffineCurveChart (seedPoint (57 : ℂ) Complex.I) t i from
    (curveChartSeedFiberEquiv t i).toRingHom).comp
      (show AffineCurveChart incidencePoint t i →+* CurveChartSeedFiber t i from
        (Algebra.TensorProduct.includeRight (R := ParameterAlgebra) (A := ℂ)
          (B := AffineCurveChart incidencePoint t i)).toRingHom)

@[simp] theorem curveChartSpecialization_mk (t : Fin 3 → ℂ)
    (i : Fin 4) (a : DehomogenizedRing incidencePoint i) :
    curveChartSpecialization t i (Ideal.Quotient.mk (affineSectionIdeal incidencePoint t i) a) =
      Ideal.Quotient.mk (affineSectionIdeal (seedPoint (57 : ℂ) Complex.I) t i)
        (seedChartSpecialization i a) := by
  change curveChartSeedFiberEquiv t i
    (1 ⊗ₜ[ParameterAlgebra] Ideal.Quotient.mk (affineSectionIdeal incidencePoint t i) a) = _
  rw [curveChartSeedFiberEquiv_tmul, one_smul]

@[simp] theorem curveChartSeedFiberEquiv_variable
    (t : Fin 3 → ℂ) (i : Fin 4) (j : Option (Fin 3)) :
    curveChartSeedFiberEquiv t i
      (1 ⊗ₜ[ParameterAlgebra] Ideal.Quotient.mk (affineSectionIdeal incidencePoint t i)
        (dehomogenizedMap incidencePoint i (X j))) =
      Ideal.Quotient.mk (affineSectionIdeal (seedPoint (57 : ℂ) Complex.I) t i)
        (dehomogenizedMap (seedPoint (57 : ℂ) Complex.I) i (X j)) := by
  rw [curveChartSeedFiberEquiv_tmul, seedChartSpecialization_variable, one_smul]

@[simp] theorem curveChartSeedFiberEquiv_coefficient
    (t : Fin 3 → ℂ) (i : Fin 4) (a : ParameterAlgebra) :
    curveChartSeedFiberEquiv t i
      (1 ⊗ₜ[ParameterAlgebra] algebraMap ParameterAlgebra
        (AffineCurveChart incidencePoint t i) a) =
      algebraMap ℂ (AffineCurveChart (seedPoint (57 : ℂ) Complex.I) t i) (seedMap a) := by
  change curveChartSeedFiberEquiv t i
    (1 ⊗ₜ[ParameterAlgebra] Ideal.Quotient.mk (affineSectionIdeal incidencePoint t i)
      (algebraMap ParameterAlgebra (DehomogenizedRing incidencePoint i) a)) = _
  rw [curveChartSeedFiberEquiv_tmul, seedChartSpecialization_coefficient, one_smul]
  rfl

#print axioms affineSectionIdeal_seed
#print axioms curveChartSeedFiberEquiv
#print axioms curveChartSpecialization_mk
#print axioms curveChartSeedFiberEquiv_coefficient

end CycleQ2RelativeCurveChartFiber
end
