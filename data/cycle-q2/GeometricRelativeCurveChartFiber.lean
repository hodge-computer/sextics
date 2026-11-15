import Proposal.GeometricRelativeCurveChart
import Proposal.GeometricIncidenceChartFiberScheme

/-!
# Exact seed base change of the relative curve's affine chart quotients

The original dehomogenized surface chart fiber equivalence preserves the
three fixed-vector rows. Its quotient therefore identifies the actual
tensor-product curve chart fiber with the same affine chart quotient at
the original literal seed, for every retained complex vector.

Source-only draft: no Lean elaboration or kernel replay has been run.
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
  simp only [affineSectionIdeal, Ideal.map_span, Set.image_range]
  apply congrArg (fun g : Fin 3 → DehomogenizedRing (seedPoint (57 : ℂ) Complex.I) i =>
    Ideal.span (Set.range g))
  funext j
  exact seedChartSpecialization_affineSectionEquation t i j

def tensorAffineSectionIdeal (t : Fin 3 → ℂ) (i : Fin 4) : Ideal (SeedChartFiber i) :=
  (affineSectionIdeal incidencePoint t i).map
    (Algebra.TensorProduct.includeRight (R := ParameterAlgebra) (A := ℂ))

theorem tensorAffineSectionIdeal_map (t : Fin 3 → ℂ) (i : Fin 4) :
    (tensorAffineSectionIdeal t i).map (seedChartFiberEquiv i).toRingHom =
      affineSectionIdeal (seedPoint (57 : ℂ) Complex.I) t i := by
  rw [tensorAffineSectionIdeal, Ideal.map_map]
  exact affineSectionIdeal_seed t i

abbrev CurveChartSeedFiber (t : Fin 3 → ℂ) (i : Fin 4) :=
  ℂ ⊗[ParameterAlgebra] AffineCurveChart incidencePoint t i

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
      (c ⊗ₜ[ParameterAlgebra] Ideal.Quotient.mk (affineSectionIdeal incidencePoint t i) a) =
        c • Ideal.Quotient.mk (affineSectionIdeal (seedPoint (57 : ℂ) Complex.I) t i)
          (seedChartSpecialization i a) := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [curveChartSeedFiberEquiv, AlgEquiv.trans_apply,
    Algebra.TensorProduct.tensorQuotientEquiv_apply_tmul, Ideal.quotientEquivAlg_mk,
    seedChartFiberEquiv_tmul, seedChartSpecialization_polynomial]
  exact (Ideal.Quotient.mkₐ ℂ
    (affineSectionIdeal (seedPoint (57 : ℂ) Complex.I) t i)).map_smul c _

def curveChartSpecialization (t : Fin 3 → ℂ) (i : Fin 4) :
    AffineCurveChart incidencePoint t i →+*
      AffineCurveChart (seedPoint (57 : ℂ) Complex.I) t i :=
  (curveChartSeedFiberEquiv t i).toRingHom.comp
    (Algebra.TensorProduct.includeRight (R := ParameterAlgebra) (A := ℂ)).toRingHom

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
