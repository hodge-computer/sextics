import Proposal.GeometricIncidenceChartSeedFiber
import Proposal.GeometricIncidenceChartMinor

/-!
# Exact seed specialization of the normalized relative Jacobian minors

Status: source-only proof draft. No elaboration or kernel replay was run.

Coefficient specialization sends the original ordered F,h equations to
the same equations at the literal seed. It therefore preserves their
geometric Jacobian minors. The exact tensor-product comparison of the
actual affine charts sends each normalized relative minor to the
corresponding normalized seed minor.

This is the compatibility needed to transfer the established seed minor
cover through the canonical affine fiber comparison. It introduces no
smoothness or flatness hypothesis and does not assert the whole-fiber
cover or a smooth base neighborhood.

The geometric strategy is due to Ben Diamond and the collaborators cited
in solution.md. Prepared for fqlx with OpenAI ChatGPT assistance.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2IncidenceSeedMinorSpecialization

open MvPolynomial
open scoped TensorProduct
open CycleQ2IncidenceUniversalChart CycleQ2IncidencePolynomialJacobianBinding
  CycleQ2GeometricIncidenceProj CycleQ2IncidenceEtaleParameter
  CycleQ2IncidenceDehomogenizedChart CycleQ2IncidenceChartMinor
  CycleQ2IncidenceChartSeedFiber

attribute [local instance] CycleQ2IncidenceSeedFiber.seedAlgebra

/-- The same ordered pair F,h is retained under the actual seed map. -/
theorem equations_seed :
    (fun a => MvPolynomial.map seedMap
      (CycleQ2IncidenceDehomogenizedChart.equations incidencePoint a)) =
        CycleQ2IncidenceDehomogenizedChart.equations
          (seedPoint (57 : ℂ) Complex.I) := by
  funext a
  fin_cases a
  · exact CycleQ2EtaleIncidenceCurve.seed_sextic.trans literal_pointEquationF.symm
  · exact CycleQ2EtaleIncidenceCurve.seed_cubic.trans literal_pointEquationH.symm

/-- Specialization preserves the geometric derivatives in the minor. -/
theorem surfaceMinor_seed (j k : Fin 5) :
    MvPolynomial.map seedMap (surfaceMinor incidencePoint j k) =
      surfaceMinor (seedPoint (57 : ℂ) Complex.I) j k := by
  change MvPolynomial.map seedMap
      (CycleQ2RelativeJacobianPatch.equationMinor
        (CycleQ2IncidenceDehomogenizedChart.equations incidencePoint) ![j, k]) =
    CycleQ2RelativeJacobianPatch.equationMinor
      (CycleQ2IncidenceDehomogenizedChart.equations
        (seedPoint (57 : ℂ) Complex.I)) ![j, k]
  rw [CycleQ2RelativeJacobianPatch.equationMinor_map, equations_seed]

/-- The exact affine fiber comparison preserves each actual normalized
Jacobian minor, including the original shifted normal coordinate. -/
theorem seedChartFiberEquiv_normalizedMinor (i : Fin 4) (j k : Fin 5) :
    seedChartFiberEquiv i
      (1 ⊗ₜ[ParameterAlgebra] normalizedMinor incidencePoint i j k) =
        normalizedMinor (seedPoint (57 : ℂ) Complex.I) i j k := by
  simpa only [normalizedMinor, surfaceMinor_seed] using
    (seedChartFiberEquiv_dehomogenizedPolynomial i (surfaceMinor incidencePoint j k))

end CycleQ2IncidenceSeedMinorSpecialization

end

#print axioms CycleQ2IncidenceSeedMinorSpecialization.surfaceMinor_seed
#print axioms CycleQ2IncidenceSeedMinorSpecialization.seedChartFiberEquiv_normalizedMinor
