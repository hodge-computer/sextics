import Proposal.GeometricIncidenceConeMinor
import Proposal.GeometricIncidenceLocalizedChart
import Proposal.GeometricIncidenceChartFinitePresentation
import Proposal.GeometricLiteralSurfaceSmooth
import Mathlib.RingTheory.Smooth.Flat

/-!
# Relative smoothness of the actual normalized-minor chart patches

Status: source-only proof draft. No elaboration or kernel replay was run.

The original cone minor localization is smooth over S by its explicit
Jacobian presentation. Its further coordinate localization is smooth.
The actual normalized-minor chart is an S-algebra retract of that
double localization, so it is formally smooth. Its explicit finite
presentation then gives smoothness and hence flatness over S.

No relative smoothness premise, nonvanishing premise, or Noetherian
hypothesis is supplied by the caller. This proves the properties of
these actual principal chart opens; a covering and a single proper
base-shrinking argument are separate obligations.

The geometric strategy is due to Ben Diamond and the collaborators cited
in solution.md. Prepared for fqlx with OpenAI ChatGPT assistance.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2IncidenceChartSmooth

open CycleQ2IncidenceUniversalChart CycleQ2IncidenceDehomogenizedChart
  CycleQ2IncidenceChartMinor CycleQ2IncidenceConeMinor
  CycleQ2IncidenceLocalizedChart CycleQ2IncidenceChartFinitePresentation

variable {S : Type} [CommRing S] [Algebra ℂ S]

theorem doubleCone_smooth (y : ParameterIndex → S) (i : Fin 4)
    (p : Fin 2 → Fin 5) (hp : Function.Injective p) :
    Algebra.Smooth S (DoubleConeRing y i (p 0) (p 1)) := by
  letI : Algebra.Smooth S (ConeMinorRing y (p 0) (p 1)) :=
    coneMinor_smooth y p hp
  letI : Algebra.Smooth (ConeMinorRing y (p 0) (p 1))
      (DoubleConeRing y i (p 0) (p 1)) :=
    Algebra.Smooth.of_isLocalization_Away (coordinateInConeMinor y i (p 0) (p 1))
  exact Algebra.Smooth.comp S (ConeMinorRing y (p 0) (p 1))
    (DoubleConeRing y i (p 0) (p 1))

/-- Every actual projective chart localized at one of the original
normalized Jacobian minors is smooth over the original coefficient base. -/
theorem normalizedMinor_smooth (y : ParameterIndex → S) (i : Fin 4)
    (p : Fin 2 → Fin 5) (hp : Function.Injective p) :
    Algebra.Smooth S (Localization.Away (normalizedMinor y i (p 0) (p 1))) := by
  letI : Algebra.Smooth S (DoubleConeRing y i (p 0) (p 1)) :=
    doubleCone_smooth y i p hp
  letI : Algebra.FormallySmooth S (LocalizedChartRing y i (p 0) (p 1)) :=
    CycleQ2LiteralSurfaceSmooth.formallySmooth_of_retract
      (localizedSection y i (p 0) (p 1))
      (localizedRetraction y i (p 0) (p 1))
      (localizedRetraction_section y i (p 0) (p 1))
  letI : Algebra.FinitePresentation S (LocalizedChartRing y i (p 0) (p 1)) :=
    dehomogenizedAway_finitePresentation y i (normalizedMinor y i (p 0) (p 1))
  exact ⟨inferInstance, inferInstance⟩

theorem normalizedMinor_flat (y : ParameterIndex → S) (i : Fin 4)
    (p : Fin 2 → Fin 5) (hp : Function.Injective p) :
    Module.Flat S (Localization.Away (normalizedMinor y i (p 0) (p 1))) := by
  letI := normalizedMinor_smooth y i p hp
  infer_instance

end CycleQ2IncidenceChartSmooth

end

#print axioms CycleQ2IncidenceChartSmooth.doubleCone_smooth
#print axioms CycleQ2IncidenceChartSmooth.normalizedMinor_smooth
#print axioms CycleQ2IncidenceChartSmooth.normalizedMinor_flat

