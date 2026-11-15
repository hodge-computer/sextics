import Proposal.GeometricFirstOrderSurface
import Proposal.GeometricRelativeCurveNeighborhood

/-!
# The original constant-section curve along the first-order parameter path

The curve is the actual pullback of the original closed immersion into
the existing first-order surface. Pasting with the retained ambient
pullback square proves that it is also the actual base change of the
original curve family along the original dual-number parameter point.

The resulting curve is proper over the dual numbers. This file makes no
flatness or nonemptiness assertion; flatness requires the separate
regular-equation calculation on its actual affine charts.

Source-only draft: no Lean elaboration or kernel replay has been run.
Prepared for `fqlx` with OpenAI ChatGPT assistance, following Ben Diamond
and the collaborators credited in solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2FirstOrderCurve

open CategoryTheory Limits AlgebraicGeometry
open CycleQ2IncidenceEtaleParameter CycleQ2GeometricIncidenceProj
  CycleQ2IncidenceFirstOrder CycleQ2FirstOrderSurface
  CycleQ2RelativeConstantCurve CycleQ2RelativeCurveNeighborhood

variable (t : Fin 3 → ℂ)

/-- The same original section, pulled back to the actual first-order surface. -/
def firstOrderCurve : Scheme :=
  pullback (relativeCurveToSurface incidencePoint t) firstOrderSurfaceToSurface

def firstOrderCurveToOriginalCurve :
    firstOrderCurve t ⟶ relativeCurve incidencePoint t :=
  pullback.fst (relativeCurveToSurface incidencePoint t) firstOrderSurfaceToSurface

def firstOrderCurveToSurface : firstOrderCurve t ⟶ firstOrderSurface :=
  pullback.snd (relativeCurveToSurface incidencePoint t) firstOrderSurfaceToSurface

def firstOrderCurveToBase :
    firstOrderCurve t ⟶ Spec (CommRingCat.of (DualNumber ℂ)) :=
  firstOrderCurveToSurface t ≫ firstOrderSurfaceToBase

theorem firstOrderCurveToSurface_isPullback :
    IsPullback (firstOrderCurveToOriginalCurve t) (firstOrderCurveToSurface t)
      (relativeCurveToSurface incidencePoint t) firstOrderSurfaceToSurface :=
  IsPullback.of_hasPullback (relativeCurveToSurface incidencePoint t)
    firstOrderSurfaceToSurface

@[reassoc] theorem firstOrderCurveToSurface_original :
    firstOrderCurveToOriginalCurve t ≫ relativeCurveToSurface incidencePoint t =
      firstOrderCurveToSurface t ≫ firstOrderSurfaceToSurface :=
  (firstOrderCurveToSurface_isPullback t).w

/-- The outer square uses the original incidence base and the original
seed-plus-derivation parameter map, with no replacement family. -/
theorem firstOrderCurve_isPullback :
    IsPullback (firstOrderCurveToOriginalCurve t) (firstOrderCurveToBase t)
      (relativeCurveToBase incidencePoint t) firstOrderParameterPoint := by
  exact (firstOrderCurveToSurface_isPullback t).paste_vert
    firstOrderSurface_isPullback

@[reassoc] theorem firstOrderCurveToOriginalCurve_overBase :
    firstOrderCurveToOriginalCurve t ≫ relativeCurveToBase incidencePoint t =
      firstOrderCurveToBase t ≫ firstOrderParameterPoint :=
  (firstOrderCurve_isPullback t).w

instance firstOrderCurveToSurface_isClosedImmersion :
    IsClosedImmersion (firstOrderCurveToSurface t) := by
  change IsClosedImmersion
    (pullback.snd (relativeCurveToSurface incidencePoint t) firstOrderSurfaceToSurface)
  infer_instance

theorem firstOrderCurveToBase_proper : IsProper (firstOrderCurveToBase t) := by
  letI := firstOrderSurfaceToBase_proper
  change IsProper (firstOrderCurveToSurface t ≫ firstOrderSurfaceToBase)
  infer_instance

end CycleQ2FirstOrderCurve

end

#print axioms CycleQ2FirstOrderCurve.firstOrderCurveToSurface_isPullback
#print axioms CycleQ2FirstOrderCurve.firstOrderCurve_isPullback
#print axioms CycleQ2FirstOrderCurve.firstOrderCurveToSurface_isClosedImmersion
#print axioms CycleQ2FirstOrderCurve.firstOrderCurveToBase_proper
