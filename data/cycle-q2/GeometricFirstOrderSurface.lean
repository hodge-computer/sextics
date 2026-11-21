import Proposal.GeometricFirstOrderNeighborhood
import Proposal.GeometricIncidenceSurfaceNeighborhood

/-!
# The actual first-order ambient surface

Base change of the retained proper smooth surface family along the
original pointed first-order parameter map gives a proper, flat surface
over the dual numbers, smooth of relative dimension two. Pasting the
two pullback squares identifies this as an actual base change of the
original incidence surface, not just of an unrelated local model.

This supplies the first-order ambient family. Flatness of the chosen
curve still needs its regular special-fiber equation to be bound to the
actual base-changed chart rings.

Source-only draft: no elaboration or kernel replay has been run.
Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md for
attribution of the geometric route and the protected certificate gap.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2FirstOrderSurface

open CategoryTheory Limits AlgebraicGeometry
open CycleQ2IncidenceEtaleParameter CycleQ2GeometricIncidenceProj
  CycleQ2IncidenceSmoothNeighborhood CycleQ2IncidenceSurfaceNeighborhood
  CycleQ2IncidenceFirstOrder CycleQ2FirstOrderNeighborhood

def firstOrderSurface : Scheme :=
  pullback seedSmoothFamily firstOrderToSeedBase

def firstOrderSurfaceToBase :
    firstOrderSurface ⟶ Spec (CommRingCat.of (DualNumber ℂ)) :=
  pullback.snd seedSmoothFamily firstOrderToSeedBase

def firstOrderSurfaceToRetained : firstOrderSurface ⟶ seedSmoothSource.toScheme :=
  pullback.fst seedSmoothFamily firstOrderToSeedBase

def firstOrderSurfaceToSurface : firstOrderSurface ⟶ surface incidencePoint :=
  firstOrderSurfaceToRetained ≫ seedSmoothSource.ι

/-- The outer square is the actual pullback of the original incidence
surface along the original dual-number parameter point. -/
theorem firstOrderSurface_isPullback :
    IsPullback firstOrderSurfaceToSurface firstOrderSurfaceToBase
      (surfaceToBase incidencePoint) firstOrderParameterPoint := by
  have h := (IsPullback.of_hasPullback seedSmoothFamily firstOrderToSeedBase).paste_horiz
    (isPullback_morphismRestrict (surfaceToBase incidencePoint) seedSmoothBase).flip
  rw [firstOrderToSeedBase_fac] at h
  exact h

theorem firstOrderSurfaceToSurface_overBase :
    firstOrderSurfaceToSurface ≫ surfaceToBase incidencePoint =
      firstOrderSurfaceToBase ≫ firstOrderParameterPoint :=
  firstOrderSurface_isPullback.w

theorem firstOrderSurfaceToBase_smoothOfRelativeDimension :
    AlgebraicGeometry.SmoothOfRelativeDimension 2 firstOrderSurfaceToBase := by
  letI : MorphismProperty.IsStableUnderBaseChange
      (@AlgebraicGeometry.SmoothOfRelativeDimension 2) :=
    smoothOfRelativeDimension_isStableUnderBaseChange 2
  change AlgebraicGeometry.SmoothOfRelativeDimension 2
    (pullback.snd seedSmoothFamily firstOrderToSeedBase)
  exact MorphismProperty.pullback_snd seedSmoothFamily firstOrderToSeedBase
    seedSmoothFamily_smoothOfRelativeDimension

theorem firstOrderSurfaceToBase_smooth :
    AlgebraicGeometry.Smooth firstOrderSurfaceToBase := by
  letI := firstOrderSurfaceToBase_smoothOfRelativeDimension
  exact AlgebraicGeometry.SmoothOfRelativeDimension.smooth 2 firstOrderSurfaceToBase

theorem firstOrderSurfaceToBase_flat :
    AlgebraicGeometry.Flat firstOrderSurfaceToBase := by
  letI := firstOrderSurfaceToBase_smooth
  infer_instance

theorem firstOrderSurfaceToBase_proper : IsProper firstOrderSurfaceToBase := by
  letI := seedSmoothFamily_proper
  change IsProper (pullback.snd seedSmoothFamily firstOrderToSeedBase)
  infer_instance

end CycleQ2FirstOrderSurface

end

#print axioms CycleQ2FirstOrderSurface.firstOrderSurface_isPullback
#print axioms CycleQ2FirstOrderSurface.firstOrderSurfaceToBase_smoothOfRelativeDimension
#print axioms CycleQ2FirstOrderSurface.firstOrderSurfaceToBase_flat
#print axioms CycleQ2FirstOrderSurface.firstOrderSurfaceToBase_proper
