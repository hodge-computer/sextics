import Proposal.GeometricRelativeConstantCurve
import Proposal.GeometricIncidenceSmoothNeighborhood

/-!
# The actual constant-section curve over the smooth seed neighborhood

The original relative curve is restricted to the already constructed base
open containing the original seed. Its map to the restricted original
surface is the target restriction of the original closed immersion. Both
restriction squares are actual pullback squares, and the composite over
the base is the exact restriction of the original curve morphism.

The curve family is proper. The containing surface family is the existing
proper smooth family. Flatness of the curve family, nonempty fibers,
relative dimension one, and the divisor-class comparison are not proved
here. In particular, a regular section can still have an empty zero locus.

Source-only draft: no Lean elaboration or kernel replay has been run.
Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md for
attribution of the geometric route and the protected certificate gap.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2RelativeCurveNeighborhood

open CategoryTheory AlgebraicGeometry
open CycleQ2IncidenceUniversalChart CycleQ2GeometricIncidenceProj
  CycleQ2IncidenceEtaleParameter CycleQ2IncidenceSurfaceProper
  CycleQ2IncidenceSmoothNeighborhood CycleQ2RelativeConstantCurve

section OriginalFamily

variable {S : Type} [CommRing S] [Algebra ℂ S]

/-- The original relative constant-section quotient is proper over its
original coefficient base, whether or not any fiber is empty. -/
theorem relativeCurveToBase_proper (y : ParameterIndex → S) (t : Fin 3 → ℂ) :
    IsProper (relativeCurveToBase y t) := by
  letI := surfaceToBase_proper y
  change IsProper (relativeCurveToSurface y t ≫ surfaceToBase y)
  infer_instance

end OriginalFamily

variable (t : Fin 3 → ℂ)

/-- The full inverse image of the existing seed neighborhood. -/
def seedSmoothCurveOpen : (relativeCurve incidencePoint t).Opens :=
  relativeCurveToBase incidencePoint t ⁻¹ᵁ seedSmoothBase

def seedSmoothCurve : Scheme := (seedSmoothCurveOpen t).toScheme

/-- The curve morphism is the actual target restriction over the same
base open used by the smooth surface family. -/
def seedSmoothCurveFamily : seedSmoothCurve t ⟶ seedSmoothBase.toScheme :=
  (relativeCurveToBase incidencePoint t) ∣_ seedSmoothBase

/-- Restrict the original closed immersion to the full surface preimage
of that base open. Its source is definitionally the same restricted curve. -/
def seedSmoothCurveToSurface : seedSmoothCurve t ⟶ seedSmoothSource.toScheme :=
  (relativeCurveToSurface incidencePoint t) ∣_ seedSmoothSource

instance seedSmoothCurveToSurface_isClosedImmersion :
    IsClosedImmersion (seedSmoothCurveToSurface t) := by
  dsimp only [seedSmoothCurveToSurface]
  infer_instance

/-- The restricted curve and surface maps form the original base square. -/
theorem seedSmoothCurveToSurface_overBase :
    seedSmoothCurveToSurface t ≫ seedSmoothFamily = seedSmoothCurveFamily t := by
  change (relativeCurveToSurface incidencePoint t) ∣_
      (surfaceToBase incidencePoint ⁻¹ᵁ seedSmoothBase) ≫
        (surfaceToBase incidencePoint) ∣_ seedSmoothBase =
    (relativeCurveToSurface incidencePoint t ≫ surfaceToBase incidencePoint) ∣_
      seedSmoothBase
  exact (morphismRestrict_comp (relativeCurveToSurface incidencePoint t)
    (surfaceToBase incidencePoint) seedSmoothBase).symm

theorem seedSmoothCurveToSurface_original :
    seedSmoothCurveToSurface t ≫ seedSmoothSource.ι =
      (seedSmoothCurveOpen t).ι ≫ relativeCurveToSurface incidencePoint t :=
  morphismRestrict_ι (relativeCurveToSurface incidencePoint t) seedSmoothSource

theorem seedSmoothCurveFamily_original :
    seedSmoothCurveFamily t ≫ seedSmoothBase.ι =
      (seedSmoothCurveOpen t).ι ≫ relativeCurveToBase incidencePoint t :=
  morphismRestrict_ι (relativeCurveToBase incidencePoint t) seedSmoothBase

/-- The inclusion into the restricted surface is the actual base change
of the original closed immersion along the surface open inclusion. -/
theorem seedSmoothCurveToSurface_isPullback :
    IsPullback (seedSmoothCurveToSurface t) (seedSmoothCurveOpen t).ι
      seedSmoothSource.ι (relativeCurveToSurface incidencePoint t) :=
  isPullback_morphismRestrict (relativeCurveToSurface incidencePoint t) seedSmoothSource

/-- The curve family is the actual base change along the chosen base open. -/
theorem seedSmoothCurveFamily_isPullback :
    IsPullback (seedSmoothCurveFamily t) (seedSmoothCurveOpen t).ι
      seedSmoothBase.ι (relativeCurveToBase incidencePoint t) :=
  isPullback_morphismRestrict (relativeCurveToBase incidencePoint t) seedSmoothBase

theorem seedSmoothCurveFamily_proper : IsProper (seedSmoothCurveFamily t) := by
  letI := relativeCurveToBase_proper incidencePoint t
  change IsProper ((relativeCurveToBase incidencePoint t) ∣_ seedSmoothBase)
  infer_instance

#print axioms relativeCurveToBase_proper
#print axioms seedSmoothCurveToSurface_isClosedImmersion
#print axioms seedSmoothCurveToSurface_overBase
#print axioms seedSmoothCurveToSurface_isPullback
#print axioms seedSmoothCurveFamily_isPullback
#print axioms seedSmoothCurveFamily_proper

end CycleQ2RelativeCurveNeighborhood
end
