import Proposal.GeometricLiteralIncidenceTimeCurve
import Proposal.GeometricFirstOrderCurveSeedFiber

/-!
# The original section family on the fixed-sextic parameter curve

The original incidence section gives a proper family over the actual smooth
parameter curve at the fixed complex sextic. Pullback by its retained
tangent gives the previously constructed first-order moving curve, with
both the base projection and the map to the incidence curve identified.
Pullback at the seed gives the original specialized section.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2LiteralIncidenceTimeFamily

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
  CycleQ2LiteralIncidenceTimeCurve CycleQ2IncidenceEtaleParameter
  CycleQ2FirstOrderCurve CycleQ2IncidenceFirstOrder
  CycleQ2RelativeConstantCurve CycleQ2RelativeCurveNeighborhood
  CycleQ2RelativeCurveSeedFiberIso CycleQ2RelativeCurveSeedProj CycleQ2SpecializedProjectiveCurve
  CycleQ2IncidencePolynomialJacobianBinding
open scoped DualNumber

variable (t : Fin 3 → ℂ)

abbrev Family := pullback toIncidence (relativeCurveToBase incidencePoint t)

def toCurve : Family t ⟶ Curve := pullback.fst _ _

def toOriginal : Family t ⟶ relativeCurve incidencePoint t := pullback.snd _ _

theorem family_proper : IsProper (toCurve t) := by
  let _ := relativeCurveToBase_proper incidencePoint t
  dsimp [toCurve]
  infer_instance

private theorem tangent_pullback :
    IsPullback (pullback.fst timeTangent (toCurve t))
      (pullback.snd timeTangent (toCurve t) ≫ toOriginal t)
      firstOrderParameterPoint (relativeCurveToBase incidencePoint t) := by
  have h := (IsPullback.of_hasPullback timeTangent (toCurve t)).paste_vert
    (IsPullback.of_hasPullback toIncidence (relativeCurveToBase incidencePoint t))
  simpa only [toOriginal, timeTangent_to_incidence] using h

def firstOrderIso : firstOrderCurve t ≅ pullback timeTangent (toCurve t) :=
  (firstOrderCurve_isPullback t).flip.isoPullback ≪≫ (tangent_pullback t).isoPullback.symm

@[reassoc, simp] theorem firstOrderIso_toBase :
    (firstOrderIso t).hom ≫ pullback.fst timeTangent (toCurve t) = firstOrderCurveToBase t := by
  simp [firstOrderIso]

@[reassoc, simp] theorem firstOrderIso_toOriginal :
    (firstOrderIso t).hom ≫ pullback.snd timeTangent (toCurve t) ≫ toOriginal t =
      firstOrderCurveToOriginalCurve t := by
  simp [firstOrderIso]

private theorem seed_pullback :
    IsPullback (pullback.fst seed (toCurve t)) (pullback.snd seed (toCurve t) ≫ toOriginal t)
      seedPointMorphism (relativeCurveToBase incidencePoint t) := by
  have h := (IsPullback.of_hasPullback seed (toCurve t)).paste_vert
    (IsPullback.of_hasPullback toIncidence (relativeCurveToBase incidencePoint t))
  simpa only [toOriginal, seed_to_incidence] using h

def seedIso :
    specializedCurve (seedPoint (57 : ℂ) Complex.I) t ≅ pullback seed (toCurve t) :=
  seedCurveFiberIso t ≪≫ (seed_pullback t).isoPullback.symm

@[reassoc, simp] theorem seedIso_toOriginal :
    (seedIso t).hom ≫ pullback.snd seed (toCurve t) ≫ toOriginal t = seedCurveToRelative t := by
  simp [seedIso]
  exact seedCurveFiberIso_hom_snd t

end CycleQ2LiteralIncidenceTimeFamily
end

#print axioms CycleQ2LiteralIncidenceTimeFamily.family_proper
#print axioms CycleQ2LiteralIncidenceTimeFamily.firstOrderIso_toOriginal
#print axioms CycleQ2LiteralIncidenceTimeFamily.seedIso_toOriginal
