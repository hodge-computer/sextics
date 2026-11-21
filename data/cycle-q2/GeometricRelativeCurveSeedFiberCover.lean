import Proposal.GeometricRelativeCurveSeedChart
import Proposal.GeometricIncidenceSeedFiberCover

/-!
# Actual coordinate opens covering the scheme-theoretic seed curve fiber

The four relative weight-one coordinate opens cover the actual curve
fiber: its image in the original incidence surface lies over the seed,
where the previously proved prime-ideal argument gives this cover.
Pullback pasting identifies each actual open subscheme of the fiber
with the already computed projective curve chart fiber. Both projection
identities are retained. The canonical global seed map pulls these
opens back to the existing specialized curve coordinate opens.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md for
attribution of the geometric route and the protected certificate gap.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2RelativeCurveSeedFiberCover

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open CycleQ2IncidenceNormalForm CycleQ2IncidenceImageLine CycleQ2IncidenceEtaleParameter
  CycleQ2IncidencePolynomialJacobianBinding
  CycleQ2GeometricIncidenceProj CycleQ2IncidenceDehomogenizedChart
  CycleQ2IncidenceChartFiberScheme CycleQ2IncidenceSeedFiberCover
  CycleQ2RelativeConstantCurve CycleQ2RelativeCurveChartScheme
  CycleQ2RelativeCurveChartFiberScheme CycleQ2RelativeCurveSeedProj
  CycleQ2SpecializedProjectiveCurve CycleQ2SpecializedCurveCoordinateChart
  CycleQ2RelativeCurveSeedChart

variable (t : Fin 3 → ℂ) (i : Fin 4)

def fiberCoordinatePatch : (RelativeCurveSchemeSeedFiber t).Opens :=
  pullback.snd seedParameterMorphism (relativeCurveToBase incidencePoint t) ⁻¹ᵁ
    curveCoordinatePatch incidencePoint t i

/-- This identifies an actual open of the global fiber with the
previously computed pullback of the actual projective coordinate chart. -/
def fiberCoordinatePatchIso :
    (fiberCoordinatePatch t i).toScheme ≅ ProjectiveCurveChartSeedFiber t i :=
  (pullbackRestrictIsoRestrict
    (pullback.snd seedParameterMorphism (relativeCurveToBase incidencePoint t))
    (curveCoordinatePatch incidencePoint t i)).symm ≪≫
      pullbackLeftPullbackSndIso seedParameterMorphism
        (relativeCurveToBase incidencePoint t) (curveCoordinatePatch incidencePoint t i).ι

@[reassoc] theorem fiberCoordinatePatchIso_inv_fst :
    (fiberCoordinatePatchIso t i).inv ≫ (fiberCoordinatePatch t i).ι ≫
        pullback.fst seedParameterMorphism (relativeCurveToBase incidencePoint t) =
      pullback.fst seedParameterMorphism (projectiveCurveChartToParameters t i) := by
  change ((pullbackLeftPullbackSndIso seedParameterMorphism
      (relativeCurveToBase incidencePoint t) (curveCoordinatePatch incidencePoint t i).ι).inv ≫
    (pullbackRestrictIsoRestrict
      (pullback.snd seedParameterMorphism (relativeCurveToBase incidencePoint t))
      (curveCoordinatePatch incidencePoint t i)).hom) ≫
      (fiberCoordinatePatch t i).ι ≫
        pullback.fst seedParameterMorphism (relativeCurveToBase incidencePoint t) = _
  dsimp only [fiberCoordinatePatch, projectiveCurveChartToParameters]
  simp only [Category.assoc, pullbackRestrictIsoRestrict_hom_ι_assoc,
    pullbackLeftPullbackSndIso_inv_fst]

@[reassoc] theorem fiberCoordinatePatchIso_inv_snd :
    (fiberCoordinatePatchIso t i).inv ≫ (fiberCoordinatePatch t i).ι ≫
        pullback.snd seedParameterMorphism (relativeCurveToBase incidencePoint t) =
      pullback.snd seedParameterMorphism (projectiveCurveChartToParameters t i) ≫
        (curveCoordinatePatch incidencePoint t i).ι := by
  change ((pullbackLeftPullbackSndIso seedParameterMorphism
      (relativeCurveToBase incidencePoint t) (curveCoordinatePatch incidencePoint t i).ι).inv ≫
    (pullbackRestrictIsoRestrict
      (pullback.snd seedParameterMorphism (relativeCurveToBase incidencePoint t))
      (curveCoordinatePatch incidencePoint t i)).hom) ≫
      (fiberCoordinatePatch t i).ι ≫
        pullback.snd seedParameterMorphism (relativeCurveToBase incidencePoint t) = _
  dsimp only [fiberCoordinatePatch, projectiveCurveChartToParameters]
  simp only [Category.assoc, pullbackRestrictIsoRestrict_hom_ι_assoc,
    pullbackLeftPullbackSndIso_inv_fst_snd]

theorem seedCurveToFiber_preimage_coordinatePatch :
    seedCurveToFiber t ⁻¹ᵁ fiberCoordinatePatch t i =
      specializedCoordinatePatch (seedPoint (57 : ℂ) Complex.I) t i := by
  rw [fiberCoordinatePatch, ← Scheme.Hom.comp_preimage, seedCurveToFiber_snd,
    seedCurveToRelative_preimage_coordinatePatch]

/-- The weight-one cover is proved for the whole actual scheme fiber,
using its original surface image and its actual seed base point. -/
theorem iSup_fiberCoordinatePatch : (⨆ i : Fin 4, fiberCoordinatePatch t i) = ⊤ := by
  apply top_unique
  intro z _
  let c := pullback.snd seedParameterMorphism (relativeCurveToBase incidencePoint t) z
  let x := relativeCurveToSurface incidencePoint t c
  have hx : surfaceToBase incidencePoint x = seedBasePoint := by
    have h := congrArg (fun f : RelativeCurveSchemeSeedFiber t ⟶
        Spec (CommRingCat.of ParameterAlgebra) => f z)
      (pullback.condition (f := seedParameterMorphism)
        (g := relativeCurveToBase incidencePoint t))
    change seedParameterMorphism
      (pullback.fst seedParameterMorphism (relativeCurveToBase incidencePoint t) z) =
        surfaceToBase incidencePoint x at h
    have hz : pullback.fst seedParameterMorphism (relativeCurveToBase incidencePoint t) z =
        (default : Spec (CommRingCat.of ℂ)) := Subsingleton.elim _ _
    rw [hz] at h
    exact h.symm
  obtain ⟨j, hj⟩ := exists_weightOne_of_over_seed x hx
  apply Opens.mem_iSup.mpr
  refine ⟨j, ?_⟩
  change c ∈ curveCoordinatePatch incidencePoint t j
  rw [curveCoordinatePatch_eq_preimage]
  exact hj

#print axioms fiberCoordinatePatchIso
#print axioms fiberCoordinatePatchIso_inv_fst
#print axioms fiberCoordinatePatchIso_inv_snd
#print axioms seedCurveToFiber_preimage_coordinatePatch
#print axioms iSup_fiberCoordinatePatch

end CycleQ2RelativeCurveSeedFiberCover
end
