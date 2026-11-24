import Proposal.GeometricRelativeCurveSeedFiberCover
import Mathlib.AlgebraicGeometry.Morphisms.IsIso

/-!
# The existing specialized curve is the actual global seed fiber

The canonical global graded specialization was already defined over the
original seed parameter map. On each of the four actual target fiber
opens, its restriction is now proved equal to the composite of the
existing specialized-curve chart equivalence, the explicit chart fiber
equivalence, and the actual target-open pullback equivalence. These
opens cover the whole actual fiber. Target-locality of isomorphisms
therefore proves that this one canonical global morphism is an
isomorphism. The resulting isomorphism retains both original pullback
projections.

No assumption about regularity, flatness, or nonemptiness is needed for
this fiber identification. Those are separate geometric obligations.
Source-only draft: no Lean elaboration or kernel replay has been run.
Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md for
attribution of the geometric route and the protected certificate gap.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2RelativeCurveSeedFiberIso

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CycleQ2IncidenceNormalForm CycleQ2IncidenceImageLine CycleQ2IncidenceEtaleParameter
  CycleQ2IncidencePolynomialJacobianBinding CycleQ2GeometricIncidenceProj
  CycleQ2IncidenceChartFiberScheme CycleQ2RelativeConstantCurve
  CycleQ2RelativeCurveChart CycleQ2RelativeCurveChartScheme
  CycleQ2RelativeCurveChartFiberScheme CycleQ2RelativeCurveSeedProj
  CycleQ2SpecializedProjectiveCurve CycleQ2SpecializedCurveCoordinateChart
  CycleQ2RelativeCurveSeedChart CycleQ2RelativeCurveSeedFiberCover

variable (t : Fin 3 → ℂ) (i : Fin 4)

def seedCoordinateFiberIso :
    (specializedCoordinatePatch (seedPoint (57 : ℂ) Complex.I) t i).toScheme ≅
      (fiberCoordinatePatch t i).toScheme :=
  specializedCoordinateAffineChart (seedPoint (57 : ℂ) Complex.I) t i ≪≫
    (projectiveCurveChartSeedFiberIso t i).symm ≪≫ (fiberCoordinatePatchIso t i).symm

/-- Compatibility with the same canonical global map is proved by
both projections of the actual scheme-theoretic fiber. -/
@[reassoc] theorem seedCoordinateFiberIso_hom_ι :
    (seedCoordinateFiberIso t i).hom ≫ (fiberCoordinatePatch t i).ι =
      (specializedCoordinatePatch (seedPoint (57 : ℂ) Complex.I) t i).ι ≫
        seedCurveToFiber t := by
  apply pullback.hom_ext
  · simp only [seedCoordinateFiberIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
      fiberCoordinatePatchIso_inv_fst, projectiveCurveChartSeedFiberIso_inv_fst,
      seedCurveToFiber_fst]
    rw [seedAffineCurveChartToComplex,
      ← specializedCoordinateAffineChart_overBase (seedPoint (57 : ℂ) Complex.I) t i]
    simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  · simp only [seedCoordinateFiberIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
      fiberCoordinatePatchIso_inv_snd, projectiveCurveChartSeedFiberIso_inv_snd_assoc,
      seedCurveToFiber_snd]
    rw [← seedCurveToRelative_on_coordinateChart t i]
    simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]

def seedCurveFiberRestrictionIso :
    (seedCurveToFiber t ⁻¹ᵁ fiberCoordinatePatch t i).toScheme ≅
      (fiberCoordinatePatch t i).toScheme :=
  (specializedCurve (seedPoint (57 : ℂ) Complex.I) t).isoOfEq
      (seedCurveToFiber_preimage_coordinatePatch t i) ≪≫
    seedCoordinateFiberIso t i

theorem seedCurveToFiber_restrict :
    (seedCurveToFiber t ∣_ fiberCoordinatePatch t i) =
      (seedCurveFiberRestrictionIso t i).hom := by
  apply (cancel_mono (fiberCoordinatePatch t i).ι).mp
  rw [morphismRestrict_ι]
  simp only [seedCurveFiberRestrictionIso, Iso.trans_hom, Category.assoc]
  rw [seedCoordinateFiberIso_hom_ι, Scheme.isoOfEq_hom_ι_assoc]

/-- The actual canonical map is an isomorphism, by its proved
restrictions on a proved covering of its actual target. -/
instance seedCurveToFiber_isIso : IsIso (seedCurveToFiber t) := by
  refine IsZariskiLocalAtTarget.of_iSup_eq_top
    (P := MorphismProperty.isomorphisms Scheme) (f := seedCurveToFiber t)
    (fun i : Fin 4 => fiberCoordinatePatch t i) (iSup_fiberCoordinatePatch t) ?_
  intro i
  change IsIso (seedCurveToFiber t ∣_ fiberCoordinatePatch t i)
  rw [seedCurveToFiber_restrict]
  infer_instance

/-- The original existing literal seed curve is the scheme-theoretic
fiber of the original fixed-vector relative curve at the retained seed. -/
def seedCurveFiberIso :
    specializedCurve (seedPoint (57 : ℂ) Complex.I) t ≅ RelativeCurveSchemeSeedFiber t :=
  asIso (seedCurveToFiber t)

@[reassoc, simp] theorem seedCurveFiberIso_hom_fst :
    (seedCurveFiberIso t).hom ≫
        pullback.fst seedParameterMorphism (relativeCurveToBase incidencePoint t) =
      specializedCurveToBase (seedPoint (57 : ℂ) Complex.I) t :=
  seedCurveToFiber_fst t

@[reassoc, simp] theorem seedCurveFiberIso_hom_snd :
    (seedCurveFiberIso t).hom ≫
        pullback.snd seedParameterMorphism (relativeCurveToBase incidencePoint t) =
      seedCurveToRelative t :=
  seedCurveToFiber_snd t

#print axioms seedCoordinateFiberIso_hom_ι
#print axioms seedCurveToFiber_restrict
#print axioms seedCurveToFiber_isIso
#print axioms seedCurveFiberIso
#print axioms seedCurveFiberIso_hom_fst
#print axioms seedCurveFiberIso_hom_snd

end CycleQ2RelativeCurveSeedFiberIso
end
