import Proposal.GeometricSmoothImageDimension
import Proposal.GeometricLiteralAbelJacobiTimeProjection
import Proposal.GeometricLiteralAmbientCylinder
import Proposal.GeometricLiteralTimeCurveAffineEmbedding
import Mathlib.AlgebraicGeometry.Noetherian

/-!
# The proper swept support of the actual moving curve family

The domain of the original second projection is a smooth relative surface
over the complex point. Its proper map to the Noetherian time open makes
the source Noetherian. The image dimension bound makes its closed image
strictly smaller than the fixed smooth threefold.

Prepared for fqlx with OpenAI ChatGPT assistance; see solution.md.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace CycleQ2LiteralSweptSupport

open Set TopologicalSpace AlgebraicGeometry CategoryTheory Limits
  CycleQ2SweptSupport CycleQ2LiteralIncidenceTimeCurve CycleQ2LiteralAbelJacobiTimeFamily
  CycleQ2IncidenceEtaleParameter CycleQ2LiteralIncidenceCylinderMap
  CycleQ2LiteralAbelJacobiTimeProjection CycleQ2IncidenceSeedFiberCover

private theorem timeCurve_noetherian : IsNoetherian Curve := by
  have := smooth_parameter_curve
  have : Smooth toComplex := SmoothOfRelativeDimension.smooth 1 _
  exact { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian toComplex }

private theorem source_noetherian (V : parameterScheme.Opens) (t : Fin 3 → ℂ)
    (hs : SmoothOfRelativeDimension 2 (projection V t ≫ (timeOpen V).ι ≫ toComplex))
    (hp : IsProper (projection V t)) : IsNoetherian (family V t) := by
  have := timeCurve_noetherian
  have : Smooth (projection V t ≫ (timeOpen V).ι ≫ toComplex) := SmoothOfRelativeDimension.smooth 2 _
  have : CompactSpace (timeOpen V).toScheme := isCompact_iff_compactSpace.mp
    (NoetherianSpace.isCompact ((timeOpen V : Curve.Opens) : Set Curve))
  have := QuasiCompact.compactSpace_of_compactSpace (projection V t)
  have hn := LocallyOfFiniteType.isLocallyNoetherian (projection V t ≫ (timeOpen V).ι ≫ toComplex)
  exact { toIsLocallyNoetherian := hn }

/-- The scheme-theoretic image of the chosen smooth section family is a proper
closed support inside the original threefold, proper over the complex point. -/
theorem swept_image (V : parameterScheme.Opens) (t : Fin 3 → ℂ) (hV : seedBasePoint ∈ V)
    (hs : SmoothOfRelativeDimension 2 (projection V t ≫ (timeOpen V).ι ≫ toComplex))
    (hp : IsProper (projection V t)) (surj : Function.Surjective (projection V t)) :
    range (q V t).imageι = closure (range (q V t)) ∧
      range (q V t).imageι ≠ univ ∧
      IsProper ((q V t).imageι ≫ pullback.fst seedSextic universalAmbientToBase) := by
  have : IsNoetherian (family V t) := source_noetherian V t hs hp
  have := CycleQ2LiteralAmbientCylinder.fixed_smooth
  have := CycleQ2LiteralAmbientCylinder.fixed_proper
  obtain ⟨x, _⟩ := surj (seedLift V hV (default : Spec (CommRingCat.of ℂ)))
  have hr : range (q V t).imageι = closure (range (q V t)) := by
    change range (q V t).ker.subschemeι = _
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.Hom.support_ker]
  refine ⟨hr, hr.trans_ne ?_, inferInstance⟩
  exact closure_range_ne_univ 2 3 (by decide)
    (projection V t ≫ (timeOpen V).ι ≫ toComplex)
    (pullback.fst seedSextic universalAmbientToBase) (q V t x) (q V t) (q_overComplex V t)

theorem swept_support_of_independent (t : Fin 3 → ℂ) (hi : AlgebraicIndependent ℚ t) :
    ∃ (V : parameterScheme.Opens) (_ : seedBasePoint ∈ V),
      SmoothOfRelativeDimension 2 (projection V t ≫ (timeOpen V).ι ≫ toComplex) ∧
      IsProper (projection V t) ∧
      range (q V t).imageι = closure (range (q V t)) ∧
      range (q V t).imageι ≠ univ ∧
      IsProper ((q V t).imageι ≫ pullback.fst seedSextic universalAmbientToBase) := by
  obtain ⟨V, hV, _, _, hs, hp, surj, _⟩ := time_family_of_independent t hi
  exact ⟨V, hV, hs, hp, swept_image V t hV hs hp surj⟩

theorem exists_swept_support :
    ∃ (t : Fin 3 → ℂ) (_ : AlgebraicIndependent ℚ t)
      (V : parameterScheme.Opens) (_ : seedBasePoint ∈ V),
      range (q V t).imageι = closure (range (q V t)) ∧
      range (q V t).imageι ≠ univ := by
  obtain ⟨t, hi, _⟩ := CycleQ2LiteralAbelJacobiIndependentRegular.exists_independent_regular
  obtain ⟨V, hV, _, _, hr, hn, _⟩ := swept_support_of_independent t hi
  exact ⟨t, hi, V, hV, hr, hn⟩

end CycleQ2LiteralSweptSupport
end

#print axioms CycleQ2LiteralSweptSupport.swept_support_of_independent
#print axioms CycleQ2LiteralSweptSupport.exists_swept_support
