import Proposal.GeometricLiteralThreefoldResidueGluing
import Proposal.GeometricLiteralThreefoldLiftTransition
import Proposal.GeometricTangentPointDifferential
import Proposal.GeometricThreefoldContractionAlongMap

/-!
# Evaluation of the oriented threefold residue at an infinitesimal point

The infinitesimal component of a point over the dual numbers contracts the
oriented regular three-form of the fixed sextic to a two-form. The evaluation
agrees on the two ends of the actual projective coordinate change.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2LiteralThreefoldChartEvaluation

open CycleQ2LiteralAbelJacobiContraction CycleQ2LiteralThreefoldChartLift
  CycleQ2LiteralThreefoldLiftTransition CycleQ2LiteralThreefoldResidueCoordinates
  CycleQ2LiteralThreefoldResidueChartMaps CycleQ2LiteralThreefoldChartVolume
  CycleQ2LiteralThreefoldResidueGluing CycleQ2TangentPointDifferential
  CycleQ2ThreefoldContractionAlongMap CycleQ2ExteriorSectionNaturality

attribute [local instance] fixedAmbientAlgebra fixedAmbientTower sourceFixedAlgebra sourceFixedTower

variable {R S S' : Type} [CommRing R] [CommRing S] [CommRing S']
  [Algebra ℂ R] [Algebra ℂ S] [Algebra ℂ S']

/-- The two-form obtained from the actual chart volume and the given tangent point. -/
def evaluate (i : Fin 4) (f : T i →ₐ[ℂ] S) (v : T i →ₐ[ℂ] Jet S)
    (hv : ∀ r, (v r).fst = f r) : Forms S 2 :=
  along 2 f (covector f v hv) ((-1 : T i)^i.val • chartVolume i)

theorem evaluate_precomp (i : Fin 4) (a : T i →ₐ[ℂ] R)
    (f : R →ₐ[ℂ] S) (v : R →ₐ[ℂ] Jet S) (hv : ∀ r, (v r).fst = f r) :
    evaluate i (f.comp a) (v.comp a) (fun r => hv (a r)) =
      along 2 f (covector f v hv)
        (exteriorDifferentialMap a 3 ((-1 : T i)^i.val • chartVolume i)) := by
  apply along_precomp
  intro r
  rw [covector_D, covector_D]
  rfl

theorem evaluate_map (i : Fin 4) (f : T i →ₐ[ℂ] S) (v : T i →ₐ[ℂ] Jet S)
    (hv : ∀ r, (v r).fst = f r) (b : S →ₐ[ℂ] S') :
    exteriorDifferentialMap b 2 (evaluate i f v hv) =
      evaluate i (b.comp f) ((jetMap b).comp v) (fun r => congrArg b (hv r)) := by
  apply along_postcomp
  intro r
  rw [covector_D, covector_D]
  rfl

theorem evaluate_add (i : Fin 4) (f : T i →ₐ[ℂ] S) (v w z : T i →ₐ[ℂ] Jet S)
    (hv : ∀ r, (v r).fst = f r) (hw : ∀ r, (w r).fst = f r) (hz : ∀ r, (z r).fst = f r)
    (hadd : ∀ r, (z r).snd = (v r).snd + (w r).snd) :
    evaluate i f z hz = evaluate i f v hv + evaluate i f w hw := by
  unfold evaluate
  rw [covector_add f v w z hv hw hz hadd, along_add, LinearMap.add_apply]

private theorem exterior_map_sign (f : R →ₐ[ℂ] S) (a : ℕ) (ω : Forms R 3) :
    exteriorDifferentialMap f 3 ((-1 : R)^a • ω) = (-1 : S)^a • exteriorDifferentialMap f 3 ω := by
  rw [(exteriorDifferentialMap f 3).map_smulₛₗ]
  simp only [map_pow, map_neg, map_one]

set_option maxHeartbeats 800000 in
/-- The orientation signs on the two chart volumes already occur in the genuine
overlap theorem before contraction by the tangent point. -/
private theorem oriented_change (i : Fin 4) (k : Fin 3) :
    exteriorDifferentialMap (fixedTargetMap i k) 3
        ((-1 : T (i.succAbove k))^(i.succAbove k).val • chartVolume (i.succAbove k)) =
      exteriorDifferentialMap (sourceMap i k) 3 ((-1 : T i)^i.val • chartVolume i) := by
  exact (exterior_map_sign (fixedTargetMap i k) _ _).trans
    ((fixedChartVolume_overlap i k).trans (exterior_map_sign (sourceMap i k) _ _).symm)

set_option maxHeartbeats 800000 in
/-- The evaluated regular two-form is independent of either weight-one chart on
the true overlap. No gradient pivot has to be inverted for this equality. -/
theorem evaluate_overlap (i : Fin 4) (k : Fin 3)
    (f : FixedOverlap i k →ₐ[ℂ] S) (v : FixedOverlap i k →ₐ[ℂ] Jet S)
    (hv : ∀ r, (v r).fst = f r) :
    evaluate (i.succAbove k) (f.comp (fixedTargetMap i k)) (v.comp (fixedTargetMap i k))
        (fun r => hv (fixedTargetMap i k r)) =
      evaluate i (f.comp (sourceMap i k)) (v.comp (sourceMap i k))
        (fun r => hv (sourceMap i k r)) := by
  exact (evaluate_precomp (i.succAbove k) (fixedTargetMap i k) f v hv).trans
    ((congrArg (along 2 f (covector f v hv)) (oriented_change i k)).trans
      (evaluate_precomp i (sourceMap i k) f v hv).symm)

end CycleQ2LiteralThreefoldChartEvaluation
end

#print axioms CycleQ2LiteralThreefoldChartEvaluation.evaluate_overlap
#print axioms CycleQ2LiteralThreefoldChartEvaluation.evaluate_map
#print axioms CycleQ2LiteralThreefoldChartEvaluation.evaluate_add
