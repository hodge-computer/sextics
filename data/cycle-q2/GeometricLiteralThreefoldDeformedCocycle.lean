import Proposal.GeometricLiteralThreefoldDeformedFrame
import Proposal.GeometricLiteralThreefoldDeformedTransition
import Proposal.GeometricLiteralThreefoldCartanEdge
import Proposal.GeometricLiteralThreefoldExteriorDerivative
import Proposal.GeometricLiteralThreefoldVolumeVariationRestriction
import Proposal.GeometricLiteralThreefoldDeformedOverlap

/-! The actual Čech–de Rham coboundary of the first-order volume.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
set_option maxRecDepth 3000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2LiteralThreefoldDeformedCocycle
open Module CycleQ2LiteralAbelJacobiContraction CycleQ2LiteralThreefoldChartLift
  CycleQ2LiteralThreefoldLiftTransition CycleQ2LiteralThreefoldLiftDifference
  CycleQ2LiteralThreefoldResidueCoordinates CycleQ2LiteralThreefoldResidueChartMaps
  CycleQ2LiteralThreefoldResidueFrame CycleQ2LiteralThreefoldResidueMinors
  CycleQ2LiteralThreefoldSurfaceNormal CycleQ2LiteralThreefoldDeformedVolume
  CycleQ2LiteralThreefoldDeformedFrame CycleQ2LiteralThreefoldDeformedTransition
  CycleQ2LiteralThreefoldCartan CycleQ2LiteralThreefoldCartanLift
  CycleQ2LiteralThreefoldCartanEdge CycleQ2LiteralThreefoldExteriorDerivative
  CycleQ2LiteralThreefoldTestEdges CycleQ2LiteralThreefoldVolumeVariationPatch
  CycleQ2LiteralThreefoldVolumeVariationEvaluation CycleQ2LiteralThreefoldVolumeVariationRestriction
  CycleQ2ExteriorSectionNaturality

variable {S : Type} [CommRing S] [Algebra ℂ S]

/-- The coefficient of ε in the split oriented volume on a weight-one chart. -/
def chartThreeForm (i : Fin 4) := chartCoefficient i • orientedVolume i

private theorem sign_variation (b : Basis (Fin 3) S (OneForms S)) (n : ℕ) (w : JetForms S 3) :
    firstVariation b ((-1 : Jet S)^n • w) = (-1 : S)^n • firstVariation b w := by
  have he : (-1 : Jet S)^n = algebraMap S (Jet S) ((-1 : S)^n) := by simp
  rw [firstVariation, map_smul, smul_eq_mul, he, firstVariation, smul_smul]
  congr 1
  change (-1 : S)^n * _ + 0 * _ = _
  rw [zero_mul, add_zero]
  rfl

private theorem sign_d (b : Basis (Fin 3) S (OneForms S)) (n : ℕ)
    (w : CycleQ2LiteralThreefoldCartan.Forms S 2) :
    exteriorD2 b ((-1 : S)^n • w) = (-1 : S)^n • exteriorD2 b w := by
  change (additive b) ((-1 : S)^n • w) = (-1 : S)^n • (additive b) w
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [pow_succ, mul_neg_one]
    exact (congrArg (additive b) (neg_smul ((-1 : S)^n) w)).trans
      (((additive b).map_neg (((-1 : S)^n) • w)).trans
        ((congrArg Neg.neg ih).trans (neg_smul ((-1 : S)^n) ((additive b) w)).symm))

private theorem canonical_oriented (i j : Fin 4) (f : T i →ₐ[ℂ] S)
    (h : IsUnit (f (CycleQ2LiteralThreefoldResidueFrame.gradient i j)))
    (b : Basis (Fin 3) S (OneForms S)) (u : Fin 3 → S)
    (hu : ∀ l, b l = KaehlerDifferential.D ℂ S (u l)) :
    firstVariation b ((-1 : Jet S)^i.val • volume (canonical i f) f (canonical_liesOver i f)) =
      exteriorDifferentialMap f 3 (chartThreeForm i) := by
  have hc := canonical_variation_of_unit i j f h b u hu
  rw [sign_variation, hc, chartThreeForm, orientedVolume, map_smulₛₗ, map_smulₛₗ]
  simp only [map_pow, map_neg, map_one]
  exact smul_comm _ _ _

section Cartan

variable {i : Fin 4} [Algebra (T i) S] [IsScalarTower ℂ (T i) S]
variable (M : Submonoid (T i)) [hM : IsLocalization M S]
variable (x y : Lift i S) (hx : LiesOver x chartPoint) (hy : LiesOver y chartPoint)
variable (j : Fin 4) (h : IsUnit (fixedGradient (i := i) (S := S) j))
variable (b : Basis (Fin 3) S (OneForms S))
variable (hb : ∀ k, b k = KaehlerDifferential.D ℂ S (chartPoint (coord i (j.succAbove k))))

include hM h hb

private theorem oriented_difference :
    firstVariation b ((-1 : Jet S)^i.val • volume x chartPoint hx) -
      firstVariation b ((-1 : Jet S)^i.val • volume y chartPoint hy) =
      exteriorD2 b (value x y (fun a => (hx a).trans (hy a).symm)) := by
  rw [← contraction_eq_value M x y hx hy, orientedVolume, map_smulₛₗ, map_pow, map_neg, map_one,
    map_smul, sign_d, sign_variation, sign_variation]
  refine (smul_sub ((-1 : S)^i.val) _ _).symm.trans ?_
  apply congrArg (fun z => (-1 : S)^i.val • z)
  rw [firstVariation, firstVariation]
  exact (sub_smul _ _ (orderedVolume b)).symm.trans (actual_volume_difference M x y hx hy j h b hb)

private theorem oriented_difference_over (f : T i →ₐ[ℂ] S) (hf : f = chartPoint)
    (x y : Lift i S) (hx : LiesOver x f) (hy : LiesOver y f) :
    firstVariation b ((-1 : Jet S)^i.val • volume x f hx) -
      firstVariation b ((-1 : Jet S)^i.val • volume y f hy) =
      exteriorD2 b (value x y (fun a => (hx a).trans (hy a).symm)) := by
  subst f
  exact oriented_difference M x y hx hy j h b hb

end Cartan

/-- On the intersection of two weight-one charts, whenever both chosen
pivots are invertible, the differential of the original test edge is the
source variation minus the target variation. -/
theorem pair (i : Fin 4) (k : Fin 3) [Algebra (T (i.succAbove k)) S]
    [IsScalarTower ℂ (T (i.succAbove k)) S] (M : Submonoid (T (i.succAbove k)))
    [IsLocalization M S] (g : FixedOverlap i k →ₐ[ℂ] S) (hg : g.comp (fixedTargetMap i k) = chartPoint)
    (a j : Fin 4) (ha : IsUnit ((g.comp (sourceMap i k)) (CycleQ2LiteralThreefoldResidueFrame.gradient i a)))
    (hj : IsUnit (fixedGradient (i := i.succAbove k) (S := S) j))
    (b : Basis (Fin 3) S (OneForms S)) (hb : ∀ l, b l = KaehlerDifferential.D ℂ S
      (chartPoint (coord (i.succAbove k) (j.succAbove l)))) :
    exteriorDifferentialMap (g.comp (sourceMap i k)) 3 (chartThreeForm i) -
        exteriorDifferentialMap (g.comp (fixedTargetMap i k)) 3 (chartThreeForm (i.succAbove k)) =
      exteriorD2 b (exteriorDifferentialMap g 2 (nativeEdge i k)) := by
  let f := g.comp (sourceMap i k)
  let q := g.comp (fixedTargetMap i k)
  let u : Fin 3 → S := fun l => chartPoint (coord (i.succAbove k) (j.succAbove l))
  have hq : IsUnit (q (CycleQ2LiteralThreefoldResidueFrame.gradient (i.succAbove k) j)) := by
    change IsUnit ((g.comp (fixedTargetMap i k)) _)
    rw [hg]
    exact hj
  rw [← canonical_oriented i a f ha b u hb, ← canonical_oriented _ j q hq b u hb]
  change firstVariation b ((-1 : Jet S)^i.val • volume (sourceLift i k g) f _) - _ = _
  rw [← normalized_volume i k g, nativeEdge_restrict, edgeAt]
  change firstVariation b ((-1 : Jet S)^(i.succAbove k).val • volume (normalizedLift i k g) _ _) -
    firstVariation b ((-1 : Jet S)^(i.succAbove k).val • volume (canonical _ q) q _) = _
  exact oriented_difference_over (M := M) (j := j) (h := hj) (b := b) (hb := hb) q hg _ _ _ _

open CycleQ2LiteralThreefoldDeformedOverlap

private theorem algebraMap_tower {A S : Type} [CommRing A] [CommRing S]
    [Algebra ℂ A] [Algebra ℂ S] (f : A →ₐ[ℂ] S) :
    letI := f.toRingHom.toAlgebra
    IsScalarTower ℂ A S := IsScalarTower.of_algHom f

/-- The coboundary identity on every actual member of the distinguished cover
of every original chart pair, free of frame and localization assumptions. -/
theorem pair_patch (i : Fin 4) (k : Fin 3) (a b : Fin 4) :
    exteriorDifferentialMap ((κ i k a b).comp (sourceMap i k)) 3 (chartThreeForm i) -
        exteriorDifferentialMap ((κ i k a b).comp (fixedTargetMap i k)) 3 (chartThreeForm (i.succAbove k)) =
      exteriorD2 (basisOn i k a b) (exteriorDifferentialMap (κ i k a b) 2 (nativeEdge i k)) := by
  let f := targetMap i k a b
  letI : Algebra (T (i.succAbove k)) (Ring i k a b) := f.toRingHom.toAlgebra
  letI : SMul (T (i.succAbove k)) (Ring i k a b) := f.toRingHom.toAlgebra.toSMul
  letI : Module (T (i.succAbove k)) (Ring i k a b) := f.toRingHom.toAlgebra.toModule
  letI : IsScalarTower ℂ (T (i.succAbove k)) (Ring i k a b) := algebraMap_tower f
  letI : IsLocalization (targetMonoid i k a b) (Ring i k a b) := target_isLocalization i k a b
  exact pair i k (targetMonoid i k a b) (κ i k a b) rfl a b
    (source_unit i k a b) (target_unit i k a b) (basisOn i k a b) (basisOn_apply i k a b)

end CycleQ2LiteralThreefoldDeformedCocycle
end

#print axioms CycleQ2LiteralThreefoldDeformedCocycle.pair_patch
