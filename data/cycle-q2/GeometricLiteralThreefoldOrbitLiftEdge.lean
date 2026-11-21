import Proposal.GeometricLiteralThreefoldOrbitLiftChange
import Proposal.GeometricLiteralThreefoldOrbitVolumeAction

/-!
# The acted chart lifts on the actual pair intersections

The normalized source lift and the target lift on an acted overlap have
the original base point after applying the inverse coordinate action.
The residue of their tangent difference is the pullback of the original
edge two-form.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2LiteralThreefoldOrbitLift

open MvPolynomial CycleQ2LiteralAbelJacobiEquations CycleQ2LiteralAbelJacobiContraction
  CycleQ2LiteralThreefoldKodairaSpencer CycleQ2LiteralThreefoldChartLift
  CycleQ2LiteralThreefoldResidueCoordinates CycleQ2LiteralThreefoldResidueChartMaps
  CycleQ2LiteralThreefoldTangentCoordinates CycleQ2LiteralThreefoldLiftDifference
  CycleQ2LiteralThreefoldLiftTransition CycleQ2LiteralThreefoldTriangleLifts
  CycleQ2LiteralThreefoldTestEdges CycleQ2LiteralThreefoldOrbitAction
  CycleQ2LiteralThreefoldOrbitVolume CycleQ2ExteriorSectionNaturality

theorem value_transform {S : Type} [CommRing S] [Algebra ℂ S] {i : Fin 4}
    (z : ℂ) (hz : z^3 = 1) (x y : Lift i S) (h : ∀ a, (x.x a).fst = (y.x a).fst) :
    value (transform z hz x) (transform z hz y) (transform_fst z hz x y h) = value x y h :=
  (congrArg (jetValue i) (tangentPoint_transform z hz x y h)).trans (jetValue_scaled_action z hz i _)

private theorem value_second {S : Type} [CommRing S] [Algebra ℂ S] {i : Fin 4}
    {x y w : Lift i S} (hy : y = w) (h : ∀ a, (x.x a).fst = (y.x a).fst)
    (hw : ∀ a, (x.x a).fst = (w.x a).fst) : value x y h = value x w hw := by
  subst w
  rfl

variable (z : ℂ) (hz : z ^ 3 = 1) (i : Fin 4) (k : Fin 3)
    (A : FixedOverlap i k →ₐ[ℂ] FixedOverlap i k)
    (hs : ∀ t, A (sourceMap i k t) = sourceMap i k (chartAction z hz i t))
    (ht : ∀ t, A (fixedTargetMap i k t) = fixedTargetMap i k (chartAction z hz (i.succAbove k) t))

def actedNormalized : Lift (i.succAbove k) (FixedOverlap i k) :=
  transform (z^2) (square_cube z hz) (normalizedLift i k A)

include hs in
theorem actedNormalized_normalizes :
    Normalizes (mapLift (sourceMap i k) (actedCanonical z hz i)) (actedNormalized z hz i k A) := by
  rw [mapLift_actedCanonical, ← show A.comp (sourceMap i k) = (sourceMap i k).comp (chartAction z hz i)
    from AlgHom.ext hs]
  exact transform_normalizes (z^2) (square_cube z hz) (normalizedLift_normalizes i k A)

include ht in
theorem actedNormalized_liesOver : LiesOver (actedNormalized z hz i k A) (fixedTargetMap i k) := by
  have H := transform_liesOver (z^2) (square_cube z hz) (x := normalizedLift i k A)
    (f := A.comp (fixedTargetMap i k)) (normalizedLift_fst i k A)
  have he : (A.comp (fixedTargetMap i k)).comp (chartAction (z ^ 2) (square_cube z hz) (i.succAbove k)) =
      fixedTargetMap i k := by
    apply AlgHom.ext
    intro t
    change A (fixedTargetMap i k _) = _
    rw [ht]
    exact congrArg (fixedTargetMap i k) (AlgHom.congr_fun (chart_inverse z hz (i.succAbove k)) t)
  rw [he] at H
  exact H

include ht in
theorem actedNormalized_value
    (he : ∀ a, ((actedNormalized z hz i k A).x a).fst =
      ((mapLift (fixedTargetMap i k) (actedCanonical z hz (i.succAbove k))).x a).fst) :
    value (actedNormalized z hz i k A) (mapLift (fixedTargetMap i k) (actedCanonical z hz (i.succAbove k))) he =
      exteriorDifferentialMap A 2 (nativeEdge i k) := by
  let h := normalizedLift_fst i k A
  have htarget : mapLift (fixedTargetMap i k) (actedCanonical z hz (i.succAbove k)) =
      transform (z^2) (square_cube z hz) (canonical (i.succAbove k) (A.comp (fixedTargetMap i k))) := by
    rw [mapLift_actedCanonical]
    exact congrArg (fun f => transform (z^2) (square_cube z hz) (canonical (i.succAbove k) f))
      (AlgHom.ext (fun t => (ht t).symm))
  exact (value_second htarget he (transform_fst (z^2) (square_cube z hz) _ _ h)).trans
    ((value_transform (z^2) (square_cube z hz) (normalizedLift i k A)
      (canonical (i.succAbove k) (A.comp (fixedTargetMap i k))) h).trans
        (nativeEdge_restrict i k A).symm)

end CycleQ2LiteralThreefoldOrbitLift
end

#print axioms CycleQ2LiteralThreefoldOrbitLift.actedNormalized_normalizes
#print axioms CycleQ2LiteralThreefoldOrbitLift.actedNormalized_liesOver
#print axioms CycleQ2LiteralThreefoldOrbitLift.actedNormalized_value
