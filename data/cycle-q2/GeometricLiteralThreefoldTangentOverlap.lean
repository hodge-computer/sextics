import Proposal.GeometricLiteralThreefoldTangentCoordinates
import Proposal.GeometricLiteralThreefoldLiftTransition

/-!
# An intrinsic tangent point on the two-chart intersection

The tangent extracted from a pair of normalized deformation lifts factors
through the affine intersection. Its restriction to the second chart is the
tangent extracted after changing both lifted coordinate systems.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralThreefoldTangentOverlap

open MvPolynomial CycleQ2LiteralAbelJacobiContraction CycleQ2LiteralThreefoldKodairaSpencer
  CycleQ2LiteralThreefoldChartLift CycleQ2LiteralThreefoldResidueCoordinates
  CycleQ2LiteralThreefoldResidueChartMaps CycleQ2LiteralThreefoldLiftTransition
  CycleQ2LiteralThreefoldTangentCoordinates

variable {S : Type} [CommRing S] [Algebra ℂ S]

theorem chart_ext {R : Type} [CommRing R] [Algebra ℂ R] (i : Fin 4)
    {f g : T i →ₐ[ℂ] R} (h : ∀ a : Index, f (q i (X a)) = g (q i (X a))) : f = g := by
  have he : f.comp (q i) = g.comp (q i) := MvPolynomial.algHom_ext h
  ext z
  obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective z
  exact AlgHom.congr_fun he p

private theorem fst_change {i : Fin 4} (x y : Lift i S) (j : Fin 4) (u v : Jet S)
    (h : ∀ a, (x.x a).fst = (y.x a).fst)
    (hu : u * linearValues i x.x j = 1) (hv : v * linearValues i y.x j = 1) (a : Index) :
    ((change x j u hu).x a).fst = ((change y j v hv).x a).fst := by
  let π := (TrivSqZeroExt.fstHom ℂ S S).toRingHom
  have he : π (linearValues i x.x j) = π (linearValues i y.x j) := by
    refine Fin.succAboveCases i ?_ (fun b => ?_) j <;> simp [linearValues, π, h]
  have huv := inverse_fst_eq _ _ _ _ he hu hv
  change π (changedCoordinate i j x.x u a) = π (changedCoordinate i j y.x v a)
  rw [map_changedCoordinate, map_changedCoordinate]
  exact congrArg₂ (fun z b => changedCoordinate i j z b a) (funext h) huv

private theorem tangentPoint_coordinate {i : Fin 4} (x y : Lift i S)
    (h : ∀ a, (x.x a).fst = (y.x a).fst) (a : Index) :
    tangentPoint x y h (q i (X a)) = difference (x.x a) (y.x a) := by
  rw [tangentPoint_mk, aeval_X, aeval_X]

/-- One common tangent point of the affine intersection has the two original
affine tangent representatives as its restrictions. -/
theorem exists_overlap_jet (i : Fin 4) (k : Fin 3) (x y : Lift i S)
    (h : ∀ a, (x.x a).fst = (y.x a).fst) (u v : Jet S)
    (hu : u * linearValues i x.x (i.succAbove k) = 1)
    (hv : v * linearValues i y.x (i.succAbove k) = 1) :
    ∃ (jet : FixedOverlap i k →ₐ[ℂ] Jet S)
      (h' : ∀ a, ((change x (i.succAbove k) u hu).x a).fst =
        ((change y (i.succAbove k) v hv).x a).fst),
      jet.comp (sourceMap i k) = tangentPoint x y h ∧
      jet.comp (fixedTargetMap i k) =
        tangentPoint (change x (i.succAbove k) u hu) (change y (i.succAbove k) v hv) h' := by
  let τ := tangentPoint x y h
  obtain ⟨hinv, hcoord⟩ := difference_change i (i.succAbove k) x.x y.x u v h hu hv
  have ha : difference u v * τ (q i (X (some k))) = 1 := by
    rw [show τ (q i (X (some k))) = difference (x.x (some k)) (y.x (some k)) from
      tangentPoint_coordinate _ _ _ _]
    simpa only [linearValues, Fin.insertNth_apply_succAbove] using hinv
  have hunit : IsUnit (τ (q i (X (some k)))) :=
    isUnit_of_dvd_one ⟨difference u v, (mul_comm _ _).trans ha |>.symm⟩
  let jet := overlapLift i k τ hunit
  let h' := fst_change x y (i.succAbove k) u v h hu hv
  refine ⟨jet, h', AlgHom.ext (fun a => overlapLift_source i k τ hunit a), ?_⟩
  apply chart_ext
  intro a
  change jet (fixedTargetMap i k (q _ (X a))) = _
  rw [show jet (fixedTargetMap i k (q _ (X a))) =
      changedCoordinate i (i.succAbove k) (fun b => τ (q i (X b))) (difference u v) a from
      overlapLift_target_of_inverse i k τ hunit _ ha a, tangentPoint_coordinate]
  have ht : (fun b => τ (q i (X b))) = fun b => difference (x.x b) (y.x b) :=
    funext (tangentPoint_coordinate _ _ _)
  rw [ht]
  exact (congrFun hcoord a).symm

end CycleQ2LiteralThreefoldTangentOverlap
end

#print axioms CycleQ2LiteralThreefoldTangentOverlap.exists_overlap_jet
