import Proposal.GeometricLiteralThreefoldOrbitActionCharts
import Proposal.GeometricLiteralThreefoldLiftTransition
import Proposal.GeometricLiteralThreefoldOverlapAtlas
import Proposal.GeometricChartSectionPullback

/-!
# The induced automorphism on a threefold overlap

The automorphism of the source chart sends its overlap coordinate to a unit
times the same coordinate. It therefore acts on the actual localization, and
the local polynomial and scheme descriptions agree on every subopen.

Prepared for fqlx with OpenAI ChatGPT assistance; see solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace CycleQ2LiteralThreefoldOrbitHodgePullback
open CategoryTheory AlgebraicGeometry MvPolynomial
  CycleQ2GeometricIncidenceProj CycleQ2LiteralThreefoldOrbitAction
  CycleQ2LiteralAbelJacobiContraction CycleQ2LiteralAbelJacobiEquations
  CycleQ2LiteralThreefoldChartLift CycleQ2LiteralThreefoldResidueCoordinates
  CycleQ2LiteralThreefoldResidueChartMaps CycleQ2LiteralThreefoldLiftTransition
  CycleQ2LiteralThreefoldOverlapAtlas CycleQ2LiteralAmbientCharts

attribute [local instance] sourceFixedAlgebra sourceFixedTower sourceFixedLocalization

variable (z : ℂ) (hz : z^3 = 1)

private theorem source_unit (i : Fin 4) (k : Fin 3) :
    IsUnit (((sourceMap i k).comp (chartAction z hz i)) (q i (X (some k)))) := by
  have hs : IsUnit (linearScale z i (i.succAbove k)) :=
    isUnit_iff_ne_zero.mpr (mul_ne_zero (char_ne_zero z hz _) (inv_ne_zero (char_ne_zero z hz _)))
  have hu : IsUnit ((sourceMap i k) (q i (X (some k)))) :=
    IsLocalization.Away.algebraMap_isUnit (S := FixedOverlap i k) (q i (X (some k)))
  have hX : chartPolynomialAction z i (X (some k)) =
      C (linearScale z i (i.succAbove k)) * X (some k) := aeval_X _ _
  change IsUnit (sourceMap i k (chartAction z hz i (Ideal.Quotient.mk _ (X (some k)))))
  rw [chartAction_mk, hX, map_mul, map_mul]
  exact (hs.map (((sourceMap i k).toRingHom.comp (Ideal.Quotient.mk _)).comp C)).mul hu

/-- The literal algebraic pullback of a regular function on the overlap. -/
def overlapAction (i : Fin 4) (k : Fin 3) : FixedOverlap i k →ₐ[ℂ] FixedOverlap i k :=
  overlapLift i k ((sourceMap i k).comp (chartAction z hz i)) (source_unit z hz i k)

theorem overlapAction_source (i : Fin 4) (k : Fin 3) (a : T i) :
    overlapAction z hz i k (sourceMap i k a) = sourceMap i k (chartAction z hz i a) :=
  overlapLift_source i k _ _ a

/-- The affine scheme square for the full localization follows from the source
chart square by composing with its standard principal-open inclusion. -/
theorem overlapIso_equivariant_of_chart (i : Fin 4) (k : Fin 3)
    (hc : chartInclusion i ≫ (threefoldAction z hz).hom =
      Spec.map (CommRingCat.ofHom (chartAction z hz i).toRingHom) ≫ chartInclusion i) :
    (overlapIso i k).hom ≫ (fixedOpen i ⊓ fixedOpen (i.succAbove k)).ι ≫ (threefoldAction z hz).hom =
      Spec.map (CommRingCat.ofHom (overlapAction z hz i k).toRingHom) ≫
        (overlapIso i k).hom ≫ (fixedOpen i ⊓ fixedOpen (i.succAbove k)).ι := by
  rw [← Category.assoc, overlapIso_hom_ι, Category.assoc, hc, ← Category.assoc, ← Spec.map_comp,
    ← Category.assoc, ← Spec.map_comp]
  apply congrArg (fun f => Spec.map f ≫ chartInclusion i)
  apply CommRingCat.hom_ext
  exact RingHom.ext (fun a => (overlapAction_source z hz i k a).symm)

private theorem target_action_of_spec_square {A B : Type} [CommRing A] [Algebra ℂ A]
    [CommRing B] [Algebra ℂ B] (f : A →ₐ[ℂ] B) (u : A →ₐ[ℂ] A) (v : B →ₐ[ℂ] B)
    {X : Scheme.{0}} (j : Spec (CommRingCat.of A) ⟶ X) [Mono j] (g : X ⟶ X)
    (hj : j ≫ g = Spec.map (CommRingCat.ofHom u.toRingHom) ≫ j)
    (he : (Spec.map (CommRingCat.ofHom f.toRingHom) ≫ j) ≫ g =
      Spec.map (CommRingCat.ofHom v.toRingHom) ≫ Spec.map (CommRingCat.ofHom f.toRingHom) ≫ j)
    (a : A) : v (f a) = f (u a) := by
  let F := CommRingCat.ofHom f.toRingHom
  let U := CommRingCat.ofHom u.toRingHom
  let V := CommRingCat.ofHom v.toRingHom
  have hs : Spec.map V ≫ Spec.map F = Spec.map F ≫ Spec.map U :=
    (cancel_mono j).mp (by simpa only [Category.assoc, hj] using he.symm)
  have h : F ≫ V = U ≫ F := Spec.map_inj.mp (by simpa only [Spec.map_comp] using hs)
  exact ConcreteCategory.congr_hom h a

/-- The same overlap pullback also commutes with the restriction from the
target chart, as both affine squares are restrictions of the same scheme map. -/
theorem overlapAction_target_of_chart (i : Fin 4) (k : Fin 3)
    (hc : ∀ l, chartInclusion l ≫ (threefoldAction z hz).hom =
      Spec.map (CommRingCat.ofHom (chartAction z hz l).toRingHom) ≫ chartInclusion l)
    (a : T (i.succAbove k)) :
    overlapAction z hz i k (fixedTargetMap i k a) =
      fixedTargetMap i k (chartAction z hz (i.succAbove k) a) := by
  have he := overlapIso_equivariant_of_chart z hz i k (hc i)
  rw [← Category.assoc, overlapIso_hom_ι_target] at he
  exact target_action_of_spec_square (fixedTargetMap i k) (chartAction z hz (i.succAbove k))
    (overlapAction z hz i k) (chartInclusion _) (threefoldAction z hz).hom (hc _) he a

end CycleQ2LiteralThreefoldOrbitHodgePullback
end

#print axioms CycleQ2LiteralThreefoldOrbitHodgePullback.overlapAction_source
#print axioms CycleQ2LiteralThreefoldOrbitHodgePullback.overlapIso_equivariant_of_chart
