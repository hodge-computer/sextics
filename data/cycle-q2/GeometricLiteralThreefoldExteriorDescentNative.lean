import Proposal.GeometricLiteralThreefoldExteriorDescent
import Proposal.GeometricLiteralThreefoldDeformedEdgeDerivative

/-! The ordinary exterior differential on the original charts and their intersections.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2LiteralThreefoldExteriorDescentNative

open CycleQ2LiteralThreefoldExteriorDescent CycleQ2LiteralThreefoldCartan
  CycleQ2LiteralThreefoldDeformedEdgeDerivative CycleQ2LiteralThreefoldDeformedOverlap
  CycleQ2LiteralAbelJacobiContraction CycleQ2LiteralThreefoldResidueFrame
  CycleQ2LiteralThreefoldResidueChartMaps CycleQ2LiteralThreefoldResidueCoordinates
  CycleQ2LiteralThreefoldExteriorDerivative CycleQ2ExteriorSectionNaturality
  CycleQ2LiteralThreefoldTestEdges CycleQ2LiteralThreefoldResidueMinors

private instance chartTwoGroup (i : Fin 4) : AddCommGroup (Forms (T i) 2) := inferInstance
private instance chartThreeGroup (i : Fin 4) : AddCommGroup (Forms (T i) 3) := inferInstance
private instance overlapTwoGroup (i : Fin 4) (k : Fin 3) :
    AddCommGroup (Forms (FixedOverlap i k) 2) := inferInstance
private instance overlapThreeGroup (i : Fin 4) (k : Fin 3) :
    AddCommGroup (Forms (FixedOverlap i k) 3) := inferInstance

private theorem separated_of_cover {A E : Type} [CommRing A] [Algebra ℂ A]
    (B : E → Type) [∀ e, CommRing (B e)] [∀ e, Algebra ℂ (B e)]
    (f : ∀ e, A →ₐ[ℂ] B e) (b : ∀ e, Module.Basis (Fin 3) (B e) (OneForms (B e)))
    (u : ∀ e, Fin 3 → B e) (hu : ∀ e r, b e r = KaehlerDifferential.D ℂ (B e) (u e r))
    (hi : ∀ z t : Forms A 3,
      (∀ e, exteriorDifferentialMap (f e) 3 z = exteriorDifferentialMap (f e) 3 t) → z = t) :
    Separated A := by
  intro z t h
  apply hi z t
  intro e
  have hz := h (B e) (f e) (b e) (u e) (hu e)
  change exteriorDifferentialMap (f e) 3 (z - t) = additive (b e) (exteriorDifferentialMap (f e) 2 0) at hz
  rwa [map_sub, map_zero, map_zero, sub_eq_zero] at hz

theorem chartSeparated (i : Fin 4) : Separated (T i) := by
  intro z t h
  apply chart_restrictions_injective i
  intro a
  let f := IsScalarTower.toAlgHom ℂ (T i) (Patch i a)
  have hz := h (Patch i a) f (basis i a) _ (basis_apply i a)
  change exteriorDifferentialMap f 3 (z - t) = additive (basis i a) (exteriorDifferentialMap f 2 0) at hz
  rwa [map_sub, map_zero, map_zero, sub_eq_zero] at hz

theorem overlapSeparated (i : Fin 4) (k : Fin 3) : Separated (FixedOverlap i k) :=
  separated_of_cover (fun ab : Fin 4 × Fin 4 => Ring i k ab.1 ab.2)
    (fun ab => κ i k ab.1 ab.2) (fun ab => basisOn i k ab.1 ab.2)
    (fun ab r => targetMap i k ab.1 ab.2 (coord (i.succAbove k) (ab.2.succAbove r)))
    (fun ab => basisOn_apply i k ab.1 ab.2)
    (fun z t h => triple_restrictions_injective i k (fun a b => h (a,b)))

/-- The original test edge has the specified exterior derivative on the whole overlap. -/
theorem edge_differential (i : Fin 4) (k : Fin 3) :
    differential (overlapSeparated i k) (nativeEdge i k) = edgeDerivative i k := by
  apply triple_restrictions_injective i k
  intro a b
  exact (differential_represents (overlapSeparated i k) (nativeEdge i k)
    (Ring i k a b) (κ i k a b) (basisOn i k a b) _ (basisOn_apply i k a b)).trans
      (edgeDerivative_restrict i k a b).symm

end CycleQ2LiteralThreefoldExteriorDescentNative
end

#print axioms CycleQ2LiteralThreefoldExteriorDescentNative.edge_differential
