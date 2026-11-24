import Proposal.GeometricLiteralThreefoldOneFormPrimitives
import Proposal.GeometricLiteralThreefoldFunctionPrimitives
import Proposal.GeometricLiteralNonzeroSweptRestriction

/-!
# Erasing the two lower components of a hypothetical total boundary

The three lower equations of a hypothetical degree-two de Rham Cech
primitive force its two-form edge class to vanish in actual H-one of
two-forms. The function component is removed by an actual function
primitive, and the closed one-form component by the original-cover
one-form theorem. Consequently these equations cannot hold for the
original nonzero ambient test cocycle. A realization in the full total
complex and the unfiltered comparison remain separate steps.

Prepared for fqlx with OpenAI ChatGPT assistance; see solution.md.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 3000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2LiteralThreefoldLowerBoundaryObstruction
open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open CycleQ2LiteralThreefoldFirstDifferential
open CycleQ2LiteralAmbientCharts (fixedOpen fixedOpen_cover)
open CycleQ2FiniteInjectiveCech (IsOneCocycle edgeValue boundaryValue)
open CycleQ2FiniteCechDescent (Zero mapOne edgeValue_mapOne boundaryValue_mapOne)
open CycleQ2FourToFiniteCech (extendOne edgeValue_extendOne edgeAt faceAt boundaryValue_extendOne)
open CycleQ2GeometricSheafLocalIso (res)
open CycleQ2CechTwoToDerived (app app_comp)
open CycleQ2FiniteCechHOne (cechOneClass cechOneClass_eq_zero_of_primitive)
open CycleQ2LiteralThreefoldHodgeCech (hodgeCocycle)
open CycleQ2LiteralThreefoldTestClass (face ambientTestClass)
open CycleQ2LiteralThreefoldTestEdges (nativeEdge)

local instance (Y : TopCat.{0}) : HasExt.{1} (CycleQ2InjectiveCech.AbSheaf Y) := HasExt.standard _

abbrev Functions := CycleQ2LiteralThreefoldFunctionPrimitives.O
abbrev OneEdges := CycleQ2FiniteInjectiveCech.One One fixedOpen
abbrev TwoEdges := CycleQ2FiniteInjectiveCech.One Two fixedOpen
abbrev FunctionEdges := CycleQ2CechTwoToDerived.One Functions fixedOpen
abbrev FunctionFaces := CycleQ2CechTwoToDerived.Two Functions fixedOpen

/-- Actual lower equations on the original cover, with the standard total
signs. No vertex three-form equation is required for this obstruction. -/
structure LowerBoundary (η : TwoEdges) where
  vertices : Zero Two fixedOpen
  edges : OneEdges
  faces : FunctionFaces
  functions_closed : CycleQ2CechTwoToDerived.d2 Functions fixedOpen faces = 0
  one_equation : ∀ i j k W (hi : W ≤ fixedOpen i) (hj : W ≤ fixedOpen j) (hk : W ≤ fixedOpen k),
    boundaryValue One fixedOpen edges i j k W hi hj hk +
      app functionDifferential W (faceAt fixedOpen faces i j k W hi hj hk) = 0
  two_equation : ∀ i k W (hi : W ≤ fixedOpen i) (hk : W ≤ fixedOpen k),
    res Two hk (vertices k) - res Two hi (vertices i) -
      app differential W (edgeValue One fixedOpen edges i k W hi hk) =
        edgeValue Two fixedOpen η i k W hi hk

theorem exact_differential_zero (W : X.Opens) (a : Functions.obj.obj (op W)) :
    app differential W (app functionDifferential W a) = 0 := by
  rw [app_comp,function_differential_zero]
  rfl

/-- The lower equations alone force the actual derived two-form class to
be zero. Both eliminations retain the original sections and cover. -/
theorem class_zero_of_lower_boundary (η : TwoEdges) (hη : IsOneCocycle Two fixedOpen η)
    (b : LowerBoundary η) : cechOneClass fixedOpen fixedOpen_cover η hη = 0 := by
  obtain ⟨g,hg⟩ := CycleQ2LiteralThreefoldFunctionPrimitives.two_primitive b.faces b.functions_closed
  let correction := mapOne fixedOpen functionDifferential (extendOne fixedOpen g)
  let corrected := b.edges + correction
  have hc : IsOneCocycle One fixedOpen corrected := by
    intro i j k W hi hj hk
    have hb := b.one_equation i j k W hi hj hk
    have he : boundaryValue One fixedOpen correction i j k W hi hj hk =
        app functionDifferential W (faceAt fixedOpen b.faces i j k W hi hj hk) := by
      change boundaryValue One fixedOpen (mapOne fixedOpen functionDifferential (extendOne fixedOpen g)) _ _ _ _ _ _ _ = _
      rw [boundaryValue_mapOne,boundaryValue_extendOne,hg]
    change res One (le_inf hi hk) (b.edges i k + correction i k) =
      res One (le_inf hi hj) (b.edges i j + correction i j) +
        res One (le_inf hj hk) (b.edges j k + correction j k)
    simp only [map_add]
    unfold boundaryValue edgeValue at hb he
    linear_combination (norm := abel) -hb - he
  have he (i k : Fin 4) (W : X.Opens) (hi : W ≤ fixedOpen i) (hk : W ≤ fixedOpen k) :
      app differential W (edgeValue One fixedOpen corrected i k W hi hk) =
        app differential W (edgeValue One fixedOpen b.edges i k W hi hk) := by
    have hs : edgeValue One fixedOpen corrected i k W hi hk =
        edgeValue One fixedOpen b.edges i k W hi hk +
          app functionDifferential W (edgeAt fixedOpen g i k W hi hk) := by
      change res One (le_inf hi hk) (b.edges i k + correction i k) = _
      rw [map_add]
      congr 1
      exact (edgeValue_mapOne fixedOpen functionDifferential (extendOne fixedOpen g) i k W hi hk).trans
        (congrArg (app functionDifferential W) (edgeValue_extendOne fixedOpen g i k W hi hk))
    rw [hs,map_add,exact_differential_zero,add_zero]
  obtain ⟨q,hq⟩ := CycleQ2LiteralThreefoldOneFormPrimitives.differential_primitive corrected hc
  apply cechOneClass_eq_zero_of_primitive fixedOpen fixedOpen_cover η hη
    (fun i => b.vertices i - q i)
  intro i k W hi hk
  calc
    res Two hk (b.vertices k - q k) - res Two hi (b.vertices i - q i) =
        (res Two hk (b.vertices k) - res Two hi (b.vertices i)) -
          (res Two hk (q k) - res Two hi (q i)) := by
            simp only [map_sub]
            abel
    _ = edgeValue Two fixedOpen η i k W hi hk := by
      rw [hq i k W hi hk]
      change _ - app differential W (edgeValue One fixedOpen corrected i k W hi hk) = _
      rw [he]
      exact b.two_equation i k W hi hk

/-- The actual original ambient test admits none of the three lower total
boundary equations, including arbitrary function and one-form components. -/
theorem ambient_test_no_lower_boundary :
    ¬ Nonempty (LowerBoundary (hodgeCocycle nativeEdge face).val) := by
  rintro ⟨b⟩
  apply CycleQ2LiteralNonzeroSweptRestriction.ambient_nonzero
  exact class_zero_of_lower_boundary _
    (fun i j k W hi hj hk => ((hodgeCocycle nativeEdge face).condition i j k W hi hj hk).symm) b

end CycleQ2LiteralThreefoldLowerBoundaryObstruction
end
#print axioms CycleQ2LiteralThreefoldLowerBoundaryObstruction.class_zero_of_lower_boundary
#print axioms CycleQ2LiteralThreefoldLowerBoundaryObstruction.ambient_test_no_lower_boundary
