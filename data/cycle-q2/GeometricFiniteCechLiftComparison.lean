import Proposal.GeometricFiniteCechConnecting
import Proposal.GeometricFiniteCechTwoNaturality

/-!
# Comparison of lifted connecting classes on a finite cover

The boundary of a chosen edge lift can be compared to the boundary of
a second lift before normalizing their two-cochains. Both lifts give
descent data for the same two-cochain after transport along the
coefficient morphism. Independence of descent gives the equality in
degree-two cohomology.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace CycleQ2FiniteCechLiftComparison

open CategoryTheory CategoryTheory.Abelian TopologicalSpace
  CycleQ2InjectiveCech CycleQ2FiniteInjectiveCech CycleQ2FiniteCechDescent
  CycleQ2FiniteCechHOne CycleQ2FiniteCechConnecting
open CycleQ2CechTwoToDerived (app)
open CycleQ2CechTwoNaturality (derivedMap)

variable {X : TopCat.{0}} {ι : Type} [Fintype ι] (U : ι → Opens X)
local instance sheafHasExt : HasExt.{1} (AbSheaf X) := HasExt.standard _

/-- Two raw lifted boundaries related by a morphism of coefficient
sheaves give the corresponding equality of actual connecting classes. -/
theorem compare_lifted_boundaries (hcover : (⨆ i, U i) = ⊤)
    {S T : ShortComplex (AbSheaf X)} (hS : S.ShortExact) (hT : T.ShortExact)
    (f : S.X₁ ⟶ T.X₁) (b : One S.X₂ U) (d : One T.X₂ U) (c : Two S.X₁ U)
    (hb : ∀ i j k W hi hj hk, boundaryValue S.X₂ U b i j k W hi hj hk =
      app S.f W (faceValue S.X₁ U c i j k W hi hj hk))
    (hd : ∀ i j k W hi hj hk, boundaryValue T.X₂ U d i j k W hi hj hk =
      app T.f W (faceValue T.X₁ U (mapTwo U f c) i j k W hi hj hk)) :
    derivedMap f ((cechOneClass U hcover (mapOne U S.g b)
        (primitive_image_closed U S c b hb)).comp hS.extClass rfl) =
      (cechOneClass U hcover (mapOne U T.g d)
        (primitive_image_closed U T (mapTwo U f c) d hd)).comp hT.extClass rfl := by
  obtain ⟨p, hp⟩ := exists_descent_of_lift U hS hcover b c hb
  obtain ⟨q, hq⟩ := exists_descent_of_lift U hT hcover d (mapTwo U f c) hd
  exact (congrArg (derivedMap f) hp).trans
    ((CycleQ2FiniteCechTwoNaturality.descentClass_naturality U f p).trans
      ((descentClass_independent U hcover _ q).trans hq.symm))

end CycleQ2FiniteCechLiftComparison

end

#print axioms CycleQ2FiniteCechLiftComparison.compare_lifted_boundaries
