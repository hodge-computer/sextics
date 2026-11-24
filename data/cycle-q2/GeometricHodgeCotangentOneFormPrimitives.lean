import Proposal.GeometricHodgeZeroTwistScalars
import Proposal.GeometricFiniteCechOneBoundaryLifts
import Proposal.GeometricHodgeCotangentEulerCech

/-!
# Actual one-form primitives modulo the canonical hyperplane cocycle

Every closed intrinsic one-form cochain on the original four weight-one
opens of the fixed fiber differs from a canonically constant multiple of
the hyperplane logarithmic cocycle by the boundary of actual one-form
sections on those same opens. No new cohomology premise is assumed.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2HodgeCotangentOneFormPrimitives
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open CycleQ2GeometricHodgeThreefold CycleQ2GeometricHodgeThreefoldIncidence
open CycleQ2HodgeTwistRatios (U)
open CycleQ2HodgeCotangentAtlasForms (Cotangent complexOn)
open CycleQ2HodgeCotangentEulerCohomology (Add)
open CycleQ2HodgeCotangentEulerDlog (logarithmic)
open CycleQ2HodgeCotangentEulerCech
open CycleQ2InjectiveCech (AbSheaf Sections)
open CycleQ2GenericSexticGradient (CoeffRing)
open CycleQ2FiniteInjectiveCech (One IsOneCocycle edgeValue)
open CycleQ2FiniteCechHOne (cechOneClass)
open CycleQ2FiniteCechDescent (Zero)
open CycleQ2GeometricSheafLocalIso (res)
open CycleQ2GeometricAffineChartSections (schemeCoefficient)
open CycleQ2GeometricDifferentialSheaf (coefficientOn)
open CycleQ2GeometricSectionDifferentials (toSheaf)
attribute [local instance] complexOn
local instance (X : TopCat.{0}) : HasExt.{1} (AbSheaf X) := HasExt.standard _
local instance (X : TopCat.{0}) : HasExt.{1} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}) :=
  HasExt.standard _
local instance : HasExt.{1} (TopCat.Sheaf AddCommGrpCat.{0} (threefold literalEval)) :=
  HasExt.standard _

abbrev Forms := Add literalEval (Cotangent literalEval)
abbrev cover := U literalEval

def scaledLog (φ : CoeffRing →+* ℂ) (i k : Fin 4) (W : (threefold φ).Opens)
    (hi : W ≤ U φ i) (hk : W ≤ U φ k) (a : Γ(threefold φ,W)) :
    Sections (Add φ (Cotangent φ)) W :=
  toSheaf (threefold φ).sheaf (schemeCoefficient (toBase φ)) W
    (a • logarithmic φ i k W hi hk)

def scalarLog (φ : CoeffRing →+* ℂ) (c : ℂ) (i k : Fin 4) (W : (threefold φ).Opens)
    (hi : W ≤ U φ i) (hk : W ≤ U φ k) : Sections (Add φ (Cotangent φ)) W :=
  scaledLog φ i k W hi hk (coefficientOn (threefold φ).sheaf (schemeCoefficient (toBase φ)) W c)

/-- The scalar is the canonical structure-map constant, and the primitive
uses actual sections on the same four original opens. -/
theorem one_primitive (u : One Forms cover) (hu : IsOneCocycle Forms cover u) :
    ∃ c : ℂ, ∃ p : Zero Forms cover,
      ∀ (i k : Fin 4) (W : (threefold literalEval).Opens) (hi : W ≤ cover i) (hk : W ≤ cover k),
        res Forms hk (p k) - res Forms hi (p i) = edgeValue Forms cover u i k W hi hk -
          scalarLog literalEval c i k W hi hk := by
  obtain ⟨s,hs⟩ := literal_cotangentCocycle_surjective
    (cechOneClass cover (coordinateOpens_cover literalEval literal_vertex_unit) u hu)
  obtain ⟨c,hc⟩ := CycleQ2HodgeZeroTwistScalars.exists_canonical_scalar literalEval literal_vertex_unit s
  obtain ⟨p,hp⟩ := CycleQ2FiniteCechOneBoundaryLifts.difference_primitive cover
    (coordinateOpens_cover literalEval literal_vertex_unit) u
    (cotangentCocycle literalEval literal_vertex_unit s) hu
    (cotangentCocycle_closed literalEval literal_vertex_unit s) hs.symm
  refine ⟨c,p,fun i k W hi hk => ?_⟩
  have he := hp i k W hi hk
  rw [cotangentCocycle_value literalEval literal_vertex_unit s i k W hi hk,hc i W hi] at he
  exact he

end CycleQ2HodgeCotangentOneFormPrimitives
end
#print axioms CycleQ2HodgeCotangentOneFormPrimitives.one_primitive
