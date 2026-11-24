import Proposal.GeometricHodgeCotangentConormalExact
import Proposal.GeometricHodgeCotangentEulerCohomology
import Proposal.GeometricHodgeTwistConstantSections

/-!
# Global Euler boundaries surject onto intrinsic cotangent H-one

For the actual fixed smooth fiber the conormal sequence is short exact.
Vanishing of H-two of O(-6) makes ambient-kernel H-one surject onto
intrinsic cotangent H-one. Composing with the genuine Euler connecting
map gives a surjective map from global O(0) sections. The previously
checked Laurent calculation identifies its source with the base field.
Identifying its image of one with the hyperplane dlog class is separate.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2HodgeCotangentCohomology
open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace CategoryTheory.Abelian
open CycleQ2GeometricHodgeThreefold CycleQ2GeometricHodgeThreefoldIncidence
open CycleQ2HodgeThreefoldTwist
open CycleQ2HodgeCotangentEulerSheaf (ambient)
open CycleQ2HodgeCotangentAtlasForms (Cotangent)
open CycleQ2HodgeCotangentConormalComplex (conormalSequence)
open CycleQ2HodgeCotangentConormalExact (literal_conormal_shortExact cotangent_additive_epi)
open CycleQ2HodgeCotangentEulerCohomology (Add H connecting connecting_surjective)
open CycleQ2GeometricOpenCoverAdditiveExactness (additiveComplex)
open CycleQ2InjectiveCech (AbSheaf freeOpen)
local instance (X : TopCat.{0}) : HasExt.{1} (AbSheaf X) := HasExt.standard _
local instance (X : TopCat.{0}) : HasExt.{1}
    (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}) := HasExt.standard _
local instance (Y : Scheme.{0}) : HasExt.{1} (Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{0}) :=
  HasExt.standard _

local instance : HasExt.{1} (TopCat.Sheaf AddCommGrpCat.{0} (threefold literalEval)) :=
  HasExt.standard _

abbrev addConormal := additiveComplex (conormalSequence literalEval literal_vertex_unit)

theorem addConormal_shortExact : addConormal.ShortExact := by
  let F := SheafOfModules.toSheaf.{0} (threefold literalEval).ringCatSheaf
  letI : F.PreservesZeroMorphisms :=
    CycleQ2GeometricSheafLocalExactness.moduleSheaf_toSheaf_preservesZeroMorphisms
      (X := (threefold literalEval : TopCat)) (threefold literalEval).ringCatSheaf
  letI : PreservesFiniteLimits F := inferInstanceAs
    (PreservesFiniteLimits (SheafOfModules.toSheaf.{0} (threefold literalEval).ringCatSheaf))
  let hs := literal_conormal_shortExact
  letI := hs.mono_f
  have he := hs.exact.map_of_mono_of_preservesKernel F hs.mono_f inferInstance
  refine { exact := he, mono_f := ?_, epi_g := ?_ }
  · change Mono (F.map (conormalSequence literalEval literal_vertex_unit).f)
    infer_instance
  · exact cotangent_additive_epi literalEval literal_vertex_unit

theorem conormal_hTwo : Subsingleton (H literalEval (twist literalEval (-6)) 2) := by
  letI := (CycleQ2HodgeTwistTorusChart.ordinary_vanishing literalEval literal_vertex_unit (-6)).2
  exact (CycleQ2GeometricSheafCohomologyRestriction.terminalCohomologyEquiv _
    (Add literalEval (twist literalEval (-6))) ⊤ isTerminalTop 2).injective.subsingleton

/-- The cohomology map is induced by the original global cotangent morphism. -/
def ambientToCotangent : H literalEval (ambient literalEval) 1 →+
    H literalEval (Cotangent literalEval) 1 :=
  (Ext.mk₀ addConormal.g : Ext.{1} addConormal.X₂ addConormal.X₃ 0).postcomp (freeOpen (⊤ : (threefold literalEval).Opens)) (add_zero 1)

theorem ambientToCotangent_surjective : Function.Surjective ambientToCotangent := by
  intro c
  have hz := conormal_hTwo
  obtain ⟨b,hb⟩ := Ext.covariant_sequence_exact₃ (freeOpen (⊤ : (threefold literalEval).Opens))
    addConormal_shortExact c (n₁ := 2) rfl (hz.elim _ _)
  exact ⟨b,hb⟩

/-- Every intrinsic cotangent H-one class is the image of an actual Euler boundary. -/
def eulerToCotangent : Γ(twist literalEval 0,⊤) →+ H literalEval (Cotangent literalEval) 1 :=
  ambientToCotangent.comp (connecting literalEval literal_vertex_unit)

theorem eulerToCotangent_surjective : Function.Surjective eulerToCotangent :=
  ambientToCotangent_surjective.comp (connecting_surjective literalEval literal_vertex_unit)

def constants : Γ(twist literalEval 0,⊤) ≃+ ℂ :=
  (CycleQ2HodgeTwistTorusChart.globalSections literalEval literal_vertex_unit 0).trans
    CycleQ2HodgeTwistConstantSections.degreeZeroEquiv

/-- The base-field parametrization includes the checked global-section comparison. -/
def scalarToCotangent : ℂ →+ H literalEval (Cotangent literalEval) 1 :=
  eulerToCotangent.comp constants.symm.toAddMonoidHom

theorem scalarToCotangent_surjective : Function.Surjective scalarToCotangent :=
  eulerToCotangent_surjective.comp constants.symm.surjective

end CycleQ2HodgeCotangentCohomology
end
#print axioms CycleQ2HodgeCotangentCohomology.addConormal_shortExact
#print axioms CycleQ2HodgeCotangentCohomology.ambientToCotangent_surjective
#print axioms CycleQ2HodgeCotangentCohomology.scalarToCotangent_surjective
