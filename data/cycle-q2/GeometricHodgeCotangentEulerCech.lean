import Proposal.GeometricHodgeCotangentEulerDlog
import Proposal.GeometricHodgeCotangentCohomology
import Proposal.GeometricAutomorphismCohomology

/-!
# The Euler connecting class is represented by actual hyperplane dlog edges

The local Euler lifts restrict in the original sheaves. Their differences
are a genuine one-cocycle in the Euler kernel, representing the actual
connecting class. Applying the global cotangent morphism gives the
ordinary scalar-times-dlog formula on every common subopen, and the
same derived class in intrinsic cotangent cohomology.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2HodgeCotangentEulerCech
open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace CategoryTheory.Abelian
open CycleQ2GeometricHodgeThreefold CycleQ2GeometricHodgeThreefoldIncidence
open CycleQ2GenericSexticGradient (CoeffRing)
open CycleQ2HodgeThreefoldTwist CycleQ2HodgeTwistRatios
open CycleQ2HodgeCotangentEulerSheaf (ambient raw eulerMap)
open CycleQ2HodgeCotangentAtlasForms (complexOn Cotangent)
open CycleQ2HodgeCotangentEulerDlog (lift lift_euler lift_restrict edge edge_ι edge_restrict logarithmic)
open CycleQ2HodgeCotangentGlobalMap (toCotangent)
open CycleQ2HodgeCotangentEulerCohomology (Add H addEuler addEuler_shortExact connecting)
open CycleQ2SeedSectionSheafLimits (sectionKernelEquiv sectionKernelEquiv_val)
open CycleQ2SeedSectionSheafLocal (moduleRes moduleRes_comp moduleRes_app)
open CycleQ2InjectiveCech (AbSheaf Sections freeOpen freeOpenSections)
open CycleQ2FiniteInjectiveCech (One IsOneCocycle)
open CycleQ2FiniteCechDescent (mapOne mapOne_closed edgeValue_mapOne)
open CycleQ2FiniteCechHOne (cechOneClass cechOneClass_naturality)
open CycleQ2CechTwoToDerived (sectionExtZero)
open CycleQ2GeometricAffineChartSections (schemeCoefficient)
open CycleQ2GeometricSectionDifferentials (toSheaf)
attribute [local instance] complexOn
local instance (X : TopCat.{0}) : HasExt.{1} (AbSheaf X) := HasExt.standard _
local instance (X : TopCat.{0}) : HasExt.{1} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}) :=
  HasExt.standard _
local instance (Y : Scheme.{0}) : HasExt.{1} (Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{0}) :=
  HasExt.standard _
variable (φ : CoeffRing →+* ℂ)

def cocycle (s : Γ(twist φ 0,⊤)) : One (Add φ (ambient φ)) (U φ) := fun i k =>
  edge φ i k (U φ i ⊓ U φ k) inf_le_left inf_le_right (moduleRes (twist φ 0) le_top s)

theorem cocycle_value (s : Γ(twist φ 0,⊤)) (i k : Fin 4) (W : (threefold φ).Opens)
    (hi : W ≤ U φ i) (hk : W ≤ U φ k) :
    moduleRes (ambient φ) (le_inf hi hk) (cocycle φ s i k) =
      edge φ i k W hi hk (moduleRes (twist φ 0) le_top s) := by
  rw [cocycle,edge_restrict,moduleRes_comp]

theorem cocycle_closed (s : Γ(twist φ 0,⊤)) : IsOneCocycle (Add φ (ambient φ)) (U φ) (cocycle φ s) := by
  intro i j k W hi hj hk
  change moduleRes (ambient φ) (le_inf hi hk) (cocycle φ s i k) =
    moduleRes (ambient φ) (le_inf hi hj) (cocycle φ s i j) +
      moduleRes (ambient φ) (le_inf hj hk) (cocycle φ s j k)
  rw [cocycle_value φ s i k W hi hk,cocycle_value φ s i j W hi hj,cocycle_value φ s j k W hj hk]
  apply (sectionKernelEquiv (eulerMap φ) W).injective
  apply Subtype.ext
  rw [sectionKernelEquiv_val,sectionKernelEquiv_val,map_add,edge_ι,edge_ι,edge_ι]
  abel

def lifts (s : Γ(twist φ 0,⊤)) : CycleQ2FiniteCechDescent.Zero (Add φ (raw φ)) (U φ) :=
  fun i => lift φ i (U φ i) le_rfl (moduleRes (twist φ 0) le_top s)

private theorem section_zero {X : TopCat.{0}} {F : AbSheaf X} (V : Opens X) (s : Sections F V) :
    sectionExtZero V s = (CycleQ2GeometricConeCech.HZero.sectionsEquiv F V).symm s := by
  apply (CycleQ2GeometricConeCech.HZero.sectionsEquiv F V).injective
  rw [AddEquiv.apply_symm_apply,sectionExtZero,CycleQ2GeometricConeCech.HZero.sectionsEquiv_mk₀]
  exact (freeOpenSections F V).apply_symm_apply s

theorem cocycle_class (h : IsUnit (φ vertexCoefficient)) (s : Γ(twist φ 0,⊤)) :
    cechOneClass (U φ) (coordinateOpens_cover φ h) (cocycle φ s) (cocycle_closed φ s) = connecting φ h s := by
  have he := CycleQ2AutomorphismCohomology.cechOneClass_of_lifts (U φ) (coordinateOpens_cover φ h)
    (addEuler_shortExact φ h) (cocycle φ s) (cocycle_closed φ s) (lifts φ s) s (by
      intro i j W hi hj
      change moduleRes (raw φ) hj (lifts φ s j) - moduleRes (raw φ) hi (lifts φ s i) =
        (kernel.ι (eulerMap φ)).app W (moduleRes (ambient φ) (le_inf hi hj) (cocycle φ s i j))
      rw [cocycle_value φ s i j W hi hj,
        edge_ι φ i j W hi hj (moduleRes (twist φ 0) le_top s)]
      change moduleRes (raw φ) hj (lift φ j (U φ j) le_rfl (moduleRes (twist φ 0) le_top s)) -
        moduleRes (raw φ) hi (lift φ i (U φ i) le_rfl (moduleRes (twist φ 0) le_top s)) = _
      rw [lift_restrict,lift_restrict,moduleRes_comp,moduleRes_comp]) (by
      funext i
      change moduleRes (twist φ 0) le_top s = (eulerMap φ).app (U φ i) (lifts φ s i)
      rw [lifts,lift_euler])
  rw [section_zero] at he
  exact he

def cotangentCocycle (h : IsUnit (φ vertexCoefficient)) (s : Γ(twist φ 0,⊤)) :
    One (Add φ (Cotangent φ)) (U φ) :=
  mapOne (U φ) ((SheafOfModules.toSheaf (threefold φ).ringCatSheaf).map (toCotangent φ h)) (cocycle φ s)

theorem cotangentCocycle_closed (h : IsUnit (φ vertexCoefficient)) (s : Γ(twist φ 0,⊤)) :
    IsOneCocycle (Add φ (Cotangent φ)) (U φ) (cotangentCocycle φ h s) :=
  mapOne_closed (U φ) _ _ (cocycle_closed φ s)

/-- On every common subopen these are the actual hyperplane logarithmic edges. -/
theorem cotangentCocycle_value (h : IsUnit (φ vertexCoefficient)) (s : Γ(twist φ 0,⊤))
    (i k : Fin 4) (W : (threefold φ).Opens) (hi : W ≤ U φ i) (hk : W ≤ U φ k) :
    CycleQ2FiniteInjectiveCech.edgeValue (Add φ (Cotangent φ)) (U φ) (cotangentCocycle φ h s) i k W hi hk =
      toSheaf (threefold φ).sheaf (schemeCoefficient (toBase φ)) W
        (chartFrame φ 0 i W hi (moduleRes (twist φ 0) le_top s) • logarithmic φ i k W hi hk) := by
  rw [cotangentCocycle,edgeValue_mapOne]
  change (toCotangent φ h).app W (moduleRes (ambient φ) (le_inf hi hk) (cocycle φ s i k)) = _
  rw [cocycle_value φ s i k W hi hk,CycleQ2HodgeCotangentEulerDlog.globalMap_edge]

/-- The derived class is precisely the image of the original Euler boundary. -/
theorem cotangentCocycle_class (h : IsUnit (φ vertexCoefficient)) (s : Γ(twist φ 0,⊤)) :
    cechOneClass (U φ) (coordinateOpens_cover φ h) (cotangentCocycle φ h s) (cotangentCocycle_closed φ h s) =
      (connecting φ h s).comp (Ext.mk₀ ((SheafOfModules.toSheaf (threefold φ).ringCatSheaf).map
        (toCotangent φ h))) (add_zero 1) := by
  rw [← cocycle_class φ h s]
  exact (cechOneClass_naturality (U φ) (coordinateOpens_cover φ h) _ (cocycle φ s) (cocycle_closed φ s)).symm

/-- Every intrinsic degree-one class on the original fixed fiber has one
of the actual logarithmic representatives displayed above. -/
theorem literal_cotangentCocycle_surjective (c : H literalEval (Cotangent literalEval) 1) :
    ∃ s : Γ(twist literalEval 0,⊤),
      cechOneClass (U literalEval) (coordinateOpens_cover literalEval literal_vertex_unit)
        (cotangentCocycle literalEval literal_vertex_unit s)
        (cotangentCocycle_closed literalEval literal_vertex_unit s) = c := by
  obtain ⟨s,hs⟩ := CycleQ2HodgeCotangentCohomology.eulerToCotangent_surjective c
  exact ⟨s,(cotangentCocycle_class literalEval literal_vertex_unit s).trans hs⟩

end CycleQ2HodgeCotangentEulerCech
end
#print axioms CycleQ2HodgeCotangentEulerCech.cocycle_class
#print axioms CycleQ2HodgeCotangentEulerCech.cotangentCocycle_value
#print axioms CycleQ2HodgeCotangentEulerCech.cotangentCocycle_class

#print axioms CycleQ2HodgeCotangentEulerCech.literal_cotangentCocycle_surjective
