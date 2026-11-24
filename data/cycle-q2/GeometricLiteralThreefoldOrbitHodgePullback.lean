import Proposal.GeometricLiteralThreefoldOrbitHodgePullbackForms
import Proposal.GeometricAutomorphismCohomology
import Proposal.GeometricFiniteCechHOneRefinement

/-!
# Action on the four-chart Hodge cocycle of the fixed threefold

The automorphism acts by the exterior square of its scheme differential.
The derived pullback is evaluated on the four original affine charts by
restricting the true inverse-image cocycle to these charts.

Prepared for fqlx with OpenAI ChatGPT assistance; see solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace CycleQ2LiteralThreefoldOrbitHodgePullback
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace CycleQ2GeometricDifferentialSheaf
  CycleQ2InjectiveCech CycleQ2GeometricSheafLocalIso CycleQ2FiniteInjectiveCech
  CycleQ2AutomorphismCohomology CycleQ2FiniteCechOrbitPullback CycleQ2FiniteCechHOne
  CycleQ2FiniteCechRefinement CycleQ2GeometricAffineChartSections
  CycleQ2LiteralThreefoldHodgeCech CycleQ2LiteralAmbientCharts
  CycleQ2GeometricSectionDifferentials CycleQ2ExteriorSectionNaturality

local instance : HasExt.{1} (AbSheaf (show TopCat from Threefold)) := HasExt.standard _

variable (e : Threefold ≅ Threefold) (hbase : e.hom ≫ structureMap = structureMap)
  (hU : ∀ i, fixedOpen i ≤ e.hom ⁻¹ᵁ fixedOpen i)

include hbase in
theorem compatible (U : Threefold.Opens) (c : ℂ) :
    e.hom.app U (coefficientOn Threefold.sheaf coefficients U c) =
      coefficientOn Threefold.sheaf coefficients (e.hom ⁻¹ᵁ U) c := by
  rw [coefficientOn_app, hbase]

def hodgeAdd : HodgeSheaf ⟶ push e.hom.base HodgeSheaf :=
  formsAdd e.hom coefficients coefficients (compatible e hbase) 2

def hodgePull : Hodge21 →+ Hodge21 :=
  pullH (B := HodgeSheaf) (D := HodgeSheaf) (Scheme.forgetToTop.mapIso e) (hodgeAdd e hbase) 1

variable (ω : NativeEdges) (hω : ∀ (i j k : Fin 4) (hij : i < j) (hjk : j < k), Face ω i j k hij hjk)

private theorem closedCocycle : IsOneCocycle HodgeSheaf fixedOpen (hodgeCocycle ω hω).val :=
  fun i j k W hi hj hk => ((hodgeCocycle ω hω).condition i j k W hi hj hk).symm

def actedCocycle : One HodgeSheaf fixedOpen :=
  restrictOne (cover e.hom.base fixedOpen) fixedOpen id hU
    (pullOne e.hom.base (hodgeAdd e hbase) fixedOpen (hodgeCocycle ω hω).val)

theorem actedCocycle_closed : IsOneCocycle HodgeSheaf fixedOpen (actedCocycle e hbase hU ω hω) :=
  restrictOne_closed (cover e.hom.base fixedOpen) fixedOpen id hU _
    (pullOne_closed e.hom.base (hodgeAdd e hbase) fixedOpen _ (closedCocycle ω hω))

theorem hodgePull_class :
    hodgePull e hbase (hodgeClass ω hω) =
      cechOneClass fixedOpen fixedOpen_cover (actedCocycle e hbase hU ω hω)
        (actedCocycle_closed e hbase hU ω hω) :=
  (pullH_cechOneClass (Scheme.forgetToTop.mapIso e) fixedOpen fixedOpen_cover
    (cover_top e.hom.base fixedOpen fixedOpen_cover) (hodgeAdd e hbase) _
    (closedCocycle ω hω)).trans
      (cechOneClass_refinement (cover e.hom.base fixedOpen) fixedOpen id hU
        (cover_top e.hom.base fixedOpen fixedOpen_cover) fixedOpen_cover _
        (pullOne_closed e.hom.base (hodgeAdd e hbase) fixedOpen _ (closedCocycle ω hω))).symm

theorem actedCocycle_edgeValue (i j : Fin 4)
    (W : Threefold.Opens) (hi : W ≤ fixedOpen i) (hj : W ≤ fixedOpen j) :
    edgeValue HodgeSheaf fixedOpen (actedCocycle e hbase hU ω hω) i j W hi hj =
    pullTo (F := HodgeSheaf) (G := HodgeSheaf) e.hom.base (hodgeAdd e hbase)
      (show W ≤ e.hom ⁻¹ᵁ (fixedOpen i ⊓ fixedOpen j) from le_inf (hi.trans (hU i)) (hj.trans (hU j)))
      (edgeValue HodgeSheaf fixedOpen (hodgeCocycle ω hω).val i j _ inf_le_left inf_le_right) := by
  unfold actedCocycle
  rw [edgeValue_restrictOne]
  exact edgeValue_pullOne e.hom.base (hodgeAdd e hbase) fixedOpen (hodgeCocycle ω hω).val
    i j (show W ≤ e.hom ⁻¹ᵁ (fixedOpen i ⊓ fixedOpen j) from le_inf (hi.trans (hU i)) (hj.trans (hU j)))
      inf_le_left inf_le_right

end CycleQ2LiteralThreefoldOrbitHodgePullback
end

#print axioms CycleQ2LiteralThreefoldOrbitHodgePullback.hodgePull_class
#print axioms CycleQ2LiteralThreefoldOrbitHodgePullback.actedCocycle_edgeValue
