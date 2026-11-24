import Proposal.GeometricLiteralMovingDivisorChern
import Proposal.GeometricLiteralMovingDivisorOrbitFrames
import Proposal.GeometricLiteralOrbitChern
import Proposal.GeometricLiteralChernGauge

/-!
# Comparing the orbit cut out by the pivot equations with three Cartier translates

Intersect the pivot cover with the three translated native covers.  On each
intersection equality of generator ideals gives a unit connecting the product
of the three native equations to the pivot equation.  Its logarithmic
differential supplies the Čech coboundary on this common refinement.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralMovingDivisorRefinement

open CategoryTheory AlgebraicGeometry TopologicalSpace
  CycleQ2GeometricSheafLocalIso CycleQ2InjectiveCech CycleQ2FiniteInjectiveCech
  CycleQ2FiniteCechHOne CycleQ2FiniteCechRefinement
  CycleQ2LiteralNativeDifferentialSections CycleQ2LiteralNativeChernCocycle
  CycleQ2SeedSectionSheafGlobal CycleQ2SeedSectionDivisorTransitions
  CycleQ2LiteralMovingDivisorOrbitFrames CycleQ2LiteralMovingDivisorChern
  CycleQ2LiteralOrbitChern

local instance schemeSheavesHasExt (X : Scheme.{0}) :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}) := HasExt.standard _

abbrev CoverIndex := VertexIndex × Index

variable (f g k : Surface ⟶ Surface)

def comparisonCover (i : CoverIndex) : Surface.Opens :=
  pivotCover i.1 ⊓ commonCover f g k i.2

theorem comparisonCover_top : (⨆ i, comparisonCover f g k i) = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨a, ha⟩ := Opens.mem_iSup.mp
    (show x ∈ ⨆ a, pivotCover a by rw [pivotCover_covers]; trivial)
  obtain ⟨b, hb⟩ := Opens.mem_iSup.mp
    (show x ∈ ⨆ b, commonCover f g k b by rw [commonCover_top]; trivial)
  exact Opens.mem_iSup.mpr ⟨(a,b), ha,hb⟩

private abbrev pivotFrame (i : CoverIndex) :=
  frameAt i.1 (comparisonCover f g k i) inf_le_left

private abbrev productEquation (i : CoverIndex) :=
  productGenerator f g k i.2 (comparisonCover f g k i) inf_le_right

private abbrev orbitRefined := restrictOne pivotCover (comparisonCover f g k)
  Prod.fst (fun _ => inf_le_left) (logOne orbitSystem)

private abbrev productRefined := restrictOne (commonCover f g k) (comparisonCover f g k)
  Prod.snd (fun _ => inf_le_right) (productOne f g k)

private def pivotUnits : CycleQ2LiteralChernGauge.EdgeUnits (comparisonCover f g k) :=
  fun i j => orbitSystem.value
    (frameAt i.1 _ (inf_le_left.trans inf_le_left))
    (frameAt j.1 _ (inf_le_right.trans inf_le_left))

private def productUnits : CycleQ2LiteralChernGauge.EdgeUnits (comparisonCover f g k) :=
  fun i j => productUnit f g k i.2 j.2 _
    (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)

private theorem orbitRefined_eq :
    orbitRefined f g k = CycleQ2LiteralChernGauge.logOne _ (pivotUnits f g k) := by
  funext i j
  exact logOne_common orbitSystem i.1 j.1 _
    (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left)

private theorem productRefined_eq :
    productRefined f g k = CycleQ2LiteralChernGauge.logOne _ (productUnits f g k) := by
  funext i j
  change DifferentialSheaf.val.map _ (sheafLogDifferential _ (productUnit _ _ _ _ _ _ _ _)) = _
  rw [sheafLogDifferential_restrict, productUnit_restrict]
  rfl

private theorem gauge_of_equations {R : Type*} [CommRing R] (u v p q : Rˣ) (a b : R)
    (ha : Function.Injective (fun r : R => r * a))
    (hab : b = (v : R) * a) (hu : (u : R) * ((q : R) * b) = (p : R) * a) :
    u * q = p * v⁻¹ := by
  apply mul_right_cancel (b := v)
  rw [mul_assoc p, inv_mul_cancel, mul_one]
  apply Units.ext
  apply ha
  change ((u : R) * ↑q * ↑v) * a = ↑p * a
  rw [hab, ← mul_assoc, ← mul_assoc] at hu
  exact hu

/-- Equality of the actual section ideals on the common cover suffices to identify
the pivot Chern class with the product of the three translated native classes. -/
theorem orbitClass_eq_productDerivedClass
    (hspan : ∀ i : CoverIndex,
      Ideal.span {productGenerator f g k i.2 (comparisonCover f g k i) inf_le_right} =
      Ideal.span {pivotEquation (frameAt i.1 (comparisonCover f g k i) inf_le_left)}) :
    orbitClass = productDerivedClass f g k := by
  let U := comparisonCover f g k
  let d (i : CoverIndex) := existsUnique_frameUnit (pivotFrame f g k i)
    (productEquation f g k i) (hspan i)
  let s (i : CoverIndex) : Γ(Surface,U i)ˣ := (d i).exists.choose
  have hs (i : CoverIndex) : productEquation f g k i =
      (s i : Γ(Surface,U i)) * pivotEquation (pivotFrame f g k i) := (d i).exists.choose_spec
  have hW (i : CoverIndex) (W : Surface.Opens) (h : W ≤ U i) :
      productGenerator f g k i.2 W (h.trans inf_le_right) =
        targetRes h (s i : Γ(Surface,U i)) *
          pivotEquation (frameAt i.1 W (h.trans inf_le_left)) := by
    have e := congrArg (targetRes h) (hs i)
    dsimp only [productEquation] at e
    rw [map_mul, pivotEquation_restrict] at e
    exact (productGenerator_restrict f g k i.2 h inf_le_right).symm.trans e
  have gauge (i j : CoverIndex) : productUnits f g k i j *
      restrictSectionUnit (inf_le_right : U i ⊓ U j ≤ U j) (s j) =
      restrictSectionUnit inf_le_left (s i) * pivotUnits f g k i j := by
    let W := U i ⊓ U j
    let a := frameAt i.1 W (inf_le_left.trans inf_le_left)
    let b := frameAt j.1 W (inf_le_right.trans inf_le_left)
    let u : Γ(Surface,W)ˣ := productUnits f g k i j
    let v := orbitTransition a b
    let p : Γ(Surface,W)ˣ := Units.map (targetRes (inf_le_left : W ≤ U i)).toMonoidHom (s i)
    let q : Γ(Surface,W)ˣ := Units.map (targetRes (inf_le_right : W ≤ U j)).toMonoidHom (s j)
    change u * q = p * v⁻¹
    apply gauge_of_equations u v p q (pivotEquation a) (pivotEquation b)
      (pivotEquation_regular a) (orbitTransition_generator a b)
    calc
      _ = ↑u * productGenerator f g k j.2 W (inf_le_right.trans inf_le_right) :=
        congrArg (fun x : Γ(Surface,W) => (u : Γ(Surface,W)) * x) (hW j W inf_le_right).symm
      _ = productGenerator f g k i.2 W (inf_le_left.trans inf_le_right) :=
        productUnit_mul_generator f g k i.2 j.2 W
          (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)
      _ = _ := hW i W inf_le_left
  have ho := restrictOne_closed pivotCover U Prod.fst (fun _ => inf_le_left) _ (logOne_closed orbitSystem)
  have hp := restrictOne_closed (commonCover f g k) U Prod.snd (fun _ => inf_le_right) _ (productOne_closed f g k)
  change IsOneCocycle _ U (orbitRefined f g k) at ho
  change IsOneCocycle _ U (productRefined f g k) at hp
  have eo := cechOneClass_refinement pivotCover U Prod.fst (fun _ => inf_le_left)
    pivotCover_covers (comparisonCover_top f g k) _ (logOne_closed orbitSystem)
  have ep := cechOneClass_refinement (commonCover f g k) U Prod.snd (fun _ => inf_le_right)
    (commonCover_top f g k) (comparisonCover_top f g k) _ (productOne_closed f g k)
  refine eo.symm.trans (Eq.trans ?_ ep)
  change cechOneClass U _ (orbitRefined f g k) ho = cechOneClass U _ (productRefined f g k) hp
  simp only [orbitRefined_eq, productRefined_eq]
  exact (CycleQ2LiteralChernGauge.cechOneClass_eq_of_gauge U (comparisonCover_top f g k)
    (productUnits f g k) (pivotUnits f g k) _ _ s gauge).symm

end CycleQ2LiteralMovingDivisorRefinement

end

#print axioms CycleQ2LiteralMovingDivisorRefinement.orbitClass_eq_productDerivedClass
