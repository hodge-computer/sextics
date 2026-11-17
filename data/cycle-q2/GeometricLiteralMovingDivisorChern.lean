import Proposal.GeometricSeedSectionInvertible
import Proposal.GeometricLiteralNativeChernCocycle
import Proposal.GeometricFiniteCechOneAdditivity

/-!
# The Chern class of the moving curve on the original surface

We read the transition from the ideal of the specialized curve by taking
the coordinate of one equation in another local basis. Dualizing gives
the positive divisor. Its derived Chern class is the sum of the degree-ten
orbit-ideal dual class and the fourth coordinate twist.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralMovingDivisorChern

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
  CycleQ2InjectiveCech CycleQ2GeometricSheafLocalIso CycleQ2FiniteInjectiveCech
  CycleQ2FiniteCechHOne CycleQ2FiniteCechOneAdditivity
  CycleQ2LiteralProjectiveIntersections CycleQ2LiteralNativeGaugeSections
  CycleQ2LiteralNativeChernCocycle
  CycleQ2SeedProjectiveImageChart CycleQ2SeedProjectiveImageCocycle
  CycleQ2SeedSectionSheafGlobal CycleQ2SeedSectionDivisorFrames
  CycleQ2SeedSectionDivisorTransitions CycleQ2SeedSectionInvertible
  CycleQ2SeedSectionAffineInjective

open CycleQ2LiteralNativeDifferentialSections (DifferentialSheaf sheafLogDifferential
  sheafLogDifferential_restrict sheafLogDifferential_mul)

local instance schemeSheavesHasExt (X : Scheme.{0}) :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}) := HasExt.standard _

abbrev VertexIndex := Vertex × (Fin 3 × Fin 3)

def pivotCover (a : VertexIndex) : Surface.Opens := cover a.1 ⊓ pivotOpen a.1.2 a.2

theorem cover_le_patch (v : Vertex) : cover v ≤ Patch v.2 := by
  rw [cover, CycleQ2ProjectiveCartierIdeal.refinedOpen_eq]
  refine inf_le_right.trans ?_
  obtain ⟨i,j⟩ := v
  fin_cases j <;> exact le_rfl

theorem pivotCover_covers : (⨆ a, pivotCover a) = ⊤ := by
  apply top_unique
  intro x _
  have hx : x ∈ ⨆ v, cover v := by rw [cover_covers]; trivial
  obtain ⟨v, hv⟩ := Opens.mem_iSup.mp hx
  have hi := cover_le_patch v hv
  let i := v.2
  let φ : AffineRing i →+* Surface.presheaf.stalk x :=
    (Surface.presheaf.germ (Patch i) x hi).hom.comp (chartSectionMap i (Patch i) le_rfl)
  have hspan := span_map_top (fun p : Fin 3 × Fin 3 =>
    (chartFactorData i).matrix p.1 p.2) (chartFactorData i).entries_generate φ
  obtain ⟨p, hp⟩ := exists_unit_of_span_top _ hspan
  exact Opens.mem_iSup.mpr ⟨(v,p), hv, (Surface.mem_basicOpen _ x hi).mpr hp⟩

def frameAt (a : VertexIndex) (V : Surface.Opens) (h : V ≤ pivotCover a) : FrameData V :=
  (pivotFrameData a.1.2 a.2).restrict (h.trans inf_le_right)

/-- Transition functions evaluated on every common subopen of two local frames. -/
structure FrameSystem where
  value {V : Surface.Opens} : FrameData V → FrameData V → Γ(Surface,V)ˣ
  natural {V W : Surface.Opens} (f g : FrameData V) (h : W ≤ V) :
    Units.map (targetRes h).toMonoidHom (value f g) = value (f.restrict h) (g.restrict h)
  compose {V : Surface.Opens} (f g h : FrameData V) : value f g * value g h = value f h

def logOne (D : FrameSystem) : One differentialAddSheaf pivotCover := fun a b =>
  sheafLogDifferential _ (D.value (frameAt a _ inf_le_left) (frameAt b _ inf_le_right))

theorem logOne_common (D : FrameSystem) (a b : VertexIndex) (V : Surface.Opens)
    (ha : V ≤ pivotCover a) (hb : V ≤ pivotCover b) :
    edgeValue differentialAddSheaf pivotCover (logOne D) a b V ha hb =
      sheafLogDifferential V (D.value (frameAt a V ha) (frameAt b V hb)) := by
  let h := le_inf ha hb
  change DifferentialSheaf.val.map (homOfLE h).op (sheafLogDifferential _
    (D.value (frameAt a _ inf_le_left) (frameAt b _ inf_le_right))) = _
  rw [sheafLogDifferential_restrict]
  change sheafLogDifferential V (Units.map (targetRes h).toMonoidHom _) = _
  rw [D.natural]
  congr 2

theorem logOne_closed (D : FrameSystem) : IsOneCocycle differentialAddSheaf pivotCover (logOne D) := by
  intro a b c V ha hb hc
  change edgeValue _ _ _ a c V ha hc = edgeValue _ _ _ a b V ha hb + edgeValue _ _ _ b c V hb hc
  rw [logOne_common, logOne_common, logOne_common, ← sheafLogDifferential_mul, D.compose]

def coordinateSystem (k : ℕ) : FrameSystem where
  value {V} f g := ((transitionUnit f.chart g.chart V f.within g.within)⁻¹) ^ k
  natural {V W} f g h := by
    rw [map_pow, map_inv]
    exact congrArg (fun u : Γ(Surface,W)ˣ => u⁻¹ ^ k)
      (transitionUnit_restrict _ _ V W h f.within g.within)
  compose {V} f g h := by
    rw [← mul_pow, ← mul_inv_rev, transitionUnit_cocycle]

abbrev coordinateOne (k : ℕ) := logOne (coordinateSystem k)

def coordinateClass (k : ℕ) : differentialAddSheaf.H' 1 ⊤ :=
  cechOneClass pivotCover pivotCover_covers (coordinateOne k) (logOne_closed _)

def divisorSystem : FrameSystem where
  value f g := (divisorTransition f g)⁻¹
  natural f g h := by rw [map_inv, divisorTransition_restrict]
  compose f g h := by rw [← mul_inv_rev, mul_comm, divisorTransition_cocycle]

/-- The coordinate of a genuine moving curve equation in another actual ideal basis. -/
def curveFrame {V : Surface.Opens} (t : Fin 3 → ℂ) (ht : ∀ i, ChartRegular t i) (f : FrameData V) :=
  curveIdealFrame t ht f.chart V f.within f.pivot f.pivotUnit f.pivot_eq

theorem curveFrame_apply {V : Surface.Opens} (t : Fin 3 → ℂ) (ht : ∀ i, ChartRegular t i)
    (f : FrameData V) (r : Γ(Surface,V)) : curveFrame t ht f r = r • curveGenerator t f := by
  change (CycleQ2SeedSectionSheafKernel.evaluationToCurveIdeal t).app V
    (sourceFrame f.chart V f.within f.pivot f.pivotUnit f.pivot_eq r) = _
  rw [sourceFrame_apply, Scheme.Modules.Hom.app_smul]
  rfl

theorem curveFrame_coordinate {V : Surface.Opens} (t : Fin 3 → ℂ) (ht : ∀ i, ChartRegular t i)
    (f g : FrameData V) :
    (curveFrame t ht f).symm (curveGenerator t g) = (divisorTransition f g : Γ(Surface,V)) := by
  apply (curveFrame t ht f).injective
  rw [LinearEquiv.apply_symm_apply, curveFrame_apply, curveGenerator_transition t f g]

def movingUnit {V : Surface.Opens} (t : Fin 3 → ℂ) (ht : ∀ i, ChartRegular t i)
    (f g : FrameData V) : Γ(Surface,V)ˣ :=
  (show IsUnit ((curveFrame t ht f).symm (curveGenerator t g)) by
    rw [curveFrame_coordinate]; exact (divisorTransition f g).isUnit).unit

theorem movingUnit_eq {V : Surface.Opens} (t : Fin 3 → ℂ) (ht : ∀ i, ChartRegular t i)
    (f g : FrameData V) : movingUnit t ht f g = divisorTransition f g := by
  apply Units.ext
  exact (IsUnit.unit_spec _).trans (curveFrame_coordinate t ht f g)

def movingSystem (t : Fin 3 → ℂ) (ht : ∀ i, ChartRegular t i) : FrameSystem where
  value f g := (movingUnit t ht f g)⁻¹
  natural f g h := by simp only [movingUnit_eq, map_inv, divisorTransition_restrict]
  compose f g h := by simp only [movingUnit_eq]; exact divisorSystem.compose f g h

private theorem positive_orbit {V : Surface.Opens} (f g : FrameData V) :
    (orbitTransition f g)⁻¹ = divisorSystem.value f g * ((coordinateSystem 4).value f g)⁻¹ := by
  change _ = (divisorTransition f g)⁻¹ * ((transitionUnit _ _ _ _ _)⁻¹ ^ 4)⁻¹
  rw [divisorTransition_eq_twist_mul_orbit]
  simp [mul_inv_rev]

def orbitSystem : FrameSystem where
  value f g := (orbitTransition f g)⁻¹
  natural f g h := by
    rw [positive_orbit, positive_orbit, map_mul, map_inv, divisorSystem.natural, (coordinateSystem 4).natural]
  compose f g h := by
    simp only [positive_orbit]
    rw [mul_mul_mul_comm, ← mul_inv_rev, mul_comm ((coordinateSystem 4).value g h),
      (coordinateSystem 4).compose, divisorSystem.compose]

def movingClass (t : Fin 3 → ℂ) (ht : ∀ i, ChartRegular t i) : differentialAddSheaf.H' 1 ⊤ :=
  cechOneClass pivotCover pivotCover_covers (logOne (movingSystem t ht)) (logOne_closed _)

def orbitClass : differentialAddSheaf.H' 1 ⊤ :=
  cechOneClass pivotCover pivotCover_covers (logOne orbitSystem) (logOne_closed _)

theorem movingOne_eq (t : Fin 3 → ℂ) (ht : ∀ i, ChartRegular t i) :
    logOne (movingSystem t ht) = logOne orbitSystem + coordinateOne 4 := by
  funext a b
  dsimp only [logOne, movingSystem, orbitSystem, coordinateOne, coordinateSystem, Pi.add_apply]
  rw [movingUnit_eq, divisorTransition_eq_twist_mul_orbit, mul_inv_rev, ← inv_pow, sheafLogDifferential_mul]

theorem movingClass_eq (t : Fin 3 → ℂ) (ht : ∀ i, ChartRegular t i) :
    movingClass t ht = orbitClass + coordinateClass 4 := by
  let η := cechOneClassHom (F := differentialAddSheaf) pivotCover pivotCover_covers
  apply (congrArg η (show (⟨logOne (movingSystem t ht), logOne_closed _⟩ :
      oneCocycles (F := differentialAddSheaf) pivotCover) =
      ⟨logOne orbitSystem, logOne_closed _⟩ + ⟨coordinateOne 4, logOne_closed _⟩ from
      Subtype.ext (movingOne_eq t ht))).trans
  exact η.map_add _ _

end CycleQ2LiteralMovingDivisorChern

end

#print axioms CycleQ2LiteralMovingDivisorChern.curveFrame_coordinate
#print axioms CycleQ2LiteralMovingDivisorChern.movingClass_eq
