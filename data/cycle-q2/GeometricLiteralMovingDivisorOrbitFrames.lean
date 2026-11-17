import Proposal.GeometricCartierDeformation
import Proposal.GeometricSeedOrbitDivisor
import Proposal.GeometricSeedSectionDivisorTransitions

/-!
# Change of generators for the three original curve translates

On each original matrix-pivot open the selected row generates the product
of the three translated curve ideals in the ring of surface sections.
A triple of principal generators therefore gives a unique change of frame.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralMovingDivisorOrbitFrames

open CategoryTheory AlgebraicGeometry TopologicalSpace
open CycleQ2SeedProjectiveImageCocycle CycleQ2SeedProjectiveImageChart
  CycleQ2SeedSectionDivisorFrames CycleQ2SeedSectionDivisorTransitions
  CycleQ2SeedOrbitDivisor CycleQ2LinkageComponentAlgebra
  CycleQ2SeedSectionSheafSections CycleQ2SeedSectionSheafGlobal

variable {V : Surface.Opens}

def translateIdeal (i : Fin 3) (V : Surface.Opens) (hi : V ≤ Patch i) (z : ℂ) :
    Ideal Γ(Surface,V) :=
  (originalCurveTranslateIdeal i z).map (chartSectionMap i V hi)

open CycleQ2SeedTrace CycleQ2SeedCyclicAction CycleQ2GeometricSeedNormalIdeals CycleQ2NormalConnecting
  CycleQ2GeometricSeedNormalizedCoordinates CycleQ2LiteralCyclicDeformation
  CycleQ2GeometricSurfaceDehomogenizedCharts

/-- The cubic generator vanishes on the surface after each of the three actions. -/
theorem translateIdeal_eq_pair (i : Fin 3) (V : Surface.Opens) (hi : V ≤ Patch i)
    (z : ℂ) (hz : z^3 = 1) :
    translateIdeal i V hi z = Ideal.span
      {polynomialSection i V hi (polynomialAction z (originalF1 57)),
        polynomialSection i V hi (polynomialAction z originalF2)} := by
  have hc : polynomialAction z (thetaH 1) = thetaH 1 := by
    rw [← normalizedCubic_eq_thetaH_one (r := (57 : ℂ))]
    exact polynomialAction_cubic z hz
  have hzero : affinePolynomial i (thetaH 1) = 0 := dehomogenizedMap_equation 57 1 i.succ 1
  rw [translateIdeal, originalCurveTranslateIdeal, Ideal.map_map, ambientCurveIdeal,
    Ideal.map_span, ← Set.range_comp]
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨a,rfl⟩
    fin_cases a
    · exact Ideal.subset_span (Set.mem_insert _ _)
    · exact Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))
    · change chartSectionMap i V hi (affinePolynomial i (polynomialAction z (thetaH 1))) ∈ _
      rw [hc, hzero, map_zero]
      exact Ideal.zero_mem _
  · apply Ideal.span_le.mpr
    rintro a (ha | ha)
    · subst a
      exact Ideal.subset_span ⟨0,rfl⟩
    · obtain rfl := Set.mem_singleton_iff.mp ha
      exact Ideal.subset_span ⟨1,rfl⟩

def pivotEquation (f : FrameData V) : Γ(Surface,V) :=
  sectionLeft f.chart V f.within f.pivot.1

theorem pivotEquation_regular (f : FrameData V) :
    Function.Injective (fun r : Γ(Surface,V) => r * pivotEquation f) := by
  intro r s h
  apply generator_scalar_injective f
  apply sourceCoordinate_injective f.chart V f.within
  simp only [map_smul]
  exact (show r * sourceCoordinate f.chart V f.within (generator f) =
      s * sourceCoordinate f.chart V f.within (generator f) by
    simpa only [generator, sourceGenerator_coordinate, pivotEquation] using h)

theorem pivotEquation_span (f : FrameData V) :
    Ideal.span {pivotEquation f} = (OrbitIdeal f.chart).map (chartSectionMap f.chart V f.within) := by
  unfold OrbitIdeal
  rw [CycleQ2SeedProjectiveImageTwist.Regrading.leftIdeal_eq_span, Ideal.map_span, ← Set.range_comp]
  change Ideal.span {pivotEquation f} = Ideal.span (Set.range (sectionLeft f.chart V f.within))
  apply le_antisymm
  · exact (Ideal.span_singleton_le_iff_mem _).mpr (Ideal.subset_span ⟨f.pivot.1,rfl⟩)
  · apply Ideal.span_le.mpr
    rintro _ ⟨a,rfl⟩
    apply Ideal.mem_span_singleton.mpr
    refine ⟨sectionMatrix f.chart V f.within a f.pivot.2 * ↑f.pivotUnit⁻¹, ?_⟩
    exact (sectionLeft_pivot f.chart V f.within f.pivot f.pivotUnit f.pivot_eq a).trans (mul_comm _ _)

theorem pivotEquation_span_product (f : FrameData V) :
    Ideal.span {pivotEquation f} = translateIdeal f.chart V f.within 1 *
      translateIdeal f.chart V f.within complexRoot *
      translateIdeal f.chart V f.within (complexRoot^2) := by
  rw [pivotEquation_span, orbitIdeal_eq_originalCurveTranslate_product, Ideal.map_mul, Ideal.map_mul]
  rfl

/-- The frame parameter is uniquely determined even when the section ring has zero divisors. -/
theorem existsUnique_frameUnit (f : FrameData V) (p : Γ(Surface,V))
    (hp : Ideal.span {p} = Ideal.span {pivotEquation f}) :
    ∃! u : Γ(Surface,V)ˣ, p = (u : Γ(Surface,V)) * pivotEquation f := by
  obtain ⟨a, ha⟩ := Ideal.span_singleton_le_span_singleton.mp hp.le
  obtain ⟨b, hb⟩ := Ideal.span_singleton_le_span_singleton.mp hp.ge
  have hab : a * b = 1 := by
    apply pivotEquation_regular f
    calc
      a * b * pivotEquation f = (pivotEquation f * a) * b := by ring
      _ = pivotEquation f := by rw [← ha, ← hb]
      _ = 1 * pivotEquation f := (one_mul _).symm
  let u : Γ(Surface,V)ˣ := ⟨a,b,hab,(mul_comm _ _).trans hab⟩
  have hu : p = (u : Γ(Surface,V)) * pivotEquation f := ha.trans (mul_comm _ _)
  refine ⟨u, hu, fun v hv => Units.ext (pivotEquation_regular f (hv.symm.trans hu))⟩

structure TranslateFrame (f : FrameData V) where
  first : Γ(Surface,V)
  second : Γ(Surface,V)
  third : Γ(Surface,V)
  first_span : Ideal.span {first} = translateIdeal f.chart V f.within 1
  second_span : Ideal.span {second} = translateIdeal f.chart V f.within complexRoot
  third_span : Ideal.span {third} = translateIdeal f.chart V f.within (complexRoot^2)

theorem translateIdeal_restrict (i : Fin 3) (hi : V ≤ Patch i) (z : ℂ)
    {W : Surface.Opens} (h : W ≤ V) :
    (translateIdeal i V hi z).map (targetRes h) = translateIdeal i W (h.trans hi) z := by
  unfold translateIdeal
  rw [Ideal.map_map]
  congr 1
  exact RingHom.ext (fun x =>
    CycleQ2SeedSectionSheafEvaluation.chartSectionMap_restrict i V W h hi x)

theorem pivotEquation_restrict (f : FrameData V) {W : Surface.Opens} (h : W ≤ V) :
    targetRes h (pivotEquation f) = pivotEquation (f.restrict h) :=
  CycleQ2SeedSectionSheafEvaluation.chartSectionMap_restrict f.chart V W h f.within _

namespace TranslateFrame

variable {f g : FrameData V}

def product (a : TranslateFrame f) : Γ(Surface,V) := a.first * a.second * a.third

theorem product_span (a : TranslateFrame f) :
    Ideal.span {a.product} = Ideal.span {pivotEquation f} := by
  rw [pivotEquation_span_product, ← a.first_span, ← a.second_span, ← a.third_span,
    Ideal.span_singleton_mul_span_singleton, Ideal.span_singleton_mul_span_singleton]
  rfl

def gauge (a : TranslateFrame f) : Γ(Surface,V)ˣ :=
  (existsUnique_frameUnit f a.product a.product_span).exists.choose

theorem product_eq (a : TranslateFrame f) : a.product = (a.gauge : Γ(Surface,V)) * pivotEquation f :=
  (existsUnique_frameUnit f a.product a.product_span).exists.choose_spec

def restrict (a : TranslateFrame f) {W : Surface.Opens} (h : W ≤ V) :
    TranslateFrame (f.restrict h) where
  first := targetRes h a.first
  second := targetRes h a.second
  third := targetRes h a.third
  first_span := by
    change Ideal.span {targetRes h a.first} = translateIdeal f.chart W (h.trans f.within) 1
    rw [← translateIdeal_restrict f.chart f.within 1 h, ← a.first_span, Ideal.map_span, Set.image_singleton]
  second_span := by
    change Ideal.span {targetRes h a.second} = translateIdeal f.chart W (h.trans f.within) complexRoot
    rw [← translateIdeal_restrict f.chart f.within complexRoot h, ← a.second_span, Ideal.map_span, Set.image_singleton]
  third_span := by
    change Ideal.span {targetRes h a.third} = translateIdeal f.chart W (h.trans f.within) (complexRoot^2)
    rw [← translateIdeal_restrict f.chart f.within (complexRoot^2) h, ← a.third_span, Ideal.map_span, Set.image_singleton]

theorem product_restrict (a : TranslateFrame f) {W : Surface.Opens} (h : W ≤ V) :
    targetRes h a.product = (a.restrict h).product := by
  simp only [product, map_mul, restrict]

theorem gauge_restrict (a : TranslateFrame f) {W : Surface.Opens} (h : W ≤ V) :
    Units.map (targetRes h).toMonoidHom a.gauge = (a.restrict h).gauge := by
  apply Units.ext
  apply pivotEquation_regular (f.restrict h)
  change targetRes h (a.gauge : Γ(Surface,V)) * _ = _
  rw [← pivotEquation_restrict, ← map_mul, ← a.product_eq, product_restrict]
  exact (a.restrict h).product_eq.trans (congrArg (fun x : Γ(Surface,W) => ((a.restrict h).gauge : Γ(Surface,W)) * x) (pivotEquation_restrict f h).symm)

/-- The positive orbit transition and the three positive translated Cartier transitions
    differ by the vertex change of generators. -/
theorem transition (a : TranslateFrame f) (b : TranslateFrame g)
    (u : Γ(Surface,V)ˣ) (hu : (u : Γ(Surface,V)) * b.product = a.product) :
    u * b.gauge = a.gauge * (orbitTransition f g)⁻¹ := by
  apply mul_right_cancel (b := orbitTransition f g)
  rw [mul_assoc a.gauge, inv_mul_cancel, mul_one]
  apply Units.ext
  apply pivotEquation_regular f
  simp only [Units.val_mul]
  calc
    (↑u * ↑b.gauge * ↑(orbitTransition f g)) * pivotEquation f =
        ↑u * (↑b.gauge * ((orbitTransition f g : Γ(Surface,V)) * pivotEquation f)) := by ring
    _ = ↑u * b.product := by
      have hg : pivotEquation g = (orbitTransition f g : Γ(Surface,V)) * pivotEquation f :=
        orbitTransition_generator f g
      rw [← hg, ← b.product_eq]
    _ = ↑a.gauge * pivotEquation f := hu.trans a.product_eq

end TranslateFrame

end CycleQ2LiteralMovingDivisorOrbitFrames

#print axioms CycleQ2LiteralMovingDivisorOrbitFrames.pivotEquation_span_product
#print axioms CycleQ2LiteralMovingDivisorOrbitFrames.TranslateFrame.transition
