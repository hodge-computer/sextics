import Proposal.GeometricSeedSectionSheafIso

/-!
# Explicit frames of the original twisted source

The generator on a unit matrix-pivot open is a section of the original
global kernel, obtained by the already proved inverse chart projection.
It is a basis of its actual module of sections. Evaluation sends this
generator to the original row equation for the same constant vector.

These frames are independent of that vector. They therefore also frame
the native ideal of every regular section curve, through the existing
canonical isomorphism. The transition and Chern comparisons are developed
from these actual frames, rather than from a replacement line bundle.

Prepared for fqlx with OpenAI ChatGPT assistance. The geometric route and
its attribution, and the separate protected exactness gap, are in solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2SeedSectionDivisorFrames

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry Matrix
open CycleQ2SegreFactorSequence CycleQ2SegreLinkageDuality
open CycleQ2SeedProjectiveImageChart CycleQ2SeedProjectiveImageCocycle
  CycleQ2SeedSectionSheaf CycleQ2SeedSectionSheafSections
  CycleQ2SeedSectionSheafMono CycleQ2SeedSectionSheafIdealOverlap
  CycleQ2SeedSectionSheafLocal CycleQ2SeedSectionSheafImage
  CycleQ2SeedSectionSheafGlobal CycleQ2SeedSectionSheafKernel
  CycleQ2SeedSectionSheafIso CycleQ2SeedSectionAffineInjective
  CycleQ2SeedSectionSheafCurveBinding

section Linkage

variable {R : Type} [CommRing R]

/-- The original left sections have the same row ratios as the matrix. -/
theorem left_matrix_balance (F : FactorData R) (a c b : Fin 3) :
    F.left a * F.matrix c b = F.left c * F.matrix a b := by
  apply F.regular
  calc
    F.linkage * (F.left a * F.matrix c b) =
        F.left a * (F.linkage * F.matrix c b) := by ring
    _ = F.left a * (F.left c * F.right b) := by rw [F.product]
    _ = F.left c * (F.left a * F.right b) := by ring
    _ = F.left c * (F.linkage * F.matrix a b) := by rw [F.product]
    _ = F.linkage * (F.left c * F.matrix a b) := by ring

end Linkage

/-- A literal original left generator, lifted into the native global kernel. -/
def sourceGenerator (i : Fin 3) (V : Surface.Opens) (hi : V ≤ Patch i)
    (a : Fin 3) : Γ(twistedIdeal, V) :=
  sourceOfChartSection i V hi (generatorSection i V hi a)

theorem sourceGenerator_projection (i : Fin 3) (V : Surface.Opens)
    (hi : V ≤ Patch i) (a : Fin 3) :
    (chartProjection i).app V (sourceGenerator i V hi a) =
      generatorSection i V hi a :=
  chartProjection_sourceOfChartSection i V hi _

theorem sourceGenerator_coordinate (i : Fin 3) (V : Surface.Opens)
    (hi : V ≤ Patch i) (a : Fin 3) :
    sourceCoordinate i V hi (sourceGenerator i V hi a) = sectionLeft i V hi a := by
  change idealCoordinate i V hi
    ((chartProjection i).app V (sourceGenerator i V hi a)) = _
  rw [sourceGenerator_projection, generatorSection_coordinate]

theorem sourceCoordinate_injective (i : Fin 3) (V : Surface.Opens)
    (hi : V ≤ Patch i) : Function.Injective (sourceCoordinate i V hi) :=
  (idealCoordinate_injective i V hi).comp (chartProjection_app_injective i V hi)

/-- Evaluation is the original row, with the same t and no rescaling. -/
theorem sourceGenerator_evaluation (t : Fin 3 → ℂ) (i : Fin 3)
    (V : Surface.Opens) (hi : V ≤ Patch i) (a : Fin 3) :
    (globalEvaluation t).app V (sourceGenerator i V hi a) = sectionRows t i V hi a := by
  rw [globalEvaluation_on_patch]
  change evaluationCoordinate t i V hi
    ((chartProjection i).app V (sourceGenerator i V hi a)) = _
  rw [sourceGenerator_projection, generatorSection_evaluation]

theorem sectionRows_basis (i : Fin 3) (V : Surface.Opens) (hi : V ≤ Patch i)
    (a b : Fin 3) :
    sectionRows (Pi.single b 1) i V hi a = sectionMatrix i V hi a b := by
  rw [sectionRows_eq_mulVec]
  simp [Matrix.mulVec, dotProduct, Pi.single_apply,
    CycleQ2SeedSectionBalance.sectionConstant, apply_ite]

theorem sectionLeft_matrix_balance (i : Fin 3) (V : Surface.Opens)
    (hi : V ≤ Patch i) (a c b : Fin 3) :
    sectionLeft i V hi a * sectionMatrix i V hi c b =
      sectionLeft i V hi c * sectionMatrix i V hi a b := by
  simpa only [map_mul, sectionLeft, sectionMatrix, RingHom.mapMatrix_apply,
    Matrix.map_apply] using
    congrArg (chartSectionMap i V hi)
      (left_matrix_balance (chartFactorData i) a c b)

/-- A unit pivot supplies the actual ratios of the original ideal generators. -/
theorem sectionLeft_pivot (i : Fin 3) (V : Surface.Opens) (hi : V ≤ Patch i)
    (p : Fin 3 × Fin 3) (up : Γ(Surface, V)ˣ)
    (hp : (up : Γ(Surface, V)) = sectionMatrix i V hi p.1 p.2) (a : Fin 3) :
    sectionLeft i V hi a =
      (sectionMatrix i V hi a p.2 * (↑(up⁻¹) : Γ(Surface, V))) *
        sectionLeft i V hi p.1 := by
  have hb := sectionLeft_matrix_balance i V hi a p.1 p.2
  rw [← hp] at hb
  calc
    sectionLeft i V hi a =
        (sectionLeft i V hi a * (up : Γ(Surface, V))) *
          (↑(up⁻¹) : Γ(Surface, V)) := by
      rw [mul_assoc, Units.mul_inv, mul_one]
    _ = (sectionLeft i V hi p.1 * sectionMatrix i V hi a p.2) *
        (↑(up⁻¹) : Γ(Surface, V)) := by rw [hb]
    _ = _ := by ring

def sourceFrameMap (i : Fin 3) (V : Surface.Opens) (hi : V ≤ Patch i)
    (a : Fin 3) : Γ(Surface, V) →ₗ[Γ(Surface, V)] Γ(twistedIdeal, V) where
  toFun r := r • sourceGenerator i V hi a
  map_add' r s := add_smul r s _
  map_smul' r s := mul_smul r s _

theorem sourceFrameMap_injective (i : Fin 3) (V : Surface.Opens)
    (hi : V ≤ Patch i) (p : Fin 3 × Fin 3) (up : Γ(Surface, V)ˣ)
    (hp : (up : Γ(Surface, V)) = sectionMatrix i V hi p.1 p.2) :
    Function.Injective (sourceFrameMap i V hi p.1) := by
  intro r s hrs
  have h := congrArg (globalEvaluationLinear (Pi.single p.2 1) V) hrs
  change globalEvaluationLinear (Pi.single p.2 1) V
      (r • sourceGenerator i V hi p.1) =
    globalEvaluationLinear (Pi.single p.2 1) V
      (s • sourceGenerator i V hi p.1) at h
  rw [map_smul, map_smul] at h
  have he := sourceGenerator_evaluation (Pi.single p.2 1) i V hi p.1
  change globalEvaluationLinear (Pi.single p.2 1) V
      (sourceGenerator i V hi p.1) = sectionRows (Pi.single p.2 1) i V hi p.1 at he
  rw [he, sectionRows_basis, ← hp] at h
  change r * (up : Γ(Surface, V)) = s * (up : Γ(Surface, V)) at h
  have hc := congrArg (fun x : Γ(Surface, V) => x * (↑(up⁻¹) : Γ(Surface, V))) h
  simpa only [mul_assoc, Units.mul_inv, mul_one] using hc

theorem sourceFrameMap_surjective (i : Fin 3) (V : Surface.Opens)
    (hi : V ≤ Patch i) (p : Fin 3 × Fin 3) (up : Γ(Surface, V)ˣ)
    (hp : (up : Γ(Surface, V)) = sectionMatrix i V hi p.1 p.2) :
    Function.Surjective (sourceFrameMap i V hi p.1) := by
  intro s
  have hx : sourceCoordinate i V hi s ∈ Ideal.span (Set.range (sectionLeft i V hi)) := by
    rw [← idealCoordinate_range_span]
    exact ⟨(chartProjection i).app V s, rfl⟩
  have hspan : Ideal.span (Set.range (sectionLeft i V hi)) ≤
      Ideal.span {sectionLeft i V hi p.1} := by
    apply Ideal.span_le.mpr
    rintro _ ⟨a, rfl⟩
    apply Ideal.mem_span_singleton.mpr
    refine ⟨sectionMatrix i V hi a p.2 * (↑(up⁻¹) : Γ(Surface, V)), ?_⟩
    rw [sectionLeft_pivot i V hi p up hp a]
    ring
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton.mp (hspan hx)
  refine ⟨r, ?_⟩
  apply sourceCoordinate_injective i V hi
  change sourceCoordinate i V hi (r • sourceGenerator i V hi p.1) = _
  rw [map_smul, sourceGenerator_coordinate]
  change r * sectionLeft i V hi p.1 = sourceCoordinate i V hi s
  exact (mul_comm _ _).trans hr.symm

/-- A basis of the sections of the actual original kernel on each unit-pivot open. -/
def sourceFrame (i : Fin 3) (V : Surface.Opens) (hi : V ≤ Patch i)
    (p : Fin 3 × Fin 3) (up : Γ(Surface, V)ˣ)
    (hp : (up : Γ(Surface, V)) = sectionMatrix i V hi p.1 p.2) :
    Γ(Surface, V) ≃ₗ[Γ(Surface, V)] Γ(twistedIdeal, V) :=
  LinearEquiv.ofBijective (sourceFrameMap i V hi p.1)
    ⟨sourceFrameMap_injective i V hi p up hp,
      sourceFrameMap_surjective i V hi p up hp⟩

theorem sourceFrame_apply (i : Fin 3) (V : Surface.Opens) (hi : V ≤ Patch i)
    (p : Fin 3 × Fin 3) (up : Γ(Surface, V)ˣ)
    (hp : (up : Γ(Surface, V)) = sectionMatrix i V hi p.1 p.2)
    (r : Γ(Surface, V)) :
    sourceFrame i V hi p up hp r = r • sourceGenerator i V hi p.1 := rfl

theorem sourceFrame_evaluation (t : Fin 3 → ℂ) (i : Fin 3)
    (V : Surface.Opens) (hi : V ≤ Patch i) (p : Fin 3 × Fin 3)
    (up : Γ(Surface, V)ˣ)
    (hp : (up : Γ(Surface, V)) = sectionMatrix i V hi p.1 p.2)
    (r : Γ(Surface, V)) :
    (globalEvaluation t).app V (sourceFrame i V hi p up hp r) =
      r * sectionRows t i V hi p.1 := by
  rw [sourceFrame_apply, Scheme.Modules.Hom.app_smul, sourceGenerator_evaluation]
  rfl

/-- The frame generators restrict as sections of the actual sheaf. -/
theorem sourceGenerator_restrict (i : Fin 3) (V W : Surface.Opens)
    (hWV : W ≤ V) (hi : V ≤ Patch i) (a : Fin 3) :
    moduleRes twistedIdeal hWV (sourceGenerator i V hi a) =
      sourceGenerator i W (hWV.trans hi) a := by
  apply sourceCoordinate_injective i W (hWV.trans hi)
  change sourceCoordinate i W (hWV.trans hi)
      (twistedIdeal.presheaf.map (homOfLE hWV).op (sourceGenerator i V hi a)) = _
  rw [← sourceCoordinate_restrict, sourceGenerator_coordinate, sourceGenerator_coordinate]
  exact CycleQ2SeedSectionSheafEvaluation.chartSectionMap_restrict i V W hWV hi _

/-- The same original section curve has this actual native ideal frame. -/
def curveIdealFrame (t : Fin 3 → ℂ) (hreg : ∀ i : Fin 3, ChartRegular t i)
    (i : Fin 3) (V : Surface.Opens) (hi : V ≤ Patch i) (p : Fin 3 × Fin 3)
    (up : Γ(Surface, V)ˣ)
    (hp : (up : Γ(Surface, V)) = sectionMatrix i V hi p.1 p.2) :
    Γ(Surface, V) ≃ₗ[Γ(Surface, V)] Γ(curveIdeal t, V) :=
  (sourceFrame i V hi p up hp).trans
    (LinearEquiv.ofBijective (((evaluationToCurveIdeal t).val.app (op V)).hom)
      ⟨evaluationToCurveIdeal_app_injective t hreg V,
        evaluationToCurveIdeal_app_surjective t hreg V⟩)

/-- Under the genuine ideal inclusion this frame is the literal row equation. -/
theorem curveIdealFrame_coordinate (t : Fin 3 → ℂ)
    (hreg : ∀ i : Fin 3, ChartRegular t i) (i : Fin 3)
    (V : Surface.Opens) (hi : V ≤ Patch i) (p : Fin 3 × Fin 3)
    (up : Γ(Surface, V)ˣ)
    (hp : (up : Γ(Surface, V)) = sectionMatrix i V hi p.1 p.2)
    (r : Γ(Surface, V)) :
    (CycleQ2GeometricIntrinsicNormal.kernelIdealSectionEquiv (curveToSurface t) V
      (curveIdealFrame t hreg i V hi p up hp r) : Γ(Surface, V)) =
      r * sectionRows t i V hi p.1 := by
  change (CycleQ2GeometricIntrinsicNormal.kernelIdealSectionEquiv (curveToSurface t) V
      ((evaluationToCurveIdeal t).app V (sourceFrame i V hi p up hp r)) :
        Γ(Surface, V)) = _
  rw [evaluationToCurveIdeal_coordinate]
  exact sourceFrame_evaluation t i V hi p up hp r

/-- For the original regular vector the frame equation is a non-zero-divisor
in the actual structure-sheaf section ring on every unit-pivot open. -/
theorem curveEquation_regular_on_pivot (t : Fin 3 → ℂ)
    (hreg : ∀ i : Fin 3, ChartRegular t i) (i : Fin 3)
    (V : Surface.Opens) (hi : V ≤ Patch i) (p : Fin 3 × Fin 3)
    (up : Γ(Surface, V)ˣ)
    (hp : (up : Γ(Surface, V)) = sectionMatrix i V hi p.1 p.2) :
    IsSMulRegular Γ(Surface, V) (sectionRows t i V hi p.1) := by
  intro r s hrs
  apply sourceFrameMap_injective i V hi p up hp
  apply CycleQ2SeedSectionSheafGlobalMono.globalEvaluation_app_injective t hreg V
  change (globalEvaluation t).app V (r • sourceGenerator i V hi p.1) =
    (globalEvaluation t).app V (s • sourceGenerator i V hi p.1)
  rw [Scheme.Modules.Hom.app_smul, Scheme.Modules.Hom.app_smul,
    sourceGenerator_evaluation]
  change r * sectionRows t i V hi p.1 = s * sectionRows t i V hi p.1
  simpa only [smul_eq_mul, mul_comm] using hrs

end CycleQ2SeedSectionDivisorFrames

end

#print axioms CycleQ2SeedSectionDivisorFrames.sourceGenerator_evaluation
#print axioms CycleQ2SeedSectionDivisorFrames.sourceFrame
#print axioms CycleQ2SeedSectionDivisorFrames.curveIdealFrame_coordinate
#print axioms CycleQ2SeedSectionDivisorFrames.curveEquation_regular_on_pivot
