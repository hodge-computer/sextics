import Proposal.GeometricSeedSectionDivisorFrames
import Proposal.GeometricSurfaceProjectiveCoefficients

/-!
# Transitions of the original curve ideal and the retained hyperplane twist

These are transition functions of the actual native kernel sheaf and of
the actual curve ideal, on common unit-pivot subopens of the original
projective charts. The unit is computed from the original matrix entries.
Its cocycle law is proved from the actual frame equations and their
injectivity. In particular no curve parameter enters the unit.

The degree-fourteen curve-ideal transition is the product of the
degree-ten orbit-ideal transition and the fourth power of the original
coordinate-ratio unit. Their universal dlog identity retains both the
hyperplane term and the dual-frame sign. This supplies concrete local
data for the Chern comparison; it does not identify a Kodaira--Spencer
contraction, geometric Serre trace, or Abel--Jacobi derivative.

Prepared for fqlx with OpenAI ChatGPT assistance; see solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2SeedSectionDivisorTransitions

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry Matrix
open CycleQ2SeedProjectiveImageCocycle CycleQ2SeedSectionSheaf
  CycleQ2SeedSectionSheafSections CycleQ2SeedSectionSheafTwist
  CycleQ2SeedSectionDivisorFrames CycleQ2SeedSectionSheafKernel
  CycleQ2SeedSectionSheafLocal CycleQ2SeedSectionSheafGlobal

/-- An original chart and a matrix entry that is a unit on this actual open. -/
structure FrameData (V : Surface.Opens) where
  chart : Fin 3
  within : V ≤ Patch chart
  pivot : Fin 3 × Fin 3
  pivotUnit : Γ(Surface, V)ˣ
  pivot_eq : (pivotUnit : Γ(Surface, V)) =
    sectionMatrix chart V within pivot.1 pivot.2

variable {V : Surface.Opens}

def generator (f : FrameData V) : Γ(twistedIdeal, V) :=
  sourceGenerator f.chart V f.within f.pivot.1

theorem generator_scalar_injective (f : FrameData V) :
    Function.Injective (fun r : Γ(Surface, V) => r • generator f) :=
  sourceFrameMap_injective f.chart V f.within f.pivot f.pivotUnit f.pivot_eq

theorem sectionMatrix_cofactors (f : FrameData V) :
    CycleQ2SegreLocal.cofactors (sectionMatrix f.chart V f.within) = 0 :=
  CycleQ2SegreCech.cofactors_map_zero
    (chartSectionMap f.chart V f.within)
    (CycleQ2SeedProjectiveImageChart.chartFactorData f.chart).matrix
    (CycleQ2SeedProjectiveImageChart.chartFactorData f.chart).cofactors_zero

/-- The second pivot, expressed in the first original coordinate chart. -/
def secondPivot (f g : FrameData V) : Γ(Surface, V)ˣ :=
  (transitionUnit f.chart g.chart V f.within g.within)⁻¹ ^ 14 * g.pivotUnit

theorem secondPivot_val (f g : FrameData V) :
    (secondPivot f g : Γ(Surface, V)) =
      sectionMatrix f.chart V f.within g.pivot.1 g.pivot.2 := by
  have hM := congrArg (fun M => M g.pivot.1 g.pivot.2)
    (sectionMatrix_change f.chart g.chart V f.within g.within)
  change sectionMatrix g.chart V g.within g.pivot.1 g.pivot.2 =
    (transitionUnit f.chart g.chart V f.within g.within : Γ(Surface, V)) ^ 14 *
      sectionMatrix f.chart V f.within g.pivot.1 g.pivot.2 at hM
  simp only [secondPivot, Units.val_mul, Units.val_pow_eq_pow_val]
  rw [g.pivot_eq, hM, ← mul_assoc, ← mul_pow, Units.inv_mul, one_pow, one_mul]

/-- The actual row ratio, in a common ring of original surface sections. -/
def pivotTransition (f g : FrameData V) : Γ(Surface, V)ˣ :=
  CycleQ2SegreCech.transition (sectionMatrix f.chart V f.within)
    (sectionMatrix_cofactors f) f.pivot g.pivot f.pivotUnit
    (secondPivot f g) f.pivot_eq (secondPivot_val f g)

theorem pivotTransition_val (f g : FrameData V) :
    (pivotTransition f g : Γ(Surface, V)) =
      sectionMatrix f.chart V f.within g.pivot.1 f.pivot.2 *
        (↑(f.pivotUnit⁻¹) : Γ(Surface, V)) := rfl

/-- Transition of the literal orbit-ideal generators, of degree ten. -/
def orbitTransition (f g : FrameData V) : Γ(Surface, V)ˣ :=
  transitionUnit f.chart g.chart V f.within g.within ^ 10 * pivotTransition f g

/-- Transition of the actual source/curve-ideal frames, of degree fourteen. -/
def divisorTransition (f g : FrameData V) : Γ(Surface, V)ˣ :=
  transitionUnit f.chart g.chart V f.within g.within ^ 14 * pivotTransition f g

theorem orbitTransition_generator (f g : FrameData V) :
    sectionLeft g.chart V g.within g.pivot.1 =
      (orbitTransition f g : Γ(Surface, V)) *
        sectionLeft f.chart V f.within f.pivot.1 := by
  have hL := congrFun (sectionLeft_change f.chart g.chart V f.within g.within)
    g.pivot.1
  change sectionLeft g.chart V g.within g.pivot.1 =
    (transitionUnit f.chart g.chart V f.within g.within : Γ(Surface, V)) ^ 10 *
      sectionLeft f.chart V f.within g.pivot.1 at hL
  rw [hL, sectionLeft_pivot f.chart V f.within f.pivot f.pivotUnit f.pivot_eq]
  simp only [orbitTransition, Units.val_mul, Units.val_pow_eq_pow_val, pivotTransition_val]
  ring

/-- This is an equality of sections of the independently defined global kernel. -/
theorem generator_transition (f g : FrameData V) :
    generator g = (divisorTransition f g : Γ(Surface, V)) • generator f := by
  apply sourceCoordinate_injective f.chart V f.within
  rw [sourceCoordinate_transition f.chart g.chart V f.within g.within]
  change (transitionUnit f.chart g.chart V f.within g.within : Γ(Surface, V)) ^ 4 *
      sourceCoordinate g.chart V g.within
        (sourceGenerator g.chart V g.within g.pivot.1) = _
  rw [sourceGenerator_coordinate, orbitTransition_generator, map_smul]
  change _ = (divisorTransition f g : Γ(Surface, V)) *
    sourceCoordinate f.chart V f.within
      (sourceGenerator f.chart V f.within f.pivot.1)
  rw [sourceGenerator_coordinate]
  simp only [orbitTransition, divisorTransition, Units.val_mul, Units.val_pow_eq_pow_val]
  ring

/-- The matrix formula is the unique unit giving the actual frame change. -/
theorem divisorTransition_unique (f g : FrameData V) (u : Γ(Surface, V)ˣ)
    (hu : generator g = (u : Γ(Surface, V)) • generator f) :
    u = divisorTransition f g := by
  apply Units.ext
  apply generator_scalar_injective f
  exact hu.symm.trans (generator_transition f g)

theorem divisorTransition_self (f : FrameData V) : divisorTransition f f = 1 := by
  exact (divisorTransition_unique f f 1 (by simp)).symm

/-- The cocycle law follows inside the actual source, using an actual basis. -/
theorem divisorTransition_cocycle (f g h : FrameData V) :
    divisorTransition f g * divisorTransition g h = divisorTransition f h := by
  apply divisorTransition_unique f h
  rw [generator_transition g h, generator_transition f g]
  simp only [smul_smul, Units.val_mul, mul_comm]

theorem divisorTransition_reverse (f g : FrameData V) :
    divisorTransition g f = (divisorTransition f g)⁻¹ := by
  have h := divisorTransition_cocycle f g f
  rw [divisorTransition_self] at h
  exact (eq_inv_iff_mul_eq_one.mpr (by simpa only [mul_comm] using h))

/-- The curve parameter changes the inclusion, while the frame transition is fixed. -/
def curveGenerator (t : Fin 3 → ℂ) (f : FrameData V) : Γ(curveIdeal t, V) :=
  (evaluationToCurveIdeal t).app V (generator f)

theorem curveGenerator_transition (t : Fin 3 → ℂ) (f g : FrameData V) :
    curveGenerator t g =
      (divisorTransition f g : Γ(Surface, V)) • curveGenerator t f := by
  unfold curveGenerator
  rw [generator_transition, Scheme.Modules.Hom.app_smul]

/-- The fourth-power factor has the original negative-fourth source orientation. -/
theorem divisorTransition_eq_twist_mul_orbit (f g : FrameData V) :
    divisorTransition f g =
      transitionUnit f.chart g.chart V f.within g.within ^ 4 * orbitTransition f g := by
  unfold divisorTransition orbitTransition
  rw [← mul_assoc, ← pow_add]

/-! ## Restriction of the actual frame and transition data -/

theorem sectionMatrix_restrict (i : Fin 3) {V W : Surface.Opens}
    (hWV : W ≤ V) (hi : V ≤ Patch i) (a b : Fin 3) :
    targetRes hWV (sectionMatrix i V hi a b) =
      sectionMatrix i W (hWV.trans hi) a b :=
  CycleQ2SeedSectionSheafEvaluation.chartSectionMap_restrict i V W hWV hi _

def FrameData.restrict (f : FrameData V) {W : Surface.Opens} (hWV : W ≤ V) :
    FrameData W where
  chart := f.chart
  within := hWV.trans f.within
  pivot := f.pivot
  pivotUnit := Units.map (targetRes hWV).toMonoidHom f.pivotUnit
  pivot_eq := by
    change targetRes hWV (f.pivotUnit : Γ(Surface, V)) = _
    rw [f.pivot_eq]
    exact sectionMatrix_restrict f.chart hWV f.within f.pivot.1 f.pivot.2

theorem generator_restrict (f : FrameData V) {W : Surface.Opens} (hWV : W ≤ V) :
    moduleRes twistedIdeal hWV (generator f) = generator (f.restrict hWV) :=
  sourceGenerator_restrict f.chart V W hWV f.within f.pivot.1

/-- The actual transition units commute with the original structure restrictions. -/
theorem divisorTransition_restrict (f g : FrameData V) {W : Surface.Opens}
    (hWV : W ≤ V) :
    Units.map (targetRes hWV).toMonoidHom (divisorTransition f g) =
      divisorTransition (f.restrict hWV) (g.restrict hWV) := by
  apply divisorTransition_unique
  have h := congrArg (moduleRes twistedIdeal hWV) (generator_transition f g)
  rw [← generator_restrict g hWV, ← generator_restrict f hWV]
  change moduleRes twistedIdeal hWV (generator g) =
    targetRes hWV (divisorTransition f g : Γ(Surface, V)) •
      moduleRes twistedIdeal hWV (generator f)
  change sourceRes hWV (generator g) =
    targetRes hWV (divisorTransition f g : Γ(Surface, V)) • sourceRes hWV (generator f)
  change sourceRes hWV (generator g) =
    sourceRes hWV ((divisorTransition f g : Γ(Surface, V)) • generator f) at h
  rw [sourceRes_smul] at h
  exact h

/-! ## Universal differentials with the actual projective complex coefficients -/

local instance sectionsAlgebra (V : Surface.Opens) : Algebra ℂ Γ(Surface, V) :=
  (CycleQ2GeometricDifferentialSheaf.coefficientOn Surface.sheaf
    (CycleQ2GeometricSurfaceCoefficients.projectiveGlobalCoefficient 57 1) V).toAlgebra

theorem divisorTransition_dlog (f g : FrameData V) :
    CycleQ2SegreCech.unitDlog ℂ (divisorTransition f g) =
      CycleQ2SegreCech.unitDlog ℂ (orbitTransition f g) +
        4 • CycleQ2SegreCech.unitDlog ℂ
          (transitionUnit f.chart g.chart V f.within g.within) := by
  rw [divisorTransition_eq_twist_mul_orbit,
    CycleQ2SegreCech.unitDlog_mul, CycleQ2SegreCech.unitDlog_pow, add_comm]

/-- Dual frames give the positive E + 4H orientation, with no lost twist. -/
theorem dualTransition_dlog (f g : FrameData V) :
    CycleQ2SegreCech.unitDlog ℂ ((divisorTransition f g)⁻¹) =
      CycleQ2SegreCech.unitDlog ℂ ((orbitTransition f g)⁻¹) +
        4 • CycleQ2SegreCech.unitDlog ℂ
          ((transitionUnit f.chart g.chart V f.within g.within)⁻¹) := by
  rw [CycleQ2SegreCech.unitDlog_inv, divisorTransition_dlog,
    CycleQ2SegreCech.unitDlog_inv, CycleQ2SegreCech.unitDlog_inv]
  simp only [smul_neg, neg_add_rev, add_comm]

theorem divisorTransition_dlog_cocycle (f g h : FrameData V) :
    CycleQ2SegreCech.unitDlog ℂ (divisorTransition f g) +
      CycleQ2SegreCech.unitDlog ℂ (divisorTransition g h) =
        CycleQ2SegreCech.unitDlog ℂ (divisorTransition f h) := by
  rw [← CycleQ2SegreCech.unitDlog_mul, divisorTransition_cocycle]

end CycleQ2SeedSectionDivisorTransitions

end

#print axioms CycleQ2SeedSectionDivisorTransitions.generator_transition
#print axioms CycleQ2SeedSectionDivisorTransitions.curveGenerator_transition
#print axioms CycleQ2SeedSectionDivisorTransitions.divisorTransition_cocycle
#print axioms CycleQ2SeedSectionDivisorTransitions.divisorTransition_restrict
#print axioms CycleQ2SeedSectionDivisorTransitions.dualTransition_dlog
