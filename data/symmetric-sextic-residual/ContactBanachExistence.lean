import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Complex.Basic

/-!
# The analytic step in the exact contact certificate

This file contains the Banach fixed-point step, with constants deliberately
rounded to one half.  The actual contact data must prove the hypotheses;
there is no assumed root or additional axiom here.
-/

noncomputable section

namespace ContactBanachExistence

open Metric Set
open scoped NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

/-- A square approximate left inverse with defect below one is injective. -/
theorem injective_of_half_defect (B J : E →ₗ[ℂ] E)
    (hdefect : ∀ v, ‖v - B (J v)‖ ≤ (1 / 2 : ℝ) * ‖v‖) :
    Function.Injective B := by
  have hBJ : Function.Injective (B.comp J) := by
    intro u v huv
    have hzero : B (J (u - v)) = 0 := by
      simp only [map_sub]
      exact sub_eq_zero.mpr huv
    have h := hdefect (u - v)
    rw [hzero, sub_zero] at h
    have hn : ‖u - v‖ = 0 := by
      have := norm_nonneg (u - v)
      linarith
    exact sub_eq_zero.mp (norm_eq_zero.mp hn)
  have hJ : Function.Injective J := by
    intro u v huv
    exact hBJ (congrArg B huv)
  have hJs : Function.Surjective J := LinearMap.injective_iff_surjective.mp hJ
  intro u v huv
  obtain ⟨x, rfl⟩ := hJs u
  obtain ⟨y, rfl⟩ := hJs v
  exact congrArg J (hBJ huv)

/-- A quantitative square Newton certificate has an actual complex zero.

The domain norm is the usual norm on `E`; in the application `E = Fin 44 → ℂ`
with its supremum norm.  Rational bounds for `|re| + |im|` can therefore be
used as conservative upper bounds for the complex coefficients.
-/
theorem exists_zero_in_closedBall
    (F : E → E) (B J : E →ₗ[ℂ] E) (c : E) (r : ℝ)
    (hr : 0 < r)
    (hcenter : ‖B (F c)‖ ≤ r / 2)
    (hcontract : ∀ x ∈ closedBall c r, ∀ y ∈ closedBall c r,
      ‖(x - B (F x)) - (y - B (F y))‖ ≤ (1 / 2 : ℝ) * ‖x - y‖)
    (hdefect : ∀ v, ‖v - B (J v)‖ ≤ (1 / 2 : ℝ) * ‖v‖) :
    ∃ x ∈ closedBall c r, F x = 0 := by
  let T : E → E := fun x => x - B (F x)
  have hc : c ∈ closedBall c r := mem_closedBall_self hr.le
  have hTcenter : dist (T c) c ≤ r / 2 := by
    simpa [T, dist_eq_norm, sub_right_comm] using hcenter
  have hmaps : MapsTo T (closedBall c r) (closedBall c r) := by
    intro x hx
    change dist (T x) c ≤ r
    calc
      dist (T x) c ≤ dist (T x) (T c) + dist (T c) c := dist_triangle _ _ _
      _ ≤ (1 / 2 : ℝ) * dist x c + r / 2 := by
        exact add_le_add (by simpa [T, dist_eq_norm] using hcontract x hx c hc) hTcenter
      _ ≤ r := by
        have hx' : dist x c ≤ r := hx
        linarith
  have hrestricted : ContractingWith (1 / 2 : ℝ≥0)
      (hmaps.restrict T (closedBall c r) (closedBall c r)) := by
    constructor
    · norm_num
    · rw [lipschitzWith_iff_dist_le_mul]
      intro x y
      have h := hcontract x x.property y y.property
      change dist (T x) (T y) ≤ ((1 / 2 : ℝ≥0) : ℝ) * dist (x : E) (y : E)
      simpa [T, dist_eq_norm] using h
  obtain ⟨x, hx, hfixed, _⟩ := ContractingWith.exists_fixedPoint'
    (isClosed_closedBall.isComplete) hmaps hrestricted hc (edist_ne_top _ _)
  refine ⟨x, hx, ?_⟩
  have hB : B (F x) = 0 := by
    have h := hfixed.eq
    change x - B (F x) = x at h
    exact sub_eq_self.mp h
  apply injective_of_half_defect B J hdefect
  simpa using hB

/-- A bound on the derivative of the Newton map supplies the contraction
hypothesis used by the preceding theorem. -/
theorem newton_half_lipschitz_of_derivative
    (F : E → E) (B : E →L[ℂ] E) (A : E → E →L[ℂ] E)
    (c : E) (r : ℝ)
    (hderiv : ∀ x ∈ closedBall c r, HasFDerivAt F (A x) x)
    (hbound : ∀ x ∈ closedBall c r,
      ‖ContinuousLinearMap.id ℂ E - B.comp (A x)‖ ≤ (1 / 2 : ℝ)) :
    ∀ x ∈ closedBall c r, ∀ y ∈ closedBall c r,
      ‖(x - B (F x)) - (y - B (F y))‖ ≤ (1 / 2 : ℝ) * ‖x - y‖ := by
  intro x hx y hy
  exact (convex_closedBall c r).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun z hz => ((hasFDerivAt_id z).sub
      (B.hasFDerivAt.comp z (hderiv z hz))).hasFDerivWithinAt)
    hbound hy hx

end ContactBanachExistence
