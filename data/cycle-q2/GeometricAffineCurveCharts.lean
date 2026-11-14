import Proposal.GeometricCurveCoordinates
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Actual affine equations and Jacobian charts for the sparse projective curve

The two pairs below are obtained by substituting x1 = 1 and x2 = 1 into
exactly `relation r 0` and `curveH θ`. Neither the complex parameter r nor θ
is changed. In particular this file does not identify θ = 0 with θ = 1.

For each pair and each choice of two pivot coordinates, the Jacobian
localization has a constructed submersive presentation. Mathlib's cotangent
sequence then gives a basis of its actual Kahler differential module. The
rank is one on a nonzero localization. This is not a dimension-count premise.

The missing global statements are kept separate: identifying these affine
quotient schemes with the specified projective opens, proving the Jacobian
opens cover the whole curve at a chosen seed, and the canonical/Serre trace
comparison. No completion of the protected certificate is asserted.

Validation: this module compiles under Lean 4.33.1 and the pinned Mathlib
revision, and passes independent leanchecker replay. This validates the
local statements below, not the missing global comparisons.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2GeometricAffineCurveCharts

open MvPolynomial

abbrev AffinePoly := MvPolynomial (Fin 3) ℂ

section Formulas
variable {R : Type*} [CommRing R]

/-- Affine equation on x1 = 1; the middle coordinate is x2/x1. -/
def quadricOne (r a _b c : R) : R := a ^ 2 - r * c

def cubicOne (i θ a b c : R) : R :=
  c ^ 3 + b ^ 3 + b * c + a * b * c + a - i * (1 + c ^ 3) + θ * a ^ 3

/-- Affine equation on x2 = 1; the middle coordinate is x1/x2. -/
def quadricTwo (r a b c : R) : R := a ^ 2 - r * b * c

def cubicTwo (i θ a b c : R) : R :=
  c ^ 3 + 1 + b * c + a * c + a * b ^ 2 - i * (b ^ 3 + c ^ 3) + θ * a ^ 3

end Formulas

def firstQuadric (r : ℂ) : AffinePoly :=
  quadricOne (C r) (X 0) (X 1) (X 2)

def firstCubic (θ : ℂ) : AffinePoly :=
  cubicOne (C Complex.I) (C θ) (X 0) (X 1) (X 2)

def secondQuadric (r : ℂ) : AffinePoly :=
  quadricTwo (C r) (X 0) (X 1) (X 2)

def secondCubic (θ : ℂ) : AffinePoly :=
  cubicTwo (C Complex.I) (C θ) (X 0) (X 1) (X 2)

def firstDehomogenize : CycleQ2SeedTrace.Poly →ₐ[ℂ] AffinePoly :=
  aeval ![X 0, 1, X 1, X 2]

def secondDehomogenize : CycleQ2SeedTrace.Poly →ₐ[ℂ] AffinePoly :=
  aeval ![X 0, X 1, 1, X 2]

/-- Source binding to the existing quadratic relation, not a new curve. -/
theorem firstDehomogenize_quadric (r : ℂ) :
    firstDehomogenize (CycleQ2SeedTrace.relation r 0) = firstQuadric r := by
  simp [firstDehomogenize, CycleQ2SeedTrace.relation, firstQuadric, quadricOne]

theorem secondDehomogenize_quadric (r : ℂ) :
    secondDehomogenize (CycleQ2SeedTrace.relation r 0) = secondQuadric r := by
  simp [secondDehomogenize, CycleQ2SeedTrace.relation, secondQuadric, quadricTwo]

/-- Source binding includes every term of the original sparse cubic. -/
theorem firstDehomogenize_cubic (θ : ℂ) :
    firstDehomogenize (CycleQ2SeedCechTheta.curveH θ) = firstCubic θ := by
  simp [firstDehomogenize, CycleQ2SeedCechTheta.curveH,
    CycleQ2SeedTrace.h, CycleQ2SeedTrace.b, firstCubic, cubicOne]

theorem secondDehomogenize_cubic (θ : ℂ) :
    secondDehomogenize (CycleQ2SeedCechTheta.curveH θ) = secondCubic θ := by
  simp [secondDehomogenize, CycleQ2SeedCechTheta.curveH,
    CycleQ2SeedTrace.h, CycleQ2SeedTrace.b, secondCubic, cubicTwo]

/-! ## Actual quotient rings and their Jacobian localizations -/

def chartIdeal (v : Fin 2 → AffinePoly) : Ideal AffinePoly :=
  Ideal.span (Set.range v)

abbrev ChartRing (v : Fin 2 → AffinePoly) := AffinePoly ⧸ chartIdeal v

/-- The permutation specifies which coordinate is free: it is e(0).
The two pivot coordinates are e(1) and e(2). -/
def chartPresentation (v : Fin 2 → AffinePoly) (e : Equiv.Perm (Fin 3)) :
    Algebra.PreSubmersivePresentation ℂ (ChartRing v) (Fin 3) (Fin 2) :=
  Algebra.PreSubmersivePresentation.naive (v := v)
    (fun j => e j.succ) (e.injective.comp (Fin.succ_injective 2))

abbrev JacobianPatch (v : Fin 2 → AffinePoly) (e : Equiv.Perm (Fin 3)) :=
  Localization.Away (chartPresentation v e).jacobian

/-- The added variable is the inverse of the actual Jacobian minor.
The composite presentation has four variables and three relations. -/
def smoothPresentation (v : Fin 2 → AffinePoly) (e : Equiv.Perm (Fin 3)) :
    Algebra.SubmersivePresentation ℂ (JacobianPatch v e)
      (Unit ⊕ Fin 3) (Unit ⊕ Fin 2) where
  toPreSubmersivePresentation :=
    (Algebra.PreSubmersivePresentation.localizationAway (JacobianPatch v e)
      (chartPresentation v e).jacobian).comp (chartPresentation v e)
  jacobian_isUnit := by
    have hu : IsUnit (algebraMap (ChartRing v) (JacobianPatch v e)
        (chartPresentation v e).jacobian) :=
      IsLocalization.Away.algebraMap_isUnit _
    simpa only [Algebra.PreSubmersivePresentation.comp_jacobian_eq_jacobian_smul_jacobian,
      Algebra.PreSubmersivePresentation.localizationAway_jacobian, Algebra.smul_def]
      using hu.mul hu

theorem smoothPresentation_dimension (v : Fin 2 → AffinePoly)
    (e : Equiv.Perm (Fin 3)) : (smoothPresentation v e).dimension = 1 := by
  change Nat.card (Unit ⊕ Fin 3) - Nat.card (Unit ⊕ Fin 2) = 1
  norm_num [Nat.card_eq_fintype_card]

/-- This is freeness of mathlib's Kahler module, not a separately named
rank-one stand-in. It follows from the constructed presentation. -/
theorem jacobianPatch_kaehler_free (v : Fin 2 → AffinePoly)
    (e : Equiv.Perm (Fin 3)) :
    Module.Free (JacobianPatch v e) (KaehlerDifferential ℂ (JacobianPatch v e)) :=
  (smoothPresentation v e).free_kaehlerDifferential

/-- Exclude an empty localization only when asserting its module rank. -/
theorem jacobianPatch_kaehler_rank (v : Fin 2 → AffinePoly)
    (e : Equiv.Perm (Fin 3)) [Nontrivial (JacobianPatch v e)] :
    Module.rank (JacobianPatch v e) (KaehlerDifferential ℂ (JacobianPatch v e)) = 1 := by
  simpa [smoothPresentation_dimension] using
    (smoothPresentation v e).rank_kaehlerDifferential

abbrev FirstJacobianPatch (r θ : ℂ) (e : Equiv.Perm (Fin 3)) :=
  JacobianPatch ![firstQuadric r, firstCubic θ] e

abbrev SecondJacobianPatch (r θ : ℂ) (e : Equiv.Perm (Fin 3)) :=
  JacobianPatch ![secondQuadric r, secondCubic θ] e

/-- Both concrete affine equations now have genuine local cotangent bases.
No condition r = 57, r^3 = 2, or θ = 0 is smuggled into the statement. -/
theorem actual_chart_kaehler_free (r θ : ℂ) (e : Equiv.Perm (Fin 3)) :
    Module.Free (FirstJacobianPatch r θ e)
      (KaehlerDifferential ℂ (FirstJacobianPatch r θ e)) ∧
    Module.Free (SecondJacobianPatch r θ e)
      (KaehlerDifferential ℂ (SecondJacobianPatch r θ e)) :=
  ⟨jacobianPatch_kaehler_free _ e, jacobianPatch_kaehler_free _ e⟩

end CycleQ2GeometricAffineCurveCharts

end
