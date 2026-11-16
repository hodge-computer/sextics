import Proposal.GeometricIncidenceChartMinor
import Mathlib.RingTheory.Localization.Basic
import Mathlib.RingTheory.Smooth.Flat

/-!
# Smoothness of the original incidence-surface cone minor patches

The standard-smooth Jacobian presentation uses the ordered equations F,h.
Their span is exactly the existing pointEquations ideal, and the quotient
equivalence preserves every polynomial and coefficient. The induced
localization algebra equivalence sends the presentation Jacobian to the
original surface minor. Thus the actual PointSurface localization is
smooth and flat over its coefficient algebra, with no smoothness premise.

The geometric strategy is due to Ben Diamond and the collaborators cited
in solution.md. Prepared for fqlx with OpenAI ChatGPT assistance.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2IncidenceConeMinor

open MvPolynomial
open CycleQ2IncidenceUniversalChart CycleQ2IncidenceImageLine
  CycleQ2GeometricIncidenceProj CycleQ2IncidenceDehomogenizedChart
  CycleQ2IncidenceChartMinor CycleQ2RelativeJacobianPatch

variable {S : Type} [CommRing S] [Algebra ℂ S]

/-- Ordering the displayed equations as F,h leaves the actual quotient ideal unchanged. -/
theorem equationIdeal_eq (y : ParameterIndex → S) :
    Ideal.span (Set.range (equations y)) = pointEquations y := by
  change Ideal.span (Set.range (equations y)) =
    Ideal.span {pointEquationH y, pointEquationF y}
  apply congrArg Ideal.span
  ext a
  constructor
  · rintro ⟨j, rfl⟩
    fin_cases j <;> simp [CycleQ2IncidenceDehomogenizedChart.equations]
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rintro (rfl | rfl)
    · exact ⟨1, rfl⟩
    · exact ⟨0, rfl⟩

def equationQuotientEquiv (y : ParameterIndex → S) :
    EquationQuotient (equations y) ≃ₐ[S] PointSurface y :=
  Ideal.quotientEquivAlgOfEq S (equationIdeal_eq y)

@[simp] theorem equationQuotientEquiv_mk (y : ParameterIndex → S)
    (q : MvPolynomial (Fin 5) S) :
    equationQuotientEquiv y (Ideal.Quotient.mk (Ideal.span (Set.range (equations y))) q) =
      surfaceQuotient y q :=
  Ideal.quotientEquivAlgOfEq_mk S (equationIdeal_eq y) q

/-- The image of the presentation Jacobian is the original geometric minor. -/
theorem jacobian_image (y : ParameterIndex → S)
    (p : Fin 2 → Fin 5) (hp : Function.Injective p) :
    equationQuotientEquiv y (prePresentation (equations y) p hp).jacobian =
      surfaceQuotient y (surfaceMinor y (p 0) (p 1)) := by
  rw [prePresentation_jacobian, equationQuotientEquiv_mk]
  rfl

/-- Localization preserves the exact quotient and its original S-coefficients. -/
def coneMinorAlgEquiv (y : ParameterIndex → S)
    (p : Fin 2 → Fin 5) (hp : Function.Injective p) :
    JacobianPatch (equations y) p hp ≃ₐ[S]
      Localization.Away (surfaceQuotient y (surfaceMinor y (p 0) (p 1))) :=
  IsLocalization.algEquivOfAlgEquiv
    (M := Submonoid.powers (prePresentation (equations y) p hp).jacobian)
    (T := Submonoid.powers (surfaceQuotient y (surfaceMinor y (p 0) (p 1))))
    (JacobianPatch (equations y) p hp)
    (Localization.Away (surfaceQuotient y (surfaceMinor y (p 0) (p 1))))
    (equationQuotientEquiv y) (by
      rw [Submonoid.map_powers]
      exact congrArg Submonoid.powers (jacobian_image y p hp))

@[simp] theorem coneMinorAlgEquiv_base (y : ParameterIndex → S)
    (p : Fin 2 → Fin 5) (hp : Function.Injective p)
    (a : EquationQuotient (equations y)) :
    coneMinorAlgEquiv y p hp
        (algebraMap (EquationQuotient (equations y)) (JacobianPatch (equations y) p hp) a) =
      algebraMap (PointSurface y)
        (Localization.Away (surfaceQuotient y (surfaceMinor y (p 0) (p 1))))
        (equationQuotientEquiv y a) :=
  IsLocalization.algEquivOfAlgEquiv_eq _ a

@[simp] theorem coneMinorAlgEquiv_polynomial (y : ParameterIndex → S)
    (p : Fin 2 → Fin 5) (hp : Function.Injective p)
    (q : MvPolynomial (Fin 5) S) :
    coneMinorAlgEquiv y p hp
        (algebraMap (EquationQuotient (equations y)) (JacobianPatch (equations y) p hp)
          (Ideal.Quotient.mk (Ideal.span (Set.range (equations y))) q)) =
      algebraMap (PointSurface y)
        (Localization.Away (surfaceQuotient y (surfaceMinor y (p 0) (p 1))))
        (surfaceQuotient y q) := by
  rw [coneMinorAlgEquiv_base, equationQuotientEquiv_mk]

/-- The actual cone minor patch is smooth over the original coefficient algebra. -/
theorem coneMinor_smooth (y : ParameterIndex → S)
    (p : Fin 2 → Fin 5) (hp : Function.Injective p) :
    Algebra.Smooth S
      (Localization.Away (surfaceQuotient y (surfaceMinor y (p 0) (p 1)))) := by
  letI : Algebra.Smooth S (JacobianPatch (equations y) p hp) :=
    CycleQ2RelativeJacobianPatch.patch_smooth (equations y) p hp
  exact Algebra.Smooth.of_equiv (coneMinorAlgEquiv y p hp)

theorem coneMinor_flat (y : ParameterIndex → S)
    (p : Fin 2 → Fin 5) (hp : Function.Injective p) :
    Module.Flat S
      (Localization.Away (surfaceQuotient y (surfaceMinor y (p 0) (p 1)))) := by
  letI := coneMinor_smooth y p hp
  infer_instance

end CycleQ2IncidenceConeMinor

end

#print axioms CycleQ2IncidenceConeMinor.jacobian_image
#print axioms CycleQ2IncidenceConeMinor.coneMinorAlgEquiv
#print axioms CycleQ2IncidenceConeMinor.coneMinor_smooth
#print axioms CycleQ2IncidenceConeMinor.coneMinor_flat
