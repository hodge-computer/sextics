import Proposal.GeometricLiteralMovingResidueExact
import Proposal.GeometricLiteralCotangentTrace

/-!
# The residue trace and lifting through the moving pole sheaf

The surface residue applied to the connecting map on the actual moving
pole quotient gives a scalar. It vanishes exactly on the classes lifted
from H¹ of the pole sheaf. The target consists of residues of the canonical
classes that become zero on allowing poles along the moving divisor.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace CycleQ2LiteralMovingQuotientTrace

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite TopologicalSpace AlgebraicGeometry
  CycleQ2LiteralMovingResidueExact CycleQ2LiteralCotangentTrace
  CycleQ2SeedSectionAffineInjective

local instance (X : Scheme.{0}) :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}) := HasExt.standard _

local instance : HasExt.{1} (TopCat.Sheaf AddCommGrpCat.{0}
    (show TopCat from CycleQ2SeedProjectiveImageCocycle.Surface)) := HasExt.standard _

variable (t : Fin 3 → ℂ) (ht : ∀ i, ChartRegular t i)

/-- Surface residue of a class of the actual quotient by regular two-forms. -/
def residueTrace : (residueQuotient t).H' 1 ⊤ →+ ℂ :=
  algebraicTrace.toAddMonoidHom.comp (residueConnecting t ht ⊤)

theorem residueTrace_eq_zero_iff (x : (residueQuotient t).H' 1 ⊤) :
    residueTrace t ht x = 0 ↔
      ∃ y : (residueComplex t).X₂.H' 1 ⊤,
        y.comp (Ext.mk₀ (residueComplex t).g) (add_zero 1) = x := by
  change algebraicTrace (residueConnecting t ht ⊤ x) = 0 ↔ _
  rw [algebraicTrace_eq_zero_iff, residueConnecting_apply]
  constructor
  · exact Ext.covariant_sequence_exact₃ _ (residueShortExact t ht) x rfl
  · rintro ⟨y,rfl⟩
    rw [Ext.comp_assoc_of_second_deg_zero, ShortComplex.ShortExact.comp_extClass, Ext.comp_zero]

/-- The inverse image of a scalar under the surface trace specifies precisely
whether that scalar occurs as the residue of a moving quotient class. -/
theorem mem_trace_range_iff (c : ℂ) :
    c ∈ (residueTrace t ht).range ↔
      (algebraicTraceEquiv.symm c).comp (Ext.mk₀ (residueComplex t).f) (add_zero 2) = 0 := by
  constructor
  · rintro ⟨x,rfl⟩
    change (algebraicTraceEquiv.symm (algebraicTraceEquiv (residueConnecting t ht ⊤ x))).comp _ _ = 0
    rw [LinearEquiv.symm_apply_apply, residueConnecting_apply, Ext.comp_assoc_of_third_deg_zero,
      ShortComplex.ShortExact.extClass_comp, Ext.comp_zero]
  · intro h
    obtain ⟨x,hx⟩ := Ext.covariant_sequence_exact₁ _ (residueShortExact t ht)
      (algebraicTraceEquiv.symm c) h rfl
    refine ⟨x, ?_⟩
    change algebraicTraceEquiv (residueConnecting t ht ⊤ x) = c
    rw [residueConnecting_apply, hx, LinearEquiv.apply_symm_apply]

end CycleQ2LiteralMovingQuotientTrace
end

#print axioms CycleQ2LiteralMovingQuotientTrace.residueTrace_eq_zero_iff
#print axioms CycleQ2LiteralMovingQuotientTrace.mem_trace_range_iff
