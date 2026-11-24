import Proposal.GeometricLiteralMovingResidueExact
import Proposal.GeometricLiteralMovingResidueBoundary
import Proposal.GeometricLiteralMovingResidueBasis

/-!
# The surface differential map into the moving residue quotient

A one-form on the surface maps locally to its wedge with the logarithmic
differential of the moving Cartier equation. Frame changes add a regular
two-form. The local residue maps therefore define one additive sheaf morphism.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2LiteralMovingResidueGluing
section QuotientFrames

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
  CycleQ2GeometricDifferentialSheaf CycleQ2GeometricExteriorSheaf
  CycleQ2LiteralNativeDifferentialSections CycleQ2LiteralMovingResidueFaces
  CycleQ2LiteralMovingResiduePole
  CycleQ2SeedSectionDivisorTransitions CycleQ2SeedSectionAffineInjective
open CycleQ2CanonicalResidueSheaf (CanonicalForms)
open CycleQ2GeometricModuleLocalIso (addSheaf)
open CycleQ2LiteralMovingResidueExact (regularInclusion residueQuotient)

variable (t : Fin 3 → ℂ) (ht : ∀ i, ChartRegular t i) {W : Surface.Opens}

open CycleQ2LiteralMovingResidueBasis (FramedAffine)
open CycleQ2LiteralMovingResidueBoundary (lift lift_restrict)

private def residueValue (j : FrameData W) (β : OneForms W) : (residueQuotient t).obj.obj (op W) :=
  (cokernel.π (regularInclusion t)).hom.app (op W) (lift t ht j β)

/-- The regular last term in the ordered pole identity is zero in the quotient. -/
private theorem residueValue_face (j k : FrameData W) (β γ : OneForms W) :
    residueValue t ht k γ - residueValue t ht k (β+γ) + residueValue t ht j β = 0 := by
  let π := (cokernel.π (regularInclusion t)).hom.app (op W)
  let ω := wedgeSection Surface.sheaf DifferentialSheaf.val 2 W
    ![sheafLogDifferential W (positiveTransition j k), β]
  have hq : π ((regularInclusion t).hom.app (op W) ω) = 0 :=
    congrArg (fun f : addSheaf CanonicalForms ⟶ residueQuotient t => f.hom.app (op W) ω)
      (cokernel.condition (regularInclusion t))
  have h := congrArg π (CycleQ2LiteralMovingResidueBoundary.lift_boundary t ht j k β γ (β+γ) rfl)
  change π (lift t ht k γ - lift t ht k (β+γ) + lift t ht j β) =
    π ((regularInclusion t).hom.app (op W) ω) at h
  rw [hq, map_add, map_sub] at h
  exact h

/-- The class of the logarithmic pole on the original pivot open. -/
def framedResidue (j : FrameData W) : OneForms W →+ (residueQuotient t).obj.obj (op W) :=
  AddMonoidHom.mk' (residueValue t ht j) (by
    intro β γ
    have h := residueValue_face t ht j j β γ
    calc
      _ = residueValue t ht j (β + γ) +
            (residueValue t ht j γ - residueValue t ht j (β + γ) + residueValue t ht j β) := by rw [h,add_zero]
      _ = _ := by abel)

theorem framedResidue_apply (j : FrameData W) (β : OneForms W) :
    framedResidue t ht j β = (cokernel.π (regularInclusion t)).hom.app (op W)
      (lift t ht j β) := rfl

/-- Changing a moving ideal basis adds a regular logarithmic two-form. -/
theorem framedResidue_change (j k : FrameData W) (β : OneForms W) :
    framedResidue t ht j β = framedResidue t ht k β :=
  add_left_cancel ((residueValue_face t ht j k β 0).trans
    (residueValue_face t ht k k β 0).symm)

theorem framedResidue_restrict (j : FrameData W) {V : Surface.Opens} (h : V ≤ W) (k : FrameData V)
    (β : OneForms W) :
    (residueQuotient t).obj.map (homOfLE h).op (framedResidue t ht j β) =
      framedResidue t ht k (DifferentialSheaf.val.map (homOfLE h).op β) := by
  rw [← framedResidue_change t ht (j.restrict h) k, framedResidue_apply, framedResidue_apply,
    ← NatTrans.naturality_apply]
  exact congrArg ((cokernel.π (regularInclusion t)).hom.app (op V)) (lift_restrict t ht j h β)

/-- The genuine map from one-forms on the original surface to the quotient sheaf. -/
def surfaceResidue : addSheaf DifferentialSheaf ⟶ residueQuotient t :=
  CycleQ2LiteralMovingResidueBasis.extend (F := addSheaf DifferentialSheaf)
    (fun W => framedResidue t ht W.frame)
    (fun W V h β => (framedResidue_restrict t ht W.frame h V.frame β).symm)

theorem surfaceResidue_basis (W : FramedAffine) (β : OneForms W.carrier) :
    (surfaceResidue t ht).hom.app (op W.carrier) β = framedResidue t ht W.frame β :=
  CycleQ2LiteralMovingResidueBasis.extend_apply _ _ W β

/-- The same formula holds on every framed open, even when it is not affine. -/
theorem surfaceResidue_app (j : FrameData W) (β : OneForms W) :
    (surfaceResidue t ht).hom.app (op W) β = framedResidue t ht j β := by
  let A := {a : FramedAffine // a.carrier ≤ W}
  have hc : W ≤ ⨆ a : A, a.val.carrier := by
    intro x hx
    obtain ⟨V, ⟨B,rfl⟩, hxB, hBW⟩ := Opens.isBasis_iff_nbhd.mp
      CycleQ2LiteralMovingResidueBasis.isBasis_framedAffine hx
    exact Opens.mem_iSup.mpr ⟨⟨B,hBW⟩, hxB⟩
  apply (residueQuotient t).eq_of_locally_eq' (fun a : A => a.val.carrier) W
    (fun a => homOfLE a.property) hc
  intro a
  rw [← NatTrans.naturality_apply, surfaceResidue_basis]
  exact (framedResidue_restrict t ht j a.property a.val.frame β).symm

end QuotientFrames
end CycleQ2LiteralMovingResidueGluing
end
#print axioms CycleQ2LiteralMovingResidueGluing.framedResidue_restrict
#print axioms CycleQ2LiteralMovingResidueGluing.framedResidue_change

#print axioms CycleQ2LiteralMovingResidueGluing.surfaceResidue_app
