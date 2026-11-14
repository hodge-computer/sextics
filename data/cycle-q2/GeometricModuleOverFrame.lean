import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Proposal.GeometricModuleLocalIso

/-!
# Evaluating an actual over-site frame on every subopen

An isomorphism from the restriction of a module sheaf to the unit module
on an open's over-site supplies the natural family of linear equivalences
used by the actual two-open module gluing theorem. The component and
inverse-generator formulas use the original isomorphism maps directly.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
universe u

namespace CycleQ2GeometricModuleOverFrame

open CategoryTheory Opposite TopologicalSpace
open CycleQ2GeometricModuleLocalIso

variable {X : TopCat.{u}} {R : X.Sheaf RingCat.{u}}
variable {M : SheafOfModules.{u} R} {U : Opens X}

/-- Evaluate the genuine over-site isomorphism at each subopen. -/
def patchIsoOfOverFrame
    (e : M.over U ≅ SheafOfModules.unit (R.over U)) :
    PatchIso M (SheafOfModules.unit R) U where
  app O hO := ((SheafOfModules.evaluation (R.over U)
    (op (Over.mk (homOfLE hO)))).mapIso e).toLinearEquiv
  naturality {O P} hPO hO s := by
    let f : Over.mk (homOfLE (hPO.trans hO)) ⟶ Over.mk (homOfLE hO) :=
      Over.homMk (homOfLE hPO) (Subsingleton.elim _ _)
    exact (PresheafOfModules.naturality_apply e.hom.val f.op s).symm

@[simp] theorem patchIsoOfOverFrame_app
    (e : M.over U ≅ SheafOfModules.unit (R.over U))
    (O : Opens X) (hO : O ≤ U) (s : M.val.obj (op O)) :
    (patchIsoOfOverFrame e).app O hO s =
      e.hom.val.app (op (Over.mk (homOfLE hO))) s := rfl

@[simp] theorem patchIsoOfOverFrame_symm_app
    (e : M.over U ≅ SheafOfModules.unit (R.over U))
    (O : Opens X) (hO : O ≤ U) (a : R.obj.obj (op O)) :
    ((patchIsoOfOverFrame e).app O hO).symm a =
      e.inv.val.app (op (Over.mk (homOfLE hO))) a := rfl

/-- The local generator is exactly the image of one under the original
inverse over-site isomorphism, with no intervening comparison map. -/
theorem patchIsoOfOverFrame_inverse_one
    (e : M.over U ≅ SheafOfModules.unit (R.over U))
    (O : Opens X) (hO : O ≤ U) :
    ((patchIsoOfOverFrame e).app O hO).symm (1 : R.obj.obj (op O)) =
      e.inv.val.app (op (Over.mk (homOfLE hO))) (1 : R.obj.obj (op O)) := rfl

#print axioms patchIsoOfOverFrame
#print axioms patchIsoOfOverFrame_inverse_one

end CycleQ2GeometricModuleOverFrame
end
