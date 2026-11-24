import Proposal.GeometricLiteralAffineCotangent

/-!
# The original global epsilon differential in the canonical cotangent sheaf

The actual dual-number structure morphism supplies the global epsilon
parameter. Its restriction to every original native chart is the original
native epsilon. The genuine closed-fibre pullback unit carries its
universal differential to the canonical restricted cotangent sheaf and
therefore defines a global structure-module morphism into that sheaf.
Faithfulness and the full global exact sequence are further obligations.

Prepared for fqlx with OpenAI ChatGPT assistance; see solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralCotangentEpsilon

open scoped DualNumber
open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry HomogeneousLocalization
  CycleQ2LiteralGradedDeformation CycleQ2LiteralProjectiveDeformation
  CycleQ2LiteralProjectiveDualFamily CycleQ2LiteralProjectiveIntersections
  CycleQ2LiteralProjectiveIntersectionKernel CycleQ2LiteralProjectiveCotangent
  CycleQ2LiteralAffineCotangent CycleQ2GeometricDifferentialSheaf

def globalDualCoefficient : ℂ[ε] →+* Γ(projectiveDeformation, ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of ℂ[ε])).inv ≫ firstOrderStructure.appTop).hom

def totalEpsilon : Γ(projectiveDeformation, ⊤) := globalDualCoefficient ε

theorem totalEpsilon_square : totalEpsilon * totalEpsilon = 0 := by
  rw [totalEpsilon, ← map_mul, DualNumber.eps_mul_eps, map_zero]

def nativeDualCoefficient (s : Finset Vertex) : ℂ[ε] →+* ThickRing s :=
  (fromZeroRingHom deformationGrade (Submonoid.powers (thickProduct s))).comp
    dualCoefficient.toRingHom

theorem nativeDualCoefficient_epsilon (s : Finset Vertex) :
    nativeDualCoefficient s ε = nativeEpsilon s := by
  change fromZeroRingHom deformationGrade _ (dualCoefficient ε) = _
  rw [dualCoefficient_epsilon]
  rfl

theorem native_firstOrderStructure (s : Finset Vertex) (hs : s.Nonempty) :
    thickAffineMap s hs ≫ firstOrderStructure =
      Spec.map (CommRingCat.ofHom (nativeDualCoefficient s)) := by
  rw [firstOrderStructure, Proj.awayι_toSpecZero_assoc, ← Spec.map_comp]
  rfl

theorem totalEpsilon_native (s : Finset Vertex) (hs : s.Nonempty) :
    (thickAffineMap s hs).appTop totalEpsilon =
      (Scheme.ΓSpecIso (CommRingCat.of (ThickRing s))).inv (nativeEpsilon s) := by
  have h := congrArg
    (fun f : Spec (CommRingCat.of (ThickRing s)) ⟶ Spec (CommRingCat.of ℂ[ε]) =>
      f.appTop ((Scheme.ΓSpecIso (CommRingCat.of ℂ[ε])).inv ε))
    (native_firstOrderStructure s hs)
  have hn := ConcreteCategory.congr_hom (C := CommRingCat)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (nativeDualCoefficient s))).symm
    (ε : ℂ[ε])
  have he := congrArg
    (fun x : ThickRing s => (Scheme.ΓSpecIso (CommRingCat.of (ThickRing s))).inv x)
    (nativeDualCoefficient_epsilon s)
  exact h.trans (hn.trans he)

def restrictedEpsilonDifferential : restrictedCotangentSheaf.val.obj (op ⊤) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction closedFiber).unit.app
    totalDifferentialSheaf).val.app (op ⊤)
      ((universalDifferential projectiveDeformation.sheaf totalGlobalCoefficient).d totalEpsilon)

def epsilonSections : restrictedCotangentSheaf.sections :=
  restrictedCotangentSheaf.val.sectionsMk
    (fun U => restrictedCotangentSheaf.val.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op
      restrictedEpsilonDifferential)
    (fun U V f => by rw [← restrictedCotangentSheaf.val.map_comp_apply]; congr 2)

def epsilonInclusion : SheafOfModules.unit (ringSheaf ClosedSurface.sheaf) ⟶
    restrictedCotangentSheaf := restrictedCotangentSheaf.unitHomEquiv.symm epsilonSections

theorem epsilonInclusion_apply (U : ClosedSurface.Opens) (a : Γ(ClosedSurface, U)) :
    epsilonInclusion.val.app (op U) a =
      a • restrictedCotangentSheaf.val.map (homOfLE (show U ≤ ⊤ from le_top)).op
        restrictedEpsilonDifferential := rfl

theorem epsilonInclusion_global_one :
    epsilonInclusion.val.app (op ⊤) (1 : Γ(ClosedSurface, ⊤)) =
      restrictedEpsilonDifferential := by
  rw [epsilonInclusion_apply, one_smul]
  change restrictedCotangentSheaf.val.presheaf.map (𝟙 (op ⊤)) restrictedEpsilonDifferential = _
  exact congrArg
    (fun f : restrictedCotangentSheaf.val.presheaf.obj (op ⊤) ⟶
      restrictedCotangentSheaf.val.presheaf.obj (op ⊤) => f restrictedEpsilonDifferential)
    (restrictedCotangentSheaf.val.presheaf.map_id (op ⊤))

end CycleQ2LiteralCotangentEpsilon

end

#print axioms CycleQ2LiteralCotangentEpsilon.totalEpsilon_native
#print axioms CycleQ2LiteralCotangentEpsilon.epsilonInclusion_global_one
