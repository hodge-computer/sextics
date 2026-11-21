import Proposal.GeometricTwistedModuleCore
import Proposal.GeometricSeedSectionSheafLimits

/-!
# Gluing a line bundle in its coordinate frames

On a scheme, an overlap cocycle of invertible functions defines the kernel of
the difference map between the products of the actual structure modules on
the patches and on their intersections. Sections on the patches are functions
on the literal intersections with the opens.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2HodgeAtlasLine

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite
open CycleQ2GeometricProjectiveCurve.Twisted
open CycleQ2SeedSectionSheafLimits

variable {X : Scheme.{0}}


abbrev restrictRing {V W : X.Opens} (h : W ≤ V) : Γ(X,V) →+* Γ(X,W) :=
  (X.presheaf.map (homOfLE h).op).hom

theorem restrictRing_comp {V W Z : X.Opens} (hW : W ≤ V) (hZ : Z ≤ W) (a : Γ(X,V)) :
    restrictRing hZ (restrictRing hW a) = restrictRing (hZ.trans hW) a := by
  exact res_comp X.sheaf hW hZ a

theorem restrictRing_self (V : X.Opens) (a : Γ(X,V)) : restrictRing (le_refl V) a = a :=
  res_self X.sheaf V a

private abbrev patchAction (U V : X.Opens) : Module (Γ(X,V)) (Γ(X,V ⊓ U)) :=
  Module.compHom (Γ(X,V ⊓ U)) (restrictRing (X := X) (show V ⊓ U ≤ V from inf_le_left))

def patchModule (U : X.Opens) : X.Modules := by
  letI (V : X.Opensᵒᵖ) : Module (X.ringCatSheaf.obj.obj V) ((patchAdd X.sheaf U).obj.obj V) :=
    patchAction U V.unop
  exact ⟨PresheafOfModules.ofPresheaf (patchAdd X.sheaf U).obj (by
    intro V W f a b
    change Γ(X,V.unop) at a
    change Γ(X,V.unop ⊓ U) at b
    have h : W.unop ≤ V.unop := leOfHom f.unop
    change restrictRing (X := X) (inf_le_inf_right U h) (restrictRing (X := X) (show V.unop ⊓ U ≤ V.unop from inf_le_left) a * b) =
      restrictRing (X := X) inf_le_left (restrictRing (X := X) h a) * restrictRing (X := X) (inf_le_inf_right U h) b
    rw [map_mul, restrictRing_comp, restrictRing_comp]), (patchAdd X.sheaf U).property⟩

def patchRestrict {U V : X.Opens} (h : V ≤ U) : patchModule U ⟶ patchModule V :=
  ⟨PresheafOfModules.homMk (patchAddRestriction X.sheaf h).hom (by
    intro W r s
    change Γ(X,W.unop) at r
    change Γ(X,W.unop ⊓ U) at s
    change restrictRing (X := X) (inf_le_inf_left W.unop h) (restrictRing (X := X) (show W.unop ⊓ U ≤ W.unop from inf_le_left) r * s) = _
    change _ = restrictRing (X := X) inf_le_left r * restrictRing (X := X) (inf_le_inf_left W.unop h) s
    rw [map_mul, restrictRing_comp])⟩

def patchMultiply (U : X.Opens) (a : Γ(X,U)) : patchModule U ⟶ patchModule U :=
  ⟨PresheafOfModules.homMk (patchMul X.sheaf U a).hom (by
    intro V r s
    change Γ(X,V.unop) at r
    change Γ(X,V.unop ⊓ U) at s
    change restrictRing (X := X) (show V.unop ⊓ U ≤ U from inf_le_right) a * (restrictRing (X := X) (show V.unop ⊓ U ≤ V.unop from inf_le_left) r * s) =
      restrictRing (X := X) inf_le_left r * (restrictRing (X := X) inf_le_right a * s)
    ring)⟩

variable {I : Type} (U : I → X.Opens)

/-- Transition functions in the convention sᵢ = gᵢⱼ sⱼ. -/
structure Transition where
  unit (i j : I) (V : X.Opens) (hi : V ≤ U i) (hj : V ≤ U j) : Γ(X,V)ˣ
  self (i : I) (V : X.Opens) (hi : V ≤ U i) : unit i i V hi hi = 1
  compose (i j k : I) (V : X.Opens) (hi : V ≤ U i) (hj : V ≤ U j) (hk : V ≤ U k) :
    unit i j V hi hj * unit j k V hj hk = unit i k V hi hk
  restrict (i j : I) {V W : X.Opens} (hi : V ≤ U i) (hj : V ≤ U j) (hW : W ≤ V) :
    Units.map (restrictRing (X := X) hW).toMonoidHom (unit i j V hi hj) =
      unit i j W (hW.trans hi) (hW.trans hj)

abbrev Pieces := fun i : I => patchModule (U i)
abbrev Pairs := fun p : I × I => patchModule (U p.1 ⊓ U p.2)

variable {U} (g : Transition U)

def difference : (∏ᶜ Pieces U) ⟶ (∏ᶜ Pairs U) :=
  Pi.lift fun p : I × I =>
    Pi.π (Pieces U) p.1 ≫ patchRestrict (show U p.1 ⊓ U p.2 ≤ _ from inf_le_left) -
    Pi.π (Pieces U) p.2 ≫ patchRestrict inf_le_right ≫
      patchMultiply _ (g.unit p.1 p.2 _ inf_le_left inf_le_right : Γ(X,_))

def line : X.Modules := kernel (difference g)

def projection (i : I) : line g ⟶ patchModule (U i) :=
  kernel.ι (difference g) ≫ Pi.π (Pieces U) i

theorem projection_compatible (i j : I) :
    projection g i ≫ patchRestrict (show U i ⊓ U j ≤ _ from inf_le_left) =
      projection g j ≫ patchRestrict inf_le_right ≫
        patchMultiply _ (g.unit i j _ inf_le_left inf_le_right : Γ(X,_)) := by
  have h := congrArg (fun f => f ≫ Pi.π (Pairs U) (i,j)) (kernel.condition (difference g))
  simpa only [Category.assoc, difference, Pi.lift_π, Preadditive.comp_sub, zero_comp, sub_eq_zero,
    projection] using h

end CycleQ2HodgeAtlasLine
end

#print axioms CycleQ2HodgeAtlasLine.projection_compatible
