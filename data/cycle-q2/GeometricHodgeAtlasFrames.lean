import Proposal.GeometricHodgeAtlasLine
import Proposal.GeometricSeedSectionSheafLocal

/-!
# Sections and local frames of an atlas line bundle

The kernel sheaf has the expected compatible tuples of functions on each
intersection with a chart. On any open inside a single chart, its chosen
coordinate gives a linear isomorphism with the actual structure ring.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2HodgeAtlasLine

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite
open CycleQ2SeedSectionSheafLimits
open CycleQ2SeedSectionSheafLocal (moduleRes moduleRes_app)

variable {X : Scheme.{0}} {I : Type} {U : I → X.Opens} (g : Transition U)

def component (i : I) (V : X.Opens) (s : Γ(line g,V)) : Γ(X,V ⊓ U i) :=
  (projection g i).app V s

theorem component_injective (V : X.Opens) (s t : Γ(line g,V))
    (h : ∀ i, component g i V s = component g i V t) : s = t := by
  apply (sectionKernelEquiv (difference g) V).injective
  apply Subtype.ext
  rw [sectionKernelEquiv_val, sectionKernelEquiv_val]
  apply (sectionProductEquiv (Pieces U) V).injective
  funext i
  rw [sectionProductEquiv_apply, sectionProductEquiv_apply]
  exact h i

abbrev triple (V : X.Opens) (i j : I) := V ⊓ (U i ⊓ U j)

def Compatible (V : X.Opens) (s : ∀ i, Γ(X,V ⊓ U i)) : Prop :=
  ∀ i j, restrictRing (X := X) (inf_le_inf_left V (inf_le_left : U i ⊓ U j ≤ U i)) (s i) =
    (g.unit i j (triple (U := U) V i j) (inf_le_right.trans inf_le_left) (inf_le_right.trans inf_le_right) :
      Γ(X,triple (U := U) V i j)) * restrictRing (X := X) (inf_le_inf_left V inf_le_right) (s j)

private theorem restricted_unit (i j : I) (V : X.Opens) :
    restrictRing (X := X) (show triple (U := U) V i j ≤ U i ⊓ U j from inf_le_right)
        (g.unit i j (U i ⊓ U j) inf_le_left inf_le_right : Γ(X,_)) =
      g.unit i j (triple (U := U) V i j) (inf_le_right.trans inf_le_left) (inf_le_right.trans inf_le_right) :=
  congrArg Units.val (g.restrict i j inf_le_left inf_le_right (show triple (U := U) V i j ≤ _ from inf_le_right))

theorem component_compatible (V : X.Opens) (s : Γ(line g,V)) : Compatible g V (component g · V s) := by
  intro i j
  have h := congrArg (fun f : line g ⟶ patchModule (U i ⊓ U j) => f.app V s) (projection_compatible g i j)
  change restrictRing (X := X) _ (component g i V s) = restrictRing (X := X) _ _ * restrictRing (X := X) _ (component g j V s) at h
  rwa [restricted_unit] at h

def pack (V : X.Opens) (s : ∀ i, Γ(X,V ⊓ U i)) (hs : Compatible g V s) : Γ(line g,V) :=
  (sectionKernelEquiv (difference g) V).symm
    ⟨(sectionProductEquiv (Pieces U) V).symm s, by
      change (difference g).app V _ = 0
      apply (sectionProductEquiv (Pairs U) V).injective
      funext p
      rw [sectionProductEquiv_apply, map_zero]
      change (difference g ≫ Pi.π (Pairs U) p).app V _ = 0
      rw [difference, Pi.lift_π]
      let d := (sectionProductEquiv (Pieces U) V).symm s
      change restrictRing (inf_le_inf_left V (inf_le_left : U p.1 ⊓ U p.2 ≤ U p.1))
          ((Pi.π (Pieces U) p.1).app V d) -
        restrictRing (show triple (U := U) V p.1 p.2 ≤ U p.1 ⊓ U p.2 from inf_le_right)
          (g.unit p.1 p.2 _ inf_le_left inf_le_right : Γ(X,_)) *
        restrictRing (inf_le_inf_left V (inf_le_right : U p.1 ⊓ U p.2 ≤ U p.2))
          ((Pi.π (Pieces U) p.2).app V d) = 0
      apply sub_eq_zero.mpr
      dsimp only [d]
      rw [sectionProductEquiv_symm_apply, sectionProductEquiv_symm_apply, restricted_unit]
      exact hs _ _⟩

@[simp] theorem component_pack (V : X.Opens) (s : ∀ i, Γ(X,V ⊓ U i)) (hs : Compatible g V s) (i : I) :
    component g i V (pack g V s hs) = s i := by
  change (Pi.π (Pieces U) i).app V ((kernel.ι (difference g)).app V _) = s i
  rw [pack, sectionKernelEquiv_symm_val, sectionProductEquiv_symm_apply]

theorem component_add (i : I) (V : X.Opens) (s t : Γ(line g,V)) :
    component g i V (s + t) = component g i V s + component g i V t :=
  ((projection g i).app V).hom.map_add s t

theorem component_smul (i : I) (V : X.Opens) (a : Γ(X,V)) (s : Γ(line g,V)) :
    component g i V (a • s) = restrictRing (show V ⊓ U i ≤ V from inf_le_left) a * component g i V s :=
  ((projection g i).val.app (op V)).hom.map_smul a s

def coordinate (i : I) (V : X.Opens) (hi : V ≤ U i) : Γ(line g,V) →ₗ[Γ(X,V)] Γ(X,V) where
  toFun s := restrictRing (X := X) (le_inf le_rfl hi) (component g i V s)
  map_add' s t := by simp [component]
  map_smul' a s := by
    change restrictRing (le_inf le_rfl hi) (component g i V (a • s)) =
      a * restrictRing (le_inf le_rfl hi) (component g i V s)
    rw [component_smul, map_mul, restrictRing_comp, restrictRing_self]

theorem coordinate_restrict (i : I) {V W : X.Opens} (hi : V ≤ U i) (hW : W ≤ V) (s : Γ(line g,V)) :
    coordinate g i W (hW.trans hi) (moduleRes (line g) hW s) = restrictRing (X := X) hW (coordinate g i V hi s) := by
  change restrictRing (X := X) _ ((projection g i).app W (moduleRes (line g) hW s)) =
    restrictRing (X := X) hW (restrictRing (X := X) _ ((projection g i).app V s))
  rw [← moduleRes_app]
  change restrictRing (X := X) _ (restrictRing (X := X) _ _) = _
  rw [restrictRing_comp, restrictRing_comp]
  rfl

theorem coordinate_transition (i j : I) (V : X.Opens) (hi : V ≤ U i) (hj : V ≤ U j) (s : Γ(line g,V)) :
    coordinate g i V hi s = (g.unit i j V hi hj : Γ(X,V)) * coordinate g j V hj s := by
  have hV : V ≤ triple (U := U) V i j := le_inf le_rfl (le_inf hi hj)
  have h := congrArg (restrictRing (X := X) hV) (component_compatible g V s i j)
  rw [map_mul, restrictRing_comp, restrictRing_comp] at h
  have hu := congrArg Units.val (g.restrict i j (inf_le_right.trans inf_le_left)
    (inf_le_right.trans inf_le_right) hV)
  change restrictRing (X := X) hV _ = _ at hu
  rw [hu] at h
  exact h

private def localFamily (i : I) (V : X.Opens) (hi : V ≤ U i) (a : Γ(X,V)) (j : I) : Γ(X,V ⊓ U j) :=
  (g.unit j i _ inf_le_right (inf_le_left.trans hi) : Γ(X,_)) * restrictRing (X := X) inf_le_left a

private theorem localFamily_compatible (i : I) (V : X.Opens) (hi : V ≤ U i) (a : Γ(X,V)) :
    Compatible g V (localFamily g i V hi a) := by
  intro j k
  unfold localFamily
  simp only [map_mul, restrictRing_comp]
  have hr (l : I) (h : triple (U := U) V j k ≤ V ⊓ U l) :
      restrictRing (X := X) h (g.unit l i (V ⊓ U l) inf_le_right (inf_le_left.trans hi) : Γ(X,_)) =
      (g.unit l i (triple (U := U) V j k) (h.trans inf_le_right) (inf_le_left.trans hi) : Γ(X,triple (U := U) V j k)) :=
    congrArg Units.val (g.restrict l i inf_le_right (inf_le_left.trans hi) h)
  rw [hr, hr, ← mul_assoc]
  exact congrArg (fun u : Γ(X,triple (U := U) V j k)ˣ => u.val * restrictRing (X := X) inf_le_left a)
    (g.compose j k i _ (inf_le_right.trans inf_le_left) (inf_le_right.trans inf_le_right)
      (inf_le_left.trans hi)).symm

def fromCoordinate (i : I) (V : X.Opens) (hi : V ≤ U i) (a : Γ(X,V)) : Γ(line g,V) :=
  pack g V (localFamily g i V hi a) (localFamily_compatible g i V hi a)

theorem coordinate_fromCoordinate (i : I) (V : X.Opens) (hi : V ≤ U i) (a : Γ(X,V)) :
    coordinate g i V hi (fromCoordinate g i V hi a) = a := by
  change restrictRing (X := X) _ (component g i V (fromCoordinate g i V hi a)) = a
  rw [fromCoordinate, component_pack, localFamily, g.self, Units.val_one, one_mul, restrictRing_comp, restrictRing_self]

theorem component_fromCoordinate (i j : I) (V : X.Opens) (hi : V ≤ U i) (s : Γ(line g,V)) :
    component g j V (fromCoordinate g i V hi (coordinate g i V hi s)) = component g j V s := by
  let W := V ⊓ U j
  have h := coordinate_transition g j i W inf_le_right (inf_le_left.trans hi) (moduleRes (line g) inf_le_left s)
  rw [coordinate_restrict g i hi inf_le_left] at h
  change restrictRing (X := X) _ ((projection g j).app W (moduleRes (line g) inf_le_left s)) = _ at h
  rw [← moduleRes_app] at h
  change restrictRing (X := X) _ (restrictRing (X := X) _ (component g j V s)) = _ at h
  rw [restrictRing_comp, restrictRing_self] at h
  simpa only [fromCoordinate, component_pack, localFamily] using h.symm

def frame (i : I) (V : X.Opens) (hi : V ≤ U i) : Γ(line g,V) ≃ₗ[Γ(X,V)] Γ(X,V) :=
  LinearEquiv.ofBijective (coordinate g i V hi) ⟨fun s t h => component_injective g V s t
    (fun j => (component_fromCoordinate g i j V hi s).symm.trans
      ((congrArg (fun a => component g j V (fromCoordinate g i V hi a)) h).trans
        (component_fromCoordinate g i j V hi t))), fun a => ⟨_, coordinate_fromCoordinate g i V hi a⟩⟩

end CycleQ2HodgeAtlasLine
end

#print axioms CycleQ2HodgeAtlasLine.frame
