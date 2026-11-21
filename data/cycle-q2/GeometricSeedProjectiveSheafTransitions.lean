import Proposal.GeometricSeedProjectiveOverlapComparisons

/-!
# Native sheaf transitions on the actual projective pair overlap

The four canonical comparisons transport the established image and dual
model transitions to the original restricted projective sheaves on the
spectrum of the actual overlap section ring. The dual model retains the
positive degree-four coordinate multiplier.

The resulting sheaf square uses the restrictions of the original
projectiveImageDualIso on both sides. Both transition morphisms commute
with restriction to every subopen of this fixed overlap spectrum.
Compatibility among independently constructed pair overlaps, the triple
cocycle, and the global internal-Hom identification remain separate steps.

Source-only draft: no Lean elaboration or kernel replay has been run.
Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md for
attribution of the geometric route and the protected certificate gap.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u v

namespace CycleQ2SeedProjectiveSheafTransitions

open CategoryTheory AlgebraicGeometry
open CycleQ2SeedProjectiveLocalizedDuality CycleQ2SeedProjectiveAffineOverlap
  CycleQ2SeedOverlapTransitionModels CycleQ2SeedProjectiveOverlapComparisons

/-- A model square transports through comparison isomorphisms while
retaining the two original vertical morphisms. -/
theorem conjugatedTransition_square
    {C : Type u} [Category.{v} C]
    {IL IR DL DR ML MR NL NR : C}
    (LI : IL ≅ ML) (RI : IR ≅ MR)
    (LD : DL ≅ NL) (RD : DR ≅ NR)
    (TI : ML ≅ MR) (TD : NL ≅ NR)
    (l : IL ⟶ DL) (r : IR ⟶ DR)
    (ml : ML ⟶ NL) (mr : MR ⟶ NR)
    (hL : l ≫ LD.hom = LI.hom ≫ ml)
    (hR : r ≫ RD.hom = RI.hom ≫ mr)
    (hmodel : TI.hom ≫ mr = ml ≫ TD.hom) :
    (LI ≪≫ TI ≪≫ RI.symm).hom ≫ r =
      l ≫ (LD ≪≫ TD ≪≫ RD.symm).hom := by
  apply (cancel_mono RD.hom).mp
  calc
    ((LI ≪≫ TI ≪≫ RI.symm).hom ≫ r) ≫ RD.hom =
        LI.hom ≫ TI.hom ≫ mr := by
      simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
      rw [hR]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
    _ = (LI.hom ≫ ml) ≫ TD.hom := by
      rw [hmodel, Category.assoc]
    _ = (l ≫ LD.hom) ≫ TD.hom :=
      congrArg (fun k => k ≫ TD.hom) hL.symm
    _ = (l ≫ (LD ≪≫ TD ≪≫ RD.symm).hom) ≫ RD.hom := by
      simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc,
        Iso.inv_hom_id, Category.comp_id]

/-- The image transition between the original restricted projective sheaves. -/
def imageOverlapTransition (i j : Fin 3) :
    leftImageOverlap i j ≅ rightImageOverlap i j :=
  leftImageComparison i j ≪≫ modelImageTransition i j ≪≫
    (rightImageComparison i j).symm

/-- The original restricted dual sheaves inherit the positive fourth-power
model transition through their canonical comparisons. -/
def dualOverlapTransition (i j : Fin 3) :
    leftDualOverlap i j ≅ rightDualOverlap i j :=
  leftDualComparison i j ≪≫ modelDualTransition i j ≪≫
    (rightDualComparison i j).symm

/-- The entire native sheaf square commutes with the original restricted dualities. -/
theorem nativeSheaf_square (i j : Fin 3) :
    (imageOverlapTransition i j).hom ≫ (rightOverlapDuality i j).hom =
      (leftOverlapDuality i j).hom ≫ (dualOverlapTransition i j).hom := by
  exact conjugatedTransition_square
    (leftImageComparison i j) (rightImageComparison i j)
    (leftDualComparison i j) (rightDualComparison i j)
    (modelImageTransition i j) (modelDualTransition i j)
    (leftOverlapDuality i j).hom (rightOverlapDuality i j).hom
    (leftModelDuality i j).hom (rightModelDuality i j).hom
    (leftComparison_naturality i j) (rightComparison_naturality i j)
    (modelTransition_square i j)

/-- The image transition commutes with all restrictions within this pair overlap. -/
theorem imageOverlapTransition_restrict (i j : Fin 3)
    {V W : (Spec (OverlapSections i j)).Opens} (f : V ⟶ W) :
    (leftImageOverlap i j).presheaf.map f.op ≫
        (imageOverlapTransition i j).hom.app V =
      (imageOverlapTransition i j).hom.app W ≫
        (rightImageOverlap i j).presheaf.map f.op :=
  (imageOverlapTransition i j).hom.mapPresheaf.naturality f.op

/-- The dual transition has the same native restriction compatibility. -/
theorem dualOverlapTransition_restrict (i j : Fin 3)
    {V W : (Spec (OverlapSections i j)).Opens} (f : V ⟶ W) :
    (leftDualOverlap i j).presheaf.map f.op ≫
        (dualOverlapTransition i j).hom.app V =
      (dualOverlapTransition i j).hom.app W ≫
        (rightDualOverlap i j).presheaf.map f.op :=
  (dualOverlapTransition i j).hom.mapPresheaf.naturality f.op

#print axioms conjugatedTransition_square
#print axioms imageOverlapTransition
#print axioms dualOverlapTransition
#print axioms nativeSheaf_square
#print axioms imageOverlapTransition_restrict
#print axioms dualOverlapTransition_restrict

end CycleQ2SeedProjectiveSheafTransitions
end
