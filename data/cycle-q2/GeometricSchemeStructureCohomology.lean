import Proposal.GeometricClosedEmbeddingCohomology

/-!
# Structure-sheaf cohomology under a scheme isomorphism

The actual scheme section isomorphisms identify the target structure sheaf
with the direct image of the source structure sheaf. Transporting Ext and
then the terminal-open comparison gives ordinary cohomology in every degree.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2SchemeStructureCohomology

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open CycleQ2GeometricProjectiveHOne (structureAdditiveSheaf additiveForget)
open CycleQ2ClosedEmbeddingSheafExact (push)
open CycleQ2ClosedEmbeddingCohomology (pushHEquiv)
open CycleQ2InjectiveCech (AbSheaf)
open CycleQ2GeometricSheafCohomologyRestriction (terminalCohomologyEquiv)

local instance (X : TopCat.{0}) : HasExt.{1} (AbSheaf X) := HasExt.standard _

variable {X Y : Scheme.{0}} (e : X ≅ Y)

def structurePushIso : structureAdditiveSheaf Y ≅
    (push e.hom.base).obj (structureAdditiveSheaf X) := by
  apply ObjectProperty.isoMk _
  refine NatIso.ofComponents (fun U => additiveForget.mapIso (asIso (e.hom.app U.unop))) ?_
  intro U V f
  change additiveForget.map (Y.presheaf.map f) ≫ additiveForget.map (e.hom.app V.unop) =
    additiveForget.map (e.hom.app U.unop) ≫ additiveForget.map _
  rw [← Functor.map_comp, ← Functor.map_comp]
  exact congrArg additiveForget.map (e.hom.naturality f)

def openCohomology (n : ℕ) :
    (structureAdditiveSheaf X).H' n ⊤ ≃+ (structureAdditiveSheaf Y).H' n ⊤ :=
  (pushHEquiv e.hom.base e.hom.isClosedEmbedding (structureAdditiveSheaf X) n).trans
    ((((Sheaf.cohomologyPresheafFunctor _ n).mapIso (structurePushIso e).symm).app
      (op ⊤)).addCommGroupIsoToAddEquiv)

def ordinaryCohomology (n : ℕ) :
    (structureAdditiveSheaf X).H n ≃+ (structureAdditiveSheaf Y).H n :=
  (terminalCohomologyEquiv _ (structureAdditiveSheaf X) ⊤ isTerminalTop n).symm.trans
    ((openCohomology e n).trans
      (terminalCohomologyEquiv _ (structureAdditiveSheaf Y) ⊤ isTerminalTop n))

end CycleQ2SchemeStructureCohomology
end

#print axioms CycleQ2SchemeStructureCohomology.structurePushIso
#print axioms CycleQ2SchemeStructureCohomology.ordinaryCohomology
