import Proposal.GeometricProjectiveDescent

/-!
# A normalized finite cocycle representing a homogeneous triple section

The fourth coordinate open is empty. A section on the triple intersection
therefore extends by zero on the other three faces to a closed two-cochain.
The normalized finite-family extension retains the prescribed section.

Prepared for fqlx with OpenAI ChatGPT assistance; see solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralOrbitCoordinateClassRepresentative

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
  CycleQ2GeometricSheafLocalIso CycleQ2InjectiveCech CycleQ2FiniteInjectiveCech
  CycleQ2FourToFiniteCech CycleQ2ThreeOpenInjectiveComparison CycleQ2ThreeOpenCechH2
  CycleQ2CoordinateMVBinding CycleQ2GeometricProjectiveHOne CycleQ2CartierProjectiveCover
  CycleQ2ProjectiveCoordinateH2 CycleQ2GeometricHomogeneousWeight CycleQ2CartierSurfaceGrading

section
variable {X : TopCat.{0}} (F : AbSheaf X) (U : Fin 4 → Opens X)

private def firstFace (s : Sections F (TripleOpen (U 0) (U 1) (U 2))) :
    CycleQ2CechTwoToDerived.Two F U :=
  ⟨res F (le_inf (le_inf (inf_le_left.trans inf_le_left) inf_le_right)
    (le_inf (inf_le_left.trans inf_le_right) inf_le_right)) s, 0, 0, 0⟩

private theorem firstFace_closed (h : U 3 = ⊥)
    (s : Sections F (TripleOpen (U 0) (U 1) (U 2))) :
    CycleQ2CechTwoToDerived.d2 F U (firstFace F U s) = 0 := by
  have hO : ((U 0 ⊓ U 1) ⊓ U 2) ⊓ U 3 = ⊥ := by rw [h, inf_bot_eq]
  have hsub : Subsingleton (CycleQ2CechTwoToDerived.Three F U) := by
    change Subsingleton (F.obj.obj (op (((U 0 ⊓ U 1) ⊓ U 2) ⊓ U 3)))
    rw [hO]
    exact AddCommGrpCat.isZero_iff_subsingleton.mp (TopCat.Sheaf.isTerminalOfEmpty F).isZero
  exact hsub.elim _ _

private theorem selectedTriple_firstFace (s : Sections F (TripleOpen (U 0) (U 1) (U 2))) :
    selectedTriple U (extendTwo U (firstFace F U s)) 0 1 2 = s := by
  rw [selectedTriple_extendTwo_first]
  exact (res_comp F _ _ s).trans (res_self F _ s)

end

private abbrev coordinateSheaf (r : ℂ) := structureAdditiveSheaf (projectiveSurface r 1)

def representative (r : ℂ) (q : HomogeneousCoordinateTop r) :
    Two (coordinateSheaf r) (coordinateFamily r) :=
  extendTwo (coordinateFamily r) (firstFace (coordinateSheaf r) _ (tripleSections r 1 q))

theorem representative_normalized (r : ℂ) (q : HomogeneousCoordinateTop r) :
    NormalizedTwo _ _ (representative r q) := extendTwo_normalized _ _

theorem representative_closed (r : ℂ) (q : HomogeneousCoordinateTop r) :
    IsTwoCocycle _ _ (representative r q) := by
  apply extendTwo_closed _ (coordinateFamily_cover r)
  apply firstFace_closed
  exact Proj.basicOpen_zero (surfaceGrade r 1)

theorem selectedTriple_representative (r : ℂ) (q : HomogeneousCoordinateTop r) :
    selectedTriple (coordinateFamily r) (representative r q) 0 1 2 = tripleSections r 1 q :=
  selectedTriple_firstFace _ _ _

end CycleQ2LiteralOrbitCoordinateClassRepresentative

end

#print axioms CycleQ2LiteralOrbitCoordinateClassRepresentative.representative_closed
#print axioms CycleQ2LiteralOrbitCoordinateClassRepresentative.selectedTriple_representative
