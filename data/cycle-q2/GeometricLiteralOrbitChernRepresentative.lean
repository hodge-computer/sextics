import Proposal.GeometricLiteralCanonicalH2Surjective

/-!
# Coordinate representative of the actual Chern boundary

Affine H¹ and H² vanishing on the coordinate cover gives a homogeneous
representative for every structure-sheaf degree-two class.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace CycleQ2LiteralOrbitTrace

open CycleQ2GeometricHomogeneousWeight
open CategoryTheory TopologicalSpace
  CycleQ2ThreeOpenH2Naturality CycleQ2GeometricProjectiveHOne
  CycleQ2ProjectiveCoordinateH2 CycleQ2ProjectiveCoordinateCohomology
  CycleQ2CanonicalCoordinateH2

local instance schemeSheavesHasExt (S : AlgebraicGeometry.Scheme.{0}) :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology S) AddCommGrpCat.{0}) := HasExt.standard _

/-- The two coordinate-cover boundaries applied to a homogeneous fraction. -/
def structureCoordinateClass : HomogeneousCoordinateTop 57 →+
    (structureAdditiveSheaf CycleQ2CanonicalCoordinateH2.Surface).H' 2 ⊤ :=
  (connectingAtTop (structureAdditiveSheaf CycleQ2CanonicalCoordinateH2.Surface)
    (CycleQ2CanonicalCoordinateH2.CoordinateOpen 0) (CycleQ2CanonicalCoordinateH2.CoordinateOpen 1)
    (CycleQ2CanonicalCoordinateH2.CoordinateOpen 2) CycleQ2CanonicalCoordinateH2.coordinateCover).comp
    (tripleSections 57 1).toRingHom.toAddMonoidHom

/-- The affineness of the three charts and their pair intersections gives
a homogeneous representative for each degree-two class. -/
theorem structureCoordinateClass_surjective : Function.Surjective structureCoordinateClass := by
  let F := structureAdditiveSheaf Surface
  have h2 (i : Fin 3) : Subsingleton (F.H' 2 (CoordinateOpen i)) :=
    affineFrameHTwo_subsingleton (coordinateOpenChart 57 1 i) F (CategoryTheory.Iso.refl _)
      (CycleQ2GeometricAffineHTwo.affine_H_two_subsingleton _)
  have h1 (i j : Fin 3) : Subsingleton (F.H' 1 (CoordinateOpen i ⊓ CoordinateOpen j)) := by
    rw [← coordinateIntersection_pair 57 1 i j]
    exact coordinateIntersection_H_one_subsingleton 57 1 {i,j} (by simp)
  let := h2 0
  let := h2 1
  let := h2 2
  let := h1 0 1
  let := h1 0 2
  let := h1 1 2
  exact (CycleQ2ThreeOpenH2Surjectivity.connectingAtTop_surjective F
    (CoordinateOpen 0) (CoordinateOpen 1) (CoordinateOpen 2) coordinateCover).comp
      (tripleSections 57 1).surjective

end CycleQ2LiteralOrbitTrace
end

#print axioms CycleQ2LiteralOrbitTrace.structureCoordinateClass_surjective
