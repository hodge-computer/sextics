import Proposal.GeometricCanonicalCoordinateH2
import Proposal.GeometricThreeOpenH2Surjectivity
import Proposal.GeometricAffineHTwo
import Proposal.GeometricAffineHigherChartRestriction

/-!
# Three-open representatives for the canonical surface cohomology

Every canonical degree-two class on the original closed surface admits a
representative on the triple coordinate intersection. Affine H¹ and H²
vanishing, transported using the residue frames, gives surjectivity of
the two Mayer–Vietoris connecting maps.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2LiteralCanonicalH2Surjective

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open CycleQ2GeometricSeedNormalIdeals CycleQ2GeometricCartierNormalLift CycleQ2CartierProjectiveCover
  CycleQ2GeometricConeCech.HZero CycleQ2ThreeOpenCechH2
  CycleQ2ThreeOpenH2Naturality CycleQ2CanonicalCoordinateH2
  CycleQ2GeometricProjectiveHOne CycleQ2ProjectiveCoordinateCohomology

local instance surfaceHasExt :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology (show TopCat from Surface))
      AddCommGrpCat.{0}) := CycleQ2CoordinateTopDescent.coordinateSurfaceHasExt 57 1

private def coordinateFrame (i : Fin 3) :
    CycleQ2GeometricSheafLocalIso.PatchIso CanonicalSheaf
      (structureAdditiveSheaf Surface) (CoordinateOpen i) := by
  have hi : CycleQ2SeedQuotientFiniteFree.remainingIndex i = i.succ.castSucc := by
    fin_cases i <;> rfl
  have ho : CoordinateOpen i = CycleQ2FullSurfaceResidueCover.coordinateOpen i :=
    congrArg (fun j : Fin 5 => Proj.basicOpen (CycleQ2CartierSurfaceGrading.surfaceGrade 57 1)
      (surfaceQuotient 57 1 (MvPolynomial.X j))) hi
  rw [ho]
  exact CycleQ2SurfaceCoordinateFrames.coordinateCanonicalAdditiveFrame i

theorem canonicalPairHOne_subsingleton (i j : Fin 3) :
    Subsingleton (CanonicalSheaf.H' 1 (CoordinateOpen i ⊓ CoordinateOpen j)) := by
  let U := coordinateIntersection 57 1 {i,j}
  have hU : U = CoordinateOpen i ⊓ CoordinateOpen j := coordinateIntersection_pair 57 1 i j
  have hle : U ≤ CoordinateOpen i := hU.le.trans inf_le_left
  let e := coordinateFrame i
  let f : CycleQ2GeometricSheafLocalIso.PatchIso CanonicalSheaf (structureAdditiveSheaf Surface) U :=
    { app := fun O hO => e.app O (hO.trans hle)
      naturality := fun h hO s => e.naturality h (hO.trans hle) s }
  rw [← hU]
  exact affineFrameHOne_subsingleton (coordinateChart 57 1 {i,j} (by simp))
    CanonicalSheaf (overIsoOfPatchIso f)

theorem canonicalCoordinateHTwo_subsingleton (i : Fin 3) :
    Subsingleton (CanonicalSheaf.H' 2 (CoordinateOpen i)) :=
  affineFrameHTwo_subsingleton (coordinateOpenChart 57 1 i) CanonicalSheaf
    (overIsoOfPatchIso (coordinateFrame i)) (CycleQ2GeometricAffineHTwo.affine_H_two_subsingleton _)

/-- Every canonical cohomology class has a triple-section representative. -/
theorem canonicalConnecting_surjective : Function.Surjective canonicalConnecting := by
  let := canonicalCoordinateHTwo_subsingleton 0
  let := canonicalCoordinateHTwo_subsingleton 1
  let := canonicalCoordinateHTwo_subsingleton 2
  let := canonicalPairHOne_subsingleton 0 1
  let := canonicalPairHOne_subsingleton 0 2
  let := canonicalPairHOne_subsingleton 1 2
  exact CycleQ2ThreeOpenH2Surjectivity.connectingAtTop_surjective CanonicalSheaf
    (CoordinateOpen 0) (CoordinateOpen 1) (CoordinateOpen 2) coordinateCover

end CycleQ2LiteralCanonicalH2Surjective
end

#print axioms CycleQ2LiteralCanonicalH2Surjective.canonicalPairHOne_subsingleton
#print axioms CycleQ2LiteralCanonicalH2Surjective.canonicalConnecting_surjective
