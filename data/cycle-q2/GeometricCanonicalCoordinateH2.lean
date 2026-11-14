import Proposal.GeometricCanonicalCubicDiagram
import Proposal.GeometricSurfaceCoordinateFrames
import Proposal.GeometricThreeOpenH2Naturality
import Proposal.GeometricProjectiveDescent
import Proposal.GeometricCoordinateCechTrace

/-!
# The original cubic image on the actual three-coordinate cover

Status: source-only proof draft; verification is deferred at the user's request.
The unchanged Cartier class is identified with its retained negative coordinate
representative by the existing projective descent. Naturality then identifies
its image under multiplication by every actual global cubic two-form with the
actual canonical three-open connecting image of that same section. The local
canonical H¹ hypotheses are supplied by the genuine coordinate frames.

The last theorem retains the fixed nonzero detector coefficient on the same
representative. Proving that a canonical boundary has zero such coefficient
requires the separately constructed restriction-compatible coordinate maps.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2CanonicalCoordinateH2

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open CycleQ2GeometricProjectiveHOne CycleQ2CartierProjectiveCover
  CycleQ2GeometricSurfaceCoordinates CycleQ2GeometricSeedNormalIdeals
  CycleQ2GeometricCartierNormalLift CycleQ2CartierSurfaceGrading
  CycleQ2GeometricFourOpenCech CycleQ2GeometricCartierCech
  CycleQ2GeometricHomogeneousWeight CycleQ2GeometricLaurentTop
  CycleQ2NormalConnecting CycleQ2ProjectiveCoordinateH2
  CycleQ2ProjectiveCartierDerived CycleQ2LiteralProjectiveDescent
  CycleQ2CanonicalResidueSheaf CycleQ2CanonicalResidueDiagram
  CycleQ2CanonicalCubicDiagram CycleQ2ThreeOpenH2Naturality

abbrev Surface := projectiveSurface (57 : ℂ) 1
abbrev CanonicalSheaf := canonicalResidueAdditiveComplex.X₁
abbrev CoordinateOpen (i : Fin 3) : Surface.Opens :=
  CycleQ2ProjectiveCoordinateCohomology.coordinateOpen 57 1 i
abbrev TripleOpen : Surface.Opens :=
  CycleQ2ThreeOpenCechH2.TripleOpen (CoordinateOpen 0) (CoordinateOpen 1) (CoordinateOpen 2)
abbrev WeightedCubic := CycleQ2SurfaceCubicGluing.WeightedCubic

local instance surfaceHasExt :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology Surface) AddCommGrpCat.{0}) :=
  HasExt.standard _

theorem coordinateCover :
    (CoordinateOpen 0 ⊔ CoordinateOpen 1) ⊔ CoordinateOpen 2 = ⊤ :=
  CycleQ2ProjectiveCoordinateCohomology.coordinate_three_cover 57 1 one_ne_zero

/-- The whole-coordinate frames give H¹ vanishing on the unchanged
coordinate cover used by the original Laurent computation. -/
theorem canonicalCoordinateHOne_subsingleton (i : Fin 3) :
    Subsingleton (CanonicalSheaf.H' 1 (CoordinateOpen i)) := by
  have h := CycleQ2SurfaceCoordinateFrames.coordinateCanonicalHOne_subsingleton i
  fin_cases i <;> exact h

/-- The actual canonical three-open map, with its union identified with
the top open by the already proved coordinate cover. -/
def canonicalConnecting : CanonicalSheaf.obj.obj (op TripleOpen) →+
    CanonicalSheaf.H' 2 ⊤ :=
  connectingAtTop CanonicalSheaf (CoordinateOpen 0) (CoordinateOpen 1) (CoordinateOpen 2)
    coordinateCover

theorem canonicalConnecting_eq_zero_iff (s : CanonicalSheaf.obj.obj (op TripleOpen)) :
    canonicalConnecting s = 0 ↔
      ∃ (a : CanonicalSheaf.obj.obj (op (CoordinateOpen 0 ⊓ CoordinateOpen 1)))
        (b : CanonicalSheaf.obj.obj (op (CoordinateOpen 0 ⊓ CoordinateOpen 2)))
        (c : CanonicalSheaf.obj.obj (op (CoordinateOpen 1 ⊓ CoordinateOpen 2))),
        CycleQ2ThreeOpenSectionH2.boundary CanonicalSheaf
          (CoordinateOpen 0) (CoordinateOpen 1) (CoordinateOpen 2) (a,b,c) = s := by
  letI : Subsingleton (CanonicalSheaf.H' 1 (CoordinateOpen 0)) :=
    canonicalCoordinateHOne_subsingleton 0
  letI : Subsingleton (CanonicalSheaf.H' 1 (CoordinateOpen 1)) :=
    canonicalCoordinateHOne_subsingleton 1
  letI : Subsingleton (CanonicalSheaf.H' 1 (CoordinateOpen 2)) :=
    canonicalCoordinateHOne_subsingleton 2
  exact connectingAtTop_eq_zero_iff CanonicalSheaf
    (CoordinateOpen 0) (CoordinateOpen 1) (CoordinateOpen 2) coordinateCover s

/-- Multiply the actual degree-zero homogeneous overlap section by the
restriction of the actual global cubic two-form. -/
def cubicTripleSection (p : WeightedCubic) (q : HomogeneousCoordinateTop 57) :
    CanonicalSheaf.obj.obj (op TripleOpen) :=
  ((globalFormAdditiveDiagram (CycleQ2GlobalSurfaceCubics.globalCubicSection p)).τ₁).hom.app
    (op TripleOpen) (tripleSections 57 1 q)

/-- The exact triple-section multiplication square follows from
naturality of the original two Mayer--Vietoris boundaries. -/
theorem cubicH2_coordinateConnecting (p : WeightedCubic) (q : HomogeneousCoordinateTop 57) :
    cubicH2 p (connectingAtTop (structureAdditiveSheaf Surface)
      (CoordinateOpen 0) (CoordinateOpen 1) (CoordinateOpen 2) coordinateCover
      (tripleSections 57 1 q)) = canonicalConnecting (cubicTripleSection p q) :=
  connectingAtTop_naturality
    (globalFormAdditiveDiagram (CycleQ2GlobalSurfaceCubics.globalCubicSection p)).τ₁
    (CoordinateOpen 0) (CoordinateOpen 1) (CoordinateOpen 2) coordinateCover
    (tripleSections 57 1 q)

/-- The exact sign of the retained original Cartier descent is preserved
when its actual global cubic image is expressed on the coordinate cover. -/
theorem original_cubicH2_eq_coordinate
    (p : WeightedCubic)
    (dH : TwoCocycles (homogeneousCoordinateSystem 57))
    (c : TwoCocycles (literalSystem.left ∅)) (d : TwoCocycles (literalSystem.right ∅))
    (hL : literalLeftEmpty.mapCycle c = literalHomogeneousCartierCycle)
    (hR : literalRightEmpty.mapCycle d = dH)
    (hcd : literalSystem.SecondDescent c.val d.val) :
    cubicH2 p literalDerivedClassAtTop =
      canonicalConnecting (cubicTripleSection p (-homogeneousCoordinateRepresentative 57 dH)) := by
  have hB : literalDerivedClassAtTop = connectingAtTop (structureAdditiveSheaf Surface)
      (CoordinateOpen 0) (CoordinateOpen 1) (CoordinateOpen 2) coordinateCover
      (tripleSections 57 1 (-homogeneousCoordinateRepresentative 57 dH)) := by
    apply literalTerminalCohomologyEquiv.injective
    exact literalDerivedClass_eq_signed_coordinate dH c d hL hR hcd
  rw [hB]
  exact cubicH2_coordinateConnecting p (-homogeneousCoordinateRepresentative 57 dH)

/-- A single original homogeneous descendant supplies the exact canonical
multiplication identity for every cubic and the fixed nonzero algebraic
detector coefficient. Neither the descendant nor the form is chosen to fit
a subsequently selected trace. -/
theorem exists_original_cubic_coordinate_representative :
    ∃ dH : TwoCocycles (homogeneousCoordinateSystem 57),
      CartierCoordinateDescent 57 (cartierCycle 57 1 derivativeA 0)
        (forgetCoordinateCycle 57 dH) ∧
      (∀ p : WeightedCubic, cubicH2 p literalDerivedClassAtTop =
        canonicalConnecting (cubicTripleSection p
          (-homogeneousCoordinateRepresentative 57 dH))) ∧
      (coordinateLaurent 57 Finset.univ
        (surfaceQuotient 57 1 detectorCubic •
          (homogeneousCoordinateRepresentative 57 dH).val) (2,2)).coeff
            (fun _ => -1) ≠ 0 := by
  obtain ⟨dH,c,d,hL,hR,hcd,ho,_hB,_hne,hcoefficient,_hprojected⟩ :=
    literal_retained_global_descent
  exact ⟨dH,ho,fun p => original_cubicH2_eq_coordinate p dH c d hL hR hcd,hcoefficient⟩

#print axioms canonicalConnecting_eq_zero_iff
#print axioms cubicH2_coordinateConnecting
#print axioms original_cubicH2_eq_coordinate
#print axioms exists_original_cubic_coordinate_representative

end CycleQ2CanonicalCoordinateH2

end
