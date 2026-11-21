import Proposal.GeometricCanonicalResidueNonzero
import Proposal.GeometricCanonicalResidueScalar

/-!
# Scalar compatibility of the literal canonical residue coefficient

The fixed coordinate Laurent coefficient and both Mayer--Vietoris
boundaries use the same complex structure on the actual projective
surface. On canonical sections this action is multiplication by the
restricted global complex coefficient.

Prepared for fqlx with OpenAI ChatGPT assistance; see solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralCanonicalTraceLinearity

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
  CycleQ2GeometricDifferentialSheaf CycleQ2GeometricSheafCohomologyScalar
  CycleQ2CartierSurfaceGrading CycleQ2GeometricSeedNormalIdeals
  CycleQ2GeometricCartierNormalLift CycleQ2GeometricSurfaceCoordinates
  CycleQ2GeometricSurfaceCoefficients CycleQ2ProjectiveCoordinateCohomology
  CycleQ2ProjectiveCoordinateH2 CycleQ2SurfaceSectionCoefficients
  CycleQ2SurfaceCechTwoScalar CycleQ2CanonicalResidueNonzero
  CycleQ2CanonicalCoordinateH2 CycleQ2CoordinateCechTrace

private abbrev Forms := CycleQ2CanonicalResidueSheaf.CanonicalForms

local instance : HasExt.{1} (Sheaf (Opens.grothendieckTopology Surface) AddCommGrpCat.{0}) :=
  HasExt.standard _

/-- The induced endomorphism of the actual canonical sections over the triple open. -/
def sectionScalar (c : ℂ) : CanonicalSheaf.obj.obj (op TripleOpen) →+
    CanonicalSheaf.obj.obj (op TripleOpen) :=
  ((scalarEnd Surface.sheaf (surfaceGlobalCoefficient 57 1) Forms c).hom.app (op TripleOpen)).hom

theorem canonicalConnecting_smul (c : ℂ) (s : CanonicalSheaf.obj.obj (op TripleOpen)) :
    canonicalConnecting (sectionScalar c s) = c • canonicalConnecting s :=
  (CycleQ2ThreeOpenH2Naturality.connectingAtTop_naturality
    (scalarEnd Surface.sheaf (surfaceGlobalCoefficient 57 1) Forms c)
    (CoordinateOpen 0) (CoordinateOpen 1) (CoordinateOpen 2) coordinateCover s).symm

private theorem sectionCoefficient_scalar (I : Finset (Fin 3)) (hI : I.Nonempty) (c : ℂ) :
    sectionCoefficient 57 1 I hI
        (coefficientOn Surface.sheaf (surfaceGlobalCoefficient 57 1)
          (coordinateIntersection 57 1 I) c) = algebraMap ℂ (CoordinateLocal 57 1 I) c := by
  have h := coefficientOn_basicOpen 57 1 (coordinateProduct 57 1 I)
    (coordinateProduct_mem_grade 57 1 I) (Finset.card_pos.mpr hI) c
  have hh := congrArg (fun z : HomogeneousCoordinateLocal 57 1 I => z.val) h
  refine hh.trans ?_
  change Localization.mk (algebraMap ℂ (SurfaceRing 57 1) c) 1 = _
  rw [Localization.mk_one_eq_algebraMap, ← IsScalarTower.algebraMap_apply]

private theorem coefficientAt_scalar (I : Finset (Fin 3)) (hI : I.Nonempty)
    (O : Surface.Opens) (hO : O = coordinateIntersection 57 1 I)
    (c : ℂ) (s : Forms.val.obj (op O)) :
    CycleQ2CanonicalCoordinateCoefficients.canonicalCoefficientAt I hI O hO
      ((scalarEnd Surface.sheaf (surfaceGlobalCoefficient 57 1) Forms c).hom.app (op O) s) =
    c • CycleQ2CanonicalCoordinateCoefficients.canonicalCoefficientAt I hI O hO s := by
  subst O
  let i := hI.choose
  let hi : i ∈ I := hI.choose_spec
  let U := coordinateIntersection 57 1 I
  let a := coefficientOn Surface.sheaf (surfaceGlobalCoefficient 57 1) U c
  let f := (CycleQ2SurfaceCoordinateFrames.coordinateExteriorFrame i).app U
    (intersection_le_chart 57 1 i hi)
  let k := (CycleQ2SurfaceCoordinateCubicFrames.orientation i : CoordinateLocal 57 1 I) *
    algebraMap (SurfaceRing 57 1) (CoordinateLocal 57 1 I) ((coordinateElement 57 1 i)^3)
  change k * (sectionCoefficient 57 1 I hI) (f (a • s)) =
    c • (k * (sectionCoefficient 57 1 I hI) (f s))
  rw [map_smul, smul_eq_mul, map_mul, sectionCoefficient_scalar, Algebra.smul_def]
  ring

theorem canonicalSectionTrace_smul (c : ℂ) (s : CanonicalSheaf.obj.obj (op TripleOpen)) :
    canonicalSectionTrace (sectionScalar c s) = c • canonicalSectionTrace s := by
  have h := coefficientAt_scalar Finset.univ (by simp) TripleOpen
    (coordinateIntersection_univ 57 1).symm c s
  change CycleQ2CanonicalCoordinateCoefficients.canonicalCoefficient (sectionScalar c s) =
    c • CycleQ2CanonicalCoordinateCoefficients.canonicalCoefficient s at h
  exact (congrArg (localCoefficient 57 Finset.univ (2,2) (fun _ => -1)) h).trans
    ((localCoefficient 57 Finset.univ (2,2) (fun _ => -1)).map_smul c _)

end CycleQ2LiteralCanonicalTraceLinearity

end

#print axioms CycleQ2LiteralCanonicalTraceLinearity.canonicalSectionTrace_smul
#print axioms CycleQ2LiteralCanonicalTraceLinearity.canonicalConnecting_smul
