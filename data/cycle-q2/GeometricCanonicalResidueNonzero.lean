import Proposal.GeometricCanonicalCoordinateH2
import Proposal.GeometricCanonicalCoordinateCoefficients

/-!
# Nonvanishing of the original cubic canonical connecting image

Status: source-only proof draft; verification is deferred at the user's request.
The detector here is the fixed cubic X₀³ from the original coordinate Laurent
calculation. It is distinct from the selected cubic used by the incidence
normal-class computation. The exact negative sign of the retained Cartier
coordinate representative is preserved.

The endpoint uses the actual coefficient maps from canonical sections on
the pair and triple coordinate opens. No arbitrary trace on the
whole derived H² group is chosen. Nonvanishing of the additive residue
connecting map alone does not assert its injectivity: a subsequent finite
trace comparison must retain actual complex linearity and the actual
pushforward-boundary image of the fixed one-dimensional curve Čech quotient. The final
moving-cycle/support primitive is a separate geometric step.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2CanonicalResidueNonzero

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry MvPolynomial
open CycleQ2SeedTrace CycleQ2CartierSurfaceGrading
  CycleQ2GeometricCartierCech CycleQ2GeometricLaurentTop
  CycleQ2GeometricSurfaceCoordinates CycleQ2GeometricSeedNormalIdeals
  CycleQ2CoordinateCechTrace CycleQ2CanonicalCoordinateH2
  CycleQ2CanonicalCoordinateCoefficients CycleQ2CanonicalCubicDiagram
  CycleQ2CanonicalResidueDiagram CycleQ2ProjectiveCartierDerived
  CycleQ2GeometricIntrinsicCartierCohomology CycleQ2GlobalCubicAdjunctionCohomology

local instance surfaceHasExt :
    HasExt.{1} (Sheaf
      (Opens.grothendieckTopology CycleQ2CanonicalCoordinateH2.Surface)
      AddCommGrpCat.{0}) := HasExt.standard _

/-- The original algebraic detector, with its proved weighted degree. -/
def detectorWeightedCubic : WeightedCubic :=
  ⟨detectorCubic, by
    have hX : (X (0 : Fin 5) : WeightedPoly).IsWeightedHomogeneous weight 1 := by
      simpa only [weight_castSucc] using
        isWeightedHomogeneous_X ℂ weight (0 : Fin 4).castSucc
    simpa only [detectorCubic] using hX.pow 3⟩

/-- The coefficient fixed in the original coordinate trace annihilates
every ordinary pair-boundary, with arbitrary localization pole orders. -/
theorem coordinateCoefficient_boundary_zero (r : ℂ)
    (a : CoordinateLocal r 1 {0,1}) (b : CoordinateLocal r 1 {0,2})
    (c : CoordinateLocal r 1 {1,2}) :
    localCoefficient r Finset.univ (2,2) (fun _ => -1)
      (coordinateRestriction r 1 (Finset.subset_univ {1,2}) c -
        coordinateRestriction r 1 (Finset.subset_univ {0,2}) b +
        coordinateRestriction r 1 (Finset.subset_univ {0,1}) a) = 0 :=
  (coordinate_all_negative_zero_iff r _).mpr ⟨a,b,c,rfl⟩
    (2,2) (fun _ => -1) (by intro i; norm_num)

/-- A fixed functional on actual canonical triple sections. The coefficient
and local determinant normalization were fixed before the Cartier class. -/
def canonicalSectionTrace : CanonicalSheaf.obj.obj (op TripleOpen) →+ ℂ :=
  (localCoefficient 57 Finset.univ (2,2) (fun _ => -1)).toAddMonoidHom.comp
    canonicalCoefficient

/-- Every genuine canonical pair-boundary has zero fixed coordinate trace. -/
theorem canonicalSectionTrace_boundary
    (a : CanonicalSheaf.obj.obj (op (CoordinateOpen 0 ⊓ CoordinateOpen 1)))
    (b : CanonicalSheaf.obj.obj (op (CoordinateOpen 0 ⊓ CoordinateOpen 2)))
    (c : CanonicalSheaf.obj.obj (op (CoordinateOpen 1 ⊓ CoordinateOpen 2))) :
    canonicalSectionTrace (CycleQ2ThreeOpenSectionH2.boundary CanonicalSheaf
      (CoordinateOpen 0) (CoordinateOpen 1) (CoordinateOpen 2) (a,b,c)) = 0 := by
  change localCoefficient 57 Finset.univ (2,2) (fun _ => -1)
    (canonicalCoefficient (CycleQ2ThreeOpenSectionH2.boundary CanonicalSheaf
      (CoordinateOpen 0) (CoordinateOpen 1) (CoordinateOpen 2) (a,b,c))) = 0
  rw [canonicalCoefficient_boundary]
  exact coordinateCoefficient_boundary_zero 57
    (canonicalPairCoefficient 0 1 a) (canonicalPairCoefficient 0 2 b)
    (canonicalPairCoefficient 1 2 c)

theorem canonicalBoundary_le_trace_kernel :
    (CycleQ2ThreeOpenSectionH2.boundary CanonicalSheaf
      (CoordinateOpen 0) (CoordinateOpen 1) (CoordinateOpen 2)).range ≤
        canonicalSectionTrace.ker := by
  rintro s ⟨⟨a,b,c⟩,rfl⟩
  exact canonicalSectionTrace_boundary a b c

/-- The fixed trace on the actual canonical Čech quotient. This construction
uses only genuine pair-boundaries; it is not an arbitrarily chosen extension
to the whole derived H² group. -/
def canonicalCechTrace :
    CycleQ2ThreeOpenSectionH2.CechH2 CanonicalSheaf
      (CoordinateOpen 0) (CoordinateOpen 1) (CoordinateOpen 2) →+ ℂ :=
  QuotientAddGroup.lift
    (CycleQ2ThreeOpenSectionH2.boundary CanonicalSheaf
      (CoordinateOpen 0) (CoordinateOpen 1) (CoordinateOpen 2)).range
    canonicalSectionTrace canonicalBoundary_le_trace_kernel

/-- The actual local H¹ vanishing makes every section with zero derived
connecting image an actual canonical boundary, so its fixed trace vanishes. -/
theorem canonicalSectionTrace_zero_of_connecting_zero
    (s : CanonicalSheaf.obj.obj (op TripleOpen)) (hs : canonicalConnecting s = 0) :
    canonicalSectionTrace s = 0 := by
  obtain ⟨a,b,c,rfl⟩ := (canonicalConnecting_eq_zero_iff s).mp hs
  exact canonicalSectionTrace_boundary a b c

/-- The actual detector-cubic image of the unchanged Cartier class in
canonical H² is nonzero. The representative remains the retained `-q`. -/
theorem detector_cubicH2_ne_zero :
    cubicH2 detectorWeightedCubic literalDerivedClassAtTop ≠ 0 := by
  obtain ⟨dH,_hdescent,himage,hcoefficient⟩ :=
    exists_original_cubic_coordinate_representative
  let q := homogeneousCoordinateRepresentative 57 dH
  intro hz
  have hzero : canonicalConnecting (cubicTripleSection detectorWeightedCubic (-q)) = 0 :=
    (himage detectorWeightedCubic).symm.trans hz
  have ht := canonicalSectionTrace_zero_of_connecting_zero
    (cubicTripleSection detectorWeightedCubic (-q)) hzero
  change localCoefficient 57 Finset.univ (2,2) (fun _ => -1)
    (canonicalCoefficient (cubicTripleSection detectorWeightedCubic (-q))) = 0 at ht
  rw [canonicalCoefficient_cubicTripleSection] at ht
  have ht' : -(localCoefficient 57 Finset.univ (2,2) (fun _ => -1)
      (surfaceQuotient 57 1 detectorCubic • q.val)) = 0 := by
    simpa only [detectorWeightedCubic, HomogeneousLocalization.val_neg, smul_neg,
      map_neg] using ht
  exact hcoefficient (neg_eq_zero.mp ht')

/-- The original Cartier/canonical diagram now has a proved nonzero
value under its actual canonical residue connecting map. -/
theorem canonicalResidueConnecting_value_ne_zero :
    canonicalOpenConnecting ⊤
      (surfaceAdjunctionH1 detectorWeightedCubic literalNormalClassAtTop) ≠ 0 := by
  rw [originalClass_cubic_connecting]
  exact detector_cubicH2_ne_zero

/-- The actual additive canonical residue connecting map is nonzero.
Its injectivity requires the further genuine scalar/one-dimensional comparison
specified in the module header; it is not inferred merely from this statement. -/
theorem canonicalResidueConnecting_ne_zero : canonicalOpenConnecting ⊤ ≠ 0 := by
  intro h
  exact canonicalResidueConnecting_value_ne_zero
    (DFunLike.congr_fun h (surfaceAdjunctionH1 detectorWeightedCubic literalNormalClassAtTop))

#print axioms canonicalCechTrace
#print axioms canonicalSectionTrace_zero_of_connecting_zero
#print axioms detector_cubicH2_ne_zero
#print axioms canonicalResidueConnecting_value_ne_zero
#print axioms canonicalResidueConnecting_ne_zero

end CycleQ2CanonicalResidueNonzero

end
