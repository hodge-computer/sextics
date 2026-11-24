import Proposal.GeometricLiteralCanonicalCoefficientWeight
import Proposal.GeometricLiteralCanonicalProjectionFrame

/-!
# The Laurent residue detects canonical Čech classes

The Laurent description of weight three has one strictly negative monomial.
When its coefficient vanishes, the ordinary localization boundary has pair
primitives. Projecting those primitives to degree three realizes each of them
by a canonical section on its pair open.

Prepared for fqlx with OpenAI ChatGPT assistance; see solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralCanonicalTraceInjective

open CategoryTheory Opposite AlgebraicGeometry
  CycleQ2GeometricSurfaceCoordinates CycleQ2GeometricLaurentTop
  CycleQ2ProjectiveCoordinateCohomology CycleQ2ProjectiveCoordinateH2
  CycleQ2CanonicalCoordinateCoefficients
  CycleQ2CanonicalResidueNonzero CycleQ2SeedCechThreeOpen CycleQ2CoordinateCechTrace
  CycleQ2LiteralCanonicalDegreeProjection CycleQ2LiteralCanonicalCoefficientWeight
  CycleQ2LiteralCanonicalCoefficientRange

private theorem degreeThree_mem_range_at (I : Finset (Fin 3)) (hI : I.Nonempty)
    (O : Surface.Opens) (hO : O = coordinateIntersection 57 1 I)
    (p : CoordinateLocal 57 1 I) :
    degreeThree I hI p ∈ (canonicalCoefficientAt I hI O hO).range := by
  subst O
  exact degreeThree_mem_range I hI p

private theorem degreeThree_fixed_at (I : Finset (Fin 3)) (hI : I.Nonempty)
    (O : Surface.Opens) (hO : O = coordinateIntersection 57 1 I)
    (s : CanonicalForms.val.obj (op O)) :
    degreeThree I hI (canonicalCoefficientAt I hI O hO s) =
      canonicalCoefficientAt I hI O hO s := by
  subst O
  exact degreeThree_canonicalCoefficientOn I hI s

private theorem pair_primitive (i j : Fin 3) (p : CoordinateLocal 57 1 {i,j}) :
    ∃ s, canonicalPairCoefficient i j s = degreeThree {i,j} (by simp) p :=
  degreeThree_mem_range_at {i,j} (by simp) _ (coordinateIntersection_pair 57 1 i j).symm p

/-- Vanishing of the distinguished coefficient yields genuine canonical
pair sections with the prescribed triple boundary. -/
theorem canonicalSection_mem_boundary_of_trace_zero
    (s : CanonicalSheaf.obj.obj (op TripleOpen)) (hs : canonicalSectionTrace s = 0) :
    s ∈ (CycleQ2ThreeOpenSectionH2.boundary CanonicalSheaf
      (CoordinateOpen 0) (CoordinateOpen 1) (CoordinateOpen 2)).range := by
  have hw := canonicalCoefficient_weight s
  obtain ⟨p01,p02,p12,hp⟩ := (coordinate_all_negative_zero_iff 57 (canonicalCoefficient s)).mp
    (by
      intro ab e he
      by_contra hne
      have hdeg := (mem_coordinateLocalWeight_iff 57 3 Finset.univ _).mp hw ab e hne
      obtain ⟨rfl, rfl⟩ := strictlyNegative_weight_three_unique ab e he hdeg
      exact hne hs)
  obtain ⟨s01,h01⟩ := pair_primitive 0 1 p01
  obtain ⟨s02,h02⟩ := pair_primitive 0 2 p02
  obtain ⟨s12,h12⟩ := pair_primitive 1 2 p12
  refine ⟨(s01,s02,s12), ?_⟩
  apply canonicalCoefficientAt_injective Finset.univ (by simp) TripleOpen
    (coordinateIntersection_univ 57 1).symm
  change canonicalCoefficient _ = canonicalCoefficient s
  rw [canonicalCoefficient_boundary, h01, h02, h12]
  have h := congrArg (degreeThree Finset.univ (by simp)) hp
  rw [map_add, map_sub, degreeThree_restrict, degreeThree_restrict, degreeThree_restrict] at h
  exact h.trans (degreeThree_fixed_at Finset.univ (by simp) TripleOpen
    (coordinateIntersection_univ 57 1).symm s)

theorem canonicalConnecting_zero_of_sectionTrace_zero
    (s : CanonicalSheaf.obj.obj (op TripleOpen)) (hs : canonicalSectionTrace s = 0) :
    CycleQ2CanonicalCoordinateH2.canonicalConnecting s = 0 := by
  obtain ⟨⟨a,b,c⟩,h⟩ := canonicalSection_mem_boundary_of_trace_zero s hs
  exact (CycleQ2CanonicalCoordinateH2.canonicalConnecting_eq_zero_iff s).mpr ⟨a,b,c,h⟩

theorem canonicalSectionTrace_eq_zero_iff (s : CanonicalSheaf.obj.obj (op TripleOpen)) :
    canonicalSectionTrace s = 0 ↔ CycleQ2CanonicalCoordinateH2.canonicalConnecting s = 0 :=
  ⟨canonicalConnecting_zero_of_sectionTrace_zero s, canonicalSectionTrace_zero_of_connecting_zero s⟩

/-- The fixed residue embeds the canonical three-open Čech quotient in ℂ. -/
theorem canonicalCechTrace_injective : Function.Injective canonicalCechTrace :=
  (QuotientAddGroup.injective_lift_iff _ _ _).2
    (le_antisymm canonicalBoundary_le_trace_kernel
      (fun s hs => canonicalSection_mem_boundary_of_trace_zero s hs))

end CycleQ2LiteralCanonicalTraceInjective

end

#print axioms CycleQ2LiteralCanonicalTraceInjective.canonicalSection_mem_boundary_of_trace_zero
#print axioms CycleQ2LiteralCanonicalTraceInjective.canonicalSectionTrace_eq_zero_iff
#print axioms CycleQ2LiteralCanonicalTraceInjective.canonicalCechTrace_injective
