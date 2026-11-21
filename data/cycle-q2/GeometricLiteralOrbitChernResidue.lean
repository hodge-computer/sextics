import Proposal.GeometricLiteralOrbitCoordinateResidue
import Proposal.GeometricLiteralOrbitConnectingAction
import Proposal.GeometricLiteralOrbitCoordinateClassAction
import Proposal.GeometricLiteralCotangentTrace

/-!
# The cubic pairing of the three translated Chern classes

The cotangent extension intertwines pullback of the Cartier Chern class
with the action on its normal boundary. On the stable coordinate cover the
normal action is the squared character times the projective pullback.
The resulting cubic pairing is three times the original nonzero pairing.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2LiteralOrbitChernResidue

open CategoryTheory CategoryTheory.Abelian TopologicalSpace AlgebraicGeometry
  CycleQ2GeometricHomogeneousWeight CycleQ2CanonicalCoordinateH2
  CycleQ2CanonicalResidueNonzero CycleQ2CanonicalCubicDiagram
  CycleQ2IncidenceFirstOrderCanonicalH2 CycleQ2LiteralCotangentTrace
  CycleQ2LiteralCotangentShortExact CycleQ2LiteralSheafOneClasses
  CycleQ2LiteralOrbitAction CycleQ2LiteralOrbitBoundary
  CycleQ2LiteralOrbitChern CycleQ2LiteralOrbitDerivedPullback
  CycleQ2LiteralOrbitCoordinateClass CycleQ2LiteralOrbitTrace
  CycleQ2AutomorphismCohomology CycleQ2AutomorphismGlobalSections

local instance additiveHasExt : HasExt.{1} (TopCat.Sheaf AddCommGrpCat.{0}
    (CycleQ2LiteralProjectiveCotangent.ClosedSurface : TopCat)) := HasExt.standard _

local instance schemeSheavesHasExt (S : Scheme.{0}) :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology S) AddCommGrpCat.{0}) := HasExt.standard _

private theorem connecting_orbit {V W : Type*} [AddCommGroup V] [AddCommGroup W]
    (D : V →+ W) (x y : V) (P : V →+ V) (N : W →+ W)
    (q w : W) (hy : y = x + P x + P (P x)) (hP : ∀ u, D (P u) = N (D u))
    (hq : q = D x) (hw : q + N q + N (N q) = w) : D y = w := by
  rw [hy]
  simpa only [map_add, hP, ← hq] using hw

private def delta : cotangentAdditiveComplex.X₃.H' 1 ⊤ →+ cotangentAdditiveComplex.X₁.H' 2 ⊤ :=
  CycleQ2GeometricIntrinsicCartierCohomology.openConnecting cotangentAdditiveShortExact 1 ⊤

variable (z : ℂ) (hz : z ^ 3 = 1)

private theorem transfer_orbit {V W : Type*} [AddCommGroup V] [AddCommGroup W]
    (f f' : W →+ V) (n n' : V →+ V) (hf : f = f') (hn : n = n') (q w : W)
    (h : f q + n (f q) + n (n (f q)) = f w) :
    f' q + n' (f' q) + n' (n' (f' q)) = f' w := by
  subst f' n'
  exact h

private theorem structureMap_eq :
    CycleQ2LiteralOrbitCoordinateClass.coordinateStructureClass 57 = structureCoordinateClass := rfl

private theorem normalMap_eq :
    normalPullH2 z hz = CycleQ2LiteralOrbitConnectingAction.boundaryPull z hz := rfl

private def normalOrbitProof (q : HomogeneousCoordinateTop 57) :=
  transfer_orbit _ _ _ _ structureMap_eq (normalMap_eq z hz) q
    (CycleQ2LiteralOrbitCoordinate.weightedTriple z hz q) (normalPull_coordinate_orbit z hz q)

private theorem delta_pull (u : cotangentAdditiveComplex.X₃.H' 1 ⊤) :
    delta (chernPull z hz u) = CycleQ2LiteralOrbitConnectingAction.boundaryPull z hz (delta u) :=
  CycleQ2LiteralOrbitConnectingAction.chernPull_connecting z hz u

set_option maxHeartbeats 1200000 in
private def orbitCoordinateProof (q : HomogeneousCoordinateTop 57)
    (hq : structureCoordinateClass q = chernDerivedClass.comp cotangentAdditiveShortExact.extClass rfl) :=
  connecting_orbit delta chernDerivedClass (orbitDerivedClass z hz)
    (chernPull z hz) (CycleQ2LiteralOrbitConnectingAction.boundaryPull z hz)
    (structureCoordinateClass q) (structureCoordinateClass (CycleQ2LiteralOrbitCoordinate.weightedTriple z hz q))
    (orbitDerivedClass_eq_derived_orbit z hz) (delta_pull z hz)
    hq (normalOrbitProof z hz q)

/-- The actual boundary of the three translated Chern classes is the
class of their weighted triple section. -/
theorem orbitDerivedClass_connecting_coordinate (q : HomogeneousCoordinateTop 57)
    (hq : structureCoordinateClass q = chernDerivedClass.comp cotangentAdditiveShortExact.extClass rfl) :
    type_of% (orbitCoordinateProof z hz q hq) := orbitCoordinateProof z hz q hq

/-- The retained cubic evaluates the literal orbit product to three times
the residue of the single-curve Chern class. -/
theorem orbitDerivedClass_cubic_trace (hprim : z^2 + z + 1 = 0) :
    algebraicTrace (cubicH2 firstOrderWeightedCubic
      ((orbitDerivedClass z hz).comp cotangentAdditiveShortExact.extClass rfl)) =
    (3 : ℕ) • algebraicTrace (cubicH2 firstOrderWeightedCubic
      (chernDerivedClass.comp cotangentAdditiveShortExact.extClass rfl)) := by
  obtain ⟨q,hq⟩ := structureCoordinateClass_surjective (chernDerivedClass.comp cotangentAdditiveShortExact.extClass rfl)
  change algebraicTrace (cubicH2 firstOrderWeightedCubic (delta (orbitDerivedClass z hz))) = _
  rw [orbitDerivedClass_connecting_coordinate z hz q hq, ← hq]
  exact CycleQ2LiteralOrbitCoordinateResidue.weightedTriple_cubic_trace z hz hprim q

theorem orbitDerivedClass_cubic_trace_ne_zero (hprim : z^2 + z + 1 = 0) :
    algebraicTrace (cubicH2 firstOrderWeightedCubic
      ((orbitDerivedClass z hz).comp cotangentAdditiveShortExact.extClass rfl)) ≠ 0 := by
  rw [orbitDerivedClass_cubic_trace z hz hprim, nsmul_eq_mul]
  exact mul_ne_zero (by norm_num) chernCubic_trace_ne_zero

theorem orbitDerivedClass_cubicH2 (hprim : z^2 + z + 1 = 0) :
    cubicH2 firstOrderWeightedCubic ((orbitDerivedClass z hz).comp cotangentAdditiveShortExact.extClass rfl) =
    (3 : ℕ) • cubicH2 firstOrderWeightedCubic
      (chernDerivedClass.comp cotangentAdditiveShortExact.extClass rfl) := by
  apply algebraicTrace_injective
  rw [map_nsmul]
  exact orbitDerivedClass_cubic_trace z hz hprim

end CycleQ2LiteralOrbitChernResidue
end

#print axioms CycleQ2LiteralOrbitChernResidue.orbitDerivedClass_cubic_trace_ne_zero
#print axioms CycleQ2LiteralOrbitChernResidue.orbitDerivedClass_cubicH2
