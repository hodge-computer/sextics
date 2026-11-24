import Proposal.GeometricLiteralCartierLiftedTransitions

/-!
# The actual correction one-cochain on the original Cartier cover

Each entry uses its pair's actual lifted transition and the restriction
of the same chosen first singleton splitting. The six entries belong
to the original surface localizations. Their genuine Cech coboundary
has the two previously checked correction faces and two zero faces.
No arbitrary coboundary or comparison cochain is assumed.

Prepared for fqlx with OpenAI ChatGPT assistance; see solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralCartierCorrectionCochain

open CycleQ2GeometricCartierNormalLift CycleQ2LiteralCartierTransitionBinding
  CycleQ2LiteralCartierSplittings CycleQ2LiteralCartierOverlapSplittings
  CycleQ2LiteralCartierKodairaSpencer CycleQ2LiteralCartierAtiyahFaces
  CycleQ2LiteralCartierCochainNaturality CycleQ2LiteralCartierLiftedTransitions
  CycleQ2GeometricSquareZeroSplittings CycleQ2GeometricFourOpenCech
  CycleQ2GeometricCartierCech

attribute [local instance] CycleQ2LiteralCartierTransitionBinding.cubicSelfModule
  CycleQ2LiteralCartierTransitionBinding.cubicOppositeModule
  CycleQ2LiteralCartierTransitionBinding.cubicCentralScalar
  CycleQ2LiteralCartierTransitionBinding.cubicSmulCommClass
  CycleQ2GeometricSurfaceFirstOrder.reducedAlgebra
  CycleQ2GeometricKernelLocalization.localReductionAlgebra
  CycleQ2LiteralCartierSplittings.complexReductionTower
  CycleQ2LiteralCartierOverlapSplittings.baseReductionAlgebra

def scalarCorrection (i : Fin 4) (s : Finset (Fin 4)) (hi : i ∈ s)
    (u : (Thick s)ˣ) : CoverLocal 57 1 s :=
  closedRingEquiv s
    (unitCorrection (kernelEquiv s) (splittingOn i s hi) (splittingOn_reduction i s hi) u)

theorem scalarCorrection_restrict {s t : Finset (Fin 4)} (hst : s ⊆ t)
    (i : Fin 4) (hi : i ∈ s) (u : (Thick s)ˣ) :
    coverRestriction 57 1 hst (scalarCorrection i s hi u) =
      scalarCorrection i t (hst hi) (restrictUnit hst u) :=
  comparedCorrection_restrict hst i hi u

theorem scalarCorrection_one (i : Fin 4) (s : Finset (Fin 4)) (hi : i ∈ s) :
    scalarCorrection i s hi 1 = 0 := by
  rw [scalarCorrection, unitCorrection_one, map_zero]

/-- The six genuine coefficient entries, in order 01,02,03,12,13,23. -/
def correctionOne : OneCochain (CoverLocal 57 1) :=
  ((scalarCorrection 0 {0,1} (by simp) lifted01,
    scalarCorrection 0 {0,2} (by simp) lifted02,
    scalarCorrection 0 {0,3} (by simp) lifted03),
   (scalarCorrection 1 {1,2} (by simp) lifted12,
    scalarCorrection 1 {1,3} (by simp) lifted13,
    scalarCorrection 2 {2,3} (by simp) lifted23))

theorem correctionOne_boundary012 :
    (d1 (surfaceSystem 57 1) correctionOne).1.1 =
      closedRingEquiv {0,1,2} (correction {0,1,2} (by simp) (by simp) (by simp)) := by
  change coverRestriction 57 1 (s := {1,2}) (t := {0,1,2}) (by decide)
      (scalarCorrection 1 {1,2} (by simp) lifted12) -
    coverRestriction 57 1 (s := {0,2}) (t := {0,1,2}) (by decide)
      (scalarCorrection 0 {0,2} (by simp) lifted02) +
    coverRestriction 57 1 (s := {0,1}) (t := {0,1,2}) (by decide)
      (scalarCorrection 0 {0,1} (by simp) lifted01) = _
  rw [scalarCorrection_restrict, scalarCorrection_restrict, scalarCorrection_restrict]
  rw [restrict_lifted12 _ (by simp) (by simp) (by simp),
    restrict_lifted02 _ (by simp) (by simp) (by simp), restrict_lifted01 _ (by simp)]
  simp only [scalarCorrection, correction, map_add, map_sub]

theorem correctionOne_boundary013 :
    (d1 (surfaceSystem 57 1) correctionOne).1.2 =
      closedRingEquiv {0,1,3} (correction {0,1,3} (by simp) (by simp) (by simp)) := by
  change coverRestriction 57 1 (s := {1,3}) (t := {0,1,3}) (by decide)
      (scalarCorrection 1 {1,3} (by simp) lifted13) -
    coverRestriction 57 1 (s := {0,3}) (t := {0,1,3}) (by decide)
      (scalarCorrection 0 {0,3} (by simp) lifted03) +
    coverRestriction 57 1 (s := {0,1}) (t := {0,1,3}) (by decide)
      (scalarCorrection 0 {0,1} (by simp) lifted01) = _
  rw [scalarCorrection_restrict, scalarCorrection_restrict, scalarCorrection_restrict]
  rw [restrict_lifted13 _ (by simp) (by simp) (by simp),
    restrict_lifted03 _ (by simp) (by simp) (by simp), restrict_lifted01 _ (by simp)]
  simp only [scalarCorrection, correction, map_add, map_sub]

theorem correctionOne_boundary023 :
    (d1 (surfaceSystem 57 1) correctionOne).2.1 = 0 := by
  change coverRestriction 57 1 (s := {2,3}) (t := {0,2,3}) (by decide)
      (scalarCorrection 2 {2,3} (by simp) lifted23) -
    coverRestriction 57 1 (s := {0,3}) (t := {0,2,3}) (by decide)
      (scalarCorrection 0 {0,3} (by simp) lifted03) +
    coverRestriction 57 1 (s := {0,2}) (t := {0,2,3}) (by decide)
      (scalarCorrection 0 {0,2} (by simp) lifted02) = 0
  rw [scalarCorrection_restrict, scalarCorrection_restrict, scalarCorrection_restrict,
    restrict_lifted23, scalarCorrection_one, second_transition_consistent _ (by decide)]
  abel

theorem correctionOne_boundary123 :
    (d1 (surfaceSystem 57 1) correctionOne).2.2 = 0 := by
  change coverRestriction 57 1 (s := {2,3}) (t := {1,2,3}) (by decide)
      (scalarCorrection 2 {2,3} (by simp) lifted23) -
    coverRestriction 57 1 (s := {1,3}) (t := {1,2,3}) (by decide)
      (scalarCorrection 1 {1,3} (by simp) lifted13) +
    coverRestriction 57 1 (s := {1,2}) (t := {1,2,3}) (by decide)
      (scalarCorrection 1 {1,2} (by simp) lifted12) = 0
  rw [scalarCorrection_restrict, scalarCorrection_restrict, scalarCorrection_restrict,
    restrict_lifted23, scalarCorrection_one, first_transition_consistent _ (by decide)]
  abel

def correctionRepresentative : TwoCochain (CoverLocal 57 1) :=
  ((closedRingEquiv {0,1,2} (correction {0,1,2} (by simp) (by simp) (by simp)),
    closedRingEquiv {0,1,3} (correction {0,1,3} (by simp) (by simp) (by simp))), (0,0))

/-- The previously checked face corrections are exactly the coboundary
of the constructed original pair cochain, with all four faces verified. -/
theorem correctionOne_boundary :
    d1 (surfaceSystem 57 1) correctionOne = correctionRepresentative :=
  Prod.ext (Prod.ext correctionOne_boundary012 correctionOne_boundary013)
    (Prod.ext correctionOne_boundary023 correctionOne_boundary123)

end CycleQ2LiteralCartierCorrectionCochain

end

#print axioms CycleQ2LiteralCartierCorrectionCochain.correctionOne_boundary012
#print axioms CycleQ2LiteralCartierCorrectionCochain.correctionOne_boundary013
#print axioms CycleQ2LiteralCartierCorrectionCochain.correctionOne_boundary
