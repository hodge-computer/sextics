import Proposal.GeometricLiteralCartierCorrectionCochain

/-!
# The actual cone-level KS/dlog cup class equals the original Cartier class

The cup entries are independently defined by the actual constructed
splitting derivations applied to the actual universal logarithmic
differentials. The original transition-defect cochain equals their sum
with the genuine correction coboundary. Thus their actual Cech class
is the negative original Cartier class and is nonzero.

This is a comparison in the original Cartier cone Cech complex. It
does not yet identify the cup with a projective Chern/KS class or an
Abel--Jacobi derivative and does not prove protected residue exactness.

Prepared for fqlx with OpenAI ChatGPT assistance; see solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralCartierCupClass

open CycleQ2SeedTrace CycleQ2NormalConnecting CycleQ2GeometricCartierNormalLift
  CycleQ2LiteralCartierTransitionBinding CycleQ2LiteralCartierSplittings
  CycleQ2LiteralCartierAtiyahFaces CycleQ2LiteralCartierCorrectionCochain
  CycleQ2LiteralCartierKodairaSpencer CycleQ2LiteralCartierCochainNaturality
  CycleQ2LiteralCartierLiftedTransitions CycleQ2GeometricSquareZeroSplittings
  CycleQ2GeometricFourOpenCech CycleQ2GeometricCartierCech

attribute [local instance] CycleQ2LiteralCartierTransitionBinding.cubicSelfModule
  CycleQ2LiteralCartierTransitionBinding.cubicOppositeModule
  CycleQ2LiteralCartierTransitionBinding.cubicCentralScalar
  CycleQ2LiteralCartierTransitionBinding.cubicSmulCommClass
  CycleQ2GeometricSurfaceFirstOrder.reducedAlgebra
  CycleQ2GeometricKernelLocalization.localReductionAlgebra
  CycleQ2LiteralCartierSplittings.complexReductionTower
  CycleQ2LiteralCartierOverlapSplittings.baseReductionAlgebra

/-- Evaluation of the actual closed splitting difference on the universal
logarithmic differential of the reduction of an actual lifted transition. -/
def contractionOn (s : Finset (Fin 4)) (i j : Fin 4) (hi : i ∈ s) (hj : j ∈ s)
    (u : (Thick s)ˣ) : ClosedRing s :=
  (kodairaSpencer s i j hi hj).liftKaehlerDifferential
    (logDifferential (K := ℂ) (reducedUnit (C := ClosedRing s) u))

theorem contractionOn_one (s : Finset (Fin 4)) (i j : Fin 4)
    (hi : i ∈ s) (hj : j ∈ s) : contractionOn s i j hi hj 1 = 0 := by
  unfold contractionOn
  rw [show reducedUnit (C := ClosedRing s) (1 : (Thick s)ˣ) = 1 from map_one _,
    logDifferential_one, map_zero]

/-- All four genuine Cech cup entries. Each uses the restriction of the
actual jk pair transition with the actual i,j splitting difference. -/
def cupRepresentative : TwoCochain (CoverLocal 57 1) :=
  ((closedRingEquiv {0,1,2} (contractionOn {0,1,2} 0 1 (by simp) (by simp)
      (restrictUnit (s := {1,2}) (t := {0,1,2}) (by decide) lifted12)),
    closedRingEquiv {0,1,3} (contractionOn {0,1,3} 0 1 (by simp) (by simp)
      (restrictUnit (s := {1,3}) (t := {0,1,3}) (by decide) lifted13))),
   (closedRingEquiv {0,2,3} (contractionOn {0,2,3} 0 2 (by simp) (by simp)
      (restrictUnit (s := {2,3}) (t := {0,2,3}) (by decide) lifted23)),
    closedRingEquiv {1,2,3} (contractionOn {1,2,3} 1 2 (by simp) (by simp)
      (restrictUnit (s := {2,3}) (t := {1,2,3}) (by decide) lifted23))))

theorem cupRepresentative012 : cupRepresentative.1.1 =
    closedRingEquiv {0,1,2} (cup {0,1,2} (by simp) (by simp) (by simp)) := by
  change closedRingEquiv {0,1,2} (contractionOn _ _ _ _ _ _) = _
  rw [restrict_lifted12 _ (by simp) (by simp) (by simp)]
  rfl

theorem cupRepresentative013 : cupRepresentative.1.2 =
    closedRingEquiv {0,1,3} (cup {0,1,3} (by simp) (by simp) (by simp)) := by
  change closedRingEquiv {0,1,3} (contractionOn _ _ _ _ _ _) = _
  rw [restrict_lifted13 _ (by simp) (by simp) (by simp)]
  rfl

theorem cupRepresentative023 : cupRepresentative.2.1 = 0 := by
  change closedRingEquiv {0,2,3} (contractionOn _ _ _ _ _ _) = _
  rw [restrict_lifted23, contractionOn_one, map_zero]

theorem cupRepresentative123 : cupRepresentative.2.2 = 0 := by
  change closedRingEquiv {1,2,3} (contractionOn _ _ _ _ _ _) = _
  rw [restrict_lifted23, contractionOn_one, map_zero]

/-- A proved cochain equality with the original transition defects;
the cup was defined from actual derivations, independently of this equality. -/
theorem defect_eq_coboundary_add_cup :
    defectRepresentative = d1 (surfaceSystem 57 1) correctionOne + cupRepresentative := by
  rw [correctionOne_boundary]
  refine Prod.ext (Prod.ext ?_ ?_) (Prod.ext ?_ ?_)
  · change defect012 = correctionRepresentative.1.1 + cupRepresentative.1.1
    rw [cupRepresentative012]
    change defect012 =
      closedRingEquiv {0,1,2} (correction {0,1,2} (by simp) (by simp) (by simp)) +
      closedRingEquiv {0,1,2} (cup {0,1,2} (by simp) (by simp) (by simp))
    rw [← map_add, atiyah_face012, defect012_eq_negative_boundary]
  · change defect013 = correctionRepresentative.1.2 + cupRepresentative.1.2
    rw [cupRepresentative013]
    change defect013 =
      closedRingEquiv {0,1,3} (correction {0,1,3} (by simp) (by simp) (by simp)) +
      closedRingEquiv {0,1,3} (cup {0,1,3} (by simp) (by simp) (by simp))
    rw [← map_add, atiyah_face013, defect013_eq_negative_boundary]
  · change (0 : CoverLocal 57 1 {0,2,3}) = 0 + cupRepresentative.2.1
    rw [cupRepresentative023, zero_add]
  · change (0 : CoverLocal 57 1 {1,2,3}) = 0 + cupRepresentative.2.2
    rw [cupRepresentative123, zero_add]

theorem cupRepresentative_closed : d2 (surfaceSystem 57 1) cupRepresentative = 0 := by
  have he : cupRepresentative = defectRepresentative - d1 (surfaceSystem 57 1) correctionOne := by
    rw [defect_eq_coboundary_add_cup]
    abel
  rw [he, map_sub, defectRepresentative_closed, d2_d1, sub_self]

def cupCycle : TwoCocycles (surfaceSystem 57 1) :=
  ⟨cupRepresentative, cupRepresentative_closed⟩

def cupClass : ActualSecondCech 57 1 := classOf (surfaceSystem 57 1) cupCycle

/-- Quotienting the actual closed cup cocycle kills the constructed
correction coboundary and yields the original transition-defect class. -/
theorem cupClass_eq_defectClass : cupClass = defectClass := by
  have hc : defectCycle = boundaryMap (surfaceSystem 57 1) correctionOne + cupCycle :=
    Subtype.ext defect_eq_coboundary_add_cup
  have hb : classOf (surfaceSystem 57 1)
      (boundaryMap (surfaceSystem 57 1) correctionOne) = 0 :=
    (classOf_eq_zero_iff _ _).mpr ⟨correctionOne, rfl⟩
  rw [defectClass, hc, map_add, hb, zero_add]
  rfl

theorem cupClass_eq_negative_original :
    cupClass = -cartierClass 57 1 derivativeA 0 := by
  rw [cupClass_eq_defectClass, defectClass_eq_negative_original]

theorem cupClass_ne_zero : cupClass ≠ 0 := by
  rw [cupClass_eq_defectClass]
  exact defectClass_ne_zero

end CycleQ2LiteralCartierCupClass

end

#print axioms CycleQ2LiteralCartierCupClass.defect_eq_coboundary_add_cup
#print axioms CycleQ2LiteralCartierCupClass.cupClass_eq_negative_original
#print axioms CycleQ2LiteralCartierCupClass.cupClass_ne_zero
