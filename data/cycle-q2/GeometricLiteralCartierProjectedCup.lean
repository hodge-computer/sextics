import Proposal.GeometricLiteralCartierCupClass
import Proposal.GeometricCartierDerivedClass
import Proposal.GeometricCartierNormalBinding

/-!
# Canonical projective image of the actual cone cup cochain

The already constructed degree-zero additive projection is applied to
the actual cone correction and cup cochains. Actual homogeneous chart
section equivalences identify its values with sections of the original
projective structure sheaf. The projection commutes with restrictions,
so the proved cone coboundary identity survives in the native projective
Cech complex and its genuine derived cohomology.

Projection is only asserted additive. This file does not identify the
projected cup with a contraction of projective Chern and KS classes;
that requires a separate comparison of the factors and their gauges.

Prepared for fqlx with OpenAI ChatGPT assistance; see solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralCartierProjectedCup

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
  CycleQ2SeedTrace CycleQ2NormalConnecting CycleQ2GeometricSeedNormalIdeals
  CycleQ2GeometricCartierNormalLift CycleQ2GeometricFourOpenCech
  CycleQ2GeometricCartierCech CycleQ2CartierSurfaceGrading CycleQ2CartierHomogeneousCech
  CycleQ2CartierProjectiveCover CycleQ2GradedLocalizationProjection
  CycleQ2ProjectiveCartierIntersections CycleQ2ProjectiveCartierDerived
  CycleQ2LiteralCartierTransitionBinding CycleQ2LiteralCartierCorrectionCochain
  CycleQ2LiteralCartierCupClass

local instance schemeSheavesHasExt (X : Scheme.{0}) :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}) :=
  HasExt.standard _

/-- Canonical additive projection to actual projective sections. -/
def projectSection (s : Finset (Fin 4)) (hs : s.Nonempty) :
    CoverLocal 57 1 s →+ CycleQ2ProjectiveCartierCochain.Sections 57 1 s :=
  (coverSectionsEquiv 57 1 s hs).toAddEquiv.toAddMonoidHom.comp
    (degreeZeroAddHom (surfaceGrade 57 1) (coverProduct_mem_grade 57 1 s))

theorem projectSection_restrict {s t : Finset (Fin 4)} (hs : s.Nonempty)
    (ht : t.Nonempty) (hst : s ⊆ t) (x : CoverLocal 57 1 s) :
    CycleQ2ProjectiveCartierCochain.restriction 57 1 hst (projectSection s hs x) =
      projectSection t ht (coverRestriction 57 1 hst x) := by
  change (projectiveSurface 57 1).presheaf.map (homOfLE (coverPatch_mono 57 1 hst)).op
      (coverSectionsEquiv 57 1 s hs (degreeZero (surfaceGrade 57 1) (coverProduct_mem_grade 57 1 s) x)) =
    coverSectionsEquiv 57 1 t ht (degreeZero (surfaceGrade 57 1) (coverProduct_mem_grade 57 1 t) (coverRestriction 57 1 hst x))
  rw [coverSectionsEquiv_restrict 57 1 hs ht hst]
  congr 1
  exact (degreeZero_naturality (surfaceGrade 57 1) (coverProduct_mem_grade 57 1 s)
    (coverProduct_mem_grade 57 1 (t \ s)) (coverProduct_factor 57 1 hst)
    (coverProduct_mem_grade 57 1 t) (coverRestriction 57 1 hst) x).symm

def nativeOne (p : OneCochain (CoverLocal 57 1)) : CycleQ2ProjectiveCartierCochain.One 57 1 :=
  ⟨projectSection {0,1} (by simp) p.1.1,
   projectSection {0,2} (by simp) p.1.2.1,
   projectSection {0,3} (by simp) p.1.2.2,
   projectSection {1,2} (by simp) p.2.1,
   projectSection {1,3} (by simp) p.2.2.1,
   projectSection {2,3} (by simp) p.2.2.2⟩

def nativeTwo (c : TwoCochain (CoverLocal 57 1)) : CycleQ2ProjectiveCartierCochain.Two 57 1 :=
  ⟨projectSection {0,1,2} (by simp) c.1.1,
   projectSection {0,1,3} (by simp) c.1.2,
   projectSection {0,2,3} (by simp) c.2.1,
   projectSection {1,2,3} (by simp) c.2.2⟩

def projectOne (p : OneCochain (CoverLocal 57 1)) : CechOne 57 1 :=
  toOne 57 1 (nativeOne p)

def projectTwo : TwoCochain (CoverLocal 57 1) →+ CechTwo 57 1 where
  toFun c := toTwo 57 1 (nativeTwo c)
  map_zero' := by
    simp only [nativeTwo, toTwo, Prod.fst_zero, Prod.snd_zero, map_zero]
    rfl
  map_add' c d := by
    simp only [nativeTwo, toTwo, Prod.fst_add, Prod.snd_add, map_add]
    rfl

private theorem fourFaces_ext {A B C D : Type*} (x y : FourFaces A B C D)
    (h0 : x.face012 = y.face012) (h1 : x.face013 = y.face013)
    (h2 : x.face023 = y.face023) (h3 : x.face123 = y.face123) : x = y := by
  cases x
  cases y
  cases h0
  cases h1
  cases h2
  cases h3
  rfl

/-- The actual degree-zero projection carries an actual scalar
coboundary to the coboundary of its projected native section cochain. -/
theorem projectTwo_d1 (p : OneCochain (CoverLocal 57 1)) :
    projectTwo (d1 (surfaceSystem 57 1) p) =
      CycleQ2CechTwoToDerived.d1 (additiveSheaf 57 1) (coverFamily 57 1) (projectOne p) := by
  change toTwo 57 1 (nativeTwo _) =
    CycleQ2CechTwoToDerived.d1 (additiveSheaf 57 1) (coverFamily 57 1) (toOne 57 1 (nativeOne p))
  rw [← toTwo_oneDifferential]
  apply congrArg (toTwo 57 1)
  apply fourFaces_ext
  · change projectSection {0,1,2} (by simp)
      (coverRestriction 57 1 (s := {1,2}) (t := {0,1,2}) (by decide) p.2.1 -
        coverRestriction 57 1 (s := {0,2}) (t := {0,1,2}) (by decide) p.1.2.1 +
        coverRestriction 57 1 (s := {0,1}) (t := {0,1,2}) (by decide) p.1.1) =
      CycleQ2ProjectiveCartierCochain.restriction 57 1 (s := {1,2}) (t := {0,1,2}) (by decide)
        (projectSection {1,2} (by simp) p.2.1) -
      CycleQ2ProjectiveCartierCochain.restriction 57 1 (s := {0,2}) (t := {0,1,2}) (by decide)
        (projectSection {0,2} (by simp) p.1.2.1) +
      CycleQ2ProjectiveCartierCochain.restriction 57 1 (s := {0,1}) (t := {0,1,2}) (by decide)
        (projectSection {0,1} (by simp) p.1.1)
    rw [map_add, map_sub, projectSection_restrict (s := {1,2}) (t := {0,1,2}) (by simp) (by simp),
      projectSection_restrict (s := {0,2}) (t := {0,1,2}) (by simp) (by simp),
      projectSection_restrict (s := {0,1}) (t := {0,1,2}) (by simp) (by simp)]
  · change projectSection {0,1,3} (by simp)
      (coverRestriction 57 1 (s := {1,3}) (t := {0,1,3}) (by decide) p.2.2.1 -
        coverRestriction 57 1 (s := {0,3}) (t := {0,1,3}) (by decide) p.1.2.2 +
        coverRestriction 57 1 (s := {0,1}) (t := {0,1,3}) (by decide) p.1.1) =
      CycleQ2ProjectiveCartierCochain.restriction 57 1 (s := {1,3}) (t := {0,1,3}) (by decide)
        (projectSection {1,3} (by simp) p.2.2.1) -
      CycleQ2ProjectiveCartierCochain.restriction 57 1 (s := {0,3}) (t := {0,1,3}) (by decide)
        (projectSection {0,3} (by simp) p.1.2.2) +
      CycleQ2ProjectiveCartierCochain.restriction 57 1 (s := {0,1}) (t := {0,1,3}) (by decide)
        (projectSection {0,1} (by simp) p.1.1)
    rw [map_add, map_sub, projectSection_restrict (s := {1,3}) (t := {0,1,3}) (by simp) (by simp),
      projectSection_restrict (s := {0,3}) (t := {0,1,3}) (by simp) (by simp),
      projectSection_restrict (s := {0,1}) (t := {0,1,3}) (by simp) (by simp)]
  · change projectSection {0,2,3} (by simp)
      (coverRestriction 57 1 (s := {2,3}) (t := {0,2,3}) (by decide) p.2.2.2 -
        coverRestriction 57 1 (s := {0,3}) (t := {0,2,3}) (by decide) p.1.2.2 +
        coverRestriction 57 1 (s := {0,2}) (t := {0,2,3}) (by decide) p.1.2.1) =
      CycleQ2ProjectiveCartierCochain.restriction 57 1 (s := {2,3}) (t := {0,2,3}) (by decide)
        (projectSection {2,3} (by simp) p.2.2.2) -
      CycleQ2ProjectiveCartierCochain.restriction 57 1 (s := {0,3}) (t := {0,2,3}) (by decide)
        (projectSection {0,3} (by simp) p.1.2.2) +
      CycleQ2ProjectiveCartierCochain.restriction 57 1 (s := {0,2}) (t := {0,2,3}) (by decide)
        (projectSection {0,2} (by simp) p.1.2.1)
    rw [map_add, map_sub, projectSection_restrict (s := {2,3}) (t := {0,2,3}) (by simp) (by simp),
      projectSection_restrict (s := {0,3}) (t := {0,2,3}) (by simp) (by simp),
      projectSection_restrict (s := {0,2}) (t := {0,2,3}) (by simp) (by simp)]
  · change projectSection {1,2,3} (by simp)
      (coverRestriction 57 1 (s := {2,3}) (t := {1,2,3}) (by decide) p.2.2.2 -
        coverRestriction 57 1 (s := {1,3}) (t := {1,2,3}) (by decide) p.2.2.1 +
        coverRestriction 57 1 (s := {1,2}) (t := {1,2,3}) (by decide) p.2.1) =
      CycleQ2ProjectiveCartierCochain.restriction 57 1 (s := {2,3}) (t := {1,2,3}) (by decide)
        (projectSection {2,3} (by simp) p.2.2.2) -
      CycleQ2ProjectiveCartierCochain.restriction 57 1 (s := {1,3}) (t := {1,2,3}) (by decide)
        (projectSection {1,3} (by simp) p.2.2.1) +
      CycleQ2ProjectiveCartierCochain.restriction 57 1 (s := {1,2}) (t := {1,2,3}) (by decide)
        (projectSection {1,2} (by simp) p.2.1)
    rw [map_add, map_sub, projectSection_restrict (s := {2,3}) (t := {1,2,3}) (by simp) (by simp),
      projectSection_restrict (s := {1,3}) (t := {1,2,3}) (by simp) (by simp),
      projectSection_restrict (s := {1,2}) (t := {1,2,3}) (by simp) (by simp)]

theorem projectSection_boundary012 :
    projectSection {0,1,2} (by simp) (boundary012 57 1 derivativeA 0) =
      coverSectionsEquiv 57 1 {0,1,2} (by simp) literalHomogeneousBoundary012 := by
  change coverSectionsEquiv 57 1 {0,1,2} (by simp)
    (degreeZero (surfaceGrade 57 1) (coverProduct_mem_grade 57 1 {0,1,2}) _) = _
  rw [← literalHomogeneousBoundary012_val, degreeZero_val]

theorem projectSection_boundary013 :
    projectSection {0,1,3} (by simp) (boundary013 57 1 derivativeA 0) =
      coverSectionsEquiv 57 1 {0,1,3} (by simp) literalHomogeneousBoundary013 := by
  change coverSectionsEquiv 57 1 {0,1,3} (by simp)
    (degreeZero (surfaceGrade 57 1) (coverProduct_mem_grade 57 1 {0,1,3}) _) = _
  rw [← literalHomogeneousBoundary013_val, degreeZero_val]

theorem projectTwo_original :
    projectTwo (cartierCycle 57 1 derivativeA 0).val = literalCocycle := by
  change toTwo 57 1 (nativeTwo _) = toTwo 57 1 _
  congr 1
  change FourFaces.mk (projectSection {0,1,2} _ (boundary012 57 1 derivativeA 0))
    (projectSection {0,1,3} _ (boundary013 57 1 derivativeA 0))
    (projectSection {0,2,3} _ 0) (projectSection {1,2,3} _ 0) = _
  rw [projectSection_boundary012, projectSection_boundary013, map_zero, map_zero]
  rfl

/-- The cup is projected from its independent original derivation/dlog
construction, rather than defined as the negative Cartier cocycle. -/
def projectedCup : CechTwo 57 1 := projectTwo cupRepresentative

def projectedCorrection : CechOne 57 1 := projectOne correctionOne

theorem projectedCup_eq :
    projectedCup = -literalCocycle -
      CycleQ2CechTwoToDerived.d1 (additiveSheaf 57 1) (coverFamily 57 1) projectedCorrection := by
  have h := congrArg projectTwo defect_eq_coboundary_add_cup
  rw [map_add, projectTwo_d1, defectRepresentative_eq_negative_original,
    map_neg, projectTwo_original] at h
  change -literalCocycle =
    CycleQ2CechTwoToDerived.d1 (additiveSheaf 57 1) (coverFamily 57 1) projectedCorrection + projectedCup at h
  rw [h]
  abel

theorem projectedCup_closed :
    CycleQ2CechTwoToDerived.d2 (additiveSheaf 57 1) (coverFamily 57 1) projectedCup = 0 := by
  change (CycleQ2CechTwoComparison.twoDifferentialHom
    (F := additiveSheaf 57 1) (coverFamily 57 1)) projectedCup = 0
  rw [projectedCup_eq, map_sub, map_neg]
  change -(CycleQ2CechTwoToDerived.d2 (additiveSheaf 57 1) (coverFamily 57 1) literalCocycle) -
    CycleQ2CechTwoToDerived.d2 (additiveSheaf 57 1) (coverFamily 57 1) (CycleQ2CechTwoToDerived.d1 (additiveSheaf 57 1) (coverFamily 57 1) projectedCorrection) = 0
  rw [literalCocycle_closed, CycleQ2CechTwoToDerived.d2_d1, neg_zero, sub_self]

def projectedCupCycle :
    CycleQ2CechTwoComparison.twoCycles (F := additiveSheaf 57 1) (coverFamily 57 1) :=
  ⟨projectedCup, projectedCup_closed⟩

/-- Genuine H'2 of the native projective additive structure sheaf. -/
def projectedDerivedClass : (additiveSheaf 57 1).H' 2 ⊤ :=
  CycleQ2CechTwoComparison.cyclesClass (coverFamily 57 1) literal_cover projectedCupCycle

theorem projectedDerivedClass_eq_negative_original :
    projectedDerivedClass = -literalDerivedClassAtTop := by
  have hc : projectedCupCycle = -CycleQ2LiteralCartierComparison.literalTwoCycle -
      CycleQ2CechTwoComparison.oneBoundaryHom (coverFamily 57 1) projectedCorrection :=
    Subtype.ext projectedCup_eq
  have hb : CycleQ2CechTwoComparison.cyclesClass (coverFamily 57 1) literal_cover
      (CycleQ2CechTwoComparison.oneBoundaryHom (coverFamily 57 1) projectedCorrection) = 0 :=
    CycleQ2CechTwoComparison.boundaries_le_kernel (coverFamily 57 1) literal_cover
      ⟨projectedCorrection, rfl⟩
  rw [projectedDerivedClass, hc, map_sub, map_neg, hb, sub_zero]
  rfl

/-- The canonical projective image has the actual original intrinsic
normal boundary and its already established sign. -/
theorem projectedDerivedClass_eq_originalNormalBoundary :
    projectedDerivedClass =
      CycleQ2GeometricIntrinsicCartierCohomology.literalOpenConnecting ⊤
        CycleQ2IntrinsicSurfaceNormalCohomology.literalIntrinsicNormalClass := by
  rw [projectedDerivedClass_eq_negative_original,
    CycleQ2GeometricIntrinsicCartierCohomology.literalOpenConnecting_originalNormalClass]

theorem projectedDerivedClass_ne_zero : projectedDerivedClass ≠ 0 := by
  rw [projectedDerivedClass_eq_negative_original, neg_ne_zero]
  exact literalDerivedClassAtTop_ne_zero

end CycleQ2LiteralCartierProjectedCup

end

#print axioms CycleQ2LiteralCartierProjectedCup.projectSection_restrict
#print axioms CycleQ2LiteralCartierProjectedCup.projectTwo_d1
#print axioms CycleQ2LiteralCartierProjectedCup.projectedDerivedClass_eq_negative_original
#print axioms CycleQ2LiteralCartierProjectedCup.projectedDerivedClass_ne_zero

#print axioms CycleQ2LiteralCartierProjectedCup.projectedDerivedClass_eq_originalNormalBoundary
