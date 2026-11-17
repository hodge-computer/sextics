import Proposal.GeometricLiteralNativeCupSectionValues

/-!
# The original projected cup on increasing refined faces

The actual section values of the transported cone cup are the original
four projective cup faces restricted to the twelve-open cover. On
nondecreasing original Cartier indices, repeated indices give the
correct zero values and the four strict faces retain their original
representatives. All equality-of-open transports are actual sheaf maps.

Prepared for fqlx with OpenAI ChatGPT assistance; see solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralNativeConeSectionFaces

open AlgebraicGeometry CategoryTheory TopologicalSpace
  CycleQ2InjectiveCech CycleQ2GeometricSheafLocalIso CycleQ2FiniteInjectiveCech
  CycleQ2CartierProjectiveCover CycleQ2ProjectiveCartierIntersections
  CycleQ2LiteralProjectiveIntersections CycleQ2LiteralNativeCupFrameGauge
  CycleQ2LiteralNativeCupOriginalFaces CycleQ2LiteralNativeGaugeSections
  CycleQ2LiteralGaugeAdjustedCohomology CycleQ2LiteralNativeCupSectionValues
  CycleQ2LiteralCartierProjectedCup CycleQ2LiteralCartierCupClass

attribute [local instance] CycleQ2LiteralCartierTransitionBinding.cubicSelfModule
  CycleQ2LiteralCartierTransitionBinding.cubicOppositeModule
  CycleQ2LiteralCartierTransitionBinding.cubicCentralScalar
  CycleQ2LiteralCartierTransitionBinding.cubicSmulCommClass
  CycleQ2GeometricSurfaceFirstOrder.reducedAlgebra
  CycleQ2GeometricKernelLocalization.localReductionAlgebra
  CycleQ2LiteralCartierSplittings.complexReductionTower
  CycleQ2LiteralCartierOverlapSplittings.baseReductionAlgebra

theorem refinedOriginalCup_faceValue (u v w : Vertex) (W : Opens (projectiveSurface 57 1))
    (hu : W ≤ cover u) (hv : W ≤ cover v) (hw : W ≤ cover w) :
    faceValue coefficientSheaf cover refinedOriginalCup u v w W hu hv hw =
      CycleQ2FourToFiniteCech.faceAt (coverFamily 57 1) projectedCup u.1 v.1 w.1 W
        (hu.trans (cover_first u)) (hv.trans (cover_first v)) (hw.trans (cover_first w)) := by
  rw [refinedOriginalCup, CycleQ2FiniteCechRefinement.faceValue_restrictTwo]
  exact CycleQ2FourToFiniteCech.faceValue_extendTwo (coverFamily 57 1) projectedCup u.1 v.1 w.1 W _ _ _

theorem coneCupValue_original012 (l m n : Fin 3) (W : Opens (projectiveSurface 57 1))
    (hu : W ≤ cover (0,l)) (hv : W ≤ cover (1,m)) (hw : W ≤ cover (2,n)) :
    coneCupValue (0,l) (1,m) (2,n) W hu hv hw =
      faceValue coefficientSheaf cover refinedOriginalCup (0,l) (1,m) (2,n) W hu hv hw := by
  rw [refinedOriginalCup_faceValue]
  unfold coneCupValue
  rw [projectedConeCup_original012, intersectionValue_projectSection]
  change res coefficientSheaf _ (projectSection {0,1,2} (by simp) cupRepresentative.1.1) =
    res coefficientSheaf _ (tripleSectionsEquiv 57 1 0 1 2
      (projectSection {0,1,2} (by simp) cupRepresentative.1.1))
  change res coefficientSheaf _ (projectSection {0,1,2} (by simp) cupRepresentative.1.1) =
    res coefficientSheaf _ (res coefficientSheaf _ (projectSection {0,1,2} (by simp) cupRepresentative.1.1))
  rw [res_comp]

theorem coneCupValue_original013 (l m n : Fin 3) (W : Opens (projectiveSurface 57 1))
    (hu : W ≤ cover (0,l)) (hv : W ≤ cover (1,m)) (hw : W ≤ cover (3,n)) :
    coneCupValue (0,l) (1,m) (3,n) W hu hv hw =
      faceValue coefficientSheaf cover refinedOriginalCup (0,l) (1,m) (3,n) W hu hv hw := by
  rw [refinedOriginalCup_faceValue]
  unfold coneCupValue
  rw [projectedConeCup_original013, intersectionValue_projectSection]
  change res coefficientSheaf _ (projectSection {0,1,3} (by simp) cupRepresentative.1.2) =
    res coefficientSheaf _ (tripleSectionsEquiv 57 1 0 1 3
      (projectSection {0,1,3} (by simp) cupRepresentative.1.2))
  change res coefficientSheaf _ (projectSection {0,1,3} (by simp) cupRepresentative.1.2) =
    res coefficientSheaf _ (res coefficientSheaf _ (projectSection {0,1,3} (by simp) cupRepresentative.1.2))
  rw [res_comp]

theorem coneCupValue_original023 (l m n : Fin 3) (W : Opens (projectiveSurface 57 1))
    (hu : W ≤ cover (0,l)) (hv : W ≤ cover (2,m)) (hw : W ≤ cover (3,n)) :
    coneCupValue (0,l) (2,m) (3,n) W hu hv hw =
      faceValue coefficientSheaf cover refinedOriginalCup (0,l) (2,m) (3,n) W hu hv hw := by
  rw [refinedOriginalCup_faceValue]
  unfold coneCupValue
  rw [projectedConeCup_original023, map_zero]
  change 0 = res coefficientSheaf _ (tripleSectionsEquiv 57 1 0 2 3
    (projectSection {0,2,3} (by simp) cupRepresentative.2.1))
  simp only [cupRepresentative023, map_zero]

theorem coneCupValue_original123 (l m n : Fin 3) (W : Opens (projectiveSurface 57 1))
    (hu : W ≤ cover (1,l)) (hv : W ≤ cover (2,m)) (hw : W ≤ cover (3,n)) :
    coneCupValue (1,l) (2,m) (3,n) W hu hv hw =
      faceValue coefficientSheaf cover refinedOriginalCup (1,l) (2,m) (3,n) W hu hv hw := by
  rw [refinedOriginalCup_faceValue]
  unfold coneCupValue
  rw [projectedConeCup_original123, map_zero]
  change 0 = res coefficientSheaf _ (tripleSectionsEquiv 57 1 1 2 3
    (projectSection {1,2,3} (by simp) cupRepresentative.2.2))
  simp only [cupRepresentative123, map_zero]

theorem projectedConeCup_sameFirstCartier (s : Finset Vertex) (a : Fin 4) (l m : Fin 3) (w : Vertex)
    (hu : (a,l) ∈ s) (hv : (a,m) ∈ s) (hw : w ∈ s) :
    projectedConeCup s (a,l) (a,m) w hu hv hw = 0 := by
  rw [projectedConeCup_corrections]
  exact sub_self _

theorem coneCupValue_refined_repeatFirst (a : Fin 4) (l m : Fin 3) (w : Vertex)
    (W : Opens (projectiveSurface 57 1)) (hu : W ≤ cover (a,l)) (hv : W ≤ cover (a,m)) (hw : W ≤ cover w) :
    coneCupValue (a,l) (a,m) w W hu hv hw =
      faceValue coefficientSheaf cover refinedOriginalCup (a,l) (a,m) w W hu hv hw := by
  unfold coneCupValue
  rw [projectedConeCup_sameFirstCartier, map_zero]
  rw [refinedOriginalCup, CycleQ2FiniteCechRefinement.faceValue_restrictTwo]
  exact (oldFiniteCup_normalized.repeat12 a w.1 W (hu.trans (cover_first (a,l))) (hw.trans (cover_first w))).symm

theorem coneCupValue_refined_repeatLast (u : Vertex) (a : Fin 4) (m n : Fin 3)
    (W : Opens (projectiveSurface 57 1)) (hu : W ≤ cover u) (hv : W ≤ cover (a,m)) (hw : W ≤ cover (a,n)) :
    coneCupValue u (a,m) (a,n) W hu hv hw =
      faceValue coefficientSheaf cover refinedOriginalCup u (a,m) (a,n) W hu hv hw := by
  unfold coneCupValue
  rw [projectedConeCup_sameLastCartier, map_zero]
  rw [refinedOriginalCup, CycleQ2FiniteCechRefinement.faceValue_restrictTwo]
  exact (oldFiniteCup_normalized.repeat23 u.1 a W (hu.trans (cover_first u)) (hv.trans (cover_first (a,m)))).symm

theorem coneCupValue_refined_nondecreasing (u v w : Vertex) (huv : u.1 ≤ v.1) (hvw : v.1 ≤ w.1)
    (W : Opens (projectiveSurface 57 1)) (hu : W ≤ cover u) (hv : W ≤ cover v) (hw : W ≤ cover w) :
    coneCupValue u v w W hu hv hw = faceValue coefficientSheaf cover refinedOriginalCup u v w W hu hv hw := by
  rcases u with ⟨a,l⟩
  rcases v with ⟨b,m⟩
  rcases w with ⟨c,n⟩
  by_cases hab : a = b
  · subst b
    exact coneCupValue_refined_repeatFirst a l m (c,n) W hu hv hw
  by_cases hbc : b = c
  · subst c
    exact coneCupValue_refined_repeatLast (a,l) b m n W hu hv hw
  have hab' : a.val < b.val := by
    have hne : a.val ≠ b.val := fun h => hab (Fin.ext h)
    change a.val ≤ b.val at huv
    omega
  have hbc' : b.val < c.val := by
    have hne : b.val ≠ c.val := fun h => hbc (Fin.ext h)
    change b.val ≤ c.val at hvw
    omega
  have hcases : (a.val = 0 ∧ b.val = 1 ∧ c.val = 2) ∨
      (a.val = 0 ∧ b.val = 1 ∧ c.val = 3) ∨
      (a.val = 0 ∧ b.val = 2 ∧ c.val = 3) ∨
      (a.val = 1 ∧ b.val = 2 ∧ c.val = 3) := by
    have ha := a.isLt
    have hb := b.isLt
    have hc := c.isLt
    omega
  rcases hcases with h | h | h | h
  · rcases h with ⟨ha,hb,hc⟩
    have ha' : a = 0 := Fin.ext ha
    have hb' : b = 1 := Fin.ext hb
    have hc' : c = 2 := Fin.ext hc
    subst a
    subst b
    subst c
    exact coneCupValue_original012 l m n W hu hv hw
  · rcases h with ⟨ha,hb,hc⟩
    have ha' : a = 0 := Fin.ext ha
    have hb' : b = 1 := Fin.ext hb
    have hc' : c = 3 := Fin.ext hc
    subst a
    subst b
    subst c
    exact coneCupValue_original013 l m n W hu hv hw
  · rcases h with ⟨ha,hb,hc⟩
    have ha' : a = 0 := Fin.ext ha
    have hb' : b = 2 := Fin.ext hb
    have hc' : c = 3 := Fin.ext hc
    subst a
    subst b
    subst c
    exact coneCupValue_original023 l m n W hu hv hw
  · rcases h with ⟨ha,hb,hc⟩
    have ha' : a = 1 := Fin.ext ha
    have hb' : b = 2 := Fin.ext hb
    have hc' : c = 3 := Fin.ext hc
    subst a
    subst b
    subst c
    exact coneCupValue_original123 l m n W hu hv hw

end CycleQ2LiteralNativeConeSectionFaces

end

#print axioms CycleQ2LiteralNativeConeSectionFaces.coneCupValue_original012
#print axioms CycleQ2LiteralNativeConeSectionFaces.coneCupValue_original013
#print axioms CycleQ2LiteralNativeConeSectionFaces.coneCupValue_refined_nondecreasing
