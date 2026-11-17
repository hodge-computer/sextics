import Proposal.GeometricLiteralCotangentRestriction
import Proposal.GeometricLiteralCotangentShortExact
import Proposal.GeometricLiteralSheafOneClasses
import Proposal.GeometricFiniteCechConnecting
import Proposal.GeometricIncidenceFirstOrderCanonicalH2

/-!
# The original Chern class under the cotangent connecting map

The alternating tensor lifts on the native intersections give a one-cochain
of the actual restricted cotangent sheaf. Its reduction is the original
Chern cocycle. Its boundary is the image of the original scalar cup.
The finite-cover connecting theorem identifies the resulting Ext class
with the nonzero class computed from the original Cartier faces.

Prepared for fqlx with OpenAI ChatGPT assistance; see solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralCotangentConnecting

open CategoryTheory CategoryTheory.Abelian AlgebraicGeometry Opposite TopologicalSpace
  CycleQ2InjectiveCech CycleQ2GeometricSheafLocalIso CycleQ2FiniteInjectiveCech
  CycleQ2FiniteCechDescent CycleQ2FiniteCechHOne CycleQ2FiniteCechConnecting
  CycleQ2LiteralProjectiveIntersections CycleQ2LiteralProjectiveIntersectionRestrictions
  CycleQ2LiteralNativeGaugeSections CycleQ2LiteralNativeCupSectionValues
  CycleQ2LiteralNativeCotangent CycleQ2LiteralCotangentOrderedLift
  CycleQ2LiteralNativeDifferentialSections CycleQ2LiteralNativeChernCocycle
  CycleQ2LiteralNativeCupDerivedClass CycleQ2LiteralSheafOneClasses
  CycleQ2LiteralSheafChernKodairaSpencerCup CycleQ2LiteralCotangentShortExact
  CycleQ2LiteralCotangentRestriction

open CycleQ2CechTwoToDerived (app app_res)

attribute [local instance] CycleQ2LiteralProjectiveIntersectionKernel.nativeReductionAlgebra
  CycleQ2LiteralProjectiveIntersectionComplex.thickComplexAlgebra
  CycleQ2LiteralProjectiveIntersectionComplex.closedComplexAlgebra
  CycleQ2LiteralProjectiveIntersectionComplex.thickComplexSMul
  CycleQ2LiteralProjectiveIntersectionComplex.closedComplexSMul
  CycleQ2LiteralProjectiveIntersectionComplex.thickComplexModule
  CycleQ2LiteralProjectiveIntersectionComplex.closedComplexModule
  CycleQ2LiteralProjectiveIntersectionComplex.complexReductionTower

local instance additiveHasExt : HasExt.{1} (TopCat.Sheaf AddCommGrpCat.{0}
    (CycleQ2LiteralProjectiveCotangent.ClosedSurface : TopCat)) := HasExt.standard _

local instance schemeSheavesHasExt (X : Scheme.{0}) :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}) := HasExt.standard _

private theorem class_congr {F : AbSheaf Surface} {b b' : One F cover}
    (hb : IsOneCocycle F cover b) (hb' : IsOneCocycle F cover b') (e : b = b') :
    cechOneClass cover cover_covers b hb = cechOneClass cover cover_covers b' hb' := by
  cases e
  rfl

/-- An ordered cotangent lift of the Cartier cocycle and its actual boundary
on every subopen of a triple intersection. -/
theorem exists_chernOne_nativeLift :
    ∃ b : One cotangentAdditiveComplex.X₂ cover,
      mapOne cover cotangentAdditiveComplex.g b = chernOne ∧
      ∀ u v w W hu hv hw,
        boundaryValue cotangentAdditiveComplex.X₂ cover b u v w W hu hv hw =
          app cotangentAdditiveComplex.f W
            (faceValue coefficientSheaf cover nativeCupCocycle u v w W hu hv hw) := by
  let M : AbSheaf Surface := cotangentAdditiveComplex.X₂
  let b : One M cover := fun u v => res M (common_le_pair u v (cover u ⊓ cover v)
    inf_le_left inf_le_right) (nativeTensorToSheaf {u,v} (by simp) (orderedLift {u,v} u v (by simp) (by simp)))
  have common (s : Finset Vertex) (hs : s.Nonempty) (u v : Vertex)
      (hu : u ∈ s) (hv : v ∈ s) (W : Opens Surface) (hW : W ≤ closedOpen s)
      (hU : W ≤ cover u) (hV : W ≤ cover v) :
      edgeValue M cover b u v W hU hV =
        res M hW (nativeTensorToSheaf s hs (orderedLift s u v hu hv)) := by
    have hst : ({u,v} : Finset Vertex) ⊆ s := by
      simpa only [Finset.insert_subset_iff, Finset.singleton_subset_iff] using And.intro hu hv
    have hr (z : NativeCotangent {u,v}) :
        res M (closedOpen_mono hst) (nativeTensorToSheaf {u,v} (by simp) z) =
          nativeTensorToSheaf s hs (nativeTensorRestriction hst z) :=
      nativeTensorToSheaf_restrict hst (by simp) hs z
    unfold edgeValue
    dsimp only [b]
    rw [res_comp, ← orderedLift_restrict hst u v (by simp) (by simp),
      ← hr, res_comp]
  have hb : ∀ u v w W hu hv hw,
      boundaryValue M cover b u v w W hu hv hw =
        app cotangentAdditiveComplex.f W
          (faceValue coefficientSheaf cover nativeCupCocycle u v w W hu hv hw) := by
    intro u v w W hu hv hw
    let s : Finset Vertex := {u,v,w}
    have hs : s.Nonempty := by simp [s]
    have hsu : u ∈ s := by simp [s]
    have hsv : v ∈ s := by simp [s]
    have hsw : w ∈ s := by simp [s]
    have hW : W ≤ closedOpen s := common_le_triple u v w W hu hv hw
    have heps (x : ClosedRing s) : nativeTensorToSheaf s hs (nativeEpsilonInclusion s x) =
        app cotangentAdditiveComplex.f (closedOpen s) (closedSectionsEquiv s hs x) :=
      nativeTensorToSheaf_epsilon s hs x
    let J : NativeCotangent s →+ Sections M W := (res M hW).comp (nativeTensorToSheaf s hs)
    have hd := congrArg (fun x => J x) (orderedLift_boundary s u v w hsu hsv hsw)
    simp only [map_add, map_sub] at hd
    unfold boundaryValue
    rw [common s hs v w hsv hsw W hW hv hw, common s hs u w hsu hsw W hW hu hw,
      common s hs u v hsu hsv W hW hu hv]
    refine hd.trans ?_
    change res M hW (nativeTensorToSheaf s hs (nativeEpsilonInclusion s _)) = _
    rw [heps, faceValue_eq_orderedCup s hs u v w hsu hsv hsw W hW hu hv hw]
    exact (app_res cotangentAdditiveComplex.f hW
      (closedSectionsEquiv s hs (orderedCup s u v w hsu hsv hsw))).symm
  have he : mapOne cover cotangentAdditiveComplex.g b = chernOne := by
    funext u v
    dsimp only [mapOne, b, chernOne, chernValue, nativeChernSection]
    have hq (z : NativeCotangent {u,v}) :
        app cotangentAdditiveComplex.g (closedOpen {u,v}) (nativeTensorToSheaf {u,v} (by simp) z) =
          nativeFormToSheaf {u,v} (by simp) (nativeCotangentReduction {u,v} z) :=
      nativeTensorToSheaf_reduce {u,v} (by simp) z
    rw [app_res, hq, orderedLift_reduce]
    rfl
  exact ⟨b, he, hb⟩

/-- The connecting image of the actual derived Chern class is the alternating
native Kodaira--Spencer cup on the original twelve-open cover. -/
theorem chernDerivedClass_connecting_native :
    chernDerivedClass.comp cotangentAdditiveShortExact.extClass rfl = nativeCupDerivedClass := by
  obtain ⟨b, he, hb⟩ := exists_chernOne_nativeLift
  have hd := cechOneClass_connecting cover cotangentAdditiveShortExact cover_covers b nativeCupCocycle
    nativeCupCocycle_normalized nativeCupCocycle_closed hb
  have hc := class_congr (primitive_image_closed cover cotangentAdditiveComplex nativeCupCocycle b hb)
    chernOne_closed he
  change (cechOneClass cover cover_covers chernOne chernOne_closed).comp cotangentAdditiveShortExact.extClass rfl = _
  rw [← hc]
  exact hd


theorem chernDerivedClass_connecting_eq_cup :
    chernDerivedClass.comp cotangentAdditiveShortExact.extClass rfl = sheafCupDerivedClass :=
  chernDerivedClass_connecting_native.trans sheafCupDerivedClass_eq_native.symm

/-- This is the original structure-sheaf class identified by the projected
Cartier calculation. -/
theorem chernDerivedClass_connecting_eq_original :
    chernDerivedClass.comp cotangentAdditiveShortExact.extClass rfl =
      CycleQ2LiteralCartierProjectedCup.projectedDerivedClass :=
  chernDerivedClass_connecting_native.trans nativeCupDerivedClass_eq_original

theorem chernDerivedClass_connecting_eq_normalBoundary :
    chernDerivedClass.comp cotangentAdditiveShortExact.extClass rfl =
      CycleQ2GeometricIntrinsicCartierCohomology.literalOpenConnecting ⊤
        CycleQ2IntrinsicSurfaceNormalCohomology.literalIntrinsicNormalClass :=
  chernDerivedClass_connecting_eq_original.trans
    CycleQ2LiteralCartierProjectedCup.projectedDerivedClass_eq_originalNormalBoundary

/-- The retained incidence tangent's own weighted cubic takes the Chern
connecting class to a nonzero class of the canonical bundle. -/
theorem firstOrderCubic_connecting_ne_zero :
    CycleQ2CanonicalCubicDiagram.cubicH2
      CycleQ2IncidenceFirstOrderCanonicalH2.firstOrderWeightedCubic
      (chernDerivedClass.comp cotangentAdditiveShortExact.extClass rfl) ≠ 0 := by
  rw [chernDerivedClass_connecting_eq_original,
    CycleQ2LiteralCartierProjectedCup.projectedDerivedClass_eq_negative_original, map_neg]
  exact neg_ne_zero.mpr CycleQ2IncidenceFirstOrderCanonicalH2.firstOrder_canonicalH2_ne_zero

theorem chernDerivedClass_connecting_ne_zero :
    chernDerivedClass.comp cotangentAdditiveShortExact.extClass rfl ≠ 0 := by
  rw [chernDerivedClass_connecting_native]
  exact nativeCupDerivedClass_ne_zero

/-- No degree-one class of the restricted total cotangent sheaf reduces
to the actual Chern class. -/
theorem chernDerivedClass_has_no_lift (η : cotangentAdditiveComplex.X₂.H' 1 ⊤) :
    η.comp (Ext.mk₀ cotangentAdditiveComplex.g) (Nat.add_zero 1) ≠ chernDerivedClass := by
  intro h
  apply chernDerivedClass_connecting_ne_zero
  rw [← h, Ext.comp_assoc_of_second_deg_zero, ShortComplex.ShortExact.comp_extClass, Ext.comp_zero]

end CycleQ2LiteralCotangentConnecting

end

#print axioms CycleQ2LiteralCotangentConnecting.chernDerivedClass_connecting_eq_normalBoundary
#print axioms CycleQ2LiteralCotangentConnecting.chernDerivedClass_connecting_ne_zero

#print axioms CycleQ2LiteralCotangentConnecting.chernDerivedClass_has_no_lift

#print axioms CycleQ2LiteralCotangentConnecting.firstOrderCubic_connecting_ne_zero
