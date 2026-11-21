import Proposal.GeometricMarkedRelativeCylinderDetector
import Proposal.GeometricMarkedClosureBoundaryDimension
import Proposal.GeometricSmoothDimensionLower

/-!
# A marked point outside the projected boundary of its own graph

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace CycleQ2MarkedGenericCylinderDetector
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open CycleQ2LiteralIncidenceRelativeSpread CycleQ2LiteralIncidenceNormalizedSlice
  CycleQ2LiteralIncidenceRelativeCompletion CycleQ2LiteralIncidenceRelativeCorrespondence
  CycleQ2LiteralIncidenceGenericCorrespondence CycleQ2IncidenceEtaleParameter
  CycleQ2LiteralIncidenceGenericModel CycleQ2LiteralIncidenceGenericSmoothCurve
  CycleQ2GenericSmoothCurveGraph CycleQ2MarkedCylinderQuasiFinite
open CycleQ2IncidenceSeedFiberCover
open CycleQ2LiteralIncidenceRelativeCylinder (relativeQ)

private theorem qf_comp {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X)
    (hf : f.QuasiFiniteAt x) (hg : g.QuasiFiniteAt (f x)) : (f ≫ g).QuasiFiniteAt x := by
  rw [Scheme.Hom.QuasiFiniteAt, Scheme.Hom.stalkMap_comp, CommRingCat.hom_comp]
  exact RingHom.QuasiFinite.comp hf hg

private theorem qf_of_comp {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X)
    (h : (f ≫ g).QuasiFiniteAt x) : f.QuasiFiniteAt x := by
  rw [Scheme.Hom.QuasiFiniteAt, Scheme.Hom.stalkMap_comp, CommRingCat.hom_comp] at h
  exact RingHom.QuasiFinite.of_comp h

theorem marked_target_quasiFinite (V : parameterScheme.Opens) (t : Fin 3 → ℂ)
    {C D : Scheme} (r : C ⟶ Completion V) (c : C ⟶ Spec (CommRingCat.of genericField))
    (hr : r ≫ structureMap V = c ≫ CycleQ2LiteralIncidenceGenericCorrespondence.genericPoint)
    (j : D ⟶ C) (a : D ⟶ Time toRaw V) (ha : j ≫ r = a ≫ CycleQ2LiteralIncidenceRelativeCompletion.inclusion V)
    [IsOpenImmersion j] [LocallyQuasiFinite a] (z : TestSurface V t a)
    (hz : (relativeQ toRaw V t).QuasiFiniteAt ((pullback.snd a (curveMap toRaw V t)) z)) :
    (target V t r c hr).QuasiFiniteAt ((fromTest V t r j a ha) z) := by
  let f := fromTest V t r j a ha
  let q := target V t r c hr
  let s := pullback.snd a (curveMap toRaw V t)
  let β := pullback.fst ambientStructure (CycleQ2LiteralIncidenceGenericCorrespondence.genericPoint)
  have ho : q ≫ β = toGraph V t r ≫ ambientProjection V t := by
    simp only [q, β, target, Category.assoc, genericAmbientProjection,
      CycleQ2CoefficientBaseChange.changeMap_fst, toGenericGraph, pullback.lift_fst_assoc]
  have eq : (f ≫ q) ≫ β = s ≫ relativeQ toRaw V t := by
    rw [Category.assoc,ho]
    exact test_to_original_ambient V t r j a ha
  have h : ((f ≫ q) ≫ β).QuasiFiniteAt z := eq ▸ qf_comp s _ z (s.quasiFiniteAt z) hz
  have : IsOpenImmersion f := MorphismProperty.of_isPullback (test_square V t r j a ha) inferInstance
  exact Scheme.Hom.quasiFiniteAt_comp_iff_of_isOpenImmersion.mp (qf_of_comp _ β z h)

end CycleQ2MarkedGenericCylinderDetector

namespace CycleQ2MarkedImageDimensionLower
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Topology Order Set

private theorem dim_le_of_reflects_equal_specializations {X Y : Type*} [TopologicalSpace X]
    [QuasiSober X] [TopologicalSpace Y] [T0Space Y] (f : X → Y) (hf : Continuous f)
    (hs : ∀ x y : X, x ⤳ y → f x = f y → x = y) :
    topologicalKrullDim X ≤ topologicalKrullDim Y := by
  let F := IrreducibleCloseds.map f hf
  apply Order.krullDim_le_of_strictMono F
  intro A B hAB
  refine lt_of_le_of_ne (IrreducibleCloseds.map_mono hf hAB.le) ?_
  intro he
  let x := A.isIrreducible.genericPoint
  let y := B.isIrreducible.genericPoint
  have hx : IsGenericPoint x (A : Set X) := A.isIrreducible.isGenericPoint_genericPoint A.isClosed
  have hy : IsGenericPoint y (B : Set X) := B.isIrreducible.isGenericPoint_genericPoint B.isClosed
  have hfx : IsGenericPoint (f x) (F A : Set Y) := hx.image hf
  have hfy : IsGenericPoint (f y) (F B : Set Y) := hy.image hf
  have hyx : y = x := hs y x (hy.specializes (hAB.le hx.mem)) (hfy.eq (he ▸ hfx))
  exact hAB.ne (IrreducibleCloseds.ext (hx.def.symm.trans (hyx ▸ hy.def)))

/-- The image of a locally quasi-finite map cannot be contained in a
subspace of smaller dimension. This also applies when that subspace is reducible. -/
theorem dimension_le_of_range_subset {X Y : Scheme.{0}} (f : X ⟶ Y)
    [LocallyQuasiFinite f] {B : Set Y} (hf : Set.range f ⊆ B) :
    topologicalKrullDim X ≤ topologicalKrullDim B := by
  let h : X → B := fun x => ⟨f x, hf ⟨x,rfl⟩⟩
  apply dim_le_of_reflects_equal_specializations h (f.continuous.subtype_mk _)
  intro x y hxy he
  exact (f.isDiscrete_preimage_singleton (f y)).eq_of_specializes hxy (congrArg Subtype.val he) rfl

/-- At a quasi-finite point, the entire source image cannot be contained in
a subset of dimension less than that of every nonempty source open. -/
theorem dimension_and_outside_of_quasiFiniteAt {X Y : Scheme.{0}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] (z : X) (hz : f.QuasiFiniteAt z) (B : Set Y)
    (hb : topologicalKrullDim B ≤ 1)
    (hX : ∀ U : X.Opens, (U : Set X).Nonempty → (2 : WithBot ℕ∞) ≤ topologicalKrullDim U.toScheme) :
    (2 : WithBot ℕ∞) ≤ topologicalKrullDim (Set.range f) ∧
      ∃ x : X, f.QuasiFiniteAt x ∧ f x ∉ B := by
  let W := f.quasiFiniteLocus
  have hW : (W : Set X).Nonempty := ⟨z,hz⟩
  have hdim (A : Set Y) (hA : Set.range (W.ι ≫ f) ⊆ A) :
      (2 : WithBot ℕ∞) ≤ topologicalKrullDim A :=
    (hX W hW).trans (dimension_le_of_range_subset (W.ι ≫ f) hA)
  refine ⟨hdim (Set.range f) ?_,?_⟩
  · rintro _ ⟨w,rfl⟩
    exact ⟨W.ι w,rfl⟩
  · by_contra! h
    have hle : Set.range (W.ι ≫ f) ⊆ B := by rintro _ ⟨w,rfl⟩; exact h _ w.property
    exact (by decide : ¬ (2 : WithBot ℕ∞) ≤ 1) ((hdim B hle).trans hb)

end CycleQ2MarkedImageDimensionLower

namespace CycleQ2MarkedGenericSurvives
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Topology Order Set
open CycleQ2LiteralIncidenceRelativeSpread CycleQ2LiteralIncidenceNormalizedSlice
  CycleQ2LiteralIncidenceRelativeCompletion CycleQ2LiteralIncidenceRelativeCorrespondence
  CycleQ2LiteralIncidenceGenericCorrespondence CycleQ2IncidenceEtaleParameter
  CycleQ2GenericSmoothCurveGraph CycleQ2MarkedGenericCylinderDetector
  CycleQ2MarkedClosureBoundaryDimension CycleQ2MarkedImageDimensionLower
open CycleQ2IncidenceSeedFiberCover (seedBasePoint)
open CycleQ2MarkedCylinderQuasiFinite

theorem exists_marked_point_outside_projected_boundary :
    ∃ (t : Fin 3 → ℂ), AlgebraicIndependent ℚ t ∧ ∃ (V : parameterScheme.Opens), seedBasePoint ∈ V ∧
      ∃ (C : Scheme) (c : C ⟶ Spec (CommRingCat.of genericField)) (r : C ⟶ Completion V)
        (hc : r ≫ structureMap V = c ≫ CycleQ2LiteralIncidenceGenericCorrespondence.genericPoint)
        (D : Scheme) (j : D ⟶ C) (a : D ⟶ Time toRaw V)
        (ha : j ≫ r = a ≫ CycleQ2LiteralIncidenceRelativeCompletion.inclusion V),
        let m := fromTest V t r j a ha
        let g := target V t r c hc
        let B := (m.imageι ≫ g) '' (Set.range m.toImage)ᶜ
        IsIntegral C ∧ IsProper c ∧ SmoothOfRelativeDimension 1 c ∧
        (∃ q : C ⟶ CycleQ2LaurentProjectiveLine.line genericField, IsFinite q ∧ IsDominant q ∧
          q ≫ CycleQ2ProjectiveLineStructure.structureMap genericField = c) ∧
        IsOpenImmersion j ∧ IsDominant j ∧ SmoothOfRelativeDimension 1 (curveMap toRaw V t) ∧
        IsProper (m.imageι ≫ g) ∧ topologicalKrullDim B ≤ 1 ∧
        (2 : WithBot ℕ∞) ≤ topologicalKrullDim (Set.range (m ≫ g)) ∧
        ∃ z : TestSurface V t a, g.QuasiFiniteAt (m z) ∧ g (m z) ∉ B := by
  obtain ⟨t,ht,hw⟩ := exists_time_open_meeting_quasiFinite
  have : IrreducibleSpace monicBase := inferInstanceAs (IrreducibleSpace (Spec (CommRingCat.of MonicRing)))
  obtain ⟨V,hV,_,hsCurve,_,_,_,_,_,_⟩ := spread_of_independent toRaw seedPoint seedPoint_toRaw t ht
  have : Smooth (curveMap toRaw V t) := hsCurve.smooth
  obtain ⟨W,hW,hq⟩ := hw V hV inferInstance
  obtain ⟨C,c,r,hc,hC,hp,_,_,_,_,_,⟨q,hqfin,hqdom,hqc,hqd⟩,D,j,a,ha,hj,hjd,hD,hW',haq,_⟩ :=
    CycleQ2GenericGraphFiniteProjection.exists_smooth_curve_graph_with_quasiFinite_test (t := t) W hW
  have hqCurve : ∃ l : C ⟶ CycleQ2LaurentProjectiveLine.line genericField, IsFinite l ∧ IsDominant l ∧
      l ≫ CycleQ2ProjectiveLineStructure.structureMap genericField = c := ⟨q,hqfin,hqdom,hqc⟩
  have hc₁ : SmoothOfRelativeDimension 1 c := hqc ▸ hqd
  have := smoothOfRelativeDimension_isStableUnderBaseChange 1
  have : SmoothOfRelativeDimension 1 (pullback.fst a (curveMap toRaw V t)) :=
    MorphismProperty.pullback_fst _ _ hsCurve
  have : SmoothOfRelativeDimension 1 (j ≫ c) := smoothOfRelativeDimension_comp 0 1 j c
  have hd := smoothOfRelativeDimension_comp 1 1 (pullback.fst a (curveMap toRaw V t)) (j ≫ c)
  obtain ⟨z,_,hrel⟩ := hq a hW' (Classical.choice hD)
  have hz := marked_target_quasiFinite V t r c hc j a ha z hrel
  let m := fromTest V t r j a ha
  let g := target V t r c hc
  have : IsOpenImmersion m := MorphismProperty.of_isPullback (test_square V t r j a ha) inferInstance
  have : IsProper g := target_proper V t r c hc
  let B := (m.imageι ≫ g) '' (Set.range m.toImage)ᶜ
  have hB : topologicalKrullDim B ≤ 1 := (boundary_dimensions V t r c j a ha hc hsCurve).2
  let p := pullback.fst a (curveMap toRaw V t) ≫ j ≫ c
  have : SmoothOfRelativeDimension 2 p := hd
  have hdim (U : (TestSurface V t a).Opens) (hU : (U : Set (TestSurface V t a)).Nonempty) :
      (2 : WithBot ℕ∞) ≤ topologicalKrullDim U.toScheme :=
    by
      have : Nonempty U.toScheme := hU.to_subtype
      have : SmoothOfRelativeDimension 2 (U.ι ≫ p) := smoothOfRelativeDimension_comp 0 2 U.ι p
      exact CycleQ2SmoothDimensionLower.le_topologicalKrullDim 2 (U.ι ≫ p)
  obtain ⟨himage,w,hw,hout⟩ := dimension_and_outside_of_quasiFiniteAt (m ≫ g) z
    (Scheme.Hom.quasiFiniteAt_comp_iff_of_isOpenImmersion.mpr hz) B hB hdim
  exact ⟨t,ht,V,hV,C,c,r,hc,D,j,a,ha,hC,hp,hc₁,hqCurve,hj,hjd,hsCurve,inferInstance,hB,himage,w,
    Scheme.Hom.quasiFiniteAt_comp_iff_of_isOpenImmersion.mp hw,hout⟩

end CycleQ2MarkedGenericSurvives

#print axioms CycleQ2MarkedGenericSurvives.exists_marked_point_outside_projected_boundary
