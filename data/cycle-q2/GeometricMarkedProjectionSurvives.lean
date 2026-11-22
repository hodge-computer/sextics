import Proposal.GeometricMarkedParameterSpread
import Proposal.GeometricMarkedClosureBoundaryDimension
import Proposal.GeometricSmoothDimensionLower
import Mathlib.GroupTheory.CosetCover

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

open CycleQ2LiteralIncidenceGenericModel (Fiber TimeFiber projection genericMorphism)
open CycleQ2LiteralIncidenceGenericSmoothCurve (testMap)
open CycleQ2LiteralIncidenceRelativeNormalization (normalizedMap toCompletion)

/-- The dense test on the proper generic parameter curve is a dense open of the
generic fiber of an integral affine neighborhood containing the seed tangent. -/
def SeedCompatible (t : Fin 3 → ℂ) (V : parameterScheme.Opens) (hV : seedBasePoint ∈ V) {C D : Scheme}
    (c : C ⟶ Spec (CommRingCat.of genericField)) (r : C ⟶ Completion V)
    (j : D ⟶ C) (a : D ⟶ Time toRaw V) : Prop :=
  CycleQ2MarkedThickCylinderChart.HasTracedSeedCurve t ∧
  ∃ U : (Time toRaw V).Opens, IsAffineOpen U ∧ CycleQ2MarkedParameterSpread.marked V hV ∈ U ∧
    IsIntegral U.toScheme ∧ IsIntegral ((testMap V) ⁻¹ᵁ U).toScheme ∧
    (∃ e : Spec (CommRingCat.of (DualNumber ℂ)) ⟶ U.toScheme,
      e ≫ U.ι = CycleQ2MarkedParameterSpread.tangent V hV) ∧
    ∃ (rK : C ⟶ Fiber V) (k : D ⟶ ((testMap V) ⁻¹ᵁ U).toScheme),
      IsOpenImmersion k ∧ IsDominant k ∧ k ≫ ((testMap V) ⁻¹ᵁ U).ι ≫ testMap V = a ∧
      k ≫ ((testMap V) ⁻¹ᵁ U).ι ≫ CycleQ2LiteralIncidenceGenericModel.inclusion V = j ≫ rK ∧
      rK ≫ projection V = c ∧ rK ≫ pullback.snd genericMorphism (normalizedMap V) ≫ toCompletion V = r

theorem exists_compatible_marked_point_outside_projected_boundary :
    ∃ (t : Fin 3 → ℂ), AlgebraicIndependent ℚ t ∧ ∃ (V : parameterScheme.Opens) (hV : seedBasePoint ∈ V),
      ∃ (C : Scheme) (c : C ⟶ Spec (CommRingCat.of genericField)) (r : C ⟶ Completion V)
        (hc : r ≫ structureMap V = c ≫ CycleQ2LiteralIncidenceGenericCorrespondence.genericPoint)
        (D : Scheme) (j : D ⟶ C) (a : D ⟶ Time toRaw V)
        (ha : j ≫ r = a ≫ CycleQ2LiteralIncidenceRelativeCompletion.inclusion V),
        SeedCompatible t V hV c r j a ∧
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
  obtain ⟨t,ht,htrace,V,hV,hsCurve,U,hUA,hmark,hUI,hUK,hε,hq⟩ := CycleQ2MarkedParameterSpread.exists_detected
  obtain ⟨C,rK,hC,hp,hc₁,hqCurve,D,k,j,hk,hkd,hj,hjd,hkj⟩ :=
    CycleQ2MarkedParameterSpread.normalized_completion V U
  let c := rK ≫ projection V
  let n := pullback.snd genericMorphism (normalizedMap V) ≫ toCompletion V
  let r := rK ≫ n
  let a := k ≫ ((testMap V) ⁻¹ᵁ U).ι ≫ testMap V
  have hc : r ≫ structureMap V = c ≫ CycleQ2LiteralIncidenceGenericCorrespondence.genericPoint := by
    change (rK ≫ _ ≫ _) ≫ _ = (rK ≫ _) ≫ _
    simp only [Category.assoc]
    change rK ≫ pullback.snd _ _ ≫ normalizedMap V = rK ≫ pullback.fst _ _ ≫ genericMorphism
    rw [pullback.condition]
  have ha : j ≫ r = a ≫ CycleQ2LiteralIncidenceRelativeCompletion.inclusion V := by
    change j ≫ rK ≫ n = _
    rw [← Category.assoc j rK,← hkj]
    simp only [a,n,Category.assoc,CycleQ2LiteralIncidenceGenericModel.inclusion,testMap,
      pullback.condition_assoc,CycleQ2LiteralIncidenceRelativeNormalization.open_toCompletion]
  have hCompat : SeedCompatible t V hV c r j a :=
    ⟨htrace,U,hUA,hmark,hUI,hUK,hε,rK,k,hk,hkd,rfl,hkj,rfl,rfl⟩
  have : LocallyQuasiFinite genericMorphism :=
    (HasRingHomProperty.Spec_iff (P := @LocallyQuasiFinite)).mpr
      (RingHom.quasiFinite_algebraMap.mpr (inferInstance : Algebra.QuasiFinite MonicRing genericField))
  have : LocallyQuasiFinite (testMap V) := by dsimp only [testMap]; infer_instance
  have : LocallyQuasiFinite a := by dsimp only [a]; infer_instance
  have hW' : Set.range a ⊆ (U : Set (Time toRaw V)) := by rintro _ ⟨w,rfl⟩; exact (k w).property
  obtain ⟨d,_⟩ := j.denseRange.exists_mem_open isOpen_univ (Set.univ_nonempty : (Set.univ : Set C).Nonempty)
  have := smoothOfRelativeDimension_isStableUnderBaseChange 1
  have : SmoothOfRelativeDimension 1 (pullback.fst a (curveMap toRaw V t)) :=
    MorphismProperty.pullback_fst _ _ hsCurve
  have : SmoothOfRelativeDimension 1 (j ≫ c) := smoothOfRelativeDimension_comp 0 1 j c
  have hd := smoothOfRelativeDimension_comp 1 1 (pullback.fst a (curveMap toRaw V t)) (j ≫ c)
  obtain ⟨z,_,hrel⟩ := hq a hW' d
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
  exact ⟨t,ht,V,hV,C,c,r,hc,D,j,a,ha,hCompat,hC,hp,hc₁,hqCurve,hj,hjd,hsCurve,inferInstance,hB,himage,w,
    Scheme.Hom.quasiFiniteAt_comp_iff_of_isOpenImmersion.mp hw,hout⟩

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
  obtain ⟨t,ht,V,hV,C,c,r,hc,D,j,a,ha,_,h⟩ := exists_compatible_marked_point_outside_projected_boundary
  exact ⟨t,ht,V,hV,C,c,r,hc,D,j,a,ha,h⟩

end CycleQ2MarkedGenericSurvives

#print axioms CycleQ2MarkedGenericSurvives.exists_marked_point_outside_projected_boundary

#print axioms CycleQ2MarkedGenericSurvives.exists_compatible_marked_point_outside_projected_boundary

namespace CycleQ2HodgeBoundaryPencil

open AlgebraicGeometry CategoryTheory TopologicalSpace Topology
open CycleQ2GeometricHodgeThreefold
open CycleQ2GenericSexticGradient (CoeffRing)
open scoped BigOperators

variable {k : Type} [Field k] [Infinite k] (φ : CoeffRing →+* k)

/-- Constant linear combinations of the original four weight-one
coordinates; the ambient homogeneous ring is unchanged. -/
def linearCombination : (Fin 4 → k) →ₗ[k] cone φ where
  toFun a := ∑ i : Fin 4, a i • coord φ i.castSucc
  map_add' a b := by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c a := by
    simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul, Finset.smul_sum, smul_smul]

theorem linearCombination_single (i : Fin 4) :
    linearCombination φ (Pi.single i (1 : k)) = coord φ i.castSucc := by
  classical
  simp [linearCombination, Pi.single_apply]

theorem linearCombination_homogeneous (a : Fin 4 → k) :
    linearCombination φ a ∈ grade φ 1 :=
  (grade φ 1).sum_mem (fun i _ => (grade φ 1).smul_mem (a i) (weightOne_mem_grade φ i))

def linearOpen (a : Fin 4 → k) : (threefold φ).Opens :=
  Proj.basicOpen (grade φ) (linearCombination φ a)

theorem linearOpen_affine (a : Fin 4 → k) : IsAffineOpen (linearOpen φ a) :=
  Proj.isAffineOpen_basicOpen (grade φ) (linearCombination φ a)
    (linearCombination_homogeneous φ a) (by decide)

/-- Finitely many actual homogeneous primes can be avoided by one
constant linear combination of the original weight-one coordinates. -/
theorem exists_linear_avoiding (hu : IsUnit (φ vertexCoefficient))
    (S : Set (threefold φ)) (hS : S.Finite) :
    ∃ a : Fin 4 → k, ∀ p ∈ S,
      linearCombination φ a ∉ p.asHomogeneousIdeal.toIdeal := by
  classical
  letI : Finite S := hS.to_subtype
  let bad : S → Subspace k (Fin 4 → k) := fun p =>
    (p.val.asHomogeneousIdeal.toIdeal.restrictScalars k).comap (linearCombination φ)
  have hbad (p : S) : bad p ≠ ⊤ := by
    intro htop
    obtain ⟨i, hi⟩ := exists_weightOne_not_mem φ hu p.val
    have hm : Pi.single i (1 : k) ∈ bad p := by rw [htop]; exact Submodule.mem_top
    change linearCombination φ (Pi.single i (1 : k)) ∈ p.val.asHomogeneousIdeal.toIdeal at hm
    exact hi ((linearCombination_single φ i) ▸ hm)
  have hcover : (⋃ p : S, (bad p : Set (Fin 4 → k))) ≠ Set.univ := by
    intro h
    obtain ⟨p, hp⟩ := Subspace.exists_eq_top_of_iUnion_eq_univ h
    exact hbad p hp
  obtain ⟨a, ha⟩ : ∃ a : Fin 4 → k, a ∉ ⋃ p : S, (bad p : Set (Fin 4 → k)) := by
    by_contra! h
    exact hcover (Set.eq_univ_of_forall h)
  refine ⟨a, ?_⟩
  intro p hp hm
  exact ha (Set.mem_iUnion.mpr ⟨⟨p,hp⟩,hm⟩)

/-- Two degree-one target sections have no common zero on any closed
subset of dimension at most one. The first avoids its component generic
points; the second avoids the remaining finite closed set. -/
theorem exists_two_cover [NoetherianSpace (threefold φ)]
    (hu : IsUnit (φ vertexCoefficient)) (B : Set (threefold φ)) (hB : IsClosed B)
    (hdim : topologicalKrullDim B ≤ 1) :
    ∃ a b : Fin 4 → k, B ⊆ (linearOpen φ a ⊔ linearOpen φ b : (threefold φ).Opens) := by
  classical
  letI : NoetherianSpace B := NoetherianSpace.set B
  letI : QuasiSober B := hB.isClosedEmbedding_subtypeVal.quasiSober
  have hgen : (genericPoints B).Finite :=
    genericPoints.finite NoetherianSpace.finite_irreducibleComponents
  obtain ⟨a, ha⟩ := exists_linear_avoiding φ hu (Subtype.val '' genericPoints B)
    (hgen.image Subtype.val)
  have hfirst : ∀ p : genericPoints B, (p.val : threefold φ) ∈ linearOpen φ a := by
    intro p
    exact ha p.val ⟨p.val,p.property,rfl⟩
  obtain ⟨hfinite, _⟩ := CycleQ2OneDimensionalClosedSubsets.finite_residual
    hB hdim (linearOpen φ a) hfirst
  obtain ⟨b, hb⟩ := exists_linear_avoiding φ hu
    (B ∩ (linearOpen φ a : Set (threefold φ))ᶜ) hfinite
  refine ⟨a,b,?_⟩
  intro p hp
  by_cases ha' : p ∈ linearOpen φ a
  · exact Or.inl ha'
  · exact Or.inr (hb p ⟨hp,ha'⟩)

end CycleQ2HodgeBoundaryPencil

#print axioms CycleQ2HodgeBoundaryPencil.exists_two_cover

namespace CycleQ2PencilTimeNeighborhood

open AlgebraicGeometry CategoryTheory TopologicalSpace

variable {Z C T : Scheme.{0}} (p : Z ⟶ C) [IsProper p] (q : Z ⟶ T) (O : T.Opens)

/-- Remove from the time curve only the proper image of the pencil
base locus. Every fiber over this open remains complete. -/
def timeOpen : C.Opens :=
  ⟨(p '' (q ⁻¹ᵁ O : Set Z)ᶜ)ᶜ,
    (p.isClosedMap _ (q ⁻¹ᵁ O).isOpen.isClosed_compl).isOpen_compl⟩

theorem preimage_le : p ⁻¹ᵁ timeOpen p q O ≤ q ⁻¹ᵁ O := by
  intro z hz
  by_contra hn
  exact hz ⟨z,hn,rfl⟩

/-- If the pencil covers the omitted time fibers, its new time
neighborhood and the original time open cover the same curve. -/
theorem union_original {D : Scheme.{0}} (j : D ⟶ C) [IsOpenImmersion j]
    (h : p ⁻¹' (Set.range j)ᶜ ⊆ (q ⁻¹ᵁ O : Set Z)) :
    j.opensRange ⊔ timeOpen p q O = ⊤ := by
  apply top_unique
  intro c _
  by_cases hc : c ∈ Set.range j
  · exact Or.inl hc
  · apply Or.inr
    rintro ⟨z,hz,he⟩
    apply hz
    apply h
    change p z ∉ Set.range j
    rwa [he]

end CycleQ2PencilTimeNeighborhood

namespace CycleQ2MarkedBoundaryPencil

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Topology
open CycleQ2LiteralIncidenceRelativeSpread CycleQ2LiteralIncidenceNormalizedSlice
  CycleQ2LiteralIncidenceRelativeCompletion CycleQ2LiteralIncidenceGenericCorrespondence
  CycleQ2GenericSmoothCurveGraph
open CycleQ2IncidenceEtaleParameter (parameterScheme)
open CycleQ2GeometricHodgeThreefold (threefold vertexCoefficient)
open CycleQ2MonicGenericSmooth (coeff)
open CycleQ2GenericHodgeModel (genericHodgeIso)
open CycleQ2HodgeBoundaryPencil (linearOpen)

variable (V : parameterScheme.Opens) (t : Fin 3 → ℂ) {C D : Scheme.{0}}
  (r : C ⟶ Completion V) (c : C ⟶ Spec (CommRingCat.of genericField))
  (hc : r ≫ structureMap V = c ≫ CycleQ2LiteralIncidenceGenericCorrespondence.genericPoint)
  (j : D ⟶ C) (a : D ⟶ Time toRaw V)
  (ha : j ≫ r = a ≫ CycleQ2LiteralIncidenceRelativeCompletion.inclusion V)
  [IsOpenImmersion j] [IsProper c] [SmoothOfRelativeDimension 1 c]

/-- A genuine target pencil covers every added time fiber of the
original closure. Properness produces a time neighborhood retaining
each whole such fiber, and that neighborhood together with the original
test-time open covers the original proper curve. -/
theorem exists_time_neighborhood
    (hs : SmoothOfRelativeDimension 1 (curveMap toRaw V t)) :
    let m := fromTest V t r j a ha
    let p := m.imageι ≫ toCurve V t r
    let q := m.imageι ≫ target V t r c hc ≫ genericHodgeIso.inv
    ∃ a₀ a₁ : Fin 4 → genericField, ∃ W : C.Opens,
      j.opensRange ⊔ W = ⊤ ∧
      p ⁻¹ᵁ W ≤ q ⁻¹ᵁ (linearOpen coeff a₀ ⊔ linearOpen coeff a₁) := by
  let m := fromTest V t r j a ha
  let p := m.imageι ≫ toCurve V t r
  let q₀ := m.imageι ≫ target V t r c hc
  let q := m.imageι ≫ target V t r c hc ≫ genericHodgeIso.inv
  letI : IsProper (toCurve V t r ≫ c) := inferInstance
  letI : NoetherianSpace (Graph V t r) :=
    CycleQ2LiteralIncidenceGenericModel.noetherian_of_proper (toCurve V t r ≫ c)
  letI : IsOpenImmersion m :=
    MorphismProperty.of_isPullback (test_square V t r j a ha) inferInstance
  letI : NoetherianSpace (TestSurface V t a) :=
    m.isOpenEmbedding.isInducing.noetherianSpace
  letI : IsProper (target V t r c hc) := target_proper V t r c hc
  letI : IsProper p := inferInstanceAs (IsProper (m.imageι ≫ toCurve V t r))
  letI : IsProper q :=
    inferInstanceAs (IsProper (m.imageι ≫ target V t r c hc ≫ genericHodgeIso.inv))
  letI : IsProper CycleQ2NativeWeightedCover.ambientToField :=
    CycleQ2NativeWeightedCover.ambient_proper
  letI : NoetherianSpace genericAmbient :=
    CycleQ2LiteralIncidenceGenericModel.noetherian_of_proper CycleQ2NativeWeightedCover.ambientToField
  letI : NoetherianSpace (threefold coeff) :=
    genericHodgeIso.hom.isOpenEmbedding.isInducing.noetherianSpace
  let B₀ := q₀ '' (Set.range m.toImage)ᶜ
  let B := q '' (Set.range m.toImage)ᶜ
  have hB : IsClosed B :=
    q.isClosedMap _ m.toImage.isOpenEmbedding.isOpen_range.isClosed_compl
  have hB₀ : topologicalKrullDim B₀ ≤ 1 :=
    (CycleQ2MarkedClosureBoundaryDimension.boundary_dimensions V t r c j a ha hc hs).2
  have himage : B = genericHodgeIso.inv '' B₀ := by
    ext y
    constructor
    · rintro ⟨z,hz,rfl⟩
      exact ⟨q₀ z,⟨z,hz,rfl⟩,rfl⟩
    · rintro ⟨y,⟨z,hz,rfl⟩,rfl⟩
      exact ⟨z,hz,rfl⟩
  have hdim : topologicalKrullDim B ≤ 1 := by
    rw [himage]
    let e := genericHodgeIso.inv.isOpenEmbedding.isEmbedding.homeomorphImage B₀
    exact e.symm.isInducing.topologicalKrullDim_le.trans hB₀
  have hu : IsUnit (coeff vertexCoefficient) := by
    rw [CycleQ2MonicGenericAmbientChart.genericCoeff_vertex]
    exact isUnit_one
  obtain ⟨a₀,a₁,hcover⟩ := CycleQ2HodgeBoundaryPencil.exists_two_cover coeff hu B hB hdim
  let O := linearOpen coeff a₀ ⊔ linearOpen coeff a₁
  let W := CycleQ2PencilTimeNeighborhood.timeOpen p q O
  have hmissing : p ⁻¹' (Set.range j)ᶜ ⊆ (q ⁻¹ᵁ O : Set m.image) := by
    intro z hz
    apply hcover
    refine ⟨z,?_,rfl⟩
    change z ∈ (Set.range m.toImage)ᶜ
    rw [CycleQ2MarkedClosureBoundaryDimension.boundary_eq_time_preimage V t r c j a ha]
    exact hz
  refine ⟨a₀,a₁,W,CycleQ2PencilTimeNeighborhood.union_original p q O j hmissing,?_⟩
  exact CycleQ2PencilTimeNeighborhood.preimage_le p q O

end CycleQ2MarkedBoundaryPencil

#print axioms CycleQ2MarkedBoundaryPencil.exists_time_neighborhood

namespace CycleQ2ReciprocalSectionPencil

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open CycleQ2LaurentProjectiveLine CycleQ2ProjectiveLineStructure
open CycleQ2SmoothRelativeFrames (sectionCoefficients)
open CycleQ2RelativeAffineOverlap (restrict)
open scoped Polynomial

variable (k : Type) [Field k] {X : Scheme.{0}}
  (p : X ⟶ Spec (CommRingCat.of k))

/-- The affine chart map is the actual polynomial evaluation of the
given section, with the original coefficient map. -/
def affineMap (U : X.Opens) (u : Γ(X,U)) : U.toScheme ⟶ affineLine k :=
  U.toSpecΓ ≫ Spec.map (CommRingCat.ofHom
    (Polynomial.eval₂RingHom (sectionCoefficients p U) u))

private theorem polynomial_eval_restrict {U V : X.Opens} (h : V ≤ U) (a : Γ(X,U)) :
    (X.presheaf.map (homOfLE h).op).hom.comp
        (Polynomial.eval₂RingHom (sectionCoefficients p U) a) =
      Polynomial.eval₂RingHom (sectionCoefficients p V)
        (X.presheaf.map (homOfLE h).op a) := by
  letI : Algebra k Γ(X,U) := (sectionCoefficients p U).toAlgebra
  letI : Algebra k Γ(X,V) := (sectionCoefficients p V).toAlgebra
  apply Polynomial.ringHom_ext
  · intro r
    simp only [RingHom.comp_apply,Polynomial.coe_eval₂RingHom,Polynomial.eval₂_C]
    exact (restrict p h).commutes r
  · simp only [RingHom.comp_apply,Polynomial.coe_eval₂RingHom,Polynomial.eval₂_X]

theorem affineMap_over (U : X.Opens) (u : Γ(X,U)) :
    affineMap k p U u ≫ affineStructure k = U.ι ≫ p := by
  unfold affineMap affineStructure
  rw [Category.assoc,← Spec.map_comp]
  have h : CommRingCat.ofHom (algebraMap k k[X]) ≫ CommRingCat.ofHom
      (Polynomial.eval₂RingHom (sectionCoefficients p U) u) =
      CommRingCat.ofHom (sectionCoefficients p U) := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    exact Polynomial.eval₂_C _ _
  rw [h,CycleQ2RationalFunctionRelativeMap.sectionCoefficients_Spec]

variable (U V : X.Opens) (u : Γ(X,U)) (v : Γ(X,V))

private abbrev leftValue : Γ(X,U ⊓ V) :=
  X.presheaf.map (homOfLE (show U ⊓ V ≤ U from inf_le_left)).op u

private abbrev rightValue : Γ(X,U ⊓ V) :=
  X.presheaf.map (homOfLE (show U ⊓ V ≤ V from inf_le_right)).op v

variable (h : leftValue U V u * rightValue U V v = 1)

def overlapUnit : Γ(X,U ⊓ V)ˣ where
  val := leftValue U V u
  inv := rightValue U V v
  val_inv := h
  inv_val := by rw [mul_comm]; exact h

def torusMap : (U ⊓ V : X.Opens).toScheme ⟶ torus k :=
  (U ⊓ V : X.Opens).toSpecΓ ≫ Spec.map (CommRingCat.ofHom
    (LaurentPolynomial.eval₂ (sectionCoefficients p (U ⊓ V)) (overlapUnit U V u v h)))

private theorem zero_factor :
    X.homOfLE (show U ⊓ V ≤ U from inf_le_left) ≫ affineMap k p U u =
      torusMap k p U V u v h ≫ zeroMap k := by
  unfold affineMap torusMap zeroMap
  rw [← Category.assoc,← Scheme.Opens.toSpecΓ_SpecMap_presheaf_map,
    Category.assoc,Category.assoc,← Spec.map_comp,← Spec.map_comp]
  apply congrArg (fun f => (U ⊓ V : X.Opens).toSpecΓ ≫ Spec.map f)
  apply CommRingCat.hom_ext
  change (X.presheaf.map (homOfLE (show U ⊓ V ≤ U from inf_le_left)).op).hom.comp
    (Polynomial.eval₂RingHom (sectionCoefficients p U) u) =
    (LaurentPolynomial.eval₂ (sectionCoefficients p (U ⊓ V))
      (overlapUnit U V u v h)).comp Polynomial.toLaurent
  rw [polynomial_eval_restrict k p _ u]
  apply RingHom.ext
  intro q
  exact (LaurentPolynomial.eval₂_toLaurent (sectionCoefficients p (U ⊓ V))
    (overlapUnit U V u v h) q).symm

private theorem eval_inverted (O : X.Opens) (w : Γ(X,O)ˣ) :
    (LaurentPolynomial.eval₂ (sectionCoefficients p O) w).comp
      ((LaurentPolynomial.invert : LaurentPolynomial k ≃ₐ[k] LaurentPolynomial k).toRingHom.comp
        (Polynomial.toLaurentAlg : k[X] →ₐ[k] LaurentPolynomial k).toRingHom) =
      Polynomial.eval₂RingHom (sectionCoefficients p O) (↑w⁻¹ : Γ(X,O)) := by
  apply Polynomial.ringHom_ext
  · intro r
    simp only [RingHom.comp_apply,Polynomial.coe_eval₂RingHom,Polynomial.eval₂_C]
    change LaurentPolynomial.eval₂ (sectionCoefficients p O) w
      (LaurentPolynomial.invert (Polynomial.toLaurent (Polynomial.C r))) = _
    rw [Polynomial.toLaurent_C,LaurentPolynomial.invert_C,LaurentPolynomial.eval₂_C]
  · simp only [RingHom.comp_apply,Polynomial.coe_eval₂RingHom,Polynomial.eval₂_X]
    change LaurentPolynomial.eval₂ (sectionCoefficients p O) w
      (LaurentPolynomial.invert (Polynomial.toLaurent Polynomial.X)) = _
    rw [Polynomial.toLaurent_X,LaurentPolynomial.invert_T,LaurentPolynomial.eval₂_T]
    simp

private theorem infinity_factor :
    X.homOfLE (show U ⊓ V ≤ V from inf_le_right) ≫ affineMap k p V v =
      torusMap k p U V u v h ≫ infinityMap k := by
  unfold affineMap torusMap infinityMap inversion zeroMap
  rw [← Category.assoc,← Scheme.Opens.toSpecΓ_SpecMap_presheaf_map,
    Category.assoc,Category.assoc,← Spec.map_comp,← Spec.map_comp,← Spec.map_comp]
  apply congrArg (fun f => (U ⊓ V : X.Opens).toSpecΓ ≫ Spec.map f)
  apply CommRingCat.hom_ext
  change (X.presheaf.map (homOfLE (show U ⊓ V ≤ V from inf_le_right)).op).hom.comp
    (Polynomial.eval₂RingHom (sectionCoefficients p V) v) = _
  rw [polynomial_eval_restrict k p _ v]
  change Polynomial.eval₂RingHom (sectionCoefficients p (U ⊓ V))
      (↑(overlapUnit U V u v h)⁻¹ : Γ(X,U ⊓ V)) = _
  exact (eval_inverted k p (U ⊓ V) (overlapUnit U V u v h)).symm

private def domain : Bool → X.Opens
  | false => U
  | true => V

private def inclusion (i : Bool) : (domain U V i).toScheme ⟶ (U ⊔ V : X.Opens).toScheme := by
  cases i
  · exact X.homOfLE le_sup_left
  · exact X.homOfLE le_sup_right

private instance inclusion_open (i : Bool) : IsOpenImmersion (inclusion U V i) := by
  cases i <;> exact inferInstanceAs (IsOpenImmersion (X.homOfLE _))

/-- The two original open schemes cover their union, without an
integrality or valuation-ring assumption. -/
def twoCover : (U ⊔ V : X.Opens).toScheme.OpenCover where
  I₀ := Bool
  X i := (domain U V i).toScheme
  f i := inclusion U V i
  mem₀ := by
    rw [Scheme.ofArrows_mem_precoverage_iff]
    refine ⟨?_,fun _ => inferInstance⟩
    intro x
    rcases x.property with hx | hx
    · refine ⟨false,⟨x.val,hx⟩,?_⟩
      apply Subtype.ext
      simp [inclusion,domain]
    · refine ⟨true,⟨x.val,hx⟩,?_⟩
      apply Subtype.ext
      simp [inclusion,domain]

private theorem intersectionSquare :
    IsPullback (X.homOfLE (show U ⊓ V ≤ U from inf_le_left))
      (X.homOfLE (show U ⊓ V ≤ V from inf_le_right))
      (X.homOfLE (show U ≤ U ⊔ V from le_sup_left))
      (X.homOfLE (show V ≤ U ⊔ V from le_sup_right)) :=
  isPullback_opens_inf_le le_sup_left le_sup_right

private def piece (i : Bool) : (domain U V i).toScheme ⟶ line k := by
  cases i
  · exact affineMap k p U u ≫ chartZero k
  · exact affineMap k p V v ≫ chartInfinity k

private theorem mixed :
    pullback.fst (inclusion U V false) (inclusion U V true) ≫ piece k p U V u v false =
      pullback.snd (inclusion U V false) (inclusion U V true) ≫ piece k p U V u v true := by
  apply (cancel_epi (intersectionSquare U V).isoPullback.hom).mp
  simp only [← Category.assoc]
  rw [(intersectionSquare U V).isoPullback_hom_fst,
    (intersectionSquare U V).isoPullback_hom_snd]
  change (X.homOfLE (show U ⊓ V ≤ U from inf_le_left) ≫ affineMap k p U u) ≫ chartZero k =
    (X.homOfLE (show U ⊓ V ≤ V from inf_le_right) ≫ affineMap k p V v) ≫ chartInfinity k
  rw [zero_factor k p U V u v h,infinity_factor k p U V u v h,
    Category.assoc,Category.assoc,torus_zero,torus_infinity]

private theorem pieces_compatible (i j : Bool) :
    pullback.fst (inclusion U V i) (inclusion U V j) ≫ piece k p U V u v i =
      pullback.snd (inclusion U V i) (inclusion U V j) ≫ piece k p U V u v j := by
  cases i <;> cases j
  · rw [show pullback.fst (inclusion U V false) (inclusion U V false) = pullback.snd _ _ from
      (cancel_mono (inclusion U V false)).mp pullback.condition]
  · exact mixed k p U V u v h
  · apply (cancel_epi (pullbackSymmetry (inclusion U V false) (inclusion U V true)).hom).mp
    simpa only [← Category.assoc,pullbackSymmetry_hom_comp_fst,pullbackSymmetry_hom_comp_snd] using
      (mixed k p U V u v h).symm
  · rw [show pullback.fst (inclusion U V true) (inclusion U V true) = pullback.snd _ _ from
      (cancel_mono (inclusion U V true)).mp pullback.condition]

/-- The actual projective-line map obtained by gluing reciprocal
sections on their two original affine charts. -/
def toLine : (U ⊔ V : X.Opens).toScheme ⟶ line k :=
  (twoCover U V).glueMorphisms (piece k p U V u v) (pieces_compatible k p U V u v h)

theorem zero_chart :
    X.homOfLE (show U ≤ U ⊔ V from le_sup_left) ≫ toLine k p U V u v h =
      affineMap k p U u ≫ chartZero k :=
  (twoCover U V).ι_glueMorphisms (piece k p U V u v) (pieces_compatible k p U V u v h) false

theorem infinity_chart :
    X.homOfLE (show V ≤ U ⊔ V from le_sup_right) ≫ toLine k p U V u v h =
      affineMap k p V v ≫ chartInfinity k :=
  (twoCover U V).ι_glueMorphisms (piece k p U V u v) (pieces_compatible k p U V u v h) true

theorem toLine_over :
    toLine k p U V u v h ≫ structureMap k = (U ⊔ V : X.Opens).ι ≫ p := by
  apply (twoCover U V).hom_ext
  intro b
  cases b
  · change X.homOfLE (show U ≤ U ⊔ V from le_sup_left) ≫
      toLine k p U V u v h ≫ structureMap k = _
    rw [← Category.assoc,zero_chart,Category.assoc,chartZero_over,affineMap_over,
      ← Category.assoc,Scheme.homOfLE_ι]
  · change X.homOfLE (show V ≤ U ⊔ V from le_sup_right) ≫
      toLine k p U V u v h ≫ structureMap k = _
    rw [← Category.assoc,infinity_chart,Category.assoc,chartInfinity_over,affineMap_over,
      ← Category.assoc,Scheme.homOfLE_ι]

end CycleQ2ReciprocalSectionPencil

#print axioms CycleQ2ReciprocalSectionPencil.toLine_over

namespace CycleQ2ReciprocalSectionPencil

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open CycleQ2LaurentProjectiveLine CycleQ2ProjectiveLineStructure
open CycleQ2SmoothRelativeFrames (sectionCoefficients)
open scoped Polynomial

variable (k : Type) [Field k]

private theorem zero_range :
    (zeroMap k).opensRange = PrimeSpectrum.basicOpen (Polynomial.X : k[X]) := by
  rw [SetLike.ext'_iff]
  exact PrimeSpectrum.localization_away_comap_range (LaurentPolynomial k) (Polynomial.X : k[X])

private theorem infinity_range :
    (infinityMap k).opensRange = PrimeSpectrum.basicOpen (Polynomial.X : k[X]) := by
  rw [infinityMap,Scheme.Hom.opensRange_comp_of_isIso,zero_range]

private theorem infinity_preimage_zero :
    chartInfinity k ⁻¹ᵁ openZero k = PrimeSpectrum.basicOpen (Polynomial.X : k[X]) := by
  rw [← infinity_range k]
  apply (chartInfinity k).image_injective
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf,inf_comm,overlap,
    ← Scheme.Hom.opensRange_comp,torus_infinity]

private theorem zero_preimage_infinity :
    chartZero k ⁻¹ᵁ openInfinity k = PrimeSpectrum.basicOpen (Polynomial.X : k[X]) := by
  rw [← zero_range k]
  apply (chartZero k).image_injective
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf,overlap,
    ← Scheme.Hom.opensRange_comp,torus_zero]

variable {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of k))

private theorem affine_preimage (O : X.Opens) (w : Γ(X,O)) :
    affineMap k p O w ⁻¹ᵁ PrimeSpectrum.basicOpen (Polynomial.X : k[X]) =
      O.ι ⁻¹ᵁ X.basicOpen w := by
  rw [affineMap,Scheme.Hom.comp_preimage]
  change O.toSpecΓ ⁻¹ᵁ PrimeSpectrum.basicOpen
    ((Polynomial.eval₂RingHom (sectionCoefficients p O) w) Polynomial.X) = _
  simp only [Polynomial.coe_eval₂RingHom,Polynomial.eval₂_X]
  exact O.toSpecΓ_preimage_basicOpen w

variable (U V : X.Opens) (u : Γ(X,U)) (v : Γ(X,V))
  (h : leftValue U V u * rightValue U V v = 1)

/-- Exact chart preimages require the reciprocal section to vanish
precisely outside the overlap. This is proved below for the actual
homogeneous ratios, rather than inferred from reciprocal gluing alone. -/
theorem zero_preimage (hv : X.basicOpen v = U ⊓ V) :
    toLine k p U V u v h ⁻¹ᵁ openZero k = (U ⊔ V : X.Opens).ι ⁻¹ᵁ U := by
  have hV : X.homOfLE (show V ≤ U ⊔ V from le_sup_right) ⁻¹ᵁ
      (toLine k p U V u v h ⁻¹ᵁ openZero k) = V.ι ⁻¹ᵁ X.basicOpen v := by
    rw [← Scheme.Hom.comp_preimage,infinity_chart,Scheme.Hom.comp_preimage,
      infinity_preimage_zero,affine_preimage]
  have hU : X.homOfLE (show U ≤ U ⊔ V from le_sup_left) ⁻¹ᵁ
      (toLine k p U V u v h ⁻¹ᵁ openZero k) = ⊤ := by
    rw [← Scheme.Hom.comp_preimage,zero_chart,Scheme.Hom.comp_preimage]
    exact (congrArg (fun O => affineMap k p U u ⁻¹ᵁ O)
      (chartZero k).preimage_opensRange).trans (by rfl)
  ext x
  constructor
  · intro hx
    by_cases hxU : x.val ∈ U
    · exact hxU
    · have hxV : x.val ∈ V := x.property.resolve_left hxU
      let y : V := ⟨x.val,hxV⟩
      have hy : X.homOfLE (show V ≤ U ⊔ V from le_sup_right) y = x := by
        apply Subtype.ext
        simp [y]
      have hm : y ∈ X.homOfLE (show V ≤ U ⊔ V from le_sup_right) ⁻¹ᵁ
          (toLine k p U V u v h ⁻¹ᵁ openZero k) := by
        change X.homOfLE (show V ≤ U ⊔ V from le_sup_right) y ∈ _
        rwa [hy]
      rw [hV] at hm
      change x.val ∈ X.basicOpen v at hm
      rw [hv] at hm
      exact hm.1
  · intro hx
    let y : U := ⟨x.val,hx⟩
    have hy : X.homOfLE (show U ≤ U ⊔ V from le_sup_left) y = x := by
      apply Subtype.ext
      simp [y]
    have hm : y ∈ X.homOfLE (show U ≤ U ⊔ V from le_sup_left) ⁻¹ᵁ
        (toLine k p U V u v h ⁻¹ᵁ openZero k) := by rw [hU]; trivial
    change X.homOfLE (show U ≤ U ⊔ V from le_sup_left) y ∈ _ at hm
    rwa [hy] at hm

theorem infinity_preimage (hu : X.basicOpen u = U ⊓ V) :
    toLine k p U V u v h ⁻¹ᵁ openInfinity k = (U ⊔ V : X.Opens).ι ⁻¹ᵁ V := by
  have hU : X.homOfLE (show U ≤ U ⊔ V from le_sup_left) ⁻¹ᵁ
      (toLine k p U V u v h ⁻¹ᵁ openInfinity k) = U.ι ⁻¹ᵁ X.basicOpen u := by
    rw [← Scheme.Hom.comp_preimage,zero_chart,Scheme.Hom.comp_preimage,
      zero_preimage_infinity,affine_preimage]
  have hV : X.homOfLE (show V ≤ U ⊔ V from le_sup_right) ⁻¹ᵁ
      (toLine k p U V u v h ⁻¹ᵁ openInfinity k) = ⊤ := by
    rw [← Scheme.Hom.comp_preimage,infinity_chart,Scheme.Hom.comp_preimage]
    exact (congrArg (fun O => affineMap k p V v ⁻¹ᵁ O)
      (chartInfinity k).preimage_opensRange).trans (by rfl)
  ext x
  constructor
  · intro hx
    by_cases hxV : x.val ∈ V
    · exact hxV
    · have hxU : x.val ∈ U := x.property.resolve_right hxV
      let y : U := ⟨x.val,hxU⟩
      have hy : X.homOfLE (show U ≤ U ⊔ V from le_sup_left) y = x := by
        apply Subtype.ext
        simp [y]
      have hm : y ∈ X.homOfLE (show U ≤ U ⊔ V from le_sup_left) ⁻¹ᵁ
          (toLine k p U V u v h ⁻¹ᵁ openInfinity k) := by
        change X.homOfLE (show U ≤ U ⊔ V from le_sup_left) y ∈ _
        rwa [hy]
      rw [hU] at hm
      change x.val ∈ X.basicOpen u at hm
      rw [hu] at hm
      exact hm.2
  · intro hx
    let y : V := ⟨x.val,hx⟩
    have hy : X.homOfLE (show V ≤ U ⊔ V from le_sup_right) y = x := by
      apply Subtype.ext
      simp [y]
    have hm : y ∈ X.homOfLE (show V ≤ U ⊔ V from le_sup_right) ⁻¹ᵁ
        (toLine k p U V u v h ⁻¹ᵁ openInfinity k) := by rw [hV]; trivial
    change X.homOfLE (show V ≤ U ⊔ V from le_sup_right) y ∈ _ at hm
    rwa [hy] at hm

end CycleQ2ReciprocalSectionPencil

#print axioms CycleQ2ReciprocalSectionPencil.zero_preimage
#print axioms CycleQ2ReciprocalSectionPencil.infinity_preimage

namespace CycleQ2HodgeBoundaryPencil

open AlgebraicGeometry CategoryTheory Opposite HomogeneousLocalization
open CycleQ2GeometricHodgeThreefold
open CycleQ2GenericSexticGradient (CoeffRing)
open CycleQ2GeometricProjectiveCurve.Twisted (res res_comp res_self)

variable {k : Type} [Field k] [Infinite k] (φ : CoeffRing →+* k)

private def fraction (a b : Fin 4 → k) : Away (grade φ) (linearCombination φ a) :=
  Away.mk (grade φ) (linearCombination_homogeneous φ a) 1 (linearCombination φ b)
    (by simpa using linearCombination_homogeneous φ b)

/-- The actual homogeneous section ℓ_b/ℓ_a on any subopen of D₊(ℓ_a). -/
def ratio (a b : Fin 4 → k) (O : (threefold φ).Opens) (ha : O ≤ linearOpen φ a) :
    Γ(threefold φ,O) :=
  res (threefold φ).sheaf ha
    (Proj.awayToSection (grade φ) (linearCombination φ a) (fraction φ a b))

theorem ratio_restrict (a b : Fin 4 → k) {O P : (threefold φ).Opens}
    (ha : O ≤ linearOpen φ a) (hP : P ≤ O) :
    res (threefold φ).sheaf hP (ratio φ a b O ha) = ratio φ a b P (hP.trans ha) :=
  res_comp _ _ _ _

private abbrev den {O : (threefold φ).Opens} (a : Fin 4 → k)
    (ha : O ≤ linearOpen φ a) (q : O) : q.val.asHomogeneousIdeal.toIdeal.primeCompl :=
  ⟨linearCombination φ a,ha q.property⟩

private theorem ratio_value {O : (threefold φ).Opens} (a b : Fin 4 → k)
    (ha : O ≤ linearOpen φ a) (q : O) :
    ((ratio φ a b O ha).val q).val = Localization.mk (linearCombination φ b) (den φ a ha q ^ 1) :=
  rfl

theorem ratio_self (a : Fin 4 → k) (O : (threefold φ).Opens) (ha : O ≤ linearOpen φ a) :
    ratio φ a a O ha = 1 := by
  apply Subtype.ext
  funext q
  apply HomogeneousLocalization.val_injective
  change ((ratio φ a a O ha).val q).val = (1 : HomogeneousLocalization _ _).val
  rw [ratio_value,pow_one,HomogeneousLocalization.val_one]
  exact Localization.mk_self (den φ a ha q)

theorem ratio_comp (a b c : Fin 4 → k) (O : (threefold φ).Opens)
    (ha : O ≤ linearOpen φ a) (hb : O ≤ linearOpen φ b) :
    ratio φ a b O ha * ratio φ b c O hb = ratio φ a c O ha := by
  apply Subtype.ext
  funext q
  apply HomogeneousLocalization.val_injective
  change (((ratio φ a b O ha).val q) * ((ratio φ b c O hb).val q)).val =
    ((ratio φ a c O ha).val q).val
  rw [HomogeneousLocalization.val_mul,ratio_value,ratio_value,ratio_value]
  simp only [pow_one]
  rw [Localization.mk_mul,Localization.mk_eq_mk_iff,Localization.r_iff_exists]
  refine ⟨1,?_⟩
  simp only [Submonoid.coe_one,Submonoid.coe_mul,one_mul,den]
  ring

private theorem localizationElement (a b : Fin 4 → k) :
    Away.isLocalizationElem (𝒜 := grade φ)
      (linearCombination_homogeneous φ a) (linearCombination_homogeneous φ b) = fraction φ a b := by
  apply HomogeneousLocalization.val_injective
  simp only [Away.isLocalizationElem,fraction,Away.val_mk,pow_one]
  rfl

/-- The nonvanishing open of the actual ratio is exactly the
intersection of the two homogeneous target charts. -/
theorem ratio_basicOpen (a b : Fin 4 → k) :
    (threefold φ).basicOpen (ratio φ a b (linearOpen φ a) le_rfl) =
      linearOpen φ a ⊓ linearOpen φ b := by
  let U := linearOpen φ a
  let V := linearOpen φ b
  let e := Proj.basicOpenIsoSpec (grade φ) (linearCombination φ a)
    (linearCombination_homogeneous φ a) (by decide)
  have hsec : ratio φ a b U le_rfl =
      Proj.awayToSection (grade φ) (linearCombination φ a) (fraction φ a b) := by
    simp only [ratio,res_self]
  have hchart : e.hom ⁻¹ᵁ PrimeSpectrum.basicOpen (fraction φ a b) =
      U.ι ⁻¹ᵁ (threefold φ).basicOpen (ratio φ a b U le_rfl) := by
    change Proj.basicOpenToSpec (grade φ) (linearCombination φ a) ⁻¹ᵁ _ = _
    rw [Proj.basicOpenToSpec,Scheme.Hom.comp_preimage]
    change U.toSpecΓ ⁻¹ᵁ PrimeSpectrum.basicOpen
      (Proj.awayToSection (grade φ) (linearCombination φ a) (fraction φ a b)) = _
    rw [← hsec]
    exact U.toSpecΓ_preimage_basicOpen _
  have haw : Proj.awayι (grade φ) (linearCombination φ a)
      (linearCombination_homogeneous φ a) (by decide) ⁻¹ᵁ V =
      PrimeSpectrum.basicOpen (fraction φ a b) := by
    change Proj.awayι (grade φ) (linearCombination φ a)
      (linearCombination_homogeneous φ a) (by decide) ⁻¹ᵁ
      Proj.basicOpen (grade φ) (linearCombination φ b) = _
    rw [Proj.awayι_preimage_basicOpen (linearCombination_homogeneous φ a) (by decide)
      (linearCombination_homogeneous φ b) (by decide),localizationElement]
  have he : e.hom ≫ Proj.awayι (grade φ) (linearCombination φ a)
      (linearCombination_homogeneous φ a) (by decide) = U.ι := by
    change e.hom ≫ e.inv ≫ U.ι = U.ι
    simp only [Iso.hom_inv_id_assoc]
  have hres : U.ι ⁻¹ᵁ (threefold φ).basicOpen (ratio φ a b U le_rfl) = U.ι ⁻¹ᵁ V := by
    rw [← hchart,← haw,← Scheme.Hom.comp_preimage,he]
  have himage := congrArg (fun O => U.ι ''ᵁ O) hres
  simp only [Scheme.Hom.image_preimage_eq_opensRange_inf,U.opensRange_ι] at himage
  exact (inf_eq_right.mpr ((threefold φ).basicOpen_le _)).symm.trans himage

private theorem reciprocal (a b : Fin 4 → k) :
    (threefold φ).presheaf.map
        (homOfLE (show linearOpen φ a ⊓ linearOpen φ b ≤ linearOpen φ a from inf_le_left)).op
        (ratio φ a b (linearOpen φ a) le_rfl) *
      (threefold φ).presheaf.map
        (homOfLE (show linearOpen φ a ⊓ linearOpen φ b ≤ linearOpen φ b from inf_le_right)).op
        (ratio φ b a (linearOpen φ b) le_rfl) = 1 := by
  change res (threefold φ).sheaf inf_le_left (ratio φ a b (linearOpen φ a) le_rfl) *
    res (threefold φ).sheaf inf_le_right (ratio φ b a (linearOpen φ b) le_rfl) = 1
  rw [ratio_restrict,ratio_restrict,ratio_comp,ratio_self]

/-- The actual target pencil, with no replacement of the original
homogeneous ring or its two chosen degree-one sections. -/
def pencil (a b : Fin 4 → k) :
    (linearOpen φ a ⊔ linearOpen φ b : (threefold φ).Opens).toScheme ⟶
      CycleQ2LaurentProjectiveLine.line k :=
  CycleQ2ReciprocalSectionPencil.toLine k (toBase φ) (linearOpen φ a) (linearOpen φ b)
    (ratio φ a b (linearOpen φ a) le_rfl) (ratio φ b a (linearOpen φ b) le_rfl)
    (reciprocal φ a b)

theorem pencil_over (a b : Fin 4 → k) :
    pencil φ a b ≫ CycleQ2ProjectiveLineStructure.structureMap k =
      (linearOpen φ a ⊔ linearOpen φ b : (threefold φ).Opens).ι ≫ toBase φ :=
  CycleQ2ReciprocalSectionPencil.toLine_over k (toBase φ) _ _ _ _ _

theorem pencil_preimage_zero (a b : Fin 4 → k) :
    pencil φ a b ⁻¹ᵁ CycleQ2LaurentProjectiveLine.openZero k =
      (linearOpen φ a ⊔ linearOpen φ b : (threefold φ).Opens).ι ⁻¹ᵁ linearOpen φ a := by
  apply CycleQ2ReciprocalSectionPencil.zero_preimage
  rw [ratio_basicOpen,inf_comm]

theorem pencil_preimage_infinity (a b : Fin 4 → k) :
    pencil φ a b ⁻¹ᵁ CycleQ2LaurentProjectiveLine.openInfinity k =
      (linearOpen φ a ⊔ linearOpen φ b : (threefold φ).Opens).ι ⁻¹ᵁ linearOpen φ b := by
  apply CycleQ2ReciprocalSectionPencil.infinity_preimage
  exact ratio_basicOpen φ a b

end CycleQ2HodgeBoundaryPencil

#print axioms CycleQ2HodgeBoundaryPencil.pencil_over
#print axioms CycleQ2HodgeBoundaryPencil.pencil_preimage_zero
#print axioms CycleQ2HodgeBoundaryPencil.pencil_preimage_infinity

namespace CycleQ2AffineTimeProduct

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

variable {Z C T S : Scheme.{0}} [IsAffine S]
  (c : C ⟶ S) (t : T ⟶ S) (e : Z ⟶ pullback c t) [IsAffineHom e]

/-- An affine morphism into the actual product becomes affine over
the target after restriction to any affine time open. -/
theorem target_affine (O : C.Opens) (hO : IsAffineOpen O) :
    IsAffineHom (((e ≫ pullback.fst c t) ⁻¹ᵁ O).ι ≫ e ≫ pullback.snd c t) := by
  let P := pullback.fst c t ⁻¹ᵁ O
  letI : IsAffine O.toScheme := hO
  letI : IsAffineHom (O.ι ≫ c) := isAffineHom_of_isAffine _
  have hs : IsPullback (pullback.fst c t ∣_ O)
      (P.ι ≫ pullback.snd c t) (O.ι ≫ c) t :=
    (isPullback_morphismRestrict (pullback.fst c t) O).paste_vert
      (IsPullback.of_hasPullback c t)
  letI : IsAffineHom (P.ι ≫ pullback.snd c t) :=
    MorphismProperty.of_isPullback hs inferInstance
  letI : IsAffineHom (e ∣_ P) :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict e P).flip inferInstance
  have he : ((e ≫ pullback.fst c t) ⁻¹ᵁ O).ι ≫ e ≫ pullback.snd c t =
      (e ∣_ P) ≫ P.ι ≫ pullback.snd c t := by
    rw [← Category.assoc (e ∣_ P),morphismRestrict_ι,Category.assoc]
  rw [he]
  infer_instance

end CycleQ2AffineTimeProduct

namespace CycleQ2RelativeHodgePencil

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open CycleQ2GeometricHodgeThreefold
open CycleQ2HodgeBoundaryPencil (linearOpen pencil)
open CycleQ2GenericSexticGradient (CoeffRing)

variable {k : Type} [Field k] [Infinite k] (φ : CoeffRing →+* k)
  {Z C : Scheme.{0}} (c : C ⟶ Spec (CommRingCat.of k)) (p : Z ⟶ C)
  (q : Z ⟶ threefold φ) (hpq : p ≫ c = q ≫ toBase φ)
  (a b : Fin 4 → k) (h : ∀ z : Z, q z ∈ linearOpen φ a ⊔ linearOpen φ b)

private def toPencilOpen : Z ⟶
    (linearOpen φ a ⊔ linearOpen φ b : (threefold φ).Opens).toScheme :=
  IsOpenImmersion.lift (linearOpen φ a ⊔ linearOpen φ b : (threefold φ).Opens).ι q (by
    rintro _ ⟨z,rfl⟩
    exact ⟨⟨q z,h z⟩,rfl⟩)

private theorem toPencilOpen_fac :
    toPencilOpen φ q a b h ≫
      (linearOpen φ a ⊔ linearOpen φ b : (threefold φ).Opens).ι = q :=
  IsOpenImmersion.lift_fac _ _ _

def lineMap : Z ⟶ CycleQ2LaurentProjectiveLine.line k :=
  toPencilOpen φ q a b h ≫ pencil φ a b

theorem lineMap_over :
    lineMap φ q a b h ≫ CycleQ2ProjectiveLineStructure.structureMap k = p ≫ c := by
  rw [lineMap,Category.assoc,CycleQ2HodgeBoundaryPencil.pencil_over,
    ← Category.assoc,toPencilOpen_fac]
  exact hpq.symm

/-- Both components of the finite projection are the original time
map and the original target pencil. -/
def productMap : Z ⟶ pullback c (CycleQ2ProjectiveLineStructure.structureMap k) :=
  pullback.lift p (lineMap φ q a b h) (lineMap_over φ c p q hpq a b h).symm

@[reassoc] theorem productMap_fst :
    productMap φ c p q hpq a b h ≫ pullback.fst _ _ = p :=
  pullback.lift_fst _ _ _

@[reassoc] theorem productMap_snd :
    productMap φ c p q hpq a b h ≫ pullback.snd _ _ = lineMap φ q a b h :=
  pullback.lift_snd _ _ _

theorem preimage_zero :
    productMap φ c p q hpq a b h ⁻¹ᵁ
        (pullback.snd c (CycleQ2ProjectiveLineStructure.structureMap k) ⁻¹ᵁ
          CycleQ2LaurentProjectiveLine.openZero k) = q ⁻¹ᵁ linearOpen φ a := by
  rw [← Scheme.Hom.comp_preimage,productMap_snd,lineMap,Scheme.Hom.comp_preimage,
    CycleQ2HodgeBoundaryPencil.pencil_preimage_zero,
    ← Scheme.Hom.comp_preimage,toPencilOpen_fac]

theorem preimage_infinity :
    productMap φ c p q hpq a b h ⁻¹ᵁ
        (pullback.snd c (CycleQ2ProjectiveLineStructure.structureMap k) ⁻¹ᵁ
          CycleQ2LaurentProjectiveLine.openInfinity k) = q ⁻¹ᵁ linearOpen φ b := by
  rw [← Scheme.Hom.comp_preimage,productMap_snd,lineMap,Scheme.Hom.comp_preimage,
    CycleQ2HodgeBoundaryPencil.pencil_preimage_infinity,
    ← Scheme.Hom.comp_preimage,toPencilOpen_fac]

/-- Properness of the original time map and the actual affine chart
inverse images prove finiteness of the relative pencil. No assertion
about nonconstant components or a replacement surface is needed. -/
theorem finite [IsAffine C] [IsProper p] [IsAffineHom q] :
    IsFinite (productMap φ c p q hpq a b h) := by
  letI : IsSeparated (CycleQ2ProjectiveLineStructure.structureMap k) :=
    CycleQ2ProjectiveLineSeparated.separated k
  letI : IsProper (productMap φ c p q hpq a b h ≫ pullback.fst _ _) := by
    rw [productMap_fst]
    infer_instance
  have hproper : IsProper (productMap φ c p q hpq a b h) :=
    IsProper.of_comp _ (pullback.fst _ _)
  letI : IsAffineHom c := isAffineHom_of_isAffine _
  have haffine : IsAffineHom (productMap φ c p q hpq a b h) := by
    apply isAffineHom_of_forall_exists_isAffineOpen
    intro y
    have hy : pullback.snd c (CycleQ2ProjectiveLineStructure.structureMap k) y ∈
        CycleQ2LaurentProjectiveLine.openZero k ⊔
          CycleQ2LaurentProjectiveLine.openInfinity k := by
      rw [CycleQ2LaurentProjectiveLine.cover]
      trivial
    rcases hy with hy | hy
    · refine ⟨pullback.snd c (CycleQ2ProjectiveLineStructure.structureMap k) ⁻¹ᵁ
        CycleQ2LaurentProjectiveLine.openZero k,hy,?_,?_⟩
      · exact (isAffineOpen_opensRange (CycleQ2LaurentProjectiveLine.chartZero k)).preimage _
      · rw [preimage_zero]
        exact (CycleQ2HodgeBoundaryPencil.linearOpen_affine φ a).preimage q
    · refine ⟨pullback.snd c (CycleQ2ProjectiveLineStructure.structureMap k) ⁻¹ᵁ
        CycleQ2LaurentProjectiveLine.openInfinity k,hy,?_,?_⟩
      · exact (isAffineOpen_opensRange (CycleQ2LaurentProjectiveLine.chartInfinity k)).preimage _
      · rw [preimage_infinity]
        exact (CycleQ2HodgeBoundaryPencil.linearOpen_affine φ b).preimage q
  exact IsFinite.iff_isProper_and_isAffineHom.mpr ⟨hproper,haffine⟩

end CycleQ2RelativeHodgePencil

#print axioms CycleQ2RelativeHodgePencil.finite

namespace CycleQ2MarkedBoundaryPencil

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open CycleQ2LiteralIncidenceRelativeSpread CycleQ2LiteralIncidenceNormalizedSlice
  CycleQ2LiteralIncidenceRelativeCompletion CycleQ2LiteralIncidenceGenericCorrespondence
  CycleQ2GenericSmoothCurveGraph
open CycleQ2IncidenceEtaleParameter (parameterScheme)
open CycleQ2GeometricHodgeThreefold (threefold)
open CycleQ2MonicGenericSmooth (coeff)
open CycleQ2GenericHodgeModel (genericHodgeIso)
open CycleQ2HodgeBoundaryPencil (linearOpen)

variable (V : parameterScheme.Opens) (t : Fin 3 → ℂ) {C D : Scheme.{0}}
  (r : C ⟶ Completion V) (c : C ⟶ Spec (CommRingCat.of genericField))
  (hc : r ≫ structureMap V = c ≫ CycleQ2LiteralIncidenceGenericCorrespondence.genericPoint)
  (j : D ⟶ C) (a : D ⟶ Time toRaw V)
  (ha : j ≫ r = a ≫ CycleQ2LiteralIncidenceRelativeCompletion.inclusion V)
  [IsOpenImmersion j] [IsProper c] [SmoothOfRelativeDimension 1 c]

private theorem target_over :
    target V t r c hc ≫ pullback.snd ambientStructure genericPoint = toCurve V t r ≫ c := by
  rw [← embeddingGeneric_toAmbient V t r c hc,Category.assoc,← pullback.condition,
    ← Category.assoc,embeddingGeneric_toCurve]

/-- On each affine time subopen covered by the chosen pencil, the
finite normalization of the original closure has an actual finite map
to that time subopen times the original glued projective line. The two
chart inverse images retain the original target linear forms. -/
theorem normalized_affine_projection
    {N : Scheme.{0}} (ν : N ⟶ (fromTest V t r j a ha).image) [IsFinite ν]
    (a₀ a₁ : Fin 4 → genericField) (W : C.Opens)
    (hW : ((fromTest V t r j a ha).imageι ≫ toCurve V t r) ⁻¹ᵁ W ≤
      ((fromTest V t r j a ha).imageι ≫ target V t r c hc ≫ genericHodgeIso.inv) ⁻¹ᵁ
        (linearOpen coeff a₀ ⊔ linearOpen coeff a₁))
    (O : C.Opens) (hO : IsAffineOpen O) (hOW : O ≤ W) :
    let m := fromTest V t r j a ha
    let p := ν ≫ m.imageι ≫ toCurve V t r
    let q := ν ≫ m.imageι ≫ target V t r c hc ≫ genericHodgeIso.inv
    ∃ f : (p ⁻¹ᵁ O).toScheme ⟶
        pullback (O.ι ≫ c) (CycleQ2ProjectiveLineStructure.structureMap genericField),
      IsFinite f ∧ f ≫ pullback.fst _ _ = p ∣_ O ∧
      f ⁻¹ᵁ (pullback.snd _ _ ⁻¹ᵁ CycleQ2LaurentProjectiveLine.openZero genericField) =
        (p ⁻¹ᵁ O).ι ⁻¹ᵁ (q ⁻¹ᵁ linearOpen coeff a₀) ∧
      f ⁻¹ᵁ (pullback.snd _ _ ⁻¹ᵁ CycleQ2LaurentProjectiveLine.openInfinity genericField) =
        (p ⁻¹ᵁ O).ι ⁻¹ᵁ (q ⁻¹ᵁ linearOpen coeff a₁) := by
  let m := fromTest V t r j a ha
  let p := ν ≫ m.imageι ≫ toCurve V t r
  let q := ν ≫ m.imageι ≫ target V t r c hc ≫ genericHodgeIso.inv
  let qO := (p ⁻¹ᵁ O).ι ≫ q
  letI : NoetherianSpace (Graph V t r) :=
    CycleQ2LiteralIncidenceGenericModel.noetherian_of_proper (toCurve V t r ≫ c)
  letI : IsOpenImmersion m :=
    MorphismProperty.of_isPullback (test_square V t r j a ha) inferInstance
  letI : NoetherianSpace (TestSurface V t a) :=
    m.isOpenEmbedding.isInducing.noetherianSpace
  letI : IsAffine O.toScheme := hO
  letI : IsProper p := inferInstanceAs (IsProper (ν ≫ m.imageι ≫ toCurve V t r))
  letI : IsProper (p ∣_ O) :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict p O).flip inferInstance
  let e := ν ≫ m.imageι ≫ embeddingGeneric V t r c hc
  letI : IsAffineHom e :=
    inferInstanceAs (IsAffineHom (ν ≫ m.imageι ≫ embeddingGeneric V t r c hc))
  have hp : e ≫ pullback.fst c (pullback.snd ambientStructure genericPoint) = p := by
    simp only [e,p,Category.assoc,embeddingGeneric_toCurve]
  have hq : e ≫ pullback.snd c (pullback.snd ambientStructure genericPoint) ≫
      genericHodgeIso.inv = q := by
    simp only [e,q,Category.assoc,embeddingGeneric_toAmbient_assoc]
  letI : IsAffineHom qO := by
    have htarget := CycleQ2AffineTimeProduct.target_affine c
      (pullback.snd ambientStructure genericPoint) e O hO
    letI : IsAffineHom (((e ≫ pullback.fst c (pullback.snd ambientStructure genericPoint)) ⁻¹ᵁ O).ι ≫
        e ≫ pullback.snd c (pullback.snd ambientStructure genericPoint)) := htarget
    have hcomp : IsAffineHom
        ((((e ≫ pullback.fst c (pullback.snd ambientStructure genericPoint)) ⁻¹ᵁ O).ι ≫
          e ≫ pullback.snd c (pullback.snd ambientStructure genericPoint)) ≫ genericHodgeIso.inv) :=
      inferInstance
    simpa only [Category.assoc,hp,hq] using hcomp
  have hover : p ≫ c = q ≫ CycleQ2GeometricHodgeThreefold.toBase coeff := by
    simp only [p,q,Category.assoc,CycleQ2GenericHodgeModel.genericHodgeIso_inv_over,target_over]
  have hpq : (p ∣_ O) ≫ (O.ι ≫ c) = qO ≫ CycleQ2GeometricHodgeThreefold.toBase coeff := by
    rw [← Category.assoc,morphismRestrict_ι,Category.assoc,hover] <;> rfl
  have hcover : ∀ z : (p ⁻¹ᵁ O).toScheme,
      qO z ∈ linearOpen coeff a₀ ⊔ linearOpen coeff a₁ := by
    intro z
    exact hW (show (m.imageι ≫ toCurve V t r) (ν z.val) ∈ W from hOW z.property)
  let f := CycleQ2RelativeHodgePencil.productMap coeff (O.ι ≫ c) (p ∣_ O) qO hpq a₀ a₁ hcover
  refine ⟨f,CycleQ2RelativeHodgePencil.finite coeff (O.ι ≫ c) (p ∣_ O) qO hpq a₀ a₁ hcover,
    CycleQ2RelativeHodgePencil.productMap_fst coeff (O.ι ≫ c) (p ∣_ O) qO hpq a₀ a₁ hcover,?_,?_⟩
  · exact CycleQ2RelativeHodgePencil.preimage_zero coeff (O.ι ≫ c) (p ∣_ O) qO hpq a₀ a₁ hcover
  · exact CycleQ2RelativeHodgePencil.preimage_infinity coeff (O.ι ≫ c) (p ∣_ O) qO hpq a₀ a₁ hcover

/-- The actual marked normalization admits relative finite pencils
near every added time fiber. Its old smooth time open and the new time
neighborhood cover the same proper curve; no target open is removed
from a retained fiber. -/
theorem exists_relative_finite_model
    (hs : SmoothOfRelativeDimension 1 (curveMap toRaw V t)) :
    let m := fromTest V t r j a ha
    ∃ (N : Scheme.{0}) (ν : N ⟶ m.image) (ι : TestSurface V t a ⟶ N),
      IsFinite ν ∧ IsOpenImmersion ι ∧ IsDominant ι ∧
      ι ≫ ν = m.toImage ∧ IsIso (pullback.snd ν m.toImage) ∧
      ∃ a₀ a₁ : Fin 4 → genericField, ∃ W : C.Opens,
        j.opensRange ⊔ W = ⊤ ∧
        ∀ (O : C.Opens), IsAffineOpen O → O ≤ W →
          let p := ν ≫ m.imageι ≫ toCurve V t r
          let q := ν ≫ m.imageι ≫ target V t r c hc ≫ genericHodgeIso.inv
          ∃ f : (p ⁻¹ᵁ O).toScheme ⟶
              pullback (O.ι ≫ c) (CycleQ2ProjectiveLineStructure.structureMap genericField),
            IsFinite f ∧ f ≫ pullback.fst _ _ = p ∣_ O ∧
            f ⁻¹ᵁ (pullback.snd _ _ ⁻¹ᵁ CycleQ2LaurentProjectiveLine.openZero genericField) =
              (p ⁻¹ᵁ O).ι ⁻¹ᵁ (q ⁻¹ᵁ linearOpen coeff a₀) ∧
            f ⁻¹ᵁ (pullback.snd _ _ ⁻¹ᵁ CycleQ2LaurentProjectiveLine.openInfinity genericField) =
              (p ⁻¹ᵁ O).ι ⁻¹ᵁ (q ⁻¹ᵁ linearOpen coeff a₁) := by
  obtain ⟨N,ν,ι,hfinite,hopen,hdom,hfactor,hrecovery,_⟩ :=
    CycleQ2MarkedSurfaceNormalization.exists_finite_model V t r c j a ha hs
  obtain ⟨a₀,a₁,W,hunion,hW⟩ := exists_time_neighborhood V t r c hc j a ha hs
  letI : IsFinite ν := hfinite
  refine ⟨N,ν,ι,hfinite,hopen,hdom,hfactor,hrecovery,a₀,a₁,W,hunion,?_⟩
  intro O hO hOW
  exact normalized_affine_projection V t r c hc j a ha ν a₀ a₁ W hW O hO hOW

end CycleQ2MarkedBoundaryPencil

#print axioms CycleQ2MarkedBoundaryPencil.normalized_affine_projection
#print axioms CycleQ2MarkedBoundaryPencil.exists_relative_finite_model

namespace CycleQ2IntegralTwoFormTrace

open Algebra Module KaehlerDifferential
open CycleQ2WeightedCoordinateExterior (Form)
open CycleQ2ExactFrameThreeDeRham (exteriorPullback)
open CycleQ2FiniteFieldTwoFormTrace (traceTwo)

variable {k A L : Type} [CommRing k] [CommRing A] [Field L]
  [Algebra k A] [Algebra k L] [Algebra A L]

/-- The normal curve algebra is the integral closure in the very same
source function field. It is used only to test regularity of the
original field trace; the original finite source algebra is retained. -/
abbrev normalCurve := integralClosure A L

local instance : Algebra k (normalCurve (A := A) (L := L)) :=
  ((algebraMap A (normalCurve (A := A) (L := L))).comp (algebraMap k A)).toAlgebra
local instance : IsScalarTower k A (normalCurve (A := A) (L := L)) :=
  IsScalarTower.of_algebraMap_eq' rfl
local instance [IsScalarTower k A L] : IsScalarTower k (normalCurve (A := A) (L := L)) L :=
  IsScalarTower.of_algebraMap_eq (fun x => IsScalarTower.algebraMap_apply k A L x)

section NormalCurve

variable {F K : Type} [Field F] [CharZero F] [Field K] [IsDedekindDomain A]
  [Algebra F A] [Algebra A K] [Algebra K L] [IsScalarTower A K L]
  [Algebra.FiniteType F A] [IsFractionRing A K]
  [FiniteDimensional K L] [Algebra.IsSeparable K L]

include K in
/-- Finiteness and normality are proved for this actual integral
closure; smoothness is used only after passing to the curve over F. -/
theorem normalCurve_smooth : Algebra.Smooth F (normalCurve (A := A) (L := L)) := by
  let C := normalCurve (A := A) (L := L)
  letI : IsDedekindDomain C := integralClosure.isDedekindDomain A K L
  letI : Module.Finite A C := IsIntegralClosure.finite A K L C
  letI : Algebra.FiniteType F C :=
    Algebra.FiniteType.trans (inferInstance : Algebra.FiniteType F A) inferInstance
  exact CycleQ2NormalCurveSmooth.smooth_of_isDedekindDomain

end NormalCurve

section SourceMap

variable {B : Type} [CommRing B] [Algebra k B] [Algebra A B] [Algebra B L]
  [IsScalarTower k A B] [IsScalarTower k A L] [IsScalarTower k B L]
  [IsScalarTower A B L] [Algebra.IsIntegral A B]

/-- The original integral source algebra maps canonically into that
normal curve algebra through its unchanged function-field inclusion. -/
def toNormalCurve : B →ₐ[k] normalCurve (A := A) (L := L) :=
  (IsIntegralClosure.lift A (normalCurve (A := A) (L := L)) L (S := B)).restrictScalars k

theorem toNormalCurve_field :
    (IsScalarTower.toAlgHom k (normalCurve (A := A) (L := L)) L).comp
        (toNormalCurve (k := k) (A := A) (B := B) (L := L)) =
      IsScalarTower.toAlgHom k B L := by
  ext b
  exact IsIntegralClosure.algebraMap_lift A (normalCurve (A := A) (L := L)) L b

end SourceMap

section Trace

variable {F B K : Type} [Field F] [CharZero F] [IsDedekindDomain A]
  [CommRing B] [IsDomain B] [Field K]
  [Algebra k F] [Algebra k B] [Algebra k K]
  [Algebra F A] [Algebra F B] [Algebra F K] [Algebra F L]
  [Algebra A B] [Algebra A K] [Algebra B L] [Algebra K L]
  [IsScalarTower k F A] [IsScalarTower k F B] [IsScalarTower k F K] [IsScalarTower k F L]
  [IsScalarTower k A K] [IsScalarTower k B L] [IsScalarTower k K L]
  [IsScalarTower F A B] [IsScalarTower F A K] [IsScalarTower F B L]
  [IsScalarTower F K L] [IsScalarTower A B L] [IsScalarTower A K L]
  [Algebra.FiniteType F A] [Algebra.IsIntegral A B]
  [IsFractionRing A K] [IsFractionRing B L]
  [FiniteDimensional K L] [Algebra.IsSeparable K L]

/-- Every regular two-form on an integral finite source has a regular
trace on the original time algebra. Neither normality nor formal
smoothness of that source is a hypothesis. Pulling to the proved normal
curve leaves its original function-field form and trace unchanged. -/
theorem trace_regular (c : Ω[A⁄F] ≃ₗ[A] A) (hA : ¬ IsField A)
    (δ : Derivation k F F) (x : F) (hx : δ x = 1)
    (b : Basis (Fin 2) K Ω[K⁄k]) (hb : b 0 = D k K (algebraMap F K x))
    (ω : Form k B 2) :
    ∃ θ : Form k A 2,
      traceTwo b (exteriorPullback (IsScalarTower.toAlgHom k B L) 2 ω) =
        exteriorPullback (IsScalarTower.toAlgHom k A K) 2 θ := by
  letI : IsScalarTower k A B := IsScalarTower.to₁₂₄ k F A B
  letI : IsScalarTower k A L := IsScalarTower.to₁₂₄ k A K L
  letI : IsScalarTower F A L := IsScalarTower.to₁₂₄ F A K L
  let C := normalCurve (A := A) (L := L)
  letI : IsScalarTower k F C := IsScalarTower.of_algebraMap_eq fun y => by
    change algebraMap A C (algebraMap k A y) =
      algebraMap A C (algebraMap F A (algebraMap k F y))
    rw [IsScalarTower.algebraMap_apply k F A]
  letI : Algebra.Smooth F C := normalCurve_smooth (F := F) (A := A) (K := K) (L := L)
  letI : IsFractionRing C L := IsIntegralClosure.isFractionRing_of_finite_extension A K L C
  let i : B →ₐ[k] C := toNormalCurve (k := k) (A := A) (B := B) (L := L)
  have hi : (IsScalarTower.toAlgHom k C L).comp i = IsScalarTower.toAlgHom k B L :=
    toNormalCurve_field (k := k) (A := A) (B := B) (L := L)
  obtain ⟨θ,hθ⟩ := CycleQ2RegularFiniteTwoFormTrace.trace_regular
    (B := C) (K := K) (L := L) c hA δ x hx b hb (exteriorPullback i 2 ω)
  refine ⟨θ,?_⟩
  rw [← CycleQ2AffineDeRhamFunctorial.exteriorPullback_comp,hi] at hθ
  exact hθ

end Trace

end CycleQ2IntegralTwoFormTrace

#print axioms CycleQ2IntegralTwoFormTrace.normalCurve_smooth
#print axioms CycleQ2IntegralTwoFormTrace.toNormalCurve_field
#print axioms CycleQ2IntegralTwoFormTrace.trace_regular
