import Proposal.GeometricMonicGenericSupport

/-!
# Boundary dimension of the marked incidence surface

The scheme-theoretic closure here is the image of the test surface inside the graph
over the selected smooth proper curve. Both the added boundary and its proper image in
the target have dimension at most one. A dense open of a Noetherian scheme of dimension
at most two has complement of dimension at most one, even when the scheme is reducible.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2MarkedClosureBoundaryDimension

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
section ClosedImages

open Set Order TopologicalSpace Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  (f : X → Y) (hf : Continuous f) (hc : IsClosedMap f) [QuasiSober Y]

private def pointClosure (x : X) : IrreducibleCloseds X :=
  ⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩

include hf hc in
private theorem pointClosure_image (A : IrreducibleCloseds Y)
    (x : X) (h : f x = A.isIrreducible.genericPoint) :
    f '' (pointClosure x : Set X) = A := by
  change f '' closure {x} = (A : Set Y)
  rw [← hc.closure_image_eq_of_continuous hf, Set.image_singleton, h,
    A.isIrreducible.closure_genericPoint A.isClosed]

include hf hc in
/-- Every specialization chain of closed irreducible subsets lifts along a
surjective closed continuous map. -/
private theorem dimension_le_of_closed_surjective (hs : Function.Surjective f) :
    topologicalKrullDim Y ≤ topologicalKrullDim X := by
  have lift (p : LTSeries (IrreducibleCloseds Y)) :
      ∃ q : LTSeries (IrreducibleCloseds X),
        q.length = p.length ∧ f '' (q.head : Set X) = p.head := by
    induction p using RelSeries.inductionOn with
    | singleton A =>
      obtain ⟨x,hx⟩ := hs A.isIrreducible.genericPoint
      exact ⟨RelSeries.singleton _ (pointClosure x),rfl,pointClosure_image f hf hc A x hx⟩
    | cons p A hA ih =>
      change A < p.head at hA
      obtain ⟨q,hq,hqp⟩ := ih
      have hy : A.isIrreducible.genericPoint ∈ (p.head : Set Y) :=
        hA.le (A.isIrreducible.isGenericPoint_genericPoint A.isClosed).mem
      rw [← hqp] at hy
      obtain ⟨x,hxB,hx⟩ := hy
      have ha := pointClosure_image f hf hc A x hx
      have hlt : pointClosure x < q.head := by
        refine lt_of_le_of_ne (closure_minimal (singleton_subset_iff.mpr hxB) q.head.isClosed) ?_
        rintro he
        rw [he,hqp] at ha
        exact hA.ne (IrreducibleCloseds.ext ha.symm)
      refine ⟨q.cons _ hlt,?_,ha⟩
      change 0 + q.length + 1 = 0 + p.length + 1
      rw [hq]
  apply iSup_le
  intro p
  obtain ⟨q,hq,_⟩ := lift p
  exact hq ▸ q.length_le_krullDim

include hf hc in
/-- The projection of a closed subset has dimension at most that of the subset.
This applies to the boundary inside the marked closure for a proper projection. -/
private theorem closed_image_dimension (B : Set X) (hB : IsClosed B) :
    topologicalKrullDim (f '' B) ≤ topologicalKrullDim B := by
  let g : B → f '' B := fun x => ⟨f x,⟨x,x.property,rfl⟩⟩
  let : QuasiSober (f '' B) := (hc _ hB).isClosedEmbedding_subtypeVal.quasiSober
  apply dimension_le_of_closed_surjective g
    ((hf.comp continuous_subtype_val).subtype_mk _)
    ((hc.comp hB.isClosedMap_subtype_val).subtype_mk _)
  rintro ⟨y,x,hx,rfl⟩
  exact ⟨⟨x,hx⟩,rfl⟩

end ClosedImages

section Boundary

open TopologicalSpace Topology Order Set

variable {X : Type*} [TopologicalSpace X] [NoetherianSpace X]

/-- A dense open meets every component, so a chain in its complement extends strictly in the ambient space. -/
private theorem complement_dim_le_one (hX : topologicalKrullDim X ≤ 2) {U : Set X}
    (hU : IsOpen U) (hd : Dense U) : topologicalKrullDim (Uᶜ : Set X) ≤ 1 := by
  let B := (Uᶜ : Set X)
  let m : IrreducibleCloseds B → IrreducibleCloseds X :=
    IrreducibleCloseds.map Subtype.val continuous_subtype_val
  have hm : StrictMono m := IrreducibleCloseds.map_strictMono_of_isInducing IsInducing.subtypeVal
  change krullDim (IrreducibleCloseds B) ≤ 1
  rw [krullDim_le_one_iff]
  intro S
  by_contra! hh
  obtain ⟨T, hTS⟩ := not_isMin_iff.mp hh.1
  obtain ⟨A, hSA⟩ := not_isMax_iff.mp hh.2
  obtain ⟨Z, hZ, hAZ⟩ :=
    exists_mem_irreducibleComponents_subset_of_isIrreducible (m A : Set X) (m A).isIrreducible
  let C : IrreducibleCloseds X := ⟨Z, hZ.1, isClosed_of_mem_irreducibleComponents Z hZ⟩
  obtain ⟨O, hO, hnO, hOZ⟩ := NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent Z hZ
  obtain ⟨x, hxU, hxO⟩ := hd.exists_mem_open hO hnO
  have hB : (m A : Set X) ⊆ B :=
    closure_minimal (by rintro _ ⟨y, _, rfl⟩; exact y.2) hU.isClosed_compl
  have hAC : m A < C := lt_of_le_of_ne hAZ (by
    intro e
    have hxC : x ∈ C := hOZ hxO
    exact hB (e ▸ hxC) hxU)
  let p : LTSeries (IrreducibleCloseds X) := (RelSeries.singleton _ C).cons (m A) hAC
  let q := p.cons (m S) (by
    change m S < p.head
    have hp : p.head = m A := rfl
    rw [hp]
    exact hm hSA)
  let r := q.cons (m T) (by
    change m T < q.head
    have hq : q.head = m S := rfl
    rw [hq]
    exact hm hTS)
  have hlen := LTSeries.length_le_krullDim r
  change (3 : WithBot ℕ∞) ≤ topologicalKrullDim X at hlen
  exact (by decide : ¬ (3 : WithBot ℕ∞) ≤ 2) (hlen.trans hX)

end Boundary

open CycleQ2LiteralIncidenceRelativeSpread CycleQ2LiteralIncidenceNormalizedSlice
open CycleQ2LiteralIncidenceRelativeCompletion CycleQ2LiteralIncidenceGenericCorrespondence
open CycleQ2GenericSmoothCurveGraph
open CycleQ2IncidenceEtaleParameter (parameterScheme)

variable (V : parameterScheme.Opens) (t : Fin 3 → ℂ) {C D : Scheme.{0}}
  (r : C ⟶ Completion V) (c : C ⟶ Spec (CommRingCat.of genericField))
  (j : D ⟶ C) (a : D ⟶ Time toRaw V)
  (ha : j ≫ r = a ≫ CycleQ2LiteralIncidenceRelativeCompletion.inclusion V)
  [IsOpenImmersion j] [IsProper c] [SmoothOfRelativeDimension 1 c]

theorem boundary_dimensions
    (hc : r ≫ structureMap V = c ≫ CycleQ2LiteralIncidenceGenericCorrespondence.genericPoint)
    (hs : SmoothOfRelativeDimension 1 (curveMap toRaw V t)) :
    let f := fromTest V t r j a ha
    let q := f.imageι ≫ target V t r c hc
    topologicalKrullDim ((Set.range f.toImage)ᶜ : Set f.image) ≤ 1 ∧
    topologicalKrullDim (q '' (Set.range f.toImage)ᶜ) ≤ 1 := by
  let f := fromTest V t r j a ha
  let p := toCurve V t r ≫ c
  have : IsProper p := inferInstanceAs (IsProper (toCurve V t r ≫ c))
  have : NoetherianSpace (Graph V t r) := CycleQ2LiteralIncidenceGenericModel.noetherian_of_proper p
  have : IsOpenImmersion f :=
    MorphismProperty.of_isPullback (test_square V t r j a ha) inferInstance
  have : NoetherianSpace (TestSurface V t a) := f.isOpenEmbedding.isInducing.noetherianSpace
  have h : f ≫ p = pullback.fst a (curveMap toRaw V t) ≫ (j ≫ c) := by
    change fromTest V t r j a ha ≫ toCurve V t r ≫ c = _
    rw [← Category.assoc, ← (test_square V t r j a ha).w, Category.assoc]
  let : MorphismProperty.IsStableUnderBaseChange (@SmoothOfRelativeDimension 1) :=
    smoothOfRelativeDimension_isStableUnderBaseChange 1
  have : SmoothOfRelativeDimension 1 (pullback.fst a (curveMap toRaw V t)) :=
    MorphismProperty.pullback_fst _ _ hs
  have : SmoothOfRelativeDimension 1 (j ≫ c) := smoothOfRelativeDimension_comp 0 1 j c
  have htwo : SmoothOfRelativeDimension 2 (f ≫ p) := by
    rw [h]
    exact smoothOfRelativeDimension_comp 1 1 _ _
  let p' := f.imageι ≫ p
  have : SmoothOfRelativeDimension 2 (f.toImage ≫ p') := by simpa [p'] using htwo
  have hdim := CycleQ2CurveTopologicalDimension.dim_le_of_affines f.image 2
    (fun U => CycleQ2CurveChartDimension.chart_dimension_le 2 f.toImage p' U.2)
  have : NoetherianSpace f.image := f.imageι.isClosedEmbedding.isInducing.noetherianSpace
  have hd := complement_dim_le_one hdim f.toImage.isOpenEmbedding.isOpen_range f.toImage.denseRange
  let q := f.imageι ≫ target V t r c hc
  have : IsProper (target V t r c hc) := target_proper V t r c hc
  have : IsProper q := inferInstanceAs (IsProper (f.imageι ≫ target V t r c hc))
  exact ⟨hd,(closed_image_dimension q q.continuous q.isClosedMap _
    f.toImage.isOpenEmbedding.isOpen_range.isClosed_compl).trans hd⟩

open CycleQ2IncidenceSeedFiberCover (seedBasePoint)
open CycleQ2LiteralIncidenceRelativeCorrespondence

/-- For any independent parameter there is a seed neighborhood on which every nonempty
time test open yields a nonempty marked surface with a proper closure. Its boundary
and the image of that boundary in the original threefold have dimension at most one. -/
theorem exists_bounded_boundary (ht : AlgebraicIndependent ℚ t) :
    ∃ V : parameterScheme.Opens, seedBasePoint ∈ V ∧
      ∀ W : (Time toRaw V).Opens, (W : Set (Time toRaw V)).Nonempty →
      ∃ (C : Scheme) (c : C ⟶ Spec (CommRingCat.of genericField)) (r : C ⟶ Completion V)
        (hc : r ≫ structureMap V = c ≫ CycleQ2LiteralIncidenceGenericCorrespondence.genericPoint)
        (D : Scheme) (j : D ⟶ C) (a : D ⟶ Time toRaw V)
        (ha : j ≫ r = a ≫ CycleQ2LiteralIncidenceRelativeCompletion.inclusion V),
        let m := fromTest V t r j a ha
        IsProper c ∧ IsOpenImmersion j ∧ Nonempty D ∧ Set.range a ⊆ (W : Set (Time toRaw V)) ∧
        Nonempty (TestSurface V t a) ∧ IsProper (m.imageι ≫ target V t r c hc) ∧
        topologicalKrullDim ((Set.range m.toImage)ᶜ : Set m.image) ≤ 1 ∧
        topologicalKrullDim ((m.imageι ≫ target V t r c hc) '' (Set.range m.toImage)ᶜ) ≤ 1 := by
  obtain ⟨V,hV,hs,_,_,hSurj,_,_⟩ := exists_surjective_completion t ht
  refine ⟨V,hV,?_⟩
  intro W hW
  obtain ⟨C,c,r,hc,_,hp,_,_,_,hq,_,⟨f,_,_,hfc,hfd⟩,D,j,a,ha,hj,_,hn,hW',_⟩ :=
    CycleQ2GenericGraphFiniteProjection.exists_smooth_curve_graph_with_projection (t := t) W hW
  have : SmoothOfRelativeDimension 1 c := hfc ▸ hfd
  obtain ⟨x,_⟩ := (pullback.fst a (curveMap toRaw V t)).surjective (Classical.choice hn)
  exact ⟨C,c,r,hc,D,j,a,ha,hp,hj,hn,hW',⟨x⟩,inferInstance,boundary_dimensions V t r c j a ha hc hs⟩

end CycleQ2MarkedClosureBoundaryDimension

#print axioms CycleQ2MarkedClosureBoundaryDimension.exists_bounded_boundary
