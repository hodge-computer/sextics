import Proposal.GeometricMonicGenericSupport
import Proposal.GeometricSmoothDimensionLower

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

/-! The dimension estimate is used on the original boundary inside the
fourfold. The following constructions retain its actual points and
closed embeddings while replacing a component by a smooth dense open. -/

namespace CycleQ2SmallBoundaryStrata

open CategoryTheory AlgebraicGeometry TopologicalSpace Topology Set

variable {k : Type} [Field k] {X Y : Scheme.{0}}

/-- A smooth morphism to a field has a neighborhood with one specified
relative dimension. The neighborhood is an actual open of the source. -/
theorem smooth_dimension_neighborhood (p : X ⟶ Spec (CommRingCat.of k))
    [Smooth p] (x : X) :
    ∃ (V : X.Opens), x ∈ V ∧ ∃ n : ℕ,
      SmoothOfRelativeDimension n (V.ι ≫ p) := by
  obtain ⟨U,hU,V,hV,hx,hle,hs⟩ := Smooth.exists_isStandardSmooth p x
  have hUtop : U = ⊤ := by
    apply top_unique
    intro y _
    exact Subsingleton.elim (p x) y ▸ hle hx
  subst U
  let R := Γ(Spec (CommRingCat.of k),⊤)
  let A := Γ(X,V)
  letI : Algebra R A := (p.appLE ⊤ V hle).hom.toAlgebra
  obtain ⟨ι,σ,hσ,hι,⟨P⟩⟩ := hs.toAlgebra
  let n := P.dimension
  have hn : RingHom.IsStandardSmoothOfRelativeDimension n (p.appLE ⊤ V hle).hom :=
    ⟨ι,σ,hσ,hι,⟨P,rfl⟩⟩
  have hzero : RingHom.IsStandardSmoothOfRelativeDimension 0
      (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom :=
    RingHom.IsStandardSmoothOfRelativeDimension.equiv
      (asIso (Scheme.ΓSpecIso (CommRingCat.of k)).inv).commRingCatIsoToRingEquiv
  have hcoeff : RingHom.IsStandardSmoothOfRelativeDimension n
      (CycleQ2IntegralCurveNormalization.coefficientMap k p V).hom := by
    change RingHom.IsStandardSmoothOfRelativeDimension n
      ((p.appLE ⊤ V hle).hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom)
    simpa only [Nat.add_zero] using hn.comp hzero
  have hspec : SmoothOfRelativeDimension n (hV.fromSpec ≫ p) := by
    rw [CycleQ2IntegralCurveNormalization.fromSpec_over k p hV]
    apply (HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension n)).mpr
    exact RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _ hcoeff
  refine ⟨V,hx,n,?_⟩
  simpa only [Nat.zero_add,IsAffineOpen.fromSpec,Category.assoc,Iso.hom_inv_id_assoc] using
    (smoothOfRelativeDimension_comp 0 n hV.isoSpec.hom (hV.fromSpec ≫ p))

/-- On a scheme of dimension at most one, every smooth point has an
actual smooth neighborhood of relative dimension zero or one. -/
theorem small_smooth_neighborhood (p : X ⟶ Spec (CommRingCat.of k)) [Smooth p]
    (hdim : topologicalKrullDim X ≤ 1) (x : X) :
    ∃ (V : X.Opens), x ∈ V ∧ ∃ n : ℕ, n ≤ 1 ∧
      SmoothOfRelativeDimension n (V.ι ≫ p) := by
  obtain ⟨V,hx,n,hn⟩ := smooth_dimension_neighborhood p x
  letI : SmoothOfRelativeDimension n (V.ι ≫ p) := hn
  letI : Nonempty V.toScheme := ⟨⟨x,hx⟩⟩
  have h := (CycleQ2SmoothDimensionLower.le_topologicalKrullDim n (V.ι ≫ p)).trans
    (V.ι.isOpenEmbedding.isInducing.topologicalKrullDim_le.trans hdim)
  exact ⟨V,hx,n,by exact_mod_cast h,hn⟩

variable [CharZero k]

/-- A finite-type integral component has a smooth open through its
original generic point, with the relative dimension bounded by its
given topological dimension. -/
theorem dense_small_smooth_piece [IsIntegral X]
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    (hdim : topologicalKrullDim X ≤ 1) :
    ∃ (M : Scheme.{0}) (j : M ⟶ X), IsOpenImmersion j ∧
      genericPoint X ∈ Set.range j ∧ ∃ n : ℕ, n ≤ 1 ∧
        SmoothOfRelativeDimension n (j ≫ p) := by
  let U := p.smoothLocus
  have hη : genericPoint X ∈ U := p.genericPoint_mem_smoothLocus_of_perfectField
  have hs : Smooth (U.ι ≫ p) := by
    apply Scheme.Hom.smoothLocus_eq_top_iff.mp
    rw [← Scheme.Hom.preimage_smoothLocus_eq]
    apply top_unique
    intro y _
    exact y.property
  have hUdim := U.ι.isOpenEmbedding.isInducing.topologicalKrullDim_le.trans hdim
  obtain ⟨V,hV,n,hn,hsm⟩ := small_smooth_neighborhood (U.ι ≫ p) hUdim ⟨genericPoint X,hη⟩
  let j : V.toScheme ⟶ X := V.ι ≫ U.ι
  refine ⟨V.toScheme,j,inferInstance,⟨⟨⟨genericPoint X,hη⟩,hV⟩,rfl⟩,n,hn,?_⟩
  simpa only [j,Category.assoc] using hsm

/-- The discarded part of this actual component is a finite closed
set, rather than a projection of a larger deleted subset. -/
theorem finite_discarded [IsIntegral X] [NoetherianSpace X]
    (hdim : topologicalKrullDim X ≤ 1) {M : Scheme.{0}} (j : M ⟶ X)
    [IsOpenImmersion j] (hη : genericPoint X ∈ Set.range j) :
    ((Set.range j)ᶜ : Set X).Finite := by
  apply CycleQ2ProperCurveFiniteFibres.finite_closed_proper hdim
    j.isOpenEmbedding.isOpen_range.isClosed_compl
  intro h
  have hmem : genericPoint X ∈ (Set.range j)ᶜ := by rw [h]; exact Set.mem_univ _
  exact hmem hη

end CycleQ2SmallBoundaryStrata

namespace CycleQ2BoundaryPointClosure

open CategoryTheory AlgebraicGeometry TopologicalSpace Topology Set

variable (Y : Scheme.{0})

/-- The reduced integral closed scheme with the closure of the given
point as its underlying closed subset. -/
abbrev Model (x : Y) := (Y.fromSpecResidueField x).image

abbrev inclusion (x : Y) : Model Y x ⟶ Y := (Y.fromSpecResidueField x).imageι

instance (x : Y) : IsClosedImmersion (inclusion Y x) := inferInstance

instance integral (x : Y) : IsIntegral (Model Y x) :=
  CycleQ2IncidenceIntegralComponent.integral_image (Y.fromSpecResidueField x)

theorem range_inclusion (x : Y) : Set.range (inclusion Y x) = closure ({x} : Set Y) := by
  change Set.range (Y.fromSpecResidueField x).ker.subschemeι = _
  rw [Scheme.IdealSheafData.range_subschemeι,Scheme.Hom.support_ker,
    Scheme.range_fromSpecResidueField]

theorem genericPoint_inclusion (x : Y) : inclusion Y x (genericPoint (Model Y x)) = x := by
  let f := Y.fromSpecResidueField x
  let a : Spec (Y.residueField x) := default
  have hrange : Set.range f.toImage = {f.toImage a} := by
    ext z
    constructor
    · rintro ⟨b,rfl⟩
      exact congrArg f.toImage (Subsingleton.elim b a)
    · intro hz
      exact ⟨a,(Set.mem_singleton_iff.mp hz).symm⟩
  have hg : IsGenericPoint (f.toImage a) (Set.univ : Set f.image) := by
    change closure ({f.toImage a} : Set f.image) = Set.univ
    rw [← hrange]
    exact f.toImage.denseRange.closure_range
  have he : f.toImage a = genericPoint (Model Y x) := hg.eq (genericPoint_spec _)
  calc
    inclusion Y x (genericPoint (Model Y x)) = inclusion Y x (f.toImage a) := by rw [he]
    _ = f a := congrArg (fun g : Spec (Y.residueField x) ⟶ Y => g a) f.toImage_imageι
    _ = x := Y.fromSpecResidueField_apply x a

/-- The dimension bound is pulled back along the actual closed
embedding into the given boundary subset. -/
theorem dimension_le (x : Y) {B : Set Y} (hB : IsClosed B) (hx : x ∈ B)
    (hdim : topologicalKrullDim B ≤ 1) : topologicalKrullDim (Model Y x) ≤ 1 := by
  have hi : Set.range (inclusion Y x) ⊆ B := by
    rw [range_inclusion]
    exact closure_minimal (Set.singleton_subset_iff.mpr hx) hB
  let g : Model Y x → B := fun z => ⟨inclusion Y x z,hi ⟨z,rfl⟩⟩
  have hg : IsInducing g := IsInducing.subtypeVal.of_comp_iff.mp
    (inclusion Y x).isClosedEmbedding.isInducing
  exact hg.topologicalKrullDim_le.trans hdim

end CycleQ2BoundaryPointClosure

#print axioms CycleQ2SmallBoundaryStrata.dense_small_smooth_piece
#print axioms CycleQ2BoundaryPointClosure.genericPoint_inclusion
#print axioms CycleQ2BoundaryPointClosure.dimension_le

namespace CycleQ2OneDimensionalClosedSubsets

open TopologicalSpace Topology Order Set

variable {T : Type} [TopologicalSpace T] [T0Space T]

private def pointClosure (x : T) : IrreducibleCloseds T :=
  ⟨closure ({x} : Set T),isIrreducible_singleton.closure,isClosed_closure⟩

/-- In a space of dimension at most one, every point other than a
generic point of a component is closed. Reducibility is allowed. -/
theorem closed_of_not_generic (hdim : topologicalKrullDim T ≤ 1) {x : T}
    (hx : x ∉ genericPoints T) : IsClosed ({x} : Set T) := by
  obtain ⟨Z,hZ,hxZ⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
    (closure ({x} : Set T)) isIrreducible_singleton.closure
  let C : IrreducibleCloseds T := ⟨Z,hZ.1,isClosed_of_mem_irreducibleComponents Z hZ⟩
  have hlt : pointClosure x < C := lt_of_le_of_ne hxZ (by
    intro h
    apply hx
    change closure ({x} : Set T) ∈ irreducibleComponents T
    have he : closure ({x} : Set T) = Z :=
      congrArg (fun s : IrreducibleCloseds T => (s : Set T)) h
    rw [he]
    exact hZ)
  by_contra hclosed
  have hn : ¬ closure ({x} : Set T) ⊆ {x} := fun h =>
    hclosed ((Set.Subset.antisymm h subset_closure) ▸ isClosed_closure)
  obtain ⟨y,hy,hyx⟩ := Set.not_subset.mp hn
  have hylt : pointClosure y < pointClosure x := by
    refine lt_of_le_of_ne (closure_minimal (Set.singleton_subset_iff.mpr hy) isClosed_closure) ?_
    intro he
    apply hyx
    rw [Set.mem_singleton_iff]
    apply IsGenericPoint.eq (S := closure ({y} : Set T))
    · rfl
    · exact congrArg (fun s : IrreducibleCloseds T => (s : Set T)) he.symm
  let a : LTSeries (IrreducibleCloseds T) := (RelSeries.singleton _ C).cons (pointClosure x) hlt
  let b : LTSeries (IrreducibleCloseds T) := a.cons (pointClosure y) (by
    change pointClosure y < a.head
    simpa only [a,RelSeries.head_cons] using hylt)
  have h := LTSeries.length_le_krullDim b
  change (2 : WithBot ℕ∞) ≤ topologicalKrullDim T at h
  exact (by decide : ¬ (2 : WithBot ℕ∞) ≤ 1) (h.trans hdim)

/-- A closed set omitting every component generic point is finite in
a Noetherian sober space of dimension at most one. -/
theorem finite_closed_avoiding_generics [NoetherianSpace T] [QuasiSober T]
    (hdim : topologicalKrullDim T ≤ 1) {S : Set T} (hS : IsClosed S)
    (havoid : ∀ x ∈ genericPoints T, x ∉ S) : S.Finite := by
  obtain ⟨A,hA,hcl,hirr,hcover⟩ := NoetherianSpace.exists_finite_set_isClosed_irreducible hS
  rw [hcover]
  apply hA.sUnion
  intro W hW
  have hWS : W ⊆ S := by
    rw [hcover]
    exact Set.subset_sUnion_of_mem hW
  have hg := (hirr W hW).closure_genericPoint (hcl W hW)
  have hn : (hirr W hW).genericPoint ∉ genericPoints T := by
    intro h
    exact havoid _ h (hWS ((hirr W hW).isGenericPoint_genericPoint (hcl W hW)).mem)
  rw [← hg,(closed_of_not_generic hdim hn).closure_eq]
  exact Set.finite_singleton _

variable [NoetherianSpace T] [QuasiSober T]

/-- Covering the actual component generic points leaves only finitely
many closed points of the original boundary. -/
theorem finite_residual {B : Set T} (hB : IsClosed B)
    (hdim : topologicalKrullDim B ≤ 1) (O : Opens T)
    (hgeneric : ∀ x : genericPoints B, (x.val : T) ∈ O) :
    (B ∩ (O : Set T)ᶜ).Finite ∧
      ∀ x ∈ B ∩ (O : Set T)ᶜ, IsClosed ({x} : Set T) := by
  letI : NoetherianSpace B := NoetherianSpace.set B
  letI : QuasiSober B := hB.isClosedEmbedding_subtypeVal.quasiSober
  let S : Set B := Subtype.val ⁻¹' (O : Set T)ᶜ
  have hS : IsClosed S := O.isOpen.isClosed_compl.preimage continuous_subtype_val
  have hn : ∀ x ∈ genericPoints B, x ∉ S := by
    intro x hx hs
    exact hs (hgeneric ⟨x,hx⟩)
  have hfin := finite_closed_avoiding_generics hdim hS hn
  have himage : Subtype.val '' S = B ∩ (O : Set T)ᶜ := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact ⟨y.property,hy⟩
    · rintro ⟨hx,hxO⟩
      exact ⟨⟨x,hx⟩,hxO,rfl⟩
  refine ⟨himage ▸ hfin.image Subtype.val,?_⟩
  intro x hx
  let b : B := ⟨x,hx.1⟩
  have hb : b ∉ genericPoints B := fun h => hx.2 (hgeneric ⟨b,h⟩)
  have hc := hB.isClosedMap_subtype_val _ (closed_of_not_generic hdim hb)
  simpa only [Set.image_singleton] using hc

end CycleQ2OneDimensionalClosedSubsets

namespace CycleQ2SmallBoundaryStrata

open CategoryTheory AlgebraicGeometry TopologicalSpace Topology Set

variable {k : Type} [Field k] [CharZero k] {Y : Scheme.{0}}
  (q : Y ⟶ Spec (CommRingCat.of k)) (B : Set Y)

/-- A smooth piece of the original closed boundary. Its closure is
still embedded in the original ambient scheme; smoothness is asserted
only on the specified open source. -/
structure Chart where
  Z : Scheme.{0}
  M : Scheme.{0}
  i : Z ⟶ Y
  j : M ⟶ Z
  closed : IsClosedImmersion i
  openImmersion : IsOpenImmersion j
  dimension : ℕ
  dimension_le : dimension ≤ 1
  smooth : SmoothOfRelativeDimension dimension (j ≫ i ≫ q)
  O : Y.Opens
  support : (O : Set Y) ∩ B = (O : Set Y) ∩ Set.range i
  inside : ∀ z, i z ∈ O → z ∈ Set.range j

variable [NoetherianSpace Y] [LocallyOfFiniteType q]
  (hB : IsClosed B) (hdim : topologicalKrullDim B ≤ 1)

/-- Each original component generic point has a chart in which the
whole boundary is exactly one smooth component open. -/
theorem chart_at_generic (b : genericPoints B) :
    ∃ A : Chart q B, (b.val : Y) ∈ A.O := by
  letI : NoetherianSpace B := NoetherianSpace.set B
  letI : QuasiSober B := hB.isClosedEmbedding_subtypeVal.quasiSober
  let C := (genericPoints.component b).val
  have hC : C ∈ irreducibleComponents B := (genericPoints.component b).property
  obtain ⟨Q,hQ,hQne,hQC⟩ :=
    NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent C hC
  have hbQ : b.val ∈ Q := (genericPoints.isGenericPoint b).mem_open_set_iff hQ |>.mpr (by
    obtain ⟨x,hx⟩ := hQne
    exact ⟨x,hQC hx,hx⟩)
  obtain ⟨N,hN,hpre⟩ := (IsInducing.subtypeVal.isOpen_iff).mp hQ
  have hbN : (b.val : Y) ∈ N := by
    change b.val ∈ Subtype.val ⁻¹' N
    rw [hpre]
    exact hbQ
  let x : Y := b.val
  let Z := CycleQ2BoundaryPointClosure.Model Y x
  let i : Z ⟶ Y := CycleQ2BoundaryPointClosure.inclusion Y x
  have hiB : Set.range i ⊆ B := by
    rw [CycleQ2BoundaryPointClosure.range_inclusion]
    exact closure_minimal (Set.singleton_subset_iff.mpr b.val.property) hB
  have hiC : Set.range i = Subtype.val '' C := by
    rw [CycleQ2BoundaryPointClosure.range_inclusion]
    have h := (genericPoints.isGenericPoint b).image continuous_subtype_val
    have hc : IsClosed (Subtype.val '' C) :=
      hB.isClosedMap_subtype_val _ (isClosed_of_mem_irreducibleComponents C hC)
    exact h.def.trans hc.closure_eq
  have hBN : B ∩ N ⊆ Set.range i := by
    rintro y ⟨hyB,hyN⟩
    have hyQ : (⟨y,hyB⟩ : B) ∈ Q := by rw [← hpre]; exact hyN
    rw [hiC]
    exact ⟨⟨y,hyB⟩,hQC hyQ,rfl⟩
  have hZdim := CycleQ2BoundaryPointClosure.dimension_le Y x hB b.val.property hdim
  obtain ⟨M,j,hj,hη,n,hn,hsm⟩ := dense_small_smooth_piece (i ≫ q) hZdim
  letI : IsOpenImmersion j := hj
  let D : Set Y := i '' (Set.range j)ᶜ
  have hD : IsClosed D := i.isClosedEmbedding.isClosedMap _
    j.isOpenEmbedding.isOpen_range.isClosed_compl
  let O : Y.Opens := ⟨N ∩ Dᶜ,hN.inter hD.isOpen_compl⟩
  have hxO : x ∈ O := by
    refine ⟨hbN,?_⟩
    rintro ⟨z,hz,he⟩
    have hzη : z = genericPoint Z := i.isClosedEmbedding.injective
      (he.trans (CycleQ2BoundaryPointClosure.genericPoint_inclusion Y x).symm)
    rw [hzη] at hz
    exact hz hη
  refine ⟨⟨Z,M,i,j,inferInstance,hj,n,hn,by simpa only [Category.assoc] using hsm,O,?_,?_⟩,hxO⟩
  · ext y
    constructor
    · rintro ⟨hyO,hyB⟩
      exact ⟨hyO,hBN ⟨hyB,hyO.1⟩⟩
    · rintro ⟨hyO,hyI⟩
      exact ⟨hyO,hiB hyI⟩
  · intro z hz
    by_contra hn
    exact hz.2 ⟨z,hn,rfl⟩

/-- The actual boundary is covered by smooth curve or point pieces
away from finitely many closed points. Every chart stays in the
original ambient scheme. -/
theorem exists_smooth_open_with_finite_residual :
    ∃ O : Y.Opens,
      (B ∩ (O : Set Y)ᶜ).Finite ∧
      (∀ x ∈ B ∩ (O : Set Y)ᶜ, IsClosed ({x} : Set Y)) ∧
      ∀ y ∈ O, ∃ A : Chart q B, A.O ≤ O ∧ y ∈ A.O := by
  classical
  choose A hA using chart_at_generic q B hB hdim
  let O : Y.Opens := ⨆ b : genericPoints B, (A b).O
  have hgen : ∀ b : genericPoints B, (b.val : Y) ∈ O := fun b =>
    (le_iSup (fun b : genericPoints B => (A b).O) b) (hA b)
  obtain ⟨hfin,hclosed⟩ := CycleQ2OneDimensionalClosedSubsets.finite_residual hB hdim O hgen
  refine ⟨O,hfin,hclosed,?_⟩
  intro y hy
  obtain ⟨b,hb⟩ := Opens.mem_iSup.mp hy
  exact ⟨A b,le_iSup (fun b : genericPoints B => (A b).O) b,hb⟩

end CycleQ2SmallBoundaryStrata

#print axioms CycleQ2OneDimensionalClosedSubsets.finite_residual
#print axioms CycleQ2SmallBoundaryStrata.exists_smooth_open_with_finite_residual

namespace CycleQ2SmallBoundaryStrata

open CategoryTheory AlgebraicGeometry TopologicalSpace Topology Set

variable {k : Type} [Field k] [CharZero k] {Y : Scheme.{0}}
  (q : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType q]
  (B : Set Y) (hfinite : B.Finite)
  (hclosed : ∀ x ∈ B, IsClosed ({x} : Set Y))

/-- Each point of a finite closed-point support has a smooth chart
using the closed image of its own residue-field point. No rationality
of the point over the coefficient field is assumed. -/
theorem chart_at_closed_point (x : Y) (hx : x ∈ B) :
    ∃ A : Chart q B, x ∈ A.O := by
  let Z := CycleQ2BoundaryPointClosure.Model Y x
  let i : Z ⟶ Y := CycleQ2BoundaryPointClosure.inclusion Y x
  have hrange : Set.range i = {x} :=
    (CycleQ2BoundaryPointClosure.range_inclusion Y x).trans (hclosed x hx).closure_eq
  have hvalue (z : Z) : i z = x := Set.mem_singleton_iff.mp (hrange ▸ ⟨z,rfl⟩)
  letI : Subsingleton Z := ⟨fun z w => i.isClosedEmbedding.injective
    ((hvalue z).trans (hvalue w).symm)⟩
  have hdim : topologicalKrullDim Z ≤ 1 :=
    (topologicalKrullDim_zero_of_discreteTopology Z).trans (by decide)
  obtain ⟨M,j,hj,hη,n,hn,hsm⟩ := dense_small_smooth_piece (i ≫ q) hdim
  letI : IsOpenImmersion j := hj
  have hD : IsClosed (B \ {x}) := by
    have he : B \ {x} = ⋃ y ∈ B \ {x}, ({y} : Set Y) := by ext y; simp
    rw [he]
    exact hfinite.sdiff.isClosed_biUnion (fun y hy => hclosed y hy.1)
  let O : Y.Opens := ⟨(B \ {x})ᶜ,hD.isOpen_compl⟩
  have hxO : x ∈ O := fun h => h.2 (Set.mem_singleton x)
  refine ⟨⟨Z,M,i,j,inferInstance,hj,n,hn,by simpa only [Category.assoc] using hsm,O,?_,?_⟩,hxO⟩
  · ext y
    rw [hrange]
    constructor
    · rintro ⟨hyO,hyB⟩
      refine ⟨hyO,?_⟩
      by_contra hyx
      exact hyO ⟨hyB,hyx⟩
    · rintro ⟨hyO,hyx⟩
      refine ⟨hyO,?_⟩
      rw [Set.mem_singleton_iff.mp hyx]
      exact hx
  · intro z _
    have hz : z = genericPoint Z := Subsingleton.elim _ _
    rw [hz]
    exact hη

end CycleQ2SmallBoundaryStrata

#print axioms CycleQ2SmallBoundaryStrata.chart_at_closed_point
