import Proposal.GeometricLogarithmicGraphAgreement
import Proposal.GeometricMarkedEquationCharts
import Proposal.GeometricNormalCoordinateFrames
import Proposal.GeometricLocalDeRhamPurity
import Proposal.GeometricSupportedMayerVietorisDescent

/-! Over a field extending the complex numbers, a smooth surface closed in a Noetherian smooth
fourfold has a global supported de Rham class. On each affine equation chart its restriction
is the logarithmic class of the two equations.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false

noncomputable section

namespace CycleQ2SmoothTwoChartAgreement

open CategoryTheory AlgebraicGeometry TopologicalSpace
open CycleQ2InjectiveCech (AbSheaf)
open CycleQ2ClosedGraphSupport (complement classOf)
open CycleQ2LocalPrincipalGysin (cover locus)
open CycleQ2LocalPrincipalRestriction (res)
open CycleQ2FiniteExactAffineAtlas (HasFrame hasFrame_of_affine_le)
open CycleQ2RelativeSupportRefinement (supportMap)
open CycleQ2RelativeSupportComposition (supportMap_comp)

variable {k : Type} [Field k] [CharZero k] {X Y : Scheme.{0}}
  (p : X ⟶ Spec (CommRingCat.of k)) (q : Y ⟶ Spec (CommRingCat.of k))
  (i : X ⟶ Y) [IsClosedImmersion i] (hi : i ≫ q = p)
  [SmoothOfRelativeDimension 2 p] [SmoothOfRelativeDimension 4 q]

local instance : HasDerivedCategory.{1} (AbSheaf (show TopCat from Y)) := HasDerivedCategory.standard _
private abbrev Eoff := DerivedCategory.singleFunctor (AbSheaf (show TopCat from Y)) 0
private abbrev cleOff (i : X ⟶ Y) [IsClosedImmersion i] (U : Y.Opens) : U ⊓ complement i ≤ U := inf_le_left

open CategoryTheory.Limits
open CycleQ2ClosedGraphSupport (support)
open CycleQ2InjectiveCech (freeOpenMap)
open CycleQ2MayerVietorisRestriction (freeOpenSheaf)

theorem isZero_support_off_graph (T : Y.Opens) (h : T ≤ complement i) :
    IsZero (support i T) := by
  let : IsIso (homOfLE (cleOff i T)) := homOfLE_isIso_of_eq _ (inf_eq_left.mpr h)
  have : IsIso (freeOpenMap (cleOff i T)) :=
    inferInstanceAs (IsIso (freeOpenSheaf.map (homOfLE (cleOff i T))))
  exact isZero_cokernel_of_epi (freeOpenMap (cleOff i T))

include hi in
theorem exists_agreement_at_ambient_point (U W : Y.affineOpens) (y : Y) (hyU : y ∈ U.1) (hyW : y ∈ W.1)
    (f g : Γ(Y,U.1)) (f' g' : Γ(Y,W.1))
    (hf : Ideal.span {f,g} = i.ker.ideal U) (hg : Ideal.span {f',g'} = i.ker.ideal W)
    (ho : IsAffineOpen (cover f g).X₁ ∧ HasFrame q 4 (cover f g).X₁)
    (hn : IsAffineOpen (cover f' g').X₁ ∧ HasFrame q 4 (cover f' g').X₁) :
    ∃ (T : Y.affineOpens) (a : T.1 ≤ U.1) (b : T.1 ≤ W.1), y ∈ T.1 ∧
      restriction i a ≫ classOf i f g q 4 (locus_of_span i U f g hf) ho =
      restriction i b ≫ classOf i f' g' q 4 (locus_of_span i W f' g' hg) hn := by
  by_cases hy : y ∈ Set.range i
  · obtain ⟨x,rfl⟩ := hy
    exact exists_agreement p q i hi U W x hyU hyW f g f' g' hf hg ho hn
  · have hy' : y ∈ (U.1 ⊓ W.1) ⊓ complement i := ⟨⟨hyU,hyW⟩,hy⟩
    obtain ⟨T,hT,hyT,h⟩ := (Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens) hy'
    refine ⟨⟨T,hT⟩,(h.trans inf_le_left).trans inf_le_left,(h.trans inf_le_left).trans inf_le_right,hyT,?_⟩
    exact (Eoff.map_isZero (isZero_support_off_graph i T (h.trans inf_le_right))).eq_of_src _ _

end CycleQ2SmoothTwoChartAgreement

namespace CycleQ2SmoothSurfaceGysin
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open CycleQ2FiniteExactAffineAtlas (HasFrame hasFrame_of_affine_le)
open CycleQ2SmoothTwoChartAgreement (locus_of_span pairFrame)
open CycleQ2ClosedGraphSupport (complement support classOf)
open CycleQ2IntrinsicDeRhamSheaves (relativeDeRhamInt)
open CycleQ2InjectiveCech (AbSheaf)
open CycleQ2AdaptedAffineFrame (ExactOnOpen)
variable {k : Type} [Field k] [CharZero k] {X Y : Scheme.{0}}
  (p : X ⟶ Spec (CommRingCat.of k)) (q : Y ⟶ Spec (CommRingCat.of k))
  (i : X ⟶ Y) [IsClosedImmersion i] (hi : i ≫ q = p)
  [SmoothOfRelativeDimension 2 p] [SmoothOfRelativeDimension 4 q]

omit [CharZero k] in
include hi in
theorem exists_chart
    (x : X) (N : Y.Opens)
    (hx : i x ∈ N) :
    ∃ (U : Y.affineOpens) (f g : Γ(Y, U.1)),
      i x ∈ U.1 ∧ U.1 ≤ N ∧ HasFrame q 4 U.1 ∧
      Ideal.span {f,g} = i.ker.ideal U := by
  let : Smooth q := SmoothOfRelativeDimension.smooth 4 q
  let : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian q
  obtain ⟨U,⟨hU,hframe⟩,hzU,hUN⟩ :=
    (Opens.isBasis_iff_nbhd.mp (CycleQ2FiniteExactAffineAtlas.isBasis q 4)) hx
  obtain ⟨s,hs'⟩ :=
    CycleQ2SmoothImmersionStalkEquations.stalk_kernel_generators p q i
      hi x 4 2 (i.stalkMap_surjective x)
  obtain ⟨d,hzW,b,hb⟩ :=
    CycleQ2ClosedImmersionAffineEquations.exists_affine_equations i ⟨U,hU⟩ x hzU s hs'
  let W := Y.affineBasicOpen d
  have hfin : (Set.range b) = {b 0,b 1} := by
    ext y
    constructor
    · rintro ⟨n,rfl⟩
      fin_cases n <;> simp
    · rintro (h | h)
      · exact ⟨0,h.symm⟩
      · exact ⟨1,(Set.mem_singleton_iff.mp h).symm⟩
  refine ⟨W,b 0,b 1,hzW,(Y.basicOpen_le d).trans hUN,
    hasFrame_of_affine_le q 4 (Y.basicOpen_le d) hU W.2 hframe,?_⟩
  rwa [← hfin]

structure Chart where
  U : Y.affineOpens
  f : Γ(Y,U.1)
  g : Γ(Y,U.1)
  frame : HasFrame q 4 U.1
  equations : Ideal.span {f,g} = i.ker.ideal U

abbrev chartClass (A : Chart q i) :=
  classOf i A.f A.g q 4
    (locus_of_span _ A.U A.f A.g A.equations) (pairFrame _ A.U A.frame A.f A.g)

omit [CharZero k] in
include hi in
theorem adapted_chart
    (A : Chart q i) (x : X)
    (hx : i x ∈ A.U.1) :
    ∃ (T : Y.affineOpens) (e : T.1 ≤ A.U.1),
      i x ∈ T.1 ∧
      ∃ w : Fin 4 → Γ(Y,T.1),
        ExactOnOpen q w ∧
        w 0 = Y.presheaf.map (homOfLE e).op A.f ∧
        w 1 = Y.presheaf.map (homOfLE e).op A.g := by
  let : SmoothOfRelativeDimension (2+2) q := inferInstance
  let ρ := (Y.presheaf.germ A.U.1 (i x) hx).hom
  let f : Fin 2 → Y.presheaf.stalk (i x) := ![ρ A.f,ρ A.g]
  obtain ⟨u,b,_,hb,_⟩ := CycleQ2NormalTangentFrame.stalk_basis p q i
    hi (n := 2) (m := 2) x f
    (CycleQ2AffineEquationGerms.span_pair i A.U x hx A.f A.g A.equations)
  let ur := Fin.append f u
  have hu0 : ur 0 = ρ A.f := (Fin.append_left f u (0 : Fin 2)).trans rfl
  have hu1 : ur 1 = ρ A.g := (Fin.append_left f u (1 : Fin 2)).trans rfl
  obtain ⟨T,e,hT,w,hw,_,hf,hg⟩ :=
    CycleQ2AdaptedAffineFrame.exists_pair_frame q A.U (i x) hx A.frame A.f A.g ur
      hu0 hu1 ⟨b,hb⟩
  exact ⟨T,e,hT,w,hw,hf,hg⟩

set_option quotPrecheck false
local notation "Ch" => Chart q i
local notation "Ω" => (DerivedCategory.Q.obj (relativeDeRhamInt q 4) : DerivedCategory.{1} (AbSheaf (show TopCat from Y)))
local notation "E" => DerivedCategory.singleFunctor (AbSheaf (show TopCat from Y)) 0
local notation "res" => CycleQ2NoetherianSupport.res
local instance derived (T : TopCat.{0}) : HasDerivedCategory.{1} (AbSheaf T) := HasDerivedCategory.standard _

def atlasOpen : Option Ch → Y.Opens
  | none => complement i
  | some A => A.U.1

def atlasClass (n : Option Ch) :
    (E).obj (support i (atlasOpen q i n)) ⟶ Ω⟦(4:ℤ)⟧ := by
  cases n with
  | none =>
    exact (0 : (DerivedCategory.singleFunctor (AbSheaf (show TopCat from Y)) 0).obj
      (support i (complement i)) ⟶ (DerivedCategory.Q.obj (relativeDeRhamInt q 4))⟦(4:ℤ)⟧)
  | some A => exact chartClass q i A

omit [CharZero k] in
include hi in
theorem atlas_cover :
    (⨆ n, atlasOpen q i n) = ⊤ := by
  apply top_unique
  intro y _
  by_cases h : y ∈ Set.range i
  · obtain ⟨x,rfl⟩ := h
    obtain ⟨U,f,g,hx,_,hf,he⟩ := exists_chart p q i hi x ⊤ (by trivial)
    exact Opens.mem_iSup.mpr ⟨some ⟨U,f,g,hf,he⟩,hx⟩
  · exact Opens.mem_iSup.mpr ⟨none,h⟩

include hi in
theorem atlas_agreement
    (m n : Option Ch) (y : Y)
    (hm : y ∈ atlasOpen q i m) (hn : y ∈ atlasOpen q i n) :
    ∃ (W : Y.Opens) (e : W ≤ atlasOpen q i m)
      (d : W ≤ atlasOpen q i n), y ∈ W ∧
      res (complement i) e (atlasClass q i m) =
      res (complement i) d (atlasClass q i n) := by
  cases m with
  | none =>
    refine ⟨_ ⊓ _,inf_le_left,inf_le_right,⟨hm,hn⟩,?_⟩
    exact ((E).map_isZero (CycleQ2SmoothTwoChartAgreement.isZero_support_off_graph i _ inf_le_left)).eq_of_src _ _
  | some A =>
    cases n with
    | none =>
      refine ⟨_ ⊓ _,inf_le_left,inf_le_right,⟨hm,hn⟩,?_⟩
      exact ((E).map_isZero (CycleQ2SmoothTwoChartAgreement.isZero_support_off_graph i _ inf_le_right)).eq_of_src _ _
    | some B =>
      obtain ⟨T,e,d,h,hEq⟩ := CycleQ2SmoothTwoChartAgreement.exists_agreement_at_ambient_point
        p q i hi
        A.U B.U y hm hn A.f A.g B.f B.g A.equations B.equations
        (pairFrame _ _ A.frame _ _) (pairFrame _ _ B.frame _ _)
      exact ⟨T.1,e,d,h,hEq⟩

include hi in
theorem exists_global [Algebra ℂ k] [NoetherianSpace Y] :
    ∃ z : (E).obj (support i ⊤) ⟶ Ω⟦(4:ℤ)⟧, ∀ n,
      res (complement i) (show atlasOpen q i n ≤ ⊤ from le_top) z = atlasClass q i n := by
  refine CycleQ2SupportPurityDescent.glue_four q 4 (complement i) ?_ (atlasOpen q i)
    (atlasClass q i) (fun y => Opens.mem_iSup.mp (by rw [atlas_cover p q i hi]; trivial))
    (atlas_agreement p q i hi)
  intro n hn W z y hy
  by_cases hy' : y ∈ Set.range i
  · obtain ⟨x,rfl⟩ := hy'
    obtain ⟨U,f,g,hxU,hUW,hfr,hspan⟩ := exists_chart p q i hi x W hy
    let A : Chart q i := ⟨U,f,g,hfr,hspan⟩
    obtain ⟨T,e,hxT,w,hw,hf,hg⟩ := adapted_chart p q i hi A x hxU
    let F : CycleQ2IntrinsicFramedAffineSite.FramedOpen q 4 := ⟨T.1,T.2,⟨w,hw⟩⟩
    let : Smooth q := SmoothOfRelativeDimension.smooth 4 q
    let : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian q
    let : IsNoetherianRing Γ(Y,T.1) := IsLocallyNoetherian.component_noetherian T
    have hzero := CycleQ2AdaptedChartPurity.below_four q F w hw (n:ℤ) (by omega)
    have hl : CycleQ2LocalPrincipalGysin.locus (w 0) (w 1) =
        (T.1 : Set Y) ∩ Set.range i := by
      rw [hf,hg]
      exact CycleQ2ClosedGraphRestriction.locus_restrict i e A.f A.g
        (CycleQ2SmoothTwoChartAgreement.locus_of_span i U A.f A.g A.equations)
    have he := CycleQ2ClosedGraphSupport.union_eq_complement i (w 0) (w 1) hl
    have hQ {V' W' T' : Y.Opens} (h : V' = W') (v : V' ≤ T') (w' : W' ≤ T') :
        CycleQ2RelativeOpenSupport.quotient v = CycleQ2RelativeOpenSupport.quotient w' := by
      subst W'
      rfl
    have hsrc : support i T.1 = CycleQ2LocalPrincipalGysin.supportedQuotient (w 0) (w 1) :=
      hQ he.symm _ _
    have hsmall : Subsingleton ((E).obj (support i T.1) ⟶ Ω⟦(n:ℤ)⟧) := by
      rw [hsrc]
      exact hzero
    exact ⟨T.1,e.trans hUW,hxT,hsmall.allEq _ _⟩
  · refine ⟨W ⊓ complement i,inf_le_left,⟨hy,hy'⟩,?_⟩
    exact ((E).map_isZero
      (CycleQ2SmoothTwoChartAgreement.isZero_support_off_graph i _ inf_le_right)).eq_of_src _ _

end CycleQ2SmoothSurfaceGysin

#print axioms CycleQ2SmoothSurfaceGysin.exists_global
