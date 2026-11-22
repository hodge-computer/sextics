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

/-! Exact normal coordinates for a smooth open part of a closed subscheme.
The equations remain equations of the original closed immersion; neither
its complement nor the ambient de Rham complex is replaced by a model. -/

namespace CycleQ2SmoothMarkedNormalCharts

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open Algebra Module KaehlerDifferential
open CycleQ2SmoothStalkFrames (coefficientAlg exists_exact_frame)
open CycleQ2SmoothImmersionStalkEquations (stalkAlgHom)
open CycleQ2FiniteExactAffineAtlas (HasFrame hasFrame_of_affine_le)
open CycleQ2AdaptedAffineFrame (ExactOnOpen)

variable {k : Type} [Field k] {M Z Y : Scheme.{0}}
  (q : Y ⟶ Spec (CommRingCat.of k)) (e : Z ⟶ Y) [IsClosedImmersion e]
  (j : M ⟶ Z) [IsOpenImmersion j]

private theorem stalk_surjective (x : M) : Function.Surjective ((j ≫ e).stalkMap x) := by
  rw [Scheme.Hom.stalkMap_comp]
  exact (ConcreteCategory.bijective_of_isIso (j.stalkMap x)).surjective.comp
    (e.stalkMap_surjective (j x))

private theorem stalk_kernel (x : M) :
    RingHom.ker ((j ≫ e).stalkMap x).hom = RingHom.ker (e.stalkMap (j x)).hom := by
  rw [Scheme.Hom.stalkMap_comp,CommRingCat.hom_comp,RingHom.ker_comp_of_injective]
  exact (ConcreteCategory.bijective_of_isIso (j.stalkMap x)).injective

private theorem germ_span (U : Y.affineOpens) (x : Z) (hx : e x ∈ U.1)
    {n : ℕ} (a : Fin n → Γ(Y,U.1))
    (ha : Ideal.span (Set.range a) = e.ker.ideal U) :
    Ideal.span (Set.range (fun l => Y.presheaf.germ U.1 (e x) hx (a l))) =
      RingHom.ker (e.stalkMap x).hom := by
  rw [← CycleQ2ClosedImmersionStalkIdeal.map_kernel e U.1 U.2 x hx,
    ← e.ker_apply U,← ha,Ideal.map_span,← Set.range_comp]

variable (n m : ℕ) [SmoothOfRelativeDimension (n+m) q]
  [SmoothOfRelativeDimension m (j ≫ e ≫ q)]

private theorem normal_stalk_basis (x : M)
    (f : Fin n → Y.presheaf.stalk (e (j x)))
    (hf : Ideal.span (Set.range f) = RingHom.ker (e.stalkMap (j x)).hom) :
    letI := coefficientAlg q (e (j x))
    ∃ (u : Fin m → Y.presheaf.stalk (e (j x)))
      (b : Basis (Fin (n+m)) (Y.presheaf.stalk (e (j x)))
        Ω[Y.presheaf.stalk (e (j x))⁄k]),
      ∀ l, b l = D k _ (Fin.append f u l) := by
  let p := j ≫ e ≫ q
  let i := j ≫ e
  letI := coefficientAlg q (i x)
  letI := coefficientAlg p x
  let φ := stalkAlgHom p q i (Category.assoc j e q) x
  letI : Algebra (Y.presheaf.stalk (i x)) (M.presheaf.stalk x) := φ.toAlgebra
  let : IsLocalHom (algebraMap (Y.presheaf.stalk (i x)) (M.presheaf.stalk x)) :=
    inferInstanceAs (IsLocalHom (i.stalkMap x).hom)
  obtain ⟨_,b,_⟩ := exists_exact_frame q (i x) (n+m)
  obtain ⟨v,c,hv⟩ := exists_exact_frame p x m
  choose u hu using fun l => stalk_surjective e j x (v l)
  have hc (l : Fin m) : c l = D k _ (φ (u l)) := by
    rw [hv]
    exact congrArg (D k _) (hu l).symm
  have hf' : Ideal.span (Set.range f) = RingHom.ker φ.toRingHom :=
    hf.trans (stalk_kernel e j x).symm
  obtain ⟨b',hb'⟩ := CycleQ2FrameLifting.basis_of_baseChange_span
    (B := M.presheaf.stalk x) b (fun l => D k _ (Fin.append f u l))
    (CycleQ2NormalTangentFrame.span_after_restriction φ
      (stalk_surjective e j x) f hf' u c hc)
  exact ⟨u,b',hb'⟩

/-- Near a smooth marked point, all normal equations of the original
closed immersion are the first coordinates of an exact ambient frame. -/
theorem exists_adapted_chart (x : M) (N : Y.Opens) (hx : e (j x) ∈ N) :
    ∃ (U : Y.affineOpens), e (j x) ∈ U.1 ∧ U.1 ≤ N ∧
      ∃ u : Fin (n+m) → Γ(Y,U.1), ExactOnOpen q u ∧
        Ideal.span (Set.range (fun l : Fin n => u (Fin.castAdd m l))) = e.ker.ideal U := by
  let : Smooth q := SmoothOfRelativeDimension.smooth (n+m) q
  let : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian q
  obtain ⟨U,⟨hU,hframe⟩,hxU,hUN⟩ :=
    (Opens.isBasis_iff_nbhd.mp (CycleQ2FiniteExactAffineAtlas.isBasis q (n+m))) hx
  have hs : ∃ f : Fin n → Y.presheaf.stalk (e (j x)),
      Ideal.span (Set.range f) = RingHom.ker ((j ≫ e).stalkMap x).hom := by
    simpa only [Nat.add_sub_cancel] using
      CycleQ2SmoothImmersionStalkEquations.stalk_kernel_generators
        (j ≫ e ≫ q) q (j ≫ e) (Category.assoc j e q) x (n+m) m
        (stalk_surjective e j x)
  obtain ⟨f,hf⟩ := hs
  rw [stalk_kernel e j x] at hf
  obtain ⟨d,hxA,a,ha⟩ :=
    CycleQ2ClosedImmersionAffineEquations.exists_affine_equations
      e ⟨U,hU⟩ (j x) hxU f hf
  let A := Y.affineBasicOpen d
  have hA : HasFrame q (n+m) A.1 :=
    hasFrame_of_affine_le q (n+m) (Y.basicOpen_le d) hU A.2 hframe
  let ρ := (Y.presheaf.germ A.1 (e (j x)) hxA).hom
  obtain ⟨v,b,hb⟩ := normal_stalk_basis q e j n m x (ρ ∘ a)
    (germ_span e A (j x) hxA a ha)
  let ur := Fin.append (ρ ∘ a) v
  let fixed : Fin (n+m) → Γ(Y,A.1) := Fin.append a (fun _ : Fin m => 0)
  let active : Set (Fin (n+m)) := Set.range (Fin.castAdd m : Fin n → Fin (n+m))
  have hagree : ∀ l ∈ active, Y.presheaf.germ A.1 (e (j x)) hxA (fixed l) = ur l := by
    rintro l ⟨t,rfl⟩
    simp only [fixed,ur,Fin.append_left,Function.comp_apply]
  obtain ⟨T,h,hxT,w,hw,_,hfixed⟩ :=
    CycleQ2AdaptedAffineFrame.exists_prescribed_frame q A (e (j x)) hxA hA
      ur fixed active hagree ⟨b,hb⟩
  refine ⟨T,hxT,h.trans ((Y.basicOpen_le d).trans hUN),w,hw,?_⟩
  have hnormal : (fun l : Fin n => w (Fin.castAdd m l)) =
      fun l => Y.presheaf.map (homOfLE h).op (a l) := by
    funext l
    simpa only [fixed,Fin.append_left] using hfixed (Fin.castAdd m l) ⟨l,rfl⟩
  rw [hnormal,← e.ker.map_ideal (U := T) (V := A) h,← ha,
    Ideal.map_span,← Set.range_comp]

end CycleQ2SmoothMarkedNormalCharts

namespace CycleQ2ThreeNormalSupportPurity

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open CycleQ2InjectiveCech (AbSheaf)
open CycleQ2SupportMV (M)
open CycleQ2NoetherianSupport (res)
open CycleQ2AdaptedAffineFrame (ExactOnOpen)
open CycleQ2IntrinsicDeRhamSheaves (relativeDeRhamInt)
open CycleQ2IntrinsicFramedAffineSite (FramedOpen)

variable {k : Type} [Field k] [CharZero k] [Algebra ℂ k] {X : Scheme.{0}}
  (p : X ⟶ Spec (CommRingCat.of k)) (r : ℕ) [SmoothOfRelativeDimension r p]

local instance : HasDerivedCategory.{1} (AbSheaf (show TopCat from X)) :=
  HasDerivedCategory.standard _

private abbrev E := DerivedCategory.singleFunctor (AbSheaf (show TopCat from X)) 0
private abbrev K : DerivedCategory.{1} (AbSheaf (show TopCat from X)) :=
  DerivedCategory.Q.obj (relativeDeRhamInt p r)

def normalOpen (U : X.affineOpens) (u : Fin r → Γ(X,U.1))
    (normal : Fin 3 → Fin r) : X.Opens :=
  (X.basicOpen (u (normal 0)) ⊔ X.basicOpen (u (normal 1))) ⊔ X.basicOpen (u (normal 2))

theorem normalOpen_le (U : X.affineOpens) (u : Fin r → Γ(X,U.1))
    (normal : Fin 3 → Fin r) : normalOpen r U u normal ≤ U.1 :=
  sup_le (sup_le (X.basicOpen_le _) (X.basicOpen_le _)) (X.basicOpen_le _)

private theorem quotient_congr {A B W : X.Opens} (h : A = B) (a : A ≤ W) (b : B ≤ W) :
    CycleQ2RelativeOpenSupport.quotient a = CycleQ2RelativeOpenSupport.quotient b := by
  subst B
  rfl

private theorem normalOpen_restrict {U V : X.affineOpens} (h : V.1 ≤ U.1)
    (u : Fin r → Γ(X,U.1)) (normal : Fin 3 → Fin r) :
    normalOpen r V (fun l => X.presheaf.map (homOfLE h).op (u l)) normal =
      V.1 ⊓ normalOpen r U u normal := by
  unfold normalOpen
  rw [X.basicOpen_res,X.basicOpen_res,X.basicOpen_res,← inf_sup_left,← inf_sup_left]

/-- The exact coordinates and their actual basic opens survive every
affine refinement, with support still measured in the original ambient complex. -/
theorem affine_below_six (U : X.affineOpens) (u : Fin r → Γ(X,U.1))
    (hu : ExactOnOpen p u) (normal : Fin 3 → Fin r) (hnormal : Function.Injective normal)
    (V : X.affineOpens) (h : V.1 ≤ U.1) (n : ℤ) (hn : n < 6) :
    Subsingleton (E.obj (M (normalOpen r U u normal) V.1) ⟶ (K p r)⟦n⟧) := by
  let v : Fin r → Γ(X,V.1) := fun l => X.presheaf.map (homOfLE h).op (u l)
  have hv : ExactOnOpen p v := by
    obtain ⟨b,hb⟩ := hu
    exact CycleQ2RelativeAffineOverlap.exact_on_affine_subopen p h U.2 V.2 u b hb
  let F : FramedOpen p r := ⟨V.1,V.2,⟨v,hv⟩⟩
  let : Smooth p := SmoothOfRelativeDimension.smooth r p
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  let : IsNoetherianRing Γ(X,V.1) := IsLocallyNoetherian.component_noetherian V
  have hz := CycleQ2AdaptedTripleChartPurity.below_six_of_exact_coordinates
    p r F v normal hnormal hv n hn
  have hC : CycleQ2FramedTripleCechFormRow.unionOpen p r F (v ∘ normal) =
      V.1 ⊓ normalOpen r U u normal := normalOpen_restrict r h u normal
  have hsrc : M (normalOpen r U u normal) V.1 =
      CycleQ2FramedTripleCechFormRow.supportedQuotient p r F (v ∘ normal) :=
    quotient_congr hC.symm _ _
  rw [hsrc]
  exact hz

variable [NoetherianSpace X]

/-- Three exact normal coordinates give vanishing below six on every
subopen of their affine chart, including nonaffine complements of smaller supports. -/
theorem below_six_on_chart (U : X.affineOpens) (u : Fin r → Γ(X,U.1))
    (hu : ExactOnOpen p u) (normal : Fin 3 → Fin r) (hnormal : Function.Injective normal)
    (W : X.Opens) (hW : W ≤ U.1) (n : ℤ) (hn : n < 6) :
    Subsingleton (E.obj (M (normalOpen r U u normal) W) ⟶ (K p r)⟦n⟧) := by
  apply subsingleton_of_forall_eq 0
  intro a
  cases n with
  | negSucc n => exact CycleQ2DeRhamNegative.eq_zero p r _ _ (by omega) a
  | ofNat n =>
    refine CycleQ2SupportPurityDescent.vanish_on p r (normalOpen r U u normal) U.1 n ?_ W hW a
    intro t ht V hV b x hx
    obtain ⟨T,hT,hxT,hTV⟩ := (Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens) hx
    have hz := affine_below_six p r U u hu normal hnormal ⟨T,hT⟩ (hTV.trans hV)
      (t:ℤ) (by omega)
    exact ⟨T,hTV,hxT,hz.allEq _ _⟩

/-- Any smaller closed support inside the three-coordinate locus has
the same low-degree vanishing. The residual-support sequence is the
actual sequence of free-open quotients in the ambient space. -/
theorem residual_below_six (U : X.affineOpens) (u : Fin r → Γ(X,U.1))
    (hu : ExactOnOpen p u) (normal : Fin 3 → Fin r) (hnormal : Function.Injective normal)
    (V : X.Opens) (hV : V ≤ U.1) (hC : normalOpen r U u normal ≤ V)
    (n : ℤ) (hn : n < 6) :
    Subsingleton (E.obj (M V U.1) ⟶ (K p r)⟦n⟧) :=
  CycleQ2SupportFiltration.residual_vanishing_of_le (normalOpen r U u normal) hV hC
    (K p r) n
    (fun a => (below_six_on_chart p r U u hu normal hnormal U.1 le_rfl n hn).allEq a 0)
    (fun a => (below_six_on_chart p r U u hu normal hnormal V hV (n-1) (by omega)).allEq a 0)

end CycleQ2ThreeNormalSupportPurity

namespace CycleQ2SmoothSmallSupport

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open CycleQ2InjectiveCech (AbSheaf)
open CycleQ2ClosedGraphSupport (complement support)
open CycleQ2AdaptedAffineFrame (ExactOnOpen)
open CycleQ2IntrinsicDeRhamSheaves (relativeDeRhamInt)
open CycleQ2ThreeNormalSupportPurity (normalOpen)
open CycleQ2NoetherianSupport (res)

variable {k : Type} [Field k] {M Z Y : Scheme.{0}}
  (q : Y ⟶ Spec (CommRingCat.of k)) (e : Z ⟶ Y) [IsClosedImmersion e]
  (j : M ⟶ Z) [IsOpenImmersion j]
  [SmoothOfRelativeDimension 4 q]

private theorem basicOpen_le_complement (U : Y.affineOpens) (f : Γ(Y,U.1))
    (hf : f ∈ e.ker.ideal U) : Y.basicOpen f ≤ U.1 ⊓ complement e := by
  have hzero : (U.1 : Set Y) ∩ Y.zeroLocus (e.ker.ideal U : Set Γ(Y,U.1)) =
      (U.1 : Set Y) ∩ Set.range e := by
    rw [Set.inter_comm (U.1 : Set Y),← e.ker.coe_support_inter U,e.support_ker,
      e.isClosedEmbedding.isClosed_range.closure_eq,Set.inter_comm]
  intro y hy
  have hyU := Y.basicOpen_le f hy
  refine ⟨hyU,?_⟩
  intro hye
  have hz := ((Set.ext_iff.mp hzero y).mpr ⟨hyU,hye⟩).2
  rw [Scheme.mem_zeroLocus_iff] at hz
  exact hz f hf hy

/-- The first three members of an adapted normal frame vanish on the
original closed subscheme, including any remaining singular part. -/
theorem normalOpen_le_complement (U : Y.affineOpens) (u : Fin 4 → Γ(Y,U.1))
    (hu : ∀ l : Fin 3, u (Fin.castAdd 1 l) ∈ e.ker.ideal U) :
    normalOpen 4 U u (Fin.castAdd 1) ≤ U.1 ⊓ complement e :=
  sup_le (sup_le (basicOpen_le_complement e U _ (hu 0))
    (basicOpen_le_complement e U _ (hu 1))) (basicOpen_le_complement e U _ (hu 2))

variable (m : ℕ) [SmoothOfRelativeDimension m (j ≫ e ≫ q)]

/-- Smooth curves and smooth zero-dimensional marked pieces both
provide three distinct exact normal coordinates in the same fourfold. -/
theorem exists_three_normal_chart (hm : m ≤ 1) (x : M) (N : Y.Opens)
    (hx : e (j x) ∈ N) :
    ∃ (U : Y.affineOpens), e (j x) ∈ U.1 ∧ U.1 ≤ N ∧
      ∃ u : Fin 4 → Γ(Y,U.1), ExactOnOpen q u ∧
        ∀ l : Fin 3, u (Fin.castAdd 1 l) ∈ e.ker.ideal U := by
  have hcases : m = 0 ∨ m = 1 := by omega
  rcases hcases with rfl | rfl
  · obtain ⟨U,hxU,hUN,u,hu,hspan⟩ :=
      CycleQ2SmoothMarkedNormalCharts.exists_adapted_chart q e j 4 0 x N hx
    refine ⟨U,hxU,hUN,u,hu,?_⟩
    intro l
    rw [← hspan]
    exact Ideal.subset_span ⟨Fin.castAdd 1 l,rfl⟩
  · obtain ⟨U,hxU,hUN,u,hu,hspan⟩ :=
      CycleQ2SmoothMarkedNormalCharts.exists_adapted_chart q e j 3 1 x N hx
    refine ⟨U,hxU,hUN,u,hu,?_⟩
    intro l
    rw [← hspan]
    exact Ideal.subset_span ⟨l,rfl⟩

variable [CharZero k] [Algebra ℂ k] [NoetherianSpace Y]

local instance : HasDerivedCategory.{1} (AbSheaf (show TopCat from Y)) :=
  HasDerivedCategory.standard _

private abbrev E := DerivedCategory.singleFunctor (AbSheaf (show TopCat from Y)) 0
private abbrev K : DerivedCategory.{1} (AbSheaf (show TopCat from Y)) :=
  DerivedCategory.Q.obj (relativeDeRhamInt q 4)

/-- Low-degree purity near a marked smooth curve or point. Only the
marked source is smooth; the support is still the actual closed immersion. -/
theorem locally_below_six (hm : m ≤ 1) (x : M) (N : Y.Opens)
    (hx : e (j x) ∈ N) (n : ℤ) (hn : n < 6) :
    ∃ (U : Y.affineOpens), e (j x) ∈ U.1 ∧ U.1 ≤ N ∧
      Subsingleton (E.obj (support e U.1) ⟶ (K q)⟦n⟧) := by
  obtain ⟨U,hxU,hUN,u,hu,hI⟩ := exists_three_normal_chart q e j m hm x N hx
  have hnormal : Function.Injective (Fin.castAdd 1 : Fin 3 → Fin 4) := by
    intro a b h
    exact Fin.ext (congrArg Fin.val h)
  have hz := CycleQ2ThreeNormalSupportPurity.residual_below_six q 4 U u hu
    (Fin.castAdd 1) hnormal (U.1 ⊓ complement e) inf_le_left
    (normalOpen_le_complement e U u hI) n hn
  refine ⟨U,hxU,hUN,?_⟩
  simpa only [CycleQ2SupportMV.M,CycleQ2ClosedGraphSupport.support,← inf_assoc,inf_idem] using hz

/-- On an open meeting the closed support only in its marked smooth
part of dimension at most one, the original supported de Rham groups
vanish in every degree below six. All restrictions stay in the original
ambient fourfold and its intrinsic relative de Rham complex. -/
theorem below_six_on (hm : m ≤ 1) (O : Y.Opens)
    (hO : ∀ z : Z, e z ∈ O → z ∈ Set.range j)
    (W : Y.Opens) (hW : W ≤ O) (n : ℤ) (hn : n < 6) :
    Subsingleton (E.obj (support e W) ⟶ (K q)⟦n⟧) := by
  apply subsingleton_of_forall_eq 0
  intro a
  cases n with
  | negSucc n => exact CycleQ2DeRhamNegative.eq_zero q 4 _ _ (by omega) a
  | ofNat n =>
    refine CycleQ2SupportPurityDescent.vanish_on q 4 (complement e) O n ?_ W hW a
    intro t ht V hV b y hy
    by_cases hye : y ∈ Set.range e
    · obtain ⟨z,rfl⟩ := hye
      obtain ⟨x,rfl⟩ := hO z (hV hy)
      obtain ⟨T,hxT,hTV,hz⟩ := locally_below_six q e j m hm x V hy (t:ℤ) (by omega)
      exact ⟨T.1,hTV,hxT,hz.allEq _ _⟩
    · refine ⟨V ⊓ complement e,inf_le_left,⟨hy,hye⟩,?_⟩
      exact (E.map_isZero
        (CycleQ2SmoothTwoChartAgreement.isZero_support_off_graph e _ inf_le_right)).eq_of_src _ _

end CycleQ2SmoothSmallSupport

#print axioms CycleQ2SmoothMarkedNormalCharts.exists_adapted_chart
#print axioms CycleQ2ThreeNormalSupportPurity.below_six_on_chart
#print axioms CycleQ2SmoothSmallSupport.below_six_on
