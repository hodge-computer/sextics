import Proposal.GeometricMonicGenericSupport

/-! Restrictions, units, and changes of order for local logarithmic graph classes in the derived category.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false

noncomputable section

namespace CycleQ2ClosedGraphSupport

open CategoryTheory AlgebraicGeometry TopologicalSpace
open CycleQ2InjectiveCech (AbSheaf)
open CycleQ2RelativeOpenSupport (quotient)
open CycleQ2LocalPrincipalGysin (cover locus supportedQuotient localClass)
open CycleQ2PrincipalLogSupportClass (support_eq_zeroLocus)
open CycleQ2FiniteExactAffineAtlas (HasFrame)
open CycleQ2IntrinsicDeRhamSheaves (relativeDeRhamInt)

variable {Z X : Scheme.{0}} (i : Z ⟶ X) [IsClosedImmersion i]

/-- The actual open complement of a closed immersion. -/
def complement : X.Opens :=
  ⟨(Set.range i)ᶜ, i.isClosedEmbedding.isClosed_range.isOpen_compl⟩

abbrev support (W : X.Opens) :=
  quotient (show W ⊓ complement i ≤ W from inf_le_left)

variable {W : X.Opens} (f g : Γ(X,W))

theorem union_eq_complement
    (he : locus f g = (W : Set X) ∩ Set.range i) :
    (cover f g).X₄ = W ⊓ complement i := by
  ext x
  by_cases hx : x ∈ W
  · have hh := Set.ext_iff.mp he x
    change x ∈ W ∧ x ∈ X.zeroLocus {f,g} ↔ x ∈ W ∧ x ∈ Set.range i at hh
    rw [← support_eq_zeroLocus f g] at hh
    change x ∈ (cover f g).X₄ ↔ x ∈ W ∧ x ∉ Set.range i
    exact ⟨fun h ↦ ⟨hx,fun hg ↦ (hh.mpr ⟨hx,hg⟩).2 h⟩,
      fun h ↦ not_not.mp (fun hn ↦ h.2 (hh.mp ⟨hx,hn⟩).2)⟩
  · exact ⟨fun h ↦ (hx (CycleQ2LocalPrincipalGysin.union_le f g h)).elim,
      fun h ↦ (hx h.1).elim⟩

/-- The original local logarithmic class has the graph-relative source. -/
def classOf {k : Type} [Field k] [CharZero k] (p : X ⟶ Spec (CommRingCat.of k)) (r : ℕ)
    [SmoothOfRelativeDimension r p]
    (he : locus f g = (W : Set X) ∩ Set.range i)
    (h : IsAffineOpen (cover f g).X₁ ∧ HasFrame p r (cover f g).X₁) :
    letI : HasDerivedCategory.{1} (AbSheaf (show TopCat from X)) := HasDerivedCategory.standard _
    (DerivedCategory.singleFunctor (AbSheaf (show TopCat from X)) 0).obj (support i W) ⟶
      (DerivedCategory.Q.obj (relativeDeRhamInt p r))⟦(4:ℤ)⟧ := by
  letI : HasDerivedCategory.{1} (AbSheaf (show TopCat from X)) := HasDerivedCategory.standard _
  let hu := union_eq_complement i f g he
  exact (DerivedCategory.singleFunctor _ 0).map
    (CycleQ2RelativeSupportRefinement.supportMap
      (show W ⊓ complement i ≤ W from inf_le_left)
      (CycleQ2LocalPrincipalGysin.union_le f g) hu.ge le_rfl).τ₃ ≫ localClass p r f g h

end CycleQ2ClosedGraphSupport

namespace CycleQ2RelativeSupportComparison

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open CycleQ2InjectiveCech (AbSheaf freeOpenMap freeOpenSections freeOpenSections_naturality)
open CycleQ2MayerVietorisRestriction (freeOpenSheaf shortComplexMap)
open CycleQ2DerivedDoubleSupport (ofClosedSection sectionMap sectionMap_closed)
open CycleQ2DerivedSupportNaturality (connecting_natural)
open CycleQ2RelativeOpenSupport (shortExact relativeOfSection)
open CycleQ2RelativeSupportRefinement (supportMap)
open CycleQ2SupportedOpenRefinement (restrict_closed)

variable {X : TopCat.{0}} {K : CochainComplex (AbSheaf X) ℤ} (q : ℤ)
local instance : HasExt.{1} (AbSheaf X) := HasExt.standard _
local instance : HasDerivedCategory.{1} (AbSheaf X) := HasDerivedCategory.standard _

private abbrev E := DerivedCategory.singleFunctor (AbSheaf X) 0
private abbrev P := (K⟦q⟧).X 0
private abbrev d := (K⟦q⟧).d 0 1
abbrev cover (U V : Opens X) := Opens.mayerVietorisSquare U V

theorem relative_eq_comp {W : Opens X} (S : (Opens.grothendieckTopology X).MayerVietorisSquare)
    (h : S.X₄ ≤ W) (z : (P (K := K) q).obj.obj (op S.X₁))
    (hz : (d (K := K) q).hom.app (op S.X₁) z = 0) :
    relativeOfSection q S h z hz =
      (E (X := X)).map (supportMap h (show S.X₄ ≤ ⊤ from le_top) le_rfl le_top).τ₃ ≫
        ofClosedSection q S z hz := by
  have hm : freeOpenMap (show S.X₄ ≤ S.X₄ from le_rfl) = 𝟙 _ :=
    (freeOpenSheaf (X := X)).map_id S.X₄
  let hTop : S.X₄ ≤ (⊤ : Opens X) := le_top
  let m := supportMap h hTop le_rfl le_top
  let F := shiftFunctor (DerivedCategory (AbSheaf X)) (1 : ℤ)
  have he : (shortExact h).extClass.hom ≫
      F.map ((E (X := X)).map (freeOpenMap (show S.X₄ ≤ S.X₄ from le_rfl))) =
      (E (X := X)).map m.τ₃ ≫ (shortExact hTop).extClass.hom :=
    connecting_natural (shortExact h) (shortExact hTop) m
  have hF : F.map ((E (X := X)).map (freeOpenMap (show S.X₄ ≤ S.X₄ from le_rfl))) =
      𝟙 ((F.obj ((E (X := X)).obj (CycleQ2InjectiveCech.freeOpen S.X₄)))) := by
    rw [hm,(E (X := X)).map_id,F.map_id]
  have hh : (shortExact h).extClass.hom = (E (X := X)).map m.τ₃ ≫ (shortExact hTop).extClass.hom :=
    (Category.comp_id _).symm.trans ((congrArg (fun v ↦ (shortExact h).extClass.hom ≫ v) hF.symm).trans he)
  let b := CycleQ2DerivedOverlapClass.overlapClass q S (sectionMap q S z) (sectionMap_closed q S z hz)
  let J := (shiftFunctorAdd (DerivedCategory (AbSheaf X)) (q+1) 1).inv.app (DerivedCategory.Q.obj K)
  change (shortExact h).extClass.hom ≫ F.map b ≫ J =
    (E (X := X)).map m.τ₃ ≫ (shortExact hTop).extClass.hom ≫ F.map b ≫ J
  calc
    _ = ((E (X := X)).map m.τ₃ ≫ (shortExact hTop).extClass.hom) ≫ F.map b ≫ J :=
      congrArg (fun u ↦ u ≫ F.map b ≫ J) hh
    _ = _ := Category.assoc _ _ _

theorem eq_of_second_restriction {W : Opens X} (S : (Opens.grothendieckTopology X).MayerVietorisSquare)
    (h : S.X₄ ≤ W) (a b : (P (K := K) q).obj.obj (op S.X₁))
    (ha : (d (K := K) q).hom.app (op S.X₁) a = 0)
    (hb : (d (K := K) q).hom.app (op S.X₁) b = 0)
    (w : (P (K := K) q).obj.obj (op S.X₃))
    (hw : (d (K := K) q).hom.app (op S.X₃) w = 0)
    (he : b = a + (P (K := K) q).obj.map S.f₁₃.op w) :
    relativeOfSection q S h b hb = relativeOfSection q S h a ha := by
  rw [relative_eq_comp,relative_eq_comp,
    CycleQ2SupportedChartBoundary.class_eq_of_second_restriction q S a b ha hb w hw he]

theorem pullback_class {U' V' U V W' W : Opens X} (hU : U' ≤ U) (hV : V' ≤ V)
    (h' : U' ⊔ V' ≤ W') (h : U ⊔ V ≤ W) (hW : W' ≤ W)
    (z : (P (K := K) q).obj.obj (op (U ⊓ V)))
    (hz : (d (K := K) q).hom.app (op (U ⊓ V)) z = 0) :
    (E (X := X)).map (supportMap h' h (sup_le_sup hU hV) hW).τ₃ ≫
      relativeOfSection q (cover U V) h z hz =
    relativeOfSection q (cover U' V') h'
      ((P (K := K) q).obj.map (homOfLE (inf_le_inf hU hV)).op z)
      (restrict_closed q (inf_le_inf hU hV) z hz) := by
  let m := shortComplexMap hU hV
  let zMap := sectionMap q (cover U V) z
  let z' := (P (K := K) q).obj.map (homOfLE (inf_le_inf hU hV)).op z
  have hs : m.τ₁ ≫ zMap = sectionMap q (cover U' V') z' := by
    let e := freeOpenSections (P (K := K) q) (U' ⊓ V')
    apply e.injective
    change e (freeOpenMap (inf_le_inf hU hV) ≫ zMap) = e (e.symm z')
    rw [freeOpenSections_naturality (P (K := K) q) (inf_le_inf hU hV) zMap,e.apply_symm_apply]
    have ez : freeOpenSections (P (K := K) q) (U ⊓ V) zMap = z :=
      (freeOpenSections (P (K := K) q) (U ⊓ V)).apply_symm_apply z
    rw [ez]
    rfl
  unfold relativeOfSection
  refine (CycleQ2RelativeSupportRefinement.natural q (cover U' V') (cover U V) h' h
    (sup_le_sup hU hV) hW m rfl zMap (sectionMap_closed q (cover U V) z hz)).trans ?_
  generalize_proofs
  congr 1

end CycleQ2RelativeSupportComparison

namespace CycleQ2LocalPrincipalRestriction

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open CycleQ2InjectiveCech (AbSheaf)
open CycleQ2LocalPrincipalGysin (cover union_le localClass)
open CycleQ2RelativeSupportRefinement (supportMap)
open CycleQ2RelativeSupportComparison (pullback_class)
open CycleQ2IntrinsicFramedAffineSite (FramedOpen)
open CycleQ2IntrinsicDeRhamSheaves (relativeDeRhamInt)
open CycleQ2IntrinsicLogSupportClass (logForm logForm_closed shiftedSection shiftedSection_restrict shiftedSection_closed)
open CycleQ2SmoothRelativeFrames (sectionCoefficients)
open CycleQ2RelativeAffineOverlap (restrict)
open CycleQ2IntrinsicPrincipalScale (log_restrict)
open CycleQ2PrincipalLogRestriction (unit_restrict)
open CycleQ2PrincipalLogSupportClass (restrictionUnit restrictionUnit_val)
open CycleQ2FiniteExactAffineAtlas (HasFrame)

variable {X : Scheme.{0}} {V W : X.Opens} (e : V ≤ W)

abbrev res (f : Γ(X,W)) : Γ(X,V) :=
  X.presheaf.map (homOfLE e).op f

theorem basic_le (f : Γ(X,W)) : X.basicOpen (res e f) ≤ X.basicOpen f := by
  rw [res,X.basicOpen_res]
  exact inf_le_right

private theorem unit_res (f : Γ(X,W)) {T : X.Opens} (h : T ≤ X.basicOpen (res e f)) :
    restrictionUnit (res e f) h = restrictionUnit f (h.trans (basic_le e f)) := by
  apply Units.ext
  rw [restrictionUnit_val,restrictionUnit_val]
  dsimp only [res]
  rw [← CommRingCat.comp_apply,← Functor.map_comp]
  exact congrArg (fun p => X.presheaf.map p f) (Subsingleton.elim _ _)

variable {k : Type} [Field k] [CharZero k] (p : X ⟶ Spec (CommRingCat.of k))
  (r : ℕ) [SmoothOfRelativeDimension r p] (f g : Γ(X,W))

private abbrev A := AbSheaf (show TopCat from X)
local instance : HasDerivedCategory.{1} (A (X := X)) := HasDerivedCategory.standard _
private abbrev E := DerivedCategory.singleFunctor (A (X := X)) 0
private abbrev K := relativeDeRhamInt p r

private theorem relativeOfSection_congr {K' : CochainComplex (A (X := X)) ℤ} (q : ℤ)
    (S : (Opens.grothendieckTopology (show TopCat from X)).MayerVietorisSquare)
    {V' : X.Opens} (h : S.X₄ ≤ V') {z z' : ((K'⟦q⟧).X 0).obj.obj (op S.X₁)}
    (hz : ((K'⟦q⟧).d 0 1).hom.app (op S.X₁) z = 0)
    (hz' : ((K'⟦q⟧).d 0 1).hom.app (op S.X₁) z' = 0) (he : z = z') :
    CycleQ2RelativeOpenSupport.relativeOfSection q S h z hz =
      CycleQ2RelativeOpenSupport.relativeOfSection q S h z' hz' := by
  subst z'
  rfl

theorem class_restrict
    (ho : IsAffineOpen (cover f g).X₁ ∧ HasFrame p r (cover f g).X₁)
    (hn : IsAffineOpen (cover (res e f) (res e g)).X₁ ∧ HasFrame p r (cover (res e f) (res e g)).X₁) :
    (E (X := X)).map (supportMap (union_le (res e f) (res e g)) (union_le f g)
      (sup_le_sup (basic_le e f) (basic_le e g)) e).τ₃ ≫ localClass p r f g ho =
    localClass p r (res e f) (res e g) hn := by
  let U := (cover f g).X₁
  let T := (cover (res e f) (res e g)).X₁
  let B : FramedOpen p r := ⟨U,ho⟩
  let C : FramedOpen p r := ⟨T,hn⟩
  let h : T ≤ U := inf_le_inf (basic_le e f) (basic_le e g)
  let a := restrictionUnit f (show U ≤ X.basicOpen f from inf_le_left)
  let b := restrictionUnit g (show U ≤ X.basicOpen g from inf_le_right)
  let a' := restrictionUnit (res e f) (show T ≤ X.basicOpen (res e f) from inf_le_left)
  let b' := restrictionUnit (res e g) (show T ≤ X.basicOpen (res e g) from inf_le_right)
  let u := logForm p r B a b
  let v := logForm p r C a' b'
  let z := shiftedSection p r B u
  have hz := shiftedSection_closed p r B u (logForm_closed p r B a b)
  have he := pullback_class (K := K p r) 2 (basic_le e f) (basic_le e g)
    (union_le (res e f) (res e g)) (union_le f g) e z hz
  unfold localClass
  refine he.trans ?_
  have hu : CycleQ2IntrinsicLogSupportClass.ordinaryRestrict p r B (B' := C) (homOfLE h) u = v := by
    let : Algebra k Γ(X,U) := (sectionCoefficients p U).toAlgebra
    let : Algebra k Γ(X,T) := (sectionCoefficients p T).toAlgebra
    dsimp only [u,v]
    rw [log_restrict]
    have ha : Units.map (restrict p h).toRingHom a = a' :=
      (unit_restrict f inf_le_left h).trans (unit_res e f inf_le_left).symm
    have hb : Units.map (restrict p h).toRingHom b = b' :=
      (unit_restrict g inf_le_right h).trans (unit_res e g inf_le_right).symm
    rw [ha,hb]
  have hw := (shiftedSection_restrict p r B (B' := C) (homOfLE h) u).trans
    (congrArg (shiftedSection p r C) hu)
  exact relativeOfSection_congr 2 _ _ _ _ hw

end CycleQ2LocalPrincipalRestriction

namespace CycleQ2RelativeSupportComposition

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open CycleQ2InjectiveCech (freeOpenMap)
open CycleQ2MayerVietorisRestriction (freeOpenSheaf)
open CycleQ2RelativeSupportRefinement (supportMap)
open CycleQ2RelativeOpenSupport (sequence)

variable {X : TopCat.{0}}

private theorem open_comp {U V W : Opens X} (h : U ≤ V) (g : V ≤ W) :
    freeOpenMap h ≫ freeOpenMap g = freeOpenMap (h.trans g) :=
  (freeOpenSheaf (X := X)).map_comp (homOfLE h) (homOfLE g) |>.symm

theorem supportMap_comp {U V T W Z P : Opens X} (h : U ≤ W) (j : V ≤ Z) (k : T ≤ P)
    (u : U ≤ V) (v : V ≤ T) (w : W ≤ Z) (z : Z ≤ P) :
    (supportMap h j u w).τ₃ ≫ (supportMap j k v z).τ₃ =
      (supportMap h k (u.trans v) (w.trans z)).τ₃ := by
  let f := supportMap h j u w
  let g := supportMap j k v z
  let l := supportMap h k (u.trans v) (w.trans z)
  apply (cancel_epi (sequence h).g).mp
  change (sequence h).g ≫ f.τ₃ ≫ g.τ₃ = (sequence h).g ≫ l.τ₃
  rw [← Category.assoc,← f.comm₂₃,Category.assoc,← g.comm₂₃,← Category.assoc,← l.comm₂₃]
  exact congrArg (fun p ↦ p ≫ (sequence k).g) (open_comp w z)

end CycleQ2RelativeSupportComposition

namespace CycleQ2ClosedGraphRestriction

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open CycleQ2InjectiveCech (AbSheaf)
open CycleQ2ClosedGraphSupport (complement classOf union_eq_complement)
open CycleQ2LocalPrincipalGysin (cover locus union_le localClass)
open CycleQ2LocalPrincipalRestriction (res basic_le class_restrict)
open CycleQ2PrincipalLogSupportClass (support_eq_zeroLocus)
open CycleQ2FiniteExactAffineAtlas (HasFrame)
open CycleQ2RelativeSupportRefinement (supportMap)
open CycleQ2RelativeSupportComposition (supportMap_comp)

variable {Z X : Scheme.{0}} (i : Z ⟶ X) [IsClosedImmersion i]
  {V W : X.Opens} (e : V ≤ W) (f g : Γ(X,W))
  (he : locus f g = (W : Set X) ∩ Set.range i)

include he in
theorem locus_restrict : locus (res e f) (res e g) = (V : Set X) ∩ Set.range i := by
  have h : (cover (res e f) (res e g)).X₄ = V ⊓ complement i := by
    change X.basicOpen (res e f) ⊔ X.basicOpen (res e g) = _
    rw [res,res,X.basicOpen_res,X.basicOpen_res,← inf_sup_left,
      show X.basicOpen f ⊔ X.basicOpen g = W ⊓ complement i from union_eq_complement i f g he,
      ← inf_assoc,inf_eq_left.mpr e]
  unfold locus
  rw [← support_eq_zeroLocus]
  change (V : Set X) ∩ ((cover (res e f) (res e g)).X₄ : Set X)ᶜ = _
  rw [h]
  ext x
  change (x ∈ V ∧ ¬ (x ∈ V ∧ x ∉ Set.range i)) ↔ x ∈ V ∧ x ∈ Set.range i
  tauto

variable {k : Type} [Field k] [CharZero k] (p : X ⟶ Spec (CommRingCat.of k))
  (r : ℕ) [SmoothOfRelativeDimension r p]

local instance : HasDerivedCategory.{1} (AbSheaf (show TopCat from X)) := HasDerivedCategory.standard _
private abbrev E := DerivedCategory.singleFunctor (AbSheaf (show TopCat from X)) 0
private abbrev cle (i : Z ⟶ X) [IsClosedImmersion i] (W : X.Opens) : W ⊓ complement i ≤ W := inf_le_left

theorem classOf_restrict
    (ho : IsAffineOpen (cover f g).X₁ ∧ HasFrame p r (cover f g).X₁)
    (hn : IsAffineOpen (cover (res e f) (res e g)).X₁ ∧ HasFrame p r (cover (res e f) (res e g)).X₁) :
    E.map (supportMap (cle i V) (cle i W) (inf_le_inf e le_rfl) e).τ₃ ≫ classOf i f g p r he ho =
      classOf i (res e f) (res e g) p r (locus_restrict i e f g he) hn := by
  let hO := union_le f g
  let hN := union_le (res e f) (res e g)
  let ht : V ⊓ complement i ≤ W ⊓ complement i := inf_le_inf e le_rfl
  let hu : (cover (res e f) (res e g)).X₄ ≤ (cover f g).X₄ := sup_le_sup (basic_le e f) (basic_le e g)
  let ho' := (union_eq_complement i f g he).ge
  let hn' := (union_eq_complement i (res e f) (res e g) (locus_restrict i e f g he)).ge
  let m := (supportMap (cle i V) (cle i W) ht e).τ₃
  let mO := (supportMap (cle i W) hO ho' (show W ≤ W from le_rfl)).τ₃
  let mN := (supportMap (cle i V) hN hn' (show V ≤ V from le_rfl)).τ₃
  let u := (supportMap hN hO hu e).τ₃
  let lO := localClass p r f g ho
  let lN := localClass p r (res e f) (res e g) hn
  have hc : E.map m ≫ E.map mO = E.map mN ≫ E.map u := by
    refine (E.map_comp m mO).symm.trans ?_
    refine (congrArg E.map ?_).trans (E.map_comp mN u)
    exact (supportMap_comp (cle i V) (cle i W) hO ht ho' e le_rfl).trans
      (supportMap_comp (cle i V) hN hO hn' hu le_rfl e).symm
  change E.map m ≫ E.map mO ≫ lO = E.map mN ≫ lN
  calc
    _ = (E.map m ≫ E.map mO) ≫ lO := (Category.assoc _ _ _).symm
    _ = E.map mN ≫ E.map u ≫ lO := (congrArg (fun d ↦ d ≫ lO) hc).trans (Category.assoc _ _ _)
    _ = E.map mN ≫ lN := congrArg (fun d ↦ E.map mN ≫ d) (class_restrict e p r f g ho hn)

end CycleQ2ClosedGraphRestriction

namespace CycleQ2LocalPrincipalScaleInvariant

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open CycleQ2InjectiveCech (AbSheaf)
open CycleQ2IntrinsicLogSupportClass
open CycleQ2IntrinsicFramedAffineSite (FramedOpen)
open CycleQ2IntrinsicDeRhamSheaves (relativeDeRhamInt)
open CycleQ2PrincipalLogSupportClass (restrictionUnit restrictionUnit_val square)
open CycleQ2PrincipalLogRestriction (unit_restrict)
open CycleQ2DerivedDoubleSupport (supportQuotient ofClosedSection)
open CycleQ2RelativeSupportRefinement (supportMap)
open CycleQ2RelativeSupportComparison (pullback_class eq_of_second_restriction)
open CycleQ2LocalPrincipalGysin (localClass union_le)
open CycleQ2IntrinsicPrincipalScale (log_restrict)
open CycleQ2SmoothRelativeFrames (sectionCoefficients)
open CycleQ2RelativeAffineOverlap (restrict)
open CycleQ2DoubleLogarithmicClass (twoLog pullback_twoLog twoLog_mul_left)

variable {k : Type} [Field k] [CharZero k] {X : Scheme.{0}}
  (p : X ⟶ Spec (CommRingCat.of k)) (r : ℕ) [SmoothOfRelativeDimension r p]
  {Z : X.Opens} (f g : Γ(X,Z)) (e : Γ(X,Z)ˣ)

private abbrev A := AbSheaf (show TopCat from X)
private abbrev K : CochainComplex (A (X := X)) ℤ := relativeDeRhamInt p r
local instance : HasDerivedCategory.{1} (A (X := X)) := HasDerivedCategory.standard _
private abbrev E := DerivedCategory.singleFunctor (A (X := X)) 0

abbrev scaled := (e : Γ(X,Z)) * f
abbrev U := X.basicOpen f
abbrev U' := X.basicOpen (scaled f e)
abbrev V := X.basicOpen g

theorem scaledOpen_eq : U' f e = U f := by
  change X.basicOpen ((e : Γ(X,Z))*f) = X.basicOpen f
  rw [X.basicOpen_mul,X.basicOpen_of_isUnit e.isUnit,inf_eq_right.mpr (X.basicOpen_le f)]

abbrev refineLeft : U' f e ≤ U f := (scaledOpen_eq f e).le

private def restrictedUnit {W : X.Opens} (h : W ≤ Z) : Γ(X,W)ˣ :=
  Units.map (X.presheaf.map (homOfLE h).op).hom e

private theorem unit_restrict_comp {W W' : X.Opens} (h : W' ≤ W) (hW : W ≤ Z) :
    letI : Algebra k Γ(X,W) := (sectionCoefficients p W).toAlgebra
    letI : Algebra k Γ(X,W') := (sectionCoefficients p W').toAlgebra
    Units.map (restrict p h).toRingHom (restrictedUnit e hW) = restrictedUnit e (h.trans hW) := by
  apply Units.ext
  simp only [restrictedUnit,Units.coe_map]
  change X.presheaf.map (homOfLE h).op
      ((X.presheaf.map (homOfLE hW).op) (e : Γ(X,Z))) = _
  rw [← CommRingCat.comp_apply,← Functor.map_comp]
  exact congrArg (fun a => X.presheaf.map a (e : Γ(X,Z))) (Subsingleton.elim _ _)

private theorem restrictionUnit_scaled {W : X.Opens} (h : W ≤ U' f e) :
    restrictionUnit (scaled f e) h =
      restrictedUnit e (h.trans (X.basicOpen_le (scaled f e))) *
        restrictionUnit f (h.trans (refineLeft f e)) := by
  apply Units.ext
  rw [restrictionUnit_val,Units.val_mul,restrictionUnit_val]
  let ρ := (X.presheaf.map (homOfLE (h.trans (X.basicOpen_le (scaled f e)))).op).hom
  change ρ ((e : Γ(X,Z)) * f) = ρ e * ρ f
  exact map_mul ρ _ _

private theorem unit_algRestrict {O W : X.Opens} (t : Γ(X,Z))
    (h : O ≤ X.basicOpen t) (j : W ≤ O) :
    letI : Algebra k Γ(X,O) := (sectionCoefficients p O).toAlgebra
    letI : Algebra k Γ(X,W) := (sectionCoefficients p W).toAlgebra
    Units.map (restrict p j).toRingHom (restrictionUnit t h) = restrictionUnit t (j.trans h) :=
  unit_restrict t h j

open CycleQ2FiniteExactAffineAtlas (HasFrame)

variable (hOld : IsAffineOpen (U f ⊓ V g) ∧ HasFrame p r (U f ⊓ V g))
  (hNew : IsAffineOpen (U' f e ⊓ V g) ∧ HasFrame p r (U' f e ⊓ V g))
  (hV : IsAffineOpen (V g) ∧ HasFrame p r (V g))

private abbrev Bo : FramedOpen p r := ⟨U f ⊓ V g,hOld⟩
private abbrev Bn : FramedOpen p r := ⟨U' f e ⊓ V g,hNew⟩
private abbrev Br : FramedOpen p r := ⟨V g,hV⟩
private abbrev oldLog := logForm p r (Bo p r f g hOld) (restrictionUnit f inf_le_left) (restrictionUnit g inf_le_right)
private abbrev newLog := logForm p r (Bn p r f g e hNew) (restrictionUnit (scaled f e) inf_le_left) (restrictionUnit g inf_le_right)
private abbrev correction := logForm p r (Br p r g hV) (restrictedUnit e (X.basicOpen_le g)) (restrictionUnit g le_rfl)
private abbrev leftIncl : U' f e ⊓ V g ≤ U f ⊓ V g := inf_le_inf (refineLeft f e) le_rfl

include hV in
private theorem difference :
    newLog p r f g e hNew =
      ordinaryRestrict p r (Bo p r f g hOld) (B' := Bn p r f g e hNew) (homOfLE (leftIncl f g e)) (oldLog p r f g hOld) +
      ordinaryRestrict p r (Br p r g hV) (B' := Bn p r f g e hNew) (homOfLE (show U' f e ⊓ V g ≤ V g from inf_le_right))
        (correction p r g e hV) := by
  rw [oldLog,correction,log_restrict,log_restrict,unit_algRestrict,unit_algRestrict,unit_algRestrict,unit_restrict_comp]
  rw [newLog,restrictionUnit_scaled]
  let W := U' f e ⊓ V g
  let : Algebra k Γ(X,W) := (sectionCoefficients p W).toAlgebra
  have h := twoLog_mul_left (K := k) (restrictedUnit e ((show W ≤ V g from inf_le_right).trans (X.basicOpen_le g)))
    (restrictionUnit f (show W ≤ U f from inf_le_left.trans (refineLeft f e)))
    (restrictionUnit g (show W ≤ V g from inf_le_right))
  change _ = _ at h
  exact h.trans (add_comm _ _)

include hV in
/-- The degree-four supported class is invariant under unit scaling. -/
theorem scale_invariant :
    (E (X := X)).map (supportMap (union_le (scaled f e) g) (union_le f g)
      (sup_le_sup (refineLeft f e) le_rfl) le_rfl).τ₃ ≫ localClass p r f g hOld =
      localClass p r (scaled f e) g hNew := by
  let w := shiftedSection p r (Br p r g hV) (correction p r g e hV)
  let m := shiftedSection p r (Bo p r f g hOld) (oldLog p r f g hOld)
  let n := shiftedSection p r (Bn p r f g e hNew) (newLog p r f g e hNew)
  have hw := shiftedSection_closed p r (Br p r g hV) (correction p r g e hV)
    (logForm_closed p r (Br p r g hV) (restrictedUnit e (X.basicOpen_le g)) (restrictionUnit g le_rfl))
  have hm := shiftedSection_closed p r (Bo p r f g hOld) (oldLog p r f g hOld)
    (logForm_closed p r (Bo p r f g hOld) (restrictionUnit f inf_le_left) (restrictionUnit g inf_le_right))
  have hn := shiftedSection_closed p r (Bn p r f g e hNew) (newLog p r f g e hNew)
    (logForm_closed p r (Bn p r f g e hNew) (restrictionUnit (scaled f e) inf_le_left) (restrictionUnit g inf_le_right))
  have he := pullback_class (K := K p r) 2 (refineLeft f e) (show V g ≤ V g from le_rfl)
    (union_le (scaled f e) g) (union_le f g) le_rfl m hm
  refine he.trans (Eq.symm ?_)
  apply eq_of_second_restriction (K := K p r) 2 (Opens.mayerVietorisSquare (U' f e) (V g))
    (union_le (scaled f e) g) _ n _ hn w hw
  have h₁ := shiftedSection_restrict p r (Bo p r f g hOld) (B' := Bn p r f g e hNew)
    (homOfLE (leftIncl f g e)) (oldLog p r f g hOld)
  have h₂ := shiftedSection_restrict p r (Br p r g hV) (B' := Bn p r f g e hNew)
    (homOfLE (show U' f e ⊓ V g ≤ V g from inf_le_right)) (correction p r g e hV)
  refine (congrArg (shiftedSection p r (Bn p r f g e hNew)) (difference p r f g e hOld hNew hV)).trans ?_
  exact (shiftedSection_add p r (Bn p r f g e hNew) _ _).trans (congrArg₂ (· + ·) h₁.symm h₂.symm)

end CycleQ2LocalPrincipalScaleInvariant

namespace CycleQ2RelativeSupportSwap

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open CycleQ2InjectiveCech (AbSheaf freeOpen freeOpenMap freeOpenSections freeOpenSections_naturality)
open CycleQ2MayerVietorisRestriction (freeOpenSheaf)
open CycleQ2DerivedDoubleSupport (sectionMap sectionMap_closed)
open CycleQ2DerivedSupportSwap (overlapLE unionLE swapSequence)
open CycleQ2RelativeOpenSupport (relativeOfSection)
open CycleQ2RelativeSupportRefinement (supportMap natural)

variable {X : TopCat.{0}} (U V : Opens X)
local instance : HasDerivedCategory.{1} (AbSheaf X) := HasDerivedCategory.standard _

private abbrev S := Opens.mayerVietorisSquare U V
private abbrev T := Opens.mayerVietorisSquare V U

variable {K : CochainComplex (AbSheaf X) ℤ} (q : ℤ)
private abbrev F := ((K⟦q⟧).X 0).obj
private abbrev d := (K⟦q⟧).d 0 1
private abbrev E := DerivedCategory.singleFunctor (AbSheaf X) 0

private theorem section_neg_restrict (z : (F (K := K) q).obj (op (U ⊓ V))) :
    (-freeOpenMap (overlapLE U V)) ≫ sectionMap q (S U V) z =
      sectionMap q (T U V) (-((F q).map (homOfLE (overlapLE U V)).op z)) := by
  let e := freeOpenSections ((K⟦q⟧).X 0) (V ⊓ U)
  apply e.injective
  erw [Preadditive.neg_comp,map_neg]
  change -(freeOpenSections ((K⟦q⟧).X 0) (V ⊓ U))
    (freeOpenMap (overlapLE U V) ≫ sectionMap q (S U V) z) = _
  erw [freeOpenSections_naturality]
  change -((F q).map (homOfLE (overlapLE U V)).op
    (freeOpenSections ((K⟦q⟧).X 0) (U ⊓ V)
      ((freeOpenSections ((K⟦q⟧).X 0) (U ⊓ V)).symm z))) =
    e (e.symm (-((F q).map (homOfLE (overlapLE U V)).op z)))
  erw [AddEquiv.apply_symm_apply,AddEquiv.apply_symm_apply]

theorem swap_class {W : Opens X} (h : U ⊔ V ≤ W) (h' : V ⊔ U ≤ W)
    (z : (F (K := K) q).obj (op (U ⊓ V))) (hz : (d q).hom.app (op (U ⊓ V)) z = 0)
    (w : (F (K := K) q).obj (op (V ⊓ U))) (hw : (d q).hom.app (op (V ⊓ U)) w = 0)
    (he : w = -((F q).map (homOfLE (overlapLE U V)).op z)) :
    (E (X := X)).map (supportMap h' h (unionLE U V) le_rfl).τ₃ ≫ relativeOfSection q (S U V) h z hz =
      relativeOfSection q (T U V) h' w hw := by
  unfold relativeOfSection
  have hc := natural q (T U V) (S U V) h' h (unionLE U V) le_rfl
    (swapSequence U V) rfl (sectionMap q (S U V) z) (sectionMap_closed q (S U V) z hz)
  have hsec : (swapSequence U V).τ₁ ≫ sectionMap q (S U V) z = sectionMap q (T U V) w := by
    rw [he]
    exact section_neg_restrict U V q z
  have hclass {u v : (T U V).shortComplex.X₁ ⟶ (K⟦q⟧).X 0}
      (e : u = v) (hu : u ≫ (K⟦q⟧).d 0 1 = 0) (hv : v ≫ (K⟦q⟧).d 0 1 = 0) :
      CycleQ2RelativeOpenSupport.relativeClass q (T U V) h' u hu =
        CycleQ2RelativeOpenSupport.relativeClass q (T U V) h' v hv := by
    subst v
    rfl
  exact hc.trans (hclass hsec _ _)

end CycleQ2RelativeSupportSwap

namespace CycleQ2LocalPrincipalSwapInvariant

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open CycleQ2InjectiveCech (AbSheaf)
open CycleQ2IntrinsicFramedAffineSite (FramedOpen)
open CycleQ2FiniteExactAffineAtlas (HasFrame)
open CycleQ2IntrinsicDeRhamSheaves (relativeDeRhamInt)
open CycleQ2IntrinsicLogSupportClass
open CycleQ2PrincipalLogSupportClass (restrictionUnit)
open CycleQ2LocalPrincipalGysin (cover localClass union_le)
open CycleQ2IntrinsicPrincipalScale (log_restrict)
open CycleQ2PrincipalLogRestriction (unit_restrict)
open CycleQ2RelativeAffineOverlap (restrict)
open CycleQ2DerivedSupportSwap (overlapLE unionLE)
open CycleQ2RelativeSupportSwap (swap_class)
open CycleQ2RelativeSupportRefinement (supportMap)
open CycleQ2SmoothRelativeFrames (sectionCoefficients)

variable {k : Type} [Field k] [CharZero k] {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of k)) (r : ℕ)
  [SmoothOfRelativeDimension r p] {W : X.Opens} (f g : Γ(X,W))

private abbrev A := AbSheaf (show TopCat from X)
private abbrev K : CochainComplex (A (X := X)) ℤ := relativeDeRhamInt p r
local instance : HasDerivedCategory.{1} (A (X := X)) := HasDerivedCategory.standard _
private abbrev E := DerivedCategory.singleFunctor (A (X := X)) 0

private theorem shifted_neg (B : FramedOpen p r) (ω : OrdinaryTwo p r B) :
    shiftedSection p r B (-ω) = -shiftedSection p r B ω := by
  have h₀ : shiftedSection p r B 0 = 0 := by
    have h := shiftedSection_add p r B 0 0
    rw [zero_add] at h
    exact add_left_cancel (h.symm.trans (add_zero _).symm)
  have h := shiftedSection_add p r B (-ω) ω
  rw [neg_add_cancel,h₀] at h
  exact eq_neg_of_add_eq_zero_left h.symm

variable (hOld : IsAffineOpen (cover f g).X₁ ∧ HasFrame p r (cover f g).X₁)
  (hNew : IsAffineOpen (cover g f).X₁ ∧ HasFrame p r (cover g f).X₁)

private abbrev Bo : FramedOpen p r := ⟨(cover f g).X₁,hOld⟩
private abbrev Bn : FramedOpen p r := ⟨(cover g f).X₁,hNew⟩
private abbrev old := logForm p r (Bo p r f g hOld) (restrictionUnit f inf_le_left) (restrictionUnit g inf_le_right)
private abbrev new := logForm p r (Bn p r f g hNew) (restrictionUnit g inf_le_left) (restrictionUnit f inf_le_right)

private theorem unit_algRestrict {T O : X.Opens} (t : Γ(X,W)) (h : O ≤ X.basicOpen t) (j : T ≤ O) :
    letI : Algebra k Γ(X,O) := (sectionCoefficients p O).toAlgebra
    letI : Algebra k Γ(X,T) := (sectionCoefficients p T).toAlgebra
    Units.map (restrict p j).toRingHom (restrictionUnit t h) = restrictionUnit t (j.trans h) :=
  unit_restrict t h j

private theorem reverse_log :
    new p r f g hNew = -ordinaryRestrict p r (Bo p r f g hOld)
      (B' := Bn p r f g hNew) (homOfLE (overlapLE (X.basicOpen f) (X.basicOpen g))) (old p r f g hOld) := by
  erw [old,log_restrict,unit_algRestrict,unit_algRestrict]
  let : Algebra k Γ(X,X.basicOpen g ⊓ X.basicOpen f) :=
    (sectionCoefficients p (X.basicOpen g ⊓ X.basicOpen f)).toAlgebra
  exact CycleQ2DoubleLogarithmicClass.twoLog_swap (K := k)
    (restrictionUnit f (show X.basicOpen g ⊓ X.basicOpen f ≤ X.basicOpen f from inf_le_right))
    (restrictionUnit g (show X.basicOpen g ⊓ X.basicOpen f ≤ X.basicOpen g from inf_le_left))

/-- The support quotient maps are the ordinary ones on the equal unions. -/
theorem swap_invariant :
    (E (X := X)).map (supportMap (union_le g f) (union_le f g)
      (unionLE (X.basicOpen f) (X.basicOpen g)) le_rfl).τ₃ ≫ localClass p r f g hOld =
      localClass p r g f hNew := by
  have hO := shiftedSection_closed p r (Bo p r f g hOld) (old p r f g hOld)
    (logForm_closed p r (Bo p r f g hOld) _ _)
  have hN := shiftedSection_closed p r (Bn p r f g hNew) (new p r f g hNew)
    (logForm_closed p r (Bn p r f g hNew) _ _)
  refine swap_class (K := K p r) (X.basicOpen f) (X.basicOpen g) 2 (union_le f g) (union_le g f)
    (shiftedSection p r (Bo p r f g hOld) (old p r f g hOld)) hO
    (shiftedSection p r (Bn p r f g hNew) (new p r f g hNew)) hN ?_
  let j : Bn p r f g hNew ⟶ Bo p r f g hOld :=
    homOfLE (overlapLE (X.basicOpen f) (X.basicOpen g))
  have h := shiftedSection_restrict p r (Bo p r f g hOld) (B' := Bn p r f g hNew) j (old p r f g hOld)
  exact (congrArg (shiftedSection p r (Bn p r f g hNew)) (reverse_log p r f g hOld hNew)).trans
    ((shifted_neg p r (Bn p r f g hNew) _).trans (congrArg Neg.neg h.symm))

end CycleQ2LocalPrincipalSwapInvariant

namespace CycleQ2ClosedGraphGeneratorChanges

open CategoryTheory AlgebraicGeometry TopologicalSpace
open CycleQ2InjectiveCech (AbSheaf)
open CycleQ2ClosedGraphSupport (complement classOf union_eq_complement)
open CycleQ2LocalPrincipalGysin (cover locus union_le localClass)
open CycleQ2PrincipalLogSupportClass (support_eq_zeroLocus)
open CycleQ2FiniteExactAffineAtlas (HasFrame)
open CycleQ2RelativeSupportRefinement (supportMap)
open CycleQ2RelativeSupportComposition (supportMap_comp)
open CycleQ2LocalPrincipalScaleInvariant (scaled scaledOpen_eq)

variable {Z X : Scheme.{0}} (i : Z ⟶ X) [IsClosedImmersion i]
  {W : X.Opens} {k : Type} [Field k] [CharZero k] (p : X ⟶ Spec (CommRingCat.of k))
  (r : ℕ) [SmoothOfRelativeDimension r p]

local instance : HasDerivedCategory.{1} (AbSheaf (show TopCat from X)) := HasDerivedCategory.standard _
private abbrev E := DerivedCategory.singleFunctor (AbSheaf (show TopCat from X)) 0

theorem locus_eq_of_union_eq (f g f' g' : Γ(X,W)) (hu : (cover f g).X₄ = (cover f' g').X₄) :
    locus f g = locus f' g' := by
  unfold locus
  rw [← support_eq_zeroLocus f g,← support_eq_zeroLocus f' g']
  exact congrArg (fun U : X.Opens ↦ (W : Set X) ∩ (U : Set X)ᶜ) hu

theorem classOf_eq (f g f' g' : Γ(X,W))
    (he : locus f g = (W : Set X) ∩ Set.range i)
    (he' : locus f' g' = (W : Set X) ∩ Set.range i)
    (ho : IsAffineOpen (cover f g).X₁ ∧ HasFrame p r (cover f g).X₁)
    (hn : IsAffineOpen (cover f' g').X₁ ∧ HasFrame p r (cover f' g').X₁)
    (u : (cover f' g').X₄ ≤ (cover f g).X₄)
    (ht : E.map (supportMap (union_le f' g') (union_le f g) u le_rfl).τ₃ ≫ localClass p r f g ho =
      localClass p r f' g' hn) :
    classOf i f g p r he ho = classOf i f' g' p r he' hn := by
  let leW : W ⊓ complement i ≤ W := inf_le_left
  let e := (union_eq_complement i f g he).ge
  let e' := (union_eq_complement i f' g' he').ge
  let f₁ := (supportMap leW (union_le f' g') e' (show W ≤ W from le_rfl)).τ₃
  let f₂ := (supportMap (union_le f' g') (union_le f g) u (show W ≤ W from le_rfl)).τ₃
  let f₃ := (supportMap leW (union_le f g) e (show W ≤ W from le_rfl)).τ₃
  have hc : E.map f₃ = E.map f₁ ≫ E.map f₂ :=
    (congrArg E.map (supportMap_comp leW (union_le f' g') (union_le f g) e' u le_rfl le_rfl)).symm.trans
      (E.map_comp f₁ f₂)
  let L := localClass p r f g ho
  change E.map f₃ ≫ L = E.map f₁ ≫ localClass p r f' g' hn
  calc
    _ = (E.map f₁ ≫ E.map f₂) ≫ L := congrArg (fun u ↦ u ≫ L) hc
    _ = E.map f₁ ≫ E.map f₂ ≫ L := Category.assoc _ _ _
    _ = _ := congrArg (fun u ↦ E.map f₁ ≫ u) ht

theorem swap_locus (f g : Γ(X,W)) : locus g f = locus f g :=
  locus_eq_of_union_eq g f f g (sup_comm _ _)

theorem classOf_swap (f g : Γ(X,W))
    (he : locus f g = (W : Set X) ∩ Set.range i)
    (ho : IsAffineOpen (cover f g).X₁ ∧ HasFrame p r (cover f g).X₁)
    (hn : IsAffineOpen (cover g f).X₁ ∧ HasFrame p r (cover g f).X₁) :
    classOf i f g p r he ho = classOf i g f p r ((swap_locus f g).trans he) hn :=
  classOf_eq i p r f g g f he _ ho hn _
    (CycleQ2LocalPrincipalSwapInvariant.swap_invariant p r f g ho hn)

theorem scale_locus (f g : Γ(X,W)) (e : Γ(X,W)ˣ) : locus (scaled f e) g = locus f g :=
  locus_eq_of_union_eq (scaled f e) g f g
    (congrArg (fun U ↦ U ⊔ X.basicOpen g) (scaledOpen_eq f e))

theorem classOf_scale (f g : Γ(X,W)) (e : Γ(X,W)ˣ)
    (he : locus f g = (W : Set X) ∩ Set.range i)
    (ho : IsAffineOpen (cover f g).X₁ ∧ HasFrame p r (cover f g).X₁)
    (hn : IsAffineOpen (cover (scaled f e) g).X₁ ∧ HasFrame p r (cover (scaled f e) g).X₁)
    (hR : IsAffineOpen (X.basicOpen g) ∧ HasFrame p r (X.basicOpen g)) :
    classOf i f g p r he ho = classOf i (scaled f e) g p r ((scale_locus f g e).trans he) hn :=
  classOf_eq i p r f g (scaled f e) g he _ ho hn _
    (CycleQ2LocalPrincipalScaleInvariant.scale_invariant p r f g e ho hn hR)

end CycleQ2ClosedGraphGeneratorChanges
