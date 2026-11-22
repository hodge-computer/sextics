import Proposal.GeometricSupportedClassNonvanishing
import Proposal.GeometricSmoothSurfaceGysin
import Proposal.GeometricMarkedProjectionSurvives
import Mathlib.Topology.Homeomorph.Lemmas

/-! After deleting the projected boundary, the marked surface carries its normalized supported class on the full curve product. Its support is proper over the target open and contains a quasi-finite marked point.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false

noncomputable section

namespace CycleQ2ProperProductGysin

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open CycleQ2ProductCoefficients (productBase)
open CycleQ2ClosedGraphSupport (complement support)
open CycleQ2IntrinsicDeRhamSheaves (relativeDeRhamInt)
open CycleQ2InjectiveCech (AbSheaf)
open CycleQ2SmoothSurfaceGysin (atlasOpen atlasClass)

variable {k : Type} [Field k] [CharZero k] {M Z C T : Scheme.{0}}
  (c : C ⟶ Spec (CommRingCat.of k)) (t : T ⟶ Spec (CommRingCat.of k))
  (e : Z ⟶ pullback c t) [IsClosedImmersion e] (j : M ⟶ Z) [IsOpenImmersion j]
  [IsProper c] [SmoothOfRelativeDimension 1 c] [SmoothOfRelativeDimension 3 t]

local notation "π" => pullback.snd c t

/-- Delete precisely the target image of the boundary of the chosen closure. -/
def targetOpen : T.Opens :=
  ⟨((e ≫ π) '' (Set.range j)ᶜ)ᶜ,
    ((e ≫ π).isClosedMap _ j.isOpenEmbedding.isOpen_range.isClosed_compl).isOpen_compl⟩

abbrev productOpen := π ⁻¹ᵁ targetOpen c t e j
abbrev surfaceOpen := e ⁻¹ᵁ productOpen c t e j
abbrev embedding := e ∣_ productOpen c t e j
abbrev project := π ∣_ targetOpen c t e j
abbrev overField := (productOpen c t e j).ι ≫ productBase c t

instance : IsClosedImmersion (embedding c t e j) :=
  MorphismProperty.of_isPullback (isPullback_morphismRestrict e _).flip inferInstance
instance : IsProper (project c t e j) :=
  MorphismProperty.of_isPullback (isPullback_morphismRestrict π _).flip inferInstance
instance : SmoothOfRelativeDimension 4 (overField c t e j) := by
  let : SmoothOfRelativeDimension 4 (productBase c t) :=
    CycleQ2ProductFramedOpen.smooth_product c t 3
  exact smoothOfRelativeDimension_comp 0 4 _ _

omit [CharZero k] [SmoothOfRelativeDimension 1 c] [SmoothOfRelativeDimension 3 t] in
/-- The ambient is the fiber product of the whole proper curve with the target open. -/
theorem product_square :
    IsPullback ((productOpen c t e j).ι ≫ pullback.fst c t) (project c t e j)
      c ((targetOpen c t e j).ι ≫ t) :=
  (isPullback_morphismRestrict π _).flip.paste_horiz (IsPullback.of_hasPullback c t)

/-- The restricted closure lies entirely in the original marked surface. -/
def toMarked : (surfaceOpen c t e j).toScheme ⟶ M :=
  IsOpenImmersion.lift j (surfaceOpen c t e j).ι (by
    rintro _ ⟨z,rfl⟩
    by_contra h
    exact z.property ⟨z.val,h,rfl⟩)

instance : IsOpenImmersion (toMarked c t e j) := by
  have h : toMarked c t e j ≫ j = (surfaceOpen c t e j).ι := IsOpenImmersion.lift_fac _ _ _
  let : IsOpenImmersion (toMarked c t e j ≫ j) := h ▸ inferInstance
  exact IsOpenImmersion.of_comp _ j

omit [CharZero k] [SmoothOfRelativeDimension 1 c] [SmoothOfRelativeDimension 3 t] in
@[reassoc (attr := simp)]
theorem toMarked_fac : toMarked c t e j ≫ j = (surfaceOpen c t e j).ι :=
  IsOpenImmersion.lift_fac _ _ _

local instance derived (Y : TopCat.{0}) : HasDerivedCategory.{1} (AbSheaf Y) :=
  HasDerivedCategory.standard _

set_option quotPrecheck false
local notation "Y" => (productOpen c t e j).toScheme
local notation "I" => embedding c t e j
local notation "P" => overField c t e j
local notation "Ω" => (DerivedCategory.Q.obj (relativeDeRhamInt P 4) : DerivedCategory.{1} (AbSheaf (show TopCat from Y)))
local notation "E" => DerivedCategory.singleFunctor (AbSheaf (show TopCat from Y)) 0

/-- Every equation chart for the restricted surface has the prescribed logarithmic
normalization in the ambient product with the proper curve. Its projection is proper. -/
theorem normalized_on_product [Algebra ℂ k] [NoetherianSpace ↑(pullback c t : Scheme.{0})]
    (hs : SmoothOfRelativeDimension 2 (j ≫ e ≫ productBase c t)) :
    IsProper (I ≫ project c t e j) ∧
    ∃ z : (E).obj (support I ⊤) ⟶ Ω⟦(4:ℤ)⟧, ∀ n,
      CycleQ2NoetherianSupport.res (complement I) (show atlasOpen P I n ≤ ⊤ from le_top) z =
        atlasClass P I n := by
  let m := toMarked c t e j
  let p := m ≫ j ≫ e ≫ productBase c t
  have h : I ≫ P = p := by
    simp [embedding,overField,p,m]
  let : SmoothOfRelativeDimension 2 p := smoothOfRelativeDimension_comp 0 2 _ _
  let : NoetherianSpace Y :=
    (productOpen c t e j).ι.isOpenEmbedding.isEmbedding.isInducing.noetherianSpace
  exact ⟨inferInstance,CycleQ2SmoothSurfaceGysin.exists_global p P I h⟩

end CycleQ2ProperProductGysin

namespace CycleQ2MarkedFunctionPoint

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open CycleQ2LiteralIncidenceRelativeSpread CycleQ2LiteralIncidenceNormalizedSlice
open CycleQ2LiteralIncidenceRelativeCompletion CycleQ2LiteralIncidenceRelativeCorrespondence
open CycleQ2LiteralIncidenceGenericCorrespondence CycleQ2GenericSmoothCurveGraph
open CycleQ2IncidenceEtaleParameter (parameterScheme)
open CycleQ2NativeWeightedCover (ambientToField)
open CycleQ2InjectiveCech (AbSheaf freeOpenMap)
open CycleQ2ClosedGraphSupport (complement support)

local instance derived (X : TopCat.{0}) : HasDerivedCategory.{1} (AbSheaf X) :=
  HasDerivedCategory.standard _

/-- A supported class has zero ordinary restriction on each open disjoint from its support. -/
theorem forget_off {Y S : Scheme.{0}} (i : S ⟶ Y) [IsClosedImmersion i] (O : Y.Opens)
    (off : O ≤ complement i) {K : DerivedCategory.{1} (AbSheaf (show TopCat from Y))}
    (z : (DerivedCategory.singleFunctor (AbSheaf (show TopCat from Y)) 0).obj (support i ⊤) ⟶ K) :
    let E := DerivedCategory.singleFunctor (AbSheaf (show TopCat from Y)) 0
    E.map (freeOpenMap (show O ≤ ⊤ from le_top)) ≫
      E.map (CycleQ2SupportMV.π (complement i) ⊤) ≫ z = 0 := by
  let E := DerivedCategory.singleFunctor (AbSheaf (show TopCat from Y)) 0
  let d : O ≤ ⊤ := le_top
  have h := E.map_isZero (CycleQ2SmoothTwoChartAgreement.isZero_support_off_graph i O off)
  have hr : E.map (CycleQ2SupportMV.inc (complement i) d) ≫ z = 0 := h.eq_of_src _ _
  calc
    _ = E.map (CycleQ2SupportMV.π (complement i) O) ≫
        E.map (CycleQ2SupportMV.inc (complement i) d) ≫ z := by
      simp only [← Category.assoc,← Functor.map_comp,CycleQ2SupportMV.natural]
      rfl
    _ = 0 := by rw [hr,CategoryTheory.Limits.comp_zero]

variable (V : parameterScheme.Opens) (t : Fin 3 → ℂ) {C D S : Scheme.{0}}
  (r : C ⟶ Completion V) (c : C ⟶ Spec (CommRingCat.of genericField))
  (hc : r ≫ structureMap V = c ≫ genericPoint)
  (j : D ⟶ C) (a : D ⟶ Time toRaw V)
  (ha : j ≫ r = a ≫ CycleQ2LiteralIncidenceRelativeCompletion.inclusion V)
  (hs : SmoothOfRelativeDimension 1 (curveMap toRaw V t)) (U : genericAmbient.Opens)

set_option quotPrecheck false
local notation "m" => fromTest V t r j a ha
local notation "g" => target V t r c hc
local notation "π" => pullback.snd c ambientToField
local notation "W" => π ⁻¹ᵁ U
local notation "E" => DerivedCategory.singleFunctor (AbSheaf (show TopCat from (W).toScheme)) 0

include hs in
/-- A target neighborhood of the function point misses the marked surface. -/
theorem avoiding
    (hU : (U : Set genericAmbient) = (((m).imageι ≫ g) '' (Set.range (m).toImage)ᶜ)ᶜ)
    (i : S ⟶ (W).toScheme) [IsClosedImmersion i] (v : S ⟶ TestSurface V t a)
    (square : IsPullback i (v ≫ (m).toImage) (W).ι ((m).imageι ≫ embeddingGeneric V t r c hc)) :
    ∃ A : genericAmbient.Opens, A ≤ U ∧
      Set.range CycleQ2GenericGraphFunctionStalk.functionPoint ⊆ (A : Set genericAmbient) ∧
      ((W).ι ≫ π) ⁻¹ᵁ A ≤ complement i := by
  let A := CycleQ2GenericProperGraphSupport.complement V t
  have outside (x : Graph V t r) : g x ∉ A := fun hx =>
    hx (target_in_original_support V t r c hc ⟨x,rfl⟩)
  have htime := timeMap_smooth toRaw V
  have hsurf : SmoothOfRelativeDimension 2 (CycleQ2GenericProperGraphOpen.surfaceStructure V t) :=
    smoothOfRelativeDimension_comp 1 1 _ _
  have hproper : IsProper (CycleQ2GenericProperGraphOpen.graphStructure V t) := by
    unfold CycleQ2GenericProperGraphOpen.graphStructure
    infer_instance
  refine ⟨A,?_,?_,?_⟩
  · intro y hy
    change y ∈ (U : Set genericAmbient)
    rw [hU]
    rintro ⟨q,_,rfl⟩
    exact outside ((m).imageι q) hy
  · rintro _ ⟨x,rfl⟩
    exact CycleQ2GenericGraphFunctionStalk.functionPoint_mem hsurf hproper x
  · let O := ((W).ι ≫ π) ⁻¹ᵁ A
    have fac : i ≫ (W).ι ≫ π = v ≫ m ≫ g := by
      rw [← Category.assoc,square.w]
      simp only [Category.assoc,Scheme.Hom.toImage_imageι_assoc,embeddingGeneric_toAmbient]
    have off : O ≤ complement i := by
      rintro _ hx ⟨s,rfl⟩
      have hpoint : ((W).ι ≫ π) (i s) = g (m (v s)) :=
        congrArg (fun (f : S ⟶ genericAmbient) => f s) fac
      exact outside (m (v s)) (hpoint ▸ hx)
    exact off

set_option maxHeartbeats 1200000 in
include hs in
/-- The graph square gives a single target open containing the function point on
which the ordinary image of the specified supported class restricts to zero. -/
theorem vanishes
    (hU : (U : Set genericAmbient) = (((m).imageι ≫ g) '' (Set.range (m).toImage)ᶜ)ᶜ)
    (i : S ⟶ (W).toScheme) [IsClosedImmersion i] (v : S ⟶ TestSurface V t a)
    (square : IsPullback i (v ≫ (m).toImage) (W).ι ((m).imageι ≫ embeddingGeneric V t r c hc))
    (K : DerivedCategory.{1} (AbSheaf (show TopCat from (W).toScheme)))
    (z : (E).obj (support i ⊤) ⟶ K) :
    ∃ A : genericAmbient.Opens, A ≤ U ∧
      Set.range CycleQ2GenericGraphFunctionStalk.functionPoint ⊆ (A : Set genericAmbient) ∧
      (E).map (freeOpenMap (show ((W).ι ≫ π) ⁻¹ᵁ A ≤ ⊤ from le_top)) ≫
        (E).map (CycleQ2SupportMV.π (complement i) ⊤) ≫ z = 0 := by
  obtain ⟨A,hAU,hpoint,hoff⟩ := avoiding V t r c hc j a ha hs U hU i v square
  exact ⟨A,hAU,hpoint,forget_off i _ hoff z⟩

end CycleQ2MarkedFunctionPoint

namespace CycleQ2SurvivingProductGysin
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open CycleQ2LiteralIncidenceRelativeSpread CycleQ2LiteralIncidenceNormalizedSlice
open CycleQ2LiteralIncidenceRelativeCompletion CycleQ2LiteralIncidenceRelativeCorrespondence
open CycleQ2LiteralIncidenceGenericCorrespondence CycleQ2GenericSmoothCurveGraph
open CycleQ2IncidenceEtaleParameter (parameterScheme)
open CycleQ2IncidenceSeedFiberCover (seedBasePoint)
open CycleQ2NativeWeightedCover (ambientToField)
open CycleQ2ProductCoefficients (productBase)
open CycleQ2ProperProductGysin
open CycleQ2InjectiveCech (AbSheaf)
open CycleQ2ClosedGraphSupport (complement support)
open CycleQ2IntrinsicDeRhamSheaves (relativeDeRhamInt)
open CycleQ2SmoothSurfaceGysin (atlasOpen atlasClass)

local instance derived (X : TopCat.{0}) : HasDerivedCategory.{1} (AbSheaf X) :=
  HasDerivedCategory.standard _
set_option quotPrecheck false
local notation "T" => ambientToField

variable {Y S : Scheme.{0}}

abbrev SupportedClass (p : Y ⟶ Spec (CommRingCat.of genericField)) (i : S ⟶ Y)
    [IsClosedImmersion i] [SmoothOfRelativeDimension 4 p] :=
  (DerivedCategory.singleFunctor (AbSheaf (show TopCat from Y)) 0).obj (support i ⊤) ⟶
    (DerivedCategory.Q.obj (relativeDeRhamInt p 4))⟦(4:ℤ)⟧

abbrev IsNormalized (p : Y ⟶ Spec (CommRingCat.of genericField)) (i : S ⟶ Y)
    [IsClosedImmersion i] [SmoothOfRelativeDimension 4 p] (z : SupportedClass p i) : Prop :=
  ∀ n, CycleQ2NoetherianSupport.res (complement i) (show atlasOpen p i n ≤ ⊤ from le_top) z =
    atlasClass p i n

def HasNormalizedClass (p : Y ⟶ Spec (CommRingCat.of genericField)) (i : S ⟶ Y) : Prop :=
  ∃ (h : IsClosedImmersion i) (hs : SmoothOfRelativeDimension 4 p),
    let := h
    let := hs
    ∃ z : SupportedClass p i, IsNormalized p i z

/-- A nonzero supported class with the chart normalization. Its ordinary image vanishes
over a neighborhood of the function point contained in the chosen target open. -/
def HasNonzeroNormalizedClass (π : Y ⟶ genericAmbient) (U : genericAmbient.Opens)
    (p : Y ⟶ Spec (CommRingCat.of genericField)) (i : S ⟶ Y) : Prop :=
  ∃ (h : IsClosedImmersion i) (hs : SmoothOfRelativeDimension 4 p),
    let := h
    let := hs
    ∃ z : SupportedClass p i, z ≠ 0 ∧ IsNormalized p i z ∧
      ∃ A : genericAmbient.Opens, A ≤ U ∧
        Set.range CycleQ2GenericGraphFunctionStalk.functionPoint ⊆ (A : Set genericAmbient) ∧
        let E := DerivedCategory.singleFunctor (AbSheaf (show TopCat from Y)) 0
        E.map (CycleQ2InjectiveCech.freeOpenMap (show π ⁻¹ᵁ A ≤ ⊤ from le_top)) ≫
          E.map (CycleQ2SupportMV.π (complement i) ⊤) ≫ z = 0

/-- The Cartesian presentation of the open product as a literal fiber product. -/
theorem literalSquare {C : Scheme} (c : C ⟶ Spec (CommRingCat.of genericField))
    (U : genericAmbient.Opens) :
    IsPullback ((pullback.snd c T ⁻¹ᵁ U).ι ≫ pullback.fst c T)
      (pullback.snd c T ∣_ U) c (U.ι ≫ T) :=
  (isPullback_morphismRestrict (pullback.snd c T) U).flip.paste_horiz
    (IsPullback.of_hasPullback c T)

abbrev literalIso {C : Scheme} (c : C ⟶ Spec (CommRingCat.of genericField))
    (U : genericAmbient.Opens) := (literalSquare c U).isoPullback

abbrev literalOpen {C : Scheme} (c : C ⟶ Spec (CommRingCat.of genericField))
    (U : genericAmbient.Opens) := (literalIso c U).inv ≫ (pullback.snd c T ⁻¹ᵁ U).ι

@[reassoc]
theorem literalOpen_fst {C : Scheme} (c : C ⟶ Spec (CommRingCat.of genericField))
    (U : genericAmbient.Opens) :
    literalOpen c U ≫ pullback.fst c T = pullback.fst c (U.ι ≫ T) :=
  (Category.assoc _ _ _).trans (literalSquare c U).isoPullback_inv_fst

@[reassoc]
theorem literalOpen_snd {C : Scheme} (c : C ⟶ Spec (CommRingCat.of genericField))
    (U : genericAmbient.Opens) :
    literalOpen c U ≫ pullback.snd c T = pullback.snd c (U.ι ≫ T) ≫ U.ι := by
  rw [literalOpen, Category.assoc, ← morphismRestrict_ι, ← Category.assoc,
    (literalSquare c U).isoPullback_inv_snd]

theorem literalOpen_overField {C : Scheme} (c : C ⟶ Spec (CommRingCat.of genericField))
    (U : genericAmbient.Opens) : literalOpen c U ≫ productBase c T = productBase c (U.ι ≫ T) :=
  (Category.assoc _ _ _).symm.trans (congrArg (fun f => f ≫ c) (literalOpen_fst c U))

private theorem literal_cartesian {S X C B : Scheme} {i : S ⟶ X} {v : S ⟶ C}
    {u : X ⟶ B} {b : C ⟶ B} (h : IsPullback i v u b) {Y : Scheme} (e : X ≅ Y) :
    IsPullback (i ≫ e.hom) v (e.inv ≫ u) b := by
  apply h.of_iso (Iso.refl _) e (Iso.refl _) (Iso.refl _) <;> simp

/-- A normalized supported class on the literal product with the proper curve. Its support
projects properly and misses a target neighborhood of the function point. -/
def LiteralClass {C S : Scheme} (c : C ⟶ Spec (CommRingCat.of genericField))
    (U : genericAmbient.Opens) (i : S ⟶ pullback c (U.ι ≫ T)) : Prop :=
  let ρ := pullback.snd c (U.ι ≫ T)
  let q := productBase c (U.ι ≫ T)
  IsProper (i ≫ ρ) ∧ SmoothOfRelativeDimension 2 (i ≫ q) ∧
    ∃ (h : IsClosedImmersion i) (h₄ : SmoothOfRelativeDimension 4 q),
      let := h
      let := h₄
      ∃ z : SupportedClass q i, z ≠ 0 ∧ IsNormalized q i z ∧
        ∃ A : genericAmbient.Opens, A ≤ U ∧
          Set.range CycleQ2GenericGraphFunctionStalk.functionPoint ⊆ (A : Set genericAmbient) ∧
          (ρ ≫ U.ι) ⁻¹ᵁ A ≤ complement i ∧
          let E := DerivedCategory.singleFunctor (AbSheaf (show TopCat from (pullback c (U.ι ≫ T) : Scheme))) 0
          E.map (CycleQ2InjectiveCech.freeOpenMap (show (ρ ≫ U.ι) ⁻¹ᵁ A ≤ ⊤ from le_top)) ≫
            E.map (CycleQ2SupportMV.π (complement i) ⊤) ≫ z = 0

private theorem make_literal {C S : Scheme} (c : C ⟶ Spec (CommRingCat.of genericField))
    (U : genericAmbient.Opens) (i : S ⟶ (pullback.snd c T ⁻¹ᵁ U).toScheme)
    (x : S) [IsClosedImmersion i] [IsProper c]
    [NoetherianSpace (pullback.snd c T ⁻¹ᵁ U).toScheme]
    [SmoothOfRelativeDimension 4 ((pullback.snd c T ⁻¹ᵁ U).ι ≫ productBase c T)]
    [SmoothOfRelativeDimension 2 (i ≫ (pullback.snd c T ⁻¹ᵁ U).ι ≫ productBase c T)]
    (A : genericAmbient.Opens) (hAU : A ≤ U)
    (hpoint : Set.range CycleQ2GenericGraphFunctionStalk.functionPoint ⊆ (A : Set genericAmbient))
    (hoff : ((pullback.snd c T ⁻¹ᵁ U).ι ≫ pullback.snd c T) ⁻¹ᵁ A ≤ complement i) :
    LiteralClass c U (i ≫ (literalIso c U).hom) := by
  let e := literalIso c U
  let I := i ≫ e.hom
  let W := pullback.snd c T ⁻¹ᵁ U
  let q := productBase c (U.ι ≫ T)
  let ρ := pullback.snd c (U.ι ≫ T)
  have field : e.hom ≫ q = W.ι ≫ productBase c T := by
    change e.hom ≫ pullback.fst _ _ ≫ c = W.ι ≫ pullback.fst c T ≫ c
    rw [← Category.assoc, (literalSquare c U).isoPullback_hom_fst, Category.assoc]
  have proj : e.hom ≫ ρ ≫ U.ι = W.ι ≫ pullback.snd c T := by
    rw [← Category.assoc, (literalSquare c U).isoPullback_hom_snd, morphismRestrict_ι]
  let _ : NoetherianSpace (pullback c (U.ι ≫ T) : Scheme) := e.inv.isOpenEmbedding.isInducing.noetherianSpace
  have hq : q = e.inv ≫ (W.ι ≫ productBase c T) := by rw [← field, Iso.inv_hom_id_assoc]
  let _ : SmoothOfRelativeDimension 4 q := by
    rw [hq]
    exact smoothOfRelativeDimension_comp 0 4 _ _
  let _ : SmoothOfRelativeDimension 2 (I ≫ q) := by
    change SmoothOfRelativeDimension 2 ((i ≫ e.hom) ≫ q)
    rw [Category.assoc, field]
    infer_instance
  obtain ⟨z,hz⟩ := CycleQ2SmoothSurfaceGysin.exists_global (I ≫ q) q I rfl
  have away : (ρ ≫ U.ι) ⁻¹ᵁ A ≤ complement I := by
    rintro _ hy ⟨s,rfl⟩
    apply hoff (show i s ∈ (W.ι ≫ pullback.snd c T) ⁻¹ᵁ A from ?_) ⟨s,rfl⟩
    have eqn := congrArg (fun f : W.toScheme ⟶ genericAmbient => f (i s)) proj
    change (W.ι ≫ pullback.snd c T) (i s) ∈ A
    rw [← eqn]
    exact hy
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance, z,
    CycleQ2LogDetection.normalized_ne_zero (I ≫ q) q I rfl x z hz, hz,
    A,hAU,hpoint,away,CycleQ2MarkedFunctionPoint.forget_off I _ away z⟩

abbrev ProductProperty := ∀ {Y S : Scheme.{0}},
  (Y ⟶ genericAmbient) → genericAmbient.Opens → (Y ⟶ Spec (CommRingCat.of genericField)) →
    (S ⟶ Y) → Prop

/-- A surviving product with a property depending on seed compatibility, the open time test,
and smoothness of its marked surface over the generic field. -/
def SurvivesOnProduct (P : Prop → Prop → Prop → ProductProperty) : Prop :=
    ∃ (t : Fin 3 → ℂ), AlgebraicIndependent ℚ t ∧ ∃ V : parameterScheme.Opens, seedBasePoint ∈ V ∧
      ∃ (C : Scheme) (c : C ⟶ Spec (CommRingCat.of genericField)) (r : C ⟶ Completion V)
        (hc : r ≫ structureMap V = c ≫ genericPoint) (D : Scheme) (j : D ⟶ C)
        (a : D ⟶ Time toRaw V) (ha : j ≫ r = a ≫ CycleQ2LiteralIncidenceRelativeCompletion.inclusion V),
        let m := fromTest V t r j a ha
        let g := target V t r c hc
        let b := m.imageι ≫ embeddingGeneric V t r c hc
        let B := (m.imageι ≫ g) '' (Set.range m.toImage)ᶜ
        IsIntegral C ∧ IsProper c ∧ SmoothOfRelativeDimension 1 c ∧
        (∃ q : C ⟶ CycleQ2LaurentProjectiveLine.line genericField, IsFinite q ∧ IsDominant q ∧
          q ≫ CycleQ2ProjectiveLineStructure.structureMap genericField = c) ∧
        topologicalKrullDim B ≤ 1 ∧ (2 : WithBot ℕ∞) ≤ topologicalKrullDim (Set.range (m ≫ g)) ∧
        ∃ U : genericAmbient.Opens, (U : Set genericAmbient) = Bᶜ ∧
          let W := pullback.snd c T ⁻¹ᵁ U
          let pr := pullback.snd c T ∣_ U
          IsPullback (W.ι ≫ pullback.fst c T) pr c (U.ι ≫ T) ∧
          ∃ (S : Scheme) (i : S ⟶ W.toScheme) (v : S ⟶ TestSurface V t a),
            IsPullback i (v ≫ m.toImage) W.ι b ∧ IsOpenImmersion v ∧ IsProper (i ≫ pr) ∧
            (∃ s : S, g.QuasiFiniteAt (m (v s))) ∧
              P (∃ hV : seedBasePoint ∈ V, CycleQ2MarkedGenericSurvives.SeedCompatible t V hV c r j a)
                (IsOpenImmersion j ∧ SmoothOfRelativeDimension 2 (i ≫ W.ι ≫ productBase c T))
                (IsPullback (i ≫ (literalIso c U).hom) (v ≫ m.toImage) (literalOpen c U) b ∧
                  LiteralClass c U (i ≫ (literalIso c U).hom))
                (W.ι ≫ pullback.snd c T) U (W.ι ≫ productBase c T) i

/-- The surface and its relative smoothness on the corresponding open of the original product. -/
abbrev SurvivesWithGeometry (P : Prop → Prop → ProductProperty) : Prop :=
  SurvivesOnProduct (fun seed facts _ {_ _} π U p i => P seed facts π U p i)

/-- A surviving product with a property depending on its first-order seed compatibility. -/
abbrev SurvivesWithSeed (P : Prop → ProductProperty) : Prop :=
  SurvivesWithGeometry (fun seed _ {_ _} π U p i => P seed π U p i)

/-- The original product and support data, with a property of the supported class. -/
def SurvivesWith (P : ProductProperty) : Prop := SurvivesWithSeed (fun _ => @P)

private theorem exists_surviving_on_product (P : Prop → Prop → Prop → ProductProperty)
    (hP : ∀ {seed facts literal : Prop} {Y S : Scheme.{0}} (π : Y ⟶ genericAmbient) (U : genericAmbient.Opens)
      (p : Y ⟶ Spec (CommRingCat.of genericField)) (i : S ⟶ Y),
      seed → facts → literal → HasNonzeroNormalizedClass π U p i → P seed facts literal π U p i) : SurvivesOnProduct P := by
  obtain ⟨t,ht,V,hV,C,c,r,hc,D,j,a,ha,hCompatible,hC,hp,hc₁,hproj,hj,hjd,hs,_,hB,hd,z,hz,hout⟩ :=
    CycleQ2MarkedGenericSurvives.exists_compatible_marked_point_outside_projected_boundary
  let m := fromTest V t r j a ha
  let G := embeddingGeneric V t r c hc
  let g := target V t r c hc
  let b := m.imageι ≫ G
  let π := pullback.snd c T
  let : IsOpenImmersion m := MorphismProperty.of_isPullback (test_square V t r j a ha) hj
  let : NoetherianSpace (Graph V t r) :=
    CycleQ2LiteralIncidenceGenericModel.noetherian_of_proper (toCurve V t r ≫ c)
  let : NoetherianSpace (TestSurface V t a) := m.isOpenEmbedding.isInducing.noetherianSpace
  let : SmoothOfRelativeDimension 3 T := CycleQ2NativeGenericSmooth.ambient_smooth
  let : IsProper T := CycleQ2NativeWeightedCover.ambient_proper
  let : NoetherianSpace (genericProduct c) :=
    CycleQ2LiteralIncidenceGenericModel.noetherian_of_proper (productBase c T)
  let U := targetOpen c T b m.toImage
  let W := productOpen c T b m.toImage
  let i := CycleQ2ProperProductGysin.embedding c T b m.toImage
  let v := toMarked c T b m.toImage
  have hb : b ≫ π = m.imageι ≫ g := by
    dsimp only [b,G,π,g]
    rw [Category.assoc,embeddingGeneric_toAmbient]
  have hU : (U : Set genericAmbient) = ((m.imageι ≫ g) '' (Set.range m.toImage)ᶜ)ᶜ := by
    change ((b ≫ π) '' _)ᶜ = _
    rw [hb]
  have square : IsPullback i (v ≫ m.toImage) W.ι b := by
    rw [show v ≫ m.toImage = (surfaceOpen c T b m.toImage).ι from toMarked_fac _ _ _ _]
    exact isPullback_morphismRestrict b W
  refine ⟨t,ht,V,hV,C,c,r,hc,D,j,a,ha,hC,hp,hc₁,hproj,hB,hd,U,hU,product_square c T b m.toImage,
    _,i,v,square,inferInstance,?_⟩
  have eqm : m.toImage ≫ b ≫ π = m ≫ g := by rw [hb,Scheme.Hom.toImage_imageι_assoc]
  have hpoint : (b ≫ π) (m.toImage z) = g (m z) :=
    congrArg (fun (l : TestSurface V t a ⟶ genericAmbient) => l z) eqm
  have hmem : (b ≫ π) (m.toImage z) ∈ (U : Set genericAmbient) := by
    rw [hU,hpoint]
    exact hout
  let s : (surfaceOpen c T b m.toImage).toScheme := ⟨m.toImage z,hmem⟩
  have hsv : v s = z := m.toImage.isOpenEmbedding.injective
    (congrArg (fun (l : (surfaceOpen c T b m.toImage).toScheme ⟶ m.image) => l s)
      (toMarked_fac c T b m.toImage))
  have h : m.toImage ≫ b ≫ productBase c T =
      pullback.fst a (curveMap toRaw V t) ≫ (j ≫ c) := by
    change m.toImage ≫ (m.imageι ≫ G) ≫ pullback.fst c T ≫ c = _
    calc
      _ = m ≫ G ≫ pullback.fst c T ≫ c := by
        simp only [Category.assoc,Scheme.Hom.toImage_imageι_assoc]
      _ = m ≫ toCurve V t r ≫ c := by rw [show G ≫ pullback.fst c T ≫ c =
        toCurve V t r ≫ c from embeddingGeneric_toCurve_assoc V t r c hc c]
      _ = _ := by rw [← Category.assoc m,← (test_square V t r j a ha).w,Category.assoc]
  have hSm : SmoothOfRelativeDimension 2 (m.toImage ≫ b ≫ productBase c T) := by
    rw [h]
    let : SmoothOfRelativeDimension 1 (pullback.fst a (curveMap toRaw V t)) :=
      (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback
        (IsPullback.of_hasPullback a (curveMap toRaw V t)).flip hs
    let : SmoothOfRelativeDimension 1 (j ≫ c) := smoothOfRelativeDimension_comp 0 1 j c
    exact smoothOfRelativeDimension_comp 1 1 _ _
  obtain ⟨hproper,z',hlog⟩ := normalized_on_product c T b m.toImage hSm
  let q := overField c T b m.toImage
  let p := v ≫ m.toImage ≫ b ≫ productBase c T
  have hi : i ≫ q = p := by
    simp [i,q,CycleQ2ProperProductGysin.embedding,overField,p,v]
  let : SmoothOfRelativeDimension 2 p := smoothOfRelativeDimension_comp 0 2 _ _
  have hsource : SmoothOfRelativeDimension 2 (i ≫ q) := hi.symm ▸ inferInstanceAs
    (SmoothOfRelativeDimension 2 p)
  let _ : NoetherianSpace W.toScheme := W.ι.isOpenEmbedding.isInducing.noetherianSpace
  obtain ⟨A,hAU,hpt,hoff⟩ :=
    CycleQ2MarkedFunctionPoint.avoiding V t r c hc j a ha hs U hU i v square
  refine ⟨hproper,⟨s,hsv.symm ▸ hz⟩,hP _ _ _ _ ⟨hV, hCompatible⟩ ⟨hj, hsource⟩
    ⟨literal_cartesian square (literalIso c U), make_literal c U i s A hAU hpt hoff⟩ ?_⟩
  exact ⟨inferInstance,inferInstance,z',CycleQ2LogDetection.normalized_ne_zero p q i hi s z' hlog,
    hlog,A,hAU,hpt,CycleQ2MarkedFunctionPoint.forget_off i _ hoff z'⟩

private theorem exists_surviving_with (P : Prop → Prop → ProductProperty)
    (hP : ∀ {seed facts : Prop} {Y S : Scheme.{0}} (π : Y ⟶ genericAmbient) (U : genericAmbient.Opens)
      (p : Y ⟶ Spec (CommRingCat.of genericField)) (i : S ⟶ Y),
      seed → facts → HasNonzeroNormalizedClass π U p i → P seed facts π U p i) : SurvivesWithGeometry P :=
  exists_surviving_on_product _ (by
    intro seed facts L Y S π U p i hs hf _ hn
    exact hP π U p i hs hf hn)

/-- The product with the whole proper curve carries the normalized logarithmic class
on a nonempty marked surface after deleting a target subset of dimension at most one. -/
theorem exists_surviving_product : SurvivesWith (fun _ _ p i => HasNormalizedClass p i) :=
  exists_surviving_with (fun _ _ {_ _} _ _ p i => HasNormalizedClass p i) (by
    intro _ _ Y S π U p i _ _ h
    obtain ⟨ci,sm,z,_,hz,_⟩ := h
    exact ⟨ci,sm,z,hz⟩)

/-- The same surviving proper product admits a nonzero normalized class whose ordinary image
vanishes over a neighborhood of the function point. -/
theorem exists_surviving_nonzero_product :
    SurvivesWith (fun π U p i => HasNonzeroNormalizedClass π U p i) :=
  exists_surviving_with (fun _ _ {_ _} π U p i => HasNonzeroNormalizedClass π U p i)
    (by intro _ _ _ _ _ _ _ _ _ _ h; exact h)

/-- The curve bearing the nonzero class and its marked surface share the integral
time neighborhood through the original first-order seed. -/
theorem exists_seed_compatible_nonzero_product :
    SurvivesWithSeed (fun seed {_ _} π U p i => seed ∧ HasNonzeroNormalizedClass π U p i) :=
  exists_surviving_with (fun seed _ {_ _} π U p i => seed ∧ HasNonzeroNormalizedClass π U p i)
    (by intro _ _ _ _ _ _ _ _ hs _ h; exact ⟨hs, h⟩)

/-- The same seed-compatible nonzero class retains its open dense time test and smooth
two-dimensional source over the generic field. -/
theorem exists_seed_compatible_framed_product :
    SurvivesWithGeometry (fun seed facts {_ _} π U p i =>
      seed ∧ facts ∧ HasNonzeroNormalizedClass π U p i) :=
  exists_surviving_with _ (by
    intro _ _ _ _ _ _ _ _ hs hf h
    exact ⟨hs, hf, h⟩)

/-- The literal fiber product carries a normalized nonzero class on the same marked surface
as the open-product class, with a proper projection and an open missing the support. -/
theorem exists_seed_compatible_literal_product :
    SurvivesOnProduct (fun seed facts literal {_ _} π U p i =>
      seed ∧ facts ∧ literal ∧ HasNonzeroNormalizedClass π U p i) :=
  exists_surviving_on_product _ (by
    intro _ _ _ _ _ _ _ _ _ hs hf hl hn
    exact ⟨hs,hf,hl,hn⟩)

end CycleQ2SurvivingProductGysin
#print axioms CycleQ2SurvivingProductGysin.exists_surviving_product
#print axioms CycleQ2SurvivingProductGysin.exists_surviving_nonzero_product

#print axioms CycleQ2SurvivingProductGysin.exists_seed_compatible_nonzero_product

#print axioms CycleQ2SurvivingProductGysin.exists_seed_compatible_framed_product

#print axioms CycleQ2SurvivingProductGysin.exists_seed_compatible_literal_product

/-! The original closure boundary is kept in the fourfold. Its complement
contains the entire marked surface, before any projected boundary is
removed from the threefold. All supported classes below use the ambient
fourfold complex and the original closed immersion. -/

namespace CycleQ2MarkedClosureOpen

open CategoryTheory AlgebraicGeometry TopologicalSpace

variable {M Z Y : Scheme.{0}} (e : Z ⟶ Y) [IsClosedImmersion e]
  (j : M ⟶ Z) [IsOpenImmersion j]

/-- The actual original boundary, as a closed subset of the fourfold. -/
def boundary : Set Y := e '' (Set.range j)ᶜ

theorem boundary_closed : IsClosed (boundary e j) :=
  e.isClosedEmbedding.isClosedMap _ j.isOpenEmbedding.isOpen_range.isClosed_compl

/-- Removing only the original closure boundary retains every marked point. -/
def goodOpen : Y.Opens := ⟨(boundary e j)ᶜ,(boundary_closed e j).isOpen_compl⟩

theorem complement_le_goodOpen : CycleQ2ClosedGraphSupport.complement e ≤ goodOpen e j := by
  intro y hy
  rintro ⟨z,_,hz⟩
  exact hy ⟨z,hz⟩

/-- The residual source in the actual support filtration has exactly
the original boundary as its closed support. -/
theorem residual_complement :
    CycleQ2ClosedGraphSupport.complement e ⊔ goodOpen e j = goodOpen e j :=
  sup_eq_right.mpr (complement_le_goodOpen e j)

theorem boundary_dimension_le (h : topologicalKrullDim ((Set.range j)ᶜ : Set Z) ≤ 1) :
    topologicalKrullDim (boundary e j) ≤ 1 := by
  let a := e.isClosedEmbedding.isEmbedding.homeomorphImage ((Set.range j)ᶜ : Set Z)
  exact a.symm.isInducing.topologicalKrullDim_le.trans h

theorem marked_mem (x : M) : e (j x) ∈ goodOpen e j := by
  rintro ⟨z,hz,he⟩
  exact hz ⟨x,(e.isClosedEmbedding.injective he).symm⟩

theorem source_mem_iff (z : Z) : e z ∈ goodOpen e j ↔ z ∈ Set.range j := by
  constructor
  · intro h
    by_contra hn
    exact h ⟨z,hn,rfl⟩
  · rintro ⟨x,rfl⟩
    exact marked_mem e j x

/-- On any smaller open the surviving closed support is the original
marked surface. This equality concerns the original embedding, not its
projection to the threefold. -/
theorem marked_range_on {W : Y.Opens} (hW : W ≤ goodOpen e j) :
    (W : Set Y) ∩ Set.range e = (W : Set Y) ∩ Set.range (j ≫ e) := by
  ext y
  constructor
  · rintro ⟨hy,z,rfl⟩
    obtain ⟨x,hx⟩ := (source_mem_iff e j z).mp (hW hy)
    exact ⟨hy,x,by change e (j x) = e z; rw [hx]⟩
  · rintro ⟨hy,x,rfl⟩
    exact ⟨hy,j x,rfl⟩

def toMarked : (e ⁻¹ᵁ goodOpen e j).toScheme ⟶ M :=
  IsOpenImmersion.lift j (e ⁻¹ᵁ goodOpen e j).ι (by
    rintro _ ⟨z,rfl⟩
    exact (source_mem_iff e j z.val).mp z.property)

@[reassoc (attr := simp)] theorem toMarked_fac :
    toMarked e j ≫ j = (e ⁻¹ᵁ goodOpen e j).ι :=
  IsOpenImmersion.lift_fac _ _ _

instance toMarked_isOpenImmersion : IsOpenImmersion (toMarked e j) := by
  have : IsOpenImmersion (toMarked e j ≫ j) := by rw [toMarked_fac]; infer_instance
  exact IsOpenImmersion.of_comp _ j

def fromMarked : M ⟶ (e ⁻¹ᵁ goodOpen e j).toScheme :=
  IsOpenImmersion.lift (e ⁻¹ᵁ goodOpen e j).ι j (by
    rintro _ ⟨x,rfl⟩
    exact ⟨⟨j x,marked_mem e j x⟩,rfl⟩)

@[reassoc (attr := simp)] theorem fromMarked_fac :
    fromMarked e j ≫ (e ⁻¹ᵁ goodOpen e j).ι = j :=
  IsOpenImmersion.lift_fac _ _ _

/-- The original marked surface, with its actual map to the fourfold,
is exactly the restriction of the original closure. -/
def markedIso : M ≅ (e ⁻¹ᵁ goodOpen e j).toScheme where
  hom := fromMarked e j
  inv := toMarked e j
  hom_inv_id := by
    apply (cancel_mono j).mp
    simp only [Category.assoc,toMarked_fac,fromMarked_fac,Category.id_comp]
  inv_hom_id := by
    apply (cancel_mono (e ⁻¹ᵁ goodOpen e j).ι).mp
    simp only [Category.assoc,fromMarked_fac,toMarked_fac,Category.id_comp]

section Product

open CategoryTheory.Limits

variable {k : Type} [Field k] {C T : Scheme.{0}}
  (c : C ⟶ Spec (CommRingCat.of k)) (t : T ⟶ Spec (CommRingCat.of k))
  (b : Z ⟶ pullback c t) [IsClosedImmersion b]
  [IsProper c] [SmoothOfRelativeDimension 1 c] [SmoothOfRelativeDimension 3 t]

/-- The old product open is a smaller open of this exact boundary
complement. Its possibly larger deleted support is not used in a
dimension estimate. -/
theorem productOpen_le :
    CycleQ2ProperProductGysin.productOpen c t b j ≤ goodOpen b j := by
  intro y hy
  rintro ⟨z,hz,he⟩
  apply hy
  exact ⟨z,hz,by change (pullback.snd c t) (b z) = (pullback.snd c t) y; rw [he]⟩

end Product

end CycleQ2MarkedClosureOpen

namespace CycleQ2MarkedOpenGysin

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open Algebra Module KaehlerDifferential
open scoped TensorProduct
open CycleQ2SmoothStalkFrames (coefficientAlg exists_exact_frame)
open CycleQ2SmoothImmersionStalkEquations (stalkAlgHom)
open CycleQ2FiniteExactAffineAtlas (HasFrame hasFrame_of_affine_le)
open CycleQ2SmoothTwoChartAgreement (locus_of_span pairFrame restriction)
open CycleQ2SmoothSurfaceGysin (Chart chartClass)
open CycleQ2ClosedGraphSupport (complement support classOf)
open CycleQ2IntrinsicDeRhamSheaves (relativeDeRhamInt)
open CycleQ2InjectiveCech (AbSheaf)
open CycleQ2MarkedClosureOpen (goodOpen marked_mem source_mem_iff)
open CycleQ2AdaptedAffineFrame (ExactOnOpen)

variable {k : Type} [Field k] {M Z Y : Scheme.{0}}
  (q : Y ⟶ Spec (CommRingCat.of k)) (e : Z ⟶ Y) [IsClosedImmersion e]
  (j : M ⟶ Z) [IsOpenImmersion j]
  [SmoothOfRelativeDimension 4 q] [SmoothOfRelativeDimension 2 (j ≫ e ≫ q)]

private theorem stalk_surjective (x : M) : Function.Surjective ((j ≫ e).stalkMap x) := by
  rw [Scheme.Hom.stalkMap_comp]
  exact (ConcreteCategory.bijective_of_isIso (j.stalkMap x)).surjective.comp
    (e.stalkMap_surjective (j x))

private theorem stalk_kernel (x : M) :
    RingHom.ker ((j ≫ e).stalkMap x).hom = RingHom.ker (e.stalkMap (j x)).hom := by
  rw [Scheme.Hom.stalkMap_comp,CommRingCat.hom_comp,RingHom.ker_comp_of_injective]
  exact (ConcreteCategory.bijective_of_isIso (j.stalkMap x)).injective

/-- The two equations generate the ideal of the original closed closure
on an actual affine neighborhood of the marked point. -/
theorem exists_chart (x : M) (N : Y.Opens) (hx : e (j x) ∈ N) :
    ∃ (A : Chart q e), e (j x) ∈ A.U.1 ∧ A.U.1 ≤ N := by
  let : Smooth q := SmoothOfRelativeDimension.smooth 4 q
  let : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian q
  obtain ⟨U,⟨hU,hframe⟩,hzU,hUN⟩ :=
    (Opens.isBasis_iff_nbhd.mp (CycleQ2FiniteExactAffineAtlas.isBasis q 4)) hx
  have hi : (j ≫ e) ≫ q = j ≫ e ≫ q := Category.assoc _ _ _
  obtain ⟨s,hs⟩ := CycleQ2SmoothImmersionStalkEquations.stalk_kernel_generators
    (j ≫ e ≫ q) q (j ≫ e) hi x 4 2 (stalk_surjective e j x)
  rw [stalk_kernel e j x] at hs
  obtain ⟨d,hzW,a,ha⟩ :=
    CycleQ2ClosedImmersionAffineEquations.exists_affine_equations e ⟨U,hU⟩ (j x) hzU s hs
  have hrange : Set.range a = {a 0,a 1} := by
    ext y
    constructor
    · rintro ⟨n,rfl⟩
      fin_cases n <;> simp
    · rintro (h | h)
      · exact ⟨0,h.symm⟩
      · exact ⟨1,(Set.mem_singleton_iff.mp h).symm⟩
  let A : Chart q e := ⟨Y.affineBasicOpen d,a 0,a 1,
    hasFrame_of_affine_le q 4 (Y.basicOpen_le d) hU (Y.affineBasicOpen d).2 hframe,
    by rwa [← hrange]⟩
  exact ⟨A,hzW,(Y.basicOpen_le d).trans hUN⟩

private theorem normal_stalk_basis (x : M) (f : Fin 2 → Y.presheaf.stalk (e (j x)))
    (hf : Ideal.span (Set.range f) = RingHom.ker (e.stalkMap (j x)).hom) :
    letI := coefficientAlg q (e (j x))
    ∃ (u : Fin 2 → Y.presheaf.stalk (e (j x)))
      (b : Basis (Fin 4) (Y.presheaf.stalk (e (j x))) Ω[Y.presheaf.stalk (e (j x))⁄k]),
      ∀ l, b l = D k _ (Fin.append f u l) := by
  let p := j ≫ e ≫ q
  let i := j ≫ e
  letI := coefficientAlg q (i x)
  letI := coefficientAlg p x
  let φ := stalkAlgHom p q i (Category.assoc j e q) x
  letI : Algebra (Y.presheaf.stalk (i x)) (M.presheaf.stalk x) := φ.toAlgebra
  let : IsLocalHom (algebraMap (Y.presheaf.stalk (i x)) (M.presheaf.stalk x)) :=
    inferInstanceAs (IsLocalHom (i.stalkMap x).hom)
  obtain ⟨_,b,_⟩ := exists_exact_frame q (i x) 4
  obtain ⟨v,c,hv⟩ := exists_exact_frame p x 2
  choose u hu using fun l => stalk_surjective e j x (v l)
  have hc (l : Fin 2) : c l = D k _ (φ (u l)) := by
    rw [hv]
    exact congrArg (D k _) (hu l).symm
  have hf' : Ideal.span (Set.range f) = RingHom.ker φ.toRingHom :=
    hf.trans (stalk_kernel e j x).symm
  obtain ⟨b',hb'⟩ := CycleQ2FrameLifting.basis_of_baseChange_span
    (B := M.presheaf.stalk x) b (fun l => D k _ (Fin.append f u l))
    (CycleQ2NormalTangentFrame.span_after_restriction φ (stalk_surjective e j x) f hf' u c hc)
  exact ⟨u,b',hb'⟩

/-- The original equations are the first two coordinates of an exact
ambient frame. Smoothness is required only on the marked source. -/
theorem adapted_chart (A : Chart q e) (x : M) (hx : e (j x) ∈ A.U.1) :
    ∃ (T : Y.affineOpens) (h : T.1 ≤ A.U.1), e (j x) ∈ T.1 ∧
      ∃ w : Fin 4 → Γ(Y,T.1), ExactOnOpen q w ∧
        w 0 = Y.presheaf.map (homOfLE h).op A.f ∧
        w 1 = Y.presheaf.map (homOfLE h).op A.g := by
  let ρ := (Y.presheaf.germ A.U.1 (e (j x)) hx).hom
  let f : Fin 2 → Y.presheaf.stalk (e (j x)) := ![ρ A.f,ρ A.g]
  obtain ⟨u,b,hb⟩ := normal_stalk_basis q e j x f
    (CycleQ2AffineEquationGerms.span_pair e A.U (j x) hx A.f A.g A.equations)
  let ur := Fin.append f u
  have hu0 : ur 0 = ρ A.f := (Fin.append_left f u (0 : Fin 2)).trans rfl
  have hu1 : ur 1 = ρ A.g := (Fin.append_left f u (1 : Fin 2)).trans rfl
  obtain ⟨T,h,hxT,w,hw,_,hf,hg⟩ :=
    CycleQ2AdaptedAffineFrame.exists_pair_frame q A.U (e (j x)) hx A.frame A.f A.g
      ur hu0 hu1 ⟨b,hb⟩
  exact ⟨T,h,hxT,w,hw,hf,hg⟩

private theorem exists_matrix (U : Y.affineOpens) (x : M) (hx : e (j x) ∈ U.1)
    (f g f' g' : Γ(Y,U.1))
    (hf : Ideal.span {f,g} = e.ker.ideal U) (hg : Ideal.span {f',g'} = e.ker.ideal U) :
    ∃ a b c d : Γ(Y,U.1), f' = a*f+b*g ∧ g' = c*f+d*g ∧
      e (j x) ∈ Y.basicOpen (a*d-b*c) := by
  have hp : f' ∈ Ideal.span {f,g} := by
    rw [hf,← hg]
    exact Ideal.subset_span (Set.mem_insert _ _)
  have hq : g' ∈ Ideal.span {f,g} := by
    rw [hf,← hg]
    exact Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  obtain ⟨a,b,ha⟩ := Ideal.mem_span_pair.mp hp
  obtain ⟨c,d,hc⟩ := Ideal.mem_span_pair.mp hq
  let ρ := (Y.presheaf.germ U.1 (e (j x)) hx).hom
  let T : Matrix (Fin 2) (Fin 2) (Y.presheaf.stalk (e (j x))) := !![ρ a,ρ c;ρ b,ρ d]
  have hT : ∀ l : Fin 2, (![ρ f',ρ g'] : Fin 2 → _) l =
      ∑ v, T v l * (![ρ f,ρ g] : Fin 2 → _) v := by
    intro l
    fin_cases l <;> simp [T,Fin.sum_univ_two,← map_mul,← map_add,ha,hc]
  have hfg : Ideal.span (Set.range ![ρ f,ρ g]) = RingHom.ker ((j ≫ e).stalkMap x).hom :=
    (CycleQ2AffineEquationGerms.span_pair e U (j x) hx f g hf).trans (stalk_kernel e j x).symm
  have hfg' : Ideal.span (Set.range ![ρ f',ρ g']) = RingHom.ker ((j ≫ e).stalkMap x).hom :=
    (CycleQ2AffineEquationGerms.span_pair e U (j x) hx f' g' hg).trans (stalk_kernel e j x).symm
  have ht := CycleQ2SmoothStalkGeneratorChange.determinant_unit
    (j ≫ e ≫ q) q (j ≫ e) (Category.assoc j e q) x 4 2
    (stalk_surjective e j x) ![ρ f,ρ g] ![ρ f',ρ g'] hfg hfg' T hT
  refine ⟨a,b,c,d,ha.symm,hc.symm,(Y.mem_basicOpen _ (e (j x)) hx).mpr ?_⟩
  change IsUnit (ρ (a*d-b*c))
  simpa only [T,Matrix.det_fin_two,map_sub,map_mul,mul_comm] using ht

variable [CharZero k]

local instance derived (X : TopCat.{0}) : HasDerivedCategory.{1} (AbSheaf X) :=
  HasDerivedCategory.standard _

private abbrev E := DerivedCategory.singleFunctor (AbSheaf (show TopCat from Y)) 0
private abbrev K : DerivedCategory.{1} (AbSheaf (show TopCat from Y)) :=
  DerivedCategory.Q.obj (relativeDeRhamInt q 4)

private theorem span_restrict {T U : Y.affineOpens} (h : T.1 ≤ U.1)
    (f g : Γ(Y,U.1)) (hf : Ideal.span {f,g} = e.ker.ideal U) :
    Ideal.span {CycleQ2LocalPrincipalRestriction.res h f,CycleQ2LocalPrincipalRestriction.res h g} =
      e.ker.ideal T := by
  rw [← e.ker.map_ideal (U := T) (V := U) h,← hf,Ideal.map_span]
  simp only [Set.image_insert_eq,Set.image_singleton]
  rfl

private theorem same_chart_agreement (U : Y.affineOpens) (hU : HasFrame q 4 U.1)
    (x : M) (hx : e (j x) ∈ U.1) (f g f' g' : Γ(Y,U.1))
    (hf : Ideal.span {f,g} = e.ker.ideal U) (hg : Ideal.span {f',g'} = e.ker.ideal U)
    (ho : IsAffineOpen (CycleQ2LocalPrincipalGysin.cover f g).X₁ ∧
      HasFrame q 4 (CycleQ2LocalPrincipalGysin.cover f g).X₁)
    (hn : IsAffineOpen (CycleQ2LocalPrincipalGysin.cover f' g').X₁ ∧
      HasFrame q 4 (CycleQ2LocalPrincipalGysin.cover f' g').X₁) :
    ∃ (V : Y.affineOpens) (h : V.1 ≤ U.1), e (j x) ∈ V.1 ∧
      restriction e h ≫ classOf e f g q 4 (locus_of_span e U f g hf) ho =
        restriction e h ≫ classOf e f' g' q 4 (locus_of_span e U f' g' hg) hn := by
  obtain ⟨a,b,c,d,he,he',hd⟩ := exists_matrix q e j U x hx f g f' g' hf hg
  subst f'
  subst g'
  exact CycleQ2ClosedGraphPivotRestriction.exists_comparison e q 4 U hU (e (j x))
    f g a b c d hd (locus_of_span e U f g hf) (locus_of_span e U _ _ hg)

private theorem restriction_comp {T V U : Y.Opens} (h : T ≤ V) (a : V ≤ U) :
    restriction e h ≫ restriction e a = restriction e (h.trans a) := by
  unfold CycleQ2SmoothTwoChartAgreement.restriction
  rw [← Functor.map_comp,CycleQ2RelativeSupportComposition.supportMap_comp]

/-- Coordinate independence for the original closure ideal, proved at
the original marked points. No smoothness of the discarded closure is
used. -/
theorem chart_agreement (A B : Chart q e) (x : M)
    (hxA : e (j x) ∈ A.U.1) (hxB : e (j x) ∈ B.U.1) :
    ∃ (T : Y.affineOpens) (a : T.1 ≤ A.U.1) (b : T.1 ≤ B.U.1),
      e (j x) ∈ T.1 ∧ restriction e a ≫ chartClass q e A =
        restriction e b ≫ chartClass q e B := by
  have hx : e (j x) ∈ A.U.1 ⊓ B.U.1 := ⟨hxA,hxB⟩
  obtain ⟨V',⟨hV,hfr⟩,hxV,hVW⟩ :=
    (Opens.isBasis_iff_nbhd.mp (CycleQ2FiniteExactAffineAtlas.isBasis q 4)) hx
  let V : Y.affineOpens := ⟨V',hV⟩
  have a : V.1 ≤ A.U.1 := hVW.trans inf_le_left
  have b : V.1 ≤ B.U.1 := hVW.trans inf_le_right
  let af := CycleQ2LocalPrincipalRestriction.res a A.f
  let ag := CycleQ2LocalPrincipalRestriction.res a A.g
  let bf := CycleQ2LocalPrincipalRestriction.res b B.f
  let bg := CycleQ2LocalPrincipalRestriction.res b B.g
  have ha := pairFrame q V hfr af ag
  have hb := pairFrame q V hfr bf bg
  obtain ⟨T,m,hxT,hcomp⟩ := same_chart_agreement q e j V hfr x hxV af ag bf bg
    (span_restrict e a A.f A.g A.equations) (span_restrict e b B.f B.g B.equations) ha hb
  have hrA := CycleQ2ClosedGraphRestriction.classOf_restrict e a A.f A.g
    (locus_of_span e A.U A.f A.g A.equations) q 4 (pairFrame q A.U A.frame A.f A.g) ha
  have hrB := CycleQ2ClosedGraphRestriction.classOf_restrict e b B.f B.g
    (locus_of_span e B.U B.f B.g B.equations) q 4 (pairFrame q B.U B.frame B.f B.g) hb
  refine ⟨T,m.trans a,m.trans b,hxT,?_⟩
  rw [← restriction_comp e m a,← restriction_comp e m b,Category.assoc,Category.assoc]
  exact (congrArg (fun v => restriction e m ≫ v) hrA).trans
    (hcomp.trans (congrArg (fun v => restriction e m ≫ v) hrB).symm)

open CycleQ2NoetherianSupport (res)

/-- Normalization is stated using every original ambient equation
chart inside the specified open. The target is the ambient complex. -/
def Normalized (O : Y.Opens) (z : E.obj (support e O) ⟶ (K q)⟦(4:ℤ)⟧) : Prop :=
  ∀ (A : Chart q e) (hA : A.U.1 ≤ O), res (complement e) hA z = chartClass q e A

variable [Algebra ℂ k]

theorem locally_below_four (O : Y.Opens) (hO : O ≤ goodOpen e j)
    (n : ℕ) (hn : n ≤ 3) (W : Y.Opens) (hW : W ≤ O)
    (z : E.obj (support e W) ⟶ (K q)⟦(n:ℤ)⟧) (y : Y) (hy : y ∈ W) :
    ∃ (T : Y.Opens) (h : T ≤ W), y ∈ T ∧ res (complement e) h z = 0 := by
  by_cases hy' : y ∈ Set.range e
  · obtain ⟨a,rfl⟩ := hy'
    obtain ⟨x,rfl⟩ := (source_mem_iff e j a).mp (hO (hW hy))
    obtain ⟨A,hxA,hAW⟩ := exists_chart q e j x W hy
    obtain ⟨T,h,hxT,w,hw,hf,hg⟩ := adapted_chart q e j A x hxA
    let F : CycleQ2IntrinsicFramedAffineSite.FramedOpen q 4 := ⟨T.1,T.2,⟨w,hw⟩⟩
    let : Smooth q := SmoothOfRelativeDimension.smooth 4 q
    let : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian q
    let : IsNoetherianRing Γ(Y,T.1) := IsLocallyNoetherian.component_noetherian T
    have hz := CycleQ2AdaptedChartPurity.below_four q F w hw (n:ℤ) (by omega)
    have hl : CycleQ2LocalPrincipalGysin.locus (w 0) (w 1) =
        (T.1 : Set Y) ∩ Set.range e := by
      rw [hf,hg]
      exact CycleQ2ClosedGraphRestriction.locus_restrict e h A.f A.g
        (locus_of_span e A.U A.f A.g A.equations)
    have he := CycleQ2ClosedGraphSupport.union_eq_complement e (w 0) (w 1) hl
    have hQ {V' W' T' : Y.Opens} (a : V' = W') (v : V' ≤ T') (w' : W' ≤ T') :
        CycleQ2RelativeOpenSupport.quotient v = CycleQ2RelativeOpenSupport.quotient w' := by
      subst W'
      rfl
    have hsrc : support e T.1 = CycleQ2LocalPrincipalGysin.supportedQuotient (w 0) (w 1) :=
      hQ he.symm _ _
    have hsmall : Subsingleton (E.obj (support e T.1) ⟶ (K q)⟦(n:ℤ)⟧) := by
      rw [hsrc]
      exact hz
    exact ⟨T.1,h.trans hAW,hxT,hsmall.allEq _ _⟩
  · refine ⟨W ⊓ complement e,inf_le_left,⟨hy,hy'⟩,?_⟩
    exact (E.map_isZero
      (CycleQ2SmoothTwoChartAgreement.isZero_support_off_graph e _ inf_le_right)).eq_of_src _ _

variable [NoetherianSpace Y]

/-- There is a normalized class on every open avoiding precisely the
original closure boundary. Its source remains a sheaf on the full
ambient fourfold. -/
theorem exists_normalized (O : Y.Opens) (hO : O ≤ goodOpen e j) :
    ∃ z : E.obj (support e O) ⟶ (K q)⟦(4:ℤ)⟧, Normalized q e O z := by
  let Ch := {A : Chart q e // A.U.1 ≤ O}
  let U : Option Ch → Y.Opens
    | none => O ⊓ complement e
    | some A => A.val.U.1
  have hU : ∀ n, U n ≤ O := by
    intro n
    cases n with
    | none => exact inf_le_left
    | some A => exact A.property
  let c : ∀ n, E.obj (support e (U n)) ⟶ (K q)⟦(4:ℤ)⟧ := fun n =>
    match n with
    | none => 0
    | some A => chartClass q e A.val
  have cover : ∀ y ∈ O, ∃ n, y ∈ U n := by
    intro y hy
    by_cases he : y ∈ Set.range e
    · obtain ⟨a,rfl⟩ := he
      obtain ⟨x,rfl⟩ := (source_mem_iff e j a).mp (hO hy)
      obtain ⟨A,hx,hA⟩ := exists_chart q e j x O hy
      exact ⟨some ⟨A,hA⟩,hx⟩
    · exact ⟨none,hy,he⟩
  have agree : ∀ n m (y : Y), y ∈ U n → y ∈ U m →
      ∃ (T : Y.Opens) (a : T ≤ U n) (b : T ≤ U m),
        y ∈ T ∧ res (complement e) a (c n) = res (complement e) b (c m) := by
    intro n m y hn hm
    by_cases he : y ∈ Set.range e
    · obtain ⟨a,rfl⟩ := he
      obtain ⟨x,rfl⟩ := (source_mem_iff e j a).mp (hO (hU n hn))
      cases n with
      | none => exact False.elim (hn.2 ⟨j x,rfl⟩)
      | some A =>
        cases m with
        | none => exact False.elim (hm.2 ⟨j x,rfl⟩)
        | some B =>
          obtain ⟨T,a,b,hx,hab⟩ := chart_agreement q e j A.val B.val x hn hm
          exact ⟨T.1,a,b,hx,hab⟩
    · refine ⟨(U n ⊓ U m) ⊓ complement e,inf_le_left.trans inf_le_left,
        inf_le_left.trans inf_le_right,⟨⟨hn,hm⟩,he⟩,?_⟩
      exact (E.map_isZero
        (CycleQ2SmoothTwoChartAgreement.isZero_support_off_graph e _ inf_le_right)).eq_of_src _ _
  obtain ⟨z,hz⟩ := CycleQ2SupportPurityDescent.glue_four_on q 4 (complement e) O
    (locally_below_four q e j O hO) U hU c cover agree
  exact ⟨z,fun A hA => hz (some ⟨A,hA⟩)⟩

/-- Normalization determines a unique class on any part of the original
boundary complement. -/
theorem normalized_unique (O : Y.Opens) (hO : O ≤ goodOpen e j)
    (a b : E.obj (support e O) ⟶ (K q)⟦(4:ℤ)⟧)
    (ha : Normalized q e O a) (hb : Normalized q e O b) : a = b := by
  apply CycleQ2NoetherianSupport.eq_of_local_on (complement e) (K q) 4 O
    (CycleQ2SupportPurityDescent.vanish_on q 4 (complement e) O 3
      (locally_below_four q e j O hO)) le_rfl
  intro y hy
  by_cases he : y ∈ Set.range e
  · obtain ⟨z,rfl⟩ := he
    obtain ⟨x,rfl⟩ := (source_mem_iff e j z).mp (hO hy)
    obtain ⟨A,hx,hA⟩ := exists_chart q e j x O hy
    exact ⟨A.U.1,hA,hx,(ha A hA).trans (hb A hA).symm⟩
  · refine ⟨O ⊓ complement e,inf_le_left,⟨hy,he⟩,?_⟩
    exact (E.map_isZero
      (CycleQ2SmoothTwoChartAgreement.isZero_support_off_graph e _ inf_le_right)).eq_of_src _ _

omit [Algebra ℂ k] [NoetherianSpace Y] in
theorem normalized_restrict {V O : Y.Opens} (h : V ≤ O)
    (z : E.obj (support e O) ⟶ (K q)⟦(4:ℤ)⟧) (hz : Normalized q e O z) :
    Normalized q e V (res (complement e) h z) := by
  intro A hA
  change restriction e hA ≫ (restriction e h ≫ z) = _
  rw [← Category.assoc,restriction_comp]
  exact hz A (hA.trans h)

theorem restriction_eq_normalized {V O : Y.Opens} (h : V ≤ O) (hO : O ≤ goodOpen e j)
    (z : E.obj (support e O) ⟶ (K q)⟦(4:ℤ)⟧)
    (w : E.obj (support e V) ⟶ (K q)⟦(4:ℤ)⟧)
    (hz : Normalized q e O z) (hw : Normalized q e V w) :
    res (complement e) h z = w :=
  normalized_unique q e j V (h.trans hO) _ w (normalized_restrict q e h z hz) hw

private theorem supportMap_isIso_of_eq {X : TopCat.{0}} {U V W : Opens X}
    (hUV : U = V) (hU : U ≤ W) (hV : V ≤ W) :
    IsIso (CycleQ2RelativeSupportRefinement.supportMap hU hV hUV.le le_rfl).τ₃ := by
  subst V
  have hid : (CycleQ2RelativeSupportRefinement.supportMap hU hU le_rfl le_rfl).τ₃ = 𝟙 _ := by
    apply (cancel_epi (CycleQ2RelativeOpenSupport.sequence hU).g).mp
    have hW : CycleQ2InjectiveCech.freeOpenMap (show W ≤ W from le_rfl) = 𝟙 _ :=
      (CycleQ2MayerVietorisRestriction.freeOpenSheaf (X := X)).map_id W
    change cokernel.π _ ≫ cokernel.desc _ (CycleQ2InjectiveCech.freeOpenMap
      (show W ≤ W from le_rfl) ≫ cokernel.π _) (by rw [hW,Category.id_comp,cokernel.condition]) =
        cokernel.π _ ≫ 𝟙 _
    rw [cokernel.π_desc,hW,Category.id_comp,Category.comp_id]
  change IsIso (CycleQ2RelativeSupportRefinement.supportMap hU hU le_rfl le_rfl).τ₃
  rw [hid]
  infer_instance

omit [NoetherianSpace Y] in
/-- A marked point detects this actual ambient supported class by its
logarithmic equation-chart restriction. -/
theorem normalized_ne_zero (O : Y.Opens) (x : M) (hx : e (j x) ∈ O)
    (z : E.obj (support e O) ⟶ (K q)⟦(4:ℤ)⟧) (hz : Normalized q e O z) : z ≠ 0 := by
  obtain ⟨A,hxA,hA⟩ := exists_chart q e j x O hx
  obtain ⟨T,h,hxT,w,hw,hf,hg⟩ := adapted_chart q e j A x hxA
  let W : CycleQ2IntrinsicFramedAffineSite.FramedOpen q 4 := ⟨T.1,T.2,⟨w,hw⟩⟩
  let : Smooth q := SmoothOfRelativeDimension.smooth 4 q
  let : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian q
  let : IsNoetherianRing Γ(Y,T.1) := IsLocallyNoetherian.component_noetherian T
  have hl : CycleQ2LocalPrincipalGysin.locus (w 0) (w 1) =
      (T.1 : Set Y) ∩ Set.range e := by
    rw [hf,hg]
    exact CycleQ2ClosedGraphRestriction.locus_restrict e h A.f A.g
      (locus_of_span e A.U A.f A.g A.equations)
  have hloc := CycleQ2LogDetection.localClass_ne_zero q W w hw (e (j x)) hxT
    (show e (j x) ∈ Y.zeroLocus {w 0,w 1} from
      (show e (j x) ∈ CycleQ2LocalPrincipalGysin.locus (w 0) (w 1) from
        hl ▸ ⟨hxT,⟨j x,rfl⟩⟩).2)
  let hpair := (CycleQ2FramedCechFormRow.intersection q 4 W (w 0) (w 1)).2
  have ht : classOf e (w 0) (w 1) q 4 hl hpair ≠ 0 := by
    unfold CycleQ2ClosedGraphSupport.classOf
    let he := CycleQ2ClosedGraphSupport.union_eq_complement e (w 0) (w 1) hl
    let m := (CycleQ2RelativeSupportRefinement.supportMap
      (show T.1 ⊓ complement e ≤ T.1 from inf_le_left)
      (CycleQ2LocalPrincipalGysin.union_le (w 0) (w 1)) he.ge le_rfl).τ₃
    let : IsIso m := supportMap_isIso_of_eq he.symm _ _
    intro hh
    exact hloc ((cancel_epi (E.map m)).mp (by simpa only [comp_zero] using hh))
  have span : Ideal.span {w 0,w 1} = e.ker.ideal T := by
    rw [hf,hg,← e.ker.map_ideal (U := T) (V := A.U) h,← A.equations,Ideal.map_span]
    simp only [Set.image_insert_eq,Set.image_singleton]
    rfl
  let B : Chart q e := ⟨T,w 0,w 1,⟨w,hw⟩,span⟩
  intro hz0
  have he := hz B (h.trans hA)
  rw [hz0] at he
  exact ht (he.symm.trans (show _ ≫ 0 = (0 : E.obj (support e B.U.1) ⟶ (K q)⟦(4:ℤ)⟧) from comp_zero))

theorem exists_goodOpen_normalized :
    ∃ z : E.obj (support e (goodOpen e j)) ⟶ (K q)⟦(4:ℤ)⟧,
      Normalized q e (goodOpen e j) z :=
  exists_normalized q e j (goodOpen e j) le_rfl

end CycleQ2MarkedOpenGysin

#print axioms CycleQ2MarkedOpenGysin.exists_goodOpen_normalized
#print axioms CycleQ2MarkedOpenGysin.restriction_eq_normalized
#print axioms CycleQ2MarkedOpenGysin.normalized_ne_zero

namespace CycleQ2ProperProductGysin

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open CycleQ2ProductCoefficients (productBase)
open CycleQ2ClosedGraphSupport (complement support)
open CycleQ2IntrinsicDeRhamSheaves (relativeDeRhamInt)
open CycleQ2InjectiveCech (AbSheaf)
open CycleQ2MarkedClosureOpen (goodOpen)
open CycleQ2MarkedOpenGysin (Normalized)

variable {k : Type} [Field k] [CharZero k] [Algebra ℂ k] {M Z C T : Scheme.{0}}
  (c : C ⟶ Spec (CommRingCat.of k)) (t : T ⟶ Spec (CommRingCat.of k))
  (e : Z ⟶ pullback c t) [IsClosedImmersion e] (j : M ⟶ Z) [IsOpenImmersion j]
  [IsProper c] [SmoothOfRelativeDimension 1 c] [SmoothOfRelativeDimension 3 t]
  [SmoothOfRelativeDimension 2 (j ≫ e ≫ productBase c t)]
  [NoetherianSpace ↑(pullback c t : Scheme.{0})]

local instance : SmoothOfRelativeDimension 4 (productBase c t) :=
  CycleQ2ProductFramedOpen.smooth_product c t 3

local instance ambientDerived (X : TopCat.{0}) : HasDerivedCategory.{1} (AbSheaf X) :=
  HasDerivedCategory.standard _

private abbrev ambientE := DerivedCategory.singleFunctor
  (AbSheaf (show TopCat from pullback c t)) 0
private abbrev ambientK : DerivedCategory.{1} (AbSheaf (show TopCat from pullback c t)) :=
  DerivedCategory.Q.obj (relativeDeRhamInt (productBase c t) 4)

/-- A normalized class is first constructed on the complement of the
original closure boundary in the fourfold. Its restriction to the old
product open is normalized in the same ambient complex. -/
theorem normalized_on_original_boundary_complement :
    ∃ z : (ambientE c t).obj (support e (goodOpen e j)) ⟶ (ambientK c t)⟦(4:ℤ)⟧,
      Normalized (productBase c t) e (goodOpen e j) z ∧
      Normalized (productBase c t) e (productOpen c t e j)
        (CycleQ2NoetherianSupport.res (complement e)
          (CycleQ2MarkedClosureOpen.productOpen_le j c t e) z) := by
  obtain ⟨z,hz⟩ := CycleQ2MarkedOpenGysin.exists_goodOpen_normalized (productBase c t) e j
  exact ⟨z,hz,CycleQ2MarkedOpenGysin.normalized_restrict (productBase c t) e
    (CycleQ2MarkedClosureOpen.productOpen_le j c t e) z hz⟩

/-- Independently constructed normalized representatives on the old
product open agree with the restriction of the original-boundary
class. Both sides have the actual ambient source and target. -/
theorem original_boundary_restrict_product
    (z : (ambientE c t).obj (support e (goodOpen e j)) ⟶ (ambientK c t)⟦(4:ℤ)⟧)
    (w : (ambientE c t).obj (support e (productOpen c t e j)) ⟶ (ambientK c t)⟦(4:ℤ)⟧)
    (hz : Normalized (productBase c t) e (goodOpen e j) z)
    (hw : Normalized (productBase c t) e (productOpen c t e j) w) :
    CycleQ2NoetherianSupport.res (complement e)
      (CycleQ2MarkedClosureOpen.productOpen_le j c t e) z = w :=
  CycleQ2MarkedOpenGysin.restriction_eq_normalized (productBase c t) e j
    (CycleQ2MarkedClosureOpen.productOpen_le j c t e) le_rfl z w hz hw

end CycleQ2ProperProductGysin

#print axioms CycleQ2ProperProductGysin.normalized_on_original_boundary_complement
#print axioms CycleQ2ProperProductGysin.original_boundary_restrict_product

/-! A closed boundary of dimension at most one has no supported de
Rham classes below degree six in the original smooth fourfold. This
uses the actual component and closed-point charts, followed by the
support filtration, rather than a projected-boundary purity premise. -/

namespace CycleQ2SmallBoundaryPurity

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open CycleQ2InjectiveCech (AbSheaf freeOpenMap)
open CycleQ2MayerVietorisRestriction (freeOpenSheaf)
open CycleQ2SupportMV (M)
open CycleQ2IntrinsicDeRhamSheaves (relativeDeRhamInt)
open CycleQ2SmallBoundaryStrata (Chart)
open CycleQ2NoetherianSupport (res)

variable {Y : Scheme.{0}}

def outside (B : Set Y) (hB : IsClosed B) : Y.Opens := ⟨Bᶜ,hB.isOpen_compl⟩

private theorem quotient_congr {A B W : Y.Opens} (h : A = B) (a : A ≤ W) (b : B ≤ W) :
    CycleQ2RelativeOpenSupport.quotient a = CycleQ2RelativeOpenSupport.quotient b := by
  subst B
  rfl

private theorem isZero_off (C W : Y.Opens) (h : W ≤ C) : IsZero (M C W) := by
  let a : W ⊓ C ≤ W := inf_le_left
  letI : IsIso (homOfLE a) := homOfLE_isIso_of_eq a (inf_eq_left.mpr h)
  letI : IsIso (freeOpenMap a) := inferInstanceAs (IsIso (freeOpenSheaf.map (homOfLE a)))
  exact isZero_cokernel_of_epi (freeOpenMap a)

variable {k : Type} [Field k] [CharZero k]
  (q : Y ⟶ Spec (CommRingCat.of k)) (B : Set Y) (hB : IsClosed B)

/-- Only the equality of the two actual closed supports on this open
is used to identify the free-open source quotients. -/
theorem source_eq_on_chart (A : Chart q B) (W : Y.Opens) (hW : W ≤ A.O) :
    letI := A.closed
    M (outside B hB) W = CycleQ2ClosedGraphSupport.support A.i W := by
  letI := A.closed
  have h : W ⊓ outside B hB = W ⊓ CycleQ2ClosedGraphSupport.complement A.i := by
    ext y
    change (y ∈ W ∧ y ∉ B) ↔ (y ∈ W ∧ y ∉ Set.range A.i)
    constructor
    · rintro ⟨hyW,hyB⟩
      refine ⟨hyW,fun hyI => hyB ?_⟩
      exact ((Set.ext_iff.mp A.support y).mpr ⟨hW hyW,hyI⟩).2
    · rintro ⟨hyW,hyI⟩
      refine ⟨hyW,fun hyB => hyI ?_⟩
      exact ((Set.ext_iff.mp A.support y).mp ⟨hW hyW,hyB⟩).2
  exact quotient_congr h _ _

variable [Algebra ℂ k] [SmoothOfRelativeDimension 4 q] [NoetherianSpace Y]

local instance ambientSmooth : Smooth q := SmoothOfRelativeDimension.smooth 4 q
local instance derived (X : TopCat.{0}) : HasDerivedCategory.{1} (AbSheaf X) :=
  HasDerivedCategory.standard _

private abbrev E := DerivedCategory.singleFunctor (AbSheaf (show TopCat from Y)) 0
private abbrev K : DerivedCategory.{1} (AbSheaf (show TopCat from Y)) :=
  DerivedCategory.Q.obj (relativeDeRhamInt q 4)

/-- Smooth boundary charts give vanishing on every subopen of their
union. All source sheaves and the target complex remain on Y. -/
theorem below_six_of_charts (O : Y.Opens)
    (hcharts : ∀ y ∈ O, y ∈ B → ∃ A : Chart q B, y ∈ A.O)
    (W : Y.Opens) (hW : W ≤ O) (n : ℤ) (hn : n < 6) :
    Subsingleton (E.obj (M (outside B hB) W) ⟶ (K q)⟦n⟧) := by
  apply subsingleton_of_forall_eq 0
  intro a
  cases n with
  | negSucc n => exact CycleQ2DeRhamNegative.eq_zero q 4 _ _ (by omega) a
  | ofNat n =>
    refine CycleQ2SupportPurityDescent.vanish_on q 4 (outside B hB) O n ?_ W hW a
    intro t ht V hV b y hy
    by_cases hyB : y ∈ B
    · obtain ⟨A,hyA⟩ := hcharts y (hV hy) hyB
      letI := A.closed
      letI := A.openImmersion
      letI := A.smooth
      let T := V ⊓ A.O
      have hz := CycleQ2SmoothSmallSupport.below_six_on q A.i A.j A.dimension
        A.dimension_le A.O A.inside T inf_le_right (t:ℤ) (by omega)
      have hs : Subsingleton (E.obj (M (outside B hB) T) ⟶ (K q)⟦(t:ℤ)⟧) := by
        rw [source_eq_on_chart q B hB A T inf_le_right]
        exact hz
      exact ⟨T,inf_le_left,⟨hy,hyA⟩,hs.allEq _ _⟩
    · refine ⟨V ⊓ outside B hB,inf_le_left,⟨hy,hyB⟩,?_⟩
      exact (E.map_isZero (isZero_off (outside B hB) _ inf_le_right)).eq_of_src _ _

/-- A finite set of closed points has the same low-degree vanishing,
using the actual residue-field point charts. -/
theorem finite_below_six (hfinite : B.Finite)
    (hclosed : ∀ x ∈ B, IsClosed ({x} : Set Y))
    (W : Y.Opens) (n : ℤ) (hn : n < 6) :
    Subsingleton (E.obj (M (outside B hB) W) ⟶ (K q)⟦n⟧) :=
  below_six_of_charts q B hB ⊤
    (fun x _ hx => CycleQ2SmallBoundaryStrata.chart_at_closed_point q B hfinite hclosed x hx)
    W le_top n hn

/-- Purity for the whole original closed boundary. The finite
residual support and the smooth component opens are joined by the
actual support short exact sequence. -/
theorem below_six (hdim : topologicalKrullDim B ≤ 1) (n : ℤ) (hn : n < 6) :
    Subsingleton (E.obj (M (outside B hB) ⊤) ⟶ (K q)⟦n⟧) := by
  obtain ⟨O,hfinite,hclosed,hcover⟩ :=
    CycleQ2SmallBoundaryStrata.exists_smooth_open_with_finite_residual q B hB hdim
  let C := outside B hB
  let V : Y.Opens := C ⊔ O
  let F : Set Y := B ∩ (O : Set Y)ᶜ
  have hF : IsClosed F := hB.inter O.isOpen.isClosed_compl
  have hV : Subsingleton (E.obj (M C V) ⟶ (K q)⟦n⟧) :=
    below_six_of_charts q B hB V (by
      intro y hy hyB
      have hyO : y ∈ O := by
        rcases hy with hyC | hyO
        · exact False.elim (hyC hyB)
        · exact hyO
      obtain ⟨A,_,hyA⟩ := hcover y hyO
      exact ⟨A,hyA⟩) V le_rfl n hn
  have hFV : outside F hF = V := by
    ext y
    change (¬ (y ∈ B ∧ y ∉ O)) ↔ (y ∉ B ∨ y ∈ O)
    tauto
  have hfin : Subsingleton (E.obj (M V ⊤) ⟶ (K q)⟦n⟧) := by
    rw [← hFV]
    exact finite_below_six q F hF hfinite hclosed ⊤ n hn
  have hinj := CycleQ2SupportFiltration.restriction_injective C
    (show V ≤ ⊤ from le_top) (K q) n (by
      intro b
      have hCV : C ⊔ V = V := sup_eq_right.mpr le_sup_left
      rw [hCV] at b
      exact hfin.allEq b 0)
  apply subsingleton_of_forall_eq 0
  intro a
  apply hinj
  exact hV.allEq _ _

end CycleQ2SmallBoundaryPurity

#print axioms CycleQ2SmallBoundaryPurity.finite_below_six
#print axioms CycleQ2SmallBoundaryPurity.below_six

namespace CycleQ2MarkedClosureExtension

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open CycleQ2InjectiveCech (AbSheaf)
open CycleQ2ClosedGraphSupport (complement support)
open CycleQ2IntrinsicDeRhamSheaves (relativeDeRhamInt)
open CycleQ2MarkedClosureOpen (boundary goodOpen)
open CycleQ2MarkedOpenGysin (Normalized)
open CycleQ2NoetherianSupport (res)

variable {k : Type} [Field k] [CharZero k] [Algebra ℂ k] {M Z Y : Scheme.{0}}
  (q : Y ⟶ Spec (CommRingCat.of k)) [SmoothOfRelativeDimension 4 q]
  [NoetherianSpace Y] (e : Z ⟶ Y) [IsClosedImmersion e]
  (j : M ⟶ Z) [IsOpenImmersion j]

local instance : HasDerivedCategory.{1} (AbSheaf (show TopCat from Y)) :=
  HasDerivedCategory.standard _

private abbrev E := DerivedCategory.singleFunctor (AbSheaf (show TopCat from Y)) 0
private abbrev K : DerivedCategory.{1} (AbSheaf (show TopCat from Y)) :=
  DerivedCategory.Q.obj (relativeDeRhamInt q 4)

/-- The two boundary vanishings are consequences of the dimension of
the original closure boundary, with no purity premise remaining. -/
theorem boundary_below_six (hdim : topologicalKrullDim ((Set.range j)ᶜ : Set Z) ≤ 1)
    (n : ℤ) (hn : n < 6) :
    Subsingleton (E.obj (CycleQ2SupportMV.M (goodOpen e j) ⊤) ⟶ (K q)⟦n⟧) :=
  CycleQ2SmallBoundaryPurity.below_six q (boundary e j)
    (CycleQ2MarkedClosureOpen.boundary_closed e j)
    (CycleQ2MarkedClosureOpen.boundary_dimension_le e j hdim) n hn

/-- The specified degree-four class on the complement of the
original boundary has a unique extension to the full ambient space. -/
theorem unique_extension (hdim : topologicalKrullDim ((Set.range j)ᶜ : Set Z) ≤ 1)
    (a : E.obj (support e (goodOpen e j)) ⟶ (K q)⟦(4:ℤ)⟧) :
    ∃! b : E.obj (support e ⊤) ⟶ (K q)⟦(4:ℤ)⟧,
      res (complement e) (show goodOpen e j ≤ ⊤ from le_top) b = a := by
  apply CycleQ2SupportFiltration.existsUnique_extension (complement e)
    (show goodOpen e j ≤ ⊤ from le_top) (K q) 4
  · intro b
    rw [CycleQ2MarkedClosureOpen.residual_complement] at b
    exact (boundary_below_six q e j hdim 4 (by decide)).allEq b 0
  · intro b
    rw [CycleQ2MarkedClosureOpen.residual_complement] at b
    exact (boundary_below_six q e j hdim 5 (by decide)).allEq b 0

variable [SmoothOfRelativeDimension 2 (j ≫ e ≫ q)]

/-- There is one normalized degree-four supported class on the full
closure in the full fourfold. Its normalization is tested on the
original marked open and uses the original ambient complex. -/
theorem exists_unique_normalized (hdim : topologicalKrullDim ((Set.range j)ᶜ : Set Z) ≤ 1) :
    ∃! b : E.obj (support e ⊤) ⟶ (K q)⟦(4:ℤ)⟧,
      Normalized q e (goodOpen e j)
        (res (complement e) (show goodOpen e j ≤ ⊤ from le_top) b) := by
  obtain ⟨a,ha⟩ := CycleQ2MarkedOpenGysin.exists_goodOpen_normalized q e j
  obtain ⟨b,hb,hunique⟩ := unique_extension q e j hdim a
  refine ⟨b,hb.symm ▸ ha,?_⟩
  intro c hc
  apply hunique c
  exact CycleQ2MarkedOpenGysin.normalized_unique q e j (goodOpen e j) le_rfl _ a hc ha

/-- A surviving marked point detects the full extended class through
its original logarithmic chart normalization. -/
theorem exists_nonzero_normalized (hdim : topologicalKrullDim ((Set.range j)ᶜ : Set Z) ≤ 1)
    (x : M) :
    ∃ b : E.obj (support e ⊤) ⟶ (K q)⟦(4:ℤ)⟧, b ≠ 0 ∧
      Normalized q e (goodOpen e j)
        (res (complement e) (show goodOpen e j ≤ ⊤ from le_top) b) := by
  obtain ⟨b,hb,_⟩ := exists_unique_normalized q e j hdim
  refine ⟨b,?_,hb⟩
  have hn := CycleQ2MarkedOpenGysin.normalized_ne_zero q e j (goodOpen e j) x
    (CycleQ2MarkedClosureOpen.marked_mem e j x)
    (res (complement e) (show goodOpen e j ≤ ⊤ from le_top) b) hb
  intro he
  apply hn
  rw [he]
  exact comp_zero

end CycleQ2MarkedClosureExtension

#print axioms CycleQ2MarkedClosureExtension.unique_extension
#print axioms CycleQ2MarkedClosureExtension.exists_unique_normalized
#print axioms CycleQ2MarkedClosureExtension.exists_nonzero_normalized

namespace CycleQ2SeedCompatibleClosureClass

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open CycleQ2LiteralIncidenceRelativeSpread CycleQ2LiteralIncidenceNormalizedSlice
open CycleQ2LiteralIncidenceRelativeCompletion CycleQ2LiteralIncidenceRelativeCorrespondence
open CycleQ2LiteralIncidenceGenericCorrespondence CycleQ2GenericSmoothCurveGraph
open CycleQ2IncidenceEtaleParameter (parameterScheme)
open CycleQ2IncidenceSeedFiberCover (seedBasePoint)
open CycleQ2NativeWeightedCover (ambientToField)
open CycleQ2ProductCoefficients (productBase)
open CycleQ2ClosedGraphSupport (complement)
open CycleQ2MarkedClosureOpen (goodOpen)
open CycleQ2MarkedOpenGysin (Normalized)
open CycleQ2MarkedGenericSurvives (SeedCompatible)
open CycleQ2SurvivingProductGysin (SupportedClass)
open CycleQ2InjectiveCech (AbSheaf freeOpenMap)

local instance derived (X : TopCat.{0}) : HasDerivedCategory.{1} (AbSheaf X) :=
  HasDerivedCategory.standard _

variable (V : parameterScheme.Opens) (t : Fin 3 → ℂ) {C D : Scheme.{0}}
  (r : C ⟶ Completion V) (c : C ⟶ Spec (CommRingCat.of genericField))
  (hc : r ≫ structureMap V = c ≫ genericPoint)
  (j : D ⟶ C) (a : D ⟶ Time toRaw V)
  (ha : j ≫ r = a ≫ CycleQ2LiteralIncidenceRelativeCompletion.inclusion V)

/-- The original closed image in the full curve product misses a
target neighborhood of the actual function point. No deletion of a
projected boundary is needed for this support statement. -/
theorem full_product_avoiding
    (hs : SmoothOfRelativeDimension 1 (curveMap toRaw V t)) :
    let m := fromTest V t r j a ha
    let b := m.imageι ≫ embeddingGeneric V t r c hc
    let π := pullback.snd c ambientToField
    ∃ A : genericAmbient.Opens,
      Set.range CycleQ2GenericGraphFunctionStalk.functionPoint ⊆ (A : Set genericAmbient) ∧
      π ⁻¹ᵁ A ≤ complement b := by
  let m := fromTest V t r j a ha
  let b := m.imageι ≫ embeddingGeneric V t r c hc
  let g := target V t r c hc
  let π := pullback.snd c ambientToField
  let A := CycleQ2GenericProperGraphSupport.complement V t
  have htime := timeMap_smooth toRaw V
  have hsurf : SmoothOfRelativeDimension 2 (CycleQ2GenericProperGraphOpen.surfaceStructure V t) :=
    smoothOfRelativeDimension_comp 1 1 _ _
  have hproper : IsProper (CycleQ2GenericProperGraphOpen.graphStructure V t) := by
    unfold CycleQ2GenericProperGraphOpen.graphStructure
    infer_instance
  have hprojection : b ≫ π = m.imageι ≫ g := by
    change (m.imageι ≫ embeddingGeneric V t r c hc) ≫ pullback.snd c ambientToField = _
    rw [Category.assoc,embeddingGeneric_toAmbient]
  refine ⟨A,?_,?_⟩
  · rintro _ ⟨x,rfl⟩
    exact CycleQ2GenericGraphFunctionStalk.functionPoint_mem hsurf hproper x
  · rintro _ hy ⟨z,rfl⟩
    have hpoint : π (b z) = g (m.imageι z) :=
      congrArg (fun f : m.image ⟶ genericAmbient => f z) hprojection
    have hy' : g (m.imageι z) ∈ A := hpoint ▸ hy
    exact hy' (target_in_original_support V t r c hc ⟨m.imageι z,rfl⟩)

/-- The original seed-compatible proper curve and marked point carry
a nonzero supported class on the full product with the generic
threefold. Its normalization is imposed only on the marked smooth
open, and its ordinary image vanishes near the original function point.
The complete closure is not assumed smooth. -/
theorem exists_full_product_class :
    ∃ (t : Fin 3 → ℂ) (ht : AlgebraicIndependent ℚ t)
      (V : parameterScheme.Opens) (hV : seedBasePoint ∈ V)
      (C : Scheme) (c : C ⟶ Spec (CommRingCat.of genericField))
      (r : C ⟶ Completion V) (hc : r ≫ structureMap V = c ≫ genericPoint)
      (D : Scheme) (j : D ⟶ C) (a : D ⟶ Time toRaw V)
      (ha : j ≫ r = a ≫ CycleQ2LiteralIncidenceRelativeCompletion.inclusion V),
      let m := fromTest V t r j a ha
      let g := target V t r c hc
      let b := m.imageι ≫ embeddingGeneric V t r c hc
      let q := productBase c ambientToField
      let π := pullback.snd c ambientToField
      let B := (m.imageι ≫ g) '' (Set.range m.toImage)ᶜ
      SeedCompatible t V hV c r j a ∧
      IsIntegral C ∧ IsProper c ∧ SmoothOfRelativeDimension 1 c ∧
      (∃ f : C ⟶ CycleQ2LaurentProjectiveLine.line genericField, IsFinite f ∧ IsDominant f ∧
        f ≫ CycleQ2ProjectiveLineStructure.structureMap genericField = c) ∧
      IsOpenImmersion j ∧ IsDominant j ∧ SmoothOfRelativeDimension 1 (curveMap toRaw V t) ∧
      IsProper (b ≫ π) ∧
      topologicalKrullDim ((Set.range m.toImage)ᶜ : Set m.image) ≤ 1 ∧
      topologicalKrullDim B ≤ 1 ∧
      (2 : WithBot ℕ∞) ≤ topologicalKrullDim (Set.range (m ≫ g)) ∧
      ∃ (hm : IsOpenImmersion m) (hb : IsClosedImmersion b)
        (h₄ : SmoothOfRelativeDimension 4 q),
        letI := hm
        letI := hb
        letI := h₄
        ∃ w : TestSurface V t a, g.QuasiFiniteAt (m w) ∧ g (m w) ∉ B ∧
          ∃ Γ : SupportedClass q b, Γ ≠ 0 ∧
            Normalized q b (goodOpen b m.toImage)
              (CycleQ2NoetherianSupport.res (complement b)
                (show goodOpen b m.toImage ≤ ⊤ from le_top) Γ) ∧
            ∃ A : genericAmbient.Opens,
              Set.range CycleQ2GenericGraphFunctionStalk.functionPoint ⊆ (A : Set genericAmbient) ∧
              π ⁻¹ᵁ A ≤ complement b ∧
              let E := DerivedCategory.singleFunctor (AbSheaf (show TopCat from genericProduct c)) 0
              E.map (freeOpenMap (show π ⁻¹ᵁ A ≤ ⊤ from le_top)) ≫
                E.map (CycleQ2SupportMV.π (complement b) ⊤) ≫ Γ = 0 := by
  obtain ⟨t,ht,V,hV,C,c,r,hc,D,j,a,ha,hCompatible,hC,hp,hc₁,hproj,hj,hjd,hs,
    _,hB,hd,w,hw,hout⟩ :=
    CycleQ2MarkedGenericSurvives.exists_compatible_marked_point_outside_projected_boundary
  letI : IsIntegral C := hC
  letI : IsProper c := hp
  letI : SmoothOfRelativeDimension 1 c := hc₁
  letI : IsOpenImmersion j := hj
  let m := fromTest V t r j a ha
  let G := embeddingGeneric V t r c hc
  let b := m.imageι ≫ G
  let q := productBase c ambientToField
  let π := pullback.snd c ambientToField
  letI : IsOpenImmersion m :=
    MorphismProperty.of_isPullback (test_square V t r j a ha) hj
  letI : IsClosedImmersion b := inferInstanceAs (IsClosedImmersion (m.imageι ≫ G))
  letI : SmoothOfRelativeDimension 3 ambientToField := CycleQ2NativeGenericSmooth.ambient_smooth
  letI : IsProper ambientToField := CycleQ2NativeWeightedCover.ambient_proper
  letI : NoetherianSpace (genericProduct c) :=
    CycleQ2LiteralIncidenceGenericModel.noetherian_of_proper q
  letI : SmoothOfRelativeDimension 4 q := CycleQ2ProductFramedOpen.smooth_product c ambientToField 3
  have h : m.toImage ≫ b ≫ q =
      pullback.fst a (curveMap toRaw V t) ≫ (j ≫ c) := by
    change m.toImage ≫ (m.imageι ≫ G) ≫ pullback.fst c ambientToField ≫ c = _
    calc
      _ = m ≫ G ≫ pullback.fst c ambientToField ≫ c := by
        simp only [Category.assoc,Scheme.Hom.toImage_imageι_assoc]
      _ = m ≫ toCurve V t r ≫ c := by
        rw [show G ≫ pullback.fst c ambientToField ≫ c = toCurve V t r ≫ c from
          embeddingGeneric_toCurve_assoc V t r c hc c]
      _ = _ := by rw [← Category.assoc m,← (test_square V t r j a ha).w,Category.assoc]
  letI : SmoothOfRelativeDimension 2 (m.toImage ≫ b ≫ q) := by
    rw [h]
    letI : SmoothOfRelativeDimension 1 (pullback.fst a (curveMap toRaw V t)) :=
      (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback
        (IsPullback.of_hasPullback a (curveMap toRaw V t)).flip hs
    letI : SmoothOfRelativeDimension 1 (j ≫ c) := smoothOfRelativeDimension_comp 0 1 j c
    exact smoothOfRelativeDimension_comp 1 1 _ _
  have hdim := (CycleQ2MarkedClosureBoundaryDimension.boundary_dimensions
    V t r c j a ha hc hs).1
  obtain ⟨Γ,hΓ,hNorm⟩ :=
    CycleQ2MarkedClosureExtension.exists_nonzero_normalized q b m.toImage hdim w
  obtain ⟨A,hpoint,hoff⟩ := full_product_avoiding V t r c hc j a ha hs
  refine ⟨t,ht,V,hV,C,c,r,hc,D,j,a,ha,hCompatible,hC,hp,hc₁,hproj,hj,hjd,hs,
    inferInstance,hdim,hB,hd,inferInstance,inferInstance,inferInstance,w,hw,hout,
    Γ,hΓ,hNorm,A,hpoint,hoff,?_⟩
  exact CycleQ2MarkedFunctionPoint.forget_off b (π ⁻¹ᵁ A) hoff Γ

end CycleQ2SeedCompatibleClosureClass

#print axioms CycleQ2SeedCompatibleClosureClass.full_product_avoiding
#print axioms CycleQ2SeedCompatibleClosureClass.exists_full_product_class
