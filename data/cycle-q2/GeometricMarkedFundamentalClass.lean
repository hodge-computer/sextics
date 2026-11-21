import Proposal.GeometricSupportedClassNonvanishing
import Proposal.GeometricSmoothSurfaceGysin
import Proposal.GeometricMarkedProjectionSurvives

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
