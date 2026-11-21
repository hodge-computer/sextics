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

def HasNormalizedClass {Y S : Scheme.{0}} (p : Y ⟶ Spec (CommRingCat.of genericField))
    (i : S ⟶ Y) : Prop :=
  ∃ (h : IsClosedImmersion i) (hs : SmoothOfRelativeDimension 4 p),
    let := h
    let := hs
    ∃ z : (DerivedCategory.singleFunctor (AbSheaf (show TopCat from Y)) 0).obj (support i ⊤) ⟶
      (DerivedCategory.Q.obj (relativeDeRhamInt p 4))⟦(4:ℤ)⟧, ∀ n,
      CycleQ2NoetherianSupport.res (complement i) (show atlasOpen p i n ≤ ⊤ from le_top) z =
        atlasClass p i n

/-- The product with the whole proper curve carries the normalized logarithmic class
on a nonempty marked surface after deleting a target subset of dimension at most one. -/
theorem exists_surviving_product :
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
            (∃ s : S, g.QuasiFiniteAt (m (v s))) ∧ HasNormalizedClass (W.ι ≫ productBase c T) i := by
  obtain ⟨t,ht,V,hV,C,c,r,hc,D,j,a,ha,hC,hp,hc₁,hproj,hj,hjd,hs,_,hB,hd,z,hz,hout⟩ :=
    CycleQ2MarkedGenericSurvives.exists_marked_point_outside_projected_boundary
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
  refine ⟨t,ht,V,hV,C,c,r,hc,D,j,a,ha,hC,hp,hc₁,hproj,hB,hd,U,hU,product_square c T b m.toImage,
    _,i,v,?_,inferInstance,?_⟩
  · rw [show v ≫ m.toImage = (surfaceOpen c T b m.toImage).ι from toMarked_fac _ _ _ _]
    exact isPullback_morphismRestrict b W
  · have eqm : m.toImage ≫ b ≫ π = m ≫ g := by rw [hb,Scheme.Hom.toImage_imageι_assoc]
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
    exact ⟨hproper,⟨s,hsv.symm ▸ hz⟩,inferInstance,inferInstance,z',hlog⟩

end CycleQ2SurvivingProductGysin
#print axioms CycleQ2SurvivingProductGysin.exists_surviving_product
