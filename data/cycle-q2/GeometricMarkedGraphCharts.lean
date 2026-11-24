import Proposal.GeometricMarkedProductPivot
import Proposal.GeometricLocalGysinProjection
import Proposal.GeometricMarkedFundamentalClass

/-! The literal equation charts of the normalized supported class on the
proper parameter curve times the complement of the projected boundary.
The ordered equations on the surviving graph are the marked cubic and row.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CycleQ2MarkedPivotCover

open AlgebraicGeometry CategoryTheory MvPolynomial
open CycleQ2IncidenceEtaleParameter CycleQ2GeometricIncidenceProj CycleQ2RelativeCurveChart
  CycleQ2IncidenceDehomogenizedChart CycleQ2IncidenceUniversalChart CycleQ2IncidenceImageLine
  CycleQ2FirstOrderCurveChartFlat CycleQ2LiteralAbelJacobiSeedLiftChart CycleQ2FirstOrderCurveCharts
  CycleQ2IncidenceDensePivot CycleQ2MarkedPivotSource

attribute [local instance] CycleQ2RelativeCurveChartScheme.affineCurveChartCommRing
  CycleQ2RelativeCurveChart.pointSurfaceCommRing CycleQ2RelativeCurveChart.dehomogenizedCommRing

theorem exists_pivot_lift (t : Fin 3 → ℂ) (i : Fin 4)
    (z : Spec (CommRingCat.of (AffineCurveChart incidencePoint t i))) :
    ∃ (p : CycleQ2SegreCech.Chart) (b : Spec (CommRingCat.of (Curve t i p))),
      originalPivot t i p b = originalCurveChart t i z := by
  let f : PointSurface incidencePoint →+* AffineCurveChart incidencePoint t i :=
    (Ideal.Quotient.mk (affineSectionIdeal incidencePoint t i)).comp
      (surfaceToDehomogenized incidencePoint i)
  let q := PrimeSpectrum.comap f z
  let _ : q.asIdeal.IsPrime := q.isPrime
  have hcoord : ∃ j : Fin 5,
      CycleQ2IncidenceBasepointOpen.curveCoordinate (pointMap incidencePoint) j ∉ q.asIdeal := by
    refine ⟨i.castSucc, ?_⟩
    change Ideal.Quotient.mk (affineSectionIdeal incidencePoint t i)
      (surfaceToDehomogenized incidencePoint i (surfaceQuotient incidencePoint (X i.castSucc))) ∉ z.asIdeal
    rw [surfaceToDehomogenized_self, map_one]
    exact z.isPrime.one_notMem
  obtain ⟨j, k, h⟩ := CycleQ2IncidenceBasepointOpen.specialized_prime_pivot_cover
    (pointMap incidencePoint) CycleQ2EtaleIncidenceCurve.basepoint_unit q.asIdeal hcoord
  let p : CycleQ2SegreCech.Chart := (j,k)
  let v := toCurve incidencePoint t i p (rowPivot incidencePoint t i p)
  have hv : v ∉ z.asIdeal := by
    dsimp only [v]
    rw [toCurve_rowPivot]
    exact h
  have hlift : z ∈ Set.range (PrimeSpectrum.comap
      (algebraMap (AffineCurveChart incidencePoint t i) (Localization.Away v))) := by
    rw [PrimeSpectrum.localization_away_comap_range (Localization.Away v) v]
    exact hv
  obtain ⟨b, hb⟩ := hlift
  refine ⟨p, b, ?_⟩
  exact congrArg (fun a => originalCurveChart t i a) hb


open CycleQ2MonicGenericAmbientChartBaseChange CycleQ2LiteralIncidenceNormalizedSlice
  CycleQ2GenericSmoothCurveGraph CycleQ2LiteralIncidenceTimeCurve CycleQ2IncidenceTimeCurve
  CycleQ2LiteralIncidenceRelativeSpread CycleQ2LiteralIncidenceRelativeCylinder
  CycleQ2LiteralIncidenceCylinderMap CategoryTheory.Limits
open scoped TensorProduct

private lemma range_iso_comp {X Y Z : Scheme.{0}} (e : X ⟶ Y) [IsIso e] (k : Y ⟶ Z) :
    Set.range (e ≫ k) = Set.range k :=
  e.homeomorph.surjective.range_comp k

private theorem tensor_range {P R B : Type} [CommRing P] [CommRing R] [CommRing B]
    [Algebra P R] [Algebra P B] {X : Scheme} (f : X ⟶ Spec (CommRingCat.of P))
    (k : Spec (CommRingCat.of B) ⟶ X)
    (w : k ≫ f = Spec.map (CommRingCat.ofHom (algebraMap P B))) :
    Set.range (tensorInclusion (S := R) f k w) =
    (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap P R))) f) ⁻¹' Set.range k := by
  unfold tensorInclusion
  rw [range_iso_comp, range_iso_comp, range_iso_comp, Scheme.Pullback.range_fst]

private theorem mem_affine_chart {P R B : Type} [CommRing P] [CommRing R] [CommRing B]
    [Algebra P R] [Algebra P B] {X M D : Scheme} (f : X ⟶ Spec (CommRingCat.of P))
    (k : Spec (CommRingCat.of B) ⟶ X)
    (w : k ≫ f = Spec.map (CommRingCat.ofHom (algebraMap P B)))
    (m : M ⟶ D) (q : M ⟶ X) (u : Spec (CommRingCat.of R) ⟶ D)
    (s : IsPullback (pullback.fst u m) (pullback.snd u m ≫ q)
      (Spec.map (CommRingCat.ofHom (algebraMap P R))) f)
    (z : M) (hu : m z ∈ Set.range u) (hk : q z ∈ Set.range k) :
    z ∈ Set.range (tensorInclusion (S := R) f k w ≫ s.isoPullback.inv ≫ pullback.snd u m) := by
  obtain ⟨b,hb⟩ : z ∈ Set.range (pullback.snd u m) := by rwa [Scheme.Pullback.range_snd]
  have hbk : s.isoPullback.hom b ∈ Set.range (tensorInclusion (S := R) f k w) := by
    rw [tensor_range]
    change (s.isoPullback.hom ≫ pullback.snd _ _) b ∈ Set.range k
    rw [s.isoPullback_hom_snd]
    change q (pullback.snd u m b) ∈ Set.range k
    rwa [hb]
  obtain ⟨c,hc⟩ := hbk
  refine ⟨c, ?_⟩
  simp only [Scheme.Hom.comp_apply, hc]
  have hback : s.isoPullback.inv (s.isoPullback.hom b) = b :=
    congrArg (fun k : pullback u m ⟶ pullback u m => k b) s.isoPullback.hom_inv_id
  rwa [hback]

variable (t : Fin 3 → ℂ) {V : parameterScheme.Opens} {D : Scheme} (a : D ⟶ Time toRaw V)

theorem mem_chartToTest {R : CommRingCat} (u : Spec R ⟶ D) (z : TestSurface V t a)
    (i : Fin 4) (p : CycleQ2SegreCech.Chart)
    (hu : pullback.fst a (curveMap toRaw V t) z ∈ Set.range u)
    (hp : testOriginal t a z ∈ Set.range (originalPivot t i p)) :
    z ∈ Set.range (chartToTest t i p a u) := by
  let : Algebra P R := (actualParameters a u).toAlgebra
  unfold chartToTest
  apply mem_affine_chart
  · exact hu
  · exact hp

open CycleQ2RelativeConstantCurve MvPolynomial TopologicalSpace CycleQ2GeometricHodgeThreefold CycleQ2GeometricHodgeThreefoldIncidence
  CycleQ2RelativeCurveChartScheme CycleQ2LiteralAbelJacobiQCoordinates CycleQ2IncidenceFamilyContainment
  CycleQ2GenericSexticGradient CycleQ2IncidenceGenericPointSemantics CycleQ2IncidenceNormalForm

private theorem cover_iso {X Y : Scheme} (e : X ≅ Y)
    (U : Fin 4 → X.Opens) (V : Fin 4 → Y.Opens)
    (eqn : ∀ i, e.hom ⁻¹ᵁ V i = U i) (cover : iSup U = ⊤) (y : Y) :
    ∃ i, y ∈ V i := by
  obtain ⟨q,rfl⟩ := e.hom.homeomorph.surjective y
  have hq : q ∈ iSup U := by rw [cover]; trivial
  obtain ⟨i,hi⟩ := Opens.mem_iSup.mp hq
  refine ⟨i, ?_⟩
  change q ∈ e.hom ⁻¹ᵁ V i
  rwa [eqn]

set_option maxRecDepth 5000 in
private theorem originalChart_exists (t : Fin 3 → ℂ) (x : relativeCurve incidencePoint t) :
    ∃ i : Fin 4, x ∈ Set.range (originalCurveChart t i) := by
  have hv : IsUnit (sexticEval incidencePoint vertexCoefficient) := by
    change IsUnit ((aeval (pointSextic incidencePoint) : CoeffRing →ₐ[ℂ] ParameterAlgebra)
      (X fullSexticLeadingIndex))
    rw [aeval_X]
    exact (CycleQ2IncidenceImageLine.point_leading_units incidencePoint
      CycleQ2EtaleIncidenceCurve.leading_unit).2
  let s := relativeCurveToSurface incidencePoint t x
  let y := surfaceToThreefold incidencePoint s
  obtain ⟨i,hi⟩ := cover_iso (nativeIso incidencePoint) (coordinateOpen (sexticEval incidencePoint))
    (nativeOpen incidencePoint) (nativeIso_preimage incidencePoint)
    (coordinateOpens_cover _ hv) y
  refine ⟨i, (originalCurveChart t i).mem_opensRange.mp ?_⟩
  rw [originalCurveChart_opensRange, curveCoordinatePatch_eq_preimage]
  have hs : surfaceToThreefold incidencePoint ⁻¹ᵁ nativeOpen incidencePoint i =
      CycleQ2IncidenceDehomogenizedChart.familyCoordinatePatch incidencePoint i :=
    Proj.map_preimage_basicOpen _ _ (sexticX incidencePoint i)
  rw [← hs]
  exact hi

/-- Every marked test point belongs to a matrix pivot over an affine time neighborhood. -/
theorem exists_chart (z : TestSurface V t a) :
    ∃ (R : CommRingCat) (u : Spec R ⟶ D), IsOpenImmersion u ∧
      pullback.fst a (curveMap toRaw V t) z ∈ Set.range u ∧
      ∃ (i : Fin 4) (p : CycleQ2SegreCech.Chart), z ∈ Set.range (chartToTest t i p a u) := by
  let y := pullback.fst a (curveMap toRaw V t) z
  let c := D.affineOpenCover
  let j := c.idx y
  obtain ⟨i,b,hb⟩ := originalChart_exists t (testOriginal t a z)
  obtain ⟨p,b',hb'⟩ := exists_pivot_lift t i b
  exact ⟨c.X j, c.f j, inferInstance, c.covers y, i,p,mem_chartToTest t a (c.f j) z i p (c.covers y)
    ⟨b',hb'.trans hb⟩⟩

end CycleQ2MarkedPivotCover

namespace CycleQ2GraphChartRestriction

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

variable {X Y A L : Scheme.{0}} (f : X ⟶ Y) (g : L ⟶ X)
  [IsClosedImmersion f] [IsOpenImmersion g]

/-- Largest target open disjoint from the image of the discarded source. -/
def goodOpen : Y.Opens :=
  ⟨(f '' (Set.range g)ᶜ)ᶜ,
    (f.isClosedEmbedding.isClosedMap _ g.isOpenEmbedding.isOpen_range.isClosed_compl).isOpen_compl⟩

theorem mem_good (x : L) : f (g x) ∈ goodOpen f g := by
  rintro ⟨a,ha,he⟩
  exact ha ⟨x,(f.isClosedEmbedding.injective he).symm⟩

variable (h : L ⟶ A) (e : A ⟶ Y) [IsOpenImmersion e] (w : h ≫ e = g ≫ f)

include w

/-- The original presentation becomes Cartesian after any target test inside
the complement of the discarded part of the closed subscheme. -/
theorem isPullback_over {T : Scheme.{0}} (q : T ⟶ A)
    (hq : Set.range (q ≫ e) ⊆ (goodOpen f g : Set Y)) :
    IsPullback (pullback.fst q h) (pullback.snd q h ≫ g) (q ≫ e) f := by
  have inside (s : PullbackCone (q ≫ e) f) : Set.range s.snd ⊆ Set.range g := by
    rintro _ ⟨b,rfl⟩
    by_contra hn
    apply hq ⟨s.fst b,rfl⟩
    exact ⟨s.snd b,hn,(congrArg (fun a : s.pt ⟶ Y => a b) s.condition).symm⟩
  let lifted (s : PullbackCone (q ≫ e) f) := IsOpenImmersion.lift g s.snd (inside s)
  have lifted_fac (s : PullbackCone (q ≫ e) f) : lifted s ≫ g = s.snd :=
    IsOpenImmersion.lift_fac _ _ _
  have commute (s : PullbackCone (q ≫ e) f) : s.fst ≫ q = lifted s ≫ h := by
    apply (cancel_mono e).mp
    rw [Category.assoc, Category.assoc, w, ← Category.assoc (lifted s) g f, lifted_fac, s.condition]
  refine ⟨⟨?_⟩, ⟨PullbackCone.IsLimit.mk _
    (fun s => pullback.lift s.fst (lifted s) (commute s)) ?_ ?_ ?_⟩⟩
  · rw [← Category.assoc,pullback.condition,Category.assoc,w,Category.assoc]
  · intro s
    exact pullback.lift_fst ..
  · intro s
    exact (pullback.lift_snd_assoc ..).trans (lifted_fac s)
  · intro s m h₁ h₂
    apply pullback.hom_ext
    · exact h₁.trans (pullback.lift_fst ..).symm
    · apply (cancel_mono g).mp
      rw [Category.assoc,h₂,pullback.lift_snd,lifted_fac]

omit [IsOpenImmersion e] in
/-- In particular the target test can be any smaller open in the ambient
chart. Every point of the chosen source chart survives the initial shrinking. -/
theorem pivot_mem (x : L) : h x ∈ e ⁻¹ᵁ goodOpen f g := by
  change (h ≫ e) x ∈ goodOpen f g
  rw [w]
  exact mem_good f g x

theorem isPullback_on_open (T : A.Opens) (hT : T ≤ e ⁻¹ᵁ goodOpen f g) :
    IsPullback (pullback.fst T.ι h) (pullback.snd T.ι h ≫ g) (T.ι ≫ e) f :=
  isPullback_over f g h e w T.ι (by rintro _ ⟨t,rfl⟩; exact hT t.property)

/-- The ideal of the chart on every surviving affine open is exactly the
restriction of the defining ideal of the original closed immersion. -/
theorem ideal_on [IsClosedImmersion h] (T : A.affineOpens)
    (hT : T.1 ≤ e ⁻¹ᵁ goodOpen f g) :
    h.ker.ideal T = (f.ker.ideal ⟨e ''ᵁ T, T.2.image_of_isOpenImmersion e⟩).comap
      (e.appIso T).inv.hom := by
  let j := T.1.ι
  have hb := isPullback_on_open f g h e w T.1 hT
  have ker_eq : (pullback.fst j h).ker = f.ker.comap (j ≫ e) := by
    rw [← hb.isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso,
      Scheme.IdealSheafData.ker_fst_of_isClosedImmersion]
  have eq : h.ker.comap j = (f.ker.comap e).comap j := by
    rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion h j,
      ← Scheme.IdealSheafData.comap_comp]
    exact ker_eq
  let _ : IsAffine T.1.toScheme := T.2
  let W : T.1.toScheme.affineOpens := ⟨⊤, isAffineOpen_top _⟩
  have ev := congrArg (fun I : T.1.toScheme.IdealSheafData => I.ideal W) eq
  change (h.ker.comap j).ideal W = ((f.ker.comap e).comap j).ideal W at ev
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion h.ker j W,
    Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion (f.ker.comap e) j W] at ev
  have surv : Function.Surjective (j.appIso W).inv.hom :=
    (j.appIso W).symm.commRingCatIsoToRingEquiv.surjective
  have equality := Ideal.comap_injective_of_surjective (j.appIso W).inv.hom surv ev
  have hTW : (⟨j ''ᵁ W, W.2.image_of_isOpenImmersion j⟩ : A.affineOpens) = T := by
    apply Subtype.ext
    change T.1.ι ''ᵁ ⊤ = T.1
    rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Opens.opensRange_ι]
  have orig := (congrArg (fun V : A.affineOpens => h.ker.ideal V = (f.ker.comap e).ideal V)
    hTW).mp equality
  exact orig.trans (Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion f.ker e T)

end CycleQ2GraphChartRestriction


namespace CycleQ2PresentedGraphChart
open CategoryTheory AlgebraicGeometry TopologicalSpace
open CycleQ2SmoothSurfaceGysin (Chart)
open CycleQ2FiniteExactAffineAtlas (HasFrame)

variable {A B : CommRingCat.{0}} {X Y : Scheme.{0}} (i : X ⟶ Y)
  (j : Spec A ⟶ Y) [IsOpenImmersion j]

abbrev imagePart (T : (Spec A).affineOpens) : Y.affineOpens :=
  ⟨j ''ᵁ T.1,T.2.image_of_isOpenImmersion j⟩

def onPart (T : (Spec A).affineOpens) : A →+* Γ(Y,(imagePart j T).1) :=
  ((Scheme.ΓSpecIso A).inv ≫ (Spec A).presheaf.map (homOfLE (show T.1 ≤ ⊤ from le_top)).op ≫
    (j.appIso T.1).inv).hom

/-- The actual scalar equations continue to generate the immersion's ideal
on an arbitrary affine subopen where the restricted ideals agree. -/
theorem span_on_part (φ : A ⟶ B) (T : (Spec A).affineOpens)
    (f g : A) (h : RingHom.ker φ.hom = Ideal.span {f,g})
    (he : (Spec.map φ).ker.ideal T = (i.ker.ideal (imagePart j T)).comap (j.appIso T.1).inv.hom) :
    Ideal.span {onPart j T f,onPart j T g} = i.ker.ideal (imagePart j T) := by
  let W : (Spec A).affineOpens := ⟨⊤,isAffineOpen_top _⟩
  let ρ := (Spec A).presheaf.map (homOfLE (show T.1 ≤ ⊤ from le_top)).op
  let e := (Scheme.ΓSpecIso A).symm
  have htop : ((Spec.map φ).ker.ideal W).comap e.hom.hom = RingHom.ker φ.hom := by
    ext a
    rw [Scheme.Hom.ker_apply]
    change (Spec.map φ).appTop ((Scheme.ΓSpecIso A).inv a) = 0 ↔ φ a = 0
    have hn := ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality φ) a
    change (Scheme.ΓSpecIso B).inv (φ a) = (Spec.map φ).appTop ((Scheme.ΓSpecIso A).inv a) at hn
    rw [← hn]
    exact (Scheme.ΓSpecIso B).symm.commRingCatIsoToRingEquiv.map_eq_zero_iff
  have hspan : (Spec.map φ).ker.ideal W = Ideal.span {e.hom f,e.hom g} := by
    rw [← Ideal.map_comap_of_surjective e.hom.hom e.commRingCatIsoToRingEquiv.surjective ((Spec.map φ).ker.ideal W),htop,h,Ideal.map_span]
    simp only [Set.image_insert_eq,Set.image_singleton]
  have hT : (Spec.map φ).ker.ideal T = Ideal.span {ρ (e.hom f),ρ (e.hom g)} := by
    rw [← (Spec.map φ).ker.map_ideal (U := T) (V := W) (show T.1 ≤ ⊤ from le_top),hspan,Ideal.map_span]
    simp only [Set.image_insert_eq,Set.image_singleton]
    rfl
  let σ := (j.appIso T.1).symm
  change (Spec.map φ).ker.ideal T = (i.ker.ideal (imagePart j T)).comap σ.hom.hom at he
  rw [← Ideal.map_comap_of_surjective σ.hom.hom σ.commRingCatIsoToRingEquiv.surjective (i.ker.ideal (imagePart j T)),← he,hT,Ideal.map_span]
  simp only [Set.image_insert_eq,Set.image_singleton]
  rfl

open CategoryTheory.Limits
variable {k : Type} [Field k] {X' Y' : Scheme.{0}}
  (b : X' ⟶ Y') [IsClosedImmersion b] (o : Y ⟶ Y') [IsOpenImmersion o]
  (q : Y ⟶ Spec (CommRingCat.of k)) [SmoothOfRelativeDimension 4 q]

/-- Pull both scalar equations onto an exact frame in the actual open product.
The square identifies the restricted surface with the pullback of the closure. -/
theorem chart_on_open (v : X ⟶ X') (sq : IsPullback i v o b)
    (U : Y'.affineOpens) (f g : Γ(Y',U.1))
    (h : Ideal.span {f,g} = b.ker.ideal U) (y : Y)
    (hy : o y ∈ U.1) (O : Y.Opens) (hyO : y ∈ O) :
    ∃ (G : Chart q i) (e : o ''ᵁ G.U.1 ≤ U.1), y ∈ G.U.1 ∧ G.U.1 ≤ O ∧
      let ρ := Y'.presheaf.map (homOfLE e).op ≫ (o.appIso G.U.1).hom
      G.f = ρ f ∧ G.g = ρ g := by
  have hloc : y ∈ (o ⁻¹ᵁ U.1) ⊓ O := ⟨hy,hyO⟩
  obtain ⟨T,hT,hyT,hle⟩ := (Opens.isBasis_iff_nbhd.mp (CycleQ2FiniteExactAffineAtlas.isBasis q 4)) hloc
  let V : Y.affineOpens := ⟨T,hT.1⟩
  let V' : Y'.affineOpens := ⟨o ''ᵁ T,hT.1.image_of_isOpenImmersion o⟩
  have e : V'.1 ≤ U.1 := by
    rintro _ ⟨y',hy',rfl⟩
    exact (hle hy').1
  let α := Y'.presheaf.map (homOfLE e).op
  let E := o.appIso T
  have hV' : b.ker.ideal V' = Ideal.span {α f,α g} := by
    rw [← b.ker.map_ideal (U := V') (V := U) e,← h,Ideal.map_span]
    simp only [Set.image_insert_eq,Set.image_singleton]
    rfl
  have hk : i.ker = b.ker.comap o := by
    rw [← sq.isoPullback_hom_fst,Scheme.Hom.ker_comp_of_isIso,Scheme.IdealSheafData.ker_fst_of_isClosedImmersion]
  have hV : i.ker.ideal V = Ideal.span {E.hom (α f),E.hom (α g)} := by
    rw [hk,Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion]
    change (b.ker.ideal V').comap E.commRingCatIsoToRingEquiv.symm = _
    rw [Ideal.comap_symm,hV',Ideal.map_span]
    simp only [Set.image_insert_eq,Set.image_singleton]
    rfl
  exact ⟨⟨V,_,_,hT.2,hV.symm⟩,e,hyT,hle.trans inf_le_right,rfl,rfl⟩

local instance derived (Y : TopCat.{0}) : HasDerivedCategory.{1} (CycleQ2InjectiveCech.AbSheaf Y) :=
  HasDerivedCategory.standard _

/-- Both framing equations come from the indicated elements of the affine
presentation and give the prescribed restriction of the global supported class. -/
def DisplaysAt {X₁ Y₀ Y₁ : Scheme.{0}} (o : Y₁ ⟶ Y₀) [IsOpenImmersion o]
    (incl : X₁ ⟶ Y₁) [IsClosedImmersion incl]
    (π : Y₁ ⟶ Spec (CommRingCat.of CycleQ2LiteralIncidenceGenericCorrespondence.genericField))
    [SmoothOfRelativeDimension 4 π] (z : CycleQ2SurvivingProductGysin.SupportedClass π incl)
    (e₀ : Spec A ⟶ Y₀) [IsOpenImmersion e₀] (f g : A) (x : Spec A) (y : Y₁) (N : Y₁.Opens) : Prop :=
    ∃ (T : (Spec A).affineOpens) (G : Chart π incl) (e : o ''ᵁ G.U.1 ≤ (imagePart e₀ T).1),
      x ∈ T.1 ∧ y ∈ G.U.1 ∧ G.U.1 ≤ N ∧
      let ρ := Y₀.presheaf.map (homOfLE e).op ≫ (o.appIso G.U.1).hom
      G.f = ρ (onPart e₀ T f) ∧ G.g = ρ (onPart e₀ T g) ∧
      CycleQ2NoetherianSupport.res (CycleQ2ClosedGraphSupport.complement incl)
        (show G.U.1 ≤ ⊤ from le_top) z = CycleQ2SmoothSurfaceGysin.chartClass π incl G ∧
      ∃ u : Fin 4 → Γ(Y₁,G.U.1), u 0 = G.f ∧ u 1 = G.g ∧
        CycleQ2LocalGysinProjection.HasNativeProjection π incl ⟨G.U.1,G.U.2,G.frame⟩ u

/-- Apply the local presentation to the normalized class on the restricted
product. Both equations of the returned chart are the literal restrictions
of the input scalars, in the prescribed order. -/
theorem normalized_on_presented_open
    {X₀ X₁ Y₀ Y₁ : Scheme.{0}}
    (b : X₀ ⟶ Y₀) [IsClosedImmersion b] (o : Y₁ ⟶ Y₀) [IsOpenImmersion o]
    (incl : X₁ ⟶ Y₁) [IsClosedImmersion incl] (v : X₁ ⟶ X₀) (sq : IsPullback incl v o b)
    (π : Y₁ ⟶ Spec (CommRingCat.of CycleQ2LiteralIncidenceGenericCorrespondence.genericField))
    [SmoothOfRelativeDimension 4 π] [SmoothOfRelativeDimension 2 (incl ≫ π)]
    (z : CycleQ2SurvivingProductGysin.SupportedClass π incl)
    (hn : CycleQ2SurvivingProductGysin.IsNormalized π incl z)
    (e₀ : Spec A ⟶ Y₀) [IsOpenImmersion e₀] (l : Spec B ⟶ X₀) [IsOpenImmersion l]
    (φ : A ⟶ B) [IsClosedImmersion (Spec.map φ)]
    (w : Spec.map φ ≫ e₀ = l ≫ b) (f g : A) (hk : RingHom.ker φ.hom = Ideal.span {f,g})
    (x : Spec B) (s : X₁) (hy : o (incl s) = e₀ (Spec.map φ x))
    (N : Y₁.Opens) (hyN : incl s ∈ N) :
    DisplaysAt o incl π z e₀ f g (Spec.map φ x) (incl s) N := by
  let y := incl s
  have hx := CycleQ2GraphChartRestriction.pivot_mem b l (Spec.map φ) e₀ w x
  obtain ⟨T,hT,hxT,hle⟩ := (Opens.isBasis_iff_nbhd.mp (Spec A).isBasis_affineOpens) hx
  let V : (Spec A).affineOpens := ⟨T,hT⟩
  have hspan := span_on_part b e₀ φ V f g hk (CycleQ2GraphChartRestriction.ideal_on b l (Spec.map φ) e₀ w V hle)
  have hyV : o y ∈ (imagePart e₀ V).1 := hy ▸ ⟨_,hxT,rfl⟩
  obtain ⟨G,e,hyG,hGN,hf,hg⟩ := chart_on_open incl b o π v sq (imagePart e₀ V) _ _ hspan y hyV N hyN
  obtain ⟨B',hBG,hyB,hfB,hgB,hclass,hres⟩ :=
    CycleQ2LocalGysinProjection.normalized_chart_projection π incl (incl ≫ π) rfl G s hyG z hn
  let e' := (o.image_mono hBG).trans e
  have natural :
      (Y₀.presheaf.map (homOfLE e).op ≫ (o.appIso G.U.1).hom) ≫
          Y₁.presheaf.map (homOfLE hBG).op =
        Y₀.presheaf.map (homOfLE e').op ≫ (o.appIso B'.U.1).hom := by
    rw [Category.assoc,← o.appIso_hom_naturality,← Category.assoc,← Y₀.presheaf.map_comp]
    rfl
  exact ⟨V,B',e',hxT,hyB,hBG.trans hGN,
    hfB.trans ((congrArg (Y₁.presheaf.map (homOfLE hBG).op) hf).trans
      (ConcreteCategory.congr_hom natural (onPart e₀ V f))),
    hgB.trans ((congrArg (Y₁.presheaf.map (homOfLE hBG).op) hg).trans
      (ConcreteCategory.congr_hom natural (onPart e₀ V g))),hclass,hres⟩

end CycleQ2PresentedGraphChart

namespace CycleQ2MarkedGraphChartApplication
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open CycleQ2IncidenceEtaleParameter (parameterScheme)
open CycleQ2LiteralIncidenceRelativeSpread (Time)
open CycleQ2LiteralIncidenceNormalizedSlice (toRaw)
open CycleQ2LiteralIncidenceGenericCorrespondence (genericPoint genericField)
open CycleQ2LiteralIncidenceRelativeCompletion (Completion structureMap inclusion)
open CycleQ2NativeWeightedCover (ambientToField)
open CycleQ2ProductCoefficients (productBase)
open CycleQ2GenericSmoothCurveGraph (TestSurface fromTest test_square embeddingGeneric Graph toCurve genericProduct)
open CycleQ2IncidenceDensePivot (P Ambient Curve cubic row inclusionMap inclusion_surjective actual_test_kernel actualParameters)
open CycleQ2MarkedPivotSource (chartToTest)
open CycleQ2MarkedPivotRing (inActualProduct restriction)
open CycleQ2SurvivingProductGysin (SupportedClass IsNormalized)
open CycleQ2PresentedGraphChart (DisplaysAt)
open scoped TensorProduct

variable {V : parameterScheme.Opens} {C D S : Scheme.{0}} {R : CommRingCat.{0}}
  (t : Fin 3 → ℂ) (r : C ⟶ Completion V) (c : C ⟶ Spec (CommRingCat.of genericField)) [IsProper c]
  (hc : r ≫ structureMap V = c ≫ genericPoint) (j : D ⟶ C) [IsOpenImmersion j] (a : D ⟶ Time toRaw V)
  (ha : j ≫ r = a ≫ inclusion V) (u : Spec R ⟶ D) [IsOpenImmersion u]
  (i : Fin 4) (p : CycleQ2SegreCech.Chart)

variable {Y : Scheme.{0}} (o : Y ⟶ genericProduct c) [IsOpenImmersion o]
  (q : Y ⟶ Spec (CommRingCat.of genericField)) (incl : S ⟶ Y) [IsClosedImmersion incl]
  (v : S ⟶ TestSurface V t a)
  (sq : IsPullback incl (v ≫ (fromTest V t r j a ha).toImage) o
    ((fromTest V t r j a ha).imageι ≫ embeddingGeneric V t r c hc))
  [SmoothOfRelativeDimension 4 q]
  [SmoothOfRelativeDimension 2 (incl ≫ q)]

include sq in
private theorem displayed_on_pivot (z : SupportedClass q incl)
    (hz : IsNormalized q incl z)
    (s : S) (x : Spec (CommRingCat.of
      (letI : Algebra P R := (actualParameters a u).toAlgebra; R ⊗[P] Curve t i p)))
    (hx : chartToTest t i p a u x = v s) (N : Y.Opens) (hN : incl s ∈ N) :
    letI : Algebra P R := (actualParameters a u).toAlgebra
    let right : Ambient i p →ₐ[P] R ⊗[P] Ambient i p := Algebra.TensorProduct.includeRight
    DisplaysAt o incl q z (inActualProduct r c hc j a ha u i p)
      (right (cubic i p)) (right (row t i p)) (Spec.map (CommRingCat.ofHom (restriction a u t i p)) x)
      (incl s) N := by
  let : Algebra P R := (actualParameters a u).toAlgebra
  let m := fromTest V t r j a ha
  let b := m.imageι ≫ embeddingGeneric V t r c hc
  let e := inActualProduct r c hc j a ha u i p
  let l := chartToTest t i p a u ≫ m.toImage
  let φ := CommRingCat.ofHom (restriction a u t i p)
  let : IsOpenImmersion m := MorphismProperty.of_isPullback (test_square V t r j a ha) inferInstance
  let : NoetherianSpace (Graph V t r) :=
    CycleQ2LiteralIncidenceGenericModel.noetherian_of_proper (toCurve V t r ≫ c)
  let : NoetherianSpace (TestSurface V t a) := m.isOpenEmbedding.isInducing.noetherianSpace
  let : IsClosedImmersion (Spec.map φ) :=
    IsClosedImmersion.spec_of_surjective φ (CycleQ2MarkedPivotRing.restriction_surjective a u t i p)
  have w : Spec.map φ ≫ e = l ≫ b := CycleQ2MarkedPivotRing.commutes r c hc j a ha u t i p
  have hxy : o (incl s) = e ((Spec.map φ) x) := by
    calc
      _ = b (m.toImage (v s)) := congrArg (fun f => f s) sq.w
      _ = b (m.toImage (chartToTest t i p a u x)) := by rw [hx]
      _ = _ := (congrArg (fun f => f x) w).symm
  exact CycleQ2PresentedGraphChart.normalized_on_presented_open b o incl (v ≫ m.toImage) sq
    q z hz e l φ w _ _ (actual_test_kernel t i p a u) x s hxy N hN

/-- Every neighborhood of a surviving surface point contains a chart on
which the given normalized class uses the original two incidence equations. -/
def HasMarkedCharts (z : SupportedClass q incl) : Prop :=
  ∀ (s : S) (N : Y.Opens), incl s ∈ N →
    ∃ (R₀ : CommRingCat) (u₀ : Spec R₀ ⟶ D) (hu : IsOpenImmersion u₀),
      let _ := hu
      letI : Algebra P R₀ := (actualParameters a u₀).toAlgebra
      ∃ (i₀ : Fin 4) (p₀ : CycleQ2SegreCech.Chart)
        (x : Spec (CommRingCat.of (R₀ ⊗[P] Curve t i₀ p₀))),
        chartToTest t i₀ p₀ a u₀ x = v s ∧
        let right : Ambient i₀ p₀ →ₐ[P] R₀ ⊗[P] Ambient i₀ p₀ := Algebra.TensorProduct.includeRight
        DisplaysAt o incl q z
          (inActualProduct r c hc j a ha u₀ i₀ p₀) (right (cubic i₀ p₀)) (right (row t i₀ p₀))
          (Spec.map (CommRingCat.ofHom (restriction a u₀ t i₀ p₀)) x) (incl s) N

include sq in
theorem has_marked_charts (z : SupportedClass q incl)
    (hz : IsNormalized q incl z) :
    HasMarkedCharts t r c hc j a ha o q incl v z := by
  intro s N hN
  obtain ⟨R₀,u₀,hu,_,i₀,p₀,x,hx⟩ := CycleQ2MarkedPivotCover.exists_chart t a (v s)
  let _ := hu
  exact ⟨R₀,u₀,hu,i₀,p₀,x,hx,displayed_on_pivot t r c hc j a ha u₀ i₀ p₀ o q incl v sq z hz s x hx N hN⟩

open CycleQ2LiteralIncidenceGenericCorrespondence (genericAmbient)
open CycleQ2IncidenceSeedFiberCover (seedBasePoint)
open CycleQ2GenericSmoothCurveGraph (target)
open CycleQ2InjectiveCech (AbSheaf)
open CycleQ2ClosedGraphSupport (complement)
local instance derived (T : TopCat.{0}) : HasDerivedCategory.{1} (AbSheaf T) :=
  HasDerivedCategory.standard _

/-- The nonzero normalized proper-graph class with its traced seed, actual
equations at every surviving point, and vanishing near the function point. -/
theorem exists_presented_class :
    ∃ (t : Fin 3 → ℂ), AlgebraicIndependent ℚ t ∧
      ∃ (V : parameterScheme.Opens) (hV : seedBasePoint ∈ V) (C : Scheme)
        (c : C ⟶ Spec (CommRingCat.of genericField)) (r : C ⟶ Completion V)
        (hc : r ≫ structureMap V = c ≫ genericPoint) (D : Scheme) (j : D ⟶ C)
        (a : D ⟶ Time toRaw V) (ha : j ≫ r = a ≫ inclusion V),
          CycleQ2MarkedGenericSurvives.SeedCompatible t V hV c r j a ∧
          IsIntegral C ∧ SmoothOfRelativeDimension 1 c ∧ IsProper c ∧
          ∃ (hj : IsOpenImmersion j),
          let _ := hj
          let m := fromTest V t r j a ha
          let g := target V t r c hc
          let b := m.imageι ≫ embeddingGeneric V t r c hc
          ∃ U : genericAmbient.Opens, (U : Set genericAmbient) = ((m.imageι ≫ g) '' (Set.range m.toImage)ᶜ)ᶜ ∧
          let W := pullback.snd c ambientToField ⁻¹ᵁ U
          let q := W.ι ≫ productBase c ambientToField
          ∃ (S : Scheme) (incl : S ⟶ W.toScheme) (v : S ⟶ TestSurface V t a),
            IsPullback incl (v ≫ m.toImage) W.ι b ∧ IsOpenImmersion v ∧
            IsProper (incl ≫ (pullback.snd c ambientToField ∣_ U)) ∧
            (∃ s : S, g.QuasiFiniteAt (m (v s))) ∧
            ∃ (hi : IsClosedImmersion incl) (h₄ : SmoothOfRelativeDimension 4 q),
            let _ := hi
            let _ := h₄
            ∃ z : SupportedClass q incl, z ≠ 0 ∧ IsNormalized q incl z ∧
              HasMarkedCharts t r c hc j a ha W.ι q incl v z ∧
              ∃ A : genericAmbient.Opens, A ≤ U ∧
                Set.range CycleQ2GenericGraphFunctionStalk.functionPoint ⊆ (A : Set genericAmbient) ∧
                let E := DerivedCategory.singleFunctor (AbSheaf (show TopCat from W.toScheme)) 0
                E.map (CycleQ2InjectiveCech.freeOpenMap
                  (show (W.ι ≫ pullback.snd c ambientToField) ⁻¹ᵁ A ≤ ⊤ from le_top)) ≫
                  E.map (CycleQ2SupportMV.π (complement incl) ⊤) ≫ z = 0 := by
  obtain ⟨t,ht,V,_,C,c,r,hc,D,j,a,ha,hC,hp,hc₁,_,_,_,U,hU,_,S,i,v,sq,hv,hproper,
    hpoint,⟨hV,hseed⟩,⟨hj,hs⟩,hi,h₄,z,hnz,hn,hvan⟩ :=
    CycleQ2SurvivingProductGysin.exists_seed_compatible_framed_product
  let _ := hp
  let _ := hj
  let _ := hi
  let _ := h₄
  let _ := hs
  exact ⟨t,ht,V,hV,C,c,r,hc,D,j,a,ha,hseed,hC,hc₁,hp,hj,U,hU,S,i,v,sq,hv,hproper,hpoint,
    hi,h₄,z,hnz,hn,has_marked_charts t r c hc j a ha _ _ i v sq z hn,hvan⟩

end CycleQ2MarkedGraphChartApplication

#print axioms CycleQ2MarkedGraphChartApplication.exists_presented_class
