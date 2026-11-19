import Proposal.GeometricLiteralNonzeroSweptRestriction
import Proposal.GeometricLiteralAbelJacobiTimeProjection
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Proposal.GeometricLiteralIncidenceCylinderMap
import Proposal.GeometricIncidenceSeedFiber
import Proposal.GeometricAffineProjectiveCompletionChart
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.Noetherian
import Proposal.GeometricIncidenceProjectiveProper
import Proposal.GeometricLiteralTimeFamilyEmbedding
import Proposal.GeometricImmersionImageClosure
import Mathlib.CategoryTheory.Comma.Over.Pullback
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected

/-!
# The actual incidence correspondence over the normalized coefficient base

Base change carries the smooth marked time family over the monic weighted
sextics. Its original projection to the threefold extends through a proper
graph closure over a proper time completion. These models retain the
first-order marked curve, and the graph has a nonempty proper generic
fiber over the same coefficient field as the universal weighted chart.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false

section

/-!
# Spreading the marked incidence correspondence over sextic coefficients

A neighborhood of the marked point in the original incidence scheme carries the
proper projective curve family. Its time direction is smooth over all sextic
coefficients. Base change to any irreducible coefficient scheme through the marked
sextic therefore gives a smooth relative surface with dense open image.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/


noncomputable section
namespace CycleQ2LiteralIncidenceRelativeSpread

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
  CycleQ2IncidenceEtaleParameter CycleQ2IncidenceTimeCurve
  CycleQ2LiteralIncidenceTimeCurve CycleQ2RelativeConstantCurve
  CycleQ2IncidenceSeedFiberCover CycleQ2LiteralAbelJacobiTimeFamily

variable {B : Scheme} (i : B ⟶ sexticBase) (V : parameterScheme.Opens)

abbrev Time := pullback i (V.ι ≫ parameterToSextics)

def timeMap : Time i V ⟶ B := pullback.fst _ _

abbrev Surface (t : Fin 3 → ℂ) :=
  pullback (pullback.snd i (V.ι ≫ parameterToSextics)) ((relativeCurveToBase incidencePoint t) ∣_ V)

def curveMap (t : Fin 3 → ℂ) : Surface i V t ⟶ Time i V := pullback.fst _ _

variable (b : Spec (CommRingCat.of ℂ) ⟶ B) (hb : b ≫ i = seedSextic)

/-- The fixed-sextic time curve maps into the spread over its original marked coefficient. -/
def fixedToTime : (timeOpen V).toScheme ⟶ Time i V :=
  pullback.lift ((timeOpen V).ι ≫ toComplex ≫ b) (toIncidence ∣_ V) <| by
    simp only [Category.assoc, hb, ← Category.assoc (toIncidence ∣_ V), morphismRestrict_ι]
    simpa only [Category.assoc, timeOpen, toComplex, toIncidence] using congrArg (fun f => (timeOpen V).ι ≫ f)
      (pullback.condition (f := seedSextic) (g := parameterToSextics))

@[reassoc (attr := simp)] theorem fixedToTime_fst :
    fixedToTime i V b hb ≫ timeMap i V = (timeOpen V).ι ≫ toComplex ≫ b := pullback.lift_fst _ _ _

@[reassoc (attr := simp)] theorem fixedToTime_snd :
    fixedToTime i V b hb ≫ pullback.snd i (V.ι ≫ parameterToSextics) = toIncidence ∣_ V :=
  pullback.lift_snd _ _ _

theorem timeMap_smooth : SmoothOfRelativeDimension 1 (timeMap i V) := by
  have := parameterToSextics_smooth_relative_one
  exact (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback
    (IsPullback.of_hasPullback i (V.ι ≫ parameterToSextics)).flip
    (smoothOfRelativeDimension_comp 0 1 V.ι parameterToSextics)

/-- Every nonempty Zariski neighborhood in the time family meets the inverse image
of each nonempty open of an irreducible coefficient space. -/
theorem timeOpen_meets_coefficients [IrreducibleSpace B] (W : (Time i V).Opens)
    (hW : (W : Set (Time i V)).Nonempty) (U : B.Opens) (hU : (U : Set B).Nonempty) :
    ∃ x ∈ W, timeMap i V x ∈ U := by
  have := timeMap_smooth i V
  have : Smooth (timeMap i V) := SmoothOfRelativeDimension.smooth 1 _
  obtain ⟨_, ⟨x, hx, rfl⟩, hxU⟩ := nonempty_preirreducible_inter
    ((timeMap i V).isOpenMap _ W.isOpen) U.isOpen (hW.image _) hU
  exact ⟨x, hx, hxU⟩

include b hb in
/-- The same section vector gives a smooth relative surface after any pointed base change.
Its curve projection is proper and surjective and its image in the coefficients is dense. -/
theorem spread_of_independent [IrreducibleSpace B] (t : Fin 3 → ℂ)
    (hi : AlgebraicIndependent ℚ t) :
    ∃ V : parameterScheme.Opens, seedBasePoint ∈ V ∧
      SmoothOfRelativeDimension 1 (timeMap i V) ∧
      SmoothOfRelativeDimension 1 (curveMap i V t) ∧
      SmoothOfRelativeDimension 2 (curveMap i V t ≫ timeMap i V) ∧
      IsProper (curveMap i V t) ∧ Surjective (curveMap i V t) ∧
      IsOpen (Set.range (timeMap i V)) ∧ IsDominant (timeMap i V) ∧
      IsDominant (curveMap i V t ≫ timeMap i V) := by
  obtain ⟨W, hW, hcurve, hproper, hsurj⟩ :=
    CycleQ2LiteralAbelJacobiSeedLiftDimension.dimension_one_neighborhood_of_seedMinorCover t
      (CycleQ2LiteralAbelJacobiBertiniMinor.prime_minor_of_independent t hi)
  have hπ : SmoothOfRelativeDimension 1 (curveMap i W t) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback
      (IsPullback.of_hasPullback (pullback.snd i (W.ι ≫ parameterToSextics))
        ((relativeCurveToBase incidencePoint t) ∣_ W)).flip hcurve
  have hτ := timeMap_smooth i W
  have : Smooth (timeMap i W) := SmoothOfRelativeDimension.smooth 1 _
  have hne : Nonempty (Time i W) := ⟨fixedToTime i W b hb (seedLift W hW default)⟩
  have hdom : IsDominant (timeMap i W) :=
    ⟨IsOpenMap.denseRange_of_isPreirreducibleSpace _ (timeMap i W).isOpenMap⟩
  have hpb := (IsPullback.of_hasPullback (pullback.snd i (W.ι ≫ parameterToSextics))
    ((relativeCurveToBase incidencePoint t) ∣_ W)).flip
  have hsurBC : MorphismProperty.IsStableUnderBaseChange
      (@Surjective : MorphismProperty Scheme.{0}) := inferInstance
  have hsur : Surjective (curveMap i W t) := hsurBC.of_isPullback hpb ⟨hsurj⟩
  refine ⟨W, hW, hτ, hπ, smoothOfRelativeDimension_comp 1 1 _ _, ?_, hsur,
    (timeMap i W).isOpenMap.isOpen_range, hdom, inferInstance⟩
  exact IsProper.isStableUnderBaseChange.of_isPullback hpb hproper

end CycleQ2LiteralIncidenceRelativeSpread
end

#print axioms CycleQ2LiteralIncidenceRelativeSpread.spread_of_independent

end

section

/-!
# The normalized sextic coefficient slice through the marked incidence point

The actual seed evaluates all raw sextic coefficients at those of the
polynomial smoothF(57,I). Its coefficient of w³ is one. Fixing precisely
this coordinate embeds the affine space of monic sextics into the raw
coefficient space. The marked complex point factors through this slice.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/


noncomputable section

namespace CycleQ2LiteralIncidenceNormalizedSlice

open CategoryTheory AlgebraicGeometry MvPolynomial
  CycleQ2IncidenceMonomials CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations
  CycleQ2IncidenceImageLine CycleQ2IncidenceGenericPointSemantics
  CycleQ2IncidenceTraceFamily CycleQ2IncidenceEtaleParameter CycleQ2IncidenceTimeCurve
  CycleQ2LiteralIncidenceTimeCurve CycleQ2LiteralIncidenceCylinderMap
  CycleQ2GeometricIncidenceProj CycleQ2IncidenceFamilyContainment

attribute [local instance] CycleQ2IncidenceTimeCurve.timeParameterCommRing

abbrev MonicRing := MvPolynomial FullSexticTailIndex ℂ

def monicBase : Scheme := Spec (CommRingCat.of MonicRing)

abbrev rawSeedEval : CycleQ2IncidenceTimeCurve.SexticRing →+* ℂ :=
  seedMap.comp sexticToParameter

@[simp] theorem rawSeedEval_C (a : ℂ) : rawSeedEval (C a) = a :=
  (congrArg seedMap (CycleQ2GenericTimeDerivation.sexticToParameter_C a)).trans
    (CycleQ2IncidenceSeedFiber.seedMap_complex a)

@[simp] theorem rawSeedEval_X (e : FullInvariantIndex 6) :
    rawSeedEval (X e) = seedSexticCoefficients (57 : ℂ) Complex.I e := by
  change seedMap (sexticToParameter (X e)) = _
  rw [sexticToParameter_X, seedMap_algebraMap]
  simp [seedEvaluation, sexticParameter, baseSeed]

theorem seed_leading : seedSexticCoefficients (57 : ℂ) Complex.I fullSexticLeadingIndex = 1 := by
  simp only [seedSexticCoefficients, fullSexticLeadingIndex_exponent, smoothF_leading_coefficient]

theorem rawSeedEval_leading : rawSeedEval (X fullSexticLeadingIndex) = 1 :=
  (rawSeedEval_X _).trans seed_leading

def rawCoordinate (e : FullInvariantIndex 6) : MonicRing :=
  if h : (e.val 4).val < 3 then X ⟨e,h⟩ else 1

@[simp] theorem rawCoordinate_tail (e : FullSexticTailIndex) :
    rawCoordinate e.val = X e := by simp [rawCoordinate, e.property]

@[simp] theorem rawCoordinate_leading : rawCoordinate fullSexticLeadingIndex = 1 := by
  have h := (fullSextic_tail_iff_ne fullSexticLeadingIndex).not.mpr (not_not.mpr rfl)
  simp [rawCoordinate, h]

def rawToMonic : CycleQ2IncidenceTimeCurve.SexticRing →+* MonicRing :=
  eval₂Hom C rawCoordinate

@[simp] theorem rawToMonic_C (a : ℂ) : rawToMonic (C a) = C a := by simp [rawToMonic]
@[simp] theorem rawToMonic_X (e : FullInvariantIndex 6) : rawToMonic (X e) = rawCoordinate e := by
  simp [rawToMonic]

def toRaw : monicBase ⟶ sexticBase := Spec.map (CommRingCat.ofHom rawToMonic)

theorem rawToMonic_surjective : Function.Surjective rawToMonic := by
  let inc := (rename (Subtype.val : FullSexticTailIndex → FullInvariantIndex 6) :
    MonicRing →ₐ[ℂ] CycleQ2IncidenceTimeCurve.SexticRing)
  have h : rawToMonic.comp inc.toRingHom = RingHom.id MonicRing := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [inc]
    · intro e
      simp [inc]
  exact fun p => ⟨inc p, congrArg (fun f : MonicRing →+* MonicRing => f p) h⟩

instance toRaw_isClosedImmersion : IsClosedImmersion toRaw :=
  IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom rawToMonic) rawToMonic_surjective

def toComplex : monicBase ⟶ Spec (CommRingCat.of ℂ) :=
  Spec.map (CommRingCat.ofHom (algebraMap ℂ MonicRing))

@[reassoc, simp] theorem toRaw_over :
    toRaw ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ CycleQ2IncidenceTimeCurve.SexticRing)) =
      toComplex := by
  erw [toRaw, toComplex, ← Spec.map_comp]
  apply congrArg Spec.map
  exact CommRingCat.hom_ext (RingHom.ext rawToMonic_C)

/-- The original universal projective equation becomes the normalized full sextic
with its independent tail coefficients on this slice. -/
theorem universal_equation :
    MvPolynomial.map rawToMonic (pointEquationF universalPoint) =
      normalizedFullSextic (fun e : FullSexticTailIndex => (X e : MonicRing)) := by
  rw [pointEquationF, pointMap_familyF, map_fullInvariantPolynomial]
  have h : rawToMonic ∘ pointSextic universalPoint = rawCoordinate := by
    funext e
    exact rawToMonic_X e
  rw [h, fullInvariantPolynomial_sextic, rawCoordinate_leading]
  simp only [rawFullSextic, normalizedFullSextic, rawCoordinate_tail]

def monicSeedEval : MonicRing →+* ℂ :=
  eval (fun e : FullSexticTailIndex => seedSexticCoefficients (57 : ℂ) Complex.I e.val)

def seedPoint : Spec (CommRingCat.of ℂ) ⟶ monicBase := Spec.map (CommRingCat.ofHom monicSeedEval)

@[reassoc, simp] theorem seedPoint_over : seedPoint ≫ toComplex = 𝟙 _ := by
  erw [seedPoint, toComplex, ← Spec.map_comp, ← Spec.map_id]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  exact RingHom.ext (fun c => eval_C c)

theorem monicSeedEval_comp : monicSeedEval.comp rawToMonic = rawSeedEval := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp [monicSeedEval]
  · intro e
    rw [RingHom.comp_apply, rawToMonic_X, rawSeedEval_X]
    by_cases h : (e.val 4).val < 3
    · simp [rawCoordinate, h, monicSeedEval]
    · have he : e = fullSexticLeadingIndex := not_not.mp ((fullSextic_tail_iff_ne e).not.mp h)
      subst e
      rw [rawCoordinate_leading, map_one, seed_leading]

@[reassoc, simp] theorem seedPoint_toRaw : seedPoint ≫ toRaw = seedSextic := by
  erw [seedPoint, toRaw, seedSextic, seedPointMorphism, parameterToSextics, ← Spec.map_comp,
    ← Spec.map_comp]
  apply congrArg Spec.map
  exact CommRingCat.hom_ext monicSeedEval_comp

end CycleQ2LiteralIncidenceNormalizedSlice

end

#print axioms CycleQ2LiteralIncidenceNormalizedSlice.universal_equation
#print axioms CycleQ2LiteralIncidenceNormalizedSlice.seedPoint_toRaw

end

section

/-!
# A relative projective closure over the normalized sextic base

The finite-type incidence algebra embeds the parameter scheme in a complex
affine space. The monic slice of its marked open thus embeds into a projective
space over the normalized coefficient scheme. Its scheme-theoretic image
compactifies the entire time open over that base.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/


noncomputable section
namespace CycleQ2LiteralIncidenceRelativeCompletion

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
  CycleQ2IncidenceEtaleParameter CycleQ2IncidenceTimeCurve
  CycleQ2LiteralIncidenceRelativeSpread CycleQ2LiteralIncidenceNormalizedSlice
  CycleQ2AffineProjectiveCompletionChart CycleQ2IncidenceSeedFiberCover

attribute [local instance] CycleQ2IncidenceTimeCurve.timeParameterCommRing

private def coefficients : ℂ →+* ParameterAlgebra :=
  sexticToParameter.comp (algebraMap ℂ SexticRing)

private local instance : Algebra ℂ ParameterAlgebra := coefficients.toAlgebra

private theorem finiteType : Algebra.FiniteType ℂ ParameterAlgebra := by
  have h : sexticToParameter.FiniteType :=
    RingHom.finiteType_algebraMap.mpr (inferInstance : Algebra.FiniteType SexticRing ParameterAlgebra)
  exact h.comp (RingHom.finiteType_algebraMap.mpr inferInstance)

private theorem exists_presentation :
    ∃ (n : ℕ) (φ : MvPolynomial (Fin n) ℂ →ₐ[ℂ] ParameterAlgebra), Function.Surjective φ :=
  Algebra.FiniteType.iff_quotient_mvPolynomial''.mp finiteType

abbrev Axes := Fin exists_presentation.choose

private def presentation : MvPolynomial Axes ℂ →ₐ[ℂ] ParameterAlgebra :=
  exists_presentation.choose_spec.choose

private def intoProjective : parameterScheme ⟶ projectiveSpace Axes :=
  Spec.map (CommRingCat.ofHom presentation.toRingHom) ≫ affineChart Axes

private instance : IsImmersion intoProjective := by
  let e : parameterScheme ⟶ affineSpace Axes := Spec.map (CommRingCat.ofHom presentation.toRingHom)
  letI : IsClosedImmersion e :=
    IsClosedImmersion.spec_of_surjective _ exists_presentation.choose_spec.choose_spec
  exact IsImmersion.comp e (affineChart Axes)

private theorem intoProjective_over :
    intoProjective ≫ projectiveToComplex Axes =
      parameterToSextics ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ SexticRing)) := by
  let e : parameterScheme ⟶ affineSpace Axes := Spec.map (CommRingCat.ofHom presentation.toRingHom)
  let g := Spec.map (CommRingCat.ofHom (algebraMap ℂ (MvPolynomial Axes ℂ)))
  let h := Spec.map (CommRingCat.ofHom (algebraMap ℂ SexticRing))
  have h₁ : intoProjective ≫ projectiveToComplex Axes =
      e ≫ g :=
    (Category.assoc e (affineChart Axes) (projectiveToComplex Axes)).trans
      (congrArg (fun k => e ≫ k) (affineChart_over Axes))
  have h₂ : e ≫ g =
      Spec.map (CommRingCat.ofHom (presentation.toRingHom.comp
        (algebraMap ℂ (MvPolynomial Axes ℂ)))) :=
    (Spec.map_comp (CommRingCat.ofHom (algebraMap ℂ (MvPolynomial Axes ℂ)))
      (CommRingCat.ofHom presentation.toRingHom)).symm
  have h₃ : parameterToSextics ≫ h = Spec.map (CommRingCat.ofHom coefficients) :=
    (Spec.map_comp (CommRingCat.ofHom (algebraMap ℂ SexticRing))
      (CommRingCat.ofHom sexticToParameter)).symm
  exact h₁.trans (h₂.trans ((congrArg Spec.map
    (CommRingCat.hom_ext presentation.comp_algebraMap)).trans h₃.symm))

abbrev ProjectiveBundle := pullback toComplex (projectiveToComplex Axes)

variable (V : parameterScheme.Opens)

/-- The joint coefficient and projective coordinate map of the actual normalized time curve. -/
def graph : Time toRaw V ⟶ ProjectiveBundle :=
  pullback.lift (timeMap toRaw V) (pullback.snd _ _ ≫ V.ι ≫ intoProjective) <| by
    rw [Category.assoc, Category.assoc, intoProjective_over, ← toRaw_over]
    have h := pullback.condition_assoc (f := toRaw) (g := V.ι ≫ parameterToSextics)
      (Spec.map (CommRingCat.ofHom (algebraMap ℂ SexticRing)))
    exact h.trans (congrArg (fun a => pullback.snd toRaw (V.ι ≫ parameterToSextics) ≫ a)
      (Category.assoc V.ι parameterToSextics
        (Spec.map (CommRingCat.ofHom (algebraMap ℂ SexticRing)))))

instance : IsImmersion (graph V) := by
  have : IsImmersion (graph V ≫ pullback.snd toComplex (projectiveToComplex Axes)) := by
    rw [graph, pullback.lift_snd]
    infer_instance
  exact IsImmersion.of_comp _ (pullback.snd toComplex (projectiveToComplex Axes))

instance : QuasiCompact (graph V) := by
  let _ := finiteType
  let _ := Algebra.FiniteType.isNoetherianRing ℂ ParameterAlgebra
  have : NoetherianSpace parameterScheme :=
    inferInstanceAs (NoetherianSpace (Spec (CommRingCat.of ParameterAlgebra)))
  have : NoetherianSpace V.toScheme := NoetherianSpace.set (V : Set parameterScheme)
  have : NoetherianSpace (Time toRaw V) :=
    (pullback.snd toRaw (V.ι ≫ parameterToSextics)).isClosedEmbedding.isInducing.noetherianSpace
  infer_instance

abbrev Completion := (graph V).image

def inclusion : Time toRaw V ⟶ Completion V := (graph V).toImage

def structureMap : Completion V ⟶ monicBase :=
  (graph V).imageι ≫ pullback.fst toComplex (projectiveToComplex Axes)

instance : IsProper (structureMap V) := by
  have := projectiveToComplex_proper Axes
  unfold structureMap
  infer_instance

instance : IsOpenImmersion (inclusion V) := inferInstanceAs (IsOpenImmersion (graph V).toImage)

instance : IsDominant (inclusion V) := inferInstanceAs (IsDominant (graph V).toImage)

instance : QuasiCompact (inclusion V) := inferInstanceAs (QuasiCompact (graph V).toImage)

@[reassoc (attr := simp)] theorem inclusion_over :
    inclusion V ≫ structureMap V = timeMap toRaw V := by
  rw [inclusion, structureMap, ← Category.assoc, Scheme.Hom.toImage_imageι, graph, pullback.lift_fst]

/-- The marked time neighborhood in the proper closure is smooth of relative dimension one. -/
theorem smooth_time_neighborhood :
    SmoothOfRelativeDimension 1 (inclusion V ≫ structureMap V) := by
  rw [inclusion_over]
  exact timeMap_smooth _ _

/-- The same marked vector gives a proper time completion surjective over the full monic chart. -/
theorem exists_surjective_completion (t : Fin 3 → ℂ) (hi : AlgebraicIndependent ℚ t) :
    ∃ V : parameterScheme.Opens, seedBasePoint ∈ V ∧
      SmoothOfRelativeDimension 1 (curveMap toRaw V t) ∧
      SmoothOfRelativeDimension 2 (curveMap toRaw V t ≫ timeMap toRaw V) ∧
      IsProper (curveMap toRaw V t) ∧ Surjective (curveMap toRaw V t) ∧
      IsDominant (timeMap toRaw V) ∧ Surjective (structureMap V) := by
  have : IrreducibleSpace monicBase :=
    inferInstanceAs (IrreducibleSpace (Spec (CommRingCat.of MonicRing)))
  obtain ⟨W, hW, _, hπ, hS, hp, hs, _, hdom, _⟩ :=
    spread_of_independent toRaw seedPoint seedPoint_toRaw t hi
  have : IsDominant (inclusion W ≫ structureMap W) := by
    rw [inclusion_over]
    exact hdom
  have := IsDominant.of_comp (inclusion W) (structureMap W)
  exact ⟨W, hW, hπ, hS, hp, hs, hdom,
    surjective_of_isDominant_of_isClosed_range _ (structureMap W).isClosedMap.isClosed_range⟩

end CycleQ2LiteralIncidenceRelativeCompletion
end

#print axioms CycleQ2LiteralIncidenceRelativeCompletion.inclusion_over
#print axioms CycleQ2LiteralIncidenceRelativeCompletion.exists_surjective_completion

end

section

/-!
# The correspondence projection and tangent on the relative incidence spread

The second projection uses the original embedded incidence curve over the universal
sextic. The marked coefficient fibre is the original pointed family, including
its map to the fixed threefold and its nonconstant dual-number tangent.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/


noncomputable section
namespace CycleQ2LiteralIncidenceRelativeCylinder

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
  CycleQ2IncidenceEtaleParameter CycleQ2IncidenceTimeCurve CycleQ2IncidenceFirstOrder
  CycleQ2LiteralIncidenceTimeCurve CycleQ2RelativeConstantCurve CycleQ2IncidenceSeedFiberCover
  CycleQ2LiteralAbelJacobiTimeFamily CycleQ2LiteralIncidenceCylinderMap
  CycleQ2LiteralIncidenceRelativeSpread CycleQ2IncidencePolynomialJacobianBinding
  CycleQ2GeometricIncidenceProj CycleQ2IncidenceFamilyContainment CycleQ2FirstOrderCurve

variable {B : Scheme} (i : B ⟶ sexticBase) (V : parameterScheme.Opens) (t : Fin 3 → ℂ)

abbrev ambient := pullback i universalAmbientToBase

def toOriginal : Surface i V t ⟶ relativeCurve incidencePoint t :=
  pullback.snd _ ((relativeCurveToBase incidencePoint t) ∣_ V) ≫
    ((relativeCurveToBase incidencePoint t) ⁻¹ᵁ V).ι

theorem over_coefficients :
    (curveMap i V t ≫ timeMap i V) ≫ i = (toOriginal i V t ≫ originalToAmbient t) ≫ universalAmbientToBase := by
  let f := relativeCurveToBase incidencePoint t
  have hT : timeMap i V ≫ i = pullback.snd i (V.ι ≫ parameterToSextics) ≫ V.ι ≫ parameterToSextics :=
    pullback.condition
  have hS : curveMap i V t ≫ pullback.snd i (V.ι ≫ parameterToSextics) =
      pullback.snd _ (f ∣_ V) ≫ (f ∣_ V) := pullback.condition
  let p := pullback.snd (pullback.snd i (V.ι ≫ parameterToSextics)) (f ∣_ V)
  let j := (f ⁻¹ᵁ V).ι
  have hR : (f ∣_ V) ≫ V.ι = j ≫ f := morphismRestrict_ι f V
  have h₁ := (Category.assoc (curveMap i V t) (timeMap i V) i).trans
    ((congrArg (fun a => curveMap i V t ≫ a) hT).trans
      (Category.assoc (curveMap i V t) (pullback.snd i (V.ι ≫ parameterToSextics))
        (V.ι ≫ parameterToSextics)).symm)
  have h₂ : (p ≫ (f ∣_ V)) ≫ V.ι ≫ parameterToSextics =
      (p ≫ j) ≫ f ≫ parameterToSextics := by
    exact (Category.assoc p (f ∣_ V) (V.ι ≫ parameterToSextics)).trans
      ((congrArg (fun a => p ≫ a)
        (((Category.assoc (f ∣_ V) V.ι parameterToSextics).symm.trans
          (congrArg (fun a => a ≫ parameterToSextics) hR)).trans
            (Category.assoc j f parameterToSextics))).trans
        (Category.assoc p j (f ≫ parameterToSextics)).symm)
  have h₃ : (toOriginal i V t ≫ originalToAmbient t) ≫ universalAmbientToBase =
      (p ≫ j) ≫ f ≫ parameterToSextics :=
    (Category.assoc (toOriginal i V t) (originalToAmbient t) universalAmbientToBase).trans
      (congrArg (fun a => toOriginal i V t ≫ a) (original_over_coefficients t))
  exact h₁.trans ((congrArg (fun a => a ≫ V.ι ≫ parameterToSextics) hS).trans (h₂.trans h₃.symm))

def relativeQ : Surface i V t ⟶ ambient i :=
  pullback.lift (curveMap i V t ≫ timeMap i V) (toOriginal i V t ≫ originalToAmbient t)
    (over_coefficients i V t)

@[reassoc (attr := simp)] theorem relativeQ_fst :
    relativeQ i V t ≫ pullback.fst i universalAmbientToBase = curveMap i V t ≫ timeMap i V := pullback.lift_fst _ _ _

@[reassoc (attr := simp)] theorem relativeQ_snd :
    relativeQ i V t ≫ pullback.snd i universalAmbientToBase = toOriginal i V t ≫ originalToAmbient t :=
  pullback.lift_snd _ _ _

variable (b : Spec (CommRingCat.of ℂ) ⟶ B) (hb : b ≫ i = seedSextic)

def fixedToAmbient : FixedThreefold ⟶ ambient i :=
  pullback.lift (pullback.fst seedSextic universalAmbientToBase ≫ b) (pullback.snd _ _) <| by
    rw [Category.assoc, hb]
    exact pullback.condition (f := seedSextic) (g := universalAmbientToBase)

@[reassoc (attr := simp)] theorem fixedToAmbient_fst :
    fixedToAmbient i b hb ≫ pullback.fst i universalAmbientToBase =
      pullback.fst seedSextic universalAmbientToBase ≫ b := pullback.lift_fst _ _ _

@[reassoc (attr := simp)] theorem fixedToAmbient_snd :
    fixedToAmbient i b hb ≫ pullback.snd i universalAmbientToBase =
      pullback.snd seedSextic universalAmbientToBase := pullback.lift_snd _ _ _

theorem fixed_ambient_square :
    IsPullback (pullback.fst seedSextic universalAmbientToBase) (fixedToAmbient i b hb)
      b (pullback.fst i universalAmbientToBase) := by
  have h : IsPullback (pullback.fst seedSextic universalAmbientToBase)
      (fixedToAmbient i b hb ≫ pullback.snd i universalAmbientToBase) (b ≫ i)
      universalAmbientToBase := by
    rw [fixedToAmbient_snd, hb]
    exact IsPullback.of_hasPullback seedSextic universalAmbientToBase
  exact h.of_bot (fixedToAmbient_fst i b hb).symm
    (IsPullback.of_hasPullback i universalAmbientToBase)

def fixedToSurface : family V t ⟶ Surface i V t :=
  pullback.lift (projection V t ≫ fixedToTime i V b hb) (pullback.snd _ _) <| by
    rw [Category.assoc, fixedToTime_snd]
    exact pullback.condition

@[reassoc (attr := simp)] theorem fixedToSurface_fst :
    fixedToSurface i V t b hb ≫ curveMap i V t = projection V t ≫ fixedToTime i V b hb := pullback.lift_fst _ _ _

@[reassoc (attr := simp)] theorem fixedToSurface_snd :
    fixedToSurface i V t b hb ≫ pullback.snd _ ((relativeCurveToBase incidencePoint t) ∣_ V) =
      pullback.snd _ _ := pullback.lift_snd _ _ _

theorem fixed_time_square :
    IsPullback ((timeOpen V).ι ≫ toComplex) (fixedToTime i V b hb) b (timeMap i V) := by
  have h₀ := (isPullback_morphismRestrict toIncidence V).flip.paste_horiz
    (IsPullback.of_hasPullback seedSextic parameterToSextics)
  have h : IsPullback ((timeOpen V).ι ≫ toComplex)
      (fixedToTime i V b hb ≫ pullback.snd i (V.ι ≫ parameterToSextics)) (b ≫ i)
      (V.ι ≫ parameterToSextics) := by rw [fixedToTime_snd, hb]; exact h₀
  exact h.of_bot (by rw [fixedToTime_fst, Category.assoc]) (IsPullback.of_hasPullback ..)

theorem fixed_curve_square :
    IsPullback (projection V t) (fixedToSurface i V t b hb) (fixedToTime i V b hb) (curveMap i V t) := by
  have h : IsPullback (projection V t)
      (fixedToSurface i V t b hb ≫ pullback.snd _ ((relativeCurveToBase incidencePoint t) ∣_ V))
      (fixedToTime i V b hb ≫ pullback.snd i (V.ι ≫ parameterToSextics))
      ((relativeCurveToBase incidencePoint t) ∣_ V) := by
    rw [fixedToSurface_snd, fixedToTime_snd]
    exact IsPullback.of_hasPullback ..
  exact h.of_bot (fixedToSurface_fst i V t b hb).symm (IsPullback.of_hasPullback ..)

theorem fixed_surface_square :
    IsPullback (projection V t ≫ (timeOpen V).ι ≫ toComplex) (fixedToSurface i V t b hb)
      b (curveMap i V t ≫ timeMap i V) :=
  (fixed_curve_square i V t b hb).paste_horiz (fixed_time_square i V b hb)

theorem fixed_q :
    fixedToSurface i V t b hb ≫ relativeQ i V t =
      CycleQ2LiteralAbelJacobiTimeProjection.q V t ≫ fixedToAmbient i b hb := by
  apply pullback.hom_ext
  · simp only [Category.assoc, relativeQ_fst, fixedToSurface_fst_assoc,
      fixedToTime_fst, fixedToAmbient_fst, CycleQ2LiteralAbelJacobiTimeProjection.q_overComplex_assoc]
  · let f := relativeCurveToBase incidencePoint t
    let j := (f ⁻¹ᵁ V).ι
    let p := pullback.snd (toIncidence ∣_ V) (f ∣_ V)
    have h : fixedToSurface i V t b hb ≫ toOriginal i V t = p ≫ j := by
      exact (Category.assoc (fixedToSurface i V t b hb) (pullback.snd _ (f ∣_ V)) j).symm.trans
        (congrArg (fun a => a ≫ j) (fixedToSurface_snd i V t b hb))
    have hl := (Category.assoc (fixedToSurface i V t b hb) (relativeQ i V t)
      (pullback.snd i universalAmbientToBase)).trans
      ((congrArg (fun a => fixedToSurface i V t b hb ≫ a) (relativeQ_snd i V t)).trans
        (Category.assoc (fixedToSurface i V t b hb) (toOriginal i V t) (originalToAmbient t)).symm)
    have hr := (Category.assoc (CycleQ2LiteralAbelJacobiTimeProjection.q V t)
      (fixedToAmbient i b hb) (pullback.snd i universalAmbientToBase)).trans
      ((congrArg (fun a => CycleQ2LiteralAbelJacobiTimeProjection.q V t ≫ a)
        (fixedToAmbient_snd i b hb)).trans
        (CycleQ2LiteralAbelJacobiTimeProjection.q_original V t))
    exact hl.trans ((congrArg (fun a => a ≫ originalToAmbient t) h).trans hr.symm)

variable (hV : seedBasePoint ∈ V)

def relativeTangent : Spec (CommRingCat.of (DualNumber ℂ)) ⟶ Time i V :=
  tangentLift V hV ≫ fixedToTime i V b hb

theorem tangent_to_incidence :
    relativeTangent i V b hb hV ≫ pullback.snd i (V.ι ≫ parameterToSextics) ≫ V.ι =
      firstOrderParameterPoint := by
  simp only [relativeTangent, Category.assoc, fixedToTime_snd_assoc, morphismRestrict_ι,
    tangentLift_fac_assoc, timeTangent_to_incidence]

theorem tangent_seed :
    firstOrderClosedPoint ≫ relativeTangent i V b hb hV = seedLift V hV ≫ fixedToTime i V b hb := by
  rw [relativeTangent, ← Category.assoc, tangentLift_at_seed]

theorem tangent_over_coefficients :
    relativeTangent i V b hb hV ≫ timeMap i V = structureDual ≫ b := by
  simp only [relativeTangent, Category.assoc, fixedToTime_fst, tangentLift_fac_assoc]
  exact (pullback.lift_fst_assoc ..)

private theorem tangentFamily_square :
    IsPullback (pullback.fst (tangentLift V hV) (projection V t))
      (pullback.snd _ _ ≫ fixedToSurface i V t b hb) (relativeTangent i V b hb hV) (curveMap i V t) :=
  (IsPullback.of_hasPullback (tangentLift V hV) (projection V t)).paste_vert
    (fixed_curve_square i V t b hb)

/-- The fibre along the relative tangent is the original embedded first-order curve. -/
def tangentFamilyIso :
    firstOrderCurve t ≅ pullback (relativeTangent i V b hb hV) (curveMap i V t) :=
  firstOrderIso V t hV ≪≫ (tangentFamily_square i V t b hb hV).isoPullback

theorem tangentFamily_q :
    (tangentFamilyIso i V t b hb hV).hom ≫ pullback.snd _ _ ≫ relativeQ i V t =
      (CycleQ2LiteralIncidenceTimeFamily.firstOrderIso t).hom ≫ pullback.snd _ _ ≫
        toFixedThreefold t ≫ fixedToAmbient i b hb := by
  have h := congrArg (fun f => (firstOrderIso V t hV).hom ≫ f ≫ relativeQ i V t)
    (tangentFamily_square i V t b hb hV).isoPullback_hom_snd
  simpa only [tangentFamilyIso, Iso.trans_hom, Category.assoc, fixed_q,
    CycleQ2LiteralAbelJacobiTimeProjection.firstOrder_to_q_assoc] using h

theorem tangent_nonconstant :
    relativeTangent i V b hb hV ≠ structureDual ≫ seedLift V hV ≫ fixedToTime i V b hb := by
  intro h
  have he := congrArg (fun f => f ≫ pullback.snd i (V.ι ≫ parameterToSextics) ≫ V.ι) h
  rw [tangent_to_incidence] at he
  simp only [Category.assoc, fixedToTime_snd_assoc, morphismRestrict_ι, seedLift_fac_assoc,
    seed_to_incidence] at he
  apply timeTangent_nonconstant
  apply pullback.hom_ext
  · simp only [timeTangent, seed, Category.assoc, pullback.lift_fst, Category.comp_id]
  · simpa only [timeTangent, seed, Category.assoc, pullback.lift_snd] using he

end CycleQ2LiteralIncidenceRelativeCylinder
end

#print axioms CycleQ2LiteralIncidenceRelativeCylinder.fixed_surface_square
#print axioms CycleQ2LiteralIncidenceRelativeCylinder.tangentFamily_q
#print axioms CycleQ2LiteralIncidenceRelativeCylinder.fixed_q
#print axioms CycleQ2LiteralIncidenceRelativeCylinder.tangent_nonconstant

end

section

/-!
# Properness of the universal weighted sextic and its coefficient changes

The graded cone is finitely generated over its degree-zero part. Every
degree-zero class comes from the original coefficients, so the proper
Proj structure morphism gives properness over the full sextic base.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

noncomputable section
namespace CycleQ2LiteralRelativeAmbientProper

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial
  CycleQ2IncidenceNormalForm CycleQ2IncidenceUniversalChart CycleQ2IncidenceFamilyContainment
  CycleQ2LiteralIncidenceCylinderMap

theorem sexticCoefficient_surjective {S : Type} [CommRing S] [Algebra ℂ S]
    (y : ParameterIndex → S) : Function.Surjective (algebraMap S (sexticGrade y 0)) := by
  rintro ⟨q, hq⟩
  obtain ⟨p,hp,rfl⟩ := hq
  refine ⟨p.coeff 0, Subtype.ext ?_⟩
  change Ideal.Quotient.mk (sexticIdeal y) (C (p.coeff 0)) = Ideal.Quotient.mk (sexticIdeal y) p
  exact congrArg (Ideal.Quotient.mk (sexticIdeal y))
    (CycleQ2IncidenceProjectiveProper.polynomialGrade_zero_eq_C p hp).symm

theorem weightedThreefoldToBase_proper {S : Type} [CommRing S] [Algebra ℂ S]
    (y : ParameterIndex → S) : IsProper (weightedThreefoldToBase y) := by
  letI : Algebra.FiniteType S (CycleQ2IncidenceFamilyContainment.SexticRing y) := inferInstance
  letI : IsScalarTower S (sexticGrade y 0) (CycleQ2IncidenceFamilyContainment.SexticRing y) :=
    ⟨fun a b c => by
      change (a • (b : CycleQ2IncidenceFamilyContainment.SexticRing y)) * c = a • ((b : _) * c)
      exact smul_mul_assoc a (b : CycleQ2IncidenceFamilyContainment.SexticRing y) c⟩
  letI : Algebra.FiniteType (sexticGrade y 0) (CycleQ2IncidenceFamilyContainment.SexticRing y) :=
    Algebra.FiniteType.of_restrictScalars_finiteType S _ _
  letI : IsClosedImmersion (Spec.map (CommRingCat.ofHom (algebraMap S (sexticGrade y 0)))) :=
    IsClosedImmersion.spec_of_surjective _ (sexticCoefficient_surjective y)
  let m := Proj.toSpecZero (sexticGrade y)
  let q := Spec.map (CommRingCat.ofHom (algebraMap S (sexticGrade y 0)))
  letI : IsProper m := inferInstanceAs (IsProper (Proj.toSpecZero (sexticGrade y)))
  letI : IsProper q := inferInstanceAs (IsProper (Spec.map
    (CommRingCat.ofHom (algebraMap S (sexticGrade y 0)))))
  exact inferInstanceAs (IsProper (m ≫ q))

theorem universalAmbientToBase_proper : IsProper universalAmbientToBase :=
  weightedThreefoldToBase_proper universalPoint

theorem ambient_proper {B : Scheme} (i : B ⟶ CycleQ2IncidenceTimeCurve.sexticBase) :
    IsProper (pullback.fst i universalAmbientToBase) := by
  exact IsProper.isStableUnderBaseChange.of_isPullback
    (IsPullback.of_hasPullback i universalAmbientToBase).flip universalAmbientToBase_proper

end CycleQ2LiteralRelativeAmbientProper

#print axioms CycleQ2LiteralRelativeAmbientProper.ambient_proper

end

section

/-!
# The relative incidence family as a closed correspondence

Together, the time point and its point on the ambient sextic determine the
embedded section point. Properness over the time curve then identifies the
relative family with a closed subscheme of the product over the coefficient base.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/


noncomputable section
namespace CycleQ2LiteralIncidenceRelativeEmbedding

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
  CycleQ2IncidenceEtaleParameter CycleQ2IncidenceTimeCurve
  CycleQ2IncidencePolynomialJacobianBinding CycleQ2GeometricIncidenceProj
  CycleQ2IncidenceFamilyContainment CycleQ2RelativeConstantCurve
  CycleQ2LiteralIncidenceCylinderMap CycleQ2LiteralIncidenceRelativeSpread
  CycleQ2LiteralIncidenceRelativeCylinder

attribute [local instance] CycleQ2IncidenceTimeCurve.timeParameterCommRing

variable {B : Scheme} (i : B ⟶ sexticBase) (V : parameterScheme.Opens) (t : Fin 3 → ℂ)

abbrev Product := pullback (timeMap i V) (pullback.fst i universalAmbientToBase)

def joint : Surface i V t ⟶ Product i V :=
  pullback.lift (curveMap i V t) (relativeQ i V t) (relativeQ_fst i V t).symm

@[reassoc (attr := simp)] theorem joint_toTime :
    joint i V t ≫ pullback.fst _ _ = curveMap i V t := pullback.lift_fst _ _ _

@[reassoc (attr := simp)] theorem joint_toAmbient :
    joint i V t ≫ pullback.snd _ _ = relativeQ i V t := pullback.lift_snd _ _ _

private theorem curve_to_parameter :
    curveMap i V t ≫ pullback.snd i (V.ι ≫ parameterToSextics) ≫ V.ι =
      toOriginal i V t ≫ relativeCurveToBase incidencePoint t := by
  let f := relativeCurveToBase incidencePoint t
  let a := pullback.snd i (V.ι ≫ parameterToSextics)
  let p := pullback.snd a (f ∣_ V)
  let j := (f ⁻¹ᵁ V).ι
  exact (Category.assoc (curveMap i V t) a V.ι).symm.trans
    ((congrArg (fun g => g ≫ V.ι) (pullback.condition (f := a) (g := f ∣_ V))).trans
      ((Category.assoc p (f ∣_ V) V.ι).trans
        ((congrArg (fun g => p ≫ g) (morphismRestrict_ι f V)).trans
          (Category.assoc p j f).symm)))

private abbrev inclusion := relativeCurveToSurface incidencePoint t ≫ surfaceToThreefold incidencePoint

private theorem original_ext {W : Scheme} (g h : W ⟶ relativeCurve incidencePoint t)
    (hbase : g ≫ relativeCurveToBase incidencePoint t = h ≫ relativeCurveToBase incidencePoint t)
    (hambient : g ≫ originalToAmbient t = h ≫ originalToAmbient t) : g = h := by
  have : IsClosedImmersion (surfaceToThreefold incidencePoint) := by
    apply CycleQ2LiteralAmbientSurface.projectiveMap_closedImmersion
    rintro n b ⟨p, hp, rfl⟩
    exact ⟨Ideal.Quotient.mk (sexticIdeal incidencePoint) p, ⟨p, hp, rfl⟩, rfl⟩
  apply (cancel_mono (inclusion t)).mp
  apply CycleQ2LiteralTimeFamilyEmbedding.coefficient_joint_ext
    sexticToParameter universalPoint incidencePoint universal_to_incidence
  · simpa only [inclusion, Category.assoc, surfaceToThreefold_toBase, relativeCurveToBase] using hbase
  · simpa only [inclusion, Category.assoc, originalToAmbient] using hambient

theorem joint_mono : Mono (joint i V t) := by
  constructor
  intro W g h he
  have ht : g ≫ curveMap i V t = h ≫ curveMap i V t := by
    simpa only [Category.assoc, joint_toTime] using congrArg (· ≫ pullback.fst _ _) he
  have hq : g ≫ relativeQ i V t = h ≫ relativeQ i V t := by
    simpa only [Category.assoc, joint_toAmbient] using congrArg (· ≫ pullback.snd _ _) he
  have ho : g ≫ toOriginal i V t = h ≫ toOriginal i V t := by
    apply original_ext
    · let a := pullback.snd i (V.ι ≫ parameterToSextics) ≫ V.ι
      let f := relativeCurveToBase incidencePoint t
      have comp_eq (k : W ⟶ Surface i V t) :
          (k ≫ curveMap i V t) ≫ a = (k ≫ toOriginal i V t) ≫ f :=
        (Category.assoc k (curveMap i V t) a).trans
          ((congrArg (fun v => k ≫ v) (curve_to_parameter i V t)).trans
            (Category.assoc k (toOriginal i V t) f).symm)
      exact (comp_eq g).symm.trans ((congrArg (fun v => v ≫ a) ht).trans (comp_eq h))
    · simpa only [Category.assoc, relativeQ_snd] using
        congrArg (· ≫ pullback.snd i universalAmbientToBase) hq
  apply pullback.hom_ext ht
  let f := relativeCurveToBase incidencePoint t
  let j := (f ⁻¹ᵁ V).ι
  let p := pullback.snd (pullback.snd i (V.ι ≫ parameterToSextics)) (f ∣_ V)
  apply (cancel_mono j).mp
  exact (Category.assoc g p j).trans (ho.trans (Category.assoc h p j).symm)

theorem curveMap_proper : IsProper (curveMap i V t) := by
  let f := relativeCurveToBase incidencePoint t
  have hf : IsProper f := CycleQ2RelativeCurveNeighborhood.relativeCurveToBase_proper incidencePoint t
  have hp : IsProper (f ∣_ V) := IsProper.isStableUnderBaseChange.of_isPullback
    (isPullback_morphismRestrict f V).flip hf
  exact IsProper.isStableUnderBaseChange.of_isPullback
    (IsPullback.of_hasPullback (pullback.snd i (V.ι ≫ parameterToSextics)) (f ∣_ V)).flip hp

theorem joint_isClosedImmersion : IsClosedImmersion (joint i V t) := by
  apply (IsClosedImmersion.iff_isProper_and_mono _).mpr
  refine ⟨?_, joint_mono i V t⟩
  let p := pullback.fst i universalAmbientToBase
  letI : IsProper p := CycleQ2LiteralRelativeAmbientProper.ambient_proper i
  letI : IsProper (pullback.fst (timeMap i V) p) :=
    IsProper.isStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback (timeMap i V) p).flip (inferInstance : IsProper p)
  letI : IsProper (joint i V t ≫ pullback.fst (timeMap i V) p) := by
    rw [joint_toTime]
    exact curveMap_proper i V t
  exact IsProper.of_comp (joint i V t) (pullback.fst (timeMap i V) p)

end CycleQ2LiteralIncidenceRelativeEmbedding
end

#print axioms CycleQ2LiteralIncidenceRelativeEmbedding.joint_isClosedImmersion

end

section

/-!
# Closing a family of embedded correspondences in a relative product

A closed correspondence over an open time scheme embeds in the product with
a compactified time scheme. Its scheme-theoretic closure recovers the
original family by base change to the time open, with both projections.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/


noncomputable section
namespace CycleQ2RelativeGraphClosure

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u
variable {B U P T X : Scheme.{u}} (u : U ⟶ B) (p : P ⟶ B) (a : T ⟶ B)
  (j : U ⟶ P) (hj : j ≫ p = u)

/-- The inclusion of the product over the time open into the compactifying product. -/
def productMap : pullback u a ⟶ pullback p a :=
  pullback.lift (pullback.fst u a ≫ j) (pullback.snd u a)
    (by rw [Category.assoc, hj, pullback.condition])

@[reassoc (attr := simp)]
theorem productMap_fst :
    productMap u p a j hj ≫ pullback.fst p a = pullback.fst u a ≫ j :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem productMap_snd :
    productMap u p a j hj ≫ pullback.snd p a = pullback.snd u a :=
  pullback.lift_snd _ _ _

theorem product_square :
    IsPullback (pullback.fst u a) (productMap u p a j hj) j (pullback.fst p a) := by
  apply IsPullback.of_bot _ (productMap_fst u p a j hj).symm (IsPullback.of_hasPullback p a)
  simpa only [productMap_snd, hj] using IsPullback.of_hasPullback u a

instance [IsOpenImmersion j] : IsOpenImmersion (productMap u p a j hj) :=
  MorphismProperty.of_isPullback (product_square u p a j hj) inferInstance

instance [QuasiCompact j] : QuasiCompact (productMap u p a j hj) :=
  MorphismProperty.of_isPullback (product_square u p a j hj) inferInstance

variable (g : X ⟶ pullback u a)

abbrev graph := g ≫ productMap u p a j hj

abbrev Closure := (graph u p a j hj g).image
abbrev toClosure := (graph u p a j hj g).toImage
abbrev embedding := (graph u p a j hj g).imageι

def timeProjection : Closure u p a j hj g ⟶ P :=
  embedding u p a j hj g ≫ pullback.fst p a

def targetProjection : Closure u p a j hj g ⟶ T :=
  embedding u p a j hj g ≫ pullback.snd p a

@[reassoc (attr := simp)]
theorem toClosure_timeProjection :
    toClosure u p a j hj g ≫ timeProjection u p a j hj g = g ≫ pullback.fst u a ≫ j := by
  rw [timeProjection, ← Category.assoc, Scheme.Hom.toImage_imageι]
  simp only [graph, Category.assoc, productMap_fst]

@[reassoc (attr := simp)]
theorem toClosure_targetProjection :
    toClosure u p a j hj g ≫ targetProjection u p a j hj g = g ≫ pullback.snd u a := by
  rw [targetProjection, ← Category.assoc, Scheme.Hom.toImage_imageι]
  simp only [graph, Category.assoc, productMap_snd]

instance [IsProper p] : IsProper (targetProjection u p a j hj g) := by
  unfold targetProjection
  infer_instance

instance [IsProper a] : IsProper (timeProjection u p a j hj g) := by
  unfold timeProjection
  infer_instance

variable [IsClosedImmersion g] [IsOpenImmersion j] [QuasiCompact j]

theorem recovery :
    IsPullback (g ≫ pullback.fst u a) (toClosure u p a j hj g) j (timeProjection u p a j hj g) :=
  (CycleQ2ImmersionImageClosure.closed_in_open_pullback g (productMap u p a j hj)).paste_horiz
    (product_square u p a j hj)

instance : IsOpenImmersion (toClosure u p a j hj g) :=
  MorphismProperty.of_isPullback (recovery u p a j hj g) inferInstance

instance : IsDominant (toClosure u p a j hj g) :=
  inferInstanceAs (IsDominant (g ≫ productMap u p a j hj).toImage)

end CycleQ2RelativeGraphClosure

#print axioms CycleQ2RelativeGraphClosure.recovery

end

section

/-!
# The proper correspondence over the full normalized sextic coefficient space

Close the original family of embedded curves in the product of the proper
relative time compactification and the universal threefold. The original
family is its restriction to the dense time open. The marked seed curve and
its dual-number deformation are recovered by scheme-theoretic pullback.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/


noncomputable section
namespace CycleQ2LiteralIncidenceRelativeCorrespondence

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
  CycleQ2LiteralIncidenceRelativeSpread CycleQ2LiteralIncidenceRelativeCylinder
  CycleQ2LiteralAbelJacobiTimeFamily CycleQ2LiteralIncidenceRelativeCompletion
open CycleQ2IncidenceEtaleParameter (parameterScheme)
open CycleQ2IncidenceSeedFiberCover (seedBasePoint)
open CycleQ2LiteralIncidenceNormalizedSlice (toRaw monicBase seedPoint seedPoint_toRaw)
open CycleQ2LiteralIncidenceCylinderMap (universalAmbientToBase)

abbrev ambientStructure : ambient toRaw ⟶ monicBase :=
  pullback.fst toRaw universalAmbientToBase

variable (V : parameterScheme.Opens) (t : Fin 3 → ℂ)

private abbrev openGraph := CycleQ2LiteralIncidenceRelativeEmbedding.joint toRaw V t

abbrev Product := pullback (structureMap V) ambientStructure

abbrev Correspondence :=
  CycleQ2RelativeGraphClosure.Closure (timeMap toRaw V) (structureMap V) ambientStructure
    (inclusion V) (inclusion_over V) (openGraph V t)

/-- The scheme-theoretic graph closure in the relative product. -/
abbrev embedding : Correspondence V t ⟶ Product V :=
  CycleQ2RelativeGraphClosure.embedding (timeMap toRaw V) (structureMap V) ambientStructure
    (inclusion V) (inclusion_over V) (openGraph V t)

abbrev fromSurface : Surface toRaw V t ⟶ Correspondence V t :=
  CycleQ2RelativeGraphClosure.toClosure (timeMap toRaw V) (structureMap V) ambientStructure
    (inclusion V) (inclusion_over V) (openGraph V t)

abbrev timeProjection : Correspondence V t ⟶ Completion V :=
  CycleQ2RelativeGraphClosure.timeProjection (timeMap toRaw V) (structureMap V) ambientStructure
    (inclusion V) (inclusion_over V) (openGraph V t)

abbrev ambientProjection : Correspondence V t ⟶ ambient toRaw :=
  CycleQ2RelativeGraphClosure.targetProjection (timeMap toRaw V) (structureMap V) ambientStructure
    (inclusion V) (inclusion_over V) (openGraph V t)

instance : IsProper (ambientProjection V t) :=
  inferInstanceAs (IsProper (CycleQ2RelativeGraphClosure.targetProjection _ _ _ _ _ _))

instance : IsProper (timeProjection V t) := by
  let : IsProper ambientStructure := CycleQ2LiteralRelativeAmbientProper.ambient_proper toRaw
  exact inferInstanceAs (IsProper (CycleQ2RelativeGraphClosure.timeProjection _ _ _ _ _ _))

@[reassoc (attr := simp)]
theorem fromSurface_toTime : fromSurface V t ≫ timeProjection V t = curveMap toRaw V t ≫ inclusion V := by
  simpa only [openGraph, CycleQ2LiteralIncidenceRelativeEmbedding.joint_toTime_assoc, fromSurface, timeProjection] using
    CycleQ2RelativeGraphClosure.toClosure_timeProjection (timeMap toRaw V) (structureMap V)
      ambientStructure (inclusion V) (inclusion_over V) (openGraph V t)

@[reassoc (attr := simp)]
theorem fromSurface_toAmbient : fromSurface V t ≫ ambientProjection V t = relativeQ toRaw V t := by
  simpa only [openGraph, CycleQ2LiteralIncidenceRelativeEmbedding.joint_toAmbient, fromSurface, ambientProjection] using
    CycleQ2RelativeGraphClosure.toClosure_targetProjection (timeMap toRaw V) (structureMap V)
      ambientStructure (inclusion V) (inclusion_over V) (openGraph V t)

/-- Restricting the proper relative correspondence along the dense time open recovers its
original scheme of embedded curves over all normalized coefficients. -/
theorem timeOpen_pullback :
    IsPullback (curveMap toRaw V t) (fromSurface V t) (inclusion V) (timeProjection V t) := by
  let : IsClosedImmersion (openGraph V t) :=
    CycleQ2LiteralIncidenceRelativeEmbedding.joint_isClosedImmersion toRaw V t
  simpa only [openGraph, CycleQ2LiteralIncidenceRelativeEmbedding.joint_toTime, fromSurface, timeProjection] using
    CycleQ2RelativeGraphClosure.recovery (timeMap toRaw V) (structureMap V) ambientStructure
      (inclusion V) (inclusion_over V) (openGraph V t)

instance : IsOpenImmersion (fromSurface V t) :=
  MorphismProperty.of_isPullback (timeOpen_pullback V t) inferInstance

instance : IsDominant (fromSurface V t) := by
  let : IsClosedImmersion (openGraph V t) :=
    CycleQ2LiteralIncidenceRelativeEmbedding.joint_isClosedImmersion toRaw V t
  exact inferInstanceAs (IsDominant (CycleQ2RelativeGraphClosure.toClosure _ _ _ _ _ _))

/-- The fixed surface of moving curves is the pullback over its original marked time curve. -/
theorem markedTime_pullback :
    IsPullback (projection V t)
      (fixedToSurface toRaw V t seedPoint seedPoint_toRaw ≫ fromSurface V t)
      (fixedToTime toRaw V seedPoint seedPoint_toRaw ≫ inclusion V) (timeProjection V t) :=
  (fixed_curve_square toRaw V t seedPoint seedPoint_toRaw).paste_vert (timeOpen_pullback V t)

@[reassoc (attr := simp)]
theorem markedTime_toAmbient :
    (fixedToSurface toRaw V t seedPoint seedPoint_toRaw ≫ fromSurface V t) ≫ ambientProjection V t =
      CycleQ2LiteralAbelJacobiTimeProjection.q V t ≫ fixedToAmbient toRaw seedPoint seedPoint_toRaw := by
  rw [Category.assoc, fromSurface_toAmbient, fixed_q]

variable {Z : Scheme} (z : Z ⟶ (timeOpen V).toScheme)

/-- Base change of the proper correspondence along a marked time germ, including the dual
numbers, with the same embedded-curve scheme as the original open family. -/
def markedFiberIso :
    pullback z (projection V t) ≅ pullback
      (z ≫ fixedToTime toRaw V seedPoint seedPoint_toRaw ≫ inclusion V) (timeProjection V t) :=
  ((IsPullback.of_hasPullback z (projection V t)).paste_vert (markedTime_pullback V t)).isoPullback

@[reassoc (attr := simp)]
theorem markedFiberIso_fst :
    (markedFiberIso V t z).hom ≫ pullback.fst _ (timeProjection V t) = pullback.fst z (projection V t) :=
  ((IsPullback.of_hasPullback z (projection V t)).paste_vert (markedTime_pullback V t)).isoPullback_hom_fst

@[reassoc (attr := simp)]
theorem markedFiberIso_snd :
    (markedFiberIso V t z).hom ≫ pullback.snd _ (timeProjection V t) =
      pullback.snd z (projection V t) ≫ fixedToSurface toRaw V t seedPoint seedPoint_toRaw ≫
        fromSurface V t :=
  ((IsPullback.of_hasPullback z (projection V t)).paste_vert (markedTime_pullback V t)).isoPullback_hom_snd

@[reassoc (attr := simp)]
theorem markedFiberIso_toAmbient :
    (markedFiberIso V t z).hom ≫ pullback.snd _ (timeProjection V t) ≫ ambientProjection V t =
      pullback.snd z (projection V t) ≫ CycleQ2LiteralAbelJacobiTimeProjection.q V t ≫
        fixedToAmbient toRaw seedPoint seedPoint_toRaw := by
  simp only [markedFiberIso_snd_assoc, fromSurface_toAmbient, fixed_q]

/-- The marked fibre of the relative proper correspondence is the original plane-section curve. -/
def seedFiberIso (hV : seedBasePoint ∈ V) :=
  CycleQ2LiteralAbelJacobiTimeProjection.seedIso V t hV ≪≫ markedFiberIso V t (seedLift V hV)

/-- Its pullback at the original nonconstant dual-number tangent is the original embedded
first-order family. -/
def firstOrderFiberIso (hV : seedBasePoint ∈ V) :=
  firstOrderIso V t hV ≪≫ markedFiberIso V t (tangentLift V hV)

/-- The recovered seed curve has its original projection into the fixed threefold
over the marked coefficient point. -/
theorem seedFiberIso_toAmbient (hV : seedBasePoint ∈ V) :
    (seedFiberIso V t hV).hom ≫ pullback.snd _ (timeProjection V t) ≫ ambientProjection V t =
      (CycleQ2LiteralIncidenceTimeFamily.seedIso t).hom ≫ pullback.snd _ _ ≫
        CycleQ2LiteralIncidenceCylinderMap.toFixedThreefold t ≫ fixedToAmbient toRaw seedPoint seedPoint_toRaw := by
  simp only [seedFiberIso, Iso.trans_hom, Category.assoc, markedFiberIso_toAmbient,
    CycleQ2LiteralAbelJacobiTimeProjection.seed_to_q_assoc]

/-- The recovered first-order curve maps into the universal threefold via its original
embedded map into the fixed threefold. -/
theorem firstOrderFiberIso_toAmbient (hV : seedBasePoint ∈ V) :
    (firstOrderFiberIso V t hV).hom ≫ pullback.snd _ (timeProjection V t) ≫ ambientProjection V t =
      (CycleQ2LiteralIncidenceTimeFamily.firstOrderIso t).hom ≫ pullback.snd _ _ ≫
        CycleQ2LiteralIncidenceCylinderMap.toFixedThreefold t ≫ fixedToAmbient toRaw seedPoint seedPoint_toRaw := by
  simp only [firstOrderFiberIso, Iso.trans_hom, Category.assoc, markedFiberIso_toAmbient,
    CycleQ2LiteralAbelJacobiTimeProjection.firstOrder_to_q_assoc]

/-- Passing to the compactified full time family preserves the nonconstant tangent of
the marked moving curve. -/
theorem tangent_nonconstant (hV : seedBasePoint ∈ V) :
    relativeTangent toRaw V seedPoint seedPoint_toRaw hV ≫ inclusion V ≠
      CycleQ2LiteralIncidenceTimeCurve.structureDual ≫ seedLift V hV ≫
        fixedToTime toRaw V seedPoint seedPoint_toRaw ≫ inclusion V := by
  intro he
  apply CycleQ2LiteralIncidenceRelativeCylinder.tangent_nonconstant toRaw V seedPoint seedPoint_toRaw hV
  exact (cancel_mono (inclusion V)).mp (by simpa only [Category.assoc] using he)

theorem timeProjection_surjective (hs : Surjective (curveMap toRaw V t)) :
    Function.Surjective (timeProjection V t) := by
  let : IsDominant (fromSurface V t ≫ timeProjection V t) := by
    rw [fromSurface_toTime]
    infer_instance
  let := IsDominant.of_comp (fromSurface V t) (timeProjection V t)
  exact (timeProjection V t).surjective

/-- Every independent section triple supplies a proper relative correspondence covering its
proper time compactification and recovering the marked fixed-sextic surface on the time open. -/
theorem relative_correspondence_of_independent (t : Fin 3 → ℂ) (hi : AlgebraicIndependent ℚ t) :
    ∃ (V : parameterScheme.Opens) (_ : seedBasePoint ∈ V),
      IsProper (timeProjection V t ≫ structureMap V) ∧
      Function.Surjective (timeProjection V t) ∧ Function.Surjective (timeProjection V t ≫ structureMap V) ∧
      IsProper (ambientProjection V t) ∧
      IsOpenImmersion (fromSurface V t) ∧ IsDominant (fromSurface V t) ∧
      IsPullback (curveMap toRaw V t) (fromSurface V t) (inclusion V) (timeProjection V t) ∧
      IsPullback (projection V t) (fixedToSurface toRaw V t seedPoint seedPoint_toRaw ≫ fromSurface V t)
        (fixedToTime toRaw V seedPoint seedPoint_toRaw ≫ inclusion V) (timeProjection V t) := by
  obtain ⟨V, hV, _, _, _, hs, _, hbase⟩ := exists_surjective_completion t hi
  have htime := timeProjection_surjective V t hs
  exact ⟨V, hV, inferInstance, htime, (structureMap V).surjective.comp htime, inferInstance, inferInstance,
    inferInstance, timeOpen_pullback V t, markedTime_pullback V t⟩

end CycleQ2LiteralIncidenceRelativeCorrespondence

#print axioms CycleQ2LiteralIncidenceRelativeCorrespondence.relative_correspondence_of_independent
#print axioms CycleQ2LiteralIncidenceRelativeCorrespondence.firstOrderFiberIso

end

section

/-!
# The relative correspondence at the generic normalized sextic

Pulling the proper relative correspondence back to the fraction field of the
monic coefficient ring gives a proper surjective scheme for the chosen open
of each independent section triple. Its restriction to the corresponding
time open recovers the generic fibre of the original relative surface.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/


open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace CycleQ2CoefficientBaseChange

noncomputable section

/-- The map between the fibre products over a new coefficient scheme. -/
def changeMap {S T X Y : Scheme.{0}} (η : T ⟶ S)
    {u : X ⟶ S} {v : Y ⟶ S} (f : X ⟶ Y) (hf : f ≫ v = u) :
    pullback u η ⟶ pullback v η :=
  ((Over.pullback η).map (Over.homMk f hf : Over.mk u ⟶ Over.mk v)).left

theorem changeMap_fst {S T X Y : Scheme.{0}} (η : T ⟶ S)
    {u : X ⟶ S} {v : Y ⟶ S} (f : X ⟶ Y) (hf : f ≫ v = u) :
    changeMap η f hf ≫ pullback.fst v η = pullback.fst u η ≫ f :=
  pullback.lift_fst _ _ _

theorem changeMap_snd {S T X Y : Scheme.{0}} (η : T ⟶ S)
    {u : X ⟶ S} {v : Y ⟶ S} (f : X ⟶ Y) (hf : f ≫ v = u) :
    changeMap η f hf ≫ pullback.snd v η = pullback.snd u η :=
  pullback.lift_snd _ _ _

/-- Pulling every object in a cartesian square back through the same coefficient
morphism gives a cartesian square of the schemes over the new coefficients. -/
theorem isPullback_changeMap {S T A B C D : Scheme.{0}} (η : T ⟶ S)
    {a : A ⟶ S} {b : B ⟶ S} {c : C ⟶ S} {d : D ⟶ S}
    {f : A ⟶ B} {g : A ⟶ C} {i : B ⟶ D} {j : C ⟶ D}
    (hf : f ≫ b = a) (hg : g ≫ c = a) (hi : i ≫ d = b) (hj : j ≫ d = c)
    (H : IsPullback f g i j) :
    IsPullback (changeMap η f hf) (changeMap η g hg) (changeMap η i hi) (changeMap η j hj) := by
  let f' : Over.mk a ⟶ Over.mk b := Over.homMk f hf
  let g' : Over.mk a ⟶ Over.mk c := Over.homMk g hg
  let i' : Over.mk b ⟶ Over.mk d := Over.homMk i hi
  let j' : Over.mk c ⟶ Over.mk d := Over.homMk j hj
  have H' : IsPullback f' g' i' j' := IsPullback.of_map_of_faithful (Over.forget S) H
  exact ((H'.map (Over.pullback η)).map (Over.forget T))

end

end CycleQ2CoefficientBaseChange


open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
  CycleQ2CoefficientBaseChange CycleQ2LiteralIncidenceRelativeCorrespondence
  CycleQ2LiteralIncidenceRelativeCompletion CycleQ2LiteralIncidenceRelativeSpread
  CycleQ2LiteralIncidenceNormalizedSlice
open CycleQ2IncidenceEtaleParameter (parameterScheme)
open CycleQ2IncidenceSeedFiberCover (seedBasePoint)

namespace CycleQ2LiteralIncidenceGenericCorrespondence

noncomputable section

abbrev genericField := FractionRing MonicRing

def genericPoint : Spec (CommRingCat.of genericField) ⟶ monicBase :=
  Spec.map (CommRingCat.ofHom (algebraMap MonicRing genericField))

variable (V : parameterScheme.Opens) (t : Fin 3 → ℂ)

private theorem fromSurface_over :
    fromSurface V t ≫ timeProjection V t ≫ structureMap V =
      curveMap toRaw V t ≫ timeMap toRaw V := by
  rw [← Category.assoc, fromSurface_toTime, Category.assoc, inclusion_over]

theorem genericOpen_pullback :
    IsPullback
      (changeMap genericPoint (v := timeMap toRaw V) (curveMap toRaw V t) rfl)
      (changeMap genericPoint (fromSurface V t) (fromSurface_over V t))
      (changeMap genericPoint (inclusion V) (inclusion_over V))
      (changeMap genericPoint (v := structureMap V) (timeProjection V t) rfl) :=
  isPullback_changeMap genericPoint rfl (fromSurface_over V t) (inclusion_over V) rfl
    (timeOpen_pullback V t)

abbrev genericCorrespondence :=
  pullback (timeProjection V t ≫ structureMap V) genericPoint

abbrev toGenericField : genericCorrespondence V t ⟶ Spec (CommRingCat.of genericField) :=
  pullback.snd _ _

/-- The ambient fibre and the closed graph over the generic normalized coefficients. -/
abbrev genericAmbient := pullback ambientStructure genericPoint

private theorem ambientProjection_over :
    ambientProjection V t ≫ ambientStructure = timeProjection V t ≫ structureMap V :=
  (Category.assoc (embedding V t) (pullback.snd _ _) ambientStructure).trans
    ((congrArg (fun a => embedding V t ≫ a)
      (pullback.condition (f := structureMap V) (g := ambientStructure)).symm).trans
      (Category.assoc (embedding V t) (pullback.fst _ _) (structureMap V)).symm)

def genericAmbientProjection : genericCorrespondence V t ⟶ genericAmbient :=
  changeMap genericPoint (ambientProjection V t) (ambientProjection_over V t)

theorem genericAmbientProjection_proper :
    IsProper (genericAmbientProjection V t) := by
  let u := timeProjection V t ≫ structureMap V
  let v := ambientStructure
  let q := ambientProjection V t
  let g := genericAmbientProjection V t
  have h₁ : g ≫ pullback.snd v genericPoint = pullback.snd u genericPoint :=
    changeMap_snd genericPoint q (ambientProjection_over V t)
  have h₂ : g ≫ pullback.fst v genericPoint = pullback.fst u genericPoint ≫ q :=
    changeMap_fst genericPoint q (ambientProjection_over V t)
  have hp : IsPullback (pullback.fst u genericPoint) (g ≫ pullback.snd v genericPoint)
      (q ≫ v) genericPoint := by
    rw [h₁, ambientProjection_over V t]
    exact IsPullback.of_hasPullback u genericPoint
  have hq : IsPullback (pullback.fst u genericPoint) g q (pullback.fst v genericPoint) :=
    hp.of_bot h₂.symm (IsPullback.of_hasPullback v genericPoint)
  exact IsProper.isStableUnderBaseChange.of_isPullback hq (inferInstance : IsProper (ambientProjection V t))

theorem genericAmbientProjection_closed :
    IsClosed (Set.range (genericAmbientProjection V t)) := by
  letI := genericAmbientProjection_proper V t
  exact (genericAmbientProjection V t).isClosedMap.isClosed_range

theorem proper_surjective_generic_correspondence (hi : AlgebraicIndependent ℚ t) :
    ∃ (V : parameterScheme.Opens) (_ : seedBasePoint ∈ V),
      IsProper (toGenericField V t) ∧ Function.Surjective (toGenericField V t) := by
  obtain ⟨W, hW, hproper, _, hsurjective, _⟩ := relative_correspondence_of_independent t hi
  let : IsProper (timeProjection W t ≫ structureMap W) := hproper
  let : Surjective (timeProjection W t ≫ structureMap W) := ⟨hsurjective⟩
  exact ⟨W, hW, inferInstance, (toGenericField W t).surjective⟩

local instance (X : Scheme.{0}) : HasExt.{1} (CycleQ2InjectiveCech.AbSheaf (show TopCat from X)) :=
  HasExt.standard _

/-- The same marked family supplies the nonzero coherent pullback at the
original fiber and the proper graph over the generic coefficients. -/
theorem exists_proper_generic_with_marked_nonzero :
    ∃ (u : Fin 3 → ℂ) (W : parameterScheme.Opens) (_ : seedBasePoint ∈ W),
      AlgebraicIndependent ℚ u ∧
      IsProper (toGenericField W u) ∧ Function.Surjective (toGenericField W u) ∧
      IsProper (genericAmbientProjection W u) ∧
      CycleQ2LiteralAbelJacobiQPullbackDerived.qHodge W u
        CycleQ2LiteralThreefoldTestClass.ambientTestClass ≠ 0 := by
  obtain ⟨u, hu, hreg, _, _, _⟩ := CycleQ2LiteralAbelJacobiTimeFamily.exists_smooth_time_family
  obtain ⟨W, hW, hp, hs⟩ := proper_surjective_generic_correspondence u hu
  exact ⟨u, W, hW, hu, hp, hs, genericAmbientProjection_proper W u,
    CycleQ2LiteralNonzeroSweptRestriction.pull_nonzero u hu hreg W hW⟩

end

end CycleQ2LiteralIncidenceGenericCorrespondence

#print axioms CycleQ2LiteralIncidenceGenericCorrespondence.genericOpen_pullback
#print axioms CycleQ2LiteralIncidenceGenericCorrespondence.proper_surjective_generic_correspondence

end

#print axioms CycleQ2LiteralIncidenceGenericCorrespondence.exists_proper_generic_with_marked_nonzero
