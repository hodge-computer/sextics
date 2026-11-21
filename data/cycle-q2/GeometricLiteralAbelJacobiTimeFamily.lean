import Proposal.GeometricLiteralIncidenceTimeFamily
import Proposal.GeometricLiteralAbelJacobiSeedLiftConeRegular
import Proposal.GeometricLiteralAbelJacobiChartRegular
import Proposal.GeometricLiteralAbelJacobiBertiniMinor
import Proposal.GeometricLiteralAbelJacobiSeedLiftDimension
import Proposal.GeometricFirstOrderNeighborhood

/-!
# Smooth moving curves over the original pointed fixed-sextic parameter curve

The smooth incidence neighborhood pulls back to an open in the original
one-dimensional time curve. Its retained tangent still gives the same
first-order section scheme. The normal to the seed cubic on that time
family has a nonzero value in the fixed threefold.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace CycleQ2LiteralAbelJacobiTimeFamily

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
  CycleQ2LiteralIncidenceTimeCurve CycleQ2IncidenceEtaleParameter
  CycleQ2IncidencePolynomialJacobianBinding CycleQ2IncidenceFirstOrder
  CycleQ2FirstOrderNeighborhood CycleQ2FirstOrderCurve
  CycleQ2IncidenceSeedFiberCover CycleQ2IncidenceChartFiberScheme
  CycleQ2IncidenceProperNeighborhood CycleQ2RelativeConstantCurve
  CycleQ2RelativeCurveNeighborhood CycleQ2FirstOrderChartReduction
  CycleQ2LiteralAbelJacobiRelativeNormal

variable (V : parameterScheme.Opens)

abbrev timeOpen := toIncidence ⁻¹ᵁ V

/-- Pullback of the original incidence family to the fixed-sextic open. -/
abbrev family (t : Fin 3 → ℂ) :=
  pullback (toIncidence ∣_ V) ((relativeCurveToBase incidencePoint t) ∣_ V)

def projection (t : Fin 3 → ℂ) : family V t ⟶ (timeOpen V).toScheme := pullback.fst _ _

private theorem seed_mem (hV : seedBasePoint ∈ V) (s : Spec (CommRingCat.of ℂ)) :
    seed s ∈ timeOpen V := by
  change (seed ≫ toIncidence) s ∈ V
  rw [seed_to_incidence, Subsingleton.elim s default]
  exact hV

def seedLift (hV : seedBasePoint ∈ V) : Spec (CommRingCat.of ℂ) ⟶ (timeOpen V).toScheme :=
  IsOpenImmersion.lift (timeOpen V).ι seed (by rintro _ ⟨s, rfl⟩; exact ⟨⟨_, seed_mem V hV s⟩, rfl⟩)

@[reassoc (attr := simp)] theorem seedLift_fac (hV : seedBasePoint ∈ V) :
    seedLift V hV ≫ (timeOpen V).ι = seed := IsOpenImmersion.lift_fac _ _ _

def tangentLift (hV : seedBasePoint ∈ V) :
    Spec (CommRingCat.of (DualNumber ℂ)) ⟶ (timeOpen V).toScheme :=
  IsOpenImmersion.lift (timeOpen V).ι timeTangent (by
    rintro _ ⟨s, rfl⟩
    refine ⟨⟨_, ?_⟩, rfl⟩
    change (timeTangent ≫ toIncidence) s ∈ V
    rw [timeTangent_to_incidence, firstOrderParameterPoint_apply]
    exact hV)

@[reassoc (attr := simp)] theorem tangentLift_fac (hV : seedBasePoint ∈ V) :
    tangentLift V hV ≫ (timeOpen V).ι = timeTangent := IsOpenImmersion.lift_fac _ _ _

theorem tangentLift_at_seed (hV : seedBasePoint ∈ V) :
    firstOrderClosedPoint ≫ tangentLift V hV = seedLift V hV := by
  apply (cancel_mono (timeOpen V).ι).mp
  simp only [Category.assoc, tangentLift_fac, seedLift_fac, timeTangent_at_seed]

theorem tangentLift_nonconstant (hV : seedBasePoint ∈ V) :
    tangentLift V hV ≠ structureDual ≫ seedLift V hV := by
  intro he
  apply timeTangent_nonconstant
  simpa only [Category.assoc, tangentLift_fac, seedLift_fac] using
    (congrArg (fun f => f ≫ (timeOpen V).ι) he)

variable (t : Fin 3 → ℂ)

private theorem tangent_pullback (hV : seedBasePoint ∈ V) :
    IsPullback (pullback.fst (tangentLift V hV) (projection V t))
      (pullback.snd _ _ ≫ pullback.snd (toIncidence ∣_ V) _ ≫
        ((relativeCurveToBase incidencePoint t) ⁻¹ᵁ V).ι)
      firstOrderParameterPoint (relativeCurveToBase incidencePoint t) := by
  have h₁ := (IsPullback.of_hasPullback (tangentLift V hV) (projection V t)).paste_vert
    (IsPullback.of_hasPullback (toIncidence ∣_ V) ((relativeCurveToBase incidencePoint t) ∣_ V))
  have h₂ := h₁.paste_vert (isPullback_morphismRestrict (relativeCurveToBase incidencePoint t) V)
  simpa only [Category.assoc, morphismRestrict_ι, tangentLift_fac_assoc,
    timeTangent_to_incidence] using h₂

/-- The pointed germ on the one-dimensional open is the original first-order scheme. -/
def firstOrderIso (hV : seedBasePoint ∈ V) :
    firstOrderCurve t ≅ pullback (tangentLift V hV) (projection V t) :=
  (firstOrderCurve_isPullback t).flip.isoPullback ≪≫ (tangent_pullback V t hV).isoPullback.symm

@[reassoc, simp] theorem firstOrderIso_toBase (hV : seedBasePoint ∈ V) :
    (firstOrderIso V t hV).hom ≫ pullback.fst _ _ = firstOrderCurveToBase t := by
  simp [firstOrderIso]

/-- The germ comparison commutes with its projection to the original projective section family. -/
@[reassoc, simp] theorem firstOrderIso_toOriginal (hV : seedBasePoint ∈ V) :
    (firstOrderIso V t hV).hom ≫ pullback.snd _ _ ≫
      pullback.snd (toIncidence ∣_ V) _ ≫ ((relativeCurveToBase incidencePoint t) ⁻¹ᵁ V).ι =
        firstOrderCurveToOriginalCurve t := by
  simp [firstOrderIso]

/-- Every independent original section vector integrates its first-order motion on a fixed-sextic curve. -/
theorem time_family_of_independent (t : Fin 3 → ℂ) (hi : AlgebraicIndependent ℚ t) :
      ∃ (V : parameterScheme.Opens) (hV : seedBasePoint ∈ V),
        SmoothOfRelativeDimension 1 ((timeOpen V).ι ≫ toComplex) ∧
        SmoothOfRelativeDimension 1 (projection V t) ∧
        SmoothOfRelativeDimension 2 (projection V t ≫ (timeOpen V).ι ≫ toComplex) ∧
        IsProper (projection V t) ∧ Function.Surjective (projection V t) ∧
        tangentLift V hV ≠ structureDual ≫ seedLift V hV ∧
        ∃ hf : ∀ i, Module.Flat (DualNumber ℂ) (FirstOrderCurveChart t i),
          ∃ j : Fin 3, @relativeNormal t j.succ (hf j.succ)
            ((idealOnT t j.succ).toCotangent (cubicClass t j.succ)) ≠ 0 := by
  have hm := CycleQ2LiteralAbelJacobiBertiniMinor.prime_minor_of_independent t hi
  obtain ⟨_, hf, j, hj⟩ := CycleQ2LiteralAbelJacobiSeedLiftConeRegular.smooth_neighborhood_and_nonzero_normal
    t (CycleQ2LiteralAbelJacobiSeedLiftDimension.smooth_seed_of_seedMinorCover t hm)
  obtain ⟨V, hv, hs, hp, hsurj⟩ :=
    CycleQ2LiteralAbelJacobiSeedLiftDimension.dimension_one_neighborhood_of_seedMinorCover t hm
  have : Surjective ((relativeCurveToBase incidencePoint t) ∣_ V) := ⟨hsurj⟩
  have := smooth_parameter_curve
  have ht : SmoothOfRelativeDimension 1 ((timeOpen V).ι ≫ toComplex) :=
    smoothOfRelativeDimension_comp 0 1 _ _
  let _ : MorphismProperty.IsStableUnderBaseChange (@SmoothOfRelativeDimension 1) :=
    smoothOfRelativeDimension_isStableUnderBaseChange 1
  have hc : SmoothOfRelativeDimension 1 (projection V t) :=
    MorphismProperty.pullback_fst _ _ hs
  refine ⟨V, hv, ht, hc, smoothOfRelativeDimension_comp 1 1 _ _, ?_, ?_,
    tangentLift_nonconstant V hv, hf, j, hj⟩
  · unfold projection
    infer_instance
  · exact (pullback.fst (toIncidence ∣_ V) ((relativeCurveToBase incidencePoint t) ∣_ V)).surjective

theorem exists_smooth_time_family :
    ∃ t : Fin 3 → ℂ, AlgebraicIndependent ℚ t ∧
      (∀ i : Fin 3, CycleQ2SeedSectionAffineInjective.ChartRegular t i) ∧
      ∃ (V : parameterScheme.Opens) (hV : seedBasePoint ∈ V),
        SmoothOfRelativeDimension 1 ((timeOpen V).ι ≫ toComplex) ∧
        SmoothOfRelativeDimension 1 (projection V t) ∧
        SmoothOfRelativeDimension 2 (projection V t ≫ (timeOpen V).ι ≫ toComplex) ∧
        IsProper (projection V t) ∧ Function.Surjective (projection V t) ∧
        tangentLift V hV ≠ structureDual ≫ seedLift V hV ∧
        ∃ hf : ∀ i, Module.Flat (DualNumber ℂ) (FirstOrderCurveChart t i),
          ∃ j : Fin 3, @relativeNormal t j.succ (hf j.succ)
            ((idealOnT t j.succ).toCotangent (cubicClass t j.succ)) ≠ 0 := by
  obtain ⟨t, hi, _, hchart, _⟩ := CycleQ2LiteralAbelJacobiChartRegular.exists_independent_chartRegular
  exact ⟨t, hi, hchart, time_family_of_independent t hi⟩

end CycleQ2LiteralAbelJacobiTimeFamily
end

#print axioms CycleQ2LiteralAbelJacobiTimeFamily.firstOrderIso_toBase
#print axioms CycleQ2LiteralAbelJacobiTimeFamily.firstOrderIso_toOriginal
#print axioms CycleQ2LiteralAbelJacobiTimeFamily.exists_smooth_time_family
