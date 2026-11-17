import Proposal.GeometricLiteralAbelJacobiTimeFamily
import Proposal.GeometricLiteralIncidenceCylinderMap

/-!
# The second projection of the smooth fixed-sextic family

Restricting the incidence correspondence to the pointed time curve gives an
open subfamily with its original map to the fixed sextic threefold. Its maps on
the seed and on the infinitesimal germ agree with the original embedded family.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace CycleQ2LiteralAbelJacobiTimeProjection

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry CycleQ2IncidenceEtaleParameter
  CycleQ2LiteralIncidenceTimeCurve CycleQ2RelativeConstantCurve CycleQ2IncidencePolynomialJacobianBinding
  CycleQ2LiteralAbelJacobiTimeFamily CycleQ2LiteralIncidenceCylinderMap
  CycleQ2IncidenceSeedFiberCover CycleQ2IncidenceChartFiberScheme CycleQ2RelativeCurveNeighborhood
  CycleQ2FirstOrderCurve CycleQ2SpecializedProjectiveCurve CycleQ2IncidenceFirstOrder
  CycleQ2RelativeCurveSeedFiberIso

variable (V : parameterScheme.Opens) (t : Fin 3 → ℂ)

private abbrev sourceToOriginal := pullback.snd (toIncidence ∣_ V) ((relativeCurveToBase incidencePoint t) ∣_ V) ≫
  ((relativeCurveToBase incidencePoint t) ⁻¹ᵁ V).ι

private theorem original_square : IsPullback (projection V t) (sourceToOriginal V t)
    ((timeOpen V).ι ≫ toIncidence) (relativeCurveToBase incidencePoint t) := by
  have h := (IsPullback.of_hasPullback (toIncidence ∣_ V) ((relativeCurveToBase incidencePoint t) ∣_ V)).paste_vert
    (isPullback_morphismRestrict (relativeCurveToBase incidencePoint t) V)
  simpa only [projection, sourceToOriginal, family, timeOpen, morphismRestrict_ι] using h

/-- The map into the complete fixed-sextic incidence correspondence. -/
def familyToFull : family V t ⟶ CycleQ2LiteralIncidenceTimeFamily.Family t :=
  pullback.lift (projection V t ≫ (timeOpen V).ι) (sourceToOriginal V t)
    (by simpa only [Category.assoc] using (original_square V t).w)

@[reassoc (attr := simp)] theorem familyToFull_toCurve :
    familyToFull V t ≫ CycleQ2LiteralIncidenceTimeFamily.toCurve t = projection V t ≫ (timeOpen V).ι :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)] theorem familyToFull_toOriginal :
    familyToFull V t ≫ CycleQ2LiteralIncidenceTimeFamily.toOriginal t = sourceToOriginal V t :=
  pullback.lift_snd _ _ _

theorem family_square : IsPullback (projection V t) (familyToFull V t) (timeOpen V).ι
    (CycleQ2LiteralIncidenceTimeFamily.toCurve t) := by
  have h : IsPullback (projection V t) (familyToFull V t ≫ CycleQ2LiteralIncidenceTimeFamily.toOriginal t)
      ((timeOpen V).ι ≫ toIncidence) (relativeCurveToBase incidencePoint t) := by
    rw [familyToFull_toOriginal]
    exact original_square V t
  exact h.of_bot (familyToFull_toCurve V t).symm (IsPullback.of_hasPullback ..)

instance : IsOpenImmersion (familyToFull V t) :=
  MorphismProperty.of_isPullback (family_square V t) inferInstance

/-- The second cylinder projection on the actual smooth open time family. -/
def q : family V t ⟶ FixedThreefold := familyToFull V t ≫ toFixedThreefold t

@[reassoc, simp] theorem q_overComplex : q V t ≫ pullback.fst seedSextic universalAmbientToBase =
    projection V t ≫ (timeOpen V).ι ≫ toComplex := by simp [q]

@[reassoc, simp] theorem q_original : q V t ≫ pullback.snd seedSextic universalAmbientToBase =
    sourceToOriginal V t ≫ originalToAmbient t := by simp [q]

variable (hV : seedBasePoint ∈ V)

private theorem seed_square : IsPullback (pullback.fst (seedLift V hV) (projection V t))
    (pullback.snd _ _ ≫ familyToFull V t) seed (CycleQ2LiteralIncidenceTimeFamily.toCurve t) := by
  have h := (IsPullback.of_hasPullback (seedLift V hV) (projection V t)).paste_vert (family_square V t)
  simpa only [seedLift_fac] using h

/-- The closed fibre on the open is the original projective seed curve. -/
def seedIso : specializedCurve (seedPoint (57 : ℂ) Complex.I) t ≅ pullback (seedLift V hV) (projection V t) :=
  CycleQ2LiteralIncidenceTimeFamily.seedIso t ≪≫ (seed_square V t hV).isoPullback.symm

@[reassoc] theorem seed_to_q : (seedIso V t hV).hom ≫ pullback.snd _ _ ≫ q V t =
    (CycleQ2LiteralIncidenceTimeFamily.seedIso t).hom ≫ pullback.snd _ _ ≫ toFixedThreefold t := by
  have e := congrArg (fun g => (CycleQ2LiteralIncidenceTimeFamily.seedIso t).hom ≫ g ≫ toFixedThreefold t)
    (seed_square V t hV).isoPullback_inv_snd
  simpa only [q, seedIso, Iso.trans_hom, Iso.symm_hom, Category.assoc] using e

private theorem firstOrder_to_full :
    (firstOrderIso V t hV).hom ≫ pullback.snd _ _ ≫ familyToFull V t =
      (CycleQ2LiteralIncidenceTimeFamily.firstOrderIso t).hom ≫ pullback.snd _ _ := by
  apply pullback.hom_ext
  · change _ ≫ CycleQ2LiteralIncidenceTimeFamily.toCurve t = _ ≫ CycleQ2LiteralIncidenceTimeFamily.toCurve t
    simp only [Category.assoc, familyToFull_toCurve, ← pullback.condition_assoc,
      ← pullback.condition, firstOrderIso_toBase_assoc, CycleQ2LiteralIncidenceTimeFamily.firstOrderIso_toBase_assoc,
      tangentLift_fac]
  · change _ ≫ CycleQ2LiteralIncidenceTimeFamily.toOriginal t = _ ≫ CycleQ2LiteralIncidenceTimeFamily.toOriginal t
    simp only [Category.assoc, familyToFull_toOriginal, sourceToOriginal, firstOrderIso_toOriginal,
      CycleQ2LiteralIncidenceTimeFamily.firstOrderIso_toOriginal]

/-- Pulling the second cylinder projection back along the retained tangent gives the original
infinitesimal embedded curve in the fixed hypersurface. -/
@[reassoc] theorem firstOrder_to_q : (firstOrderIso V t hV).hom ≫ pullback.snd _ _ ≫ q V t =
    (CycleQ2LiteralIncidenceTimeFamily.firstOrderIso t).hom ≫ pullback.snd _ _ ≫ toFixedThreefold t := by
  simpa only [q, Category.assoc] using
    (congrArg (fun g => g ≫ toFixedThreefold t) (firstOrder_to_full V t hV))

end CycleQ2LiteralAbelJacobiTimeProjection
end

#print axioms CycleQ2LiteralAbelJacobiTimeProjection.family_square
#print axioms CycleQ2LiteralAbelJacobiTimeProjection.seed_to_q
#print axioms CycleQ2LiteralAbelJacobiTimeProjection.firstOrder_to_q
