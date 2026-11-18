import Proposal.GeometricLiteralTimeFamilyEmbedding
import Proposal.GeometricLiteralTimeCorrespondenceCompletion

/-!
# Recovery of the smooth family from the proper correspondence

Over the original parameter open, the joint map is a closed immersion. Hence
restricting the proper correspondence along the original time open recovers
the original family as a scheme with both its projections.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2LiteralTimeFamilyRecovery

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
  CycleQ2LiteralIncidenceTimeCurve CycleQ2LiteralIncidenceCylinderMap
  CycleQ2LiteralAbelJacobiTimeFamily CycleQ2LiteralAbelJacobiTimeProjection
  CycleQ2LiteralTimeCurveCompletion CycleQ2LiteralTimeCorrespondenceCompletion
open CycleQ2IncidenceEtaleParameter (parameterScheme)

variable (V : parameterScheme.Opens) (t : Fin 3 → ℂ)

instance openJoint_mono : Mono (openJoint V t) where
  right_cancellation {Z} g h he := by
    apply (cancel_mono (familyToFull V t)).mp
    let := CycleQ2LiteralTimeFamilyEmbedding.joint_mono t
    apply (cancel_mono (CycleQ2LiteralTimeFamilyEmbedding.joint t)).mp
    apply pullback.hom_ext
    · have hp := congrArg (fun z => z ≫ pullback.fst (inclusion (timeOpen V)) (prBase V)) he
      simp only [Category.assoc, openJoint, pullback.lift_fst] at hp
      simpa only [Category.assoc, CycleQ2LiteralTimeFamilyEmbedding.joint_toCurve,
        familyToFull_toCurve] using congrArg (fun z => z ≫ (timeOpen V).ι) hp
    · have hq := congrArg (fun z => z ≫ openProductInclusion V ≫ prFixed V) he
      simp only [Category.assoc, openJoint, openProductInclusion, pullback.lift_snd_assoc,
        CycleQ2LiteralTimeCorrespondenceCompletion.joint, prFixed, pullback.lift_snd] at hq
      simpa only [Category.assoc, CycleQ2LiteralTimeFamilyEmbedding.joint_toFixedThreefold,
        q] using hq

instance openJoint_isClosedImmersion : IsClosedImmersion (openJoint V t) :=
  (IsClosedImmersion.iff_isProper_and_mono _).mpr ⟨openJoint_proper V t, inferInstance⟩

theorem openProduct_pullback :
    IsPullback (openJoint V t) (fromFamily V t) (openProductInclusion V) (embedding V t) := by
  have h : IsPullback (openJoint V t) (openJoint V t).toImage (𝟙 _) (openJoint V t).imageι :=
    IsPullback.of_vert_isIso ⟨by simp⟩
  simpa only [Category.id_comp, fromFamily] using h.paste_vert (recovers_open_image V t)

/-- The original smooth family is the restriction of the proper correspondence
to the original dense parameter open. -/
theorem timeOpen_pullback :
    IsPullback (projection V t) (fromFamily V t) (inclusion (timeOpen V)) (baseProjection V t) := by
  have h := (openProduct_pullback V t).paste_horiz
    (IsPullback.of_hasPullback (inclusion (timeOpen V)) (prBase V))
  simpa only [openJoint, pullback.lift_fst, baseProjection] using h

theorem fromFamily_open : IsOpenImmersion (fromFamily V t) :=
  MorphismProperty.of_isPullback (timeOpen_pullback V t) inferInstance

end CycleQ2LiteralTimeFamilyRecovery

#print axioms CycleQ2LiteralTimeFamilyRecovery.openJoint_isClosedImmersion
#print axioms CycleQ2LiteralTimeFamilyRecovery.timeOpen_pullback
#print axioms CycleQ2LiteralTimeFamilyRecovery.fromFamily_open
