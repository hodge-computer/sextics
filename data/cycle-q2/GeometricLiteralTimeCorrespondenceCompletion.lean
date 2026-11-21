import Proposal.GeometricLiteralTimeCurveCompletion
import Proposal.GeometricLiteralAbelJacobiTimeProjection
import Proposal.GeometricImmersionImageClosure
import Proposal.GeometricLiteralAmbientCylinder

/-!
# Closure of the moving curve correspondence over the proper time base

The original two projections define a morphism into the product of the time
open and the fixed threefold. Close its scheme-theoretic image in the product
with the proper parameter base. Restriction to the original open recovers
the original scheme-theoretic image, including its scheme structure.
Both projections from the closure are proper.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2LiteralTimeCorrespondenceCompletion

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
  CycleQ2LiteralIncidenceTimeCurve CycleQ2LiteralIncidenceCylinderMap
  CycleQ2LiteralAbelJacobiTimeFamily CycleQ2LiteralAbelJacobiTimeProjection
  CycleQ2LiteralTimeCurveCompletion
open CycleQ2IncidenceEtaleParameter (parameterScheme)
open CycleQ2IncidenceSeedFiberCover (seedBasePoint)

/-- The same dual-number map remains nonconstant after passage to the proper base. -/
theorem tangent_nonconstant (V : parameterScheme.Opens) (hV : seedBasePoint ∈ V) :
    tangentLift V hV ≫ inclusion (timeOpen V) ≠
      structureDual ≫ seedLift V hV ≫ inclusion (timeOpen V) := by
  intro h
  apply tangentLift_nonconstant V hV
  exact (cancel_mono (inclusion (timeOpen V))).mp (by simpa only [Category.assoc] using h)

/-- The selected smooth parameter germ is a dense open of a proper complex scheme
and its retained infinitesimal motion is nonconstant there. -/
theorem exists_pointed_completion :
    ∃ (V : parameterScheme.Opens) (hV : seedBasePoint ∈ V),
      SmoothOfRelativeDimension 1 ((timeOpen V).ι ≫ toComplex) ∧
      IsOpenImmersion (inclusion (timeOpen V)) ∧ IsDominant (inclusion (timeOpen V)) ∧
      IsProper (structureMap (timeOpen V)) ∧
      tangentLift V hV ≫ inclusion (timeOpen V) ≠
        structureDual ≫ seedLift V hV ≫ inclusion (timeOpen V) := by
  obtain ⟨_, _, _, V, hV, hdim, _⟩ := exists_smooth_time_family
  exact ⟨V, hV, hdim, inferInstance, inferInstance, inferInstance, tangent_nonconstant V hV⟩

variable (V : parameterScheme.Opens) (t : Fin 3 → ℂ)

abbrev Base := Completion (timeOpen V)
abbrev fixedStructure : FixedThreefold ⟶ Spec (CommRingCat.of ℂ) :=
  pullback.fst seedSextic universalAmbientToBase

abbrev Product := pullback (structureMap (timeOpen V)) fixedStructure

abbrev prBase : Product V ⟶ Base V := pullback.fst _ _
abbrev prFixed : Product V ⟶ FixedThreefold := pullback.snd _ _

/-- The product restricted to the indicated open of the completed base. -/
abbrev OpenProduct := pullback (inclusion (timeOpen V)) (prBase V)

abbrev openProductInclusion : OpenProduct V ⟶ Product V := pullback.snd _ _

def joint : family V t ⟶ Product V :=
  pullback.lift (projection V t ≫ inclusion (timeOpen V)) (q V t) (by
    simp only [Category.assoc, inclusion_over, q_overComplex, fixedStructure])

def openJoint : family V t ⟶ OpenProduct V :=
  pullback.lift (projection V t) (joint V t) (pullback.lift_fst _ _ _).symm

/-- The closed correspondence over the original open time base. -/
abbrev OpenImage := (openJoint V t).image

def imageMap : OpenImage V t ⟶ Product V :=
  (openJoint V t).imageι ≫ openProductInclusion V

instance : QuasiCompact (imageMap V t) := by
  unfold imageMap openProductInclusion
  infer_instance

abbrev Correspondence := (imageMap V t).image

abbrev embedding : Correspondence V t ⟶ Product V := (imageMap V t).imageι
abbrev fromOpenImage : OpenImage V t ⟶ Correspondence V t := (imageMap V t).toImage

def fromFamily : family V t ⟶ Correspondence V t :=
  (openJoint V t).toImage ≫ fromOpenImage V t

def baseProjection : Correspondence V t ⟶ Base V := embedding V t ≫ prBase V
def fixedProjection : Correspondence V t ⟶ FixedThreefold := embedding V t ≫ prFixed V

instance : IsProper (baseProjection V t) := by
  let : IsProper fixedStructure := CycleQ2LiteralAmbientCylinder.fixed_proper
  unfold baseProjection prBase
  infer_instance

instance : IsProper (fixedProjection V t) := by
  unfold fixedProjection prFixed
  infer_instance

@[reassoc (attr := simp)] theorem fromFamily_embedding :
    fromFamily V t ≫ embedding V t = joint V t := by
  rw [fromFamily, Category.assoc, Scheme.Hom.toImage_imageι, imageMap,
    ← Category.assoc, Scheme.Hom.toImage_imageι]
  exact pullback.lift_snd _ _ _

@[reassoc (attr := simp)] theorem fromFamily_toBase :
    fromFamily V t ≫ baseProjection V t = projection V t ≫ inclusion (timeOpen V) := by
  rw [baseProjection, ← Category.assoc, fromFamily_embedding]
  exact pullback.lift_fst _ _ _

@[reassoc (attr := simp)] theorem fromFamily_toFixed :
    fromFamily V t ≫ fixedProjection V t = q V t := by
  rw [fixedProjection, ← Category.assoc, fromFamily_embedding]
  exact pullback.lift_snd _ _ _

theorem openJoint_proper : IsProper (openJoint V t) := by
  let : IsProper fixedStructure := CycleQ2LiteralAmbientCylinder.fixed_proper
  let : IsProper (CycleQ2LiteralIncidenceTimeFamily.toCurve t) :=
    CycleQ2LiteralIncidenceTimeFamily.family_proper t
  have hp : IsProper (projection V t) :=
    MorphismProperty.of_isPullback (family_square V t).flip inferInstance
  let : IsProper (openJoint V t ≫ pullback.fst (inclusion (timeOpen V)) (prBase V)) := by
    simpa only [openJoint, pullback.lift_fst] using hp
  exact IsProper.of_comp _ (pullback.fst (inclusion (timeOpen V)) (prBase V))

/-- Over the original open every point of the closed image comes from
the original smooth time family. -/
theorem openImage_covered : Function.Surjective (openJoint V t).toImage := by
  let := openJoint_proper V t
  exact (openJoint V t).toImage.surjective

/-- The closed image scheme on the smooth parameter neighborhood is exactly
the open part of the complete correspondence. -/
theorem recovers_open_image :
    IsPullback (openJoint V t).imageι (fromOpenImage V t) (openProductInclusion V)
      (embedding V t) :=
  CycleQ2ImmersionImageClosure.closed_in_open_pullback (openJoint V t).imageι
    (openProductInclusion V)

instance : IsOpenImmersion (fromOpenImage V t) :=
  MorphismProperty.of_isPullback (recovers_open_image V t) inferInstance

instance : IsDominant (fromOpenImage V t) :=
  inferInstanceAs (IsDominant (imageMap V t).toImage)

instance : IsDominant (fromFamily V t) := by
  let : Surjective (openJoint V t).toImage := ⟨openImage_covered V t⟩
  unfold fromFamily
  infer_instance

/-- A family surjective over the dense open continues to cover the completed base. -/
theorem baseProjection_surjective (h : Function.Surjective (projection V t)) :
    Function.Surjective (baseProjection V t) := by
  let : Surjective (projection V t) := ⟨h⟩
  let : IsDominant (fromFamily V t ≫ baseProjection V t) := by
    rw [fromFamily_toBase]
    infer_instance
  let := IsDominant.of_comp (fromFamily V t) (baseProjection V t)
  exact (baseProjection V t).surjective

/-- The smooth moving curves supply a proper correspondence surjecting onto
a proper pointed parameter base, with the original map into the fixed threefold. -/
theorem exists_proper_correspondence :
    ∃ (t : Fin 3 → ℂ) (V : parameterScheme.Opens) (hV : seedBasePoint ∈ V),
      SmoothOfRelativeDimension 1 (projection V t) ∧
      IsProper (baseProjection V t) ∧ Function.Surjective (baseProjection V t) ∧
      IsProper (fixedProjection V t) ∧ fromFamily V t ≫ fixedProjection V t = q V t ∧
      tangentLift V hV ≫ inclusion (timeOpen V) ≠
        structureDual ≫ seedLift V hV ≫ inclusion (timeOpen V) := by
  obtain ⟨t, _, _, V, hV, _, hd, _, _, hs, _⟩ := exists_smooth_time_family
  exact ⟨t, V, hV, hd, inferInstance, baseProjection_surjective V t hs, inferInstance,
    fromFamily_toFixed V t, tangent_nonconstant V hV⟩

end CycleQ2LiteralTimeCorrespondenceCompletion

#print axioms CycleQ2LiteralTimeCorrespondenceCompletion.openImage_covered
#print axioms CycleQ2LiteralTimeCorrespondenceCompletion.recovers_open_image
#print axioms CycleQ2LiteralTimeCorrespondenceCompletion.exists_proper_correspondence
