import Proposal.GeometricLiteralTimeFamilyRecovery
import Proposal.GeometricLiteralSweptSupport
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-!
# The scheme-theoretic swept image of the completed correspondence

The proper correspondence and its original open family have the same
scheme-theoretic image in the fixed threefold. The second projection of the
correspondence is proper and surjective onto that closed subscheme.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace CycleQ2LiteralProperSweptSupport

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Set
  CycleQ2LiteralIncidenceTimeCurve CycleQ2LiteralIncidenceCylinderMap
  CycleQ2LiteralAbelJacobiTimeFamily CycleQ2LiteralAbelJacobiTimeProjection
  CycleQ2LiteralTimeCorrespondenceCompletion CycleQ2LiteralSweptSupport
open CycleQ2IncidenceEtaleParameter (parameterScheme)
open CycleQ2IncidenceSeedFiberCover (seedBasePoint)

private theorem toImage_ker {X Y : Scheme} (f : X ⟶ Y) :
    f.toImage.ker = ⊥ := by
  have h : (f.toImage.ker.subschemeι ≫ f.imageι).ker = f.imageι.ker := by
    rw [Scheme.Hom.ker_comp, Scheme.IdealSheafData.ker_subschemeι,
      Scheme.IdealSheafData.map_ker, Scheme.Hom.toImage_imageι]
    exact f.ker.ker_subschemeι.symm
  have : IsIso f.toImage.ker.subschemeι :=
    IsClosedImmersion.isIso_of_ker_eq _ _ _ rfl h
  exact f.toImage.ker.ker_subschemeι.symm.trans f.toImage.ker.subschemeι.ker_eq_bot_of_isIso

variable (V : parameterScheme.Opens) (t : Fin 3 → ℂ)

/-- The original family is schematically dense inside the completed correspondence. -/
theorem fromFamily_ker : (fromFamily V t).ker = ⊥ := by
  rw [fromFamily, Scheme.Hom.ker_comp, toImage_ker, Scheme.IdealSheafData.map_bot,
    fromOpenImage, toImage_ker]

/-- The two projections into the fixed threefold define exactly the same ideal sheaf. -/
theorem fixedProjection_ker : (fixedProjection V t).ker = (q V t).ker := by
  rw [← fromFamily_toFixed V t, Scheme.Hom.ker_comp (fromFamily V t), fromFamily_ker,
    Scheme.IdealSheafData.map_bot]

/-- The proper correspondence maps to the original scheme-theoretic swept support. -/
def toSweptImage : Correspondence V t ⟶ (q V t).image :=
  (fixedProjection V t).toImage ≫ Scheme.IdealSheafData.inclusion (fixedProjection_ker V t).ge

@[reassoc (attr := simp)]
theorem toSweptImage_imageι : toSweptImage V t ≫ (q V t).imageι = fixedProjection V t := by
  simp [toSweptImage, Scheme.Hom.imageι]

/-- The factorization restricts to the original map to the swept support. -/
@[reassoc (attr := simp)]
theorem fromFamily_toSweptImage : fromFamily V t ≫ toSweptImage V t = (q V t).toImage := by
  apply (cancel_mono (q V t).imageι).mp
  simp

private theorem inclusion_isIso_of_eq {Y : Scheme} {I J : Y.IdealSheafData} (h : I = J) :
    IsIso (Scheme.IdealSheafData.inclusion h.le) := by
  subst J
  rw [Scheme.IdealSheafData.inclusion_id]
  infer_instance

instance : IsProper (toSweptImage V t) := by
  have : IsProper (toSweptImage V t ≫ (q V t).imageι) := by
    rw [toSweptImage_imageι]
    infer_instance
  exact IsProper.of_comp _ (q V t).imageι

instance : IsDominant (toSweptImage V t) := by
  have := inclusion_isIso_of_eq (fixedProjection_ker V t).symm
  unfold toSweptImage
  infer_instance

theorem toSweptImage_surjective : Function.Surjective (toSweptImage V t) :=
  (toSweptImage V t).surjective

/-- The image on points of the completed correspondence equals the whole original swept support. -/
theorem fixedProjection_range : range (fixedProjection V t) = range (q V t).imageι := by
  rw [← toSweptImage_imageι, Scheme.Hom.comp_base, TopCat.coe_comp, range_comp,
    (toSweptImage_surjective V t).range_eq, image_univ]

/-- For every independent parameter triple there is a proper correspondence over the completed
time base whose image in the fixed threefold is precisely the strict closed swept support. -/
theorem proper_correspondence_of_independent (t : Fin 3 → ℂ) (hi : AlgebraicIndependent ℚ t) :
    ∃ (V : parameterScheme.Opens) (_ : seedBasePoint ∈ V),
      IsProper (baseProjection V t) ∧ Function.Surjective (baseProjection V t) ∧
      IsOpenImmersion (fromFamily V t) ∧ (fromFamily V t).ker = ⊥ ∧
      IsProper (toSweptImage V t) ∧ Function.Surjective (toSweptImage V t) ∧
      toSweptImage V t ≫ (q V t).imageι = fixedProjection V t ∧
      range (fixedProjection V t) = closure (range (q V t)) ∧
      range (fixedProjection V t) ≠ univ := by
  obtain ⟨V, hV, _, _, hs, hp, hsurj, _⟩ := time_family_of_independent t hi
  obtain ⟨hr, hn, _⟩ := swept_image V t hV hs hp hsurj
  exact ⟨V, hV, inferInstance, baseProjection_surjective V t hsurj,
    CycleQ2LiteralTimeFamilyRecovery.fromFamily_open V t, fromFamily_ker V t,
    inferInstance, toSweptImage_surjective V t, toSweptImage_imageι V t,
    (fixedProjection_range V t).trans hr, (fixedProjection_range V t).trans_ne hn⟩

/-- There exists a proper complex correspondence, surjecting onto the completed parameter and
onto a strict closed subscheme of the fixed threefold with the original swept ideal. -/
theorem exists_strict_proper_correspondence :
    ∃ (t : Fin 3 → ℂ) (_ : AlgebraicIndependent ℚ t)
      (V : parameterScheme.Opens) (_ : seedBasePoint ∈ V),
      IsProper (fixedProjection V t ≫ fixedStructure) ∧
      Function.Surjective (baseProjection V t) ∧
      IsProper (toSweptImage V t) ∧ Function.Surjective (toSweptImage V t) ∧
      (fixedProjection V t).ker = (q V t).ker ∧
      range (fixedProjection V t) = closure (range (q V t)) ∧
      range (fixedProjection V t) ≠ univ := by
  obtain ⟨t, hi, _⟩ := CycleQ2LiteralAbelJacobiIndependentRegular.exists_independent_regular
  obtain ⟨V, hV, _, surjBase, _, _, hp, surjImage, _, hr, hn⟩ :=
    proper_correspondence_of_independent t hi
  have : IsProper fixedStructure := CycleQ2LiteralAmbientCylinder.fixed_proper
  exact ⟨t, hi, V, hV, inferInstance, surjBase, hp, surjImage, fixedProjection_ker V t, hr, hn⟩

end CycleQ2LiteralProperSweptSupport

#print axioms CycleQ2LiteralProperSweptSupport.fixedProjection_ker
#print axioms CycleQ2LiteralProperSweptSupport.exists_strict_proper_correspondence
