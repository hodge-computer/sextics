import Proposal.GeometricCanonicalResidueSheaf
import Proposal.GeometricCubicAdjunctionLocalIso
import Proposal.GeometricOffCurveResidue
import Proposal.GeometricGradedCechDescent

/-!
# Short exactness of the actual canonical residue sequence

Status: source-only proof draft; compilation and independent kernel replay
are deferred at the user's request. No new axioms or admissions are used.

Near the original curve, actual exterior frames and the actual contraction
isomorphism identify the residue complex with the unchanged Cartier
inverse-ideal complex. Component exactness is used only on the existing
principal Cartier basis, where it has already been proved. Away from the
curve the regular inclusion is the actual internal-Hom isomorphism and the
residue target is zero. These two facts give the genuine module and
additive sheaf short exact sequences on the entire literal surface.

The geometric strategy is due to Ben Diamond and the cited work of Claire
Voisin. Prepared for fqlx with OpenAI ChatGPT assistance.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2CanonicalResidueSheaf

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open CycleQ2GeometricIntrinsicNormal CycleQ2GeometricIntrinsicCartierSequence
  CycleQ2GeometricDifferentialSheaf CycleQ2GeometricCanonicalGluing
  CycleQ2LocalHomFrame CycleQ2GeometricModuleLocalIso CycleQ2NormalPushforwardIso
  CycleQ2SurfaceExteriorFrameBinding CycleQ2CubicAdjunctionLocalIso
  CycleQ2GeometricSheafLocalExactness CycleQ2IntrinsicCartierPrincipalBasis

/-- The target comparison is the actual normal-first contraction, with no
local invertibility premise left over. -/
def normalContractionFrame (a : PatchIndex) (O : Surface.Opens)
    (hO : O ≤ refinedPatch a) :
    (normalDirectImageSheaf immersion).val.obj (op O) ≃ₗ[Γ(Surface, O)]
      ResidueTarget.val.obj (op O) :=
  LinearEquiv.ofBijective ((normalContraction (frameCubic a)).val.app (op O)).hom (by
    let e := ((SheafOfModules.evaluation (ringSheaf Surface.sheaf) (op O)).mapIso
      (actualNormalPushforwardIso 57 1).symm).toLinearEquiv
    have hc := frameCubicAdjunction_bijective a (immersion ⁻¹ᵁ O)
      ((immersion.preimage_mono hO).trans (preimage_refinedPatch a).le)
    exact hc.comp e.bijective)

theorem normalContractionFrame_apply (a : PatchIndex) (O : Surface.Opens)
    (hO : O ≤ refinedPatch a)
    (s : (normalDirectImageSheaf immersion).val.obj (op O)) :
    normalContractionFrame a O hO s =
      (normalContraction (frameCubic a)).val.app (op O) s := rfl

/-- The three component properties for the fixed canonical residue complex. -/
def CanonicalResidueExactOn (O : Surface.Opens) : Prop :=
  Function.Injective ((idealRegularInclusion immersion CanonicalForms).val.app (op O)) ∧
    Function.Exact ((idealRegularInclusion immersion CanonicalForms).val.app (op O))
      (canonicalResidue.val.app (op O)) ∧
    Function.Surjective (canonicalResidue.val.app (op O))

/-- Exactness transfer uses the existing original Cartier maps on this
open. The eventual application supplies all three facts from the proved
principal Cartier basis. -/
private theorem exactOn_normal (a : PatchIndex) (O : Surface.Opens)
    (hO : O ≤ refinedPatch a)
    (hi : Function.Injective ((inverseIdealScalar immersion).val.app (op O)))
    (he : Function.Exact ((inverseIdealScalar immersion).val.app (op O))
      ((inverseIdealReduction immersion).val.app (op O)))
    (hs : Function.Surjective ((inverseIdealReduction immersion).val.app (op O))) :
    CanonicalResidueExactOn O := by
  let e₀ := (exteriorFrame 57 1 a).app O (hO.trans (refinedPatch_le a))
  let e₁ := (internalHomFrame Surface.sheaf IdealSheaf (exteriorFrame 57 1 a)).app
    O (hO.trans (refinedPatch_le a))
  let e₂ := normalContractionFrame a O hO
  have hf (s : CanonicalForms.val.obj (op O)) :
      e₁ ((idealRegularInclusion immersion CanonicalForms).val.app (op O) s) =
        (inverseIdealScalar immersion).val.app (op O) (e₀ s) :=
    internalHomFrame_idealRegularInclusion immersion CanonicalForms
      (exteriorFrame 57 1 a) O (hO.trans (refinedPatch_le a)) s
  have hg (H : PoleForms.val.obj (op O)) :
      canonicalResidue.val.app (op O) H =
        e₂ ((inverseIdealReduction immersion).val.app (op O) (e₁ H)) := by
    rw [canonicalResidue_local a O hO]
    rfl
  refine ⟨?_, ?_, ?_⟩
  · intro s t hst
    apply e₀.injective
    apply hi
    exact (hf s).symm.trans ((congrArg e₁ hst).trans (hf t))
  · intro H
    constructor
    · intro hH
      have hz : (inverseIdealReduction immersion).val.app (op O) (e₁ H) = 0 := by
        apply e₂.injective
        rw [← hg, hH, map_zero]
      obtain ⟨r, hr⟩ := (he (e₁ H)).mp hz
      refine ⟨e₀.symm r, ?_⟩
      apply e₁.injective
      rw [hf, LinearEquiv.apply_symm_apply, hr]
    · rintro ⟨s, rfl⟩
      exact canonicalResidue_regular_section O s
  · intro t
    obtain ⟨f, hf⟩ := hs (e₂.symm t)
    refine ⟨e₁.symm f, ?_⟩
    rw [hg, LinearEquiv.apply_symm_apply, hf, LinearEquiv.apply_symm_apply]

/-- Away from the actual curve, no exterior-frame assumption is needed. -/
private theorem exactOn_offCurve (O : Surface.Opens) (hO : O ≤ offCurve) :
    CanonicalResidueExactOn O := by
  have hi := CycleQ2OffCurveResidue.idealRegularInclusion_bijective
    immersion offCurve preimage_offCurve CanonicalForms O hO
  letI := target_empty_of_le hO
  refine ⟨hi.1, ?_, ?_⟩
  · intro H
    constructor
    · intro _
      exact hi.2 H
    · intro _
      exact Subsingleton.elim _ _
  · intro t
    exact ⟨0, Subsingleton.elim _ _⟩

/-- Every neighborhood contains one on which the three actual component
properties hold. This is the precise local lifting needed for sheaf
epimorphism, and does not claim surjectivity over arbitrary opens. -/
theorem canonicalResidue_exact_neighborhoods (U : Surface.Opens) (x : Surface)
    (hx : x ∈ U) :
    ∃ (V : Surface.Opens), V ≤ U ∧ x ∈ V ∧ CanonicalResidueExactOn V := by
  have hxc : x ∈ ⨆ a, residueCover a := by rw [residueCover_top]; trivial
  obtain ⟨a, ha⟩ := Opens.mem_iSup.mp hxc
  obtain ⟨V, hVB, hxV, hVU⟩ :=
    Opens.isBasis_iff_nbhd.mp (cartierPrincipalBasis_isBasis 57 1 (by norm_num) one_ne_zero)
      (show x ∈ U ⊓ residueCover a from ⟨hx, ha⟩)
  refine ⟨V, hVU.trans inf_le_left, hxV, ?_⟩
  cases a with
  | none => exact exactOn_offCurve V (hVU.trans inf_le_right)
  | some a =>
      obtain ⟨i, j, z, rfl⟩ := hVB
      have hcart := refinedPrincipal_inverseIdeal_exactness (57 : ℂ) 1 i j z
      exact exactOn_normal a _ (hVU.trans inf_le_right)
        hcart.1 hcart.2.1 hcart.2.2

def canonicalResidueExactBasis : Set Surface.Opens := {O | CanonicalResidueExactOn O}

theorem canonicalResidueExactBasis_isBasis : Opens.IsBasis canonicalResidueExactBasis := by
  rw [Opens.isBasis_iff_nbhd]
  intro U x hx
  obtain ⟨V, hVU, hxV, he⟩ := canonicalResidue_exact_neighborhoods U x hx
  exact ⟨V, he, hxV, hVU⟩

/-- The genuine canonical residue short exact sequence on the whole
literal projective surface. -/
theorem canonicalResidueComplex_shortExact : canonicalResidueComplex.ShortExact := by
  exact moduleSheaf_shortExact_of_basis (ringSheaf Surface.sheaf) canonicalResidueComplex
    canonicalResidueExactBasis canonicalResidueExactBasis_isBasis
    (fun _ h => h.1) (fun _ h => h.2.1) (fun _ h => h.2.2)

/-- The actual additive complex, retaining the original regular and
residue morphisms rather than replacing them by chosen cohomology maps. -/
def canonicalResidueAdditiveComplex : ShortComplex (TopCat.Sheaf AddCommGrpCat.{0} Surface) := by
  letI : (SheafOfModules.toSheaf.{0} (ringSheaf Surface.sheaf)).PreservesZeroMorphisms :=
    moduleSheaf_toSheaf_preservesZeroMorphisms (ringSheaf Surface.sheaf)
  exact canonicalResidueComplex.map (SheafOfModules.toSheaf.{0} (ringSheaf Surface.sheaf))

/-- Additive exactness is proved directly from the same actual component
basis, without an unproved cokernel-preservation assumption. -/
theorem canonicalResidueAdditiveComplex_shortExact :
    canonicalResidueAdditiveComplex.ShortExact := by
  exact additiveSheaf_shortExact_of_basis canonicalResidueAdditiveComplex
    canonicalResidueExactBasis canonicalResidueExactBasis_isBasis
    (fun _ h => h.1) (fun _ h => h.2.1) (fun _ h => h.2.2)

#print axioms normalContractionFrame
#print axioms canonicalResidue_exact_neighborhoods
#print axioms canonicalResidueComplex_shortExact
#print axioms canonicalResidueAdditiveComplex_shortExact

end CycleQ2CanonicalResidueSheaf

end
