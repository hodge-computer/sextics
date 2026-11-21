import Proposal.GeometricSeedFamilyChart
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent

/-!
# An actual relative-dimension-three open of the full cubic family

Each normalized projective chart retains the five original variables and
the two relations `familyEquation r` and `z_i - 1`. For a different
coordinate `z_j`, the Jacobian columns `j,i` have determinant equal to the
class of `partial_j(familyEquation r)`. Localizing at this actual derivative
gives a submersive presentation with six generators and three relations,
so the patch is standard smooth of relative dimension three over the
unchanged full cubic coefficient ring.

The native normalized chart maps embed these patches as open subschemes
of the original projective family. Their actual union is smooth of
relative dimension three over the original parameter scheme. No assertion
that the patches cover the entire family is made, and no smoothness or
nonemptiness premise is supplied.

Prepared for `fqlx` with OpenAI ChatGPT assistance,
following Ben Diamond and the project's geometric argument.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2SeedFamilyJacobian

open MvPolynomial CategoryTheory AlgebraicGeometry TopologicalSpace
open CycleQ2SeedCubicFamily CycleQ2SeedProjectiveFamily
  CycleQ2SeedFamilyNormalized CycleQ2SeedFamilyChart

local instance jacobianNormalizedCommRing (r : ℂ) (i : Fin 4) :
    CommRing (NormalizedRing r i) := Ideal.Quotient.commRing (normalizedIdeal r i)

abbrev OtherCoordinate (i : Fin 4) := {j : Fin 5 // j ≠ i.castSucc}

def derivativeColumns (i : Fin 4) (j : OtherCoordinate i) : Fin 2 → Fin 5 :=
  ![j.1, i.castSucc]

theorem derivativeColumns_injective (i : Fin 4) (j : OtherCoordinate i) :
    Function.Injective (derivativeColumns i j) := by
  intro a b hab
  fin_cases a <;> fin_cases b
  · rfl
  · exact (j.2 hab).elim
  · exact (j.2 hab.symm).elim
  · rfl

/-- The relative derivative is taken in an original geometric variable,
with every cubic parameter treated as a coefficient. -/
def normalizedDerivative (r : ℂ) (i : Fin 4) (j : Fin 5) : NormalizedRing r i :=
  normalizedQuotient r i (pderiv j (familyEquation r))

def prePresentation (r : ℂ) (i : Fin 4) (j : OtherCoordinate i) :
    Algebra.PreSubmersivePresentation ParameterRing (NormalizedRing r i)
      (Fin 5) (Fin 2) :=
  Algebra.PreSubmersivePresentation.naive (v := normalizedRelation r i)
    (derivativeColumns i j) (derivativeColumns_injective i j)

theorem prePresentation_jacobian (r : ℂ) (i : Fin 4) (j : OtherCoordinate i) :
    (prePresentation r i j).jacobian = normalizedDerivative r i j.1 := by
  rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det,
    Matrix.det_fin_two]
  simp only [Algebra.PreSubmersivePresentation.jacobiMatrix_apply]
  change normalizedQuotient r i
      (pderiv j.1 (familyEquation r) * pderiv i.castSucc (X i.castSucc - 1) -
        pderiv j.1 (X i.castSucc - 1) * pderiv i.castSucc (familyEquation r)) =
      normalizedQuotient r i (pderiv j.1 (familyEquation r))
  simp [MvPolynomial.pderiv_X, MvPolynomial.pderiv_one, Pi.single_apply, j.2, Ne.symm j.2]

/-- The actual principal localization at the computed relative derivative. -/
abbrev JacobianPatch (r : ℂ) (i : Fin 4) (j : OtherCoordinate i) :=
  Localization.Away (normalizedDerivative r i j.1)

theorem derivative_isUnit (r : ℂ) (i : Fin 4) (j : OtherCoordinate i) :
    IsUnit (algebraMap (NormalizedRing r i) (JacobianPatch r i j)
      (normalizedDerivative r i j.1)) :=
  IsLocalization.Away.algebraMap_isUnit _

/-- Localization adds one actual inverse generator and its defining relation. -/
def localizedPresentation (r : ℂ) (i : Fin 4) (j : OtherCoordinate i) :
    Algebra.PreSubmersivePresentation ParameterRing (JacobianPatch r i j)
      (Unit ⊕ Fin 5) (Unit ⊕ Fin 2) :=
  (Algebra.PreSubmersivePresentation.localizationAway
    (JacobianPatch r i j) (normalizedDerivative r i j.1)).comp
      (prePresentation r i j)

theorem localizedPresentation_jacobian (r : ℂ) (i : Fin 4) (j : OtherCoordinate i) :
    (localizedPresentation r i j).jacobian =
      algebraMap (NormalizedRing r i) (JacobianPatch r i j)
          (normalizedDerivative r i j.1) *
        algebraMap (NormalizedRing r i) (JacobianPatch r i j)
          (normalizedDerivative r i j.1) := by
  rw [localizedPresentation,
    Algebra.PreSubmersivePresentation.comp_jacobian_eq_jacobian_smul_jacobian,
    prePresentation_jacobian,
    Algebra.PreSubmersivePresentation.localizationAway_jacobian,
    Algebra.smul_def]

def submersivePresentation (r : ℂ) (i : Fin 4) (j : OtherCoordinate i) :
    Algebra.SubmersivePresentation ParameterRing (JacobianPatch r i j)
      (Unit ⊕ Fin 5) (Unit ⊕ Fin 2) where
  toPreSubmersivePresentation := localizedPresentation r i j
  jacobian_isUnit := by
    rw [localizedPresentation_jacobian]
    exact (derivative_isUnit r i j).mul (derivative_isUnit r i j)

theorem submersivePresentation_dimension (r : ℂ) (i : Fin 4) (j : OtherCoordinate i) :
    (submersivePresentation r i j).dimension = 3 := by
  change Nat.card (Unit ⊕ Fin 5) - Nat.card (Unit ⊕ Fin 2) = 3
  norm_num [Nat.card_eq_fintype_card]

/-- Genuine standard smoothness of the computed relative Jacobian patch. -/
theorem patch_standardSmooth_dimension (r : ℂ) (i : Fin 4) (j : OtherCoordinate i) :
    Algebra.IsStandardSmoothOfRelativeDimension 3 ParameterRing (JacobianPatch r i j) :=
  (submersivePresentation r i j).isStandardSmoothOfRelativeDimension
    (submersivePresentation_dimension r i j)

def patchToNormalized (r : ℂ) (i : Fin 4) (j : OtherCoordinate i) :
    Spec (CommRingCat.of (JacobianPatch r i j)) ⟶ normalizedScheme r i :=
  Spec.map (CommRingCat.ofHom
    (algebraMap (NormalizedRing r i) (JacobianPatch r i j)))

instance patchToNormalized_isOpenImmersion (r : ℂ) (i : Fin 4) (j : OtherCoordinate i) :
    IsOpenImmersion (patchToNormalized r i j) :=
  IsOpenImmersion.of_isLocalization (normalizedDerivative r i j.1)

def patchToFamily (r : ℂ) (i : Fin 4) (j : OtherCoordinate i) :
    Spec (CommRingCat.of (JacobianPatch r i j)) ⟶ family r :=
  patchToNormalized r i j ≫ normalizedChartToFamily r i

instance patchToFamily_isOpenImmersion (r : ℂ) (i : Fin 4) (j : OtherCoordinate i) :
    IsOpenImmersion (patchToFamily r i j) := by
  dsimp only [patchToFamily]
  infer_instance

theorem patchToFamily_overParameters (r : ℂ) (i : Fin 4) (j : OtherCoordinate i) :
    patchToFamily r i j ≫ familyToParameters r =
      Spec.map (CommRingCat.ofHom (algebraMap ParameterRing (JacobianPatch r i j))) := by
  rw [patchToFamily, Category.assoc, normalizedChartToFamily_overParameters,
    patchToNormalized, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro c
  exact (IsScalarTower.algebraMap_apply ParameterRing (NormalizedRing r i)
    (JacobianPatch r i j) c).symm

theorem patchToFamily_smoothOfRelativeDimension (r : ℂ) (i : Fin 4)
    (j : OtherCoordinate i) :
    SmoothOfRelativeDimension 3 (patchToFamily r i j ≫ familyToParameters r) := by
  rw [patchToFamily_overParameters]
  apply (HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension 3)).mpr
  apply RingHom.locally_of (RingHom.isStandardSmoothOfRelativeDimension_respectsIso (n := 3))
  exact (RingHom.isStandardSmoothOfRelativeDimension_algebraMap 3).mpr
    (patch_standardSmooth_dimension r i j)

/-- The patch's actual open image in the original projective family. -/
def jacobianOpen (r : ℂ) (i : Fin 4) (j : OtherCoordinate i) : (family r).Opens :=
  (patchToFamily r i j).opensRange

theorem jacobianOpen_eq_image (r : ℂ) (i : Fin 4) (j : OtherCoordinate i) :
    jacobianOpen r i j =
      normalizedChartToFamily r i ''ᵁ PrimeSpectrum.basicOpen (normalizedDerivative r i j.1) := by
  change (patchToNormalized r i j ≫ normalizedChartToFamily r i).opensRange = _
  rw [Scheme.Hom.opensRange_comp]
  exact congrArg (fun W : (normalizedScheme r i).Opens =>
    normalizedChartToFamily r i ''ᵁ W)
      (Scheme.Hom.opensRange_localizationAway (R := CommRingCat.of (NormalizedRing r i))
        (normalizedDerivative r i j.1))

theorem normalizedChartToFamily_preimage_jacobianOpen (r : ℂ) (i : Fin 4)
    (j : OtherCoordinate i) :
    normalizedChartToFamily r i ⁻¹ᵁ jacobianOpen r i j =
      PrimeSpectrum.basicOpen (normalizedDerivative r i j.1) := by
  rw [jacobianOpen_eq_image, Scheme.Hom.preimage_image_eq]

theorem jacobianOpen_smoothOfRelativeDimension (r : ℂ) (i : Fin 4)
    (j : OtherCoordinate i) :
    SmoothOfRelativeDimension 3 ((jacobianOpen r i j).ι ≫ familyToParameters r) := by
  let f := patchToFamily r i j
  have hr : Set.range f = Set.range f.opensRange.ι :=
    congrArg Opens.carrier f.opensRange.opensRange_ι.symm
  let e := IsOpenImmersion.isoOfRangeEq f f.opensRange.ι hr
  apply (MorphismProperty.cancel_left_of_respectsIso
    (P := @SmoothOfRelativeDimension 3) e.hom
    ((jacobianOpen r i j).ι ≫ familyToParameters r)).mp
  have he : e.hom ≫ f.opensRange.ι = f :=
    IsOpenImmersion.isoOfRangeEq_hom_fac f f.opensRange.ι hr
  change SmoothOfRelativeDimension 3 (e.hom ≫ f.opensRange.ι ≫ familyToParameters r)
  rw [← Category.assoc, he]
  exact patchToFamily_smoothOfRelativeDimension r i j

abbrev PatchIndex := Σ i : Fin 4, OtherCoordinate i

/-- The actual union of the derivative-localization patches. -/
def smoothOpen (r : ℂ) : (family r).Opens :=
  ⨆ q : PatchIndex, jacobianOpen r q.1 q.2

theorem jacobianOpen_le_smoothOpen (r : ℂ) (i : Fin 4) (j : OtherCoordinate i) :
    jacobianOpen r i j ≤ smoothOpen r :=
  le_iSup_of_le ⟨i, j⟩ le_rfl

/-- A nonvanishing computed derivative places the actual chart point in
the constructed relative-dimension-three open. -/
theorem mem_smoothOpen_of_derivative_not_mem (r : ℂ) (i : Fin 4)
    (j : OtherCoordinate i) (q : normalizedScheme r i)
    (h : normalizedDerivative r i j.1 ∉ q.asIdeal) :
    normalizedChartToFamily r i q ∈ smoothOpen r := by
  have hq : q ∈ normalizedChartToFamily r i ⁻¹ᵁ jacobianOpen r i j := by
    rw [normalizedChartToFamily_preimage_jacobianOpen]
    exact h
  exact jacobianOpen_le_smoothOpen r i j hq

/-- The union is smooth of relative dimension three over the unchanged
full coefficient parameter scheme. No cover of the entire family is used. -/
theorem smoothOpen_family_smoothOfRelativeDimension (r : ℂ) :
    SmoothOfRelativeDimension 3 ((smoothOpen r).ι ≫ familyToParameters r) := by
  let V : PatchIndex → (smoothOpen r).toScheme.Opens := fun q =>
    (smoothOpen r).ι ⁻¹ᵁ jacobianOpen r q.1 q.2
  have hV : (⨆ q : PatchIndex, V q) = ⊤ := by
    apply top_le_iff.mp
    intro x _
    have hx : x.1 ∈ smoothOpen r := x.2
    obtain ⟨q, hq⟩ := Opens.mem_iSup.mp hx
    exact Opens.mem_iSup.mpr ⟨q, hq⟩
  apply IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension 3) V hV
  intro q
  let U := jacobianOpen r q.1 q.2
  let g : (V q).toScheme ⟶ family r := (V q).ι ≫ (smoothOpen r).ι
  have hr : Set.range g ⊆ Set.range U.ι := by
    rintro x ⟨a, rfl⟩
    exact ⟨⟨g a, a.2⟩, rfl⟩
  let gLift := IsOpenImmersion.lift U.ι g hr
  have he : gLift ≫ U.ι = g := IsOpenImmersion.lift_fac U.ι g hr
  rw [← Category.assoc]
  change SmoothOfRelativeDimension 3 (g ≫ familyToParameters r)
  rw [← he, Category.assoc]
  exact IsZariskiLocalAtSource.comp
    (jacobianOpen_smoothOfRelativeDimension r q.1 q.2) gLift

theorem smoothOpen_family_smooth (r : ℂ) :
    Smooth ((smoothOpen r).ι ≫ familyToParameters r) := by
  letI := smoothOpen_family_smoothOfRelativeDimension r
  exact SmoothOfRelativeDimension.smooth 3 _

end CycleQ2SeedFamilyJacobian

end

#print axioms CycleQ2SeedFamilyJacobian.prePresentation_jacobian
#print axioms CycleQ2SeedFamilyJacobian.patch_standardSmooth_dimension
#print axioms CycleQ2SeedFamilyJacobian.patchToFamily_overParameters
#print axioms CycleQ2SeedFamilyJacobian.normalizedChartToFamily_preimage_jacobianOpen
#print axioms CycleQ2SeedFamilyJacobian.smoothOpen_family_smoothOfRelativeDimension
