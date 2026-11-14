import Proposal.GeometricSheafCohomologyScalar
import Proposal.GeometricProjectiveCanonicalH1
import Proposal.GeometricProjectiveCoefficients
import Proposal.GeometricTwistedModule
import Proposal.GeometricCechTrace

/-!
# The intrinsic complex action on the projective residue class

The complex action on actual derived cohomology comes from the structure
morphism and module-sheaf multiplication. The literal homogeneous
localization representatives and the actual Mayer-Vietoris boundary
respect that action. In particular the previously constructed normalized
class is a complex-linear map, and the canonical differential-sheaf
comparison is a complex-linear equivalence on cohomology.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2GeometricProjectiveCohomologyLinear

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry MvPolynomial
  CycleQ2GeometricProjectiveCurve CycleQ2GeometricDifferentialSheaf
  CycleQ2GeometricProjectiveCoefficients CycleQ2SeedTrace
  CycleQ2NormalConnecting CycleQ2SeedCechTheta

section ScalarSections

local instance (r θ : ℂ) (O : (projectiveCurve r θ).Opens) :
    Module ((projectiveCurve r θ).sheaf.obj.obj (op O))
      ((degreeOneSheaf r θ).obj.obj (op O)) :=
  degreeOneSectionsModule r θ O

def overlapCoefficient (r θ : ℂ) (z : ℂ) : OverlapProjectiveRing r θ :=
  basicOpenCoefficient r θ (curveG1 r θ * curveG2 r θ) z

theorem degreeNineRepresentative_C_mul (r θ z : ℂ) (p : Poly)
    (hp : p.IsHomogeneous 9) :
    degreeNineRepresentative r θ (C z * p) (hp.C_mul z) =
      overlapCoefficient r θ z • degreeNineRepresentative r θ p hp := by
  apply Subtype.ext
  change awayFraction r θ (curveG1 r θ * curveG2 r θ) 1 (curveMap r θ (C z * p)) =
    (overlapCoefficient r θ z).val *
      awayFraction r θ (curveG1 r θ * curveG2 r θ) 1 (curveMap r θ p)
  rw [map_mul]
  change Localization.mk _ _ =
    Localization.mk (curveMap r θ (C z)) 1 * Localization.mk _ _
  rw [Localization.mk_mul, one_mul]

theorem overlapCoefficient_sections (r θ z : ℂ) :
    (overlapProjectiveSectionsIso r θ).hom (overlapCoefficient r θ z) =
      coefficientOn (projectiveCurve r θ).sheaf (projectiveGlobalCoefficient r θ)
        (overlapProjectivePatch r θ) z := by
  have h := coefficientOn_basicOpen r θ (curveG1 r θ * curveG2 r θ)
    (curveG12_mem_grade r θ) (by decide) z
  have h' : (overlapProjectiveSectionsIso r θ).inv
      (coefficientOn (projectiveCurve r θ).sheaf (projectiveGlobalCoefficient r θ)
        (overlapProjectivePatch r θ) z) = overlapCoefficient r θ z := h
  exact (congrArg (overlapProjectiveSectionsIso r θ).hom h').symm.trans
    ((overlapProjectiveSectionsIso r θ).inv_hom_id_apply _)

theorem overlapSheafFrame_smul (r θ : ℂ)
    (a : Γ(projectiveCurve r θ, overlapProjectivePatch r θ))
    (s : (degreeOneSheaf r θ).obj.obj (op (overlapProjectivePatch r θ))) :
    overlapSheafFrame r θ (a • s) = a * overlapSheafFrame r θ s :=
  TwistedModule.firstLocalSections_smul (projectiveCurve r θ).sheaf
    (firstProjectivePatch r θ) (secondProjectivePatch r θ) (overlapProjectivePatch r θ)
    (overlapProjectivePatch_eq r θ) (projectiveTransitionUnit r θ)
    (overlapProjectivePatch r θ) ((overlapProjectivePatch_eq r θ).le.trans inf_le_left)
    a s

theorem overlapDegreeOneSectionsEquiv_scalar (r θ z : ℂ)
    (s : OverlapDegreeOne r θ) :
    overlapDegreeOneSectionsEquiv r θ (overlapCoefficient r θ z • s) =
      coefficientOn (projectiveCurve r θ).sheaf (projectiveGlobalCoefficient r θ)
        (overlapProjectivePatch r θ) z • overlapDegreeOneSectionsEquiv r θ s := by
  apply (overlapSheafFrame r θ).injective
  rw [overlapDegreeOneSectionsEquiv_coordinate, overlapSheafFrame_smul,
    overlapDegreeOneSectionsEquiv_coordinate,
    (overlapFirstDegreeOneEquiv r θ).symm.map_smul]
  change (overlapProjectiveSectionsIso r θ).hom
      (overlapCoefficient r θ z * (overlapFirstDegreeOneEquiv r θ).symm s) = _
  rw [map_mul, overlapCoefficient_sections]



end ScalarSections

open CycleQ2GeometricSheafCohomologyScalar
  CycleQ2GeometricProjectiveCanonical CycleQ2GeometricProjectiveCanonicalH1
  CycleQ2GeometricProjectiveNonzero CycleQ2GeometricCechPoleReduction
  CycleQ2GeometricCechTrace CycleQ2GeometricConeCech.HZero

local instance projectiveSheavesHasExt (r θ : ℂ) :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology (projectiveCurve r θ))
      AddCommGrpCat.{0}) := HasExt.standard _

/-- The action is induced by actual scalar multiplication on O(1). -/
instance degreeOneCohomologyModule (r θ : ℂ) (n : ℕ)
    (O : (projectiveCurve r θ).Opens) :
    Module ℂ ((degreeOneSheaf r θ).H' n O) :=
  cohomologyModule (projectiveCurve r θ).sheaf (projectiveGlobalCoefficient r θ)
    (degreeOneModuleSheaf r θ) n O

/-- The differential sheaf uses the same actual complex structure morphism. -/
instance differentialCohomologyModule (r θ : ℂ) :
    Module ℂ (DifferentialSheafH1 r θ) :=
  cohomologyModule (projectiveCurve r θ).sheaf (projectiveGlobalCoefficient r θ)
    (projectiveDifferentialSheaf r θ) 1 ⊤

/-- The already constructed canonical cohomology equivalence is linear
for the intrinsic scalar actions on both sheaves. -/
def canonicalH1LinearEquiv (r : ℂ) (hr : r ^ 3 = 2) :
    ProjectiveSheafH1 r 0 ≃ₗ[ℂ] DifferentialSheafH1 r 0 :=
  (cohomologyIsoLinear (projectiveCurve r 0).sheaf (projectiveGlobalCoefficient r 0)
    (projectiveDifferentialSheaf r 0) (projectiveCanonicalIso r hr) 1 ⊤).symm

@[simp] theorem canonicalH1LinearEquiv_apply (r : ℂ) (hr : r ^ 3 = 2)
    (x : ProjectiveSheafH1 r 0) :
    canonicalH1LinearEquiv r hr x = canonicalH1Equiv r hr x := rfl

theorem degreeOneConnecting_scalar (r θ : ℂ) (hr : r ≠ 0) (z : ℂ)
    (x : OverlapDegreeOne r θ) :
    degreeOneConnecting r θ hr (overlapCoefficient r θ z • x) =
      z • degreeOneConnecting r θ hr x := by
  let R := (projectiveCurve r θ).sheaf
  let c := projectiveGlobalCoefficient r θ
  let M := degreeOneModuleSheaf r θ
  let F := degreeOneSheaf r θ
  let S := projectiveMayerVietoris r θ hr
  let O := overlapProjectivePatch r θ
  have hsections := overlapDegreeOneSectionsEquiv_scalar r θ z x
  have hzero := sectionsEquiv_symm_scalar R c M O z
    (overlapDegreeOneSectionsEquiv r θ x)
  exact (congrArg (fun s => S.δ F 0 1 rfl ((sectionsEquiv F O).symm s))
    hsections).trans
      ((congrArg (fun t => S.δ F 0 1 rfl t) hzero).trans
        (mayerVietoris_scalar R c M S 0 1 rfl z _))

theorem degreeNineProjectiveClass_C_mul (r : ℂ) (hr : r ^ 3 = 2)
    (z : ℂ) (p : Poly) (hp : p.IsHomogeneous 9) :
    degreeNineProjectiveClass r hr (C z * p) (hp.C_mul z) =
      z • degreeNineProjectiveClass r hr p hp := by
  have hr0 : r ≠ 0 := by intro h; simp [h] at hr
  change degreeOneConnecting r 0 hr0
      (degreeNineRepresentative r 0 (C z * p) (hp.C_mul z)) =
    z • degreeOneConnecting r 0 hr0 (degreeNineRepresentative r 0 p hp)
  rw [degreeNineRepresentative_C_mul r 0 z p hp]
  exact degreeOneConnecting_scalar r 0 hr0 z _

theorem normalizedProjectiveClass_add (r : ℂ) (hr : r ^ 3 = 2) (a b : ℂ) :
    normalizedProjectiveClass r hr (a + b) =
      normalizedProjectiveClass r hr a + normalizedProjectiveClass r hr b := by
  have hr0 : r ≠ 0 := by intro h; simp [h] at hr
  change degreeOneToProjectiveH1 r 0 hr0
      (degreeNineCechClass r 0 (C (a + b) * mon 1 8 0 0)
        ((mon_homogeneous 1 8 0 0).C_mul (a + b))) = _
  simp only [map_add, add_mul]
  rw [degreeNineCechClass_add, map_add]
  rfl

theorem normalizedProjectiveClass_smul (r : ℂ) (hr : r ^ 3 = 2) (a b : ℂ) :
    normalizedProjectiveClass r hr (a * b) = a • normalizedProjectiveClass r hr b := by
  change degreeNineProjectiveClass r hr (C (a * b) * mon 1 8 0 0)
      ((mon_homogeneous 1 8 0 0).C_mul (a * b)) =
    a • degreeNineProjectiveClass r hr (C b * mon 1 8 0 0)
      ((mon_homogeneous 1 8 0 0).C_mul b)
  simpa only [map_mul, mul_assoc] using
    degreeNineProjectiveClass_C_mul r hr a (C b * mon 1 8 0 0)
      ((mon_homogeneous 1 8 0 0).C_mul b)

/-- The fixed normalization numerator defines an intrinsic linear class. -/
def normalizedProjectiveLinear (r : ℂ) (hr : r ^ 3 = 2) :
    ℂ →ₗ[ℂ] ProjectiveSheafH1 r 0 where
  toFun := normalizedProjectiveClass r hr
  map_add' := normalizedProjectiveClass_add r hr
  map_smul' := normalizedProjectiveClass_smul r hr

/-- Its image in the actual differential sheaf is linear for the action
coming from complex multiplication on differentials. -/
def normalizedCanonicalLinear (r : ℂ) (hr : r ^ 3 = 2) :
    ℂ →ₗ[ℂ] DifferentialSheafH1 r 0 :=
  (canonicalH1LinearEquiv r hr).toLinearMap.comp (normalizedProjectiveLinear r hr)

@[simp] theorem normalizedCanonicalLinear_apply (r : ℂ) (hr : r ^ 3 = 2) (z : ℂ) :
    normalizedCanonicalLinear r hr z = normalizedCanonicalClass r hr z := rfl

theorem normalizedCanonicalLinear_injective (r : ℂ) (hr : r ^ 3 = 2) :
    Function.Injective (normalizedCanonicalLinear r hr) :=
  normalizedCanonicalClass_injective r hr

#print axioms degreeOneConnecting_scalar
#print axioms canonicalH1LinearEquiv
#print axioms normalizedProjectiveLinear
#print axioms normalizedCanonicalLinear
#print axioms normalizedCanonicalLinear_injective

end CycleQ2GeometricProjectiveCohomologyLinear
end

