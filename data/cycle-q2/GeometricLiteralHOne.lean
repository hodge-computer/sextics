import Proposal.GeometricAffineCohomology
import Proposal.GeometricLiteralCanonicalClass
import Proposal.GeometricIncidenceCechTrace

/-!
# The complete literal canonical cohomology line

The complex action on the existing homogeneous Cech quotient is compared
with multiplication by actual projective coefficients. This makes the
proved Cech-to-derived equivalence complex-linear for every r ≠ 0.

At the literal incidence seed (r, θ) = (57, 1), the exact incoming Cech
coordinate and the already constructed literal canonical module isomorphism
then identify all actual H¹(Ω) with ℂ. The normalization is explicitly the
image of x₃⁹/(g₁g₂) through that canonical isomorphism. Every nonzero linear
functional on this derived group has the same kernel on maps into it.
The original paired numerators give the computed derivative row there.

No identification with a geometric Serre trace or a moving-cycle map is
asserted by this construction.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2GeometricLiteralHOne

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry MvPolynomial
  CycleQ2NormalConnecting CycleQ2SeedCechTheta
  CycleQ2GeometricProjectiveCurve CycleQ2GeometricProjectiveHOne
  CycleQ2GeometricProjectiveCohomologyLinear
  CycleQ2GeometricProjectiveCanonical CycleQ2GeometricProjectiveCanonicalH1
  CycleQ2GeometricDifferentialSheaf CycleQ2GeometricSheafCohomologyScalar
  CycleQ2GeometricLiteralCanonicalClass
  CycleQ2GeometricCechComplex CycleQ2GeometricIncidenceCechSurjectivity
  CycleQ2GeometricIncidenceCechTrace

local instance projectiveSheavesHasExt (r θ : ℂ) :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology (projectiveCurve r θ))
      AddCommGrpCat.{0}) := HasExt.standard _

private def linearEquivOfAddEquiv {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module ℂ M] [Module ℂ N] (e : M ≃+ N)
    (h : ∀ (c : ℂ) (x : M), e (c • x) = c • e x) : M ≃ₗ[ℂ] N :=
  { toAddEquiv := e
    map_smul' := h }

/-- The incoming complex action and the already checked degree-zero
coefficient action are equal in the actual overlap localization. -/
theorem overlapCoefficient_smul_eq_complex (r θ c : ℂ)
    (x : OverlapDegreeOne r θ) :
    overlapCoefficient r θ c • x = c • x := by
  apply Subtype.ext
  change (overlapCoefficient r θ c).val * (x : Overlap r θ) =
    c • (x : Overlap r θ)
  rw [Algebra.smul_def]
  congr 1

/-- The actual Mayer-Vietoris quotient map respects the original complex
module structure on the homogeneous Cech quotient. -/
theorem degreeOneToProjectiveH1_smul (r θ : ℂ) (hr : r ≠ 0)
    (c : ℂ) (z : DegreeOneCech r θ) :
    degreeOneToProjectiveH1 r θ hr (c • z) =
      c • degreeOneToProjectiveH1 r θ hr z := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
  rw [← cech_mk_smul]
  change degreeOneConnecting r θ hr (c • x) = c • degreeOneConnecting r θ hr x
  rw [← overlapCoefficient_smul_eq_complex]
  exact degreeOneConnecting_scalar r θ hr c x

/-- The full existing Cech-to-derived equivalence is linear for the
intrinsic complex action coming from the projective structure morphism. -/
def degreeOneCechHOneLinearEquiv (r θ : ℂ) (hr : r ≠ 0) :
    DegreeOneCech r θ ≃ₗ[ℂ] ProjectiveSheafH1 r θ :=
  linearEquivOfAddEquiv (degreeOneCechHOneEquiv r θ hr)
    (degreeOneToProjectiveH1_smul r θ hr)

@[simp] theorem degreeOneCechHOneLinearEquiv_apply (r θ : ℂ) (hr : r ≠ 0)
    (z : DegreeOneCech r θ) :
    degreeOneCechHOneLinearEquiv r θ hr z = degreeOneToProjectiveH1 r θ hr z := rfl

private def canonicalAdditiveIsoAt (r θ : ℂ)
    (e : projectiveDifferentialSheaf r θ ≅ degreeOneModuleSheaf r θ) :
    differentialAdditiveSheaf r θ ≅ degreeOneSheaf r θ :=
  (SheafOfModules.toSheaf (ringSheaf (projectiveCurve r θ).sheaf)).mapIso e

private def canonicalH1EquivAt (r θ : ℂ)
    (e : projectiveDifferentialSheaf r θ ≅ degreeOneModuleSheaf r θ) :
    ProjectiveSheafH1 r θ ≃+ DifferentialSheafH1 r θ :=
  (((Sheaf.cohomologyPresheafFunctor
      (Opens.grothendieckTopology (projectiveCurve r θ)) 1).mapIso
        (canonicalAdditiveIsoAt r θ e)).app (op ⊤)).addCommGroupIsoToAddEquiv.symm

private theorem canonicalH1EquivAt_smul (r θ : ℂ)
    (e : projectiveDifferentialSheaf r θ ≅ degreeOneModuleSheaf r θ)
    (c : ℂ) (x : ProjectiveSheafH1 r θ) :
    canonicalH1EquivAt r θ e (c • x) = c • canonicalH1EquivAt r θ e x :=
  cohomologyMap_scalar (projectiveCurve r θ).sheaf (projectiveGlobalCoefficient r θ)
    (degreeOneModuleSheaf r θ) e.inv 1 ⊤ c x

/-- The already constructed literal canonical map commutes with the
intrinsic scalar actions because it comes from a module-sheaf morphism. -/
theorem literalCanonicalH1Equiv_smul (c : ℂ) (x : ProjectiveSheafH1 57 1) :
    literalCanonicalH1Equiv (c • x) = c • literalCanonicalH1Equiv x :=
  canonicalH1EquivAt_smul 57 1 literalProjectiveCanonicalIso c x

private def cechCanonicalAddEquiv (r θ : ℂ) (hr : r ≠ 0)
    (e : ProjectiveSheafH1 r θ ≃+ DifferentialSheafH1 r θ) :
    DegreeOneCech r θ ≃+ DifferentialSheafH1 r θ :=
  (degreeOneCechHOneEquiv r θ hr).trans e

/-- The existing actual additive Cech and canonical comparisons. -/
def literalCechCanonicalAddEquiv :
    DegreeOneCech 57 1 ≃+ DifferentialSheafH1 57 1 :=
  cechCanonicalAddEquiv 57 1 (by norm_num) literalCanonicalH1Equiv

@[simp] theorem literalCechCanonicalAddEquiv_apply (z : DegreeOneCech 57 1) :
    literalCechCanonicalAddEquiv z =
      literalCanonicalH1Equiv (degreeOneToProjectiveH1 57 1 (by norm_num) z) := rfl

theorem literalCechCanonicalAddEquiv_smul (c : ℂ) (z : DegreeOneCech 57 1) :
    literalCechCanonicalAddEquiv (c • z) = c • literalCechCanonicalAddEquiv z := by
  change literalCanonicalH1Equiv (degreeOneToProjectiveH1 57 1 (by norm_num) (c • z)) = _
  exact (congrArg literalCanonicalH1Equiv
    (degreeOneToProjectiveH1_smul 57 1 (by norm_num) c z)).trans
      (literalCanonicalH1Equiv_smul c _)

/-- The precise canonical normalization: the image of x₃⁹/(g₁g₂). -/
def literalCanonicalNormalization : DifferentialSheafH1 57 1 :=
  literalCechCanonicalAddEquiv incidenceCechNormalization

/-- Scalar multiplication of the actual normalization class. -/
def literalCanonicalNormalizationLinear : ℂ →ₗ[ℂ] DifferentialSheafH1 57 1 :=
  LinearMap.toSpanSingleton ℂ (DifferentialSheafH1 57 1) literalCanonicalNormalization

/-- The scalar parameterization agrees pointwise with the original
Cech coordinate followed by the already constructed canonical map. -/
theorem literalCanonicalNormalizationLinear_eq_actual (c : ℂ) :
    literalCanonicalNormalizationLinear c =
      literalCechCanonicalAddEquiv (incidenceCechEquiv c) := by
  change c • literalCechCanonicalAddEquiv incidenceCechNormalization =
    literalCechCanonicalAddEquiv (c • incidenceCechNormalization)
  exact (literalCechCanonicalAddEquiv_smul c incidenceCechNormalization).symm

theorem literalCanonicalNormalizationLinear_injective :
    Function.Injective literalCanonicalNormalizationLinear := by
  intro a b hab
  apply incidenceCechEquiv.injective
  apply literalCechCanonicalAddEquiv.injective
  simpa only [literalCanonicalNormalizationLinear_eq_actual] using hab

theorem literalCanonicalNormalizationLinear_surjective :
    Function.Surjective literalCanonicalNormalizationLinear := by
  intro x
  obtain ⟨z, rfl⟩ := literalCechCanonicalAddEquiv.surjective x
  obtain ⟨c, hc⟩ := incidenceCechEquiv.surjective z
  refine ⟨c, ?_⟩
  rw [literalCanonicalNormalizationLinear_eq_actual, hc]

/-- A linear parameterization of the complete actual H¹(Ω) on the literal
incidence curve, using the original Cech normalization. -/
def literalCanonicalNormalizationEquiv : ℂ ≃ₗ[ℂ] DifferentialSheafH1 57 1 :=
  LinearEquiv.ofBijective literalCanonicalNormalizationLinear
    ⟨literalCanonicalNormalizationLinear_injective,
      literalCanonicalNormalizationLinear_surjective⟩

/-- The linear Cech comparison, recovered through the proved coordinate. -/
def literalCechCanonicalEquiv :
    DegreeOneCech 57 1 ≃ₗ[ℂ] DifferentialSheafH1 57 1 :=
  incidenceCechEquiv.symm.trans literalCanonicalNormalizationEquiv

@[simp] theorem literalCechCanonicalEquiv_apply (z : DegreeOneCech 57 1) :
    literalCechCanonicalEquiv z =
      literalCanonicalH1Equiv (degreeOneToProjectiveH1 57 1 (by norm_num) z) := by
  change literalCanonicalNormalizationLinear (incidenceCechEquiv.symm z) = _
  exact (literalCanonicalNormalizationLinear_eq_actual _).trans
    (congrArg literalCechCanonicalAddEquiv (incidenceCechEquiv.apply_symm_apply z))

@[simp] theorem literalCechCanonicalEquiv_normalization :
    literalCechCanonicalEquiv incidenceCechNormalization = literalCanonicalNormalization :=
  literalCechCanonicalEquiv_apply incidenceCechNormalization

@[simp] theorem literalCanonicalNormalizationEquiv_one :
    literalCanonicalNormalizationEquiv 1 = literalCanonicalNormalization := by
  change (1 : ℂ) • literalCanonicalNormalization = literalCanonicalNormalization
  exact one_smul _ _

/-- The resulting coordinate on the complete derived cohomology group. -/
def literalCanonicalCoordinate : DifferentialSheafH1 57 1 →ₗ[ℂ] ℂ :=
  literalCanonicalNormalizationEquiv.symm.toLinearMap

instance literalDifferentialSheafH1_finite : Module.Finite ℂ (DifferentialSheafH1 57 1) :=
  Module.Finite.of_surjective literalCanonicalNormalizationEquiv.toLinearMap
    literalCanonicalNormalizationEquiv.surjective

theorem literalDifferentialSheafH1_finrank : Module.finrank ℂ (DifferentialSheafH1 57 1) = 1 := by
  rw [← literalCanonicalNormalizationEquiv.finrank_eq]
  exact Module.finrank_self ℂ

@[simp] theorem literalCanonicalCoordinate_normalization :
    literalCanonicalCoordinate literalCanonicalNormalization = 1 := by
  change literalCanonicalNormalizationEquiv.symm literalCanonicalNormalization = 1
  apply literalCanonicalNormalizationEquiv.injective
  rw [LinearEquiv.apply_symm_apply]
  exact literalCanonicalNormalizationEquiv_one.symm

theorem literalCanonicalCoordinate_eq_zero_iff (x : DifferentialSheafH1 57 1) :
    literalCanonicalCoordinate x = 0 ↔ x = 0 :=
  literalCanonicalNormalizationEquiv.symm.map_eq_zero_iff

theorem literalCanonicalNormalization_ne_zero : literalCanonicalNormalization ≠ 0 := by
  intro hz
  have h := literalCanonicalCoordinate_normalization
  rw [hz, map_zero] at h
  exact zero_ne_one h

/-- Pulling a nonzero derived-cohomology functional back through the
actual Cech equivalence preserves nonzeroness. -/
theorem trace_comp_cech_ne_zero (τ : DifferentialSheafH1 57 1 →ₗ[ℂ] ℂ) (hτ : τ ≠ 0) :
    τ.comp literalCechCanonicalEquiv.toLinearMap ≠ 0 := by
  intro hz
  apply hτ
  ext x
  obtain ⟨z, rfl⟩ := literalCechCanonicalEquiv.surjective x
  exact congrArg (fun f : DegreeOneCech 57 1 →ₗ[ℂ] ℂ => f z) hz

/-- Every nonzero linear functional on the complete actual H¹(Ω) is
injective; the conclusion concerns the intrinsic complex action. -/
theorem nonzero_canonical_trace_injective
    (τ : DifferentialSheafH1 57 1 →ₗ[ℂ] ℂ) (hτ : τ ≠ 0) : Function.Injective τ := by
  intro x y hxy
  apply literalCechCanonicalEquiv.symm.injective
  apply nonzero_trace_injective (τ.comp literalCechCanonicalEquiv.toLinearMap)
    (trace_comp_cech_ne_zero τ hτ)
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    LinearEquiv.apply_symm_apply] using hxy

/-- Nonzero functionals on the actual canonical cohomology differ by
one common nonzero complex scalar. -/
theorem nonzero_canonical_traces_proportional
    (τ σ : DifferentialSheafH1 57 1 →ₗ[ℂ] ℂ) (hτ : τ ≠ 0) (hσ : σ ≠ 0) :
    ∃ a : ℂ, a ≠ 0 ∧ τ = a • σ := by
  obtain ⟨a, ha, heq⟩ := nonzero_traces_proportional
    (τ.comp literalCechCanonicalEquiv.toLinearMap)
    (σ.comp literalCechCanonicalEquiv.toLinearMap)
    (trace_comp_cech_ne_zero τ hτ) (trace_comp_cech_ne_zero σ hσ)
  refine ⟨a, ha, ?_⟩
  ext x
  obtain ⟨z, rfl⟩ := literalCechCanonicalEquiv.surjective x
  exact congrArg (fun f : DegreeOneCech 57 1 →ₗ[ℂ] ℂ => f z) heq

/-- Trace normalization has no effect on the kernel of any linear map
into the complete actual canonical cohomology line. -/
theorem canonical_trace_kernel_independent {V : Type*} [AddCommGroup V] [Module ℂ V]
    (f : V →ₗ[ℂ] DifferentialSheafH1 57 1)
    (τ σ : DifferentialSheafH1 57 1 →ₗ[ℂ] ℂ) (hτ : τ ≠ 0) (hσ : σ ≠ 0) :
    LinearMap.ker (τ.comp f) = LinearMap.ker (σ.comp f) := by
  ext v
  change τ (f v) = 0 ↔ σ (f v) = 0
  constructor
  · intro hv
    have hz : f v = 0 := nonzero_canonical_trace_injective τ hτ
      (hv.trans (map_zero τ).symm)
    rw [hz, map_zero]
  · intro hv
    have hz : f v = 0 := nonzero_canonical_trace_injective σ hσ
      (hv.trans (map_zero σ).symm)
    rw [hz, map_zero]

/-- The original paired degree-nine numerator, transported through our
fixed actual canonical isomorphism. -/
def literalPairedCanonicalLinear : (Fin 9 → ℂ) →ₗ[ℂ] DifferentialSheafH1 57 1 :=
  literalCechCanonicalEquiv.toLinearMap.comp pairedClassLinear

@[simp] theorem literalPairedCanonicalLinear_apply (v : Fin 9 → ℂ) :
    literalPairedCanonicalLinear v = literalCanonicalH1Equiv
      (degreeOneToProjectiveH1 57 1 (by norm_num) (pairedDegreeOneClass 57 1 v)) :=
  literalCechCanonicalEquiv_apply (pairedDegreeOneClass 57 1 v)

/-- The exact original paired-class coefficient now holds in the full
actual derived cohomology of Ω, with the displayed normalization. -/
theorem literalPairedCanonicalLinear_eq (v : Fin 9 → ℂ) :
    literalPairedCanonicalLinear v =
      (((12 + 24 * Complex.I) / 5) * derivativeTrace 1 v) • literalCanonicalNormalization := by
  change literalCechCanonicalEquiv (pairedDegreeOneClass 57 1 v) = _
  exact ((congrArg literalCechCanonicalEquiv
    (pairedClass_eq_derivativeTrace_smul_normalization v)).trans
      (literalCechCanonicalEquiv.map_smul _ _)).trans
        (congrArg (fun z : DifferentialSheafH1 57 1 =>
          (((12 + 24 * Complex.I) / 5) * derivativeTrace 1 v) • z)
          literalCechCanonicalEquiv_normalization)

theorem literalCanonicalCoordinate_paired (v : Fin 9 → ℂ) :
    literalCanonicalCoordinate (literalPairedCanonicalLinear v) =
      ((12 + 24 * Complex.I) / 5) * derivativeTrace 1 v := by
  rw [literalPairedCanonicalLinear_eq, map_smul,
    literalCanonicalCoordinate_normalization, smul_eq_mul, mul_one]

theorem literalPairedCanonicalLinear_eq_zero_iff (v : Fin 9 → ℂ) :
    literalPairedCanonicalLinear v = 0 ↔ derivativeTrace 1 v = 0 := by
  constructor
  · intro hz
    have hc : pairedDegreeOneClass 57 1 v = 0 :=
      literalCechCanonicalEquiv.injective (hz.trans (map_zero literalCechCanonicalEquiv).symm)
    exact (pairedDegreeOneClass_eq_zero_iff_derivativeTrace_zero v).mp hc
  · intro hz
    have hc := (pairedDegreeOneClass_eq_zero_iff_derivativeTrace_zero v).mpr hz
    change literalCechCanonicalEquiv (pairedDegreeOneClass 57 1 v) = 0
    rw [hc, map_zero]

/-- Every functional on actual canonical H¹ gives the two-entry row
with one common scalar, fixed by its value on the canonical normalization. -/
theorem literal_paired_trace_formula
    (τ : DifferentialSheafH1 57 1 →ₗ[ℂ] ℂ) (v : Fin 9 → ℂ) :
    τ (literalPairedCanonicalLinear v) =
      (((12 + 24 * Complex.I) / 5) * τ literalCanonicalNormalization) *
        ((Complex.I * v 1 - (1 + Complex.I) * v 8) / 6) := by
  rw [literalPairedCanonicalLinear_eq, map_smul, smul_eq_mul, smooth_derivativeTrace_explicit]
  ring

theorem literal_paired_trace_scale_ne_zero
    (τ : DifferentialSheafH1 57 1 →ₗ[ℂ] ℂ) (hτ : τ ≠ 0) :
    (((12 + 24 * Complex.I) / 5) * τ literalCanonicalNormalization) ≠ 0 := by
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    literalCechCanonicalEquiv_normalization] using
      paired_trace_scale_ne_zero (τ.comp literalCechCanonicalEquiv.toLinearMap)
        (trace_comp_cech_ne_zero τ hτ)

#print axioms degreeOneCechHOneLinearEquiv
#print axioms literalCanonicalH1Equiv_smul
#print axioms literalCanonicalNormalizationEquiv
#print axioms literalDifferentialSheafH1_finrank
#print axioms canonical_trace_kernel_independent
#print axioms literalCanonicalCoordinate_paired
#print axioms literalPairedCanonicalLinear_eq_zero_iff
#print axioms literal_paired_trace_scale_ne_zero

end CycleQ2GeometricLiteralHOne
end
