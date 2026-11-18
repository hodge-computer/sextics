import Proposal.GeometricLiteralAmbientSmooth
import Proposal.GeometricLiteralAmbientChartBaseChange
import Proposal.GeometricLiteralAmbientChartCoordinates
import Mathlib.AlgebraicGeometry.Pullbacks

/-! The four fixed-sextic affine charts on the smooth proper incidence fiber.
Their coordinate rings are precisely those carrying the Kodaira–Spencer and
residue calculations. Their maps to the original family specialize cubic
coefficients and preserve the declared normalized polynomial coordinates.
Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralAmbientCharts

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial
open CycleQ2SeedCubicFamily CycleQ2SeedProjectiveFamily CycleQ2SeedFamilyChart
  CycleQ2SeedFamilyNormalized CycleQ2LiteralAmbientSmooth CycleQ2LiteralAmbientChartBaseChange
  CycleQ2IncidenceDehomogenizedChart CycleQ2LiteralAbelJacobiContraction

attribute [local instance] incidenceAlgebra

abbrev fixedOpen (i : Fin 4) : (IncidenceFiber 57).Opens :=
  (pullback.snd incidenceParameter (familyToParameters 57)) ⁻¹ᵁ coordinateOpen 57 i

/-- These are the four weight-one opens in the same fixed smooth threefold. -/
theorem fixedOpen_cover : (⨆ i : Fin 4, fixedOpen i) = ⊤ := by
  apply top_unique
  intro z _
  apply TopologicalSpace.Opens.mem_iSup.mpr
  exact exists_weightOne_of_over_incidence 57 (pullback.fst incidenceParameter (familyToParameters 57) z)
    (pullback.snd incidenceParameter (familyToParameters 57) z)
    (congrArg (fun g : IncidenceFiber 57 ⟶ parameterScheme => g z)
      (pullback.condition (f := incidenceParameter) (g := familyToParameters 57))).symm

/-- Base change of the normalized family chart followed by the actual triangular
change of variables, whose last coordinate is the normalized `w + x₂²`. -/
def fixedRingEquiv (i : Fin 4) : ChartFiber 57 i ≃ₐ[ℂ] T i :=
  (normalizedFiberEquiv 57 i).trans ((Ideal.quotientEquivAlgOfEq ℂ (literalIdeal_eq_pair 57 i)).trans
    (CycleQ2LiteralAmbientChartCoordinates.normalizedEquiv i))

def chartSpecialization (i : Fin 4) : NormalizedRing 57 i →+* T i :=
  (fixedRingEquiv i).toRingHom.comp (Algebra.TensorProduct.includeRight
    (R := ParameterRing) (A := ℂ) (B := NormalizedRing 57 i)).toRingHom

/-- Every normalized polynomial specializes by evaluating its coefficients and
using the dehomogenization in the moving-curve and residue models. -/
@[simp] theorem chartSpecialization_polynomial (i : Fin 4) (p : FamilyPolynomial) :
    chartSpecialization i (normalizedQuotient 57 i p) =
      Ideal.Quotient.mk (fixedIdeal i)
        (dehomogenize i (MvPolynomial.map (coefficientEvaluation incidenceCoefficients) p)) := by
  change (CycleQ2LiteralAmbientChartCoordinates.normalizedEquiv i)
    ((Ideal.quotientEquivAlgOfEq ℂ (literalIdeal_eq_pair 57 i))
      ((normalizedFiberEquiv 57 i) ((Algebra.TensorProduct.includeRight
        (R := ParameterRing) (A := ℂ) (B := NormalizedRing 57 i)) (normalizedQuotient 57 i p)))) = _
  rw [normalizedFiberEquiv_includeRight]
  rfl

private abbrev AffineFiber (i : Fin 4) := pullback incidenceParameter (normalizedToParameters 57 i)

private def affineIso (i : Fin 4) : AffineFiber i ≅ Spec (CommRingCat.of (T i)) :=
  pullbackSpecIso ParameterRing ℂ (NormalizedRing 57 i) ≪≫
    Scheme.Spec.mapIso (fixedRingEquiv i).toRingEquiv.toCommRingCatIso.symm.op

private def chartPullback (i : Fin 4) :=
  pullback incidenceParameter ((coordinateOpen 57 i).ι ≫ familyToParameters 57)

private def affineToProjective (i : Fin 4) : AffineFiber i ≅ chartPullback i :=
  asIso (pullback.map incidenceParameter (normalizedToParameters 57 i) incidenceParameter
    ((coordinateOpen 57 i).ι ≫ familyToParameters 57) (𝟙 _) (normalizedAffineChart 57 i).hom
    (𝟙 _) (by simp) (by
      simpa [normalizedChartToFamily, normalizedToParameters] using
        (normalizedChartToFamily_overParameters 57 i).symm))

private def projectiveToOpen (i : Fin 4) : chartPullback i ≅ (fixedOpen i).toScheme :=
  (pullbackLeftPullbackSndIso incidenceParameter (familyToParameters 57) (coordinateOpen 57 i).ι).symm ≪≫
    pullbackRestrictIsoRestrict (pullback.snd incidenceParameter (familyToParameters 57)) (coordinateOpen 57 i)

/-- The affine scheme supporting the local variation calculation is the native
weight-one open of the specialized threefold. -/
def fixedChart (i : Fin 4) : Spec (CommRingCat.of (T i)) ≅ (fixedOpen i).toScheme :=
  (affineIso i).symm ≪≫ affineToProjective i ≪≫ projectiveToOpen i

/-- Inclusion of the explicit local model into the fixed smooth proper threefold. -/
def chartInclusion (i : Fin 4) : Spec (CommRingCat.of (T i)) ⟶ IncidenceFiber 57 :=
  (fixedChart i).hom ≫ (fixedOpen i).ι

instance (i : Fin 4) : IsOpenImmersion (chartInclusion i) := by
  unfold chartInclusion
  infer_instance

private theorem affineIso_inv_fst (i : Fin 4) :
    (affineIso i).inv ≫ pullback.fst incidenceParameter (normalizedToParameters 57 i) =
      Spec.map (CommRingCat.ofHom (algebraMap ℂ (T i))) := by
  change (Spec.map (CommRingCat.ofHom (fixedRingEquiv i).toRingHom) ≫
    (pullbackSpecIso ParameterRing ℂ (NormalizedRing 57 i)).inv) ≫ pullback.fst _ _ = _
  rw [Category.assoc, pullbackSpecIso_inv_fst', ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  exact (fixedRingEquiv i).commutes

private theorem affineIso_inv_snd (i : Fin 4) :
    (affineIso i).inv ≫ pullback.snd incidenceParameter (normalizedToParameters 57 i) =
      Spec.map (CommRingCat.ofHom (chartSpecialization i)) := by
  change (Spec.map (CommRingCat.ofHom (fixedRingEquiv i).toRingHom) ≫
    (pullbackSpecIso ParameterRing ℂ (NormalizedRing 57 i)).inv) ≫ pullback.snd _ _ = _
  rw [Category.assoc, pullbackSpecIso_inv_snd, ← Spec.map_comp]
  rfl

@[reassoc, simp] theorem chartInclusion_overComplex (i : Fin 4) :
    chartInclusion i ≫ incidenceFiberToComplex 57 =
      Spec.map (CommRingCat.ofHom (algebraMap ℂ (T i))) := by
  simp only [chartInclusion, fixedChart, projectiveToOpen, fixedOpen, affineToProjective,
    incidenceFiberToComplex, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    pullbackRestrictIsoRestrict_hom_ι_assoc, pullbackLeftPullbackSndIso_inv_fst, asIso_hom,
    pullback.lift_fst, Category.comp_id, affineIso_inv_fst]

@[reassoc, simp] theorem chartInclusion_toFamily (i : Fin 4) :
    chartInclusion i ≫ pullback.snd incidenceParameter (familyToParameters 57) =
      Spec.map (CommRingCat.ofHom (chartSpecialization i)) ≫ normalizedChartToFamily 57 i := by
  simp only [chartInclusion, fixedChart, projectiveToOpen, fixedOpen, affineToProjective,
    Iso.trans_hom, Iso.symm_hom, Category.assoc, pullbackRestrictIsoRestrict_hom_ι_assoc,
    pullbackLeftPullbackSndIso_inv_fst_snd, asIso_hom, pullback.lift_snd_assoc,
    ← affineIso_inv_snd, normalizedChartToFamily]

/-- The very affine ring used for contraction is smooth of relative dimension
three over ℂ on each coordinate chart. -/
theorem affine_smooth (i : Fin 4) : SmoothOfRelativeDimension 3
    (Spec.map (CommRingCat.ofHom (algebraMap ℂ (T i)))) := by
  rw [← chartInclusion_overComplex]
  exact IsZariskiLocalAtSource.comp (P := @SmoothOfRelativeDimension 3)
    literal_fiber_smooth (chartInclusion i)

end CycleQ2LiteralAmbientCharts

#print axioms CycleQ2LiteralAmbientCharts.fixedOpen_cover
#print axioms CycleQ2LiteralAmbientCharts.chartInclusion_overComplex
#print axioms CycleQ2LiteralAmbientCharts.chartInclusion_toFamily

#print axioms CycleQ2LiteralAmbientCharts.affine_smooth
