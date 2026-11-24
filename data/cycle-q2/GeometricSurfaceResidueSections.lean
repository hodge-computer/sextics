import Proposal.GeometricSurfaceOverlap
import Proposal.GeometricExteriorSheaf
import Proposal.GeometricSurfaceNormalCharts

/-!
# Actual signed cubic residue sections near the literal projective curve

The residue comparisons use the actual affine scheme charts, canonical complex
coefficients, universal Kähler differentials and literal equation determinants.
The cross-coordinate factor is -b^3. A fixed homogeneous cubic cancels its
weight, and the coordinate orientation signs are inserted before passing
through the canonical exterior-sheaf unit. The resulting sections glue on the
actual union of the twelve Jacobian opens. For the literal member (57,1), the
preimage of this neighborhood is the entire curve.
-/

section SurfaceResidueAssemblyPart01

section ResidueCorePart0

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2GeometricSurfaceResidueSections

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry Module
open CycleQ2GeometricDifferentialSheaf CycleQ2GeometricAffineChartSections
open CycleQ2GeometricDifferentialChartTransport CycleQ2GeometricSheafKaehlerMap
open CycleQ2GeometricSurfaceExteriorSections CycleQ2GeometricSurfaceAdjunction
open CycleQ2GeometricSurfaceDeterminantNaturality
open CycleQ2GeometricSurfaceJacobianCharts CycleQ2GeometricPrincipalChartSections

variable {X : Scheme.{0}} {U : X.Opens} {A : Type} [CommRing A] [Algebra ℂ A]
  (e : U.toScheme ≅ Spec (CommRingCat.of A))
  (f : X ⟶ Spec (CommRingCat.of ℂ))
  (h : e.inv ≫ U.ι ≫ f = Spec.map (CommRingCat.ofHom (algebraMap ℂ A)))

theorem chartKaehlerSection_D (V : Over U) (a : A) :
    chartKaehlerSection e f h V (KaehlerDifferential.D ℂ A a) =
      (universalDifferential X.sheaf (schemeCoefficient f)).d (X := op V.left)
        (chartSection e V a) :=
  sectionLift_D X.sheaf (schemeCoefficient f)
    (differentialSheaf X.sheaf (schemeCoefficient f))
    (universalDifferential X.sheaf (schemeCoefficient f)) V.left
    (chartSection e V) (chartSection_complex e f h V) a


private theorem linearEquiv_smul_normalized {R M : Type} [CommRing R]
    [AddCommGroup M] [Module R M] (e : M ≃ₗ[R] R) (m : M) (hm : e m = 1) (a : R) :
    e (a • m) = a := by
  rw [map_smul,hm,smul_eq_mul,mul_one]

private theorem linearEquiv_smul_apply {R M : Type} [CommRing R]
    [AddCommGroup M] [Module R M] (e : M ≃ₗ[R] R) (m : M) (a : R) :
    e (a • m) = a * e m := by rw [map_smul,smul_eq_mul]

section Residue

variable (v : Fin 2 → SurfacePoly) (n t : SurfacePoly)
  (eR : U.toScheme ≅ Spec (CommRingCat.of (AdjunctionPatch v n t)))
  (hR : eR.inv ≫ U.ι ≫ f =
    Spec.map (CommRingCat.ofHom (algebraMap ℂ (AdjunctionPatch v n t))))

/-- The polynomial differential viewed in the actual surface differential
sheaf on an arbitrary subopen of the Jacobian chart. -/
def polynomialDifferentialSection (V : Over U) (p : SurfacePoly) :
    (ChartDifferentialModule f).val.obj (op V) :=
  (universalDifferential X.sheaf (schemeCoefficient f)).d (X := op V.left)
    (chartSection eR V (algebraMap SurfacePoly (AdjunctionPatch v n t) p))

theorem chartResidueCoordinate_polynomial_pair (V : Over U) (p q : SurfacePoly) :
    chartResidueCoordinate f v n t eR hR V
      (exteriorPower.ιMulti Γ(X,V.left) 2
        ![polynomialDifferentialSection f v n t eR V p,
          polynomialDifferentialSection f v n t eR V q]) =
      chartSection eR V (algebraMap (SurfaceChartRing v) (AdjunctionPatch v n t)
        (augmentedJacobian v p q)) := by
  have hc := chartResidueCoordinate_wedge f v n t eR hR V
    (KaehlerDifferential.D ℂ (AdjunctionPatch v n t)
      (algebraMap SurfacePoly (AdjunctionPatch v n t) p))
    (KaehlerDifferential.D ℂ (AdjunctionPatch v n t)
      (algebraMap SurfacePoly (AdjunctionPatch v n t) q))
  simpa only [chartKaehlerSection_D, polynomialDifferentialSection,
    localSurfaceDeterminantEquiv_pair] using hc

/-- Multiplying the actual residue form by its actual Jacobian recovers
its two genuine polynomial differentials on every subopen. -/
theorem chartJacobian_smul_residue (V : Over U) :
    chartSection eR V (algebraMap (SurfaceChartRing v) (AdjunctionPatch v n t)
        (augmentedJacobian v n t)) •
      chartResidueSection f v n t eR hR V =
    exteriorPower.ιMulti Γ(X,V.left) 2
      ![polynomialDifferentialSection f v n t eR V n,
        polynomialDifferentialSection f v n t eR V t] := by
  apply (chartResidueCoordinate f v n t eR hR V).injective
  exact (linearEquiv_smul_normalized (chartResidueCoordinate f v n t eR hR V)
    (chartResidueSection f v n t eR hR V)
    (chartResidueSection_normalization f v n t eR hR V) _).trans
      (chartResidueCoordinate_polynomial_pair f v n t eR hR V n t).symm

/-- The same actual local residue, written in the common ambient section
module so comparison between two containing opens requires no new scalar choice. -/
def chartResidueSection_common (V : Over U) :
    ⋀[Γ(X,V.left)]^2 ((differentialSheaf X.sheaf (schemeCoefficient f)).val.obj (op V.left)) :=
  chartResidueSection f v n t eR hR V

def chartResidueCoordinate_common (V : Over U) :
    (⋀[Γ(X,V.left)]^2 ((differentialSheaf X.sheaf (schemeCoefficient f)).val.obj (op V.left))) ≃ₗ[
      Γ(X,V.left)] Γ(X,V.left) :=
  chartResidueCoordinate f v n t eR hR V

def polynomialDifferentialSection_common (V : Over U) (p : SurfacePoly) :
    (differentialSheaf X.sheaf (schemeCoefficient f)).val.obj (op V.left) :=
  polynomialDifferentialSection f v n t eR V p

@[simp] theorem chartResidueSection_common_normalization (V : Over U) :
    chartResidueCoordinate_common f v n t eR hR V
      (chartResidueSection_common f v n t eR hR V) = 1 :=
  chartResidueSection_normalization f v n t eR hR V

theorem chartResidueCoordinate_common_polynomial_pair (V : Over U) (p q : SurfacePoly) :
    chartResidueCoordinate_common f v n t eR hR V
      (exteriorPower.ιMulti Γ(X,V.left) 2
        ![polynomialDifferentialSection_common f v n t eR V p,
          polynomialDifferentialSection_common f v n t eR V q]) =
      chartSection eR V (algebraMap (SurfaceChartRing v) (AdjunctionPatch v n t)
        (augmentedJacobian v p q)) :=
  chartResidueCoordinate_polynomial_pair f v n t eR hR V p q

theorem chartJacobian_smul_residue_common (V : Over U) :
    chartSection eR V (algebraMap (SurfaceChartRing v) (AdjunctionPatch v n t)
        (augmentedJacobian v n t)) •
      chartResidueSection_common f v n t eR hR V =
    exteriorPower.ιMulti Γ(X,V.left) 2
      ![polynomialDifferentialSection_common f v n t eR V n,
        polynomialDifferentialSection_common f v n t eR V t] :=
  chartJacobian_smul_residue f v n t eR hR V


end Residue

section SamePresentation

variable {U₁ U₂ : X.Opens} (v : Fin 2 → SurfacePoly) (n₁ t₁ n₂ t₂ : SurfacePoly)
  (e₁ : U₁.toScheme ≅ Spec (CommRingCat.of (AdjunctionPatch v n₁ t₁)))
  (e₂ : U₂.toScheme ≅ Spec (CommRingCat.of (AdjunctionPatch v n₂ t₂)))
  (h₁ : e₁.inv ≫ U₁.ι ≫ f =
    Spec.map (CommRingCat.ofHom (algebraMap ℂ (AdjunctionPatch v n₁ t₁))))
  (h₂ : e₂.inv ≫ U₂.ι ≫ f =
    Spec.map (CommRingCat.ofHom (algebraMap ℂ (AdjunctionPatch v n₂ t₂))))

/-- Two actual affine presentations with the same restricted surface-ring
map give the same normalized residue section. -/
theorem residueSection_eq_of_base_sections (V : X.Opens) (hV₁ : V ≤ U₁) (hV₂ : V ≤ U₂)
    (hbase : ∀ a : SurfaceChartRing v,
      chartSection e₁ (Over.mk (homOfLE hV₁))
          (algebraMap (SurfaceChartRing v) (AdjunctionPatch v n₁ t₁) a) =
        chartSection e₂ (Over.mk (homOfLE hV₂))
          (algebraMap (SurfaceChartRing v) (AdjunctionPatch v n₂ t₂) a)) :
    chartResidueSection_common f v n₁ t₁ e₁ h₁ (Over.mk (homOfLE hV₁)) =
      chartResidueSection_common f v n₂ t₂ e₂ h₂ (Over.mk (homOfLE hV₂)) := by
  let V₁ : Over U₁ := Over.mk (homOfLE hV₁)
  let V₂ : Over U₂ := Over.mk (homOfLE hV₂)
  have hD (p : SurfacePoly) : polynomialDifferentialSection_common f v n₁ t₁ e₁ V₁ p =
      polynomialDifferentialSection_common f v n₂ t₂ e₂ V₂ p := by
    apply congrArg ((universalDifferential X.sheaf (schemeCoefficient f)).d (X := op V))
    rw [IsScalarTower.algebraMap_apply SurfacePoly (SurfaceChartRing v) (AdjunctionPatch v n₁ t₁),
      IsScalarTower.algebraMap_apply SurfacePoly (SurfaceChartRing v) (AdjunctionPatch v n₂ t₂)]
    exact hbase (algebraMap SurfacePoly (SurfaceChartRing v) p)
  have hu : IsUnit (chartSection e₂ V₂
      (algebraMap (SurfaceChartRing v) (AdjunctionPatch v n₂ t₂) (augmentedJacobian v n₂ t₂))) :=
    (IsLocalization.Away.algebraMap_isUnit (S := AdjunctionPatch v n₂ t₂)
      (augmentedJacobian v n₂ t₂)).map (chartSection e₂ V₂)
  apply (chartResidueCoordinate_common f v n₁ t₁ e₁ h₁ V₁).injective
  rw [chartResidueSection_common_normalization]
  apply hu.mul_left_cancel
  calc
    _ = chartSection e₂ V₂ (algebraMap (SurfaceChartRing v) (AdjunctionPatch v n₂ t₂)
        (augmentedJacobian v n₂ t₂)) := mul_one _
    _ = chartSection e₁ V₁ (algebraMap (SurfaceChartRing v) (AdjunctionPatch v n₁ t₁)
        (augmentedJacobian v n₂ t₂)) := (hbase (augmentedJacobian v n₂ t₂)).symm
    _ = chartResidueCoordinate_common f v n₁ t₁ e₁ h₁ V₁
        (exteriorPower.ιMulti Γ(X,V) 2
          ![polynomialDifferentialSection_common f v n₁ t₁ e₁ V₁ n₂,
            polynomialDifferentialSection_common f v n₁ t₁ e₁ V₁ t₂]) :=
      (chartResidueCoordinate_common_polynomial_pair f v n₁ t₁ e₁ h₁ V₁ n₂ t₂).symm
    _ = chartResidueCoordinate_common f v n₁ t₁ e₁ h₁ V₁
        (exteriorPower.ιMulti Γ(X,V) 2
          ![polynomialDifferentialSection_common f v n₂ t₂ e₂ V₂ n₂,
            polynomialDifferentialSection_common f v n₂ t₂ e₂ V₂ t₂]) := by rw [hD n₂,hD t₂]
    _ = chartResidueCoordinate_common f v n₁ t₁ e₁ h₁ V₁
        (chartSection e₂ V₂ (algebraMap (SurfaceChartRing v) (AdjunctionPatch v n₂ t₂)
          (augmentedJacobian v n₂ t₂)) • chartResidueSection_common f v n₂ t₂ e₂ h₂ V₂) :=
      congrArg (chartResidueCoordinate_common f v n₁ t₁ e₁ h₁ V₁)
        (chartJacobian_smul_residue_common f v n₂ t₂ e₂ h₂ V₂).symm
    _ = _ := linearEquiv_smul_apply
      (chartResidueCoordinate_common f v n₁ t₁ e₁ h₁ V₁)
      (chartResidueSection_common f v n₂ t₂ e₂ h₂ V₂) _

end SamePresentation


#print axioms residueSection_eq_of_base_sections
end CycleQ2GeometricSurfaceResidueSections
end

end ResidueCorePart0

section ResidueCorePart1

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2GeometricSurfaceAmbientDifferential

open MvPolynomial Module TensorProduct
open CycleQ2GeometricSurfaceAdjunction CycleQ2GeometricSurfaceWeightedChange
open CycleQ2GeometricFunctionalDifferentials

/-- The four actual polynomial coordinate differentials remain a basis
on the actual ambient principal localization. -/
def ambientKaehlerBasis :
    Basis (Option (Fin 3)) AmbientOverlap (KaehlerDifferential ℂ AmbientOverlap) := by
  letI : Algebra.FormallyEtale SurfacePoly AmbientOverlap :=
    Algebra.FormallyEtale.of_isLocalization
      (Rₘ := AmbientOverlap) (Submonoid.powers (X (some (1 : Fin 3)) : SurfacePoly))
  exact ((KaehlerDifferential.mvPolynomialBasis ℂ (Option (Fin 3))).baseChange AmbientOverlap).map
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale ℂ SurfacePoly AmbientOverlap)

theorem ambientKaehlerBasis_apply (j : Option (Fin 3)) :
    ambientKaehlerBasis j = KaehlerDifferential.D ℂ AmbientOverlap (ambientCoordinate j) := by
  letI : Algebra.FormallyEtale SurfacePoly AmbientOverlap :=
    Algebra.FormallyEtale.of_isLocalization
      (Rₘ := AmbientOverlap) (Submonoid.powers (X (some (1 : Fin 3)) : SurfacePoly))
  simp only [ambientKaehlerBasis, Basis.map_apply, Basis.baseChange_apply,
    KaehlerDifferential.mvPolynomialBasis_apply,
    KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_apply,
    KaehlerDifferential.mapBaseChange_tmul, one_smul, KaehlerDifferential.map_D]
  rfl

def ambientFunctional (j : Option (Fin 3)) :
    KaehlerDifferential ℂ AmbientOverlap →ₗ[AmbientOverlap] AmbientOverlap :=
  localFunctional (Submonoid.powers (X (some (1 : Fin 3)) : SurfacePoly)) AmbientOverlap
    ((KaehlerDifferential.mvPolynomialBasis ℂ (Option (Fin 3))).coord j)

theorem ambientFunctional_D (j : Option (Fin 3)) (a : AmbientOverlap) :
    ambientFunctional j (KaehlerDifferential.D ℂ AmbientOverlap a) = ambientPartial j a := rfl

theorem ambientKaehlerBasis_coord (j : Option (Fin 3)) :
    ambientKaehlerBasis.coord j = ambientFunctional j := by
  apply ambientKaehlerBasis.ext
  intro k
  rw [Basis.coord_apply, Basis.repr_self, ambientKaehlerBasis_apply, ambientFunctional_D,
    ambientPartial_coordinate]
  simp only [Finsupp.single_apply]

/-- Every actual localized differential has exactly the four ambient
partial coefficients used in the checked Jacobian transformation. -/
theorem ambient_D_expand (a : AmbientOverlap) :
    KaehlerDifferential.D ℂ AmbientOverlap a =
      ∑ j : Option (Fin 3), ambientPartial j a •
        KaehlerDifferential.D ℂ AmbientOverlap (ambientCoordinate j) := by
  have h := ambientKaehlerBasis.sum_repr (KaehlerDifferential.D ℂ AmbientOverlap a)
  have hc (j : Option (Fin 3)) : ambientKaehlerBasis.repr
      (KaehlerDifferential.D ℂ AmbientOverlap a) j = ambientPartial j a := by
    change ambientKaehlerBasis.coord j (KaehlerDifferential.D ℂ AmbientOverlap a) = _
    rw [ambientKaehlerBasis_coord,ambientFunctional_D]
  simpa only [hc,ambientKaehlerBasis_apply] using h.symm

#print axioms ambientKaehlerBasis
#print axioms ambient_D_expand

end CycleQ2GeometricSurfaceAmbientDifferential
end

noncomputable section
namespace CycleQ2GeometricSurfaceAmbientDifferential

open MvPolynomial Module
open CycleQ2GeometricSurfaceAdjunction CycleQ2GeometricSurfaceWeightedChange
open CycleQ2GeometricSurfaceOverlap CycleQ2GeometricSurfaceResidueTransition
open CycleQ2GeometricSurfaceDehomogenizedCharts
open CycleQ2GeometricAffineOverlap (differentialMap differentialMap_D differentialMap_smul)

/-- The actual ambient differential expansion descends through the
actual surface quotient homomorphism. -/
theorem surface_D_ambient (r θ : ℂ) (a : AmbientOverlap) :
    KaehlerDifferential.D ℂ (FirstOverlap r θ) (ambientToSurface r θ a) =
      ∑ j : Option (Fin 3), ambientToSurface r θ (ambientPartial j a) •
        KaehlerDifferential.D ℂ (FirstOverlap r θ) (coordinate (firstEquations r θ) j) := by
  have h := congrArg (differentialMap (ambientToSurface r θ)) (ambient_D_expand a)
  simpa only [differentialMap_D, map_sum, differentialMap_smul,
    ambientToSurface_coordinate] using h

theorem ambientPartial_changeEvaluate (i : Option (Fin 3)) (p : SurfacePoly) :
    ambientPartial i (ambientChangeEvaluate p) =
      ∑ j : Option (Fin 3), ambientChangeEvaluate (pderiv j p) * ambientJacobian j i := by
  change ambientPartial i (aeval ambientChangeCoordinate p) = _
  rw [derivation_aeval]
  rfl

theorem ambientToSurface_partial_change (r θ : ℂ) (p : SurfacePoly) (j : Fin 4) :
    ambientToSurface r θ
        (ambientPartial (_root_.finSuccEquiv 3 j) (ambientChangeEvaluate p)) =
      pulledGradient r θ p j := by
  rw [ambientPartial_changeEvaluate,map_sum]
  symm
  change (∑ k : Fin 4,
    (fun k : Option (Fin 3) =>
      overlapEquiv r θ (polynomialMap (secondEquations r θ) (pderiv k p)) *
        surfaceJacobian r θ k (_root_.finSuccEquiv 3 j)) (_root_.finSuccEquiv 3 k)) = _
  apply Eq.trans (Equiv.sum_comp (_root_.finSuccEquiv 3)
    (fun k : Option (Fin 3) =>
      overlapEquiv r θ (polynomialMap (secondEquations r θ) (pderiv k p)) *
        surfaceJacobian r θ k (_root_.finSuccEquiv 3 j)))
  apply Finset.sum_congr rfl
  intro k _
  rw [map_mul,ambientToSurface_changeEvaluate]
  rfl

/-- The rows used in the mixed determinant are exactly the coefficients
of the actual differential of each changed second-chart polynomial. -/
theorem surface_D_second_polynomial (r θ : ℂ) (p : SurfacePoly) :
    KaehlerDifferential.D ℂ (FirstOverlap r θ)
        (overlapEquiv r θ (polynomialMap (secondEquations r θ) p)) =
      ∑ j : Fin 4, pulledGradient r θ p j •
        KaehlerDifferential.D ℂ (FirstOverlap r θ)
          (coordinate (firstEquations r θ) (_root_.finSuccEquiv 3 j)) := by
  have h := surface_D_ambient r θ (ambientChangeEvaluate p)
  rw [ambientToSurface_changeEvaluate] at h
  calc
    _ = ∑ j : Option (Fin 3),
        ambientToSurface r θ (ambientPartial j (ambientChangeEvaluate p)) •
          KaehlerDifferential.D ℂ (FirstOverlap r θ) (coordinate (firstEquations r θ) j) := h
    _ = ∑ j : Fin 4,
        ambientToSurface r θ (ambientPartial (_root_.finSuccEquiv 3 j) (ambientChangeEvaluate p)) •
          KaehlerDifferential.D ℂ (FirstOverlap r θ)
            (coordinate (firstEquations r θ) (_root_.finSuccEquiv 3 j)) :=
      (Equiv.sum_comp (_root_.finSuccEquiv 3) _).symm
    _ = _ := by simp only [ambientToSurface_partial_change]

#print axioms surface_D_ambient
#print axioms surface_D_second_polynomial

end CycleQ2GeometricSurfaceAmbientDifferential

end

end ResidueCorePart1

section ResidueCorePart2

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2GeometricSurfaceOverlapDifferentials

open CategoryTheory Opposite AlgebraicGeometry
open CycleQ2CartierProjectiveCover CycleQ2GeometricSurfaceDehomogenizedCharts
open CycleQ2GeometricSurfaceAdjunction CycleQ2GeometricSurfaceOverlap
open CycleQ2GeometricSurfaceCoefficients CycleQ2GeometricAffineChartSections
open CycleQ2GeometricDifferentialSheaf CycleQ2GeometricSheafKaehlerMap

/-- The actual overlap-section map carries the canonical complex
constants to the actual complex coefficients of the projective surface. -/
theorem overlapSectionMap_complex (r θ : ℂ) (V : (projectiveSurface r θ).Opens)
    (hV : V ≤ overlapPatch r θ) (c : ℂ) :
    overlapSectionMap r θ V hV (algebraMap ℂ (FirstOverlap r θ) c) =
      coefficientOn (projectiveSurface r θ).sheaf (schemeCoefficient (projectiveToComplex r θ)) V c := by
  rw [IsScalarTower.algebraMap_apply ℂ (SurfaceChartRing (firstEquations r θ)) (FirstOverlap r θ),
    overlapSectionMap_first]
  exact chartSection_complex (firstAffineChart r θ) (projectiveToComplex r θ)
    (firstAffineChart_overComplex r θ) _ c

/-- The ordinary Kähler lift along the actual overlap-section map. -/
def overlapDifferentialSection (r θ : ℂ) (V : (projectiveSurface r θ).Opens)
    (hV : V ≤ overlapPatch r θ) :
    KaehlerDifferential ℂ (FirstOverlap r θ) →+
      (differentialSheaf (projectiveSurface r θ).sheaf
        (schemeCoefficient (projectiveToComplex r θ))).val.obj (op V) :=
  sectionLift (projectiveSurface r θ).sheaf (schemeCoefficient (projectiveToComplex r θ))
    (differentialSheaf (projectiveSurface r θ).sheaf (schemeCoefficient (projectiveToComplex r θ)))
    (universalDifferential (projectiveSurface r θ).sheaf (schemeCoefficient (projectiveToComplex r θ)))
    V (overlapSectionMap r θ V hV) (overlapSectionMap_complex r θ V hV)

theorem overlapDifferentialSection_D (r θ : ℂ) (V : (projectiveSurface r θ).Opens)
    (hV : V ≤ overlapPatch r θ) (a : FirstOverlap r θ) :
    overlapDifferentialSection r θ V hV (KaehlerDifferential.D ℂ (FirstOverlap r θ) a) =
      (universalDifferential (projectiveSurface r θ).sheaf
        (schemeCoefficient (projectiveToComplex r θ))).d (X := op V)
          (overlapSectionMap r θ V hV a) :=
  sectionLift_D (projectiveSurface r θ).sheaf (schemeCoefficient (projectiveToComplex r θ))
    (differentialSheaf (projectiveSurface r θ).sheaf (schemeCoefficient (projectiveToComplex r θ)))
    (universalDifferential (projectiveSurface r θ).sheaf (schemeCoefficient (projectiveToComplex r θ)))
    V (overlapSectionMap r θ V hV) (overlapSectionMap_complex r θ V hV) a

theorem overlapDifferentialSection_smul (r θ : ℂ) (V : (projectiveSurface r θ).Opens)
    (hV : V ≤ overlapPatch r θ) (a : FirstOverlap r θ)
    (ω : KaehlerDifferential ℂ (FirstOverlap r θ)) :
    overlapDifferentialSection r θ V hV (a • ω) =
      overlapSectionMap r θ V hV a • overlapDifferentialSection r θ V hV ω :=
  sectionLift_smul (projectiveSurface r θ).sheaf (schemeCoefficient (projectiveToComplex r θ))
    (differentialSheaf (projectiveSurface r θ).sheaf (schemeCoefficient (projectiveToComplex r θ)))
    (universalDifferential (projectiveSurface r θ).sheaf (schemeCoefficient (projectiveToComplex r θ)))
    V (overlapSectionMap r θ V hV) (overlapSectionMap_complex r θ V hV) a ω

#print axioms overlapSectionMap_complex
#print axioms overlapDifferentialSection_D
#print axioms overlapDifferentialSection_smul

end CycleQ2GeometricSurfaceOverlapDifferentials
end

end ResidueCorePart2

section ResidueCorePart3

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2GeometricSurfaceDeterminantBilinearity

open Module

variable {R : Type*} [CommRing R]

private theorem succAbove_four (i : Fin 4) (j : Fin 3) :
    i.succAbove j = (!![(1 : Fin 4), 2, 3; 0, 2, 3; 0, 1, 3; 0, 1, 2] i j) := by
  fin_cases i <;> fin_cases j <;> rfl

/-- Determinant bilinearity in the two cotangent-vector rows, with the
original two equation rows kept fixed. -/
theorem determinant_last_rows (u v x y : Fin 4 → R) :
    Matrix.det ![u,v,x,y] =
      ∑ i : Fin 4, ∑ j : Fin 4,
        x i * y j * Matrix.det ![u,v,Pi.single i 1,Pi.single j 1] := by
  simp [Matrix.det_succ_row_zero, Matrix.submatrix_apply, Fin.sum_univ_succ,
    succAbove_four, Pi.single_apply]
  ring

/-- The corresponding rank-two determinant distributes over the same
ambient coefficient vectors. -/
theorem rank_two_coordinate_sums (J : R) (a b x y : Fin 4 → R) :
    J * ((∑ i : Fin 4, x i * a i) * (∑ j : Fin 4, y j * b j) -
      (∑ i : Fin 4, x i * b i) * (∑ j : Fin 4, y j * a j)) =
      ∑ i : Fin 4, ∑ j : Fin 4,
        x i * y j * (J * (a i * b j - b i * a j)) := by
  simp only [Fin.sum_univ_succ]
  simp
  ring

#print axioms determinant_last_rows
#print axioms rank_two_coordinate_sums

end CycleQ2GeometricSurfaceDeterminantBilinearity
end

end ResidueCorePart3

section ResidueCorePart4

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2GeometricSurfaceCoordinateDeterminants

open MvPolynomial
open CycleQ2GeometricSurfaceAdjunction

variable {R : Type*} [CommRing R]

def polynomialGradientMap (φ : SurfacePoly →+* R) (p : SurfacePoly) (j : Fin 4) : R :=
  φ (pderiv (_root_.finSuccEquiv 3 j) p)

theorem coordinateGradient (φ : SurfacePoly →+* R) (i : Fin 4) :
    polynomialGradientMap φ (X (_root_.finSuccEquiv 3 i)) = Pi.single i 1 := by
  funext j
  by_cases hij : i = j
  · subst j
    simp [polynomialGradientMap,pderiv_X,Pi.single_apply]
  · have hidx : _root_.finSuccEquiv 3 i ≠ _root_.finSuccEquiv 3 j :=
      fun h => hij ((_root_.finSuccEquiv 3).injective h)
    simp [polynomialGradientMap,pderiv_X,Pi.single_apply,hij,hidx]

/-- After any actual ring map from the surface ring, the two coordinate
differential rows remain the corresponding standard basis rows. -/
theorem map_augmentedJacobian_coordinate_pair (v : Fin 2 → SurfacePoly)
    (φ : SurfaceChartRing v →+* R) (i j : Fin 4) :
    φ (augmentedJacobian v (X (_root_.finSuccEquiv 3 i)) (X (_root_.finSuccEquiv 3 j))) =
      Matrix.det ![
        (fun k => φ (Ideal.Quotient.mk (surfaceChartIdeal v)
          (pderiv (_root_.finSuccEquiv 3 k) (v 0)))),
        (fun k => φ (Ideal.Quotient.mk (surfaceChartIdeal v)
          (pderiv (_root_.finSuccEquiv 3 k) (v 1)))),
        Pi.single i 1,Pi.single j 1] := by
  rw [augmentedJacobian_polynomial,RingHom.map_det]
  congr 1
  ext k l
  fin_cases k <;> simp only [augmentedPolynomialRows,Matrix.cons_val_zero',Matrix.cons_val_succ']
  · rfl
  · rfl
  · exact congrFun (coordinateGradient (φ.comp (Ideal.Quotient.mk (surfaceChartIdeal v))) i) l
  · exact congrFun (coordinateGradient (φ.comp (Ideal.Quotient.mk (surfaceChartIdeal v))) j) l

#print axioms map_augmentedJacobian_coordinate_pair

end CycleQ2GeometricSurfaceCoordinateDeterminants
end

end ResidueCorePart4

end SurfaceResidueAssemblyPart01

section SurfaceResidueAssemblyPart02

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2GeometricSurfaceResidueSections

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry Module
open CycleQ2GeometricDifferentialSheaf CycleQ2GeometricAffineChartSections
open CycleQ2GeometricDifferentialChartTransport CycleQ2GeometricSheafKaehlerMap
open CycleQ2GeometricSurfaceExteriorSections CycleQ2GeometricSurfaceAdjunction
open CycleQ2GeometricSurfaceDeterminantNaturality
open CycleQ2GeometricSurfaceJacobianCharts CycleQ2GeometricPrincipalChartSections

variable {X : Scheme.{0}} {U : X.Opens}
  (f : X ⟶ Spec (CommRingCat.of ℂ))

section PrincipalPresentation

variable (v : Fin 2 → SurfacePoly)
  (eB : U.toScheme ≅ Spec (CommRingCat.of (SurfaceChartRing v)))
  (hB : eB.inv ≫ U.ι ≫ f =
    Spec.map (CommRingCat.ofHom (algebraMap ℂ (SurfaceChartRing v))))

/-- The genuine principal chart, with its literal adjunction-ring
codomain exposed before any differential-sheaf transport. -/
def jacobianPrincipalChart (n t : SurfacePoly) :
    (principalOpen eB (augmentedJacobian v n t)).toScheme ≅
      Spec (CommRingCat.of (AdjunctionPatch v n t)) :=
  principalChart eB (augmentedJacobian v n t)

include hB in
theorem jacobianPrincipalChart_overComplex (n t : SurfacePoly) :
    (jacobianPrincipalChart v eB n t).inv ≫
        (principalOpen eB (augmentedJacobian v n t)).ι ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap ℂ (AdjunctionPatch v n t))) :=
  principalChart_overComplex eB (augmentedJacobian v n t) f hB

theorem jacobianPrincipalChart_section (n t : SurfacePoly)
    (V : Over (principalOpen eB (augmentedJacobian v n t))) (a : SurfaceChartRing v) :
    chartSection (X := X) (jacobianPrincipalChart v eB n t) V
        (algebraMap (SurfaceChartRing v) (AdjunctionPatch v n t) a) =
      chartSection (X := X) eB (Over.mk (V.hom ≫ homOfLE
        (principalOpen_le eB (augmentedJacobian v n t)))) a :=
  principal_chartSection (X := X) eB (augmentedJacobian v n t) V a

theorem jacobianPrincipalChart_section_open (n t : SurfacePoly)
    (V : X.Opens) (hV : V ≤ principalOpen eB (augmentedJacobian v n t))
    (a : SurfaceChartRing v) :
    chartSection (X := X) (jacobianPrincipalChart v eB n t) (Over.mk (homOfLE hV))
        (algebraMap (SurfaceChartRing v) (AdjunctionPatch v n t) a) =
      chartSection (X := X) eB (Over.mk (homOfLE
        (hV.trans (principalOpen_le eB (augmentedJacobian v n t))))) a := by
  simpa only [Over.mk_hom,homOfLE_comp] using
    (jacobianPrincipalChart_section v eB n t (Over.mk (homOfLE hV)) a)

/-- The base-ring map of a genuine principal chart, with the common
section ring explicitly exposed before comparing two charts. -/
def jacobianPrincipalSectionMap (n t : SurfacePoly) (V : X.Opens)
    (hV : V ≤ principalOpen eB (augmentedJacobian v n t)) :
    SurfaceChartRing v →+* Γ(X,V) :=
  (chartSection (X := X) (U := principalOpen eB (augmentedJacobian v n t))
    (A := AdjunctionPatch v n t) (jacobianPrincipalChart v eB n t)
    (Over.mk (homOfLE hV))).comp
    (algebraMap (SurfaceChartRing v) (AdjunctionPatch v n t))

theorem jacobianPrincipalSectionMap_eq (n t : SurfacePoly) (V : X.Opens)
    (hV : V ≤ principalOpen eB (augmentedJacobian v n t)) :
    jacobianPrincipalSectionMap v eB n t V hV =
      chartSection (X := X) (U := U) (A := SurfaceChartRing v) eB
        (Over.mk (homOfLE (hV.trans (principalOpen_le eB (augmentedJacobian v n t))))) := by
  apply RingHom.ext
  intro a
  exact jacobianPrincipalChart_section_open v eB n t V hV a

theorem jacobianPrincipalSectionMaps_agree (n₁ t₁ n₂ t₂ : SurfacePoly)
    (V : X.Opens)
    (hV₁ : V ≤ principalOpen eB (augmentedJacobian v n₁ t₁))
    (hV₂ : V ≤ principalOpen eB (augmentedJacobian v n₂ t₂)) :
    jacobianPrincipalSectionMap v eB n₁ t₁ V hV₁ =
      jacobianPrincipalSectionMap v eB n₂ t₂ V hV₂ :=
  (jacobianPrincipalSectionMap_eq v eB n₁ t₁ V hV₁).trans
    (jacobianPrincipalSectionMap_eq v eB n₂ t₂ V hV₂).symm

def principalResidueSection (n t : SurfacePoly) (V : X.Opens)
    (hV : V ≤ principalOpen eB (augmentedJacobian v n t)) :
    ⋀[Γ(X,V)]^2 ((differentialSheaf X.sheaf (schemeCoefficient f)).val.obj (op V)) :=
  chartResidueSection_common f v n t (jacobianPrincipalChart v eB n t)
    (jacobianPrincipalChart_overComplex f v eB hB n t) (Over.mk (homOfLE hV))

/-- Residue sections agree on every intersection of actual Jacobian
principal charts of the same surface equation presentation. -/
theorem principal_residueSection_agreement (n₁ t₁ n₂ t₂ : SurfacePoly)
    (V : X.Opens)
    (hV₁ : V ≤ principalOpen eB (augmentedJacobian v n₁ t₁))
    (hV₂ : V ≤ principalOpen eB (augmentedJacobian v n₂ t₂)) :
    principalResidueSection f v eB hB n₁ t₁ V hV₁ =
      principalResidueSection f v eB hB n₂ t₂ V hV₂ := by
  apply residueSection_eq_of_base_sections (X := X) f v n₁ t₁ n₂ t₂
    (jacobianPrincipalChart v eB n₁ t₁) (jacobianPrincipalChart v eB n₂ t₂)
    (jacobianPrincipalChart_overComplex f v eB hB n₁ t₁)
    (jacobianPrincipalChart_overComplex f v eB hB n₂ t₂) V hV₁ hV₂
  intro a
  exact DFunLike.congr_fun
    (jacobianPrincipalSectionMaps_agree v eB n₁ t₁ n₂ t₂ V hV₁ hV₂) a

end PrincipalPresentation

#print axioms principal_residueSection_agreement
end CycleQ2GeometricSurfaceResidueSections
end

end SurfaceResidueAssemblyPart02

section SurfaceResidueAssemblyPart03

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2GeometricSurfaceResidueSections

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry Module MvPolynomial
open CycleQ2GeometricDifferentialSheaf CycleQ2GeometricAffineChartSections
open CycleQ2GeometricDifferentialChartTransport CycleQ2GeometricFunctionalDifferentials
open CycleQ2GeometricSurfaceExteriorSections CycleQ2GeometricSurfaceAdjunction
open CycleQ2GeometricSurfaceDeterminantBilinearity CycleQ2GeometricSurfaceCoordinateDeterminants

private theorem linearMap_sum_coordinates {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] (L : M →ₗ[R] R) (x : Fin 4 → R) (m : Fin 4 → M) :
    L (∑ j : Fin 4, x j • m j) = ∑ j : Fin 4, x j * L (m j) := by
  simp only [map_sum,map_smul,smul_eq_mul]

private theorem coefficient_determinant {R : Type*} [CommRing R]
    (J : R) (a b u v x y : Fin 4 → R)
    (h : ∀ i j : Fin 4, J * (a i * b j - b i * a j) =
      Matrix.det ![u,v,Pi.single i 1,Pi.single j 1]) :
    J * ((∑ i : Fin 4, x i * a i) * (∑ j : Fin 4, y j * b j) -
      (∑ i : Fin 4, x i * b i) * (∑ j : Fin 4, y j * a j)) = Matrix.det ![u,v,x,y] := by
  calc
    _ = ∑ i : Fin 4, ∑ j : Fin 4,
        x i * y j * (J * (a i * b j - b i * a j)) := rank_two_coordinate_sums J a b x y
    _ = ∑ i : Fin 4, ∑ j : Fin 4,
        x i * y j * Matrix.det ![u,v,Pi.single i 1,Pi.single j 1] := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      exact congrArg (fun z => x i * y j * z) (h i j)
    _ = _ := (determinant_last_rows u v x y).symm

variable {X : Scheme.{0}} {U : X.Opens}
  (f : X ⟶ Spec (CommRingCat.of ℂ))
  (v : Fin 2 → SurfacePoly) (n t : SurfacePoly)
  (eR : U.toScheme ≅ Spec (CommRingCat.of (AdjunctionPatch v n t)))
  (hR : eR.inv ≫ U.ι ≫ f =
    Spec.map (CommRingCat.ofHom (algebraMap ℂ (AdjunctionPatch v n t))))

def chartResidueBasis_common (V : Over U) :
    Basis (Fin 2) Γ(X,V.left)
      ((differentialSheaf X.sheaf (schemeCoefficient f)).val.obj (op V.left)) :=
  chartSectionBasis eR f hR (localSurfaceKaehlerBasis v n t) V

def chartSurfaceSectionMap (V : Over U) : SurfaceChartRing v →+* Γ(X,V.left) :=
  (chartSection eR V).comp (algebraMap (SurfaceChartRing v) (AdjunctionPatch v n t))

def chartCoordinateDifferential (V : Over U) (j : Fin 4) :
    (differentialSheaf X.sheaf (schemeCoefficient f)).val.obj (op V.left) :=
  polynomialDifferentialSection_common f v n t eR V (MvPolynomial.X (_root_.finSuccEquiv 3 j))

def chartEquationGradient (V : Over U) (i : Fin 2) (j : Fin 4) : Γ(X,V.left) :=
  chartSurfaceSectionMap v n t eR V
    (Ideal.Quotient.mk (surfaceChartIdeal v) (pderiv (_root_.finSuccEquiv 3 j) (v i)))

def chartAmbientDifferential (V : Over U) (x : Fin 4 → Γ(X,V.left)) :
    (differentialSheaf X.sheaf (schemeCoefficient f)).val.obj (op V.left) :=
  ∑ j : Fin 4, x j • chartCoordinateDifferential f v n t eR V j

theorem chartResidueCoordinate_common_pair (V : Over U)
    (ω η : (differentialSheaf X.sheaf (schemeCoefficient f)).val.obj (op V.left)) :
    chartResidueCoordinate_common f v n t eR hR V
      (exteriorPower.ιMulti Γ(X,V.left) 2 ![ω,η]) =
      chartSurfaceSectionMap v n t eR V (augmentedJacobian v n t) *
        ((chartResidueBasis_common f v n t eR hR V).repr ω 0 *
          (chartResidueBasis_common f v n t eR hR V).repr η 1 -
        (chartResidueBasis_common f v n t eR hR V).repr ω 1 *
          (chartResidueBasis_common f v n t eR hR V).repr η 0) := by
  exact (chartResidueCoordinate_apply f v n t eR hR V _).trans
    (congrArg (fun z => chartSurfaceSectionMap v n t eR V (augmentedJacobian v n t) * z)
      (determinantEquiv_pair (chartResidueBasis_common f v n t eR hR V) ω η))

/-- The actual residue functional evaluates every pair of ambient
coefficient vectors by the actual two equation rows and those vectors. -/
theorem chartResidueCoordinate_ambient_pair (V : Over U) (x y : Fin 4 → Γ(X,V.left)) :
    chartResidueCoordinate_common f v n t eR hR V
      (exteriorPower.ιMulti Γ(X,V.left) 2
        ![chartAmbientDifferential f v n t eR V x,
          chartAmbientDifferential f v n t eR V y]) =
      Matrix.det ![chartEquationGradient v n t eR V 0,
        chartEquationGradient v n t eR V 1,x,y] := by
  let b := chartResidueBasis_common f v n t eR hR V
  let J := chartSurfaceSectionMap v n t eR V (augmentedJacobian v n t)
  let a : Fin 4 → Γ(X,V.left) := fun j => b.repr (chartCoordinateDifferential f v n t eR V j) 0
  let c : Fin 4 → Γ(X,V.left) := fun j => b.repr (chartCoordinateDifferential f v n t eR V j) 1
  have hpair (i j : Fin 4) : J * (a i * c j - c i * a j) =
      Matrix.det ![chartEquationGradient v n t eR V 0,
        chartEquationGradient v n t eR V 1,Pi.single i 1,Pi.single j 1] := by
    exact (chartResidueCoordinate_common_pair f v n t eR hR V
      (chartCoordinateDifferential f v n t eR V i)
      (chartCoordinateDifferential f v n t eR V j)).symm.trans
        ((chartResidueCoordinate_common_polynomial_pair f v n t eR hR V
          (MvPolynomial.X (_root_.finSuccEquiv 3 i)) (MvPolynomial.X (_root_.finSuccEquiv 3 j))).trans
            (map_augmentedJacobian_coordinate_pair v (chartSurfaceSectionMap v n t eR V) i j))
  have hc (z : Fin 4 → Γ(X,V.left)) (k : Fin 2) :
      b.repr (chartAmbientDifferential f v n t eR V z) k =
        ∑ j : Fin 4, z j * b.repr (chartCoordinateDifferential f v n t eR V j) k :=
    linearMap_sum_coordinates (b.coord k) z (chartCoordinateDifferential f v n t eR V)
  rw [chartResidueCoordinate_common_pair]
  change J * (b.repr (chartAmbientDifferential f v n t eR V x) 0 *
      b.repr (chartAmbientDifferential f v n t eR V y) 1 -
    b.repr (chartAmbientDifferential f v n t eR V x) 1 *
      b.repr (chartAmbientDifferential f v n t eR V y) 0) = _
  rw [hc,hc,hc,hc]
  exact coefficient_determinant J a c (chartEquationGradient v n t eR V 0)
    (chartEquationGradient v n t eR V 1) x y hpair

#print axioms chartResidueCoordinate_ambient_pair

end CycleQ2GeometricSurfaceResidueSections
end

end SurfaceResidueAssemblyPart03

section SurfaceResidueAssemblyPart04

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2GeometricSurfaceChangedSections

open CategoryTheory Opposite AlgebraicGeometry Module MvPolynomial
open CycleQ2GeometricAffineChartSections CycleQ2GeometricDifferentialSheaf
open CycleQ2GeometricSurfaceAdjunction CycleQ2GeometricSurfaceDehomogenizedCharts
open CycleQ2GeometricSurfaceCoefficients CycleQ2CartierProjectiveCover
open CycleQ2GeometricSurfaceOverlap CycleQ2GeometricSurfaceJacobianCharts
open CycleQ2GeometricSurfaceResidueSections CycleQ2GeometricSurfaceOverlapDifferentials
open CycleQ2GeometricSurfaceAmbientDifferential CycleQ2GeometricSurfaceResidueTransition
open CycleQ2GeometricAffineCurveCharts

theorem overlapSectionMap_first_normal (r θ : ℂ) (i : Fin 2) (j : Fin 3)
    (V : (projectiveSurface r θ).Opens) (hV : V ≤ overlapPatch r θ)
    (hN : V ≤ firstNormalOpen r θ i j) (a : SurfaceChartRing (firstEquations r θ)) :
    overlapSectionMap r θ V hV
        (algebraMap (SurfaceChartRing (firstEquations r θ)) (FirstOverlap r θ) a) =
      chartSection (X := projectiveSurface r θ) (firstNormalChart r θ i j) (Over.mk (homOfLE hN))
        (algebraMap (SurfaceChartRing (firstEquations r θ))
          (Localization.Away (firstJacobian r θ i j)) a) := by
  calc
    _ = chartSection (X := projectiveSurface r θ) (firstAffineChart r θ)
        (Over.mk (homOfLE (hV.trans (overlap_le_first r θ)))) a :=
      overlapSectionMap_first r θ V hV a
    _ = _ := by
      symm
      simpa only [Over.mk_hom,homOfLE_comp] using
        (firstNormal_chartSection r θ i j (Over.mk (homOfLE hN)) a)

theorem overlapSectionMap_second_normal (r θ : ℂ) (i : Fin 2) (j : Fin 3)
    (V : (projectiveSurface r θ).Opens) (hV : V ≤ overlapPatch r θ)
    (hN : V ≤ secondNormalOpen r θ i j) (a : SurfaceChartRing (secondEquations r θ)) :
    overlapSectionMap r θ V hV
        (overlapEquiv r θ (algebraMap (SurfaceChartRing (secondEquations r θ)) (SecondOverlap r θ) a)) =
      chartSection (X := projectiveSurface r θ) (secondNormalChart r θ i j) (Over.mk (homOfLE hN))
        (algebraMap (SurfaceChartRing (secondEquations r θ))
          (Localization.Away (secondJacobian r θ i j)) a) := by
  calc
    _ = chartSection (X := projectiveSurface r θ) (secondAffineChart r θ)
        (Over.mk (homOfLE (hV.trans (overlap_le_second r θ)))) a :=
      overlapSectionMap_second r θ V hV a
    _ = _ := by
      symm
      simpa only [Over.mk_hom,homOfLE_comp] using
        (secondNormal_chartSection r θ i j (Over.mk (homOfLE hN)) a)

theorem polynomialMap_eq_tower (v : Fin 2 → SurfacePoly) (p : SurfacePoly) :
    polynomialMap v p = algebraMap (SurfaceChartRing v) (CoordinateOverlap v)
      (algebraMap SurfacePoly (SurfaceChartRing v) p) := rfl

theorem overlapSectionMap_first_polynomial (r θ : ℂ) (i : Fin 2) (j : Fin 3)
    (V : (projectiveSurface r θ).Opens) (hV : V ≤ overlapPatch r θ)
    (hN : V ≤ firstNormalOpen r θ i j) (p : SurfacePoly) :
    overlapSectionMap r θ V hV (polynomialMap (firstEquations r θ) p) =
      chartSection (X := projectiveSurface r θ) (firstNormalChart r θ i j) (Over.mk (homOfLE hN))
        (algebraMap SurfacePoly (Localization.Away (firstJacobian r θ i j)) p) := by
  rw [polynomialMap_eq_tower,overlapSectionMap_first_normal r θ i j V hV hN]
  exact congrArg (chartSection (X := projectiveSurface r θ) (firstNormalChart r θ i j)
    (Over.mk (homOfLE hN)))
    (IsScalarTower.algebraMap_apply SurfacePoly (SurfaceChartRing (firstEquations r θ))
      (Localization.Away (firstJacobian r θ i j)) p).symm

theorem overlapSectionMap_second_polynomial (r θ : ℂ) (i : Fin 2) (j : Fin 3)
    (V : (projectiveSurface r θ).Opens) (hV : V ≤ overlapPatch r θ)
    (hN : V ≤ secondNormalOpen r θ i j) (p : SurfacePoly) :
    overlapSectionMap r θ V hV (overlapEquiv r θ (polynomialMap (secondEquations r θ) p)) =
      chartSection (X := projectiveSurface r θ) (secondNormalChart r θ i j) (Over.mk (homOfLE hN))
        (algebraMap SurfacePoly (Localization.Away (secondJacobian r θ i j)) p) := by
  rw [polynomialMap_eq_tower,overlapSectionMap_second_normal r θ i j V hV hN]
  exact congrArg (chartSection (X := projectiveSurface r θ) (secondNormalChart r θ i j)
    (Over.mk (homOfLE hN)))
    (IsScalarTower.algebraMap_apply SurfacePoly (SurfaceChartRing (secondEquations r θ))
      (Localization.Away (secondJacobian r θ i j)) p).symm

def firstPolynomialDifferential (r θ : ℂ) (i : Fin 2) (j : Fin 3)
    (V : (projectiveSurface r θ).Opens) (hN : V ≤ firstNormalOpen r θ i j) (p : SurfacePoly) :
    (differentialSheaf (projectiveSurface r θ).sheaf
      (schemeCoefficient (CycleQ2GeometricSurfaceCoefficients.projectiveToComplex r θ))).val.obj (op V) :=
  polynomialDifferentialSection_common (CycleQ2GeometricSurfaceCoefficients.projectiveToComplex r θ) (firstEquations r θ)
    (normalPolynomial (firstQuadric r) i) (includeCurve (MvPolynomial.X j))
    (firstNormalChart r θ i j) (Over.mk (homOfLE hN)) p

def secondPolynomialDifferential (r θ : ℂ) (i : Fin 2) (j : Fin 3)
    (V : (projectiveSurface r θ).Opens) (hN : V ≤ secondNormalOpen r θ i j) (p : SurfacePoly) :
    (differentialSheaf (projectiveSurface r θ).sheaf
      (schemeCoefficient (CycleQ2GeometricSurfaceCoefficients.projectiveToComplex r θ))).val.obj (op V) :=
  polynomialDifferentialSection_common (CycleQ2GeometricSurfaceCoefficients.projectiveToComplex r θ) (secondEquations r θ)
    (normalPolynomial (secondQuadric r) i) (includeCurve (MvPolynomial.X j))
    (secondNormalChart r θ i j) (Over.mk (homOfLE hN)) p

theorem overlapDifferentialSection_first_normal (r θ : ℂ) (i : Fin 2) (j : Fin 3)
    (V : (projectiveSurface r θ).Opens) (hV : V ≤ overlapPatch r θ)
    (hN : V ≤ firstNormalOpen r θ i j) (p : SurfacePoly) :
    overlapDifferentialSection r θ V hV
        (KaehlerDifferential.D ℂ (FirstOverlap r θ) (polynomialMap (firstEquations r θ) p)) =
      firstPolynomialDifferential r θ i j V hN p := by
  rw [overlapDifferentialSection_D]
  exact congrArg ((universalDifferential (projectiveSurface r θ).sheaf
    (schemeCoefficient (CycleQ2GeometricSurfaceCoefficients.projectiveToComplex r θ))).d (X := op V))
    (overlapSectionMap_first_polynomial r θ i j V hV hN p)

theorem overlapDifferentialSection_second_normal (r θ : ℂ) (i : Fin 2) (j : Fin 3)
    (V : (projectiveSurface r θ).Opens) (hV : V ≤ overlapPatch r θ)
    (hN : V ≤ secondNormalOpen r θ i j) (p : SurfacePoly) :
    overlapDifferentialSection r θ V hV
        (KaehlerDifferential.D ℂ (FirstOverlap r θ)
          (overlapEquiv r θ (polynomialMap (secondEquations r θ) p))) =
      secondPolynomialDifferential r θ i j V hN p := by
  rw [overlapDifferentialSection_D]
  exact congrArg ((universalDifferential (projectiveSurface r θ).sheaf
    (schemeCoefficient (CycleQ2GeometricSurfaceCoefficients.projectiveToComplex r θ))).d (X := op V))
    (overlapSectionMap_second_polynomial r θ i j V hV hN p)

/-- The literal weighted coordinate change gives the coefficients of the
actual second-chart polynomial differential on every common subopen. -/
theorem secondPolynomialDifferential_expansion (r θ : ℂ)
    (i₁ i₂ : Fin 2) (j₁ j₂ : Fin 3)
    (V : (projectiveSurface r θ).Opens) (hV : V ≤ overlapPatch r θ)
    (h₁ : V ≤ firstNormalOpen r θ i₁ j₁) (h₂ : V ≤ secondNormalOpen r θ i₂ j₂)
    (p : SurfacePoly) :
    secondPolynomialDifferential r θ i₂ j₂ V h₂ p =
      ∑ k : Fin 4, overlapSectionMap r θ V hV (pulledGradient r θ p k) •
        firstPolynomialDifferential r θ i₁ j₁ V h₁ (MvPolynomial.X (_root_.finSuccEquiv 3 k)) := by
  have h := congrArg (overlapDifferentialSection r θ V hV)
    (surface_D_second_polynomial r θ p)
  rw [overlapDifferentialSection_second_normal r θ i₂ j₂ V hV h₂ p,map_sum] at h
  simpa only [overlapDifferentialSection_smul,coordinate,
    overlapDifferentialSection_first_normal r θ i₁ j₁ V hV h₁] using h

#print axioms overlapSectionMap_first_normal
#print axioms secondPolynomialDifferential_expansion

end CycleQ2GeometricSurfaceChangedSections
end

end SurfaceResidueAssemblyPart04

section SurfaceResidueAssemblyPart05

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2GeometricSurfaceResidueCrossCoordinates

open CategoryTheory Opposite AlgebraicGeometry Module MvPolynomial
open CycleQ2GeometricAffineChartSections
open CycleQ2GeometricDifferentialSheaf (differentialSheaf)
open CycleQ2GeometricSurfaceAdjunction CycleQ2GeometricSurfaceDehomogenizedCharts
open CycleQ2GeometricSurfaceCoefficients CycleQ2CartierProjectiveCover
open CycleQ2GeometricSurfaceOverlap CycleQ2GeometricSurfaceJacobianCharts
open CycleQ2GeometricSurfaceResidueSections CycleQ2GeometricSurfaceChangedSections
open CycleQ2GeometricSurfaceResidueTransition CycleQ2GeometricAffineCurveCharts

/-- The literal second surface-ring map with its common section-ring
codomain exposed before scalar multiplication. -/
def secondBaseSectionMap (r θ : ℂ) (i : Fin 2) (j : Fin 3)
    (V : (projectiveSurface r θ).Opens) (h : V ≤ secondNormalOpen r θ i j) :
    SurfaceChartRing (secondEquations r θ) →+* Γ(projectiveSurface r θ,V) :=
  (chartSection (X := projectiveSurface r θ)
    (A := Localization.Away (secondJacobian r θ i j))
    (secondNormalChart r θ i j) (Over.mk (homOfLE h))).comp
    (algebraMap (SurfaceChartRing (secondEquations r θ))
      (Localization.Away (secondJacobian r θ i j)))

def firstResidueCoordinate (r θ : ℂ) (i : Fin 2) (j : Fin 3)
    (V : (projectiveSurface r θ).Opens) (h : V ≤ firstNormalOpen r θ i j) :
    (⋀[Γ(projectiveSurface r θ,V)]^2
      ((differentialSheaf (projectiveSurface r θ).sheaf
        (schemeCoefficient (projectiveToComplex r θ))).val.obj (op V))) ≃ₗ[
      Γ(projectiveSurface r θ,V)] Γ(projectiveSurface r θ,V) :=
  chartResidueCoordinate_common (X := projectiveSurface r θ)
    (projectiveToComplex r θ) (firstEquations r θ)
    (normalPolynomial (firstQuadric r) i) (includeCurve (MvPolynomial.X j))
    (firstNormalChart r θ i j) (firstNormalChart_overComplex r θ i j)
    (Over.mk (homOfLE h))

def firstResidueSection (r θ : ℂ) (i : Fin 2) (j : Fin 3)
    (V : (projectiveSurface r θ).Opens) (h : V ≤ firstNormalOpen r θ i j) :
    ⋀[Γ(projectiveSurface r θ,V)]^2
      ((differentialSheaf (projectiveSurface r θ).sheaf
        (schemeCoefficient (projectiveToComplex r θ))).val.obj (op V)) :=
  chartResidueSection_common (X := projectiveSurface r θ)
    (projectiveToComplex r θ) (firstEquations r θ)
    (normalPolynomial (firstQuadric r) i) (includeCurve (MvPolynomial.X j))
    (firstNormalChart r θ i j) (firstNormalChart_overComplex r θ i j)
    (Over.mk (homOfLE h))

def secondResidueSection (r θ : ℂ) (i : Fin 2) (j : Fin 3)
    (V : (projectiveSurface r θ).Opens) (h : V ≤ secondNormalOpen r θ i j) :
    ⋀[Γ(projectiveSurface r θ,V)]^2
      ((differentialSheaf (projectiveSurface r θ).sheaf
        (schemeCoefficient (projectiveToComplex r θ))).val.obj (op V)) :=
  chartResidueSection_common (X := projectiveSurface r θ)
    (projectiveToComplex r θ) (secondEquations r θ)
    (normalPolynomial (secondQuadric r) i) (includeCurve (MvPolynomial.X j))
    (secondNormalChart r θ i j) (secondNormalChart_overComplex r θ i j)
    (Over.mk (homOfLE h))

theorem firstResidueCoordinate_normalization (r θ : ℂ) (i : Fin 2) (j : Fin 3)
    (V : (projectiveSurface r θ).Opens) (h : V ≤ firstNormalOpen r θ i j) :
    firstResidueCoordinate r θ i j V h (firstResidueSection r θ i j V h) = 1 :=
  chartResidueSection_common_normalization (projectiveToComplex r θ) (firstEquations r θ)
    (normalPolynomial (firstQuadric r) i) (includeCurve (MvPolynomial.X j))
    (firstNormalChart r θ i j) (firstNormalChart_overComplex r θ i j)
    (Over.mk (homOfLE h))

/-- The actual first-chart residue coordinate evaluates the actual
second-chart polynomial wedge by the literal signed weighted determinant. -/
theorem firstResidueCoordinate_second_pair (r θ : ℂ)
    (i₁ i₂ : Fin 2) (j₁ j₂ : Fin 3)
    (V : (projectiveSurface r θ).Opens) (hV : V ≤ overlapPatch r θ)
    (h₁ : V ≤ firstNormalOpen r θ i₁ j₁) (h₂ : V ≤ secondNormalOpen r θ i₂ j₂)
    (p q : SurfacePoly) :
    firstResidueCoordinate r θ i₁ j₁ V h₁
      (exteriorPower.ιMulti Γ(projectiveSurface r θ,V) 2
        ![secondPolynomialDifferential r θ i₂ j₂ V h₂ p,
          secondPolynomialDifferential r θ i₂ j₂ V h₂ q]) =
      overlapSectionMap r θ V hV (-(coordinate (firstEquations r θ) (some 1)^3)) *
        secondBaseSectionMap r θ i₂ j₂ V h₂
          (augmentedJacobian (secondEquations r θ) p q) := by
  have hD (a : SurfacePoly) : secondPolynomialDifferential r θ i₂ j₂ V h₂ a =
      chartAmbientDifferential (projectiveToComplex r θ) (firstEquations r θ)
        (normalPolynomial (firstQuadric r) i₁) (includeCurve (MvPolynomial.X j₁))
        (firstNormalChart r θ i₁ j₁) (Over.mk (homOfLE h₁))
        (fun k => overlapSectionMap r θ V hV (pulledGradient r θ a k)) :=
    secondPolynomialDifferential_expansion r θ i₁ i₂ j₁ j₂ V hV h₁ h₂ a
  change chartResidueCoordinate_common (projectiveToComplex r θ) (firstEquations r θ)
    (normalPolynomial (firstQuadric r) i₁) (includeCurve (MvPolynomial.X j₁))
    (firstNormalChart r θ i₁ j₁) (firstNormalChart_overComplex r θ i₁ j₁)
    (Over.mk (homOfLE h₁)) _ = _
  rw [hD p,hD q]
  refine (chartResidueCoordinate_ambient_pair (X := projectiveSurface r θ)
    (U := firstNormalOpen r θ i₁ j₁)
    (projectiveToComplex r θ) (firstEquations r θ)
    (normalPolynomial (firstQuadric r) i₁) (includeCurve (MvPolynomial.X j₁))
    (firstNormalChart r θ i₁ j₁) (firstNormalChart_overComplex r θ i₁ j₁)
    (Over.mk (homOfLE h₁))
    (fun k => overlapSectionMap r θ V hV (pulledGradient r θ p k))
    (fun k => overlapSectionMap r θ V hV (pulledGradient r θ q k))).trans ?_
  calc
    _ = overlapSectionMap r θ V hV (mixedGradientMatrix r θ p q).det := by
      symm
      rw [RingHom.map_det]
      congr 1
      ext k l
      fin_cases k <;> simp only [mixedGradientMatrix,Matrix.cons_val_zero',Matrix.cons_val_succ']
      · exact overlapSectionMap_first_normal r θ i₁ j₁ V hV h₁ _
      · exact overlapSectionMap_first_normal r θ i₁ j₁ V hV h₁ _
      · rfl
      · rfl
    _ = _ := by
      rw [mixedJacobian_transition,map_mul,overlapSectionMap_second_normal r θ i₂ j₂ V hV h₂]
      rfl

#print axioms firstResidueCoordinate_second_pair

theorem secondJacobian_smul_residue (r θ : ℂ) (i : Fin 2) (j : Fin 3)
    (V : (projectiveSurface r θ).Opens) (h : V ≤ secondNormalOpen r θ i j) :
    secondBaseSectionMap r θ i j V h (secondJacobian r θ i j) •
      secondResidueSection r θ i j V h =
      exteriorPower.ιMulti Γ(projectiveSurface r θ,V) 2
        ![secondPolynomialDifferential r θ i j V h (normalPolynomial (secondQuadric r) i),
          secondPolynomialDifferential r θ i j V h (includeCurve (MvPolynomial.X j))] :=
  chartJacobian_smul_residue_common (projectiveToComplex r θ) (secondEquations r θ)
    (normalPolynomial (secondQuadric r) i) (includeCurve (MvPolynomial.X j))
    (secondNormalChart r θ i j) (secondNormalChart_overComplex r θ i j)
    (Over.mk (homOfLE h))

private theorem normalized_residue_transfer {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] (E : M ≃ₗ[R] R)
    (m₁ m₂ : M) (J T : R) (hnorm : E m₁ = 1) (hJ : IsUnit J)
    (hpair : E (J • m₂) = T * J) : m₂ = T • m₁ := by
  apply E.injective
  have h₁ : E (T • m₁) = T := by
    simp only [map_smul,hnorm,smul_eq_mul,mul_one]
  rw [h₁]
  apply hJ.mul_left_cancel
  calc
    J * E m₂ = E (J • m₂) := by rw [map_smul,smul_eq_mul]
    _ = T * J := hpair
    _ = J * T := mul_comm _ _

/-- The genuine local residue sections transform by the signed cubic
factor on every common subopen of the two actual projective coordinate charts. -/
theorem residueSection_transition (r θ : ℂ)
    (i₁ i₂ : Fin 2) (j₁ j₂ : Fin 3)
    (V : (projectiveSurface r θ).Opens) (hV : V ≤ overlapPatch r θ)
    (h₁ : V ≤ firstNormalOpen r θ i₁ j₁) (h₂ : V ≤ secondNormalOpen r θ i₂ j₂) :
    secondResidueSection r θ i₂ j₂ V h₂ =
      overlapSectionMap r θ V hV (-(coordinate (firstEquations r θ) (some 1)^3)) •
        firstResidueSection r θ i₁ j₁ V h₁ := by
  let J : Γ(projectiveSurface r θ,V) :=
    secondBaseSectionMap r θ i₂ j₂ V h₂ (secondJacobian r θ i₂ j₂)
  have hJ : IsUnit J :=
    (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (secondJacobian r θ i₂ j₂))
      (secondJacobian r θ i₂ j₂)).map
      (chartSection (X := projectiveSurface r θ) (secondNormalChart r θ i₂ j₂)
        (Over.mk (homOfLE h₂)))
  apply normalized_residue_transfer (firstResidueCoordinate r θ i₁ j₁ V h₁)
    (firstResidueSection r θ i₁ j₁ V h₁) (secondResidueSection r θ i₂ j₂ V h₂)
    J _ (firstResidueCoordinate_normalization r θ i₁ j₁ V h₁) hJ
  exact (congrArg (firstResidueCoordinate r θ i₁ j₁ V h₁)
    (secondJacobian_smul_residue r θ i₂ j₂ V h₂)).trans
      (firstResidueCoordinate_second_pair r θ i₁ i₂ j₁ j₂ V hV h₁ h₂
        (normalPolynomial (secondQuadric r) i₂) (includeCurve (MvPolynomial.X j₂)))

#print axioms residueSection_transition

end CycleQ2GeometricSurfaceResidueCrossCoordinates
end

end SurfaceResidueAssemblyPart05

section SurfaceResidueAssemblyPart06

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2GeometricSurfaceCubicResidues

open CategoryTheory Opposite AlgebraicGeometry Module MvPolynomial
open CycleQ2SeedTrace CycleQ2CartierProjectiveCover
open CycleQ2GeometricAffineChartSections CycleQ2GeometricSurfaceAdjunction
open CycleQ2GeometricDifferentialSheaf (differentialSheaf)
open CycleQ2GeometricSurfaceDehomogenizedCharts CycleQ2GeometricSurfaceCoefficients
open CycleQ2GeometricSurfaceOverlap CycleQ2GeometricSurfaceJacobianCharts
open CycleQ2GeometricSurfaceChangedSections CycleQ2GeometricSurfaceResidueTransition
open CycleQ2GeometricSurfaceResidueCrossCoordinates CycleQ2GeometricExteriorSheaf
open CycleQ2GeometricAffineCurveCharts

private theorem orientation_of_raw {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] (a b : M) (h : b = -a) :
    ((-1 : R)^1) • a = ((-1 : R)^2) • b := by
  rw [pow_one,neg_one_sq,one_smul,neg_one_smul]
  exact h.symm

/-- The fixed polynomial coefficient in the actual first coordinate chart. -/
def firstCoefficientSection (r θ : ℂ) (V : (projectiveSurface r θ).Opens)
    (h : V ≤ coordinatePatch r θ 1) (p : WeightedPoly) : Γ(projectiveSurface r θ,V) :=
  chartSection (X := projectiveSurface r θ) (firstAffineChart r θ) (Over.mk (homOfLE h))
    (algebraMap SurfacePoly (SurfaceChartRing (firstEquations r θ))
      (firstSurfaceDehomogenize p))

/-- The same fixed polynomial coefficient in the actual second coordinate chart. -/
def secondCoefficientSection (r θ : ℂ) (V : (projectiveSurface r θ).Opens)
    (h : V ≤ coordinatePatch r θ 2) (p : WeightedPoly) : Γ(projectiveSurface r θ,V) :=
  chartSection (X := projectiveSurface r θ) (secondAffineChart r θ) (Over.mk (homOfLE h))
    (algebraMap SurfacePoly (SurfaceChartRing (secondEquations r θ))
      (secondSurfaceDehomogenize p))

theorem overlap_firstCoefficient (r θ : ℂ) (V : (projectiveSurface r θ).Opens)
    (hV : V ≤ overlapPatch r θ) (h : V ≤ coordinatePatch r θ 1) (p : WeightedPoly) :
    overlapSectionMap r θ V hV (polynomialMap (firstEquations r θ) (firstSurfaceDehomogenize p)) =
      firstCoefficientSection r θ V h p := by
  rw [polynomialMap_eq_tower]
  exact overlapSectionMap_first r θ V hV _

theorem overlap_secondCoefficient (r θ : ℂ) (V : (projectiveSurface r θ).Opens)
    (hV : V ≤ overlapPatch r θ) (h : V ≤ coordinatePatch r θ 2) (p : WeightedPoly) :
    overlapSectionMap r θ V hV
        (overlapEquiv r θ (polynomialMap (secondEquations r θ) (secondSurfaceDehomogenize p))) =
      secondCoefficientSection r θ V h p := by
  rw [polynomialMap_eq_tower]
  exact overlapSectionMap_second r θ V hV _

def firstCubicResidueSection (r θ : ℂ) (i : Fin 2) (j : Fin 3)
    (V : (projectiveSurface r θ).Opens) (h : V ≤ firstNormalOpen r θ i j)
    (p : WeightedPoly) :
    ⋀[Γ(projectiveSurface r θ,V)]^2
      ((differentialSheaf (projectiveSurface r θ).sheaf
        (schemeCoefficient (projectiveToComplex r θ))).val.obj (op V)) :=
  firstCoefficientSection r θ V (h.trans (firstNormalOpen_le r θ i j)) p •
    firstResidueSection r θ i j V h

def secondCubicResidueSection (r θ : ℂ) (i : Fin 2) (j : Fin 3)
    (V : (projectiveSurface r θ).Opens) (h : V ≤ secondNormalOpen r θ i j)
    (p : WeightedPoly) :
    ⋀[Γ(projectiveSurface r θ,V)]^2
      ((differentialSheaf (projectiveSurface r θ).sheaf
        (schemeCoefficient (projectiveToComplex r θ))).val.obj (op V)) :=
  secondCoefficientSection r θ V (h.trans (secondNormalOpen_le r θ i j)) p •
    secondResidueSection r θ i j V h

theorem cubicCoefficient_transition (r θ : ℂ)
    (V : (projectiveSurface r θ).Opens) (hV : V ≤ overlapPatch r θ)
    (h₁ : V ≤ coordinatePatch r θ 1) (h₂ : V ≤ coordinatePatch r θ 2)
    (p : WeightedPoly) (hp : p.IsWeightedHomogeneous CycleQ2CartierSurfaceGrading.weight 3) :
    secondCoefficientSection r θ V h₂ p *
        overlapSectionMap r θ V hV (-(coordinate (firstEquations r θ) (some 1)^3)) =
      -firstCoefficientSection r θ V h₁ p := by
  calc
    _ = overlapSectionMap r θ V hV
        (overlapEquiv r θ (polynomialMap (secondEquations r θ) (secondSurfaceDehomogenize p)) *
          -(coordinate (firstEquations r θ) (some 1)^3)) := by
      rw [map_mul,overlap_secondCoefficient r θ V hV h₂ p]
    _ = overlapSectionMap r θ V hV
        (-polynomialMap (firstEquations r θ) (firstSurfaceDehomogenize p)) :=
      congrArg (overlapSectionMap r θ V hV) (rawCubic_transition_scalar r θ p hp)
    _ = _ := by rw [map_neg,overlap_firstCoefficient r θ V hV h₁ p]

/-- The actual fixed cubic cancels the residue weight, with the raw
coordinate orientation sign retained. -/
theorem rawCubicSection_transition (r θ : ℂ)
    (i₁ i₂ : Fin 2) (j₁ j₂ : Fin 3)
    (V : (projectiveSurface r θ).Opens) (hV : V ≤ overlapPatch r θ)
    (h₁ : V ≤ firstNormalOpen r θ i₁ j₁) (h₂ : V ≤ secondNormalOpen r θ i₂ j₂)
    (p : WeightedPoly) (hp : p.IsWeightedHomogeneous CycleQ2CartierSurfaceGrading.weight 3) :
    secondCubicResidueSection r θ i₂ j₂ V h₂ p =
      -firstCubicResidueSection r θ i₁ j₁ V h₁ p := by
  rw [secondCubicResidueSection,firstCubicResidueSection,
    residueSection_transition r θ i₁ i₂ j₁ j₂ V hV h₁ h₂,smul_smul,
    cubicCoefficient_transition r θ V hV _ _ p hp,neg_smul]

/-- With the actual projective coordinate orientation (-1)^i, the two
fixed-cubic local exterior sections agree. -/
theorem orientedCubicSection_agreement (r θ : ℂ)
    (i₁ i₂ : Fin 2) (j₁ j₂ : Fin 3)
    (V : (projectiveSurface r θ).Opens) (hV : V ≤ overlapPatch r θ)
    (h₁ : V ≤ firstNormalOpen r θ i₁ j₁) (h₂ : V ≤ secondNormalOpen r θ i₂ j₂)
    (p : WeightedPoly) (hp : p.IsWeightedHomogeneous CycleQ2CartierSurfaceGrading.weight 3) :
    ((-1 : Γ(projectiveSurface r θ,V))^1) • firstCubicResidueSection r θ i₁ j₁ V h₁ p =
      ((-1 : Γ(projectiveSurface r θ,V))^2) • secondCubicResidueSection r θ i₂ j₂ V h₂ p := by
  exact orientation_of_raw (R := Γ(projectiveSurface r θ,V)) _ _
    (rawCubicSection_transition r θ i₁ i₂ j₁ j₂ V hV h₁ h₂ p hp)

def firstCubicSheafSection (r θ : ℂ) (i : Fin 2) (j : Fin 3)
    (V : (projectiveSurface r θ).Opens) (h : V ≤ firstNormalOpen r θ i j)
    (p : WeightedPoly) :
    (exteriorSheaf (projectiveSurface r θ).sheaf
      (differentialSheaf (projectiveSurface r θ).sheaf
        (schemeCoefficient (projectiveToComplex r θ))).val 2).val.obj (op V) :=
  firstCoefficientSection r θ V (h.trans (firstNormalOpen_le r θ i j)) p •
    chartResidueSheafSection (projectiveToComplex r θ) (firstEquations r θ)
      (normalPolynomial (firstQuadric r) i) (includeCurve (MvPolynomial.X j))
      (firstNormalChart r θ i j) (firstNormalChart_overComplex r θ i j)
      (Over.mk (homOfLE h))

def secondCubicSheafSection (r θ : ℂ) (i : Fin 2) (j : Fin 3)
    (V : (projectiveSurface r θ).Opens) (h : V ≤ secondNormalOpen r θ i j)
    (p : WeightedPoly) :
    (exteriorSheaf (projectiveSurface r θ).sheaf
      (differentialSheaf (projectiveSurface r θ).sheaf
        (schemeCoefficient (projectiveToComplex r θ))).val 2).val.obj (op V) :=
  secondCoefficientSection r θ V (h.trans (secondNormalOpen_le r θ i j)) p •
    chartResidueSheafSection (projectiveToComplex r θ) (secondEquations r θ)
      (normalPolynomial (secondQuadric r) i) (includeCurve (MvPolynomial.X j))
      (secondNormalChart r θ i j) (secondNormalChart_overComplex r θ i j)
      (Over.mk (homOfLE h))

theorem firstCubicSheafSection_eq (r θ : ℂ) (i : Fin 2) (j : Fin 3)
    (V : (projectiveSurface r θ).Opens) (h : V ≤ firstNormalOpen r θ i j)
    (p : WeightedPoly) :
    firstCubicSheafSection r θ i j V h p =
      exteriorSection (projectiveSurface r θ).sheaf
        (differentialSheaf (projectiveSurface r θ).sheaf
          (schemeCoefficient (projectiveToComplex r θ))).val 2 V
          (firstCubicResidueSection r θ i j V h p) :=
  (map_smul (exteriorSection (projectiveSurface r θ).sheaf
    (differentialSheaf (projectiveSurface r θ).sheaf
      (schemeCoefficient (projectiveToComplex r θ))).val 2 V) _ _).symm

theorem secondCubicSheafSection_eq (r θ : ℂ) (i : Fin 2) (j : Fin 3)
    (V : (projectiveSurface r θ).Opens) (h : V ≤ secondNormalOpen r θ i j)
    (p : WeightedPoly) :
    secondCubicSheafSection r θ i j V h p =
      exteriorSection (projectiveSurface r θ).sheaf
        (differentialSheaf (projectiveSurface r θ).sheaf
          (schemeCoefficient (projectiveToComplex r θ))).val 2 V
          (secondCubicResidueSection r θ i j V h p) :=
  (map_smul (exteriorSection (projectiveSurface r θ).sheaf
    (differentialSheaf (projectiveSurface r θ).sheaf
      (schemeCoefficient (projectiveToComplex r θ))).val 2 V) _ _).symm

theorem rawCubicSheafSection_transition (r θ : ℂ)
    (i₁ i₂ : Fin 2) (j₁ j₂ : Fin 3)
    (V : (projectiveSurface r θ).Opens) (hV : V ≤ overlapPatch r θ)
    (h₁ : V ≤ firstNormalOpen r θ i₁ j₁) (h₂ : V ≤ secondNormalOpen r θ i₂ j₂)
    (p : WeightedPoly) (hp : p.IsWeightedHomogeneous CycleQ2CartierSurfaceGrading.weight 3) :
    secondCubicSheafSection r θ i₂ j₂ V h₂ p =
      -firstCubicSheafSection r θ i₁ j₁ V h₁ p := by
  let E := exteriorSection (projectiveSurface r θ).sheaf
    (differentialSheaf (projectiveSurface r θ).sheaf
      (schemeCoefficient (projectiveToComplex r θ))).val 2 V
  exact (secondCubicSheafSection_eq r θ i₂ j₂ V h₂ p).trans
    ((congrArg E (rawCubicSection_transition r θ i₁ i₂ j₁ j₂ V hV h₁ h₂ p hp)).trans
      ((map_neg E (firstCubicResidueSection r θ i₁ j₁ V h₁ p)).trans
        (congrArg Neg.neg (firstCubicSheafSection_eq r θ i₁ j₁ V h₁ p).symm)))

/-- The signed fixed-cubic sections agree in the genuine exterior-square
sheaf of the actual projective surface differential sheaf. -/
theorem orientedCubicSheafSection_agreement (r θ : ℂ)
    (i₁ i₂ : Fin 2) (j₁ j₂ : Fin 3)
    (V : (projectiveSurface r θ).Opens) (hV : V ≤ overlapPatch r θ)
    (h₁ : V ≤ firstNormalOpen r θ i₁ j₁) (h₂ : V ≤ secondNormalOpen r θ i₂ j₂)
    (p : WeightedPoly) (hp : p.IsWeightedHomogeneous CycleQ2CartierSurfaceGrading.weight 3) :
    ((-1 : Γ(projectiveSurface r θ,V))^1) • firstCubicSheafSection r θ i₁ j₁ V h₁ p =
      ((-1 : Γ(projectiveSurface r θ,V))^2) • secondCubicSheafSection r θ i₂ j₂ V h₂ p := by
  exact orientation_of_raw (R := Γ(projectiveSurface r θ,V)) _ _
    (rawCubicSheafSection_transition r θ i₁ i₂ j₁ j₂ V hV h₁ h₂ p hp)

#print axioms rawCubicSection_transition
#print axioms orientedCubicSheafSection_agreement

end CycleQ2GeometricSurfaceCubicResidues
end

end SurfaceResidueAssemblyPart06

section SurfaceResidueAssemblyPart07

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2GeometricSurfaceResidueRestriction

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry Module
open CycleQ2GeometricAffineChartSections CycleQ2GeometricDifferentialSheaf
open CycleQ2GeometricSheafKaehlerMap CycleQ2GeometricSurfaceExteriorSections
open CycleQ2GeometricDifferentialChartTransport CycleQ2GeometricExteriorSheaf

variable {X : Scheme.{0}} {U : X.Opens} {A : Type} [CommRing A] [Algebra ℂ A]
  (e : U.toScheme ≅ Spec (CommRingCat.of A))
  (f : X ⟶ Spec (CommRingCat.of ℂ))
  (h : e.inv ≫ U.ι ≫ f = Spec.map (CommRingCat.ofHom (algebraMap ℂ A)))

theorem chartKaehlerSection_restrict {V W : Over U} (g : V ⟶ W)
    (ω : KaehlerDifferential ℂ A) :
    (differentialSheaf X.sheaf (schemeCoefficient f)).val.map g.left.op
        (chartKaehlerSection e f h W ω) = chartKaehlerSection e f h V ω :=
  sectionLift_restriction X.sheaf (schemeCoefficient f)
    (differentialSheaf X.sheaf (schemeCoefficient f))
    (universalDifferential X.sheaf (schemeCoefficient f)) W.left
    (chartSection e W) (chartSection_complex e f h W)
    V.left g.left.le (chartSection e V) (chartSection_complex e f h V)
    (chartSection_naturality e g) ω

/-- Transport through an actual affine chart and the canonical
exterior-sheaf unit commutes with every actual open restriction. -/
theorem chartExteriorSheafSection_restrict
    (b : Basis (Fin 2) A (KaehlerDifferential ℂ A))
    {V W : Over U} (g : V ⟶ W) (ω : ⋀[A]^2 (KaehlerDifferential ℂ A)) :
    (exteriorSheaf X.sheaf (differentialSheaf X.sheaf (schemeCoefficient f)).val 2).val.map g.left.op
        (exteriorSection X.sheaf (differentialSheaf X.sheaf (schemeCoefficient f)).val 2 W.left
          (chartExteriorSection e f h b W ω)) =
      exteriorSection X.sheaf (differentialSheaf X.sheaf (schemeCoefficient f)).val 2 V.left
        (chartExteriorSection e f h b V ω) := by
  have hω : ω ∈ Submodule.span A (Set.range (exteriorPower.ιMulti A 2)) := by
    rw [exteriorPower.ιMulti_span]
    trivial
  induction hω using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨a,rfl⟩ := hx
      have ha : a = ![a 0,a 1] := by funext i; fin_cases i <;> rfl
      rw [ha,chartExteriorSection_wedge,chartExteriorSection_wedge]
      change (exteriorSheaf X.sheaf (differentialSheaf X.sheaf (schemeCoefficient f)).val 2).val.map
          g.left.op (wedgeSection X.sheaf
            (differentialSheaf X.sheaf (schemeCoefficient f)).val 2 W.left
              ![chartKaehlerSection e f h W (a 0),chartKaehlerSection e f h W (a 1)]) =
        wedgeSection X.sheaf (differentialSheaf X.sheaf (schemeCoefficient f)).val 2 V.left
          ![chartKaehlerSection e f h V (a 0),chartKaehlerSection e f h V (a 1)]
      rw [wedgeSection_restrict]
      congr 1
      funext i
      fin_cases i <;> simp only [Matrix.cons_val_zero',Matrix.cons_val_succ']
      · exact chartKaehlerSection_restrict e f h g (a 0)
      · exact chartKaehlerSection_restrict e f h g (a 1)
  | zero => simp only [map_zero]
  | add x y _ _ hx hy => simp only [map_add,hx,hy]
  | smul a x _ hx =>
      let P := chartExteriorSection e f h b W
      let Q := chartExteriorSection e f h b V
      let EW := exteriorSection X.sheaf
        (differentialSheaf X.sheaf (schemeCoefficient f)).val 2 W.left
      let EV := exteriorSection X.sheaf
        (differentialSheaf X.sheaf (schemeCoefficient f)).val 2 V.left
      let L := (exteriorSheaf X.sheaf
        (differentialSheaf X.sheaf (schemeCoefficient f)).val 2).val.restrictₛₗ g.left.op
      change L (EW (P (a • x))) = EV (Q (a • x))
      calc
        _ = L (EW (chartSection e W a • P x)) :=
          congrArg (fun z => L (EW z)) (map_smulₛₗ P a x)
        _ = L (chartSection e W a • EW (P x)) :=
          congrArg L (map_smul EW (chartSection e W a) (P x))
        _ = X.presheaf.map g.left.op (chartSection e W a) • L (EW (P x)) :=
          map_smulₛₗ L (chartSection e W a) (EW (P x))
        _ = chartSection e V a • L (EW (P x)) :=
          congrArg (fun c : Γ(X,V.left) => c • L (EW (P x)))
            (chartSection_naturality e g a)
        _ = chartSection e V a • EV (Q x) :=
          congrArg (fun z => chartSection e V a • z) hx
        _ = EV (chartSection e V a • Q x) := (map_smul EV _ _).symm
        _ = _ := congrArg EV (map_smulₛₗ Q a x).symm

open CycleQ2GeometricSurfaceAdjunction

/-- The actual local residue sections form the restriction family of
their value on the whole actual Jacobian chart. -/
theorem chartResidueSheafSection_restrict
    (v : Fin 2 → SurfacePoly) (n t : SurfacePoly)
    (eR : U.toScheme ≅ Spec (CommRingCat.of (AdjunctionPatch v n t)))
    (hR : eR.inv ≫ U.ι ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap ℂ (AdjunctionPatch v n t))))
    {V W : Over U} (g : V ⟶ W) :
    (exteriorSheaf X.sheaf (differentialSheaf X.sheaf (schemeCoefficient f)).val 2).val.map g.left.op
        (chartResidueSheafSection f v n t eR hR W) =
      chartResidueSheafSection f v n t eR hR V :=
  chartExteriorSheafSection_restrict eR f hR (localSurfaceKaehlerBasis v n t) g
    (localSurfaceResidueForm v n t)

#print axioms chartResidueSheafSection_restrict

end CycleQ2GeometricSurfaceResidueRestriction
end

end SurfaceResidueAssemblyPart07

section SurfaceResidueAssemblyPart08

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2GeometricSurfaceResidueCompatibility

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry Module MvPolynomial
open CycleQ2SeedTrace CycleQ2CartierProjectiveCover
open CycleQ2GeometricAffineChartSections CycleQ2GeometricSurfaceAdjunction
open CycleQ2GeometricDifferentialSheaf (differentialSheaf ringSheaf)
open CycleQ2GeometricSurfaceDehomogenizedCharts CycleQ2GeometricSurfaceCoefficients
open CycleQ2GeometricSurfaceOverlap CycleQ2GeometricSurfaceJacobianCharts
open CycleQ2GeometricSurfaceResidueSections CycleQ2GeometricSurfaceResidueCrossCoordinates
open CycleQ2GeometricSurfaceCubicResidues CycleQ2GeometricSurfaceResidueRestriction
open CycleQ2GeometricExteriorSheaf CycleQ2GeometricAffineCurveCharts

abbrev surfaceExteriorModule (r θ : ℂ) :=
  exteriorSheaf (projectiveSurface r θ).sheaf
    (differentialSheaf (projectiveSurface r θ).sheaf
      (schemeCoefficient (projectiveToComplex r θ))).val 2

theorem firstResidueSection_agreement (r θ : ℂ)
    (i₁ i₂ : Fin 2) (j₁ j₂ : Fin 3)
    (V : (projectiveSurface r θ).Opens)
    (h₁ : V ≤ firstNormalOpen r θ i₁ j₁) (h₂ : V ≤ firstNormalOpen r θ i₂ j₂) :
    firstResidueSection r θ i₁ j₁ V h₁ = firstResidueSection r θ i₂ j₂ V h₂ :=
  principal_residueSection_agreement (X := projectiveSurface r θ)
    (projectiveToComplex r θ) (firstEquations r θ) (firstAffineChart r θ)
    (firstAffineChart_overComplex r θ)
    (normalPolynomial (firstQuadric r) i₁) (includeCurve (MvPolynomial.X j₁))
    (normalPolynomial (firstQuadric r) i₂) (includeCurve (MvPolynomial.X j₂)) V h₁ h₂

theorem secondResidueSection_agreement (r θ : ℂ)
    (i₁ i₂ : Fin 2) (j₁ j₂ : Fin 3)
    (V : (projectiveSurface r θ).Opens)
    (h₁ : V ≤ secondNormalOpen r θ i₁ j₁) (h₂ : V ≤ secondNormalOpen r θ i₂ j₂) :
    secondResidueSection r θ i₁ j₁ V h₁ = secondResidueSection r θ i₂ j₂ V h₂ :=
  principal_residueSection_agreement (X := projectiveSurface r θ)
    (projectiveToComplex r θ) (secondEquations r θ) (secondAffineChart r θ)
    (secondAffineChart_overComplex r θ)
    (normalPolynomial (secondQuadric r) i₁) (includeCurve (MvPolynomial.X j₁))
    (normalPolynomial (secondQuadric r) i₂) (includeCurve (MvPolynomial.X j₂)) V h₁ h₂

theorem firstCubicSheafSection_agreement (r θ : ℂ)
    (i₁ i₂ : Fin 2) (j₁ j₂ : Fin 3)
    (V : (projectiveSurface r θ).Opens)
    (h₁ : V ≤ firstNormalOpen r θ i₁ j₁) (h₂ : V ≤ firstNormalOpen r θ i₂ j₂)
    (p : WeightedPoly) :
    firstCubicSheafSection r θ i₁ j₁ V h₁ p = firstCubicSheafSection r θ i₂ j₂ V h₂ p := by
  have hraw : firstCubicResidueSection r θ i₁ j₁ V h₁ p =
      firstCubicResidueSection r θ i₂ j₂ V h₂ p :=
    congrArg (fun ω => firstCoefficientSection r θ V
      (h₁.trans (firstNormalOpen_le r θ i₁ j₁)) p • ω)
      (firstResidueSection_agreement r θ i₁ i₂ j₁ j₂ V h₁ h₂)
  exact (firstCubicSheafSection_eq r θ i₁ j₁ V h₁ p).trans
    ((congrArg (exteriorSection (projectiveSurface r θ).sheaf
      (differentialSheaf (projectiveSurface r θ).sheaf
        (schemeCoefficient (projectiveToComplex r θ))).val 2 V) hraw).trans
          (firstCubicSheafSection_eq r θ i₂ j₂ V h₂ p).symm)

theorem secondCubicSheafSection_agreement (r θ : ℂ)
    (i₁ i₂ : Fin 2) (j₁ j₂ : Fin 3)
    (V : (projectiveSurface r θ).Opens)
    (h₁ : V ≤ secondNormalOpen r θ i₁ j₁) (h₂ : V ≤ secondNormalOpen r θ i₂ j₂)
    (p : WeightedPoly) :
    secondCubicSheafSection r θ i₁ j₁ V h₁ p = secondCubicSheafSection r θ i₂ j₂ V h₂ p := by
  have hraw : secondCubicResidueSection r θ i₁ j₁ V h₁ p =
      secondCubicResidueSection r θ i₂ j₂ V h₂ p :=
    congrArg (fun ω => secondCoefficientSection r θ V
      (h₁.trans (secondNormalOpen_le r θ i₁ j₁)) p • ω)
      (secondResidueSection_agreement r θ i₁ i₂ j₁ j₂ V h₁ h₂)
  exact (secondCubicSheafSection_eq r θ i₁ j₁ V h₁ p).trans
    ((congrArg (exteriorSection (projectiveSurface r θ).sheaf
      (differentialSheaf (projectiveSurface r θ).sheaf
        (schemeCoefficient (projectiveToComplex r θ))).val 2 V) hraw).trans
          (secondCubicSheafSection_eq r θ i₂ j₂ V h₂ p).symm)

theorem firstCoefficientSection_restrict (r θ : ℂ)
    {V W : (projectiveSurface r θ).Opens} (hVW : V ≤ W)
    (hW : W ≤ coordinatePatch r θ 1) (p : WeightedPoly) :
    (projectiveSurface r θ).presheaf.map (homOfLE hVW).op
        (firstCoefficientSection r θ W hW p) =
      firstCoefficientSection r θ V (hVW.trans hW) p := by
  let g : Over.mk (homOfLE (hVW.trans hW)) ⟶ Over.mk (homOfLE hW) :=
    Over.homMk (homOfLE hVW) (Subsingleton.elim _ _)
  exact chartSection_naturality (firstAffineChart r θ) g
    (algebraMap SurfacePoly (SurfaceChartRing (firstEquations r θ))
      (firstSurfaceDehomogenize p))

theorem secondCoefficientSection_restrict (r θ : ℂ)
    {V W : (projectiveSurface r θ).Opens} (hVW : V ≤ W)
    (hW : W ≤ coordinatePatch r θ 2) (p : WeightedPoly) :
    (projectiveSurface r θ).presheaf.map (homOfLE hVW).op
        (secondCoefficientSection r θ W hW p) =
      secondCoefficientSection r θ V (hVW.trans hW) p := by
  let g : Over.mk (homOfLE (hVW.trans hW)) ⟶ Over.mk (homOfLE hW) :=
    Over.homMk (homOfLE hVW) (Subsingleton.elim _ _)
  exact chartSection_naturality (secondAffineChart r θ) g
    (algebraMap SurfacePoly (SurfaceChartRing (secondEquations r θ))
      (secondSurfaceDehomogenize p))

theorem firstCubicSheafSection_restrict (r θ : ℂ) (i : Fin 2) (j : Fin 3)
    {V W : (projectiveSurface r θ).Opens} (hVW : V ≤ W)
    (hW : W ≤ firstNormalOpen r θ i j) (p : WeightedPoly) :
    (surfaceExteriorModule r θ).val.map (homOfLE hVW).op
        (firstCubicSheafSection r θ i j W hW p) =
      firstCubicSheafSection r θ i j V (hVW.trans hW) p := by
  let g : Over.mk (homOfLE (hVW.trans hW)) ⟶ Over.mk (homOfLE hW) :=
    Over.homMk (homOfLE hVW) (Subsingleton.elim _ _)
  have hρ := chartResidueSheafSection_restrict (projectiveToComplex r θ) (firstEquations r θ)
    (normalPolynomial (firstQuadric r) i) (includeCurve (MvPolynomial.X j))
    (firstNormalChart r θ i j) (firstNormalChart_overComplex r θ i j) g
  refine ((surfaceExteriorModule r θ).val.map_smul (homOfLE hVW).op
    (firstCoefficientSection r θ W (hW.trans (firstNormalOpen_le r θ i j)) p)
    (chartResidueSheafSection (projectiveToComplex r θ) (firstEquations r θ)
      (normalPolynomial (firstQuadric r) i) (includeCurve (MvPolynomial.X j))
      (firstNormalChart r θ i j) (firstNormalChart_overComplex r θ i j)
      (Over.mk (homOfLE hW)))).trans ?_
  exact congrArg₂ (fun (c : Γ(projectiveSurface r θ,V))
    (s : (surfaceExteriorModule r θ).val.obj (op V)) => c • s)
    (firstCoefficientSection_restrict r θ hVW (hW.trans (firstNormalOpen_le r θ i j)) p) hρ

theorem secondCubicSheafSection_restrict (r θ : ℂ) (i : Fin 2) (j : Fin 3)
    {V W : (projectiveSurface r θ).Opens} (hVW : V ≤ W)
    (hW : W ≤ secondNormalOpen r θ i j) (p : WeightedPoly) :
    (surfaceExteriorModule r θ).val.map (homOfLE hVW).op
        (secondCubicSheafSection r θ i j W hW p) =
      secondCubicSheafSection r θ i j V (hVW.trans hW) p := by
  let g : Over.mk (homOfLE (hVW.trans hW)) ⟶ Over.mk (homOfLE hW) :=
    Over.homMk (homOfLE hVW) (Subsingleton.elim _ _)
  have hρ := chartResidueSheafSection_restrict (projectiveToComplex r θ) (secondEquations r θ)
    (normalPolynomial (secondQuadric r) i) (includeCurve (MvPolynomial.X j))
    (secondNormalChart r θ i j) (secondNormalChart_overComplex r θ i j) g
  refine ((surfaceExteriorModule r θ).val.map_smul (homOfLE hVW).op
    (secondCoefficientSection r θ W (hW.trans (secondNormalOpen_le r θ i j)) p)
    (chartResidueSheafSection (projectiveToComplex r θ) (secondEquations r θ)
      (normalPolynomial (secondQuadric r) i) (includeCurve (MvPolynomial.X j))
      (secondNormalChart r θ i j) (secondNormalChart_overComplex r θ i j)
      (Over.mk (homOfLE hW)))).trans ?_
  exact congrArg₂ (fun (c : Γ(projectiveSurface r θ,V))
    (s : (surfaceExteriorModule r θ).val.obj (op V)) => c • s)
    (secondCoefficientSection_restrict r θ hVW (hW.trans (secondNormalOpen_le r θ i j)) p) hρ

#print axioms firstCubicSheafSection_agreement
#print axioms firstCubicSheafSection_restrict
#print axioms secondCubicSheafSection_restrict

end CycleQ2GeometricSurfaceResidueCompatibility
end

end SurfaceResidueAssemblyPart08

section SurfaceResidueAssemblyPart09

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2GeometricSurfaceCubicResidues

open AlgebraicGeometry MvPolynomial
open CycleQ2SeedTrace CycleQ2CartierProjectiveCover
open CycleQ2GeometricSurfaceDehomogenizedCharts CycleQ2GeometricSurfaceOverlap
open CycleQ2GeometricSurfaceAdjunction

/-- The actual coefficient transition for every weighted degree, in the
same actual overlap-section ring used by the residue comparison. -/
theorem homogeneousCoefficient_transition (r θ : ℂ)
    (V : (projectiveSurface r θ).Opens) (hV : V ≤ overlapPatch r θ)
    (h₁ : V ≤ coordinatePatch r θ 1) (h₂ : V ≤ coordinatePatch r θ 2)
    (n : ℕ) (p : WeightedPoly)
    (hp : p.IsWeightedHomogeneous CycleQ2CartierSurfaceGrading.weight n) :
    secondCoefficientSection r θ V h₂ p =
      firstCoefficientSection r θ V h₁ p *
        (overlapSectionMap r θ V hV (inverse (firstEquations r θ)))^n := by
  calc
    _ = overlapSectionMap r θ V hV
        (overlapEquiv r θ (polynomialMap (secondEquations r θ) (secondSurfaceDehomogenize p))) :=
      (overlap_secondCoefficient r θ V hV h₂ p).symm
    _ = overlapSectionMap r θ V hV
        (polynomialMap (firstEquations r θ) (firstSurfaceDehomogenize p) *
          inverse (firstEquations r θ)^n) :=
      congrArg (overlapSectionMap r θ V hV) (overlapEquiv_dehomogenize r θ n p hp)
    _ = _ := by rw [map_mul,map_pow,overlap_firstCoefficient r θ V hV h₁ p]

#print axioms homogeneousCoefficient_transition

end CycleQ2GeometricSurfaceCubicResidues

namespace CycleQ2GeometricSurfaceResidueGluing

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open CycleQ2SeedTrace CycleQ2CartierProjectiveCover
open CycleQ2GeometricDifferentialSheaf (ringSheaf)
open CycleQ2GeometricSurfaceJacobianCharts CycleQ2GeometricSurfaceOverlap
open CycleQ2GeometricSurfaceCubicResidues CycleQ2GeometricSurfaceResidueCompatibility

abbrev ResidueIndex := Bool × Fin 2 × Fin 3

def residueOpen (r θ : ℂ) (a : ResidueIndex) : (projectiveSurface r θ).Opens :=
  match a.1 with
  | false => firstNormalOpen r θ a.2.1 a.2.2
  | true => secondNormalOpen r θ a.2.1 a.2.2

/-- The actual union of the twelve Jacobian opens used near the curve. -/
def residueNeighborhood (r θ : ℂ) : (projectiveSurface r θ).Opens :=
  ⨆ a : ResidueIndex, residueOpen r θ a

theorem firstNormal_le_residueNeighborhood (r θ : ℂ) (i : Fin 2) (j : Fin 3) :
    firstNormalOpen r θ i j ≤ residueNeighborhood r θ :=
  le_iSup (residueOpen r θ) (false,i,j)

theorem secondNormal_le_residueNeighborhood (r θ : ℂ) (i : Fin 2) (j : Fin 3) :
    secondNormalOpen r θ i j ≤ residueNeighborhood r θ :=
  le_iSup (residueOpen r θ) (true,i,j)

/-- Coordinate 1 has sign -1 and coordinate 2 has sign +1, exactly as
certified by the oriented local residue comparison. -/
def localSectionOn (r θ : ℂ) (a : ResidueIndex)
    (V : (projectiveSurface r θ).Opens) (hV : V ≤ residueOpen r θ a)
    (p : WeightedPoly) : (surfaceExteriorModule r θ).val.obj (op V) := by
  rcases a with ⟨s,i,j⟩
  cases s
  · exact -firstCubicSheafSection r θ i j V hV p
  · exact secondCubicSheafSection r θ i j V hV p

def localSection (r θ : ℂ) (p : WeightedPoly) (a : ResidueIndex) :
    (surfaceExteriorModule r θ).val.obj (op (residueOpen r θ a)) :=
  localSectionOn r θ a (residueOpen r θ a) le_rfl p

theorem localSectionOn_restrict (r θ : ℂ) (a : ResidueIndex)
    {V W : (projectiveSurface r θ).Opens} (hVW : V ≤ W)
    (hW : W ≤ residueOpen r θ a) (p : WeightedPoly) :
    (surfaceExteriorModule r θ).val.map (homOfLE hVW).op
        (localSectionOn r θ a W hW p) =
      localSectionOn r θ a V (hVW.trans hW) p := by
  rcases a with ⟨s,i,j⟩
  cases s
  · exact (map_neg ((surfaceExteriorModule r θ).val.restrictₛₗ (homOfLE hVW).op) _).trans
      (congrArg Neg.neg (firstCubicSheafSection_restrict r θ i j hVW hW p))
  · exact secondCubicSheafSection_restrict r θ i j hVW hW p

theorem localSectionOn_agreement (r θ : ℂ) (a b : ResidueIndex)
    (V : (projectiveSurface r θ).Opens)
    (ha : V ≤ residueOpen r θ a) (hb : V ≤ residueOpen r θ b)
    (p : WeightedPoly) (hp : p.IsWeightedHomogeneous CycleQ2CartierSurfaceGrading.weight 3) :
    localSectionOn r θ a V ha p = localSectionOn r θ b V hb p := by
  rcases a with ⟨sa,ia,ja⟩
  rcases b with ⟨sb,ib,jb⟩
  cases sa <;> cases sb
  · exact congrArg Neg.neg (firstCubicSheafSection_agreement r θ ia ib ja jb V ha hb p)
  · have hV : V ≤ overlapPatch r θ := by
      rw [overlapPatch_eq]
      exact le_inf (ha.trans (firstNormalOpen_le r θ ia ja))
        (hb.trans (secondNormalOpen_le r θ ib jb))
    exact (rawCubicSheafSection_transition r θ ia ib ja jb V hV ha hb p hp).symm
  · have hV : V ≤ overlapPatch r θ := by
      rw [overlapPatch_eq]
      exact le_inf (hb.trans (firstNormalOpen_le r θ ib jb))
        (ha.trans (secondNormalOpen_le r θ ia ja))
    exact rawCubicSheafSection_transition r θ ib ia jb ja V hV hb ha p hp
  · exact secondCubicSheafSection_agreement r θ ia ib ja jb V ha hb p

def surfaceExteriorAdditiveSheaf (r θ : ℂ) :
    (projectiveSurface r θ).carrier.Sheaf AddCommGrpCat.{0} :=
  (SheafOfModules.toSheaf (ringSheaf (projectiveSurface r θ).sheaf)).obj
    (surfaceExteriorModule r θ)

theorem localSection_compatible (r θ : ℂ) (p : WeightedPoly)
    (hp : p.IsWeightedHomogeneous CycleQ2CartierSurfaceGrading.weight 3) :
    TopCat.Presheaf.IsCompatible (surfaceExteriorAdditiveSheaf r θ).obj
      (residueOpen r θ) (localSection r θ p) := by
  intro a b
  exact (localSectionOn_restrict r θ a
    (show residueOpen r θ a ⊓ residueOpen r θ b ≤ residueOpen r θ a from inf_le_left)
    le_rfl p).trans
      ((localSectionOn_agreement r θ a b (residueOpen r θ a ⊓ residueOpen r θ b)
        inf_le_left inf_le_right p hp).trans
          (localSectionOn_restrict r θ b
            (show residueOpen r θ a ⊓ residueOpen r θ b ≤ residueOpen r θ b from inf_le_right)
            le_rfl p).symm)

/-- The signed local fixed-cubic forms glue uniquely in the genuine
exterior-square sheaf on the actual Jacobian neighborhood. -/
theorem existsUnique_gluedCubicSection (r θ : ℂ) (p : WeightedPoly)
    (hp : p.IsWeightedHomogeneous CycleQ2CartierSurfaceGrading.weight 3) :
    ∃! σ : (surfaceExteriorModule r θ).val.obj (op (residueNeighborhood r θ)),
      ∀ a : ResidueIndex,
        (surfaceExteriorModule r θ).val.map
          (homOfLE (le_iSup (residueOpen r θ) a)).op σ = localSection r θ p a := by
  let F : (projectiveSurface r θ).carrier.Sheaf AddCommGrpCat.{0} :=
    (SheafOfModules.toSheaf (ringSheaf (projectiveSurface r θ).sheaf)).obj
      (surfaceExteriorModule r θ)
  have hc : TopCat.Presheaf.IsCompatible F.obj (residueOpen r θ) (localSection r θ p) :=
    localSection_compatible r θ p hp
  obtain ⟨σ,hσ,hu⟩ := F.existsUnique_gluing' (residueOpen r θ)
    (residueNeighborhood r θ) (fun a => homOfLE (le_iSup (residueOpen r θ) a)) le_rfl
    (localSection r θ p) hc
  refine ⟨σ,fun a => hσ a,?_⟩
  intro τ hτ
  apply hu τ
  intro a
  exact hτ a

def gluedCubicSection (r θ : ℂ) (p : WeightedPoly)
    (hp : p.IsWeightedHomogeneous CycleQ2CartierSurfaceGrading.weight 3) :
    (surfaceExteriorModule r θ).val.obj (op (residueNeighborhood r θ)) :=
  Classical.choose (existsUnique_gluedCubicSection r θ p hp)

theorem gluedCubicSection_restrict (r θ : ℂ) (p : WeightedPoly)
    (hp : p.IsWeightedHomogeneous CycleQ2CartierSurfaceGrading.weight 3) (a : ResidueIndex) :
    (surfaceExteriorModule r θ).val.map
        (homOfLE (le_iSup (residueOpen r θ) a)).op (gluedCubicSection r θ p hp) =
      localSection r θ p a :=
  (Classical.choose_spec (existsUnique_gluedCubicSection r θ p hp)).1 a

theorem gluedCubicSection_on_subopen (r θ : ℂ) (p : WeightedPoly)
    (hp : p.IsWeightedHomogeneous CycleQ2CartierSurfaceGrading.weight 3)
    (a : ResidueIndex) (V : (projectiveSurface r θ).Opens) (hV : V ≤ residueOpen r θ a) :
    (surfaceExteriorModule r θ).val.map
        (homOfLE (hV.trans (le_iSup (residueOpen r θ) a))).op (gluedCubicSection r θ p hp) =
      localSectionOn r θ a V hV p := by
  calc
    _ = (surfaceExteriorModule r θ).val.map (homOfLE hV).op
        ((surfaceExteriorModule r θ).val.map
          (homOfLE (le_iSup (residueOpen r θ) a)).op (gluedCubicSection r θ p hp)) :=
      (surfaceExteriorModule r θ).val.map_comp_apply
        (homOfLE (le_iSup (residueOpen r θ) a)).op (homOfLE hV).op _
    _ = (surfaceExteriorModule r θ).val.map (homOfLE hV).op (localSection r θ p a) :=
      congrArg ((surfaceExteriorModule r θ).val.map (homOfLE hV).op)
        (gluedCubicSection_restrict r θ p hp a)
    _ = _ := localSectionOn_restrict r θ a hV le_rfl p

theorem gluedCubicSection_unique (r θ : ℂ) (p : WeightedPoly)
    (hp : p.IsWeightedHomogeneous CycleQ2CartierSurfaceGrading.weight 3)
    (σ : (surfaceExteriorModule r θ).val.obj (op (residueNeighborhood r θ)))
    (hσ : ∀ a : ResidueIndex,
      (surfaceExteriorModule r θ).val.map
        (homOfLE (le_iSup (residueOpen r θ) a)).op σ = localSection r θ p a) :
    σ = gluedCubicSection r θ p hp :=
  (Classical.choose_spec (existsUnique_gluedCubicSection r θ p hp)).2 σ hσ

theorem gluedCubicSection_firstChart (r θ : ℂ) (p : WeightedPoly)
    (hp : p.IsWeightedHomogeneous CycleQ2CartierSurfaceGrading.weight 3)
    (i : Fin 2) (j : Fin 3) (V : (projectiveSurface r θ).Opens)
    (hV : V ≤ firstNormalOpen r θ i j) :
    (surfaceExteriorModule r θ).val.map
        (homOfLE (hV.trans (firstNormal_le_residueNeighborhood r θ i j))).op
        (gluedCubicSection r θ p hp) = -firstCubicSheafSection r θ i j V hV p :=
  gluedCubicSection_on_subopen r θ p hp (false,i,j) V hV

theorem gluedCubicSection_secondChart (r θ : ℂ) (p : WeightedPoly)
    (hp : p.IsWeightedHomogeneous CycleQ2CartierSurfaceGrading.weight 3)
    (i : Fin 2) (j : Fin 3) (V : (projectiveSurface r θ).Opens)
    (hV : V ≤ secondNormalOpen r θ i j) :
    (surfaceExteriorModule r θ).val.map
        (homOfLE (hV.trans (secondNormal_le_residueNeighborhood r θ i j))).op
        (gluedCubicSection r θ p hp) = secondCubicSheafSection r θ i j V hV p :=
  gluedCubicSection_on_subopen r θ p hp (true,i,j) V hV

/-- For the literal member used throughout the argument, this actual
surface neighborhood contains the entire image of the curve. -/
theorem literal_residueNeighborhood_preimage :
    CycleQ2GeometricLiteralSurface.curveToSurface 57 1 ⁻¹ᵁ residueNeighborhood 57 1 = ⊤ := by
  apply le_antisymm le_top
  apply (le_of_eq CycleQ2GeometricSurfaceNormalCover.normalSurfaceOpen_preimage_cover.symm).trans
  apply sup_le
  · refine iSup_le fun i => iSup_le fun j => ?_
    intro x hx
    exact firstNormal_le_residueNeighborhood 57 1 i j hx
  · refine iSup_le fun i => iSup_le fun j => ?_
    intro x hx
    exact secondNormal_le_residueNeighborhood 57 1 i j hx

#print axioms existsUnique_gluedCubicSection
#print axioms gluedCubicSection_on_subopen
#print axioms literal_residueNeighborhood_preimage

end CycleQ2GeometricSurfaceResidueGluing
end

end SurfaceResidueAssemblyPart09
