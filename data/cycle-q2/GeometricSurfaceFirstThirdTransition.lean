import Proposal.GeometricSurfaceFirstThirdAmbient
import Proposal.GeometricCrossChartResidueSections
import Proposal.GeometricSurfaceCoordinateSections

/-!
# The actual first-to-third residue transition

Status: source-only proof draft; verification is deferred at the user's request.
The ambient localization maps to the actual common section ring using the
original homogeneous coordinate ratios. The positive mixed determinant and
actual Kähler differential expansion then identify the two original residue
sections. Their fixed degree-three coefficients cancel the transition factor.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2SurfaceFirstThirdTransition

open MvPolynomial Module
open CycleQ2GeometricSurfaceAdjunction CycleQ2GeometricSurfaceDehomogenizedCharts
open CycleQ2CartierSurfaceGrading CycleQ2ThirdSurfaceChart

section ActualSections

open CategoryTheory Opposite AlgebraicGeometry
open CycleQ2CartierProjectiveCover CycleQ2GeometricAffineChartSections
open CycleQ2GeometricDifferentialSheaf CycleQ2GeometricSheafKaehlerMap
open CycleQ2GeometricExteriorSheaf
open CycleQ2GeometricSurfaceResidueSections CycleQ2SurfaceCommonOpen
open CycleQ2SurfaceResidueSheafOverlap CycleQ2GeometricSurfaceCoefficients
open CycleQ2CrossChartResidueSections
open Ambient

variable (r θ : ℂ) (n₁ t₁ n₃ t₃ : SurfacePoly)
  (V : (projectiveSurface r θ).Opens)
  (h₁ : V ≤ firstPatchOpen r θ n₁ t₁)
  (h₃ : V ≤ thirdPatchOpen r θ n₃ t₃)

def firstPolynomialSection : SurfacePoly →+* Γ(projectiveSurface r θ,V) :=
  (chartSection (firstPatchChart r θ n₁ t₁) (Over.mk (homOfLE h₁))).comp
    (algebraMap SurfacePoly (AdjunctionPatch (firstEquations r θ) n₁ t₁))

def thirdPolynomialSection : SurfacePoly →+* Γ(projectiveSurface r θ,V) :=
  (chartSection (thirdPatchChart r θ n₃ t₃) (Over.mk (homOfLE h₃))).comp
    (algebraMap SurfacePoly (AdjunctionPatch (thirdEquations r θ) n₃ t₃))

theorem firstPolynomialSection_equation (j : Fin 2) :
    firstPolynomialSection r θ n₁ t₁ V h₁ (firstEquations r θ j) = 0 := by
  change chartSection _ _ (algebraMap SurfacePoly (AdjunctionPatch _ _ _)
    (firstEquations r θ j)) = 0
  rw [IsScalarTower.algebraMap_apply SurfacePoly (SurfaceChartRing (firstEquations r θ))
    (AdjunctionPatch (firstEquations r θ) n₁ t₁)]
  have hj : algebraMap SurfacePoly (SurfaceChartRing (firstEquations r θ))
      (firstEquations r θ j) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨j,rfl⟩)
  rw [hj, map_zero, map_zero]

theorem firstPolynomialSection_base (p : SurfacePoly) :
    firstPolynomialSection r θ n₁ t₁ V h₁ p =
      chartSurfaceSectionMap (firstEquations r θ) n₁ t₁
        (firstPatchChart r θ n₁ t₁) (Over.mk (homOfLE h₁))
        (Ideal.Quotient.mk (surfaceChartIdeal (firstEquations r θ)) p) := by
  change chartSection _ _ (algebraMap SurfacePoly (AdjunctionPatch _ _ _) p) = _
  rw [IsScalarTower.algebraMap_apply SurfacePoly (SurfaceChartRing (firstEquations r θ))
    (AdjunctionPatch (firstEquations r θ) n₁ t₁)]
  rfl

theorem thirdPolynomialSection_base (p : SurfacePoly) :
    thirdPolynomialSection r θ n₃ t₃ V h₃ p =
      chartSurfaceSectionMap (thirdEquations r θ) n₃ t₃
        (thirdPatchChart r θ n₃ t₃) (Over.mk (homOfLE h₃))
        (Ideal.Quotient.mk (surfaceChartIdeal (thirdEquations r θ)) p) := by
  change chartSection _ _ (algebraMap SurfacePoly (AdjunctionPatch _ _ _) p) = _
  rw [IsScalarTower.algebraMap_apply SurfacePoly (SurfaceChartRing (thirdEquations r θ))
    (AdjunctionPatch (thirdEquations r θ) n₃ t₃)]
  rfl

variable (φ : AmbientOverlap →+* Γ(projectiveSurface r θ,V))
  (hsource : ∀ p : SurfacePoly, φ (base p) =
    firstPolynomialSection r θ n₁ t₁ V h₁ p)
  (htarget : ∀ p : SurfacePoly, φ (ambientChangeEvaluate p) =
    thirdPolynomialSection r θ n₃ t₃ V h₃ p)

include hsource in
theorem ambientSectionMap_complex (c : ℂ) :
    φ (algebraMap ℂ AmbientOverlap c) =
      coefficientOn (projectiveSurface r θ).sheaf
        (schemeCoefficient (CycleQ2GeometricSurfaceCoefficients.projectiveToComplex r θ)) V c := by
  have hc : algebraMap ℂ AmbientOverlap c = base (C c) := by
    exact (base.commutes c).symm
  rw [hc, hsource]
  change chartSection (firstPatchChart r θ n₁ t₁) (Over.mk (homOfLE h₁))
    (algebraMap SurfacePoly (AdjunctionPatch (firstEquations r θ) n₁ t₁) (C c)) = _
  have hC : algebraMap SurfacePoly (AdjunctionPatch (firstEquations r θ) n₁ t₁) (C c) =
      algebraMap ℂ (AdjunctionPatch (firstEquations r θ) n₁ t₁) c := by
    exact (IsScalarTower.algebraMap_apply ℂ SurfacePoly
      (AdjunctionPatch (firstEquations r θ) n₁ t₁) c).symm
  rw [hC]
  exact chartSection_complex (firstPatchChart r θ n₁ t₁)
    (CycleQ2GeometricSurfaceCoefficients.projectiveToComplex r θ)
    (firstPatchChart_overComplex r θ n₁ t₁) _ c

def ambientDifferentialSection : KaehlerDifferential ℂ AmbientOverlap →+
    (differentialSheaf (projectiveSurface r θ).sheaf
      (schemeCoefficient (CycleQ2GeometricSurfaceCoefficients.projectiveToComplex r θ))).val.obj (op V) :=
  sectionLift (projectiveSurface r θ).sheaf
    (schemeCoefficient (CycleQ2GeometricSurfaceCoefficients.projectiveToComplex r θ))
    (differentialSheaf (projectiveSurface r θ).sheaf
      (schemeCoefficient (CycleQ2GeometricSurfaceCoefficients.projectiveToComplex r θ)))
    (universalDifferential (projectiveSurface r θ).sheaf
      (schemeCoefficient (CycleQ2GeometricSurfaceCoefficients.projectiveToComplex r θ)))
    V φ (ambientSectionMap_complex r θ n₁ t₁ V h₁ φ hsource)

include hsource in
theorem ambientDifferentialSection_D (a : AmbientOverlap) :
    ambientDifferentialSection r θ n₁ t₁ V h₁ φ hsource
        (KaehlerDifferential.D ℂ AmbientOverlap a) =
      (universalDifferential (projectiveSurface r θ).sheaf
        (schemeCoefficient (CycleQ2GeometricSurfaceCoefficients.projectiveToComplex r θ))).d
        (X := op V) (φ a) :=
  sectionLift_D (projectiveSurface r θ).sheaf
    (schemeCoefficient (CycleQ2GeometricSurfaceCoefficients.projectiveToComplex r θ))
    (differentialSheaf (projectiveSurface r θ).sheaf
      (schemeCoefficient (CycleQ2GeometricSurfaceCoefficients.projectiveToComplex r θ)))
    (universalDifferential (projectiveSurface r θ).sheaf
      (schemeCoefficient (CycleQ2GeometricSurfaceCoefficients.projectiveToComplex r θ)))
    V φ (ambientSectionMap_complex r θ n₁ t₁ V h₁ φ hsource) a

include hsource in
theorem ambientDifferentialSection_smul (a : AmbientOverlap)
    (ω : KaehlerDifferential ℂ AmbientOverlap) :
    ambientDifferentialSection r θ n₁ t₁ V h₁ φ hsource (a • ω) =
      φ a • ambientDifferentialSection r θ n₁ t₁ V h₁ φ hsource ω :=
  sectionLift_smul (projectiveSurface r θ).sheaf
    (schemeCoefficient (CycleQ2GeometricSurfaceCoefficients.projectiveToComplex r θ))
    (differentialSheaf (projectiveSurface r θ).sheaf
      (schemeCoefficient (CycleQ2GeometricSurfaceCoefficients.projectiveToComplex r θ)))
    (universalDifferential (projectiveSurface r θ).sheaf
      (schemeCoefficient (CycleQ2GeometricSurfaceCoefficients.projectiveToComplex r θ)))
    V φ (ambientSectionMap_complex r θ n₁ t₁ V h₁ φ hsource) a ω

include hsource htarget in
theorem thirdPolynomialDifferential_expansion (p : SurfacePoly) :
    polynomialDifferentialSection_common
        (CycleQ2GeometricSurfaceCoefficients.projectiveToComplex r θ)
        (thirdEquations r θ) n₃ t₃ (thirdPatchChart r θ n₃ t₃)
        (Over.mk (homOfLE h₃)) p =
      chartAmbientDifferential
        (CycleQ2GeometricSurfaceCoefficients.projectiveToComplex r θ)
        (firstEquations r θ) n₁ t₁ (firstPatchChart r θ n₁ t₁)
        (Over.mk (homOfLE h₁)) (pulledGradient φ p) := by
  let L := ambientDifferentialSection r θ n₁ t₁ V h₁ φ hsource
  have hsourceD (j : Option (Fin 3)) :
      L (KaehlerDifferential.D ℂ AmbientOverlap (ambientCoordinate j)) =
        polynomialDifferentialSection_common
          (CycleQ2GeometricSurfaceCoefficients.projectiveToComplex r θ)
          (firstEquations r θ) n₁ t₁ (firstPatchChart r θ n₁ t₁)
          (Over.mk (homOfLE h₁)) (X j) := by
    rw [ambientDifferentialSection_D]
    apply congrArg ((universalDifferential (projectiveSurface r θ).sheaf
      (schemeCoefficient (CycleQ2GeometricSurfaceCoefficients.projectiveToComplex r θ))).d
      (X := op V))
    exact hsource (X j)
  have htargetD : L (KaehlerDifferential.D ℂ AmbientOverlap (ambientChangeEvaluate p)) =
      polynomialDifferentialSection_common
        (CycleQ2GeometricSurfaceCoefficients.projectiveToComplex r θ)
        (thirdEquations r θ) n₃ t₃ (thirdPatchChart r θ n₃ t₃)
        (Over.mk (homOfLE h₃)) p := by
    rw [ambientDifferentialSection_D]
    apply congrArg ((universalDifferential (projectiveSurface r θ).sheaf
      (schemeCoefficient (CycleQ2GeometricSurfaceCoefficients.projectiveToComplex r θ))).d
      (X := op V))
    exact htarget p
  rw [← htargetD, ambient_D_expand, map_sum]
  simp only [L, ambientDifferentialSection_smul, hsourceD]
  symm
  exact Equiv.sum_comp (_root_.finSuccEquiv 3)
    (fun j : Option (Fin 3) => φ (ambientPartial j (ambientChangeEvaluate p)) •
      polynomialDifferentialSection_common
        (CycleQ2GeometricSurfaceCoefficients.projectiveToComplex r θ)
        (firstEquations r θ) n₁ t₁ (firstPatchChart r θ n₁ t₁)
        (Over.mk (homOfLE h₁)) (X j))

include hsource htarget in
theorem actual_mixed_determinant (p q : SurfacePoly) :
    Matrix.det ![
      chartEquationGradient (firstEquations r θ) n₁ t₁
        (firstPatchChart r θ n₁ t₁) (Over.mk (homOfLE h₁)) 0,
      chartEquationGradient (firstEquations r θ) n₁ t₁
        (firstPatchChart r θ n₁ t₁) (Over.mk (homOfLE h₁)) 1,
      pulledGradient φ p, pulledGradient φ q] =
      ((φ (ambientCoordinate (some 2)))^3) *
        chartSurfaceSectionMap (thirdEquations r θ) n₃ t₃
          (thirdPatchChart r θ n₃ t₃) (Over.mk (homOfLE h₃))
          (augmentedJacobian (thirdEquations r θ) p q) := by
  have hF : sourcePolynomialMap φ (firstEquations r θ 0) = 0 :=
    (hsource _).trans (firstPolynomialSection_equation r θ n₁ t₁ V h₁ 0)
  have hh : sourcePolynomialMap φ (firstEquations r θ 1) = 0 :=
    (hsource _).trans (firstPolynomialSection_equation r θ n₁ t₁ V h₁ 1)
  have hleft : ![
      chartEquationGradient (firstEquations r θ) n₁ t₁
        (firstPatchChart r θ n₁ t₁) (Over.mk (homOfLE h₁)) 0,
      chartEquationGradient (firstEquations r θ) n₁ t₁
        (firstPatchChart r θ n₁ t₁) (Over.mk (homOfLE h₁)) 1,
      pulledGradient φ p, pulledGradient φ q] = mixedGradientMatrix φ r θ p q := by
    ext i j
    fin_cases i <;> simp only [mixedGradientMatrix, Matrix.cons_val_zero', Matrix.cons_val_succ']
    · exact ((hsource _).trans (firstPolynomialSection_base r θ n₁ t₁ V h₁ _)).symm
    · exact ((hsource _).trans (firstPolynomialSection_base r θ n₁ t₁ V h₁ _)).symm
    · rfl
    · rfl
  have hright : (changedGradientMatrix φ r θ p q).det =
      chartSurfaceSectionMap (thirdEquations r θ) n₃ t₃
        (thirdPatchChart r θ n₃ t₃) (Over.mk (homOfLE h₃))
        (augmentedJacobian (thirdEquations r θ) p q) := by
    rw [augmentedJacobian_polynomial, RingHom.map_det]
    congr 1
    ext i j
    exact (htarget _).trans (thirdPolynomialSection_base r θ n₃ t₃ V h₃ _)
  rw [hleft, mixedJacobian_transition r θ φ hF hh p q, hright]

/-- The determinant calculation is now an equality of the genuine
exterior-sheaf sections on the actual projective overlap. -/
include hsource htarget in
theorem residueSheafSection_transition_of_maps :
    chartResidueSheafSection
        (CycleQ2GeometricSurfaceCoefficients.projectiveToComplex r θ)
        (thirdEquations r θ) n₃ t₃ (thirdPatchChart r θ n₃ t₃)
        (thirdPatchChart_overComplex r θ n₃ t₃) (Over.mk (homOfLE h₃)) =
      ((φ (ambientCoordinate (some 2)))^3) •
        chartResidueSheafSection
          (CycleQ2GeometricSurfaceCoefficients.projectiveToComplex r θ)
          (firstEquations r θ) n₁ t₁ (firstPatchChart r θ n₁ t₁)
          (firstPatchChart_overComplex r θ n₁ t₁) (Over.mk (homOfLE h₁)) :=
  CycleQ2CrossChartResidueSections.residueSheafSection_transition
    (CycleQ2GeometricSurfaceCoefficients.projectiveToComplex r θ)
    (firstEquations r θ) (thirdEquations r θ) n₁ t₁ n₃ t₃
    (firstPatchChart r θ n₁ t₁) (thirdPatchChart r θ n₃ t₃)
    (firstPatchChart_overComplex r θ n₁ t₁) (thirdPatchChart_overComplex r θ n₃ t₃)
    V h₁ h₃ (pulledGradient φ) (((φ (ambientCoordinate (some 2)))^3))
    (thirdPolynomialDifferential_expansion r θ n₁ t₁ n₃ t₃ V h₁ h₃ φ hsource htarget)
    (actual_mixed_determinant r θ n₁ t₁ n₃ t₃ V h₁ h₃ φ hsource htarget)

include hsource htarget in
theorem orientedCubicSections_agree_of_maps (p : MvPolynomial (Fin 5) ℂ)
    (hp : p.IsWeightedHomogeneous weight 3) :
    firstCubicSection r θ n₁ t₁ p (Over.mk (homOfLE h₁)) =
      thirdCubicSection r θ n₃ t₃ p (Over.mk (homOfLE h₃)) := by
  have hcoeff : thirdPolynomialSection r θ n₃ t₃ V h₃ (thirdDehomogenize p) *
      ((φ (ambientCoordinate (some 2)))^3) =
      firstPolynomialSection r θ n₁ t₁ V h₁ (firstSurfaceDehomogenize p) := by
    rw [← htarget, ← hsource]
    exact cubic_scalar_balance φ p hp
  unfold firstCubicSection thirdCubicSection
  rw [residueSheafSection_transition_of_maps r θ n₁ t₁ n₃ t₃ V h₁ h₃ φ hsource htarget,
    ← mul_smul]
  change firstPolynomialSection r θ n₁ t₁ V h₁ (firstSurfaceDehomogenize p) • _ =
    (thirdPolynomialSection r θ n₃ t₃ V h₃ (thirdDehomogenize p) * _) • _
  rw [hcoeff]

end ActualSections

section LiteralMapBinding

open CategoryTheory Opposite AlgebraicGeometry
open CycleQ2CartierProjectiveCover CycleQ2GeometricAffineChartSections
open CycleQ2GeometricSurfaceJacobianCharts CycleQ2GeometricPrincipalChartSections
open CycleQ2SurfaceCommonOpen CycleQ2SurfaceResidueSheafOverlap
open CycleQ2SurfaceCoordinateSections CycleQ2SeedTrace
open Ambient

variable (r θ : ℂ) (n₁ t₁ n₃ t₃ : SurfacePoly)
  (V : (projectiveSurface r θ).Opens)
  (h₁ : V ≤ firstPatchOpen r θ n₁ t₁)
  (h₃ : V ≤ thirdPatchOpen r θ n₃ t₃)

/-- An arbitrary augmented patch uses the unchanged first chart's
actual homogeneous coefficient sections. -/
theorem firstPolynomialSection_homogeneous (n : ℕ) (p : MvPolynomial (Fin 5) ℂ)
    (hp : p.IsWeightedHomogeneous weight n) :
    firstPolynomialSection r θ n₁ t₁ V h₁ (firstSurfaceDehomogenize p) =
      coordinatePolynomialSection r θ 1 V (h₁.trans (firstPatchOpen_le r θ n₁ t₁)) p := by
  calc
    _ = chartSection (firstAffineChart r θ)
        (Over.mk (homOfLE (h₁.trans (firstPatchOpen_le r θ n₁ t₁))))
        (algebraMap SurfacePoly (SurfaceChartRing (firstEquations r θ))
          (firstSurfaceDehomogenize p)) := by
      change chartSection
        (principalChart (firstAffineChart r θ) (augmentedJacobian (firstEquations r θ) n₁ t₁))
        (Over.mk (homOfLE h₁))
        (algebraMap SurfacePoly (AdjunctionPatch (firstEquations r θ) n₁ t₁)
          (firstSurfaceDehomogenize p)) = _
      rw [IsScalarTower.algebraMap_apply SurfacePoly (SurfaceChartRing (firstEquations r θ))
        (AdjunctionPatch (firstEquations r θ) n₁ t₁)]
      simpa only [Over.mk_hom, homOfLE_comp] using
        (principal_chartSection (firstAffineChart r θ)
          (augmentedJacobian (firstEquations r θ) n₁ t₁) (Over.mk (homOfLE h₁))
          (algebraMap SurfacePoly (SurfaceChartRing (firstEquations r θ))
            (firstSurfaceDehomogenize p)))
    _ = _ := first_chart_polynomial_section r θ V
      (h₁.trans (firstPatchOpen_le r θ n₁ t₁)) n p hp

/-- On the third chart the generic coordinate map is the literal map. -/
theorem thirdPolynomialSection_weighted (p : MvPolynomial (Fin 5) ℂ) :
    thirdPolynomialSection r θ n₃ t₃ V h₃ (thirdDehomogenize p) =
      coordinatePolynomialSection r θ 3 V (h₃.trans (thirdPatchOpen_le r θ n₃ t₃)) p := by
  calc
    _ = chartSection (thirdAffineChart r θ)
        (Over.mk (homOfLE (h₃.trans (thirdPatchOpen_le r θ n₃ t₃))))
        (algebraMap SurfacePoly (ThirdChartRing r θ) (thirdDehomogenize p)) := by
      change chartSection
        (principalChart (thirdAffineChart r θ) (augmentedJacobian (thirdEquations r θ) n₃ t₃))
        (Over.mk (homOfLE h₃))
        (algebraMap SurfacePoly (AdjunctionPatch (thirdEquations r θ) n₃ t₃)
          (thirdDehomogenize p)) = _
      rw [IsScalarTower.algebraMap_apply SurfacePoly (ThirdChartRing r θ)
        (AdjunctionPatch (thirdEquations r θ) n₃ t₃)]
      simpa only [Over.mk_hom, homOfLE_comp] using
        (principal_chartSection (thirdAffineChart r θ)
          (augmentedJacobian (thirdEquations r θ) n₃ t₃) (Over.mk (homOfLE h₃))
          (algebraMap SurfacePoly (ThirdChartRing r θ) (thirdDehomogenize p)))
    _ = _ := rfl

/-- The inverse ratio and every coefficient are actual structure-sheaf
sections; this is the projective weighted identity on the given open. -/
theorem homogeneous_section_change (n : ℕ) (p : MvPolynomial (Fin 5) ℂ)
    (hp : p.IsWeightedHomogeneous weight n) :
    thirdPolynomialSection r θ n₃ t₃ V h₃ (thirdDehomogenize p) =
      (thirdPolynomialSection r θ n₃ t₃ V h₃ (X (some 1)))^n *
        firstPolynomialSection r θ n₁ t₁ V h₁ (firstSurfaceDehomogenize p) := by
  have h := coordinatePolynomialSection_change r θ 1 3 V
    (h₁.trans (firstPatchOpen_le r θ n₁ t₁))
    (h₃.trans (thirdPatchOpen_le r θ n₃ t₃)) n p hp
  rw [← thirdPolynomialSection_weighted r θ n₃ t₃ V h₃ p,
    ← thirdPolynomialSection_weighted r θ n₃ t₃ V h₃ (X (1 : Fin 5)),
    ← firstPolynomialSection_homogeneous r θ n₁ t₁ V h₁ n p hp] at h
  simpa only [thirdDehomogenize_eq, aeval_X, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_succ] using h

theorem literal_ratio_inverse :
    firstPolynomialSection r θ n₁ t₁ V h₁ (X (some 2)) *
      thirdPolynomialSection r θ n₃ t₃ V h₃ (X (some 1)) = 1 := by
  have hX : (X (3 : Fin 5) : MvPolynomial (Fin 5) ℂ).IsWeightedHomogeneous weight 1 := by
    simpa only [weight_castSucc] using
      isWeightedHomogeneous_X ℂ weight (3 : Fin 4).castSucc
  have h := coordinateRatio_inverse r θ 1 3 V
    (h₁.trans (firstPatchOpen_le r θ n₁ t₁))
    (h₃.trans (thirdPatchOpen_le r θ n₃ t₃))
  rw [← firstPolynomialSection_homogeneous r θ n₁ t₁ V h₁ 1 (X (3 : Fin 5)) hX,
    ← thirdPolynomialSection_weighted r θ n₃ t₃ V h₃ (X (1 : Fin 5))] at h
  simpa only [firstSurfaceDehomogenize, thirdDehomogenize_eq, aeval_X,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ] using h

theorem source_last_isUnit :
    IsUnit (firstPolynomialSection r θ n₁ t₁ V h₁ (X (some 2))) :=
  isUnit_iff_exists_inv.mpr ⟨thirdPolynomialSection r θ n₃ t₃ V h₃ (X (some 1)),
    literal_ratio_inverse r θ n₁ t₁ n₃ t₃ V h₁ h₃⟩

/-- The actual ambient map into the common section ring. Its inverse
coordinate is justified by the actual projective ratio identity. -/
def literalAmbientSectionMap : AmbientOverlap →+* Γ(projectiveSurface r θ,V) :=
  Localization.awayLift (firstPolynomialSection r θ n₁ t₁ V h₁)
    (X (some (2 : Fin 3))) (source_last_isUnit r θ n₁ t₁ n₃ t₃ V h₁ h₃)

theorem literalAmbientSectionMap_source (p : SurfacePoly) :
    literalAmbientSectionMap r θ n₁ t₁ n₃ t₃ V h₁ h₃ (base p) =
      firstPolynomialSection r θ n₁ t₁ V h₁ p :=
  IsLocalization.Away.lift_eq _ (source_last_isUnit r θ n₁ t₁ n₃ t₃ V h₁ h₃) p

theorem literalAmbientSectionMap_inverse :
    literalAmbientSectionMap r θ n₁ t₁ n₃ t₃ V h₁ h₃ ambientInverse =
      thirdPolynomialSection r θ n₃ t₃ V h₃ (X (some 1)) := by
  apply (source_last_isUnit r θ n₁ t₁ n₃ t₃ V h₁ h₃).mul_left_cancel
  have h := congrArg (literalAmbientSectionMap r θ n₁ t₁ n₃ t₃ V h₁ h₃)
    coordinate_mul_inverse
  rw [map_mul, ambientCoordinate, literalAmbientSectionMap_source, map_one] at h
  exact h.trans (literal_ratio_inverse r θ n₁ t₁ n₃ t₃ V h₁ h₃).symm

/-- The ambient substitution agrees with the actual third chart on
every polynomial, proved from the four homogeneous coordinate sections. -/
theorem literalAmbientSectionMap_target (p : SurfacePoly) :
    literalAmbientSectionMap r θ n₁ t₁ n₃ t₃ V h₁ h₃ (ambientChangeEvaluate p) =
      thirdPolynomialSection r θ n₃ t₃ V h₃ p := by
  have hmaps :
      (literalAmbientSectionMap r θ n₁ t₁ n₃ t₃ V h₁ h₃).comp ambientChangeEvaluate.toRingHom =
        thirdPolynomialSection r θ n₃ t₃ V h₃ := by
    apply MvPolynomial.ringHom_ext
    · intro c
      have h := homogeneous_section_change r θ n₁ t₁ n₃ t₃ V h₁ h₃
        0 (C c) (isWeightedHomogeneous_C weight c)
      have hC : ambientChangeEvaluate (C c) = base (C c) := by simp
      change literalAmbientSectionMap r θ n₁ t₁ n₃ t₃ V h₁ h₃
        (ambientChangeEvaluate (C c)) = _
      rw [hC, literalAmbientSectionMap_source]
      simpa only [thirdDehomogenize, dehomogenize, firstSurfaceDehomogenize,
        aeval_C, pow_zero, one_mul] using h.symm
    · intro j
      change literalAmbientSectionMap r θ n₁ t₁ n₃ t₃ V h₁ h₃
        (ambientChangeEvaluate (X j)) = _
      cases j with
      | none =>
          have h := homogeneous_section_change r θ n₁ t₁ n₃ t₃ V h₁ h₃
            2 originalF2 originalF2_homogeneous
          have hthird : thirdDehomogenize originalF2 = X none := dehomogenize_f2 3
          rw [hthird, firstSurfaceDehomogenize_f2] at h
          simp only [ambientChangeEvaluate, aeval_X, ambientChangeCoordinate,
            map_mul, map_pow, literalAmbientSectionMap_inverse, ambientCoordinate,
            literalAmbientSectionMap_source]
          exact (mul_comm _ _).trans h.symm
      | some j =>
          fin_cases j
          · have hX : (X (0 : Fin 5) : MvPolynomial (Fin 5) ℂ).IsWeightedHomogeneous weight 1 := by
              simpa only [weight_castSucc] using
                isWeightedHomogeneous_X ℂ weight (0 : Fin 4).castSucc
            have h := homogeneous_section_change r θ n₁ t₁ n₃ t₃ V h₁ h₃ 1 (X (0 : Fin 5)) hX
            simp only [thirdDehomogenize_eq, firstSurfaceDehomogenize, aeval_X,
              Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ, pow_one] at h
            simp only [ambientChangeEvaluate, aeval_X, ambientChangeCoordinate,
              Matrix.cons_val_zero, map_mul, literalAmbientSectionMap_inverse, ambientCoordinate,
              literalAmbientSectionMap_source]
            exact (mul_comm _ _).trans h.symm
          · simpa only [ambientChangeEvaluate, aeval_X, ambientChangeCoordinate,
              Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ] using
              literalAmbientSectionMap_inverse r θ n₁ t₁ n₃ t₃ V h₁ h₃
          · have hX : (X (2 : Fin 5) : MvPolynomial (Fin 5) ℂ).IsWeightedHomogeneous weight 1 := by
              simpa only [weight_castSucc] using
                isWeightedHomogeneous_X ℂ weight (2 : Fin 4).castSucc
            have h := homogeneous_section_change r θ n₁ t₁ n₃ t₃ V h₁ h₃ 1 (X (2 : Fin 5)) hX
            simp only [thirdDehomogenize_eq, firstSurfaceDehomogenize, aeval_X,
              Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ, pow_one] at h
            simp only [ambientChangeEvaluate, aeval_X, ambientChangeCoordinate,
              Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ,
              map_mul, literalAmbientSectionMap_inverse,
              ambientCoordinate, literalAmbientSectionMap_source]
            exact (mul_comm _ _).trans h.symm
  exact RingHom.congr_fun hmaps p

/-- The raw positive residue transition on the actual common subopen,
with its coefficient fixed by the original first-chart coordinate. -/
theorem literal_residueSheafSection_transition :
    CycleQ2GeometricExteriorSheaf.chartResidueSheafSection
        (CycleQ2GeometricSurfaceCoefficients.projectiveToComplex r θ)
        (thirdEquations r θ) n₃ t₃ (thirdPatchChart r θ n₃ t₃)
        (thirdPatchChart_overComplex r θ n₃ t₃) (Over.mk (homOfLE h₃)) =
      (firstPolynomialSection r θ n₁ t₁ V h₁ (X (some 2)))^3 •
        CycleQ2GeometricExteriorSheaf.chartResidueSheafSection
          (CycleQ2GeometricSurfaceCoefficients.projectiveToComplex r θ)
          (firstEquations r θ) n₁ t₁ (firstPatchChart r θ n₁ t₁)
          (CycleQ2SurfaceResidueSheafOverlap.firstPatchChart_overComplex r θ n₁ t₁)
          (Over.mk (homOfLE h₁)) := by
  have h := residueSheafSection_transition_of_maps r θ n₁ t₁ n₃ t₃ V h₁ h₃
    (literalAmbientSectionMap r θ n₁ t₁ n₃ t₃ V h₁ h₃)
    (literalAmbientSectionMap_source r θ n₁ t₁ n₃ t₃ V h₁ h₃)
    (literalAmbientSectionMap_target r θ n₁ t₁ n₃ t₃ V h₁ h₃)
  simpa only [ambientCoordinate, literalAmbientSectionMap_source] using h

/-- Closed signed cubic compatibility on every actual common subopen.
There is no supplied extension or residue compatibility premise. -/
theorem orientedCubicSections_agree_on_open (p : MvPolynomial (Fin 5) ℂ)
    (hp : p.IsWeightedHomogeneous weight 3) :
    firstCubicSection r θ n₁ t₁ p (Over.mk (homOfLE h₁)) =
      thirdCubicSection r θ n₃ t₃ p (Over.mk (homOfLE h₃)) :=
  orientedCubicSections_agree_of_maps r θ n₁ t₁ n₃ t₃ V h₁ h₃
    (literalAmbientSectionMap r θ n₁ t₁ n₃ t₃ V h₁ h₃)
    (literalAmbientSectionMap_source r θ n₁ t₁ n₃ t₃ V h₁ h₃)
    (literalAmbientSectionMap_target r θ n₁ t₁ n₃ t₃ V h₁ h₃) p hp

end LiteralMapBinding

section OverCompatibility

open CategoryTheory Opposite AlgebraicGeometry
open CycleQ2CartierProjectiveCover CycleQ2SurfaceCommonOpen
open CycleQ2SurfaceResidueSheafOverlap

variable (r θ : ℂ) (n₁ t₁ n₃ t₃ : SurfacePoly)

def firstCommonSubopen (V : Over (firstPatchOpen r θ n₁ t₁ ⊓ thirdPatchOpen r θ n₃ t₃)) :
    Over (firstPatchOpen r θ n₁ t₁) :=
  Over.mk (V.hom ≫ homOfLE inf_le_left)

def thirdCommonSubopen (V : Over (firstPatchOpen r θ n₁ t₁ ⊓ thirdPatchOpen r θ n₃ t₃)) :
    Over (thirdPatchOpen r θ n₃ t₃) :=
  Over.mk (V.hom ≫ homOfLE inf_le_right)

/-- The exact overlap API consumed by global cubic gluing. The first and third
charts both carry the existing positive orientation. -/
theorem orientedCubicSections_agree (p : MvPolynomial (Fin 5) ℂ)
    (hp : p.IsWeightedHomogeneous weight 3)
    (V : Over (firstPatchOpen r θ n₁ t₁ ⊓ thirdPatchOpen r θ n₃ t₃)) :
    firstCubicSection r θ n₁ t₁ p (firstCommonSubopen r θ n₁ t₁ n₃ t₃ V) =
      thirdCubicSection r θ n₃ t₃ p (thirdCommonSubopen r θ n₁ t₁ n₃ t₃ V) := by
  simpa only [firstCommonSubopen, thirdCommonSubopen, homOfLE_comp] using
    orientedCubicSections_agree_on_open r θ n₁ t₁ n₃ t₃ V.left
      ((leOfHom V.hom).trans inf_le_left) ((leOfHom V.hom).trans inf_le_right) p hp

#print axioms orientedCubicSections_agree

end OverCompatibility

end CycleQ2SurfaceFirstThirdTransition

end
