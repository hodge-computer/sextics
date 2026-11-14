import Proposal.GeometricIntrinsicNormal
import Proposal.GeometricSurfaceDifferentialCharts
import Proposal.GeometricCanonicalSheaf
import Proposal.GeometricCurveCover
import Proposal.GeometricSurfaceCurveCharts
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2GeometricSchemeDifferentialMap

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open CycleQ2GeometricDifferentialSheaf CycleQ2GeometricIntrinsicNormal
open CycleQ2GeometricAffineChartSections CycleQ2GeometricSheafKaehlerMap

variable {X Y : Scheme.{0}} (j : X ⟶ Y)
  (cX : ℂ →+* Γ(X,⊤)) (cY : ℂ →+* Γ(Y,⊤))

/-- The actual direct image of the sheaf of complex differentials. -/
def imageDifferentialModule : SheafOfModules.{0} (ringSheaf Y.sheaf) :=
  (SheafOfModules.pushforward (F := Opens.map j.base) (schemeRingMap j)).obj
    (differentialSheaf X.sheaf cX)

variable (hc : ∀ (U : Y.Opens) (c : ℂ),
  j.app U (coefficientOn Y.sheaf cY U c) =
    coefficientOn X.sheaf cX (j ⁻¹ᵁ U) c)

/-- Pullback of functions followed by the actual universal differential
is a natural derivation into the actual direct image. -/
def imageDifferentialDerivation :
    (imageDifferentialModule j cX).val.Derivation' (coefficientMap Y.sheaf cY) where
  d {U} := ((universalDifferential X.sheaf cX).d
    (X := op (j ⁻¹ᵁ U.unop))).comp (j.app U.unop).hom.toAddMonoidHom
  d_mul {U} a b := by
    change (universalDifferential X.sheaf cX).d (j.app U.unop (a*b)) = _
    rw [map_mul,(universalDifferential X.sheaf cX).d_mul]
    rfl
  d_map {U V} f a := by
    change (universalDifferential X.sheaf cX).d (j.app V.unop (Y.presheaf.map f a)) =
      (differentialSheaf X.sheaf cX).val.map ((Opens.map j.base).map f.unop).op
        ((universalDifferential X.sheaf cX).d (j.app U.unop a))
    have hn := ConcreteCategory.congr_hom (j.naturality f) a
    change j.app V.unop (Y.presheaf.map f a) =
      X.presheaf.map ((Opens.map j.base).map f.unop).op (j.app U.unop a) at hn
    rw [hn]
    exact (universalDifferential X.sheaf cX).d_map _ _
  d_app {U} c := by
    change (universalDifferential X.sheaf cX).d
      (j.app U.unop (coefficientOn Y.sheaf cY U.unop c)) = 0
    rw [hc]
    exact (universalDifferential X.sheaf cX).d_app c

/-- The canonical morphism of differential sheaves induced by the scheme map. -/
def schemeDifferentialMap :
    differentialSheaf Y.sheaf cY ⟶ imageDifferentialModule j cX :=
  differentialLift Y.sheaf cY (imageDifferentialModule j cX)
    (imageDifferentialDerivation j cX cY hc)

theorem schemeDifferentialMap_D (U : Y.Opens) (a : Γ(Y,U)) :
    (schemeDifferentialMap j cX cY hc).val.app (op U)
      ((universalDifferential Y.sheaf cY).d a) =
      (universalDifferential X.sheaf cX).d (j.app U a) :=
  PresheafOfModules.Derivation.congr_d
    (differentialLift_fac Y.sheaf cY (imageDifferentialModule j cX)
      (imageDifferentialDerivation j cX cY hc)) a

/-- A function in the actual ideal has zero pulled-back differential. -/
theorem schemeDifferentialMap_ideal (U : Y.Opens)
    (a : RingHom.ker (j.app U).hom) :
    (schemeDifferentialMap j cX cY hc).val.app (op U)
      ((universalDifferential Y.sheaf cY).d (a : Γ(Y,U))) = 0 := by
  rw [schemeDifferentialMap_D,a.property,map_zero]

/-- The map is determined by its value on actual local function differentials. -/
theorem schemeDifferentialMap_unique
    (g : differentialSheaf Y.sheaf cY ⟶ imageDifferentialModule j cX)
    (hg : ∀ (U : Y.Opens) (a : Γ(Y,U)),
      g.val.app (op U) ((universalDifferential Y.sheaf cY).d a) =
        (universalDifferential X.sheaf cX).d (j.app U a)) :
    g = schemeDifferentialMap j cX cY hc := by
  apply differentialLift_unique Y.sheaf cY (imageDifferentialModule j cX)
  ext U a
  exact (hg U.unop a).trans (schemeDifferentialMap_D j cX cY hc U.unop a).symm

section AffineForms

variable {A : Type} [CommRing A] [Algebra ℂ A]
  (U : Y.Opens) (f : A →+* Γ(Y,U))
  (hf : ∀ c : ℂ, f (algebraMap ℂ A c) = coefficientOn Y.sheaf cY U c)

include hc hf in
theorem pulledSection_complex (c : ℂ) :
    ((j.app U).hom.comp f) (algebraMap ℂ A c) =
      coefficientOn X.sheaf cX (j ⁻¹ᵁ U) c := by
  change j.app U (f (algebraMap ℂ A c)) = _
  rw [hf,hc]

/-- The canonical sheaf map carries every affine Kähler form by the same
actual section-ring homomorphism; this includes its precise coefficients. -/
theorem schemeDifferentialMap_sectionLift (ω : KaehlerDifferential ℂ A) :
    (schemeDifferentialMap j cX cY hc).val.app (op U)
      (sectionLift Y.sheaf cY (differentialSheaf Y.sheaf cY)
        (universalDifferential Y.sheaf cY) U f hf ω) =
      sectionLift X.sheaf cX (differentialSheaf X.sheaf cX)
        (universalDifferential X.sheaf cX) (j ⁻¹ᵁ U) ((j.app U).hom.comp f)
        (pulledSection_complex j cX cY hc U f hf) ω := by
  have hω : ω ∈ Submodule.span A (Set.range (KaehlerDifferential.D ℂ A)) := by
    rw [KaehlerDifferential.span_range_derivation]
    trivial
  induction hω using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨a,rfl⟩ := hx
      rw [sectionLift_D,sectionLift_D,schemeDifferentialMap_D]
      rfl
  | zero => simp only [map_zero]
  | add x y _ _ hx hy => simp only [map_add,hx,hy]
  | smul a x _ hx =>
      rw [sectionLift_smul,sectionLift_smul,
        ((schemeDifferentialMap j cX cY hc).val.app (op U)).hom.map_smul,hx]
      rfl

end AffineForms

def literalCurveDifferentialMap (r θ : ℂ) :
    CycleQ2GeometricSurfaceCoefficients.projectiveDifferentialSheaf r θ ⟶
      imageDifferentialModule (CycleQ2GeometricLiteralSurface.curveToSurface r θ)
        (projectiveGlobalCoefficient r θ) :=
  schemeDifferentialMap (CycleQ2GeometricLiteralSurface.curveToSurface r θ)
    (projectiveGlobalCoefficient r θ)
    (CycleQ2GeometricSurfaceCoefficients.projectiveGlobalCoefficient r θ)
    (CycleQ2GeometricSurfaceComplexRestriction.curveToSurface_coefficient_app r θ)

#print axioms schemeDifferentialMap_D
#print axioms schemeDifferentialMap_ideal
#print axioms schemeDifferentialMap_unique
#print axioms schemeDifferentialMap_sectionLift
#print axioms literalCurveDifferentialMap

end CycleQ2GeometricSchemeDifferentialMap
end

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2GeometricSurfaceNormalCover

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry MvPolynomial
open CycleQ2GeometricAffineCurveCharts CycleQ2GeometricSurfaceAdjunction
open CycleQ2GeometricSurfaceCurveCharts CycleQ2GeometricSurfaceJacobianCharts
open CycleQ2GeometricSurfacePrincipalCurveCharts CycleQ2GeometricDehomogenizedCharts
open CycleQ2GeometricProjectiveCurve
open CycleQ2SeedTrace CycleQ2SeedCechTheta CycleQ2NormalConnecting
open CycleQ2GeometricSparseJacobianCover

def firstCurveEvaluation (r θ : ℂ) :
    CurveRing r θ →+* ChartRing ![firstQuadric r,firstCubic θ] :=
  (Ideal.quotientEquivAlgOfEq ℂ (congrArg chartIdeal (dehomogenizedEquations_one r θ))).toRingHom.comp
    (curveToDehomogenized r θ 1)

def secondCurveEvaluation (r θ : ℂ) :
    CurveRing r θ →+* ChartRing ![secondQuadric r,secondCubic θ] :=
  (Ideal.quotientEquivAlgOfEq ℂ (congrArg chartIdeal (dehomogenizedEquations_two r θ))).toRingHom.comp
    (curveToDehomogenized r θ 2)

@[simp] theorem firstCurveEvaluation_curveMap (r θ : ℂ) (p : Poly) :
    firstCurveEvaluation r θ (curveMap r θ p) =
      Ideal.Quotient.mk (chartIdeal ![firstQuadric r,firstCubic θ]) (firstDehomogenize p) := by
  change Ideal.quotientEquivAlgOfEq ℂ (congrArg chartIdeal (dehomogenizedEquations_one r θ))
    (Ideal.Quotient.mk _ (dehomogenize 1 p)) = _
  rw [Ideal.quotientEquivAlgOfEq_mk,dehomogenize_one]

@[simp] theorem secondCurveEvaluation_curveMap (r θ : ℂ) (p : Poly) :
    secondCurveEvaluation r θ (curveMap r θ p) =
      Ideal.Quotient.mk (chartIdeal ![secondQuadric r,secondCubic θ]) (secondDehomogenize p) := by
  change Ideal.quotientEquivAlgOfEq ℂ (congrArg chartIdeal (dehomogenizedEquations_two r θ))
    (Ideal.Quotient.mk _ (dehomogenize 2 p)) = _
  rw [Ideal.quotientEquivAlgOfEq_mk,dehomogenize_two]

theorem firstCurveEvaluation_ambient (r θ : ℂ) (p : WeightedPoly) :
    firstCurveEvaluation r θ (ambientCurveMap r θ p) =
      polynomialToCurve (firstQuadric r) (firstCubic θ) (firstSurfaceDehomogenize p) := by
  change firstCurveEvaluation r θ (curveMap r θ (substitute p)) = _
  rw [firstCurveEvaluation_curveMap,firstPolynomialToCurve_dehomogenize]

theorem secondCurveEvaluation_ambient (r θ : ℂ) (p : WeightedPoly) :
    secondCurveEvaluation r θ (ambientCurveMap r θ p) =
      polynomialToCurve (secondQuadric r) (secondCubic θ) (secondSurfaceDehomogenize p) := by
  change secondCurveEvaluation r θ (curveMap r θ (substitute p)) = _
  rw [secondCurveEvaluation_curveMap,secondPolynomialToCurve_dehomogenize]

/-- The original quartic denominators have no common prime on any actual
coordinate chart; its distinguished homogeneous coordinate maps to one. -/
theorem curveEvaluation_denominatorCover {B : Type} [CommRing B]
    (r θ : ℂ) (hr : r ≠ 0) (φ : CurveRing r θ →+* B)
    (i : Fin 4) (hi : φ (curveMap r θ (X i))=1)
    (P : Ideal B) [P.IsPrime] : φ (curveG1 r θ) ∉ P ∨ φ (curveG2 r θ) ∉ P := by
  let Q : Ideal (CurveRing r θ) := P.comap φ
  let : Q.IsPrime := Ideal.comap_isPrime _ _
  apply CycleQ2SeedTwoOpenCover.relevant_prime_cover r θ hr Q
  refine ⟨i,?_⟩
  change φ (curveMap r θ (X i)) ∉ P
  rw [hi]
  exact Ideal.IsPrime.one_notMem inferInstance

theorem first_denominatorCover (r θ : ℂ) (hr : r ≠ 0)
    (P : Ideal (ChartRing ![firstQuadric r,firstCubic θ])) [P.IsPrime] :
    polynomialToCurve (firstQuadric r) (firstCubic θ)
      (firstSurfaceDehomogenize (originalG1 r)) ∉ P ∨
    polynomialToCurve (firstQuadric r) (firstCubic θ)
      (firstSurfaceDehomogenize originalG2) ∉ P := by
  have hi : firstCurveEvaluation r θ (curveMap r θ (X 1))=1 := by
    rw [firstCurveEvaluation_curveMap]
    simp [firstDehomogenize]
  simpa only [curveG1,curveG2,firstCurveEvaluation_ambient] using
    curveEvaluation_denominatorCover r θ hr (firstCurveEvaluation r θ) 1 hi P

theorem second_denominatorCover (r θ : ℂ) (hr : r ≠ 0)
    (P : Ideal (ChartRing ![secondQuadric r,secondCubic θ])) [P.IsPrime] :
    polynomialToCurve (secondQuadric r) (secondCubic θ)
      (secondSurfaceDehomogenize (originalG1 r)) ∉ P ∨
    polynomialToCurve (secondQuadric r) (secondCubic θ)
      (secondSurfaceDehomogenize originalG2) ∉ P := by
  have hi : secondCurveEvaluation r θ (curveMap r θ (X 2))=1 := by
    rw [secondCurveEvaluation_curveMap]
    simp [secondDehomogenize]
  simpa only [curveG1,curveG2,secondCurveEvaluation_ambient] using
    curveEvaluation_denominatorCover r θ hr (secondCurveEvaluation r θ) 2 hi P

/-- The six actual first normal/Jacobian charts cover every prime of the
literal incidence curve chart. Both factors of each augmented minor are retained. -/
theorem first_normalPrimeCover
    (P : Ideal (ChartRing ![firstQuadric 57,firstCubic 1])) [P.IsPrime] :
    ∃ (i : Fin 2) (j : Fin 3), firstAffineCurveMap 57 1 (firstJacobian 57 1 i j) ∉ P := by
  obtain ⟨j,hj⟩ := CycleQ2GeometricIncidenceJacobianCover.first_chart_exists_minor_not_mem P inferInstance
  rcases first_denominatorCover 57 1 (by norm_num) P with hg | hg
  · refine ⟨1,j,?_⟩
    change surfaceToCurve _ _ _ _ _ (augmentedJacobian _ _ _) ∉ P
    rw [normalAugmentedJacobian_restriction]
    simp only [normalMultiplier,Matrix.cons_val_one,Matrix.cons_val_zero]
    intro hp
    rcases (inferInstance : P.IsPrime).mem_or_mem hp with hp | hp
    · exact hg hp
    · exact hj hp
  · refine ⟨0,j,?_⟩
    change surfaceToCurve _ _ _ _ _ (augmentedJacobian _ _ _) ∉ P
    rw [normalAugmentedJacobian_restriction]
    simp only [normalMultiplier,Matrix.cons_val_zero,map_neg]
    intro hp
    rcases (inferInstance : P.IsPrime).mem_or_mem hp with hp | hp
    · exact hg (P.neg_mem_iff.mp hp)
    · exact hj hp

/-- The second coordinate chart is covered by the same literal construction. -/
theorem second_normalPrimeCover
    (P : Ideal (ChartRing ![secondQuadric 57,secondCubic 1])) [P.IsPrime] :
    ∃ (i : Fin 2) (j : Fin 3), secondAffineCurveMap 57 1 (secondJacobian 57 1 i j) ∉ P := by
  obtain ⟨j,hj⟩ := CycleQ2GeometricIncidenceJacobianCover.second_chart_exists_minor_not_mem P inferInstance
  rcases second_denominatorCover 57 1 (by norm_num) P with hg | hg
  · refine ⟨1,j,?_⟩
    change surfaceToCurve _ _ _ _ _ (augmentedJacobian _ _ _) ∉ P
    rw [normalAugmentedJacobian_restriction]
    simp only [normalMultiplier,Matrix.cons_val_one,Matrix.cons_val_zero]
    intro hp
    rcases (inferInstance : P.IsPrime).mem_or_mem hp with hp | hp
    · exact hg hp
    · exact hj hp
  · refine ⟨0,j,?_⟩
    change surfaceToCurve _ _ _ _ _ (augmentedJacobian _ _ _) ∉ P
    rw [normalAugmentedJacobian_restriction]
    simp only [normalMultiplier,Matrix.cons_val_zero,map_neg]
    intro hp
    rcases (inferInstance : P.IsPrime).mem_or_mem hp with hp | hp
    · exact hg (P.neg_mem_iff.mp hp)
    · exact hj hp

#print axioms first_normalPrimeCover
#print axioms second_normalPrimeCover

section ActualOpenCover

variable {X : Scheme.{0}} {U : X.Opens} {A : Type} [CommRing A] [Algebra ℂ A]
  (e : U.toScheme ≅ Spec (CommRingCat.of A))

omit [Algebra ℂ A] in
theorem principalOpen_image (a : A) :
    principalOpen e a = (e.inv ≫ U.ι) ''ᵁ PrimeSpectrum.basicOpen a := by
  unfold principalOpen principalImmersion
  rw [Scheme.Hom.opensRange_comp,
    Scheme.Hom.opensRange_localizationAway (R := CommRingCat.of A) a]

theorem principalOpen_cover_two {ι κ : Type} (a : ι → κ → A)
    (h : (⨆ i, ⨆ j, PrimeSpectrum.basicOpen (a i j)) = ⊤) :
    (⨆ i, ⨆ j, principalOpen e (a i j)) = U := by
  simp_rw [principalOpen_image]
  rw [← Scheme.Hom.image_iSup₂,h,Scheme.Hom.image_top_eq_opensRange,
    Scheme.Hom.opensRange_comp_of_isIso,Scheme.Opens.opensRange_ι]

end ActualOpenCover

/-- The actual first normal-curve immersions cover the entire first
coordinate patch of the literal projective curve. -/
theorem first_normalOpen_cover :
    (⨆ i : Fin 2, ⨆ j : Fin 3, firstNormalCurveOpen 57 1 i j) =
      coordinateProjectivePatch 57 1 1 := by
  apply principalOpen_cover_two (CycleQ2GeometricAffineProjectiveCharts.firstAffineChart 57 1)
    (fun i j => firstAffineCurveMap 57 1 (firstJacobian 57 1 i j))
  apply top_unique
  intro P _
  obtain ⟨i,j,hj⟩ := first_normalPrimeCover P.asIdeal
  exact Opens.mem_iSup.mpr ⟨i,Opens.mem_iSup.mpr ⟨j,hj⟩⟩

theorem second_normalOpen_cover :
    (⨆ i : Fin 2, ⨆ j : Fin 3, secondNormalCurveOpen 57 1 i j) =
      coordinateProjectivePatch 57 1 2 := by
  apply principalOpen_cover_two (CycleQ2GeometricAffineProjectiveCharts.secondAffineChart 57 1)
    (fun i j => secondAffineCurveMap 57 1 (secondJacobian 57 1 i j))
  apply top_unique
  intro P _
  obtain ⟨i,j,hj⟩ := second_normalPrimeCover P.asIdeal
  exact Opens.mem_iSup.mpr ⟨i,Opens.mem_iSup.mpr ⟨j,hj⟩⟩

/-- All twelve actual Jacobian curve opens cover the literal projective
curve. The cover concerns the curve; no cover of the entire surface is asserted. -/
theorem normalOpen_cover :
    (⨆ i : Fin 2, ⨆ j : Fin 3, firstNormalCurveOpen 57 1 i j) ⊔
      (⨆ i : Fin 2, ⨆ j : Fin 3, secondNormalCurveOpen 57 1 i j) = ⊤ := by
  rw [first_normalOpen_cover,second_normalOpen_cover]
  exact CycleQ2GeometricProjectiveAffine.first_second_coordinate_cover 57 1 (by norm_num)

#print axioms first_normalOpen_cover
#print axioms second_normalOpen_cover
#print axioms normalOpen_cover

end CycleQ2GeometricSurfaceNormalCover
end

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2GeometricSurfaceNormalCover

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open CycleQ2GeometricLiteralSurface CycleQ2GeometricSurfaceJacobianCharts
open CycleQ2GeometricSurfacePrincipalCurveCharts

/-- The normal curve chart is the actual inverse image of its surface
chart, not merely an isomorphic affine scheme. -/
theorem firstNormalOpen_preimage (r θ : ℂ) (i : Fin 2) (j : Fin 3) :
    curveToSurface r θ ⁻¹ᵁ firstNormalOpen r θ i j =
      firstNormalCurveOpen r θ i j := by
  simpa only [Scheme.Hom.preimage_top,Scheme.Hom.image_top_eq_opensRange,
    firstNormalOpen,firstNormalCurveOpen,principalOpen] using
    (IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback
      (firstNormalCurve_isPullback r θ i j) ⊤).symm

theorem secondNormalOpen_preimage (r θ : ℂ) (i : Fin 2) (j : Fin 3) :
    curveToSurface r θ ⁻¹ᵁ secondNormalOpen r θ i j =
      secondNormalCurveOpen r θ i j := by
  simpa only [Scheme.Hom.preimage_top,Scheme.Hom.image_top_eq_opensRange,
    secondNormalOpen,secondNormalCurveOpen,principalOpen] using
    (IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback
      (secondNormalCurve_isPullback r θ i j) ⊤).symm

#print axioms firstNormalOpen_preimage
#print axioms secondNormalOpen_preimage

end CycleQ2GeometricSurfaceNormalCover
end

noncomputable section
namespace CycleQ2GeometricSurfaceNormalCover
open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open CycleQ2GeometricLiteralSurface CycleQ2GeometricSurfaceJacobianCharts
open CycleQ2GeometricSurfacePrincipalCurveCharts

/-- The actual surface chart family covers the closed curve after inverse
image. This is the support condition used for gluing intrinsic normal sections. -/
theorem normalSurfaceOpen_preimage_cover :
    (⨆ i : Fin 2, ⨆ j : Fin 3, curveToSurface 57 1 ⁻¹ᵁ firstNormalOpen 57 1 i j) ⊔
      (⨆ i : Fin 2, ⨆ j : Fin 3, curveToSurface 57 1 ⁻¹ᵁ secondNormalOpen 57 1 i j) = ⊤ := by
  simp_rw [firstNormalOpen_preimage,secondNormalOpen_preimage]
  exact normalOpen_cover

#print axioms normalSurfaceOpen_preimage_cover
end CycleQ2GeometricSurfaceNormalCover
end

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2GeometricNormalCharts
open CategoryTheory Opposite AlgebraicGeometry
open CycleQ2GeometricIntrinsicNormal CycleQ2GeometricLiteralSurface
open CycleQ2GeometricSurfaceCurveCharts CycleQ2GeometricProjectiveCurve
open CycleQ2GeometricSurfaceDehomogenizedCharts
open CycleQ2GeometricSurfaceAdjunction CycleQ2GeometricAffineCurveCharts
open CycleQ2SeedTrace CycleQ2SeedCechTheta CycleQ2NormalConnecting
open CycleQ2GeometricSeedNormalIdeals
open CycleQ2CartierProjectiveCover (coordinatePatch)
open scoped TensorProduct

/-- The two literal coordinate immersions used for evaluating intrinsic
normal sections. Their source rings are the original equation quotients. -/
abbrev firstSurfaceImmersion (r θ : ℂ) :=
  (CycleQ2GeometricSurfaceDehomogenizedCharts.firstAffineChart r θ).inv ≫
    (coordinatePatch r θ 1).ι

abbrev secondSurfaceImmersion (r θ : ℂ) :=
  (CycleQ2GeometricSurfaceDehomogenizedCharts.secondAffineChart r θ).inv ≫
    (coordinatePatch r θ 2).ι

abbrev firstCurveImmersion (r θ : ℂ) :=
  (CycleQ2GeometricAffineProjectiveCharts.firstAffineChart r θ).inv ≫
    (coordinateProjectivePatch r θ 1).ι

abbrev secondCurveImmersion (r θ : ℂ) :=
  (CycleQ2GeometricAffineProjectiveCharts.secondAffineChart r θ).inv ≫
    (coordinateProjectivePatch r θ 2).ι

@[simp] theorem firstSurfaceImmersion_range (r θ : ℂ) :
    (firstSurfaceImmersion r θ).opensRange = coordinatePatch r θ 1 := by
  rw [Scheme.Hom.opensRange_comp_of_isIso,
    Scheme.Opens.opensRange_ι]

@[simp] theorem secondSurfaceImmersion_range (r θ : ℂ) :
    (secondSurfaceImmersion r θ).opensRange = coordinatePatch r θ 2 := by
  rw [Scheme.Hom.opensRange_comp_of_isIso,
    Scheme.Opens.opensRange_ι]

/-- Reindexing a sheaf section along equality of actual open sets. -/
def sectionEqualityEquiv {Y : Scheme.{0}} (M : Y.Modules)
    {U V : Y.Opens} (h : U = V) :
    M.val.obj (op V) ≃ M.val.obj (op U) :=
  (M.val.presheaf.mapIso (eqToIso h).op).addCommGroupIsoToAddEquiv.toEquiv

@[simp] theorem sectionEqualityEquiv_apply {Y : Scheme.{0}} (M : Y.Modules)
    {U V : Y.Opens} (h : U = V) (s : M.val.obj (op V)) :
    sectionEqualityEquiv M h s = M.val.map (homOfLE h.le).op s := by
  subst V
  rfl

/-- Intrinsic normal sections on the actual first projective surface chart
are precisely the functionals on its actual base-changed conormal module. -/
def firstCoordinateNormalEquiv (r θ : ℂ) :
    letI : Algebra (SurfaceChartRing (firstEquations r θ))
      (ChartRing ![firstQuadric r, firstCubic θ]) :=
      (firstAffineCurveMap r θ).toRingHom.toAlgebra
    (normalDirectImageSheaf (curveToSurface r θ)).val.obj
      (op (coordinatePatch r θ 1)) ≃
    (ChartRing ![firstQuadric r, firstCubic θ] ⊗[SurfaceChartRing (firstEquations r θ)]
      (RingHom.ker (firstAffineCurveMap r θ).toRingHom).Cotangent →ₗ[
        ChartRing ![firstQuadric r, firstCubic θ]] ChartRing ![firstQuadric r, firstCubic θ]) := by
  letI : Algebra (SurfaceChartRing (firstEquations r θ))
    (ChartRing ![firstQuadric r, firstCubic θ]) :=
      (firstAffineCurveMap r θ).toRingHom.toAlgebra
  exact (sectionEqualityEquiv (normalDirectImageSheaf (curveToSurface r θ))
    (firstSurfaceImmersion_range r θ)).trans
    (normalOpenAlgebraConormalEquiv (CommRingCat.ofHom (firstAffineCurveMap r θ).toRingHom)
      (curveToSurface r θ) (firstSurfaceImmersion r θ) (firstCurveImmersion r θ)
      (firstAffineChart_isPullback r θ))

/-- The same intrinsic normal comparison on the second coordinate chart. -/
def secondCoordinateNormalEquiv (r θ : ℂ) :
    letI : Algebra (SurfaceChartRing (secondEquations r θ))
      (ChartRing ![secondQuadric r, secondCubic θ]) :=
      (secondAffineCurveMap r θ).toRingHom.toAlgebra
    (normalDirectImageSheaf (curveToSurface r θ)).val.obj
      (op (coordinatePatch r θ 2)) ≃
    (ChartRing ![secondQuadric r, secondCubic θ] ⊗[SurfaceChartRing (secondEquations r θ)]
      (RingHom.ker (secondAffineCurveMap r θ).toRingHom).Cotangent →ₗ[
        ChartRing ![secondQuadric r, secondCubic θ]] ChartRing ![secondQuadric r, secondCubic θ]) := by
  letI : Algebra (SurfaceChartRing (secondEquations r θ))
    (ChartRing ![secondQuadric r, secondCubic θ]) :=
      (secondAffineCurveMap r θ).toRingHom.toAlgebra
  exact (sectionEqualityEquiv (normalDirectImageSheaf (curveToSurface r θ))
    (secondSurfaceImmersion_range r θ)).trans
    (normalOpenAlgebraConormalEquiv (CommRingCat.ofHom (secondAffineCurveMap r θ).toRingHom)
      (curveToSurface r θ) (secondSurfaceImmersion r θ) (secondCurveImmersion r θ)
      (secondAffineChart_isPullback r θ))

#print axioms firstCoordinateNormalEquiv
#print axioms secondCoordinateNormalEquiv

section Evaluation
variable {X Y : Scheme.{0}} {A B : CommRingCat.{0}} (φ : A ⟶ B)
  (j : X ⟶ Y) (i : Spec A ⟶ Y) (k : Spec B ⟶ X)
  [IsOpenImmersion i] [IsOpenImmersion k]
  (H : IsPullback (Spec.map φ) k i j)

/-- Evaluate a genuine normal section on an ideal element represented in
an actual affine chart, then read the result in the original curve algebra. -/
def normalOpenIdealValue
    (f : (normalDirectImageSheaf j).val.obj (op i.opensRange))
    (a : RingHom.ker φ.hom) : B :=
  specTopRingEquiv B
    ((baseChangeStructureSectionIso j i k (Spec.map φ) H ⊤).hom
      (normalSectionEvaluate j (i ''ᵁ ⊤)
        ((normalDirectImageSheaf j).val.map
          (homOfLE (i.image_le_opensRange ⊤)).op f)
        (normalOpenIdealPullback j i k (Spec.map φ) H ⊤
          ((affineKernelSectionSemilinearEquiv φ).symm a))))

@[simp] theorem normalOpenAlgebraConormalEquiv_class
    (f : (normalDirectImageSheaf j).val.obj (op i.opensRange))
    (a : RingHom.ker φ.hom) :
    letI : Algebra A B := φ.hom.toAlgebra
    normalOpenAlgebraConormalEquiv φ j i k H f
      ((1 : B) ⊗ₜ[A] (RingHom.ker φ.hom).toCotangent a) =
      normalOpenIdealValue φ j i k H f a := by
  letI : Algebra A B := φ.hom.toAlgebra
  simpa only [one_mul, normalOpenIdealValue] using normalOpenAlgebraConormalEquiv_tmul φ j i k H f 1 a

#print axioms normalOpenAlgebraConormalEquiv_class

end Evaluation

section SymbolicNormalChart
variable (q h : AffinePoly) (g₁ g₂ k : SurfacePoly) (n : Fin 2) (t : Fin 3)
variable {X Y : Scheme.{0}} (j : X ⟶ Y)
  (iS : Spec (CommRingCat.of (NormalSurfacePatch q h g₁ g₂ k n t)) ⟶ Y)
  (iC : Spec (CommRingCat.of (NormalCurvePatch q h g₁ g₂ k n t)) ⟶ X)
  [IsOpenImmersion iS] [IsOpenImmersion iC]
  (H : IsPullback (Spec.map (CommRingCat.ofHom (normalChartMap q h g₁ g₂ k n t).toRingHom))
    iC iS j)

/-- The conormal dual in the local adjunction theorem is the actual normal
sheaf on any proved affine normal-chart square. The ring comparison is made
at symbolic polynomial parameters before specializing the projective charts. -/
def normalChartIntrinsicEquiv :
    (normalDirectImageSheaf j).val.obj (op iS.opensRange) ≃
      (NormalConormal q h g₁ g₂ k n t →ₗ[NormalCurvePatch q h g₁ g₂ k n t]
        NormalCurvePatch q h g₁ g₂ k n t) :=
  normalOpenAlgebraConormalEquiv
    (CommRingCat.ofHom (normalChartMap q h g₁ g₂ k n t).toRingHom) j iS iC H

#print axioms normalChartIntrinsicEquiv

/-- A literal defining equation as an element of the local curve ideal. -/
def normalChartIdealEquation (a : Fin 2) :
    RingHom.ker (normalChartMap q h g₁ g₂ k n t).toRingHom :=
  ⟨algebraMap SurfacePoly (NormalSurfacePatch q h g₁ g₂ k n t) (normalPolynomial q a),
    normalEquation_mem q h g₁ g₂ k n t a⟩

/-- Actual normal-sheaf evaluation, normalized only through the chart's
structure-ring isomorphisms, on either defining equation. -/
def normalChartEquationValue
    (f : (normalDirectImageSheaf j).val.obj (op iS.opensRange)) (a : Fin 2) :
    NormalCurvePatch q h g₁ g₂ k n t :=
  normalOpenIdealValue (CommRingCat.ofHom (normalChartMap q h g₁ g₂ k n t).toRingHom)
    j iS iC H f (normalChartIdealEquation q h g₁ g₂ k n t a)

@[simp] theorem normalChartIntrinsicEquiv_equation
    (f : (normalDirectImageSheaf j).val.obj (op iS.opensRange)) (a : Fin 2) :
    normalChartIntrinsicEquiv q h g₁ g₂ k n t j iS iC H f
      (normalEquationClass q h g₁ g₂ k n t a) =
      normalChartEquationValue q h g₁ g₂ k n t j iS iC H f a := by
  exact normalOpenAlgebraConormalEquiv_class
    (CommRingCat.ofHom (normalChartMap q h g₁ g₂ k n t).toRingHom)
    j iS iC H f (normalChartIdealEquation q h g₁ g₂ k n t a)

#print axioms normalChartIntrinsicEquiv_equation

theorem normalChartIntrinsic_ext
    (f g : (normalDirectImageSheaf j).val.obj (op iS.opensRange))
    (hfg : ∀ a, normalChartEquationValue q h g₁ g₂ k n t j iS iC H f a =
      normalChartEquationValue q h g₁ g₂ k n t j iS iC H g a) : f = g := by
  apply (normalChartIntrinsicEquiv q h g₁ g₂ k n t j iS iC H).injective
  apply LinearMap.ext_on (normalEquationClasses_span q h g₁ g₂ k n t)
  rintro x ⟨a, rfl⟩
  exact (normalChartIntrinsicEquiv_equation q h g₁ g₂ k n t j iS iC H f a).trans
    ((hfg a).trans (normalChartIntrinsicEquiv_equation q h g₁ g₂ k n t j iS iC H g a).symm)

def normalChartVectorSection :
    (normalDirectImageSheaf j).val.obj (op iS.opensRange) :=
  (normalChartIntrinsicEquiv q h g₁ g₂ k n t j iS iC H).symm
    (normalVector q h g₁ g₂ k n t)

@[simp] theorem normalChartVectorSection_equation (a : Fin 2) :
    normalChartEquationValue q h g₁ g₂ k n t j iS iC H
      (normalChartVectorSection q h g₁ g₂ k n t j iS iC H) a =
      ![normalCoefficientMap q h g₁ g₂ k n t g₂,
        -normalCoefficientMap q h g₁ g₂ k n t g₁] a := by
  rw [← normalChartIntrinsicEquiv_equation, normalChartVectorSection, Equiv.apply_symm_apply]
  exact normalVector_equation q h g₁ g₂ k n t a

theorem normalChartVectorSection_unique
    (f : (normalDirectImageSheaf j).val.obj (op iS.opensRange))
    (hf : ∀ a, normalChartEquationValue q h g₁ g₂ k n t j iS iC H f a =
      ![normalCoefficientMap q h g₁ g₂ k n t g₂,
        -normalCoefficientMap q h g₁ g₂ k n t g₁] a) :
    f = normalChartVectorSection q h g₁ g₂ k n t j iS iC H := by
  apply (normalChartIntrinsicEquiv q h g₁ g₂ k n t j iS iC H).injective
  rw [normalChartVectorSection, Equiv.apply_symm_apply]
  apply normalVector_unique q h g₁ g₂ k n t
  intro a
  exact (normalChartIntrinsicEquiv_equation q h g₁ g₂ k n t j iS iC H f a).trans (hf a)

#print axioms normalChartIntrinsic_ext
#print axioms normalChartVectorSection_equation
#print axioms normalChartVectorSection_unique
end SymbolicNormalChart

open CycleQ2GeometricSurfaceJacobianCharts CycleQ2GeometricSurfacePrincipalCurveCharts

/-- The actual surface normal chart, with the local adjunction ring exposed
in its type so all downstream normal comparisons share the same scalars. -/
def firstNormalSurfaceImmersion (r θ : ℂ) (i : Fin 2) (j : Fin 3) :
    Spec (CommRingCat.of (FirstNormalRing r θ i j)) ⟶ surface r θ :=
  principalImmersion (CycleQ2GeometricSurfaceDehomogenizedCharts.firstAffineChart r θ)
    (firstJacobian r θ i j)

instance firstNormalSurfaceImmersion_isOpenImmersion (r θ : ℂ) (i : Fin 2) (j : Fin 3) :
    IsOpenImmersion (firstNormalSurfaceImmersion r θ i j) := by
  dsimp [firstNormalSurfaceImmersion]
  infer_instance

@[simp] theorem firstNormalSurfaceImmersion_range (r θ : ℂ) (i : Fin 2) (j : Fin 3) :
    (firstNormalSurfaceImmersion r θ i j).opensRange = firstNormalOpen r θ i j := rfl

abbrev FirstNormalConormal (r θ : ℂ) (i : Fin 2) (j : Fin 3) :=
  NormalConormal (firstQuadric r) (firstCubic θ)
    (firstSurfaceDehomogenize (originalG1 r)) (firstSurfaceDehomogenize originalG2)
    (firstSurfaceDehomogenize (thetaK θ)) i j

/-- On this actual projective Jacobian open, intrinsic normal sections are
the exact conormal dual used by the local adjunction isomorphism. -/
def firstNormalSectionEquiv (r θ : ℂ) (i : Fin 2) (j : Fin 3) :
    (normalDirectImageSheaf (curveToSurface r θ)).val.obj (op (firstNormalOpen r θ i j)) ≃
      (FirstNormalConormal r θ i j →ₗ[FirstNormalCurveRing r θ i j]
        FirstNormalCurveRing r θ i j) :=
  normalChartIntrinsicEquiv (firstQuadric r) (firstCubic θ)
    (firstSurfaceDehomogenize (originalG1 r)) (firstSurfaceDehomogenize originalG2)
    (firstSurfaceDehomogenize (thetaK θ)) i j
    (curveToSurface r θ) (firstNormalSurfaceImmersion r θ i j)
    (firstNormalCurveImmersion r θ i j) (firstNormalCurve_isPullback r θ i j)

def firstNormalIdealEquation (r θ : ℂ) (i : Fin 2) (j : Fin 3) (a : Fin 2) :
    RingHom.ker (firstNormalCurveMap r θ i j).toRingHom :=
  normalChartIdealEquation (firstQuadric r) (firstCubic θ)
    (firstSurfaceDehomogenize (originalG1 r)) (firstSurfaceDehomogenize originalG2)
    (firstSurfaceDehomogenize (thetaK θ)) i j a

/-- Actual sheaf evaluation on either literal defining equation, expressed
in the original affine curve algebra through its actual chart isomorphism. -/
def firstNormalEquationValue (r θ : ℂ) (i : Fin 2) (j : Fin 3)
    (f : (normalDirectImageSheaf (curveToSurface r θ)).val.obj
      (op (firstNormalOpen r θ i j))) (a : Fin 2) : FirstNormalCurveRing r θ i j :=
  normalChartEquationValue (firstQuadric r) (firstCubic θ)
    (firstSurfaceDehomogenize (originalG1 r)) (firstSurfaceDehomogenize originalG2)
    (firstSurfaceDehomogenize (thetaK θ)) i j
    (curveToSurface r θ) (firstNormalSurfaceImmersion r θ i j)
    (firstNormalCurveImmersion r θ i j) (firstNormalCurve_isPullback r θ i j) f a

@[simp] theorem firstNormalSectionEquiv_equation (r θ : ℂ) (i : Fin 2) (j : Fin 3)
    (f : (normalDirectImageSheaf (curveToSurface r θ)).val.obj
      (op (firstNormalOpen r θ i j))) (a : Fin 2) :
    firstNormalSectionEquiv r θ i j f
      (normalEquationClass (firstQuadric r) (firstCubic θ)
    (firstSurfaceDehomogenize (originalG1 r)) (firstSurfaceDehomogenize originalG2)
    (firstSurfaceDehomogenize (thetaK θ)) i j a) =
      firstNormalEquationValue r θ i j f a :=
  normalChartIntrinsicEquiv_equation (firstQuadric r) (firstCubic θ)
    (firstSurfaceDehomogenize (originalG1 r)) (firstSurfaceDehomogenize originalG2)
    (firstSurfaceDehomogenize (thetaK θ)) i j
    (curveToSurface r θ) (firstNormalSurfaceImmersion r θ i j)
    (firstNormalCurveImmersion r θ i j) (firstNormalCurve_isPullback r θ i j) f a

theorem firstNormalSection_ext (r θ : ℂ) (i : Fin 2) (j : Fin 3)
    (f g : (normalDirectImageSheaf (curveToSurface r θ)).val.obj
      (op (firstNormalOpen r θ i j)))
    (hfg : ∀ a, firstNormalEquationValue r θ i j f a =
      firstNormalEquationValue r θ i j g a) : f = g :=
  normalChartIntrinsic_ext (firstQuadric r) (firstCubic θ)
    (firstSurfaceDehomogenize (originalG1 r)) (firstSurfaceDehomogenize originalG2)
    (firstSurfaceDehomogenize (thetaK θ)) i j
    (curveToSurface r θ) (firstNormalSurfaceImmersion r θ i j)
    (firstNormalCurveImmersion r θ i j) (firstNormalCurve_isPullback r θ i j) f g hfg

/-- The literal polynomial normal vector (G₂, −G₁), as a section of the
intrinsic normal sheaf on the actual projective Jacobian open. -/
def firstNormalVectorSection (r θ : ℂ) (i : Fin 2) (j : Fin 3) :
    (normalDirectImageSheaf (curveToSurface r θ)).val.obj (op (firstNormalOpen r θ i j)) :=
  normalChartVectorSection (firstQuadric r) (firstCubic θ)
    (firstSurfaceDehomogenize (originalG1 r)) (firstSurfaceDehomogenize originalG2)
    (firstSurfaceDehomogenize (thetaK θ)) i j
    (curveToSurface r θ) (firstNormalSurfaceImmersion r θ i j)
    (firstNormalCurveImmersion r θ i j) (firstNormalCurve_isPullback r θ i j)

@[simp] theorem firstNormalVectorSection_equation (r θ : ℂ)
    (i : Fin 2) (j : Fin 3) (a : Fin 2) :
    firstNormalEquationValue r θ i j (firstNormalVectorSection r θ i j) a =
      ![normalCoefficientMap (firstQuadric r) (firstCubic θ)
    (firstSurfaceDehomogenize (originalG1 r)) (firstSurfaceDehomogenize originalG2)
    (firstSurfaceDehomogenize (thetaK θ)) i j (firstSurfaceDehomogenize originalG2),
        -normalCoefficientMap (firstQuadric r) (firstCubic θ)
    (firstSurfaceDehomogenize (originalG1 r)) (firstSurfaceDehomogenize originalG2)
    (firstSurfaceDehomogenize (thetaK θ)) i j (firstSurfaceDehomogenize (originalG1 r))] a :=
  normalChartVectorSection_equation (firstQuadric r) (firstCubic θ)
    (firstSurfaceDehomogenize (originalG1 r)) (firstSurfaceDehomogenize originalG2)
    (firstSurfaceDehomogenize (thetaK θ)) i j
    (curveToSurface r θ) (firstNormalSurfaceImmersion r θ i j)
    (firstNormalCurveImmersion r θ i j) (firstNormalCurve_isPullback r θ i j) a

theorem firstNormalVectorSection_unique (r θ : ℂ) (i : Fin 2) (j : Fin 3)
    (f : (normalDirectImageSheaf (curveToSurface r θ)).val.obj
      (op (firstNormalOpen r θ i j)))
    (hf : ∀ a, firstNormalEquationValue r θ i j f a =
      ![normalCoefficientMap (firstQuadric r) (firstCubic θ)
    (firstSurfaceDehomogenize (originalG1 r)) (firstSurfaceDehomogenize originalG2)
    (firstSurfaceDehomogenize (thetaK θ)) i j (firstSurfaceDehomogenize originalG2),
        -normalCoefficientMap (firstQuadric r) (firstCubic θ)
    (firstSurfaceDehomogenize (originalG1 r)) (firstSurfaceDehomogenize originalG2)
    (firstSurfaceDehomogenize (thetaK θ)) i j (firstSurfaceDehomogenize (originalG1 r))] a) :
    f = firstNormalVectorSection r θ i j :=
  normalChartVectorSection_unique (firstQuadric r) (firstCubic θ)
    (firstSurfaceDehomogenize (originalG1 r)) (firstSurfaceDehomogenize originalG2)
    (firstSurfaceDehomogenize (thetaK θ)) i j
    (curveToSurface r θ) (firstNormalSurfaceImmersion r θ i j)
    (firstNormalCurveImmersion r θ i j) (firstNormalCurve_isPullback r θ i j) f hf

#print axioms firstNormalSectionEquiv
#print axioms firstNormalSectionEquiv_equation
#print axioms firstNormalSection_ext
#print axioms firstNormalVectorSection_equation
#print axioms firstNormalVectorSection_unique

/-- The actual surface normal chart, with the local adjunction ring exposed
in its type so all downstream normal comparisons share the same scalars. -/
def secondNormalSurfaceImmersion (r θ : ℂ) (i : Fin 2) (j : Fin 3) :
    Spec (CommRingCat.of (SecondNormalRing r θ i j)) ⟶ surface r θ :=
  principalImmersion (CycleQ2GeometricSurfaceDehomogenizedCharts.secondAffineChart r θ)
    (secondJacobian r θ i j)

instance secondNormalSurfaceImmersion_isOpenImmersion (r θ : ℂ) (i : Fin 2) (j : Fin 3) :
    IsOpenImmersion (secondNormalSurfaceImmersion r θ i j) := by
  dsimp [secondNormalSurfaceImmersion]
  infer_instance

@[simp] theorem secondNormalSurfaceImmersion_range (r θ : ℂ) (i : Fin 2) (j : Fin 3) :
    (secondNormalSurfaceImmersion r θ i j).opensRange = secondNormalOpen r θ i j := rfl

abbrev SecondNormalConormal (r θ : ℂ) (i : Fin 2) (j : Fin 3) :=
  NormalConormal (secondQuadric r) (secondCubic θ)
    (secondSurfaceDehomogenize (originalG1 r)) (secondSurfaceDehomogenize originalG2)
    (secondSurfaceDehomogenize (thetaK θ)) i j

/-- On this actual projective Jacobian open, intrinsic normal sections are
the exact conormal dual used by the local adjunction isomorphism. -/
def secondNormalSectionEquiv (r θ : ℂ) (i : Fin 2) (j : Fin 3) :
    (normalDirectImageSheaf (curveToSurface r θ)).val.obj (op (secondNormalOpen r θ i j)) ≃
      (SecondNormalConormal r θ i j →ₗ[SecondNormalCurveRing r θ i j]
        SecondNormalCurveRing r θ i j) :=
  normalChartIntrinsicEquiv (secondQuadric r) (secondCubic θ)
    (secondSurfaceDehomogenize (originalG1 r)) (secondSurfaceDehomogenize originalG2)
    (secondSurfaceDehomogenize (thetaK θ)) i j
    (curveToSurface r θ) (secondNormalSurfaceImmersion r θ i j)
    (secondNormalCurveImmersion r θ i j) (secondNormalCurve_isPullback r θ i j)

def secondNormalIdealEquation (r θ : ℂ) (i : Fin 2) (j : Fin 3) (a : Fin 2) :
    RingHom.ker (secondNormalCurveMap r θ i j).toRingHom :=
  normalChartIdealEquation (secondQuadric r) (secondCubic θ)
    (secondSurfaceDehomogenize (originalG1 r)) (secondSurfaceDehomogenize originalG2)
    (secondSurfaceDehomogenize (thetaK θ)) i j a

/-- Actual sheaf evaluation on either literal defining equation, expressed
in the original affine curve algebra through its actual chart isomorphism. -/
def secondNormalEquationValue (r θ : ℂ) (i : Fin 2) (j : Fin 3)
    (f : (normalDirectImageSheaf (curveToSurface r θ)).val.obj
      (op (secondNormalOpen r θ i j))) (a : Fin 2) : SecondNormalCurveRing r θ i j :=
  normalChartEquationValue (secondQuadric r) (secondCubic θ)
    (secondSurfaceDehomogenize (originalG1 r)) (secondSurfaceDehomogenize originalG2)
    (secondSurfaceDehomogenize (thetaK θ)) i j
    (curveToSurface r θ) (secondNormalSurfaceImmersion r θ i j)
    (secondNormalCurveImmersion r θ i j) (secondNormalCurve_isPullback r θ i j) f a

@[simp] theorem secondNormalSectionEquiv_equation (r θ : ℂ) (i : Fin 2) (j : Fin 3)
    (f : (normalDirectImageSheaf (curveToSurface r θ)).val.obj
      (op (secondNormalOpen r θ i j))) (a : Fin 2) :
    secondNormalSectionEquiv r θ i j f
      (normalEquationClass (secondQuadric r) (secondCubic θ)
    (secondSurfaceDehomogenize (originalG1 r)) (secondSurfaceDehomogenize originalG2)
    (secondSurfaceDehomogenize (thetaK θ)) i j a) =
      secondNormalEquationValue r θ i j f a :=
  normalChartIntrinsicEquiv_equation (secondQuadric r) (secondCubic θ)
    (secondSurfaceDehomogenize (originalG1 r)) (secondSurfaceDehomogenize originalG2)
    (secondSurfaceDehomogenize (thetaK θ)) i j
    (curveToSurface r θ) (secondNormalSurfaceImmersion r θ i j)
    (secondNormalCurveImmersion r θ i j) (secondNormalCurve_isPullback r θ i j) f a

theorem secondNormalSection_ext (r θ : ℂ) (i : Fin 2) (j : Fin 3)
    (f g : (normalDirectImageSheaf (curveToSurface r θ)).val.obj
      (op (secondNormalOpen r θ i j)))
    (hfg : ∀ a, secondNormalEquationValue r θ i j f a =
      secondNormalEquationValue r θ i j g a) : f = g :=
  normalChartIntrinsic_ext (secondQuadric r) (secondCubic θ)
    (secondSurfaceDehomogenize (originalG1 r)) (secondSurfaceDehomogenize originalG2)
    (secondSurfaceDehomogenize (thetaK θ)) i j
    (curveToSurface r θ) (secondNormalSurfaceImmersion r θ i j)
    (secondNormalCurveImmersion r θ i j) (secondNormalCurve_isPullback r θ i j) f g hfg

/-- The literal polynomial normal vector (G₂, −G₁), as a section of the
intrinsic normal sheaf on the actual projective Jacobian open. -/
def secondNormalVectorSection (r θ : ℂ) (i : Fin 2) (j : Fin 3) :
    (normalDirectImageSheaf (curveToSurface r θ)).val.obj (op (secondNormalOpen r θ i j)) :=
  normalChartVectorSection (secondQuadric r) (secondCubic θ)
    (secondSurfaceDehomogenize (originalG1 r)) (secondSurfaceDehomogenize originalG2)
    (secondSurfaceDehomogenize (thetaK θ)) i j
    (curveToSurface r θ) (secondNormalSurfaceImmersion r θ i j)
    (secondNormalCurveImmersion r θ i j) (secondNormalCurve_isPullback r θ i j)

@[simp] theorem secondNormalVectorSection_equation (r θ : ℂ)
    (i : Fin 2) (j : Fin 3) (a : Fin 2) :
    secondNormalEquationValue r θ i j (secondNormalVectorSection r θ i j) a =
      ![normalCoefficientMap (secondQuadric r) (secondCubic θ)
    (secondSurfaceDehomogenize (originalG1 r)) (secondSurfaceDehomogenize originalG2)
    (secondSurfaceDehomogenize (thetaK θ)) i j (secondSurfaceDehomogenize originalG2),
        -normalCoefficientMap (secondQuadric r) (secondCubic θ)
    (secondSurfaceDehomogenize (originalG1 r)) (secondSurfaceDehomogenize originalG2)
    (secondSurfaceDehomogenize (thetaK θ)) i j (secondSurfaceDehomogenize (originalG1 r))] a :=
  normalChartVectorSection_equation (secondQuadric r) (secondCubic θ)
    (secondSurfaceDehomogenize (originalG1 r)) (secondSurfaceDehomogenize originalG2)
    (secondSurfaceDehomogenize (thetaK θ)) i j
    (curveToSurface r θ) (secondNormalSurfaceImmersion r θ i j)
    (secondNormalCurveImmersion r θ i j) (secondNormalCurve_isPullback r θ i j) a

theorem secondNormalVectorSection_unique (r θ : ℂ) (i : Fin 2) (j : Fin 3)
    (f : (normalDirectImageSheaf (curveToSurface r θ)).val.obj
      (op (secondNormalOpen r θ i j)))
    (hf : ∀ a, secondNormalEquationValue r θ i j f a =
      ![normalCoefficientMap (secondQuadric r) (secondCubic θ)
    (secondSurfaceDehomogenize (originalG1 r)) (secondSurfaceDehomogenize originalG2)
    (secondSurfaceDehomogenize (thetaK θ)) i j (secondSurfaceDehomogenize originalG2),
        -normalCoefficientMap (secondQuadric r) (secondCubic θ)
    (secondSurfaceDehomogenize (originalG1 r)) (secondSurfaceDehomogenize originalG2)
    (secondSurfaceDehomogenize (thetaK θ)) i j (secondSurfaceDehomogenize (originalG1 r))] a) :
    f = secondNormalVectorSection r θ i j :=
  normalChartVectorSection_unique (secondQuadric r) (secondCubic θ)
    (secondSurfaceDehomogenize (originalG1 r)) (secondSurfaceDehomogenize originalG2)
    (secondSurfaceDehomogenize (thetaK θ)) i j
    (curveToSurface r θ) (secondNormalSurfaceImmersion r θ i j)
    (secondNormalCurveImmersion r θ i j) (secondNormalCurve_isPullback r θ i j) f hf

#print axioms secondNormalSectionEquiv
#print axioms secondNormalSectionEquiv_equation
#print axioms secondNormalSection_ext
#print axioms secondNormalVectorSection_equation
#print axioms secondNormalVectorSection_unique

end CycleQ2GeometricNormalCharts
end

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2GeometricIntrinsicNormal
open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
  CycleQ2GeometricDifferentialSheaf

variable {X Y : Scheme.{0}} (j : X ⟶ Y)

/-- The intrinsic normal direct image vanishes on every open whose
preimage in the curve is empty. -/
theorem normalSections_subsingleton_of_preimage_eq_bot (U : Y.Opens)
    (hU : j ⁻¹ᵁ U = ⊥) :
    Subsingleton ((normalDirectImageSheaf j).val.obj (op U)) := by
  constructor
  intro f g
  apply Subtype.ext
  apply NatTrans.ext
  funext V
  apply ConcreteCategory.hom_ext
  intro m
  have hV : j ⁻¹ᵁ V.unop.left = ⊥ := by
    apply le_antisymm
    · exact (show j ⁻¹ᵁ V.unop.left ≤ j ⁻¹ᵁ U from
        fun _ hx => V.unop.hom.le hx).trans (le_of_eq hU)
    · exact bot_le
  have hsub : Subsingleton ((imageStructureModule j).val.obj (op V.unop.left)) := by
    change Subsingleton Γ(X, j ⁻¹ᵁ V.unop.left)
    rw [hV]
    infer_instance
  exact hsub.elim _ _

section Closed
variable [IsClosedImmersion j]

/-- The actual open complement of the closed immersion's image. -/
def closedImageComplement : Y.Opens :=
  ⟨(Set.range j)ᶜ, j.isClosedEmbedding.isClosed_range.isOpen_compl⟩

@[simp] theorem preimage_closedImageComplement : j ⁻¹ᵁ closedImageComplement j = ⊥ := by
  ext x
  change (j x ∉ Set.range j) ↔ False
  simp

/-- Covering the curve preimage is sufficient for gluing intrinsic normal
sections on a surface open. The proof adds the complement of the closed
image, where the actual normal sheaf is zero. -/
theorem existsUnique_normalGluing_of_preimage_cover
    {ι : Type} (U : Y.Opens) (V : ι → Y.Opens) (hVU : ∀ a, V a ≤ U)
    (hcover : j ⁻¹ᵁ U ≤ ⨆ a, j ⁻¹ᵁ V a)
    (s : ∀ a, (normalDirectImageSheaf j).val.obj (op (V a)))
    (hs : ∀ a b,
      (normalDirectImageSheaf j).val.map (homOfLE (show V a ⊓ V b ≤ V a from inf_le_left)).op
        (s a) =
      (normalDirectImageSheaf j).val.map (homOfLE (show V a ⊓ V b ≤ V b from inf_le_right)).op
        (s b)) :
    ∃! t : (normalDirectImageSheaf j).val.obj (op U),
      ∀ a, (normalDirectImageSheaf j).val.map (homOfLE (hVU a)).op t = s a := by
  let M := normalDirectImageSheaf j
  let F : Y.carrier.Sheaf AddCommGrpCat.{0} :=
    (SheafOfModules.toSheaf (ringSheaf Y.sheaf)).obj M
  let W := U ⊓ closedImageComplement j
  have hW : j ⁻¹ᵁ W = ⊥ := by
    apply le_antisymm
    · exact (show j ⁻¹ᵁ W ≤ j ⁻¹ᵁ closedImageComplement j from
        fun _ hx => hx.2).trans (le_of_eq (preimage_closedImageComplement j))
    · exact bot_le
  let B : Option ι → Y.Opens := fun a => match a with | none => W | some a => V a
  let st : ∀ a, M.val.obj (op (B a)) := fun a => by
    cases a with
    | none => exact 0
    | some a => exact s a
  have hBU : ∀ a, B a ≤ U := by
    rintro (_ | a)
    · exact inf_le_left
    · exact hVU a
  have hB : U ≤ iSup B := by
    intro y hy
    by_cases h : y ∈ Set.range j
    · obtain ⟨x, rfl⟩ := h
      have hx := hcover hy
      rw [Opens.mem_iSup] at hx
      obtain ⟨a, ha⟩ := hx
      exact (le_iSup B (some a)) ha
    · exact (le_iSup B none) ⟨hy, h⟩
  have hcompat : TopCat.Presheaf.IsCompatible F.obj B st := by
    rintro (_ | a) (_ | b)
    · rfl
    · have hsub := normalSections_subsingleton_of_preimage_eq_bot j (W ⊓ V b)
        (le_antisymm ((show j ⁻¹ᵁ (W ⊓ V b) ≤ j ⁻¹ᵁ W from
          fun _ hx => hx.1).trans (le_of_eq hW)) bot_le)
      exact hsub.elim _ _
    · have hsub := normalSections_subsingleton_of_preimage_eq_bot j (V a ⊓ W)
        (le_antisymm ((show j ⁻¹ᵁ (V a ⊓ W) ≤ j ⁻¹ᵁ W from
          fun _ hx => hx.2).trans (le_of_eq hW)) bot_le)
      exact hsub.elim _ _
    · exact hs a b
  obtain ⟨t, ht, hu⟩ := F.existsUnique_gluing' B U (fun a => homOfLE (hBU a)) hB st hcompat
  refine ⟨t, fun a => ht (some a), ?_⟩
  intro t' ht'
  apply hu t'
  rintro (_ | a)
  · exact (normalSections_subsingleton_of_preimage_eq_bot j W hW).elim _ _
  · exact ht' a

#print axioms normalSections_subsingleton_of_preimage_eq_bot
#print axioms existsUnique_normalGluing_of_preimage_cover
end Closed
end CycleQ2GeometricIntrinsicNormal
end
