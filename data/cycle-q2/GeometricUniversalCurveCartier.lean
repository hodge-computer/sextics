import Proposal.GeometricUniversalCurveSection
import Proposal.GeometricGradedCechDescent
import Proposal.GeometricIncidenceEtaleParameter
import Mathlib.RingTheory.MvPolynomial.Localization

/-!
# Cartier charts of the actual universal incidence curve

The nine original matrix entries define projective opens of the original
surface over `S[T0,T1,T2]`. On each such open, the equation is the actual
degree-zero fraction `(M*T)i / Mij`. The ordinary localization is compared
with a polynomial ring over the corresponding original surface localization;
its regular linear equation then descends to the genuine degree-zero chart.

This establishes local regular principal equations for the original closed
immersion. It does not assert flatness over the section-parameter base:
the zero section parameter still has the whole surface as its fiber.

The geometric strategy is due to Ben Diamond and the cited work of Claire
Voisin. Prepared for fqlx with OpenAI ChatGPT assistance.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2UniversalCurveCartier

open CategoryTheory AlgebraicGeometry MvPolynomial Matrix HomogeneousLocalization
open CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations
  CycleQ2IncidenceUniversalChart CycleQ2IncidenceImageLine
  CycleQ2GeometricIncidenceProj CycleQ2IncidenceGenericPointSemantics
  CycleQ2IncidencePolynomialRelations CycleQ2IncidenceCoefficientRelations
  CycleQ2SegreGenericSection CycleQ2GenericLinearSection
  CycleQ2UniversalCurveSection CycleQ2GradedLocalizationProjection

attribute [local instance] MvPolynomial.algebraMvPolynomial

variable {S : Type} [CommRing S] [Algebra ℂ S]

local instance pointCommRing (y : ParameterIndex → S) : CommRing (PointSurface y) := inferInstance
local instance curveCommRing (y : ParameterIndex → S) : CommRing (GenericCurveRing y) := inferInstance

/-! ## The unchanged surface before imposing the section equation -/

def surfaceCoefficientExtension (y : ParameterIndex → S) :
    PointSurface y →+* PointSurface (sectionPoint y) :=
  Ideal.Quotient.lift (pointEquations y)
    ((Ideal.Quotient.mk (pointEquations (sectionPoint y))).comp
      (MvPolynomial.map (C : S →+* SectionBase S))) (by
        intro p hp
        apply Ideal.Quotient.eq_zero_iff_mem.mpr
        rw [← pointEquations_sectionPoint y]
        exact Ideal.mem_map_of_mem _ hp)

@[simp] theorem surfaceCoefficientExtension_mk (y : ParameterIndex → S)
    (p : MvPolynomial (Fin 5) S) :
    surfaceCoefficientExtension y (Ideal.Quotient.mk (pointEquations y) p) =
      Ideal.Quotient.mk (pointEquations (sectionPoint y))
        (MvPolynomial.map (C : S →+* SectionBase S) p) := rfl

def fromSurfacePolynomial (y : ParameterIndex → S) :
    SectionPolynomial y →+* PointSurface (sectionPoint y) :=
  MvPolynomial.eval₂Hom (surfaceCoefficientExtension y)
    (fun j => Ideal.Quotient.mk (pointEquations (sectionPoint y))
      (C (X j : SectionBase S)))

@[simp] theorem fromSurfacePolynomial_C (y : ParameterIndex → S) (a : PointSurface y) :
    fromSurfacePolynomial y (C a) = surfaceCoefficientExtension y a := by
  simp [fromSurfacePolynomial]

@[simp] theorem fromSurfacePolynomial_X (y : ParameterIndex → S) (j : Fin 3) :
    fromSurfacePolynomial y (X j) =
      Ideal.Quotient.mk (pointEquations (sectionPoint y))
        (C (X j : SectionBase S)) := by
  simp [fromSurfacePolynomial]

def toSurfacePolynomial (y : ParameterIndex → S) :
    PointSurface (sectionPoint y) →+* SectionPolynomial y :=
  Ideal.Quotient.lift (pointEquations (sectionPoint y)) (toSectionPolynomial y) (by
    intro p hp
    have hm := Ideal.mem_map_of_mem (toSectionPolynomial y) hp
    rw [toSectionPolynomial_pointEquations y] at hm
    exact hm)

@[simp] theorem toSurfacePolynomial_mk (y : ParameterIndex → S)
    (p : MvPolynomial (Fin 5) (SectionBase S)) :
    toSurfacePolynomial y (Ideal.Quotient.mk (pointEquations (sectionPoint y)) p) =
      toSectionPolynomial y p := rfl

private theorem from_to_surface_parameter (y : ParameterIndex → S) (p : SectionBase S) :
    fromSurfacePolynomial y (toSectionPolynomial y (C p)) =
      Ideal.Quotient.mk (pointEquations (sectionPoint y)) (C p) := by
  induction p using MvPolynomial.induction_on with
  | C a =>
      rw [show (C (C a) : MvPolynomial (Fin 5) (SectionBase S)) =
        MvPolynomial.map (C : S →+* SectionBase S) (C a) by simp]
      rw [toSectionPolynomial_map, fromSurfacePolynomial_C]
      rfl
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p j hp =>
      simp only [map_mul, hp, toSectionPolynomial_parameter, fromSurfacePolynomial_X]

private theorem from_to_surface_polynomial (y : ParameterIndex → S)
    (p : MvPolynomial (Fin 5) (SectionBase S)) :
    fromSurfacePolynomial y (toSectionPolynomial y p) =
      Ideal.Quotient.mk (pointEquations (sectionPoint y)) p := by
  have h : (fromSurfacePolynomial y).comp (toSectionPolynomial y) =
      Ideal.Quotient.mk (pointEquations (sectionPoint y)) := by
    apply MvPolynomial.ringHom_ext
    · exact from_to_surface_parameter y
    · intro j
      change fromSurfacePolynomial y (toSectionPolynomial y (X j)) = _
      rw [show (X j : MvPolynomial (Fin 5) (SectionBase S)) =
        MvPolynomial.map (C : S →+* SectionBase S) (X j) by simp]
      rw [toSectionPolynomial_map, fromSurfacePolynomial_C]
      rfl
  exact RingHom.congr_fun h p

private theorem to_from_surface_polynomial (y : ParameterIndex → S)
    (p : SectionPolynomial y) :
    toSurfacePolynomial y (fromSurfacePolynomial y p) = p := by
  have h : (toSurfacePolynomial y).comp (fromSurfacePolynomial y) =
      RingHom.id (SectionPolynomial y) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective (I := pointEquations y) a
      change toSurfacePolynomial y (fromSurfacePolynomial y
        (C (Ideal.Quotient.mk (pointEquations y) q))) = _
      rw [fromSurfacePolynomial_C, surfaceCoefficientExtension_mk,
        toSurfacePolynomial_mk, toSectionPolynomial_map]
      rfl
    · intro j
      change toSurfacePolynomial y (fromSurfacePolynomial y (X j)) = _
      rw [fromSurfacePolynomial_X, toSurfacePolynomial_mk, toSectionPolynomial_parameter]
      rfl
  exact RingHom.congr_fun h p

/-- Polynomial extension of the actual surface quotient, retaining the
original coefficient and geometric coordinates. -/
def surfacePolynomialEquiv (y : ParameterIndex → S) :
    PointSurface (sectionPoint y) ≃+* SectionPolynomial y where
  toFun := toSurfacePolynomial y
  invFun := fromSurfacePolynomial y
  left_inv a := by
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
    exact from_to_surface_polynomial y p
  right_inv := to_from_surface_polynomial y
  map_add' := map_add (toSurfacePolynomial y)
  map_mul' := map_mul (toSurfacePolynomial y)

@[simp] theorem surfacePolynomialEquiv_mk (y : ParameterIndex → S)
    (p : MvPolynomial (Fin 5) (SectionBase S)) :
    surfacePolynomialEquiv y (Ideal.Quotient.mk (pointEquations (sectionPoint y)) p) =
      toSectionPolynomial y p := rfl

/-- The comparison commutes with the original quotient to the curve. -/
theorem surfacePolynomialEquiv_curve (y : ParameterIndex → S)
    (a : PointSurface (sectionPoint y)) :
    genericCurveRingEquiv y (genericCurveSurfaceRingMap y a) =
      Ideal.Quotient.mk
        (sectionIdeal (CycleQ2IncidenceBasepointOpen.curveMatrix (pointMap y)))
          (surfacePolynomialEquiv y a) := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  rfl

abbrev basePivot (y : ParameterIndex → S) (p : CycleQ2SegreCech.Chart) : PointSurface y :=
  CycleQ2IncidenceBasepointOpen.curveMatrix (pointMap y) p.1 p.2

def pivot (y : ParameterIndex → S) (p : CycleQ2SegreCech.Chart) :
    PointSurface (sectionPoint y) :=
  Ideal.Quotient.mk (pointEquations (sectionPoint y))
    (pointMatrixPolynomial (sectionPoint y) p.1 p.2)

def equation (y : ParameterIndex → S) (i : Fin 3) : PointSurface (sectionPoint y) :=
  Ideal.Quotient.mk (pointEquations (sectionPoint y)) (genericSectionEquation y i)

theorem pivot_homogeneous (y : ParameterIndex → S) (p : CycleQ2SegreCech.Chart) :
    pivot y p ∈ surfaceGrade (sectionPoint y) 14 :=
  ⟨_, pointMatrixPolynomial_homogeneous (sectionPoint y) p.1 p.2, rfl⟩

theorem equation_homogeneous (y : ParameterIndex → S) (i : Fin 3) :
    equation y i ∈ surfaceGrade (sectionPoint y) 14 :=
  ⟨_, genericSectionEquation_homogeneous y i, rfl⟩

@[simp] theorem surfacePolynomialEquiv_pivot (y : ParameterIndex → S)
    (p : CycleQ2SegreCech.Chart) :
    surfacePolynomialEquiv y (pivot y p) = C (basePivot y p) :=
  toSectionPolynomial_matrix y p.1 p.2

@[simp] theorem surfacePolynomialEquiv_equation (y : ParameterIndex → S) (i : Fin 3) :
    surfacePolynomialEquiv y (equation y i) =
      sectionVector (CycleQ2IncidenceBasepointOpen.curveMatrix (pointMap y)) i :=
  toSectionPolynomial_equation y i

abbrev CoefficientPivot (y : ParameterIndex → S) (p : CycleQ2SegreCech.Chart) :=
  Localization.Away (basePivot y p)

abbrev OrdinaryPivot (y : ParameterIndex → S) (p : CycleQ2SegreCech.Chart) :=
  Localization.Away (pivot y p)

abbrev ProjectivePivot (y : ParameterIndex → S) (p : CycleQ2SegreCech.Chart) :=
  HomogeneousLocalization.Away (surfaceGrade (sectionPoint y)) (pivot y p)

local instance coefficientPivotCommRing (y : ParameterIndex → S) (p : CycleQ2SegreCech.Chart) :
    CommRing (CoefficientPivot y p) := inferInstance
local instance ordinaryPivotCommRing (y : ParameterIndex → S) (p : CycleQ2SegreCech.Chart) :
    CommRing (OrdinaryPivot y p) := inferInstance
local instance projectivePivotCommRing (y : ParameterIndex → S) (p : CycleQ2SegreCech.Chart) :
    CommRing (ProjectivePivot y p) := inferInstance

/-- The genuine ordinary pivot localization is polynomial in the unchanged
three section variables over the corresponding surface localization. -/
def pivotLocalizationEquiv (y : ParameterIndex → S) (p : CycleQ2SegreCech.Chart) :
    OrdinaryPivot y p ≃+* MvPolynomial (Fin 3) (CoefficientPivot y p) :=
  IsLocalization.ringEquivOfRingEquiv
    (M := Submonoid.powers (pivot y p))
    (T := (Submonoid.powers (basePivot y p)).map
      (C : PointSurface y →+* SectionPolynomial y))
    (OrdinaryPivot y p) (MvPolynomial (Fin 3) (CoefficientPivot y p))
    (surfacePolynomialEquiv y) (by
      simp only [Submonoid.map_powers]
      exact congrArg Submonoid.powers (surfacePolynomialEquiv_pivot y p))

@[simp] theorem pivotLocalizationEquiv_algebraMap (y : ParameterIndex → S)
    (p : CycleQ2SegreCech.Chart) (a : PointSurface (sectionPoint y)) :
    pivotLocalizationEquiv y p (algebraMap _ (OrdinaryPivot y p) a) =
      MvPolynomial.map (algebraMap (PointSurface y) (CoefficientPivot y p))
        (surfacePolynomialEquiv y a) :=
  IsLocalization.ringEquivOfRingEquiv_eq _ a

def localizedMatrix (y : ParameterIndex → S) (p : CycleQ2SegreCech.Chart) :
    Matrix (Fin 3) (Fin 3) (CoefficientPivot y p) :=
  (algebraMap (PointSurface y) (CoefficientPivot y p)).mapMatrix
    (CycleQ2IncidenceBasepointOpen.curveMatrix (pointMap y))

theorem localizedMatrix_pivot_isUnit (y : ParameterIndex → S)
    (p : CycleQ2SegreCech.Chart) : IsUnit (localizedMatrix y p p.1 p.2) :=
  IsLocalization.Away.algebraMap_isUnit (basePivot y p)

@[simp] theorem pivotLocalizationEquiv_equation (y : ParameterIndex → S)
    (p : CycleQ2SegreCech.Chart) (i : Fin 3) :
    pivotLocalizationEquiv y p
      (algebraMap _ (OrdinaryPivot y p) (equation y i)) =
        sectionVector (localizedMatrix y p) i := by
  rw [pivotLocalizationEquiv_algebraMap, surfacePolynomialEquiv_equation,
    sectionVector_map]
  rfl

/-! ## The regular equation in the genuine projective chart ring -/

def projectiveEquation (y : ParameterIndex → S) (p : CycleQ2SegreCech.Chart) :
    ProjectivePivot y p :=
  HomogeneousLocalization.Away.mk (surfaceGrade (sectionPoint y))
    (pivot_homogeneous y p) 1 (equation y p.1) (by
      simpa only [one_smul] using equation_homogeneous y p.1)

theorem projectiveEquation_val_mul (y : ParameterIndex → S)
    (p : CycleQ2SegreCech.Chart) :
    (projectiveEquation y p).val *
      algebraMap _ (OrdinaryPivot y p) (pivot y p) =
        algebraMap _ (OrdinaryPivot y p) (equation y p.1) := by
  have hs := IsLocalization.mk'_spec (OrdinaryPivot y p)
    (equation y p.1) (powerDenominator (pivot y p) 1)
  simpa only [projectiveEquation, HomogeneousLocalization.Away.val_mk,
    Localization.mk_eq_mk', powerDenominator, pow_one] using hs

/-- The original row is regular after ordinary pivot localization because
one of its coefficients is a unit and the section variables are independent. -/
theorem ordinaryEquation_regular (y : ParameterIndex → S)
    (p : CycleQ2SegreCech.Chart) :
    IsSMulRegular (OrdinaryPivot y p)
      (algebraMap _ (OrdinaryPivot y p) (equation y p.1)) := by
  have hr := localEquation_regular (localizedMatrix y p) p
    (localizedMatrix_pivot_isUnit y p)
  intro a b hab
  apply (pivotLocalizationEquiv y p).injective
  apply hr.left
  have he := congrArg (pivotLocalizationEquiv y p) hab
  simpa only [smul_eq_mul, map_mul, pivotLocalizationEquiv_equation,
    localEquation] using he

/-- The actual fraction `(M*T)i/Mij` is a nonzerodivisor in the degree-zero
projective chart, with no reducedness or field assumption on `S`. -/
theorem projectiveEquation_regular (y : ParameterIndex → S)
    (p : CycleQ2SegreCech.Chart) :
    IsSMulRegular (ProjectivePivot y p) (projectiveEquation y p) := by
  apply isSMulRegular_of_val
  apply IsSMulRegular.of_right_eq_zero_of_smul
  intro a ha
  apply (ordinaryEquation_regular y p).right_eq_zero_of_smul
  change algebraMap _ (OrdinaryPivot y p) (equation y p.1) * a = 0
  change (projectiveEquation y p).val * a = 0 at ha
  rw [← projectiveEquation_val_mul]
  calc
    ((projectiveEquation y p).val *
          algebraMap _ (OrdinaryPivot y p) (pivot y p)) * a =
        algebraMap _ (OrdinaryPivot y p) (pivot y p) *
          ((projectiveEquation y p).val * a) := by ring
    _ = 0 := by rw [ha, mul_zero]

def surfaceSectionKernel (y : ParameterIndex → S) :
    Ideal (PointSurface (sectionPoint y)) :=
  RingHom.ker (genericCurveSurfaceRingMap y)

theorem surfaceSectionKernel_map (y : ParameterIndex → S) :
    (surfaceSectionKernel y).map (surfacePolynomialEquiv y).toRingHom =
      sectionIdeal (CycleQ2IncidenceBasepointOpen.curveMatrix (pointMap y)) := by
  have hk : surfaceSectionKernel y =
      (sectionIdeal (CycleQ2IncidenceBasepointOpen.curveMatrix (pointMap y))).comap
        (surfacePolynomialEquiv y).toRingHom := by
    ext a
    change genericCurveSurfaceRingMap y a = 0 ↔
      surfacePolynomialEquiv y a ∈
        sectionIdeal (CycleQ2IncidenceBasepointOpen.curveMatrix (pointMap y))
    rw [← (genericCurveRingEquiv y).map_eq_zero_iff,
      surfacePolynomialEquiv_curve, Ideal.Quotient.eq_zero_iff_mem]
  rw [hk]
  exact Ideal.map_comap_of_surjective (surfacePolynomialEquiv y).toRingHom
    (surfacePolynomialEquiv y).surjective _

theorem ordinaryKernel_map (y : ParameterIndex → S) (p : CycleQ2SegreCech.Chart) :
    ((surfaceSectionKernel y).map (algebraMap _ (OrdinaryPivot y p))).map
        (pivotLocalizationEquiv y p).toRingHom =
      sectionIdeal (localizedMatrix y p) := by
  rw [Ideal.map_map]
  have hcomp : (pivotLocalizationEquiv y p).toRingHom.comp
      (algebraMap _ (OrdinaryPivot y p)) =
        (MvPolynomial.map (algebraMap (PointSurface y) (CoefficientPivot y p))).comp
          (surfacePolynomialEquiv y).toRingHom := by
    apply RingHom.ext
    intro a
    exact pivotLocalizationEquiv_algebraMap y p a
  rw [hcomp, ← Ideal.map_map, surfaceSectionKernel_map,
    sectionIdeal, Ideal.map_span]
  congr 1
  ext q
  constructor
  · rintro ⟨a, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, (sectionVector_map _ _ i).symm⟩
  · rintro ⟨i, rfl⟩
    exact ⟨_, ⟨i, rfl⟩, sectionVector_map _ _ i⟩

theorem ordinaryKernel_principal [Nontrivial S] (y : ParameterIndex → S)
    (he : ∀ q, aeval y ((presentation ℂ 57).equation q) = 0)
    (hu : IsUnit (aeval y (leadingProduct ℂ))) (p : CycleQ2SegreCech.Chart) :
    (surfaceSectionKernel y).map (algebraMap _ (OrdinaryPivot y p)) =
      Ideal.span {algebraMap _ (OrdinaryPivot y p) (equation y p.1)} := by
  apply (pivotLocalizationEquiv y p).idealComapOrderIso.symm.injective
  change ((surfaceSectionKernel y).map (algebraMap _ (OrdinaryPivot y p))).map
      (pivotLocalizationEquiv y p).toRingHom =
    (Ideal.span {algebraMap _ (OrdinaryPivot y p) (equation y p.1)}).map
      (pivotLocalizationEquiv y p).toRingHom
  rw [ordinaryKernel_map, Ideal.map_span, Set.image_singleton]
  change sectionIdeal (localizedMatrix y p) =
    Ideal.span {pivotLocalizationEquiv y p
      (algebraMap _ (OrdinaryPivot y p) (equation y p.1))}
  rw [pivotLocalizationEquiv_equation]
  obtain ⟨u, hu'⟩ := localizedMatrix_pivot_isUnit y p
  have hc := @CycleQ2SegreCech.cofactors_map_zero
    (PointSurface y) (inferInstance : CommRing (PointSurface y))
    (CoefficientPivot y p) (inferInstance : CommRing (CoefficientPivot y p))
    (algebraMap (PointSurface y) (CoefficientPivot y p))
    (CycleQ2IncidenceBasepointOpen.curveMatrix (pointMap y))
    (curveMatrix_cofactors y he hu)
  exact sectionIdeal_principal (localizedMatrix y p) hc p u hu'

theorem ordinaryKernel_principal_fraction [Nontrivial S] (y : ParameterIndex → S)
    (he : ∀ q, aeval y ((presentation ℂ 57).equation q) = 0)
    (hu : IsUnit (aeval y (leadingProduct ℂ))) (p : CycleQ2SegreCech.Chart) :
    (surfaceSectionKernel y).map (algebraMap _ (OrdinaryPivot y p)) =
      Ideal.span {(projectiveEquation y p).val} := by
  rw [ordinaryKernel_principal y he hu p, ← projectiveEquation_val_mul,
    Ideal.span_singleton_mul_right_unit
      (IsLocalization.Away.algebraMap_isUnit (pivot y p))]

section HomogeneousKernel

variable {R A B : Type} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B]
variable (𝒜 : ℕ → Submodule R A) (ℬ : ℕ → Submodule R B)
  [GradedRing 𝒜] [GradedRing ℬ] (f : 𝒜 →+*ᵍ ℬ)

private theorem gradedAwayMap_mk_eq_zero_iff (s : A) {d : ℕ} (hs : s ∈ 𝒜 d)
    (n : ℕ) (a : A) (ha : a ∈ 𝒜 (n • d)) :
    Away.map f s (Away.mk 𝒜 hs n a ha) = 0 ↔
      ∃ k : ℕ, s ^ k * a ∈ RingHom.ker f := by
  rw [Away.map_mk, HomogeneousLocalization.ext_iff_val,
    HomogeneousLocalization.val_zero, Away.val_mk, Localization.mk_eq_mk',
    IsLocalization.mk'_eq_zero_iff]
  constructor
  · rintro ⟨⟨b, hb⟩, hz⟩
    obtain ⟨k, rfl⟩ := hb
    refine ⟨k, ?_⟩
    change f (s ^ k * a) = 0
    simpa only [map_mul, map_pow] using hz
  · rintro ⟨k, hk⟩
    refine ⟨⟨(f s) ^ k, Submonoid.pow_mem _ (Submonoid.mem_powers _) _⟩, ?_⟩
    change f (s ^ k * a) = 0 at hk
    simpa only [map_mul, map_pow] using hk

/-- Kernel of the actual projective chart map is the contraction of the
ordinary localization of its original homogeneous kernel. -/
theorem gradedAwayMap_ker (s : A) {d : ℕ} (hs : s ∈ 𝒜 d) :
    RingHom.ker (Away.map f s) =
      ((RingHom.ker f).map (algebraMap A (Localization.Away s))).comap
        (algebraMap (Away 𝒜 s) (Localization.Away s)) := by
  ext z
  obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective 𝒜 hs z
  change Away.map f s (Away.mk 𝒜 hs n a ha) = 0 ↔
    (Away.mk 𝒜 hs n a ha).val ∈
      (RingHom.ker f).map (algebraMap A (Localization.Away s))
  rw [gradedAwayMap_mk_eq_zero_iff, Away.val_mk, Localization.mk_eq_mk',
    IsLocalization.mk'_mem_map_algebraMap_iff]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨s ^ k, ⟨k, rfl⟩, hk⟩
  · rintro ⟨b, ⟨k, rfl⟩, hk⟩
    exact ⟨k, hk⟩

end HomogeneousKernel

/-- The kernel of the genuine degree-zero quotient map is generated by
the displayed regular fraction. This is the affine Cartier assertion for
the unchanged projective incidence curve. -/
theorem projectiveKernel_principal [Nontrivial S] (y : ParameterIndex → S)
    (he : ∀ q, aeval y ((presentation ℂ 57).equation q) = 0)
    (hu : IsUnit (aeval y (leadingProduct ℂ))) (p : CycleQ2SegreCech.Chart) :
    RingHom.ker (Away.map (genericCurveSurfaceRingMap y) (pivot y p)) =
      Ideal.span {projectiveEquation y p} := by
  rw [gradedAwayMap_ker (R := SectionBase S)
    (A := PointSurface (sectionPoint y)) (B := GenericCurveRing y)
    (surfaceGrade (sectionPoint y)) (genericCurveGrade y)
    (genericCurveSurfaceRingMap y) (pivot y p) (pivot_homogeneous y p)]
  change ((surfaceSectionKernel y).map (algebraMap _ (OrdinaryPivot y p))).comap
    (algebraMap (ProjectivePivot y p) (OrdinaryPivot y p)) = _
  rw [ordinaryKernel_principal_fraction y he hu p]
  exact principalIdeal_comap_val (surfaceGrade (sectionPoint y))
    (pivot_homogeneous y p) (projectiveEquation y p)

/-! ## The actual projective closed immersion and its section ideals -/

section ClosedProjectiveMap

variable {R A B : Type} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B]
variable (𝒜 : ℕ → Submodule R A) (ℬ : ℕ → Submodule R B)
  [GradedRing 𝒜] [GradedRing ℬ] (f : 𝒜 →+*ᵍ ℬ)
variable (hf : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f)
variable (hsur : ∀ (n : ℕ) (b : B), b ∈ ℬ n → ∃ a : A, a ∈ 𝒜 n ∧ f a = b)

include hsur in
private theorem gradedAwayMap_surjective (s : A) {d : ℕ} (hs : s ∈ 𝒜 d) :
    Function.Surjective (Away.map f s) := by
  intro z
  obtain ⟨n, b, hb, rfl⟩ := Away.mk_surjective ℬ (f.2 hs) z
  obtain ⟨a, ha, rfl⟩ := hsur (n • d) b hb
  refine ⟨Away.mk 𝒜 hs n a ha, ?_⟩
  simp only [Away.map_mk]

include hsur in
private theorem projectiveMap_closedImmersion : IsClosedImmersion (Proj.map f hf) := by
  have hc : (⨆ i : Σ n : PNat, 𝒜 n, Proj.basicOpen 𝒜 (i.2 : A)) = ⊤ := by
    have hh := (Proj.affineOpenCover 𝒜).openCover.iSup_opensRange
    change (⨆ i : Σ n : PNat, 𝒜 n,
      (Proj.awayι 𝒜 (i.2 : A) i.2.2 i.1.2).opensRange) = ⊤ at hh
    simpa only [Proj.opensRange_awayι] using hh
  refine IsZariskiLocalAtTarget.of_iSup_eq_top
    (P := @IsClosedImmersion) (f := Proj.map f hf)
    (fun i : Σ n : PNat, 𝒜 n => Proj.basicOpen 𝒜 (i.2 : A)) hc ?_
  intro i
  have he : (Proj.map f hf ∣_ Proj.basicOpen 𝒜 (i.2 : A)) =
      (Proj.basicOpenIsoSpec ℬ (f i.2) (f.2 i.2.2) i.1.2).hom ≫
        Spec.map (CommRingCat.ofHom (R := Away 𝒜 (i.2 : A))
          (S := Away ℬ (f i.2)) (Away.map f i.2)) ≫
          (Proj.basicOpenIsoSpec 𝒜 (i.2 : A) i.2.2 i.1.2).inv := by
    have hcomm := Proj.awayι_comp_map f hf i.1.2 (i.2 : A) i.2.2
    apply (cancel_mono (Proj.basicOpen 𝒜 (i.2 : A)).ι).mp
    rw [morphismRestrict_ι]
    change (Proj.basicOpen ℬ (f i.2)).ι ≫ Proj.map f hf =
      (Proj.basicOpenIsoSpec ℬ (f i.2) (f.2 i.2.2) i.1.2).hom ≫
        (Spec.map (CommRingCat.ofHom (R := Away 𝒜 (i.2 : A))
          (S := Away ℬ (f i.2)) (Away.map f i.2)) ≫
          Proj.awayι 𝒜 (i.2 : A) i.2.2 i.1.2)
    rw [← hcomm]
    simp only [Proj.awayι, Category.assoc, Iso.hom_inv_id_assoc]
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom
      (R := Away 𝒜 (i.2 : A)) (S := Away ℬ (f i.2)) (Away.map f i.2))) :=
    IsClosedImmersion.spec_of_surjective _
      (gradedAwayMap_surjective 𝒜 ℬ f hsur i.2 i.2.2)
  rw [he]
  infer_instance

end ClosedProjectiveMap

/-- This is the previously defined `genericCurveToSurface`, now proved to
be a closed immersion. No incidence equation or smoothness is assumed. -/
instance genericCurveToSurface_isClosedImmersion (y : ParameterIndex → S) :
    IsClosedImmersion (genericCurveToSurface y) := by
  apply projectiveMap_closedImmersion (R := SectionBase S)
    (A := PointSurface (sectionPoint y)) (B := GenericCurveRing y)
    (surfaceGrade (sectionPoint y))
    (genericCurveGrade y) (genericCurveSurfaceRingMap y)
    (irrelevant_le_map_genericCurveSurfaceRingMap y)
  rintro n b ⟨q, hq, rfl⟩
  exact ⟨Ideal.Quotient.mk (pointEquations (sectionPoint y)) q, ⟨q, hq, rfl⟩, rfl⟩

def pivotOpen (y : ParameterIndex → S) (p : CycleQ2SegreCech.Chart) :
    (surface (sectionPoint y)).Opens :=
  Proj.basicOpen (surfaceGrade (sectionPoint y)) (pivot y p)

theorem pivotOpen_isAffineOpen (y : ParameterIndex → S) (p : CycleQ2SegreCech.Chart) :
    IsAffineOpen (pivotOpen y p) :=
  Proj.isAffineOpen_basicOpen (surfaceGrade (sectionPoint y)) (pivot y p)
    (pivot_homogeneous y p) (by decide)

def pivotSectionsEquiv (y : ParameterIndex → S) (p : CycleQ2SegreCech.Chart) :
    ProjectivePivot y p ≃+* Γ(surface (sectionPoint y), pivotOpen y p) :=
  (Proj.basicOpenIsoAway (surfaceGrade (sectionPoint y)) (pivot y p)
    (pivot_homogeneous y p) (by decide)).commRingCatIsoToRingEquiv

def curvePivotSectionsEquiv (y : ParameterIndex → S) (p : CycleQ2SegreCech.Chart) :
    Away (genericCurveGrade y) (genericCurveSurfaceRingMap y (pivot y p)) ≃+*
      Γ(genericCurve y, genericCurveToSurface y ⁻¹ᵁ pivotOpen y p) :=
  (Proj.basicOpenIsoAway (genericCurveGrade y)
    (genericCurveSurfaceRingMap y (pivot y p))
    ((genericCurveSurfaceRingMap y).2 (pivot_homogeneous y p))
    (by decide)).commRingCatIsoToRingEquiv

theorem genericCurveToSurface_app_pivot (y : ParameterIndex → S)
    (p : CycleQ2SegreCech.Chart) (z : ProjectivePivot y p) :
    (genericCurveToSurface y).app (pivotOpen y p) (pivotSectionsEquiv y p z) =
      curvePivotSectionsEquiv y p
        (Away.map (genericCurveSurfaceRingMap y) (pivot y p) z) := by
  have h := ConcreteCategory.congr_hom
    (Proj.awayToSection_comp_appLE (genericCurveSurfaceRingMap y)
      (irrelevant_le_map_genericCurveSurfaceRingMap y) (pivot_homogeneous y p)) z
  change (genericCurveToSurface y).appLE (pivotOpen y p)
      (genericCurveToSurface y ⁻¹ᵁ pivotOpen y p) le_rfl
      (Proj.awayToSection (surfaceGrade (sectionPoint y)) (pivot y p) z) =
    Proj.awayToSection (genericCurveGrade y) (genericCurveSurfaceRingMap y (pivot y p))
      (Away.map (genericCurveSurfaceRingMap y) (pivot y p) z) at h
  rw [Scheme.Hom.appLE_eq_app] at h
  exact h

def pivotEquationSection (y : ParameterIndex → S) (p : CycleQ2SegreCech.Chart) :
    Γ(surface (sectionPoint y), pivotOpen y p) :=
  pivotSectionsEquiv y p (projectiveEquation y p)

theorem pivotEquationSection_regular (y : ParameterIndex → S)
    (p : CycleQ2SegreCech.Chart) :
    IsSMulRegular Γ(surface (sectionPoint y), pivotOpen y p) (pivotEquationSection y p) := by
  intro a b hab
  apply (pivotSectionsEquiv y p).symm.injective
  apply projectiveEquation_regular y p
  have hm := congrArg (pivotSectionsEquiv y p).symm hab
  simpa only [smul_eq_mul, map_mul, pivotEquationSection,
    RingEquiv.symm_apply_apply] using hm

/-- The actual structure-map kernel on each projective pivot open is
the principal ideal of the displayed regular section. -/
theorem pivotSectionKernel_principal [Nontrivial S] (y : ParameterIndex → S)
    (he : ∀ q, aeval y ((presentation ℂ 57).equation q) = 0)
    (hu : IsUnit (aeval y (leadingProduct ℂ))) (p : CycleQ2SegreCech.Chart) :
    RingHom.ker ((genericCurveToSurface y).app (pivotOpen y p)).hom =
      Ideal.span {pivotEquationSection y p} := by
  have hk : (RingHom.ker ((genericCurveToSurface y).app (pivotOpen y p)).hom).comap
      (pivotSectionsEquiv y p).toRingHom =
      RingHom.ker (Away.map (genericCurveSurfaceRingMap y) (pivot y p)) := by
    ext a
    change (genericCurveToSurface y).app (pivotOpen y p) (pivotSectionsEquiv y p a) = 0 ↔ _
    rw [genericCurveToSurface_app_pivot]
    exact (curvePivotSectionsEquiv y p).map_eq_zero_iff
  rw [← Ideal.map_comap_of_surjective (pivotSectionsEquiv y p).toRingHom
      (pivotSectionsEquiv y p).surjective
      (RingHom.ker ((genericCurveToSurface y).app (pivotOpen y p)).hom),
    hk, projectiveKernel_principal y he hu p, Ideal.map_span, Set.image_singleton]
  rfl

/-! ## The proved basepoint open covers the entire actual surface -/

theorem surface_irrelevant_le_coordinateIdeal (y : ParameterIndex → S) :
    (HomogeneousIdeal.irrelevant (surfaceGrade y)).toIdeal ≤
      Ideal.span (Set.range (fun j : Fin 5 => Ideal.Quotient.mk (pointEquations y) (X j))) := by
  apply (HomogeneousIdeal.toIdeal_irrelevant_le _).mpr
  intro n hn a ha
  obtain ⟨q, hq, rfl⟩ := ha
  have hqI : q ∈ MvPolynomial.idealOfVars (Fin 5) S := by
    have hh : q ∈ MvPolynomial.idealOfVars (Fin 5) S ^ 1 := by
      apply (MvPolynomial.mem_pow_idealOfVars_iff' 1 q).mpr
      intro e he
      have he0 : e = 0 := (Finsupp.degree_eq_zero_iff e).mp (by omega)
      subst e
      by_contra hc
      have hz : 0 = n := by simpa only [map_zero] using hq hc
      omega
    simpa only [pow_one] using hh
  have hmap : MvPolynomial.idealOfVars (Fin 5) S ≤
      (Ideal.span (Set.range (fun j : Fin 5 =>
        Ideal.Quotient.mk (pointEquations y) (X j)))).comap
          (Ideal.Quotient.mk (pointEquations y)) := by
    apply Ideal.span_le.mpr
    rintro _ ⟨j, rfl⟩
    exact Ideal.subset_span ⟨j, rfl⟩
  exact hmap hqI

theorem surface_coordinate_exists (y : ParameterIndex → S) (x : surface y) :
    ∃ j : Fin 5, CycleQ2IncidenceBasepointOpen.curveCoordinate (pointMap y) j ∉
      x.asHomogeneousIdeal.toIdeal := by
  by_contra hn
  push_neg at hn
  apply x.not_irrelevant_le
  apply toIdeal_le_toIdeal_iff.mp
  apply (surface_irrelevant_le_coordinateIdeal y).trans
  apply Ideal.span_le.mpr
  rintro _ ⟨j, rfl⟩
  exact hn j

theorem sectionPoint_aeval (y : ParameterIndex → S)
    (a : CycleQ2IncidenceBasepointOpen.Coeff) :
    aeval (sectionPoint y) a = C (aeval y a) := by
  exact (MvPolynomial.comp_aeval_apply (f := y)
    (IsScalarTower.toAlgHom ℂ S (SectionBase S)) a).symm

theorem pivot_eq_curveMatrix (y : ParameterIndex → S) (p : CycleQ2SegreCech.Chart) :
    pivot y p = CycleQ2IncidenceBasepointOpen.curveMatrix (pointMap (sectionPoint y)) p.1 p.2 := by
  rw [pivot, pointMatrixPolynomial_eq]
  rfl

/-- All nine genuine projective pivot opens cover the entire universal
surface whenever the already proved basepoint-open polynomial is invertible. -/
theorem pivotOpen_cover [Nontrivial S] (y : ParameterIndex → S)
    (hb : IsUnit (aeval y CycleQ2IncidenceBasepointOpen.basepointPolynomial)) :
    (⨆ p : CycleQ2SegreCech.Chart, pivotOpen y p) = ⊤ := by
  have hb' : IsUnit (aeval (sectionPoint y)
      CycleQ2IncidenceBasepointOpen.basepointPolynomial) := by
    rw [sectionPoint_aeval]
    exact hb.map C
  apply top_unique
  intro x hx
  have hx' := surface_coordinate_exists (sectionPoint y) x
  obtain ⟨i, j, hij⟩ := CycleQ2IncidenceBasepointOpen.specialized_prime_pivot_cover
    (pointMap (sectionPoint y)) hb' x.asHomogeneousIdeal.toIdeal hx'
  apply TopologicalSpace.Opens.mem_iSup.mpr
  refine ⟨(i, j), ?_⟩
  change pivot y (i, j) ∉ x.asHomogeneousIdeal.toIdeal
  rw [pivot_eq_curveMatrix]
  exact hij

/-- An explicit affine Cartier cover for the original universal curve
closed immersion. Every generator and kernel is an actual scheme section. -/
theorem genericCurve_cartier_cover [Nontrivial S] (y : ParameterIndex → S)
    (he : ∀ q, aeval y ((presentation ℂ 57).equation q) = 0)
    (hu : IsUnit (aeval y (leadingProduct ℂ)))
    (hb : IsUnit (aeval y CycleQ2IncidenceBasepointOpen.basepointPolynomial)) :
    (⨆ p : CycleQ2SegreCech.Chart, pivotOpen y p) = ⊤ ∧
      ∀ p : CycleQ2SegreCech.Chart,
        IsSMulRegular Γ(surface (sectionPoint y), pivotOpen y p) (pivotEquationSection y p) ∧
        RingHom.ker ((genericCurveToSurface y).app (pivotOpen y p)).hom =
          Ideal.span {pivotEquationSection y p} :=
  ⟨pivotOpen_cover y hb, fun p =>
    ⟨pivotEquationSection_regular y p, pivotSectionKernel_principal y he hu p⟩⟩

section ActualEtaleIncidence

open CycleQ2IncidenceEtaleParameter CycleQ2IncidenceTraceGeometry

/-- The actual étale parameter algebra satisfies every hypothesis of the
Cartier-cover theorem. No additional geometric input is requested. -/
theorem incidencePoint_cartier_cover :
    (⨆ p : CycleQ2SegreCech.Chart, pivotOpen incidencePoint p) = ⊤ ∧
      ∀ p : CycleQ2SegreCech.Chart,
        IsSMulRegular Γ(surface (sectionPoint incidencePoint), pivotOpen incidencePoint p)
          (pivotEquationSection incidencePoint p) ∧
        RingHom.ker ((genericCurveToSurface incidencePoint).app
          (pivotOpen incidencePoint p)).hom =
            Ideal.span {pivotEquationSection incidencePoint p} :=
  genericCurve_cartier_cover incidencePoint
    (tracePoint_original_equations splitting.P splitting.B _ sliceCoordinate incidence_isTracePoint)
    (tracePoint_leading_unit splitting.P splitting.B _ sliceCoordinate incidence_isTracePoint)
    (tracePoint_extra_unit splitting.P splitting.B _ sliceCoordinate incidence_isTracePoint)

end ActualEtaleIncidence

#print axioms surfacePolynomialEquiv
#print axioms pivotLocalizationEquiv
#print axioms projectiveEquation_regular
#print axioms projectiveKernel_principal
#print axioms genericCurveToSurface_isClosedImmersion
#print axioms pivotSectionKernel_principal
#print axioms pivotOpen_cover
#print axioms genericCurve_cartier_cover
#print axioms incidencePoint_cartier_cover

end CycleQ2UniversalCurveCartier

end
