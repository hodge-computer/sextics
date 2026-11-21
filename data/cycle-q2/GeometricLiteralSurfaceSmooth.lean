import Proposal.GeometricSurfaceProjectiveCoefficients
import Proposal.GeometricSeedSurfaceGradient
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.RingTheory.Smooth.Locus
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent

/-!
The whole literal surface at (r, theta) = (57, 1) is smooth over C.

This file uses the existing polynomial Jacobian cover of every relevant
prime. It first proves smoothness of the four weight-one localizations
of the actual affine cone. The existing dehomogenized chart is an
explicit C-algebra retract of that localization, so it is formally
smooth and, being finitely presented, smooth. Finally the existing
coordinate cover and the existing structure-morphism compatibility
identify these rings with affine charts of the original weighted Proj.

The concluding theorem is about the existing scheme structure and its
existing structure morphism to Spec C.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralSurfaceSmooth

open CategoryTheory TopologicalSpace AlgebraicGeometry MvPolynomial
open CycleQ2SeedTrace CycleQ2NormalConnecting CycleQ2ConormalJacobian
open CycleQ2GeometricSeedNormalIdeals CycleQ2GeometricCartierNormalLift
open CycleQ2CartierProjectiveCover
open CycleQ2GeometricSurfaceDehomogenizedCharts
open CycleQ2GeometricSurfaceCoefficients

/-! ## A polynomial Jacobian criterion on a chosen principal open -/

abbrev EquationQuotient (v : Fin 2 → WeightedPoly) :=
  WeightedPoly ⧸ Ideal.span (Set.range v)

def equationMinor (v : Fin 2 → WeightedPoly) (p : Fin 2 → Fin 5) : WeightedPoly :=
  pderiv (p 0) (v 0) * pderiv (p 1) (v 1) -
    pderiv (p 1) (v 0) * pderiv (p 0) (v 1)

def conePrePresentation (v : Fin 2 → WeightedPoly)
    (p : Fin 2 → Fin 5) (hp : Function.Injective p) :
    Algebra.PreSubmersivePresentation ℂ (EquationQuotient v) (Fin 5) (Fin 2) :=
  Algebra.PreSubmersivePresentation.naive (v := v) p hp

theorem conePrePresentation_jacobian (v : Fin 2 → WeightedPoly)
    (p : Fin 2 → Fin 5) (hp : Function.Injective p) :
    (conePrePresentation v p hp).jacobian =
      Ideal.Quotient.mk (Ideal.span (Set.range v)) (equationMinor v p) := by
  rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det,
    Matrix.det_fin_two]
  simp only [Algebra.PreSubmersivePresentation.jacobiMatrix_apply]
  change Ideal.Quotient.mk (Ideal.span (Set.range v))
      (pderiv (p 0) (v 0) * pderiv (p 1) (v 1) -
        pderiv (p 0) (v 1) * pderiv (p 1) (v 0)) = _
  apply congrArg (Ideal.Quotient.mk (Ideal.span (Set.range v)))
  dsimp only [equationMinor]
  rw [mul_comm (pderiv (p 0) (v 1)) (pderiv (p 1) (v 0))]

abbrev ConeJacobianPatch (v : Fin 2 → WeightedPoly)
    (p : Fin 2 → Fin 5) (hp : Function.Injective p) :=
  Localization.Away (conePrePresentation v p hp).jacobian

/-- The localization at the actual determinant has a finite
submersive presentation, obtained by adding its inverse. -/
def coneJacobianPresentation (v : Fin 2 → WeightedPoly)
    (p : Fin 2 → Fin 5) (hp : Function.Injective p) :
    Algebra.SubmersivePresentation ℂ (ConeJacobianPatch v p hp)
      (Unit ⊕ Fin 5) (Unit ⊕ Fin 2) where
  toPreSubmersivePresentation :=
    (Algebra.PreSubmersivePresentation.localizationAway
      (ConeJacobianPatch v p hp) (conePrePresentation v p hp).jacobian).comp
        (conePrePresentation v p hp)
  jacobian_isUnit := by
    have hu : IsUnit (algebraMap (EquationQuotient v) (ConeJacobianPatch v p hp)
        (conePrePresentation v p hp).jacobian) :=
      IsLocalization.Away.algebraMap_isUnit _
    simpa only [Algebra.PreSubmersivePresentation.comp_jacobian_eq_jacobian_smul_jacobian,
      Algebra.PreSubmersivePresentation.localizationAway_jacobian, Algebra.smul_def]
      using hu.mul hu

theorem coneJacobianPatch_smooth (v : Fin 2 → WeightedPoly)
    (p : Fin 2 → Fin 5) (hp : Function.Injective p) :
    Algebra.Smooth ℂ (ConeJacobianPatch v p hp) := by
  letI : Algebra.IsStandardSmooth ℂ (ConeJacobianPatch v p hp) :=
    (coneJacobianPresentation v p hp).isStandardSmooth
  infer_instance

/-- A Jacobian-minor cover of the polynomial primes above D(t)
proves smoothness of the actual quotient localized at t. -/
theorem coneLocalization_smooth_of_minor_cover
    (v : Fin 2 → WeightedPoly) (t : WeightedPoly)
    (hcover : ∀ (P : Ideal WeightedPoly), P.IsPrime →
      (∀ a : Fin 2, v a ∈ P) → t ∉ P →
      ∃ p : Fin 2 → Fin 5, Function.Injective p ∧ equationMinor v p ∉ P) :
    Algebra.Smooth ℂ
      (Localization.Away (Ideal.Quotient.mk (Ideal.span (Set.range v)) t)) := by
  letI : Algebra.FinitePresentation ℂ (EquationQuotient v) :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  apply (Algebra.basicOpen_subset_smoothLocus_iff_smooth
    (R := ℂ) (A := EquationQuotient v)).mp
  intro q hq
  let P : Ideal WeightedPoly :=
    Ideal.comap (Ideal.Quotient.mk (Ideal.span (Set.range v))) q.asIdeal
  have hP : P.IsPrime := inferInstance
  have hv : ∀ a : Fin 2, v a ∈ P := by
    intro a
    change Ideal.Quotient.mk (Ideal.span (Set.range v)) (v a) ∈ q.asIdeal
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.subset_span (Set.mem_range_self a))]
    exact q.asIdeal.zero_mem
  have ht : t ∉ P := hq
  obtain ⟨p, hp, hm⟩ := hcover P hP hv ht
  apply (Algebra.basicOpen_subset_smoothLocus_iff_smooth
    (R := ℂ) (A := EquationQuotient v)
    (f := (conePrePresentation v p hp).jacobian)).mpr
      (coneJacobianPatch_smooth v p hp)
  change (conePrePresentation v p hp).jacobian ∉ q.asIdeal
  rw [conePrePresentation_jacobian]
  exact hm

/-- The closed whole-seed Jacobian certificate applies to each of
the four weight-one coordinate localizations of the original cone. -/
theorem literal_coordinateLocalization_smooth (i : Fin 4) :
    Algebra.Smooth ℂ (CoordinateLocalization 57 1 i) := by
  apply coneLocalization_smooth_of_minor_cover (surfaceEquations 57 1) (X i.castSucc)
  intro P hP hv ht
  letI : P.IsPrime := hP
  obtain ⟨j, k, hm⟩ := CycleQ2SeedSurfaceGradient.actual_prime_normal_cover P
    (hv 0) (hv 1) ⟨i.castSucc, ht⟩
  have hjk : j ≠ k := by
    intro h
    subst k
    apply hm
    simp only [CycleQ2SeedSurfaceGradient.actualNormalMinor, Matrix.det_fin_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, sub_self]
    exact P.zero_mem
  let p : Fin 2 → Fin 5 := ![j, k]
  refine ⟨p, ?_, ?_⟩
  · intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [p]
  · simpa only [equationMinor, p, surfaceEquations,
      CycleQ2SeedSurfaceGradient.actualNormalMinor, Matrix.det_fin_two,
      Matrix.cons_val_zero, Matrix.cons_val_one] using hm

/-! ## The exact projective chart is an algebra retract of the cone chart -/

/-- Formal smoothness descends to an algebra retract, by composing
the square-zero lifting problem with the retraction and its section. -/
theorem formallySmooth_of_retract
    {k A B : Type} [CommRing k] [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B] [Algebra.FormallySmooth k A]
    (s : B →ₐ[k] A) (r : A →ₐ[k] B) (h : ∀ x : B, r (s x) = x) :
    Algebra.FormallySmooth k B := by
  apply Algebra.FormallySmooth.of_comp_surjective
  intro T _ _ I hI f
  obtain ⟨g, hg⟩ := Algebra.FormallySmooth.comp_surjective k A I hI (f.comp r)
  refine ⟨g.comp s, ?_⟩
  apply AlgHom.ext
  intro x
  exact (AlgHom.congr_fun hg (s x)).trans (congrArg f (h x))

def coordinateInclusionAlgHom (r θ : ℂ) (i : Fin 4) :
    CoordinateRing r θ i →ₐ[ℂ] CoordinateLocalization r θ i where
  toRingHom := algebraMap (CoordinateRing r θ i) (CoordinateLocalization r θ i)
  commutes' c := by
    rw [coordinate_algebraMap]
    change (constants r θ i c).val = algebraMap ℂ (CoordinateLocalization r θ i) c
    rw [constants_val,
      IsScalarTower.algebraMap_apply ℂ (SurfaceRing r θ) (CoordinateLocalization r θ i)]
    rfl

def surfaceToDehomogenizedAlgHom (r θ : ℂ) (i : Fin 4) :
    SurfaceRing r θ →ₐ[ℂ] DehomogenizedRing r θ i where
  toRingHom := surfaceToDehomogenized r θ i
  commutes' c := by
    change surfaceToDehomogenized r θ i (surfaceQuotient r θ (C c)) =
      dehomogenizedMap r θ i (C c)
    rw [surfaceToDehomogenized_surfaceQuotient]
    exact congrArg (dehomogenizedMap r θ i) ((dehomogenize i).commutes c)

/-- This is the existing map which sets the chosen weight-one coordinate to 1. -/
def dehomogenizedRetraction (r θ : ℂ) (i : Fin 4) :
    CoordinateLocalization r θ i →ₐ[ℂ] DehomogenizedRing r θ i :=
  IsLocalization.Away.liftAlgHom
    (S := CoordinateLocalization r θ i)
    (f := surfaceToDehomogenizedAlgHom r θ i)
    (surfaceQuotient r θ (X i.castSucc)) (by
      change IsUnit (surfaceToDehomogenized r θ i (surfaceQuotient r θ (X i.castSucc)))
      rw [surfaceToDehomogenized_self]
      exact isUnit_one)

/-- The section is the existing inverse dehomogenization by homogeneous fractions. -/
def dehomogenizedSection (r θ : ℂ) (i : Fin 4) :
    DehomogenizedRing r θ i →ₐ[ℂ] CoordinateLocalization r θ i :=
  (coordinateInclusionAlgHom r θ i).comp (coordinateChartAlgEquiv r θ i).symm.toAlgHom

theorem dehomogenizedRetraction_section (r θ : ℂ) (i : Fin 4)
    (x : DehomogenizedRing r θ i) :
    dehomogenizedRetraction r θ i (dehomogenizedSection r θ i x) = x := by
  exact toDehomogenized_fromDehomogenized r θ i x

/-- Smoothness transfers to the actual affine equation ring, without
changing its complex algebra structure. -/
theorem dehomogenized_smooth_of_coordinateLocalization_smooth
    (r θ : ℂ) (i : Fin 4) [Algebra.Smooth ℂ (CoordinateLocalization r θ i)] :
    Algebra.Smooth ℂ (DehomogenizedRing r θ i) := by
  letI : Algebra.FormallySmooth ℂ (DehomogenizedRing r θ i) :=
    formallySmooth_of_retract (dehomogenizedSection r θ i)
      (dehomogenizedRetraction r θ i) (dehomogenizedRetraction_section r θ i)
  letI : Algebra.FinitePresentation ℂ (DehomogenizedRing r θ i) :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  exact ⟨inferInstance, inferInstance⟩

theorem literal_dehomogenized_smooth (i : Fin 4) :
    Algebra.Smooth ℂ (DehomogenizedRing 57 1 i) := by
  letI := literal_coordinateLocalization_smooth i
  exact dehomogenized_smooth_of_coordinateLocalization_smooth 57 1 i

/-! ## Whole-surface scheme smoothness over the exact base field -/

theorem literal_coordinatePatch_smooth (i : Fin 4) :
    AlgebraicGeometry.Smooth
      ((coordinatePatch 57 1 i.castSucc).ι ≫ projectiveToComplex 57 1) := by
  apply (MorphismProperty.cancel_left_of_respectsIso
    (P := @AlgebraicGeometry.Smooth) (coordinateAffineChart 57 1 i).inv
    ((coordinatePatch 57 1 i.castSucc).ι ≫ projectiveToComplex 57 1)).mp
  rw [coordinateAffineChart_overComplex]
  apply (HasRingHomProperty.Spec_iff (P := @AlgebraicGeometry.Smooth)).mpr
  exact RingHom.smooth_algebraMap.mpr (literal_dehomogenized_smooth i)

/-- The weight-one coordinate charts cover the actual literal surface.
This follows directly from the equations, without cohomology assumptions. -/
theorem literal_weightOne_cover :
    (⨆ i : Fin 4, coordinatePatch (57 : ℂ) 1 i.castSucc) = ⊤ := by
  apply top_le_iff.mp
  intro q _
  have hq : q ∈ ⨆ j : Fin 5, coordinatePatch (57 : ℂ) 1 j := by
    rw [coordinatePatches_cover]
    trivial
  obtain ⟨j, hj⟩ := Opens.mem_iSup.mp hq
  letI : q.asHomogeneousIdeal.toIdeal.IsPrime := q.isPrime
  let P : Ideal WeightedPoly :=
    Ideal.comap (surfaceQuotient (57 : ℂ) 1) q.asHomogeneousIdeal.toIdeal
  letI : P.IsPrime := inferInstance
  have hF₀ : actualSeedEquation (57 : ℂ) 1 ∈ P := by
    change surfaceQuotient (57 : ℂ) 1 (actualSeedEquation 57 1) ∈
      q.asHomogeneousIdeal.toIdeal
    rw [surfaceQuotient_F]
    exact q.asHomogeneousIdeal.toIdeal.zero_mem
  have hh₀ : thetaH 1 ∈ P := by
    change surfaceQuotient (57 : ℂ) 1 (thetaH 1) ∈ q.asHomogeneousIdeal.toIdeal
    rw [surfaceQuotient_h]
    exact q.asHomogeneousIdeal.toIdeal.zero_mem
  have hF : CycleQ2IncidenceEquations.smoothF (57 : ℂ) Complex.I ∈ P := by
    simpa only [actualSeedEquation_eq_smoothF] using hF₀
  have hh : CycleQ2IncidenceEquations.smoothH Complex.I ∈ P := by
    simpa only [smoothH_eq_thetaH] using hh₀
  have hx : ∃ j : Fin 5, X j ∉ P := ⟨j, hj⟩
  rcases CycleQ2SeedCoordinateCover.seedPrime_coordinate_cover (57 : ℂ) Complex.I
      P hh hF hx with h₁ | h₂ | h₃
  · exact Opens.mem_iSup.mpr ⟨1, h₁⟩
  · exact Opens.mem_iSup.mpr ⟨2, h₂⟩
  · exact Opens.mem_iSup.mpr ⟨3, h₃⟩

/-- The literal weighted projective surface at (57,1) is smooth over C.
The source is the existing projectiveSurface and the morphism is its
existing projectiveToComplex; no smoothness premise is supplied. -/
theorem literal_surface_smooth :
    AlgebraicGeometry.Smooth (projectiveToComplex (57 : ℂ) (1 : ℂ)) := by
  exact IsZariskiLocalAtSource.of_iSup_eq_top
    (P := @AlgebraicGeometry.Smooth)
    (fun i : Fin 4 => coordinatePatch (57 : ℂ) 1 i.castSucc)
    literal_weightOne_cover literal_coordinatePatch_smooth

end CycleQ2LiteralSurfaceSmooth

end

#print axioms CycleQ2LiteralSurfaceSmooth.coneLocalization_smooth_of_minor_cover
#print axioms CycleQ2LiteralSurfaceSmooth.literal_coordinateLocalization_smooth
#print axioms CycleQ2LiteralSurfaceSmooth.formallySmooth_of_retract
#print axioms CycleQ2LiteralSurfaceSmooth.dehomogenizedRetraction_section
#print axioms CycleQ2LiteralSurfaceSmooth.literal_dehomogenized_smooth
#print axioms CycleQ2LiteralSurfaceSmooth.literal_surface_smooth
