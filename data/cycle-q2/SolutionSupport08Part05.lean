import Proposal.SolutionSupport08Part04

/-! Components extracted from SolutionSupport08.lean, in their original order.
See solution.md for the mathematical and verification status. -/

set_option Elab.async false

/- Component: continuation_20261112/SeedGlobalConormal.lean -/
section
/-! Global equation-class bases of the actual seed conormal modules.
These use polynomial regularity and therefore need no Jacobian chart.
-/

noncomputable section
open scoped BigOperators TensorProduct
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2SeedGlobalConormal
open CycleQ2SeedTrace CycleQ2NormalConnecting CycleQ2ConormalJacobian
  CycleQ2SeedRegularLeading CycleQ2NaturalNormalMap

theorem source_relation_coefficients (r θ : ℂ) (v : Fin 3 → WeightedPoly)
    (hv : (∑ i, v i * curveEquations r θ i)=0) :
    ∀ i, v i ∈ ambientCurveIdeal r θ := by
  simpa only [ambientCurveIdeal,curveEquations] using
    CycleQ2MonicRegular.triple_relation_coefficients auxiliaryOrder
      (originalF1 r) originalF2 (thetaH θ)
      (f1_leading_data r).2 f2_leading_data.2 (h_leading_data θ).2
      (f1_f2_coprime r) (f1_h_coprime r θ) (f2_h_coprime θ) v hv

theorem target_relation_coefficients (r θ : ℂ) (v : Fin 2 → WeightedPoly)
    (hv : (∑ i, v i * surfaceEquations r θ i)=0) :
    ∀ i, v i ∈ surfaceIdeal r θ := by
  simpa only [surfaceIdeal,surfaceEquations] using
    CycleQ2MonicRegular.pair_relation_coefficients auxiliaryOrder
      (actualSeedEquation r θ) (thetaH θ)
      (F_leading_data r θ).2 (h_leading_data θ).2
      (F_h_coprime r θ) v hv

section ScalarExtension
variable {S : Type*} [CommRing S] [Algebra WeightedPoly S]

/-- The three original equation classes form a basis on any scalar
extension of the actual curve quotient, including the whole quotient. -/
def seedConormalBasis (r θ : ℂ)
    (hI : ∀ p ∈ ambientCurveIdeal r θ, algebraMap WeightedPoly S p=0) :
    Module.Basis (Fin 3) S (S ⊗[WeightedPoly] (ambientCurveIdeal r θ).Cotangent) :=
  CycleQ2ConormalRegular.conormalBasis (ambientCurveIdeal r θ)
    (curveEquations r θ) rfl hI (source_relation_coefficients r θ)

@[simp] theorem seedConormalBasis_apply (r θ : ℂ)
    (hI : ∀ p ∈ ambientCurveIdeal r θ, algebraMap WeightedPoly S p=0) (i : Fin 3) :
    seedConormalBasis r θ hI i = (1:S) ⊗ₜ[WeightedPoly] conormalGenerator r θ i :=
  CycleQ2ConormalRegular.conormalBasis_apply _ _ _ _ _ _

/-- The two target equation classes also form a global basis after
restriction to the curve. No g1- or g2-unit condition is needed. -/
def surfaceConormalBasis (r θ : ℂ)
    (hI : ∀ p ∈ ambientCurveIdeal r θ, algebraMap WeightedPoly S p=0) :
    Module.Basis (Fin 2) S (S ⊗[WeightedPoly] (surfaceIdeal r θ).Cotangent) :=
  CycleQ2ConormalRegular.conormalBasis (surfaceIdeal r θ)
    (surfaceEquations r θ) rfl
    (fun p hp => hI p (surfaceIdeal_le_curveIdeal r θ hp))
    (target_relation_coefficients r θ)

@[simp] theorem surfaceConormalBasis_apply (r θ : ℂ)
    (hI : ∀ p ∈ ambientCurveIdeal r θ, algebraMap WeightedPoly S p=0) (j : Fin 2) :
    surfaceConormalBasis r θ hI j =
      generator (S := S) (surfaceIdeal r θ) (surfaceEquations r θ) rfl j :=
  CycleQ2ConormalRegular.conormalBasis_apply _ _ _ _ _ _

/-- Both sides of the natural dual cotangent map are now expressed in
genuine global equation-class bases. -/
theorem naturalNormalMap_in_global_equation_bases
    [Algebra ℂ S] [IsScalarTower ℂ WeightedPoly S] (r θ : ℂ)
    (hI : ∀ p ∈ ambientCurveIdeal r θ, algebraMap WeightedPoly S p=0)
    (φ : S ⊗[WeightedPoly] (ambientCurveIdeal r θ).Cotangent →ₗ[S] S) :
    ((surfaceConormalBasis r θ hI).constr S).symm (naturalNormalMap r θ φ) =
      equationMap (algebraMap WeightedPoly S (originalG1 r))
        (algebraMap WeightedPoly S originalG2) (algebraMap WeightedPoly S (thetaK θ))
        (((seedConormalBasis r θ hI).constr S).symm φ) := by
  change (fun j => naturalNormalMap r θ φ (surfaceConormalBasis r θ hI j)) =
    equationMap _ _ _ (fun i => φ (seedConormalBasis r θ hI i))
  simpa only [surfaceConormalBasis_apply,seedConormalBasis_apply] using
    naturalNormalMap_equation_coordinates (S := S) r θ φ

end ScalarExtension
end CycleQ2SeedGlobalConormal

#print axioms CycleQ2SeedGlobalConormal.seedConormalBasis
#print axioms CycleQ2SeedGlobalConormal.surfaceConormalBasis
#print axioms CycleQ2SeedGlobalConormal.naturalNormalMap_in_global_equation_bases
end
end


/- Component: continuation_20261112/UniversalSurfaceRestrictions.lean -/
section
/-! # Canonical restriction maps and the actual coordinate Čech kernel -/

noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2UniversalSurfaceRestrictions

open MvPolynomial CycleQ2IncidenceNormalForm CycleQ2UniversalSurface
  CycleQ2SeedQuotientFiniteFree
  CycleQ2SeedCechThreeOpen CycleQ2SeedCechLocalization CycleQ2UniversalSurfaceLocalizedBasis

variable (R : Type*) [CommRing R]

instance surfaceLocalAway (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R) (s : Finset (Fin 3)) :
    IsLocalization.Away (algebraMap (Base R) (SurfaceRing R hcoeff Fcoeff) (baseProduct R s))
      (SurfaceLocal R hcoeff Fcoeff s) := by
  have hh : Algebra.algebraMapSubmonoid (SurfaceRing R hcoeff Fcoeff)
      (Submonoid.powers (baseProduct R s)) =
      Submonoid.powers (algebraMap (Base R) (SurfaceRing R hcoeff Fcoeff) (baseProduct R s)) := by
    exact Submonoid.map_powers _ _
  rw [IsLocalization.Away, ← hh]
  infer_instance

theorem baseProduct_dvd {s t : Finset (Fin 3)} (hst : s ⊆ t) :
    baseProduct R s ∣ baseProduct R t :=
  Finset.prod_dvd_prod_of_subset s t (fun i ↦ X i) hst

theorem surfaceProduct_isUnit (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R) {s t : Finset (Fin 3)} (hst : s ⊆ t) :
    IsUnit (algebraMap (SurfaceRing R hcoeff Fcoeff) (SurfaceLocal R hcoeff Fcoeff t)
      (algebraMap (Base R) (SurfaceRing R hcoeff Fcoeff) (baseProduct R s))) := by
  apply IsLocalization.Away.isUnit_of_dvd (S := SurfaceLocal R hcoeff Fcoeff t)
    (algebraMap (Base R) (SurfaceRing R hcoeff Fcoeff) (baseProduct R t))
  exact map_dvd (algebraMap (Base R) (SurfaceRing R hcoeff Fcoeff)) (baseProduct_dvd R hst)

/-- The universal localization map, with no chosen Laurent inverse. -/
def restriction (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R) {s t : Finset (Fin 3)} (hst : s ⊆ t) :
    SurfaceLocal R hcoeff Fcoeff s →+* SurfaceLocal R hcoeff Fcoeff t :=
  IsLocalization.Away.lift
    (S := SurfaceLocal R hcoeff Fcoeff s)
    (P := SurfaceLocal R hcoeff Fcoeff t)
    (g := algebraMap (SurfaceRing R hcoeff Fcoeff) (SurfaceLocal R hcoeff Fcoeff t))
    (algebraMap (Base R) (SurfaceRing R hcoeff Fcoeff) (baseProduct R s))
    (surfaceProduct_isUnit R hcoeff Fcoeff hst)

@[simp] theorem restriction_algebraMap (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R) {s t : Finset (Fin 3)} (hst : s ⊆ t)
    (p : SurfaceRing R hcoeff Fcoeff) :
    restriction R hcoeff Fcoeff hst (algebraMap (SurfaceRing R hcoeff Fcoeff) (SurfaceLocal R hcoeff Fcoeff s) p) =
      algebraMap (SurfaceRing R hcoeff Fcoeff) (SurfaceLocal R hcoeff Fcoeff t) p :=
  IsLocalization.Away.lift_eq (S := SurfaceLocal R hcoeff Fcoeff s)
    (P := SurfaceLocal R hcoeff Fcoeff t) _ (surfaceProduct_isUnit R hcoeff Fcoeff hst) p

theorem coordinates_mul_base [Nontrivial R] (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R) (s : Finset (Fin 3))
    (p : SurfaceLocal R hcoeff Fcoeff s) (c : Base R) (ab : ShiftIndex) :
    localizedCoordinates R hcoeff Fcoeff s
      (p * algebraMap (SurfaceRing R hcoeff Fcoeff) (SurfaceLocal R hcoeff Fcoeff s)
        (algebraMap (Base R) (SurfaceRing R hcoeff Fcoeff) c)) ab =
      baseToLaurent R c * localizedCoordinates R hcoeff Fcoeff s p ab := by
  rw [← IsScalarTower.algebraMap_apply (Base R) (SurfaceRing R hcoeff Fcoeff) (SurfaceLocal R hcoeff Fcoeff s) c,
    IsScalarTower.algebraMap_apply (Base R) (coordinateLocalization R s) (SurfaceLocal R hcoeff Fcoeff s) c,
    mul_comm p, ← Algebra.smul_def]
  rw [localizedCoordinates_smul, localizationToLaurent_algebraMap]

/-- Canonical restriction becomes literal inclusion in common Laurent coordinates. -/
theorem coordinates_restriction [Nontrivial R] (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R)
    {s t : Finset (Fin 3)} (hst : s ⊆ t) (z : SurfaceLocal R hcoeff Fcoeff s) (ab : ShiftIndex) :
    localizedCoordinates R hcoeff Fcoeff t (restriction R hcoeff Fcoeff hst z) ab =
      localizedCoordinates R hcoeff Fcoeff s z ab := by
  obtain ⟨n, p, hp⟩ := IsLocalization.Away.surj
    (algebraMap (Base R) (SurfaceRing R hcoeff Fcoeff) (baseProduct R s)) z
  have hp' : z * algebraMap (SurfaceRing R hcoeff Fcoeff) (SurfaceLocal R hcoeff Fcoeff s)
      (algebraMap (Base R) (SurfaceRing R hcoeff Fcoeff) (baseProduct R s ^ n)) =
      algebraMap (SurfaceRing R hcoeff Fcoeff) (SurfaceLocal R hcoeff Fcoeff s) p := by
    simpa only [map_pow] using hp
  have hs := congrArg (fun z ↦ localizedCoordinates R hcoeff Fcoeff s z ab) hp'
  simp only [coordinates_mul_base, localizedCoordinates_algebraMap] at hs
  have ht := congrArg (restriction R hcoeff Fcoeff hst) hp'
  simp only [map_mul, restriction_algebraMap] at ht
  have ht' := congrArg (fun z ↦ localizedCoordinates R hcoeff Fcoeff t z ab) ht
  simp only [coordinates_mul_base, localizedCoordinates_algebraMap] at ht'
  have hu : IsUnit (baseToLaurent R (baseProduct R s ^ n)) := by
    rw [map_pow, baseToLaurent_baseProduct]
    exact (T_isUnit R _).pow n
  exact hu.mul_right_injective (ht'.trans hs.symm)

/-- Every graded one-cocycle for the canonical three-coordinate localization
complex of the actual universal normalized quotient is an actual coboundary. -/
theorem coordinateCech_exact [Nontrivial R] (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R) (g : LaurentGrade)
    (p01 : SurfaceLocal R hcoeff Fcoeff {0, 1}) (p02 : SurfaceLocal R hcoeff Fcoeff {0, 2})
    (p12 : SurfaceLocal R hcoeff Fcoeff {1, 2})
    (hg01 : ∀ ab, HasGrade ab g (localizedCoordinates R hcoeff Fcoeff {0, 1} p01 ab))
    (hg02 : ∀ ab, HasGrade ab g (localizedCoordinates R hcoeff Fcoeff {0, 2} p02 ab))
    (hg12 : ∀ ab, HasGrade ab g (localizedCoordinates R hcoeff Fcoeff {1, 2} p12 ab))
    (hc : restriction R hcoeff Fcoeff (show ({0, 1} : Finset (Fin 3)) ⊆ Finset.univ by decide) p01 -
      restriction R hcoeff Fcoeff (show ({0, 2} : Finset (Fin 3)) ⊆ Finset.univ by decide) p02 +
      restriction R hcoeff Fcoeff (show ({1, 2} : Finset (Fin 3)) ⊆ Finset.univ by decide) p12 = 0) :
    ∃ (q0 : SurfaceLocal R hcoeff Fcoeff {0}) (q1 : SurfaceLocal R hcoeff Fcoeff {1})
      (q2 : SurfaceLocal R hcoeff Fcoeff {2}),
      (∀ ab, HasGrade ab g (localizedCoordinates R hcoeff Fcoeff {0} q0 ab)) ∧
      (∀ ab, HasGrade ab g (localizedCoordinates R hcoeff Fcoeff {1} q1 ab)) ∧
      (∀ ab, HasGrade ab g (localizedCoordinates R hcoeff Fcoeff {2} q2 ab)) ∧
      p01 = restriction R hcoeff Fcoeff (show ({1} : Finset (Fin 3)) ⊆ {0, 1} by decide) q1 -
        restriction R hcoeff Fcoeff (show ({0} : Finset (Fin 3)) ⊆ {0, 1} by decide) q0 ∧
      p02 = restriction R hcoeff Fcoeff (show ({2} : Finset (Fin 3)) ⊆ {0, 2} by decide) q2 -
        restriction R hcoeff Fcoeff (show ({0} : Finset (Fin 3)) ⊆ {0, 2} by decide) q0 ∧
      p12 = restriction R hcoeff Fcoeff (show ({2} : Finset (Fin 3)) ⊆ {1, 2} by decide) q2 -
        restriction R hcoeff Fcoeff (show ({1} : Finset (Fin 3)) ⊆ {1, 2} by decide) q1 := by
  have hc' (ab : ShiftIndex) : localizedCoordinates R hcoeff Fcoeff {0, 1} p01 ab -
      localizedCoordinates R hcoeff Fcoeff {0, 2} p02 ab +
      localizedCoordinates R hcoeff Fcoeff {1, 2} p12 ab = 0 := by
    have hh := congrArg (fun z ↦ localizedCoordinates R hcoeff Fcoeff Finset.univ z ab) hc
    simpa only [map_add, map_sub, map_zero, Pi.add_apply, Pi.sub_apply, Pi.zero_apply,
      coordinates_restriction] using hh
  obtain ⟨q0, q1, q2, hg0, hg1, hg2, he01, he02, he12⟩ :=
    localized_nineSummand_kernel R hcoeff Fcoeff g p01 p02 p12 hg01 hg02 hg12 hc'
  refine ⟨q0, q1, q2, hg0, hg1, hg2, ?_, ?_, ?_⟩
  · apply localizedCoordinates_injective R hcoeff Fcoeff {0, 1}
    funext ab
    simpa only [map_sub, Pi.sub_apply, coordinates_restriction] using he01 ab
  · apply localizedCoordinates_injective R hcoeff Fcoeff {0, 2}
    funext ab
    simpa only [map_sub, Pi.sub_apply, coordinates_restriction] using he02 ab
  · apply localizedCoordinates_injective R hcoeff Fcoeff {1, 2}
    funext ab
    simpa only [map_sub, Pi.sub_apply, coordinates_restriction] using he12 ab

end CycleQ2UniversalSurfaceRestrictions

#print axioms CycleQ2UniversalSurfaceRestrictions.coordinateCech_exact
end
end


/- Component: continuation_20261112/SeedSurfaceBranchSparse.lean -/
section
namespace CycleQ2SeedSurfaceBranchSparse
open CycleQ2SeedSurfaceSparsePolynomial
open scoped BigOperators

def denominator (j : Fin 3) : GaussianInt := ![denominator1,denominator2,denominator3] j
def multipliers (j : Fin 3) : Fin 8 → Sparse := ![multipliers1,multipliers2,multipliers3] j

theorem identity {R : Type*} [CommRing R] (j : Fin 3) (φ : GaussianInt →+* R)
    (x : Fin 5 → R) :
    φ (denominator j) * x j.succ.castSucc^17 =
      ∑ k, eval φ x (multipliers j k) * eval φ x (generators k) := by
  fin_cases j
  · exact identity1 φ x
  · exact identity2 φ x
  · exact identity3 φ x

end CycleQ2SeedSurfaceBranchSparse

#print axioms CycleQ2SeedSurfaceBranchSparse.identity
end


/- Component: continuation_20261112/SeedActualNormalCech.lean -/
section
/-!
# The genuine normal connecting class on the two actual seed opens

The two coefficient rings and their overlap are the existing localizations
of the actual curve, with the polynomial algebra structures supplied by
w = -x2². Global equation-class conormal bases realize the local lift
formulas as genuine normal homomorphisms. Their canonical Hom restrictions
have equal target image, so their difference defines an actual kernel
cochain. The kernel Cech quotient is identified with the scalar quotient
by the two restriction images, and the connecting class corresponds to
normalOverlapCoefficient.

This is the ungraded two-open Cech module of the affine cone. Its graded
pieces, projective sheaf interpretation, and Abel–Jacobi comparison are
separate steps. The final residue theorem is an identity on the genuine
connecting representative, using the previously constructed Laurent maps.
-/

noncomputable section
open scoped TensorProduct
set_option autoImplicit false
set_option maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2ActualNormalCech

open CycleQ2ConormalJacobian CycleQ2NaturalNormalMap CycleQ2NormalConnecting
  CycleQ2SeedTrace CycleQ2GenuineNormalConnecting CycleQ2NormalRestriction
  CycleQ2SeedGlobalConormal CycleQ2SeedCechTheta

/-- The literal five-variable curve map, as a complex algebra homomorphism. -/
def ambientCurveAlg (r θ : ℂ) : P →ₐ[ℂ] CurveRing r θ :=
  (Ideal.Quotient.mkₐ ℂ (CycleQ2SeedCechTheta.curveIdeal r θ)).comp substitute

@[simp] theorem ambientCurveAlg_apply (r θ : ℂ) (p : P) :
    ambientCurveAlg r θ p = ambientCurveMap r θ p := rfl

/-- Cache the standard complex actions before introducing the polynomial
algebra structures on the reducible localization aliases. -/
instance (priority := 2000) firstComplexAlgebra (r θ : ℂ) : Algebra ℂ (FirstOpen r θ) :=
  inferInstance
instance (priority := 2000) firstComplexSMul (r θ : ℂ) : SMul ℂ (FirstOpen r θ) :=
  (firstComplexAlgebra r θ).toSMul
instance (priority := 2000) firstComplexModule (r θ : ℂ) : Module ℂ (FirstOpen r θ) :=
  @Algebra.toModule ℂ (FirstOpen r θ) _ _ (firstComplexAlgebra r θ)

instance (priority := 2000) secondComplexAlgebra (r θ : ℂ) : Algebra ℂ (SecondOpen r θ) :=
  inferInstance
instance (priority := 2000) secondComplexSMul (r θ : ℂ) : SMul ℂ (SecondOpen r θ) :=
  (secondComplexAlgebra r θ).toSMul
instance (priority := 2000) secondComplexModule (r θ : ℂ) : Module ℂ (SecondOpen r θ) :=
  @Algebra.toModule ℂ (SecondOpen r θ) _ _ (secondComplexAlgebra r θ)

instance (priority := 2000) overlapComplexAlgebra (r θ : ℂ) : Algebra ℂ (Overlap r θ) :=
  inferInstance
instance (priority := 2000) overlapComplexSMul (r θ : ℂ) : SMul ℂ (Overlap r θ) :=
  (overlapComplexAlgebra r θ).toSMul
instance (priority := 2000) overlapComplexModule (r θ : ℂ) : Module ℂ (Overlap r θ) :=
  @Algebra.toModule ℂ (Overlap r θ) _ _ (overlapComplexAlgebra r θ)

def firstAmbientAlg (r θ : ℂ) : P →ₐ[ℂ] FirstOpen r θ :=
  (IsScalarTower.toAlgHom ℂ (CurveRing r θ) (FirstOpen r θ)).comp (ambientCurveAlg r θ)

def secondAmbientAlg (r θ : ℂ) : P →ₐ[ℂ] SecondOpen r θ :=
  (IsScalarTower.toAlgHom ℂ (CurveRing r θ) (SecondOpen r θ)).comp (ambientCurveAlg r θ)

def overlapAmbientAlg (r θ : ℂ) : P →ₐ[ℂ] Overlap r θ :=
  (IsScalarTower.toAlgHom ℂ (CurveRing r θ) (Overlap r θ)).comp (ambientCurveAlg r θ)

instance (priority := 2000) firstAlgebra (r θ : ℂ) : Algebra P (FirstOpen r θ) :=
  (firstAmbientAlg r θ).toRingHom.toAlgebra
instance (priority := 2000) secondAlgebra (r θ : ℂ) : Algebra P (SecondOpen r θ) :=
  (secondAmbientAlg r θ).toRingHom.toAlgebra
instance (priority := 2000) overlapAlgebra (r θ : ℂ) : Algebra P (Overlap r θ) :=
  (overlapAmbientAlg r θ).toRingHom.toAlgebra

/-- These instances use exactly the actions of the preceding algebras;
they prevent expensive rediscovery through localization and quotient types. -/
instance (priority := 2000) firstPolynomialSMul (r θ : ℂ) : SMul P (FirstOpen r θ) :=
  (firstAlgebra r θ).toSMul
instance (priority := 2000) firstPolynomialModule (r θ : ℂ) : Module P (FirstOpen r θ) :=
  @Algebra.toModule P (FirstOpen r θ) _ _ (firstAlgebra r θ)

instance (priority := 2000) secondPolynomialSMul (r θ : ℂ) : SMul P (SecondOpen r θ) :=
  (secondAlgebra r θ).toSMul
instance (priority := 2000) secondPolynomialModule (r θ : ℂ) : Module P (SecondOpen r θ) :=
  @Algebra.toModule P (SecondOpen r θ) _ _ (secondAlgebra r θ)

instance (priority := 2000) overlapPolynomialSMul (r θ : ℂ) : SMul P (Overlap r θ) :=
  (overlapAlgebra r θ).toSMul
instance (priority := 2000) overlapPolynomialModule (r θ : ℂ) : Module P (Overlap r θ) :=
  @Algebra.toModule P (Overlap r θ) _ _ (overlapAlgebra r θ)

instance firstTower (r θ : ℂ) : IsScalarTower ℂ P (FirstOpen r θ) :=
  IsScalarTower.of_algHom (firstAmbientAlg r θ)
instance secondTower (r θ : ℂ) : IsScalarTower ℂ P (SecondOpen r θ) :=
  IsScalarTower.of_algHom (secondAmbientAlg r θ)
instance overlapTower (r θ : ℂ) : IsScalarTower ℂ P (Overlap r θ) :=
  IsScalarTower.of_algHom (overlapAmbientAlg r θ)

@[simp] theorem first_algebraMap (r θ : ℂ) (p : P) :
    algebraMap P (FirstOpen r θ) p = firstOpenAmbient r θ p := rfl
@[simp] theorem second_algebraMap (r θ : ℂ) (p : P) :
    algebraMap P (SecondOpen r θ) p = secondOpenAmbient r θ p := rfl
@[simp] theorem overlap_algebraMap (r θ : ℂ) (p : P) :
    algebraMap P (Overlap r θ) p = overlapAmbient r θ p := rfl

/-- No new annihilation hypothesis is needed: the actual substitution map
kills the three literal curve equations. -/
theorem ambientCurveMap_kills (r θ : ℂ) (p : P)
    (hp : p ∈ ambientCurveIdeal r θ) : ambientCurveMap r θ p = 0 := by
  have hi : ambientCurveIdeal r θ ≤ RingHom.ker (ambientCurveMap r θ) := by
    rw [ambientCurveIdeal, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    fin_cases i <;>
      simp [curveEquations, RingHom.mem_ker]
  exact hi hp

theorem first_annihilates (r θ : ℂ) :
    ∀ p ∈ ambientCurveIdeal r θ, algebraMap P (FirstOpen r θ) p = 0 := by
  intro p hp
  change algebraMap (CurveRing r θ) (FirstOpen r θ) (ambientCurveMap r θ p) = 0
  rw [ambientCurveMap_kills r θ p hp, map_zero]

theorem second_annihilates (r θ : ℂ) :
    ∀ p ∈ ambientCurveIdeal r θ, algebraMap P (SecondOpen r θ) p = 0 := by
  intro p hp
  change algebraMap (CurveRing r θ) (SecondOpen r θ) (ambientCurveMap r θ p) = 0
  rw [ambientCurveMap_kills r θ p hp, map_zero]

theorem overlap_annihilates (r θ : ℂ) :
    ∀ p ∈ ambientCurveIdeal r θ, algebraMap P (Overlap r θ) p = 0 := by
  intro p hp
  change algebraMap (CurveRing r θ) (Overlap r θ) (ambientCurveMap r θ p) = 0
  rw [ambientCurveMap_kills r θ p hp, map_zero]

/-- The existing restriction ring maps respect the literal polynomial action. -/
def firstRestrictionAlg (r θ : ℂ) : FirstOpen r θ →ₐ[P] Overlap r θ where
  __ := firstRestriction r θ
  commutes' p := by
    change firstRestriction r θ (firstOpenAmbient r θ p) = overlapAmbient r θ p
    exact IsLocalization.Away.awayToAwayRight_eq _ _ _

def secondRestrictionAlg (r θ : ℂ) : SecondOpen r θ →ₐ[P] Overlap r θ where
  __ := secondRestriction r θ
  commutes' p := by
    change secondRestriction r θ (secondOpenAmbient r θ p) = overlapAmbient r θ p
    exact IsLocalization.Away.awayToAwayLeft_eq _ _ _

@[simp] theorem firstRestrictionAlg_apply (r θ : ℂ) (x : FirstOpen r θ) :
    firstRestrictionAlg r θ x = firstRestriction r θ x := rfl
@[simp] theorem secondRestrictionAlg_apply (r θ : ℂ) (x : SecondOpen r θ) :
    secondRestrictionAlg r θ x = secondRestriction r θ x := rfl

def firstBasis (r θ : ℂ) :
    Module.Basis (Fin 3) (FirstOpen r θ) (CurveConormal (S := FirstOpen r θ) r θ) :=
  seedConormalBasis (S := FirstOpen r θ) r θ (first_annihilates r θ)
def secondBasis (r θ : ℂ) :
    Module.Basis (Fin 3) (SecondOpen r θ) (CurveConormal (S := SecondOpen r θ) r θ) :=
  seedConormalBasis (S := SecondOpen r θ) r θ (second_annihilates r θ)
def overlapBasis (r θ : ℂ) :
    Module.Basis (Fin 3) (Overlap r θ) (CurveConormal (S := Overlap r θ) r θ) :=
  seedConormalBasis (S := Overlap r θ) r θ (overlap_annihilates r θ)

@[simp] theorem firstBasis_apply (r θ : ℂ) (i : Fin 3) :
    firstBasis r θ i = curveClass r θ i :=
  seedConormalBasis_apply (S := FirstOpen r θ) r θ (first_annihilates r θ) i
@[simp] theorem secondBasis_apply (r θ : ℂ) (i : Fin 3) :
    secondBasis r θ i = curveClass r θ i :=
  seedConormalBasis_apply (S := SecondOpen r θ) r θ (second_annihilates r θ) i
@[simp] theorem overlapBasis_apply (r θ : ℂ) (i : Fin 3) :
    overlapBasis r θ i = curveClass r θ i :=
  seedConormalBasis_apply (S := Overlap r θ) r θ (overlap_annihilates r θ) i

theorem firstUnit_value (r θ : ℂ) :
    (firstOpenUnit r θ : FirstOpen r θ) = algebraMap P (FirstOpen r θ) (originalG1 r) :=
  IsUnit.unit_spec _
theorem secondUnit_value (r θ : ℂ) :
    (secondOpenUnit r θ : SecondOpen r θ) = algebraMap P (SecondOpen r θ) originalG2 :=
  IsUnit.unit_spec _
theorem firstOverlapUnit_value (r θ : ℂ) :
    (firstOverlapUnit r θ : Overlap r θ) = algebraMap P (Overlap r θ) (originalG1 r) :=
  coe_firstOverlapUnit r θ
theorem secondOverlapUnit_value (r θ : ℂ) :
    (secondOverlapUnit r θ : Overlap r θ) = algebraMap P (Overlap r θ) originalG2 :=
  coe_secondOverlapUnit r θ

/-- The actual normal map is surjective on the first open: every genuine
target homomorphism is lifted by its two actual equation values. -/
theorem first_normal_surjective (r θ : ℂ) :
    Function.Surjective (naturalNormalMap (S := FirstOpen r θ) r θ) := by
  intro ψ
  refine ⟨firstGenuineLift r θ (firstBasis r θ) (firstOpenUnit r θ)
    (-ψ (surfaceClass r θ 0)) (-ψ (surfaceClass r θ 1)), ?_⟩
  apply surfaceNormal_ext r θ
  intro j
  have hh := congrFun (firstGenuineLift_equations r θ (firstBasis r θ)
    (firstBasis_apply r θ) (firstOpenUnit r θ) (firstUnit_value r θ)
    (-ψ (surfaceClass r θ 0)) (-ψ (surfaceClass r θ 1))) j
  fin_cases j <;> simpa using hh

/-- Surjectivity on the complementary actual open. -/
theorem second_normal_surjective (r θ : ℂ) :
    Function.Surjective (naturalNormalMap (S := SecondOpen r θ) r θ) := by
  intro ψ
  refine ⟨secondGenuineLift r θ (secondBasis r θ) (secondOpenUnit r θ)
    (-ψ (surfaceClass r θ 0)) (-ψ (surfaceClass r θ 1)), ?_⟩
  apply surfaceNormal_ext r θ
  intro j
  have hh := congrFun (secondGenuineLift_equations r θ (secondBasis r θ)
    (secondBasis_apply r θ) (secondOpenUnit r θ) (secondUnit_value r θ)
    (-ψ (surfaceClass r θ 0)) (-ψ (surfaceClass r θ 1))) j
  fin_cases j <;> simpa using hh

abbrev FirstKernel (r θ : ℂ) := NormalKernel (S := FirstOpen r θ) r θ
abbrev SecondKernel (r θ : ℂ) := NormalKernel (S := SecondOpen r θ) r θ
abbrev OverlapKernel (r θ : ℂ) := NormalKernel (S := Overlap r θ) r θ

/-- Cache the inherited additive groups and scalar modules of the genuine
kernel subtypes, keeping the same subtype operations and polynomial action. -/
instance (priority := 2000) firstKernelAddCommGroup (r θ : ℂ) :
    AddCommGroup (FirstKernel r θ) :=
  Submodule.addCommGroup (LinearMap.ker (naturalNormalMap (S := FirstOpen r θ) r θ))
instance (priority := 2000) firstKernelAddCommMonoid (r θ : ℂ) :
    AddCommMonoid (FirstKernel r θ) := (firstKernelAddCommGroup r θ).toAddCommMonoid
instance (priority := 2000) firstKernelPolynomialModule (r θ : ℂ) :
    Module P (FirstKernel r θ) := inferInstance

instance (priority := 2000) secondKernelAddCommGroup (r θ : ℂ) :
    AddCommGroup (SecondKernel r θ) :=
  Submodule.addCommGroup (LinearMap.ker (naturalNormalMap (S := SecondOpen r θ) r θ))
instance (priority := 2000) secondKernelAddCommMonoid (r θ : ℂ) :
    AddCommMonoid (SecondKernel r θ) := (secondKernelAddCommGroup r θ).toAddCommMonoid
instance (priority := 2000) secondKernelPolynomialModule (r θ : ℂ) :
    Module P (SecondKernel r θ) := inferInstance

instance (priority := 2000) overlapKernelAddCommGroup (r θ : ℂ) :
    AddCommGroup (OverlapKernel r θ) :=
  Submodule.addCommGroup (LinearMap.ker (naturalNormalMap (S := Overlap r θ) r θ))
instance (priority := 2000) overlapKernelAddCommMonoid (r θ : ℂ) :
    AddCommMonoid (OverlapKernel r θ) := (overlapKernelAddCommGroup r θ).toAddCommMonoid
instance (priority := 2000) overlapKernelPolynomialModule (r θ : ℂ) :
    Module P (OverlapKernel r θ) := inferInstance

def firstKernelEquivalence (r θ : ℂ) : FirstOpen r θ ≃ₗ[P] FirstKernel r θ :=
  (firstKernelEquiv r θ (firstBasis r θ) (firstBasis_apply r θ)
    (firstOpenUnit r θ) (firstUnit_value r θ)).restrictScalars P

def secondKernelEquivalence (r θ : ℂ) : SecondOpen r θ ≃ₗ[P] SecondKernel r θ :=
  (secondKernelEquiv r θ (secondBasis r θ) (secondBasis_apply r θ)
    (secondOpenUnit r θ) (secondUnit_value r θ)).restrictScalars P

def overlapKernelEquivalence (r θ : ℂ) : Overlap r θ ≃ₗ[P] OverlapKernel r θ :=
  (firstKernelEquiv r θ (overlapBasis r θ) (overlapBasis_apply r θ)
    (firstOverlapUnit r θ) (firstOverlapUnit_value r θ)).restrictScalars P

def firstKernelRestriction (r θ : ℂ) : FirstKernel r θ →ₗ[P] OverlapKernel r θ :=
  kernelRestriction r θ (firstRestrictionAlg r θ)
def secondKernelRestriction (r θ : ℂ) : SecondKernel r θ →ₗ[P] OverlapKernel r θ :=
  kernelRestriction r θ (secondRestrictionAlg r θ)

theorem firstKernelRestriction_trivialization (r θ : ℂ) (c : FirstOpen r θ) :
    firstKernelRestriction r θ (firstKernelEquivalence r θ c) =
      overlapKernelEquivalence r θ (firstRestriction r θ c) :=
  kernelParam_restriction r θ (firstRestrictionAlg r θ)
    (firstBasis r θ) (firstBasis_apply r θ)
    (overlapBasis r θ) (overlapBasis_apply r θ) c

theorem secondKernelRestriction_trivialization (r θ : ℂ) (c : SecondOpen r θ) :
    secondKernelRestriction r θ (secondKernelEquivalence r θ c) =
      overlapKernelEquivalence r θ (secondRestriction r θ c) :=
  kernelParam_restriction r θ (secondRestrictionAlg r θ)
    (secondBasis r θ) (secondBasis_apply r θ)
    (overlapBasis r θ) (overlapBasis_apply r θ) c

/-- Degree-unrestricted scalar Cech coboundaries on the two actual opens. -/
def scalarBoundaries (r θ : ℂ) : Submodule P (Overlap r θ) :=
  LinearMap.range (firstRestrictionAlg r θ).toLinearMap ⊔
    LinearMap.range (secondRestrictionAlg r θ).toLinearMap

/-- Genuine normal-kernel coboundaries using the canonical Hom restrictions. -/
def normalBoundaries (r θ : ℂ) : Submodule P (OverlapKernel r θ) :=
  LinearMap.range (firstKernelRestriction r θ) ⊔
    LinearMap.range (secondKernelRestriction r θ)

abbrev ScalarCech (r θ : ℂ) := (Overlap r θ) ⧸ scalarBoundaries r θ
abbrev NormalCech (r θ : ℂ) := (OverlapKernel r θ) ⧸ normalBoundaries r θ

private theorem map_first_range (r θ : ℂ) :
    (LinearMap.range (firstKernelRestriction r θ)).map
        (overlapKernelEquivalence r θ).symm.toLinearMap =
      LinearMap.range (firstRestrictionAlg r θ).toLinearMap := by
  ext z
  constructor
  · rintro ⟨x, ⟨y, rfl⟩, rfl⟩
    obtain ⟨c, rfl⟩ := (firstKernelEquivalence r θ).surjective y
    refine ⟨c, ?_⟩
    rw [firstKernelRestriction_trivialization]
    exact ((overlapKernelEquivalence r θ).symm_apply_apply (firstRestriction r θ c)).symm
  · rintro ⟨c, rfl⟩
    refine ⟨firstKernelRestriction r θ (firstKernelEquivalence r θ c),
      ⟨firstKernelEquivalence r θ c, rfl⟩, ?_⟩
    rw [firstKernelRestriction_trivialization]
    exact (overlapKernelEquivalence r θ).symm_apply_apply (firstRestriction r θ c)

private theorem map_second_range (r θ : ℂ) :
    (LinearMap.range (secondKernelRestriction r θ)).map
        (overlapKernelEquivalence r θ).symm.toLinearMap =
      LinearMap.range (secondRestrictionAlg r θ).toLinearMap := by
  ext z
  constructor
  · rintro ⟨x, ⟨y, rfl⟩, rfl⟩
    obtain ⟨c, rfl⟩ := (secondKernelEquivalence r θ).surjective y
    refine ⟨c, ?_⟩
    rw [secondKernelRestriction_trivialization]
    exact ((overlapKernelEquivalence r θ).symm_apply_apply (secondRestriction r θ c)).symm
  · rintro ⟨c, rfl⟩
    refine ⟨secondKernelRestriction r θ (secondKernelEquivalence r θ c),
      ⟨secondKernelEquivalence r θ c, rfl⟩, ?_⟩
    rw [secondKernelRestriction_trivialization]
    exact (overlapKernelEquivalence r θ).symm_apply_apply (secondRestriction r θ c)

theorem normalBoundaries_map (r θ : ℂ) :
    (normalBoundaries r θ).map (overlapKernelEquivalence r θ).symm.toLinearMap =
      scalarBoundaries r θ := by
  rw [normalBoundaries, Submodule.map_sup, map_first_range, map_second_range]
  rfl

/-- The actual kernel Cech module is canonically identified with the scalar
Cech module by its equation generator, compatibly on both opens. -/
def normalCechEquivalence (r θ : ℂ) : NormalCech r θ ≃ₗ[P] ScalarCech r θ :=
  Submodule.Quotient.equiv (normalBoundaries r θ) (scalarBoundaries r θ)
    (overlapKernelEquivalence r θ).symm (normalBoundaries_map r θ)

def actualFirstLift (r θ : ℂ) (A L : P) : CurveNormal (S := FirstOpen r θ) r θ :=
  fromCoordinates r θ (firstBasis r θ) (firstNormalLift r θ A L)
def actualSecondLift (r θ : ℂ) (A L : P) : CurveNormal (S := SecondOpen r θ) r θ :=
  fromCoordinates r θ (secondBasis r θ) (secondNormalLift r θ A L)

theorem actualFirstLift_restriction (r θ : ℂ) (A L : P) :
    curveRestriction r θ (firstRestrictionAlg r θ) (actualFirstLift r θ A L) =
      firstGenuineLift r θ (overlapBasis r θ) (firstOverlapUnit r θ)
        (overlapAmbient r θ A) (overlapAmbient r θ L) := by
  rw [actualFirstLift, fromCoordinates_restriction r θ (firstRestrictionAlg r θ)
    (firstBasis r θ) (firstBasis_apply r θ) (overlapBasis r θ) (overlapBasis_apply r θ)]
  change fromCoordinates r θ (overlapBasis r θ)
      (fun i => firstRestriction r θ (firstNormalLift r θ A L i)) = _
  rw [firstNormalLift_restriction]
  rfl

theorem actualSecondLift_restriction (r θ : ℂ) (A L : P) :
    curveRestriction r θ (secondRestrictionAlg r θ) (actualSecondLift r θ A L) =
      secondGenuineLift r θ (overlapBasis r θ) (secondOverlapUnit r θ)
        (overlapAmbient r θ A) (overlapAmbient r θ L) := by
  rw [actualSecondLift, fromCoordinates_restriction r θ (secondRestrictionAlg r θ)
    (secondBasis r θ) (secondBasis_apply r θ) (overlapBasis r θ) (overlapBasis_apply r θ)]
  change fromCoordinates r θ (overlapBasis r θ)
      (fun i => secondRestriction r θ (secondNormalLift r θ A L i)) = _
  rw [secondNormalLift_restriction]
  rfl

/-- Difference of restrictions of actual normal lifts, in the actual kernel. -/
def connectingRepresentative (r θ : ℂ) (A L : P) : OverlapKernel r θ :=
  ⟨curveRestriction r θ (firstRestrictionAlg r θ) (actualFirstLift r θ A L) -
    curveRestriction r θ (secondRestrictionAlg r θ) (actualSecondLift r θ A L), by
    change naturalNormalMap r θ (_ - _) = 0
    rw [map_sub, actualFirstLift_restriction, actualSecondLift_restriction,
      genuineLifts_same_image r θ (overlapBasis r θ) (overlapBasis_apply r θ)
        (firstOverlapUnit r θ) (secondOverlapUnit r θ)
        (firstOverlapUnit_value r θ) (secondOverlapUnit_value r θ), sub_self]⟩

/-- The genuine kernel representative is the old scalar coefficient times
the actual intrinsic generator, with no assumed connecting-class identity. -/
theorem connectingRepresentative_eq (r θ : ℂ) (A L : P) :
    connectingRepresentative r θ A L =
      overlapKernelEquivalence r θ (normalOverlapCoefficient r θ A L) := by
  apply Subtype.ext
  change curveRestriction r θ (firstRestrictionAlg r θ) (actualFirstLift r θ A L) -
      curveRestriction r θ (secondRestrictionAlg r θ) (actualSecondLift r θ A L) = _
  rw [actualFirstLift_restriction, actualSecondLift_restriction,
    genuineLift_difference r θ (overlapBasis r θ)
      (firstOverlapUnit r θ) (secondOverlapUnit r θ)
      (firstOverlapUnit_value r θ) (secondOverlapUnit_value r θ)]
  rfl

def connectingClass (r θ : ℂ) (A L : P) : NormalCech r θ :=
  Submodule.Quotient.mk (connectingRepresentative r θ A L)

/-- The actual two-open connecting class has exactly the previously
computed scalar Cech class. -/
theorem connectingClass_eq_scalar (r θ : ℂ) (A L : P) :
    normalCechEquivalence r θ (connectingClass r θ A L) =
      (Submodule.Quotient.mk (normalOverlapCoefficient r θ A L) : ScalarCech r θ) := by
  change (Submodule.Quotient.mk ((overlapKernelEquivalence r θ).symm
    (connectingRepresentative r θ A L)) : ScalarCech r θ) = _
  rw [connectingRepresentative_eq, LinearEquiv.symm_apply_apply]

/-- Altering either local lift by an arbitrary actual kernel section
changes the kernel cochain by a genuine two-open coboundary. -/
theorem connectingClass_change_lifts (r θ : ℂ) (A L : P)
    (a : FirstKernel r θ) (b : SecondKernel r θ) :
    (Submodule.Quotient.mk (connectingRepresentative r θ A L +
      firstKernelRestriction r θ a - secondKernelRestriction r θ b) : NormalCech r θ) =
        connectingClass r θ A L := by
  apply (Submodule.Quotient.eq (normalBoundaries r θ)).mpr
  have ha : firstKernelRestriction r θ a ∈ normalBoundaries r θ :=
    Submodule.mem_sup_left (show firstKernelRestriction r θ a ∈
      LinearMap.range (firstKernelRestriction r θ) from ⟨a, rfl⟩)
  have hb : secondKernelRestriction r θ b ∈ normalBoundaries r θ :=
    Submodule.mem_sup_right (show secondKernelRestriction r θ b ∈
      LinearMap.range (secondKernelRestriction r θ) from ⟨b, rfl⟩)
  change connectingRepresentative r θ A L + firstKernelRestriction r θ a -
    secondKernelRestriction r θ b - connectingRepresentative r θ A L ∈ _
  convert (normalBoundaries r θ).sub_mem ha hb using 1 <;> abel

/-- Scalar boundaries remain boundaries after multiplication by a function
from the actual curve ring; this does not require choosing a polynomial lift. -/
theorem scalarBoundaries_mul_base (r θ : ℂ) (z : Overlap r θ) (p : CurveRing r θ)
    (hz : z ∈ scalarBoundaries r θ) :
    z * algebraMap (CurveRing r θ) (Overlap r θ) p ∈ scalarBoundaries r θ := by
  obtain ⟨x, ⟨a, rfl⟩, y, ⟨b, rfl⟩, hab⟩ := Submodule.mem_sup.mp hz
  apply Submodule.mem_sup.mpr
  refine ⟨firstRestrictionAlg r θ (a * algebraMap (CurveRing r θ) (FirstOpen r θ) p),
    ⟨a * algebraMap (CurveRing r θ) (FirstOpen r θ) p, rfl⟩,
    secondRestrictionAlg r θ (b * algebraMap (CurveRing r θ) (SecondOpen r θ) p),
    ⟨b * algebraMap (CurveRing r θ) (SecondOpen r θ) p, rfl⟩, ?_⟩
  change firstRestriction r θ (a * algebraMap (CurveRing r θ) (FirstOpen r θ) p) +
    secondRestriction r θ (b * algebraMap (CurveRing r θ) (SecondOpen r θ) p) = _
  simp only [map_mul, firstRestriction, secondRestriction,
    IsLocalization.Away.awayToAwayRight_eq, IsLocalization.Away.awayToAwayLeft_eq]
  rw [← add_mul]
  exact congrArg (fun t : Overlap r θ => t * algebraMap (CurveRing r θ) (Overlap r θ) p) hab

theorem coefficient_boundary_of_connectingClass_zero (r θ : ℂ) (A L : P)
    (hz : connectingClass r θ A L = 0) :
    normalOverlapCoefficient r θ A L ∈ scalarBoundaries r θ := by
  have hh := congrArg (normalCechEquivalence r θ) hz
  rw [connectingClass_eq_scalar, map_zero] at hh
  exact (Submodule.Quotient.mk_eq_zero (scalarBoundaries r θ)).mp hh

theorem paired_boundary_of_connectingClass_zero (r θ : ℂ) (p : CycleQ2SeedTrace.Poly)
    (hz : connectingClass r θ derivativeA 0 = 0) :
    pairedNormalOverlap r θ p ∈ scalarBoundaries r θ := by
  exact scalarBoundaries_mul_base r θ _ (curveMap r θ p)
    (coefficient_boundary_of_connectingClass_zero r θ derivativeA 0 hz)

/-- Pair the genuine connecting representative with the actual cubic. The
residue comparison here is on representatives, before graded descent. -/
def pairedConnectingRepresentative (r θ : ℂ) (p : CycleQ2SeedTrace.Poly) : Overlap r θ :=
  (overlapKernelEquivalence r θ).symm
      (connectingRepresentative r θ CycleQ2NormalConnecting.derivativeA 0) *
    algebraMap (CurveRing r θ) (Overlap r θ) (curveMap r θ p)

theorem pairedConnectingRepresentative_eq (r θ : ℂ) (p : CycleQ2SeedTrace.Poly) :
    pairedConnectingRepresentative r θ p = CycleQ2NormalConnecting.pairedNormalOverlap r θ p := by
  rw [pairedConnectingRepresentative, connectingRepresentative_eq,
    LinearEquiv.symm_apply_apply]
  rfl

/-- The already computed incidence trace is now evaluated on a genuine
normal connecting representative, via the actual overlap localization. -/
theorem connectingRepresentative_residue (r θ : ℂ) (hr : r ≠ 0)
    (v : Fin 9 → ℂ) :
    CycleQ2SeedCechTheta.endpointResidue r θ false
        (overlapToLaurent r θ false hr
          (pairedConnectingRepresentative r θ (cubicDeformation v))) -
      CycleQ2SeedCechTheta.endpointResidue r θ true
        (overlapToLaurent r θ true hr
          (pairedConnectingRepresentative r θ (cubicDeformation v))) =
      -(3 * r)⁻¹ * derivativeTrace θ v := by
  simp only [pairedConnectingRepresentative_eq]
  exact actual_overlap_trace_deformation r θ hr v

end CycleQ2ActualNormalCech

#print axioms CycleQ2ActualNormalCech.normalCechEquivalence
#print axioms CycleQ2ActualNormalCech.connectingClass_eq_scalar
#print axioms CycleQ2ActualNormalCech.connectingClass_change_lifts
#print axioms CycleQ2ActualNormalCech.pairedConnectingRepresentative_eq

#print axioms CycleQ2ActualNormalCech.connectingRepresentative_residue
end
end


/- Component: continuation_20261112/UniversalSurfaceLinearCoordinates.lean -/
section
/-! # Scalar compatibility of the actual localized universal surface coordinates -/

noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2UniversalSurfaceLinearCoordinates

open MvPolynomial CycleQ2IncidenceNormalForm CycleQ2UniversalSurface
  CycleQ2SeedQuotientFiniteFree
  CycleQ2SeedCechThreeOpen CycleQ2SeedCechLocalization CycleQ2UniversalSurfaceLocalizedBasis
  CycleQ2UniversalSurfaceRestrictions

variable (R : Type*) [CommRing R]

theorem base_C_surface (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R) (c : R) :
    algebraMap (Base R) (SurfaceRing R hcoeff Fcoeff) (C c) = algebraMap R (SurfaceRing R hcoeff Fcoeff) c := by
  change Ideal.Quotient.mk _ (remainingInclusion R (C c)) = Ideal.Quotient.mk _ (C c)
  simp [remainingInclusion]

theorem localized_scalar_eq (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R) (s : Finset (Fin 3)) (c : R)
    (p : SurfaceLocal R hcoeff Fcoeff s) :
    algebraMap (Base R) (coordinateLocalization R s) (C c) • p = c • p := by
  simp only [Algebra.smul_def]
  rw [← IsScalarTower.algebraMap_apply (Base R) (coordinateLocalization R s) (SurfaceLocal R hcoeff Fcoeff s),
    IsScalarTower.algebraMap_apply (Base R) (SurfaceRing R hcoeff Fcoeff) (SurfaceLocal R hcoeff Fcoeff s), base_C_surface,
    ← IsScalarTower.algebraMap_apply R (SurfaceRing R hcoeff Fcoeff) (SurfaceLocal R hcoeff Fcoeff s)]

theorem localizedCoordinates_R_smul [Nontrivial R] (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R) (s : Finset (Fin 3))
    (c : R) (p : SurfaceLocal R hcoeff Fcoeff s) :
    localizedCoordinates R hcoeff Fcoeff s (c • p) = c • localizedCoordinates R hcoeff Fcoeff s p := by
  funext ab
  rw [← localized_scalar_eq R hcoeff Fcoeff s c p, localizedCoordinates_smul,
    localizationToLaurent_algebraMap]
  change baseToLaurent R (algebraMap R (Base R) c) * _ = c • _
  rw [AlgHom.commutes, Algebra.smul_def]

def linearCoordinates [Nontrivial R] (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R) (s : Finset (Fin 3)) :
    SurfaceLocal R hcoeff Fcoeff s →ₗ[R] (ShiftIndex → Laurent (R := R)) where
  __ := localizedCoordinates R hcoeff Fcoeff s
  map_smul' c p := localizedCoordinates_R_smul R hcoeff Fcoeff s c p

@[simp] theorem linearCoordinates_apply [Nontrivial R] (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R) (s : Finset (Fin 3))
    (p : SurfaceLocal R hcoeff Fcoeff s) :
    linearCoordinates R hcoeff Fcoeff s p = localizedCoordinates R hcoeff Fcoeff s p := rfl

def restrictionLinear [Nontrivial R] (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R) {s t : Finset (Fin 3)} (hst : s ⊆ t) :
    SurfaceLocal R hcoeff Fcoeff s →ₗ[R] SurfaceLocal R hcoeff Fcoeff t where
  __ := (restriction R hcoeff Fcoeff hst).toAddMonoidHom
  map_smul' c p := by
    apply localizedCoordinates_injective R hcoeff Fcoeff t
    funext ab
    change localizedCoordinates R hcoeff Fcoeff t (restriction R hcoeff Fcoeff hst (c • p)) ab =
      localizedCoordinates R hcoeff Fcoeff t (c • restriction R hcoeff Fcoeff hst p) ab
    simp only [localizedCoordinates_R_smul, Pi.smul_apply, coordinates_restriction]

end CycleQ2UniversalSurfaceLinearCoordinates

#print axioms CycleQ2UniversalSurfaceLinearCoordinates.linearCoordinates
#print axioms CycleQ2UniversalSurfaceLinearCoordinates.restrictionLinear
end
end


/- Component: continuation_20261112/SeedSurfaceBranchGradient.lean -/
section
/-! # The actual r=57 branch Jacobian cover

The exact Gaussian-integer identities are bound to the literal sextic
q=x0^6+x2^6-57^3*x1^3*x3^3 and cubic h=smoothH I.  They put the
seventeenth powers of x1,x2,x3 in the equation-and-Jacobian ideal.
The consequence concerns every prime on these three coordinate opens.
-/

noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 30000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2SeedSurfaceBranchGradient

open MvPolynomial CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations
open scoped BigOperators

def branchEquation : Poly ℂ :=
  X 0^6 + X 2^6 - C ((57 : ℂ)^3)*X 1^3*X 3^3

def minor (j k : Fin 4) : Poly ℂ :=
  pderiv j.castSucc branchEquation * pderiv k.castSucc (smoothH Complex.I) -
    pderiv k.castSucc branchEquation * pderiv j.castSucc (smoothH Complex.I)

def minorPairs : Fin 6 → Fin 4 × Fin 4 :=
  ![(0,1), (0,2), (0,3), (1,2), (1,3), (2,3)]

def generators : Fin 8 → Poly ℂ :=
  ![branchEquation, smoothH Complex.I, minor 0 1, minor 0 2, minor 0 3,
    minor 1 2, minor 1 3, minor 2 3]

def coefficientMap : GaussianInt →+* Poly ℂ :=
  (C : ℂ →+* Poly ℂ).comp GaussianInt.toComplex

def sparsePolynomial (p : CycleQ2SeedSurfaceSparsePolynomial.Sparse) : Poly ℂ :=
  CycleQ2SeedSurfaceSparsePolynomial.eval coefficientMap (fun j => X j) p

def witnesses (j : Fin 3) (k : Fin 8) : Poly ℂ :=
  sparsePolynomial (CycleQ2SeedSurfaceBranchSparse.multipliers j k)

theorem generators_binding (j : Fin 8) :
    sparsePolynomial (CycleQ2SeedSurfaceBranchSparse.generators j) = generators j := by
  have hc : (C (57 : ℂ) : Poly ℂ) = 57 := map_ofNat _ _
  have hn (k : Fin 5) : pderiv k (57 : Poly ℂ) = 0 := by
    rw [←hc]
    exact pderiv_C
  fin_cases j <;>
    simp [sparsePolynomial, coefficientMap, CycleQ2SeedSurfaceSparsePolynomial.eval,
      CycleQ2SeedSurfaceSparsePolynomial.termValue, CycleQ2SeedSurfaceSparsePolynomial.monomial,
      CycleQ2SeedSurfaceBranchSparse.generators, GaussianInt.toComplex,
      Zsqrtd.lift_apply_apply, generators, minor, branchEquation,
      smoothH, smoothB, smoothA, Derivation.leibniz, map_pow, map_ofNat, hn] <;> ring

theorem denominator_ne_zero (j : Fin 3) :
    (CycleQ2SeedSurfaceBranchSparse.denominator j : ℂ) ≠ 0 := by
  intro h
  have hz : CycleQ2SeedSurfaceBranchSparse.denominator j = 0 :=
    GaussianInt.toComplex_injective (h.trans (map_zero GaussianInt.toComplex).symm)
  have hre := congrArg Zsqrtd.re hz
  fin_cases j <;>
    norm_num [CycleQ2SeedSurfaceBranchSparse.denominator,
      CycleQ2SeedSurfaceBranchSparse.denominator1,
      CycleQ2SeedSurfaceBranchSparse.denominator2,
      CycleQ2SeedSurfaceBranchSparse.denominator3] at hre

theorem coordinate_power_identity (j : Fin 3) :
    C (CycleQ2SeedSurfaceBranchSparse.denominator j : ℂ) * X j.succ.castSucc^17 =
      ∑ k, witnesses j k * generators k := by
  calc
    C (CycleQ2SeedSurfaceBranchSparse.denominator j : ℂ) * X j.succ.castSucc^17 =
        ∑ k, witnesses j k *
          sparsePolynomial (CycleQ2SeedSurfaceBranchSparse.generators k) :=
      CycleQ2SeedSurfaceBranchSparse.identity j coefficientMap (fun k => X k)
    _ = _ := by simp only [generators_binding]

def jacobianIdeal : Ideal (Poly ℂ) := Ideal.span (Set.range generators)

theorem coordinate_power_mem_jacobian (j : Fin 3) :
    (X j.succ.castSucc : Poly ℂ)^17 ∈ jacobianIdeal := by
  have hsum : C ((CycleQ2SeedSurfaceBranchSparse.denominator j : ℂ)) *
      X j.succ.castSucc^17 ∈ jacobianIdeal := by
    rw [coordinate_power_identity]
    apply Ideal.sum_mem
    intro k _
    apply Ideal.mul_mem_left
    exact Ideal.subset_span (Set.mem_range_self k)
  have h := Ideal.mul_mem_left jacobianIdeal
    (C (((CycleQ2SeedSurfaceBranchSparse.denominator j : ℂ))⁻¹)) hsum
  have hc : C (((CycleQ2SeedSurfaceBranchSparse.denominator j : ℂ))⁻¹) *
      C ((CycleQ2SeedSurfaceBranchSparse.denominator j : ℂ)) = (1 : Poly ℂ) := by
    rw [←map_mul, inv_mul_cancel₀ (denominator_ne_zero j), map_one]
  simpa only [←mul_assoc, hc, one_mul] using h

/-- The branch Jacobian minors cover the three coordinate opens that
cover every relevant prime of the actual seed surface. -/
theorem prime_minor_cover (P : Ideal (Poly ℂ)) [P.IsPrime]
    (hq : branchEquation ∈ P) (hh : smoothH Complex.I ∈ P)
    (hx : ∃ j : Fin 3, X j.succ.castSucc ∉ P) :
    ∃ j : Fin 6, minor (minorPairs j).1 (minorPairs j).2 ∉ P := by
  by_contra! hzero
  have hgen (j : Fin 8) : generators j ∈ P := by
    fin_cases j
    · exact hq
    · exact hh
    · exact hzero 0
    · exact hzero 1
    · exact hzero 2
    · exact hzero 3
    · exact hzero 4
    · exact hzero 5
  have hle : jacobianIdeal ≤ P := by
    apply Ideal.span_le.mpr
    rintro _ ⟨j,rfl⟩
    exact hgen j
  obtain ⟨j,hj⟩ := hx
  exact hj ((inferInstance : P.IsPrime).mem_of_pow_mem _
    (hle (coordinate_power_mem_jacobian j)))

theorem field_minor_cover {K : Type*} [Field K] (φ : Poly ℂ →+* K)
    (hq : φ branchEquation = 0) (hh : φ (smoothH Complex.I) = 0)
    (hx : ∃ j : Fin 3, φ (X j.succ.castSucc) ≠ 0) :
    ∃ j : Fin 6, φ (minor (minorPairs j).1 (minorPairs j).2) ≠ 0 := by
  letI : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime φ
  exact prime_minor_cover (RingHom.ker φ) hq hh hx

end CycleQ2SeedSurfaceBranchGradient

#print axioms CycleQ2SeedSurfaceBranchGradient.coordinate_power_mem_jacobian
#print axioms CycleQ2SeedSurfaceBranchGradient.prime_minor_cover
end
end


/- Component: continuation_20261112/SeedNormalNonzero.lean -/
section
/-!
# Nonvanishing of the genuine ambient-test normal connecting class

A vanishing genuine kernel Cech class would make its cubic-paired scalar
representative a sum of actual single-open sections. Localization clearing
then gives an unrestricted polynomial boundary witness. Homogeneous
projection produces a boundary in the already checked all-poles canonical
Cech complex, contradicting the computed nonzero residue.

The class here is the ambient test direction (A=x2*x3³*w,L=0). It is distinct
from the vanishing normal obstruction of the fixed-sextic incidence family.
The chosen curve is not itself invariant under the order-three action; an
orbit trace comparison is not asserted here. The test polynomial has
character one, the invariant cubic has character zero, and the ambient
residue volume has character two. The corresponding Serre-dual surface
cohomology component for the eventual comparison is character one.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2SeedNormalNonzero

open CycleQ2NormalConnecting CycleQ2SeedCechTheta CycleQ2ActualNormalCech
  CycleQ2SeedBoundaryProjection CycleQ2SeedLocalizationBoundary

/-- A nonzero cubic trace detects the genuine ambient-test normal class in
the actual two-open kernel quotient, including all ungraded boundaries. -/
theorem ambient_test_connectingClass_ne_zero (r θ : ℂ) (hr : r ≠ 0)
    (v : Fin 9 → ℂ) (hv : derivativeTrace θ v ≠ 0) :
    connectingClass r θ derivativeA 0 ≠ 0 := by
  intro hz
  have hbd := paired_boundary_of_connectingClass_zero r θ (cubicDeformation v) hz
  obtain ⟨x, ⟨a, rfl⟩, y, ⟨b, rfl⟩, hab⟩ := Submodule.mem_sup.mp hbd
  change firstRestriction r θ a + secondRestriction r θ b =
    pairedNormalOverlap r θ (cubicDeformation v) at hab
  obtain ⟨N, M, q, s, hN, hM, hmem⟩ :=
    paired_boundary_witness r θ hr (cubicDeformation v) a b hab.symm
  exact no_unrestricted_boundary r θ hr v hv N M q s hN hM hmem

/-- The existing explicit cubic detects this actual normal class for every
nonzero seed parameter r and every theta. -/
theorem ambient_test_nonzero (r θ : ℂ) (hr : r ≠ 0) :
    connectingClass r θ derivativeA 0 ≠ 0 := by
  apply ambient_test_connectingClass_ne_zero r θ hr selectedTangent
  rw [selectedTangent_trace]
  norm_num

/-- In particular, the literal smooth incidence seed has a nonzero genuine
ambient-test normal connecting class. -/
theorem actual_seed_ambient_test_nonzero :
    connectingClass 57 1 derivativeA 0 ≠ 0 :=
  ambient_test_nonzero 57 1 (by norm_num)

end CycleQ2SeedNormalNonzero

#print axioms CycleQ2SeedNormalNonzero.ambient_test_connectingClass_ne_zero
#print axioms CycleQ2SeedNormalNonzero.ambient_test_nonzero
#print axioms CycleQ2SeedNormalNonzero.actual_seed_ambient_test_nonzero
end
end


/- Component: continuation_20261112/MovingClassBridge.lean -/
section Q2UncompiledNormalKoszulBridge

/-!
# The literal seed quotient maps to the genuine normal Cech module

Development continuation; compilation status is recorded in solution.md.
This extends `CycleQ2SeedNormalNonzero`.

The map sends a polynomial numerator p to p/(g1*g2) on the actual curve
overlap. Each of the five complete-intersection generators is killed:
the three curve equations vanish already in the overlap, and each of the
two remaining generators gives a single-open boundary. Consequently the
map factors through the existing `CycleQ2SeedTrace.SeedAlgebra`.

The target is the existing quotient of actual normal-kernel sections,
identified with scalar sections by `normalCechEquivalence`. This fragment
does not identify that ungraded quotient with projective sheaf cohomology,
construct the surface semiregularity map, or assert a Serre trace comparison.
-/

section
noncomputable section
set_option autoImplicit false

namespace CycleQ2NormalKoszulBridge

open CycleQ2ConormalJacobian CycleQ2SeedTrace CycleQ2NormalConnecting
  CycleQ2ActualNormalCech CycleQ2SeedNormalNonzero

/-- The simple-pole numerator map in the actual overlap localization. -/
def simplePoleRepresentative (r θ : ℂ) : P →ₗ[P] Overlap r θ where
  toFun p := algebraMap P (Overlap r θ) p *
    (↑((firstOverlapUnit r θ)⁻¹) : Overlap r θ) *
    (↑((secondOverlapUnit r θ)⁻¹) : Overlap r θ)
  map_add' p q := by
    simp only [map_add, add_mul]
  map_smul' a p := by
    simp only [smul_eq_mul, Algebra.smul_def, map_mul, mul_assoc, RingHom.id_apply]

@[simp] theorem simplePoleRepresentative_apply (r θ : ℂ) (p : P) :
    simplePoleRepresentative r θ p = algebraMap P (Overlap r θ) p *
      (↑((firstOverlapUnit r θ)⁻¹) : Overlap r θ) *
      (↑((secondOverlapUnit r θ)⁻¹) : Overlap r θ) := rfl

/-- The actual scalar Cech class of the simple-pole representative. -/
def simplePoleClass (r θ : ℂ) : P →ₗ[P] ScalarCech r θ :=
  (scalarBoundaries r θ).mkQ.comp (simplePoleRepresentative r θ)

@[simp] theorem simplePoleClass_apply (r θ : ℂ) (p : P) :
    simplePoleClass r θ p =
      (Submodule.Quotient.mk (simplePoleRepresentative r θ p) : ScalarCech r θ) := rfl

theorem simplePoleRepresentative_zero_of_curve (r θ : ℂ) (p : P)
    (hp : p ∈ ambientCurveIdeal r θ) :
    simplePoleRepresentative r θ p = 0 := by
  rw [simplePoleRepresentative_apply, overlap_annihilates r θ p hp,
    zero_mul, zero_mul]

theorem simplePoleClass_zero_of_curve (r θ : ℂ) (p : P)
    (hp : p ∈ ambientCurveIdeal r θ) : simplePoleClass r θ p = 0 := by
  change (scalarBoundaries r θ).mkQ (simplePoleRepresentative r θ p) = 0
  rw [simplePoleRepresentative_zero_of_curve r θ p hp, map_zero]

theorem simplePoleClass_curveEquation (r θ : ℂ) (i : Fin 3) :
    simplePoleClass r θ (curveEquations r θ i) = 0 :=
  simplePoleClass_zero_of_curve r θ _ (curveEquation_mem r θ i)

/-- Cancelling g1 leaves the inverse of g2, a section on the second open. -/
theorem simplePoleRepresentative_g1 (r θ : ℂ) :
    simplePoleRepresentative r θ (originalG1 r) =
      secondRestriction r θ (↑((secondOpenUnit r θ)⁻¹) : SecondOpen r θ) := by
  rw [simplePoleRepresentative_apply, ← firstOverlapUnit_value,
    (firstOverlapUnit r θ).mul_inv, one_mul]
  rfl

/-- Cancelling g2 leaves the inverse of g1, a section on the first open. -/
theorem simplePoleRepresentative_g2 (r θ : ℂ) :
    simplePoleRepresentative r θ originalG2 =
      firstRestriction r θ (↑((firstOpenUnit r θ)⁻¹) : FirstOpen r θ) := by
  rw [simplePoleRepresentative_apply, ← secondOverlapUnit_value]
  calc
    (secondOverlapUnit r θ : Overlap r θ) *
        (↑((firstOverlapUnit r θ)⁻¹) : Overlap r θ) *
        (↑((secondOverlapUnit r θ)⁻¹) : Overlap r θ) =
        (↑((firstOverlapUnit r θ)⁻¹) : Overlap r θ) *
          ((secondOverlapUnit r θ : Overlap r θ) *
            (↑((secondOverlapUnit r θ)⁻¹) : Overlap r θ)) := by ring
    _ = (↑((firstOverlapUnit r θ)⁻¹) : Overlap r θ) := by
      rw [(secondOverlapUnit r θ).mul_inv, mul_one]
    _ = _ := rfl

theorem simplePoleClass_g1 (r θ : ℂ) :
    simplePoleClass r θ (originalG1 r) = 0 := by
  rw [simplePoleClass_apply]
  apply (Submodule.Quotient.mk_eq_zero (scalarBoundaries r θ)).mpr
  rw [simplePoleRepresentative_g1]
  exact Submodule.mem_sup_right
    (show secondRestriction r θ (↑((secondOpenUnit r θ)⁻¹) : SecondOpen r θ) ∈
      LinearMap.range (secondRestrictionAlg r θ).toLinearMap from
        ⟨(↑((secondOpenUnit r θ)⁻¹) : SecondOpen r θ), rfl⟩)

theorem simplePoleClass_g2 (r θ : ℂ) :
    simplePoleClass r θ originalG2 = 0 := by
  rw [simplePoleClass_apply]
  apply (Submodule.Quotient.mk_eq_zero (scalarBoundaries r θ)).mpr
  rw [simplePoleRepresentative_g2]
  exact Submodule.mem_sup_left
    (show firstRestriction r θ (↑((firstOpenUnit r θ)⁻¹) : FirstOpen r θ) ∈
      LinearMap.range (firstRestrictionAlg r θ).toLinearMap from
        ⟨(↑((firstOpenUnit r θ)⁻¹) : FirstOpen r θ), rfl⟩)

/-- Every generator of the existing five-generator seed ideal maps to zero.
No abstract quotient-pairing or geometric trace hypothesis is supplied. -/
theorem originalIdeal_le_ker (r : ℂ) :
    originalIdeal r ≤ LinearMap.ker (simplePoleClass r 0) := by
  rw [originalIdeal, Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  change simplePoleClass r 0 (originalRelations r i) = 0
  fin_cases i
  · simpa [originalRelations, curveEquations] using
      simplePoleClass_curveEquation r 0 0
  · simpa [originalRelations] using simplePoleClass_g1 r 0
  · simpa [originalRelations, curveEquations] using
      simplePoleClass_curveEquation r 0 1
  · simpa [originalRelations] using simplePoleClass_g2 r 0
  · simpa [originalRelations, curveEquations, thetaH] using
      simplePoleClass_curveEquation r 0 2

/-- The Koszul simple-pole boundary from the literal seed quotient to the
existing scalar Cech module. The construction needs no smoothness premise. -/
def seedScalarBoundary (r : ℂ) : SeedAlgebra r →ₗ[P] ScalarCech r 0 :=
  (originalIdeal r).liftQ (simplePoleClass r 0) (originalIdeal_le_ker r)

@[simp] theorem seedScalarBoundary_mk (r : ℂ) (p : P) :
    seedScalarBoundary r (seedQuotient r p) = simplePoleClass r 0 p := rfl

/-- The same actual boundary with values in genuine normal-kernel sections
modulo the actual restriction boundaries. -/
def seedNormalBoundary (r : ℂ) : SeedAlgebra r →ₗ[P] NormalCech r 0 :=
  (normalCechEquivalence r 0).symm.toLinearMap.comp (seedScalarBoundary r)

@[simp] theorem normalCechEquivalence_seedNormalBoundary (r : ℂ)
    (x : SeedAlgebra r) :
    normalCechEquivalence r 0 (seedNormalBoundary r x) = seedScalarBoundary r x := by
  change normalCechEquivalence r 0
      ((normalCechEquivalence r 0).symm (seedScalarBoundary r x)) = _
  exact (normalCechEquivalence r 0).apply_symm_apply _

/-- The actual normal lift difference has the simple-pole numerator kL-A. -/
theorem normalOverlapCoefficient_eq_simplePole (r θ : ℂ) (A L : P) :
    normalOverlapCoefficient r θ A L =
      simplePoleRepresentative r θ (thetaK θ * L - A) := by
  simp only [normalOverlapCoefficient, overlapCoefficient,
    simplePoleRepresentative_apply, overlap_algebraMap, map_sub, map_mul]
  ring

theorem connectingClass_eq_simplePole (r θ : ℂ) (A L : P) :
    connectingClass r θ A L =
      (normalCechEquivalence r θ).symm
        (simplePoleClass r θ (thetaK θ * L - A)) := by
  apply (normalCechEquivalence r θ).injective
  rw [connectingClass_eq_scalar, LinearEquiv.apply_symm_apply]
  rw [simplePoleClass_apply, normalOverlapCoefficient_eq_simplePole]

/-- The existing normal connecting class factors through the literal seed
algebra. In particular, changing kL-A by any of the five ideal generators
does not change the actual normal class. -/
theorem connectingClass_eq_seedNormalBoundary (r : ℂ) (A L : P) :
    connectingClass r 0 A L =
      seedNormalBoundary r (seedQuotient r (originalK * L - A)) := by
  rw [connectingClass_eq_simplePole]
  change (normalCechEquivalence r 0).symm
      (simplePoleClass r 0 (thetaK 0 * L - A)) =
    (normalCechEquivalence r 0).symm
      (simplePoleClass r 0 (originalK * L - A))
  simp only [thetaK, map_zero, zero_mul, add_zero]

/-- This is an actual nonzero value of the constructed quotient map,
detected by the already proved localization-residue calculation. -/
theorem seedNormalBoundary_test_ne_zero (r : ℂ) (hr : r ≠ 0) :
    seedNormalBoundary r (seedQuotient r (-derivativeA)) ≠ 0 := by
  have h := ambient_test_nonzero r 0 hr
  rw [connectingClass_eq_seedNormalBoundary, mul_zero, zero_sub] at h
  exact h

theorem seedNormalBoundary_ne_zero (r : ℂ) (hr : r ≠ 0) :
    seedNormalBoundary r ≠ 0 := by
  intro hz
  apply seedNormalBoundary_test_ne_zero r hr
  rw [hz, LinearMap.zero_apply]

section DegreeNine

open MvPolynomial CycleQ2SeedCechTheta CycleQ2SeedBoundaryProjection
  CycleQ2SeedLocalizationBoundary

/-- The literal inclusion of the four unweighted coordinates into the
five-variable weighted polynomial ring, before imposing w=-x2^2. -/
def polynomialLift : Poly →ₐ[ℂ] P :=
  MvPolynomial.aeval ![X 0, X 1, X 2, X 3]

@[simp] theorem substitute_polynomialLift (p : Poly) :
    substitute (polynomialLift p) = p := by
  have hh : substitute.comp polynomialLift = AlgHom.id ℂ Poly := by
    ext1 i
    change substitute (polynomialLift (X i)) = X i
    fin_cases i <;> simp [polynomialLift, substitute]
  exact congrArg (fun f : Poly →ₐ[ℂ] Poly => f p) hh

/-- Eliminating w and lifting back does not change the class in the literal
five-variable seed algebra: the eliminated equation is one of its generators. -/
theorem seedQuotient_polynomialLift_substitute (r : ℂ) (p : P) :
    seedQuotient r (polynomialLift (substitute p)) = seedQuotient r p := by
  have hf2 : seedQuotient r originalF2 = 0 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact Ideal.subset_span ⟨2, rfl⟩
  have hw : seedQuotient r (X 4) = -((seedQuotient r (X 2)) ^ 2) := by
    rw [originalF2, map_add, map_pow] at hf2
    exact eq_neg_of_add_eq_zero_left hf2
  have hh : (seedQuotient r).comp (polynomialLift.comp substitute) = seedQuotient r := by
    ext1 i
    change seedQuotient r (polynomialLift (substitute (X i))) = seedQuotient r (X i)
    fin_cases i <;> simp [polynomialLift, substitute, hw]
  exact congrArg (fun f : P →ₐ[ℂ] SeedAlgebra r => f p) hh

theorem simplePoleClass_substitute (r : ℂ) (p : P) :
    simplePoleClass r 0 p = simplePoleClass r 0 (polynomialLift (substitute p)) := by
  have hh := congrArg (seedScalarBoundary r) (seedQuotient_polynomialLift_substitute r p)
  exact hh.symm

private theorem lift_relation_zero (r : ℂ) :
    polynomialLift (relation r 0) = originalF1 r := by
  simp [polynomialLift, relation, originalF1]

private theorem lift_relation_three (r : ℂ) :
    polynomialLift (relation r 3) = originalH := by
  simp [polynomialLift, relation, h, b, originalH, originalB]

private theorem g1_lift_relation (r : ℂ) :
    originalG1 r =
      originalF1 r * (X 0 ^ 2 + C (2 * r) * X 1 * X 3) +
        C (3 * r ^ 2) * polynomialLift (relation r 1) := by
  simp [polynomialLift, relation, originalG1, originalF1, map_mul, map_pow]
  simp only [map_ofNat]
  ring

private theorem g2_lift_relation (r : ℂ) :
    originalG2 = originalF2 * (X 4 - 2 * X 2 ^ 2) +
      C (3 : ℂ) * polynomialLift (relation r 2) := by
  simp [polynomialLift, relation, originalG2, originalF2]
  simp only [map_ofNat]
  ring

private theorem mem_of_constant_mul (I : Ideal P) (c : ℂ) (hc : c ≠ 0)
    (p : P) (hp : C c * p ∈ I) : p ∈ I := by
  have hh := I.mul_mem_left (C (c⁻¹)) hp
  simpa only [← mul_assoc, ← map_mul, inv_mul_cancel₀ hc, map_one, one_mul] using hh

/-- The four-variable relation ideal maps into the original five-variable
ideal. The only divisions are by 3 and by 3*r^2, with r explicitly nonzero. -/
theorem polynomialLift_relation_mem (r : ℂ) (hr : r ≠ 0) (i : Fin 4) :
    polynomialLift (relation r i) ∈ originalIdeal r := by
  have hg (j : Fin 5) : originalRelations r j ∈ originalIdeal r :=
    Ideal.subset_span ⟨j, rfl⟩
  have hf1 : originalF1 r ∈ originalIdeal r := hg 0
  have hg1 : originalG1 r ∈ originalIdeal r := hg 1
  have hf2 : originalF2 ∈ originalIdeal r := hg 2
  have hg2 : originalG2 ∈ originalIdeal r := hg 3
  fin_cases i
  · change polynomialLift (relation r 0) ∈ originalIdeal r
    rw [lift_relation_zero]
    exact hf1
  · apply mem_of_constant_mul (originalIdeal r) (3 * r ^ 2)
      (mul_ne_zero (by norm_num) (pow_ne_zero _ hr))
    have hh := (originalIdeal r).sub_mem hg1
      ((originalIdeal r).mul_mem_right
        (X 0 ^ 2 + C (2 * r) * X 1 * X 3) hf1)
    rw [g1_lift_relation, add_sub_cancel_left] at hh
    exact hh
  · apply mem_of_constant_mul (originalIdeal r) (3 : ℂ) (by norm_num)
    have hh := (originalIdeal r).sub_mem hg2
      ((originalIdeal r).mul_mem_right (X 4 - 2 * X 2 ^ 2) hf2)
    rw [g2_lift_relation r, add_sub_cancel_left] at hh
    exact hh
  · change polynomialLift (relation r 3) ∈ originalIdeal r
    rw [lift_relation_three]
    exact hg 4

theorem polynomialLift_mem (r : ℂ) (hr : r ≠ 0) {p : Poly}
    (hp : p ∈ reducedIdeal r) : polynomialLift p ∈ originalIdeal r := by
  have hle : reducedIdeal r ≤ Ideal.comap polynomialLift.toRingHom (originalIdeal r) := by
    rw [reducedIdeal, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact polynomialLift_relation_mem r hr i
  exact hle hp

/-- An explicit comparison between the two existing quotient algebras,
used here as a complex-linear map. -/
def reducedToSeed (r : ℂ) (hr : r ≠ 0) : ReducedAlgebra r →ₗ[ℂ] SeedAlgebra r :=
  ((reducedIdeal r).restrictScalars ℂ).liftQ
    ((seedQuotient r).toLinearMap.comp polynomialLift.toLinearMap) (by
      intro p hp
      change seedQuotient r (polynomialLift p) = 0
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (polynomialLift_mem r hr hp))

@[simp] theorem reducedToSeed_mk (r : ℂ) (hr : r ≠ 0) (p : Poly) :
    reducedToSeed r hr (reducedQuotient r p) = seedQuotient r (polynomialLift p) := rfl

/-- The actual simple-pole class attached to the four-variable quotient. -/
def reducedScalarBoundary (r : ℂ) (hr : r ≠ 0) :
    ReducedAlgebra r →ₗ[ℂ] ScalarCech r 0 :=
  ((seedScalarBoundary r).restrictScalars ℂ).comp (reducedToSeed r hr)

@[simp] theorem reducedScalarBoundary_mk (r : ℂ) (hr : r ≠ 0) (p : Poly) :
    reducedScalarBoundary r hr (reducedQuotient r p) =
      simplePoleClass r 0 (polynomialLift p) := rfl

/-- The image in the actual Cech module of the distinguished degree-nine
normalization monomial. -/
def normalizationCechClass (r : ℂ) (hr : r ≠ 0) : ScalarCech r 0 :=
  reducedScalarBoundary r hr (normalizationClass r)

/-- The existing quotient trace is the coefficient of the actual simple-pole
class on the degree-nine image. This does not presuppose a Serre trace. -/
theorem reducedScalarBoundary_degreeNine (r : ℂ) (hr : r ≠ 0)
    (hcube : r ^ 3 = 2) {x : ReducedAlgebra r} (hx : x ∈ degreeNinePiece r) :
    reducedScalarBoundary r hr x =
      reducedTrace r hcube x • normalizationCechClass r hr := by
  calc
    reducedScalarBoundary r hr x = reducedScalarBoundary r hr
        (reducedTrace r hcube x • normalizationClass r) :=
      congrArg (reducedScalarBoundary r hr) (degreeNine_class_eq_trace_smul r hcube hx)
    _ = _ := map_smul (reducedScalarBoundary r hr) _ _

theorem simplePoleClass_degreeNine (r : ℂ) (hr : r ≠ 0) (hcube : r ^ 3 = 2)
    (p : Poly) (hp : p.IsHomogeneous 9) :
    simplePoleClass r 0 (polynomialLift p) =
      traceLinear r p • normalizationCechClass r hr := by
  simpa only [reducedScalarBoundary_mk, reducedTrace_mk] using
    (reducedScalarBoundary_degreeNine r hr hcube
      (x := reducedQuotient r p) ⟨p, hp, rfl⟩)

/-- Pairing the ambient-test normal class with a cubic is exactly the
simple-pole class of the lifted negative derivative numerator. -/
theorem simplePoleRepresentative_lift_derivative (r θ : ℂ) (p : Poly) :
    simplePoleRepresentative r θ (polynomialLift (-derivativeNumerator p)) =
      pairedNormalOverlap r θ p := by
  simp only [simplePoleRepresentative_apply, overlap_algebraMap, overlapAmbient,
    ambientCurveMap, RingHom.comp_apply, substitute_polynomialLift,
    pairedNormalOverlap, normalOverlapCoefficient, overlapCoefficient,
    map_zero, mul_zero, zero_sub]
  rw [← substitute_derivativeA p]
  simp only [show ∀ x : Poly, substitute.toRingHom (polynomialLift x) = x from
    substitute_polynomialLift]
  simp only [map_neg, map_mul, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
  ring

/-- The same all-poles boundary argument used for the genuine normal class
also detects the cubic-paired scalar class itself. -/
theorem pairedScalarClass_ne_zero (r θ : ℂ) (hr : r ≠ 0)
    (v : Fin 9 → ℂ) (hv : derivativeTrace θ v ≠ 0) :
    (Submodule.Quotient.mk
      (pairedNormalOverlap r θ (cubicDeformation v)) : ScalarCech r θ) ≠ 0 := by
  intro hz
  have hbd := (Submodule.Quotient.mk_eq_zero (scalarBoundaries r θ)).mp hz
  obtain ⟨x, ⟨a, rfl⟩, y, ⟨b, rfl⟩, hab⟩ := Submodule.mem_sup.mp hbd
  change firstRestriction r θ a + secondRestriction r θ b =
    pairedNormalOverlap r θ (cubicDeformation v) at hab
  obtain ⟨N, M, q, s, hN, hM, hmem⟩ :=
    paired_boundary_witness r θ hr (cubicDeformation v) a b hab.symm
  exact no_unrestricted_boundary r θ hr v hv N M q s hN hM hmem

/-- The distinguished degree-nine image is nonzero in the actual ungraded
Cech quotient, including boundaries with unrestricted pole orders. -/
theorem normalizationCechClass_ne_zero (r : ℂ) (hr : r ≠ 0)
    (hcube : r ^ 3 = 2) : normalizationCechClass r hr ≠ 0 := by
  intro hz
  have hv : derivativeTrace 0 selectedTangent ≠ 0 := by
    rw [selectedTangent_trace]
    norm_num
  apply pairedScalarClass_ne_zero r 0 hr selectedTangent hv
  rw [← simplePoleRepresentative_lift_derivative]
  change simplePoleClass r 0
    (polynomialLift (-derivativeNumerator (cubicDeformation selectedTangent))) = 0
  rw [simplePoleClass_degreeNine r hr hcube _
    (derivativeNumerator_homogeneous selectedTangent).neg, hz, smul_zero]

/-- The existing finite trace detects vanishing of the genuine simple-pole
class for every homogeneous degree-nine numerator, not just the saved matrix. -/
theorem simplePoleClass_degreeNine_eq_zero_iff (r : ℂ) (hr : r ≠ 0)
    (hcube : r ^ 3 = 2) (p : Poly) (hp : p.IsHomogeneous 9) :
    simplePoleClass r 0 (polynomialLift p) = 0 ↔ traceLinear r p = 0 := by
  rw [simplePoleClass_degreeNine r hr hcube p hp]
  constructor
  · intro hz
    rcases smul_eq_zero.mp hz with hc | hnormalization
    · exact hc
    · exact False.elim ((normalizationCechClass_ne_zero r hr hcube) hnormalization)
  · intro hc
    rw [hc, zero_smul]

/-- The existing five-variable seed trace is now the coefficient of a
specific nonzero class in the genuine scalar Cech quotient. The degree
condition is imposed on the actual eliminated numerator. -/
theorem seedTrace_simplePoleClass (r : ℂ) (hr : r ≠ 0) (hcube : r ^ 3 = 2)
    (p : P) (hp : (substitute p).IsHomogeneous 9) :
    simplePoleClass r 0 p =
      seedTrace r hcube (seedQuotient r p) • normalizationCechClass r hr := by
  rw [simplePoleClass_substitute,
    simplePoleClass_degreeNine r hr hcube (substitute p) hp, seedTrace_mk]

/-- The finite quotient trace and the actual Cech class have exactly the
same vanishing criterion on the canonical degree-nine numerators. -/
theorem seedTrace_eq_zero_iff_simplePoleClass (r : ℂ) (hr : r ≠ 0)
    (hcube : r ^ 3 = 2) (p : P) (hp : (substitute p).IsHomogeneous 9) :
    seedTrace r hcube (seedQuotient r p) = 0 ↔ simplePoleClass r 0 p = 0 := by
  rw [seedTrace_mk, simplePoleClass_substitute,
    simplePoleClass_degreeNine_eq_zero_iff r hr hcube (substitute p) hp]

end DegreeNine

end CycleQ2NormalKoszulBridge
end
end

end Q2UncompiledNormalKoszulBridge


/- Component: continuation_20261112/UniversalSurfaceTopCech.lean -/
section
/-! # The seven-dimensional quotient of the actual universal normalized localization complex -/

noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2UniversalSurfaceTopCech

open CycleQ2IncidenceNormalForm CycleQ2UniversalSurface CycleQ2SeedQuotientFiniteFree
  CycleQ2SeedCechThreeOpen CycleQ2SeedCechLocalization CycleQ2UniversalSurfaceLocalizedBasis
  CycleQ2UniversalSurfaceRestrictions CycleQ2UniversalSurfaceLinearCoordinates CycleQ2SeedCechTopCohomology

variable (R : Type*) [CommRing R] [Nontrivial R]

/-- Degree-zero, character-zero sections inside the actual coordinate localization. -/
def gradedLocal (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R) (s : Finset (Fin 3)) : Submodule R (SurfaceLocal R hcoeff Fcoeff s) :=
  (gradedFamilies R).comap (linearCoordinates R hcoeff Fcoeff s)

def gradedCoordinates (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R) (s : Finset (Fin 3)) :
    gradedLocal R hcoeff Fcoeff s →ₗ[R] gradedFamilies R where
  toFun p := ⟨linearCoordinates R hcoeff Fcoeff s p.val, p.property⟩
  map_add' p q := by apply Subtype.ext; exact map_add (linearCoordinates R hcoeff Fcoeff s) p.val q.val
  map_smul' c p := by apply Subtype.ext; exact map_smul (linearCoordinates R hcoeff Fcoeff s) c p.val

@[simp] theorem gradedCoordinates_apply (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R) (s : Finset (Fin 3))
    (p : gradedLocal R hcoeff Fcoeff s) :
    (gradedCoordinates R hcoeff Fcoeff s p).val = localizedCoordinates R hcoeff Fcoeff s p.val := rfl

theorem gradedCoordinates_injective (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R) (s : Finset (Fin 3)) :
    Function.Injective (gradedCoordinates R hcoeff Fcoeff s) := by
  intro p q hpq
  apply Subtype.ext
  exact localizedCoordinates_injective R hcoeff Fcoeff s (congrArg Subtype.val hpq)

theorem gradedCoordinates_range (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R) (s : Finset (Fin 3)) :
    LinearMap.range (gradedCoordinates R hcoeff Fcoeff s) = poleSubmodule R s := by
  ext p
  constructor
  · rintro ⟨q, rfl⟩ ab
    exact localizedCoordinates_hasPoles R hcoeff Fcoeff s q.val ab
  · intro hp
    obtain ⟨q, hq⟩ := (mem_range_localizedCoordinates R hcoeff Fcoeff s p.val).mpr hp
    have hqg : q ∈ gradedLocal R hcoeff Fcoeff s := by
      change linearCoordinates R hcoeff Fcoeff s q ∈ gradedFamilies R
      rw [linearCoordinates_apply, hq]
      exact p.property
    refine ⟨⟨q, hqg⟩, ?_⟩
    exact Subtype.ext hq

def totalEquiv (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R) : gradedLocal R hcoeff Fcoeff Finset.univ ≃ₗ[R] gradedFamilies R :=
  LinearEquiv.ofBijective (gradedCoordinates R hcoeff Fcoeff Finset.univ)
    ⟨gradedCoordinates_injective R hcoeff Fcoeff Finset.univ, by
      intro p
      have hp : p ∈ poleSubmodule R Finset.univ := by
        intro ab e i hi _
        exact False.elim (hi (Finset.mem_univ i))
      rw [← gradedCoordinates_range R hcoeff Fcoeff Finset.univ] at hp
      exact hp⟩

@[simp] theorem totalEquiv_apply (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R) (p : gradedLocal R hcoeff Fcoeff Finset.univ) :
    totalEquiv R hcoeff Fcoeff p = gradedCoordinates R hcoeff Fcoeff Finset.univ p := rfl

def gradedRestriction (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R) {s t : Finset (Fin 3)} (hst : s ⊆ t) :
    gradedLocal R hcoeff Fcoeff s →ₗ[R] gradedLocal R hcoeff Fcoeff t where
  toFun p := ⟨restrictionLinear R hcoeff Fcoeff hst p.val, by
    intro ab
    change HasGrade ab 0 (localizedCoordinates R hcoeff Fcoeff t (restriction R hcoeff Fcoeff hst p.val) ab)
    rw [coordinates_restriction]
    exact p.property ab⟩
  map_add' p q := by apply Subtype.ext; exact map_add (restrictionLinear R hcoeff Fcoeff hst) p.val q.val
  map_smul' c p := by apply Subtype.ext; exact map_smul (restrictionLinear R hcoeff Fcoeff hst) c p.val

theorem gradedCoordinates_restriction (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R)
    {s t : Finset (Fin 3)} (hst : s ⊆ t) :
    (gradedCoordinates R hcoeff Fcoeff t).comp (gradedRestriction R hcoeff Fcoeff hst) =
      gradedCoordinates R hcoeff Fcoeff s := by
  ext p ab e
  change (localizedCoordinates R hcoeff Fcoeff t (restriction R hcoeff Fcoeff hst p.val) ab).coeff e =
    (localizedCoordinates R hcoeff Fcoeff s p.val ab).coeff e
  rw [coordinates_restriction]

/-- The boundary submodule is the sum of the images of the actual three
canonical ring restrictions from pair-open sections. -/
def actualBoundary (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R) : Submodule R (gradedLocal R hcoeff Fcoeff Finset.univ) :=
  LinearMap.range (gradedRestriction R hcoeff Fcoeff (show ({0, 1} : Finset (Fin 3)) ⊆ Finset.univ by decide)) ⊔
  LinearMap.range (gradedRestriction R hcoeff Fcoeff (show ({0, 2} : Finset (Fin 3)) ⊆ Finset.univ by decide)) ⊔
  LinearMap.range (gradedRestriction R hcoeff Fcoeff (show ({1, 2} : Finset (Fin 3)) ⊆ Finset.univ by decide))

theorem map_actualBoundary (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R) :
    (actualBoundary R hcoeff Fcoeff).map (totalEquiv R hcoeff Fcoeff).toLinearMap = topBoundary R := by
  change (actualBoundary R hcoeff Fcoeff).map (gradedCoordinates R hcoeff Fcoeff Finset.univ) = _
  simp only [actualBoundary, Submodule.map_sup, ← LinearMap.range_comp,
    gradedCoordinates_restriction, gradedCoordinates_range, topBoundary]

abbrev ActualTopCechQuotient (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R) :=
  gradedLocal R hcoeff Fcoeff Finset.univ ⧸ actualBoundary R hcoeff Fcoeff

def actualTopEquiv (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R) : ActualTopCechQuotient R hcoeff Fcoeff ≃ₗ[R] TopCechQuotient R :=
  Submodule.Quotient.equiv _ _ (totalEquiv R hcoeff Fcoeff) (map_actualBoundary R hcoeff Fcoeff)

def actualTopBasis (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R) : Module.Basis TopIndex R (ActualTopCechQuotient R hcoeff Fcoeff) :=
  (topCechBasis R).map (actualTopEquiv R hcoeff Fcoeff).symm

@[simp] theorem actualTopBasis_apply (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R) (q : TopIndex) :
    actualTopEquiv R hcoeff Fcoeff (actualTopBasis R hcoeff Fcoeff q) =
      Submodule.Quotient.mk (basisSection R q) := by
  simp [actualTopBasis]

theorem actualTop_rank_seven (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R) :
    Module.finrank R (ActualTopCechQuotient R hcoeff Fcoeff) = 7 := by
  rw [Module.finrank_eq_card_basis (actualTopBasis R hcoeff Fcoeff), topIndex_count]

end CycleQ2UniversalSurfaceTopCech

#print axioms CycleQ2UniversalSurfaceTopCech.actualTop_rank_seven
end
end


/- Component: continuation_20261112/UniversalSurfaceCharacterCech.lean -/
section
/-! # The actual universal localization complex in every character -/

noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2UniversalSurfaceCharacterCech

open CycleQ2IncidenceNormalForm CycleQ2UniversalSurface CycleQ2SeedQuotientFiniteFree
  CycleQ2SeedCechThreeOpen CycleQ2SeedCechLocalization CycleQ2UniversalSurfaceLocalizedBasis
  CycleQ2UniversalSurfaceRestrictions CycleQ2UniversalSurfaceLinearCoordinates CycleQ2CharacterTopCech

variable (R : Type*) [CommRing R] [Nontrivial R] (χ : ZMod 3)

/-- Degree-zero sections of the explicitly specified character inside the actual coordinate localization. -/
def gradedLocal (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R) (s : Finset (Fin 3)) : Submodule R (SurfaceLocal R hcoeff Fcoeff s) :=
  (gradedFamilies R χ).comap (linearCoordinates R hcoeff Fcoeff s)

def gradedCoordinates (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R) (s : Finset (Fin 3)) :
    gradedLocal R χ hcoeff Fcoeff s →ₗ[R] gradedFamilies R χ where
  toFun p := ⟨linearCoordinates R hcoeff Fcoeff s p.val, p.property⟩
  map_add' p q := by apply Subtype.ext; exact map_add (linearCoordinates R hcoeff Fcoeff s) p.val q.val
  map_smul' c p := by apply Subtype.ext; exact map_smul (linearCoordinates R hcoeff Fcoeff s) c p.val

@[simp] theorem gradedCoordinates_apply (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R) (s : Finset (Fin 3))
    (p : gradedLocal R χ hcoeff Fcoeff s) :
    (gradedCoordinates R χ hcoeff Fcoeff s p).val = localizedCoordinates R hcoeff Fcoeff s p.val := rfl

theorem gradedCoordinates_injective (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R) (s : Finset (Fin 3)) :
    Function.Injective (gradedCoordinates R χ hcoeff Fcoeff s) := by
  intro p q hpq
  apply Subtype.ext
  exact localizedCoordinates_injective R hcoeff Fcoeff s (congrArg Subtype.val hpq)

theorem gradedCoordinates_range (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R) (s : Finset (Fin 3)) :
    LinearMap.range (gradedCoordinates R χ hcoeff Fcoeff s) = poleSubmodule R χ s := by
  ext p
  constructor
  · rintro ⟨q, rfl⟩ ab
    exact localizedCoordinates_hasPoles R hcoeff Fcoeff s q.val ab
  · intro hp
    obtain ⟨q, hq⟩ := (mem_range_localizedCoordinates R hcoeff Fcoeff s p.val).mpr hp
    have hqg : q ∈ gradedLocal R χ hcoeff Fcoeff s := by
      change linearCoordinates R hcoeff Fcoeff s q ∈ gradedFamilies R χ
      rw [linearCoordinates_apply, hq]
      exact p.property
    refine ⟨⟨q, hqg⟩, ?_⟩
    exact Subtype.ext hq

def totalEquiv (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R) : gradedLocal R χ hcoeff Fcoeff Finset.univ ≃ₗ[R] gradedFamilies R χ :=
  LinearEquiv.ofBijective (gradedCoordinates R χ hcoeff Fcoeff Finset.univ)
    ⟨gradedCoordinates_injective R χ hcoeff Fcoeff Finset.univ, by
      intro p
      have hp : p ∈ poleSubmodule R χ Finset.univ := by
        intro ab e i hi _
        exact False.elim (hi (Finset.mem_univ i))
      rw [← gradedCoordinates_range R χ hcoeff Fcoeff Finset.univ] at hp
      exact hp⟩

@[simp] theorem totalEquiv_apply (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R) (p : gradedLocal R χ hcoeff Fcoeff Finset.univ) :
    totalEquiv R χ hcoeff Fcoeff p = gradedCoordinates R χ hcoeff Fcoeff Finset.univ p := rfl

def gradedRestriction (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R) {s t : Finset (Fin 3)} (hst : s ⊆ t) :
    gradedLocal R χ hcoeff Fcoeff s →ₗ[R] gradedLocal R χ hcoeff Fcoeff t where
  toFun p := ⟨restrictionLinear R hcoeff Fcoeff hst p.val, by
    intro ab
    change HasGrade ab (0,χ) (localizedCoordinates R hcoeff Fcoeff t (restriction R hcoeff Fcoeff hst p.val) ab)
    rw [coordinates_restriction]
    exact p.property ab⟩
  map_add' p q := by apply Subtype.ext; exact map_add (restrictionLinear R hcoeff Fcoeff hst) p.val q.val
  map_smul' c p := by apply Subtype.ext; exact map_smul (restrictionLinear R hcoeff Fcoeff hst) c p.val

theorem gradedCoordinates_restriction (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R)
    {s t : Finset (Fin 3)} (hst : s ⊆ t) :
    (gradedCoordinates R χ hcoeff Fcoeff t).comp (gradedRestriction R χ hcoeff Fcoeff hst) =
      gradedCoordinates R χ hcoeff Fcoeff s := by
  ext p ab e
  change (localizedCoordinates R hcoeff Fcoeff t (restriction R hcoeff Fcoeff hst p.val) ab).coeff e =
    (localizedCoordinates R hcoeff Fcoeff s p.val ab).coeff e
  rw [coordinates_restriction]

/-- The boundary submodule is the sum of the images of the actual three
canonical ring restrictions from pair-open sections. -/
def actualBoundary (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R) : Submodule R (gradedLocal R χ hcoeff Fcoeff Finset.univ) :=
  LinearMap.range (gradedRestriction R χ hcoeff Fcoeff (show ({0, 1} : Finset (Fin 3)) ⊆ Finset.univ by decide)) ⊔
  LinearMap.range (gradedRestriction R χ hcoeff Fcoeff (show ({0, 2} : Finset (Fin 3)) ⊆ Finset.univ by decide)) ⊔
  LinearMap.range (gradedRestriction R χ hcoeff Fcoeff (show ({1, 2} : Finset (Fin 3)) ⊆ Finset.univ by decide))

theorem map_actualBoundary (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R) :
    (actualBoundary R χ hcoeff Fcoeff).map (totalEquiv R χ hcoeff Fcoeff).toLinearMap = topBoundary R χ := by
  change (actualBoundary R χ hcoeff Fcoeff).map (gradedCoordinates R χ hcoeff Fcoeff Finset.univ) = _
  simp only [actualBoundary, Submodule.map_sup, ← LinearMap.range_comp,
    gradedCoordinates_restriction, gradedCoordinates_range, topBoundary]

abbrev ActualTopCechQuotient (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R) :=
  gradedLocal R χ hcoeff Fcoeff Finset.univ ⧸ actualBoundary R χ hcoeff Fcoeff

def actualTopEquiv (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R) : ActualTopCechQuotient R χ hcoeff Fcoeff ≃ₗ[R] TopCechQuotient R χ :=
  Submodule.Quotient.equiv _ _ (totalEquiv R χ hcoeff Fcoeff) (map_actualBoundary R χ hcoeff Fcoeff)

def actualTopBasis (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R) : Module.Basis (TopIndex χ) R (ActualTopCechQuotient R χ hcoeff Fcoeff) :=
  (topCechBasis R χ).map (actualTopEquiv R χ hcoeff Fcoeff).symm

@[simp] theorem actualTopBasis_apply (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R) (q : (TopIndex χ)) :
    actualTopEquiv R χ hcoeff Fcoeff (actualTopBasis R χ hcoeff Fcoeff q) =
      Submodule.Quotient.mk (basisSection R χ q) := by
  simp [actualTopBasis]

theorem actualTop_rank (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R) :
    Module.finrank R (ActualTopCechQuotient R χ hcoeff Fcoeff) = if χ=0 then 7 else 8 := by
  rw [Module.finrank_eq_card_basis (actualTopBasis R χ hcoeff Fcoeff), topIndex_count χ]

theorem actualTop_rank_characterOne (hcoeff : FullCubicTailIndex → R)
    (Fcoeff : FullSexticTailIndex → R) :
    Module.finrank R (ActualTopCechQuotient R (1 : ZMod 3) hcoeff Fcoeff) = 8 := by
  simpa using actualTop_rank R (1 : ZMod 3) hcoeff Fcoeff

end CycleQ2UniversalSurfaceCharacterCech

#print axioms CycleQ2UniversalSurfaceCharacterCech.actualTop_rank

#print axioms CycleQ2UniversalSurfaceCharacterCech.actualTop_rank_characterOne
end
end


/- Component: continuation_20261112/SeedSurfaceGradient.lean -/
section
/-! # A relevant-prime Jacobian cover for the actual seed surface

For G=w^3+q and F=G+h*k, the two-row Jacobian minors of (F,h) agree
with those of (G,h) modulo h.  Away from w=0, the cubic gradient cover
and partial_w G=3*w^2 give a minor.  On w=0, the exact branch cover
gives a minor.  The conclusion is bound to actualSeedEquation57 1 and
thetaH1 and holds at every relevant prime over the complex coefficients.
-/

noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 30000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2SeedSurfaceGradient

open MvPolynomial CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations
  CycleQ2NormalConnecting
open scoped BigOperators

def gMinor (j k : Fin 5) : Poly ℂ :=
  pderiv j (seedG (57 : ℂ)) * pderiv k (smoothH Complex.I) -
    pderiv k (seedG (57 : ℂ)) * pderiv j (smoothH Complex.I)

def surfaceMinor (j k : Fin 5) : Poly ℂ :=
  pderiv j (smoothF (57 : ℂ) Complex.I) * pderiv k (smoothH Complex.I) -
    pderiv k (smoothF (57 : ℂ) Complex.I) * pderiv j (smoothH Complex.I)

def correctionMinor (j k : Fin 5) : Poly ℂ :=
  pderiv j (smoothK Complex.I) * pderiv k (smoothH Complex.I) -
    pderiv k (smoothK Complex.I) * pderiv j (smoothH Complex.I)

theorem seedG_eq_branch :
    seedG (57 : ℂ) = CycleQ2SeedSurfaceBranchGradient.branchEquation + X 4^3 := by
  rw [seedG, CycleQ2SegreSeed.seedG_expanded]
  simp only [CycleQ2SeedSurfaceBranchGradient.branchEquation, map_pow]
  ring

theorem surfaceMinor_eq (j k : Fin 5) :
    surfaceMinor j k = gMinor j k + smoothH Complex.I * correctionMinor j k := by
  unfold surfaceMinor gMinor correctionMinor
  simp only [smoothF, map_add, Derivation.leibniz, smul_eq_mul]
  ring

theorem surfaceMinor_not_mem (P : Ideal (Poly ℂ))
    (hh : smoothH Complex.I ∈ P) {j k : Fin 5}
    (hg : gMinor j k ∉ P) : surfaceMinor j k ∉ P := by
  intro hs
  have hc : smoothH Complex.I * correctionMinor j k ∈ P :=
    Ideal.mul_mem_right _ _ hh
  have h := P.sub_mem hs hc
  rw [surfaceMinor_eq, add_sub_cancel_right] at h
  exact hg h

theorem gMinor_base (j k : Fin 4) :
    gMinor j.castSucc k.castSucc = CycleQ2SeedSurfaceBranchGradient.minor j k := by
  have hd (a : Fin 4) : pderiv a.castSucc (seedG (57 : ℂ)) =
      pderiv a.castSucc CycleQ2SeedSurfaceBranchGradient.branchEquation := by
    rw [seedG_eq_branch, map_add]
    have hz : pderiv a.castSucc (X (4 : Fin 5)^3 : Poly ℂ) = 0 := by
      fin_cases a <;> simp
    rw [hz, add_zero]
  unfold gMinor CycleQ2SeedSurfaceBranchGradient.minor
  rw [hd, hd]

theorem gMinor_w (j : Fin 4) :
    gMinor 4 j.castSucc = (3 : Poly ℂ)*X 4^2*
      pderiv j.castSucc (smoothH Complex.I) := by
  have hg : pderiv (4 : Fin 5) (seedG (57 : ℂ)) = (3 : Poly ℂ)*X 4^2 := by
    rw [seedG_eq_branch]
    simp [CycleQ2SeedSurfaceBranchGradient.branchEquation] <;> ring
  have hh : pderiv (4 : Fin 5) (smoothH Complex.I : Poly ℂ) = 0 := by
    simp [smoothH, smoothB, smoothA]
  simp only [gMinor, hg, hh, mul_zero, sub_zero]

theorem cubic_prime_gradient_cover (P : Ideal (Poly ℂ)) [P.IsPrime]
    (hx : ∃ j : Fin 4, X j.castSucc ∉ P) :
    ∃ j : Fin 4, pderiv j.castSucc (smoothH Complex.I : Poly ℂ) ∉ P := by
  by_contra! hzero
  have hle : Ideal.span (Set.range (fun k : Fin 4 =>
      pderiv k.castSucc (smoothH Complex.I : Poly ℂ))) ≤ P := by
    apply Ideal.span_le.mpr
    rintro _ ⟨j,rfl⟩
    exact hzero j
  obtain ⟨j,hj⟩ := hx
  exact hj ((inferInstance : P.IsPrime).mem_of_pow_mem 5
    (hle (CycleQ2SeedCubicGradient.coordinate_power_mem_gradient_ideal j)))

/-- All relevant primes of the actual incidence seed surface admit a
nonvanishing two-column Jacobian minor. -/
theorem prime_minor_cover (P : Ideal (Poly ℂ)) [P.IsPrime]
    (hF : smoothF (57 : ℂ) Complex.I ∈ P) (hh : smoothH Complex.I ∈ P)
    (hx : ∃ j : Fin 5, X j ∉ P) :
    ∃ j k : Fin 5, surfaceMinor j k ∉ P := by
  have hbase : ∃ j : Fin 3, X j.succ.castSucc ∉ P := by
    rcases CycleQ2SeedCoordinateCover.seedPrime_coordinate_cover (57 : ℂ)
      Complex.I P hh hF hx with h1 | h2 | h3
    · exact ⟨0,h1⟩
    · exact ⟨1,h2⟩
    · exact ⟨2,h3⟩
  by_cases hw : (X (4 : Fin 5) : Poly ℂ) ∈ P
  · have hprod : smoothH Complex.I * smoothK Complex.I ∈ P :=
      Ideal.mul_mem_right _ _ hh
    have hG : seedG (57 : ℂ) ∈ P := by
      simpa only [smoothF, add_sub_cancel_right] using P.sub_mem hF hprod
    have hw3 : (X (4 : Fin 5) : Poly ℂ)^3 ∈ P :=
      Ideal.pow_mem_of_mem P hw 3 (by decide)
    have hq : CycleQ2SeedSurfaceBranchGradient.branchEquation ∈ P := by
      rw [seedG_eq_branch] at hG
      simpa only [add_sub_cancel_right] using P.sub_mem hG hw3
    obtain ⟨a,ha⟩ := CycleQ2SeedSurfaceBranchGradient.prime_minor_cover P hq hh hbase
    refine ⟨(CycleQ2SeedSurfaceBranchGradient.minorPairs a).1.castSucc,
      (CycleQ2SeedSurfaceBranchGradient.minorPairs a).2.castSucc,?_⟩
    apply surfaceMinor_not_mem P hh
    simpa only [gMinor_base] using ha
  · have hbase4 : ∃ j : Fin 4, X j.castSucc ∉ P := by
      obtain ⟨j,hj⟩ := hbase
      exact ⟨j.succ,hj⟩
    obtain ⟨j,hj⟩ := cubic_prime_gradient_cover P hbase4
    have h3 : (3 : Poly ℂ) ∉ P := by
      apply Ideal.notMem_of_isUnit P
      simpa only [map_ofNat] using
        (isUnit_iff_ne_zero.mpr (by norm_num : (3 : ℂ) ≠ 0)).map
          (C : ℂ →+* Poly ℂ)
    have hw2 : (X (4 : Fin 5) : Poly ℂ)^2 ∉ P := by
      intro h
      exact hw ((inferInstance : P.IsPrime).mem_of_pow_mem 2 h)
    refine ⟨4,j.castSucc,surfaceMinor_not_mem P hh ?_⟩
    rw [gMinor_w]
    exact (inferInstance : P.IsPrime).mul_notMem
      ((inferInstance : P.IsPrime).mul_notMem h3 hw2) hj

def actualNormalMinor (j k : Fin 5) : Poly ℂ :=
  Matrix.det (fun a b : Fin 2 =>
    pderiv (![j,k] b) (![actualSeedEquation 57 1,thetaH 1] a))

theorem actualNormalMinor_eq (j k : Fin 5) :
    actualNormalMinor j k = surfaceMinor j k := by
  simp only [actualNormalMinor, Matrix.det_fin_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, actualSeedEquation_eq_smoothF, ←smoothH_eq_thetaH]
  rfl

/-- The cover is bound to the literal ordered target tuple (F,h) used
in the global conormal construction. -/
theorem actual_prime_normal_cover (P : Ideal (Poly ℂ)) [P.IsPrime]
    (hF : actualSeedEquation 57 1 ∈ P) (hh : thetaH 1 ∈ P)
    (hx : ∃ j : Fin 5, X j ∉ P) :
    ∃ j k : Fin 5, actualNormalMinor j k ∉ P := by
  rw [actualSeedEquation_eq_smoothF] at hF
  rw [←smoothH_eq_thetaH] at hh
  obtain ⟨j,k,hjk⟩ := prime_minor_cover P hF hh hx
  exact ⟨j,k,by simpa only [actualNormalMinor_eq] using hjk⟩

theorem actual_field_normal_cover {K : Type*} [Field K]
    (φ : Poly ℂ →+* K) (hF : φ (actualSeedEquation 57 1) = 0)
    (hh : φ (thetaH 1) = 0) (hx : ∃ j : Fin 5, φ (X j) ≠ 0) :
    ∃ j k : Fin 5, IsUnit (φ (actualNormalMinor j k)) := by
  letI : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime φ
  obtain ⟨j,k,hjk⟩ := actual_prime_normal_cover (RingHom.ker φ) hF hh hx
  exact ⟨j,k,isUnit_iff_ne_zero.mpr hjk⟩

end CycleQ2SeedSurfaceGradient

#print axioms CycleQ2SeedSurfaceGradient.prime_minor_cover
#print axioms CycleQ2SeedSurfaceGradient.actual_prime_normal_cover
#print axioms CycleQ2SeedSurfaceGradient.actual_field_normal_cover
end
end


