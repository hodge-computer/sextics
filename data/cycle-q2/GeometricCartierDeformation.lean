import Proposal.GeometricGradedCechDescent
import Proposal.GeometricCartierOrdinaryScalar
import Proposal.GeometricProjectiveDescent
import Proposal.GeometricSurfaceAdjunction
import Proposal.GeometricSquareZeroAtiyah
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
import Proposal.GeometricFamilyDeformation
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Tactic.FinCases
import Proposal.GeometricCartierOrbitCompatibility

section SourceSurfaceSmoothSplittings

/-! Constructed algebra splittings on actual surface Jacobian opens.
Formal smoothness comes from the explicit submersive presentation of
the actual two-equation quotient; the first-order kernel is the actual
kernel supplied by the deformation construction. -/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace CycleQ2GeometricSquareZeroSplittings

variable {K E C : Type*} [CommRing K] [CommRing E] [CommRing C]
variable [Algebra K E] [Algebra K C] [Algebra E C] [IsScalarTower K E C]
variable (e : C ≃ₗ[E] RingHom.ker (algebraMap E C))

include e in
theorem kernel_square_eq_bot : RingHom.ker (algebraMap E C) ^ 2 = ⊥ := by
  apply le_antisymm _ bot_le
  rw [pow_two]
  apply Ideal.mul_le.mpr
  intro x hx y hy
  exact kernel_mul_zero e x y hx hy

/-- A genuine algebra section, chosen by the infinitesimal lifting
property of the actual formally smooth closed ring. -/
def smoothSplitting [Algebra.FormallySmooth K C]
    (hρ : Function.Surjective (algebraMap E C)) : C →ₐ[K] E :=
  Algebra.FormallySmooth.liftOfSurjective (AlgHom.id K C)
    (IsScalarTower.toAlgHom K E C) hρ
    ⟨2, kernel_square_eq_bot e⟩

@[simp] theorem reduction_smoothSplitting [Algebra.FormallySmooth K C]
    (hρ : Function.Surjective (algebraMap E C)) (x : C) :
    algebraMap E C (smoothSplitting (K := K) e hρ x) = x :=
  Algebra.FormallySmooth.liftOfSurjective_apply (AlgHom.id K C)
    (IsScalarTower.toAlgHom K E C) hρ ⟨2, kernel_square_eq_bot e⟩ x

end CycleQ2GeometricSquareZeroSplittings

namespace CycleQ2GeometricSurfaceSmoothSplittings

open MvPolynomial CycleQ2GeometricSurfaceAdjunction

/-- The pivot coordinates belong to the actual affine polynomial ring. -/
def prePresentation (v : Fin 2 → SurfacePoly)
    (p : Fin 2 → Option (Fin 3)) (hp : Function.Injective p) :
    Algebra.PreSubmersivePresentation ℂ (SurfaceChartRing v) (Option (Fin 3)) (Fin 2) :=
  Algebra.PreSubmersivePresentation.naive (v := v) p hp

abbrev JacobianSurfacePatch (v : Fin 2 → SurfacePoly)
    (p : Fin 2 → Option (Fin 3)) (hp : Function.Injective p) :=
  Localization.Away (prePresentation v p hp).jacobian

theorem prePresentation_jacobian (v : Fin 2 → SurfacePoly)
    (p : Fin 2 → Option (Fin 3)) (hp : Function.Injective p) :
    (prePresentation v p hp).jacobian =
      Ideal.Quotient.mk (surfaceChartIdeal v)
        (pderiv (p 0) (v 0) * pderiv (p 1) (v 1) -
          pderiv (p 0) (v 1) * pderiv (p 1) (v 0)) := by
  rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det,
    Matrix.det_fin_two]
  simp only [Algebra.PreSubmersivePresentation.jacobiMatrix_apply]
  rfl

/-- Inverting the literal Jacobian minor gives a submersive
presentation of the same quotient localization, with one new inverse
variable and one new inverse relation. -/
def smoothPresentation (v : Fin 2 → SurfacePoly)
    (p : Fin 2 → Option (Fin 3)) (hp : Function.Injective p) :
    Algebra.SubmersivePresentation ℂ (JacobianSurfacePatch v p hp)
      (Unit ⊕ Option (Fin 3)) (Unit ⊕ Fin 2) where
  toPreSubmersivePresentation :=
    (Algebra.PreSubmersivePresentation.localizationAway
      (JacobianSurfacePatch v p hp) (prePresentation v p hp).jacobian).comp
        (prePresentation v p hp)
  jacobian_isUnit := by
    have hu : IsUnit (algebraMap (SurfaceChartRing v) (JacobianSurfacePatch v p hp)
        (prePresentation v p hp).jacobian) :=
      IsLocalization.Away.algebraMap_isUnit _
    simpa only [Algebra.PreSubmersivePresentation.comp_jacobian_eq_jacobian_smul_jacobian,
      Algebra.PreSubmersivePresentation.localizationAway_jacobian, Algebra.smul_def]
      using hu.mul hu

theorem jacobianSurfacePatch_formallySmooth (v : Fin 2 → SurfacePoly)
    (p : Fin 2 → Option (Fin 3)) (hp : Function.Injective p) :
    Algebra.FormallySmooth ℂ (JacobianSurfacePatch v p hp) := by
  letI : Algebra.IsStandardSmooth ℂ (JacobianSurfacePatch v p hp) :=
    (smoothPresentation v p hp).isStandardSmooth
  infer_instance

/-- On each actual Jacobian open the actual nilpotent reduction admits
an algebra section.  No splitting or geometry comparison is supplied. -/
def jacobianSurfaceSplitting (v : Fin 2 → SurfacePoly)
    (p : Fin 2 → Option (Fin 3)) (hp : Function.Injective p)
    (E : Type*) [CommRing E] [Algebra ℂ E]
    [Algebra E (JacobianSurfacePatch v p hp)]
    [IsScalarTower ℂ E (JacobianSurfacePatch v p hp)]
    (e : JacobianSurfacePatch v p hp ≃ₗ[E]
      RingHom.ker (algebraMap E (JacobianSurfacePatch v p hp)))
    (hρ : Function.Surjective (algebraMap E (JacobianSurfacePatch v p hp))) :
    JacobianSurfacePatch v p hp →ₐ[ℂ] E := by
  letI := jacobianSurfacePatch_formallySmooth v p hp
  exact CycleQ2GeometricSquareZeroSplittings.smoothSplitting e hρ

@[simp] theorem reduction_jacobianSurfaceSplitting (v : Fin 2 → SurfacePoly)
    (p : Fin 2 → Option (Fin 3)) (hp : Function.Injective p)
    (E : Type*) [CommRing E] [Algebra ℂ E]
    [Algebra E (JacobianSurfacePatch v p hp)]
    [IsScalarTower ℂ E (JacobianSurfacePatch v p hp)]
    (e : JacobianSurfacePatch v p hp ≃ₗ[E]
      RingHom.ker (algebraMap E (JacobianSurfacePatch v p hp)))
    (hρ : Function.Surjective (algebraMap E (JacobianSurfacePatch v p hp)))
    (x : JacobianSurfacePatch v p hp) :
    algebraMap E (JacobianSurfacePatch v p hp)
      (jacobianSurfaceSplitting v p hp E e hρ x) = x := by
  letI := jacobianSurfacePatch_formallySmooth v p hp
  exact CycleQ2GeometricSquareZeroSplittings.reduction_smoothSplitting (K := ℂ) e hρ x

end CycleQ2GeometricSurfaceSmoothSplittings

end
end SourceSurfaceSmoothSplittings

section SourceFirstOrderSplittings

/-! Actual algebra splittings of the quotient by f - epsilon a.
The ambient derivation is used only before passage to the quotient.
Its negative graph kills the deformed relation; only the difference
of two ambient derivations descends to the closed hypersurface. -/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace CycleQ2GeometricSurfaceFirstOrder

variable {K R : Type*} [CommRing K] [CommRing R] [Algebra K R]

/-- The negative graph is an actual algebra homomorphism into the
dual numbers, with the sign fixed by f - epsilon a. -/
def negativeGraph (D : Derivation K R R) : R →ₐ[K] Dual R where
  toFun x := (x, -D x)
  map_zero' := by apply TrivSqZeroExt.ext <;> simp
  map_one' := by apply TrivSqZeroExt.ext <;> simp
  map_add' x y := by
    apply TrivSqZeroExt.ext
    · rfl
    · change -D (x + y) = -D x + -D y
      rw [map_add, neg_add]
  map_mul' x y := by
    apply TrivSqZeroExt.ext
    · rfl
    · change -D (x * y) = x * (-D y) + (-D x) * y
      rw [Derivation.leibniz]
      change -(x * D y + y * D x) = _
      ring
  commutes' k := by
    apply TrivSqZeroExt.ext
    · rfl
    · change -D (algebraMap K R k) = 0
      rw [Derivation.map_algebraMap, neg_zero]

@[simp] theorem negativeGraph_apply (D : Derivation K R R) (x : R) :
    negativeGraph D x = (x, -D x) := rfl

theorem negativeGraph_relation (D : Derivation K R R) (f a : R) (hD : D f = a) :
    negativeGraph D f = relation f a := by
  apply TrivSqZeroExt.ext
  · rfl
  · exact congrArg Neg.neg hD

def rawSplitting (f a : R) (D : Derivation K R R) : R →ₐ[K] Deformation f a :=
  (Ideal.Quotient.mkₐ K (deformationIdeal f a)).comp (negativeGraph D)

theorem rawSplitting_f (f a : R) (D : Derivation K R R) (hD : D f = a) :
    rawSplitting f a D f = 0 := by
  change Ideal.Quotient.mk (deformationIdeal f a) (negativeGraph D f) = 0
  rw [negativeGraph_relation D f a hD]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)

/-- This map really descends through the closed equation, because its
negative graph sends f to the actual deformed relation f - epsilon a. -/
def splitting (f a : R) (D : Derivation K R R) (hD : D f = a) :
    Closed f →ₐ[K] Deformation f a :=
  Ideal.Quotient.liftₐ (Ideal.span ({f} : Set R)) (rawSplitting f a D) (by
    have h : Ideal.span ({f} : Set R) ≤ RingHom.ker (rawSplitting f a D).toRingHom := by
      apply Ideal.span_le.mpr
      intro x hx
      have hx' : x = f := hx
      subst x
      exact rawSplitting_f f a D hD
    exact fun x hx => h hx)

@[simp] theorem splitting_mk (f a : R) (D : Derivation K R R) (hD : D f = a) (p : R) :
    splitting f a D hD (Ideal.Quotient.mk (Ideal.span ({f} : Set R)) p) =
      Ideal.Quotient.mk (deformationIdeal f a) ((p, -D p) : Dual R) := rfl

@[simp] theorem reduction_splitting (f a : R)
    (D : Derivation K R R) (hD : D f = a) (x : Closed f) :
    reduction f a (splitting f a D hD x) = x := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

/-- The difference of two actual descended algebra maps has exactly
the indicated epsilon coefficient.  No individual D is descended. -/
theorem splitting_difference_mk (f a : R)
    (D₀ D₁ : Derivation K R R) (h₀ : D₀ f = a) (h₁ : D₁ f = a) (p : R) :
    splitting f a D₁ h₁ (Ideal.Quotient.mk (Ideal.span ({f} : Set R)) p) -
      splitting f a D₀ h₀ (Ideal.Quotient.mk (Ideal.span ({f} : Set R)) p) =
      epsilon f a (Ideal.Quotient.mk (Ideal.span ({f} : Set R)) (D₀ p - D₁ p)) := by
  rw [splitting_mk, splitting_mk, epsilon_mk]
  calc
    _ = Ideal.Quotient.mk (deformationIdeal f a)
        (((p, -D₁ p) : Dual R) - ((p, -D₀ p) : Dual R)) :=
      (map_sub (Ideal.Quotient.mk (deformationIdeal f a)) _ _).symm
    _ = _ := congrArg (Ideal.Quotient.mk (deformationIdeal f a)) (by
      apply TrivSqZeroExt.ext
      · change p - p = 0
        exact sub_self p
      · change -D₁ p - -D₀ p = D₀ p - D₁ p
        ring)

theorem difference_preserves_closed_ideal (f : R)
    (D₀ D₁ : Derivation K R R) (h : D₀ f = D₁ f) (p : R)
    (hp : Ideal.Quotient.mk (Ideal.span ({f} : Set R)) p = 0) :
    Ideal.Quotient.mk (Ideal.span ({f} : Set R)) ((D₀ - D₁) p) = 0 := by
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp (Ideal.Quotient.eq_zero_iff_mem.mp hp)
  rw [← hb, Derivation.leibniz]
  change Ideal.Quotient.mk (Ideal.span ({f} : Set R))
    (b * (D₀ f - D₁ f) + f * (D₀ b - D₁ b)) = 0
  rw [h, sub_self, mul_zero, zero_add, map_mul]
  have hf : Ideal.Quotient.mk (Ideal.span ({f} : Set R)) f = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self f)
  rw [hf, zero_mul]

/-- The ambient difference, and only this difference, descends to an
actual derivation of the closed hypersurface ring. -/
def tangentDifference (f : R) (D₀ D₁ : Derivation K R R) (h : D₀ f = D₁ f) :
    Derivation K (Closed f) (Closed f) :=
  Derivation.liftOfSurjective
    (f := Ideal.Quotient.mkₐ K (Ideal.span ({f} : Set R)))
    Ideal.Quotient.mk_surjective
    (difference_preserves_closed_ideal f D₀ D₁ h)

@[simp] theorem tangentDifference_mk (f : R)
    (D₀ D₁ : Derivation K R R) (h : D₀ f = D₁ f) (p : R) :
    tangentDifference f D₀ D₁ h
      (Ideal.Quotient.mk (Ideal.span ({f} : Set R)) p) =
      Ideal.Quotient.mk (Ideal.span ({f} : Set R)) (D₀ p - D₁ p) :=
  Derivation.liftOfSurjective_apply
    (f := Ideal.Quotient.mkₐ K (Ideal.span ({f} : Set R)))
    Ideal.Quotient.mk_surjective
    (difference_preserves_closed_ideal f D₀ D₁ h) p

theorem splitting_difference (f a : R)
    (D₀ D₁ : Derivation K R R) (h₀ : D₀ f = a) (h₁ : D₁ f = a) (x : Closed f) :
    splitting f a D₁ h₁ x - splitting f a D₀ h₀ x =
      epsilon f a (tangentDifference f D₀ D₁ (h₀.trans h₁.symm) x) := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [tangentDifference_mk]
  exact splitting_difference_mk f a D₀ D₁ h₀ h₁ p

end CycleQ2GeometricSurfaceFirstOrder

end
end SourceFirstOrderSplittings

section SourceFirstOrderCartierRelation

/-! The factored Cartier relation inside the actual quotient by
f - epsilon a, and the transition units on its genuine principal
localizations.  All epsilon coefficients use the canonical localized
kernel map from the original first-order deformation. -/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace CycleQ2GeometricSurfaceFirstOrder

open CycleQ2GeometricKernelLocalization

variable {R : Type*} [CommRing R]

attribute [local instance] reducedAlgebra
attribute [local instance] CycleQ2GeometricKernelLocalization.localReductionAlgebra

/-- The defining first-order equation itself, in the actual quotient. -/
theorem deformation_equation (f a : R) :
    deformationCoordinate f a f =
      epsilon f a (Ideal.Quotient.mk (Ideal.span ({f} : Set R)) a) := by
  have hz : Ideal.Quotient.mk (deformationIdeal f a) (relation f a) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self (relation f a))
  rw [relation_eq, map_sub] at hz
  exact sub_eq_zero.mp hz

/-- The unchanged polynomial function in the actual localized deformation. -/
def localPolynomialMap (f a t : R) : R →+* LocalDeformation f a t :=
  (@algebraMap (Deformation f a) (LocalDeformation f a t)
      (inferInstance : CommSemiring (Deformation f a))
      (inferInstance : Semiring (LocalDeformation f a t)) inferInstance).comp
    ((Ideal.Quotient.mk (deformationIdeal f a)).comp (TrivSqZeroExt.inlHom R R))

/-- The unchanged closed polynomial function in the actual localized fibre. -/
def localClosedPolynomialMap (f a t : R) : R →+* LocalClosed f a t :=
  (algebraMap (Closed f) (LocalClosed f a t)).comp
    (Ideal.Quotient.mk (Ideal.span ({f} : Set R)))

theorem localPolynomialMap_reduction (f a t p : R) :
    algebraMap (LocalDeformation f a t) (LocalClosed f a t)
      (localPolynomialMap f a t p) = localClosedPolynomialMap f a t p := by
  change localReduction (Deformation f a) (Closed f) (deformationCoordinate f a t)
      (@algebraMap (Deformation f a) (LocalDeformation f a t)
        (inferInstance : CommSemiring (Deformation f a))
        (inferInstance : Semiring (LocalDeformation f a t)) inferInstance
        (deformationCoordinate f a p)) =
    algebraMap (Closed f) (LocalClosed f a t)
      (Ideal.Quotient.mk (Ideal.span ({f} : Set R)) p)
  exact localReduction_base (Deformation f a) (Closed f)
    (deformationCoordinate f a t) (deformationCoordinate f a p)

/-- Localization retains the original coefficient of epsilon; this is
the same kernel equivalence used for the projector obstruction. -/
theorem local_deformation_equation (f a t : R)
    (hf : ∀ x : R, f * x = 0 → x = 0) :
    localPolynomialMap f a t f =
      CycleQ2GeometricSquareZeroSplittings.epsilon (localKernelEquiv f a t hf)
        (localClosedPolynomialMap f a t a) := by
  change (@algebraMap (Deformation f a) (LocalDeformation f a t)
      (inferInstance : CommSemiring (Deformation f a))
      (inferInstance : Semiring (LocalDeformation f a t)) inferInstance)
      (deformationCoordinate f a f) =
    (localKernelEquiv f a t hf
      (algebraMap (Closed f) (LocalClosed f a t)
        (Ideal.Quotient.mk (Ideal.span ({f} : Set R)) a))).val
  rw [localKernelEquiv_base, deformation_equation]

/-- A proved polynomial factorization becomes the exact relation
needed by the genuine transition-unit defect calculation. -/
theorem local_factored_deformation_equation (f a t f₁ f₂ g₁ g₂ : R)
    (hf : ∀ x : R, f * x = 0 → x = 0)
    (hF : f = f₁ * g₁ + f₂ * g₂) :
    localPolynomialMap f a t f₁ * localPolynomialMap f a t g₁ +
      localPolynomialMap f a t f₂ * localPolynomialMap f a t g₂ =
        CycleQ2GeometricSquareZeroSplittings.epsilon (localKernelEquiv f a t hf)
          (localClosedPolynomialMap f a t a) := by
  rw [← map_mul, ← map_mul, ← map_add, ← hF]
  exact local_deformation_equation f a t hf

theorem localPolynomialMap_denominator_isUnit (f a t : R) :
    IsUnit (localPolynomialMap f a t t) := by
  exact IsLocalization.Away.algebraMap_isUnit
    (S := LocalDeformation f a t) (deformationCoordinate f a t)

/-- On the actual triple intersection D(g1*g2*f1), all four factors
are units.  The fourth unit is constructed from the actual square-zero
deformation equation, rather than assumed from the reduced surface. -/
theorem local_cartier_units012 (f a f₁ f₂ g₁ g₂ : R)
    (hf : ∀ x : R, f * x = 0 → x = 0)
    (hF : f = f₁ * g₁ + f₂ * g₂) :
    IsUnit (localPolynomialMap f a (g₁ * g₂ * f₁) f₁) ∧
      IsUnit (localPolynomialMap f a (g₁ * g₂ * f₁) f₂) ∧
      IsUnit (localPolynomialMap f a (g₁ * g₂ * f₁) g₁) ∧
      IsUnit (localPolynomialMap f a (g₁ * g₂ * f₁) g₂) := by
  let φ := localPolynomialMap f a (g₁ * g₂ * f₁)
  have hd : IsUnit ((φ g₁ * φ g₂) * φ f₁) := by
    simpa only [map_mul] using localPolynomialMap_denominator_isUnit f a (g₁ * g₂ * f₁)
  have hf₁ := (IsUnit.mul_iff.mp hd).2
  have hg₁ := (IsUnit.mul_iff.mp (IsUnit.mul_iff.mp hd).1).1
  have hg₂ := (IsUnit.mul_iff.mp (IsUnit.mul_iff.mp hd).1).2
  have hother := CycleQ2GeometricCartierTransitionUnits.complementary_factors_are_units
    (localKernelEquiv f a (g₁ * g₂ * f₁) hf) (φ f₁) (φ f₂) (φ g₁) (φ g₂)
    (localClosedPolynomialMap f a (g₁ * g₂ * f₁) a)
    (local_factored_deformation_equation f a (g₁ * g₂ * f₁) f₁ f₂ g₁ g₂ hf hF)
    (hf₁.mul hg₁)
  exact ⟨hf₁, hother.1, hg₁, hg₂⟩

/-- The complementary actual triple D(g1*g2*f2), with no independent
unit premise on f1. -/
theorem local_cartier_units013 (f a f₁ f₂ g₁ g₂ : R)
    (hf : ∀ x : R, f * x = 0 → x = 0)
    (hF : f = f₁ * g₁ + f₂ * g₂) :
    IsUnit (localPolynomialMap f a (g₁ * g₂ * f₂) f₁) ∧
      IsUnit (localPolynomialMap f a (g₁ * g₂ * f₂) f₂) ∧
      IsUnit (localPolynomialMap f a (g₁ * g₂ * f₂) g₁) ∧
      IsUnit (localPolynomialMap f a (g₁ * g₂ * f₂) g₂) := by
  let φ := localPolynomialMap f a (g₁ * g₂ * f₂)
  have hd : IsUnit ((φ g₁ * φ g₂) * φ f₂) := by
    simpa only [map_mul] using localPolynomialMap_denominator_isUnit f a (g₁ * g₂ * f₂)
  have hf₂ := (IsUnit.mul_iff.mp hd).2
  have hg₁ := (IsUnit.mul_iff.mp (IsUnit.mul_iff.mp hd).1).1
  have hg₂ := (IsUnit.mul_iff.mp (IsUnit.mul_iff.mp hd).1).2
  have heq : φ f₂ * φ g₂ + φ f₁ * φ g₁ =
      CycleQ2GeometricSquareZeroSplittings.epsilon (localKernelEquiv f a (g₁ * g₂ * f₂) hf)
        (localClosedPolynomialMap f a (g₁ * g₂ * f₂) a) := by
    rw [add_comm]
    exact local_factored_deformation_equation f a (g₁ * g₂ * f₂) f₁ f₂ g₁ g₂ hf hF
  have hother := CycleQ2GeometricCartierTransitionUnits.complementary_factors_are_units
    (localKernelEquiv f a (g₁ * g₂ * f₂) hf) (φ f₂) (φ f₁) (φ g₂) (φ g₁)
    (localClosedPolynomialMap f a (g₁ * g₂ * f₂) a) heq (hf₂.mul hg₂)
  exact ⟨hother.1, hf₂, hg₁, hg₂⟩

end CycleQ2GeometricSurfaceFirstOrder

end
end SourceFirstOrderCartierRelation

section SourceFirstOrderCartierCocycle

/-! Actual lifted Cartier transition defects on the two nonzero triple
faces.  The units are constructed in the principal localizations of
the genuine first-order quotient; they are not supplied as comparison
data. -/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace CycleQ2GeometricSurfaceFirstOrder

open CycleQ2GeometricKernelLocalization CycleQ2GeometricCartierTransitionUnits
open CycleQ2GeometricSquareZeroSplittings

variable {R : Type*} [CommRing R]

attribute [local instance] reducedAlgebra
attribute [local instance] CycleQ2GeometricKernelLocalization.localReductionAlgebra

/-- The four actual units on D(g1*g2*f1), in order f1,f2,g1,g2. -/
def factorUnits012 (f a f₁ f₂ g₁ g₂ : R)
    (hf : ∀ x : R, f * x = 0 → x = 0)
    (hF : f = f₁ * g₁ + f₂ * g₂) :
    Fin 4 → (LocalDeformation f a (g₁ * g₂ * f₁))ˣ :=
  let h := local_cartier_units012 f a f₁ f₂ g₁ g₂ hf hF
  ![h.1.unit, h.2.1.unit, h.2.2.1.unit, h.2.2.2.unit]

@[simp] theorem factorUnits012_value (f a f₁ f₂ g₁ g₂ : R)
    (hf : ∀ x : R, f * x = 0 → x = 0)
    (hF : f = f₁ * g₁ + f₂ * g₂) (i : Fin 4) :
    (factorUnits012 f a f₁ f₂ g₁ g₂ hf hF i : LocalDeformation f a (g₁ * g₂ * f₁)) =
      localPolynomialMap f a (g₁ * g₂ * f₁) (![f₁, f₂, g₁, g₂] i) := by
  fin_cases i
  · exact (local_cartier_units012 f a f₁ f₂ g₁ g₂ hf hF).1.unit_spec
  · exact (local_cartier_units012 f a f₁ f₂ g₁ g₂ hf hF).2.1.unit_spec
  · exact (local_cartier_units012 f a f₁ f₂ g₁ g₂ hf hF).2.2.1.unit_spec
  · exact (local_cartier_units012 f a f₁ f₂ g₁ g₂ hf hF).2.2.2.unit_spec

@[simp] theorem factorUnits012_reduced (f a f₁ f₂ g₁ g₂ : R)
    (hf : ∀ x : R, f * x = 0 → x = 0)
    (hF : f = f₁ * g₁ + f₂ * g₂) (i : Fin 4) :
    (reducedUnit (C := LocalClosed f a (g₁ * g₂ * f₁))
      (factorUnits012 f a f₁ f₂ g₁ g₂ hf hF i) : LocalClosed f a (g₁ * g₂ * f₁)) =
      localClosedPolynomialMap f a (g₁ * g₂ * f₁) (![f₁, f₂, g₁, g₂] i) := by
  rw [reducedUnit_val, factorUnits012_value, localPolynomialMap_reduction]

theorem factorUnits012_relation (f a f₁ f₂ g₁ g₂ : R)
    (hf : ∀ x : R, f * x = 0 → x = 0)
    (hF : f = f₁ * g₁ + f₂ * g₂) :
    (factorUnits012 f a f₁ f₂ g₁ g₂ hf hF 0 : LocalDeformation f a (g₁ * g₂ * f₁)) *
        factorUnits012 f a f₁ f₂ g₁ g₂ hf hF 2 +
      (factorUnits012 f a f₁ f₂ g₁ g₂ hf hF 1 : LocalDeformation f a (g₁ * g₂ * f₁)) *
        factorUnits012 f a f₁ f₂ g₁ g₂ hf hF 3 =
      CycleQ2GeometricSquareZeroSplittings.epsilon
        (localKernelEquiv f a (g₁ * g₂ * f₁) hf)
        (localClosedPolynomialMap f a (g₁ * g₂ * f₁) a) := by
  simpa only [factorUnits012_value, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] using
    local_factored_deformation_equation f a (g₁ * g₂ * f₁) f₁ f₂ g₁ g₂ hf hF

/-- The actual 012 transition defect, with its actual epsilon coefficient. -/
def transitionDefect012 (f a f₁ f₂ g₁ g₂ : R)
    (hf : ∀ x : R, f * x = 0 → x = 0)
    (hF : f = f₁ * g₁ + f₂ * g₂) : LocalClosed f a (g₁ * g₂ * f₁) :=
  cartierUnitDefect (localKernelEquiv f a (g₁ * g₂ * f₁) hf)
    (factorUnits012 f a f₁ f₂ g₁ g₂ hf hF 0)
    (factorUnits012 f a f₁ f₂ g₁ g₂ hf hF 1)
    (factorUnits012 f a f₁ f₂ g₁ g₂ hf hF 2)
    (factorUnits012 f a f₁ f₂ g₁ g₂ hf hF 3)
    (localClosedPolynomialMap f a (g₁ * g₂ * f₁) a)
    (factorUnits012_relation f a f₁ f₂ g₁ g₂ hf hF)

theorem transitionDefect012_value (f a f₁ f₂ g₁ g₂ : R)
    (hf : ∀ x : R, f * x = 0 → x = 0)
    (hF : f = f₁ * g₁ + f₂ * g₂) :
    transitionDefect012 f a f₁ f₂ g₁ g₂ hf hF =
      localClosedPolynomialMap f a (g₁ * g₂ * f₁) a *
        (↑((reducedUnit (C := LocalClosed f a (g₁ * g₂ * f₁))
          (factorUnits012 f a f₁ f₂ g₁ g₂ hf hF 2))⁻¹) : LocalClosed f a (g₁ * g₂ * f₁)) *
        (↑((reducedUnit (C := LocalClosed f a (g₁ * g₂ * f₁))
          (factorUnits012 f a f₁ f₂ g₁ g₂ hf hF 0))⁻¹) : LocalClosed f a (g₁ * g₂ * f₁)) :=
  cartierUnitDefect_first _ _ _ _ _ _ _

/-- The four actual units on D(g1*g2*f2), in order f1,f2,g1,g2. -/
def factorUnits013 (f a f₁ f₂ g₁ g₂ : R)
    (hf : ∀ x : R, f * x = 0 → x = 0)
    (hF : f = f₁ * g₁ + f₂ * g₂) :
    Fin 4 → (LocalDeformation f a (g₁ * g₂ * f₂))ˣ :=
  let h := local_cartier_units013 f a f₁ f₂ g₁ g₂ hf hF
  ![h.1.unit, h.2.1.unit, h.2.2.1.unit, h.2.2.2.unit]

@[simp] theorem factorUnits013_value (f a f₁ f₂ g₁ g₂ : R)
    (hf : ∀ x : R, f * x = 0 → x = 0)
    (hF : f = f₁ * g₁ + f₂ * g₂) (i : Fin 4) :
    (factorUnits013 f a f₁ f₂ g₁ g₂ hf hF i : LocalDeformation f a (g₁ * g₂ * f₂)) =
      localPolynomialMap f a (g₁ * g₂ * f₂) (![f₁, f₂, g₁, g₂] i) := by
  fin_cases i
  · exact (local_cartier_units013 f a f₁ f₂ g₁ g₂ hf hF).1.unit_spec
  · exact (local_cartier_units013 f a f₁ f₂ g₁ g₂ hf hF).2.1.unit_spec
  · exact (local_cartier_units013 f a f₁ f₂ g₁ g₂ hf hF).2.2.1.unit_spec
  · exact (local_cartier_units013 f a f₁ f₂ g₁ g₂ hf hF).2.2.2.unit_spec

@[simp] theorem factorUnits013_reduced (f a f₁ f₂ g₁ g₂ : R)
    (hf : ∀ x : R, f * x = 0 → x = 0)
    (hF : f = f₁ * g₁ + f₂ * g₂) (i : Fin 4) :
    (reducedUnit (C := LocalClosed f a (g₁ * g₂ * f₂))
      (factorUnits013 f a f₁ f₂ g₁ g₂ hf hF i) : LocalClosed f a (g₁ * g₂ * f₂)) =
      localClosedPolynomialMap f a (g₁ * g₂ * f₂) (![f₁, f₂, g₁, g₂] i) := by
  rw [reducedUnit_val, factorUnits013_value, localPolynomialMap_reduction]

theorem factorUnits013_relation (f a f₁ f₂ g₁ g₂ : R)
    (hf : ∀ x : R, f * x = 0 → x = 0)
    (hF : f = f₁ * g₁ + f₂ * g₂) :
    (factorUnits013 f a f₁ f₂ g₁ g₂ hf hF 0 : LocalDeformation f a (g₁ * g₂ * f₂)) *
        factorUnits013 f a f₁ f₂ g₁ g₂ hf hF 2 +
      (factorUnits013 f a f₁ f₂ g₁ g₂ hf hF 1 : LocalDeformation f a (g₁ * g₂ * f₂)) *
        factorUnits013 f a f₁ f₂ g₁ g₂ hf hF 3 =
      CycleQ2GeometricSquareZeroSplittings.epsilon
        (localKernelEquiv f a (g₁ * g₂ * f₂) hf)
        (localClosedPolynomialMap f a (g₁ * g₂ * f₂) a) := by
  simpa only [factorUnits013_value, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] using
    local_factored_deformation_equation f a (g₁ * g₂ * f₂) f₁ f₂ g₁ g₂ hf hF

/-- The actual 013 transition defect, with its actual epsilon coefficient. -/
def transitionDefect013 (f a f₁ f₂ g₁ g₂ : R)
    (hf : ∀ x : R, f * x = 0 → x = 0)
    (hF : f = f₁ * g₁ + f₂ * g₂) : LocalClosed f a (g₁ * g₂ * f₂) :=
  cartierUnitDefect (localKernelEquiv f a (g₁ * g₂ * f₂) hf)
    (factorUnits013 f a f₁ f₂ g₁ g₂ hf hF 0)
    (factorUnits013 f a f₁ f₂ g₁ g₂ hf hF 1)
    (factorUnits013 f a f₁ f₂ g₁ g₂ hf hF 2)
    (factorUnits013 f a f₁ f₂ g₁ g₂ hf hF 3)
    (localClosedPolynomialMap f a (g₁ * g₂ * f₂) a)
    (factorUnits013_relation f a f₁ f₂ g₁ g₂ hf hF)

theorem transitionDefect013_value (f a f₁ f₂ g₁ g₂ : R)
    (hf : ∀ x : R, f * x = 0 → x = 0)
    (hF : f = f₁ * g₁ + f₂ * g₂) :
    transitionDefect013 f a f₁ f₂ g₁ g₂ hf hF =
      -localClosedPolynomialMap f a (g₁ * g₂ * f₂) a *
        (↑((reducedUnit (C := LocalClosed f a (g₁ * g₂ * f₂))
          (factorUnits013 f a f₁ f₂ g₁ g₂ hf hF 3))⁻¹) : LocalClosed f a (g₁ * g₂ * f₂)) *
        (↑((reducedUnit (C := LocalClosed f a (g₁ * g₂ * f₂))
          (factorUnits013 f a f₁ f₂ g₁ g₂ hf hF 1))⁻¹) : LocalClosed f a (g₁ * g₂ * f₂)) :=
  cartierUnitDefect_second _ _ _ _ _ _ _

end CycleQ2GeometricSurfaceFirstOrder

namespace CycleQ2GeometricSurfaceFirstOrder

open CycleQ2GeometricKernelLocalization CycleQ2GeometricSquareZeroSplittings

variable {R : Type*} [CommRing R]

attribute [local instance] reducedAlgebra
attribute [local instance] CycleQ2GeometricKernelLocalization.localReductionAlgebra

def localClosedDenominator (f a t : R) :
    Submonoid.powers (reduction f a (deformationCoordinate f a t)) :=
  ⟨reduction f a (deformationCoordinate f a t), 1, pow_one _⟩

/-- The literal fraction p/t in the actual localized closed fibre. -/
def localFraction (f a t p : R) : LocalClosed f a t :=
  IsLocalization.mk' (LocalClosed f a t)
    (Ideal.Quotient.mk (Ideal.span ({f} : Set R)) p) (localClosedDenominator f a t)

theorem localFraction_spec (f a t p : R) :
    localFraction f a t p * localClosedPolynomialMap f a t t =
      localClosedPolynomialMap f a t p :=
  IsLocalization.mk'_spec (LocalClosed f a t)
    (Ideal.Quotient.mk (Ideal.span ({f} : Set R)) p) (localClosedDenominator f a t)

private theorem inverse_pair_cancel {S : Type*} [CommRing S]
    (a : S) (u v w : Sˣ) :
    (a * (↑(u⁻¹) : S) * (↑(w⁻¹) : S)) * ((u : S) * v * w) = a * v := by
  calc
    _ = (a * (v : S)) * ((↑(u⁻¹) : S) * u) * ((↑(w⁻¹) : S) * w) := by ring
    _ = _ := by rw [u.inv_mul, w.inv_mul, mul_one, mul_one]

/-- The actual first-order 012 transition defect is the literal
fraction a*g2/(g1*g2*f1), hence a/(g1*f1). -/
theorem transitionDefect012_fraction (f a f₁ f₂ g₁ g₂ : R)
    (hf : ∀ x : R, f * x = 0 → x = 0)
    (hF : f = f₁ * g₁ + f₂ * g₂) :
    transitionDefect012 f a f₁ f₂ g₁ g₂ hf hF =
      localFraction f a (g₁ * g₂ * f₁) (a * g₂) := by
  let φ := localClosedPolynomialMap f a (g₁ * g₂ * f₁)
  let U : Fin 4 → (LocalClosed f a (g₁ * g₂ * f₁))ˣ := fun i =>
    reducedUnit (factorUnits012 f a f₁ f₂ g₁ g₂ hf hF i)
  have h₀ : (U 0 : LocalClosed f a (g₁ * g₂ * f₁)) = φ f₁ :=
    factorUnits012_reduced f a f₁ f₂ g₁ g₂ hf hF 0
  have h₂ : (U 2 : LocalClosed f a (g₁ * g₂ * f₁)) = φ g₁ :=
    factorUnits012_reduced f a f₁ f₂ g₁ g₂ hf hF 2
  have h₃ : (U 3 : LocalClosed f a (g₁ * g₂ * f₁)) = φ g₂ :=
    factorUnits012_reduced f a f₁ f₂ g₁ g₂ hf hF 3
  have hd : φ (g₁ * g₂ * f₁) =
      (U 2 : LocalClosed f a (g₁ * g₂ * f₁)) * U 3 * U 0 := by
    rw [map_mul, map_mul, ← h₀, ← h₂, ← h₃]
  have hv : transitionDefect012 f a f₁ f₂ g₁ g₂ hf hF =
      φ a * (↑((U 2)⁻¹) : LocalClosed f a (g₁ * g₂ * f₁)) *
        (↑((U 0)⁻¹) : LocalClosed f a (g₁ * g₂ * f₁)) :=
    transitionDefect012_value f a f₁ f₂ g₁ g₂ hf hF
  apply (IsLocalization.map_units (LocalClosed f a (g₁ * g₂ * f₁))
    (localClosedDenominator f a (g₁ * g₂ * f₁))).mul_left_inj.mp
  change transitionDefect012 f a f₁ f₂ g₁ g₂ hf hF * φ (g₁ * g₂ * f₁) =
    localFraction f a (g₁ * g₂ * f₁) (a * g₂) * φ (g₁ * g₂ * f₁)
  rw [localFraction_spec, hv, hd]
  change _ = φ (a * g₂)
  rw [map_mul, ← h₃]
  exact inverse_pair_cancel (φ a) (U 2) (U 3) (U 0)

/-- The actual first-order 013 transition defect is the literal
fraction -a*g1/(g1*g2*f2), hence -a/(g2*f2). -/
theorem transitionDefect013_fraction (f a f₁ f₂ g₁ g₂ : R)
    (hf : ∀ x : R, f * x = 0 → x = 0)
    (hF : f = f₁ * g₁ + f₂ * g₂) :
    transitionDefect013 f a f₁ f₂ g₁ g₂ hf hF =
      localFraction f a (g₁ * g₂ * f₂) (-a * g₁) := by
  let φ := localClosedPolynomialMap f a (g₁ * g₂ * f₂)
  let U : Fin 4 → (LocalClosed f a (g₁ * g₂ * f₂))ˣ := fun i =>
    reducedUnit (factorUnits013 f a f₁ f₂ g₁ g₂ hf hF i)
  have h₁ : (U 1 : LocalClosed f a (g₁ * g₂ * f₂)) = φ f₂ :=
    factorUnits013_reduced f a f₁ f₂ g₁ g₂ hf hF 1
  have h₂ : (U 2 : LocalClosed f a (g₁ * g₂ * f₂)) = φ g₁ :=
    factorUnits013_reduced f a f₁ f₂ g₁ g₂ hf hF 2
  have h₃ : (U 3 : LocalClosed f a (g₁ * g₂ * f₂)) = φ g₂ :=
    factorUnits013_reduced f a f₁ f₂ g₁ g₂ hf hF 3
  have hd : φ (g₁ * g₂ * f₂) =
      (U 3 : LocalClosed f a (g₁ * g₂ * f₂)) * U 2 * U 1 := by
    rw [map_mul, map_mul, ← h₁, ← h₂, ← h₃]
    rw [mul_comm (U 2 : LocalClosed f a (g₁ * g₂ * f₂)) (U 3)]
  have hv : transitionDefect013 f a f₁ f₂ g₁ g₂ hf hF =
      -φ a * (↑((U 3)⁻¹) : LocalClosed f a (g₁ * g₂ * f₂)) *
        (↑((U 1)⁻¹) : LocalClosed f a (g₁ * g₂ * f₂)) :=
    transitionDefect013_value f a f₁ f₂ g₁ g₂ hf hF
  apply (IsLocalization.map_units (LocalClosed f a (g₁ * g₂ * f₂))
    (localClosedDenominator f a (g₁ * g₂ * f₂))).mul_left_inj.mp
  change transitionDefect013 f a f₁ f₂ g₁ g₂ hf hF * φ (g₁ * g₂ * f₂) =
    localFraction f a (g₁ * g₂ * f₂) (-a * g₁) * φ (g₁ * g₂ * f₂)
  rw [localFraction_spec, hv, hd]
  change _ = φ (-a * g₁)
  rw [map_mul, map_neg, ← h₂]
  exact inverse_pair_cancel (-φ a) (U 3) (U 2) (U 1)

end CycleQ2GeometricSurfaceFirstOrder

end
end SourceFirstOrderCartierCocycle


section LiteralOriginalCartierTransitionBinding

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralCartierTransitionBinding

open MvPolynomial CycleQ2SeedTrace CycleQ2NormalConnecting
  CycleQ2GeometricSeedNormalIdeals CycleQ2GeometricCartierNormalLift
  CycleQ2GeometricSurfaceFirstOrder CycleQ2GeometricKernelLocalization


abbrev CubicRing := CycleQ2GeometricUniversalSurfaceFirstOrder.CubicQuotient ℂ (CycleQ2GeometricSeedNormalizedCoordinates.cubicCoefficients 57)

local instance cubicSelfModule : Module CubicRing CubicRing := Semiring.toModule
local instance cubicOppositeModule : Module CubicRingᵐᵒᵖ CubicRing := Semiring.toOppositeModule
local instance cubicCentralScalar : IsCentralScalar CubicRing CubicRing where
  op_smul_eq_smul x y := by
    change y * x = x * y
    exact mul_comm y x
local instance cubicSmulCommClass : SMulCommClass CubicRing CubicRingᵐᵒᵖ CubicRing where
  smul_comm x y z := by
    change x * (z * MulOpposite.unop y) = (x * z) * MulOpposite.unop y
    exact (mul_assoc x z (MulOpposite.unop y)).symm

def cubicMap : WeightedPoly →+* CubicRing :=
  Ideal.Quotient.mk (CycleQ2GeometricUniversalSurfaceFirstOrder.cubicIdeal ℂ (CycleQ2GeometricSeedNormalizedCoordinates.cubicCoefficients 57))

def equation : CubicRing :=
  CycleQ2GeometricUniversalSurfaceFirstOrder.sexticClass ℂ (CycleQ2GeometricSeedNormalizedCoordinates.cubicCoefficients 57) (CycleQ2GeometricSeedNormalizedCoordinates.sexticCoefficients 57)

def perturbation : CubicRing := cubicMap derivativeA
def firstEquation : CubicRing := cubicMap (originalF1 57)
def secondEquation : CubicRing := cubicMap originalF2
def firstCofactor : CubicRing := cubicMap (originalG1 57)
def secondCofactor : CubicRing := cubicMap originalG2

theorem equation_regular : ∀ x : CubicRing, equation * x = 0 → x = 0 :=
  CycleQ2GeometricUniversalSurfaceFirstOrder.sexticClass_regular ℂ (CycleQ2GeometricSeedNormalizedCoordinates.cubicCoefficients 57) (CycleQ2GeometricSeedNormalizedCoordinates.sexticCoefficients 57)

theorem cubicMap_cubic : cubicMap (thetaH 1) = 0 := by
  rw [← CycleQ2GeometricSeedNormalizedCoordinates.normalizedCubic_eq_thetaH_one 57]
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact Ideal.subset_span (Set.mem_singleton _)

theorem equation_factorization :
    equation = firstEquation * firstCofactor + secondEquation * secondCofactor := by
  change cubicMap (CycleQ2IncidenceNormalForm.normalizedFullSextic
    (CycleQ2GeometricSeedNormalizedCoordinates.sexticCoefficients 57)) = _
  rw [CycleQ2GeometricSeedNormalizedCoordinates.normalizedSextic_eq_actualSeedEquation]
  simp only [actualSeedEquation, map_add, map_mul, cubicMap_cubic, zero_mul,
    add_zero, firstEquation, firstCofactor, secondEquation, secondCofactor]

/-- The closed fibre of the original first-order family is the same
literal surface used for the already computed Cartier class. -/
def closedEquiv : Closed equation ≃+* SurfaceRing 57 1 :=
  (CycleQ2GeometricUniversalSurfaceFirstOrder.closedSurfaceEquiv ℂ (CycleQ2GeometricSeedNormalizedCoordinates.cubicCoefficients 57) (CycleQ2GeometricSeedNormalizedCoordinates.sexticCoefficients 57)).toRingEquiv.trans
    (CycleQ2GeometricSeedNormalizedCoordinates.surfaceNormalizedRingEquiv 57).toRingEquiv.symm

@[simp] theorem closedEquiv_polynomial (p : WeightedPoly) :
    closedEquiv (Ideal.Quotient.mk (Ideal.span ({equation} : Set CubicRing))
      (cubicMap p)) = surfaceQuotient 57 1 p := by
  apply (CycleQ2GeometricSeedNormalizedCoordinates.surfaceNormalizedRingEquiv 57).injective
  change CycleQ2GeometricSeedNormalizedCoordinates.surfaceNormalizedRingEquiv 57
      ((CycleQ2GeometricSeedNormalizedCoordinates.surfaceNormalizedRingEquiv 57).symm
        (CycleQ2GeometricUniversalSurfaceFirstOrder.closedSurfaceEquiv ℂ (CycleQ2GeometricSeedNormalizedCoordinates.cubicCoefficients 57) (CycleQ2GeometricSeedNormalizedCoordinates.sexticCoefficients 57)
          (Ideal.Quotient.mk (Ideal.span ({equation} : Set CubicRing)) (cubicMap p)))) = _
  rw [AlgEquiv.apply_symm_apply]
  exact (CycleQ2GeometricUniversalSurfaceFirstOrder.closedSurfaceEquiv_mk ℂ
    (CycleQ2GeometricSeedNormalizedCoordinates.cubicCoefficients 57)
    (CycleQ2GeometricSeedNormalizedCoordinates.sexticCoefficients 57) p).trans
    (CycleQ2GeometricSeedNormalizedCoordinates.surfaceNormalizedRingEquiv_mk 57 p).symm

attribute [local instance] reducedAlgebra
attribute [local instance] CycleQ2GeometricKernelLocalization.localReductionAlgebra

abbrev closedCoordinate (t : CubicRing) : Closed equation :=
  @algebraMap (Deformation equation perturbation) (Closed equation)
    (inferInstance : CommSemiring (Deformation equation perturbation))
    (inferInstance : Semiring (Closed equation)) (reducedAlgebra equation perturbation)
    (deformationCoordinate equation perturbation t)

@[simp] theorem closedCoordinate_polynomial (p : WeightedPoly) :
    closedEquiv (closedCoordinate (cubicMap p)) = surfaceQuotient 57 1 p :=
  closedEquiv_polynomial p

/-- The comparison of actual principal localizations is induced by the
identity on polynomial coordinates. Its denominator equality is retained. -/
def localizedClosedEquiv (t : CubicRing) (s : Finset (Fin 4))
    (ht : closedEquiv (closedCoordinate t) = coverProduct 57 1 s) :
    LocalClosed equation perturbation t ≃+* CoverLocal 57 1 s :=
  IsLocalization.ringEquivOfRingEquiv
    (M := Submonoid.powers (closedCoordinate t))
    (T := Submonoid.powers (coverProduct 57 1 s))
    (LocalClosed equation perturbation t) (CoverLocal 57 1 s) closedEquiv
    (by rw [Submonoid.map_powers]; exact congrArg Submonoid.powers ht)

@[simp] theorem localizedClosedEquiv_base (t : CubicRing) (s : Finset (Fin 4))
    (ht : closedEquiv (closedCoordinate t) = coverProduct 57 1 s)
    (x : Closed equation) :
    localizedClosedEquiv t s ht
        (algebraMap (Closed equation) (LocalClosed equation perturbation t) x) =
      algebraMap (SurfaceRing 57 1) (CoverLocal 57 1 s) (closedEquiv x) := by
  unfold localizedClosedEquiv
  exact IsLocalization.ringEquivOfRingEquiv_eq
    (S := LocalClosed equation perturbation t) (Q := CoverLocal 57 1 s)
    (M := Submonoid.powers (closedCoordinate t))
    (T := Submonoid.powers (coverProduct 57 1 s))
    (j := closedEquiv) _ x

@[simp] theorem localizedClosedEquiv_polynomial (t : CubicRing) (s : Finset (Fin 4))
    (ht : closedEquiv (closedCoordinate t) = coverProduct 57 1 s)
    (p : WeightedPoly) :
    localizedClosedEquiv t s ht
        (localClosedPolynomialMap equation perturbation t (cubicMap p)) =
      coverPolyMap 57 1 s p := by
  change localizedClosedEquiv t s ht
      (algebraMap (Closed equation) (LocalClosed equation perturbation t)
        (Ideal.Quotient.mk (Ideal.span ({equation} : Set CubicRing)) (cubicMap p))) = _
  rw [localizedClosedEquiv_base, closedEquiv_polynomial]
  rfl

theorem denominator012 :
    closedEquiv (closedCoordinate (firstCofactor * secondCofactor * firstEquation)) =
      coverProduct 57 1 {0,1,2} := by
  change closedEquiv (closedCoordinate
    (cubicMap (originalG1 57) * cubicMap originalG2 * cubicMap (originalF1 57))) = _
  rw [← map_mul, ← map_mul, closedCoordinate_polynomial]
  simp [map_mul, coverProduct, coverElement, mul_assoc]

theorem denominator013 :
    closedEquiv (closedCoordinate (firstCofactor * secondCofactor * secondEquation)) =
      coverProduct 57 1 {0,1,3} := by
  change closedEquiv (closedCoordinate
    (cubicMap (originalG1 57) * cubicMap originalG2 * cubicMap originalF2)) = _
  rw [← map_mul, ← map_mul, closedCoordinate_polynomial]
  simp [map_mul, coverProduct, coverElement, mul_assoc]

def faceEquiv012 := localizedClosedEquiv
  (firstCofactor * secondCofactor * firstEquation) {0,1,2} denominator012

def faceEquiv013 := localizedClosedEquiv
  (firstCofactor * secondCofactor * secondEquation) {0,1,3} denominator013

@[simp] theorem faceEquiv012_polynomial (p : WeightedPoly) :
    faceEquiv012 (localClosedPolynomialMap equation perturbation
      (firstCofactor * secondCofactor * firstEquation) (cubicMap p)) =
      coverPolyMap 57 1 {0,1,2} p :=
  localizedClosedEquiv_polynomial _ _ _ _

@[simp] theorem faceEquiv013_polynomial (p : WeightedPoly) :
    faceEquiv013 (localClosedPolynomialMap equation perturbation
      (firstCofactor * secondCofactor * secondEquation) (cubicMap p)) =
      coverPolyMap 57 1 {0,1,3} p :=
  localizedClosedEquiv_polynomial _ _ _ _

open CycleQ2GeometricSquareZeroSplittings

def units012 : Fin 4 →
    (LocalDeformation equation perturbation
      (firstCofactor * secondCofactor * firstEquation))ˣ :=
  factorUnits012 equation perturbation firstEquation secondEquation
    firstCofactor secondCofactor equation_regular equation_factorization

def units013 : Fin 4 →
    (LocalDeformation equation perturbation
      (firstCofactor * secondCofactor * secondEquation))ˣ :=
  factorUnits013 equation perturbation firstEquation secondEquation
    firstCofactor secondCofactor equation_regular equation_factorization

def reduced012 (i : Fin 4) :
    (LocalClosed equation perturbation (firstCofactor * secondCofactor * firstEquation))ˣ :=
  reducedUnit (units012 i)

def reduced013 (i : Fin 4) :
    (LocalClosed equation perturbation (firstCofactor * secondCofactor * secondEquation))ˣ :=
  reducedUnit (units013 i)

theorem faceEquiv012_reduced (i : Fin 4) :
    faceEquiv012 (reduced012 i : LocalClosed equation perturbation
      (firstCofactor * secondCofactor * firstEquation)) =
      coverPolyMap 57 1 {0,1,2}
        (![originalF1 57, originalF2, originalG1 57, originalG2] i) := by
  change faceEquiv012 (reducedUnit (C := LocalClosed equation perturbation
    (firstCofactor * secondCofactor * firstEquation))
      (factorUnits012 equation perturbation firstEquation secondEquation
        firstCofactor secondCofactor equation_regular equation_factorization i) :
      LocalClosed equation perturbation
        (firstCofactor * secondCofactor * firstEquation)) = _
  rw [factorUnits012_reduced]
  fin_cases i <;>
    simp only [Matrix.cons_val_zero', Matrix.cons_val_succ'] <;>
    exact localizedClosedEquiv_polynomial _ _ _ _

theorem faceEquiv013_reduced (i : Fin 4) :
    faceEquiv013 (reduced013 i : LocalClosed equation perturbation
      (firstCofactor * secondCofactor * secondEquation)) =
      coverPolyMap 57 1 {0,1,3}
        (![originalF1 57, originalF2, originalG1 57, originalG2] i) := by
  change faceEquiv013 (reducedUnit (C := LocalClosed equation perturbation
    (firstCofactor * secondCofactor * secondEquation))
      (factorUnits013 equation perturbation firstEquation secondEquation
        firstCofactor secondCofactor equation_regular equation_factorization i) :
      LocalClosed equation perturbation
        (firstCofactor * secondCofactor * secondEquation)) = _
  rw [factorUnits013_reduced]
  fin_cases i <;>
    simp only [Matrix.cons_val_zero', Matrix.cons_val_succ'] <;>
    exact localizedClosedEquiv_polynomial _ _ _ _

private theorem map_unit_inverse {S T : Type*} [CommRing S] [CommRing T]
    (f : S →+* T) (u : Sˣ) (v : Tˣ) (h : f (u : S) = (v : T)) :
    f (↑(u⁻¹) : S) = (↑(v⁻¹) : T) := by
  have hu : Units.map f.toMonoidHom u = v := Units.ext h
  change (↑((Units.map f.toMonoidHom u)⁻¹) : T) = (↑(v⁻¹) : T)
  rw [hu]

theorem faceEquiv012_inverse_firstEquation :
    faceEquiv012 (↑((reduced012 0)⁻¹) : LocalClosed equation perturbation
      (firstCofactor * secondCofactor * firstEquation)) =
      (↑((coverUnit 57 1 {0,1,2} 2 (by simp))⁻¹) : CoverLocal 57 1 {0,1,2}) := by
  apply map_unit_inverse faceEquiv012.toRingHom
  change faceEquiv012 (reduced012 0 : LocalClosed equation perturbation
    (firstCofactor * secondCofactor * firstEquation)) =
    (coverUnit 57 1 {0,1,2} 2 (by simp) : CoverLocal 57 1 {0,1,2})
  rw [faceEquiv012_reduced, coverUnit_value]
  rfl

theorem faceEquiv012_inverse_firstCofactor :
    faceEquiv012 (↑((reduced012 2)⁻¹) : LocalClosed equation perturbation
      (firstCofactor * secondCofactor * firstEquation)) =
      (↑((coverUnit 57 1 {0,1,2} 0 (by simp))⁻¹) : CoverLocal 57 1 {0,1,2}) := by
  apply map_unit_inverse faceEquiv012.toRingHom
  change faceEquiv012 (reduced012 2 : LocalClosed equation perturbation
    (firstCofactor * secondCofactor * firstEquation)) =
    (coverUnit 57 1 {0,1,2} 0 (by simp) : CoverLocal 57 1 {0,1,2})
  rw [faceEquiv012_reduced, coverUnit_value]
  rfl

theorem faceEquiv013_inverse_secondEquation :
    faceEquiv013 (↑((reduced013 1)⁻¹) : LocalClosed equation perturbation
      (firstCofactor * secondCofactor * secondEquation)) =
      (↑((coverUnit 57 1 {0,1,3} 3 (by simp))⁻¹) : CoverLocal 57 1 {0,1,3}) := by
  apply map_unit_inverse faceEquiv013.toRingHom
  change faceEquiv013 (reduced013 1 : LocalClosed equation perturbation
    (firstCofactor * secondCofactor * secondEquation)) =
    (coverUnit 57 1 {0,1,3} 3 (by simp) : CoverLocal 57 1 {0,1,3})
  rw [faceEquiv013_reduced, coverUnit_value]
  rfl

theorem faceEquiv013_inverse_secondCofactor :
    faceEquiv013 (↑((reduced013 3)⁻¹) : LocalClosed equation perturbation
      (firstCofactor * secondCofactor * secondEquation)) =
      (↑((coverUnit 57 1 {0,1,3} 1 (by simp))⁻¹) : CoverLocal 57 1 {0,1,3}) := by
  apply map_unit_inverse faceEquiv013.toRingHom
  change faceEquiv013 (reduced013 3 : LocalClosed equation perturbation
    (firstCofactor * secondCofactor * secondEquation)) =
    (coverUnit 57 1 {0,1,3} 1 (by simp) : CoverLocal 57 1 {0,1,3})
  rw [faceEquiv013_reduced, coverUnit_value]
  rfl

/-- This entry comes from the genuine localized deformation F - εA
and the genuine transition units, before any comparison with a cochain. -/
def defect012 : CoverLocal 57 1 {0,1,2} :=
  faceEquiv012 (transitionDefect012 equation perturbation firstEquation secondEquation
    firstCofactor secondCofactor equation_regular equation_factorization)

def defect013 : CoverLocal 57 1 {0,1,3} :=
  faceEquiv013 (transitionDefect013 equation perturbation firstEquation secondEquation
    firstCofactor secondCofactor equation_regular equation_factorization)

theorem defect012_eq_negative_boundary :
    defect012 = -boundary012 57 1 derivativeA 0 := by
  unfold defect012
  rw [transitionDefect012_value, map_mul, map_mul]
  change faceEquiv012
      (localClosedPolynomialMap equation perturbation
        (firstCofactor * secondCofactor * firstEquation) (cubicMap derivativeA)) *
      faceEquiv012 (↑((reduced012 2)⁻¹) : LocalClosed equation perturbation
        (firstCofactor * secondCofactor * firstEquation)) *
      faceEquiv012 (↑((reduced012 0)⁻¹) : LocalClosed equation perturbation
        (firstCofactor * secondCofactor * firstEquation)) = _
  rw [faceEquiv012_inverse_firstCofactor, faceEquiv012_inverse_firstEquation]
  rw [faceEquiv012_polynomial, boundary012_formula]
  simp only [mul_zero, zero_sub, map_neg]
  ring

theorem defect013_eq_negative_boundary :
    defect013 = -boundary013 57 1 derivativeA 0 := by
  unfold defect013
  rw [transitionDefect013_value, map_mul, map_mul, map_neg]
  change -faceEquiv013
      (localClosedPolynomialMap equation perturbation
        (firstCofactor * secondCofactor * secondEquation) (cubicMap derivativeA)) *
      faceEquiv013 (↑((reduced013 3)⁻¹) : LocalClosed equation perturbation
        (firstCofactor * secondCofactor * secondEquation)) *
      faceEquiv013 (↑((reduced013 1)⁻¹) : LocalClosed equation perturbation
        (firstCofactor * secondCofactor * secondEquation)) = _
  rw [faceEquiv013_inverse_secondCofactor, faceEquiv013_inverse_secondEquation]
  rw [faceEquiv013_polynomial, boundary013_formula]
  simp only [mul_zero, zero_sub, map_neg]
  ring

open CycleQ2GeometricFourOpenCech CycleQ2GeometricCartierCech

def defectRepresentative : TwoCochain (CoverLocal 57 1) :=
  ((defect012, defect013), (0,0))

theorem defectRepresentative_eq_negative_original :
    defectRepresentative = -(cartierCycle 57 1 derivativeA 0).val := by
  simp only [defectRepresentative, defect012_eq_negative_boundary,
    defect013_eq_negative_boundary, cartierCycle, Prod.neg_mk, neg_zero]

theorem defectRepresentative_closed :
    d2 (surfaceSystem 57 1) defectRepresentative = 0 := by
  rw [defectRepresentative_eq_negative_original, map_neg,
    (cartierCycle 57 1 derivativeA 0).property, neg_zero]

def defectCycle : TwoCocycles (surfaceSystem 57 1) :=
  ⟨defectRepresentative, defectRepresentative_closed⟩

theorem defectCycle_eq_negative_original :
    defectCycle = -cartierCycle 57 1 derivativeA 0 :=
  Subtype.ext defectRepresentative_eq_negative_original

def defectClass : ActualSecondCech 57 1 := classOf (surfaceSystem 57 1) defectCycle

theorem defectClass_eq_negative_original :
    defectClass = -cartierClass 57 1 derivativeA 0 := by
  rw [defectClass, defectCycle_eq_negative_original, map_neg]
  rfl

theorem defectClass_ne_zero : defectClass ≠ 0 := by
  rw [defectClass_eq_negative_original, neg_ne_zero]
  exact literal_cartierClass_ne_zero

end CycleQ2LiteralCartierTransitionBinding

#print axioms CycleQ2LiteralCartierTransitionBinding.equation_factorization
#print axioms CycleQ2LiteralCartierTransitionBinding.localizedClosedEquiv_polynomial
#print axioms CycleQ2LiteralCartierTransitionBinding.defect012_eq_negative_boundary
#print axioms CycleQ2LiteralCartierTransitionBinding.defect013_eq_negative_boundary
#print axioms CycleQ2LiteralCartierTransitionBinding.defectClass_ne_zero

end
end LiteralOriginalCartierTransitionBinding


section LiteralOriginalCyclicDeformation

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralCyclicDeformation

open MvPolynomial CycleQ2LiteralCartierTransitionBinding
  CycleQ2GeometricSurfaceFirstOrder CycleQ2GeometricSurfaceCoordinates
  CycleQ2SeedCyclicAction CycleQ2GeometricSeedNormalizedCoordinates
  CycleQ2GeometricUniversalSurfaceFirstOrder CycleQ2NormalConnecting
  CycleQ2IncidenceNormalForm

attribute [local instance] CycleQ2LiteralCartierTransitionBinding.cubicSelfModule
  CycleQ2LiteralCartierTransitionBinding.cubicOppositeModule
  CycleQ2LiteralCartierTransitionBinding.cubicCentralScalar
  CycleQ2LiteralCartierTransitionBinding.cubicSmulCommClass

theorem polynomialAction_cubic (ζ : ℂ) (hζ : ζ ^ 3 = 1) :
    polynomialAction ζ (normalizedFullCubic (cubicCoefficients 57)) =
      normalizedFullCubic (cubicCoefficients 57) := by
  rw [normalizedCubic_eq_thetaH_one, ← smoothH_eq_thetaH]
  exact polynomialAction_smoothH ζ hζ Complex.I

theorem polynomialAction_equation (ζ : ℂ) (hζ : ζ ^ 3 = 1) :
    polynomialAction ζ (normalizedFullSextic (sexticCoefficients 57)) =
      normalizedFullSextic (sexticCoefficients 57) := by
  rw [normalizedSextic_eq_actualSeedEquation, actualSeedEquation_eq_smoothF]
  exact polynomialAction_smoothF ζ hζ 57 Complex.I

theorem polynomialAction_perturbation (ζ : ℂ) :
    polynomialAction ζ derivativeA = C ζ * derivativeA := by
  simp only [derivativeA, map_mul, map_pow, polynomialAction_X]
  change (C ζ * X 2) * (X 3) ^ 3 * X 4 =
    C ζ * (X 2 * X 3 ^ 3 * X 4)
  ring

/-- The literal diagonal polynomial action descends through the actual
cubic equation. -/
def cubicAction (ζ : ℂ) (hζ : ζ ^ 3 = 1) : CubicRing →+* CubicRing :=
  (Ideal.quotientMapₐ (cubicIdeal ℂ (cubicCoefficients 57))
    (polynomialAction ζ) (by
      apply Ideal.span_le.mpr
      rintro p (rfl : p = normalizedFullCubic (cubicCoefficients 57))
      change polynomialAction ζ (normalizedFullCubic (cubicCoefficients 57)) ∈
        cubicIdeal ℂ (cubicCoefficients 57)
      rw [polynomialAction_cubic ζ hζ]
      exact Ideal.subset_span (Set.mem_singleton _))).toRingHom

@[simp] theorem cubicAction_polynomial (ζ : ℂ) (hζ : ζ ^ 3 = 1)
    (p : MvPolynomial (Fin 5) ℂ) :
    cubicAction ζ hζ (cubicMap p) = cubicMap (polynomialAction ζ p) := rfl

@[simp] theorem cubicAction_equation (ζ : ℂ) (hζ : ζ ^ 3 = 1) :
    cubicAction ζ hζ equation = equation := by
  have he : equation = cubicMap
      (normalizedFullSextic (sexticCoefficients 57)) := rfl
  rw [he, cubicAction_polynomial, polynomialAction_equation ζ hζ]

theorem cubicAction_perturbation (ζ : ℂ) (hζ : ζ ^ 3 = 1) :
    cubicAction ζ hζ perturbation = cubicMap (C ζ) * perturbation := by
  rw [perturbation, cubicAction_polynomial, polynomialAction_perturbation, map_mul]

def cubicScale (ζ : ℂ) : CubicRing := cubicMap (C (ζ ^ 2))

theorem scaled_perturbation (ζ : ℂ) (hζ : ζ ^ 3 = 1) :
    cubicScale ζ * cubicAction ζ hζ perturbation = perturbation := by
  rw [cubicAction_perturbation, cubicScale, ← mul_assoc, ← map_mul, ← map_mul]
  have hz : ζ ^ 2 * ζ = 1 := (pow_succ ζ 2).symm.trans hζ
  rw [hz, map_one, map_one, one_mul]

theorem relation_fixed (ζ : ℂ) (hζ : ζ ^ 3 = 1) :
    dualMapScaled (cubicAction ζ hζ) (cubicScale ζ)
      (relation equation perturbation) = relation equation perturbation := by
  rw [dualMapScaled_relation, cubicAction_equation, scaled_perturbation]

/-- This endomorphism is defined on the actual quotient by F - εA.
The infinitesimal parameter scales by ζ², so its defining relation is fixed. -/
def deformationAction (ζ : ℂ) (hζ : ζ ^ 3 = 1) :
    Deformation equation perturbation →+* Deformation equation perturbation :=
  Ideal.Quotient.lift (deformationIdeal equation perturbation)
    ((Ideal.Quotient.mk (deformationIdeal equation perturbation)).comp
      (dualMapScaled (cubicAction ζ hζ) (cubicScale ζ))) (by
        intro x hx
        obtain ⟨u, hu⟩ := Ideal.mem_span_singleton'.mp hx
        apply Ideal.Quotient.eq_zero_iff_mem.mpr
        apply Ideal.mem_span_singleton'.mpr
        refine ⟨dualMapScaled (cubicAction ζ hζ) (cubicScale ζ) u, ?_⟩
        rw [← relation_fixed ζ hζ, ← map_mul, hu])

@[simp] theorem deformationAction_mk (ζ : ℂ) (hζ : ζ ^ 3 = 1)
    (z : Dual CubicRing) :
    deformationAction ζ hζ
        (Ideal.Quotient.mk (deformationIdeal equation perturbation) z) =
      Ideal.Quotient.mk (deformationIdeal equation perturbation)
        (dualMapScaled (cubicAction ζ hζ) (cubicScale ζ) z) := rfl

def closedAction (ζ : ℂ) (hζ : ζ ^ 3 = 1) : Closed equation →+* Closed equation :=
  Ideal.Quotient.lift (Ideal.span ({equation} : Set CubicRing))
    ((Ideal.Quotient.mk (Ideal.span ({equation} : Set CubicRing))).comp
      (cubicAction ζ hζ)) (by
        intro x hx
        obtain ⟨u, hu⟩ := Ideal.mem_span_singleton'.mp hx
        apply Ideal.Quotient.eq_zero_iff_mem.mpr
        apply Ideal.mem_span_singleton'.mpr
        refine ⟨cubicAction ζ hζ u, ?_⟩
        rw [← cubicAction_equation ζ hζ, ← map_mul, hu])

@[simp] theorem closedAction_mk (ζ : ℂ) (hζ : ζ ^ 3 = 1) (x : CubicRing) :
    closedAction ζ hζ (Ideal.Quotient.mk (Ideal.span ({equation} : Set CubicRing)) x) =
      Ideal.Quotient.mk (Ideal.span ({equation} : Set CubicRing))
        (cubicAction ζ hζ x) := rfl

def closedConstant : ℂ →+* Closed equation :=
  (Ideal.Quotient.mk (Ideal.span ({equation} : Set CubicRing))).comp (cubicMap.comp C)

@[simp] theorem closedAction_constant (ζ : ℂ) (hζ : ζ ^ 3 = 1) (c : ℂ) :
    closedAction ζ hζ (closedConstant c) = closedConstant c := by
  change Ideal.Quotient.mk (Ideal.span ({equation} : Set CubicRing))
      (cubicMap (polynomialAction ζ (C c))) = _
  rw [polynomialAction_C]
  rfl

/-- The induced closed-fibre action is exactly the existing cyclic
action on the literal seed ring, under the polynomial-preserving maps. -/
theorem closedAction_seedAction (ζ : ℂ) (hζ : ζ ^ 3 = 1) (x : Closed equation) :
    seedRingEquiv 57 (closedEquiv (closedAction ζ hζ x)) =
      seedAction ζ hζ 57 Complex.I (seedRingEquiv 57 (closedEquiv x)) := by
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective b
  change seedRingEquiv 57 (closedEquiv (closedAction ζ hζ
    (Ideal.Quotient.mk (Ideal.span ({equation} : Set CubicRing)) (cubicMap p)))) =
      seedAction ζ hζ 57 Complex.I (seedRingEquiv 57 (closedEquiv
        (Ideal.Quotient.mk (Ideal.span ({equation} : Set CubicRing)) (cubicMap p))))
  rw [closedAction_mk, cubicAction_polynomial, closedEquiv_polynomial,
    closedEquiv_polynomial]
  exact (seedRingEquiv_quotient 57 (polynomialAction ζ p)).trans
    (congrArg (seedAction ζ hζ 57 Complex.I) (seedRingEquiv_quotient 57 p)).symm

theorem reduction_action (ζ : ℂ) (hζ : ζ ^ 3 = 1)
    (z : Deformation equation perturbation) :
    reduction equation perturbation (deformationAction ζ hζ z) =
      closedAction ζ hζ (reduction equation perturbation z) := by
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
  rfl

/-- The inverse-character factor comes from the actual map of deformation
rings, before any cohomology comparison or choice of trace. -/
theorem epsilon_action (ζ : ℂ) (hζ : ζ ^ 3 = 1) (x : Closed equation) :
    deformationAction ζ hζ (epsilon equation perturbation x) =
      epsilon equation perturbation
        (closedConstant (ζ ^ 2) * closedAction ζ hζ x) := by
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [epsilon_mk, deformationAction_mk, closedAction_mk]
  change Ideal.Quotient.mk (deformationIdeal equation perturbation)
      (dualMapScaled (cubicAction ζ hζ) (cubicScale ζ) (TrivSqZeroExt.inr b)) =
    epsilon equation perturbation
      (Ideal.Quotient.mk (Ideal.span ({equation} : Set CubicRing)) (cubicScale ζ) *
        Ideal.Quotient.mk (Ideal.span ({equation} : Set CubicRing)) (cubicAction ζ hζ b))
  rw [← map_mul, epsilon_mk]
  congr 1

abbrev ActualKernel := LinearMap.ker (reduction equation perturbation).toLinearMap

def kernelAction (ζ : ℂ) (hζ : ζ ^ 3 = 1) : ActualKernel →+ ActualKernel where
  toFun z := ⟨deformationAction ζ hζ z.val, by
    change reduction equation perturbation (deformationAction ζ hζ z.val) = 0
    have hz : reduction equation perturbation z.val = 0 := z.property
    rw [reduction_action, hz, map_zero]⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' x y := Subtype.ext (map_add _ x.val y.val)

def coefficient : ActualKernel →+ Closed equation :=
  (kernelEquiv equation perturbation equation_regular).symm.toLinearMap.toAddMonoidHom

theorem coefficient_kernelAction (ζ : ℂ) (hζ : ζ ^ 3 = 1) (z : ActualKernel) :
    coefficient (kernelAction ζ hζ z) =
      closedConstant (ζ ^ 2) * closedAction ζ hζ (coefficient z) := by
  apply epsilon_injective equation perturbation equation_regular
  have he (w : ActualKernel) : epsilon equation perturbation (coefficient w) = w.val :=
    congrArg Subtype.val
      ((kernelEquiv equation perturbation equation_regular).apply_symm_apply w)
  rw [he, ← epsilon_action, he]
  rfl

theorem closedConstant_square (ζ : ℂ) (hζ : ζ ^ 3 = 1) :
    closedConstant (ζ ^ 2) * closedConstant (ζ ^ 2) = closedConstant ζ := by
  rw [← map_mul]
  apply congrArg closedConstant
  calc
    ζ ^ 2 * ζ ^ 2 = ζ ^ 3 * ζ := by ring
    _ = ζ := by rw [hζ, one_mul]

/-- The three terms of the actual infinitesimal orbit yield precisely
the twisted cyclic sum q + ζ²γ(q) + ζγ²(q). -/
theorem coefficient_orbit (ζ : ℂ) (hζ : ζ ^ 3 = 1) (z : ActualKernel) :
    coefficient (z + kernelAction ζ hζ z +
      kernelAction ζ hζ (kernelAction ζ hζ z)) =
      coefficient z + closedConstant (ζ ^ 2) * closedAction ζ hζ (coefficient z) +
        closedConstant ζ * closedAction ζ hζ (closedAction ζ hζ (coefficient z)) := by
  simp only [map_add, coefficient_kernelAction, map_mul, closedAction_constant]
  rw [← mul_assoc, closedConstant_square ζ hζ]

end CycleQ2LiteralCyclicDeformation

#print axioms CycleQ2LiteralCyclicDeformation.relation_fixed
#print axioms CycleQ2LiteralCyclicDeformation.closedAction_seedAction
#print axioms CycleQ2LiteralCyclicDeformation.epsilon_action
#print axioms CycleQ2LiteralCyclicDeformation.coefficient_orbit

end
end LiteralOriginalCyclicDeformation


section CheckedCartierConnectingV5Part1

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace CycleQ2GeometricTransitionTensorProduct

open CycleQ2GeometricSquareZeroSplittings

variable {E C : Type*} [CommRing E] [CommRing C] [Algebra E C]
variable (e : C ≃ₗ[E] RingHom.ker (algebraMap E C))

theorem tensor_cocycle (u v w a b c : Eˣ)
    (h : reducedUnit (C := C) u * reducedUnit v = reducedUnit w)
    (k : reducedUnit (C := C) a * reducedUnit b = reducedUnit c) :
    reducedUnit (C := C) (u * a) * reducedUnit (v * b) = reducedUnit (w * c) := by
  simp only [reducedUnit_mul]
  calc
    (reducedUnit u * reducedUnit a) * (reducedUnit v * reducedUnit b) =
        (reducedUnit u * reducedUnit v) * (reducedUnit a * reducedUnit b) := by ac_rfl
    _ = _ := by rw [h, k]

/-- The obstruction of the tensor product of the actual lifted
transition units is the sum of their fixed epsilon coefficients. -/
theorem unitDefect_tensor (u v w a b c : Eˣ)
    (h : reducedUnit (C := C) u * reducedUnit v = reducedUnit w)
    (k : reducedUnit (C := C) a * reducedUnit b = reducedUnit c) :
    unitDefect e (u * a) (v * b) (w * c) (tensor_cocycle u v w a b c h k) =
      unitDefect e u v w h + unitDefect e a b c k := by
  apply epsilon_injective e
  rw [map_add, epsilon_unitDefect, epsilon_unitDefect, epsilon_unitDefect]
  have hz := epsilon_mul_epsilon e (unitDefect e u v w h) (unitDefect e a b c k)
  rw [epsilon_unitDefect, epsilon_unitDefect] at hz
  have hp : (u * a) * (v * b) * (w * c)⁻¹ = (u * v * w⁻¹) * (a * b * c⁻¹) := by
    simp only [mul_inv_rev]
    ac_rfl
  rw [hp]
  simp only [Units.val_mul] at hz ⊢
  linear_combination hz

theorem unitDefect_exact_cocycle (a b c : Eˣ) (h : a * b = c) :
    unitDefect e a b c (by rw [← reducedUnit_mul, h]) = 0 := by
  apply epsilon_injective e
  rw [epsilon_unitDefect, map_zero, h, mul_inv_cancel, Units.val_one, sub_self]

/-- An ambient line-bundle twist whose transitions already lift as an
exact cocycle contributes zero to the actual scalar obstruction. -/
theorem unitDefect_tensor_exact (u v w a b c : Eˣ)
    (h : reducedUnit (C := C) u * reducedUnit v = reducedUnit w)
    (k : a * b = c) :
    unitDefect e (u * a) (v * b) (w * c)
        (tensor_cocycle u v w a b c h (by rw [← reducedUnit_mul, k])) =
      unitDefect e u v w h := by
  rw [unitDefect_tensor e u v w a b c h (by rw [← reducedUnit_mul, k]),
    unitDefect_exact_cocycle e a b c k, add_zero]

end CycleQ2GeometricTransitionTensorProduct

#print axioms CycleQ2GeometricTransitionTensorProduct.unitDefect_tensor
#print axioms CycleQ2GeometricTransitionTensorProduct.unitDefect_tensor_exact

end

end CheckedCartierConnectingV5Part1


section CheckedCartierConnectingV5Part2

/-!
# The intrinsic Cartier connecting map and its Cech computation

The original literal inverse-ideal short exact sequence gives actual derived
connecting maps, with its intrinsic complex scalar action and restriction
naturality. On any four-open cover, a genuine inverse-ideal lift with scalar
coboundary computes this same connecting map through the existing two-stage
Cech-to-derived comparison. The terminal-source comparison preserves the map.
-/

section CheckedIntrinsicConnectingCore

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2GeometricIntrinsicCartierCohomology

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite TopologicalSpace
  AlgebraicGeometry CycleQ2InjectiveCech CycleQ2CechTwoToDerived
  CycleQ2GeometricDifferentialSheaf CycleQ2GeometricSheafCohomologyScalar
  CycleQ2CechTwoOrdinaryScalar CycleQ2SurfaceCechTwoScalar
  CycleQ2GeometricIntrinsicNormal CycleQ2GeometricIntrinsicCartierSequence
  CycleQ2CartierProjectiveCover CycleQ2GeometricLiteralSurface

variable {X : TopCat.{0}}
local instance sheafHasExt : HasExt.{1} (AbSheaf X) := HasExt.standard _

/-- The actual covariant derived connecting homomorphism of a short exact
sequence of additive sheaves, given by its extension class. -/
def ordinaryConnecting {S : ShortComplex (AbSheaf X)} (hS : S.ShortExact) (n : ℕ) :
    S.X₃.H n →+ S.X₁.H (n + 1) :=
  hS.extClass.postcomp _ rfl

@[simp] theorem ordinaryConnecting_apply {S : ShortComplex (AbSheaf X)}
    (hS : S.ShortExact) (n : ℕ) (x : S.X₃.H n) :
    ordinaryConnecting hS n x = x.comp hS.extClass rfl := rfl

/-- The same connecting operation on actual open-set cohomology. -/
def openConnecting {S : ShortComplex (AbSheaf X)} (hS : S.ShortExact)
    (n : ℕ) (U : Opens X) : S.X₃.H' n U →+ S.X₁.H' (n + 1) U :=
  hS.extClass.postcomp (freeOpen U) rfl

@[simp] theorem openConnecting_apply {S : ShortComplex (AbSheaf X)}
    (hS : S.ShortExact) (n : ℕ) (U : Opens X) (x : S.X₃.H' n U) :
    openConnecting hS n U x = x.comp hS.extClass rfl := rfl

/-- Naturality is the extension-class naturality of the original short
exact sequences; no replacement cohomology map is chosen. -/
theorem ordinaryConnecting_naturality {S T : ShortComplex (AbSheaf X)}
    (hS : S.ShortExact) (hT : T.ShortExact) (f : S ⟶ T)
    (n : ℕ) (x : S.X₃.H n) :
    ordinaryConnecting hT n (Sheaf.H.map f.τ₃ n x) =
      Sheaf.H.map f.τ₁ (n + 1) (ordinaryConnecting hS n x) :=
  (CycleQ2CechTwoNaturality.connecting_naturality hS hT f n x).symm

theorem openConnecting_naturality {S T : ShortComplex (AbSheaf X)}
    (hS : S.ShortExact) (hT : T.ShortExact) (f : S ⟶ T)
    (n : ℕ) (U : Opens X) (x : S.X₃.H' n U) :
    openConnecting hT n U
        (((Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology X) n).map
          f.τ₃).app (op U) x) =
      ((Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology X) (n + 1)).map
        f.τ₁).app (op U) (openConnecting hS n U x) :=
  (CycleQ2CechTwoNaturality.connecting_naturality hS hT f n x).symm

/-- The connecting map commutes with restriction to every actual subopen. -/
theorem openConnecting_restrict {S : ShortComplex (AbSheaf X)}
    (hS : S.ShortExact) (n : ℕ) {U V : Opens X} (h : V ≤ U)
    (x : S.X₃.H' n U) :
    openConnecting hS n V ((S.X₃.cohomologyPresheaf n).map (homOfLE h).op x) =
      (S.X₁.cohomologyPresheaf (n + 1)).map (homOfLE h).op
        (openConnecting hS n U x) := by
  change ((Ext.mk₀ (freeOpenMap h)).comp x (zero_add n)).comp hS.extClass rfl =
    (Ext.mk₀ (freeOpenMap h)).comp (x.comp hS.extClass rfl) (zero_add (n + 1))
  exact Ext.comp_assoc _ _ _ (zero_add n) rfl (zero_add (n + 1))


end CycleQ2GeometricIntrinsicCartierCohomology

#print axioms CycleQ2GeometricIntrinsicCartierCohomology.ordinaryConnecting_naturality
#print axioms CycleQ2GeometricIntrinsicCartierCohomology.openConnecting_restrict

end

end CheckedIntrinsicConnectingCore

section CheckedIntrinsicConnectingModuleScalar

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2GeometricIntrinsicCartierCohomology

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite TopologicalSpace
  AlgebraicGeometry CycleQ2InjectiveCech CycleQ2CechTwoToDerived
  CycleQ2GeometricDifferentialSheaf CycleQ2GeometricSheafCohomologyScalar
  CycleQ2CechTwoOrdinaryScalar CycleQ2GeometricSheafLocalExactness

variable {X : TopCat.{0}}
local instance moduleHasExt : HasExt.{1} (AbSheaf X) := HasExt.standard _

variable (R : X.Sheaf CommRingCat.{0}) (c : ℂ →+* R.obj.obj (op ⊤))
  (S : ShortComplex (SheafOfModules.{0} (ringSheaf R)))

local instance additiveZero : (SheafOfModules.toSheaf.{0} (ringSheaf R)).PreservesZeroMorphisms :=
  moduleSheaf_toSheaf_preservesZeroMorphisms (X := X) (ringSheaf R)

/-- The underlying additive complex of the original module-sheaf maps. -/
def moduleAdditiveComplex : ShortComplex (AbSheaf X) :=
  S.map (SheafOfModules.toSheaf.{0} (ringSheaf R))

/-- Actual complex multiplication on every member of a module-sheaf complex. -/
def moduleScalarComplexEnd (z : ℂ) :
    moduleAdditiveComplex R S ⟶ moduleAdditiveComplex R S where
  τ₁ := scalarEnd R c S.X₁ z
  τ₂ := scalarEnd R c S.X₂ z
  τ₃ := scalarEnd R c S.X₃ z
  comm₁₂ := scalarEnd_naturality R c S.X₁ S.f z
  comm₂₃ := scalarEnd_naturality R c S.X₂ S.g z

theorem moduleConnecting_scalar (hS : (moduleAdditiveComplex R S).ShortExact)
    (n : ℕ) (z : ℂ) (x : (additiveSheaf R S.X₃).H n) :
    ordinaryConnecting hS n (ordinaryScalar R c S.X₃ n z x) =
      ordinaryScalar R c S.X₁ (n + 1) z (ordinaryConnecting hS n x) :=
  ordinaryConnecting_naturality hS hS (moduleScalarComplexEnd R c S z) n x


end CycleQ2GeometricIntrinsicCartierCohomology
#print axioms CycleQ2GeometricIntrinsicCartierCohomology.moduleConnecting_scalar
end

end CheckedIntrinsicConnectingModuleScalar

section CheckedIntrinsicCartierConnectingActual

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2GeometricIntrinsicCartierCohomology

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite TopologicalSpace
  AlgebraicGeometry CycleQ2InjectiveCech CycleQ2CechTwoToDerived
  CycleQ2GeometricDifferentialSheaf CycleQ2GeometricSheafCohomologyScalar
  CycleQ2CechTwoOrdinaryScalar CycleQ2SurfaceCechTwoScalar
  CycleQ2GeometricIntrinsicNormal CycleQ2GeometricIntrinsicCartierSequence
  CycleQ2CartierProjectiveCover CycleQ2GeometricLiteralSurface

variable {X : TopCat.{0}}
local instance actualHasExt : HasExt.{1} (AbSheaf X) := HasExt.standard _

section LiteralSequence

/-- The additive sheaf underlying the actual intrinsic direct-image normal. -/
abbrev intrinsicNormalAdditiveSheaf (r θ : ℂ) : AbSheaf (projectiveSurface r θ) :=
  additiveSheaf (projectiveSurface r θ).sheaf
    (normalDirectImageSheaf (curveToSurface r θ))

/-- The genuine degree-one to degree-two Cartier connecting homomorphism
for the unchanged literal curve immersion and its actual ideal. -/
def literalConnecting :
    (intrinsicNormalAdditiveSheaf 57 1).H 1 →+
      (CycleQ2GeometricProjectiveHOne.structureAdditiveSheaf (projectiveSurface 57 1)).H 2 :=
  ordinaryConnecting literalInverseIdealAdditiveComplex_shortExact 1

/-- Its open-set version, on every open of the literal surface. -/
def literalOpenConnecting (U : (projectiveSurface 57 1).Opens) :
    (intrinsicNormalAdditiveSheaf 57 1).H' 1 U →+
      (CycleQ2GeometricProjectiveHOne.structureAdditiveSheaf (projectiveSurface 57 1)).H' 2 U :=
  openConnecting literalInverseIdealAdditiveComplex_shortExact 1 U

/-- Complex linearity for the intrinsic cohomology scalar action, before
bundling a linear-map record. Both scalar operations apply the actual scalar
endomorphism of the corresponding original sheaf. -/
theorem literalConnecting_scalar (z : ℂ)
    (x : (intrinsicNormalAdditiveSheaf 57 1).H 1) :
    literalConnecting
        (ordinaryScalar (projectiveSurface 57 1).sheaf (surfaceGlobalCoefficient 57 1)
          (normalDirectImageSheaf (curveToSurface 57 1)) 1 z x) =
      ordinaryScalar (projectiveSurface 57 1).sheaf (surfaceGlobalCoefficient 57 1)
        (structureModule (projectiveSurface 57 1)) 2 z (literalConnecting x) :=
  moduleConnecting_scalar (projectiveSurface 57 1).sheaf (surfaceGlobalCoefficient 57 1)
    (literalInverseIdealComplex 57 1) literalInverseIdealAdditiveComplex_shortExact 1 z x

theorem literalOpenConnecting_restrict {U V : (projectiveSurface 57 1).Opens}
    (h : V ≤ U) (x : (intrinsicNormalAdditiveSheaf 57 1).H' 1 U) :
    literalOpenConnecting V
        (((intrinsicNormalAdditiveSheaf 57 1).cohomologyPresheaf 1).map
          (homOfLE h).op x) =
      ((CycleQ2GeometricProjectiveHOne.structureAdditiveSheaf (projectiveSurface 57 1)).cohomologyPresheaf 2).map
        (homOfLE h).op (literalOpenConnecting U x) :=
  openConnecting_restrict literalInverseIdealAdditiveComplex_shortExact 1 h x

end LiteralSequence

end CycleQ2GeometricIntrinsicCartierCohomology

#print axioms CycleQ2GeometricIntrinsicCartierCohomology.literalConnecting
#print axioms CycleQ2GeometricIntrinsicCartierCohomology.literalOpenConnecting
#print axioms CycleQ2GeometricIntrinsicCartierCohomology.literalConnecting_scalar
#print axioms CycleQ2GeometricIntrinsicCartierCohomology.literalOpenConnecting_restrict

end

end CheckedIntrinsicCartierConnectingActual

section CheckedConnectingTerminal

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2GeometricIntrinsicCartierCohomology

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite TopologicalSpace
  CycleQ2InjectiveCech CycleQ2CechTwoToDerived CycleQ2GeometricSheafCohomologyRestriction

variable {X : TopCat.{0}}
local instance terminalHasExt : HasExt.{1} (AbSheaf X) := HasExt.standard _

/-- The original terminal-source comparison intertwines the genuine
connecting homomorphisms, in every degree. -/
theorem terminalCohomologyEquiv_connecting {S : ShortComplex (AbSheaf X)}
    (hS : S.ShortExact) (n : ℕ) (x : S.X₃.H' n ⊤) :
    terminalCohomologyEquiv (Opens.grothendieckTopology X) S.X₁ ⊤ isTerminalTop (n + 1)
        (openConnecting hS n ⊤ x) =
      ordinaryConnecting hS n
        (terminalCohomologyEquiv (Opens.grothendieckTopology X) S.X₃ ⊤ isTerminalTop n x) := by
  let e := terminalFreeSheafIso (Opens.grothendieckTopology X) ⊤ isTerminalTop
  change (Ext.mk₀ e.inv).comp (x.comp hS.extClass rfl) (zero_add (n + 1)) =
    ((Ext.mk₀ e.inv).comp x (zero_add n)).comp hS.extClass rfl
  exact (Ext.comp_assoc _ _ _ (zero_add n) rfl (zero_add (n + 1))).symm

end CycleQ2GeometricIntrinsicCartierCohomology

#print axioms CycleQ2GeometricIntrinsicCartierCohomology.terminalCohomologyEquiv_connecting

end

end CheckedConnectingTerminal

section CheckedFourOpenHOne

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2FourOpenHOne

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite TopologicalSpace
  CycleQ2InjectiveCech CycleQ2GeometricSheafLocalIso CycleQ2CechTwoToDerived
  CycleQ2CechTwoComparison CycleQ2CechTwoNaturality

variable {X : TopCat.{0}}
local instance sheafHasExt : HasExt.{1} (AbSheaf X) := HasExt.standard _
variable {F G : AbSheaf X} (U : Fin 4 → Opens X)

/-- A one-cocycle is lifted into the original injective presentation and
descended to one genuine global quotient section. -/
structure OneDescent (u : One F U) where
  primitive : Zero (presentation F).X₂ U
  differential : d0 (presentation F).X₂ U primitive = mapOne U (presentation F).f u
  globalSection : Sections (presentation F).X₃ ⊤
  global_restriction : globalZero U globalSection = mapZero U (presentation F).g primitive

theorem oneDescent_nonempty (hcover : (⨆ i, U i) = ⊤)
    (u : One F U) (hu : d1 F U u = 0) : Nonempty (OneDescent U u) := by
  obtain ⟨a, ha⟩ := one_exact_of_injective U (mapOne U (presentation F).f u) (by
    rw [← mapTwo_d1, hu, mapTwo_zero])
  have hp : d0 (presentation F).X₃ U (mapZero U (presentation F).g a) = 0 := by
    rw [← mapOne_d0, ha, mapOne_comp, (presentation F).zero, mapOne_zeroHom]
  obtain ⟨t, ht⟩ := globalZero_exists U hcover _ hp
  exact ⟨⟨a, ha, t, ht⟩⟩

def oneDescentClass {u : One F U} (d : OneDescent U u) : F.H' 1 ⊤ :=
  (sectionExtZero ⊤ d.globalSection).comp (presentation_shortExact F).extClass rfl

/-- Every choice of the actual injective primitive gives the same derived
degree-one class. -/
theorem oneDescentClass_independent (hcover : (⨆ i, U i) = ⊤)
    {u : One F U} (d e : OneDescent U u) :
    oneDescentClass U d = oneDescentClass U e := by
  have hdiff : d0 (presentation F).X₂ U (d.primitive - e.primitive) = 0 := by
    rw [d0_sub, d.differential, e.differential, sub_self]
  obtain ⟨a, ha⟩ := globalZero_exists U hcover _ hdiff
  have hglobal : d.globalSection - e.globalSection = app (presentation F).g ⊤ a := by
    apply globalZero_injective U hcover
    rw [globalZero_sub, d.global_restriction, e.global_restriction,
      ← mapZero_sub, ← ha, mapZero_globalZero]
  apply sub_eq_zero.mp
  change (sectionExtZero ⊤ d.globalSection).comp (presentation_shortExact F).extClass rfl -
    (sectionExtZero ⊤ e.globalSection).comp (presentation_shortExact F).extClass rfl = 0
  have hsub :
      (sectionExtZero ⊤ d.globalSection).comp (presentation_shortExact F).extClass rfl -
        (sectionExtZero ⊤ e.globalSection).comp (presentation_shortExact F).extClass rfl =
      (sectionExtZero ⊤ (d.globalSection - e.globalSection)).comp
        (presentation_shortExact F).extClass rfl := by
    rw [sectionExtZero_sub]
    simp only [sub_eq_add_neg, Ext.add_comp, Ext.neg_comp]
  rw [hsub, hglobal, sectionExtZero_app,
    Ext.comp_assoc_of_second_deg_zero, ShortComplex.ShortExact.comp_extClass, Ext.comp_zero]

/-- The canonical actual derived class of a four-open one-cocycle. -/
def cechOneClass (hcover : (⨆ i, U i) = ⊤) (u : One F U) (hu : d1 F U u = 0) :
    F.H' 1 ⊤ :=
  oneDescentClass U (Classical.choice (oneDescent_nonempty U hcover u hu))

theorem cechOneClass_eq_oneDescentClass (hcover : (⨆ i, U i) = ⊤)
    (u : One F U) (hu : d1 F U u = 0) (d : OneDescent U u) :
    cechOneClass U hcover u hu = oneDescentClass U d :=
  oneDescentClass_independent U hcover _ d

/-- Actual presentation maps transport every component of the descent. -/
def transportOneDescent (f : F ⟶ G) {u : One F U} (d : OneDescent U u) :
    OneDescent U (mapOne U f u) where
  primitive := mapZero U (presentationMap f).τ₂ d.primitive
  differential := by
    rw [← mapOne_d0, d.differential, mapOne_comp,
      ← (presentationMap f).comm₁₂, ← mapOne_comp]
  globalSection := app (presentationMap f).τ₃ ⊤ d.globalSection
  global_restriction := by
    rw [← mapZero_globalZero, d.global_restriction, mapZero_comp,
      ← (presentationMap f).comm₂₃, ← mapZero_comp]

theorem oneDescentClass_naturality (f : F ⟶ G)
    {u : One F U} (d : OneDescent U u) :
    (oneDescentClass U d).comp (Ext.mk₀ f) (add_zero 1) =
      oneDescentClass U (transportOneDescent U f d) := by
  dsimp only [oneDescentClass, transportOneDescent]
  rw [connecting_naturality (presentation_shortExact F) (presentation_shortExact G)
    (presentationMap f), ← sectionExtZero_app]

/-- The degree-one comparison is natural for every genuine sheaf morphism. -/
theorem cechOneClass_naturality (hcover : (⨆ i, U i) = ⊤) (f : F ⟶ G)
    (u : One F U) (hu : d1 F U u = 0)
    (hfu : d1 G U (mapOne U f u) = 0) :
    (cechOneClass U hcover u hu).comp (Ext.mk₀ f) (add_zero 1) =
      cechOneClass U hcover (mapOne U f u) hfu := by
  let d := Classical.choice (oneDescent_nonempty U hcover u hu)
  change (oneDescentClass U d).comp (Ext.mk₀ f) (add_zero 1) = _
  rw [oneDescentClass_naturality]
  exact (cechOneClass_eq_oneDescentClass U hcover _ hfu
    (transportOneDescent U f d)).symm

/-- A genuine Čech boundary has zero image in actual derived H-one. -/
theorem cechOneClass_boundary (hcover : (⨆ i, U i) = ⊤)
    (a : Zero F U) (ha : d1 F U (d0 F U a) = 0) :
    cechOneClass U hcover (d0 F U a) ha = 0 := by
  let d : OneDescent U (d0 F U a) :=
    { primitive := mapZero U (presentation F).f a
      differential := (mapOne_d0 U (presentation F).f a).symm
      globalSection := 0
      global_restriction := by
        rw [globalZero_zero, mapZero_comp, (presentation F).zero, mapZero_zeroHom] }
  rw [cechOneClass_eq_oneDescentClass U hcover _ ha d]
  simp only [oneDescentClass, d, sectionExtZero, map_zero, Ext.mk₀_zero, Ext.zero_comp]

end CycleQ2FourOpenHOne

#print axioms CycleQ2FourOpenHOne.oneDescentClass_independent
#print axioms CycleQ2FourOpenHOne.cechOneClass_naturality
#print axioms CycleQ2FourOpenHOne.cechOneClass_boundary

end

end CheckedFourOpenHOne

section CheckedFourOpenConnectingBoundary

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2FourOpenConnectingBoundary

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite TopologicalSpace
  CycleQ2InjectiveCech CycleQ2CechTwoToDerived CycleQ2CechTwoComparison
  CycleQ2CechTwoNaturality CycleQ2FourOpenHOne

variable {X : TopCat.{0}}
local instance boundaryHasExt : HasExt.{1} (AbSheaf X) := HasExt.standard _

/-- A short exact sequence maps to the actual injective presentation of
its first sheaf, with identity as its first component. -/
def toPresentation {S : ShortComplex (AbSheaf X)} (hS : S.ShortExact) :
    S ⟶ presentation S.X₁ := by
  letI := hS.mono_f
  letI := hS.epi_g
  let m : S.X₂ ⟶ (presentation S.X₁).X₂ :=
    Injective.factorThru (presentation S.X₁).f S.f
  have hm : S.f ≫ m = (presentation S.X₁).f := Injective.comp_factorThru _ _
  have hz : S.f ≫ (m ≫ (presentation S.X₁).g) = 0 := by
    rw [← Category.assoc, hm, (presentation S.X₁).zero]
  exact
    { τ₁ := 𝟙 _
      τ₂ := m
      τ₃ := hS.exact.desc (m ≫ (presentation S.X₁).g) hz
      comm₁₂ := by simpa only [Category.id_comp] using hm.symm
      comm₂₃ := (hS.exact.g_desc (m ≫ (presentation S.X₁).g) hz).symm }

@[simp] theorem toPresentation_first {S : ShortComplex (AbSheaf X)} (hS : S.ShortExact) :
    (toPresentation hS).τ₁ = 𝟙 S.X₁ := rfl

variable (U : Fin 4 → Opens X)

/-- The reduction of an actual inverse-image cochain is a one-cocycle
whenever its scalar coboundary is in the original first sheaf. -/
theorem reduced_lift_closed {S : ShortComplex (AbSheaf X)}
    (b : One S.X₂ U) (c : Two S.X₁ U)
    (hb : d1 S.X₂ U b = mapTwo U S.f c) :
    d1 S.X₃ U (mapOne U S.g b) = 0 := by
  rw [← mapTwo_d1, hb, mapTwo_comp, S.zero, mapTwo_zeroHom]

/-- The actual derived connecting map sends the derived class of the
reduced lift to precisely the existing two-stage Čech-to-derived class
of its scalar coboundary. No affine vanishing or replacement trace is used. -/
theorem cechOneClass_connecting {S : ShortComplex (AbSheaf X)}
    (hS : S.ShortExact) (hcover : (⨆ i, U i) = ⊤)
    (b : One S.X₂ U) (c : Two S.X₁ U)
    (hb : d1 S.X₂ U b = mapTwo U S.f c) (hc : d2 S.X₁ U c = 0) :
    (cechOneClass U hcover (mapOne U S.g b) (reduced_lift_closed U b c hb)).comp
        hS.extClass rfl = cechTwoClass U hcover c hc := by
  let m := toPresentation hS
  let u := mapOne U S.g b
  have hu : d1 S.X₃ U u = 0 := reduced_lift_closed U b c hb
  let a := mapOne U m.τ₂ b
  have ha : d1 (presentation S.X₁).X₂ U a = mapTwo U (presentation S.X₁).f c := by
    dsimp only [a]
    rw [← mapTwo_d1, hb, mapTwo_comp, ← m.comm₁₂]
    change mapTwo U ((𝟙 S.X₁) ≫ (presentation S.X₁).f) c = _
    rw [Category.id_comp]
  let v := mapOne U m.τ₃ u
  have hv : v = mapOne U (presentation S.X₁).g a := by
    dsimp only [v, u, a]
    rw [mapOne_comp, mapOne_comp, m.comm₂₃]
  have hvclosed : d1 (presentation S.X₁).X₃ U v = 0 := by
    dsimp only [v]
    rw [← mapTwo_d1, hu, mapTwo_zero]
  let d := Classical.choice (oneDescent_nonempty U hcover v hvclosed)
  let dd : TwoDescent U c :=
    { first := a
      first_differential := ha
      second := d.primitive
      second_differential := by rw [d.differential, hv]
      globalSection := d.globalSection
      global_restriction := d.global_restriction }
  have hnat := connecting_naturality hS (presentation_shortExact S.X₁) m 1
    (cechOneClass U hcover u hu)
  have hleft : (cechOneClass U hcover u hu).comp hS.extClass rfl =
      ((cechOneClass U hcover u hu).comp (Ext.mk₀ m.τ₃) (add_zero 1)).comp
        (presentation_shortExact S.X₁).extClass rfl := by
    simpa only [m, toPresentation_first, Ext.comp_mk₀_id] using hnat
  change (cechOneClass U hcover u hu).comp hS.extClass rfl = _
  rw [hleft, cechOneClass_naturality U hcover m.τ₃ u hu hvclosed,
    cechOneClass_eq_oneDescentClass U hcover v hvclosed d,
    cechTwoClass_eq_descentClass U hcover c hc dd]
  rfl

end CycleQ2FourOpenConnectingBoundary

#print axioms CycleQ2FourOpenConnectingBoundary.toPresentation
#print axioms CycleQ2FourOpenConnectingBoundary.cechOneClass_connecting

end

end CheckedFourOpenConnectingBoundary


end CheckedCartierConnectingV5Part2


section CheckedCartierConnectingV5Part3

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2FourOpenMayerVietoris

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite TopologicalSpace
  CycleQ2InjectiveCech CycleQ2CechTwoToDerived CycleQ2FourOpenHOne
  CycleQ2ThreeOpenInjectiveComparison CycleQ2GeometricSheafLocalIso

variable {X : TopCat.{0}}
local instance sheafHasExt : HasExt.{1} (AbSheaf X) := HasExt.standard _
variable {F : AbSheaf X} (U : Fin 4 → Opens X)

/-- A genuine morphism from the two-open Mayer--Vietoris sequence to the
injective presentation retained by the four-open descent. The minus sign
is forced by the two differential conventions. -/
def oneDescentComparison {u : One F U} (d : OneDescent U u) :
    (Opens.mayerVietorisSquare (U 0) (U 1)).shortComplex ⟶ presentation F where
  τ₁ := sectionHom (U 0 ⊓ U 1) (-u.1)
  τ₂ := biprod.desc (sectionHom (U 0) (d.primitive 0))
    (sectionHom (U 1) (d.primitive 1))
  τ₃ := sectionHom (U 0 ⊔ U 1)
    (res (presentation F).X₃ le_top d.globalSection)
  comm₁₂ := by
    apply (freeOpenSections (presentation F).X₂ (U 0 ⊓ U 1)).injective
    rw [sectionHom_postcomp, sectionHom_section]
    change _ = freeOpenSections (presentation F).X₂ (U 0 ⊓ U 1)
      (biprod.lift (freeOpenMap inf_le_left) (-(freeOpenMap inf_le_right)) ≫
        biprod.desc (sectionHom (U 0) (d.primitive 0))
          (sectionHom (U 1) (d.primitive 1)))
    rw [sections_biprod_lift, map_neg]
    have hd := congrArg Prod.fst d.differential
    change res (presentation F).X₂ inf_le_right (d.primitive 1) -
      res (presentation F).X₂ inf_le_left (d.primitive 0) =
        app (presentation F).f (U 0 ⊓ U 1) u.1 at hd
    rw [← hd]
    abel
  comm₂₃ := by
    apply biprod.hom_ext'
    · simp only [GrothendieckTopology.MayerVietorisSquare.shortComplex_g,
        biprod.inl_desc_assoc]
      change sectionHom (U 0) (d.primitive 0) ≫ (presentation F).g =
        freeOpenMap le_sup_left ≫ sectionHom (U 0 ⊔ U 1)
          (res (presentation F).X₃ le_top d.globalSection)
      rw [sectionHom_postcomp, sectionHom_restrict, res_comp]
      exact congrArg (sectionHom (U 0)) (congrFun d.global_restriction 0).symm
    · simp only [GrothendieckTopology.MayerVietorisSquare.shortComplex_g,
        biprod.inr_desc_assoc]
      change sectionHom (U 1) (d.primitive 1) ≫ (presentation F).g =
        freeOpenMap le_sup_right ≫ sectionHom (U 0 ⊔ U 1)
          (res (presentation F).X₃ le_top d.globalSection)
      rw [sectionHom_postcomp, sectionHom_restrict, res_comp]
      exact congrArg (sectionHom (U 1)) (congrFun d.global_restriction 1).symm

/-- The restricted four-open injective-descent class is the actual
Mayer--Vietoris boundary of the negative edge section. -/
theorem oneDescentClass_restrict_eq_mv {u : One F U} (d : OneDescent U u) :
    (F.cohomologyPresheaf 1).map
        (homOfLE (show U 0 ⊔ U 1 ≤ ⊤ from le_top)).op (oneDescentClass U d) =
      (Opens.mayerVietorisSquare (U 0) (U 1)).δ F 0 1 rfl
        ((CycleQ2GeometricConeCech.HZero.sectionsEquiv F (U 0 ⊓ U 1)).symm (-u.1)) := by
  have h := ShortComplex.ShortExact.extClass_naturality
    (Opens.mayerVietorisSquare (U 0) (U 1)).shortComplex_shortExact
    (presentation_shortExact F) (oneDescentComparison U d)
  change (Opens.mayerVietorisSquare (U 0) (U 1)).shortComplex_shortExact.extClass.comp
      (sectionExtZero (U 0 ⊓ U 1) (-u.1)) (add_zero 1) =
    (sectionExtZero (U 0 ⊔ U 1) (res (presentation F).X₃ le_top d.globalSection)).comp
      (presentation_shortExact F).extClass (zero_add 1) at h
  rw [sectionExtZero_restrict] at h
  change (Ext.mk₀ (freeOpenMap (show U 0 ⊔ U 1 ≤ ⊤ from le_top))).comp
      ((sectionExtZero ⊤ d.globalSection).comp (presentation_shortExact F).extClass rfl)
        (zero_add 1) = _
  rw [← Ext.comp_assoc _ _ _ (zero_add 0) rfl (zero_add 1), ← h]
  change _ = (Opens.mayerVietorisSquare (U 0) (U 1)).shortComplex_shortExact.extClass.comp
    ((CycleQ2GeometricConeCech.HZero.sectionsEquiv F (U 0 ⊓ U 1)).symm (-u.1)) (add_zero 1)
  rw [sectionExtZero_eq_hzero]

/-- A canonical Čech class retains this exact sign under restriction.
No vanishing or support hypothesis is needed for the comparison. -/
theorem cechOneClass_restrict_eq_mv (hcover : (⨆ i, U i) = ⊤)
    (u : One F U) (hu : d1 F U u = 0) :
    (F.cohomologyPresheaf 1).map
        (homOfLE (show U 0 ⊔ U 1 ≤ ⊤ from le_top)).op
          (cechOneClass U hcover u hu) =
      (Opens.mayerVietorisSquare (U 0) (U 1)).δ F 0 1 rfl
        ((CycleQ2GeometricConeCech.HZero.sectionsEquiv F (U 0 ⊓ U 1)).symm (-u.1)) :=
  oneDescentClass_restrict_eq_mv U (Classical.choice (oneDescent_nonempty U hcover u hu))

end CycleQ2FourOpenMayerVietoris

#print axioms CycleQ2FourOpenMayerVietoris.oneDescentComparison
#print axioms CycleQ2FourOpenMayerVietoris.cechOneClass_restrict_eq_mv

end

end CheckedCartierConnectingV5Part3


section CheckedCartierConnectingV5Part4

/-! The original inverse-ideal lift defines an actual intrinsic-normal class.
Its genuine connecting image is precisely the unchanged original Cartier class,
both at the terminal open and in ordinary derived cohomology. -/

section CheckedLiteralNormalCocycle

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2GeometricIntrinsicCartierCohomology

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite TopologicalSpace
  AlgebraicGeometry CycleQ2InjectiveCech CycleQ2CechTwoToDerived CycleQ2FourOpenHOne
  CycleQ2FourOpenConnectingBoundary CycleQ2GeometricIntrinsicCartierSequence
  CycleQ2CartierProjectiveCover CycleQ2ProjectiveInverseIdeal
  CycleQ2GeometricSheafCohomologyRestriction

open CycleQ2ProjectiveCartierIntersections (literal_cover)
open CycleQ2ProjectiveCartierDerived
  (literalCocycle literalCocycle_closed literalDerivedClassAtTop
   literalDerivedClassAtTop_ne_zero literalTerminalCohomologyEquiv
   literalDerivedClass literalDerivedClass_ne_zero)

local instance normalClassHasExt :
    HasExt.{1} (AbSheaf (projectiveSurface 57 1)) := HasExt.standard _

/-- Reduce the original projective inverse-ideal lift through the actual
normal-sheaf morphism. The six edges and their sign are unchanged. -/
def literalNormalCocycle :
    One literalSequence.X₃ (coverFamily 57 1) :=
  mapOne (coverFamily 57 1) literalSequence.g literalConnectingOne

theorem literalNormalCocycle_closed :
    d1 literalSequence.X₃ (coverFamily 57 1) literalNormalCocycle = 0 :=
  reduced_lift_closed (S := literalSequence) (coverFamily 57 1) literalConnectingOne literalCocycle
    literalConnectingOne_boundary

/-- The actual intrinsic-normal H-one class of that original lift. -/
def literalNormalClassAtTop : literalSequence.X₃.H' 1 ⊤ :=
  cechOneClass (coverFamily 57 1) literal_cover literalNormalCocycle
    literalNormalCocycle_closed


end CycleQ2GeometricIntrinsicCartierCohomology

#print axioms CycleQ2GeometricIntrinsicCartierCohomology.literalNormalCocycle_closed
#print axioms CycleQ2GeometricIntrinsicCartierCohomology.literalNormalClassAtTop

end

end CheckedLiteralNormalCocycle

section CheckedLiteralNormalConnectingTop

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2GeometricIntrinsicCartierCohomology

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite TopologicalSpace
  AlgebraicGeometry CycleQ2InjectiveCech CycleQ2CechTwoToDerived CycleQ2FourOpenHOne
  CycleQ2FourOpenConnectingBoundary CycleQ2GeometricIntrinsicCartierSequence
  CycleQ2CartierProjectiveCover CycleQ2ProjectiveInverseIdeal
  CycleQ2GeometricSheafCohomologyRestriction

open CycleQ2ProjectiveCartierIntersections (literal_cover)
open CycleQ2ProjectiveCartierDerived
  (literalCocycle literalCocycle_closed literalDerivedClassAtTop
   literalDerivedClassAtTop_ne_zero literalTerminalCohomologyEquiv
   literalDerivedClass literalDerivedClass_ne_zero)

local instance normalTopHasExt :
    HasExt.{1} (AbSheaf (projectiveSurface 57 1)) := HasExt.standard _

/-- The genuine connecting map produces the original nonzero Cartier
class, with its exact existing normalization and positive coboundary sign. -/
theorem literalOpenConnecting_normalClass :
    literalOpenConnecting ⊤ literalNormalClassAtTop = literalDerivedClassAtTop :=
  cechOneClass_connecting (S := literalSequence) (coverFamily 57 1)
    literalInverseIdealAdditiveComplex_shortExact literal_cover
    literalConnectingOne literalCocycle literalConnectingOne_boundary literalCocycle_closed

theorem literalNormalClassAtTop_ne_zero : literalNormalClassAtTop ≠ 0 := by
  intro hz
  apply literalDerivedClassAtTop_ne_zero
  rw [← literalOpenConnecting_normalClass, hz, map_zero]


end CycleQ2GeometricIntrinsicCartierCohomology

#print axioms CycleQ2GeometricIntrinsicCartierCohomology.literalOpenConnecting_normalClass
#print axioms CycleQ2GeometricIntrinsicCartierCohomology.literalNormalClassAtTop_ne_zero

end

end CheckedLiteralNormalConnectingTop

section CheckedLiteralNormalConnectingOrdinary

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2GeometricIntrinsicCartierCohomology

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite TopologicalSpace
  AlgebraicGeometry CycleQ2InjectiveCech CycleQ2CechTwoToDerived CycleQ2FourOpenHOne
  CycleQ2FourOpenConnectingBoundary CycleQ2GeometricIntrinsicCartierSequence
  CycleQ2CartierProjectiveCover CycleQ2ProjectiveInverseIdeal
  CycleQ2GeometricSheafCohomologyRestriction

open CycleQ2ProjectiveCartierIntersections (literal_cover)
open CycleQ2ProjectiveCartierDerived
  (literalCocycle literalCocycle_closed literalDerivedClassAtTop
   literalDerivedClassAtTop_ne_zero literalTerminalCohomologyEquiv
   literalDerivedClass literalDerivedClass_ne_zero)

local instance normalOrdinaryHasExt :
    HasExt.{1} (AbSheaf (projectiveSurface 57 1)) := HasExt.standard _

/-- The same class in ordinary derived cohomology, using the existing
terminal-source equivalence. -/
def literalNormalClass : literalSequence.X₃.H 1 :=
  terminalCohomologyEquiv (Opens.grothendieckTopology (projectiveSurface 57 1))
    literalSequence.X₃ ⊤ isTerminalTop 1 literalNormalClassAtTop

/-- The ordinary connecting map gives precisely the original ordinary
Cartier H-two class; no alternative surface class is introduced. -/
theorem literalConnecting_normalClass :
    literalConnecting literalNormalClass = literalDerivedClass :=
  (terminalCohomologyEquiv_connecting (S := literalSequence) literalInverseIdealAdditiveComplex_shortExact
    1 literalNormalClassAtTop).symm.trans
      (congrArg literalTerminalCohomologyEquiv literalOpenConnecting_normalClass)

theorem literalNormalClass_ne_zero : literalNormalClass ≠ 0 := by
  intro hz
  apply literalDerivedClass_ne_zero
  rw [← literalConnecting_normalClass, hz, map_zero]

theorem literalConnecting_ne_zero : literalConnecting ≠ 0 := by
  intro hz
  apply literalDerivedClass_ne_zero
  rw [← literalConnecting_normalClass, hz]
  rfl


end CycleQ2GeometricIntrinsicCartierCohomology

#print axioms CycleQ2GeometricIntrinsicCartierCohomology.literalConnecting_normalClass
#print axioms CycleQ2GeometricIntrinsicCartierCohomology.literalNormalClass_ne_zero
#print axioms CycleQ2GeometricIntrinsicCartierCohomology.literalConnecting_ne_zero

end

end CheckedLiteralNormalConnectingOrdinary

end CheckedCartierConnectingV5Part4
