import Proposal.GeometricSurfaceAdjunction
import Proposal.GeometricSquareZeroAtiyah
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
import Proposal.GeometricFamilyDeformation
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Tactic.FinCases

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
