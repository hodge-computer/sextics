import Mathlib.RingTheory.Localization.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Algebra.MvPolynomial.CommRing

/-! Reusable finite-algebra and contact calculus extracted from `HeadOfNaps`’
accepted quadric-contact-broken (#122) and holdout-q2 (#124) proofs.
See this directory’s README for hypotheses, entry points, and attribution. -/

/-! Coefficients regular at a known good parameter value.
A matrix is invertible in this coefficient ring whenever its specialization is.
This avoids claiming that a single specialized solution solves the generic problem. -/
namespace RegularSpecialization

variable {R K : Type*} [CommRing R] [Field K]

/-- All polynomial denominators whose value at the chosen point is nonzero. -/
def denominators (f : R →+* K) : Submonoid R where
  carrier := {r | f r ≠ 0}
  one_mem' := by simp
  mul_mem' := by intro a b ha hb; simpa using mul_ne_zero ha hb

@[simp] theorem mem_denominators (f : R →+* K) (r : R) :
    r ∈ denominators f ↔ f r ≠ 0 := Iff.rfl

abbrev Coefficients (f : R →+* K) := Localization (denominators f)

/-- Evaluation is defined on these fractions, with no partial-function convention. -/
noncomputable def specialize (f : R →+* K) : Coefficients f →+* K :=
  IsLocalization.lift (fun s : denominators f => isUnit_iff_ne_zero.mpr s.property)

@[simp] theorem specialize_algebraMap (f : R →+* K) (r : R) :
    specialize f (algebraMap R (Coefficients f) r) = f r :=
  IsLocalization.lift_eq _ r

/-- A coefficient is a unit exactly when it has nonzero specialization. -/
theorem isUnit_iff_specialize_ne_zero (f : R →+* K) (x : Coefficients f) :
    IsUnit x ↔ specialize f x ≠ 0 := by
  constructor
  · intro h
    exact (h.map (specialize f)).ne_zero
  · intro hx
    obtain ⟨r, s, rfl⟩ := IsLocalization.exists_mk'_eq (denominators f) x
    have hr : f r ≠ 0 := by
      have he := congrArg (specialize f) (IsLocalization.mk'_spec (Coefficients f) r s)
      simp only [map_mul, specialize_algebraMap] at he
      rw [← he]
      exact mul_ne_zero hx s.property
    have hu : IsUnit (algebraMap R (Coefficients f) r) :=
      IsLocalization.map_units (Coefficients f) (⟨r, hr⟩ : denominators f)
    rw [← IsLocalization.mk'_spec (Coefficients f) r s] at hu
    exact ((Commute.all _ _).isUnit_mul_iff.mp hu).1

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Specialization certifies generic matrix invertibility in the regular coefficient ring. -/
theorem isUnit_det_iff (f : R →+* K) (A : Matrix n n (Coefficients f)) :
    IsUnit A.det ↔ (A.map (specialize f)).det ≠ 0 := by
  rw [isUnit_iff_specialize_ne_zero, RingHom.map_det]
  rfl

/-- A supplied inverse of the specialized matrix suffices; no large determinant expansion. -/
theorem isUnit_det_of_specialized_right_inverse
    (f : R →+* K) (A : Matrix n n (Coefficients f)) (B : Matrix n n K)
    (h : A.map (specialize f) * B = 1) : IsUnit A.det := by
  rw [isUnit_det_iff]
  exact Matrix.det_ne_zero_of_right_inverse h

theorem mul_inverse_of_specialized_right_inverse
    (f : R →+* K) (A : Matrix n n (Coefficients f)) (B : Matrix n n K)
    (h : A.map (specialize f) * B = 1) : A * A⁻¹ = 1 :=
  Matrix.mul_nonsing_inv A (isUnit_det_of_specialized_right_inverse f A B h)

theorem inverse_mul_of_specialized_right_inverse
    (f : R →+* K) (A : Matrix n n (Coefficients f)) (B : Matrix n n K)
    (h : A.map (specialize f) * B = 1) : A⁻¹ * A = 1 :=
  Matrix.nonsing_inv_mul A (isUnit_det_of_specialized_right_inverse f A B h)

end RegularSpecialization

