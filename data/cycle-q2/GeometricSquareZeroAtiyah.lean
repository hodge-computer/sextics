import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.Tactic.Ring
import Mathlib.RingTheory.Nilpotent.Basic
import Proposal.GeometricCartierNormalLift
import Mathlib.Tactic.Abel

section SourceSquareZeroSplittings

/-! Actual differences of algebra splittings of a square-zero extension.
The input linear equivalence identifies the genuine reduction kernel,
with its genuine module action; it is supplied by the localized first-
order deformation.  No ambient derivation is asserted to descend. -/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace CycleQ2GeometricSquareZeroSplittings

variable {K E C : Type*} [CommRing K] [CommRing E] [CommRing C]
variable [Algebra K E] [Algebra K C] [Algebra E C] [IsScalarTower K E C]

variable (e : C ≃ₗ[E] RingHom.ker (algebraMap E C))

/-- The inclusion of the actual reduction kernel, with its fixed
coefficient normalization. -/
def epsilon : C →ₗ[E] E :=
  (RingHom.ker (algebraMap E C)).subtype.comp e.toLinearMap

@[simp] theorem epsilon_apply (x : C) : epsilon e x = (e x).val := rfl

theorem epsilon_injective : Function.Injective (epsilon e) :=
  Subtype.val_injective.comp e.injective

@[simp] theorem reduction_epsilon (x : C) :
    algebraMap E C (epsilon e x) = 0 := (e x).property

theorem mul_epsilon (z : E) (x : C) :
    z * epsilon e x = epsilon e (algebraMap E C z * x) := by
  simpa only [Algebra.smul_def, Algebra.algebraMap_self, RingHom.id_apply] using
    ((epsilon e).map_smul z x).symm

theorem epsilon_mul_epsilon (x y : C) :
    epsilon e x * epsilon e y = 0 := by
  rw [mul_epsilon, reduction_epsilon, zero_mul, map_zero]

/-- Extract the unique coefficient of a genuine kernel element. -/
def coefficient (z : E) (hz : algebraMap E C z = 0) : C :=
  e.symm ⟨z, hz⟩

@[simp] theorem epsilon_coefficient (z : E) (hz : algebraMap E C z = 0) :
    epsilon e (coefficient e z hz) = z :=
  congrArg Subtype.val (e.apply_symm_apply ⟨z, hz⟩)

include e in
theorem kernel_mul_zero (x y : E) (hx : algebraMap E C x = 0)
    (hy : algebraMap E C y = 0) : x * y = 0 := by
  rw [← epsilon_coefficient e x hx, ← epsilon_coefficient e y hy]
  exact epsilon_mul_epsilon e _ _

variable (σ τ : C →ₐ[K] E)
variable (hσ : ∀ x, algebraMap E C (σ x) = x)
variable (hτ : ∀ x, algebraMap E C (τ x) = x)

/-- The difference τ−σ takes values in the actual square-zero kernel. -/
def differenceLinear : C →ₗ[K] C :=
  (e.symm.toLinearMap.restrictScalars K).comp
    ((τ.toLinearMap - σ.toLinearMap).codRestrict
      ((RingHom.ker (algebraMap E C)).restrictScalars K) (fun x => by
        change algebraMap E C (τ x - σ x) = 0
        rw [map_sub, hτ, hσ, sub_self]))

@[simp] theorem epsilon_differenceLinear (x : C) :
    epsilon e (differenceLinear e σ τ hσ hτ x) = τ x - σ x := by
  change (e (e.symm ⟨τ x - σ x, _⟩)).val = _
  exact congrArg Subtype.val (e.apply_symm_apply _)

include hσ in
theorem epsilon_mul_of_splitting (x y : C) :
    epsilon e (x * y) = σ x * epsilon e y := by
  rw [mul_epsilon, hσ]

/-- The actual splitting difference is a derivation on the closed ring.
This is the local Kodaira--Spencer representative, with sign τ−σ. -/
def difference : Derivation K C C where
  toLinearMap := differenceLinear e σ τ hσ hτ
  map_one_eq_zero' := by
    apply epsilon_injective e
    rw [epsilon_differenceLinear, map_one, map_one, sub_self, map_zero]
  leibniz' x y := by
    apply epsilon_injective e
    change epsilon e (differenceLinear e σ τ hσ hτ (x * y)) =
      epsilon e (x * differenceLinear e σ τ hσ hτ y +
        y * differenceLinear e σ τ hσ hτ x)
    rw [epsilon_differenceLinear, map_add,
      epsilon_mul_of_splitting e σ hσ, epsilon_mul_of_splitting e σ hσ,
      epsilon_differenceLinear, epsilon_differenceLinear, map_mul, map_mul]
    have hz : (τ x - σ x) * (τ y - σ y) = 0 := by
      apply kernel_mul_zero e <;> rw [map_sub, hτ, hσ, sub_self]
    calc
      τ x * τ y - σ x * σ y =
          σ x * (τ y - σ y) + σ y * (τ x - σ x) +
            (τ x - σ x) * (τ y - σ y) := by ring
      _ = _ := by rw [hz, add_zero]

@[simp] theorem epsilon_difference (x : C) :
    epsilon e (difference e σ τ hσ hτ x) = τ x - σ x :=
  epsilon_differenceLinear e σ τ hσ hτ x

/-- The actual universal logarithmic differential of a transition unit. -/
def logDifferential (g : Cˣ) : KaehlerDifferential K C :=
  (↑(g⁻¹) : C) • KaehlerDifferential.D K C (g : C)

theorem contraction_logDifferential (g : Cˣ) :
    (difference e σ τ hσ hτ).liftKaehlerDifferential (logDifferential (K := K) g) =
      (↑(g⁻¹) : C) * difference e σ τ hσ hτ (g : C) := by
  simp only [logDifferential, map_smul, Derivation.liftKaehlerDifferential_comp_D,
    smul_eq_mul]

/-- Contraction is the normalized difference of the actual splittings
on the actual transition function. -/
theorem epsilon_contraction_logDifferential (g : Cˣ) :
    epsilon e
      ((difference e σ τ hσ hτ).liftKaehlerDifferential
        (logDifferential (K := K) g)) =
      σ (↑(g⁻¹) : C) * (τ (g : C) - σ (g : C)) := by
  rw [contraction_logDifferential, epsilon_mul_of_splitting e σ hσ,
    epsilon_difference]

end CycleQ2GeometricSquareZeroSplittings

end
end SourceSquareZeroSplittings

section SourceSquareZeroAtiyahComparison

/-! Exact cocycle-level comparison between actual transition defects and
the contraction of actual splitting differences with universal dlog.
The sign is product minus direct transition.  This is an algebraic
identity, not an identification with a Hodge-theoretic derivative. -/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace CycleQ2GeometricSquareZeroSplittings

variable {K E C : Type*} [CommRing K] [CommRing E] [CommRing C]
variable [Algebra K E] [Algebra K C] [Algebra E C] [IsScalarTower K E C]

def reducedUnit (u : Eˣ) : Cˣ := Units.map (algebraMap E C).toMonoidHom u

@[simp] theorem reducedUnit_val (u : Eˣ) :
    (reducedUnit (C := C) u : C) = algebraMap E C (u : E) := rfl

@[simp] theorem reducedUnit_mul (u v : Eˣ) :
    reducedUnit (C := C) (u * v) = reducedUnit u * reducedUnit v := map_mul _ _ _

@[simp] theorem reducedUnit_inv (u : Eˣ) :
    reducedUnit (C := C) u⁻¹ = (reducedUnit u)⁻¹ := map_inv _ _

def normalizedUnitValue (σ : C →ₐ[K] E) (u : Eˣ) : E :=
  (u : E) * σ (↑((reducedUnit (C := C) u)⁻¹) : C)

theorem normalizedUnitValue_reduction (σ : C →ₐ[K] E)
    (hσ : ∀ x, algebraMap E C (σ x) = x) (u : Eˣ) :
    algebraMap E C (normalizedUnitValue σ u) = 1 := by
  rw [normalizedUnitValue, map_mul, hσ]
  exact (reducedUnit (C := C) u).mul_inv

theorem normalizedUnitValue_mul (σ : C →ₐ[K] E) (u v : Eˣ) :
    normalizedUnitValue σ (u * v) =
      normalizedUnitValue σ u * normalizedUnitValue σ v := by
  simp only [normalizedUnitValue, reducedUnit_mul, mul_inv_rev,
    Units.val_mul, map_mul]
  ring

variable (e : C ≃ₗ[E] RingHom.ker (algebraMap E C))
variable (σ τ : C →ₐ[K] E)
variable (hσ : ∀ x, algebraMap E C (σ x) = x)
variable (hτ : ∀ x, algebraMap E C (τ x) = x)

/-- Compare an actual lifted transition unit with its lift under σ,
using the fixed coefficient of the genuine reduction kernel. -/
def unitCorrection (u : Eˣ) : C :=
  coefficient e (normalizedUnitValue σ u - 1) (by
    rw [map_sub, normalizedUnitValue_reduction σ hσ, map_one, sub_self])

@[simp] theorem epsilon_unitCorrection (u : Eˣ) :
    epsilon e (unitCorrection e σ hσ u) = normalizedUnitValue σ u - 1 :=
  epsilon_coefficient e _ _

@[simp] theorem unitCorrection_one : unitCorrection e σ hσ (1 : Eˣ) = 0 := by
  apply epsilon_injective e
  simp only [epsilon_unitCorrection, normalizedUnitValue, reducedUnit, map_one,
    inv_one, Units.val_one, one_mul, sub_self, map_zero]

theorem unitCorrection_mul (u v : Eˣ) :
    unitCorrection e σ hσ (u * v) =
      unitCorrection e σ hσ u + unitCorrection e σ hσ v := by
  apply epsilon_injective e
  rw [map_add, epsilon_unitCorrection, epsilon_unitCorrection,
    epsilon_unitCorrection, normalizedUnitValue_mul]
  have hz : (normalizedUnitValue σ u - 1) * (normalizedUnitValue σ v - 1) = 0 := by
    apply kernel_mul_zero e
    · rw [map_sub, normalizedUnitValue_reduction σ hσ, map_one, sub_self]
    · rw [map_sub, normalizedUnitValue_reduction σ hσ, map_one, sub_self]
  calc
    normalizedUnitValue σ u * normalizedUnitValue σ v - 1 =
        (normalizedUnitValue σ u - 1) + (normalizedUnitValue σ v - 1) +
          (normalizedUnitValue σ u - 1) * (normalizedUnitValue σ v - 1) := by ring
    _ = _ := by rw [hz, add_zero]

theorem unitCorrection_inv (u : Eˣ) :
    unitCorrection e σ hσ u⁻¹ = -unitCorrection e σ hσ u := by
  have h := unitCorrection_mul e σ hσ u u⁻¹
  rw [mul_inv_cancel, unitCorrection_one] at h
  calc
    unitCorrection e σ hσ u⁻¹ =
        (unitCorrection e σ hσ u + unitCorrection e σ hσ u⁻¹) -
          unitCorrection e σ hσ u := by ring
    _ = _ := by rw [← h, zero_sub]

/-- Changing the actual local splitting changes the transition
correction by precisely the contraction of its universal dlog. -/
theorem unitCorrection_change (u : Eˣ) :
    unitCorrection e σ hσ u - unitCorrection e τ hτ u =
      (difference e σ τ hσ hτ).liftKaehlerDifferential
        (logDifferential (K := K) (reducedUnit (C := C) u)) := by
  let g : Cˣ := reducedUnit u
  let δ : Derivation K C C := difference e σ τ hσ hτ
  apply epsilon_injective e
  rw [map_sub, epsilon_unitCorrection, epsilon_unitCorrection,
    contraction_logDifferential]
  change normalizedUnitValue σ u - 1 - (normalizedUnitValue τ u - 1) =
    epsilon e ((↑(g⁻¹) : C) * δ (g : C))
  have hi : δ (↑(g⁻¹) : C) = -(↑(g⁻¹) : C) ^ 2 * δ (g : C) := by
    simpa only [smul_eq_mul] using δ.leibniz_of_mul_eq_one g.inv_mul
  calc
    normalizedUnitValue σ u - 1 - (normalizedUnitValue τ u - 1) =
        -(u : E) * epsilon e (δ (↑(g⁻¹) : C)) := by
      dsimp only [normalizedUnitValue, δ, g]
      rw [epsilon_difference]
      ring
    _ = epsilon e (-((g : C)) * δ (↑(g⁻¹) : C)) := by
      rw [mul_epsilon, map_neg]
      rfl
    _ = epsilon e ((↑(g⁻¹) : C) * δ (g : C)) := by
      congr 1
      rw [hi]
      calc
        -(g : C) * (-(↑(g⁻¹) : C) ^ 2 * δ (g : C)) =
            (↑(g⁻¹) : C) * δ (g : C) * ((g : C) * ↑(g⁻¹)) := by ring
        _ = _ := by rw [g.mul_inv, mul_one]

/-- The actual product-minus-direct transition defect.  Its reduction
vanishes because the actual reduced units satisfy the cocycle law. -/
def unitDefect (u v w : Eˣ)
    (h : reducedUnit (C := C) u * reducedUnit v = reducedUnit w) : C :=
  coefficient e (((u * v * w⁻¹ : Eˣ) : E) - 1) (by
    simp only [map_sub, map_one, Units.val_mul, map_mul]
    change ((reducedUnit (C := C) u * reducedUnit v *
      (reducedUnit w)⁻¹ : Cˣ) : C) - 1 = 0
    rw [h, mul_inv_cancel, Units.val_one, sub_self])

@[simp] theorem epsilon_unitDefect (u v w : Eˣ)
    (h : reducedUnit (C := C) u * reducedUnit v = reducedUnit w) :
    epsilon e (unitDefect e u v w h) = ((u * v * w⁻¹ : Eˣ) : E) - 1 :=
  epsilon_coefficient e _ _

theorem unitDefect_eq_corrections (u v w : Eˣ)
    (h : reducedUnit (C := C) u * reducedUnit v = reducedUnit w) :
    unitDefect e u v w h = unitCorrection e σ hσ u +
      unitCorrection e σ hσ v - unitCorrection e σ hσ w := by
  have hg : reducedUnit (C := C) (u * v * w⁻¹) = 1 := by
    rw [reducedUnit_mul, reducedUnit_mul, reducedUnit_inv, h, mul_inv_cancel]
  have he : unitDefect e u v w h = unitCorrection e σ hσ (u * v * w⁻¹) := by
    apply epsilon_injective e
    rw [epsilon_unitDefect, epsilon_unitCorrection, normalizedUnitValue,
      hg, inv_one, Units.val_one, map_one, mul_one]
  rw [he, unitCorrection_mul, unitCorrection_mul, unitCorrection_inv,
    sub_eq_add_neg]

/-- The precise algebraic Atiyah--Kodaira--Spencer cocycle identity.
The scalar obstruction is the actual transition defect.  The correction
terms form a Čech coboundary; the remaining term evaluates the actual
closed-ring splitting difference on the actual universal dlog class. -/
theorem unitDefect_eq_boundary_add_contraction (u v w : Eˣ)
    (h : reducedUnit (C := C) u * reducedUnit v = reducedUnit w) :
    unitDefect e u v w h =
      (unitCorrection e τ hτ v - unitCorrection e σ hσ w +
        unitCorrection e σ hσ u) +
      (difference e σ τ hσ hτ).liftKaehlerDifferential
        (logDifferential (K := K) (reducedUnit (C := C) v)) := by
  rw [unitDefect_eq_corrections e σ hσ]
  have hc := unitCorrection_change e σ τ hσ hτ v
  rw [← hc]
  ring

end CycleQ2GeometricSquareZeroSplittings

end
end SourceSquareZeroAtiyahComparison

section SourceCartierTransitionUnits

/-! The actual transition-unit calculation for a factored Cartier
divisor in a square-zero hypersurface deformation.  The convention is
product minus direct transition.  The defining relation is
f1*g1 + f2*g2 = epsilon(a), where a=A-kL, so the resulting obstruction
is the negative of the named Cartier cochain with B=kL-A. -/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace CycleQ2GeometricCartierTransitionUnits

open CycleQ2GeometricSquareZeroSplittings

variable {E C : Type*} [CommRing E] [CommRing C] [Algebra E C]
variable (e : C ≃ₗ[E] RingHom.ker (algebraMap E C))

/-- Inverting one product in the factored equation makes the other
product invertible as well: the discrepancy lies in the actual
square-zero kernel.  This constructs the missing pairwise transition
units on the actual Cartier cover. -/
theorem complementary_factors_are_units (f₁ f₂ g₁ g₂ : E) (a : C)
    (hF : f₁ * g₁ + f₂ * g₂ = epsilon e a) (h : IsUnit (f₁ * g₁)) :
    IsUnit f₂ ∧ IsUnit g₂ := by
  have hn : IsNilpotent (epsilon e a) := by
    refine ⟨2, ?_⟩
    rw [pow_two]
    exact epsilon_mul_epsilon e a a
  have hp : IsUnit (f₂ * g₂) := by
    have hu : IsUnit (-(f₁ * g₁) + epsilon e a) :=
      hn.isUnit_add_left_of_commute h.neg (Commute.all _ _)
    have he : f₂ * g₂ = -(f₁ * g₁) + epsilon e a := by
      rw [← hF]
      ring
    exact he.symm ▸ hu
  exact IsUnit.mul_iff.mp hp

/-- The exact inverse-ideal transition from 1/f2 to 1/f1. -/
def transition01 (g₁ g₂ : Eˣ) : Eˣ := -g₁ * g₂⁻¹

theorem reduced_factorization (f₁ f₂ g₁ g₂ : Eˣ) (a : C)
    (hF : (f₁ : E) * g₁ + (f₂ : E) * g₂ = epsilon e a) :
    (reducedUnit (C := C) f₁ : C) * (reducedUnit (C := C) g₁ : C) +
      (reducedUnit (C := C) f₂ : C) * (reducedUnit (C := C) g₂ : C) = 0 := by
  have h := congrArg (algebraMap E C) hF
  simpa only [reducedUnit_val, map_add, map_mul, reduction_epsilon] using h

/-- The reductions of the actual lifted transition units obey the
ordinary line-bundle cocycle law. -/
theorem transition_reduced_cocycle (f₁ f₂ g₁ g₂ : Eˣ) (a : C)
    (hF : (f₁ : E) * g₁ + (f₂ : E) * g₂ = epsilon e a) :
    reducedUnit (C := C) (transition01 g₁ g₂) * reducedUnit f₁ = reducedUnit f₂ := by
  apply Units.ext
  apply (reducedUnit (C := C) g₂).mul_left_inj.mp
  simp only [reducedUnit, transition01, Units.coe_map, Units.val_mul,
    Units.val_neg, map_mul]
  change (algebraMap E C (-(g₁ : E)) *
      algebraMap E C (↑(g₂⁻¹) : E) * algebraMap E C (f₁ : E)) *
      algebraMap E C (g₂ : E) =
    algebraMap E C (f₂ : E) * algebraMap E C (g₂ : E)
  rw [map_neg]
  have hi : algebraMap E C (↑(g₂⁻¹) : E) * algebraMap E C (g₂ : E) = 1 := by
    rw [← map_mul, g₂.inv_mul, map_one]
  have hz := reduced_factorization e f₁ f₂ g₁ g₂ a hF
  change algebraMap E C (f₁ : E) * algebraMap E C (g₁ : E) +
    algebraMap E C (f₂ : E) * algebraMap E C (g₂ : E) = 0 at hz
  calc
    _ = -(algebraMap E C (f₁ : E) * algebraMap E C (g₁ : E)) *
          (algebraMap E C (↑(g₂⁻¹) : E) * algebraMap E C (g₂ : E)) := by ring
    _ = -(algebraMap E C (f₁ : E) * algebraMap E C (g₁ : E)) := by rw [hi, mul_one]
    _ = algebraMap E C (f₂ : E) * algebraMap E C (g₂ : E) -
          (algebraMap E C (f₁ : E) * algebraMap E C (g₁ : E) +
            algebraMap E C (f₂ : E) * algebraMap E C (g₂ : E)) := by ring
    _ = _ := by rw [hz, sub_zero]

def cartierUnitDefect (f₁ f₂ g₁ g₂ : Eˣ) (a : C)
    (hF : (f₁ : E) * g₁ + (f₂ : E) * g₂ = epsilon e a) : C :=
  unitDefect e (transition01 g₁ g₂) f₁ f₂
    (transition_reduced_cocycle e f₁ f₂ g₁ g₂ a hF)

/-- The 013 expression of the product-minus-direct defect. -/
theorem cartierUnitDefect_second (f₁ f₂ g₁ g₂ : Eˣ) (a : C)
    (hF : (f₁ : E) * g₁ + (f₂ : E) * g₂ = epsilon e a) :
    cartierUnitDefect e f₁ f₂ g₁ g₂ a hF =
      -a * (↑((reducedUnit (C := C) g₂)⁻¹) : C) *
        (↑((reducedUnit (C := C) f₂)⁻¹) : C) := by
  apply epsilon_injective e
  rw [cartierUnitDefect, epsilon_unitDefect]
  change (-(g₁ : E) * ↑(g₂⁻¹) * (f₁ : E) * ↑(f₂⁻¹)) - 1 = _
  have hc : (f₂ : E) * (g₂ : E) * ↑(g₂⁻¹) * ↑(f₂⁻¹) = 1 := by
    rw [Units.mul_inv_cancel_right, f₂.mul_inv]
  calc
    _ = -((f₁ : E) * g₁ + (f₂ : E) * g₂) * ↑(g₂⁻¹) * ↑(f₂⁻¹) := by
      rw [show (1 : E) = (f₂ : E) * (g₂ : E) * ↑(g₂⁻¹) * ↑(f₂⁻¹) from hc.symm]
      ring
    _ = -(epsilon e a) * ↑(g₂⁻¹) * ↑(f₂⁻¹) := by rw [hF]
    _ = (↑(g₂⁻¹) * ↑(f₂⁻¹)) * epsilon e (-a) := by rw [map_neg]; ring
    _ = epsilon e (algebraMap E C (↑(g₂⁻¹) * ↑(f₂⁻¹)) * (-a)) :=
      mul_epsilon e _ _
    _ = _ := by
      congr 1
      change algebraMap E C (↑(g₂⁻¹) * ↑(f₂⁻¹)) * (-a) =
        -a * algebraMap E C (↑(g₂⁻¹)) * algebraMap E C (↑(f₂⁻¹))
      rw [map_mul]
      ring

/-- The same literal defect in its 012 expression.  The conversion
uses the actual reduced factorization, not an arbitrary rescaling. -/
theorem cartierUnitDefect_first (f₁ f₂ g₁ g₂ : Eˣ) (a : C)
    (hF : (f₁ : E) * g₁ + (f₂ : E) * g₂ = epsilon e a) :
    cartierUnitDefect e f₁ f₂ g₁ g₂ a hF =
      a * (↑((reducedUnit (C := C) g₁)⁻¹) : C) *
        (↑((reducedUnit (C := C) f₁)⁻¹) : C) := by
  let u : Cˣ := reducedUnit g₁ * reducedUnit f₁
  let v : Cˣ := reducedUnit g₂ * reducedUnit f₂
  have hsum : (u : C) + (v : C) = 0 := by
    have hz := reduced_factorization e f₁ f₂ g₁ g₂ a hF
    dsimp only [u, v, Units.val_mul]
    simpa only [mul_comm] using hz
  have huv : (u : C) = -(v : C) := by
    calc
      (u : C) = (u : C) + (v : C) - (v : C) := by ring
      _ = -(v : C) := by rw [hsum, zero_sub]
  have hi : (↑(u⁻¹) : C) = -(↑(v⁻¹) : C) := by
    apply Units.inv_eq_of_mul_eq_one_left
    rw [huv, neg_mul_neg, v.inv_mul]
  rw [cartierUnitDefect_second]
  have hleft : -a * (↑((reducedUnit (C := C) g₂)⁻¹) : C) *
      (↑((reducedUnit (C := C) f₂)⁻¹) : C) = -a * (↑(v⁻¹) : C) := by
    simp only [v, mul_inv_rev, Units.val_mul]
    ring
  have hright : a * (↑((reducedUnit (C := C) g₁)⁻¹) : C) *
      (↑((reducedUnit (C := C) f₁)⁻¹) : C) = a * (↑(u⁻¹) : C) := by
    simp only [u, mul_inv_rev, Units.val_mul]
    ring
  rw [hleft, hright, hi]
  ring

/-- With B=kL-A, both genuine transition-defect entries have the
opposite sign from the already named Cartier boundary entries. -/
theorem cartierUnitDefect_minus_boundary (f₁ f₂ g₁ g₂ : Eˣ) (B : C)
    (hF : (f₁ : E) * g₁ + (f₂ : E) * g₂ = epsilon e (-B)) :
    cartierUnitDefect e f₁ f₂ g₁ g₂ (-B) hF =
        -B * (↑((reducedUnit (C := C) g₁)⁻¹) : C) *
          (↑((reducedUnit (C := C) f₁)⁻¹) : C) ∧
      cartierUnitDefect e f₁ f₂ g₁ g₂ (-B) hF =
        B * (↑((reducedUnit (C := C) g₂)⁻¹) : C) *
          (↑((reducedUnit (C := C) f₂)⁻¹) : C) := by
  constructor
  · exact cartierUnitDefect_first e f₁ f₂ g₁ g₂ (-B) hF
  · simpa only [neg_neg] using cartierUnitDefect_second e f₁ f₂ g₁ g₂ (-B) hF

end CycleQ2GeometricCartierTransitionUnits

end
end SourceCartierTransitionUnits

section SourceCartierFrameGauge

/-! Actual frame changes for the inverse ideal and for the normalized
square-zero transition defect.  The inverse-ideal frame is a genuine
linear map on the ideal; no inverse of its Cartier generator is taken
in the surface ring.  The weight-two/weight-four formula is the one
needed for the dehomogenized equations and cofactors. -/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace CycleQ2GeometricCartierFrameGauge

open CycleQ2GeometricCartierNormalLift
open CycleQ2GeometricSquareZeroSplittings

section PrincipalIdeal

variable {S : Type*} [CommRing S]

theorem unitGenerator_regular (b : S) (hb : IsSMulRegular S b) (u : Sˣ) :
    IsSMulRegular S ((u : S) * b) := by
  intro x y h
  apply hb
  change b * x = b * y
  apply u.mul_right_inj.mp
  change ((u : S) * b) * x = ((u : S) * b) * y at h
  simpa only [mul_assoc] using h

theorem unitGenerator_span (I : Ideal S) (b : S)
    (hI : I = Ideal.span ({b} : Set S)) (u : Sˣ) :
    I = Ideal.span ({(u : S) * b} : Set S) := by
  rw [Ideal.span_singleton_mul_left_unit u.isUnit]
  exact hI

/-- A change of the actual regular generator acts contragrediently on
the genuine inverse-ideal functional. -/
theorem inverseIdealGenerator_unit (I : Ideal S) (b : S)
    (hb : IsSMulRegular S b) (hI : I = Ideal.span ({b} : Set S)) (u : Sˣ) :
    inverseIdealGenerator I ((u : S) * b)
        (unitGenerator_regular b hb u) (unitGenerator_span I b hI u) =
      (↑(u⁻¹) : S) • inverseIdealGenerator I b hb hI := by
  ext x
  apply unitGenerator_regular b hb u
  change ((u : S) * b) *
      inverseIdealGenerator I ((u : S) * b)
        (unitGenerator_regular b hb u) (unitGenerator_span I b hI u) x =
    ((u : S) * b) * ((↑(u⁻¹) : S) * inverseIdealGenerator I b hb hI x)
  calc
    _ = (x : S) := by
      rw [mul_comm, inverseIdealGenerator_mul]
    _ = ((u : S) * (↑(u⁻¹) : S)) *
        (inverseIdealGenerator I b hb hI x * b) := by
      rw [u.mul_inv, one_mul, inverseIdealGenerator_mul]
    _ = _ := by ring

/-- The cofactor-normalized functional keeps both homogeneous weights:
the Cartier equation has weight two and its cofactor has weight four. -/
theorem cofactorHom_weight_change (I : Ideal S) (b c : S)
    (hb : IsSMulRegular S b) (hI : I = Ideal.span ({b} : Set S)) (u : Sˣ) :
    cofactorHom I ((↑(u^2) : S) * b) ((↑(u^4) : S) * c)
        (unitGenerator_regular b hb (u^2))
        (unitGenerator_span I b hI (u^2)) =
      (↑(u^2) : S) • cofactorHom I b c hb hI := by
  apply LinearMap.ext
  intro x
  have hx := LinearMap.congr_fun (inverseIdealGenerator_unit I b hb hI (u^2)) x
  change inverseIdealGenerator I ((↑(u^2) : S) * b)
      (unitGenerator_regular b hb (u^2)) (unitGenerator_span I b hI (u^2)) x =
    (↑((u^2)⁻¹) : S) * inverseIdealGenerator I b hb hI x at hx
  change (-((↑(u^4) : S) * c)) *
      inverseIdealGenerator I ((↑(u^2) : S) * b)
        (unitGenerator_regular b hb (u^2)) (unitGenerator_span I b hI (u^2)) x =
    (↑(u^2) : S) * ((-c) * inverseIdealGenerator I b hb hI x)
  rw [hx]
  have hu : (↑(u^2) : S) * (↑((u^2)⁻¹) : S) = 1 := (u^2).mul_inv
  have hpow : (↑(u^4) : S) = (↑(u^2) : S)^2 := by
    simp only [Units.val_pow_eq_pow_val]
    ring
  rw [hpow]
  calc
    _ = ((↑(u^2) : S) * (↑((u^2)⁻¹) : S)) *
        ((↑(u^2) : S) * ((-c) * inverseIdealGenerator I b hb hI x)) := by ring
    _ = _ := by rw [hu, one_mul]

end PrincipalIdeal

section TransitionDefect

variable {E C : Type*} [CommRing E] [CommRing C] [Algebra E C]

/-- If local frames are multiplied by aᵢ, the transition from i to j
is multiplied by aⱼ/aᵢ. -/
def gauge (a b u : Eˣ) : Eˣ := b * u * a⁻¹

theorem gauge_comp (a b c u v : Eˣ) :
    gauge a b u * gauge b c v = gauge a c (u * v) := by
  calc
    _ = (b * b⁻¹) * (c * (u * v) * a⁻¹) := by
      dsimp only [gauge]
      ac_rfl
    _ = _ := by rw [mul_inv_cancel, one_mul]; rfl

theorem gauge_reduced (a b u : Eˣ) :
    reducedUnit (C := C) (gauge a b u) =
      gauge (reducedUnit a) (reducedUnit b) (reducedUnit u) := by
  simp only [gauge, reducedUnit_mul, reducedUnit_inv]

theorem gauge_cocycle (a b c u v w : Eˣ)
    (h : reducedUnit (C := C) u * reducedUnit v = reducedUnit w) :
    reducedUnit (C := C) (gauge a b u) * reducedUnit (gauge b c v) =
      reducedUnit (gauge a c w) := by
  rw [gauge_reduced, gauge_reduced, gauge_reduced]
  rw [gauge_comp, h]

theorem gauge_product (a b c u v w : Eˣ) :
    gauge a b u * gauge b c v * (gauge a c w)⁻¹ = u * v * w⁻¹ := by
  rw [gauge_comp]
  dsimp only [gauge]
  rw [mul_comm c (u * v), mul_comm c w]
  simp only [mul_inv_rev, inv_inv, mul_assoc,
    inv_mul_cancel_left, mul_inv_cancel_left]

/-- Frame normalization preserves the actual product-minus-direct
kernel coefficient exactly, including its sign and epsilon scale. -/
theorem unitDefect_gauge
    (e : C ≃ₗ[E] RingHom.ker (algebraMap E C))
    (a b c u v w : Eˣ)
    (h : reducedUnit (C := C) u * reducedUnit v = reducedUnit w) :
    unitDefect e (gauge a b u) (gauge b c v) (gauge a c w)
        (gauge_cocycle a b c u v w h) =
      unitDefect e u v w h := by
  apply epsilon_injective e
  rw [epsilon_unitDefect, epsilon_unitDefect, gauge_product]

end TransitionDefect

end CycleQ2GeometricCartierFrameGauge

end
end SourceCartierFrameGauge

section SourceSquareZeroDlogCocycle

/-! Universal logarithmic differentials and the actual splitting-
difference cup cocycle.  These are identities in genuine Kähler
differentials on a common intersection, with the fixed coefficient
map of the actual square-zero kernel. -/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace CycleQ2GeometricSquareZeroSplittings

section Dlog

variable {K C : Type*} [CommRing K] [CommRing C] [Algebra K C]

theorem logDifferential_one : logDifferential (K := K) (1 : Cˣ) = 0 := by
  simp [logDifferential]

theorem logDifferential_mul (u v : Cˣ) :
    logDifferential (K := K) (u * v) =
      logDifferential (K := K) u + logDifferential (K := K) v := by
  change (↑((u * v)⁻¹) : C) • KaehlerDifferential.D K C ((u : C) * (v : C)) = _
  rw [(KaehlerDifferential.D K C).leibniz, smul_add, smul_smul, smul_smul]
  have hu : (↑((u * v)⁻¹) : C) * (u : C) = (↑(v⁻¹) : C) := by
    simp [mul_inv_rev, mul_assoc, mul_left_comm, mul_comm]
  have hv : (↑((u * v)⁻¹) : C) * (v : C) = (↑(u⁻¹) : C) := by
    simp only [mul_inv_rev, Units.val_mul]
    calc
      _ = (↑(u⁻¹) : C) * ((↑(v⁻¹) : C) * (v : C)) := by ring
      _ = _ := by rw [v.inv_mul, mul_one]
  rw [hu, hv]
  exact add_comm _ _

theorem logDifferential_inv (u : Cˣ) :
    logDifferential (K := K) u⁻¹ = -logDifferential (K := K) u := by
  apply add_left_cancel (a := logDifferential (K := K) u)
  rw [← logDifferential_mul, mul_inv_cancel, logDifferential_one, add_neg_cancel]

/-- The actual multiplicative transition cocycle gives an additive
one-cocycle in the actual module of Kähler differentials. -/
theorem logDifferential_cocycle (u v w : Cˣ) (h : u * v = w) :
    logDifferential (K := K) v - logDifferential (K := K) w +
      logDifferential (K := K) u = 0 := by
  rw [← h, logDifferential_mul]
  abel

/-- Changing actual local line-bundle frames changes dlog by the
literal differential coboundary of the frame multipliers. -/
theorem logDifferential_gauge (a b u : Cˣ) :
    logDifferential (K := K) (CycleQ2GeometricCartierFrameGauge.gauge a b u) =
      logDifferential (K := K) u +
        (logDifferential (K := K) b - logDifferential (K := K) a) := by
  rw [CycleQ2GeometricCartierFrameGauge.gauge,
    logDifferential_mul, logDifferential_mul, logDifferential_inv]
  abel

end Dlog

section SplittingDifference

variable {K E C : Type*} [CommRing K] [CommRing E] [CommRing C]
variable [Algebra K E] [Algebra K C] [Algebra E C] [IsScalarTower K E C]
variable (e : C ≃ₗ[E] RingHom.ker (algebraMap E C))
variable (σ τ υ : C →ₐ[K] E)
variable (hσ : ∀ x, algebraMap E C (σ x) = x)
variable (hτ : ∀ x, algebraMap E C (τ x) = x)
variable (hυ : ∀ x, algebraMap E C (υ x) = x)

/-- Actual differences of splittings obey the Čech cocycle equation. -/
theorem difference_trans :
    difference e σ υ hσ hυ = difference e σ τ hσ hτ + difference e τ υ hτ hυ := by
  ext x
  apply epsilon_injective e
  change epsilon e (difference e σ υ hσ hυ x) =
    epsilon e (difference e σ τ hσ hτ x + difference e τ υ hτ hυ x)
  rw [map_add, epsilon_difference, epsilon_difference, epsilon_difference]
  ring

theorem contraction_difference_trans (ω : KaehlerDifferential K C) :
    (difference e σ υ hσ hυ).liftKaehlerDifferential ω =
      (difference e σ τ hσ hτ).liftKaehlerDifferential ω +
        (difference e τ υ hτ hυ).liftKaehlerDifferential ω := by
  rw [difference_trans e σ τ υ hσ hτ hυ]
  have h := (KaehlerDifferential.linearMapEquivDerivation K C).symm.map_add
    (difference e σ τ hσ hτ) (difference e τ υ hτ hυ)
  exact LinearMap.congr_fun h ω

/-- On a quadruple intersection, the cup expression from the actual
splitting differences and actual transition dlog is closed.  The two
identities used are precisely the splitting and unit cocycle laws. -/
theorem contraction_cocycle (u v w : Cˣ) (h : u * v = w) :
    (difference e τ υ hτ hυ).liftKaehlerDifferential (logDifferential (K := K) v) -
      (difference e σ υ hσ hυ).liftKaehlerDifferential (logDifferential (K := K) v) +
      (difference e σ τ hσ hτ).liftKaehlerDifferential (logDifferential (K := K) w) -
      (difference e σ τ hσ hτ).liftKaehlerDifferential (logDifferential (K := K) u) = 0 := by
  rw [contraction_difference_trans e σ τ υ hσ hτ hυ,
    ← h, logDifferential_mul, map_add]
  ring

end SplittingDifference

end CycleQ2GeometricSquareZeroSplittings

end
end SourceSquareZeroDlogCocycle
