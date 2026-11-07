import HodgeComputer.Constructions.HoldoutCover.Piola
import Mathlib.Tactic.LinearCombination

/-!
# Balancing a coefficient vector field by one scalar derivative

Suppose `w₀` matches a source `p`, while `c` rescales the equation by `a`.
If `div(c)=(r+1)*a` and `c(ell)=a*ell`, the correction
`w=w₀+(s/ell^r)*c` matches modulo the equation and has the required
divergence exactly when `c(s)=-ell^r*div(w₀)`.

This is a reversible reduction within the displayed class of corrections.
It does not assert the existence of a scalar primitive or the spanning
of arbitrary coefficient fields. The coordinate set, field, equation,
source, exponent and derivations are arbitrary.
-/

noncomputable section

namespace CoefficientBalance

open HoldoutConstruction
open scoped BigOperators

variable {K ι : Type*} [Field K] [Fintype ι]

def action (D : ι → Derivation ℤ K K) (v : ι → K) : Derivation ℤ K K :=
  ∑ i, v i • D i

theorem action_apply (D : ι → Derivation ℤ K K) (v : ι → K) (f : K) :
    action D v f = ∑ i, v i * D i f := by
  change Derivation.coeFnAddMonoidHom (∑ i, v i • D i) f = _
  rw [map_sum]
  simp only [Finset.sum_apply, Derivation.coeFnAddMonoidHom_apply,
    Derivation.smul_apply, smul_eq_mul]

theorem action_add_scaled (D : ι → Derivation ℤ K K)
    (w c : ι → K) (t f : K) :
    action D (fun i => w i+t*c i) f = action D w f+t*action D c f := by
  simp only [action_apply, add_mul, Finset.sum_add_distrib, mul_assoc,
    Finset.mul_sum]

theorem divergence_add_scaled (D : ι → Derivation ℤ K K)
    (w c : ι → K) (t : K) :
    fieldDivergence D (fun i => w i+t*c i) =
      fieldDivergence D w+action D c t+t*fieldDivergence D c := by
  simp only [fieldDivergence, map_add, Derivation.leibniz, smul_eq_mul,
    Finset.sum_add_distrib, action_apply, Finset.mul_sum]
  ring

section Quotients

variable {R : Type*} [CommRing R]

/-- Coefficient matching can be checked after taking one common denominator
in any differential domain embedded in a field. -/
theorem quotient_action
    (D : ι → Derivation ℤ R R) (E : ι → Derivation ℤ K K)
    (φ : R →+* K) (compatible : ∀ i p, E i (φ p) = φ (D i p))
    (d f : R) (z : ι → R) :
    action E (fun i => φ (z i)/φ d) (φ f) =
      φ (∑ i, z i*D i f)/φ d := by
  simp only [action_apply, compatible, map_sum, map_mul, div_eq_mul_inv,
    Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem quotient_divergence
    (D : ι → Derivation ℤ R R) (E : ι → Derivation ℤ K K)
    (φ : R →+* K) (compatible : ∀ i p, E i (φ p) = φ (D i p))
    (d : R) (z : ι → R) :
    fieldDivergence E (fun i => φ (z i)/φ d) =
      φ (d*(∑ i, D i (z i))-(∑ i, z i*D i d))/(φ d)^2 := by
  simp only [fieldDivergence, Derivation.leibniz_div, compatible, smul_eq_mul]
  rw [← Finset.mul_sum]
  have hs : (∑ i, (φ d*φ (D i (z i))-φ (z i)*φ (D i d))) =
      φ (d*(∑ i, D i (z i))-(∑ i, z i*D i d)) := by
    simp only [map_sub, map_mul, map_sum, Finset.mul_sum,
      Finset.sum_sub_distrib]
  rw [hs]
  simp only [div_eq_mul_inv, inv_pow, mul_comm]

/-- Clear the matching and divergence equations together. The denominator
is arbitrary; in particular, it can contain additional invariant divisors. -/
theorem clear_balance
    (D : ι → Derivation ℤ R R) (E : ι → Derivation ℤ K K)
    (φ : R →+* K) (hinj : Function.Injective φ)
    (compatible : ∀ i p, E i (φ p) = φ (D i p))
    (d h f p : R) (z : ι → R) (hd : φ d ≠ 0)
    (hmatch : action E (fun i => φ (z i)/φ d) (φ f) =
      φ p+(φ h/φ d)*φ f)
    (hdiv : fieldDivergence E (fun i => φ (z i)/φ d) = φ h/φ d) :
    (∑ i, z i*D i f) = d*p+h*f ∧
      d*(∑ i, D i (z i))-(∑ i, z i*D i d) = d*h := by
  rw [quotient_action D E φ compatible] at hmatch
  rw [quotient_divergence D E φ compatible] at hdiv
  constructor
  · apply hinj
    simp only [map_add, map_mul]
    field_simp at hmatch
    linear_combination hmatch
  · apply hinj
    simp only [map_mul]
    field_simp at hdiv
    linear_combination hdiv

end Quotients

/-- Multiplication by `ell^r` converts the scalar balance operator into an
ordinary derivative. The exponent is arbitrary and may be zero. -/
theorem integrating_factor (T : Derivation ℤ K K) (ell a t : K) (r : ℕ)
    (hell : T ell = a*ell) :
    T (ell^r*t) = ell^r*(T t+(r:K)*a*t) := by
  cases r with
  | zero => simp
  | succ r =>
    simp only [Derivation.leibniz, Derivation.leibniz_pow, hell,
      smul_eq_mul, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
    ring

/-- The inverse integrating factor keeps the differential equation exact. -/
theorem inverse_integrating_factor (T : Derivation ℤ K K) (ell a s : K) (r : ℕ)
    (h0 : ell ≠ 0) (hell : T ell = a*ell) :
    T (s/ell^r)+(r:K)*a*(s/ell^r) = T s/ell^r := by
  have h := integrating_factor T ell a (s/ell^r) r hell
  have hs : ell^r*(s/ell^r)=s := by field_simp
  rw [hs] at h
  apply (eq_div_iff (pow_ne_zero r h0)).mpr
  simpa only [mul_comm] using h.symm

def correctedField (w c : ι → K) (ell s : K) (r : ℕ) : ι → K :=
  fun i => w i+(s/ell^r)*c i

/-- Matching modulo the equation follows from the displayed tangent
direction, without any scalar integration hypothesis. -/
theorem corrected_matching (D : ι → Derivation ℤ K K)
    (w c : ι → K) (f p a ell s : K) (r : ℕ)
    (hw : action D w f = p) (hc : action D c f = a*f) :
    action D (correctedField w c ell s r) f = p+(a*s/ell^r)*f := by
  change action D (fun i => w i+(s/ell^r)*c i) f = _
  rw [action_add_scaled, hw, hc]
  ring

/-- The whole divergence defect is one derivative in the coefficient-fiber
direction; no restriction on the poles of `s` is imposed. -/
theorem corrected_divergence (D : ι → Derivation ℤ K K)
    (w c : ι → K) (ell a s : K) (r : ℕ)
    (h0 : ell ≠ 0) (hell : action D c ell = a*ell)
    (hdiv : fieldDivergence D c = ((r+1:ℕ):K)*a) :
    fieldDivergence D (correctedField w c ell s r)-a*s/ell^r =
      fieldDivergence D w+action D c s/ell^r := by
  change fieldDivergence D (fun i => w i+(s/ell^r)*c i)-a*s/ell^r = _
  rw [divergence_add_scaled, hdiv]
  have h := inverse_integrating_factor (action D c) ell a s r h0 hell
  push_cast
  linear_combination h

/-- A complete exactness test for the scalar equation is a complete test
for divergence balance in this explicitly parameterized class. -/
theorem balanced_iff (D : ι → Derivation ℤ K K)
    (w c : ι → K) (ell a s : K) (r : ℕ)
    (h0 : ell ≠ 0) (hell : action D c ell = a*ell)
    (hdiv : fieldDivergence D c = ((r+1:ℕ):K)*a) :
    fieldDivergence D (correctedField w c ell s r) = a*s/ell^r ↔
      action D c s = -(ell^r)*fieldDivergence D w := by
  have h := corrected_divergence D w c ell a s r h0 hell hdiv
  constructor
  · intro hb
    rw [hb, sub_self] at h
    have h' : action D c s/ell^r = -fieldDivergence D w := by
      linear_combination -h
    have he := (div_eq_iff (pow_ne_zero r h0)).mp h'
    linear_combination he
  · intro hs
    rw [hs] at h
    have hz : -(ell^r)*fieldDivergence D w/ell^r = -fieldDivergence D w := by
      field_simp
    rw [hz] at h
    linear_combination h

/-- Rescaling a nonzero coordinate derivative makes its coordinate have
derivative one and retains all first integrals. -/
theorem rescaled_coordinate (T : Derivation ℤ K K) (lambda h : K)
    (h0 : h ≠ 0) (hlambda : T lambda = h) :
    (h⁻¹ • T) lambda = 1 := by
  simp [Derivation.smul_apply, smul_eq_mul, hlambda, h0]

theorem rescaled_constant (T : Derivation ℤ K K) (h a : K) (ha : T a = 0) :
    (h⁻¹ • T) a = 0 := by
  simp [Derivation.smul_apply, smul_eq_mul, ha]

#print axioms integrating_factor
#print axioms corrected_matching
#print axioms balanced_iff
#print axioms clear_balance

end CoefficientBalance
