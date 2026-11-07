import WeightedPolynomialModel
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Tactic.Ring

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace WeightedSupport.PolynomialModel
open MvPolynomial

theorem swapIndex_involutive : Function.Involutive swapIndex := by
  change ∀ i : Fin 6, swapIndex (swapIndex i) = i
  decide +kernel

theorem swapIndex_injective : Function.Injective swapIndex := swapIndex_involutive.injective

theorem sigma_involutive (e : Exponent) : sigma (sigma e) = e := by
  funext i
  change e (swapIndex (swapIndex i)) = e i
  rw [swapIndex_involutive i]

theorem exponent_mapDomain (e : Exponent) :
    (exponent e).mapDomain swapIndex = exponent (sigma e) := by
  ext j
  have h := Finsupp.mapDomain_apply swapIndex_injective (exponent e) (swapIndex j)
  simpa only [swapIndex_involutive j, exponent_apply, sigma] using h

theorem rename_L : rename swapIndex L = L := by
  simp [L_explicit, swapIndex]
  ring

theorem rename_D : rename swapIndex D = -D := by
  simp [D, swapIndex]
  ring

theorem rename_H : rename swapIndex H = H := by
  simp [H, swapIndex]
  ring

theorem rename_Q : rename swapIndex Q = -Q := by
  simp only [Q, map_add, map_mul, map_pow, rename_D, rename_L, rename_C, rename_X,
    show swapIndex 5 = 5 from rfl]
  ring

theorem rename_HQ : rename swapIndex (H * Q) = -(H * Q) := by
  rw [map_mul, rename_H, rename_Q, mul_neg]

theorem rename_orbitPolynomial (a : Exponent) :
    rename swapIndex (orbitPolynomial a) = orbitPolynomial a := by
  classical
  by_cases h : a = sigma a
  · rw [orbitPolynomial, if_pos h, add_zero, rename_monomial, exponent_mapDomain]
    exact congrArg (fun e => monomial (exponent e) (1 : ℤ)) h.symm
  · rw [orbitPolynomial, if_neg h, map_add, rename_monomial, rename_monomial,
      exponent_mapDomain, exponent_mapDomain, sigma_involutive, add_comm]

theorem Q_times_orbit_anti (a : Exponent) :
    rename swapIndex (Q * orbitPolynomial a) = -(Q * orbitPolynomial a) := by
  rw [map_mul, rename_Q, rename_orbitPolynomial, neg_mul]

theorem HQ_times_orbit_anti (a : Exponent) :
    rename swapIndex ((H * Q) * orbitPolynomial a) = -((H * Q) * orbitPolynomial a) := by
  rw [map_mul, rename_HQ, rename_orbitPolynomial, neg_mul]

theorem coeff_anti (p : Poly) (hp : rename swapIndex p = -p) (e : Exponent) :
    coeff (exponent (sigma e)) p = -coeff (exponent e) p := by
  have h := coeff_rename_mapDomain swapIndex swapIndex_injective p (exponent e)
  rw [exponent_mapDomain, hp, coeff_neg] at h
  exact neg_eq_iff_eq_neg.mp h

#print axioms Q_times_orbit_anti
#print axioms HQ_times_orbit_anti

end WeightedSupport.PolynomialModel
