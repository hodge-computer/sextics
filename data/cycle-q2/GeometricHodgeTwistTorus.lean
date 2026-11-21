import Proposal.GeometricSurfaceCoordinates
import Mathlib.Algebra.MonoidAlgebra.Lift

/-!
# Evaluation of localized chart coefficients on the common torus

The three normalized weight-one coordinates are units on the common torus.
The Laurent expansion of a localized chart coefficient can therefore be
evaluated there. The resulting ring homomorphism agrees with every chart
restriction carrying the original coordinates and constants to these values.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CycleQ2HodgeTwistTorus

open MvPolynomial CycleQ2SeedCechThreeOpen CycleQ2SeedCechLocalization
open CycleQ2SeedQuotientFiniteFree (Base)

variable {R Tgt : Type*} [CommRing R] [CommRing Tgt] (ρ : R →+* Tgt) (u : Fin 3 → Tgtˣ)

def powers : Multiplicative LaurentExponent →* Tgt where
  toFun e := ((∏ q, u q ^ e.toAdd q : Tgtˣ) : Tgt)
  map_one' := by simp
  map_mul' x y := by
    change ((∏ q, u q ^ (x.toAdd q + y.toAdd q) : Tgtˣ) : Tgt) = _
    simp only [zpow_add, Finset.prod_mul_distrib, Units.val_mul]

def evaluate : Laurent (R := R) →+* Tgt :=
  AddMonoidAlgebra.liftNCRingHom ρ (powers u) (fun _ _ => Commute.all _ _)

theorem evaluate_single (e : LaurentExponent) (c : R) :
    evaluate ρ u (AddMonoidAlgebra.single e c) = ρ c * ((∏ q, u q ^ e q : Tgtˣ) : Tgt) := by
  exact AddMonoidAlgebra.liftNCRingHom_single ..

theorem evaluate_sum (p : Laurent (R := R)) :
    evaluate ρ u p = p.coeff.sum (fun e c => ρ c * ((∏ q, u q ^ e q : Tgtˣ) : Tgt)) := by
  conv_lhs => rw [← AddMonoidAlgebra.sum_coeff_single p]
  rw [map_finsuppSum]
  simp only [evaluate_single]

theorem evaluate_C (c : R) : evaluate ρ u (baseToLaurent R (C c)) = ρ c := by
  change evaluate ρ u (baseToLaurent R (monomial 0 c)) = _
  rw [baseToLaurent_monomial, evaluate_single]
  simp

theorem evaluate_X (q : Fin 3) : evaluate ρ u (baseToLaurent R (X q)) = (u q).val := by
  rw [baseToLaurent_X]
  change evaluate ρ u (AddMonoidAlgebra.single (openExponent {q}) 1) = _
  rw [evaluate_single]
  classical
  simp [openExponent, Finset.prod_ite_eq']

/-- A chart-to-torus map is determined by the three original coordinates and the scalars. -/
theorem evaluate_restriction (B : Finset (Fin 3)) (g : coordinateLocalization R B →+* Tgt)
    (hc : ∀ c : R, g (algebraMap (Base R) (coordinateLocalization R B) (C c)) = ρ c)
    (hx : ∀ q : Fin 3, g (algebraMap (Base R) (coordinateLocalization R B) (X q)) = (u q).val)
    (p : coordinateLocalization R B) :
    evaluate ρ u (localizationToLaurent R B p) = g p := by
  have he : (evaluate ρ u).comp (localizationToLaurent R B) = g := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (baseProduct R B))
    apply MvPolynomial.ringHom_ext
    · intro c
      change evaluate ρ u (localizationToLaurent R B (algebraMap _ _ (C c))) = _
      rw [localizationToLaurent_algebraMap, evaluate_C]
      exact (hc c).symm
    · intro q
      change evaluate ρ u (localizationToLaurent R B (algebraMap _ _ (X q))) = _
      rw [localizationToLaurent_algebraMap, evaluate_X]
      exact (hx q).symm
  exact RingHom.congr_fun he p

end CycleQ2HodgeTwistTorus
end

#print axioms CycleQ2HodgeTwistTorus.evaluate_restriction
