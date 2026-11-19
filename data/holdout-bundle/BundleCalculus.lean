import Proposal.BundleConic

/-! Polynomial evaluation and all five derivatives of the relative quotient.
The sixth, parameter, direction is restored by the physical transport. -/

noncomputable section

namespace HoldoutBundle
variable {R S : Type*} [CommRing R] [CommRing S]

theorem kPoly_eval (f : R →+* S) (a b : R) (x : Fin 5 → S) :
    MvPolynomial.eval₂Hom f x (kPoly a b) = K (f a) (f b) x := by
  simp [kPoly, K]

theorem kPoly_pderiv (a b : R) (j : Fin 5) :
    MvPolynomial.pderiv j (kPoly a b) =
      gradient (MvPolynomial.C a) (MvPolynomial.C b) MvPolynomial.X j := by
  fin_cases j <;>
    simp [kPoly, K, gradient, MvPolynomial.pderiv_pow, MvPolynomial.pderiv_mul,
      smul_eq_mul] <;> ring

theorem kPoly_pderiv_eval (f : R →+* S) (a b : R) (x : Fin 5 → S) (j : Fin 5) :
    MvPolynomial.eval₂Hom f x (MvPolynomial.pderiv j (kPoly a b)) =
      gradient (f a) (f b) x j := by
  rw [kPoly_pderiv]
  fin_cases j <;> simp [gradient, map_ofNat]

end HoldoutBundle

#print axioms HoldoutBundle.kPoly_pderiv
