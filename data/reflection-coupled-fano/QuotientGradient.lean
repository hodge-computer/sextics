import Proposal.CoupledDomain
import Proposal.QuarticIncidence

/-! The coordinate gradient used by the quartic incidence is exactly the
formal multivariate gradient of the fixed reflection quotient equation. -/

noncomputable section
namespace ReflectionCoupledFano

variable {R S : Type*} [CommRing R] [CommRing S]

theorem hypersurface_eval (f : R →+* S) (c : R) (x : Fin 6 → S) :
    MvPolynomial.eval₂Hom f x (hypersurface c 3 1) = H (f c) x := by
  simp [hypersurface, H, map_ofNat]

theorem hypersurface_pderiv (c : R) (i : Fin 6) :
    MvPolynomial.pderiv i (hypersurface c 3 1) =
      gradient (MvPolynomial.C c) MvPolynomial.X i := by
  have h2 (j : Fin 6) : MvPolynomial.pderiv j (2 : MvPolynomial (Fin 6) R) = 0 :=
    Derivation.map_natCast _ 2
  have h3 (j : Fin 6) : MvPolynomial.pderiv j (3 : MvPolynomial (Fin 6) R) = 0 :=
    Derivation.map_natCast _ 3
  fin_cases i <;>
    norm_num [hypersurface, gradient, MvPolynomial.pderiv_pow,
      MvPolynomial.pderiv_mul, h2, h3, Pi.single_apply, Fin.ext_iff,
      Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one,
      show (2 : Fin 6) ≠ 0 by decide, show (3 : Fin 6) ≠ 0 by decide,
      show (4 : Fin 6) ≠ 0 by decide, show (5 : Fin 6) ≠ 0 by decide,
      show (2 : Fin 6) ≠ 1 by decide, show (3 : Fin 6) ≠ 1 by decide,
      show (4 : Fin 6) ≠ 1 by decide, show (5 : Fin 6) ≠ 1 by decide,
      show (3 : Fin 6) ≠ 2 by decide, show (4 : Fin 6) ≠ 2 by decide,
      show (5 : Fin 6) ≠ 2 by decide, show (4 : Fin 6) ≠ 3 by decide,
      show (5 : Fin 6) ≠ 3 by decide, show (5 : Fin 6) ≠ 4 by decide] <;> ring

theorem hypersurface_pderiv_eval (f : R →+* S) (c : R) (x : Fin 6 → S) (i : Fin 6) :
    MvPolynomial.eval₂Hom f x (MvPolynomial.pderiv i (hypersurface c 3 1)) =
      gradient (f c) x i := by
  rw [hypersurface_pderiv, gradient_map]
  simp

end ReflectionCoupledFano

#print axioms ReflectionCoupledFano.hypersurface_pderiv_eval
