import Proposal.CubicMatrixCertificate

noncomputable section
namespace QuadricContact.CubicMatrixCertificate
open MvPolynomial
variable {K E n R : Type*} [CommRing K] [IsDomain K] [CommRing E] [Algebra K E]
variable [Fintype n] [DecidableEq n] [CommRing R]

/-- Every specialization of the determinant denominator is the determinant of
its specialized linear pencil. -/
theorem denominator_eval₂ (ρ : E →ₐ[K] Matrix n n K) (x y : E)
    (g : K →+* R) (v : Fin 4 → R) :
    MvPolynomial.eval₂Hom g v (denominator ρ x y) =
      (v 0 • (1 : Matrix n n R) - v 2 • (ρ x).map g - v 3 • (ρ y).map g).det := by
  unfold denominator
  rw [RingHom.map_det]
  congr 1
  ext a b
  simp [matrixPole, ConcreteLine.pole, polynomialMatrixMap_X, polynomialMatrixMap_C,
    Matrix.map_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.mul_smul,
    Matrix.mul_one, smul_eq_mul, map_ofNat]
  by_cases hab : a = b <;>
    simp [← coe_eval₂Hom, Matrix.one_apply, hab]

/-- The fiber S=2t², B=C=1 turns the pole into the norm pencil for x+y. -/
theorem denominator_norm_fiber (ρ : E →ₐ[K] Matrix n n K) (x y : E)
    (g : K →+* R) :
    MvPolynomial.eval₂Hom (Polynomial.C.comp g)
      ![(2 : Polynomial R) * Polynomial.X ^ 2, 0, 1, 1] (denominator ρ x y) =
      (((2 : Polynomial R) * Polynomial.X ^ 2) • (1 : Matrix n n (Polynomial R)) -
        ((ρ (x+y)).map g).map (Polynomial.C : R →+* Polynomial R)).det := by
  rw [denominator_eval₂]
  congr 1
  ext a b : 2
  simp [Matrix.sub_apply, Matrix.smul_apply, Matrix.add_apply, Matrix.map_apply,
    RingHom.comp_apply, map_add, sub_sub]

end QuadricContact.CubicMatrixCertificate
#print axioms QuadricContact.CubicMatrixCertificate.denominator_norm_fiber
