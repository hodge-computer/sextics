import Mod5Smoothness
import SymmetricReflections

/-!
The exact protected sextic has no nonzero common zero of its first partial
derivatives over C. This is its projective Jacobian nonsingularity condition.
The proof lifts the Fermat reduction modulo 5 through Mod5Smoothness.
-/

noncomputable section
namespace SymmetricSmoothness
open MvPolynomial SexticModFive
open scoped BigOperators

abbrev IntPoly := MvPolynomial Vars ℤ

def qx : IntPoly := X 0 * X 1 + X 0 * X 2 + X 1 * X 2
def qy : IntPoly := X 3 * X 4 + X 3 * X 5 + X 4 * X 5

def integerSextic : IntPoly :=
  C 7 * (∑ i : Vars, X i ^ 6) + C 5 * (qx^2 * qy) + C 10 * (qx * qy^2)

theorem qx_homogeneous : qx.IsHomogeneous 2 := by
  exact (((isHomogeneous_X ℤ 0).mul (isHomogeneous_X ℤ 1)).add
    ((isHomogeneous_X ℤ 0).mul (isHomogeneous_X ℤ 2))).add
    ((isHomogeneous_X ℤ 1).mul (isHomogeneous_X ℤ 2))

theorem qy_homogeneous : qy.IsHomogeneous 2 := by
  exact (((isHomogeneous_X ℤ 3).mul (isHomogeneous_X ℤ 4)).add
    ((isHomogeneous_X ℤ 3).mul (isHomogeneous_X ℤ 5))).add
    ((isHomogeneous_X ℤ 4).mul (isHomogeneous_X ℤ 5))

theorem integerSextic_homogeneous : integerSextic.IsHomogeneous 6 := by
  have hsum : (∑ i : Vars, (X i : IntPoly)^6).IsHomogeneous 6 :=
    IsHomogeneous.sum _ _ _ (fun i _ => isHomogeneous_X_pow i 6)
  exact ((hsum.C_mul 7).add (((qx_homogeneous.pow 2).mul qy_homogeneous).C_mul 5)).add
    ((qx_homogeneous.mul (qy_homogeneous.pow 2)).C_mul 10)

theorem derivative_homogeneous (i : Vars) :
    (pderiv i integerSextic).IsHomogeneous 5 := by
  intro d hd
  have hcoeff : coeff (d + Finsupp.single i 1) integerSextic ≠ 0 := by
    intro hz
    simp [coeff_pderiv, hz] at hd
  have hdeg := integerSextic_homogeneous hcoeff
  simp only [map_add, Finsupp.weight_single, Pi.one_apply, smul_eq_mul, mul_one] at hdeg
  omega

theorem integerSextic_mod_five :
    map (Int.castRingHom (ZMod 5)) integerSextic =
      C 2 * ∑ i : Vars, X i ^ 6 := by
  have h7 : (Int.castRingHom (ZMod 5)) 7 = 2 := by decide
  have h5 : (Int.castRingHom (ZMod 5)) 5 = 0 := by decide
  have h10 : (Int.castRingHom (ZMod 5)) 10 = 0 := by decide
  simp only [integerSextic, map_add, map_mul, map_C, map_sum, map_pow, map_X,
    h7, h5, h10, C_0, zero_mul, add_zero]

theorem derivative_mod_five (i : Vars) :
    map (Int.castRingHom (ZMod 5)) (pderiv i integerSextic) =
      C 2 * X i ^ 5 := by
  rw [← pderiv_map, integerSextic_mod_five, pderiv_C_mul]
  have h6 : (6 : MvPolynomial Vars (ZMod 5)) = 1 := by
    have h := congrArg (C : ZMod 5 → MvPolynomial Vars (ZMod 5))
      (show (6 : ZMod 5) = 1 from by decide)
    simpa only [map_ofNat, map_one] using h
  simp [map_sum, pderiv_X, Pi.single_apply, mul_ite, h6]

theorem integerSextic_complex_binding :
    map (Int.castRingHom ℂ) integerSextic = C (7 : ℂ) * HodgeSubmission.F := by
  rw [SymmetricReflections.exactF_compact]
  have hseven : (C (7 : ℂ) : MvPolynomial Vars ℂ) * C (1/7 : ℂ) = 1 := by
    rw [← map_mul]
    norm_num
  rw [SymmetricReflections.compactF, mul_add, ← mul_assoc (C (7 : ℂ)) (C (1/7 : ℂ)),
    hseven, one_mul]
  rw [show (C (7 : ℂ) : MvPolynomial Vars ℂ) = 7 from map_natCast C 7]
  simp [integerSextic, qx, qy, SymmetricReflections.QX, SymmetricReflections.QY,
    Fin.sum_univ_succ]
  ring

theorem gradient_vanishes_only_at_origin
    (x : Fin 6 → ℂ) (hx : ∀ i, eval x (pderiv i HodgeSubmission.F) = 0) : x = 0 := by
  apply common_zero_is_origin (fun i => pderiv i integerSextic)
    derivative_homogeneous derivative_mod_five x
  intro i
  have hg : map (Int.castRingHom ℂ) (pderiv i integerSextic) =
      C (7 : ℂ) * pderiv i HodgeSubmission.F := by
    rw [← pderiv_map, integerSextic_complex_binding]
    simp
  have he := congrArg (eval x) hg
  simpa [eval_map, hx i] using he

theorem nonzero_point_has_nonzero_partial (x : Fin 6 → ℂ) (hx : x ≠ 0) :
    ∃ i, eval x (pderiv i HodgeSubmission.F) ≠ 0 := by
  by_contra h
  push Not at h
  exact hx (gradient_vanishes_only_at_origin x h)

theorem target_homogeneous : HodgeSubmission.F.IsHomogeneous 6 := by
  have h := (integerSextic_homogeneous.map (Int.castRingHom ℂ)).C_mul (1/7 : ℂ)
  rw [integerSextic_complex_binding, ← mul_assoc, ← map_mul] at h
  norm_num at h
  exact h

theorem target_ne_zero : HodgeSubmission.F ≠ 0 := by
  intro hf
  have h := gradient_vanishes_only_at_origin (fun _ => 1) (by simp [hf])
  have hi := congrFun h 0
  norm_num at hi

theorem target_totalDegree : HodgeSubmission.F.totalDegree = 6 :=
  target_homogeneous.totalDegree target_ne_zero

theorem source_homogeneous : HodgeSubmission.A.IsHomogeneous 6 := by
  rw [SymmetricReflections.exactA_compact]
  exact (((((isHomogeneous_X ℂ 0).mul (isHomogeneous_X ℂ 1)).mul
    (isHomogeneous_X ℂ 2)).mul (isHomogeneous_X ℂ 3)).mul
    (isHomogeneous_X ℂ 4)).mul (isHomogeneous_X ℂ 5)

#print axioms gradient_vanishes_only_at_origin
#print axioms nonzero_point_has_nonzero_partial
#print axioms target_homogeneous
#print axioms target_ne_zero
#print axioms target_totalDegree
#print axioms source_homogeneous
end SymmetricSmoothness
