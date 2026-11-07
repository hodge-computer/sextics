import SymmetricSmoothness
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Quasismoothness of the exact weighted fiber at lambda = 1

The integral weighted equation is `7 F_raw = 13 G`, in coordinates
`(a,b,c,d,u)` of weights `(1,1,1,1,2)`. Replace `u` by `z²` and append
`2 w⁶`. After multiplying the six ordinary partial derivatives by
`(3,1,3,1,4,1)`, their reductions modulo five are exactly `2 Xᵢ⁵`.
The existing symbolic Macaulay determinant theorem then applies.

Taking a square root in an algebraic closure transfers the result to the
five weighted coordinates. The endpoint proves the projective Jacobian
criterion directly; it makes no claim about contact correspondences or a
certificate for the original fourfold.
-/

noncomputable section

namespace WeightedFiberSmoothness

set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

open MvPolynomial SexticModFive
open scoped BigOperators

abbrev IntWeighted := MvPolynomial (Fin 5) ℤ
abbrev IntOrdinary := MvPolynomial (Fin 6) ℤ
abbrev ComplexWeighted := MvPolynomial (Fin 5) ℂ

def leftQuadric : IntWeighted := X 0 ^ 2 + C 2 * X 0 * X 1 - X 4
def rightQuadric : IntWeighted := X 2 ^ 2 + C 2 * X 2 * X 3 - X 4

/-- This is thirteen times the actual monic cubic `G` at lambda one. -/
def integerWeighted : IntWeighted :=
  C 7 * (C 2 * X 0 ^ 6 + X 1 ^ 6 + C 2 * X 2 ^ 6 + X 3 ^ 6 +
    C 30 * X 0 ^ 4 * X 4 + C 30 * X 2 ^ 4 * X 4 +
    C 30 * X 0 ^ 2 * X 4 ^ 2 + C 30 * X 2 ^ 2 * X 4 ^ 2 + C 4 * X 4 ^ 3) +
    C 5 * leftQuadric ^ 2 * rightQuadric +
    C 10 * leftQuadric * rightQuadric ^ 2

def squareCoordinates : Fin 5 → IntOrdinary :=
  ![X 0, X 1, X 2, X 3, X 4 ^ 2]

def squareLift : IntWeighted →+* IntOrdinary := eval₂Hom C squareCoordinates

@[simp] theorem squareLift_C (r : ℤ) : squareLift (C r) = C r :=
  eval₂Hom_C C squareCoordinates r

@[simp] theorem squareLift_X (i : Fin 5) : squareLift (X i) = squareCoordinates i :=
  eval₂Hom_X' C squareCoordinates i

def paddedSextic : IntOrdinary := squareLift integerWeighted + C 2 * X 5 ^ 6

def reflectionCoordinates : Fin 6 → IntOrdinary :=
  ![X 0 + X 4, X 0 - X 4, X 1, X 2 + X 4, X 2 - X 4, X 3]

theorem padded_eq_reflection :
    paddedSextic = eval₂ C reflectionCoordinates SymmetricSmoothness.integerSextic +
      C 2 * X 5 ^ 6 := by
  simp [paddedSextic, integerWeighted, leftQuadric, rightQuadric,
    squareCoordinates, reflectionCoordinates, SymmetricSmoothness.integerSextic,
    SymmetricSmoothness.qx, SymmetricSmoothness.qy, Fin.sum_univ_succ, map_ofNat]
  ring

theorem padded_homogeneous : paddedSextic.IsHomogeneous 6 := by
  rw [padded_eq_reflection]
  have hl : ∀ i, (reflectionCoordinates i).IsHomogeneous 1 := by
    intro i
    fin_cases i
    · exact (isHomogeneous_X ℤ 0).add (isHomogeneous_X ℤ 4)
    · exact (isHomogeneous_X ℤ 0).sub (isHomogeneous_X ℤ 4)
    · exact isHomogeneous_X ℤ 1
    · exact (isHomogeneous_X ℤ 2).add (isHomogeneous_X ℤ 4)
    · exact (isHomogeneous_X ℤ 2).sub (isHomogeneous_X ℤ 4)
    · exact isHomogeneous_X ℤ 3
  have h := SymmetricSmoothness.integerSextic_homogeneous.eval₂ C
    reflectionCoordinates (fun r => isHomogeneous_C _ r) hl
  have h' : (eval₂ C reflectionCoordinates SymmetricSmoothness.integerSextic).IsHomogeneous 6 :=
    by simpa using h
  exact h'.add (isHomogeneous_C_mul_X_pow 2 5 6)

def diagonal : Fin 6 → ZMod 5 := ![4,2,4,2,3,2]

theorem padded_mod_five :
    map (Int.castRingHom (ZMod 5)) paddedSextic =
      ∑ i : Fin 6, C (diagonal i) * X i ^ 6 := by
  norm_num [paddedSextic, integerWeighted, squareCoordinates,
    leftQuadric, rightQuadric, diagonal, Fin.sum_univ_succ, map_ofNat,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four]
  ring_nf
  have : CharP (MvPolynomial (Fin 6) (ZMod 5)) 5 := inferInstance
  reduce_mod_char!
  rfl

def gradientScale : Fin 6 → ℤ := ![3,1,3,1,4,1]

def scaledGradient (i : Fin 6) : IntOrdinary :=
  C (gradientScale i) * pderiv i paddedSextic

theorem scaledGradient_homogeneous (i : Fin 6) :
    (scaledGradient i).IsHomogeneous 5 := by
  apply IsHomogeneous.C_mul
  intro d hd
  have hc : coeff (d + Finsupp.single i 1) paddedSextic ≠ 0 := by
    intro hz
    simp [coeff_pderiv, hz] at hd
  have hdeg := padded_homogeneous hc
  simp only [map_add, Finsupp.weight_single, Pi.one_apply, smul_eq_mul, mul_one] at hdeg
  omega

theorem scaledGradient_mod_five (i : Fin 6) :
    map (Int.castRingHom (ZMod 5)) (scaledGradient i) = C 2 * X i ^ 5 := by
  rw [scaledGradient, map_mul, map_C, ← pderiv_map, padded_mod_five]
  have h6 : (6 : MvPolynomial (Fin 6) (ZMod 5)) = 1 := by
    have h := congrArg (C : ZMod 5 → MvPolynomial (Fin 6) (ZMod 5))
      (show (6 : ZMod 5) = 1 from by decide)
    simpa only [map_ofNat, map_one] using h
  have hpartial : pderiv i (∑ j : Fin 6, C (diagonal j) * X j ^ 6) =
      C (diagonal i) * X i ^ 5 := by
    simp [map_sum, pderiv_X, Pi.single_apply, mul_ite, h6]
  rw [hpartial, ← mul_assoc, ← map_mul]
  have hs : (Int.castRingHom (ZMod 5)) (gradientScale i) * diagonal i = 2 := by
    fin_cases i <;> decide
  rw [hs]

theorem padded_gradient_vanishes_only_at_origin
    {K : Type*} [Field K] [CharZero K] (x : Fin 6 → K)
    (hx : ∀ i, eval₂ (Int.castRingHom K) x (pderiv i paddedSextic) = 0) : x = 0 := by
  apply SexticModFive.common_zero_is_origin scaledGradient
    scaledGradient_homogeneous scaledGradient_mod_five x
  intro i
  simp [scaledGradient, hx i]

theorem padded_partials (i : Fin 6) :
    pderiv i paddedSextic =
      ![squareLift (pderiv 0 integerWeighted),
        squareLift (pderiv 1 integerWeighted),
        squareLift (pderiv 2 integerWeighted),
        squareLift (pderiv 3 integerWeighted),
        C 2 * X 4 * squareLift (pderiv 4 integerWeighted),
        C 12 * X 5 ^ 5] i := by
  fin_cases i <;>
    simp only [paddedSextic, integerWeighted, leftQuadric, rightQuadric,
      map_add, map_sub, pderiv_C, pderiv_mul, pderiv_pow,
      map_mul, map_pow, squareLift_C, squareLift_X, squareCoordinates,
      pderiv_X, Pi.single_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons] <;>
    norm_num [map_ofNat, Fin.ext_iff] <;> ring

theorem squareLift_eval {K : Type*} [CommRing K]
    (P : IntWeighted) (a b c d z : K) :
    eval₂ (Int.castRingHom K) ![a,b,c,d,z,0] (squareLift P) =
      eval₂ (Int.castRingHom K) ![a,b,c,d,z^2] P := by
  change eval₂ _ _ (eval₂ C squareCoordinates P) = _
  rw [← eval₂_assoc]
  congr 1
  funext i
  fin_cases i <;> simp [squareCoordinates]

theorem weighted_gradient_vanishes_only_at_origin_of_algClosed
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    (x : Fin 5 → K)
    (hx : ∀ i, eval₂ (Int.castRingHom K) x (pderiv i integerWeighted) = 0) : x = 0 := by
  obtain ⟨z,hz⟩ := IsAlgClosed.exists_pow_nat_eq (x 4) (n := 2) (by decide)
  let y : Fin 6 → K := ![x 0,x 1,x 2,x 3,z,0]
  have heval (P : IntWeighted) :
      eval₂ (Int.castRingHom K) y (squareLift P) = eval₂ (Int.castRingHom K) x P := by
    rw [squareLift_eval, hz]
    congr 1
    funext i
    fin_cases i <;> rfl
  have hy : y = 0 := by
    apply padded_gradient_vanishes_only_at_origin y
    intro i
    rw [padded_partials]
    fin_cases i <;> simp [heval, hx, y]
  funext i
  fin_cases i
  · exact congrFun hy 0
  · exact congrFun hy 1
  · exact congrFun hy 2
  · exact congrFun hy 3
  · have hz0 : z = 0 := congrFun hy 4
    change x 4 = 0
    rw [← hz, hz0, zero_pow (by decide)]

/-- The weighted Jacobian has no nonzero common zero over any
characteristic-zero field, by passing to an algebraic closure. -/
theorem integer_gradient_vanishes_only_at_origin
    {K : Type*} [Field K] [CharZero K] (x : Fin 5 → K)
    (hx : ∀ i, eval₂ (Int.castRingHom K) x (pderiv i integerWeighted) = 0) : x = 0 := by
  let φ : K →+* AlgebraicClosure K := algebraMap K (AlgebraicClosure K)
  have hmap : φ.comp (Int.castRingHom K) = Int.castRingHom (AlgebraicClosure K) :=
    Subsingleton.elim _ _
  have hzero : (fun i => φ (x i)) = 0 := by
    apply weighted_gradient_vanishes_only_at_origin_of_algClosed
    intro i
    have h := congrArg φ (hx i)
    rw [eval₂_comp_left, hmap, map_zero] at h
    exact h
  funext i
  apply φ.injective
  simpa using congrFun hzero i

/-- The same monic weighted polynomial used in the exact contact circuit. -/
def weightedG : ComplexWeighted :=
  C (1/13 : ℂ) * map (Int.castRingHom ℂ) integerWeighted

theorem exact_target_binding (a b c d z : ℂ) :
    eval ![a,b,c,d,z^2] weightedG =
      (7/13 : ℂ) * SymmetricReflections.transformedF a b c d z z := by
  rw [SymmetricReflections.transformedF_formula]
  simp [weightedG, integerWeighted, leftQuadric, rightQuadric]
  ring

/-- This is the quasismoothness Jacobian criterion for the exact lambda-one
weighted fiber, including points whose weight-two coordinate is nonzero. -/
theorem gradient_vanishes_only_at_origin (x : Fin 5 → ℂ)
    (hx : ∀ i, eval x (pderiv i weightedG) = 0) : x = 0 := by
  apply integer_gradient_vanishes_only_at_origin x
  intro i
  have h := hx i
  simp only [weightedG, pderiv_C_mul, pderiv_map, eval_mul, eval_C, eval_map] at h
  exact (mul_eq_zero.mp h).resolve_left (by norm_num)

theorem nonzero_point_has_nonzero_partial (x : Fin 5 → ℂ) (hx : x ≠ 0) :
    ∃ i, eval x (pderiv i weightedG) ≠ 0 := by
  by_contra h
  push Not at h
  exact hx (gradient_vanishes_only_at_origin x h)

theorem weighted_vertex_value (u : ℂ) : eval ![0,0,0,0,u] weightedG = u^3 := by
  norm_num [weightedG, integerWeighted, leftQuadric, rightQuadric, eval_map,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four]
  ring

#print axioms padded_gradient_vanishes_only_at_origin
#print axioms integer_gradient_vanishes_only_at_origin
#print axioms exact_target_binding
#print axioms gradient_vanishes_only_at_origin
#print axioms nonzero_point_has_nonzero_partial
#print axioms weighted_vertex_value

end WeightedFiberSmoothness
