import Proposal.SymmetricNegativeJacobian
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

/-! The actual twelve Jacobian polynomials have weighted degree six and odd
`(c,d)` parity. Both properties are proved simultaneously in the grading
monoid `ℕ × ZMod 2`. -/

noncomputable section

namespace SymmetricNegativeJacobian

open MvPolynomial
open scoped BigOperators

set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

def bidegreeWeight : Fin 5 → ℕ × ZMod 2 :=
  ![(1,0),(1,0),(1,1),(1,1),(2,0)]

@[simp] theorem bidegreeWeight_zero : bidegreeWeight 0 = (1,0) := rfl
@[simp] theorem bidegreeWeight_one : bidegreeWeight 1 = (1,0) := rfl
@[simp] theorem bidegreeWeight_two : bidegreeWeight 2 = (1,1) := rfl
@[simp] theorem bidegreeWeight_three : bidegreeWeight 3 = (1,1) := rfl
@[simp] theorem bidegreeWeight_four : bidegreeWeight 4 = (2,0) := rfl

theorem weightedG_bihomogeneous :
    WeightedFiberSmoothness.weightedG.IsWeightedHomogeneous bidegreeWeight (6,0) := by
  have hX (i : Fin 5) : (X i : Poly).IsWeightedHomogeneous bidegreeWeight
      (bidegreeWeight i) := isWeightedHomogeneous_X ℂ _ _
  have ha2 : (X 0 ^ 2 : Poly).IsWeightedHomogeneous bidegreeWeight (2,0) := by
    convert (hX 0).pow 2 using 1 <;> norm_num [nsmul_eq_mul, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four] <;> decide
  have hc2 : (X 2 ^ 2 : Poly).IsWeightedHomogeneous bidegreeWeight (2,0) := by
    convert (hX 2).pow 2 using 1 <;> norm_num [nsmul_eq_mul, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four] <;> decide
  have ha4 : (X 0 ^ 4 : Poly).IsWeightedHomogeneous bidegreeWeight (4,0) := by
    convert (hX 0).pow 4 using 1 <;> norm_num [nsmul_eq_mul, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four] <;> decide
  have hc4 : (X 2 ^ 4 : Poly).IsWeightedHomogeneous bidegreeWeight (4,0) := by
    convert (hX 2).pow 4 using 1 <;> norm_num [nsmul_eq_mul, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four] <;> decide
  have h6 (i : Fin 4) : (X i.castSucc ^ 6 : Poly).IsWeightedHomogeneous
      bidegreeWeight (6,0) := by
    convert (hX i.castSucc).pow 6 using 1
    fin_cases i <;> norm_num [nsmul_eq_mul, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four] <;> decide
  have hu : (X 4 : Poly).IsWeightedHomogeneous bidegreeWeight (2,0) := by
    simpa [Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four] using hX 4
  have hu2 : (X 4 ^ 2 : Poly).IsWeightedHomogeneous bidegreeWeight (4,0) := by
    convert hu.pow 2 using 1 <;> norm_num [nsmul_eq_mul] <;> decide
  have hu3 : (X 4 ^ 3 : Poly).IsWeightedHomogeneous bidegreeWeight (6,0) := by
    convert hu.pow 3 using 1 <;> norm_num [nsmul_eq_mul] <;> decide
  have hab : (X 0 * X 1 : Poly).IsWeightedHomogeneous bidegreeWeight (2,0) := by
    simpa [Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four] using (hX 0).mul (hX 1)
  have hcd : (X 2 * X 3 : Poly).IsWeightedHomogeneous bidegreeWeight (2,0) := by
    convert (hX 2).mul (hX 3) using 1 <;> norm_num [Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four] <;> decide
  have hq : IsWeightedHomogeneous bidegreeWeight
      (map (Int.castRingHom ℂ) WeightedFiberSmoothness.leftQuadric) (2,0) := by
    simpa [WeightedFiberSmoothness.leftQuadric, map_ofNat, mul_assoc] using
      (ha2.add (hab.C_mul 2)).sub hu
  have hr : IsWeightedHomogeneous bidegreeWeight
      (map (Int.castRingHom ℂ) WeightedFiberSmoothness.rightQuadric) (2,0) := by
    simpa [WeightedFiberSmoothness.rightQuadric, map_ofNat, mul_assoc] using
      (hc2.add (hcd.C_mul 2)).sub hu
  have hq2r : IsWeightedHomogeneous bidegreeWeight
      ((map (Int.castRingHom ℂ) WeightedFiberSmoothness.leftQuadric)^2 *
      map (Int.castRingHom ℂ) WeightedFiberSmoothness.rightQuadric) (6,0) := by
    convert (hq.pow 2).mul hr using 1 <;> norm_num [nsmul_eq_mul] <;> decide
  have hqr2 : IsWeightedHomogeneous bidegreeWeight
      (map (Int.castRingHom ℂ) WeightedFiberSmoothness.leftQuadric *
      (map (Int.castRingHom ℂ) WeightedFiberSmoothness.rightQuadric)^2) (6,0) := by
    convert hq.mul (hr.pow 2) using 1 <;> norm_num [nsmul_eq_mul] <;> decide
  have ha4u : (X 0 ^ 4 * X 4 : Poly).IsWeightedHomogeneous bidegreeWeight (6,0) := by
    simpa using ha4.mul hu
  have hc4u : (X 2 ^ 4 * X 4 : Poly).IsWeightedHomogeneous bidegreeWeight (6,0) := by
    simpa using hc4.mul hu
  have ha2u2 : (X 0 ^ 2 * X 4 ^ 2 : Poly).IsWeightedHomogeneous bidegreeWeight (6,0) := by
    simpa using ha2.mul hu2
  have hc2u2 : (X 2 ^ 2 * X 4 ^ 2 : Poly).IsWeightedHomogeneous bidegreeWeight (6,0) := by
    simpa using hc2.mul hu2
  have hmain0 := (((h6 0).C_mul 2).add (h6 1)).add ((h6 2).C_mul 2)
  have hmain1 := ((hmain0.add (h6 3)).add (ha4u.C_mul 30)).add (hc4u.C_mul 30)
  have hmain := ((hmain1.add (ha2u2.C_mul 30)).add (hc2u2.C_mul 30)).add (hu3.C_mul 4)
  have hint := ((hmain.C_mul 7).add (hq2r.C_mul 5)).add (hqr2.C_mul 10)
  simpa [WeightedFiberSmoothness.weightedG, WeightedFiberSmoothness.integerWeighted,
    map_ofNat, mul_assoc] using hint.C_mul (1/13 : ℂ)

def derivativeBidegree (i : Fin 5) : ℕ × ZMod 2 :=
  (6 - (bidegreeWeight i).1, -(bidegreeWeight i).2)

theorem partial_bihomogeneous (i : Fin 5) :
    (pderiv i WeightedFiberSmoothness.weightedG).IsWeightedHomogeneous
      bidegreeWeight (derivativeBidegree i) := by
  intro e he
  have hc : coeff (e + Finsupp.single i 1) WeightedFiberSmoothness.weightedG ≠ 0 := by
    intro hz
    simp [coeff_pderiv, hz] at he
  have h := weightedG_bihomogeneous hc
  rw [map_add, Finsupp.weight_single, one_smul] at h
  apply Prod.ext
  · have hfst := congrArg Prod.fst h
    simp only [Prod.fst_add] at hfst
    change (Finsupp.weight bidegreeWeight e).1 = 6 - (bidegreeWeight i).1
    omega
  · have hsnd := congrArg Prod.snd h
    simp only [Prod.snd_add] at hsnd
    change (Finsupp.weight bidegreeWeight e).2 = -(bidegreeWeight i).2
    exact eq_neg_of_add_eq_zero_left hsnd

def multiplierBidegree (j : Fin 12) : ℕ × ZMod 2 :=
  ((bidegreeWeight (partialIndex j)).1, 1 + (bidegreeWeight (partialIndex j)).2)

theorem multiplier_bihomogeneous (j : Fin 12) :
    (map (Int.castRingHom ℂ) (multiplier j)).IsWeightedHomogeneous
      bidegreeWeight (multiplierBidegree j) := by
  have hX (i : Fin 5) : (X i : Poly).IsWeightedHomogeneous bidegreeWeight
      (bidegreeWeight i) := isWeightedHomogeneous_X ℂ _ _
  fin_cases j
  · simpa [multiplier, multiplierBidegree, partialIndex, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four] using hX 2
  · simpa [multiplier, multiplierBidegree, partialIndex, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four] using hX 3
  · simpa [multiplier, multiplierBidegree, partialIndex, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four] using hX 2
  · simpa [multiplier, multiplierBidegree, partialIndex, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four] using hX 3
  · convert hX 0 using 1 <;>
      norm_num [multiplier, multiplierBidegree, partialIndex, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four] <;> decide
  · convert hX 1 using 1 <;>
      norm_num [multiplier, multiplierBidegree, partialIndex, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four] <;> decide
  · convert hX 0 using 1 <;>
      norm_num [multiplier, multiplierBidegree, partialIndex, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four] <;> decide
  · convert hX 1 using 1 <;>
      norm_num [multiplier, multiplierBidegree, partialIndex, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four] <;> decide
  · simpa [multiplier, multiplierBidegree, partialIndex, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four] using
      (hX 0).mul (hX 2)
  · simpa [multiplier, multiplierBidegree, partialIndex, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four] using
      (hX 0).mul (hX 3)
  · simpa [multiplier, multiplierBidegree, partialIndex, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four] using
      (hX 1).mul (hX 2)
  · simpa [multiplier, multiplierBidegree, partialIndex, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four] using
      (hX 1).mul (hX 3)

theorem direction_bihomogeneous (j : Fin 12) :
    (direction j).IsWeightedHomogeneous bidegreeWeight (6,1) := by
  have h := (multiplier_bihomogeneous j).mul (partial_bihomogeneous (partialIndex j))
  change (direction j).IsWeightedHomogeneous bidegreeWeight
    (multiplierBidegree j + derivativeBidegree (partialIndex j)) at h
  convert h using 1
  fin_cases j <;>
    norm_num [multiplierBidegree, derivativeBidegree, partialIndex, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four] <;> decide

#print axioms weightedG_bihomogeneous
#print axioms direction_bihomogeneous

end SymmetricNegativeJacobian
