import Proposal.SolutionSupport01Part03

/-! Components extracted from SolutionSupport01.lean, in their original order.
See solution.md for the mathematical and verification status. -/

set_option Elab.async false

/- Component: continuation_3/SegreModularCubicChecks2.lean -/
section
set_option maxHeartbeats 2000000000
set_option maxRecDepth 100000
set_option Elab.async false
namespace CycleQ2SegreModularCubicData
open CycleQ2SparseGaussianPolynomial CycleQ2SegreGaussianTangentData

def kqError2 : Towers := addTowers (normalizeTower a0 a1 b0 32 (mulTowers k q02)) (negTowers kq2)
private theorem kq_length2 : kqError2.length≤3 := by decide +kernel
private theorem kq_inner2 : ∀ b : Fin 3, (kqError2[b.val]?.getD []).length≤3 := by
  decide +kernel
private theorem kq_block2_0_0 : checkTowerBlock kqError2 0 0=true := by
  decide +kernel
private theorem kq_block2_0_1 : checkTowerBlock kqError2 0 1=true := by
  decide +kernel
private theorem kq_block2_0_2 : checkTowerBlock kqError2 0 2=true := by
  decide +kernel
private theorem kq_block2_1_0 : checkTowerBlock kqError2 1 0=true := by
  decide +kernel
private theorem kq_block2_1_1 : checkTowerBlock kqError2 1 1=true := by
  decide +kernel
private theorem kq_block2_1_2 : checkTowerBlock kqError2 1 2=true := by
  decide +kernel
private theorem kq_block2_2_0 : checkTowerBlock kqError2 2 0=true := by
  decide +kernel
private theorem kq_block2_2_1 : checkTowerBlock kqError2 2 1=true := by
  decide +kernel
private theorem kq_block2_2_2 : checkTowerBlock kqError2 2 2=true := by
  decide +kernel
private theorem kq_blocks2 (b a : Fin 3) : checkTowerBlock kqError2 b a=true := by
  fin_cases b <;> fin_cases a
  · exact kq_block2_0_0
  · exact kq_block2_0_1
  · exact kq_block2_0_2
  · exact kq_block2_1_0
  · exact kq_block2_1_1
  · exact kq_block2_1_2
  · exact kq_block2_2_0
  · exact kq_block2_2_1
  · exact kq_block2_2_2

theorem eval_kq2 {R : Type*} [CommRing R]
    (φ : GaussianInt →+* R) (x : Fin 5 → R) (w z v : R)
    (hz : z^3=evalLayers φ x v a0+evalLayers φ x v a1*z)
    (hw : w^3=evalLayers φ x v b0-z^6) :
    evalTowers φ x w z v kq2=evalTowers φ x w z v k * evalTowers φ x w z v q02 := by
  have he := evalTowers_eq_zero_of_block_checks φ x w z v 3 3 kqError2
    kq_length2 kq_inner2 kq_blocks2
  rw [kqError2,eval_addTowers,eval_negTowers,
    eval_normalizeTower φ x w z v a0 a1 b0 hz hw,eval_mulTowers] at he
  exact (sub_eq_zero.mp (by simpa only [sub_eq_add_neg] using he)).symm

def cubicError2_0 : Towers := addTowers
  (normalizeTower a0 a1 b0 32 (mulTowers monomialCubic0 kq2)) (negTowers cubic2_0)
theorem cubic_check2_0 : checkTowers cubicError2_0=true := by decide +kernel

theorem eval_cubic2_0 {R : Type*} [CommRing R]
    (φ : GaussianInt →+* R) (x : Fin 5 → R) (w z v : R)
    (hz : z^3=evalLayers φ x v a0+evalLayers φ x v a1*z)
    (hw : w^3=evalLayers φ x v b0-z^6) :
    evalTowers φ x w z v cubic2_0=evalTowers φ x w z v monomialCubic0 *
      evalTowers φ x w z v k * evalTowers φ x w z v q02 := by
  rw [evaluation_of_normal_error_check φ x w z v a0 a1 b0 hz hw 32
    (mulTowers monomialCubic0 kq2) cubic2_0 cubic_check2_0,
    eval_mulTowers,eval_kq2 φ x w z v hz hw,mul_assoc]

def cubicError2_1 : Towers := addTowers
  (normalizeTower a0 a1 b0 32 (mulTowers monomialCubic1 kq2)) (negTowers cubic2_1)
theorem cubic_check2_1 : checkTowers cubicError2_1=true := by decide +kernel

theorem eval_cubic2_1 {R : Type*} [CommRing R]
    (φ : GaussianInt →+* R) (x : Fin 5 → R) (w z v : R)
    (hz : z^3=evalLayers φ x v a0+evalLayers φ x v a1*z)
    (hw : w^3=evalLayers φ x v b0-z^6) :
    evalTowers φ x w z v cubic2_1=evalTowers φ x w z v monomialCubic1 *
      evalTowers φ x w z v k * evalTowers φ x w z v q02 := by
  rw [evaluation_of_normal_error_check φ x w z v a0 a1 b0 hz hw 32
    (mulTowers monomialCubic1 kq2) cubic2_1 cubic_check2_1,
    eval_mulTowers,eval_kq2 φ x w z v hz hw,mul_assoc]

def cubicError2_2 : Towers := addTowers
  (normalizeTower a0 a1 b0 32 (mulTowers monomialCubic2 kq2)) (negTowers cubic2_2)
theorem cubic_check2_2 : checkTowers cubicError2_2=true := by decide +kernel

theorem eval_cubic2_2 {R : Type*} [CommRing R]
    (φ : GaussianInt →+* R) (x : Fin 5 → R) (w z v : R)
    (hz : z^3=evalLayers φ x v a0+evalLayers φ x v a1*z)
    (hw : w^3=evalLayers φ x v b0-z^6) :
    evalTowers φ x w z v cubic2_2=evalTowers φ x w z v monomialCubic2 *
      evalTowers φ x w z v k * evalTowers φ x w z v q02 := by
  rw [evaluation_of_normal_error_check φ x w z v a0 a1 b0 hz hw 32
    (mulTowers monomialCubic2 kq2) cubic2_2 cubic_check2_2,
    eval_mulTowers,eval_kq2 φ x w z v hz hw,mul_assoc]

def cubicError2_3 : Towers := addTowers
  (normalizeTower a0 a1 b0 32 (mulTowers monomialCubic3 kq2)) (negTowers cubic2_3)
theorem cubic_check2_3 : checkTowers cubicError2_3=true := by decide +kernel

theorem eval_cubic2_3 {R : Type*} [CommRing R]
    (φ : GaussianInt →+* R) (x : Fin 5 → R) (w z v : R)
    (hz : z^3=evalLayers φ x v a0+evalLayers φ x v a1*z)
    (hw : w^3=evalLayers φ x v b0-z^6) :
    evalTowers φ x w z v cubic2_3=evalTowers φ x w z v monomialCubic3 *
      evalTowers φ x w z v k * evalTowers φ x w z v q02 := by
  rw [evaluation_of_normal_error_check φ x w z v a0 a1 b0 hz hw 32
    (mulTowers monomialCubic3 kq2) cubic2_3 cubic_check2_3,
    eval_mulTowers,eval_kq2 φ x w z v hz hw,mul_assoc]

def cubicError2_4 : Towers := addTowers
  (normalizeTower a0 a1 b0 32 (mulTowers monomialCubic4 kq2)) (negTowers cubic2_4)
theorem cubic_check2_4 : checkTowers cubicError2_4=true := by decide +kernel

theorem eval_cubic2_4 {R : Type*} [CommRing R]
    (φ : GaussianInt →+* R) (x : Fin 5 → R) (w z v : R)
    (hz : z^3=evalLayers φ x v a0+evalLayers φ x v a1*z)
    (hw : w^3=evalLayers φ x v b0-z^6) :
    evalTowers φ x w z v cubic2_4=evalTowers φ x w z v monomialCubic4 *
      evalTowers φ x w z v k * evalTowers φ x w z v q02 := by
  rw [evaluation_of_normal_error_check φ x w z v a0 a1 b0 hz hw 32
    (mulTowers monomialCubic4 kq2) cubic2_4 cubic_check2_4,
    eval_mulTowers,eval_kq2 φ x w z v hz hw,mul_assoc]

def cubicError2_5 : Towers := addTowers
  (normalizeTower a0 a1 b0 32 (mulTowers monomialCubic5 kq2)) (negTowers cubic2_5)
theorem cubic_check2_5 : checkTowers cubicError2_5=true := by decide +kernel

theorem eval_cubic2_5 {R : Type*} [CommRing R]
    (φ : GaussianInt →+* R) (x : Fin 5 → R) (w z v : R)
    (hz : z^3=evalLayers φ x v a0+evalLayers φ x v a1*z)
    (hw : w^3=evalLayers φ x v b0-z^6) :
    evalTowers φ x w z v cubic2_5=evalTowers φ x w z v monomialCubic5 *
      evalTowers φ x w z v k * evalTowers φ x w z v q02 := by
  rw [evaluation_of_normal_error_check φ x w z v a0 a1 b0 hz hw 32
    (mulTowers monomialCubic5 kq2) cubic2_5 cubic_check2_5,
    eval_mulTowers,eval_kq2 φ x w z v hz hw,mul_assoc]

def cubicError2_6 : Towers := addTowers
  (normalizeTower a0 a1 b0 32 (mulTowers monomialCubic6 kq2)) (negTowers cubic2_6)
theorem cubic_check2_6 : checkTowers cubicError2_6=true := by decide +kernel

theorem eval_cubic2_6 {R : Type*} [CommRing R]
    (φ : GaussianInt →+* R) (x : Fin 5 → R) (w z v : R)
    (hz : z^3=evalLayers φ x v a0+evalLayers φ x v a1*z)
    (hw : w^3=evalLayers φ x v b0-z^6) :
    evalTowers φ x w z v cubic2_6=evalTowers φ x w z v monomialCubic6 *
      evalTowers φ x w z v k * evalTowers φ x w z v q02 := by
  rw [evaluation_of_normal_error_check φ x w z v a0 a1 b0 hz hw 32
    (mulTowers monomialCubic6 kq2) cubic2_6 cubic_check2_6,
    eval_mulTowers,eval_kq2 φ x w z v hz hw,mul_assoc]

def cubicError2_7 : Towers := addTowers
  (normalizeTower a0 a1 b0 32 (mulTowers monomialCubic7 kq2)) (negTowers cubic2_7)
theorem cubic_check2_7 : checkTowers cubicError2_7=true := by decide +kernel

theorem eval_cubic2_7 {R : Type*} [CommRing R]
    (φ : GaussianInt →+* R) (x : Fin 5 → R) (w z v : R)
    (hz : z^3=evalLayers φ x v a0+evalLayers φ x v a1*z)
    (hw : w^3=evalLayers φ x v b0-z^6) :
    evalTowers φ x w z v cubic2_7=evalTowers φ x w z v monomialCubic7 *
      evalTowers φ x w z v k * evalTowers φ x w z v q02 := by
  rw [evaluation_of_normal_error_check φ x w z v a0 a1 b0 hz hw 32
    (mulTowers monomialCubic7 kq2) cubic2_7 cubic_check2_7,
    eval_mulTowers,eval_kq2 φ x w z v hz hw,mul_assoc]

def cubicError2_8 : Towers := addTowers
  (normalizeTower a0 a1 b0 32 (mulTowers monomialCubic8 kq2)) (negTowers cubic2_8)
theorem cubic_check2_8 : checkTowers cubicError2_8=true := by decide +kernel

theorem eval_cubic2_8 {R : Type*} [CommRing R]
    (φ : GaussianInt →+* R) (x : Fin 5 → R) (w z v : R)
    (hz : z^3=evalLayers φ x v a0+evalLayers φ x v a1*z)
    (hw : w^3=evalLayers φ x v b0-z^6) :
    evalTowers φ x w z v cubic2_8=evalTowers φ x w z v monomialCubic8 *
      evalTowers φ x w z v k * evalTowers φ x w z v q02 := by
  rw [evaluation_of_normal_error_check φ x w z v a0 a1 b0 hz hw 32
    (mulTowers monomialCubic8 kq2) cubic2_8 cubic_check2_8,
    eval_mulTowers,eval_kq2 φ x w z v hz hw,mul_assoc]

end CycleQ2SegreModularCubicData
#print axioms CycleQ2SegreModularCubicData.eval_cubic2_8
end


