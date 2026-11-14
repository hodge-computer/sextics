import Proposal.SolutionSupport01Part02

/-! Components extracted from SolutionSupport01.lean, in their original order.
See solution.md for the mathematical and verification status. -/

set_option Elab.async false

/- Component: continuation_3/SegreModularCubicChecks1.lean -/
section
set_option maxHeartbeats 2000000000
set_option maxRecDepth 100000
set_option Elab.async false
namespace CycleQ2SegreModularCubicData
open CycleQ2SparseGaussianPolynomial CycleQ2SegreGaussianTangentData

def kqError1 : Towers := addTowers (normalizeTower a0 a1 b0 32 (mulTowers k q01)) (negTowers kq1)
theorem kq_check1 : checkTowers kqError1=true := by decide +kernel

theorem eval_kq1 {R : Type*} [CommRing R]
    (φ : GaussianInt →+* R) (x : Fin 5 → R) (w z v : R)
    (hz : z^3=evalLayers φ x v a0+evalLayers φ x v a1*z)
    (hw : w^3=evalLayers φ x v b0-z^6) :
    evalTowers φ x w z v kq1=evalTowers φ x w z v k * evalTowers φ x w z v q01 := by
  rw [evaluation_of_normal_error_check φ x w z v a0 a1 b0 hz hw 32 (mulTowers k q01) kq1 kq_check1,eval_mulTowers]

def cubicError1_0 : Towers := addTowers
  (normalizeTower a0 a1 b0 32 (mulTowers monomialCubic0 kq1)) (negTowers cubic1_0)
theorem cubic_check1_0 : checkTowers cubicError1_0=true := by decide +kernel

theorem eval_cubic1_0 {R : Type*} [CommRing R]
    (φ : GaussianInt →+* R) (x : Fin 5 → R) (w z v : R)
    (hz : z^3=evalLayers φ x v a0+evalLayers φ x v a1*z)
    (hw : w^3=evalLayers φ x v b0-z^6) :
    evalTowers φ x w z v cubic1_0=evalTowers φ x w z v monomialCubic0 *
      evalTowers φ x w z v k * evalTowers φ x w z v q01 := by
  rw [evaluation_of_normal_error_check φ x w z v a0 a1 b0 hz hw 32
    (mulTowers monomialCubic0 kq1) cubic1_0 cubic_check1_0,
    eval_mulTowers,eval_kq1 φ x w z v hz hw,mul_assoc]

def cubicError1_1 : Towers := addTowers
  (normalizeTower a0 a1 b0 32 (mulTowers monomialCubic1 kq1)) (negTowers cubic1_1)
theorem cubic_check1_1 : checkTowers cubicError1_1=true := by decide +kernel

theorem eval_cubic1_1 {R : Type*} [CommRing R]
    (φ : GaussianInt →+* R) (x : Fin 5 → R) (w z v : R)
    (hz : z^3=evalLayers φ x v a0+evalLayers φ x v a1*z)
    (hw : w^3=evalLayers φ x v b0-z^6) :
    evalTowers φ x w z v cubic1_1=evalTowers φ x w z v monomialCubic1 *
      evalTowers φ x w z v k * evalTowers φ x w z v q01 := by
  rw [evaluation_of_normal_error_check φ x w z v a0 a1 b0 hz hw 32
    (mulTowers monomialCubic1 kq1) cubic1_1 cubic_check1_1,
    eval_mulTowers,eval_kq1 φ x w z v hz hw,mul_assoc]

def cubicError1_2 : Towers := addTowers
  (normalizeTower a0 a1 b0 32 (mulTowers monomialCubic2 kq1)) (negTowers cubic1_2)
theorem cubic_check1_2 : checkTowers cubicError1_2=true := by decide +kernel

theorem eval_cubic1_2 {R : Type*} [CommRing R]
    (φ : GaussianInt →+* R) (x : Fin 5 → R) (w z v : R)
    (hz : z^3=evalLayers φ x v a0+evalLayers φ x v a1*z)
    (hw : w^3=evalLayers φ x v b0-z^6) :
    evalTowers φ x w z v cubic1_2=evalTowers φ x w z v monomialCubic2 *
      evalTowers φ x w z v k * evalTowers φ x w z v q01 := by
  rw [evaluation_of_normal_error_check φ x w z v a0 a1 b0 hz hw 32
    (mulTowers monomialCubic2 kq1) cubic1_2 cubic_check1_2,
    eval_mulTowers,eval_kq1 φ x w z v hz hw,mul_assoc]

def cubicError1_3 : Towers := addTowers
  (normalizeTower a0 a1 b0 32 (mulTowers monomialCubic3 kq1)) (negTowers cubic1_3)
theorem cubic_check1_3 : checkTowers cubicError1_3=true := by decide +kernel

theorem eval_cubic1_3 {R : Type*} [CommRing R]
    (φ : GaussianInt →+* R) (x : Fin 5 → R) (w z v : R)
    (hz : z^3=evalLayers φ x v a0+evalLayers φ x v a1*z)
    (hw : w^3=evalLayers φ x v b0-z^6) :
    evalTowers φ x w z v cubic1_3=evalTowers φ x w z v monomialCubic3 *
      evalTowers φ x w z v k * evalTowers φ x w z v q01 := by
  rw [evaluation_of_normal_error_check φ x w z v a0 a1 b0 hz hw 32
    (mulTowers monomialCubic3 kq1) cubic1_3 cubic_check1_3,
    eval_mulTowers,eval_kq1 φ x w z v hz hw,mul_assoc]

def cubicError1_4 : Towers := addTowers
  (normalizeTower a0 a1 b0 32 (mulTowers monomialCubic4 kq1)) (negTowers cubic1_4)
theorem cubic_check1_4 : checkTowers cubicError1_4=true := by decide +kernel

theorem eval_cubic1_4 {R : Type*} [CommRing R]
    (φ : GaussianInt →+* R) (x : Fin 5 → R) (w z v : R)
    (hz : z^3=evalLayers φ x v a0+evalLayers φ x v a1*z)
    (hw : w^3=evalLayers φ x v b0-z^6) :
    evalTowers φ x w z v cubic1_4=evalTowers φ x w z v monomialCubic4 *
      evalTowers φ x w z v k * evalTowers φ x w z v q01 := by
  rw [evaluation_of_normal_error_check φ x w z v a0 a1 b0 hz hw 32
    (mulTowers monomialCubic4 kq1) cubic1_4 cubic_check1_4,
    eval_mulTowers,eval_kq1 φ x w z v hz hw,mul_assoc]

def cubicError1_5 : Towers := addTowers
  (normalizeTower a0 a1 b0 32 (mulTowers monomialCubic5 kq1)) (negTowers cubic1_5)
theorem cubic_check1_5 : checkTowers cubicError1_5=true := by decide +kernel

theorem eval_cubic1_5 {R : Type*} [CommRing R]
    (φ : GaussianInt →+* R) (x : Fin 5 → R) (w z v : R)
    (hz : z^3=evalLayers φ x v a0+evalLayers φ x v a1*z)
    (hw : w^3=evalLayers φ x v b0-z^6) :
    evalTowers φ x w z v cubic1_5=evalTowers φ x w z v monomialCubic5 *
      evalTowers φ x w z v k * evalTowers φ x w z v q01 := by
  rw [evaluation_of_normal_error_check φ x w z v a0 a1 b0 hz hw 32
    (mulTowers monomialCubic5 kq1) cubic1_5 cubic_check1_5,
    eval_mulTowers,eval_kq1 φ x w z v hz hw,mul_assoc]

def cubicError1_6 : Towers := addTowers
  (normalizeTower a0 a1 b0 32 (mulTowers monomialCubic6 kq1)) (negTowers cubic1_6)
theorem cubic_check1_6 : checkTowers cubicError1_6=true := by decide +kernel

theorem eval_cubic1_6 {R : Type*} [CommRing R]
    (φ : GaussianInt →+* R) (x : Fin 5 → R) (w z v : R)
    (hz : z^3=evalLayers φ x v a0+evalLayers φ x v a1*z)
    (hw : w^3=evalLayers φ x v b0-z^6) :
    evalTowers φ x w z v cubic1_6=evalTowers φ x w z v monomialCubic6 *
      evalTowers φ x w z v k * evalTowers φ x w z v q01 := by
  rw [evaluation_of_normal_error_check φ x w z v a0 a1 b0 hz hw 32
    (mulTowers monomialCubic6 kq1) cubic1_6 cubic_check1_6,
    eval_mulTowers,eval_kq1 φ x w z v hz hw,mul_assoc]

def cubicError1_7 : Towers := addTowers
  (normalizeTower a0 a1 b0 32 (mulTowers monomialCubic7 kq1)) (negTowers cubic1_7)
theorem cubic_check1_7 : checkTowers cubicError1_7=true := by decide +kernel

theorem eval_cubic1_7 {R : Type*} [CommRing R]
    (φ : GaussianInt →+* R) (x : Fin 5 → R) (w z v : R)
    (hz : z^3=evalLayers φ x v a0+evalLayers φ x v a1*z)
    (hw : w^3=evalLayers φ x v b0-z^6) :
    evalTowers φ x w z v cubic1_7=evalTowers φ x w z v monomialCubic7 *
      evalTowers φ x w z v k * evalTowers φ x w z v q01 := by
  rw [evaluation_of_normal_error_check φ x w z v a0 a1 b0 hz hw 32
    (mulTowers monomialCubic7 kq1) cubic1_7 cubic_check1_7,
    eval_mulTowers,eval_kq1 φ x w z v hz hw,mul_assoc]

def cubicError1_8 : Towers := addTowers
  (normalizeTower a0 a1 b0 32 (mulTowers monomialCubic8 kq1)) (negTowers cubic1_8)
theorem cubic_check1_8 : checkTowers cubicError1_8=true := by decide +kernel

theorem eval_cubic1_8 {R : Type*} [CommRing R]
    (φ : GaussianInt →+* R) (x : Fin 5 → R) (w z v : R)
    (hz : z^3=evalLayers φ x v a0+evalLayers φ x v a1*z)
    (hw : w^3=evalLayers φ x v b0-z^6) :
    evalTowers φ x w z v cubic1_8=evalTowers φ x w z v monomialCubic8 *
      evalTowers φ x w z v k * evalTowers φ x w z v q01 := by
  rw [evaluation_of_normal_error_check φ x w z v a0 a1 b0 hz hw 32
    (mulTowers monomialCubic8 kq1) cubic1_8 cubic_check1_8,
    eval_mulTowers,eval_kq1 φ x w z v hz hw,mul_assoc]

end CycleQ2SegreModularCubicData
#print axioms CycleQ2SegreModularCubicData.eval_cubic1_8
end


