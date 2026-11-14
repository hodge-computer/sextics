import Proposal.SolutionSupport01Part01

/-! Components extracted from SolutionSupport01.lean, in their original order.
See solution.md for the mathematical and verification status. -/

set_option Elab.async false

/- Component: continuation_3/SegreModularCubicChecks0.lean -/
section
set_option maxHeartbeats 2000000000
set_option maxRecDepth 100000
set_option Elab.async false
namespace CycleQ2SegreModularCubicData
open CycleQ2SparseGaussianPolynomial CycleQ2SegreGaussianTangentData

def kqError0 : Towers := addTowers (normalizeTower a0 a1 b0 32 (mulTowers k q00)) (negTowers kq0)
theorem kq_check0 : checkTowers kqError0=true := by decide +kernel

theorem eval_kq0 {R : Type*} [CommRing R]
    (φ : GaussianInt →+* R) (x : Fin 5 → R) (w z v : R)
    (hz : z^3=evalLayers φ x v a0+evalLayers φ x v a1*z)
    (hw : w^3=evalLayers φ x v b0-z^6) :
    evalTowers φ x w z v kq0=evalTowers φ x w z v k * evalTowers φ x w z v q00 := by
  rw [evaluation_of_normal_error_check φ x w z v a0 a1 b0 hz hw 32 (mulTowers k q00) kq0 kq_check0,eval_mulTowers]

def cubicError0_0 : Towers := addTowers
  (normalizeTower a0 a1 b0 32 (mulTowers monomialCubic0 kq0)) (negTowers cubic0_0)
theorem cubic_check0_0 : checkTowers cubicError0_0=true := by decide +kernel

theorem eval_cubic0_0 {R : Type*} [CommRing R]
    (φ : GaussianInt →+* R) (x : Fin 5 → R) (w z v : R)
    (hz : z^3=evalLayers φ x v a0+evalLayers φ x v a1*z)
    (hw : w^3=evalLayers φ x v b0-z^6) :
    evalTowers φ x w z v cubic0_0=evalTowers φ x w z v monomialCubic0 *
      evalTowers φ x w z v k * evalTowers φ x w z v q00 := by
  rw [evaluation_of_normal_error_check φ x w z v a0 a1 b0 hz hw 32
    (mulTowers monomialCubic0 kq0) cubic0_0 cubic_check0_0,
    eval_mulTowers,eval_kq0 φ x w z v hz hw,mul_assoc]

def cubicError0_1 : Towers := addTowers
  (normalizeTower a0 a1 b0 32 (mulTowers monomialCubic1 kq0)) (negTowers cubic0_1)
theorem cubic_check0_1 : checkTowers cubicError0_1=true := by decide +kernel

theorem eval_cubic0_1 {R : Type*} [CommRing R]
    (φ : GaussianInt →+* R) (x : Fin 5 → R) (w z v : R)
    (hz : z^3=evalLayers φ x v a0+evalLayers φ x v a1*z)
    (hw : w^3=evalLayers φ x v b0-z^6) :
    evalTowers φ x w z v cubic0_1=evalTowers φ x w z v monomialCubic1 *
      evalTowers φ x w z v k * evalTowers φ x w z v q00 := by
  rw [evaluation_of_normal_error_check φ x w z v a0 a1 b0 hz hw 32
    (mulTowers monomialCubic1 kq0) cubic0_1 cubic_check0_1,
    eval_mulTowers,eval_kq0 φ x w z v hz hw,mul_assoc]

def cubicError0_2 : Towers := addTowers
  (normalizeTower a0 a1 b0 32 (mulTowers monomialCubic2 kq0)) (negTowers cubic0_2)
theorem cubic_check0_2 : checkTowers cubicError0_2=true := by decide +kernel

theorem eval_cubic0_2 {R : Type*} [CommRing R]
    (φ : GaussianInt →+* R) (x : Fin 5 → R) (w z v : R)
    (hz : z^3=evalLayers φ x v a0+evalLayers φ x v a1*z)
    (hw : w^3=evalLayers φ x v b0-z^6) :
    evalTowers φ x w z v cubic0_2=evalTowers φ x w z v monomialCubic2 *
      evalTowers φ x w z v k * evalTowers φ x w z v q00 := by
  rw [evaluation_of_normal_error_check φ x w z v a0 a1 b0 hz hw 32
    (mulTowers monomialCubic2 kq0) cubic0_2 cubic_check0_2,
    eval_mulTowers,eval_kq0 φ x w z v hz hw,mul_assoc]

def cubicError0_3 : Towers := addTowers
  (normalizeTower a0 a1 b0 32 (mulTowers monomialCubic3 kq0)) (negTowers cubic0_3)
theorem cubic_check0_3 : checkTowers cubicError0_3=true := by decide +kernel

theorem eval_cubic0_3 {R : Type*} [CommRing R]
    (φ : GaussianInt →+* R) (x : Fin 5 → R) (w z v : R)
    (hz : z^3=evalLayers φ x v a0+evalLayers φ x v a1*z)
    (hw : w^3=evalLayers φ x v b0-z^6) :
    evalTowers φ x w z v cubic0_3=evalTowers φ x w z v monomialCubic3 *
      evalTowers φ x w z v k * evalTowers φ x w z v q00 := by
  rw [evaluation_of_normal_error_check φ x w z v a0 a1 b0 hz hw 32
    (mulTowers monomialCubic3 kq0) cubic0_3 cubic_check0_3,
    eval_mulTowers,eval_kq0 φ x w z v hz hw,mul_assoc]

def cubicError0_4 : Towers := addTowers
  (normalizeTower a0 a1 b0 32 (mulTowers monomialCubic4 kq0)) (negTowers cubic0_4)
theorem cubic_check0_4 : checkTowers cubicError0_4=true := by decide +kernel

theorem eval_cubic0_4 {R : Type*} [CommRing R]
    (φ : GaussianInt →+* R) (x : Fin 5 → R) (w z v : R)
    (hz : z^3=evalLayers φ x v a0+evalLayers φ x v a1*z)
    (hw : w^3=evalLayers φ x v b0-z^6) :
    evalTowers φ x w z v cubic0_4=evalTowers φ x w z v monomialCubic4 *
      evalTowers φ x w z v k * evalTowers φ x w z v q00 := by
  rw [evaluation_of_normal_error_check φ x w z v a0 a1 b0 hz hw 32
    (mulTowers monomialCubic4 kq0) cubic0_4 cubic_check0_4,
    eval_mulTowers,eval_kq0 φ x w z v hz hw,mul_assoc]

def cubicError0_5 : Towers := addTowers
  (normalizeTower a0 a1 b0 32 (mulTowers monomialCubic5 kq0)) (negTowers cubic0_5)
theorem cubic_check0_5 : checkTowers cubicError0_5=true := by decide +kernel

theorem eval_cubic0_5 {R : Type*} [CommRing R]
    (φ : GaussianInt →+* R) (x : Fin 5 → R) (w z v : R)
    (hz : z^3=evalLayers φ x v a0+evalLayers φ x v a1*z)
    (hw : w^3=evalLayers φ x v b0-z^6) :
    evalTowers φ x w z v cubic0_5=evalTowers φ x w z v monomialCubic5 *
      evalTowers φ x w z v k * evalTowers φ x w z v q00 := by
  rw [evaluation_of_normal_error_check φ x w z v a0 a1 b0 hz hw 32
    (mulTowers monomialCubic5 kq0) cubic0_5 cubic_check0_5,
    eval_mulTowers,eval_kq0 φ x w z v hz hw,mul_assoc]

def cubicError0_6 : Towers := addTowers
  (normalizeTower a0 a1 b0 32 (mulTowers monomialCubic6 kq0)) (negTowers cubic0_6)
theorem cubic_check0_6 : checkTowers cubicError0_6=true := by decide +kernel

theorem eval_cubic0_6 {R : Type*} [CommRing R]
    (φ : GaussianInt →+* R) (x : Fin 5 → R) (w z v : R)
    (hz : z^3=evalLayers φ x v a0+evalLayers φ x v a1*z)
    (hw : w^3=evalLayers φ x v b0-z^6) :
    evalTowers φ x w z v cubic0_6=evalTowers φ x w z v monomialCubic6 *
      evalTowers φ x w z v k * evalTowers φ x w z v q00 := by
  rw [evaluation_of_normal_error_check φ x w z v a0 a1 b0 hz hw 32
    (mulTowers monomialCubic6 kq0) cubic0_6 cubic_check0_6,
    eval_mulTowers,eval_kq0 φ x w z v hz hw,mul_assoc]

def cubicError0_7 : Towers := addTowers
  (normalizeTower a0 a1 b0 32 (mulTowers monomialCubic7 kq0)) (negTowers cubic0_7)
theorem cubic_check0_7 : checkTowers cubicError0_7=true := by decide +kernel

theorem eval_cubic0_7 {R : Type*} [CommRing R]
    (φ : GaussianInt →+* R) (x : Fin 5 → R) (w z v : R)
    (hz : z^3=evalLayers φ x v a0+evalLayers φ x v a1*z)
    (hw : w^3=evalLayers φ x v b0-z^6) :
    evalTowers φ x w z v cubic0_7=evalTowers φ x w z v monomialCubic7 *
      evalTowers φ x w z v k * evalTowers φ x w z v q00 := by
  rw [evaluation_of_normal_error_check φ x w z v a0 a1 b0 hz hw 32
    (mulTowers monomialCubic7 kq0) cubic0_7 cubic_check0_7,
    eval_mulTowers,eval_kq0 φ x w z v hz hw,mul_assoc]

def cubicError0_8 : Towers := addTowers
  (normalizeTower a0 a1 b0 32 (mulTowers monomialCubic8 kq0)) (negTowers cubic0_8)
theorem cubic_check0_8 : checkTowers cubicError0_8=true := by decide +kernel

theorem eval_cubic0_8 {R : Type*} [CommRing R]
    (φ : GaussianInt →+* R) (x : Fin 5 → R) (w z v : R)
    (hz : z^3=evalLayers φ x v a0+evalLayers φ x v a1*z)
    (hw : w^3=evalLayers φ x v b0-z^6) :
    evalTowers φ x w z v cubic0_8=evalTowers φ x w z v monomialCubic8 *
      evalTowers φ x w z v k * evalTowers φ x w z v q00 := by
  rw [evaluation_of_normal_error_check φ x w z v a0 a1 b0 hz hw 32
    (mulTowers monomialCubic8 kq0) cubic0_8 cubic_check0_8,
    eval_mulTowers,eval_kq0 φ x w z v hz hw,mul_assoc]

end CycleQ2SegreModularCubicData
#print axioms CycleQ2SegreModularCubicData.eval_cubic0_8
end


