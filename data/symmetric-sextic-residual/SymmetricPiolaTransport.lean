import HodgeComputer.Constructions.ResidueTransport.PiolaContraction
import HodgeComputer.Constructions.ResidueTransport.CoordinateIndependence
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination

/-!
# Normalized currents in the actual reflection chart

The chart is `(a,lambda,b,c,d,v) ↦
a*(1+v,1-v,b,c+lambda*v,c-lambda*v,d)`.
Its inverse Jacobian and the pushed-forward current are explicit below.
The input current has zero radial component. Its other five components
must be divided by `4*v`, not by the full six-dimensional Jacobian.

The final theorem transports both normalized equations. It is a field
identity, not an existence theorem: it does not supply a relative primitive
or the regular-local-ring map needed to clear this chart on the protected
projective hypersurface.
-/

noncomputable section

namespace SymmetricPiolaTransport

open HoldoutConstruction
open scoped BigOperators

variable {K : Type*} [Field K] [CharZero K]

set_option maxHeartbeats 2000000

def jacobian (a lam b c d v : K) : Matrix (Fin 6) (Fin 6) K :=
  !![1+v, 0, 0, 0, 0, a;
     1-v, 0, 0, 0, 0, -a;
     b, 0, a, 0, 0, 0;
     c+lam*v, a*v, 0, a, 0, a*lam;
     c-lam*v, -a*v, 0, a, 0, -a*lam;
     d, 0, 0, 0, a, 0]

/-- Rows differentiate `(a,lambda,b,c,d,v)` with respect to the six original
coordinates, in their original order. -/
def inverseJacobian (a lam b c d v : K) : Matrix (Fin 6) (Fin 6) K :=
  !![1/2, 1/2, 0, 0, 0, 0;
     -lam/(2*a*v), lam/(2*a*v), 0, 1/(2*a*v), -1/(2*a*v), 0;
     -b/(2*a), -b/(2*a), 1/a, 0, 0, 0;
     -c/(2*a), -c/(2*a), 0, 1/(2*a), 1/(2*a), 0;
     -d/(2*a), -d/(2*a), 0, 0, 0, 1/a;
     (1-v)/(2*a), -(1+v)/(2*a), 0, 0, 0, 0]

theorem jacobian_det (a lam b c d v : K) :
    (jacobian a lam b c d v).det = 4*a^5*v := by
  simp [jacobian, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Matrix.submatrix]
  dsimp [Fin.succAbove, Matrix.vecCons, Fin.cons, Fin.cases,
    Fin.induction, Fin.induction.go]
  ring

theorem jacobian_mul_inverse (a lam b c d v : K) (ha : a ≠ 0) (hv : v ≠ 0) :
    jacobian a lam b c d v * inverseJacobian a lam b c d v = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [jacobian, inverseJacobian, Matrix.mul_apply, Fin.sum_univ_succ,
      Matrix.one_apply] <;> field_simp <;> ring

theorem inverse_mul_jacobian (a lam b c d v : K) (ha : a ≠ 0) (hv : v ≠ 0) :
    inverseJacobian a lam b c d v * jacobian a lam b c d v = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [jacobian, inverseJacobian, Matrix.mul_apply, Fin.sum_univ_succ,
      Matrix.one_apply] <;> field_simp <;> ring

/-- The inverse Jacobian defines the original coordinate derivations. -/
def physicalDerivative (D : Fin 6 → Derivation ℤ K K)
    (a lam b c d v : K) (j : Fin 6) : Derivation ℤ K K :=
  ∑ k, inverseJacobian a lam b c d v k j • D k

theorem physicalDerivative_apply (D : Fin 6 → Derivation ℤ K K)
    (a lam b c d v : K) (j : Fin 6) (z : K) :
    physicalDerivative D a lam b c d v j z =
      ∑ k, inverseJacobian a lam b c d v k j * D k z := by
  change Derivation.coeFnAddMonoidHom
    (∑ k, inverseJacobian a lam b c d v k j • D k) z = _
  rw [map_sum]
  simp only [Finset.sum_apply, Derivation.coeFnAddMonoidHom_apply,
    Derivation.smul_apply, smul_eq_mul]

theorem jacobian_mixed (D : Fin 6 → Derivation ℤ K K) (x : Fin 6 → K)
    (hx : ∀ i j, D i (x j) = if i = j then 1 else 0) (i j k : Fin 6) :
    D k (jacobian (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) j i) =
      D i (jacobian (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) j k) := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp [jacobian, Derivation.leibniz, smul_eq_mul, hx]

def chartCoordinates (x : Fin 6 → K) : Fin 6 → K :=
  ![x 0*(1+x 5), x 0*(1-x 5), x 0*x 2,
    x 0*(x 3+x 1*x 5), x 0*(x 3-x 1*x 5), x 0*x 4]

theorem chartCoordinates_derivative (D : Fin 6 → Derivation ℤ K K)
    (x : Fin 6 → K) (hx : ∀ i j, D i (x j) = if i = j then 1 else 0)
    (i j : Fin 6) :
    D i (chartCoordinates x j) =
      jacobian (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) j i := by
  fin_cases i <;> fin_cases j <;>
    simp [chartCoordinates, jacobian, Derivation.leibniz, smul_eq_mul, hx] <;> ring

/-- The transported derivations really differentiate the original coordinates. -/
theorem physicalDerivative_coordinate (D : Fin 6 → Derivation ℤ K K)
    (x : Fin 6 → K) (hx : ∀ i j, D i (x j) = if i = j then 1 else 0)
    (ha : x 0 ≠ 0) (hv : x 5 ≠ 0) (i j : Fin 6) :
    physicalDerivative D (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) i
      (chartCoordinates x j) = if j = i then 1 else 0 := by
  rw [physicalDerivative_apply]
  simp_rw [chartCoordinates_derivative D x hx]
  have h := congrArg (fun M : Matrix (Fin 6) (Fin 6) K => M j i)
    (jacobian_mul_inverse (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) ha hv)
  simpa only [Matrix.mul_apply, Matrix.one_apply, mul_comm] using h

/-- Original-coordinate polynomial evaluation is injective. The hypothesis
on constants is satisfied by the canonical chart partial derivatives. -/
theorem physicalPolynomialMap_injective {k : Type*} [Field k] [CharZero k]
    (φ : k →+* K) (D : Fin 6 → Derivation ℤ K K) (x : Fin 6 → K)
    (hC : ∀ i c, D i (φ c) = 0)
    (hx : ∀ i j, D i (x j) = if i = j then 1 else 0)
    (ha : x 0 ≠ 0) (hv : x 5 ≠ 0) :
    Function.Injective (MvPolynomial.eval₂Hom φ (chartCoordinates x)) := by
  apply ResidueCoordinateIndependence.injective_of_coordinate_derivations
    φ (chartCoordinates x)
    (physicalDerivative D (x 0) (x 1) (x 2) (x 3) (x 4) (x 5))
  · intro i c
    simp only [physicalDerivative_apply, hC, mul_zero, Finset.sum_const_zero]
  · exact physicalDerivative_coordinate D x hx ha hv

theorem physicalPolynomialMap_compatible {k : Type*} [CommRing k]
    (φ : k →+* K) (D : Fin 6 → Derivation ℤ K K) (x : Fin 6 → K)
    (hC : ∀ i c, D i (φ c) = 0)
    (hx : ∀ i j, D i (x j) = if i = j then 1 else 0)
    (ha : x 0 ≠ 0) (hv : x 5 ≠ 0)
    (i : Fin 6) (p : MvPolynomial (Fin 6) k) :
    physicalDerivative D (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) i
      (MvPolynomial.eval₂Hom φ (chartCoordinates x) p) =
      MvPolynomial.eval₂Hom φ (chartCoordinates x) (MvPolynomial.pderiv i p) := by
  have hc : ∀ c, physicalDerivative D (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) i
      (φ c) = 0 := by
    intro c
    simp only [physicalDerivative_apply, hC, mul_zero, Finset.sum_const_zero]
  rw [derivation_eval₂_chain _ φ (chartCoordinates x) hc p]
  simp [physicalDerivative_coordinate D x hx ha hv]

/-- Input for the six-dimensional Piola formula: the factor `a^5` cancels
the radial part of the Jacobian, and the radial component is zero. -/
def volumeCurrent (a : K) (w : Fin 5 → K) : Fin 6 → K :=
  Fin.cases 0 (fun i => a^5*w i)

/-- The six original-coordinate components of the transported current.
The five entries of `w` are ordered `(lambda,b,c,d,v)`. -/
def physicalCurrent (a lam v : K) (w : Fin 5 → K) : Fin 6 → K :=
  ![a*w 4/(4*v), -a*w 4/(4*v), a*w 1/(4*v),
    a*(v*w 0+w 2+lam*w 4)/(4*v),
    a*(-v*w 0+w 2-lam*w 4)/(4*v), a*w 3/(4*v)]

theorem physicalCurrent_eq_piola (a lam b c d v : K) (w : Fin 5 → K)
    (ha : a ≠ 0) (hv : v ≠ 0) :
    physicalCurrent a lam v w = fun j =>
      ∑ i, (volumeCurrent a w i / (jacobian a lam b c d v).det) *
        jacobian a lam b c d v j i := by
  rw [jacobian_det]
  funext j
  fin_cases j <;>
    simp [physicalCurrent, volumeCurrent, jacobian, Fin.sum_univ_succ] <;>
    field_simp <;> ring

theorem volumeCurrent_divergence (D : Fin 6 → Derivation ℤ K K)
    (a : K) (w : Fin 5 → K) (ha : ∀ i : Fin 5, D i.succ a = 0) :
    fieldDivergence D (volumeCurrent a w) =
      a^5 * ∑ i : Fin 5, D i.succ (w i) := by
  rw [fieldDivergence, Fin.sum_univ_succ]
  simp [volumeCurrent, Derivation.leibniz, Derivation.leibniz_pow,
    ha, smul_eq_mul, Finset.mul_sum]

theorem volumeCurrent_contraction (D : Fin 6 → Derivation ℤ K K)
    (a H : K) (w : Fin 5 → K) (ha : ∀ i : Fin 5, D i.succ a = 0) :
    (∑ i, volumeCurrent a w i * D i (a^6*H)) =
      a^11 * ∑ i : Fin 5, w i * D i.succ H := by
  rw [Fin.sum_univ_succ]
  simp only [volumeCurrent, Fin.cases_zero, zero_mul, Fin.cases_succ,
    Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul, ha,
    mul_zero, zero_mul, add_zero, zero_add, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Both normalized equations transport on the actual reflection chart.
There is no Euler correction and no additional pole along the equation.
Regularity of the rational chart coordinates is a separate algebraic step. -/
theorem normalized_current_transport
    (D : Fin 6 → Derivation ℤ K K) (x : Fin 6 → K)
    (hx : ∀ i j, D i (x j) = if i = j then 1 else 0)
    (ha : x 0 ≠ 0) (hv : x 5 ≠ 0)
    (H AH r : K) (w : Fin 5 → K)
    (hnormal : (∑ i : Fin 5, w i * D i.succ H) = AH)
    (hdiv : (∑ i : Fin 5, D i.succ (w i)) = H*r) :
    let E := physicalDerivative D (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)
    let V := physicalCurrent (x 0) (x 1) (x 5) w
    (∑ j, V j * E j ((x 0)^6*H)) = (x 0)^6*AH/(4*x 5) ∧
      fieldDivergence E V = ((x 0)^6*H)*(r/(4*(x 0)^6*x 5)) := by
  dsimp only
  have hradial : ∀ i : Fin 5, D i.succ (x 0) = 0 := by
    intro i
    simp [hx]
  have hdet : (jacobian (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)).det ≠ 0 := by
    rw [jacobian_det]
    exact mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ ha)) hv
  rw [physicalCurrent_eq_piola (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) w ha hv]
  constructor
  · rw [piola_contraction D _ _ _
      (inverse_mul_jacobian _ _ _ _ _ _ ha hv)
      (physicalDerivative_apply D _ _ _ _ _ _),
      volumeCurrent_contraction D _ _ _ hradial, hnormal, jacobian_det]
    field_simp
    <;> ring
  · rw [piola_divergence D _ _ _
      (jacobian_mul_inverse _ _ _ _ _ _ ha hv)
      (inverse_mul_jacobian _ _ _ _ _ _ ha hv) hdet
      (physicalDerivative_apply D _ _ _ _ _ _)
      (jacobian_mixed D x hx),
      volumeCurrent_divergence D _ _ hradial, hdiv, jacobian_det]
    field_simp
    <;> ring

#print axioms jacobian_mul_inverse
#print axioms inverse_mul_jacobian
#print axioms normalized_current_transport

end SymmetricPiolaTransport
