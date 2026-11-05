import HodgeComputer.Verify
import Proposal.HoldoutAlgebra
import Proposal.MatrixBezout

/-! Denominator legality for the endpoint reduction. The leading coefficient
argument is reused from the accepted quadric-contact proof. The only geometric
input here is the exact specialization `F ↦ c^6+5`; no irreducibility assertion
or generic smoothness assumption is needed. -/

noncomputable section
namespace HoldoutDenominator
open MvPolynomial HodgeComputer

/-- Protected variable order: `(x,a,c,y,b,d)`. -/
def targetF : Poly :=
  HoldoutAlgebra.sextic (X 0) (X 1) (X 2) (X 3) (X 4) (X 5)

/-- Regard `c=X2` as the univariate coordinate; coefficient order is
`(x,a,y,b,d)`. -/
def toUni : Poly →+* Polynomial Coeff :=
  MvPolynomial.eval₂Hom (Polynomial.C.comp MvPolynomial.C)
    ![Polynomial.C (X 0), Polynomial.C (X 1), Polynomial.X,
      Polynomial.C (X 2), Polynomial.C (X 3), Polynomial.C (X 4)]

def fromUni : Polynomial Coeff →+* Poly :=
  Polynomial.eval₂RingHom
    (MvPolynomial.eval₂Hom MvPolynomial.C ![X 0, X 1, X 3, X 4, X 5]) (X 2)

@[simp] theorem toUni_X0 : toUni (X 0) = Polynomial.C (X 0) := by simp [toUni]
@[simp] theorem toUni_X1 : toUni (X 1) = Polynomial.C (X 1) := by simp [toUni]
@[simp] theorem toUni_X2 : toUni (X 2) = Polynomial.X := by simp [toUni]
@[simp] theorem toUni_X3 : toUni (X 3) = Polynomial.C (X 2) := by simp [toUni]
@[simp] theorem toUni_X4 : toUni (X 4) = Polynomial.C (X 3) := by simp [toUni]
@[simp] theorem toUni_X5 : toUni (X 5) = Polynomial.C (X 4) := by simp [toUni]
@[simp] theorem toUni_C (c : ℂ) : toUni (C c) = Polynomial.C (C c) := by simp [toUni]

@[simp] theorem fromUni_t : fromUni Polynomial.X = X 2 := by simp [fromUni]

theorem retract : fromUni.comp toUni = RingHom.id Poly := by
  apply MvPolynomial.ringHom_ext
  · intro c; simp [toUni, fromUni]
  · intro i; fin_cases i <;> simp [toUni, fromUni]

def fUni : Polynomial Coeff :=
  Polynomial.X ^ 6 +
  Polynomial.C (X 1 ^ 3 * X 3 * X 4) * Polynomial.X ^ 1 +
  Polynomial.C (X 0 ^ 6 + X 1 ^ 6 + X 2 ^ 6 + X 3 ^ 6 + X 4 ^ 6 +
    X 0 ^ 3 * X 1 * X 2 * X 3) * Polynomial.X ^ 0

theorem toUni_F : toUni targetF = fUni := by
  simp only [targetF, HoldoutAlgebra.sextic, fUni, map_add, map_mul, map_pow,
    toUni_X0, toUni_X1, toUni_X2, toUni_X3, toUni_X4, toUni_X5]
  polynomial

theorem fUni_degree : fUni.natDegree = 6 := by
  unfold fUni
  compute_degree!

theorem fUni_lc : fUni.leadingCoeff = 1 := by
  rw [Polynomial.leadingCoeff, fUni_degree]
  simp only [fUni, Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow,
    Polynomial.coeff_X_pow]
  norm_num

def point (k : ℂ) : Fin 5 → ℂ := ![1, 1, k^2, k, 0]
def specialize (k : ℂ) : Coeff →+* ℂ := MvPolynomial.eval (point k)

def fiberValues (k : ℂ) : Fin 6 → Polynomial ℂ :=
  ![1, 1, Polynomial.X, Polynomial.C (k^2), Polynomial.C k, 0]

def fiber (k : ℂ) : Poly →+* Polynomial ℂ :=
  MvPolynomial.eval₂Hom Polynomial.C (fiberValues k)

def fFiber : Polynomial ℂ := Polynomial.X ^ 6 + 5

@[simp] theorem fiber_C (k r : ℂ) : fiber k (C r) = Polynomial.C r := by simp [fiber]
@[simp] theorem fiber_X (k : ℂ) (i : Fin 6) : fiber k (X i) = fiberValues k i := by
  simp [fiber]

/-- Identifies direct substitution with coefficient specialization of the
univariate polynomial used by `relPrime_of_specialization`. -/
theorem fiber_eq_specialization (k : ℂ) (P : Poly) :
    fiber k P = (toUni P).map (specialize k) := by
  have h : fiber k = (Polynomial.mapRingHom (specialize k)).comp toUni := by
    apply MvPolynomial.ringHom_ext
    · intro c; simp [fiber, toUni, specialize]
    · intro i; fin_cases i <;> simp [fiber, fiberValues, toUni, specialize, point]
  exact congrArg (fun φ : Poly →+* Polynomial ℂ => φ P) h

theorem fiber_F {k : ℂ} (hk : k^2+k+1=0) : fiber k targetF = fFiber := by
  have hk' : (Polynomial.C k)^2 + Polynomial.C k + 1 = 0 := by
    simpa only [map_add, map_pow, map_one, map_zero] using congrArg Polynomial.C hk
  simpa [fiber, fiberValues, targetF, HoldoutAlgebra.sextic, fFiber] using
    HoldoutAlgebra.sextic_good_fiber hk' (Polynomial.X : Polynomial ℂ)

theorem specialized_F {k : ℂ} (hk : k^2+k+1=0) :
    (toUni targetF).map (specialize k) = fFiber := by
  rw [← fiber_eq_specialization, fiber_F hk]

/-- A single univariate fiber proves legality of the full multivariate
polynomial denominator. -/
theorem denominator_legal {k : ℂ} (hk : k^2+k+1=0) (D : Poly)
    (h : IsRelPrime fFiber (fiber k D)) : IsRelPrime targetF D := by
  apply HodgeComputer.relPrime_of_retract toUni fromUni retract
  apply HodgeComputer.relPrime_of_specialization (specialize k)
  · rw [toUni_F, fUni_lc]
    exact isUnit_one
  · rw [specialized_F hk, ← fiber_eq_specialization]
    exact h

theorem fFiber_degree : fFiber.natDegree = 6 := by
  unfold fFiber
  compute_degree!

theorem targetF_not_isUnit : ¬ IsUnit targetF := by
  intro h
  have hu := h.map toUni
  have hd := Polynomial.natDegree_eq_zero_of_isUnit hu
  rw [toUni_F, fUni_degree] at hd
  omega

theorem denominator_ne_zero_of_legal (D : Poly) (h : IsRelPrime targetF D) : D ≠ 0 := by
  intro hz
  apply targetF_not_isUnit
  exact h dvd_rfl (by rw [hz]; exact dvd_zero targetF)

section Matrix
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Norm denominator on the fiber `U=V=1`, `S=c²`, `T=0`,
with `M=Me+Mf`. -/
def normFiber (M : Matrix n n ℂ) : Polynomial ℂ :=
  ((Polynomial.X ^ 2 : Polynomial ℂ) • (1 : Matrix n n (Polynomial ℂ)) -
    M.map Polynomial.C).det

/-- Invertibility of the cubic evaluated at `Me+Mf` proves legality of the
norm denominator, without expanding its degree-54 determinant. -/
theorem normFiber_legal (M K : Matrix n n ℂ)
    (hK : (M^3 + (5 : ℂ) • (1 : Matrix n n ℂ)) * K = 1) :
    IsRelPrime fFiber (normFiber M) := by
  have hm : ((M.map Polynomial.C)^3 + (0 : Polynomial ℂ) • M.map Polynomial.C +
      (5 : Polynomial ℂ) • (1 : Matrix n n (Polynomial ℂ))) *
      K.map Polynomial.C = 1 := by
    have hh := congrArg ((Polynomial.C : ℂ →+* Polynomial ℂ).mapMatrix) hK
    have hfive : (Polynomial.C : ℂ →+* Polynomial ℂ).mapMatrix
        ((5 : ℂ) • (1 : Matrix n n ℂ)) =
        (5 : Polynomial ℂ) • (1 : Matrix n n (Polynomial ℂ)) := by
      ext i j : 2
      by_cases hij : i = j <;>
        simp [Matrix.smul_apply, hij, Polynomial.C_ofNat]
    simp only [map_mul, map_add, map_pow, map_one, hfive,
      RingHom.mapMatrix_apply] at hh
    simpa only [zero_smul, add_zero] using hh
  have hh := QuadricContactMatrixBezout.relPrime_cubic_det
    (Polynomial.X ^ 2 : Polynomial ℂ) 0 5 (M.map Polynomial.C) (K.map Polynomial.C) hm
  simpa [fFiber, normFiber, ← pow_mul] using hh

/-- Complete multivariate denominator check once the fiber of the constructed
polynomial is identified with the norm pencil. -/
theorem denominator_legal_of_normFiber {k : ℂ} (hk : k^2+k+1=0)
    (D : Poly) (M K : Matrix n n ℂ)
    (hK : (M^3 + (5 : ℂ) • (1 : Matrix n n ℂ)) * K = 1)
    (hD : fiber k D = normFiber M) : IsRelPrime targetF D := by
  apply denominator_legal hk D
  rw [hD]
  exact normFiber_legal M K hK

/-- Homogeneous clearing may multiply the norm by a nonzero constant on the
chosen fiber; such a factor preserves legality. -/
theorem denominator_legal_of_scaled_normFiber {k : ℂ} (hk : k^2+k+1=0)
    (D : Poly) (M K : Matrix n n ℂ) (u : ℂ) (hu : u ≠ 0)
    (hK : (M^3 + (5 : ℂ) • (1 : Matrix n n ℂ)) * K = 1)
    (hD : fiber k D = Polynomial.C u * normFiber M) : IsRelPrime targetF D := by
  apply denominator_legal hk D
  rw [hD]
  have hu' : IsUnit (Polynomial.C u : Polynomial ℂ) :=
    (isUnit_iff_ne_zero.mpr hu).map Polynomial.C
  exact hu'.isRelPrime_right.mul_right (normFiber_legal M K hK)

end Matrix
end HoldoutDenominator

#print axioms HoldoutDenominator.denominator_legal
#print axioms HoldoutDenominator.normFiber_legal
