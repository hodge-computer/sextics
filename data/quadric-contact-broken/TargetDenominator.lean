import HodgeComputer.Verify

noncomputable section
namespace QuadricContactDenominator
open MvPolynomial HodgeComputer

/-- Variable order is the protected order X0,X1,X2,Y0,Y1,Y2. -/
def targetF : Poly :=
  X 0 ^ 6 + X 3 ^ 6 + 5 * X 0 ^ 4 * X 3 ^ 2 + 5 * X 0 ^ 2 * X 3 ^ 4 +
  5 * (X 0 ^ 2 + X 3 ^ 2) *
    (X 1 ^ 2 * X 4 ^ 2 + X 1 * X 2 * X 4 * X 5 + X 2 ^ 2 * X 5 ^ 2) +
  X 1 ^ 6 + X 4 ^ 6 + X 2 ^ 6 + X 5 ^ 6 +
  C (5 / 7 : ℂ) * X 0 * X 3 * X 1 * X 4 * (X 2 ^ 2 + 2 * X 5 ^ 2)

def toUni : Poly →+* Polynomial Coeff :=
  MvPolynomial.eval₂Hom (Polynomial.C.comp MvPolynomial.C)
    (fun i => if i.val = 0 then Polynomial.X
      else Polynomial.C (MvPolynomial.X ⟨i.val - 1, by omega⟩))

def fromUni : Polynomial Coeff →+* Poly :=
  Polynomial.eval₂RingHom
    (MvPolynomial.eval₂Hom MvPolynomial.C (fun i => MvPolynomial.X i.succ))
    (MvPolynomial.X 0)

@[simp] theorem toUni_X0 : toUni (X 0) = Polynomial.X := by
  simp only [toUni, MvPolynomial.eval₂Hom_X']; rfl
@[simp] theorem toUni_X1 : toUni (X 1) = Polynomial.C (X 0) := by
  simp only [toUni, MvPolynomial.eval₂Hom_X']; rfl
@[simp] theorem toUni_X2 : toUni (X 2) = Polynomial.C (X 1) := by
  simp only [toUni, MvPolynomial.eval₂Hom_X']; rfl
@[simp] theorem toUni_X3 : toUni (X 3) = Polynomial.C (X 2) := by
  simp only [toUni, MvPolynomial.eval₂Hom_X']; rfl
@[simp] theorem toUni_X4 : toUni (X 4) = Polynomial.C (X 3) := by
  simp only [toUni, MvPolynomial.eval₂Hom_X']; rfl
@[simp] theorem toUni_X5 : toUni (X 5) = Polynomial.C (X 4) := by
  simp only [toUni, MvPolynomial.eval₂Hom_X']; rfl
@[simp] theorem toUni_C (c : ℂ) : toUni (C c) = Polynomial.C (C c) := by
  simp [toUni]
@[simp] theorem fromUni_w (i : Fin 5) :
    fromUni (Polynomial.C (X i)) = X i.succ := by
  simp [fromUni]
@[simp] theorem fromUni_t : fromUni Polynomial.X = X 0 := by simp [fromUni]

theorem retract : fromUni.comp toUni = RingHom.id Poly := by
  apply MvPolynomial.ringHom_ext
  · intro c; simp [toUni, fromUni]
  · intro i; fin_cases i <;> simp

def fUni : Polynomial Coeff :=
  Polynomial.X ^ 6 + Polynomial.C (5 * X 2 ^ 2) * Polynomial.X ^ 4 +
  Polynomial.C (5 * X 2 ^ 4 + 5 *
    (X 0 ^ 2 * X 3 ^ 2 + X 0 * X 1 * X 3 * X 4 + X 1 ^ 2 * X 4 ^ 2)) *
      Polynomial.X ^ 2 +
  Polynomial.C (C (5 / 7 : ℂ) * X 2 * X 0 * X 3 * (X 1 ^ 2 + 2 * X 4 ^ 2)) *
      Polynomial.X ^ 1 +
  Polynomial.C (X 2 ^ 6 +
    5 * X 2 ^ 2 * (X 0 ^ 2 * X 3 ^ 2 + X 0 * X 1 * X 3 * X 4 + X 1 ^ 2 * X 4 ^ 2) +
    X 0 ^ 6 + X 3 ^ 6 + X 1 ^ 6 + X 4 ^ 6) * Polynomial.X ^ 0

theorem toUni_F : toUni targetF = fUni := by
  simp only [targetF, fUni, map_add, map_mul, map_pow, map_ofNat,
    toUni_C, toUni_X0, toUni_X1, toUni_X2, toUni_X3, toUni_X4, toUni_X5]
  polynomial

theorem fUni_degree : fUni.natDegree = 6 := by
  unfold fUni; compute_degree!

theorem fUni_lc : fUni.leadingCoeff = 1 := by
  rw [Polynomial.leadingCoeff, fUni_degree]
  simp only [fUni, Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_X_pow]
  norm_num

/-- Sets a=c=b=1,y=0,d=2 and leaves x=X0 as the univariate coordinate. -/
def point : Fin 5 → ℂ := fun i => if i.val = 2 then 0 else if i.val = 4 then 2 else 1
def specialize : Coeff →+* ℂ := MvPolynomial.eval point

def fFiber : Polynomial ℂ := Polynomial.X ^ 6 + 35 * Polynomial.X ^ 2 + 67

theorem fiber_F : (toUni targetF).map specialize = fFiber := by
  rw [toUni_F]
  norm_num [fUni, specialize, point, fFiber] <;> polynomial

/-- All geometric complications of denominator pullback reduce to this one
univariate coprimality check. No irreducibility/smoothness of F is needed. -/
theorem denominator_legal (D : Poly)
    (h : IsRelPrime fFiber ((toUni D).map specialize)) : IsRelPrime targetF D := by
  apply HodgeComputer.relPrime_of_retract toUni fromUni retract
  apply HodgeComputer.relPrime_of_specialization specialize
  · rw [toUni_F, fUni_lc]
    exact isUnit_one
  · rw [fiber_F]
    exact h

theorem fFiber_degree : fFiber.natDegree = 6 := by
  unfold fFiber
  compute_degree!

theorem targetF_not_isUnit : ¬ IsUnit targetF := by
  intro h
  have hu := (h.map toUni).map (Polynomial.mapRingHom specialize)
  change IsUnit ((toUni targetF).map specialize) at hu
  rw [fiber_F] at hu
  have hd := Polynomial.natDegree_eq_zero_of_isUnit hu
  rw [fFiber_degree] at hd
  omega

/-- A legal denominator cannot vanish, since the protected F is not a unit. -/
theorem denominator_ne_zero_of_legal (D : Poly) (h : IsRelPrime targetF D) : D ≠ 0 := by
  intro hz
  apply targetF_not_isUnit
  exact h dvd_rfl (by rw [hz]; exact dvd_zero targetF)

end QuadricContactDenominator

#print axioms QuadricContactDenominator.denominator_legal
