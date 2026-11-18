import HodgeComputer.Constructions.HoldoutCover.GenericIncidence
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.Derivation.MapCoeffs
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
The exact weighted-quartic incidence for reflection-coupled-fano.

There are twenty-four positive coefficient variables: degrees 1--4 in each
of six coordinates. The first five coordinates have weight one and degree
at most four. The final coordinate has weight two; its coefficients in
degrees 5--7 are fixed to zero and its coefficient in degree 8 is fixed
to one. The twenty-four equations are all positive coefficients of the
weighted degree-six defining equation, up to degree 24.

The deformation coefficient c is a parameter. The intended arithmetic
coefficient ring contains 1/7 and c=5/7; its reduction modulo five is c=0.
All incidence equations and Jacobian identities below commute with scalar
maps, so the modular computation concerns exactly this integral lift.

This file only gives the incidence identities. It does not assert that a
nonsingular seed exists and does not assert a Hodge certificate.
-/

noncomputable section

namespace ReflectionCoupledFano

open Polynomial

abbrev Index := Fin 6 × Fin 4
abbrev Coeff (R : Type*) [CommRing R] := MvPolynomial Index R
abbrev CurvePoly (R : Type*) [CommRing R] := Polynomial (Coeff R)

variable {R S : Type*} [CommRing R] [CommRing S]

/-- Exact reflection quotient, in coordinate order X0,X1,X2,Y0,Y1,u. -/
def H (c : R) (x : Fin 6 → R) : R :=
  x 0 ^ 6 + x 1 ^ 6 + x 2 ^ 6 + x 3 ^ 6 + x 4 ^ 6 + x 5 ^ 3 +
  c * (x 0 ^ 3 * x 1 * x 3 * x 4 +
    x 0 * x 1 * x 3 ^ 3 * x 4 + x 0 * x 1 * x 3 ^ 2 * x 5 +
    2 * x 0 * x 1 * x 4 ^ 2 * x 5 + 3 * x 0 * x 2 ^ 3 * x 3 * x 4 +
    2 * x 1 ^ 3 * x 2 * x 3 * x 4 + x 1 * x 2 * x 3 * x 4 ^ 3)

def phi (x : Fin 6 → R) (i : Fin 6) : CurvePoly R :=
  Polynomial.C (MvPolynomial.C (x i)) +
    ∑ j : Fin 4, Polynomial.C (MvPolynomial.X (i,j)) * Polynomial.X ^ (j.val + 1) +
    if i = 5 then Polynomial.X ^ 8 else 0

def systemPoly (c : R) (x : Fin 6 → R) : CurvePoly R :=
  H (Polynomial.C (MvPolynomial.C c)) (phi x)

def equationDegree (i : Index) : ℕ := 4 * i.1.val + i.2.val + 1

def equations (c : R) (x : Fin 6 → R) (i : Index) : Coeff R :=
  (systemPoly c x).coeff (equationDegree i)

@[simp] theorem equationDegree_pos (i : Index) : 0 < equationDegree i := by
  simp [equationDegree]

theorem equationDegree_le (i : Index) : equationDegree i ≤ 24 := by
  have h₁ := i.1.isLt
  have h₂ := i.2.isLt
  dsimp [equationDegree]
  omega

theorem equationDegree_covers {n : ℕ} (hn : 0 < n) (hn' : n ≤ 24) :
    ∃ i : Index, equationDegree i = n := by
  refine ⟨(⟨(n-1)/4, by omega⟩, ⟨(n-1)%4, Nat.mod_lt _ (by decide)⟩), ?_⟩
  dsimp [equationDegree]
  omega

@[simp] theorem phi_constant (x : Fin 6 → R) (i : Fin 6) :
    (phi x i).coeff 0 = MvPolynomial.C (x i) := by
  by_cases hi : i = 5 <;> simp [phi, Fin.sum_univ_succ, hi]

theorem systemPoly_constant (c : R) (x : Fin 6 → R) :
    (systemPoly c x).coeff 0 = MvPolynomial.C (H c x) := by
  change Polynomial.constantCoeff (systemPoly c x) = _
  simp only [systemPoly, H, map_add, map_mul, map_pow, map_ofNat,
    Polynomial.constantCoeff_apply, phi_constant, Polynomial.coeff_C_zero]

def valueCurve (x : Fin 6 → R) (v : Index → R) (i : Fin 6) : Polynomial R :=
  (phi x i).map (MvPolynomial.eval₂Hom (RingHom.id R) v)

theorem valueCurve_explicit (x : Fin 6 → R) (v : Index → R) (i : Fin 6) :
    valueCurve x v i = Polynomial.C (x i) +
      ∑ j : Fin 4, Polynomial.C (v (i,j)) * Polynomial.X ^ (j.val + 1) +
      if i = 5 then Polynomial.X ^ 8 else 0 := by
  by_cases hi : i = 5 <;> simp [valueCurve, phi, Fin.sum_univ_succ, hi]

@[simp] theorem valueCurve_constant (x : Fin 6 → R) (v : Index → R) (i : Fin 6) :
    (valueCurve x v i).coeff 0 = x i := by
  simp [valueCurve]

def gradient (c : R) (x : Fin 6 → R) : Fin 6 → R :=
  ![6*x 0^5 + c*(3*x 0^2*x 1*x 3*x 4 + x 1*x 3^3*x 4 +
      x 1*x 3^2*x 5 + 2*x 1*x 4^2*x 5 + 3*x 2^3*x 3*x 4),
    6*x 1^5 + c*(x 0^3*x 3*x 4 + x 0*x 3^3*x 4 + x 0*x 3^2*x 5 +
      2*x 0*x 4^2*x 5 + 6*x 1^2*x 2*x 3*x 4 + x 2*x 3*x 4^3),
    6*x 2^5 + c*(9*x 0*x 2^2*x 3*x 4 + 2*x 1^3*x 3*x 4 + x 1*x 3*x 4^3),
    6*x 3^5 + c*(x 0^3*x 1*x 4 + 3*x 0*x 1*x 3^2*x 4 + 2*x 0*x 1*x 3*x 5 +
      3*x 0*x 2^3*x 4 + 2*x 1^3*x 2*x 4 + x 1*x 2*x 4^3),
    6*x 4^5 + c*(x 0^3*x 1*x 3 + x 0*x 1*x 3^3 + 4*x 0*x 1*x 4*x 5 +
      3*x 0*x 2^3*x 3 + 2*x 1^3*x 2*x 3 + 3*x 1*x 2*x 3*x 4^2),
    3*x 5^2 + c*(x 0*x 1*x 3^2 + 2*x 0*x 1*x 4^2)]

def coefficientDeriv (i : Index) : Derivation R (CurvePoly R) (CurvePoly R) :=
  PolynomialModule.equivPolynomialSelf.compDer (MvPolynomial.pderiv i).mapCoeffs

@[simp] theorem coefficientDeriv_coeff (i : Index) (f : CurvePoly R) (n : ℕ) :
    (coefficientDeriv i f).coeff n = MvPolynomial.pderiv i (f.coeff n) := rfl

@[simp] theorem coefficientDeriv_C (i : Index) (f : Coeff R) :
    coefficientDeriv i (Polynomial.C f) = Polynomial.C (MvPolynomial.pderiv i f) := by
  ext n
  by_cases hn : n = 0 <;> simp [coefficientDeriv_coeff, Polynomial.coeff_C, hn]

@[simp] theorem coefficientDeriv_X (i : Index) :
    coefficientDeriv i (Polynomial.X : CurvePoly R) = 0 := by
  ext n
  simp [coefficientDeriv_coeff, Polynomial.coeff_X, apply_ite]

@[simp] theorem coefficientDeriv_two (i : Index) :
    coefficientDeriv i (2 : CurvePoly R) = 0 := by
  rw [show (2 : CurvePoly R) = 1+1 by norm_num]
  simp

@[simp] theorem coefficientDeriv_three (i : Index) :
    coefficientDeriv i (3 : CurvePoly R) = 0 := by
  rw [show (3 : CurvePoly R) = 1+1+1 by norm_num]
  simp

theorem phi_coefficientDeriv (x : Fin 6 → R) (j : Index) (i : Fin 6) :
    coefficientDeriv j (phi x i) =
      if i = j.1 then Polynomial.X ^ (j.2.val + 1) else 0 := by
  rcases j with ⟨j,k⟩
  fin_cases j <;> fin_cases k <;> fin_cases i <;>
    simp [phi, Fin.sum_univ_succ, Derivation.leibniz, Derivation.leibniz_pow,
      smul_eq_mul]

theorem systemPoly_coefficientDeriv (c : R) (x : Fin 6 → R) (j : Index) :
    coefficientDeriv j (systemPoly c x) =
      gradient (Polynomial.C (MvPolynomial.C c)) (phi x) j.1 *
        Polynomial.X ^ (j.2.val + 1) := by
  unfold systemPoly H
  simp only [map_add, map_sub, Derivation.leibniz, Derivation.leibniz_pow,
    coefficientDeriv_C, MvPolynomial.pderiv_C, Polynomial.C_0,
    coefficientDeriv_two, coefficientDeriv_three,
    mul_zero, add_zero, phi_coefficientDeriv, smul_eq_mul]
  rcases j with ⟨j,k⟩
  fin_cases j <;>
    simp [gradient, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] <;> ring

theorem equations_pderiv (c : R) (x : Fin 6 → R) (i j : Index) :
    MvPolynomial.pderiv j (equations c x i) =
      (gradient (Polynomial.C (MvPolynomial.C c)) (phi x) j.1 *
        Polynomial.X ^ (j.2.val + 1)).coeff (equationDegree i) := by
  rw [equations, ← coefficientDeriv_coeff, systemPoly_coefficientDeriv]

theorem phi_map (f : R →+* S) (x : Fin 6 → R) (i : Fin 6) :
    (phi x i).map (MvPolynomial.map f) = phi (fun i => f (x i)) i := by
  by_cases hi : i = 5 <;> simp [phi, Fin.sum_univ_succ, hi]

theorem systemPoly_map (f : R →+* S) (c : R) (x : Fin 6 → R) :
    (systemPoly c x).map (MvPolynomial.map f) =
      systemPoly (f c) (fun i => f (x i)) := by
  simp [systemPoly, H, phi_map]

theorem equations_map (f : R →+* S) (c : R) (x : Fin 6 → R) (i : Index) :
    MvPolynomial.map f (equations c x i) = equations (f c) (fun i => f (x i)) i := by
  rw [equations, ← Polynomial.coeff_map, systemPoly_map]
  rfl

theorem equations_pderiv_map (f : R →+* S) (c : R) (x : Fin 6 → R) (i j : Index) :
    MvPolynomial.map f (MvPolynomial.pderiv j (equations c x i)) =
      MvPolynomial.pderiv j (equations (f c) (fun i => f (x i)) i) := by
  rw [← MvPolynomial.pderiv_map, equations_map]

theorem phi_eval₂ (f : R →+* S) (x : Fin 6 → R) (v : Index → S) (i : Fin 6) :
    (phi x i).map (MvPolynomial.eval₂Hom f v) = valueCurve (fun i => f (x i)) v i := by
  rw [valueCurve_explicit]
  by_cases hi : i = 5 <;> simp [phi, Fin.sum_univ_succ, hi]

theorem systemPoly_eval₂ (f : R →+* S) (c : R) (x : Fin 6 → R) (v : Index → S) :
    (systemPoly c x).map (MvPolynomial.eval₂Hom f v) =
      H (Polynomial.C (f c)) (valueCurve (fun i => f (x i)) v) := by
  simp [systemPoly, H, phi_eval₂]

theorem equations_eval₂ (f : R →+* S) (c : R) (x : Fin 6 → R)
    (v : Index → S) (i : Index) :
    MvPolynomial.eval₂Hom f v (equations c x i) =
      (H (Polynomial.C (f c)) (valueCurve (fun i => f (x i)) v)).coeff
        (equationDegree i) := by
  rw [equations, ← Polynomial.coeff_map, systemPoly_eval₂]

theorem equations_pderiv_eval₂ (f : R →+* S) (c : R) (x : Fin 6 → R)
    (v : Index → S) (i j : Index) :
    MvPolynomial.eval₂Hom f v (MvPolynomial.pderiv j (equations c x i)) =
      (gradient (Polynomial.C (f c)) (valueCurve (fun i => f (x i)) v) j.1 *
        Polynomial.X ^ (j.2.val + 1)).coeff (equationDegree i) := by
  rw [equations_pderiv, ← Polynomial.coeff_map]
  congr 1
  rcases j with ⟨j,k⟩
  fin_cases j <;> simp [gradient, phi_eval₂,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]

theorem systemPoly_degree_le (c : R) (x : Fin 6 → R) :
    (systemPoly c x).natDegree ≤ 24 := by
  unfold systemPoly H phi
  simp only [Fin.sum_univ_succ]
  norm_num
  compute_degree

theorem coefficientDeriv_degree_le (j : Index) (f : CurvePoly R) (n : ℕ)
    (h : f.natDegree ≤ n) : (coefficientDeriv j f).natDegree ≤ n := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro m hm
  rw [coefficientDeriv_coeff,
    Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt h hm), map_zero]

theorem gradientVariation_degree_le (c : R) (x : Fin 6 → R)
    (v : Index → R) (j : Index) :
    (gradient (Polynomial.C c) (valueCurve x v) j.1 *
      Polynomial.X ^ (j.2.val + 1)).natDegree ≤ 24 := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro m hm
  have h := coefficientDeriv_degree_le j (systemPoly c x) 24 (systemPoly_degree_le c x)
  have hz := Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt h hm)
  rw [coefficientDeriv_coeff] at hz
  have hmapp := congrArg (MvPolynomial.eval₂Hom (RingHom.id R) v) hz
  rw [map_zero] at hmapp
  rw [← coefficientDeriv_coeff, systemPoly_coefficientDeriv] at hmapp
  rw [← Polynomial.coeff_map] at hmapp
  convert hmapp using 1
  rcases j with ⟨j,k⟩
  fin_cases j <;> simp [gradient, phi_eval₂,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]

theorem gradient_map (f : R →+* S) (c : R) (x : Fin 6 → R) (i : Fin 6) :
    f (gradient c x i) = gradient (f c) (fun i => f (x i)) i := by
  fin_cases i <;> simp [gradient, map_ofNat]

theorem gradient_constant (c : R) (x : Fin 6 → R) (v : Index → R) (i : Fin 6) :
    (gradient (Polynomial.C c) (valueCurve x v) i).coeff 0 = gradient c x i := by
  simpa only [Polynomial.constantCoeff_apply, Polynomial.coeff_C_zero,
    valueCurve_constant] using
      gradient_map (Polynomial.constantCoeff : Polynomial R →+* R)
        (Polynomial.C c) (valueCurve x v) i

theorem gradient_degree_le (c : R) (x : Fin 6 → R) (v : Index → R) (i : Fin 6) :
    (gradient (Polynomial.C c) (valueCurve x v) i).natDegree ≤ 24 := by
  have h := gradientVariation_degree_le c x v (i,0)
  change (gradient (Polynomial.C c) (valueCurve x v) i * Polynomial.X^1).natDegree ≤ 24 at h
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  have hz := Polynomial.coeff_eq_zero_of_natDegree_lt
    (lt_of_le_of_lt h (show 24 < n+1 by omega))
  simpa only [Polynomial.coeff_mul_X_pow] using hz

theorem eq_constant_of_positive_coefficients (f : Polynomial R)
    (hdegree : f.natDegree ≤ 24)
    (hpositive : ∀ i : Index, f.coeff (equationDegree i) = 0) :
    f = Polynomial.C (f.coeff 0) := by
  ext n
  by_cases hn : n = 0
  · subst n
    simp
  · rw [Polynomial.coeff_C, ite_eq_right hn]
    by_cases h24 : n ≤ 24
    · obtain ⟨i, hi⟩ := equationDegree_covers (Nat.pos_of_ne_zero hn) h24
      rw [← hi]
      exact hpositive i
    · exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)

theorem systemPoly_eq_constant (c : R) (x : Fin 6 → R)
    (h : ∀ i : Index, equations c x i = 0) :
    systemPoly c x = Polynomial.C (MvPolynomial.C (H c x)) := by
  rw [eq_constant_of_positive_coefficients _ (systemPoly_degree_le c x) h,
    systemPoly_constant]

end ReflectionCoupledFano

#print axioms ReflectionCoupledFano.equations_pderiv_eval₂
#print axioms ReflectionCoupledFano.systemPoly_eq_constant
