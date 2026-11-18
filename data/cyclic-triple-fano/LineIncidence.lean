import HodgeComputer.Constructions.HoldoutCover.GenericIncidence
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.Derivation.MapCoeffs
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
Weighted-line incidence for the cyclic triple-cover quotient, in order
Y0,Y1,X0,X1,Y2,Z. The seed curve is due to rbajaj5 (discussion #112).
The incidence, normal, and descent architecture is adapted from fqlx's reflection-coupled-fano proof.
This module fixes six positive coefficients, with Y1 advancing at unit speed.
-/

noncomputable section

namespace CyclicTriple

open Polynomial

abbrev Index := Fin 6
abbrev Coeff (R : Type*) [CommRing R] := MvPolynomial Index R
abbrev CurvePoly (R : Type*) [CommRing R] := Polynomial (Coeff R)

variable {R S : Type*} [CommRing R] [CommRing S]

def H (c : R) (x : Fin 6 → R) : R :=
  x 0^6 + x 1^6 + x 2^6 + x 3^6 + x 4^6 + x 5^2 +
  c * (x 2^3*x 3*x 0*x 1 + x 2^3*x 5 + x 2^2*x 0*x 1*x 4^2 +
    x 2*x 3*x 1^3*x 4 + x 2*x 5*x 1*x 4 + x 3*x 5*x 0*x 1)

def variationCoordinate : Index → Fin 6 := ![0,2,4,5,5,5]
def variationDegree : Index → ℕ := ![1,1,1,1,2,3]

def phi (x : Fin 6 → R) (i : Fin 6) : CurvePoly R :=
  ![C (MvPolynomial.C (x 0)) + C (MvPolynomial.X 0)*X,
    C (MvPolynomial.C (x 1)) + X,
    C (MvPolynomial.C (x 2)) + C (MvPolynomial.X 1)*X,
    C (MvPolynomial.C (x 3)),
    C (MvPolynomial.C (x 4)) + C (MvPolynomial.X 2)*X,
    C (MvPolynomial.C (x 5)) + C (MvPolynomial.X 3)*X +
      C (MvPolynomial.X 4)*X^2 + C (MvPolynomial.X 5)*X^3] i

def systemPoly (c : R) (x : Fin 6 → R) : CurvePoly R :=
  H (Polynomial.C (MvPolynomial.C c)) (phi x)

def equationDegree (i : Index) : ℕ := i.val + 1

def equations (c : R) (x : Fin 6 → R) (i : Index) : Coeff R :=
  (systemPoly c x).coeff (equationDegree i)

@[simp] theorem equationDegree_pos (i : Index) : 0 < equationDegree i := by
  simp [equationDegree]

theorem equationDegree_le (i : Index) : equationDegree i ≤ 6 := by
  have h₁ := i.isLt
  dsimp [equationDegree]
  omega

theorem equationDegree_covers {n : ℕ} (hn : 0 < n) (hn' : n ≤ 6) :
    ∃ i : Index, equationDegree i = n := by
  refine ⟨⟨n-1, by omega⟩, ?_⟩
  dsimp [equationDegree]
  omega

@[simp] theorem phi_constant (x : Fin 6 → R) (i : Fin 6) :
    (phi x i).coeff 0 = MvPolynomial.C (x i) := by
  fin_cases i <;> simp [phi]

theorem systemPoly_constant (c : R) (x : Fin 6 → R) :
    (systemPoly c x).coeff 0 = MvPolynomial.C (H c x) := by
  change Polynomial.constantCoeff (systemPoly c x) = _
  simp only [systemPoly, H, map_add, map_mul, map_pow, map_ofNat,
    Polynomial.constantCoeff_apply, phi_constant, Polynomial.coeff_C_zero]

def valueCurve (x : Fin 6 → R) (v : Index → R) (i : Fin 6) : Polynomial R :=
  (phi x i).map (MvPolynomial.eval₂Hom (RingHom.id R) v)

theorem valueCurve_explicit (x : Fin 6 → R) (v : Index → R) (i : Fin 6) :
    valueCurve x v i =
      ![C (x 0)+C (v 0)*X, C (x 1)+X, C (x 2)+C (v 1)*X,
        C (x 3), C (x 4)+C (v 2)*X,
        C (x 5)+C (v 3)*X+C (v 4)*X^2+C (v 5)*X^3] i := by
  fin_cases i <;> simp [valueCurve, phi]

@[simp] theorem valueCurve_constant (x : Fin 6 → R) (v : Index → R) (i : Fin 6) :
    (valueCurve x v i).coeff 0 = x i := by
  simp [valueCurve]

def gradient (c : R) (x : Fin 6 → R) : Fin 6 → R :=
  ![c*(x 1*x 2^3*x 3 + x 1*x 2^2*x 4^2 + x 1*x 3*x 5) + 6*x 0^5,
    c*(x 0*x 2^3*x 3 + x 0*x 2^2*x 4^2 + x 0*x 3*x 5 + 3*x 1^2*x 2*x 3*x 4 + x 2*x 4*x 5) + 6*x 1^5,
    c*(3*x 0*x 1*x 2^2*x 3 + 2*x 0*x 1*x 2*x 4^2 + x 1^3*x 3*x 4 + x 1*x 4*x 5 + 3*x 2^2*x 5) + 6*x 2^5,
    c*(x 0*x 1*x 2^3 + x 0*x 1*x 5 + x 1^3*x 2*x 4) + 6*x 3^5,
    c*(2*x 0*x 1*x 2^2*x 4 + x 1^3*x 2*x 3 + x 1*x 2*x 5) + 6*x 4^5,
    c*(x 0*x 1*x 3 + x 1*x 2*x 4 + x 2^3) + 2*x 5]

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
      if i = variationCoordinate j then Polynomial.X ^ (variationDegree j) else 0 := by
  fin_cases j <;> fin_cases i <;>
    simp [phi, variationCoordinate, variationDegree, Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul]

theorem systemPoly_coefficientDeriv (c : R) (x : Fin 6 → R) (j : Index) :
    coefficientDeriv j (systemPoly c x) =
      gradient (Polynomial.C (MvPolynomial.C c)) (phi x) (variationCoordinate j) *
        Polynomial.X ^ (variationDegree j) := by
  unfold systemPoly H
  simp only [map_add, map_sub, Derivation.leibniz, Derivation.leibniz_pow,
    coefficientDeriv_C, MvPolynomial.pderiv_C, Polynomial.C_0,
    coefficientDeriv_two, coefficientDeriv_three,
    mul_zero, add_zero, phi_coefficientDeriv, smul_eq_mul]
  fin_cases j <;>
    simp [gradient, variationCoordinate, variationDegree, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] <;> ring

theorem equations_pderiv (c : R) (x : Fin 6 → R) (i j : Index) :
    MvPolynomial.pderiv j (equations c x i) =
      (gradient (Polynomial.C (MvPolynomial.C c)) (phi x) (variationCoordinate j) *
        Polynomial.X ^ (variationDegree j)).coeff (equationDegree i) := by
  rw [equations, ← coefficientDeriv_coeff, systemPoly_coefficientDeriv]

theorem phi_map (f : R →+* S) (x : Fin 6 → R) (i : Fin 6) :
    (phi x i).map (MvPolynomial.map f) = phi (fun i => f (x i)) i := by
  fin_cases i <;> simp [phi]

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
  fin_cases i <;> simp [phi]

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
      (gradient (Polynomial.C (f c)) (valueCurve (fun i => f (x i)) v) (variationCoordinate j) *
        Polynomial.X ^ (variationDegree j)).coeff (equationDegree i) := by
  rw [equations_pderiv, ← Polynomial.coeff_map]
  congr 1
  fin_cases j <;> simp [gradient, variationCoordinate, variationDegree, phi_eval₂,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]

theorem systemPoly_degree_le (c : R) (x : Fin 6 → R) :
    (systemPoly c x).natDegree ≤ 6 := by
  unfold systemPoly H phi
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Matrix.head_cons, Matrix.tail_cons]
  compute_degree

theorem coefficientDeriv_degree_le (j : Index) (f : CurvePoly R) (n : ℕ)
    (h : f.natDegree ≤ n) : (coefficientDeriv j f).natDegree ≤ n := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro m hm
  rw [coefficientDeriv_coeff,
    Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt h hm), map_zero]

theorem gradientVariation_degree_le (c : R) (x : Fin 6 → R)
    (v : Index → R) (j : Index) :
    (gradient (Polynomial.C c) (valueCurve x v) (variationCoordinate j) *
      Polynomial.X ^ (variationDegree j)).natDegree ≤ 6 := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro m hm
  have h := coefficientDeriv_degree_le j (systemPoly c x) 6 (systemPoly_degree_le c x)
  have hz := Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt h hm)
  rw [coefficientDeriv_coeff] at hz
  have hmapp := congrArg (MvPolynomial.eval₂Hom (RingHom.id R) v) hz
  rw [map_zero] at hmapp
  rw [← coefficientDeriv_coeff, systemPoly_coefficientDeriv] at hmapp
  rw [← Polynomial.coeff_map] at hmapp
  convert hmapp using 1
  fin_cases j <;> simp [gradient, variationCoordinate, variationDegree, phi_eval₂,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]

theorem gradient_map (f : R →+* S) (c : R) (x : Fin 6 → R) (i : Fin 6) :
    f (gradient c x i) = gradient (f c) (fun i => f (x i)) i := by
  fin_cases i <;> simp [gradient, variationCoordinate, variationDegree, map_ofNat]

theorem gradient_constant (c : R) (x : Fin 6 → R) (v : Index → R) (i : Fin 6) :
    (gradient (Polynomial.C c) (valueCurve x v) i).coeff 0 = gradient c x i := by
  simpa only [Polynomial.constantCoeff_apply, Polynomial.coeff_C_zero,
    valueCurve_constant] using
      gradient_map (Polynomial.constantCoeff : Polynomial R →+* R)
        (Polynomial.C c) (valueCurve x v) i

theorem gradient_degree_le (c : R) (x : Fin 6 → R) (v : Index → R) :
    (gradient (Polynomial.C c) (valueCurve x v) 0).natDegree ≤ 6 := by
  have h := gradientVariation_degree_le c x v 0
  change (gradient (Polynomial.C c) (valueCurve x v) 0 * Polynomial.X^1).natDegree ≤ 6 at h
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  have hz := Polynomial.coeff_eq_zero_of_natDegree_lt
    (lt_of_le_of_lt h (show 6 < n+1 by omega))
  simpa only [Polynomial.coeff_mul_X_pow] using hz

theorem eq_constant_of_positive_coefficients (f : Polynomial R)
    (hdegree : f.natDegree ≤ 6)
    (hpositive : ∀ i : Index, f.coeff (equationDegree i) = 0) :
    f = Polynomial.C (f.coeff 0) := by
  ext n
  by_cases hn : n = 0
  · subst n
    simp
  · rw [Polynomial.coeff_C, ite_eq_right hn]
    by_cases h6 : n ≤ 6
    · obtain ⟨i, hi⟩ := equationDegree_covers (Nat.pos_of_ne_zero hn) h6
      rw [← hi]
      exact hpositive i
    · exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)

theorem systemPoly_eq_constant (c : R) (x : Fin 6 → R)
    (h : ∀ i : Index, equations c x i = 0) :
    systemPoly c x = Polynomial.C (MvPolynomial.C (H c x)) := by
  rw [eq_constant_of_positive_coefficients _ (systemPoly_degree_le c x) h,
    systemPoly_constant]

end CyclicTriple

#print axioms CyclicTriple.equations_pderiv_eval₂
#print axioms CyclicTriple.systemPoly_eq_constant
