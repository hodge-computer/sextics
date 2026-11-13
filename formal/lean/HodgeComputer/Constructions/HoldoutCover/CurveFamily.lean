import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.RingTheory.Derivation.MapCoeffs
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/- Source component: CurveIncidence -/
section
/-!
The anchored weighted-conic incidence used in the holdout construction.
There are twelve variable positive coefficients and twelve nonconstant
coefficient equations. The endpoint is a parameter in the coefficient ring.
This file alone asserts neither nonsingularity nor a Hodge certificate.
-/

noncomputable section


namespace HoldoutConicIncidence

abbrev Index := Fin 6 ⊕ Fin 6

variable {R : Type*} [CommRing R]

abbrev Coeff (R : Type*) [CommRing R] := MvPolynomial Index R
abbrev CurvePoly (R : Type*) [CommRing R] := Polynomial (Coeff R)

def evenVar (i : Fin 6) : Coeff R := MvPolynomial.X (Sum.inl i)
def oddVar (i : Fin 6) : Coeff R := MvPolynomial.X (Sum.inr i)

/-- The weighted sextic equation on the quotient cone. -/
def H (alpha beta : R) (x : Fin 5 → R) : R :=
  x 0 ^ 6 + x 1 ^ 6 + x 2 ^ 6 +
  x 4 * (alpha * x 0 ^ 3 * x 1 + beta * x 1 ^ 3 * x 2) +
  x 3 ^ 3 - 3 * x 3 * x 4 ^ 2

/-- Anchored conic, with the entire middle coordinate fixed to x1+kλ. -/
def phi (k : R) (x : Fin 5 → R) : Fin 5 → CurvePoly R :=
  ![Polynomial.C (MvPolynomial.C (x 0)) +
      Polynomial.C (oddVar 0) * Polynomial.X +
      Polynomial.C (evenVar 0) * Polynomial.X ^ 2,
    Polynomial.C (MvPolynomial.C (x 1)) +
      Polynomial.C (MvPolynomial.C k) * Polynomial.X,
    Polynomial.C (MvPolynomial.C (x 2)) +
      Polynomial.C (oddVar 1) * Polynomial.X +
      Polynomial.C (evenVar 1) * Polynomial.X ^ 2,
    Polynomial.C (MvPolynomial.C (x 3)) +
      Polynomial.C (oddVar 2) * Polynomial.X +
      Polynomial.C (evenVar 2) * Polynomial.X ^ 2 +
      Polynomial.C (oddVar 3) * Polynomial.X ^ 3 +
      Polynomial.C (evenVar 3) * Polynomial.X ^ 4,
    Polynomial.C (MvPolynomial.C (x 4)) +
      Polynomial.C (evenVar 4) * Polynomial.X +
      Polynomial.C (oddVar 4) * Polynomial.X ^ 2 +
      Polynomial.C (evenVar 5) * Polynomial.X ^ 3 +
      Polynomial.C (oddVar 5) * Polynomial.X ^ 4]

def systemPoly (alpha beta k : R) (x : Fin 5 → R) : CurvePoly R :=
  H (Polynomial.C (MvPolynomial.C alpha))
    (Polynomial.C (MvPolynomial.C beta)) (phi k x)

/-- Even coefficients come first, so the seed Jacobian is block diagonal. -/
def equationDegree : Index → ℕ
  | Sum.inl i => 2 * (i.val + 1)
  | Sum.inr i => 2 * i.val + 1

def equations (alpha beta k : R) (x : Fin 5 → R) (i : Index) : Coeff R :=
  (systemPoly alpha beta k x).coeff (equationDegree i)

@[simp] theorem equationDegree_pos (i : Index) : 0 < equationDegree i := by
  rcases i with i | i <;> dsimp [equationDegree] <;> omega

@[simp] theorem phi_constant (k : R) (x : Fin 5 → R) (i : Fin 5) :
    (phi k x i).coeff 0 = MvPolynomial.C (x i) := by
  fin_cases i <;> simp [phi]

theorem systemPoly_constant (alpha beta k : R) (x : Fin 5 → R) :
    (systemPoly alpha beta k x).coeff 0 = MvPolynomial.C (H alpha beta x) := by
  change Polynomial.constantCoeff (systemPoly alpha beta k x) = _
  simp only [systemPoly, H, map_add, map_mul, map_sub, map_pow,
    Polynomial.constantCoeff_apply, phi_constant, Polynomial.coeff_C_zero]
  norm_num
  rw [show (MvPolynomial.C (3 : R) : Coeff R) = 3 by
    rw [show (3 : R) = 1+1+1 by norm_num]
    simp; norm_num]

/-- Differentiate coefficients while leaving the curve parameter fixed. -/
def coefficientDeriv (i : Index) :
    Derivation R (CurvePoly R) (CurvePoly R) :=
  PolynomialModule.equivPolynomialSelf.compDer (MvPolynomial.pderiv i).mapCoeffs

@[simp] theorem coefficientDeriv_coeff (i : Index) (f : CurvePoly R) (n : ℕ) :
    (coefficientDeriv i f).coeff n = MvPolynomial.pderiv i (f.coeff n) := rfl

@[simp] theorem coefficientDeriv_C (i : Index) (f : Coeff R) :
    coefficientDeriv i (Polynomial.C f) = Polynomial.C (MvPolynomial.pderiv i f) := by
  apply Polynomial.ext
  intro n
  by_cases hn : n = 0 <;> simp [coefficientDeriv_coeff, Polynomial.coeff_C, hn]

@[simp] theorem coefficientDeriv_X (i : Index) :
    coefficientDeriv i (Polynomial.X : CurvePoly R) = 0 := by
  ext n
  simp [coefficientDeriv_coeff, Polynomial.coeff_X, apply_ite]

@[simp] theorem coefficientDeriv_three (i : Index) :
    coefficientDeriv i (3 : CurvePoly R) = 0 := by
  rw [show (3 : CurvePoly R) = 1+1+1 by norm_num]
  simp

/-- Each coefficient variable changes exactly one coordinate monomial. -/
def coefficientCoordinate : Index → Fin 5
  | Sum.inl i => ![0, 2, 3, 3, 4, 4] i
  | Sum.inr i => ![0, 2, 3, 3, 4, 4] i

def coefficientDegree : Index → ℕ
  | Sum.inl i => ![2, 2, 2, 4, 1, 3] i
  | Sum.inr i => ![1, 1, 1, 3, 2, 4] i

theorem phi_coefficientDeriv (k : R) (x : Fin 5 → R)
    (j : Index) (i : Fin 5) :
    coefficientDeriv j (phi k x i) =
      if i = coefficientCoordinate j then Polynomial.X ^ coefficientDegree j else 0 := by
  rcases j with j | j <;> fin_cases j <;> fin_cases i <;>
    simp [phi, evenVar, oddVar, coefficientCoordinate, coefficientDegree,
      Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul]

/-- Ordinary partial derivatives of the five-coordinate defining polynomial. -/
def gradient (alpha beta : R) (x : Fin 5 → R) : Fin 5 → R :=
  ![6 * x 0 ^ 5 + 3 * alpha * x 0 ^ 2 * x 1 * x 4,
    6 * x 1 ^ 5 + alpha * x 0 ^ 3 * x 4 + 3 * beta * x 1 ^ 2 * x 2 * x 4,
    6 * x 2 ^ 5 + beta * x 1 ^ 3 * x 4,
    3 * x 3 ^ 2 - 3 * x 4 ^ 2,
    alpha * x 0 ^ 3 * x 1 + beta * x 1 ^ 3 * x 2 - 6 * x 3 * x 4]

theorem systemPoly_coefficientDeriv (alpha beta k : R) (x : Fin 5 → R)
    (j : Index) :
    coefficientDeriv j (systemPoly alpha beta k x) =
      gradient (Polynomial.C (MvPolynomial.C alpha))
        (Polynomial.C (MvPolynomial.C beta)) (phi k x) (coefficientCoordinate j) *
      Polynomial.X ^ coefficientDegree j := by
  unfold systemPoly H
  simp only [map_add, map_sub, Derivation.leibniz, Derivation.leibniz_pow,
    coefficientDeriv_C, MvPolynomial.pderiv_C, Polynomial.C_0,
    mul_zero, add_zero, phi_coefficientDeriv,
    smul_eq_mul]
  rcases j with j | j <;> fin_cases j <;>
    simp [gradient, coefficientCoordinate, coefficientDegree,
      Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val] <;> ring

theorem equations_pderiv (alpha beta k : R) (x : Fin 5 → R) (i j : Index) :
    MvPolynomial.pderiv j (equations alpha beta k x i) =
      (gradient (Polynomial.C (MvPolynomial.C alpha))
        (Polynomial.C (MvPolynomial.C beta)) (phi k x) (coefficientCoordinate j) *
        Polynomial.X ^ coefficientDegree j).coeff (equationDegree i) := by
  rw [equations, ← coefficientDeriv_coeff, systemPoly_coefficientDeriv]

end HoldoutConicIncidence
end
end

/- Source component: CurveTranslation -/
section
/-! Exact recentering of the anchored polynomial curves. -/

noncomputable section

namespace HoldoutConicIncidence

variable {R : Type*} [CommRing R]

def valueCurve (k : R) (x : Fin 5 → R) (v : Index → R) : Fin 5 → Polynomial R :=
  fun i => (phi k x i).map (MvPolynomial.eval₂Hom (RingHom.id R) v)

theorem valueCurve_explicit (k : R) (x : Fin 5 → R) (v : Index → R) :
    valueCurve k x v =
      ![Polynomial.C (x 0) + Polynomial.C (v (Sum.inr 0))*Polynomial.X +
          Polynomial.C (v (Sum.inl 0))*Polynomial.X^2,
        Polynomial.C (x 1) + Polynomial.C k*Polynomial.X,
        Polynomial.C (x 2) + Polynomial.C (v (Sum.inr 1))*Polynomial.X +
          Polynomial.C (v (Sum.inl 1))*Polynomial.X^2,
        Polynomial.C (x 3) + Polynomial.C (v (Sum.inr 2))*Polynomial.X +
          Polynomial.C (v (Sum.inl 2))*Polynomial.X^2 +
          Polynomial.C (v (Sum.inr 3))*Polynomial.X^3 +
          Polynomial.C (v (Sum.inl 3))*Polynomial.X^4,
        Polynomial.C (x 4) + Polynomial.C (v (Sum.inl 4))*Polynomial.X +
          Polynomial.C (v (Sum.inr 4))*Polynomial.X^2 +
          Polynomial.C (v (Sum.inl 5))*Polynomial.X^3 +
          Polynomial.C (v (Sum.inr 5))*Polynomial.X^4] := by
  funext i
  fin_cases i <;> simp [valueCurve, phi, evenVar, oddVar]

def endpoint (k : R) (x : Fin 5 → R) (v : Index → R) (t : R) : Fin 5 → R :=
  fun i => (valueCurve k x v i).eval t

/-- Taylor recentering of positive coefficients, with integral binomial factors. -/
def recenter (v : Index → R) (t : R) : Index → R
  | Sum.inl i =>
    ![v (Sum.inl 0), v (Sum.inl 1),
      v (Sum.inl 2) + 3*v (Sum.inr 3)*t + 6*v (Sum.inl 3)*t^2,
      v (Sum.inl 3),
      v (Sum.inl 4) + 2*v (Sum.inr 4)*t + 3*v (Sum.inl 5)*t^2 +
        4*v (Sum.inr 5)*t^3,
      v (Sum.inl 5) + 4*v (Sum.inr 5)*t] i
  | Sum.inr i =>
    ![v (Sum.inr 0) + 2*v (Sum.inl 0)*t,
      v (Sum.inr 1) + 2*v (Sum.inl 1)*t,
      v (Sum.inr 2) + 2*v (Sum.inl 2)*t + 3*v (Sum.inr 3)*t^2 +
        4*v (Sum.inl 3)*t^3,
      v (Sum.inr 3) + 4*v (Sum.inl 3)*t,
      v (Sum.inr 4) + 3*v (Sum.inl 5)*t + 6*v (Sum.inr 5)*t^2,
      v (Sum.inr 5)] i

@[simp] theorem recenter_zero (v : Index → R) : recenter v 0 = v := by
  funext i
  rcases i with i | i <;> fin_cases i <;> simp [recenter]

theorem recenter_add (v : Index → R) (s t : R) :
    recenter (recenter v s) t = recenter v (s+t) := by
  funext i
  rcases i with i | i <;> fin_cases i <;> simp [recenter] <;> ring

theorem valueCurve_recenter (k : R) (x : Fin 5 → R) (v : Index → R)
    (t : R) (i : Fin 5) :
    valueCurve k (endpoint k x v t) (recenter v t) i =
      (valueCurve k x v i).comp (Polynomial.X + Polynomial.C t) := by
  simp only [valueCurve_explicit]
  fin_cases i <;>
    simp [endpoint, valueCurve_explicit, recenter, Polynomial.add_comp,
      Polynomial.mul_comp, Polynomial.pow_comp, Polynomial.C_ofNat] <;> ring

theorem endpoint_recenter (k : R) (x : Fin 5 → R) (v : Index → R)
    (s t : R) :
    endpoint k (endpoint k x v s) (recenter v s) t = endpoint k x v (s+t) := by
  funext i
  change (valueCurve k (endpoint k x v s) (recenter v s) i).eval t =
    (valueCurve k x v i).eval (s+t)
  rw [valueCurve_recenter]
  simp [Polynomial.eval_comp, add_comm]

theorem valueCurve_system (alpha beta k : R) (x : Fin 5 → R) (v : Index → R) :
    (systemPoly alpha beta k x).map (MvPolynomial.eval₂Hom (RingHom.id R) v) =
      H (Polynomial.C alpha) (Polynomial.C beta) (valueCurve k x v) := by
  simp [systemPoly, H, valueCurve]

theorem valueCurve_system_recenter (alpha beta k : R) (x : Fin 5 → R)
    (v : Index → R) (t : R) :
    H (Polynomial.C alpha) (Polynomial.C beta)
      (valueCurve k (endpoint k x v t) (recenter v t)) =
    (H (Polynomial.C alpha) (Polynomial.C beta) (valueCurve k x v)).comp
      (Polynomial.X + Polynomial.C t) := by
  unfold H
  simp only [valueCurve_recenter, Polynomial.add_comp, Polynomial.mul_comp,
    Polynomial.sub_comp, Polynomial.pow_comp, Polynomial.C_comp, Polynomial.ofNat_comp]
  norm_num

theorem systemPoly_degree_le (alpha beta k : R) (x : Fin 5 → R) :
    (systemPoly alpha beta k x).natDegree ≤ 12 := by
  unfold systemPoly H phi
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  compute_degree

theorem equationDegree_le (i : Index) : equationDegree i ≤ 12 := by
  rcases i with i | i <;> dsimp [equationDegree] <;> have := i.isLt <;> omega

theorem equationDegree_covers {n : ℕ} (hn : 0 < n) (h12 : n ≤ 12) :
    ∃ i : Index, equationDegree i = n := by
  by_cases he : n % 2 = 0
  · refine ⟨Sum.inl ⟨n/2-1, by omega⟩, ?_⟩
    dsimp [equationDegree]
    omega
  · refine ⟨Sum.inr ⟨n/2, by omega⟩, ?_⟩
    dsimp [equationDegree]
    omega

/-- The twelve indexed coefficients are exactly all possible positive
coefficients of a polynomial of degree at most twelve. -/
theorem eq_constant_of_positive_coefficients (f : Polynomial R)
    (hdegree : f.natDegree ≤ 12)
    (hpositive : ∀ i : Index, f.coeff (equationDegree i) = 0) :
    f = Polynomial.C (f.coeff 0) := by
  apply Polynomial.ext
  intro n
  by_cases hn : n = 0
  · subst n
    simp
  · rw [Polynomial.coeff_C, if_neg hn]
    by_cases h12 : n ≤ 12
    · obtain ⟨i, hi⟩ := equationDegree_covers (Nat.pos_of_ne_zero hn) h12
      rw [← hi]
      exact hpositive i
    · exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)

theorem systemPoly_eq_constant (alpha beta k : R) (x : Fin 5 → R)
    (h : ∀ i : Index, equations alpha beta k x i = 0) :
    systemPoly alpha beta k x = Polynomial.C (MvPolynomial.C (H alpha beta x)) := by
  rw [eq_constant_of_positive_coefficients _ (systemPoly_degree_le alpha beta k x) h,
    systemPoly_constant]

end HoldoutConicIncidence
end
end

/- Source component: CurveFamilyData -/
section
/-! Scalar evaluation and degree bounds for the anchored coefficient family. -/

noncomputable section

namespace HoldoutConicIncidence

variable {R : Type*} [CommRing R]

def coeffEval (v : Index → R) : Coeff R →+* R :=
  MvPolynomial.eval₂Hom (RingHom.id R) v

theorem equations_eval (alpha beta k : R) (x : Fin 5 → R) (v : Index → R)
    (i : Index) :
    coeffEval v (equations alpha beta k x i) =
      (H (Polynomial.C alpha) (Polynomial.C beta) (valueCurve k x v)).coeff
        (equationDegree i) := by
  rw [← valueCurve_system]
  simp [equations, coeffEval, Polynomial.coeff_map]

theorem equations_pderiv_eval (alpha beta k : R) (x : Fin 5 → R)
    (v : Index → R) (i j : Index) :
    coeffEval v (MvPolynomial.pderiv j (equations alpha beta k x i)) =
      (gradient (Polynomial.C alpha) (Polynomial.C beta) (valueCurve k x v)
        (coefficientCoordinate j) * Polynomial.X ^ coefficientDegree j).coeff
          (equationDegree i) := by
  rw [equations_pderiv]
  rw [← Polynomial.coeff_map]
  congr 1
  rcases j with j | j <;> fin_cases j <;>
    simp [coeffEval, gradient, valueCurve, coefficientCoordinate, coefficientDegree,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]


@[simp] theorem valueCurve_constant (k : R) (x : Fin 5 → R) (v : Index → R)
    (i : Fin 5) : (valueCurve k x v i).coeff 0 = x i := by
  simp [valueCurve, Polynomial.coeff_map, phi_constant]

@[simp] theorem coefficientDegree_pos (j : Index) : 0 < coefficientDegree j := by
  rcases j with j | j <;> fin_cases j <;> simp [coefficientDegree]

theorem coefficientDeriv_degree_le (j : Index) (f : CurvePoly R) (n : ℕ)
    (h : f.natDegree ≤ n) : (coefficientDeriv j f).natDegree ≤ n := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro m hm
  rw [coefficientDeriv_coeff,
    Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt h hm), map_zero]

/-- Coefficient differentiation cannot increase the degree in the independent
curve parameter. Evaluation of the coefficient variables also cannot increase it. -/
theorem gradientVariation_degree_le (alpha beta k : R) (x : Fin 5 → R)
    (v : Index → R) (j : Index) :
    (gradient (Polynomial.C alpha) (Polynomial.C beta) (valueCurve k x v)
      (coefficientCoordinate j) * Polynomial.X^coefficientDegree j).natDegree ≤ 12 := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro m hm
  have h := coefficientDeriv_degree_le j (systemPoly alpha beta k x) 12
    (systemPoly_degree_le alpha beta k x)
  have hz := Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt h hm)
  rw [coefficientDeriv_coeff] at hz
  have hmapp := congrArg (coeffEval v) hz
  rw [map_zero] at hmapp
  rw [← coefficientDeriv_coeff, systemPoly_coefficientDeriv] at hmapp
  rw [← Polynomial.coeff_map] at hmapp
  convert hmapp using 1
  rcases j with j | j <;> fin_cases j <;>
      simp [coeffEval, gradient, valueCurve, coefficientCoordinate, coefficientDegree,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]

end HoldoutConicIncidence
end
end

/- Source component: CurveIncidenceMap -/
section
/-! The concrete anchored coefficient equations commute with base change.
In particular, a seed in a residue field evaluates the very same polynomial
presentation that is used over the generic coefficient field. -/

noncomputable section

namespace HoldoutConicIncidence

variable {R S : Type*} [CommRing R] [CommRing S]

theorem phi_map (f : R →+* S) (k : R) (x : Fin 5 → R) (i : Fin 5) :
    (phi k x i).map (MvPolynomial.map f) = phi (f k) (fun i => f (x i)) i := by
  fin_cases i <;> simp [phi, evenVar, oddVar]

theorem systemPoly_map (f : R →+* S) (alpha beta k : R) (x : Fin 5 → R) :
    (systemPoly alpha beta k x).map (MvPolynomial.map f) =
      systemPoly (f alpha) (f beta) (f k) (fun i => f (x i)) := by
  simp [systemPoly, H, phi_map]

theorem equations_map (f : R →+* S) (alpha beta k : R) (x : Fin 5 → R)
    (i : Index) :
    MvPolynomial.map f (equations alpha beta k x i) =
      equations (f alpha) (f beta) (f k) (fun i => f (x i)) i := by
  rw [equations, ← Polynomial.coeff_map, systemPoly_map]
  rfl

theorem equations_pderiv_map (f : R →+* S) (alpha beta k : R)
    (x : Fin 5 → R) (i j : Index) :
    MvPolynomial.map f (MvPolynomial.pderiv j (equations alpha beta k x i)) =
      MvPolynomial.pderiv j
        (equations (f alpha) (f beta) (f k) (fun i => f (x i)) i) := by
  rw [← MvPolynomial.pderiv_map, equations_map]

theorem phi_eval₂ (f : R →+* S) (k : R) (x : Fin 5 → R)
    (v : Index → S) (i : Fin 5) :
    (phi k x i).map (MvPolynomial.eval₂Hom f v) =
      valueCurve (f k) (fun i => f (x i)) v i := by
  rw [valueCurve_explicit]
  fin_cases i <;> simp [phi, evenVar, oddVar]

theorem systemPoly_eval₂ (f : R →+* S) (alpha beta k : R) (x : Fin 5 → R)
    (v : Index → S) :
    (systemPoly alpha beta k x).map (MvPolynomial.eval₂Hom f v) =
      H (Polynomial.C (f alpha)) (Polynomial.C (f beta))
        (valueCurve (f k) (fun i => f (x i)) v) := by
  simp [systemPoly, H, phi_eval₂]

theorem equations_eval₂ (f : R →+* S) (alpha beta k : R) (x : Fin 5 → R)
    (v : Index → S) (i : Index) :
    MvPolynomial.eval₂Hom f v (equations alpha beta k x i) =
      (H (Polynomial.C (f alpha)) (Polynomial.C (f beta))
        (valueCurve (f k) (fun i => f (x i)) v)).coeff (equationDegree i) := by
  rw [equations, ← Polynomial.coeff_map, systemPoly_eval₂]

theorem equations_pderiv_eval₂ (f : R →+* S) (alpha beta k : R)
    (x : Fin 5 → R) (v : Index → S) (i j : Index) :
    MvPolynomial.eval₂Hom f v (MvPolynomial.pderiv j (equations alpha beta k x i)) =
      (gradient (Polynomial.C (f alpha)) (Polynomial.C (f beta))
        (valueCurve (f k) (fun i => f (x i)) v) (coefficientCoordinate j) *
          Polynomial.X^coefficientDegree j).coeff (equationDegree i) := by
  rw [equations_pderiv, ← Polynomial.coeff_map]
  congr 1
  rcases j with j | j <;> fin_cases j <;>
    simp [gradient, coefficientCoordinate, coefficientDegree, phi_eval₂,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]

end HoldoutConicIncidence
end
end
