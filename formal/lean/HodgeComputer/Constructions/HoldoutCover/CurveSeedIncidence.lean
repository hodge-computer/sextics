import Mathlib.Algebra.Polynomial.Roots
import HodgeComputer.Constructions.HoldoutCover.CurveGradientBlocks
import HodgeComputer.Constructions.HoldoutCover.CurveJacobianScaling
import HodgeComputer.Constructions.HoldoutCover.CurveSeed

/- Source component: CurveJacobianSeed -/
section
/-! Nonsingularity of the two scaled Jacobian blocks at the exact conic seed. -/

noncomputable section

namespace HoldoutConicJacobian

theorem seed_relation (p : HoldoutConic.Seed) :
    ((p.r : ℂ)-1)*(p.q^2)^2 = (p.r : ℂ)*((p.r : ℂ)^2+(p.r : ℂ)-1) := by
  have h1 : 1-p.r ≠ 0 := by linarith [p.lower]
  have h : (p.r-1)*HoldoutConic.R p.r = p.r*(p.r^2+p.r-1) := by
    unfold HoldoutConic.R
    field_simp
    ring
  have hc : ((p.r : ℂ)-1)*(HoldoutConic.R p.r : ℂ) =
      (p.r : ℂ)*((p.r : ℂ)^2+(p.r : ℂ)-1) := by exact_mod_cast h
  rw [show (p.q^2)^2 = p.q^4 by ring, p.q_power]
  exact hc

theorem seed_even_core (p : HoldoutConic.Seed) :
    Matrix.det (evenCore (p.r : ℂ) (p.q^2)) ≠ 0 := by
  have hr : (p.r : ℂ) ≠ 0 := by
    exact_mod_cast (show p.r ≠ 0 by linarith [p.lower])
  have hr1 : (p.r : ℂ)-1 ≠ 0 := by
    exact_mod_cast (show p.r-1 ≠ 0 by linarith [p.lower])
  have hg : evenFactor (p.r : ℂ) ≠ 0 := by
    have h := ne_of_gt (HoldoutConic.gEven_pos p.lower)
    unfold HoldoutConic.gEven at h
    unfold evenFactor
    exact_mod_cast h
  exact even_core_nonsingular _ _ hr hr1 (pow_ne_zero 2 p.q_ne_zero) hg
    (seed_relation p)

theorem seed_odd_core (p : HoldoutConic.Seed) :
    Matrix.det (oddCore (p.r : ℂ) (p.q^2)) ≠ 0 := by
  have hr : (p.r : ℂ) ≠ 0 := by
    exact_mod_cast (show p.r ≠ 0 by linarith [p.lower])
  have hg : oddFactor (p.r : ℂ) ≠ 0 := by
    have h := ne_of_gt (HoldoutConic.gOdd_pos p.lower)
    unfold HoldoutConic.gOdd at h
    unfold oddFactor
    exact_mod_cast h
  exact odd_core_nonsingular _ _ hr hg (seed_relation p)

theorem seed_even_rows (p : HoldoutConic.Seed) (i : Fin 6) :
    evenRows (p.r : ℂ) (p.q^2) i ≠ 0 := by
  have hr1 : (p.r : ℂ)-1 ≠ 0 := by
    exact_mod_cast (show p.r-1 ≠ 0 by linarith [p.lower])
  fin_cases i <;> simp [evenRows, hr1, p.q_ne_zero]

theorem seed_odd_rows (p : HoldoutConic.Seed) (i : Fin 6) :
    oddRows (p.r : ℂ) (p.q^2) i ≠ 0 := by
  have hr1 : (p.r : ℂ)-1 ≠ 0 := by
    exact_mod_cast (show p.r-1 ≠ 0 by linarith [p.lower])
  fin_cases i <;> simp [oddRows, hr1, p.q_ne_zero]

theorem seed_even_block (p : HoldoutConic.Seed) :
    Matrix.det (evenBlock (p.r : ℂ) (p.q^2)) ≠ 0 := by
  rw [evenBlock, Matrix.det_mul, Matrix.det_diagonal]
  apply mul_ne_zero _ (seed_even_core p)
  exact Finset.prod_ne_zero_iff.mpr (fun i _ => seed_even_rows p i)

theorem seed_odd_block (p : HoldoutConic.Seed) :
    Matrix.det (oddBlock (p.r : ℂ) (p.q^2)) ≠ 0 := by
  rw [oddBlock, Matrix.det_mul, Matrix.det_diagonal]
  apply mul_ne_zero _ (seed_odd_core p)
  exact Finset.prod_ne_zero_iff.mpr (fun i _ => seed_odd_rows p i)

theorem seed_full_block (p : HoldoutConic.Seed) :
    Matrix.det (fullBlock (p.r : ℂ) (p.q^2)) ≠ 0 := by
  rw [fullBlock, Matrix.det_fromBlocks_zero₂₁]
  exact mul_ne_zero (seed_even_block p) (seed_odd_block p)

theorem seed_U (p : HoldoutConic.Seed) :
    (p.alpha*p.k)*p.q*((p.r : ℂ)-1) = 3*(2*(p.r : ℂ)-1) := by
  have h : (p.alpha*p.k)*p.q = (HoldoutConic.a p.r : ℂ) := by
    unfold HoldoutConic.Seed.alpha
    field_simp [p.q_ne_zero, p.k_ne_zero]
  rw [h]
  have h1 : 1-p.r ≠ 0 := by linarith [p.lower]
  have hr : HoldoutConic.a p.r*(p.r-1) = 3*(2*p.r-1) := by
    unfold HoldoutConic.a
    field_simp
    ring
  exact_mod_cast hr

theorem seed_V (p : HoldoutConic.Seed) :
    (p.beta*p.k^3)*p.q = 3*(1-2*(p.r : ℂ)) := by
  have h : (p.beta*p.k^3)*p.q = (HoldoutConic.b p.r : ℂ) := by
    unfold HoldoutConic.Seed.beta
    field_simp [p.q_ne_zero, p.k_ne_zero]
  rw [h]
  simp [HoldoutConic.b]

theorem seed_A (p : HoldoutConic.Seed) :
    ((p.r : ℂ)/p.q)*p.q = (p.r : ℂ) :=
  div_mul_cancel₀ _ p.q_ne_zero

theorem seed_Q (p : HoldoutConic.Seed) :
    ((p.r : ℂ)-1)*p.q^4 = (p.r : ℂ)*((p.r : ℂ)^2+(p.r : ℂ)-1) := by
  convert seed_relation p using 1
  ring

theorem seed_original_even (p : HoldoutConic.Seed) :
    Matrix.det (originalEven p.q (p.alpha*p.k) (p.beta*p.k^3) ((p.r : ℂ)/p.q)) ≠ 0 :=
  original_even_nonsingular _ _ _ _ _ (seed_U p) (seed_V p) (seed_A p) (seed_Q p)
    p.q_ne_zero (seed_even_block p)

theorem seed_original_odd (p : HoldoutConic.Seed) :
    Matrix.det (originalOdd p.q (p.alpha*p.k) (p.beta*p.k^3) ((p.r : ℂ)/p.q)) ≠ 0 :=
  original_odd_nonsingular _ _ _ _ _ (seed_U p) (seed_V p) (seed_A p) (seed_Q p)
    p.q_ne_zero (seed_odd_block p)


end HoldoutConicJacobian

#print axioms HoldoutConicJacobian.seed_full_block
end
end

/- Source component: CurveIncidenceSeed -/
section
/-! The exact seed solves the anchored coefficient system, and its
coefficient Jacobian is the two explicit nonsingular parity blocks. -/

noncomputable section

namespace HoldoutConicIncidence

variable {R : Type*} [CommRing R]

def seedEndpoint : Fin 5 → ℂ := ![1,0,0,-1,0]

def seedCoefficients (p : HoldoutConic.Seed) : Index → ℂ
  | Sum.inl i => ![0,1,-p.q^2,-1,(p.r : ℂ)/p.q,p.q] i
  | Sum.inr _ => 0

theorem seed_curve_values (p : HoldoutConic.Seed) :
    valueCurve p.k seedEndpoint (seedCoefficients p) =
      ![1, Polynomial.C p.k * Polynomial.X, Polynomial.X^2,
        -(1+Polynomial.C (p.q^2)*Polynomial.X^2+Polynomial.X^4),
        Polynomial.C ((p.r : ℂ)/p.q)*Polynomial.X+Polynomial.C p.q*Polynomial.X^3] := by
  rw [valueCurve_explicit]
  funext i
  fin_cases i <;>
    simp [seedEndpoint, seedCoefficients, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val]
  ring

theorem seed_system_zero (p : HoldoutConic.Seed) :
    H (Polynomial.C p.alpha) (Polynomial.C p.beta)
      (valueCurve p.k seedEndpoint (seedCoefficients p)) = 0 := by
  apply Polynomial.funext
  intro t
  rw [seed_curve_values]
  simpa [H, HoldoutConic.H, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val, Polynomial.C_ofNat] using p.curve 1 t

theorem seed_equations (p : HoldoutConic.Seed) (i : Index) :
    coeffEval (seedCoefficients p) (equations p.alpha p.beta p.k seedEndpoint i) = 0 := by
  rw [equations_eval, seed_system_zero]
  simp

theorem seed_gradient (p : HoldoutConic.Seed) (j : Index) :
    gradient (Polynomial.C p.alpha) (Polynomial.C p.beta)
      (valueCurve p.k seedEndpoint (seedCoefficients p)) (coefficientCoordinate j) =
    sparseGradient p.q (p.alpha*p.k) (p.beta*p.k^3) ((p.r : ℂ)/p.q)
      (coefficientCoordinate j) := by
  rw [seed_curve_values]
  rcases j with j | j <;> fin_cases j <;>
    simp [gradient, sparseGradient, coefficientCoordinate,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Polynomial.C_ofNat] <;> ring

def seedJacobian (p : HoldoutConic.Seed) : Matrix Index Index ℂ :=
  fun i j => coeffEval (seedCoefficients p)
    (MvPolynomial.pderiv j (equations p.alpha p.beta p.k seedEndpoint i))

theorem seedJacobian_entries (p : HoldoutConic.Seed) (i j : Index) :
    seedJacobian p i j =
      (sparseGradient p.q (p.alpha*p.k) (p.beta*p.k^3) ((p.r : ℂ)/p.q)
        (coefficientCoordinate j) * Polynomial.X^coefficientDegree j).coeff
          (equationDegree i) := by
  rw [seedJacobian, equations_pderiv_eval, seed_gradient]



theorem seedJacobian_blocks (p : HoldoutConic.Seed) :
    seedJacobian p = Matrix.fromBlocks
      (HoldoutConicJacobian.originalEven p.q (p.alpha*p.k) (p.beta*p.k^3) ((p.r : ℂ)/p.q))
      0 0
      (HoldoutConicJacobian.originalOdd p.q (p.alpha*p.k) (p.beta*p.k^3) ((p.r : ℂ)/p.q)) := by
  rw [← gradientCoefficientMatrix_blocks]
  ext i j
  exact seedJacobian_entries p i j

theorem seedJacobian_nonsingular (p : HoldoutConic.Seed) :
    Matrix.det (seedJacobian p) ≠ 0 := by
  rw [seedJacobian_blocks, Matrix.det_fromBlocks_zero₂₁]
  exact mul_ne_zero (HoldoutConicJacobian.seed_original_even p)
    (HoldoutConicJacobian.seed_original_odd p)

end HoldoutConicIncidence

#print axioms HoldoutConicIncidence.seed_equations
#print axioms HoldoutConicIncidence.seedJacobian_nonsingular
end
end
