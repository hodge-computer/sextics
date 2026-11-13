import HodgeComputer.Constructions.HoldoutCover.CurveJacobianStaged

/- Source component: CurveJacobianScaling -/
section
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace HoldoutConicJacobian
variable {K : Type*} [Field K]

def evenRows (r z : K) : Fin 6 → K :=
  ![3*(r-1), 3*(r-1), 3*(r-1), 3*(r-1), 3*(r-1), 3*z*(r-1)^2]
def oddRows (r z : K) : Fin 6 → K :=
  ![3*z*(r-1)^2, 3*(r-1), 3*(r-1), 3*(r-1), 3*(r-1), 3*z*(r-1)^2]
def evenBlock (r z : K) : Matrix (Fin 6) (Fin 6) K :=
  Matrix.diagonal (evenRows r z) * evenCore r z
def oddBlock (r z : K) : Matrix (Fin 6) (Fin 6) K :=
  Matrix.diagonal (oddRows r z) * oddCore r z
def fullBlock (r z : K) : Matrix (Fin 6 ⊕ Fin 6) (Fin 6 ⊕ Fin 6) K :=
  Matrix.fromBlocks (evenBlock r z) 0 0 (oddBlock r z)
def pColumns (q : K) : Fin 6 → K := ![1,1,1,1,q,q]

def originalEven (q u v a : K) : Matrix (Fin 6) (Fin 6) K :=
  !![6, 0, 3, 0, 6*a + u, 0;
     3*a*u, 0, -3*a^2 + 6*q^2, 3, 6*a*q^2 + 6*q, 6*a + u;
     3*q*u, a*v, -6*a*q + 3*q^4 + 6, -3*a^2 + 6*q^2, 6*a + 6*q^3 + v, 6*a*q^2 + 6*q;
     0, q*v, 3*q^2, -6*a*q + 3*q^4 + 6, 6*q, 6*a + 6*q^3 + v;
     0, 0, 3, 3*q^2, 0, 6*q;
     0, 6, 0, 3, 0, 0]

def originalOdd (q u v a : K) : Matrix (Fin 6) (Fin 6) K :=
  !![6, 0, 3, 0, 0, 0;
     3*a*u, 0, -3*a^2 + 6*q^2, 3, 6*a + u, 0;
     3*q*u, a*v, -6*a*q + 3*q^4 + 6, -3*a^2 + 6*q^2, 6*a*q^2 + 6*q, 6*a + u;
     0, q*v, 3*q^2, -6*a*q + 3*q^4 + 6, 6*a + 6*q^3 + v, 6*a*q^2 + 6*q;
     0, 0, 3, 3*q^2, 6*q, 6*a + 6*q^3 + v;
     0, 6, 0, 3, 0, 6*q]

private theorem scaling_cell_0 (r q u v a : K)
    (hU : u*q*(r-1) = 3*(2*r-1)) (_hV : v*q = 3*(1-2*r))
    (hA : a*q = r) (_hQ : (r-1)*q^4 = r*(r^2+r-1)) :
    q*(r - 1)*(6*a*q*r - 6*a*q + q*r*u - q*u - 6*r^2 + 3) = 0 := by
  linear_combination (q*(r - 1))*hU + (6*q*(r - 1)^2)*hA

private theorem scaling_cell_1 (r q u v a : K)
    (hU : u*q*(r-1) = 3*(2*r-1)) (_hV : v*q = 3*(1-2*r))
    (hA : a*q = r) (_hQ : (r-1)*q^4 = r*(r^2+r-1)) :
    3*(r - 1)*(a*q^2*r*u - a*q^2*u - 6*r^2 + 3*r) = 0 := by
  linear_combination (3*a*q*(r - 1))*hU + (9*(r - 1)*(2*r - 1))*hA

private theorem scaling_cell_2 (r q u v a : K)
    (_hU : u*q*(r-1) = 3*(2*r-1)) (_hV : v*q = 3*(1-2*r))
    (hA : a*q = r) (hQ : (r-1)*q^4 = r*(r^2+r-1)) :
    3*(r - 1)*(-a^2*q^2*r + a^2*q^2 + 2*q^4*r - 2*q^4 - r^3 - 3*r^2 + 2*r) = 0 := by
  linear_combination (-3*(r - 1)^2*(a*q + r))*hA + (6*(r - 1))*hQ

private theorem scaling_cell_3 (r q u v a : K)
    (_hU : u*q*(r-1) = 3*(2*r-1)) (_hV : v*q = 3*(1-2*r))
    (hA : a*q = r) (_hQ : (r-1)*q^4 = r*(r^2+r-1)) :
    6*q^3*(r - 1)^2*(a*q - r) = 0 := by
  linear_combination (6*q^3*(r - 1)^2)*hA

private theorem scaling_cell_4 (r q u v a : K)
    (hU : u*q*(r-1) = 3*(2*r-1)) (_hV : v*q = 3*(1-2*r))
    (_hA : a*q = r) (_hQ : (r-1)*q^4 = r*(r^2+r-1)) :
    3*q^2*(r - 1)*(q*r*u - q*u - 6*r + 3) = 0 := by
  linear_combination (3*q^2*(r - 1))*hU

private theorem scaling_cell_5 (r q u v a : K)
    (_hU : u*q*(r-1) = 3*(2*r-1)) (hV : v*q = 3*(1-2*r))
    (hA : a*q = r) (_hQ : (r-1)*q^4 = r*(r^2+r-1)) :
    (r - 1)^2*(a*q^2*v + 6*r^2 - 3*r) = 0 := by
  linear_combination (a*q*(r - 1)^2)*hV + (-3*(r - 1)^2*(2*r - 1))*hA

private theorem scaling_cell_6 (r q u v a : K)
    (_hU : u*q*(r-1) = 3*(2*r-1)) (_hV : v*q = 3*(1-2*r))
    (hA : a*q = r) (hQ : (r-1)*q^4 = r*(r^2+r-1)) :
    3*q^2*(r - 1)*(-2*a*q*r + 2*a*q + q^4*r - q^4 - r^3 + r^2 - r) = 0 := by
  linear_combination (-6*q^2*(r - 1)^2)*hA + (3*q^2*(r - 1))*hQ

private theorem scaling_cell_7 (r q u v a : K)
    (_hU : u*q*(r-1) = 3*(2*r-1)) (hV : v*q = 3*(1-2*r))
    (hA : a*q = r) (hQ : (r-1)*q^4 = r*(r^2+r-1)) :
    q*(r - 1)*(6*a*q*r - 6*a*q + 6*q^4*r - 6*q^4 + q*r*v - q*v - 6*r^3 - 6*r^2 + 3*r + 3) = 0 := by
  linear_combination (q*(r - 1)^2)*hV + (6*q*(r - 1)^2)*hA + (6*q*(r - 1))*hQ

private theorem scaling_cell_8 (r q u v a : K)
    (_hU : u*q*(r-1) = 3*(2*r-1)) (hV : v*q = 3*(1-2*r))
    (_hA : a*q = r) (_hQ : (r-1)*q^4 = r*(r^2+r-1)) :
    q^2*(r - 1)^2*(q*v + 6*r - 3) = 0 := by
  linear_combination (q^2*(r - 1)^2)*hV

private theorem scaling_cell_9 (r q u v a : K)
    (_hU : u*q*(r-1) = 3*(2*r-1)) (_hV : v*q = 3*(1-2*r))
    (_hA : a*q = r) (hQ : (r-1)*q^4 = r*(r^2+r-1)) :
    3*(r - 1)*(q^4*r - q^4 - r^3 - r^2 + r) = 0 := by
  linear_combination (3*(r - 1))*hQ

theorem even_scaling (r q u v a : K)
    (hU : u*q*(r-1) = 3*(2*r-1)) (hV : v*q = 3*(1-2*r))
    (hA : a*q = r) (hQ : (r-1)*q^4 = r*(r^2+r-1)) :
    ((r-1)^2*q^2) • originalEven q u v a =
      evenBlock r (q^2) * Matrix.diagonal (pColumns q) := by
  ext i j
  simp only [Matrix.smul_apply, smul_eq_mul, evenBlock, Matrix.mul_diagonal,
    Matrix.diagonal_mul]
  fin_cases i <;> fin_cases j

  · change ((r-1)^2*q^2)*(6) =
      (3*(r-1))*(2*r*(q^2) - 2*(q^2))*(1)

    ring

  · change ((r-1)^2*q^2)*(0) =
      (3*(r-1))*(0)*(1)

    ring

  · change ((r-1)^2*q^2)*(3) =
      (3*(r-1))*(r*(q^2) - (q^2))*(1)

    ring

  · change ((r-1)^2*q^2)*(0) =
      (3*(r-1))*(0)*(1)

    ring

  · change ((r-1)^2*q^2)*(6*a + u) =
      (3*(r-1))*(2*r^2 - 1)*(q)

    linear_combination scaling_cell_0 r q u v a hU hV hA hQ

  · change ((r-1)^2*q^2)*(0) =
      (3*(r-1))*(0)*(q)

    ring

  · change ((r-1)^2*q^2)*(3*a*u) =
      (3*(r-1))*(6*r^2 - 3*r)*(1)

    linear_combination scaling_cell_1 r q u v a hU hV hA hQ

  · change ((r-1)^2*q^2)*(0) =
      (3*(r-1))*(0)*(1)

    ring

  · change ((r-1)^2*q^2)*(-3*a^2 + 6*q^2) =
      (3*(r-1))*(r^3 + 3*r^2 - 2*r)*(1)

    linear_combination scaling_cell_2 r q u v a hU hV hA hQ

  · change ((r-1)^2*q^2)*(3) =
      (3*(r-1))*(r*(q^2) - (q^2))*(1)

    ring

  · change ((r-1)^2*q^2)*(6*a*q^2 + 6*q) =
      (3*(r-1))*(2*r^2*(q^2) - 2*(q^2))*(q)

    linear_combination scaling_cell_3 r q u v a hU hV hA hQ

  · change ((r-1)^2*q^2)*(6*a + u) =
      (3*(r-1))*(2*r^2 - 1)*(q)

    linear_combination scaling_cell_0 r q u v a hU hV hA hQ

  · change ((r-1)^2*q^2)*(3*q*u) =
      (3*(r-1))*(6*r*(q^2) - 3*(q^2))*(1)

    linear_combination scaling_cell_4 r q u v a hU hV hA hQ

  · change ((r-1)^2*q^2)*(a*v) =
      (3*(r-1))*(-2*r^3 + 3*r^2 - r)*(1)

    linear_combination scaling_cell_5 r q u v a hU hV hA hQ

  · change ((r-1)^2*q^2)*(-6*a*q + 3*q^4 + 6) =
      (3*(r-1))*(r^3*(q^2) - r^2*(q^2) + 3*r*(q^2) - 2*(q^2))*(1)

    linear_combination scaling_cell_6 r q u v a hU hV hA hQ

  · change ((r-1)^2*q^2)*(-3*a^2 + 6*q^2) =
      (3*(r-1))*(r^3 + 3*r^2 - 2*r)*(1)

    linear_combination scaling_cell_2 r q u v a hU hV hA hQ

  · change ((r-1)^2*q^2)*(6*a + 6*q^3 + v) =
      (3*(r-1))*(2*r^3 + 2*r^2 - r - 1)*(q)

    linear_combination scaling_cell_7 r q u v a hU hV hA hQ

  · change ((r-1)^2*q^2)*(6*a*q^2 + 6*q) =
      (3*(r-1))*(2*r^2*(q^2) - 2*(q^2))*(q)

    linear_combination scaling_cell_3 r q u v a hU hV hA hQ

  · change ((r-1)^2*q^2)*(0) =
      (3*(r-1))*(0)*(1)

    ring

  · change ((r-1)^2*q^2)*(q*v) =
      (3*(r-1))*(-2*r^2*(q^2) + 3*r*(q^2) - (q^2))*(1)

    linear_combination scaling_cell_8 r q u v a hU hV hA hQ

  · change ((r-1)^2*q^2)*(3*q^2) =
      (3*(r-1))*(r^3 + r^2 - r)*(1)

    linear_combination scaling_cell_9 r q u v a hU hV hA hQ

  · change ((r-1)^2*q^2)*(-6*a*q + 3*q^4 + 6) =
      (3*(r-1))*(r^3*(q^2) - r^2*(q^2) + 3*r*(q^2) - 2*(q^2))*(1)

    linear_combination scaling_cell_6 r q u v a hU hV hA hQ

  · change ((r-1)^2*q^2)*(6*q) =
      (3*(r-1))*(2*r*(q^2) - 2*(q^2))*(q)

    ring

  · change ((r-1)^2*q^2)*(6*a + 6*q^3 + v) =
      (3*(r-1))*(2*r^3 + 2*r^2 - r - 1)*(q)

    linear_combination scaling_cell_7 r q u v a hU hV hA hQ

  · change ((r-1)^2*q^2)*(0) =
      (3*(r-1))*(0)*(1)

    ring

  · change ((r-1)^2*q^2)*(0) =
      (3*(r-1))*(0)*(1)

    ring

  · change ((r-1)^2*q^2)*(3) =
      (3*(r-1))*(r*(q^2) - (q^2))*(1)

    ring

  · change ((r-1)^2*q^2)*(3*q^2) =
      (3*(r-1))*(r^3 + r^2 - r)*(1)

    linear_combination scaling_cell_9 r q u v a hU hV hA hQ

  · change ((r-1)^2*q^2)*(0) =
      (3*(r-1))*(0)*(q)

    ring

  · change ((r-1)^2*q^2)*(6*q) =
      (3*(r-1))*(2*r*(q^2) - 2*(q^2))*(q)

    ring

  · change ((r-1)^2*q^2)*(0) =
      (3*(q^2)*(r-1)^2)*(0)*(1)

    ring

  · change ((r-1)^2*q^2)*(6) =
      (3*(q^2)*(r-1)^2)*(2)*(1)

    ring

  · change ((r-1)^2*q^2)*(0) =
      (3*(q^2)*(r-1)^2)*(0)*(1)

    ring

  · change ((r-1)^2*q^2)*(3) =
      (3*(q^2)*(r-1)^2)*(1)*(1)

    ring

  · change ((r-1)^2*q^2)*(0) =
      (3*(q^2)*(r-1)^2)*(0)*(q)

    ring

  · change ((r-1)^2*q^2)*(0) =
      (3*(q^2)*(r-1)^2)*(0)*(q)

    ring

theorem original_even_nonsingular (r q u v a : K)
    (hU : u*q*(r-1) = 3*(2*r-1)) (hV : v*q = 3*(1-2*r))
    (hA : a*q = r) (hQ : (r-1)*q^4 = r*(r^2+r-1))
    (hq : q ≠ 0) (hb : Matrix.det (evenBlock r (q^2)) ≠ 0) :
    Matrix.det (originalEven q u v a) ≠ 0 := by
  have hn : Matrix.det (evenBlock r (q^2) * Matrix.diagonal (pColumns q)) ≠ 0 := by
    rw [Matrix.det_mul, Matrix.det_diagonal]
    apply mul_ne_zero hb
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    fin_cases i <;> simp [pColumns, hq]
  intro hz
  have hd := congrArg Matrix.det (even_scaling r q u v a hU hV hA hQ)
  simp only [Matrix.det_smul, hz, mul_zero] at hd
  exact hn hd.symm

theorem odd_scaling (r q u v a : K)
    (hU : u*q*(r-1) = 3*(2*r-1)) (hV : v*q = 3*(1-2*r))
    (hA : a*q = r) (hQ : (r-1)*q^4 = r*(r^2+r-1)) :
    ((r-1)^2*q^2) • originalOdd q u v a =
      oddBlock r (q^2) * Matrix.diagonal (pColumns q) := by
  ext i j
  simp only [Matrix.smul_apply, smul_eq_mul, oddBlock, Matrix.mul_diagonal,
    Matrix.diagonal_mul]
  fin_cases i <;> fin_cases j

  · change ((r-1)^2*q^2)*(6) =
      (3*(q^2)*(r-1)^2)*(2)*(1)

    ring

  · change ((r-1)^2*q^2)*(0) =
      (3*(q^2)*(r-1)^2)*(0)*(1)

    ring

  · change ((r-1)^2*q^2)*(3) =
      (3*(q^2)*(r-1)^2)*(1)*(1)

    ring

  · change ((r-1)^2*q^2)*(0) =
      (3*(q^2)*(r-1)^2)*(0)*(1)

    ring

  · change ((r-1)^2*q^2)*(0) =
      (3*(q^2)*(r-1)^2)*(0)*(q)

    ring

  · change ((r-1)^2*q^2)*(0) =
      (3*(q^2)*(r-1)^2)*(0)*(q)

    ring

  · change ((r-1)^2*q^2)*(3*a*u) =
      (3*(r-1))*(6*r^2 - 3*r)*(1)

    linear_combination scaling_cell_1 r q u v a hU hV hA hQ

  · change ((r-1)^2*q^2)*(0) =
      (3*(r-1))*(0)*(1)

    ring

  · change ((r-1)^2*q^2)*(-3*a^2 + 6*q^2) =
      (3*(r-1))*(r^3 + 3*r^2 - 2*r)*(1)

    linear_combination scaling_cell_2 r q u v a hU hV hA hQ

  · change ((r-1)^2*q^2)*(3) =
      (3*(r-1))*(r*(q^2) - (q^2))*(1)

    ring

  · change ((r-1)^2*q^2)*(6*a + u) =
      (3*(r-1))*(2*r^2 - 1)*(q)

    linear_combination scaling_cell_0 r q u v a hU hV hA hQ

  · change ((r-1)^2*q^2)*(0) =
      (3*(r-1))*(0)*(q)

    ring

  · change ((r-1)^2*q^2)*(3*q*u) =
      (3*(r-1))*(6*r*(q^2) - 3*(q^2))*(1)

    linear_combination scaling_cell_4 r q u v a hU hV hA hQ

  · change ((r-1)^2*q^2)*(a*v) =
      (3*(r-1))*(-2*r^3 + 3*r^2 - r)*(1)

    linear_combination scaling_cell_5 r q u v a hU hV hA hQ

  · change ((r-1)^2*q^2)*(-6*a*q + 3*q^4 + 6) =
      (3*(r-1))*(r^3*(q^2) - r^2*(q^2) + 3*r*(q^2) - 2*(q^2))*(1)

    linear_combination scaling_cell_6 r q u v a hU hV hA hQ

  · change ((r-1)^2*q^2)*(-3*a^2 + 6*q^2) =
      (3*(r-1))*(r^3 + 3*r^2 - 2*r)*(1)

    linear_combination scaling_cell_2 r q u v a hU hV hA hQ

  · change ((r-1)^2*q^2)*(6*a*q^2 + 6*q) =
      (3*(r-1))*(2*r^2*(q^2) - 2*(q^2))*(q)

    linear_combination scaling_cell_3 r q u v a hU hV hA hQ

  · change ((r-1)^2*q^2)*(6*a + u) =
      (3*(r-1))*(2*r^2 - 1)*(q)

    linear_combination scaling_cell_0 r q u v a hU hV hA hQ

  · change ((r-1)^2*q^2)*(0) =
      (3*(r-1))*(0)*(1)

    ring

  · change ((r-1)^2*q^2)*(q*v) =
      (3*(r-1))*(-2*r^2*(q^2) + 3*r*(q^2) - (q^2))*(1)

    linear_combination scaling_cell_8 r q u v a hU hV hA hQ

  · change ((r-1)^2*q^2)*(3*q^2) =
      (3*(r-1))*(r^3 + r^2 - r)*(1)

    linear_combination scaling_cell_9 r q u v a hU hV hA hQ

  · change ((r-1)^2*q^2)*(-6*a*q + 3*q^4 + 6) =
      (3*(r-1))*(r^3*(q^2) - r^2*(q^2) + 3*r*(q^2) - 2*(q^2))*(1)

    linear_combination scaling_cell_6 r q u v a hU hV hA hQ

  · change ((r-1)^2*q^2)*(6*a + 6*q^3 + v) =
      (3*(r-1))*(2*r^3 + 2*r^2 - r - 1)*(q)

    linear_combination scaling_cell_7 r q u v a hU hV hA hQ

  · change ((r-1)^2*q^2)*(6*a*q^2 + 6*q) =
      (3*(r-1))*(2*r^2*(q^2) - 2*(q^2))*(q)

    linear_combination scaling_cell_3 r q u v a hU hV hA hQ

  · change ((r-1)^2*q^2)*(0) =
      (3*(r-1))*(0)*(1)

    ring

  · change ((r-1)^2*q^2)*(0) =
      (3*(r-1))*(0)*(1)

    ring

  · change ((r-1)^2*q^2)*(3) =
      (3*(r-1))*(r*(q^2) - (q^2))*(1)

    ring

  · change ((r-1)^2*q^2)*(3*q^2) =
      (3*(r-1))*(r^3 + r^2 - r)*(1)

    linear_combination scaling_cell_9 r q u v a hU hV hA hQ

  · change ((r-1)^2*q^2)*(6*q) =
      (3*(r-1))*(2*r*(q^2) - 2*(q^2))*(q)

    ring

  · change ((r-1)^2*q^2)*(6*a + 6*q^3 + v) =
      (3*(r-1))*(2*r^3 + 2*r^2 - r - 1)*(q)

    linear_combination scaling_cell_7 r q u v a hU hV hA hQ

  · change ((r-1)^2*q^2)*(0) =
      (3*(q^2)*(r-1)^2)*(0)*(1)

    ring

  · change ((r-1)^2*q^2)*(6) =
      (3*(q^2)*(r-1)^2)*(2)*(1)

    ring

  · change ((r-1)^2*q^2)*(0) =
      (3*(q^2)*(r-1)^2)*(0)*(1)

    ring

  · change ((r-1)^2*q^2)*(3) =
      (3*(q^2)*(r-1)^2)*(1)*(1)

    ring

  · change ((r-1)^2*q^2)*(0) =
      (3*(q^2)*(r-1)^2)*(0)*(q)

    ring

  · change ((r-1)^2*q^2)*(6*q) =
      (3*(q^2)*(r-1)^2)*(2)*(q)

    ring

theorem original_odd_nonsingular (r q u v a : K)
    (hU : u*q*(r-1) = 3*(2*r-1)) (hV : v*q = 3*(1-2*r))
    (hA : a*q = r) (hQ : (r-1)*q^4 = r*(r^2+r-1))
    (hq : q ≠ 0) (hb : Matrix.det (oddBlock r (q^2)) ≠ 0) :
    Matrix.det (originalOdd q u v a) ≠ 0 := by
  have hn : Matrix.det (oddBlock r (q^2) * Matrix.diagonal (pColumns q)) ≠ 0 := by
    rw [Matrix.det_mul, Matrix.det_diagonal]
    apply mul_ne_zero hb
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    fin_cases i <;> simp [pColumns, hq]
  intro hz
  have hd := congrArg Matrix.det (odd_scaling r q u v a hU hV hA hQ)
  simp only [Matrix.det_smul, hz, mul_zero] at hd
  exact hn hd.symm

end HoldoutConicJacobian
end
end
