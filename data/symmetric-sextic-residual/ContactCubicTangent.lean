import Proposal.ContactCubicExistence

/-!
# A nontrivial first-order norm-contact deformation on the actual target

The derivative of the actual 44-equation expansion is checked as a literal
polynomial identity. Invertibility of that actual Jacobian solves the other
44 velocities while rho0 has derivative one. This is a first-order polynomial
deformation, not a normal-bundle or Hodge-theoretic assertion.
-/

noncomputable section

namespace ContactCubicTangent

open MvPolynomial ContactCubicData ContactCubicTargetBinding
open ContactPolynomialBounds ContactExactArithmetic Metric
open scoped BigOperators

set_option maxHeartbeats 24000000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false

def Q1linear (v : Fin 44 → ℂ) : Poly := Q1 v - C (1/4 : ℂ) * X 0 ^ 2
def Q2linear (v : Fin 44 → ℂ) : Poly := Q2 v - X 0 * X 1
def Q1dot (v : Fin 44 → ℂ) : Poly := X 0 ^ 2 + Q1linear v

def normalRestriction (x : Fin 44 → ℂ) : Poly :=
  C 3 * Q1 x ^ 2 - C 2 * h2 * Q1 x + h4

def fixedResidualDerivative (x v : Fin 44 → ℂ) : Poly :=
  normalRestriction x * Q1linear v + quartic x * Q2linear v + Q2 x * quartic v +
    C 2 * evenCubic x * evenCubic v - C 2 * oddCubic x * oddCubic v

def integerRhoDerivative : Fin 44 → IntPolynomial 44 :=
  ![[],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [(2496, [3, 3])],
    [(4992, [2, 3]), (-6400, [3])],
    [(-2560, []), (4992, [1, 3]), (-6400, [2]), (2496, [2, 2]), (-30080, [3])],
    [(-2560, []), (-6400, [1]), (4992, [1, 2]), (-30080, [2])],
    [(12800, []), (-30080, [1]), (2496, [1, 1])],
    [(4992, [0, 3])],
    [(-6400, [0]), (4992, [0, 2])],
    [(-30080, [0]), (4992, [0, 1])],
    [(2496, [0, 0])],
    [(-5120, [3])],
    [(-7680, []), (-5120, [2])],
    [(-3840, []), (-5120, [1])],
    [(-5120, [0])],
    [(-28192, [3])],
    [(-5440, []), (-28192, [2])],
    [(-9440, []), (-28192, [1])],
    [(-1280, []), (-28192, [0])],
    [(-2560, [])],
    [(5916, [])]]

def rhoDerivative (x : Fin 44 → ℂ) : Space 44 :=
  fun i => poly (complexPoly (integerRhoDerivative i)) x

/-- The derivative of the saved full residual expansion in an arbitrary
velocity of the 44 active contact coefficients. -/
theorem fixed_derivative_expansion (x v : Fin 44 → ℂ) :
    (∑ i : Fin 44, C ((systemDeriv polynomials x v) i) * sexticMonomial i) =
      C (832 : ℂ) * fixedResidualDerivative x v := by
  apply MvPolynomial.funext
  intro y
  norm_num [Fin.sum_univ_succ, ContactCubicData.polynomials, ContactCubicData.integerPolys,
    systemDeriv, polyDeriv, monomialDeriv, ContactPolynomialBounds.monomial,
    sexticMonomial, fixedResidualDerivative, normalRestriction, Q1linear, Q2linear,
    Q1, Q2, evenCubic, oddCubic, quartic, h2, h4, leftCore, rightCore]
  ring

/-- The extra rho0 derivative is the actual a^2 normal coefficient, with
the same factor832 as the saved integer equations. -/
theorem rho_derivative_expansion (x : Fin 44 → ℂ) :
    (∑ i : Fin 44, C (rhoDerivative x i) * sexticMonomial i) =
      C (832 : ℂ) * (X 0 ^ 2 * normalRestriction x) := by
  apply MvPolynomial.funext
  intro y
  norm_num [Fin.sum_univ_succ, rhoDerivative, integerRhoDerivative, complexPoly,
    poly, ContactPolynomialBounds.monomial, sexticMonomial, normalRestriction,
    Q1, h2, h4, leftCore, rightCore]
  ring

def secondFactorDot (x v : Fin 44 → ℂ) : Poly :=
  Q1dot v * (C 2 * Q1 x - h2 - X 4)

def linearizedContactExpression (x v : Fin 44 → ℂ) : Poly :=
  Q1dot v * secondFactor x + firstFactor x * secondFactorDot x v +
    Q2linear v * quartic x + Q2 x * quartic v +
    (evenCubic v + oddCubic v) * (evenCubic x - oddCubic x) +
    (evenCubic x + oddCubic x) * (evenCubic v - oddCubic v)

theorem linearized_expression_eq (x v : Fin 44 → ℂ) :
    linearizedContactExpression x v =
      fixedResidualDerivative x v + X 0 ^ 2 * normalRestriction x := by
  dsimp [linearizedContactExpression, firstFactor, secondFactor, secondFactorDot,
    fixedResidualDerivative, normalRestriction, Q1dot]
  norm_num only [map_ofNat]
  ring

theorem exists_linearized_contact (x : Fin 44 → ℂ)
    (hregular : Function.Bijective (systemDeriv polynomials x)) :
    ∃ v : Fin 44 → ℂ, linearizedContactExpression x v = 0 := by
  obtain ⟨v, hv⟩ := hregular.surjective (-rhoDerivative x)
  refine ⟨v, ?_⟩
  have h := fixed_derivative_expansion x v
  rw [hv] at h
  simp only [Pi.neg_apply, map_neg, neg_mul, Finset.sum_neg_distrib] at h
  rw [rho_derivative_expansion] at h
  have hz : C (832 : ℂ) *
      (fixedResidualDerivative x v + X 0 ^ 2 * normalRestriction x) = 0 := by
    rw [mul_add, ← h]
    ring
  rw [linearized_expression_eq]
  exact (mul_eq_zero.mp hz).resolve_left (by simp)

/-- The ab coefficient of Q1dot vanishes while that of Q2 is one; its a^2
coefficient is one. The evaluations below extract these coefficients. -/
theorem Q1dot_not_scalar_Q2 (x v : Fin 44 → ℂ) (c : ℂ) :
    Q1dot v ≠ C c * Q2 x := by
  intro h
  have hp := congrArg (eval (fun i : Fin 5 => if i.val = 0 then (1 : ℂ) else if i.val = 1 then 1 else 0)) h
  have hm := congrArg (eval (fun i : Fin 5 => if i.val = 0 then (1 : ℂ) else if i.val = 1 then -1 else 0)) h
  norm_num [Q1dot, Q1linear, Q1, Q2] at hp hm
  have hc : c = 0 := by
    linear_combination (1/2 : ℂ) * hm - (1/2 : ℂ) * hp
  subst c
  have ha := congrArg (eval (fun i : Fin 5 => if i.val = 0 then (1 : ℂ) else 0)) h
  norm_num [Q1dot, Q1linear, Q1,
    show (2 : Fin 5) ≠ 0 from by decide,
    show (3 : Fin 5) ≠ 0 from by decide] at ha

/-- The u coefficient also excludes adding a multiple of the first quadric.
This is the literal algebraic nontriviality needed before normal-bundle use. -/
theorem Q1dot_not_quadric_span (x v : Fin 44 → ℂ) (a b : ℂ) :
    Q1dot v ≠ C a * firstFactor x + C b * Q2 x := by
  intro h
  have hu := congrArg (eval (fun i : Fin 5 => if i.val = 4 then (1 : ℂ) else 0)) h
  norm_num [Q1dot, Q1linear, Q1, Q2, firstFactor] at hu
  have ha : a = 0 := hu.symm
  subst a
  simp only [map_zero, zero_mul, zero_add] at h
  exact Q1dot_not_scalar_Q2 x v b h

/-- The actual finite root certificate supplies the exact norm identity and
a nontrivial first-order deformation of that identity. -/
theorem exists_actual_contact_and_tangent (hcert : ∀ i, RowCertificate i) :
    ∃ x ∈ closedBall center radius, ∃ v : Fin 44 → ℂ,
      (∀ i, poly (polynomials i) x = 0) ∧
      Function.Bijective (systemDeriv polynomials x) ∧
      WeightedFiberSmoothness.weightedG =
        firstFactor x * secondFactor x + Q2 x * quartic x +
          (evenCubic x + oddCubic x) * (evenCubic x - oddCubic x) ∧
      linearizedContactExpression x v = 0 ∧
      (∀ a b : ℂ, Q1dot v ≠ C a * firstFactor x + C b * Q2 x) := by
  obtain ⟨x, hx, hz, hregular, hcontact⟩ :=
    ContactCubicBounds.exists_regular_target_contact hcert
  obtain ⟨v, hlinear⟩ := exists_linearized_contact x hregular
  exact ⟨x, hx, v, hz, hregular, hcontact, hlinear, Q1dot_not_quadric_span x v⟩


/-- An unconditional actual contact point with a nontrivial first-order norm
identity. All 44 finite arithmetic certificates have already been proved. -/
theorem regular_contact_tangent_exists :
    ∃ x ∈ closedBall center radius, ∃ v : Fin 44 → ℂ,
      (∀ i, poly (polynomials i) x = 0) ∧
      Function.Bijective (systemDeriv polynomials x) ∧
      WeightedFiberSmoothness.weightedG =
        firstFactor x * secondFactor x + Q2 x * quartic x +
          (evenCubic x + oddCubic x) * (evenCubic x - oddCubic x) ∧
      linearizedContactExpression x v = 0 ∧
      (∀ a b : ℂ, Q1dot v ≠ C a * firstFactor x + C b * Q2 x) :=
  exists_actual_contact_and_tangent rowCertificate

#print axioms fixed_derivative_expansion
#print axioms rho_derivative_expansion
#print axioms Q1dot_not_quadric_span
#print axioms exists_actual_contact_and_tangent
#print axioms regular_contact_tangent_exists

end ContactCubicTangent
