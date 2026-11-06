import HodgeComputer.Constructions.FiniteAlgebra.FractionDerivation
import Proposal.PolynomialLift
import Proposal.HomogeneousSubstitution
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

noncomputable section
namespace QuadricContactHorizontal
open MvPolynomial QuadricContactClearing
abbrev Coeff := RegularSpecialization.Coefficients goodParameters

def polynomialHorizontal (k : Fin 4) : Derivation ℚ BasePoly BasePoly :=
  ![(X 0 : BasePoly) • pderiv 0 - (X 3 : BasePoly) • pderiv 3,
    -(X 3 : BasePoly) • pderiv 0 + (X 0 : BasePoly) • pderiv 3,
    (X 1 : BasePoly) • pderiv 1 + (X 4 : BasePoly) • pderiv 4,
    (X 2 : BasePoly) • pderiv 2 + (X 5 : BasePoly) • pderiv 5] k

def horizontal (k : Fin 4) : Derivation ℚ FunctionField FunctionField :=
  QuadricContactFraction.extend (polynomialHorizontal k)

@[simp] theorem horizontal_map (k : Fin 4) (P : BasePoly) :
    horizontal k (baseMap P) = baseMap (polynomialHorizontal k P) :=
  QuadricContactFraction.extend_map _ _

theorem horizontal_map_S (P : BasePoly) :
    horizontal 0 (baseMap P) = baseMap (QuadricContactLift.horizontalS P) := by
  rw [horizontal_map]; rfl
 theorem horizontal_map_T (P : BasePoly) :
    horizontal 1 (baseMap P) = baseMap (QuadricContactLift.horizontalT P) := by
  rw [horizontal_map]; rfl
 theorem horizontal_map_B (P : BasePoly) :
    horizontal 2 (baseMap P) = baseMap (QuadricContactLift.horizontalB P) := by
  rw [horizontal_map]; rfl
 theorem horizontal_map_C (P : BasePoly) :
    horizontal 3 (baseMap P) = baseMap (QuadricContactLift.horizontalC P) := by
  rw [horizontal_map]; rfl

theorem horizontal_parameter_X (k : Fin 4) (j : Fin 2) :
    horizontal k (parameterMap (X j)) = 0 := by
  fin_cases k <;> fin_cases j <;>
    simp [parameterMap, Derivation.leibniz_div, coordinate, horizontal_map,
      polynomialHorizontal, Derivation.sub_apply, Derivation.add_apply,
      Derivation.smul_apply, pderiv_X, Pi.single_apply, smul_eq_mul] <;> ring

theorem horizontal_parameter (k : Fin 4) (P : Parameters) :
    horizontal k (parameterMap P) = 0 := by
  induction P using MvPolynomial.induction_on with
  | C r =>
      simpa only [parameterMap, eval₂Hom_C] using (horizontal k).map_algebraMap r
  | add p q hp hq => simp [hp, hq]
  | mul_X p j hp =>
      rw [map_mul, Derivation.leibniz, hp, horizontal_parameter_X]
      simp

theorem horizontal_regular (k : Fin 4) (r : Coeff) :
    horizontal k (regularParameterMap r) = 0 := by
  obtain ⟨⟨p,q⟩,he⟩ := IsLocalization.surj (RegularSpecialization.denominators goodParameters) r
  have hm := congrArg regularParameterMap he
  simp only [map_mul, regularParameterMap_algebraMap] at hm
  have hd := congrArg (horizontal k) hm
  simp only [Derivation.leibniz, horizontal_parameter, smul_eq_mul, mul_zero, zero_add] at hd
  exact (mul_eq_zero.mp hd).resolve_left (parameterMap_ne_zero_of_good q.property)

def active (j : Fin 4) : FunctionField :=
  ![2 * (coordinate 0 ^ 2 + coordinate 3 ^ 2),
    4 * coordinate 0 * coordinate 3, coordinate 1 ^ 2, coordinate 2 ^ 2] j

def scale (k : Fin 4) : FunctionField :=
  ![4 * (coordinate 0 ^ 2 - coordinate 3 ^ 2),
    4 * (coordinate 0 ^ 2 - coordinate 3 ^ 2),
    2 * coordinate 1 ^ 2, 2 * coordinate 2 ^ 2] k

@[simp] theorem horizontal_natCast (k : Fin 4) (n : ℕ) :
    horizontal k (n : FunctionField) = 0 := (horizontal k).map_natCast n

@[simp] theorem horizontal_two (k : Fin 4) :
    horizontal k (2 : FunctionField) = 0 := (horizontal k).map_natCast 2
@[simp] theorem horizontal_four (k : Fin 4) :
    horizontal k (4 : FunctionField) = 0 := (horizontal k).map_natCast 4

theorem horizontal_active (k j : Fin 4) :
    horizontal k (active j) = if j = k then scale k else 0 := by
  fin_cases k <;> fin_cases j <;>
    simp [active, scale, coordinate, Derivation.leibniz_pow, Derivation.leibniz,
      horizontal_map, polynomialHorizontal, Derivation.sub_apply, Derivation.add_apply,
      Derivation.smul_apply, pderiv_X, Pi.single_apply, smul_eq_mul,
      horizontal_two, horizontal_four] <;> ring_nf <;> simp

def activeMap : MvPolynomial (Fin 4) Coeff →+* FunctionField :=
  eval₂Hom regularParameterMap active

@[simp] theorem activeMap_X (j : Fin 4) : activeMap (X j) = active j := by simp [activeMap]
@[simp] theorem activeMap_C (r : Coeff) : activeMap (C r) = regularParameterMap r := by simp [activeMap]

/-- Actual chain rule for the rational substitution with passive regular coefficients. -/
theorem horizontal_activeMap (k : Fin 4) (P : MvPolynomial (Fin 4) Coeff) :
    horizontal k (activeMap P) = scale k * activeMap (pderiv k P) := by
  induction P using MvPolynomial.induction_on with
  | C r => simp [horizontal_regular]
  | add p q hp hq => simp only [map_add, hp, hq, mul_add]
  | mul_X p j hp =>
      simp only [pderiv_mul, map_add, map_mul, activeMap_X, Derivation.leibniz,
        smul_eq_mul, hp, pderiv_X, Pi.single_apply, apply_ite, map_one, map_zero,
        horizontal_active]
      by_cases h : j = k
      · subst j; simp; ring
      · have h' : k ≠ j := Ne.symm h
        simp [h, h']; ring

end QuadricContactHorizontal
#print axioms QuadricContactHorizontal.horizontal_regular
#print axioms QuadricContactHorizontal.horizontal_activeMap
