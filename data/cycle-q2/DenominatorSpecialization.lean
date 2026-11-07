import Proposal.CurrentCore
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.RingTheory.Coprime.Basic

/-! The actual monic specialization and legal derivative pivot.
These small identities do not depend on the archived physical-current DAG. -/
noncomputable section
set_option maxHeartbeats 2000000
namespace CycleQ2Concrete.Denominator
abbrev UPoly := Polynomial ℂ

def specVars : Fin 6 → UPoly := ![Polynomial.X, 1, 1, 2, 2, 1]
def spec : CycleQ2Concrete.Poly →+* UPoly :=
  MvPolynomial.eval₂Hom Polynomial.C specVars

def f : UPoly := Polynomial.X^6 + 2*Polynomial.X^3 + Polynomial.X + 132

@[simp] lemma spec_C (c : ℂ) : spec (MvPolynomial.C c) = Polynomial.C c := by
  simp [spec]
@[simp] lemma spec_X (i : Fin 6) : spec (MvPolynomial.X i) = specVars i := by
  simp [spec]

/-- Exact binding of the small univariate polynomial to the original sextic. -/
theorem specialized_originalF : spec CycleQ2Workspace.originalF = f := by
  apply Polynomial.funext
  intro x
  unfold CycleQ2Workspace.originalF HodgeSubmission.F f
  simp [map_add, map_mul, map_pow, specVars]
  norm_num <;> ring

abbrev Coeff := MvPolynomial (Fin 5) ℂ

def equation : Polynomial Coeff :=
  Polynomial.X^6 +
    (Polynomial.C (MvPolynomial.C (1/2) * MvPolynomial.X 0 * MvPolynomial.X 2 * MvPolynomial.X 3) * Polynomial.X^3 +
    Polynomial.C (MvPolynomial.C (1/2) * MvPolynomial.X 1^3 * MvPolynomial.X 2 * MvPolynomial.X 4) * Polynomial.X +
    Polynomial.C ((MvPolynomial.X 0)^6 + (MvPolynomial.X 1)^6 + (MvPolynomial.X 2)^6 +
      (MvPolynomial.X 3)^6 + (MvPolynomial.X 4)^6 +
      MvPolynomial.C (1/2) * MvPolynomial.X 0^3 * MvPolynomial.X 1 * MvPolynomial.X 3 * MvPolynomial.X 4))

lemma equation_monic : equation.Monic := by
  apply Polynomial.monic_X_pow_add
  apply lt_of_le_of_lt (Polynomial.degree_add_le _ _)
  apply max_lt
  · apply lt_of_le_of_lt (Polynomial.degree_add_le _ _)
    apply max_lt
    · exact lt_of_le_of_lt (Polynomial.degree_C_mul_X_pow_le 3 _) (by decide)
    · simpa using lt_of_le_of_lt (Polynomial.degree_C_mul_X_pow_le 1 _) (by decide : (1 : WithBot ℕ) < 6)
  · exact lt_of_le_of_lt Polynomial.degree_C_le (by decide)

lemma originalF_univariate :
    MvPolynomial.finSuccEquiv ℂ 5 CycleQ2Workspace.originalF = equation := by
  have he : (Fin.cases (Polynomial.X : Polynomial Coeff) (fun j => Polynomial.C (MvPolynomial.X j))) =
      ![Polynomial.X,Polynomial.C (MvPolynomial.X 0),Polynomial.C (MvPolynomial.X 1),
        Polynomial.C (MvPolynomial.X 2),Polynomial.C (MvPolynomial.X 3),Polynomial.C (MvPolynomial.X 4)] := by
    funext i
    fin_cases i <;> rfl
  simp [CycleQ2Workspace.originalF,HodgeSubmission.F,equation,MvPolynomial.finSuccEquiv_apply,he]
  ring

def coefficientSpec : Coeff →+* ℂ := MvPolynomial.eval ![1,1,2,2,1]

lemma mapped_univariate (P : CycleQ2Concrete.Poly) :
    (MvPolynomial.finSuccEquiv ℂ 5 P).map coefficientSpec = spec P := by
  have he : (Fin.cases (Polynomial.X : Polynomial Coeff) (fun j => Polynomial.C (MvPolynomial.X j))) =
      ![Polynomial.X,Polynomial.C (MvPolynomial.X 0),Polynomial.C (MvPolynomial.X 1),
        Polynomial.C (MvPolynomial.X 2),Polynomial.C (MvPolynomial.X 3),Polynomial.C (MvPolynomial.X 4)] := by
    funext i
    fin_cases i <;> rfl
  induction P using MvPolynomial.induction_on with
  | C a => simp [MvPolynomial.finSuccEquiv_apply,coefficientSpec,spec]
  | add p q hp hq => simp only [map_add,Polynomial.map_add,hp,hq]
  | mul_X p i hp =>
    rw [map_mul,Polynomial.map_mul,hp,map_mul]
    congr 1
    fin_cases i <;> simp [MvPolynomial.finSuccEquiv_apply,he,coefficientSpec,spec,specVars,Polynomial.C_ofNat]

lemma ambient_relPrime_of_specialization (D : CycleQ2Concrete.Poly)
    (h : IsRelPrime f (spec D)) : IsRelPrime CycleQ2Workspace.originalF D := by
  apply IsRelPrime.of_map (MvPolynomial.finSuccEquiv ℂ 5)
  apply HodgeComputer.relPrime_of_specialization coefficientSpec
  · rw [originalF_univariate]
    rw [equation_monic]
    exact isUnit_one
  · rw [mapped_univariate,mapped_univariate,specialized_originalF]
    exact h

/-- The five tangent directions use this derivative as their pivot. Its
specialization is linear, so its legality requires no irreducibility assumption. -/
lemma specialized_tangentPivot :
    spec (MvPolynomial.pderiv (5 : Fin 6) CycleQ2Workspace.originalF) =
      Polynomial.X + 7 := by
  have h0 : specVars 0 = Polynomial.X := rfl
  have h1 : specVars 1 = (1 : UPoly) := rfl
  have h2 : specVars 2 = (1 : UPoly) := rfl
  have h3 : specVars 3 = (2 : UPoly) := rfl
  have h4 : specVars 4 = (2 : UPoly) := rfl
  have h5 : specVars 5 = (1 : UPoly) := rfl
  apply Polynomial.funext
  intro x
  unfold CycleQ2Workspace.originalF HodgeSubmission.F
  norm_num [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_pow,
    MvPolynomial.pderiv_X, Pi.single_apply, map_add, map_mul, map_pow,
    Fin.ext_iff, h0, h1, h2, h3, h4, h5, map_ofNat]
  ring

/-- A small exact Bezout identity: f(-7) = 117088. -/
lemma tangentPivot_bezout : IsCoprime f (Polynomial.X + 7) := by
  refine ⟨Polynomial.C (1 / 117088 : ℂ),
    -Polynomial.C (1 / 117088 : ℂ) *
      (Polynomial.X ^ 5 - 7 * Polynomial.X ^ 4 + 49 * Polynomial.X ^ 3 -
        341 * Polynomial.X ^ 2 + 2387 * Polynomial.X - 16708), ?_⟩
  apply Polynomial.funext
  intro x
  simp only [f, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_neg, Polynomial.eval_C, Polynomial.eval_X]
  norm_num <;> ring

/-- Dividing by the selected partial derivative introduces an allowed pole. -/
theorem tangentPivot_legal :
    IsRelPrime CycleQ2Workspace.originalF
      (MvPolynomial.pderiv (5 : Fin 6) CycleQ2Workspace.originalF) := by
  apply ambient_relPrime_of_specialization
  rw [specialized_tangentPivot]
  exact tangentPivot_bezout.isRelPrime

theorem tangentPivot_ne_zero :
    MvPolynomial.pderiv (5 : Fin 6) CycleQ2Workspace.originalF ≠ 0 := by
  intro h
  have hs := specialized_tangentPivot
  rw [h, map_zero] at hs
  have hc := congrArg (fun p : UPoly => p.coeff 1) hs
  norm_num at hc

#print axioms tangentPivot_legal
#print axioms tangentPivot_ne_zero

end CycleQ2Concrete.Denominator
