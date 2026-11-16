import Proposal.JacobianModel
import HodgeComputer.Constructions.HoldoutCover.HypersurfaceDomain
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! Integrality of the explicit Jacobian cone, using a simple Eisenstein
specialization. The shared Eisenstein lemma is due to the credited
HoldoutCover contributors. Prepared with OpenAI Codex assistance.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace MixedPolarJacobianDomain
open Polynomial
abbrev Coeff := MvPolynomial (Fin 5) ℂ
/-- Coefficient coordinates T,c1,c2,R,X, with outer variable Y. -/
def rhs : Coeff :=
  MvPolynomial.X 4^3+
  MvPolynomial.C (1/432 : ℂ)*MixedPolarJacobian.a8
    (MvPolynomial.X 1) (MvPolynomial.X 2) 1 (MvPolynomial.X 3) (MvPolynomial.X 0)*MvPolynomial.X 4+
  MvPolynomial.C (1/432 : ℂ)*MixedPolarJacobian.b256
    (MvPolynomial.X 1) (MvPolynomial.X 2) 1 (MvPolynomial.X 3) (MvPolynomial.X 0)
def equation : Polynomial Coeff := X^2-C rhs
lemma equation_monic : equation.Monic := monic_X_pow_sub_C _ (by decide)
def specialization : Coeff →+* Polynomial ℂ :=
  MvPolynomial.eval₂Hom C ![X+1,0,0,1,3]
def eisensteinConstant : Polynomial ℂ := C 27*X+C (27/4)*X^2
lemma equation_specialization : equation.map specialization=X^2+C eisensteinConstant := by
  simp only [equation,Polynomial.map_sub,Polynomial.map_pow,Polynomial.map_X,Polynomial.map_C]
  have hr : specialization rhs= -eisensteinConstant := by
    have h432 : (C (1/432 : ℂ) : Polynomial ℂ)*432=1 := by
      calc
        _ = C ((1/432 : ℂ)*432) := by simp only [map_mul,map_ofNat]
        _ = 1 := by norm_num
    have hrat : (C (27/4 : ℂ) : Polynomial ℂ)=2916*C (1/432 : ℂ) := by
      calc
        _ = C ((2916 : ℂ)*(1/432)) := by congr 1; norm_num
        _ = _ := by simp only [map_mul,map_ofNat]
    simp [rhs,specialization,MixedPolarJacobian.a8,MixedPolarJacobian.a432,MixedPolarJacobian.b256,MixedPolarJacobian.b432,eisensteinConstant]
    rw [hrat]
    simp only [map_ofNat,one_div] at h432 ⊢
    linear_combination -27*(1+X)*h432
  rw [hr,map_neg,sub_neg_eq_add]
lemma equation_irreducible : Irreducible equation := by
  apply equation_monic.irreducible_of_irreducible_map specialization
  rw [equation_specialization]
  exact HoldoutConstruction.irreducible_power_add_constant eisensteinConstant
    (by simp [eisensteinConstant]) (by norm_num [eisensteinConstant]) 2 (by decide)
instance equation_domain : IsDomain (AdjoinRoot equation) :=
  AdjoinRoot.isDomain_of_prime equation_irreducible.prime

lemma integral_scaling {S : Type*} [CommRing S] (f : ℂ →+* S)
    (c₁ c₂ r t x y : S) :
    432*(y^2-x^3-f (1/432)*MixedPolarJacobian.a8 c₁ c₂ 1 r t*x-
      f (1/432)*MixedPolarJacobian.b256 c₁ c₂ 1 r t)=
      MixedPolarJacobian.equation c₁ c₂ 1 r t x y := by
  have h432 : (432 : S)*f (1/432)=1 := by
    calc
      _ = f ((432 : ℂ)*(1/432)) := by simp only [map_mul,map_ofNat]
      _ = 1 := by norm_num
  have h432 : (432 : S)*f (1/432)=1 := by
    calc
      _ = f ((432 : ℂ)*(1/432)) := by simp only [map_mul,map_ofNat]
      _ = 1 := by norm_num
  unfold MixedPolarJacobian.equation
  linear_combination (-MixedPolarJacobian.a8 c₁ c₂ 1 r t*x)*h432 +
    (-MixedPolarJacobian.b256 c₁ c₂ 1 r t)*h432
#print axioms equation_irreducible
end MixedPolarJacobianDomain
