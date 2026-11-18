import HodgeTestbed.Algebra
import Proposal.HoldoutAlgebra
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! Polynomial endpoint lift, with all derivatives in protected coordinate order
`(x,a,c,y,b,d)`. The normalized active coordinates are `(U,V,S,T)` with
`T=k*c*d`. Multiplication by `x²*a²` clears the two horizontal denominators.
The source and divergence hypotheses below are actual polynomial derivative
identities; they must be supplied by the cubic construction. -/

noncomputable section
namespace HoldoutEndpointLift
open MvPolynomial HodgeTestbed

variable {R : Type*} [CommRing R]
abbrev Poly := MvPolynomial (Fin 6) R

def delta (k : R) : Poly (R := R) := X 2^2-C (k^2)*X 5^2
def clearing : Poly (R := R) := X 0^2*X 1^2

def horizontalU (P : Poly (R := R)) : Poly (R := R) := X 0*pderiv 0 P+X 3*pderiv 3 P
def horizontalV (P : Poly (R := R)) : Poly (R := R) := X 1*pderiv 1 P+X 4*pderiv 4 P
def horizontalS (P : Poly (R := R)) : Poly (R := R) := X 2*pderiv 2 P-X 5*pderiv 5 P
def horizontalT (k : R) (P : Poly (R := R)) : Poly (R := R) :=
  -2*C k*X 5*pderiv 2 P+2*C (k^2)*X 2*pderiv 5 P

def denominator (Q : Poly (R := R)) : Poly (R := R) := clearing*Q

def numerators (k : R) (PU PV PS PT : Poly (R := R)) : Fin 6 → Poly (R := R) :=
  ![delta k*X 0*X 1^2*PU,
    delta k*X 1*X 0^2*PV,
    clearing*(X 2*PS-2*C k*X 5*PT),
    delta k*X 3*X 1^2*PU,
    delta k*X 4*X 0^2*PV,
    clearing*(-X 5*PS+2*C (k^2)*X 2*PT)]

def source (k : R) (F PU PV PS PT : Poly (R := R)) : Poly (R := R) :=
  delta k*X 1^2*PU*horizontalU F +
    delta k*X 0^2*PV*horizontalV F +
    clearing*(PS*horizontalS F+PT*horizontalT k F)

def divergenceCondition (k : R) (Q PU PV PS PT : Poly (R := R)) : Poly (R := R) :=
  delta k*X 1^2*(Q*horizontalU PU-PU*horizontalU Q) +
    delta k*X 0^2*(Q*horizontalV PV-PV*horizontalV Q) +
    clearing*(Q*horizontalS PS-PS*horizontalS Q+
      Q*horizontalT k PT-PT*horizontalT k Q)

theorem lift_directional (k : R) (F PU PV PS PT : Poly (R := R)) :
    directional F (numerators k PU PV PS PT) = source k F PU PV PS PT := by
  simp only [directional, Fin.sum_univ_six, numerators, Matrix.cons_val,
    source, horizontalU, horizontalV, horizontalS, horizontalT]
  ring

theorem lift_divergence_numerator (k : R) (Q PU PV PS PT : Poly (R := R)) :
    divergenceNumerator (denominator Q) (numerators k PU PV PS PT) =
      clearing*divergenceCondition k Q PU PV PS PT := by
  have htwo (i : Fin 6) : pderiv i (2 : Poly (R := R)) = 0 :=
    (pderiv i).map_natCast 2
  simp only [divergenceNumerator, divergence, directional, Fin.sum_univ_six,
    numerators, Matrix.cons_val, denominator, clearing, delta,
    divergenceCondition, horizontalU, horizontalV, horizontalS, horizontalT]
  simp only [map_add, map_sub, map_neg, pderiv_mul, pderiv_pow,
    pderiv_X, pderiv_C, Pi.single_apply, htwo, Fin.isValue]
  norm_num [Fin.ext_iff]
  ring

/-- The pole-two strict cleared equation. -/
theorem lift_strict_q2 (k : R) (F A Q PU PV PS PT : Poly (R := R))
    (hs : 2*source k F PU PV PS PT=A*denominator Q)
    (hd : divergenceCondition k Q PU PV PS PT=0) :
    A*(denominator Q)^2 -
      2*denominator Q*directional F (numerators k PU PV PS PT) +
      F*divergenceNumerator (denominator Q) (numerators k PU PV PS PT)=0 := by
  rw [lift_directional,lift_divergence_numerator,hd,mul_zero,mul_zero,add_zero]
  linear_combination -denominator Q*hs

theorem delta_homogeneous (k : R) : (delta k).IsHomogeneous 2 := by
  exact (isHomogeneous_X_pow 2 2).sub ((isHomogeneous_X_pow 5 2).C_mul (k^2))

theorem clearing_homogeneous : (clearing (R := R)).IsHomogeneous 4 := by
  exact (isHomogeneous_X_pow 0 2).mul (isHomogeneous_X_pow 1 2)

theorem denominator_homogeneous {Q : Poly (R := R)} {h : ℕ}
    (hQ : Q.IsHomogeneous h) : (denominator Q).IsHomogeneous (h+4) := by
  simpa only [denominator,Nat.add_comm] using clearing_homogeneous.mul hQ

theorem numerators_homogeneous (k : R) {PU PV PS PT : Poly (R := R)} {h : ℕ}
    (hU : PU.IsHomogeneous h) (hV : PV.IsHomogeneous h)
    (hS : PS.IsHomogeneous h) (hT : PT.IsHomogeneous h) :
    ∀ i, (numerators k PU PV PS PT i).IsHomogeneous (h+5) := by
  have hu (i : Fin 6) :=
    (((delta_homogeneous k).mul (isHomogeneous_X R i)).mul
      (isHomogeneous_X_pow 1 2)).mul hU
  have hv (i : Fin 6) :=
    (((delta_homogeneous k).mul (isHomogeneous_X R i)).mul
      (isHomogeneous_X_pow 0 2)).mul hV
  have hs := clearing_homogeneous.mul
    (((isHomogeneous_X R 2).mul hS).sub
      (((isHomogeneous_X R 5).C_mul (2*k)).mul hT))
  have ht := clearing_homogeneous.mul
    ((((isHomogeneous_X R 5).neg).mul hS).add
      (((isHomogeneous_X R 2).C_mul (2*k^2)).mul hT))
  intro i
  fin_cases i
  · simpa [numerators,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using hu 0
  · simpa [numerators,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using hv 1
  · simpa [numerators,map_mul,map_ofNat,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using hs
  · simpa [numerators,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using hu 3
  · simpa [numerators,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using hv 4
  · simpa [numerators,map_mul,map_ofNat,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using ht

end HoldoutEndpointLift

namespace HoldoutChainRule
open MvPolynomial

/-- A coefficient-independent chain rule usable after localization. Passive
coefficients are not silently constant: their annihilation is an explicit
hypothesis, to be proved for the endpoint horizontal derivations. -/
theorem eval₂_pderiv {K R S : Type*} [CommRing K] [CommRing R] [CommRing S]
    [Algebra K S] (D : Derivation K S S) (f : R →+* S)
    (v : Fin 4 → S) (i : Fin 4) (s : S)
    (hc : ∀ r, D (f r)=0)
    (hv : ∀ j, D (v j)=if j=i then s else 0)
    (P : MvPolynomial (Fin 4) R) :
    D (eval₂Hom f v P)=s*eval₂Hom f v (pderiv i P) := by
  induction P using MvPolynomial.induction_on with
  | C r => simp [hc]
  | add p q hp hq => simp only [map_add,hp,hq,mul_add]
  | mul_X p j hp =>
      simp only [pderiv_mul,map_add,map_mul,eval₂Hom_X',Derivation.leibniz,
        smul_eq_mul,hp,pderiv_X,Pi.single_apply,apply_ite,map_one,map_zero,hv]
      by_cases h : j=i
      · subst j; simp [hv]; ring
      · have h' : i≠j := Ne.symm h
        simp [h,h',hv]; ring

end HoldoutChainRule

#print axioms HoldoutEndpointLift.lift_strict_q2
#print axioms HoldoutChainRule.eval₂_pderiv
