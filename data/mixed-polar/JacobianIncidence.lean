import Proposal.JacobianModel
import HodgeComputer.Constructions.PolynomialCurves.WeierstrassConic
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.Derivation.MapCoeffs
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.ComputeDegree

/-!
The integral thirteen-equation conic incidence for the mixed-polar Jacobian.
The coefficient-incidence method follows fqlx's shared constructions and the
accepted ternary-deformation proof. This module specializes that method to the
new weighted Jacobian equation; it does not assert the protected certificate.
Adapted from the accepted cyclic and transitive constructions of hodgepodgeconjecture and fqlx; this mixed-polar specialization was prepared for benediamond with OpenAI Codex assistance.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
namespace CycleJacobianIncidence
open Polynomial
export WeierstrassConic (Coeff CurvePoly cv cp curve coefficientDeriv coefficientDeriv_coeff coefficientDeriv_C
  coefficientDeriv_X slotCoordinate slotDegree curve_coefficientDeriv curveEval valueCurve curveEval_eq_valueCurve)
variable {R : Type*} [CommRing R]

/-- The fixed-alpha model, in curve-coordinate order R,X,Y. -/
def H (c₁ c₂ t : R) (v : Fin 3 → R) : R :=
  CycleJacobian.equation c₁ c₂ 1 (v 0) t (v 1) (v 2)

def a8r (c₁ c₂ r t : R) : R :=
  -8*c₁^4*c₂^7*r*t^2 - 4*c₁^4*c₂^7*t^3 - 12*c₁^4*c₂*r^2*t - 8*c₁^4*c₂*r*t^2 + 2*c₁^3*c₂^7*r*t^2 + 3*c₁^3*c₂*r^2*t

def b256r (c₁ c₂ r t : R) : R :=
  -5832*c₁^12*c₂^12*r*t^4 - 5832*c₁^12*c₂^12*t^5 - 17496*c₁^12*c₂^6*r^2*t^3 - 23328*c₁^12*c₂^6*r*t^4 - 5832*c₁^12*c₂^6*t^5 - 11664*c₁^12*r^3*t^2 - 17496*c₁^12*r^2*t^3 - 5832*c₁^12*r*t^4 + 648*c₁^10*c₂^12*r*t^4 + 324*c₁^10*c₂^12*t^5 + 1944*c₁^10*c₂^6*r^2*t^3 + 1296*c₁^10*c₂^6*r*t^4 + 1296*c₁^10*r^3*t^2 + 972*c₁^10*r^2*t^3 - 140*c₁^9*c₂^12*r*t^4 - 16*c₁^9*c₂^12*t^5 - 420*c₁^9*c₂^6*r^2*t^3 - 64*c₁^9*c₂^6*r*t^4 - 280*c₁^9*r^3*t^2 - 48*c₁^9*r^2*t^3 + 6*c₁^8*c₂^12*r*t^4 + 18*c₁^8*c₂^6*r^2*t^3 + 12*c₁^8*r^3*t^2 - 17496*c₁^6*c₂^12*r^2*t^3 - 23328*c₁^6*c₂^12*r*t^4 - 5832*c₁^6*c₂^12*t^5 - 46656*c₁^6*c₂^6*r^3*t^2 - 69984*c₁^6*c₂^6*r^2*t^3 - 23328*c₁^6*c₂^6*r*t^4 - 29160*c₁^6*r^4*t - 46656*c₁^6*r^3*t^2 - 17496*c₁^6*r^2*t^3 + 972*c₁^4*c₂^12*r^2*t^3 + 648*c₁^4*c₂^12*r*t^4 + 2592*c₁^4*c₂^6*r^3*t^2 + 1944*c₁^4*c₂^6*r^2*t^3 + 1620*c₁^4*r^4*t + 1296*c₁^4*r^3*t^2 - 162*c₁^3*c₂^12*r^2*t^3 - 216*c₁^3*c₂^9*r^3*t^2 - 324*c₁^3*c₂^9*r^2*t^3 - 108*c₁^3*c₂^9*r*t^4 - 432*c₁^3*c₂^6*r^3*t^2 - 270*c₁^3*c₂^3*r^4*t - 432*c₁^3*c₂^3*r^3*t^2 - 162*c₁^3*c₂^3*r^2*t^3 - 270*c₁^3*r^4*t - 11664*c₂^12*r^3*t^2 - 17496*c₂^12*r^2*t^3 - 5832*c₂^12*r*t^4 - 29160*c₂^6*r^4*t - 46656*c₂^6*r^3*t^2 - 17496*c₂^6*r^2*t^3 - 17496*r^5 - 29160*r^4*t - 11664*r^3*t^2

def gradient (c₁ c₂ t : R) (v : Fin 3 → R) : Fin 3 → R :=
  ![-54*a8r c₁ c₂ (v 0) t*(v 1)-b256r c₁ c₂ (v 0) t,
    -1296*(v 1)^2-54*CycleJacobian.a8 c₁ c₂ 1 (v 0) t,864*(v 2)]

lemma H_map {S : Type*} [CommRing S] (f : R →+* S)
    (c₁ c₂ t : R) (v : Fin 3 → R) :
    f (H c₁ c₂ t v)=H (f c₁) (f c₂) (f t) (fun i => f (v i)) := by
  simp only [H,CycleJacobian.equation,CycleJacobian.a8,CycleJacobian.b256,
    map_add,map_sub,map_mul,map_pow,map_neg,map_ofNat,map_one]
lemma gradient_map {S : Type*} [CommRing S] (f : R →+* S)
    (c₁ c₂ t : R) (v : Fin 3 → R) (i : Fin 3) :
    f (gradient c₁ c₂ t v i)=gradient (f c₁) (f c₂) (f t) (fun j => f (v j)) i := by
  fin_cases i <;> simp [gradient,a8r,b256r,CycleJacobian.a8,map_ofNat]

def equations (c₁ c₂ : R) (k : Fin 2 → R) (i : Fin 13) : Coeff R :=
  (H (cp c₁) (cp c₂) X (curve k)).coeff i.val

lemma H_coefficientDeriv (c₁ c₂ : R) (k : Fin 2 → R) (j : Fin 13) :
    coefficientDeriv j (H (cp c₁) (cp c₂) X (curve k)) =
      gradient (cp c₁) (cp c₂) X (curve k) (slotCoordinate j)*X^slotDegree j := by
  have h2 : coefficientDeriv j (2 : CurvePoly R)=0 := (coefficientDeriv j).map_natCast 2
  have h3 : coefficientDeriv j (3 : CurvePoly R)=0 := (coefficientDeriv j).map_natCast 3
  have h4 : coefficientDeriv j (4 : CurvePoly R)=0 := (coefficientDeriv j).map_natCast 4
  have h16 : coefficientDeriv j (16 : CurvePoly R)=0 := (coefficientDeriv j).map_natCast 16
  have h54 : coefficientDeriv j (54 : CurvePoly R)=0 := (coefficientDeriv j).map_natCast 54
  have h324 : coefficientDeriv j (324 : CurvePoly R)=0 := (coefficientDeriv j).map_natCast 324
  have h432 : coefficientDeriv j (432 : CurvePoly R)=0 := (coefficientDeriv j).map_natCast 432
  have h2916 : coefficientDeriv j (2916 : CurvePoly R)=0 := (coefficientDeriv j).map_natCast 2916
  unfold H CycleJacobian.equation CycleJacobian.a8 CycleJacobian.b256
  simp only [map_add,map_sub,map_neg,h2,h3,h4,h16,h54,h324,h432,h2916,Derivation.leibniz,Derivation.leibniz_pow,
    Derivation.map_one_eq_zero,
    cp,coefficientDeriv_C,MvPolynomial.pderiv_C,Polynomial.C_0,coefficientDeriv_X,
    smul_zero,zero_smul,add_zero,curve_coefficientDeriv,smul_eq_mul]
  fin_cases j <;> simp [gradient,a8r,b256r,CycleJacobian.a8,slotCoordinate,slotDegree] <;> ring
lemma equations_pderiv (c₁ c₂ : R) (k : Fin 2 → R) (i j : Fin 13) :
    MvPolynomial.pderiv j (equations c₁ c₂ k i)=
      (gradient (cp c₁) (cp c₂) X (curve k) (slotCoordinate j)*X^slotDegree j).coeff i.val := by
  rw [equations,← coefficientDeriv_coeff,H_coefficientDeriv]
lemma H_natDegree_le (c₁ c₂ : R) (k : Fin 2 → R) :
    (H (cp c₁) (cp c₂) X (curve k)).natDegree ≤ 12 := by
  unfold H CycleJacobian.equation CycleJacobian.a8 CycleJacobian.b256 curve cv cp
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val]
  compute_degree

lemma equations_eval {S : Type*} [CommRing S] (c₁ c₂ : R) (k : Fin 2 → R)
    (f : R →+* S) (v : Fin 13 → S) (i : Fin 13) :
    MvPolynomial.eval₂Hom f v (equations c₁ c₂ k i)=
      (H (C (f c₁)) (C (f c₂)) X (curveEval k f v)).coeff i.val := by
  change (MvPolynomial.eval₂Hom f v) ((H (cp c₁) (cp c₂) X (curve k)).coeff i.val) = _
  rw [← Polynomial.coeff_map]
  congr 1
  change (Polynomial.mapRingHom (MvPolynomial.eval₂Hom f v)) (H (cp c₁) (cp c₂) X (curve k)) = _
  rw [H_map]
  simp only [Polynomial.coe_mapRingHom,cp,Polynomial.map_C,
    Polynomial.map_X,MvPolynomial.eval₂Hom_C,curveEval]
  rfl
lemma equations_pderiv_eval {S : Type*} [CommRing S] (c₁ c₂ : R) (k : Fin 2 → R)
    (f : R →+* S) (v : Fin 13 → S) (i j : Fin 13) :
    MvPolynomial.eval₂Hom f v (MvPolynomial.pderiv j (equations c₁ c₂ k i))=
      (gradient (C (f c₁)) (C (f c₂)) X (curveEval k f v) (slotCoordinate j)*X^slotDegree j).coeff i.val := by
  rw [equations_pderiv,← Polynomial.coeff_map,Polynomial.map_mul,Polynomial.map_pow,Polynomial.map_X]
  congr 2
  change (Polynomial.mapRingHom (MvPolynomial.eval₂Hom f v))
    (gradient (cp c₁) (cp c₂) X (curve k) (slotCoordinate j)) = _
  rw [gradient_map]
  simp only [Polynomial.coe_mapRingHom,cp,Polynomial.map_C,
    Polynomial.map_X,MvPolynomial.eval₂Hom_C,curveEval]
  rfl

end CycleJacobianIncidence
