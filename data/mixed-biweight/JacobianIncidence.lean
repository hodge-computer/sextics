import Proposal.JacobianModel
import HodgeComputer.Constructions.PolynomialCurves.WeierstrassConic
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.Derivation.MapCoeffs
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.ComputeDegree

/-!
The integral thirteen-equation conic incidence for the mixed-biweight Jacobian.
The coefficient-incidence method follows fqlx's shared constructions and the
accepted ternary-deformation proof. This module specializes that method to the
new weighted Jacobian equation; it does not assert the protected certificate.
Prepared with OpenAI Codex assistance for hodgepodgeconjecture; adapted by fqlx with Codex assistance.
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
  27*c₁^3*c₂*t*(2*r*(r+c₂^6*t)+r^2)-
  108*c₁*c₂*t*((r+c₁^6*t)*(r+c₂^6*t)+r*((r+c₂^6*t)+(r+c₁^6*t)))-
  4*c₁^2*c₂^4*r*t^2

def b256r (c₁ c₂ r t : R) : R :=
  -78732*((r+t)*(r+c₁^6*t)^2*(r+c₂^6*t)^2+
    (r+t)^2*(r+c₁^6*t)*(r+c₂^6*t)^2+
    (r+t)^2*(r+c₁^6*t)^2*(r+c₂^6*t))
  -729*c₁^3*c₂^3*t*(2*r*(r+t)^2*(r+c₂^6*t)+
    r^2*(2*(r+t)*(r+c₂^6*t)+(r+t)^2))
  -216*c₂^3*t^2*((r+c₁^6*t)^2*(r+c₂^6*t)+
    r*(2*(r+c₁^6*t)*(r+c₂^6*t)+(r+c₁^6*t)^2))
  -729*c₁^3*t*(2*r*(r+c₁^6*t)*(r+c₂^6*t)^2+
    r^2*((r+c₂^6*t)^2+2*(r+c₁^6*t)*(r+c₂^6*t)))
  +162*c₁^2*c₂^3*t^2*(2*r*(r+c₁^6*t)*(r+c₂^6*t)+
    r^2*((r+c₂^6*t)+(r+c₁^6*t)))
  -81*c₁^4*c₂^3*t^2*(3*r^2*(r+c₂^6*t)+r^3)
  -6*c₁^3*c₂^6*r^2*t^3

def gradient (c₁ c₂ t : R) (v : Fin 3 → R) : Fin 3 → R :=
  ![-27*a8r c₁ c₂ (v 0) t*(v 1)-b256r c₁ c₂ (v 0) t,
    -17496*(v 1)^2-27*CycleJacobian.a8 c₁ c₂ 1 (v 0) t,11664*(v 2)]

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
  have h108 : coefficientDeriv j (108 : CurvePoly R)=0 := (coefficientDeriv j).map_natCast 108
  have h5832 : coefficientDeriv j (5832 : CurvePoly R)=0 := (coefficientDeriv j).map_natCast 5832
  have h27 : coefficientDeriv j (27 : CurvePoly R)=0 := (coefficientDeriv j).map_natCast 27
  have h39366 : coefficientDeriv j (39366 : CurvePoly R)=0 := (coefficientDeriv j).map_natCast 39366
  have h729 : coefficientDeriv j (729 : CurvePoly R)=0 := (coefficientDeriv j).map_natCast 729
  have h216 : coefficientDeriv j (216 : CurvePoly R)=0 := (coefficientDeriv j).map_natCast 216
  have h162 : coefficientDeriv j (162 : CurvePoly R)=0 := (coefficientDeriv j).map_natCast 162
  have h81 : coefficientDeriv j (81 : CurvePoly R)=0 := (coefficientDeriv j).map_natCast 81
  have h2 : coefficientDeriv j (2 : CurvePoly R)=0 := (coefficientDeriv j).map_natCast 2
  unfold H CycleJacobian.equation CycleJacobian.a8 CycleJacobian.b256
  simp only [map_add,map_sub,map_neg,Derivation.leibniz,Derivation.leibniz_pow,
    h108,h5832,h27,h39366,h729,h216,h162,h81,h2,Derivation.map_one_eq_zero,
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
