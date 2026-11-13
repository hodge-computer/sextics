import Proposal.JacobianModel
import HodgeComputer.Constructions.PolynomialCurves.WeierstrassConic
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.Derivation.MapCoeffs
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.ComputeDegree

/-!
The integral thirteen-equation conic incidence for the holdout-moving-branch Jacobian.
The coefficient-incidence method follows fqlx's shared constructions and the
accepted ternary-deformation proof. This module specializes that method to the
new weighted Jacobian equation; it does not assert the protected certificate.
Prepared with OpenAI Codex assistance for hodgepodgeconjecture; transitive cubic adaptation by fqlx, specialized here for benediamond with Codex assistance.
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
  -1764*c₁^7*c₂^8*t^3 - 3528*c₁^7*c₂^2*r*t^2 + 8232*c₁^3*c₂^7*r*t^2 + 12348*c₁^3*c₂*r^2*t - 56*c₁^2*c₂^6*r*t^2 - 3528*c₁*c₂^8*r*t^2 - 5292*c₁*c₂^2*r^2*t

def b256r (c₁ c₂ r t : R) : R :=
  -1500282*c₁^12*c₂^12*r*t^4 - 1500606*c₁^12*c₂^12*t^5 - 4500846*c₁^12*c₂^6*r^2*t^3 - 6001776*c₁^12*c₂^6*r*t^4 - 1500282*c₁^12*c₂^6*t^5 - 3000564*c₁^12*r^3*t^2 - 4500846*c₁^12*r^2*t^3 - 1500282*c₁^12*r*t^4 - 222264*c₁^9*c₂^12*r*t^4 - 666792*c₁^9*c₂^6*r^2*t^3 - 444528*c₁^9*r^3*t^2 + 4536*c₁^8*c₂^11*r*t^4 + 6804*c₁^8*c₂^5*r^2*t^3 - 4500846*c₁^6*c₂^12*r^2*t^3 - 6002424*c₁^6*c₂^12*r*t^4 - 1500282*c₁^6*c₂^12*t^5 - 12002256*c₁^6*c₂^6*r^3*t^2 - 18005328*c₁^6*c₂^6*r^2*t^3 - 6001128*c₁^6*c₂^6*r*t^4 - 7501410*c₁^6*r^4*t - 12002256*c₁^6*r^3*t^2 - 4500846*c₁^6*r^2*t^3 - 31752*c₁^4*c₂^10*r^2*t^3 - 42336*c₁^4*c₂^4*r^3*t^2 - 333396*c₁^3*c₂^12*r^2*t^3 - 444528*c₁^3*c₂^9*r^3*t^2 - 666864*c₁^3*c₂^9*r^2*t^3 - 222264*c₁^3*c₂^9*r*t^4 - 889056*c₁^3*c₂^6*r^3*t^2 - 555660*c₁^3*c₂^3*r^4*t - 889056*c₁^3*c₂^3*r^3*t^2 - 333396*c₁^3*c₂^3*r^2*t^3 - 555660*c₁^3*r^4*t + 6804*c₁^2*c₂^11*r^2*t^3 + 9072*c₁^2*c₂^5*r^3*t^2 - 3000564*c₂^12*r^3*t^2 - 4501818*c₂^12*r^2*t^3 - 1500282*c₂^12*r*t^4 - 7501410*c₂^6*r^4*t - 12003552*c₂^6*r^3*t^2 - 4500846*c₂^6*r^2*t^3 - 4500846*r^5 - 7501410*r^4*t - 3000564*r^3*t^2

def gradient (c₁ c₂ t : R) (v : Fin 3 → R) : Fin 3 → R :=
  ![-27*a8r c₁ c₂ (v 0) t*(v 1)-b256r c₁ c₂ (v 0) t,
    -333396*(v 1)^2-27*CycleJacobian.a8 c₁ c₂ 1 (v 0) t,222264*(v 2)]

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
  have h24 : coefficientDeriv j (24 : CurvePoly R)=0 := (coefficientDeriv j).map_natCast 24
  have h27 : coefficientDeriv j (27 : CurvePoly R)=0 := (coefficientDeriv j).map_natCast 27
  have h28 : coefficientDeriv j (28 : CurvePoly R)=0 := (coefficientDeriv j).map_natCast 28
  have h324 : coefficientDeriv j (324 : CurvePoly R)=0 := (coefficientDeriv j).map_natCast 324
  have h1764 : coefficientDeriv j (1764 : CurvePoly R)=0 := (coefficientDeriv j).map_natCast 1764
  have h2268 : coefficientDeriv j (2268 : CurvePoly R)=0 := (coefficientDeriv j).map_natCast 2268
  have h4116 : coefficientDeriv j (4116 : CurvePoly R)=0 := (coefficientDeriv j).map_natCast 4116
  have h10584 : coefficientDeriv j (10584 : CurvePoly R)=0 := (coefficientDeriv j).map_natCast 10584
  have h111132 : coefficientDeriv j (111132 : CurvePoly R)=0 := (coefficientDeriv j).map_natCast 111132
  have h750141 : coefficientDeriv j (750141 : CurvePoly R)=0 := (coefficientDeriv j).map_natCast 750141
  unfold H CycleJacobian.equation CycleJacobian.a8 CycleJacobian.b256
  simp only [map_add,map_sub,map_neg,h2,h24,h27,h28,h324,h1764,h2268,h4116,h10584,h111132,h750141,Derivation.leibniz,Derivation.leibniz_pow,
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
