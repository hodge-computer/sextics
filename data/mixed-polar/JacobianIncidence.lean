import Proposal.JacobianModel
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
Adapted from the accepted constructions of fqlx and hodgepodgeconjecture.
Prepared for benediamond with OpenAI Codex assistance.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
namespace MixedPolarJacobianIncidence
open Polynomial
variable {R : Type*} [CommRing R]

/-- The fixed-alpha model, in curve-coordinate order R,X,Y. -/
def H (c₁ c₂ t : R) (v : Fin 3 → R) : R :=
  MixedPolarJacobian.equation c₁ c₂ 1 (v 0) t (v 1) (v 2)

def a8r (cOne cTwo r t : R) : R :=
  -432*cOne^4*cTwo^7*r*t^2 -216*cOne^4*cTwo^7*t^3 -648*cOne^4*cTwo*r^2*t -432*cOne^4*cTwo*r*t^2 +108*cOne^3*cTwo^7*r*t^2 +162*cOne^3*cTwo*r^2*t
def b256r (cOne cTwo r t : R) : R :=
  -5832*cOne^12*cTwo^12*r*t^4 -5832*cOne^12*cTwo^12*t^5 -17496*cOne^12*cTwo^6*r^2*t^3 -23328*cOne^12*cTwo^6*r*t^4 -5832*cOne^12*cTwo^6*t^5 -11664*cOne^12*r^3*t^2 -17496*cOne^12*r^2*t^3 -5832*cOne^12*r*t^4 +648*cOne^10*cTwo^12*r*t^4 +324*cOne^10*cTwo^12*t^5 +1944*cOne^10*cTwo^6*r^2*t^3 +1296*cOne^10*cTwo^6*r*t^4 +1296*cOne^10*r^3*t^2 +972*cOne^10*r^2*t^3 -140*cOne^9*cTwo^12*r*t^4 -16*cOne^9*cTwo^12*t^5 -420*cOne^9*cTwo^6*r^2*t^3 -64*cOne^9*cTwo^6*r*t^4 -280*cOne^9*r^3*t^2 -48*cOne^9*r^2*t^3 +6*cOne^8*cTwo^12*r*t^4 +18*cOne^8*cTwo^6*r^2*t^3 +12*cOne^8*r^3*t^2 -17496*cOne^6*cTwo^12*r^2*t^3 -23328*cOne^6*cTwo^12*r*t^4 -5832*cOne^6*cTwo^12*t^5 -46656*cOne^6*cTwo^6*r^3*t^2 -69984*cOne^6*cTwo^6*r^2*t^3 -23328*cOne^6*cTwo^6*r*t^4 -29160*cOne^6*r^4*t -46656*cOne^6*r^3*t^2 -17496*cOne^6*r^2*t^3 +972*cOne^4*cTwo^12*r^2*t^3 +648*cOne^4*cTwo^12*r*t^4 +2592*cOne^4*cTwo^6*r^3*t^2 +1944*cOne^4*cTwo^6*r^2*t^3 +1620*cOne^4*r^4*t +1296*cOne^4*r^3*t^2 -162*cOne^3*cTwo^12*r^2*t^3 -216*cOne^3*cTwo^9*r^3*t^2 -324*cOne^3*cTwo^9*r^2*t^3 -108*cOne^3*cTwo^9*r*t^4 -432*cOne^3*cTwo^6*r^3*t^2 -270*cOne^3*cTwo^3*r^4*t -432*cOne^3*cTwo^3*r^3*t^2 -162*cOne^3*cTwo^3*r^2*t^3 -270*cOne^3*r^4*t -11664*cTwo^12*r^3*t^2 -17496*cTwo^12*r^2*t^3 -5832*cTwo^12*r*t^4 -29160*cTwo^6*r^4*t -46656*cTwo^6*r^3*t^2 -17496*cTwo^6*r^2*t^3 -17496*r^5 -29160*r^4*t -11664*r^3*t^2

def gradient (c₁ c₂ t : R) (v : Fin 3 → R) : Fin 3 → R :=
  ![-a8r c₁ c₂ (v 0) t*(v 1)-b256r c₁ c₂ (v 0) t,
    -1296*(v 1)^2-MixedPolarJacobian.a8 c₁ c₂ 1 (v 0) t,864*(v 2)]

lemma H_map {S : Type*} [CommRing S] (f : R →+* S)
    (c₁ c₂ t : R) (v : Fin 3 → R) :
    f (H c₁ c₂ t v)=H (f c₁) (f c₂) (f t) (fun i => f (v i)) := by
  simp only [H,MixedPolarJacobian.equation,MixedPolarJacobian.a8,MixedPolarJacobian.a432,MixedPolarJacobian.b256,MixedPolarJacobian.b432,
    map_add,map_sub,map_mul,map_pow,map_neg,map_ofNat,map_one]
lemma gradient_map {S : Type*} [CommRing S] (f : R →+* S)
    (c₁ c₂ t : R) (v : Fin 3 → R) (i : Fin 3) :
    f (gradient c₁ c₂ t v i)=gradient (f c₁) (f c₂) (f t) (fun j => f (v j)) i := by
  fin_cases i <;> simp [gradient,a8r,b256r,MixedPolarJacobian.a8,MixedPolarJacobian.a432,map_ofNat]

abbrev Coeff (R : Type*) [CommRing R] := MvPolynomial (Fin 13) R
abbrev CurvePoly (R : Type*) [CommRing R] := Polynomial (Coeff R)
def cv (i : Fin 13) : CurvePoly R := C (MvPolynomial.X i)
def cp (r : R) : CurvePoly R := C (MvPolynomial.C r)
def curve (k : Fin 2 → R) : Fin 3 → CurvePoly R :=
  ![cp (k 0)+cv 0*X+cv 1*X^2,
    cp (k 1)+cv 2*X+cv 3*X^2+cv 4*X^3+cv 5*X^4,
    cv 6+cv 7*X+cv 8*X^2+cv 9*X^3+cv 10*X^4+cv 11*X^5+cv 12*X^6]
def equations (c₁ c₂ : R) (k : Fin 2 → R) (i : Fin 13) : Coeff R :=
  (H (cp c₁) (cp c₂) X (curve k)).coeff i.val

def coefficientDeriv (i : Fin 13) : Derivation R (CurvePoly R) (CurvePoly R) :=
  PolynomialModule.equivPolynomialSelf.compDer (MvPolynomial.pderiv i).mapCoeffs
@[simp] lemma coefficientDeriv_coeff (i : Fin 13) (f : CurvePoly R) (n : ℕ) :
    (coefficientDeriv i f).coeff n = MvPolynomial.pderiv i (f.coeff n) := rfl
@[simp] lemma coefficientDeriv_C (i : Fin 13) (p : Coeff R) :
    coefficientDeriv i (C p) = C (MvPolynomial.pderiv i p) := by
  ext n
  by_cases hn : n=0 <;> simp [coefficientDeriv_coeff,Polynomial.coeff_C,hn]
@[simp] lemma coefficientDeriv_X (i : Fin 13) : coefficientDeriv i (X : CurvePoly R)=0 := by
  ext n
  simp [coefficientDeriv_coeff,Polynomial.coeff_X,apply_ite]
def slotCoordinate : Fin 13 → Fin 3 := ![0,0,1,1,1,1,2,2,2,2,2,2,2]
def slotDegree : Fin 13 → ℕ := ![1,2,1,2,3,4,0,1,2,3,4,5,6]
lemma curve_coefficientDeriv (k : Fin 2 → R) (j : Fin 13) (i : Fin 3) :
    coefficientDeriv j (curve k i)=if i=slotCoordinate j then X^slotDegree j else 0 := by
  fin_cases j <;> fin_cases i <;>
    simp [curve,cv,cp,slotCoordinate,slotDegree,Derivation.leibniz,Derivation.leibniz_pow,smul_eq_mul]
lemma H_coefficientDeriv (c₁ c₂ : R) (k : Fin 2 → R) (j : Fin 13) :
    coefficientDeriv j (H (cp c₁) (cp c₂) X (curve k)) =
      gradient (cp c₁) (cp c₂) X (curve k) (slotCoordinate j)*X^slotDegree j := by
  have h4 : coefficientDeriv j (4 : CurvePoly R)=0 := (coefficientDeriv j).map_natCast 4
  have h3 : coefficientDeriv j (3 : CurvePoly R)=0 := (coefficientDeriv j).map_natCast 3
  have h6 : coefficientDeriv j (6 : CurvePoly R)=0 := (coefficientDeriv j).map_natCast 6
  have h12 : coefficientDeriv j (12 : CurvePoly R)=0 := (coefficientDeriv j).map_natCast 12
  have h16 : coefficientDeriv j (16 : CurvePoly R)=0 := (coefficientDeriv j).map_natCast 16
  have h18 : coefficientDeriv j (18 : CurvePoly R)=0 := (coefficientDeriv j).map_natCast 18
  have h32 : coefficientDeriv j (32 : CurvePoly R)=0 := (coefficientDeriv j).map_natCast 32
  have h48 : coefficientDeriv j (48 : CurvePoly R)=0 := (coefficientDeriv j).map_natCast 48
  have h54 : coefficientDeriv j (54 : CurvePoly R)=0 := (coefficientDeriv j).map_natCast 54
  have h64 : coefficientDeriv j (64 : CurvePoly R)=0 := (coefficientDeriv j).map_natCast 64
  have h70 : coefficientDeriv j (70 : CurvePoly R)=0 := (coefficientDeriv j).map_natCast 70
  have h108 : coefficientDeriv j (108 : CurvePoly R)=0 := (coefficientDeriv j).map_natCast 108
  have h140 : coefficientDeriv j (140 : CurvePoly R)=0 := (coefficientDeriv j).map_natCast 140
  have h162 : coefficientDeriv j (162 : CurvePoly R)=0 := (coefficientDeriv j).map_natCast 162
  have h216 : coefficientDeriv j (216 : CurvePoly R)=0 := (coefficientDeriv j).map_natCast 216
  have h270 : coefficientDeriv j (270 : CurvePoly R)=0 := (coefficientDeriv j).map_natCast 270
  have h280 : coefficientDeriv j (280 : CurvePoly R)=0 := (coefficientDeriv j).map_natCast 280
  have h324 : coefficientDeriv j (324 : CurvePoly R)=0 := (coefficientDeriv j).map_natCast 324
  have h420 : coefficientDeriv j (420 : CurvePoly R)=0 := (coefficientDeriv j).map_natCast 420
  have h432 : coefficientDeriv j (432 : CurvePoly R)=0 := (coefficientDeriv j).map_natCast 432
  have h648 : coefficientDeriv j (648 : CurvePoly R)=0 := (coefficientDeriv j).map_natCast 648
  have h864 : coefficientDeriv j (864 : CurvePoly R)=0 := (coefficientDeriv j).map_natCast 864
  have h972 : coefficientDeriv j (972 : CurvePoly R)=0 := (coefficientDeriv j).map_natCast 972
  have h1296 : coefficientDeriv j (1296 : CurvePoly R)=0 := (coefficientDeriv j).map_natCast 1296
  have h1620 : coefficientDeriv j (1620 : CurvePoly R)=0 := (coefficientDeriv j).map_natCast 1620
  have h1944 : coefficientDeriv j (1944 : CurvePoly R)=0 := (coefficientDeriv j).map_natCast 1944
  have h2592 : coefficientDeriv j (2592 : CurvePoly R)=0 := (coefficientDeriv j).map_natCast 2592
  have h2916 : coefficientDeriv j (2916 : CurvePoly R)=0 := (coefficientDeriv j).map_natCast 2916
  have h5832 : coefficientDeriv j (5832 : CurvePoly R)=0 := (coefficientDeriv j).map_natCast 5832
  have h11664 : coefficientDeriv j (11664 : CurvePoly R)=0 := (coefficientDeriv j).map_natCast 11664
  have h17496 : coefficientDeriv j (17496 : CurvePoly R)=0 := (coefficientDeriv j).map_natCast 17496
  have h23328 : coefficientDeriv j (23328 : CurvePoly R)=0 := (coefficientDeriv j).map_natCast 23328
  have h29160 : coefficientDeriv j (29160 : CurvePoly R)=0 := (coefficientDeriv j).map_natCast 29160
  have h46656 : coefficientDeriv j (46656 : CurvePoly R)=0 := (coefficientDeriv j).map_natCast 46656
  have h69984 : coefficientDeriv j (69984 : CurvePoly R)=0 := (coefficientDeriv j).map_natCast 69984
  unfold H MixedPolarJacobian.equation MixedPolarJacobian.a8 MixedPolarJacobian.b256 MixedPolarJacobian.a432 MixedPolarJacobian.b432
  simp only [map_add,map_sub,map_neg,Derivation.leibniz,Derivation.leibniz_pow,
    h4,h3,h6,h12,h16,h18,h32,h48,h54,h64,h70,h108,h140,h162,h216,h270,h280,h324,h420,h432,h648,h864,h972,h1296,h1620,h1944,h2592,h2916,h5832,h11664,h17496,h23328,h29160,h46656,h69984,Derivation.map_one_eq_zero,
    cp,coefficientDeriv_C,MvPolynomial.pderiv_C,Polynomial.C_0,coefficientDeriv_X,
    smul_zero,zero_smul,add_zero,curve_coefficientDeriv,smul_eq_mul]
  fin_cases j <;> simp [gradient,a8r,b256r,MixedPolarJacobian.a8,MixedPolarJacobian.a432,slotCoordinate,slotDegree] <;> ring
lemma equations_pderiv (c₁ c₂ : R) (k : Fin 2 → R) (i j : Fin 13) :
    MvPolynomial.pderiv j (equations c₁ c₂ k i)=
      (gradient (cp c₁) (cp c₂) X (curve k) (slotCoordinate j)*X^slotDegree j).coeff i.val := by
  rw [equations,← coefficientDeriv_coeff,H_coefficientDeriv]
lemma H_natDegree_le (c₁ c₂ : R) (k : Fin 2 → R) :
    (H (cp c₁) (cp c₂) X (curve k)).natDegree ≤ 12 := by
  unfold H MixedPolarJacobian.equation MixedPolarJacobian.a8 MixedPolarJacobian.b256 MixedPolarJacobian.a432 MixedPolarJacobian.b432 curve cv cp
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val]
  compute_degree

def curveEval {S : Type*} [CommRing S] (k : Fin 2 → R) (f : R →+* S)
    (v : Fin 13 → S) : Fin 3 → Polynomial S :=
  fun i => (curve k i).map (MvPolynomial.eval₂Hom f v)
def valueCurve (k : Fin 2 → R) (v : Fin 13 → R) : Fin 3 → Polynomial R :=
  ![C (k 0)+C (v 0)*X+C (v 1)*X^2,
    C (k 1)+C (v 2)*X+C (v 3)*X^2+C (v 4)*X^3+C (v 5)*X^4,
    C (v 6)+C (v 7)*X+C (v 8)*X^2+C (v 9)*X^3+C (v 10)*X^4+C (v 11)*X^5+C (v 12)*X^6]
lemma curveEval_eq_valueCurve {S : Type*} [CommRing S] (k : Fin 2 → R)
    (f : R →+* S) (v : Fin 13 → S) :
    curveEval k f v=valueCurve (fun i => f (k i)) v := by
  funext i
  fin_cases i <;> simp [curveEval,curve,valueCurve,cv,cp]
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

end MixedPolarJacobianIncidence
