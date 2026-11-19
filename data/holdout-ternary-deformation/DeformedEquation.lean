import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.RingTheory.Derivation.MapCoeffs
import Mathlib.Tactic

/-!
Exact replacement conic for holdout-ternary-deformation, with coefficient 1/14.
The coefficient-incidence method follows fqlx's accepted holdout construction.
The mod-five approach also draws on 1337isnot1337's crossed-ternary-asymmetric proof.
This new seed and its formalization were prepared with OpenAI Codex assistance
for hodgepodgeconjecture. This module alone asserts no HasCertificate theorem.
-/
noncomputable section
set_option profiler true
set_option profiler.threshold 100
namespace DeformedConic
open Polynomial
variable {R : Type*} [CommRing R]

/-- Fourteen times the exact weighted quotient, over an arbitrary base ring. -/
def H (a b : R) (x : Fin 5 → R) : R :=
  14*(x 0^6+x 1^6+x 2^6+x 4*(a*x 0^3*x 1+b*x 1^3*x 2)+
    x 3^3-3*x 3*x 4^2)+x 0^5*x 1+2*x 1^5*x 2+x 2^5*x 0

def gradient (a b : R) (x : Fin 5 → R) : Fin 5 → R :=
  ![84*x 0^5+42*a*x 0^2*x 1*x 4+5*x 0^4*x 1+x 2^5,
    84*x 1^5+14*a*x 0^3*x 4+42*b*x 1^2*x 2*x 4+x 0^5+10*x 1^4*x 2,
    84*x 2^5+14*b*x 1^3*x 4+2*x 1^5+5*x 2^4*x 0,
    42*x 3^2-42*x 4^2,
    14*a*x 0^3*x 1+14*b*x 1^3*x 2-84*x 3*x 4]

lemma H_map {S : Type*} [CommRing S] (f : R →+* S) (a b : R) (x : Fin 5 → R) :
    f (H a b x)=H (f a) (f b) (fun i => f (x i)) := by
  simp only [H,map_add,map_sub,map_mul,map_pow,map_ofNat]
lemma gradient_map {S : Type*} [CommRing S] (f : R →+* S)
    (a b : R) (x : Fin 5 → R) (i : Fin 5) :
    f (gradient a b x i)=gradient (f a) (f b) (fun j => f (x j)) i := by
  fin_cases i <;> simp [gradient,map_ofNat]

abbrev Coeff (R : Type*) [CommRing R] := MvPolynomial (Fin 13) R
abbrev CurvePoly (R : Type*) [CommRing R] := Polynomial (Coeff R)
def cv (i : Fin 13) : CurvePoly R := C (MvPolynomial.X i)
def cp (r : R) : CurvePoly R := C (MvPolynomial.C r)
/-- The constants of x2,S,P are independent parameters; x1=t. -/
def curve (k : Fin 3 → R) : Fin 5 → CurvePoly R :=
  ![cv 0+cv 1*X+cv 2*X^2,
    X,
    cp (k 0)+cv 3*X+cv 4*X^2,
    cp (k 1)+cv 5*X+cv 6*X^2+cv 7*X^3+cv 8*X^4,
    cp (k 2)+cv 9*X+cv 10*X^2+cv 11*X^3+cv 12*X^4]
def equations (a b : R) (k : Fin 3 → R) (i : Fin 13) : Coeff R :=
  (H (cp a) (cp b) (curve k)).coeff i.val

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
def slotCoordinate : Fin 13 → Fin 5 := ![0,0,0,2,2,3,3,3,3,4,4,4,4]
def slotDegree : Fin 13 → ℕ := ![0,1,2,1,2,1,2,3,4,1,2,3,4]
lemma curve_coefficientDeriv (k : Fin 3 → R) (j : Fin 13) (i : Fin 5) :
    coefficientDeriv j (curve k i)=if i=slotCoordinate j then X^slotDegree j else 0 := by
  fin_cases j <;> fin_cases i <;>
    simp [curve,cv,cp,slotCoordinate,slotDegree,Derivation.leibniz,Derivation.leibniz_pow,smul_eq_mul]
lemma H_coefficientDeriv (a b : R) (k : Fin 3 → R) (j : Fin 13) :
    coefficientDeriv j (H (cp a) (cp b) (curve k)) =
      gradient (cp a) (cp b) (curve k) (slotCoordinate j)*X^slotDegree j := by
  have h2 : coefficientDeriv j (2 : CurvePoly R)=0 := (coefficientDeriv j).map_natCast 2
  have h3 : coefficientDeriv j (3 : CurvePoly R)=0 := (coefficientDeriv j).map_natCast 3
  have h14 : coefficientDeriv j (14 : CurvePoly R)=0 := (coefficientDeriv j).map_natCast 14
  unfold H
  simp only [map_add,map_sub,Derivation.leibniz,Derivation.leibniz_pow,h2,h3,h14,
    cp,coefficientDeriv_C,MvPolynomial.pderiv_C,Polynomial.C_0,
    smul_zero,zero_smul,add_zero,curve_coefficientDeriv,smul_eq_mul]
  fin_cases j <;> simp [gradient,slotCoordinate,slotDegree] <;> ring
lemma equations_pderiv (a b : R) (k : Fin 3 → R) (i j : Fin 13) :
    MvPolynomial.pderiv j (equations a b k i)=
      (gradient (cp a) (cp b) (curve k) (slotCoordinate j)*X^slotDegree j).coeff i.val := by
  rw [equations,← coefficientDeriv_coeff,H_coefficientDeriv]
lemma H_natDegree_le (a b : R) (k : Fin 3 → R) :
    (H (cp a) (cp b) (curve k)).natDegree ≤ 12 := by
  unfold H curve cv cp
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val]
  compute_degree

def curveEval {S : Type*} [CommRing S] (k : Fin 3 → R) (f : R →+* S)
    (v : Fin 13 → S) : Fin 5 → Polynomial S :=
  fun i => (curve k i).map (MvPolynomial.eval₂Hom f v)

def valueCurve (k : Fin 3 → R) (v : Fin 13 → R) : Fin 5 → Polynomial R :=
  ![C (v 0)+C (v 1)*X+C (v 2)*X^2,
    X,
    C (k 0)+C (v 3)*X+C (v 4)*X^2,
    C (k 1)+C (v 5)*X+C (v 6)*X^2+C (v 7)*X^3+C (v 8)*X^4,
    C (k 2)+C (v 9)*X+C (v 10)*X^2+C (v 11)*X^3+C (v 12)*X^4]
lemma curveEval_eq_valueCurve {S : Type*} [CommRing S] (k : Fin 3 → R)
    (f : R →+* S) (v : Fin 13 → S) :
    curveEval k f v=valueCurve (fun i => f (k i)) v := by
  funext i
  fin_cases i <;> simp [curveEval,curve,valueCurve,cv,cp]
lemma equations_eval {S : Type*} [CommRing S] (a b : R) (k : Fin 3 → R)
    (f : R →+* S) (v : Fin 13 → S) (i : Fin 13) :
    MvPolynomial.eval₂Hom f v (equations a b k i)=
      (H (C (f a)) (C (f b)) (curveEval k f v)).coeff i.val := by
  change (MvPolynomial.eval₂Hom f v) ((H (cp a) (cp b) (curve k)).coeff i.val) = _
  rw [← Polynomial.coeff_map]
  congr 2
  change (Polynomial.mapRingHom (MvPolynomial.eval₂Hom f v)) (H (cp a) (cp b) (curve k)) = _
  rw [H_map]
  change H ((cp a).map (MvPolynomial.eval₂Hom f v))
    ((cp b).map (MvPolynomial.eval₂Hom f v)) (curveEval k f v) = _
  simp only [cp,Polynomial.map_C,MvPolynomial.eval₂Hom_C]
lemma equations_pderiv_eval {S : Type*} [CommRing S] (a b : R) (k : Fin 3 → R)
    (f : R →+* S) (v : Fin 13 → S) (i j : Fin 13) :
    MvPolynomial.eval₂Hom f v (MvPolynomial.pderiv j (equations a b k i))=
      (gradient (C (f a)) (C (f b)) (curveEval k f v) (slotCoordinate j)*X^slotDegree j).coeff i.val := by
  rw [equations_pderiv,← Polynomial.coeff_map,Polynomial.map_mul,Polynomial.map_pow,Polynomial.map_X]
  congr 3
  change (Polynomial.mapRingHom (MvPolynomial.eval₂Hom f v))
    (gradient (cp a) (cp b) (curve k) (slotCoordinate j)) = _
  rw [gradient_map]
  change gradient ((cp a).map (MvPolynomial.eval₂Hom f v))
    ((cp b).map (MvPolynomial.eval₂Hom f v)) (curveEval k f v) (slotCoordinate j) = _
  simp only [cp,Polynomial.map_C,MvPolynomial.eval₂Hom_C]

lemma curve_map {S : Type*} [CommRing S] (f : R →+* S) (k : Fin 3 → R) (i : Fin 5) :
    (curve k i).map (MvPolynomial.map f)=curve (fun j => f (k j)) i := by
  fin_cases i <;> simp [curve,cv,cp]
lemma equations_map {S : Type*} [CommRing S] (f : R →+* S)
    (a b : R) (k : Fin 3 → R) (i : Fin 13) :
    MvPolynomial.map f (equations a b k i)=equations (f a) (f b) (fun j => f (k j)) i := by
  rw [equations,← Polynomial.coeff_map]
  have hh : (H (cp a) (cp b) (curve k)).map (MvPolynomial.map f)=
      H (cp (f a)) (cp (f b)) (curve (fun j => f (k j))) := by
    change (Polynomial.mapRingHom (MvPolynomial.map f)) (H (cp a) (cp b) (curve k)) = _
    rw [H_map]
    change H ((cp a).map (MvPolynomial.map f)) ((cp b).map (MvPolynomial.map f))
      (fun j => (curve k j).map (MvPolynomial.map f)) = _
    simp only [cp,Polynomial.map_C,MvPolynomial.map_C]
    congr 1
    funext j
    exact curve_map f k j
  rw [hh]
  rfl
lemma equations_pderiv_map {S : Type*} [CommRing S] (f : R →+* S)
    (a b : R) (k : Fin 3 → R) (i j : Fin 13) :
    MvPolynomial.map f (MvPolynomial.pderiv j (equations a b k i))=
      MvPolynomial.pderiv j (equations (f a) (f b) (fun j => f (k j)) i) := by
  rw [← MvPolynomial.pderiv_map,equations_map]

lemma H_eval_natDegree_le {S : Type*} [CommRing S] (f : R →+* S)
    (a b : R) (k : Fin 3 → R) (v : Fin 13 → S) :
    (H (C (f a)) (C (f b)) (curveEval k f v)).natDegree ≤ 12 := by
  have h : (H (cp a) (cp b) (curve k)).map (MvPolynomial.eval₂Hom f v) =
      H (C (f a)) (C (f b)) (curveEval k f v) := by
    change (Polynomial.mapRingHom (MvPolynomial.eval₂Hom f v)) (H (cp a) (cp b) (curve k)) = _
    rw [H_map]
    simp only [Polynomial.coe_mapRingHom,cp,Polynomial.map_C,MvPolynomial.eval₂Hom_C,curveEval]
    rfl
  rw [← h]
  exact Polynomial.natDegree_map_le.trans (H_natDegree_le a b k)


end DeformedConic
