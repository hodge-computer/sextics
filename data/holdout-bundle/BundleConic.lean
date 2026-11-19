import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.RingTheory.Derivation.MapCoeffs
import Mathlib.Tactic

/-!
The complementary diagonal quotient's weighted conic incidence.

This module fixes K = S + X0^3 X1 p + X1^3 X2 q + a p^3 + b q^3.
Its twelve equations are exactly coefficients t^1,...,t^12 of a weighted
conic with independent endpoint constants and distinguished coordinate X1=t.
The coefficient-incidence formalization is adapted from fqlx's accepted
HoldoutCover construction and hodgepodgeconjecture's deformed-conic application.
The complementary quotient, seed and adaptation were developed with OpenAI
ChatGPT assistance. This module alone asserts no certificate.
-/
noncomputable section
namespace HoldoutBundle
open Polynomial
variable {R : Type*} [CommRing R]

/-- The exact complementary weighted quotient over an arbitrary base ring. -/
def K (a b : R) (x : Fin 5 → R) : R :=
  x 0^6+x 1^6+x 2^6+x 0^3*x 1*x 3+x 1^3*x 2*x 4+a*x 3^3+b*x 4^3

def gradient (a b : R) (x : Fin 5 → R) : Fin 5 → R :=
  ![6*x 0^5+3*x 0^2*x 1*x 3,
    6*x 1^5+x 0^3*x 3+3*x 1^2*x 2*x 4,
    6*x 2^5+x 1^3*x 4,
    x 0^3*x 1+3*a*x 3^2,
    x 1^3*x 2+3*b*x 4^2]

def kPoly (a b : R) : MvPolynomial (Fin 5) R :=
  K (MvPolynomial.C a) (MvPolynomial.C b) MvPolynomial.X

def endpoint (a b : R) (k : Fin 4 → R) : R :=
  (k 0)^6+(k 1)^6+a*(k 2)^3+b*(k 3)^3

lemma K_map {S : Type*} [CommRing S] (f : R →+* S) (a b : R) (x : Fin 5 → R) :
    f (K a b x)=K (f a) (f b) (fun i => f (x i)) := by
  simp only [K,map_add,map_sub,map_mul,map_pow,map_ofNat]
lemma gradient_map {S : Type*} [CommRing S] (f : R →+* S)
    (a b : R) (x : Fin 5 → R) (i : Fin 5) :
    f (gradient a b x i)=gradient (f a) (f b) (fun j => f (x j)) i := by
  fin_cases i <;> simp [gradient,map_ofNat]

abbrev Coeff (R : Type*) [CommRing R] := MvPolynomial (Fin 12) R
abbrev CurvePoly (R : Type*) [CommRing R] := Polynomial (Coeff R)
def cv (i : Fin 12) : CurvePoly R := C (MvPolynomial.X i)
def cp (r : R) : CurvePoly R := C (MvPolynomial.C r)
/-- Four endpoint constants; X1=t; twelve positive coefficients. -/
def curve (k : Fin 4 → R) : Fin 5 → CurvePoly R :=
  ![cp (k 0)+cv 0*X+cv 1*X^2,
    X,
    cp (k 1)+cv 2*X+cv 3*X^2,
    cp (k 2)+cv 4*X+cv 5*X^2+cv 6*X^3+cv 7*X^4,
    cp (k 3)+cv 8*X+cv 9*X^2+cv 10*X^3+cv 11*X^4]
def equations (a b : R) (k : Fin 4 → R) (i : Fin 12) : Coeff R :=
  (K (cp a) (cp b) (curve k)).coeff (i.val+1)

def coefficientDeriv (i : Fin 12) : Derivation R (CurvePoly R) (CurvePoly R) :=
  PolynomialModule.equivPolynomialSelf.compDer (MvPolynomial.pderiv i).mapCoeffs
@[simp] lemma coefficientDeriv_coeff (i : Fin 12) (f : CurvePoly R) (n : ℕ) :
    (coefficientDeriv i f).coeff n = MvPolynomial.pderiv i (f.coeff n) := rfl
@[simp] lemma coefficientDeriv_C (i : Fin 12) (p : Coeff R) :
    coefficientDeriv i (C p) = C (MvPolynomial.pderiv i p) := by
  ext n
  by_cases hn : n=0 <;> simp [coefficientDeriv_coeff,Polynomial.coeff_C,hn]
@[simp] lemma coefficientDeriv_X (i : Fin 12) : coefficientDeriv i (X : CurvePoly R)=0 := by
  ext n
  simp [coefficientDeriv_coeff,Polynomial.coeff_X,apply_ite]
def slotCoordinate : Fin 12 → Fin 5 := ![0,0,2,2,3,3,3,3,4,4,4,4]
def slotDegree : Fin 12 → ℕ := ![1,2,1,2,1,2,3,4,1,2,3,4]
lemma curve_coefficientDeriv (k : Fin 4 → R) (j : Fin 12) (i : Fin 5) :
    coefficientDeriv j (curve k i)=if i=slotCoordinate j then X^slotDegree j else 0 := by
  fin_cases j <;> fin_cases i <;>
    simp [curve,cv,cp,slotCoordinate,slotDegree,Derivation.leibniz,Derivation.leibniz_pow,smul_eq_mul]
lemma K_coefficientDeriv (a b : R) (k : Fin 4 → R) (j : Fin 12) :
    coefficientDeriv j (K (cp a) (cp b) (curve k)) =
      gradient (cp a) (cp b) (curve k) (slotCoordinate j)*X^slotDegree j := by
  have h2 : coefficientDeriv j (2 : CurvePoly R)=0 := (coefficientDeriv j).map_natCast 2
  have h3 : coefficientDeriv j (3 : CurvePoly R)=0 := (coefficientDeriv j).map_natCast 3
  unfold K
  simp only [map_add,map_sub,Derivation.leibniz,Derivation.leibniz_pow,h2,h3,
    cp,coefficientDeriv_C,MvPolynomial.pderiv_C,Polynomial.C_0,
    smul_zero,zero_smul,add_zero,curve_coefficientDeriv,smul_eq_mul]
  fin_cases j <;> simp [gradient,slotCoordinate,slotDegree] <;> ring
lemma equations_pderiv (a b : R) (k : Fin 4 → R) (i j : Fin 12) :
    MvPolynomial.pderiv j (equations a b k i)=
      (gradient (cp a) (cp b) (curve k) (slotCoordinate j)*X^slotDegree j).coeff (i.val+1) := by
  rw [equations,← coefficientDeriv_coeff,K_coefficientDeriv]
lemma K_natDegree_le (a b : R) (k : Fin 4 → R) :
    (K (cp a) (cp b) (curve k)).natDegree ≤ 12 := by
  unfold K curve cv cp
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val]
  compute_degree

def curveEval {S : Type*} [CommRing S] (k : Fin 4 → R) (f : R →+* S)
    (v : Fin 12 → S) : Fin 5 → Polynomial S :=
  fun i => (curve k i).map (MvPolynomial.eval₂Hom f v)

def valueCurve (k : Fin 4 → R) (v : Fin 12 → R) : Fin 5 → Polynomial R :=
  ![C (k 0)+C (v 0)*X+C (v 1)*X^2,
    X,
    C (k 1)+C (v 2)*X+C (v 3)*X^2,
    C (k 2)+C (v 4)*X+C (v 5)*X^2+C (v 6)*X^3+C (v 7)*X^4,
    C (k 3)+C (v 8)*X+C (v 9)*X^2+C (v 10)*X^3+C (v 11)*X^4]
lemma curveEval_eq_valueCurve {S : Type*} [CommRing S] (k : Fin 4 → R)
    (f : R →+* S) (v : Fin 12 → S) :
    curveEval k f v=valueCurve (fun i => f (k i)) v := by
  funext i
  fin_cases i <;> simp [curveEval,curve,valueCurve,cv,cp]
lemma equations_eval {S : Type*} [CommRing S] (a b : R) (k : Fin 4 → R)
    (f : R →+* S) (v : Fin 12 → S) (i : Fin 12) :
    MvPolynomial.eval₂Hom f v (equations a b k i)=
      (K (C (f a)) (C (f b)) (curveEval k f v)).coeff (i.val+1) := by
  change (MvPolynomial.eval₂Hom f v) ((K (cp a) (cp b) (curve k)).coeff (i.val+1)) = _
  rw [← Polynomial.coeff_map]
  congr 2
  change (Polynomial.mapRingHom (MvPolynomial.eval₂Hom f v)) (K (cp a) (cp b) (curve k)) = _
  rw [K_map]
  change K ((cp a).map (MvPolynomial.eval₂Hom f v))
    ((cp b).map (MvPolynomial.eval₂Hom f v)) (curveEval k f v) = _
  simp only [cp,Polynomial.map_C,MvPolynomial.eval₂Hom_C]
lemma equations_pderiv_eval {S : Type*} [CommRing S] (a b : R) (k : Fin 4 → R)
    (f : R →+* S) (v : Fin 12 → S) (i j : Fin 12) :
    MvPolynomial.eval₂Hom f v (MvPolynomial.pderiv j (equations a b k i))=
      (gradient (C (f a)) (C (f b)) (curveEval k f v) (slotCoordinate j)*X^slotDegree j).coeff (i.val+1) := by
  rw [equations_pderiv,← Polynomial.coeff_map,Polynomial.map_mul,Polynomial.map_pow,Polynomial.map_X]
  congr 3
  change (Polynomial.mapRingHom (MvPolynomial.eval₂Hom f v))
    (gradient (cp a) (cp b) (curve k) (slotCoordinate j)) = _
  rw [gradient_map]
  change gradient ((cp a).map (MvPolynomial.eval₂Hom f v))
    ((cp b).map (MvPolynomial.eval₂Hom f v)) (curveEval k f v) (slotCoordinate j) = _
  simp only [cp,Polynomial.map_C,MvPolynomial.eval₂Hom_C]

lemma curve_map {S : Type*} [CommRing S] (f : R →+* S) (k : Fin 4 → R) (i : Fin 5) :
    (curve k i).map (MvPolynomial.map f)=curve (fun j => f (k j)) i := by
  fin_cases i <;> simp [curve,cv,cp]
lemma equations_map {S : Type*} [CommRing S] (f : R →+* S)
    (a b : R) (k : Fin 4 → R) (i : Fin 12) :
    MvPolynomial.map f (equations a b k i)=equations (f a) (f b) (fun j => f (k j)) i := by
  rw [equations,← Polynomial.coeff_map]
  have hh : (K (cp a) (cp b) (curve k)).map (MvPolynomial.map f)=
      K (cp (f a)) (cp (f b)) (curve (fun j => f (k j))) := by
    change (Polynomial.mapRingHom (MvPolynomial.map f)) (K (cp a) (cp b) (curve k)) = _
    rw [K_map]
    change K ((cp a).map (MvPolynomial.map f)) ((cp b).map (MvPolynomial.map f))
      (fun j => (curve k j).map (MvPolynomial.map f)) = _
    simp only [cp,Polynomial.map_C,MvPolynomial.map_C]
    congr 1
    funext j
    exact curve_map f k j
  rw [hh]
  rfl
lemma equations_pderiv_map {S : Type*} [CommRing S] (f : R →+* S)
    (a b : R) (k : Fin 4 → R) (i j : Fin 12) :
    MvPolynomial.map f (MvPolynomial.pderiv j (equations a b k i))=
      MvPolynomial.pderiv j (equations (f a) (f b) (fun j => f (k j)) i) := by
  rw [← MvPolynomial.pderiv_map,equations_map]

lemma K_eval_natDegree_le {S : Type*} [CommRing S] (f : R →+* S)
    (a b : R) (k : Fin 4 → R) (v : Fin 12 → S) :
    (K (C (f a)) (C (f b)) (curveEval k f v)).natDegree ≤ 12 := by
  have h : (K (cp a) (cp b) (curve k)).map (MvPolynomial.eval₂Hom f v) =
      K (C (f a)) (C (f b)) (curveEval k f v) := by
    change (Polynomial.mapRingHom (MvPolynomial.eval₂Hom f v)) (K (cp a) (cp b) (curve k)) = _
    rw [K_map]
    simp only [Polynomial.coe_mapRingHom,cp,Polynomial.map_C,MvPolynomial.eval₂Hom_C,curveEval]
    rfl
  rw [← h]
  exact Polynomial.natDegree_map_le.trans (K_natDegree_le a b k)


/-- The full positive-coefficient gradient matrix. -/
def valueJacobian (a b : R) (k : Fin 4 → R) (v : Fin 12 → R) :
    Matrix (Fin 12) (Fin 12) R := fun i j =>
  (gradient (C a) (C b) (valueCurve k v) (slotCoordinate j)*X^slotDegree j).coeff
    (i.val+1)

lemma K_valueCurve_constant (a b : R) (k : Fin 4 → R) (v : Fin 12 → R) :
    (K (C a) (C b) (valueCurve k v)).coeff 0 = endpoint a b k := by
  change (Polynomial.constantCoeff : Polynomial R →+* R)
    (K (C a) (C b) (valueCurve k v)) = _
  rw [K_map]
  simp [K,valueCurve,endpoint]

lemma K_valueCurve_natDegree_le (a b : R) (k : Fin 4 → R) (v : Fin 12 → R) :
    (K (C a) (C b) (valueCurve k v)).natDegree ≤ 12 := by
  simpa only [RingHom.id_apply,curveEval_eq_valueCurve] using
    K_eval_natDegree_le (RingHom.id R) a b k v

end HoldoutBundle
