import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.Derivation.MapCoeffs
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases

/-!
# Conics in a Weierstrass cone

A polynomial curve `(r, x, y)` of degrees `(2, 4, 6)` in a parameter, with the
constant terms of `r` and `x` prescribed. Its thirteen remaining coefficients
are the variables of the coefficient ring. The module defines the curve, the
derivations in its coefficients, and its evaluation at a point of the
coefficient space. It fixes no equation: an application supplies the
polynomial that the curve is to satisfy.

The coefficient-incidence method follows `fqlx`'s shared constructions and the
accepted ternary-deformation proof. This curve shape is extracted from
`hodgepodgeconjecture`'s accepted cyclic cubic construction,
`data/cycle-three/JacobianIncidence.lean` (PR #165), prepared with OpenAI
Codex assistance.
-/

noncomputable section
namespace WeierstrassConic
open Polynomial
variable {R : Type*} [CommRing R]

abbrev Coeff (R : Type*) [CommRing R] := MvPolynomial (Fin 13) R

abbrev CurvePoly (R : Type*) [CommRing R] := Polynomial (Coeff R)

def cv (i : Fin 13) : CurvePoly R := C (MvPolynomial.X i)

def cp (r : R) : CurvePoly R := C (MvPolynomial.C r)

def curve (k : Fin 2 → R) : Fin 3 → CurvePoly R :=
  ![cp (k 0)+cv 0*X+cv 1*X^2,
    cp (k 1)+cv 2*X+cv 3*X^2+cv 4*X^3+cv 5*X^4,
    cv 6+cv 7*X+cv 8*X^2+cv 9*X^3+cv 10*X^4+cv 11*X^5+cv 12*X^6]

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

end WeierstrassConic
