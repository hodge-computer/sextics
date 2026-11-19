import Mathlib.RingTheory.Derivation.MapCoeffs
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

/-!
Exact companion incidences for the fixed split-ternary-q2 target.
The polynomial seed and its finite matrix inverses are adapted from the
accepted crossed-ternary-asymmetric construction by 1337isnot1337, which
credits the moving-conic method of fqlx and the Sextics authors. OpenAI Codex
assisted this adaptation for fqlx. Only target-specific arithmetic is retained
here; no certificate or specialization theorem is asserted by these lemmas.
-/

noncomputable section

namespace SplitCompanion
open Polynomial

/-- Seven times the first protected ternary, with the optional deformation
`5*s*x₀⁴*x₁²`. Setting `s=0` recovers exactly the protected polynomial. -/
def first {R : Type*} [CommRing R] (s : R) (z : Fin 3 → R) : R :=
  7*(z 0^6+z 1^6+z 2^6)+
    5*(z 0^5*z 1+z 0^2*z 1^3*z 2+3*z 0*z 2^5+
      2*z 1^5*z 2+s*z 0^4*z 1^2)

/-- Seven times the second protected ternary. -/
def second {R : Type*} [CommRing R] (z : Fin 3 → R) : R :=
  7*(z 0^6+z 1^6+z 2^6)+
    5*(2*z 0^5*z 1+2*z 0^3*z 1*z 2^2+z 0*z 2^5+3*z 1^5*z 2)

/-- `true` selects the deformed first ternary; `false` the second. -/
def H {R : Type*} [CommRing R] (which : Bool) (s : R) (z : Fin 5 → R) : R :=
  (if which then first s ![z 0,z 1,z 2] else second ![z 0,z 1,z 2])+
    7*(z 3^3+z 4^3)

def gradient {R : Type*} [CommRing R] (which : Bool) (s : R)
    (z : Fin 5 → R) : Fin 5 → R :=
  if which then
    ![7*(6*z 0^5)+5*(5*z 0^4*z 1+2*z 0*z 1^3*z 2+3*z 2^5+4*s*z 0^3*z 1^2),
      7*(6*z 1^5)+5*(z 0^5+3*z 0^2*z 1^2*z 2+10*z 1^4*z 2+2*s*z 0^4*z 1),
      7*(6*z 2^5)+5*(z 0^2*z 1^3+15*z 0*z 2^4+2*z 1^5),
      7*(3*z 3^2),7*(3*z 4^2)]
  else
    ![7*(6*z 0^5)+5*(10*z 0^4*z 1+6*z 0^2*z 1*z 2^2+z 2^5),
      7*(6*z 1^5)+5*(2*z 0^5+2*z 0^3*z 2^2+15*z 1^4*z 2),
      7*(6*z 2^5)+5*(4*z 0^3*z 1*z 2+5*z 0*z 2^4+3*z 1^5),
      7*(3*z 3^2),7*(3*z 4^2)]

lemma H_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (which : Bool) (s : R) (z : Fin 5 → R) :
    f (H which s z)=H which (f s) (fun i => f (z i)) := by
  cases which <;> simp [H,first,second,map_ofNat]

lemma gradient_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (which : Bool) (s : R) (z : Fin 5 → R) (i : Fin 5) :
    f (gradient which s z i)=gradient which (f s) (fun j => f (z j)) i := by
  cases which <;> fin_cases i <;> simp [gradient,map_ofNat]

lemma H_derivation {R : Type*} [CommRing R] (D : Derivation ℤ R R)
    (which : Bool) (s : R) (hs : D s=0) (z : Fin 5 → R) :
    D (H which s z)=∑ i,gradient which s z i*D (z i) := by
  have h2 : D (2 : R)=0 := D.map_natCast 2
  have h3 : D (3 : R)=0 := D.map_natCast 3
  have h5 : D (5 : R)=0 := D.map_natCast 5
  have h7 : D (7 : R)=0 := D.map_natCast 7
  cases which <;>
    simp [H,first,second,gradient,Fin.sum_univ_succ,h2,h3,h5,h7,
      Derivation.leibniz,Derivation.leibniz_pow,smul_eq_mul,hs] <;> ring

abbrev Coeff (R : Type*) [CommRing R] := MvPolynomial (Fin 13) R
abbrev CurvePoly (R : Type*) [CommRing R] := Polynomial (Coeff R)
def coeffVar {R : Type*} [CommRing R] (i : Fin 13) : CurvePoly R := Polynomial.C (MvPolynomial.X i)
def constPoly {R : Type*} [CommRing R] (r : R) : CurvePoly R := Polynomial.C (MvPolynomial.C r)

def curve {R : Type*} [CommRing R] (k : Fin 3 → R) : Fin 5 → CurvePoly R :=
  ![4*X,
    coeffVar 0+coeffVar 1*X+coeffVar 2*X^2,
    constPoly (k 0)+coeffVar 3*X+coeffVar 4*X^2,
    constPoly (k 1)+coeffVar 5*X+coeffVar 6*X^2+coeffVar 7*X^3+coeffVar 8*X^4,
    constPoly (k 2)+coeffVar 9*X+coeffVar 10*X^2+coeffVar 11*X^3+coeffVar 12*X^4]

def equations {R : Type*} [CommRing R] (which : Bool) (s : R)
    (k : Fin 3 → R) (i : Fin 13) : Coeff R :=
  (H which (constPoly s) (curve k)).coeff i.val

def coefficientDeriv {R : Type*} [CommRing R] (i : Fin 13) :
    Derivation ℤ (CurvePoly R) (CurvePoly R) :=
  (PolynomialModule.equivPolynomialSelf.compDer (MvPolynomial.pderiv i).mapCoeffs).restrictScalars ℤ

@[simp] lemma coefficientDeriv_coeff {R : Type*} [CommRing R]
    (i : Fin 13) (f : CurvePoly R) (n : ℕ) :
    (coefficientDeriv i f).coeff n=MvPolynomial.pderiv i (f.coeff n) := rfl

@[simp] lemma coefficientDeriv_C {R : Type*} [CommRing R]
    (i : Fin 13) (P : Coeff R) :
    coefficientDeriv i (Polynomial.C P)=Polynomial.C (MvPolynomial.pderiv i P) := by
  ext n
  by_cases hn : n=0 <;> simp [coefficientDeriv_coeff,Polynomial.coeff_C,hn]

@[simp] lemma coefficientDeriv_X {R : Type*} [CommRing R] (i : Fin 13) :
    coefficientDeriv i (X : CurvePoly R)=0 := by
  ext n
  simp [coefficientDeriv_coeff,Polynomial.coeff_X,apply_ite]

def slotCoordinate : Fin 13 → Fin 5 := ![1,1,1,2,2,3,3,3,3,4,4,4,4]
def slotDegree : Fin 13 → ℕ := ![0,1,2,1,2,1,2,3,4,1,2,3,4]

lemma curve_coefficientDeriv {R : Type*} [CommRing R]
    (k : Fin 3 → R) (j : Fin 13) (i : Fin 5) :
    coefficientDeriv j (curve k i)=
      if i=slotCoordinate j then X^slotDegree j else 0 := by
  have h4 : coefficientDeriv j (4 : CurvePoly R)=0 := (coefficientDeriv j).map_natCast 4
  fin_cases j <;> fin_cases i <;>
    simp_all [curve,coeffVar,constPoly,slotCoordinate,slotDegree,Derivation.leibniz,
      Derivation.leibniz_pow,smul_eq_mul,h4]

lemma H_coefficientDeriv {R : Type*} [CommRing R]
    (which : Bool) (s : R) (k : Fin 3 → R) (j : Fin 13) :
    coefficientDeriv j (H which (constPoly s) (curve k))=
      gradient which (constPoly s) (curve k) (slotCoordinate j)*X^slotDegree j := by
  have h (z : Fin 5 → CurvePoly R) : coefficientDeriv j (H which (constPoly s) z)=
      ∑ i,gradient which (constPoly s) z i*coefficientDeriv j (z i) :=
    H_derivation (coefficientDeriv j) which (constPoly s)
      (show coefficientDeriv j (constPoly s)=0 by simp [constPoly]) z
  rw [h]
  simp only [curve_coefficientDeriv]
  rw [Finset.sum_eq_single (slotCoordinate j)]
  · simp
  · intro b hb hbj
    simp [hbj]
  · simp

lemma equations_pderiv {R : Type*} [CommRing R]
    (which : Bool) (s : R) (k : Fin 3 → R) (i j : Fin 13) :
    MvPolynomial.pderiv j (equations which s k i)=
      (gradient which (constPoly s) (curve k) (slotCoordinate j)*X^slotDegree j).coeff i.val := by
  rw [equations,← coefficientDeriv_coeff,H_coefficientDeriv]

def curveEval {R S : Type*} [CommRing R] [CommRing S]
    (k : Fin 3 → R) (f : R →+* S) (v : Fin 13 → S) (i : Fin 5) : Polynomial S :=
  (curve k i).map (MvPolynomial.eval₂Hom f v)

lemma equations_eval {R S : Type*} [CommRing R] [CommRing S]
    (which : Bool) (s : R) (k : Fin 3 → R) (f : R →+* S)
    (v : Fin 13 → S) (i : Fin 13) :
    MvPolynomial.eval₂Hom f v (equations which s k i)=
      (H which (Polynomial.C (f s)) (curveEval k f v)).coeff i.val := by
  change (MvPolynomial.eval₂Hom f v) ((H which (constPoly s) (curve k)).coeff i.val)=_
  rw [← Polynomial.coeff_map]
  have h := H_map (Polynomial.mapRingHom (MvPolynomial.eval₂Hom f v)) which (constPoly s) (curve k)
  convert congrArg (fun p : Polynomial S => p.coeff i.val) h using 1 <;> simp [constPoly] <;> rfl

lemma equations_pderiv_eval {R S : Type*} [CommRing R] [CommRing S]
    (which : Bool) (s : R) (k : Fin 3 → R) (f : R →+* S)
    (v : Fin 13 → S) (i j : Fin 13) :
    MvPolynomial.eval₂Hom f v (MvPolynomial.pderiv j (equations which s k i))=
      (gradient which (Polynomial.C (f s)) (curveEval k f v) (slotCoordinate j)*X^slotDegree j).coeff i.val := by
  rw [equations_pderiv,← Polynomial.coeff_map,Polynomial.map_mul,Polynomial.map_pow,Polynomial.map_X]
  have h := gradient_map (Polynomial.mapRingHom (MvPolynomial.eval₂Hom f v)) which (constPoly s) (curve k) (slotCoordinate j)
  convert congrArg (fun p : Polynomial S => (p*X^slotDegree j).coeff i.val) h using 1 <;> simp [constPoly] <;> rfl

lemma H_natDegree_le {R : Type*} [CommRing R]
    (which : Bool) (s : R) (k : Fin 3 → R) :
    (H which (constPoly s) (curve k)).natDegree ≤ 12 := by
  cases which <;> unfold H first second curve coeffVar constPoly <;>
    simp only [Bool.false_eq_true,ite_false,ite_true,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val] <;> compute_degree

end SplitCompanion

/- Source component: ConicSeedModFive. -/
section
noncomputable section
namespace SplitCompanionSeed
open Polynomial
abbrev K := ZMod 5
def x : Polynomial K := 4 * X
def a : Polynomial K := 2 - X^2
def y : Polynomial K := 4 + 2 * X^2
def s : Polynomial K := 3*x^2 + 3*a^2
def t : Polynomial K := 4*x^2 + 2*a^2

theorem incidence : x^6+a^6+y^6+s^3+t^3=0 := by
  have heq : x^6+a^6+y^6+s^3+t^3 = 5 * ((20)*X^12+(480)*X^10+(6960)*X^8+(49920)*X^6+(27840)*X^4+(7680)*X^2+(1280)) := by
    dsimp [x, a, y, s, t]
    ring
  rw [heq, ← Polynomial.C_ofNat]
  have hz : (5 : K) = 0 := by decide
  rw [hz, map_zero, zero_mul]

def columns : Fin 14 → Polynomial K :=
  ![x^5, X*x^5, a^5, X*a^5, y^5, X*y^5,
    3*s^2, X*(3*s^2), X^2*(3*s^2), X^3*(3*s^2),
    3*t^2, X*(3*t^2), X^2*(3*t^2), X^3*(3*t^2)]
def evaluated : Matrix (Fin 12) (Fin 14) K :=
  fun i j => (columns j).coeff i.val

def expandedColumns : Fin 14 → Polynomial K := ![(1024)*X^5,
(1024)*X^6,
(-1)*X^10+(10)*X^8+(-40)*X^6+(80)*X^4+(-80)*X^2+(32),
(-1)*X^11+(10)*X^9+(-40)*X^7+(80)*X^5+(-80)*X^3+(32)*X^1,
(32)*X^10+(320)*X^8+(1280)*X^6+(2560)*X^4+(2560)*X^2+(1024),
(32)*X^11+(320)*X^9+(1280)*X^7+(2560)*X^5+(2560)*X^3+(1024)*X^1,
(27)*X^8+(648)*X^6+(4104)*X^4+(2592)*X^2+(432),
(27)*X^9+(648)*X^7+(4104)*X^5+(2592)*X^3+(432)*X^1,
(27)*X^10+(648)*X^8+(4104)*X^6+(2592)*X^4+(432)*X^2,
(27)*X^11+(648)*X^9+(4104)*X^7+(2592)*X^5+(432)*X^3,
(12)*X^8+(672)*X^6+(9504)*X^4+(2688)*X^2+(192),
(12)*X^9+(672)*X^7+(9504)*X^5+(2688)*X^3+(192)*X^1,
(12)*X^10+(672)*X^8+(9504)*X^6+(2688)*X^4+(192)*X^2,
(12)*X^11+(672)*X^9+(9504)*X^7+(2688)*X^5+(192)*X^3]

theorem columns_expanded : columns = expandedColumns := by
  funext j
  fin_cases j <;> norm_num [columns, expandedColumns, x, a, y, s, t] <;> ring

def explicit : Matrix (Fin 12) (Fin 14) K := !![0, 0, 2, 0, 4, 0, 2, 0, 0, 0, 2, 0, 0, 0;
0, 0, 0, 2, 0, 4, 0, 2, 0, 0, 0, 2, 0, 0;
0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 3, 0, 2, 0;
0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 3, 0, 2;
0, 0, 0, 0, 0, 0, 4, 0, 2, 0, 4, 0, 3, 0;
4, 0, 0, 0, 0, 0, 0, 4, 0, 2, 0, 4, 0, 3;
0, 4, 0, 0, 0, 0, 3, 0, 4, 0, 2, 0, 4, 0;
0, 0, 0, 0, 0, 0, 0, 3, 0, 4, 0, 2, 0, 4;
0, 0, 0, 0, 0, 0, 2, 0, 3, 0, 2, 0, 2, 0;
0, 0, 0, 0, 0, 0, 0, 2, 0, 3, 0, 2, 0, 2;
0, 0, 4, 0, 2, 0, 0, 0, 2, 0, 0, 0, 2, 0;
0, 0, 0, 4, 0, 2, 0, 0, 0, 2, 0, 0, 0, 2]

def right : Matrix (Fin 14) (Fin 12) K := !![0, 0, 0, 1, 0, 4, 0, 1, 0, 2, 0, 0;
0, 0, 4, 0, 1, 0, 4, 0, 3, 0, 0, 0;
4, 0, 0, 0, 3, 0, 0, 0, 0, 0, 2, 0;
0, 4, 0, 3, 0, 0, 0, 3, 0, 1, 0, 2;
2, 0, 0, 0, 3, 0, 0, 0, 2, 0, 4, 0;
0, 2, 0, 3, 0, 0, 0, 3, 0, 3, 0, 4;
0, 0, 4, 0, 0, 0, 0, 0, 4, 0, 0, 0;
0, 0, 0, 4, 0, 0, 0, 0, 0, 4, 0, 0;
0, 0, 0, 0, 1, 0, 0, 0, 3, 0, 0, 0;
0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0;
0, 0, 1, 0, 1, 0, 0, 0, 2, 0, 0, 0;
0, 0, 0, 2, 0, 0, 0, 1, 0, 4, 0, 0;
0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

theorem evaluated_eq : evaluated = explicit := by
  ext i j
  simp only [evaluated, columns_expanded]
  fin_cases i <;> fin_cases j <;>
    norm_num [expandedColumns, explicit, Polynomial.coeff_add, Polynomial.coeff_mul,
      Polynomial.coeff_X_pow, Polynomial.coeff_ofNat_zero, Polynomial.coeff_ofNat_succ, Polynomial.coeff_X,
      Finsupp.single_apply] <;> decide
theorem right_inverse : explicit * right = 1 := by decide
theorem evaluated_right_inverse : evaluated * right = 1 := by
  rw [evaluated_eq, right_inverse]
end SplitCompanionSeed
end
end

/- Source component: ConicSeedCoefficients. -/
section

noncomputable section
namespace SplitCompanionSeed
open Polynomial

lemma columns_degree (j : Fin 14) : (columns j).natDegree ≤ 11 := by
  fin_cases j <;> simp only [columns,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val]
  all_goals dsimp [x,a,y,s,t]
  all_goals compute_degree
  all_goals omega

lemma column_coeff (j : Fin 14) (n : ℕ) :
    (columns j).coeff n = if h : n<12 then explicit ⟨n,h⟩ j else 0 := by
  classical
  by_cases hn : n<12
  · rw [dite_eq_left hn,← evaluated_eq]
    rfl
  · rw [dite_eq_right hn]
    exact coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (columns_degree j) (by omega))

end SplitCompanionSeed
end
end


namespace SplitCompanion
open Polynomial
abbrev K := ZMod 5
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

def parameters : Fin 3 → K := ![4,2,3]
def seed : Fin 13 → K := ![2,0,4,0,2,0,1,0,3,0,1,0,2]

lemma polyNat_eq {m n : ℕ} (h : (m : K)=(n : K)) :
    (m : Polynomial K)=(n : Polynomial K) := by
  simpa only [map_natCast] using congrArg (Polynomial.C : K →+* Polynomial K) h

lemma five_zero_poly : (5 : Polynomial K)=0 := by
  have h : (5 : K)=0 := by decide
  simpa only [map_ofNat,map_zero] using congrArg (Polynomial.C : K →+* Polynomial K) h

lemma seed_s_reduced : SplitCompanionSeed.s=2+X^2+3*X^4 := by
  have he : SplitCompanionSeed.s=12+36*X^2+3*X^4 := by
    dsimp [SplitCompanionSeed.s,SplitCompanionSeed.x,SplitCompanionSeed.a]
    ring
  have h12 : (12 : Polynomial K)=2 := polyNat_eq (by decide : (12 : K)=2)
  have h36 : (36 : Polynomial K)=1 := polyNat_eq (by decide : (36 : K)=1)
  rw [he,h12,h36,one_mul]
lemma seed_t_reduced : SplitCompanionSeed.t=3+X^2+2*X^4 := by
  have he : SplitCompanionSeed.t=8+56*X^2+2*X^4 := by
    dsimp [SplitCompanionSeed.t,SplitCompanionSeed.x,SplitCompanionSeed.a]
    ring
  have h8 : (8 : Polynomial K)=3 := polyNat_eq (by decide : (8 : K)=3)
  have h56 : (56 : Polynomial K)=1 := polyNat_eq (by decide : (56 : K)=1)
  rw [he,h8,h56,one_mul]
lemma seed_a_reduced : SplitCompanionSeed.a=2+4*X^2 := by
  have h : (4 : Polynomial K) = -1 := by
    have he : (4 : K) = -1 := by decide
    simpa only [map_ofNat,map_neg,map_one] using
      congrArg (Polynomial.C : K →+* Polynomial K) he
  dsimp [SplitCompanionSeed.a]
  rw [h]
  ring

lemma curveEval_seed : curveEval parameters (RingHom.id K) seed=
    ![SplitCompanionSeed.x,SplitCompanionSeed.a,SplitCompanionSeed.y,
      SplitCompanionSeed.s,SplitCompanionSeed.t] := by
  have hc2 : Polynomial.C (2 : K)=(2 : Polynomial K) := map_natCast Polynomial.C 2
  have hc3 : Polynomial.C (3 : K)=(3 : Polynomial K) := map_natCast Polynomial.C 3
  have hc4 : Polynomial.C (4 : K)=(4 : Polynomial K) := map_natCast Polynomial.C 4
  funext i
  fin_cases i <;> simp [curveEval,curve,coeffVar,constPoly,seed,parameters,
    seed_a_reduced,seed_s_reduced,seed_t_reduced,
    SplitCompanionSeed.x,SplitCompanionSeed.y,hc2,hc3,hc4]

lemma H_seed_zero (which : Bool) (s : K) :
    H which (Polynomial.C s) (curveEval parameters (RingHom.id K) seed)=0 := by
  rw [curveEval_seed]
  cases which <;>
    simp only [H,first,second,Bool.false_eq_true,ite_false,ite_true,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val,
      five_zero_poly,zero_mul,add_zero]
  all_goals have h := SplitCompanionSeed.incidence
  all_goals linear_combination 7*h

lemma seed_equations (which : Bool) (s : K) (i : Fin 13) :
    MvPolynomial.eval₂Hom (RingHom.id K) seed (equations which s parameters i)=0 := by
  rw [equations_eval]
  simpa using congrArg (fun p : Polynomial K => p.coeff i.val) (H_seed_zero which s)

def basicGradient : Fin 5 → Polynomial K :=
  ![SplitCompanionSeed.x^5,SplitCompanionSeed.a^5,SplitCompanionSeed.y^5,
    3*SplitCompanionSeed.s^2,3*SplitCompanionSeed.t^2]

lemma gradient_seed (which : Bool) (s : K) (i : Fin 5) :
    gradient which (Polynomial.C s) (curveEval parameters (RingHom.id K) seed) i=
      2*basicGradient i := by
  have h7 : (7 : Polynomial K)=2 := polyNat_eq (by decide : (7 : K)=2)
  have h6 : (6 : Polynomial K)=1 := polyNat_eq (by decide : (6 : K)=1)
  rw [curveEval_seed]
  cases which <;> fin_cases i <;>
    simp [gradient,basicGradient,h7,h6,five_zero_poly]

def sourceColumn : Fin 13 → Fin 14 := ![2,3,3,5,5,7,8,9,9,11,12,13,13]
def sourceShift : Fin 13 → ℕ := ![0,0,1,0,1,0,0,0,1,0,0,0,1]

lemma seedColumns_eq (which : Bool) (s : K) (j : Fin 13) :
    gradient which (Polynomial.C s) (curveEval parameters (RingHom.id K) seed)
      (slotCoordinate j)*X^slotDegree j=
      2*(X^sourceShift j*SplitCompanionSeed.columns (sourceColumn j)) := by
  rw [gradient_seed]
  fin_cases j <;> simp [sourceColumn,sourceShift,basicGradient,slotCoordinate,slotDegree,
    SplitCompanionSeed.columns] <;> ring

lemma coeff_scaled_shift (j : Fin 14) (s n : ℕ) :
    (2*(X^s*SplitCompanionSeed.columns j)).coeff n=
      2*(if s ≤ n then (if h : n-s<12 then
        SplitCompanionSeed.explicit ⟨n-s,h⟩ j else 0) else 0) := by
  have h2 : (2 : Polynomial K)=Polynomial.C (2 : K) := (map_natCast Polynomial.C 2).symm
  rw [h2,Polynomial.coeff_C_mul,Polynomial.coeff_X_pow_mul',SplitCompanionSeed.column_coeff]

def seedJacobian (which : Bool) (s : K) : Matrix (Fin 13) (Fin 13) K := fun i j =>
  MvPolynomial.eval₂Hom (RingHom.id K) seed (MvPolynomial.pderiv j (equations which s parameters i))

def seedJacobianExplicit : Matrix (Fin 13) (Fin 13) K := !![4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
0, 4, 0, 3, 0, 4, 0, 0, 0, 4, 0, 0, 0;
0, 0, 4, 0, 3, 0, 4, 0, 0, 0, 4, 0, 0;
0, 0, 0, 0, 0, 4, 0, 4, 0, 1, 0, 4, 0;
0, 0, 0, 0, 0, 0, 4, 0, 4, 0, 1, 0, 4;
0, 0, 0, 0, 0, 3, 0, 4, 0, 3, 0, 1, 0;
0, 0, 0, 0, 0, 0, 3, 0, 4, 0, 3, 0, 1;
0, 0, 0, 0, 0, 1, 0, 3, 0, 4, 0, 3, 0;
0, 0, 0, 0, 0, 0, 1, 0, 3, 0, 4, 0, 3;
0, 0, 0, 0, 0, 4, 0, 1, 0, 4, 0, 4, 0;
3, 0, 0, 0, 0, 0, 4, 0, 1, 0, 4, 0, 4;
0, 3, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0;
0, 0, 3, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4]

def seedJacobianRight : Matrix (Fin 13) (Fin 13) K := !![4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
0, 2, 0, 3, 0, 1, 0, 3, 0, 1, 0, 1, 0;
3, 0, 2, 0, 3, 0, 1, 0, 3, 0, 1, 0, 1;
0, 1, 0, 1, 0, 3, 0, 1, 0, 3, 0, 2, 0;
4, 0, 1, 0, 1, 0, 3, 0, 1, 0, 3, 0, 2;
0, 0, 0, 3, 0, 4, 0, 1, 0, 4, 0, 0, 0;
2, 0, 0, 0, 3, 0, 4, 0, 1, 0, 4, 0, 0;
0, 0, 0, 4, 0, 4, 0, 4, 0, 2, 0, 0, 0;
1, 0, 0, 0, 4, 0, 4, 0, 4, 0, 2, 0, 0;
0, 0, 0, 2, 0, 4, 0, 4, 0, 4, 0, 0, 0;
2, 0, 0, 0, 2, 0, 4, 0, 4, 0, 4, 0, 0;
0, 0, 0, 4, 0, 1, 0, 4, 0, 3, 0, 0, 0;
4, 0, 0, 0, 4, 0, 1, 0, 4, 0, 3, 0, 0]

def seedFreeExplicit : Matrix (Fin 12) (Fin 12) K := !![4, 0, 3, 0, 4, 0, 0, 0, 4, 0, 0, 0;
0, 4, 0, 3, 0, 4, 0, 0, 0, 4, 0, 0;
0, 0, 0, 0, 4, 0, 4, 0, 1, 0, 4, 0;
0, 0, 0, 0, 0, 4, 0, 4, 0, 1, 0, 4;
0, 0, 0, 0, 3, 0, 4, 0, 3, 0, 1, 0;
0, 0, 0, 0, 0, 3, 0, 4, 0, 3, 0, 1;
0, 0, 0, 0, 1, 0, 3, 0, 4, 0, 3, 0;
0, 0, 0, 0, 0, 1, 0, 3, 0, 4, 0, 3;
0, 0, 0, 0, 4, 0, 1, 0, 4, 0, 4, 0;
0, 0, 0, 0, 0, 4, 0, 1, 0, 4, 0, 4;
3, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0;
0, 3, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4]

def seedFreeRight : Matrix (Fin 12) (Fin 12) K := !![2, 0, 3, 0, 1, 0, 3, 0, 1, 0, 1, 0;
0, 2, 0, 3, 0, 1, 0, 3, 0, 1, 0, 1;
1, 0, 1, 0, 3, 0, 1, 0, 3, 0, 2, 0;
0, 1, 0, 1, 0, 3, 0, 1, 0, 3, 0, 2;
0, 0, 3, 0, 4, 0, 1, 0, 4, 0, 0, 0;
0, 0, 0, 3, 0, 4, 0, 1, 0, 4, 0, 0;
0, 0, 4, 0, 4, 0, 4, 0, 2, 0, 0, 0;
0, 0, 0, 4, 0, 4, 0, 4, 0, 2, 0, 0;
0, 0, 2, 0, 4, 0, 4, 0, 4, 0, 0, 0;
0, 0, 0, 2, 0, 4, 0, 4, 0, 4, 0, 0;
0, 0, 4, 0, 1, 0, 4, 0, 3, 0, 0, 0;
0, 0, 0, 4, 0, 1, 0, 4, 0, 3, 0, 0]


lemma seedJacobian_eq (which : Bool) (s : K) :
    seedJacobian which s=seedJacobianExplicit := by
  ext i j
  rw [seedJacobian,equations_pderiv_eval,seedColumns_eq,coeff_scaled_shift]
  fin_cases i <;> fin_cases j <;> decide

lemma seedJacobian_right : seedJacobianExplicit*seedJacobianRight=1 := by decide

lemma seed_jacobian_unit (which : Bool) (s : K) :
    IsUnit (Matrix.det (fun i j => MvPolynomial.eval₂Hom (RingHom.id K) seed
      (MvPolynomial.pderiv i (equations which s parameters j)))) := by
  change IsUnit (seedJacobian which s).transpose.det
  rw [Matrix.det_transpose,seedJacobian_eq]
  have hdet : seedJacobianExplicit.det*seedJacobianRight.det=1 := by
    rw [← Matrix.det_mul,seedJacobian_right,Matrix.det_one]
  apply isUnit_iff_ne_zero.mpr
  intro h
  rw [h,zero_mul] at hdet
  exact zero_ne_one hdet

def freeCoordinate : Fin 12 → Fin 5 := ![1,1,2,2,3,3,3,3,4,4,4,4]
def freeDegree : Fin 12 → ℕ := ![0,1,0,1,0,1,2,3,0,1,2,3]
def freeMatrix {R : Type*} [CommRing R] (which : Bool) (s : R)
    (k : Fin 3 → R) : Matrix (Fin 12) (Fin 12) (Coeff R) := fun i j =>
  (gradient which (constPoly s) (curve k) (freeCoordinate j)*X^freeDegree j).coeff i.val

def seedFree (which : Bool) (s : K) : Matrix (Fin 12) (Fin 12) K := fun i j =>
  MvPolynomial.eval₂Hom (RingHom.id K) seed (freeMatrix which s parameters i j)

lemma eval_freeMatrix_entry {R S : Type*} [CommRing R] [CommRing S]
    (which : Bool) (s : R) (k : Fin 3 → R) (f : R →+* S) (v : Fin 13 → S) (i j : Fin 12) :
    MvPolynomial.eval₂Hom f v (freeMatrix which s k i j)=
      (gradient which (Polynomial.C (f s)) (curveEval k f v) (freeCoordinate j)*X^freeDegree j).coeff i.val := by
  change (MvPolynomial.eval₂Hom f v)
    ((gradient which (constPoly s) (curve k) (freeCoordinate j)*X^freeDegree j).coeff i.val)=_
  rw [← Polynomial.coeff_map,Polynomial.map_mul,Polynomial.map_pow,Polynomial.map_X]
  have h := gradient_map (Polynomial.mapRingHom (MvPolynomial.eval₂Hom f v)) which
    (constPoly s) (curve k) (freeCoordinate j)
  convert congrArg (fun p : Polynomial S => (p*X^freeDegree j).coeff i.val) h using 1 <;> simp [constPoly] <;> rfl

lemma freeColumns_seed (which : Bool) (s : K) (j : Fin 12) :
    gradient which (Polynomial.C s) (curveEval parameters (RingHom.id K) seed)
      (freeCoordinate j)*X^freeDegree j=
      2*(X^0*SplitCompanionSeed.columns ⟨j.val+2,by omega⟩) := by
  rw [gradient_seed]
  fin_cases j <;> simp [freeCoordinate,freeDegree,basicGradient,SplitCompanionSeed.columns] <;> ring

lemma seedFree_eq (which : Bool) (s : K) : seedFree which s=seedFreeExplicit := by
  ext i j
  rw [seedFree,eval_freeMatrix_entry,freeColumns_seed,coeff_scaled_shift]
  fin_cases i <;> fin_cases j <;> decide

lemma seedFree_right : seedFreeExplicit*seedFreeRight=1 := by decide

lemma seedFree_det_ne_zero (which : Bool) (s : K) : (seedFree which s).det ≠ 0 := by
  rw [seedFree_eq]
  have hdet : seedFreeExplicit.det*seedFreeRight.det=1 := by
    rw [← Matrix.det_mul,seedFree_right,Matrix.det_one]
  intro h
  rw [h,zero_mul] at hdet
  exact zero_ne_one hdet

end SplitCompanion
