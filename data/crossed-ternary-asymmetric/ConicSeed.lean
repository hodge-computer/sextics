import Proposal.RadialResidues
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

/- Prepared with OpenAI Codex assistance for contributor 1337isnot1337.
See solution.md for the construction, provenance, and prior-work credit. -/

/- Source component: FixedConicFamily. -/
section

/- The dimension-matched family fixes the first coordinate to 4t. The three
   free coefficient parameters are the constant coefficients of y, S and T. The remaining thirteen coefficients are incidence
   variables. Mathematical source: the explicit mod-5 conic in this work;
   coefficientwise differentiation follows the accepted fqlx construction. -/
noncomputable section
namespace CrossedFixedConic
open Polynomial
open CrossedConicIncidence (H gradient)
variable {R : Type*} [CommRing R]
abbrev Coeff (R : Type*) [CommRing R] := MvPolynomial (Fin 13) R
abbrev CurvePoly (R : Type*) [CommRing R] := Polynomial (Coeff R)

def coeffVar (i : Fin 13) : CurvePoly R := Polynomial.C (MvPolynomial.X i)
def constPoly (r : R) : CurvePoly R := Polynomial.C (MvPolynomial.C r)
def curve (k : Fin 3 → R) : Fin 5 → CurvePoly R :=
  ![4*X,
    coeffVar 0+coeffVar 1*X+coeffVar 2*X^2,
    constPoly (k 0)+coeffVar 3*X+coeffVar 4*X^2,
    constPoly (k 1)+coeffVar 5*X+coeffVar 6*X^2+coeffVar 7*X^3+coeffVar 8*X^4,
    constPoly (k 2)+coeffVar 9*X+coeffVar 10*X^2+coeffVar 11*X^3+coeffVar 12*X^4]

def equations (k : Fin 3 → R) (i : Fin 13) : Coeff R := (H (curve k)).coeff i.val

def coefficientDeriv (i : Fin 13) : Derivation R (CurvePoly R) (CurvePoly R) :=
  PolynomialModule.equivPolynomialSelf.compDer (MvPolynomial.pderiv i).mapCoeffs

@[simp] lemma coefficientDeriv_coeff (i : Fin 13) (f : CurvePoly R) (n : ℕ) :
    (coefficientDeriv i f).coeff n = MvPolynomial.pderiv i (f.coeff n) := rfl
@[simp] lemma coefficientDeriv_C (i : Fin 13) (P : Coeff R) :
    coefficientDeriv i (Polynomial.C P) = Polynomial.C (MvPolynomial.pderiv i P) := by
  ext n
  by_cases hn : n=0 <;> simp [coefficientDeriv_coeff,Polynomial.coeff_C,hn]
@[simp] lemma coefficientDeriv_X (i : Fin 13) : coefficientDeriv i (X : CurvePoly R) = 0 := by
  ext n
  simp [coefficientDeriv_coeff,Polynomial.coeff_X,apply_ite]

def slotCoordinate : Fin 13 → Fin 5 := ![1,1,1,2,2,3,3,3,3,4,4,4,4]
def slotDegree : Fin 13 → ℕ := ![0,1,2,1,2,1,2,3,4,1,2,3,4]

lemma curve_coefficientDeriv (k : Fin 3 → R) (j : Fin 13) (i : Fin 5) :
    coefficientDeriv j (curve k i) =
      if i=slotCoordinate j then X^slotDegree j else 0 := by
  have h4 : coefficientDeriv j (4 : CurvePoly R)=0 := (coefficientDeriv j).map_natCast 4
  fin_cases j <;> fin_cases i <;>
    simp_all [curve,coeffVar,constPoly,slotCoordinate,slotDegree,Derivation.leibniz,
      Derivation.leibniz_pow,smul_eq_mul]

lemma H_coefficientDeriv (k : Fin 3 → R) (j : Fin 13) :
    coefficientDeriv j (H (curve k)) = gradient (curve k) (slotCoordinate j)*X^slotDegree j := by
  have h2 : coefficientDeriv j (2 : CurvePoly R)=0 := (coefficientDeriv j).map_natCast 2
  have h5 : coefficientDeriv j (5 : CurvePoly R)=0 := (coefficientDeriv j).map_natCast 5
  have h7 : coefficientDeriv j (7 : CurvePoly R)=0 := (coefficientDeriv j).map_natCast 7
  unfold H
  simp only [map_add,Derivation.leibniz,Derivation.leibniz_pow,h2,h5,h7,
    smul_zero,zero_smul,add_zero,curve_coefficientDeriv,smul_eq_mul]
  fin_cases j <;> simp_all [gradient,slotCoordinate,slotDegree] <;> ring

lemma equations_pderiv (k : Fin 3 → R) (i j : Fin 13) :
    MvPolynomial.pderiv j (equations k i) =
      (gradient (curve k) (slotCoordinate j)*X^slotDegree j).coeff i.val := by
  rw [equations,← coefficientDeriv_coeff,H_coefficientDeriv]

lemma H_natDegree_le (k : Fin 3 → R) : (H (curve k)).natDegree ≤ 12 := by
  unfold H curve coeffVar constPoly
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val]
  compute_degree

end CrossedFixedConic
end
end

/- Source component: ConicSeedModFive. -/
section
noncomputable section
namespace CrossedConicSeed
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
end CrossedConicSeed
end
end

/- Source component: CrossedConicSeedBinding. -/
section

noncomputable section
namespace CrossedConicIncidence
open Polynomial
abbrev K := ZMod 5

def seed : Fin 13 → K := ![0,4,0,2,0,4,4,0,2,2,0,1,0]

lemma polyNat_eq {m n : ℕ} (h : (m : K) = (n : K)) :
    (m : Polynomial K) = (n : Polynomial K) := by
  simpa only [map_natCast] using congrArg (Polynomial.C : K →+* Polynomial K) h

lemma seed_s_reduced : CrossedConicSeed.s = 2+X^2+3*X^4 := by
  have he : CrossedConicSeed.s = 12+36*X^2+3*X^4 := by
    dsimp [CrossedConicSeed.s,CrossedConicSeed.x,CrossedConicSeed.a]
    ring
  have h12 : (12 : Polynomial K) = 2 := polyNat_eq (by decide : (12 : K)=2)
  have h36 : (36 : Polynomial K) = 1 := polyNat_eq (by decide : (36 : K)=1)
  rw [he,h12,h36,one_mul]
lemma seed_t_reduced : CrossedConicSeed.t = 3+X^2+2*X^4 := by
  have he : CrossedConicSeed.t = 8+56*X^2+2*X^4 := by
    dsimp [CrossedConicSeed.t,CrossedConicSeed.x,CrossedConicSeed.a]
    ring
  have h8 : (8 : Polynomial K) = 3 := polyNat_eq (by decide : (8 : K)=3)
  have h56 : (56 : Polynomial K) = 1 := polyNat_eq (by decide : (56 : K)=1)
  rw [he,h8,h56,one_mul]

lemma seed_a_reduced : CrossedConicSeed.a = 2+4*X^2 := by
  have h : (4 : Polynomial K) = -1 := by
    have he : (4 : K) = -1 := by decide
    simpa only [map_ofNat,map_neg,map_one] using
      congrArg (Polynomial.C : K →+* Polynomial K) he
  dsimp [CrossedConicSeed.a]
  rw [h]
  ring

lemma curveEval_seed : curveEval seed =
    ![CrossedConicSeed.x,CrossedConicSeed.a,CrossedConicSeed.y,
      CrossedConicSeed.s,CrossedConicSeed.t] := by
  have hc2 : Polynomial.C (2 : K) = (2 : Polynomial K) := map_natCast Polynomial.C 2
  have hc4 : Polynomial.C (4 : K) = (4 : Polynomial K) := map_natCast Polynomial.C 4
  funext i
  fin_cases i <;>
    simp [curveEval,curve,coeffVar,seed,seed_a_reduced,seed_s_reduced,seed_t_reduced,
      CrossedConicSeed.x,CrossedConicSeed.y,hc2,hc4]

lemma five_zero_poly : (5 : Polynomial K)=0 := by
  have h : (5 : K)=0 := by decide
  simpa only [map_ofNat,map_zero] using congrArg (Polynomial.C : K →+* Polynomial K) h

lemma H_seed_zero : H (curveEval seed) = 0 := by
  rw [curveEval_seed]
  have he : H ![CrossedConicSeed.x,CrossedConicSeed.a,CrossedConicSeed.y,
      CrossedConicSeed.s,CrossedConicSeed.t] =
      2*(CrossedConicSeed.x^6+CrossedConicSeed.a^6+CrossedConicSeed.y^6+
        CrossedConicSeed.s^3+CrossedConicSeed.t^3)+
      5*((CrossedConicSeed.x^6+CrossedConicSeed.a^6+CrossedConicSeed.y^6+
        CrossedConicSeed.s^3+CrossedConicSeed.t^3)+
        (CrossedConicSeed.x^5*CrossedConicSeed.a+
        CrossedConicSeed.x^3*CrossedConicSeed.a*CrossedConicSeed.y^2+
        CrossedConicSeed.x*CrossedConicSeed.a*CrossedConicSeed.y^4+
        2*CrossedConicSeed.x*CrossedConicSeed.a^5)) := by
    dsimp [H]
    ring
  rw [he,CrossedConicSeed.incidence,five_zero_poly]
  ring

lemma seed_equations (i : Fin 13) : MvPolynomial.aeval seed (equations i)=0 := by
  rw [equations_eval,H_seed_zero,Polynomial.coeff_zero]

end CrossedConicIncidence
end
end

/- Source component: ConicSeedCoefficients. -/
section

noncomputable section
namespace CrossedConicSeed
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

end CrossedConicSeed
end
end

/- Source component: FixedConicSeed. -/
section

noncomputable section
namespace CrossedFixedConic
open Polynomial
open CrossedConicIncidence (H gradient H_map gradient_map)
abbrev K := ZMod 5

def parameters : Fin 3 → K := ![4,2,3]
def seed : Fin 13 → K := ![2,0,4,0,2,0,1,0,3,0,1,0,2]

def curveEval {R S : Type*} [CommRing R] [CommRing S]
    (k : Fin 3 → R) (f : R →+* S) (v : Fin 13 → S) (i : Fin 5) : Polynomial S :=
  (curve k i).map (MvPolynomial.eval₂Hom f v)

lemma equations_eval {R S : Type*} [CommRing R] [CommRing S]
    (k : Fin 3 → R) (f : R →+* S) (v : Fin 13 → S) (i : Fin 13) :
    MvPolynomial.eval₂Hom f v (equations k i) = (H (curveEval k f v)).coeff i.val := by
  change (MvPolynomial.eval₂Hom f v) ((H (curve k)).coeff i.val) = _
  rw [← Polynomial.coeff_map]
  exact congrArg (fun p : Polynomial S => p.coeff i.val)
    (H_map (Polynomial.mapRingHom (MvPolynomial.eval₂Hom f v)) (curve k))

lemma equations_pderiv_eval {R S : Type*} [CommRing R] [CommRing S]
    (k : Fin 3 → R) (f : R →+* S) (v : Fin 13 → S) (i j : Fin 13) :
    MvPolynomial.eval₂Hom f v (MvPolynomial.pderiv j (equations k i)) =
      (gradient (curveEval k f v) (slotCoordinate j)*X^slotDegree j).coeff i.val := by
  rw [equations_pderiv,← Polynomial.coeff_map,Polynomial.map_mul,
    Polynomial.map_pow,Polynomial.map_X]
  exact congrArg (fun p : Polynomial S => (p*X^slotDegree j).coeff i.val)
    (gradient_map (Polynomial.mapRingHom (MvPolynomial.eval₂Hom f v))
      (curve k) (slotCoordinate j))

lemma curveEval_seed : curveEval parameters (RingHom.id K) seed =
    ![CrossedConicSeed.x,CrossedConicSeed.a,CrossedConicSeed.y,
      CrossedConicSeed.s,CrossedConicSeed.t] := by
  have hc2 : Polynomial.C (2 : K) = (2 : Polynomial K) := map_natCast Polynomial.C 2
  have hc3 : Polynomial.C (3 : K) = (3 : Polynomial K) := map_natCast Polynomial.C 3
  have hc4 : Polynomial.C (4 : K) = (4 : Polynomial K) := map_natCast Polynomial.C 4
  funext i
  fin_cases i <;> simp [curveEval,curve,coeffVar,constPoly,seed,parameters,
    CrossedConicIncidence.seed_a_reduced,CrossedConicIncidence.seed_s_reduced,
    CrossedConicIncidence.seed_t_reduced,CrossedConicSeed.x,CrossedConicSeed.y,hc2,hc3,hc4]

lemma H_seed_zero : H (curveEval parameters (RingHom.id K) seed) = 0 := by
  rw [curveEval_seed,← CrossedConicIncidence.curveEval_seed]
  exact CrossedConicIncidence.H_seed_zero

lemma seed_equations (i : Fin 13) :
    MvPolynomial.eval₂Hom (RingHom.id K) seed (equations parameters i)=0 := by
  rw [equations_eval,H_seed_zero,Polynomial.coeff_zero]

def basicGradient : Fin 5 → Polynomial K :=
  ![CrossedConicSeed.x^5,CrossedConicSeed.a^5,CrossedConicSeed.y^5,
    3*CrossedConicSeed.s^2,3*CrossedConicSeed.t^2]

lemma gradient_seed (i : Fin 5) :
    gradient (curveEval parameters (RingHom.id K) seed) i = 2*basicGradient i := by
  have h42 : (42 : Polynomial K)=2 := CrossedConicIncidence.polyNat_eq (by decide : (42 : K)=2)
  have h21 : (21 : Polynomial K)=1 := CrossedConicIncidence.polyNat_eq (by decide : (21 : K)=1)
  have h23 : (2 : Polynomial K)*3=1 := by
    have he : (2 : K)*3=1 := by decide
    simpa only [map_mul,map_ofNat,map_one] using
      congrArg (Polynomial.C : K →+* Polynomial K) he
  rw [curveEval_seed]
  fin_cases i <;> simp [gradient,basicGradient,h42,h21,CrossedConicIncidence.five_zero_poly]
  all_goals rw [← mul_assoc,h23,one_mul]

def sourceColumn : Fin 13 → Fin 14 := ![2,3,3,5,5,7,8,9,9,11,12,13,13]
def sourceShift : Fin 13 → ℕ := ![0,0,1,0,1,0,0,0,1,0,0,0,1]

lemma seedColumns_eq (j : Fin 13) :
    gradient (curveEval parameters (RingHom.id K) seed) (slotCoordinate j)*X^slotDegree j =
      2*(X^sourceShift j*CrossedConicSeed.columns (sourceColumn j)) := by
  rw [gradient_seed]
  fin_cases j <;> simp [sourceColumn,sourceShift,basicGradient,slotCoordinate,slotDegree,
    CrossedConicSeed.columns] <;> ring

end CrossedFixedConic
end
end

/- Source component: FixedConicMatrices. -/
section

noncomputable section
namespace CrossedFixedConic
open Polynomial
open CrossedConicIncidence (gradient gradient_map)
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

lemma coeff_scaled_shift (j : Fin 14) (s n : ℕ) :
    (2*(X^s*CrossedConicSeed.columns j)).coeff n =
      2*(if s ≤ n then (if h : n-s<12 then
        CrossedConicSeed.explicit ⟨n-s,h⟩ j else 0) else 0) := by
  have h2 : (2 : Polynomial K) = Polynomial.C (2 : K) := (map_natCast Polynomial.C 2).symm
  rw [h2,Polynomial.coeff_C_mul,Polynomial.coeff_X_pow_mul',CrossedConicSeed.column_coeff]

def seedJacobian : Matrix (Fin 13) (Fin 13) K := fun i j =>
  MvPolynomial.eval₂Hom (RingHom.id K) seed (MvPolynomial.pderiv j (equations parameters i))

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

lemma seedJacobian_eq : seedJacobian = seedJacobianExplicit := by
  ext i j
  rw [seedJacobian,equations_pderiv_eval,seedColumns_eq,coeff_scaled_shift]
  fin_cases i <;> fin_cases j <;> decide

lemma seedJacobian_right : seedJacobianExplicit*seedJacobianRight=1 := by decide

lemma seed_jacobian_unit : IsUnit (Matrix.det (fun i j =>
    MvPolynomial.eval₂Hom (RingHom.id K) seed (MvPolynomial.pderiv i (equations parameters j)))) := by
  change IsUnit seedJacobian.transpose.det
  rw [Matrix.det_transpose,seedJacobian_eq]
  have hdet : seedJacobianExplicit.det*seedJacobianRight.det=1 := by
    rw [← Matrix.det_mul,seedJacobian_right,Matrix.det_one]
  apply isUnit_iff_ne_zero.mpr
  intro h
  rw [h,zero_mul] at hdet
  exact zero_ne_one hdet

def freeCoordinate : Fin 12 → Fin 5 := ![1,1,2,2,3,3,3,3,4,4,4,4]
def freeDegree : Fin 12 → ℕ := ![0,1,0,1,0,1,2,3,0,1,2,3]
def freeMatrix {R : Type*} [CommRing R] (k : Fin 3 → R) :
    Matrix (Fin 12) (Fin 12) (Coeff R) := fun i j =>
  (gradient (curve k) (freeCoordinate j)*X^freeDegree j).coeff i.val

def seedFree : Matrix (Fin 12) (Fin 12) K := fun i j =>
  MvPolynomial.eval₂Hom (RingHom.id K) seed (freeMatrix parameters i j)

lemma eval_freeMatrix_entry {R S : Type*} [CommRing R] [CommRing S]
    (k : Fin 3 → R) (f : R →+* S) (v : Fin 13 → S) (i j : Fin 12) :
    MvPolynomial.eval₂Hom f v (freeMatrix k i j) =
      (gradient (curveEval k f v) (freeCoordinate j)*X^freeDegree j).coeff i.val := by
  change (MvPolynomial.eval₂Hom f v)
    ((gradient (curve k) (freeCoordinate j)*X^freeDegree j).coeff i.val) = _
  rw [← Polynomial.coeff_map,Polynomial.map_mul,Polynomial.map_pow,Polynomial.map_X]
  exact congrArg (fun p : Polynomial S => (p*X^freeDegree j).coeff i.val)
    (gradient_map (Polynomial.mapRingHom (MvPolynomial.eval₂Hom f v))
      (curve k) (freeCoordinate j))

lemma freeColumns_seed (j : Fin 12) :
    gradient (curveEval parameters (RingHom.id K) seed) (freeCoordinate j)*X^freeDegree j =
      2*(X^0*CrossedConicSeed.columns ⟨j.val+2,by omega⟩) := by
  rw [gradient_seed]
  fin_cases j <;> simp [freeCoordinate,freeDegree,basicGradient,CrossedConicSeed.columns] <;> ring

lemma seedFree_eq : seedFree = seedFreeExplicit := by
  ext i j
  rw [seedFree,eval_freeMatrix_entry,freeColumns_seed,coeff_scaled_shift]
  fin_cases i <;> fin_cases j <;> decide

lemma seedFree_right : seedFreeExplicit*seedFreeRight=1 := by decide

lemma seedFree_det_ne_zero : seedFree.det ≠ 0 := by
  rw [seedFree_eq]
  have hdet : seedFreeExplicit.det*seedFreeRight.det=1 := by
    rw [← Matrix.det_mul,seedFree_right,Matrix.det_one]
  intro h
  rw [h,zero_mul] at hdet
  exact zero_ne_one hdet

end CrossedFixedConic
end
end

/- Source component: FixedConicBaseChange. -/
section

noncomputable section
namespace CrossedFixedConic
open Polynomial
open CrossedConicIncidence (H gradient H_map gradient_map)

lemma curve_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (k : Fin 3 → R) (i : Fin 5) :
    (curve k i).map (MvPolynomial.map f) = curve (fun j => f (k j)) i := by
  have h4 : (4 : CurvePoly R).map (MvPolynomial.map f) = (4 : CurvePoly S) :=
    map_natCast (Polynomial.mapRingHom (MvPolynomial.map f)) 4
  fin_cases i <;> simp [curve,coeffVar,constPoly,h4]

lemma equations_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (k : Fin 3 → R) (i : Fin 13) :
    MvPolynomial.map f (equations k i) = equations (fun j => f (k j)) i := by
  rw [equations,← Polynomial.coeff_map]
  have hh : (H (curve k)).map (MvPolynomial.map f) = H (curve (fun j => f (k j))) := by
    have h := H_map (Polynomial.mapRingHom (MvPolynomial.map f)) (curve k)
    change (H (curve k)).map (MvPolynomial.map f) = _ at h
    rw [h]
    congr 1
    funext j
    exact curve_map f k j
  rw [hh]
  rfl

lemma equations_pderiv_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (k : Fin 3 → R) (i j : Fin 13) :
    MvPolynomial.map f (MvPolynomial.pderiv j (equations k i)) =
      MvPolynomial.pderiv j (equations (fun j => f (k j)) i) := by
  rw [← MvPolynomial.pderiv_map,equations_map]

lemma freeMatrix_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (k : Fin 3 → R) (i j : Fin 12) :
    MvPolynomial.map f (freeMatrix k i j) = freeMatrix (fun j => f (k j)) i j := by
  rw [freeMatrix,← Polynomial.coeff_map,Polynomial.map_mul,Polynomial.map_pow,Polynomial.map_X]
  have hh : (gradient (curve k) (freeCoordinate j)).map (MvPolynomial.map f) =
      gradient (curve (fun j => f (k j))) (freeCoordinate j) := by
    have h := gradient_map (Polynomial.mapRingHom (MvPolynomial.map f)) (curve k) (freeCoordinate j)
    change (gradient (curve k) (freeCoordinate j)).map (MvPolynomial.map f) = _ at h
    rw [h]
    congr 1
    funext l
    exact curve_map f k l
  rw [hh]
  rfl

lemma freeDet_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (k : Fin 3 → R) :
    MvPolynomial.map f (freeMatrix k).det = (freeMatrix (fun j => f (k j))).det := by
  rw [RingHom.map_det]
  congr 1
  funext i j
  exact freeMatrix_map f k i j

end CrossedFixedConic
end
end
