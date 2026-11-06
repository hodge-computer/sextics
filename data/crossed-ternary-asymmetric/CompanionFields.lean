import HodgeComputer.Constructions.EllipticCompanions.CompanionAlgebra
import HodgeComputer.Constructions.HoldoutCover.AlgebraicFields
import HodgeComputer.Constructions.HoldoutCover.EvaluationMatrix
import HodgeComputer.Constructions.HoldoutCover.HypersurfaceDomain
import HodgeComputer.Constructions.HoldoutCover.PolynomialCalculus
import HodgeComputer.Constructions.HoldoutCover.PolynomialFamilyBridge
import HodgeComputer.Constructions.HoldoutCover.ResidueClearing
import HodgeComputer.Constructions.HoldoutCover.ResidueDerivatives
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Derivation.MapCoeffs
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Tactic

/- Prepared with OpenAI Codex assistance for contributor 1337isnot1337.
See solution.md for the construction, provenance, and prior-work credit. -/

/- Source component: FanoCompanionDomain. -/
section

noncomputable section
set_option maxHeartbeats 400000
namespace CrossedFano
open Polynomial
abbrev Coeff := MvPolynomial (Fin 4) ℂ

def lower : Polynomial Coeff :=
  C (MvPolynomial.C (10/7 : ℂ)*MvPolynomial.X 0)*X^5+
  C (MvPolynomial.C (5/7 : ℂ)*
    ((MvPolynomial.X 0)^5+(MvPolynomial.X 0)^3*(MvPolynomial.X 1)^2+
      MvPolynomial.X 0*(MvPolynomial.X 1)^4))*X+
  C ((MvPolynomial.X 0)^6+(MvPolynomial.X 1)^6+
    (MvPolynomial.X 2)^3+(MvPolynomial.X 3)^3)

def equation : Polynomial Coeff := X^6+lower

lemma lower_degree : lower.degree < 6 := by
  unfold lower
  compute_degree <;> norm_num
lemma equation_monic : equation.Monic := by
  exact monic_X_pow_add (by simpa using lower_degree)

def specialization : Coeff →+* ℂ[X] :=
  MvPolynomial.eval₂Hom C ![0,0,X-1,1]

lemma equation_specialization : equation.map specialization =
    (X : (ℂ[X])[X])^6+C ((X-1)^3+1) := by
  simp [equation,lower,specialization]

lemma equation_irreducible : Irreducible equation := by
  apply equation_monic.irreducible_of_irreducible_map specialization
  rw [equation_specialization]
  have he : (X-1)^3+1 = (X^3-3*X^2+3*X : ℂ[X]) := by ring
  rw [he]
  exact HoldoutConstruction.irreducible_power_add_constant
    (X^3-3*X^2+3*X : ℂ[X]) (by simp) (by norm_num) 6 (by decide)

abbrev CoordinateRing := AdjoinRoot equation
instance : IsDomain CoordinateRing := AdjoinRoot.isDomain_of_prime equation_irreducible.prime
abbrev FunctionField := FractionRing CoordinateRing

end CrossedFano
end
end

/- Source component: FanoAffineDomain. -/
section

noncomputable section
namespace CrossedFanoAffine
open Polynomial
abbrev Coeff := MvPolynomial (Fin 3) ℂ

def lower : Polynomial Coeff :=
  C (MvPolynomial.C (10/7 : ℂ)*MvPolynomial.X 0)*X^5+
  C (MvPolynomial.C (5/7 : ℂ)*
    ((MvPolynomial.X 0)^5+(MvPolynomial.X 0)^3+MvPolynomial.X 0))*X+
  C ((MvPolynomial.X 0)^6+1+(MvPolynomial.X 1)^3+(MvPolynomial.X 2)^3)

def equation : Polynomial Coeff := X^6+lower
lemma lower_degree : lower.degree<6 := by
  unfold lower
  compute_degree <;> norm_num
lemma equation_monic : equation.Monic := monic_X_pow_add (by simpa using lower_degree)

def specialization : Coeff →+* ℂ[X] := MvPolynomial.eval₂Hom C ![0,X-1,0]
lemma equation_specialization : equation.map specialization =
    (X : (ℂ[X])[X])^6+C ((X-1)^3+1) := by
  simp [equation,lower,specialization]
  ring

lemma equation_irreducible : Irreducible equation := by
  apply equation_monic.irreducible_of_irreducible_map specialization
  rw [equation_specialization]
  have he : (X-1)^3+1=(X^3-3*X^2+3*X : ℂ[X]) := by ring
  rw [he]
  exact HoldoutConstruction.irreducible_power_add_constant
    (X^3-3*X^2+3*X : ℂ[X]) (by simp) (by norm_num) 6 (by decide)

abbrev CoordinateRing := AdjoinRoot equation
instance : IsDomain CoordinateRing := AdjoinRoot.isDomain_of_prime equation_irreducible.prime
abbrev FunctionField := FractionRing CoordinateRing

end CrossedFanoAffine
end
end

/- Source component: FanoCubicPresentation. -/
section

noncomputable section
namespace CrossedFanoCubic
open Polynomial
abbrev Coeff := MvPolynomial (Fin 3) ℂ
/-- Coefficient order S,x,a; T is the monic normal variable. -/
def base : Coeff := MvPolynomial.X 1^6+MvPolynomial.X 2^6+1+
  MvPolynomial.C (5/7 : ℂ)*(MvPolynomial.X 1^5*MvPolynomial.X 2+
    MvPolynomial.X 1^3*MvPolynomial.X 2+MvPolynomial.X 1*MvPolynomial.X 2+
    2*MvPolynomial.X 1*MvPolynomial.X 2^5)
def equation : Polynomial Coeff := X^3+C (base+MvPolynomial.X 0^3)
lemma equation_monic : equation.Monic := monic_X_pow_add_C _ (by decide : (3 : ℕ)≠0)
def specialization : Coeff →+* ℂ[X] := MvPolynomial.eval₂Hom C ![X-1,0,0]
lemma equation_specialization : equation.map specialization=
    (X : (ℂ[X])[X])^3+C ((X-1)^3+1) := by
  simp [equation,base,specialization]
  ring
lemma equation_irreducible : Irreducible equation := by
  apply equation_monic.irreducible_of_irreducible_map specialization
  rw [equation_specialization]
  have he : (X-1)^3+1=(X^3-3*X^2+3*X : ℂ[X]) := by ring
  rw [he]
  exact HoldoutConstruction.irreducible_power_add_constant
    (X^3-3*X^2+3*X : ℂ[X]) (by simp) (by norm_num) 3 (by decide)

abbrev CoordinateRing := AdjoinRoot equation
instance : IsDomain CoordinateRing := AdjoinRoot.isDomain_of_prime equation_irreducible.prime
abbrev FunctionField := FractionRing CoordinateRing

def affineEquation : MvPolynomial (Fin 4) ℂ :=
  MvPolynomial.X 0^6+MvPolynomial.X 1^6+1+
    MvPolynomial.C (5/7 : ℂ)*(MvPolynomial.X 1^5*MvPolynomial.X 0+
      MvPolynomial.X 1^3*MvPolynomial.X 0+MvPolynomial.X 1*MvPolynomial.X 0+
      2*MvPolynomial.X 1*MvPolynomial.X 0^5)+MvPolynomial.X 2^3+MvPolynomial.X 3^3

lemma old_univariate : MvPolynomial.finSuccEquiv ℂ 3 affineEquation=CrossedFanoAffine.equation := by
  have hc : C (MvPolynomial.C (5/7 : ℂ))*(2 : Polynomial (MvPolynomial (Fin 3) ℂ))=
      C (MvPolynomial.C (10/7 : ℂ)) := by
    let φ : ℂ →+* Polynomial (MvPolynomial (Fin 3) ℂ) := Polynomial.C.comp MvPolynomial.C
    change φ (5/7)*2=φ (10/7)
    rw [← show φ 2=(2 : Polynomial (MvPolynomial (Fin 3) ℂ)) from map_natCast φ 2,← map_mul]
    congr 1
    norm_num
  have hv : (Fin.cases (Polynomial.X : Polynomial (MvPolynomial (Fin 3) ℂ))
      (fun j => C (MvPolynomial.X j)))=![X,C (MvPolynomial.X 0),C (MvPolynomial.X 1),C (MvPolynomial.X 2)] := by
    funext j; fin_cases j <;> rfl
  simp [affineEquation,MvPolynomial.finSuccEquiv_apply,hv,CrossedFanoAffine.equation,
    CrossedFanoAffine.lower]
  linear_combination C (MvPolynomial.X 0)*X^5*hc

def reverse : Fin 4 ≃ Fin 4 where
  toFun i := ![3,2,1,0] i
  invFun i := ![3,2,1,0] i
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

lemma new_univariate : MvPolynomial.finSuccEquiv ℂ 3
    (MvPolynomial.rename reverse affineEquation)=equation := by
  have hv : (Fin.cases (Polynomial.X : Polynomial (MvPolynomial (Fin 3) ℂ))
      (fun j => C (MvPolynomial.X j)))=![X,C (MvPolynomial.X 0),C (MvPolynomial.X 1),C (MvPolynomial.X 2)] := by
    funext j; fin_cases j <;> rfl
  have h2 : MvPolynomial.rename reverse (2 : MvPolynomial (Fin 4) ℂ)=2 := map_natCast _ 2
  have hc2 : Polynomial.C (2 : Coeff)=(2 : Polynomial Coeff) := map_natCast _ 2
  simp only [affineEquation,map_add,map_mul,map_pow,map_one,h2,MvPolynomial.rename_X,MvPolynomial.rename_C]
  simp [MvPolynomial.finSuccEquiv_apply,hv,equation,base,reverse,hc2]
  ring

end CrossedFanoCubic
end
end

/- Source component: CrossedConicIncidence. -/
section

/- The square coefficient incidence for the actual ternary companion.
   Coefficientwise differentiation follows the generic mechanism used in
   fqlx's accepted moving-conic proof, with the present equation and slots. -/
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
namespace CrossedConicIncidence
open Polynomial
abbrev Coeff := MvPolynomial (Fin 13) ℤ
abbrev CurvePoly := Polynomial Coeff

def coeffVar (i : Fin 13) : CurvePoly := Polynomial.C (MvPolynomial.X i)
def curve : Fin 5 → CurvePoly :=
  ![coeffVar 0+coeffVar 1*X+coeffVar 2*X^2,
    coeffVar 3+coeffVar 4*X+coeffVar 5*X^2,
    coeffVar 6+coeffVar 7*X+coeffVar 8*X^2,
    coeffVar 9+coeffVar 10*X+coeffVar 11*X^2+coeffVar 12*X^3+3*X^4,
    3+X^2+2*X^4]

def H {R : Type*} [CommRing R] (z : Fin 5 → R) : R :=
  7*(z 0^6+z 1^6+z 2^6+z 3^3+z 4^3)+
  5*(z 0^5*z 1+z 0^3*z 1*z 2^2+z 0*z 1*z 2^4+2*z 0*z 1^5)

def gradient {R : Type*} [CommRing R] (z : Fin 5 → R) : Fin 5 → R :=
  ![42*z 0^5+5*(5*z 0^4*z 1+3*z 0^2*z 1*z 2^2+z 1*z 2^4+2*z 1^5),
    42*z 1^5+5*(z 0^5+z 0^3*z 2^2+z 0*z 2^4+10*z 0*z 1^4),
    42*z 2^5+5*(2*z 0^3*z 1*z 2+4*z 0*z 1*z 2^3),
    21*z 3^2,21*z 4^2]

def equations (i : Fin 13) : Coeff := (H curve).coeff i.val

def coefficientDeriv (i : Fin 13) : Derivation ℤ CurvePoly CurvePoly :=
  PolynomialModule.equivPolynomialSelf.compDer (MvPolynomial.pderiv i).mapCoeffs

@[simp] lemma coefficientDeriv_coeff (i : Fin 13) (f : CurvePoly) (n : ℕ) :
    (coefficientDeriv i f).coeff n = MvPolynomial.pderiv i (f.coeff n) := rfl

@[simp] lemma coefficientDeriv_C (i : Fin 13) (P : Coeff) :
    coefficientDeriv i (Polynomial.C P) = Polynomial.C (MvPolynomial.pderiv i P) := by
  ext n
  by_cases hn : n=0 <;> simp [coefficientDeriv_coeff,Polynomial.coeff_C,hn]

@[simp] lemma coefficientDeriv_X (i : Fin 13) : coefficientDeriv i (X : CurvePoly) = 0 := by
  ext n
  simp [coefficientDeriv_coeff,Polynomial.coeff_X,apply_ite]

def slotCoordinate : Fin 13 → Fin 5 := ![0,0,0,1,1,1,2,2,2,3,3,3,3]
def slotDegree : Fin 13 → ℕ := ![0,1,2,0,1,2,0,1,2,0,1,2,3]

lemma curve_coefficientDeriv (j : Fin 13) (i : Fin 5) :
    coefficientDeriv j (curve i) =
      if i=slotCoordinate j then X^slotDegree j else 0 := by
  have h2 : coefficientDeriv j (2 : CurvePoly)=0 := (coefficientDeriv j).map_natCast 2
  have h3 : coefficientDeriv j (3 : CurvePoly)=0 := (coefficientDeriv j).map_natCast 3
  fin_cases j <;> fin_cases i <;>
    simp_all [curve,coeffVar,slotCoordinate,slotDegree,Derivation.leibniz,
      Derivation.leibniz_pow,smul_eq_mul,h2,h3]

lemma H_coefficientDeriv (j : Fin 13) :
    coefficientDeriv j (H curve) = gradient curve (slotCoordinate j)*X^slotDegree j := by
  have h2 : coefficientDeriv j (2 : CurvePoly)=0 := (coefficientDeriv j).map_natCast 2
  have h5 : coefficientDeriv j (5 : CurvePoly)=0 := (coefficientDeriv j).map_natCast 5
  have h7 : coefficientDeriv j (7 : CurvePoly)=0 := (coefficientDeriv j).map_natCast 7
  unfold H
  simp only [map_add,Derivation.leibniz,Derivation.leibniz_pow,h2,h5,h7,
    smul_zero,zero_smul,add_zero,curve_coefficientDeriv,smul_eq_mul]
  fin_cases j <;>
    simp_all [gradient,slotCoordinate,slotDegree] <;> ring

lemma equations_pderiv (i j : Fin 13) :
    MvPolynomial.pderiv j (equations i) =
      (gradient curve (slotCoordinate j)*X^slotDegree j).coeff i.val := by
  rw [equations,← coefficientDeriv_coeff,H_coefficientDeriv]

lemma H_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (z : Fin 5 → R) : f (H z) = H (fun i => f (z i)) := by
  have h2 : f (2 : R) = (2 : S) := map_natCast f 2
  have h5 : f (5 : R) = (5 : S) := map_natCast f 5
  have h7 : f (7 : R) = (7 : S) := map_natCast f 7
  simp [H,h2,h5,h7]

lemma gradient_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (z : Fin 5 → R) (i : Fin 5) :
    f (gradient z i) = gradient (fun i => f (z i)) i := by
  have h2 : f (2 : R) = (2 : S) := map_natCast f 2
  have h3 : f (3 : R) = (3 : S) := map_natCast f 3
  have h4 : f (4 : R) = (4 : S) := map_natCast f 4
  have h5 : f (5 : R) = (5 : S) := map_natCast f 5
  have h10 : f (10 : R) = (10 : S) := map_natCast f 10
  have h21 : f (21 : R) = (21 : S) := map_natCast f 21
  have h42 : f (42 : R) = (42 : S) := map_natCast f 42
  fin_cases i <;> simp [gradient,h2,h3,h4,h5,h10,h21,h42]

def curveEval {T : Type*} [CommRing T] [Algebra ℤ T] (v : Fin 13 → T)
    (i : Fin 5) : Polynomial T := (curve i).map (MvPolynomial.aeval v).toRingHom

lemma equations_eval {T : Type*} [CommRing T] [Algebra ℤ T]
    (v : Fin 13 → T) (i : Fin 13) :
    MvPolynomial.aeval v (equations i) = (H (curveEval v)).coeff i.val := by
  change (MvPolynomial.aeval v).toRingHom ((H curve).coeff i.val) = _
  rw [← Polynomial.coeff_map]
  exact congrArg (fun f : Polynomial T => f.coeff i.val)
    (H_map (Polynomial.mapRingHom (MvPolynomial.aeval v).toRingHom) curve)

lemma equations_pderiv_eval {T : Type*} [CommRing T] [Algebra ℤ T]
    (v : Fin 13 → T) (i j : Fin 13) :
    MvPolynomial.aeval v (MvPolynomial.pderiv j (equations i)) =
      (gradient (curveEval v) (slotCoordinate j)*X^slotDegree j).coeff i.val := by
  rw [equations_pderiv]
  change (MvPolynomial.aeval v).toRingHom
    ((gradient curve (slotCoordinate j)*X^slotDegree j).coeff i.val) = _
  rw [← Polynomial.coeff_map,Polynomial.map_mul,
    Polynomial.map_pow,Polynomial.map_X]
  exact congrArg (fun f : Polynomial T => (f*X^slotDegree j).coeff i.val)
    (gradient_map (Polynomial.mapRingHom (MvPolynomial.aeval v).toRingHom)
      curve (slotCoordinate j))

def freeCoordinate : Fin 12 → Fin 5 := ![0,0,1,1,2,2,3,3,3,3,4,4]
def freeDegree : Fin 12 → ℕ := ![0,1,0,1,0,1,0,1,2,3,0,1]
def freeMatrix : Matrix (Fin 12) (Fin 12) Coeff := fun i j =>
  (gradient curve (freeCoordinate j)*X^freeDegree j).coeff i.val
def planeMatrix : Matrix (Fin 3) (Fin 3) Coeff := fun i j =>
  (curve (i.castAdd 2)).coeff j.val
def openMinor : Coeff := freeMatrix.det*planeMatrix.det

lemma H_natDegree_le : (H curve).natDegree ≤ 12 := by
  unfold H curve coeffVar
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val]
  compute_degree

end CrossedConicIncidence
end
end

/- Source component: CrossedConicCalculus. -/
section

noncomputable section
namespace CrossedConicIncidence
open scoped BigOperators

lemma H_derivation {R : Type*} [CommRing R] (D : Derivation ℤ R R) (z : Fin 5 → R) :
    D (H z)=∑ i,gradient z i*D (z i) := by
  have h2 : D (2:R)=0 := D.map_natCast 2
  have h5 : D (5:R)=0 := D.map_natCast 5
  have h7 : D (7:R)=0 := D.map_natCast 7
  simp only [H,map_add,Derivation.leibniz,Derivation.leibniz_pow,h2,h5,h7,
    smul_eq_mul,zero_mul,add_zero,Fin.sum_univ_succ,Finset.sum_empty,Finset.sum_const_zero]
  simp only [gradient,Matrix.cons_val_zero,Matrix.cons_val_succ,Fin.isValue]
  dsimp
  ring

lemma gradient_derivation_pairing {R : Type*} [CommRing R]
    (D : Derivation ℤ R R) (z : Fin 5 → R) (hz : H z=0) :
    (∑ i,gradient z i*D (z i))=0 := by
  rw [← H_derivation,hz,map_zero]

lemma two_step_evaluation_det {R : Type*} [CommRing R]
    (P : Matrix (Fin 5) (Fin 5) R)
    (h0 : ∀ j, P 0 j=if j=0 then 1 else 0)
    (h11 : P 1 1=4)
    (h1 : ∀ j : Fin 3,P 1 j.succ.succ=0)
    (he : ∀ i j : Fin 3,P i.succ.succ j.succ.succ=if i=j then 1 else 0) :
    P.det=4 := by
  rw [HoldoutConstruction.det_single_first_row P (by intro j; simp [h0])]
  rw [HoldoutConstruction.det_single_first_row (P.submatrix Fin.succ Fin.succ) h1]
  have hi : (P.submatrix Fin.succ Fin.succ).submatrix Fin.succ Fin.succ=
      (1 : Matrix (Fin 3) (Fin 3) R) := by
    funext i j
    exact he i j
  rw [hi,Matrix.det_one,mul_one]
  change P 0 0*P 1 1=4
  rw [h0,if_pos rfl,h11,one_mul]

end CrossedConicIncidence
end
end

/- Source component: FanoAffineCoordinates. -/
section

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace CrossedFanoAffine
open Polynomial HoldoutConstruction

instance : CharZero FunctionField :=
  charZero_of_injective_ringHom (f:=algebraMap ℂ FunctionField) (algebraMap ℂ FunctionField).injective

def coefficientMap : Coeff →+* FunctionField :=
  (algebraMap CoordinateRing FunctionField).comp (AdjoinRoot.of equation)

lemma coefficientMap_injective : Function.Injective coefficientMap :=
  (IsFractionRing.injective CoordinateRing FunctionField).comp
    (AdjoinRoot.of.injective_of_degree_ne_zero
      (ne_of_gt (equation_monic.degree_pos_of_not_isUnit equation_irreducible.not_isUnit)))

@[simp] lemma coefficientMap_C (c : ℂ) : coefficientMap (MvPolynomial.C c)=algebraMap ℂ FunctionField c := rfl

def coordinate (i : Fin 3) : FunctionField := coefficientMap (MvPolynomial.X i)
def normal : FunctionField := algebraMap CoordinateRing FunctionField (AdjoinRoot.root equation)

lemma normal_root : equation.eval₂ coefficientMap normal=0 := by
  have h := congrArg (algebraMap CoordinateRing FunctionField) (AdjoinRoot.eval₂_root equation)
  rw [map_zero,Polynomial.hom_eval₂] at h
  exact h

lemma cleared_equation : CrossedConicIncidence.H
    ![coordinate 0,normal,1,coordinate 1,coordinate 2]=0 := by
  have h := normal_root
  simp only [equation,lower,Polynomial.eval₂_add,Polynomial.eval₂_pow,Polynomial.eval₂_X,
    Polynomial.eval₂_mul,Polynomial.eval₂_C,map_add,map_mul,map_pow,map_one,
    coefficientMap_C,Polynomial.eval₂_one] at h
  have h5 : algebraMap ℂ FunctionField (5/7 : ℂ)=(5/7 : FunctionField) := by
    rw [map_div₀]
    congr 1 <;> exact map_natCast _ _
  have h10 : algebraMap ℂ FunctionField (10/7 : ℂ)=(10/7 : FunctionField) := by
    rw [map_div₀]
    congr 1 <;> exact map_natCast _ _
  rw [h5,h10] at h
  unfold CrossedConicIncidence.H
  simp [Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Matrix.vecHead,Matrix.vecTail,
    coordinate]
  linear_combination 7*h

end CrossedFanoAffine
end
end

/- Source component: FanoRadialEmbedding. -/
section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 100000
namespace CrossedFanoRadial
open Polynomial HoldoutConstruction
abbrev AffineField := CrossedFanoAffine.FunctionField
abbrev RadialField := RatFunc AffineField

def coefficientEmbedding : CrossedFanoAffine.Coeff →+* AffineField := CrossedFanoAffine.coefficientMap
def rawPolynomialMap : CrossedFano.Coeff →+* Polynomial AffineField :=
  (Polynomial.mapRingHom coefficientEmbedding).comp
    ((MvPolynomial.finSuccEquiv ℂ 3).toRingHom.comp
      (MvPolynomial.rename (Equiv.swap (0 : Fin 4) 1)).toRingHom)

lemma rawPolynomialMap_injective : Function.Injective rawPolynomialMap :=
  (Polynomial.map_injective coefficientEmbedding CrossedFanoAffine.coefficientMap_injective).comp
    ((MvPolynomial.finSuccEquiv ℂ 3).injective.comp
      (MvPolynomial.rename_injective (R:=ℂ) (Equiv.swap (0 : Fin 4) 1)
        (Equiv.swap (0 : Fin 4) 1).injective))

lemma rawPolynomialMap_C (c : ℂ) : rawPolynomialMap (MvPolynomial.C c)=
    Polynomial.C (algebraMap ℂ AffineField c) := by
  simp [rawPolynomialMap,coefficientEmbedding,MvPolynomial.rename_C,
    MvPolynomial.finSuccEquiv_apply]

lemma rawPolynomialMap_X (i : Fin 4) : rawPolynomialMap (MvPolynomial.X i)=
    ![C (CrossedFanoAffine.coordinate 0),X,C (CrossedFanoAffine.coordinate 1),
      C (CrossedFanoAffine.coordinate 2)] i := by
  have hv : (Fin.cases (Polynomial.X : Polynomial CrossedFanoAffine.Coeff)
      (fun j => C (MvPolynomial.X j)))=![X,C (MvPolynomial.X 0),C (MvPolynomial.X 1),C (MvPolynomial.X 2)] := by
    funext j
    fin_cases j <;> rfl
  fin_cases i <;>
    simp [rawPolynomialMap,coefficientEmbedding,CrossedFanoAffine.coordinate,
      MvPolynomial.finSuccEquiv_apply,hv,Equiv.swap_apply_def]

def polynomialCoefficientMap : CrossedFano.Coeff →+* Polynomial AffineField :=
  rawPolynomialMap.comp CrossedWeightedRadial.monomialMap

lemma polynomialCoefficientMap_injective : Function.Injective polynomialCoefficientMap := by
  intro p q h
  apply CrossedWeightedRadial.monomialMap_injective (R:=ℂ)
  apply rawPolynomialMap_injective
  exact h

def coefficientMap : CrossedFano.Coeff →+* RadialField :=
  (algebraMap (Polynomial AffineField) RadialField).comp polynomialCoefficientMap

lemma coefficientMap_injective : Function.Injective coefficientMap :=
  (IsFractionRing.injective (Polynomial AffineField) RadialField).comp polynomialCoefficientMap_injective

def coneCoordinate (i : Fin 5) : RadialField :=
  ![RatFunc.X*RatFunc.C (CrossedFanoAffine.coordinate 0),
    RatFunc.X*RatFunc.C CrossedFanoAffine.normal,RatFunc.X,
    RatFunc.X^2*RatFunc.C (CrossedFanoAffine.coordinate 1),
    RatFunc.X^2*RatFunc.C (CrossedFanoAffine.coordinate 2)] i

lemma coefficientMap_C (c : ℂ) : coefficientMap (MvPolynomial.C c)=algebraMap ℂ RadialField c := by
  rw [coefficientMap,RingHom.comp_apply,polynomialCoefficientMap,RingHom.comp_apply,
    CrossedWeightedRadial.monomialMap_C,rawPolynomialMap_C]
  rfl

lemma coefficientMap_X (i : Fin 4) : coefficientMap (MvPolynomial.X i)=
    ![coneCoordinate 0,coneCoordinate 2,coneCoordinate 3,coneCoordinate 4] i := by
  rw [coefficientMap,RingHom.comp_apply,polynomialCoefficientMap,RingHom.comp_apply,
    CrossedWeightedRadial.monomialMap_X]
  fin_cases i <;> simp [rawPolynomialMap_X,coneCoordinate,RatFunc.algebraMap_X,RatFunc.algebraMap_C]
  all_goals ring

lemma coneCoordinate_equation : CrossedConicIncidence.H coneCoordinate=0 := by
  have h := congrArg (RatFunc.C : AffineField →+* RadialField)
    CrossedFanoAffine.cleared_equation
  rw [map_zero,CrossedConicIncidence.H_map] at h
  simp [CrossedConicIncidence.H,coneCoordinate] at h ⊢
  linear_combination (RatFunc.X : RadialField)^6*h

lemma normal_root : CrossedFano.equation.eval₂ coefficientMap (coneCoordinate 1)=0 := by
  have h := coneCoordinate_equation
  simp only [CrossedFano.equation,CrossedFano.lower,Polynomial.eval₂_add,
    Polynomial.eval₂_pow,Polynomial.eval₂_X,Polynomial.eval₂_mul,Polynomial.eval₂_C,
    map_add,map_mul,map_pow,coefficientMap_C,coefficientMap_X]
  have h5 : algebraMap ℂ RadialField (5/7 : ℂ)=(5/7 : RadialField) := by
    rw [map_div₀]
    congr 1 <;> exact map_natCast _ _
  have h10 : algebraMap ℂ RadialField (10/7 : ℂ)=(10/7 : RadialField) := by
    rw [map_div₀]
    congr 1 <;> exact map_natCast _ _
  rw [h5,h10]
  simp [Matrix.cons_val_two,Matrix.cons_val_three,Matrix.vecHead,Matrix.vecTail]
  unfold CrossedConicIncidence.H at h
  linear_combination h/7

def coneRingMap : CrossedFano.CoordinateRing →+* RadialField :=
  AdjoinRoot.lift (f:=CrossedFano.equation) coefficientMap (coneCoordinate 1) normal_root

lemma coneRingMap_injective : Function.Injective coneRingMap :=
  monic_root_embedding_injective CrossedFano.equation CrossedFano.equation_monic
    CrossedFano.equation_irreducible coefficientMap coefficientMap_injective
    (coneCoordinate 1) normal_root

def coneFieldMap : CrossedFano.FunctionField →+* RadialField :=
  IsFractionRing.lift coneRingMap_injective

end CrossedFanoRadial
end
end

/- Source component: FanoAffineDerivations. -/
section

noncomputable section
namespace CrossedFanoAffine
open HoldoutConstruction
local instance : Algebra ℤ FunctionField := Ring.toIntAlgebra _

abbrev hypersurface := CrossedMonicHypersurface.equation equation
abbrev residueMap := CrossedMonicHypersurface.residueMap equation
def tangent (i : Fin 3) : Derivation ℤ FunctionField FunctionField :=
  CrossedMonicHypersurface.tangent equation equation_monic equation_irreducible i

lemma residueMap_coordinate (j : Fin 3) : residueMap (MvPolynomial.X j.succ)=coordinate j :=
  CrossedMonicHypersurface.residueMap_X_succ equation j

lemma tangent_coordinate (i j : Fin 3) : tangent i (coordinate j)=if j=i then 1 else 0 := by
  rw [← residueMap_coordinate]
  exact CrossedMonicHypersurface.tangent_parameter equation equation_monic equation_irreducible i j

@[simp] lemma tangent_base (i : Fin 3) (c : ℂ) : tangent i (algebraMap ℂ FunctionField c)=0 :=
  CrossedMonicHypersurface.tangent_constant equation equation_monic equation_irreducible i c

def normalGradient : FunctionField := residueMap (MvPolynomial.pderiv 0 hypersurface)
lemma normalGradient_ne_zero : normalGradient≠0 :=
  CrossedMonicHypersurface.normal_ne_zero equation equation_monic equation_irreducible

end CrossedFanoAffine
end
end

/- Source component: FanoConeProjection. -/
section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 100000
namespace CrossedFano
open Polynomial HoldoutConstruction

def hypersurface : MvPolynomial (Fin 5) ℂ :=
  CrossedConicIncidence.H ![MvPolynomial.X 1,MvPolynomial.X 0,MvPolynomial.X 2,
    MvPolynomial.X 3,MvPolynomial.X 4]

lemma scalar_five_seven : C (MvPolynomial.C (5/7 : ℂ))*(7 : Polynomial Coeff)=5 := by
  let φ : ℂ →+* Polynomial Coeff := Polynomial.C.comp MvPolynomial.C
  change φ (5/7)*7=5
  rw [← show φ 7=(7 : Polynomial Coeff) from map_natCast φ 7,← map_mul]
  norm_num
  exact map_natCast φ 5

lemma scalar_ten_seven : C (MvPolynomial.C (10/7 : ℂ))*(7 : Polynomial Coeff)=10 := by
  let φ : ℂ →+* Polynomial Coeff := Polynomial.C.comp MvPolynomial.C
  change φ (10/7)*7=10
  rw [← show φ 7=(7 : Polynomial Coeff) from map_natCast φ 7,← map_mul]
  norm_num
  exact map_natCast φ 10

lemma independent_vector : (Fin.cases (Polynomial.X : Polynomial Coeff)
    (fun j => C (MvPolynomial.X j)))=
    ![X,C (MvPolynomial.X 0),C (MvPolynomial.X 1),C (MvPolynomial.X 2),C (MvPolynomial.X 3)] := by
  funext i
  fin_cases i <;> rfl

lemma hypersurface_univariate : MvPolynomial.finSuccEquiv ℂ 4 hypersurface=7*equation := by
  simp [hypersurface,CrossedConicIncidence.H,equation,lower,
    MvPolynomial.finSuccEquiv_apply,Polynomial.C_ofNat,independent_vector]
  try dsimp
  linear_combination -(C (MvPolynomial.X 0)^5+C (MvPolynomial.X 0)^3*C (MvPolynomial.X 1)^2+
    C (MvPolynomial.X 0)*C (MvPolynomial.X 1)^4)*X*scalar_five_seven -
    C (MvPolynomial.X 0)*X^5*scalar_ten_seven

lemma hypersurface_partial (j : Fin 5) : integerPartial j hypersurface=
    CrossedConicIncidence.gradient
      ![MvPolynomial.X 1,MvPolynomial.X 0,MvPolynomial.X 2,MvPolynomial.X 3,MvPolynomial.X 4]
      (Equiv.swap (0 : Fin 5) 1 j) := by
  rw [hypersurface,CrossedConicIncidence.H_derivation]
  fin_cases j <;>
    simp [CrossedConicIncidence.gradient,Fin.sum_univ_succ,Equiv.swap_apply_def,
      integerPartial_X_of_ne]

def projection : MvPolynomial (Fin 5) ℂ →+* CoordinateRing :=
  (AdjoinRoot.mk equation).comp (MvPolynomial.finSuccEquiv ℂ 4).toRingHom

lemma projection_surjective : Function.Surjective projection :=
  (AdjoinRoot.mk_surjective (g:=equation)).comp (MvPolynomial.finSuccEquiv ℂ 4).surjective

@[simp] lemma projection_X_zero : projection (MvPolynomial.X 0)=AdjoinRoot.root equation := by
  change AdjoinRoot.mk equation (MvPolynomial.finSuccEquiv ℂ 4 (MvPolynomial.X 0))=_
  rw [MvPolynomial.finSuccEquiv_X_zero]
  rfl

@[simp] lemma projection_X_succ (i : Fin 4) :
    projection (MvPolynomial.X i.succ)=AdjoinRoot.of equation (MvPolynomial.X i) := by
  change AdjoinRoot.mk equation (MvPolynomial.finSuccEquiv ℂ 4 (MvPolynomial.X i.succ))=_
  rw [MvPolynomial.finSuccEquiv_X_succ]
  rfl

lemma seven_unit : IsUnit (7 : Polynomial Coeff) := by
  have h : IsUnit (7 : ℂ) := isUnit_iff_ne_zero.mpr (by norm_num)
  exact (h.map (MvPolynomial.C : ℂ →+* Coeff)).map (Polynomial.C : Coeff →+* Polynomial Coeff)

lemma projection_kernel (p : MvPolynomial (Fin 5) ℂ) :
    projection p=0 ↔ hypersurface ∣ p := by
  change AdjoinRoot.mk equation (MvPolynomial.finSuccEquiv ℂ 4 p)=0 ↔ _
  rw [AdjoinRoot.mk_eq_zero]
  rw [← map_dvd_iff (MvPolynomial.finSuccEquiv ℂ 4),hypersurface_univariate]
  exact (seven_unit.mul_left_dvd).symm

def residueMap : MvPolynomial (Fin 5) ℂ →+* FunctionField :=
  (algebraMap CoordinateRing FunctionField).comp projection

lemma residueMap_kernel (p : MvPolynomial (Fin 5) ℂ) :
    residueMap p=0 ↔ hypersurface ∣ p :=
  residue_fractionMap_kernel projection hypersurface projection_kernel p

@[simp] lemma residueMap_C (c : ℂ) : residueMap (MvPolynomial.C c)=algebraMap ℂ FunctionField c := by
  change algebraMap CoordinateRing FunctionField
    (AdjoinRoot.mk equation (MvPolynomial.finSuccEquiv ℂ 4 (MvPolynomial.C c))) = _
  rw [show MvPolynomial.finSuccEquiv ℂ 4 (MvPolynomial.C c)=C (MvPolynomial.C c)
    from (MvPolynomial.finSuccEquiv ℂ 4).commutes c]
  rfl

lemma hypersurface_normal_univariate :
    MvPolynomial.finSuccEquiv ℂ 4 (integerPartial 0 hypersurface)=7*equation.derivative := by
  have h2 : MvPolynomial.pderiv (R:=ℂ) (0 : Fin 5) (2 : MvPolynomial (Fin 5) ℂ)=0 :=
    (MvPolynomial.pderiv 0).map_natCast 2
  have h5 : MvPolynomial.pderiv (R:=ℂ) (0 : Fin 5) (5 : MvPolynomial (Fin 5) ℂ)=0 :=
    (MvPolynomial.pderiv 0).map_natCast 5
  have h7 : MvPolynomial.pderiv (R:=ℂ) (0 : Fin 5) (7 : MvPolynomial (Fin 5) ℂ)=0 :=
    (MvPolynomial.pderiv 0).map_natCast 7
  simp [hypersurface,CrossedConicIncidence.H,equation,lower,integerPartial,
    MvPolynomial.pderiv_mul,MvPolynomial.pderiv_pow,Pi.single_apply,
    MvPolynomial.finSuccEquiv_apply,Polynomial.C_ofNat,independent_vector,h2,h5,h7]
  try dsimp
  simp only [derivative_add,derivative_mul,derivative_pow,derivative_C,derivative_X]
  linear_combination -(C (MvPolynomial.X 0)^5+C (MvPolynomial.X 0)^3*C (MvPolynomial.X 1)^2+
    C (MvPolynomial.X 0)*C (MvPolynomial.X 1)^4)*scalar_five_seven -
    5*C (MvPolynomial.X 0)*X^4*scalar_ten_seven

lemma normal_ne_zero : residueMap (integerPartial 0 hypersurface)≠0 := by
  have hp : equation.natDegree≠0 := by
    intro h
    have he := equation_monic.degree_pos_of_not_isUnit equation_irreducible.not_isUnit
    rw [degree_eq_natDegree equation_monic.ne_zero,h] at he
    exact (lt_irrefl _ he)
  have hd := AdjoinRoot.mk_ne_zero_of_degree_lt equation_monic
    (Polynomial.derivative_ne_zero.mpr hp) (degree_derivative_lt equation_monic.ne_zero)
  change algebraMap CoordinateRing FunctionField
    (AdjoinRoot.mk equation (MvPolynomial.finSuccEquiv ℂ 4 (integerPartial 0 hypersurface)))≠0
  rw [hypersurface_normal_univariate,map_mul,map_mul]
  apply mul_ne_zero
  · exact (seven_unit.map (AdjoinRoot.mk equation)).map
      (algebraMap CoordinateRing FunctionField) |>.ne_zero
  · simpa only [map_zero] using (IsFractionRing.injective CoordinateRing FunctionField).ne hd

local instance : Algebra ℤ FunctionField := Ring.toIntAlgebra _

def tangent (i : Fin 4) : Derivation ℤ FunctionField FunctionField :=
  residueTangent (K:=FunctionField) projection projection_surjective
    (integerPartial 0) (integerPartial i.succ) hypersurface projection_kernel normal_ne_zero

lemma tangent_apply (i : Fin 4) (p : MvPolynomial (Fin 5) ℂ) :
    tangent i (residueMap p)=residueMap (integerPartial i.succ p)-
      residueMap (integerPartial i.succ hypersurface)/residueMap (integerPartial 0 hypersurface)*
      residueMap (integerPartial 0 p) :=
  residueTangent_apply (K:=FunctionField) projection projection_surjective
    (integerPartial 0) (integerPartial i.succ) hypersurface projection_kernel normal_ne_zero p

@[simp] lemma tangent_base (i : Fin 4) (c : ℂ) : tangent i (algebraMap ℂ FunctionField c)=0 := by
  rw [← residueMap_C,tangent_apply]
  simp only [integerPartial_C,map_zero,mul_zero,sub_self]

lemma tangent_parameter (i j : Fin 4) :
    tangent i (residueMap (MvPolynomial.X j.succ))=if j=i then 1 else 0 := by
  rw [tangent_apply,integerPartial_X_of_ne 0 j.succ (Fin.succ_ne_zero j)]
  simp only [map_zero,mul_zero,sub_zero]
  by_cases h : j=i
  · subst j; simp
  · have hs : j.succ≠i.succ := fun he => h (Fin.succ_injective _ he)
    simp [integerPartial_X_of_ne _ _ hs,h]

end CrossedFano
end
end
