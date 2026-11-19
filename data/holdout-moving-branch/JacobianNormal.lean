import Proposal.JacobianHypersurface

/-! The polynomial normal field for the monic Jacobian equation. The finite
incidence system was formulated for 111132 times this equation, so its normal is
scaled by 111132 here. Prepared with OpenAI Codex assistance. -/
noncomputable section
namespace CycleJacobianNormal
open HoldoutConstruction CycleJacobianIncidence CycleJacobianLifting CycleJacobianFamily
  CycleJacobianParameters CycleJacobianGeometry CycleJacobianEmbedding CycleJacobianHypersurface Polynomial
open scoped BigOperators
local notation "v" => (MvPolynomial.X : Fin 6 → Ambient)
def selectedCoordinate : Fin 3 → Fin 6 := ![4,5,0]
lemma integral_hypersurface :
    111132*hypersurface=H (v 2) (v 3) (v 1) ![v 4,v 5,v 0] :=
  CycleJacobianDomain.integral_scaling MvPolynomial.C (v 2) (v 3) (v 4) (v 1) (v 5) (v 0)
lemma selected_partial (j : Fin 3) :
    111132*MvPolynomial.pderiv (selectedCoordinate j) hypersurface=
      gradient (v 2) (v 3) (v 1) ![v 4,v 5,v 0] j := by
  have h2 (i : Fin 6) : MvPolynomial.pderiv i (2 : Ambient)=0 := (MvPolynomial.pderiv i).map_natCast 2
  have h24 (i : Fin 6) : MvPolynomial.pderiv i (24 : Ambient)=0 := (MvPolynomial.pderiv i).map_natCast 24
  have h27 (i : Fin 6) : MvPolynomial.pderiv i (27 : Ambient)=0 := (MvPolynomial.pderiv i).map_natCast 27
  have h28 (i : Fin 6) : MvPolynomial.pderiv i (28 : Ambient)=0 := (MvPolynomial.pderiv i).map_natCast 28
  have h324 (i : Fin 6) : MvPolynomial.pderiv i (324 : Ambient)=0 := (MvPolynomial.pderiv i).map_natCast 324
  have h1764 (i : Fin 6) : MvPolynomial.pderiv i (1764 : Ambient)=0 := (MvPolynomial.pderiv i).map_natCast 1764
  have h2268 (i : Fin 6) : MvPolynomial.pderiv i (2268 : Ambient)=0 := (MvPolynomial.pderiv i).map_natCast 2268
  have h4116 (i : Fin 6) : MvPolynomial.pderiv i (4116 : Ambient)=0 := (MvPolynomial.pderiv i).map_natCast 4116
  have h10584 (i : Fin 6) : MvPolynomial.pderiv i (10584 : Ambient)=0 := (MvPolynomial.pderiv i).map_natCast 10584
  have h111132 (i : Fin 6) : MvPolynomial.pderiv i (111132 : Ambient)=0 := (MvPolynomial.pderiv i).map_natCast 111132
  have h750141 (i : Fin 6) : MvPolynomial.pderiv i (750141 : Ambient)=0 := (MvPolynomial.pderiv i).map_natCast 750141
  have h := congrArg (MvPolynomial.pderiv (selectedCoordinate j)) integral_hypersurface
  simp only [MvPolynomial.pderiv_mul,h2,h24,h27,h28,h324,h1764,h2268,h4116,h10584,h111132,h750141,zero_mul,zero_add] at h
  rw [h]
  fin_cases j <;>
    simp [selectedCoordinate,H,CycleJacobian.equation,CycleJacobian.a8,CycleJacobian.b256,
      gradient,a8r,b256r,MvPolynomial.pderiv_mul,h2,h24,h27,h28,h324,h1764,h2268,h4116,h10584,h111132,h750141,MvPolynomial.pderiv_pow,
      MvPolynomial.pderiv_X,Pi.single_apply,
      show (0:Fin 6)≠4 by decide,
      show (0:Fin 6)≠5 by decide,
      show (1:Fin 6)≠0 by decide,
      show (1:Fin 6)≠4 by decide,
      show (1:Fin 6)≠5 by decide,
      show (2:Fin 6)≠0 by decide,
      show (2:Fin 6)≠4 by decide,
      show (2:Fin 6)≠5 by decide,
      show (3:Fin 6)≠0 by decide,
      show (3:Fin 6)≠4 by decide,
      show (3:Fin 6)≠5 by decide,
      show (4:Fin 6)≠0 by decide,
      show (4:Fin 6)≠5 by decide,
      show (5:Fin 6)≠0 by decide,
      show (5:Fin 6)≠4 by decide] <;> ring

def polynomialEval : Ambient →+* Polynomial CoefficientField :=
  MvPolynomial.eval₂Hom (C.comp constantMap) fullCurve
lemma polynomialEval_C (z : ℂ) : polynomialEval (MvPolynomial.C z)=C (constantMap z) := by
  simp [polynomialEval]
lemma polynomialEval_X (i : Fin 6) : polynomialEval (MvPolynomial.X i)=fullCurve i := by
  simp [polynomialEval]
lemma polynomialEval_selected_partial (j : Fin 3) :
    111132*polynomialEval (MvPolynomial.pderiv (selectedCoordinate j) hypersurface)=conicGradient j := by
  have h := congrArg polynomialEval (selected_partial j)
  rw [map_mul,map_ofNat,gradient_map] at h
  convert h using 1
  fin_cases j <;> simp [polynomialEval,conicGradient,gradient,fullCurve]

def normal (i : Fin 6) : Polynomial CoefficientField := 111132*fullNormal i
lemma normal_pairing :
    (∑ i,polynomialEval (MvPolynomial.pderiv i hypersurface)*normal i)=1 := by
  have h0 := polynomialEval_selected_partial 0
  have h1 := polynomialEval_selected_partial 1
  have h2 := polynomialEval_selected_partial 2
  simp only [selectedCoordinate,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val] at h0 h1 h2
  have hp := conicNormal_pairing
  simp only [polynomialPairing,Fin.sum_univ_succ,Fin.sum_univ_zero,Fin.reduceSucc,add_zero] at hp
  simp only [normal,fullNormal,Fin.sum_univ_succ,Matrix.cons_val_zero,Matrix.cons_val_succ,Fin.sum_univ_zero,Fin.reduceSucc]
  linear_combination (conicNormal 0)*h0+(conicNormal 1)*h1+(conicNormal 2)*h2+hp

def evaluationMatrix : Matrix (Fin 6) (Fin 6) (Polynomial CoefficientField) :=
  fun i => Fin.cases (normal i) (fun j => polynomialDerivation j (fullCurve i))
lemma evaluationMatrix_det_constant : evaluationMatrix.det.coeff 0=111132*(conicNormal 2).coeff 0 := by
  calc
    _ = Matrix.det (fun i j => (evaluationMatrix i j).coeff 0) :=
      (constantCoeff : Polynomial CoefficientField →+* CoefficientField).map_det _
    _ = _ := by
      apply endpoint_det
      · intro i
        change (111132*fullNormal i).coeff 0=_
        rw [← constantCoeff_apply,map_mul,map_ofNat,constantCoeff_apply,fullNormal_constant]
        split_ifs <;> simp
      · change (timePolynomialDerivation (fullCurve 1)).coeff 0=1
        rw [fullCurve_time,timePolynomialDerivation_apply]
        simp
      · intro j
        change (coefficientPolynomialDerivation (coefficientDerivation j) (fullCurve 1)).coeff 0=0
        rw [fullCurve_time,coefficientPolynomialDerivation_coeff]
        simp
      · intro i j
        change (coefficientPolynomialDerivation (coefficientDerivation j)
          (fullCurve i.succ.succ)).coeff 0=if i=j then 1 else 0
        rw [coefficientPolynomialDerivation_coeff,fullCurve_endpoint,coefficientDerivation_parameter]
lemma evaluationMatrix_det_ne_zero : evaluationMatrix.det≠0 := by
  intro h
  have hc := evaluationMatrix_det_constant
  rw [h,Polynomial.coeff_zero] at hc
  exact (mul_ne_zero (by norm_num) conicNormal_constant_nonzero) hc.symm
#print axioms normal_pairing
#print axioms evaluationMatrix_det_ne_zero
end CycleJacobianNormal
