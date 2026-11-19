import Proposal.JacobianHypersurface

/-! The polynomial normal field for the monic Jacobian equation. The finite
incidence system was formulated for 432 times this equation, so its normal is
scaled by 432 here. Prepared with OpenAI Codex assistance. -/
noncomputable section
namespace MixedPolarJacobianNormal
open HoldoutConstruction MixedPolarJacobianIncidence MixedPolarJacobianLifting MixedPolarJacobianFamily
  MixedPolarJacobianParameters MixedPolarJacobianGeometry MixedPolarJacobianEmbedding MixedPolarJacobianHypersurface Polynomial
open scoped BigOperators
local notation "v" => (MvPolynomial.X : Fin 6 → Ambient)
def selectedCoordinate : Fin 3 → Fin 6 := ![4,5,0]
lemma integral_hypersurface :
    432*hypersurface=H (v 2) (v 3) (v 1) ![v 4,v 5,v 0] :=
  MixedPolarJacobianDomain.integral_scaling MvPolynomial.C (v 2) (v 3) (v 4) (v 1) (v 5) (v 0)
lemma selected_partial (j : Fin 3) :
    432*MvPolynomial.pderiv (selectedCoordinate j) hypersurface=
      gradient (v 2) (v 3) (v 1) ![v 4,v 5,v 0] j := by
  have h4 (i : Fin 6) : MvPolynomial.pderiv i (4 : Ambient)=0 := (MvPolynomial.pderiv i).map_natCast 4
  have h3 (i : Fin 6) : MvPolynomial.pderiv i (3 : Ambient)=0 := (MvPolynomial.pderiv i).map_natCast 3
  have h6 (i : Fin 6) : MvPolynomial.pderiv i (6 : Ambient)=0 := (MvPolynomial.pderiv i).map_natCast 6
  have h12 (i : Fin 6) : MvPolynomial.pderiv i (12 : Ambient)=0 := (MvPolynomial.pderiv i).map_natCast 12
  have h16 (i : Fin 6) : MvPolynomial.pderiv i (16 : Ambient)=0 := (MvPolynomial.pderiv i).map_natCast 16
  have h18 (i : Fin 6) : MvPolynomial.pderiv i (18 : Ambient)=0 := (MvPolynomial.pderiv i).map_natCast 18
  have h32 (i : Fin 6) : MvPolynomial.pderiv i (32 : Ambient)=0 := (MvPolynomial.pderiv i).map_natCast 32
  have h48 (i : Fin 6) : MvPolynomial.pderiv i (48 : Ambient)=0 := (MvPolynomial.pderiv i).map_natCast 48
  have h54 (i : Fin 6) : MvPolynomial.pderiv i (54 : Ambient)=0 := (MvPolynomial.pderiv i).map_natCast 54
  have h64 (i : Fin 6) : MvPolynomial.pderiv i (64 : Ambient)=0 := (MvPolynomial.pderiv i).map_natCast 64
  have h70 (i : Fin 6) : MvPolynomial.pderiv i (70 : Ambient)=0 := (MvPolynomial.pderiv i).map_natCast 70
  have h108 (i : Fin 6) : MvPolynomial.pderiv i (108 : Ambient)=0 := (MvPolynomial.pderiv i).map_natCast 108
  have h140 (i : Fin 6) : MvPolynomial.pderiv i (140 : Ambient)=0 := (MvPolynomial.pderiv i).map_natCast 140
  have h162 (i : Fin 6) : MvPolynomial.pderiv i (162 : Ambient)=0 := (MvPolynomial.pderiv i).map_natCast 162
  have h216 (i : Fin 6) : MvPolynomial.pderiv i (216 : Ambient)=0 := (MvPolynomial.pderiv i).map_natCast 216
  have h270 (i : Fin 6) : MvPolynomial.pderiv i (270 : Ambient)=0 := (MvPolynomial.pderiv i).map_natCast 270
  have h280 (i : Fin 6) : MvPolynomial.pderiv i (280 : Ambient)=0 := (MvPolynomial.pderiv i).map_natCast 280
  have h324 (i : Fin 6) : MvPolynomial.pderiv i (324 : Ambient)=0 := (MvPolynomial.pderiv i).map_natCast 324
  have h420 (i : Fin 6) : MvPolynomial.pderiv i (420 : Ambient)=0 := (MvPolynomial.pderiv i).map_natCast 420
  have h432 (i : Fin 6) : MvPolynomial.pderiv i (432 : Ambient)=0 := (MvPolynomial.pderiv i).map_natCast 432
  have h648 (i : Fin 6) : MvPolynomial.pderiv i (648 : Ambient)=0 := (MvPolynomial.pderiv i).map_natCast 648
  have h864 (i : Fin 6) : MvPolynomial.pderiv i (864 : Ambient)=0 := (MvPolynomial.pderiv i).map_natCast 864
  have h972 (i : Fin 6) : MvPolynomial.pderiv i (972 : Ambient)=0 := (MvPolynomial.pderiv i).map_natCast 972
  have h1296 (i : Fin 6) : MvPolynomial.pderiv i (1296 : Ambient)=0 := (MvPolynomial.pderiv i).map_natCast 1296
  have h1620 (i : Fin 6) : MvPolynomial.pderiv i (1620 : Ambient)=0 := (MvPolynomial.pderiv i).map_natCast 1620
  have h1944 (i : Fin 6) : MvPolynomial.pderiv i (1944 : Ambient)=0 := (MvPolynomial.pderiv i).map_natCast 1944
  have h2592 (i : Fin 6) : MvPolynomial.pderiv i (2592 : Ambient)=0 := (MvPolynomial.pderiv i).map_natCast 2592
  have h2916 (i : Fin 6) : MvPolynomial.pderiv i (2916 : Ambient)=0 := (MvPolynomial.pderiv i).map_natCast 2916
  have h5832 (i : Fin 6) : MvPolynomial.pderiv i (5832 : Ambient)=0 := (MvPolynomial.pderiv i).map_natCast 5832
  have h11664 (i : Fin 6) : MvPolynomial.pderiv i (11664 : Ambient)=0 := (MvPolynomial.pderiv i).map_natCast 11664
  have h17496 (i : Fin 6) : MvPolynomial.pderiv i (17496 : Ambient)=0 := (MvPolynomial.pderiv i).map_natCast 17496
  have h23328 (i : Fin 6) : MvPolynomial.pderiv i (23328 : Ambient)=0 := (MvPolynomial.pderiv i).map_natCast 23328
  have h29160 (i : Fin 6) : MvPolynomial.pderiv i (29160 : Ambient)=0 := (MvPolynomial.pderiv i).map_natCast 29160
  have h46656 (i : Fin 6) : MvPolynomial.pderiv i (46656 : Ambient)=0 := (MvPolynomial.pderiv i).map_natCast 46656
  have h69984 (i : Fin 6) : MvPolynomial.pderiv i (69984 : Ambient)=0 := (MvPolynomial.pderiv i).map_natCast 69984
  have h := congrArg (MvPolynomial.pderiv (selectedCoordinate j)) integral_hypersurface
  simp only [MvPolynomial.pderiv_mul,h432,zero_mul,zero_add] at h
  rw [h]
  fin_cases j <;>
    simp [selectedCoordinate,H,MixedPolarJacobian.equation,MixedPolarJacobian.a8,MixedPolarJacobian.a432,MixedPolarJacobian.b256,MixedPolarJacobian.b432,
      gradient,a8r,b256r,MvPolynomial.pderiv_mul,MvPolynomial.pderiv_pow,
      MvPolynomial.pderiv_X,Pi.single_apply,h4,h3,h6,h12,h16,h18,h32,h48,h54,h64,h70,h108,h140,h162,h216,h270,h280,h324,h420,h432,h648,h864,h972,h1296,h1620,h1944,h2592,h2916,h5832,h11664,h17496,h23328,h29160,h46656,h69984,
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
    432*polynomialEval (MvPolynomial.pderiv (selectedCoordinate j) hypersurface)=conicGradient j := by
  have h := congrArg polynomialEval (selected_partial j)
  rw [map_mul,map_ofNat,gradient_map] at h
  convert h using 1
  fin_cases j <;> simp [polynomialEval,conicGradient,gradient,fullCurve]

def normal (i : Fin 6) : Polynomial CoefficientField := 432*fullNormal i
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
lemma evaluationMatrix_det_constant : evaluationMatrix.det.coeff 0=432*(conicNormal 2).coeff 0 := by
  calc
    _ = Matrix.det (fun i j => (evaluationMatrix i j).coeff 0) :=
      (constantCoeff : Polynomial CoefficientField →+* CoefficientField).map_det _
    _ = _ := by
      apply HoldoutConstruction.endpoint_det
      · intro i
        change (432*fullNormal i).coeff 0=_
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
end MixedPolarJacobianNormal
