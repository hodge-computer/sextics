import Proposal.QuarticSeed

noncomputable section
namespace CoupledFanoQuarticSeed
open Polynomial
variable {K : Type*} [Field K] [CharP K 5]

def seedGradient (j : K) : Fin 6 → K[X] :=
  ![-C j*(1+X^20), C (2-j)*(X^5+X^15), -C j*X^10,
    -C j*(X^5-X^15), 1-X^20, 3+X^4+4*X^8+X^12+3*X^16]

lemma seedGradient_weight_one {j : K} (hj : j^2=2) (i : Fin 5) :
    seedGradient j i.castSucc = 6*(seedX j i)^5 := by
  have h5 : (5 : K[X])=0 := CharP.cast_eq_zero _ 5
  have hjp : (C j : K[X])^2=2 := by simp only [←map_pow,hj,map_ofNat]
  fin_cases i
  · norm_num [seedGradient, seedX, Fin.castSucc_mk, Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val, map_ofNat]
    linear_combination (-6*(C j)^3*X^20 - 30*(C j)^3*X^16 - 60*(C j)^3*X^12 - 60*(C j)^3*X^8 - 30*(C j)^3*X^4 - 6*(C j)^3 - 12*(C j)*X^20 - 60*(C j)*X^16 - 120*(C j)*X^12 - 120*(C j)*X^8 - 60*(C j)*X^4 - 12*(C j))*hjp + (-5*(C j)*X^20 - 24*(C j)*X^16 - 48*(C j)*X^12 - 48*(C j)*X^8 - 24*(C j)*X^4 - 5*(C j))*h5
  · norm_num [seedGradient, seedX, Fin.castSucc_mk, Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val, map_ofNat]
    linear_combination (-6*(C j)^3*X^15 - 30*(C j)^3*X^13 - 60*(C j)^3*X^11 - 60*(C j)^3*X^9 - 30*(C j)^3*X^7 - 6*(C j)^3*X^5 - 60*(C j)^2*X^15 - 300*(C j)^2*X^13 - 600*(C j)^2*X^11 - 600*(C j)^2*X^9 - 300*(C j)^2*X^7 - 60*(C j)^2*X^5 - 252*(C j)*X^15 - 1260*(C j)*X^13 - 2520*(C j)*X^11 - 2520*(C j)*X^9 - 1260*(C j)*X^7 - 252*(C j)*X^5 - 600*X^15 - 3000*X^13 - 6000*X^11 - 6000*X^9 - 3000*X^7 - 600*X^5)*hjp + (-197*(C j)*X^15 - 984*(C j)*X^13 - 1968*(C j)*X^11 - 1968*(C j)*X^9 - 984*(C j)*X^7 - 197*(C j)*X^5 - 278*X^15 - 1392*X^13 - 2784*X^11 - 2784*X^9 - 1392*X^7 - 278*X^5)*h5
  · norm_num [seedGradient, seedX, Fin.castSucc_mk, Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val, map_ofNat]
    linear_combination (-6*(C j)^3*X^10 - 12*(C j)*X^10)*hjp + (-5*(C j)*X^10)*h5
  · norm_num [seedGradient, seedX, Fin.castSucc_mk, Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val, map_ofNat]
    linear_combination (6*(C j)^3*X^15 - 30*(C j)^3*X^13 + 60*(C j)^3*X^11 - 60*(C j)^3*X^9 + 30*(C j)^3*X^7 - 6*(C j)^3*X^5 + 12*(C j)*X^15 - 60*(C j)*X^13 + 120*(C j)*X^11 - 120*(C j)*X^9 + 60*(C j)*X^7 - 12*(C j)*X^5)*hjp + (5*(C j)*X^15 - 24*(C j)*X^13 + 48*(C j)*X^11 - 48*(C j)*X^9 + 24*(C j)*X^7 - 5*(C j)*X^5)*h5
  · norm_num [seedGradient, seedX, Fin.castSucc_mk, Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val, map_ofNat]
    linear_combination (0)*hjp + (X^20 - 6*X^16 + 12*X^12 - 12*X^8 + 6*X^4 - 1)*h5

lemma seedGradient_weight_two (j : K) :
    seedGradient j 5 = 3*(seedU (K:=K))^2 := by
  have h5 : (5 : K[X])=0 := CharP.cast_eq_zero _ 5
  simp only [seedGradient, seedU, Matrix.cons_val, map_ofNat]
  linear_combination (-X^12 - X^8 - X^4)*h5

end CoupledFanoQuarticSeed
