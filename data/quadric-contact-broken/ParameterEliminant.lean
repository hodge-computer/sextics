import Proposal.ParameterSpecialization
import Proposal.GenericMonicPolynomial
import Proposal.GenericSpecialization
import HodgeComputer.Constructions.FiniteAlgebra.AdjoinRootUnits

namespace ParameterEliminant
open Polynomial
open ParameterSpecialization

noncomputable def P : Polynomial Coefficients :=
  GenericMonicPolynomial.monicPolynomial p q s k u v

theorem P_monic : P.Monic :=
  GenericMonicPolynomial.monicPolynomial_monic p q s k u v isUnit_leadingCoefficient

theorem P_natDegree : P.natDegree = 27 :=
  GenericMonicPolynomial.monicPolynomial_natDegree p q s k u v isUnit_leadingCoefficient

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem P_specialize : P.map ParameterSpecialization.specialize = GenericSpecialization.P := by
  unfold P GenericMonicPolynomial.monicPolynomial
  simp only [Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C]
  simp only [map_mul ParameterSpecialization.specialize,
    GenericMonicPolynomial.coefficient_map ParameterSpecialization.specialize]
  rw [FiniteAlgebraInverse.map_ringInverse _ _ isUnit_leadingCoefficient]
  simp only [map_mul ParameterSpecialization.specialize, map_pow ParameterSpecialization.specialize, specialize_p, specialize_q, specialize_s,
    specialize_k, specialize_u, specialize_v, Ring.inverse_eq_inv]
  apply Polynomial.funext
  intro z
  simp only [GenericSpecialization.P, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_finsetSum]
  norm_num [GenericMonicPolynomial.coefficient, List.getD, GenericMonicPolynomial.coefficient0, GenericMonicPolynomial.coefficient1, GenericMonicPolynomial.coefficient2, GenericMonicPolynomial.coefficient3, GenericMonicPolynomial.coefficient4, GenericMonicPolynomial.coefficient5, GenericMonicPolynomial.coefficient6, GenericMonicPolynomial.coefficient7, GenericMonicPolynomial.coefficient8, GenericMonicPolynomial.coefficient9, GenericMonicPolynomial.coefficient10, GenericMonicPolynomial.coefficient11, GenericMonicPolynomial.coefficient12, GenericMonicPolynomial.coefficient13, GenericMonicPolynomial.coefficient14, GenericMonicPolynomial.coefficient15, GenericMonicPolynomial.coefficient16, GenericMonicPolynomial.coefficient17, GenericMonicPolynomial.coefficient18, GenericMonicPolynomial.coefficient19, GenericMonicPolynomial.coefficient20, GenericMonicPolynomial.coefficient21, GenericMonicPolynomial.coefficient22, GenericMonicPolynomial.coefficient23, GenericMonicPolynomial.coefficient24, GenericMonicPolynomial.coefficient25, GenericMonicPolynomial.coefficient26, GenericLineChart.eliminantCoeff0, GenericLineChart.eliminantCoeff1, GenericLineChart.eliminantCoeff2, GenericLineChart.eliminantCoeff3, GenericLineChart.eliminantCoeff4, GenericLineChart.eliminantCoeff5, GenericLineChart.eliminantCoeff6, GenericLineChart.eliminantCoeff7, GenericLineChart.eliminantCoeff8, GenericLineChart.eliminantCoeff9, GenericLineChart.eliminantCoeff10, GenericLineChart.eliminantCoeff11, GenericLineChart.eliminantCoeff12, GenericLineChart.eliminantCoeff13, GenericLineChart.eliminantCoeff14, GenericLineChart.eliminantCoeff15, GenericLineChart.eliminantCoeff16, GenericLineChart.eliminantCoeff17, GenericLineChart.eliminantCoeff18, GenericLineChart.eliminantCoeff19, GenericLineChart.eliminantCoeff20, GenericLineChart.eliminantCoeff21, GenericLineChart.eliminantCoeff22, GenericLineChart.eliminantCoeff23, GenericLineChart.eliminantCoeff24, GenericLineChart.eliminantCoeff25, GenericLineChart.eliminantCoeff26, Fin.sum_univ_succ, GenericSpecialization.P]
  ring

abbrev E := AdjoinRoot P
noncomputable def root : E := AdjoinRoot.root P

noncomputable def toSpecial : E →+* AdjoinRoot GenericSpecialization.P :=
  AdjoinRoot.map ParameterSpecialization.specialize P GenericSpecialization.P
    (by simpa only [P_specialize] using dvd_refl GenericSpecialization.P)

@[simp] theorem toSpecial_root :
    toSpecial root = AdjoinRoot.root GenericSpecialization.P := by
  simp [toSpecial, root]

@[simp] theorem toSpecial_algebraMap (c : Coefficients) :
    toSpecial (algebraMap Coefficients E c) =
      algebraMap ℚ (AdjoinRoot GenericSpecialization.P) (ParameterSpecialization.specialize c) := by
  simp [toSpecial, AdjoinRoot.algebraMap_eq]

theorem isUnit_of_special_isUnit (x : E) (h : IsUnit (toSpecial x)) : IsUnit x := by
  exact AdjoinRootSpecialization.isUnit_of_map_isUnit point P P_monic
    GenericSpecialization.P P_specialize.symm _ x h

end ParameterEliminant
