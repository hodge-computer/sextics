import Proposal.GoodFiberSources
import HodgeComputer.Constructions.FiniteAlgebra.CheckedPolynomialListDegree

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace HoldoutQ2.NewSpecialization

theorem sourceMinor_gradient (i : Fin 10) (j : Fin 4) :
    sourceMinor i (Fin.castAdd 6 j) =
      HodgeComputer.CubicSurfaces.LineContact.gradientCoefficients (2 : ℚ) 2 1 1 i j := by
  have hm : (Matrix.of fun (i : Fin 10) (j : Fin 4) => sourceMinor i (Fin.castAdd 6 j)) =
      HodgeComputer.CubicSurfaces.LineContact.gradientCoefficients (2 : ℚ) 2 1 1 := by decide +kernel
  exact congrFun (congrFun hm i) j

def sourceCoefficientData : Fin 10 → List ℚ :=
  ![source0Data, source1Data, source2Data, source3Data, source4Data,
    source5Data, source6Data, source7Data, source8Data, source9Data]

theorem sourcePoly_encode (i : Fin 10) :
    sourcePoly i = CheckedPolynomialLists.encode (sourceCoefficientData i) := by
  fin_cases i <;> rfl

theorem sourceMinor_coefficient (i : Fin 10) (j : Fin 6) :
    sourceMinor i (Fin.natAdd 4 j) = (sourcePoly i).coeff j.val := by
  rw [sourcePoly_encode, CheckedPolynomialLists.coeff_encode]
  revert i j
  decide +kernel

end HoldoutQ2.NewSpecialization
