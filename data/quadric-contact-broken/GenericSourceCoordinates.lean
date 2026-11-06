import Proposal.GenericSourceReductions
import HodgeComputer.Constructions.FiniteAlgebra.CheckedPolynomialListDegree
import Mathlib.Tactic.FinCases

noncomputable section
namespace GenericSpecialization
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open CheckedPolynomialLists

def sourcePolyFamily : Fin 8 → Polynomial ℚ :=
  ![source_0, source_1, source_2, source_3, source_4, source_5, source_6, source_7]

def sourceDataFamily : Fin 8 → List ℚ :=
  ![source_0_data, source_1_data, source_2_data, source_3_data,
    source_4_data, source_5_data, source_6_data, source_7_data]

lemma sourcePolyFamily_encode (i : Fin 8) :
    sourcePolyFamily i = encode (sourceDataFamily i) := by
  fin_cases i
  · exact (encode_source_0_data).symm
  · exact (encode_source_1_data).symm
  · exact (encode_source_2_data).symm
  · exact (encode_source_3_data).symm
  · exact (encode_source_4_data).symm
  · exact (encode_source_5_data).symm
  · exact (encode_source_6_data).symm
  · exact (encode_source_7_data).symm


lemma sourceDataFamily_length : ∀ i, (sourceDataFamily i).length = 27 := by
  decide +kernel

theorem sourcePolyFamily_natDegree (i : Fin 8) : (sourcePolyFamily i).natDegree < 27 := by
  rw [sourcePolyFamily_encode]
  apply Nat.lt_succ_of_le
  exact natDegree_encode_le _ 26 (by rw [sourceDataFamily_length])

lemma sourceMinor_data (i j : Fin 8) :
    sourceMinor i j = (sourceDataFamily i).getD j.val 0 := by
  fin_cases i <;> fin_cases j <;> decide +kernel

theorem sourceMinor_coefficient (i j : Fin 8) :
    sourceMinor i j = (sourcePolyFamily i).coeff j.val := by
  rw [sourcePolyFamily_encode, coeff_encode]
  exact sourceMinor_data i j

end GenericSpecialization
