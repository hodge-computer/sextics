import Proposal.BundlePhysical
import Proposal.BundleCompatibility

/-! The concrete independently constructed diagonal field map, with every
coordinate and coefficient value bound to the protected physical sextic. -/

noncomputable section

namespace HoldoutBundle

def physicalDiagonalFieldMap : DiagonalFieldMap where
  baseMap := basePhysicalFieldMap
  fieldMap := quotientPhysicalFieldMap
  complex := basePhysicalFieldMap_complex
  lambda := basePhysicalFieldMap_lambda
  coefficient := quotientPhysicalFieldMap_base
  root := quotientPhysicalFieldMap_coordinate 0
  parameter := by
    intro j
    rw [quotientPhysicalFieldMap_coordinate]
    simpa only [physicalModelCoordinates, physicalQuotientTail, Matrix.cons_val_succ] using
      (five_tuple_castSucc (physicalY 1) (physicalY 2) physicalP physicalQ physicalLambda j).symm

end HoldoutBundle

#print axioms HoldoutBundle.physicalDiagonalFieldMap
