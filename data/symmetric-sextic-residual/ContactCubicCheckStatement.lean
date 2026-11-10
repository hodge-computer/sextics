import Proposal.ContactCubicValues
import Proposal.ContactExactArithmetic

namespace ContactCubicData

open ContactExactArithmetic

abbrev RowCertificate (i : Fin 44) : Prop :=
  (∀ t ∈ integerPolys i, t.2.length ≤ 3) ∧
  evalScaled 3 centerDen (integerPolys i) centerNum = residualNum i ∧
  (∀ j, jacobianScaled 3 centerDen (integerPolys i) centerNum j = jacobianNum i j) ∧
  dotInt (inverseNum i) residualNum = newtonResidualNum i ∧
  (∀ j, (if i = j then ((inverseDen * centerDen ^ 2 : ℕ) : GaussianInt) else 0) -
    dotInt (inverseNum i) (fun k => jacobianNum k j) = defectNum i j) ∧
  4 * mass (centerNum i) ≤ 399 * centerDen ∧
  rowMass (inverseNum i) ≤ 2 * inverseDen ∧
  mass (newtonResidualNum i) ≤ 2 ^ 423 ∧
  rowMass (defectNum i) ≤ 2 ^ 382 ∧
  hessianMassInt 100 (integerPolys i) ≤ 2 ^ 23

end ContactCubicData
