import HodgeComputer.CoordinateChanges

/-! The coordinate permutation for the cyclic-triple application. -/
noncomputable section
namespace CyclicTriple

def coordinateOrder : Fin 6 ≃ Fin 6 where
  toFun := ![3,4,0,1,5,2]
  invFun := ![2,3,5,0,1,4]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

end CyclicTriple
