import Proposal.ArithmeticLifting
import Proposal.QuarticSeedJacobian

/-!
Closed seed instantiation of the arithmetic lifting theorem. Algebraic
closedness supplies j^2=2 in characteristic five; the explicit quartic and
its kernel-checked Jacobian then produce the generic characteristic-zero
field factor. No finite-precision lifting calculation is used as evidence
inside this theorem.
-/

noncomputable section
namespace ReflectionCoupledFano.Arithmetic
open HoldoutConstruction

theorem exists_generic_field :
    ∃ I : Ideal GenericIncidence, I.IsMaximal ∧
      Module.Finite GenericEndpoint (GenericIncidence ⧸ I) ∧
      Algebra.IsSeparable GenericEndpoint (GenericIncidence ⧸ I) ∧
      (∀ i, MvPolynomial.aeval
        (openGenericCoordinates integralEquations (1,0) I) (integralEquations i) = 0) ∧
      IsUnit (Matrix.det (fun i k => MvPolynomial.aeval
        (openGenericCoordinates integralEquations (1,0) I)
          (MvPolynomial.pderiv i (integralEquations k)))) ∧
      IsUnit (openGenericCoordinates integralEquations (1,0) I (1,0)) := by
  letI : Fact (Nat.Prime 5) := ⟨by decide⟩
  let T := AlgebraicClosure (ZMod 5)
  obtain ⟨j, hj⟩ := IsAlgClosed.exists_pow_nat_eq (2 : T) (show 0 < 2 by decide)
  exact exists_generic_field_of_seed j hj (modJacobian_det_isUnit hj)

end ReflectionCoupledFano.Arithmetic

#print axioms ReflectionCoupledFano.Arithmetic.exists_generic_field
