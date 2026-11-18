import Proposal.JacobianClearing

/-! The polynomial source predicted by the cubic-to-Jacobian calculation.
The derivative identity and its residue primitive are proved here. Identifying
this source with the original sextic residue still requires the covariant
transport, including its exact correction, in Lean. The normalization follows
the earlier exact algebraic research packet, with classical cubic invariant
credit to Tom Fisher and the sources cited there. Prepared with OpenAI Codex
assistance for hodgepodgeconjecture. -/
noncomputable section
namespace CycleJacobianSource
open HoldoutConstruction CycleJacobianHypersurface CycleJacobianEmbedding CycleJacobianResidue
open Polynomial
local notation "v" => (MvPolynomial.X : Fin 6 → Ambient)
/-- 36864 times the polynomial source, in coordinate order Y,T,c1,c2,R,X. -/
def sourceNumerator : Ambient :=
  32*v 4^2*v 1*v 2^2*v 3^3*v 5-
  3456*(v 4+v 1)*(v 4+v 2^6*v 1)^2*(v 4+v 3^6*v 1)^2-
  32*v 4^2*v 1*(2*v 2^3*v 3^3*(v 4+v 1)*(v 4+v 3^6*v 1)+v 3^3*(v 4+v 2^6*v 1)^2)-
  48*v 4^2*v 1*v 2^2*v 3^2*(v 4+v 2^6*v 1)*(v 4+v 3^6*v 1)
def source : Ambient := MvPolynomial.C (1/36864 : ℂ)*sourceNumerator
/-- The auxiliary parameter is only differentiated and then set to one. -/
def alphaModel : Polynomial Ambient :=
  CycleJacobian.equation (C (v 2)) (C (v 3)) X (C (v 4)) (C (v 1)) (C (v 5)) (C (v 0))
lemma source_scale : 36864*source=sourceNumerator := by
  have h : (36864 : Ambient)*MvPolynomial.C (1/36864 : ℂ)=1 := by
    calc
      _ = MvPolynomial.C ((36864 : ℂ)*(1/36864)) := by simp only [map_mul,map_ofNat]
      _ = 1 := by norm_num
  rw [source,← mul_assoc,h,one_mul]
lemma alpha_derivative : alphaModel.derivative.eval 1= -v 4*sourceNumerator := by
  simp [alphaModel,CycleJacobian.equation,CycleJacobian.a8,CycleJacobian.b256,
    Polynomial.derivative_mul,Polynomial.derivative_pow,sourceNumerator]
  ring
lemma alpha_source_identity : alphaModel.derivative.eval 1= -36864*v 4*source := by
  rw [alpha_derivative,← source_scale]
  ring
/-- The proposed Jacobian source has a rational primitive with no remaining assumptions. -/
theorem source_residue_solution :
    ∃ w : Fin 5 → TargetField,
      residueDivergence tangent (residueMap (MvPolynomial.pderiv 0 hypersurface)) w=
        -(residueMap (MvPolynomial.pderiv 0 source)/residueMap (MvPolynomial.pderiv 0 hypersurface)-
          residueMap source*residueMap (MvPolynomial.pderiv 0 (MvPolynomial.pderiv 0 hypersurface))/
            (residueMap (MvPolynomial.pderiv 0 hypersurface))^2) :=
  target_residue_solution source
#print axioms alpha_source_identity
#print axioms source_residue_solution
end CycleJacobianSource
