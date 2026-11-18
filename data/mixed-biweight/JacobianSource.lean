import Proposal.JacobianResidue

/-! The exact polynomial alpha-source for the mixed-biweight Jacobian.
Its derivative identity and rational residue primitive are proved here;
PhysicalCubicJets and PhysicalPrimitive perform its physical transport.
Classical cubic invariant theory is credited to its authors, including Tom Fisher.
The accepted cyclic construction supplies the architecture; adapted by fqlx
with OpenAI Codex assistance. -/
noncomputable section
namespace CycleJacobianSource
open HoldoutConstruction CycleJacobianHypersurface CycleJacobianEmbedding CycleJacobianResidue
open Polynomial
local notation "v" => (MvPolynomial.X : Fin 6 → Ambient)
/-- Numerator of the exact alpha-source, in Y,T,c1,c2,R,X order. -/
def sourceNumerator : Ambient :=
  -(v 4+v 1)*(v 4+v 3^6*v 1)*
    (54*(v 4+v 2^6*v 1)^2*(v 4+v 3^6*v 1)+v 2^3*v 3^3*v 4^2*v 1)
def source : Ambient := MvPolynomial.C (1/576 : ℂ)*sourceNumerator
/-- The auxiliary parameter is differentiated before evaluation at one. -/
def alphaModel : Polynomial Ambient :=
  CycleJacobian.equation (C (v 2)) (C (v 3)) X (C (v 4)) (C (v 1)) (C (v 5)) (C (v 0))
lemma source_scale : 576*source=sourceNumerator := by
  have h : (576 : Ambient)*MvPolynomial.C (1/576 : ℂ)=1 := by
    calc
      _ = MvPolynomial.C ((576 : ℂ)*(1/576)) := by simp only [map_mul,map_ofNat]
      _ = 1 := by norm_num
  rw [source,← mul_assoc,h,one_mul]
lemma alpha_derivative : alphaModel.derivative.eval 1= -1458*v 4*sourceNumerator := by
  simp [alphaModel,CycleJacobian.equation,CycleJacobian.a8,CycleJacobian.b256,
    Polynomial.derivative_mul,Polynomial.derivative_pow,sourceNumerator]
  ring
lemma alpha_source_identity : alphaModel.derivative.eval 1= -839808*v 4*source := by
  rw [alpha_derivative,← source_scale]
  ring
/-- Every polynomial source, in particular this exact source, has a primitive. -/
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
