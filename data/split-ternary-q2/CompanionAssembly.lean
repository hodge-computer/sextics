import Proposal.ProductDivergence
import Proposal.CompanionElliptic
import Proposal.CompanionTheta
import Proposal.CompanionThetaExistence

/- Exact binding of the companion primitives to the protected split target.
Prepared with OpenAI Codex assistance for fqlx. -/
noncomputable section
namespace SplitTernaryProduct
open CrossedElliptic
local instance : Algebra ℤ K := Ring.toIntAlgebra _

lemma secondPolynomial_binding : secondPolynomial=SplitGCompanion.p := by
  simp only [secondPolynomial,SplitTernaryPhysical.rightTernary,SplitGCompanion.p]
  ring

lemma firstPolynomial_binding : firstPolynomial=SplitFCompanion.p := by
  simp only [firstPolynomial,SplitTernaryPhysical.leftTernary,SplitFCompanion.p]
  ring

lemma alpha_binding : alpha=phi SplitFCompanion.h/u^5 := by
  simp only [alpha,SplitFCompanion.h,map_mul,map_pow,phi_X,firstIndex,
    Matrix.cons_val_zero,Matrix.cons_val_one]

theorem ordinary_primitive : OrdinaryPrimitive := by
  have hv : v^3=psi SplitGCompanion.p := by
    rw [← secondPolynomial_binding,psi_q]
    exact v_cube
  obtain ⟨bf,cr,cz,he,hkill⟩ := SplitGElliptic.ordinary_scalar_primitive psi psi_injective
    v v_ne_zero hv (DY 0) (DY 1) (DY_psi_C 0) (DY_psi_C 1)
    (DY_psi_X 0) (DY_psi_X 1)
  refine ⟨bf,cr,cz,?_,hkill⟩
  simpa only [psi_X,secondIndex,Matrix.cons_val_zero,Matrix.cons_val_one,beta] using he

theorem theta_primitive : ThetaPrimitive := by
  have hu : u^3=phi SplitFCompanion.p := by
    rw [← firstPolynomial_binding,phi_p]
    exact u_cube
  obtain ⟨bf,cx,ca,he,hkill⟩ := SplitFElliptic.theta_scalar_primitive_complete phi phi_injective
    u u_ne_zero hu (DX 0) (DX 1) (DX_phi_C 0) (DX_phi_C 1)
    (DX_phi_X 0) (DX_phi_X 1)
  refine ⟨bf,cx,ca,?_,hkill⟩
  rw [← alpha_binding] at he
  exact he

theorem physical_certificate :
    HodgeComputer.HasCertificate SplitTernaryPhysical.physicalF SplitTernaryPhysical.physicalA 2 :=
  certificate_of_companion_primitives ordinary_primitive theta_primitive

#print axioms ordinary_primitive
#print axioms theta_primitive
#print axioms physical_certificate
end SplitTernaryProduct
