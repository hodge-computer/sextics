import Proposal.PhysicalJacobianMap
import HodgeComputer.Constructions.ResidueTransport.Density
import Proposal.PhysicalClearing

/-! Assembling the rational residue primitive on the fixed sextic. Its three
terms are the pulled-back Jacobian primitive, the moving-map correction, and
the normal-chart correction. The final clearing theorem is the shared
construction credited to fqlx and the Hodge Computer collaborators.
Original cycle-three construction prepared with OpenAI Codex assistance.
Adapted to mixed-biweight for fqlx with OpenAI Codex assistance. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace CyclePhysicalPrimitive
open HoldoutConstruction CyclePhysical CyclePhysicalCoordinates
open CyclePhysicalNormalTransport CyclePhysicalCubicTangent
open CyclePhysicalCubicJets CyclePhysicalCubicVolume
open CyclePhysicalJacobianCoordinates CyclePhysicalJacobianMap
open CycleCubicFieldDifferential.Physical
local instance : Algebra ℤ FunctionField := Ring.toIntAlgebra _
open scoped BigOperators

lemma divergence_sub {K ι : Type*} [Field K] [Fintype ι]
    (D : ι → Derivation ℤ K K) (g : K) (v w : ι → K) :
    residueDivergence D g (v-w)=residueDivergence D g v-residueDivergence D g w := by
  simp only [residueDivergence,fieldDivergence,Pi.sub_apply,map_sub,sub_mul,
    Finset.sum_sub_distrib]
  ring

theorem physical_residue_solution : ∃ w : Fin 5 → FunctionField,
    residueDivergence tangent (gradient 0) w=
      -(residueMap (MvPolynomial.pderiv 0 source)/gradient 0-
        residueMap source*hessian 0 0/(gradient 0)^2) := by
  obtain ⟨w,hw⟩ := mapped_source_solution
  let pulled : Fin 5 → FunctionField := fun i =>
    (gradient 0/(2*targetY))*(matrix.det*(inverse.mulVec w) i)
  have hp : residueDivergence tangent (gradient 0) pulled=
      -ratio^3*(aDot*xi+bDot)/(2*eta^2) := by
    have h := CycleResidueTransport.piola_pullback tangent coordinateDerivation matrix inverse
      matrix_inverse inverse_matrix matrix_det_nonzero coordinateDerivation_apply matrix_mixed
      (gradient 0) (2*targetY) normal_ne_zero
      (mul_ne_zero (by norm_num) targetY_nonzero) w
    rw [hw] at h
    change residueDivergence tangent (gradient 0) pulled=_ at h
    rw [h]
    have hd : (gradient 0/(2*targetY))*matrix.det= -144*radial*ratio^3 := by
      rw [div_mul_eq_mul_div,density_multiplier]
    rw [hd]
    have hr := radial_ne_zero
    have he := CyclePhysicalCubicJets.eta_nonzero
    field_simp
    ring
  let correction : Fin 5 → FunctionField := fun i =>
    (xiDot/(2*eta)/3)*volumeVector i
  refine ⟨pulled+correction-correctionVector,?_⟩
  rw [divergence_sub,residueDivergence_add,hp]
  have hc := CyclePhysicalCubicVolume.correction_divergence (xiDot/(2*eta))
  change residueDivergence tangent (gradient 0) correction=_ at hc
  rw [hc,physical_source_transport]
  linear_combination ratio^3*source_transport

theorem certificate : HodgeComputer.HasCertificate sextic source 1 := by
  obtain ⟨w,hw⟩ := physical_residue_solution
  exact certificate_of_residue_solution w hw

end CyclePhysicalPrimitive
#print axioms CyclePhysicalPrimitive.certificate
