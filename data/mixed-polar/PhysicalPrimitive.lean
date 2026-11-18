import Proposal.PhysicalJacobianMap
import Proposal.BalancedNormal
import HodgeComputer.Constructions.ResidueTransport.Density
import HodgeComputer.Constructions.HoldoutCover.FiniteTrace

/-! Assemble the exact balanced-source primitive, descend its finite
quadratic coefficient extension, and apply the shared legal clearing and
homogeneous-certificate theorem. The construction follows the accepted
Jacobian primitive architecture of fqlx and hodgepodgeconjecture, including
both moving-map and normal-chart corrections. Prepared with Codex assistance. -/
noncomputable section
namespace MixedPolarPhysicalPrimitive
open HoldoutConstruction MixedPolarPhysical MixedPolarPhysicalCoordinates
open MixedPolarPhysicalShear MixedPolarPhysicalTangent MixedPolarPhysicalCubicJets
open MixedPolarExtendedVolume MixedPolarPhysicalJacobianCoordinates MixedPolarPhysicalJacobianMap
open scoped BigOperators

def physicalNormalSource : FunctionField :=
  residueMap (MvPolynomial.pderiv 0 source)/gradient 0-
    residueMap source*hessian 0 0/(gradient 0)^2

theorem extension_residue_solution :
    ∃ w : Fin 5 → Extension,
      residueDivergence liftedTangent (ι (gradient 0)) w=ι (-physicalNormalSource) := by
  obtain ⟨w,hw⟩ := mapped_source_solution
  let pulled : Fin 5 → Extension := fun i =>
    (ι (gradient 0)/(2*targetY))*(matrix.det*(inverse.mulVec w) i)
  have hp : residueDivergence liftedTangent (ι (gradient 0)) pulled=
      -ι MixedPolarPhysicalNormalTransport.sourceFactor*(aDot*xi+bDot)/(2*eta^2) := by
    have hn : ι (gradient 0)≠0 := (map_ne_zero ι).2 MixedPolarPhysical.normal_ne_zero
    have h := CycleResidueTransport.piola_pullback liftedTangent coordinateDerivation
      matrix inverse matrix_inverse inverse_matrix matrix_det_nonzero
      coordinateDerivation_apply matrix_mixed (ι (gradient 0)) (2*targetY)
      hn (mul_ne_zero (by norm_num) targetY_nonzero) w
    rw [hw] at h
    change residueDivergence liftedTangent (ι (gradient 0)) pulled=_ at h
    rw [h]
    have hd : (ι (gradient 0)/(2*targetY))*matrix.det=
        -144*ι radial*(ι ratio)^3 := by
      rw [div_mul_eq_mul_div,density_multiplier]
    rw [hd]
    have hr : ι radial≠0 := (map_ne_zero ι).2 radial_ne_zero
    have he := MixedPolarPhysicalCubicJets.eta_nonzero
    simp only [MixedPolarPhysicalNormalTransport.sourceFactor,map_mul,map_pow]
    field_simp
    ring
  let moving : Fin 5 → Extension := fun i => (xiDot/(2*eta)/3)*balancedVector i
  let correction : Fin 5 → Extension := fun i =>
    ι (MixedPolarPhysicalNormalTransport.correctionVector i)
  have hc : residueDivergence liftedTangent (ι (gradient 0)) correction=
      ι (residueDivergence MixedPolarPhysical.tangent (gradient 0)
        MixedPolarPhysicalNormalTransport.correctionVector) :=
    residueDivergence_map ι MixedPolarPhysical.tangent liftedTangent lifted_on_base
      (gradient 0) MixedPolarPhysicalNormalTransport.correctionVector
  have hnormal : ι physicalNormalSource=
      ι MixedPolarPhysicalNormalTransport.sourceFactor*
        (ι MixedPolarPhysicalNormalTransport.cubicNormalJet/normal)+
          residueDivergence liftedTangent (ι (gradient 0)) correction := by
    rw [hc,normal_identity]
    have h := congrArg ι
      (MixedPolarPhysicalNormalTransport.physical_source_transport cubic_normal_ne_zero)
    simpa only [physicalNormalSource,map_sub,map_div₀,map_mul,map_pow,map_add,
      mul_div_assoc] using h
  have hm : residueDivergence liftedTangent (ι (gradient 0)) moving=
      ι MixedPolarPhysicalNormalTransport.sourceFactor*normal/3*
        extendedDerivative (xiDot/(2*eta)) :=
    MixedPolarExtendedVolume.correction_divergence (xiDot/(2*eta))
  have hj : ι MixedPolarPhysicalNormalTransport.cubicNormalJet/normal=
      (aDot*xi+bDot)/(2*eta^2)-(normal/3)*extendedDerivative (xiDot/(2*eta)) := by
    simpa only [normal_identity] using MixedPolarPhysicalCubicJets.source_transport
  obtain ⟨v,hv⟩ := MixedPolarBalanced.residue_solution_of_balanced_transport
    liftedTangent extendedDerivative (ι (gradient 0)) (ι physicalNormalSource)
    (ι MixedPolarPhysicalNormalTransport.sourceFactor) normal eta xi aDot bDot
    (ι MixedPolarPhysicalNormalTransport.cubicNormalJet) xiDot
    pulled moving correction hnormal hp hm hj
  exact ⟨v,by simpa only [map_neg] using hv⟩

theorem physical_residue_solution :
    ∃ w : Fin 5 → FunctionField,
      residueDivergence MixedPolarPhysical.tangent (gradient 0) w= -physicalNormalSource :=
  residue_solution_descends_finite MixedPolarPhysical.tangent liftedTangent
    lifted_on_base (gradient 0) (-physicalNormalSource) extension_residue_solution

theorem certificate : HodgeComputer.HasCertificate sextic 1 source := by
  obtain ⟨w,hw⟩ := physical_residue_solution
  exact certificate_of_residue_solution w hw

end MixedPolarPhysicalPrimitive
#print axioms MixedPolarPhysicalPrimitive.certificate
