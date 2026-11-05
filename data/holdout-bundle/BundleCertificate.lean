import Proposal.BundleQuotientPrimitive
import Proposal.BundlePhysicalMap
import Proposal.BundleAssembly

/-!
Assembly of the complementary diagonal-quotient certificate for the
missing summand, followed by the unchanged two-summand holdout bundle.
There are no remaining geometric or primitive hypotheses in the final
existential statements. The coefficient field and conic are selected
from the proved finite incidence construction.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace HoldoutBundle
open HoldoutConstruction

local instance certificateIntAlgebra : Algebra ℤ QuotientField := Ring.toIntAlgebra _

private theorem fraction_source_identity {L : Type*} [Field L]
    (a b c g : L) (hg : g ≠ 0) :
    (a*g-b*c)/g^2 + -(a/g-b*c/g^2) = 0 := by
  field_simp [hg]
  <;> ring

theorem quotient_density_residue_solution :
    ∃ w : Fin 4 → QuotientField,
      quotientResidueSource + residueDivergence quotientTangent quotientNormal w = 0 := by
  obtain ⟨w, hw⟩ := quotient_polynomial_residue_solution quotientDensity
  refine ⟨w, ?_⟩
  unfold quotientResidueSource quotientNormal
  rw [hw]
  exact fraction_source_identity _ _ _ _ quotient_normal_ne_zero

theorem star_certificate : HodgeComputer.HasCertificate holdoutSextic Astar 1 := by
  obtain ⟨w, hw⟩ := quotient_density_residue_solution
  exact certificate_of_quotient_residue physicalDiagonalFieldMap w hw

theorem bundle_certificate : HodgeComputer.HasCertificate holdoutSextic Abundle 1 :=
  bundle_certificate_of_star star_certificate

end HoldoutBundle

#print axioms HoldoutBundle.star_certificate
#print axioms HoldoutBundle.bundle_certificate
