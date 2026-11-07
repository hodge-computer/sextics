import Proposal.Assembly
import Proposal.RadialNormalization

/-! The protected pole-order-two target is equivalent to a normalized solution.
The same-denominator radial construction is supplied by the shared theorem for
arbitrary dimension, hypersurface degree, and admissible pole parameter. -/
noncomputable section
namespace CycleQ2Normalization
open MvPolynomial HodgeComputer HodgeTestbed CycleQ2Workspace CycleQ2Assembly

/-- The normalization does not narrow the original existential target. -/
theorem originalGoal_iff_normalized :
    OriginalGoal ↔ Nonempty NormalizedRationalSolution := by
  constructor
  · intro h
    change HasCertificate originalF 2 originalA at h
    obtain ⟨D, N, Q, h⟩ := h
    rw [originalF_totalDegree] at h
    obtain ⟨N', hv, hfirst, hsecond⟩ := HodgeComputer.RadialNormalization.normalize_verify (by decide) h
    refine ⟨{
      degree := D.totalDegree
      denominator := D
      numerators := N'
      quotient := Q
      denominator_ne_zero := hv.denominator_ne_zero
      denominator_homogeneous := hv.denominator_homogeneous
      numerator_homogeneous := ?_
      denominator_legal := hv.denominator_legal
      first_normal := hfirst
      second_normal := hsecond
    }⟩
    intro i
    have hn : HodgeComputer.Homogeneous (N' i) ((D.totalDegree + 7 : ℕ) : ℤ) := by
      convert hv.numerator_homogeneous i using 1 <;> omega
    simpa only [Int.toNat_natCast] using hn.isHomogeneous (by omega)
  · rintro ⟨s⟩
    exact certificate_of_normalized_solution s

end CycleQ2Normalization
