import HodgeTarget
import Proposal.Certificate

/-!
Cyclic triple-cover certificate. The free line is due to rbajaj5; the
incidence, integration, trace and clearing constructions build on fqlx,
HeadOfNaps, Benjamin E. Diamond, and the Lean/mathlib contributors.
Prepared with OpenAI Codex assistance for benediamond.
-/
noncomputable section
namespace CyclicTriple

@[simp] theorem coordinate_zero : coordinateOrder 0 = 3 := rfl
@[simp] theorem coordinate_one : coordinateOrder 1 = 4 := rfl
@[simp] theorem coordinate_two : coordinateOrder 2 = 0 := rfl
@[simp] theorem coordinate_three : coordinateOrder 3 = 1 := rfl
@[simp] theorem coordinate_four : coordinateOrder 4 = 5 := rfl
@[simp] theorem coordinate_five : coordinateOrder 5 = 2 := rfl

theorem protected_F : HodgeSubmission.F =
    MvPolynomial.rename coordinateOrder (hypersurface coupling 6 3) := by
  have hc : (MvPolynomial.C (5/7 : ℂ) : HodgeComputer.Poly) =
      5*MvPolynomial.C (1/7 : ℂ) := by
    rw [show (5/7 : ℂ) = 5*(1/7) by ring, map_mul, map_ofNat]
  simp only [hypersurface, coupling, map_add, map_mul, map_pow, MvPolynomial.rename_C,
    MvPolynomial.rename_X, hc, map_ofNat, coordinate_zero, coordinate_one,
    coordinate_two, coordinate_three, coordinate_four, coordinate_five]
  change HodgeSubmission.F = _
  simp only [HodgeSubmission.F]
  ring

theorem protected_A : HodgeSubmission.A = MvPolynomial.rename coordinateOrder physicalSource := by
  simp only [physicalSource, map_mul, map_pow, MvPolynomial.rename_X, HodgeSubmission.A,
    coordinate_zero, coordinate_two, coordinate_five]
end CyclicTriple

theorem Submission.certificate :
    HodgeComputer.HasCertificate HodgeSubmission.F HodgeSubmission.A HodgeSubmission.q := by
  rw [CyclicTriple.protected_F, CyclicTriple.protected_A]
  exact CyclicTriple.certificate_rename CyclicTriple.coordinateOrder _ _ 1
    CyclicTriple.physical_certificate

#print axioms Submission.certificate
