import HodgeTarget
import Proposal.CoupledDomain

/-!
Exact source binding. The definitions of F, A, and q come only from the
protected HodgeTarget generated from reflection-coupled-fano/instance.rec.
-/

noncomputable section
namespace ReflectionCoupledFano

theorem protected_F : HodgeSubmission.F = hypersurface (5/7 : ℂ) 6 2 := by
  have hc : (MvPolynomial.C (5/7 : ℂ) : HodgeComputer.Poly) =
      5 * MvPolynomial.C (1/7 : ℂ) := by
    rw [show (5/7 : ℂ) = 5 * (1/7) by ring, map_mul, map_ofNat]
  simp only [HodgeSubmission.F, hypersurface, hc]
  ring

theorem protected_A : HodgeSubmission.A = physicalSource (R := ℂ) := by
  rfl

theorem protected_q : HodgeSubmission.q = 1 := rfl

end ReflectionCoupledFano

#print axioms ReflectionCoupledFano.protected_F
