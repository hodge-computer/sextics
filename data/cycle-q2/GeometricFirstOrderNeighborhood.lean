import Proposal.GeometricIncidenceFirstOrder
import Proposal.GeometricIncidenceSmoothNeighborhood
import Mathlib.RingTheory.DualNumber

/-!
# The actual first-order parameter point lies in the retained neighborhood

The spectrum of the dual numbers over a field has one point: every prime
is the epsilon ideal. The original pointed first-order incidence map
therefore has its entire topological image at the retained seed point.
It factors through the previously constructed seedSmoothBase by the
actual open-immersion lifting property.

Source-only draft: no elaboration or kernel replay has been run.
Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md for
attribution of the geometric route and the protected certificate gap.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2FirstOrderNeighborhood

open scoped DualNumber
open CategoryTheory AlgebraicGeometry
open CycleQ2IncidenceEtaleParameter CycleQ2IncidenceSeedFiberCover
  CycleQ2IncidenceSmoothNeighborhood CycleQ2IncidenceFirstOrder

theorem dualNumber_prime_ideal {k : Type} [Field k]
    (p : PrimeSpectrum k[ε]) : p.asIdeal = Ideal.span {ε} := by
  have heps : (ε : k[ε]) ∈ p.asIdeal :=
    (p.isPrime.mem_or_mem_of_mul_eq_zero DualNumber.eps_mul_eps).elim id id
  rcases DualNumber.ideal_trichotomy p.asIdeal with h | h | h
  · rw [h] at heps
    have hz : (ε : k[ε]) = 0 := by
      simpa only [Submodule.mem_bot] using heps
    have hs := congrArg TrivSqZeroExt.snd hz
    simp only [DualNumber.snd_eps, TrivSqZeroExt.snd_zero] at hs
    exact (one_ne_zero hs).elim
  · exact h
  · exact (p.isPrime.ne_top h).elim

theorem firstOrderPoint_eq_closedPoint
    (x : Spec (CommRingCat.of (DualNumber ℂ))) :
    x = firstOrderClosedPoint (default : Spec (CommRingCat.of ℂ)) := by
  apply PrimeSpectrum.ext
  rw [dualNumber_prime_ideal, dualNumber_prime_ideal]

theorem firstOrderParameterPoint_apply
    (x : Spec (CommRingCat.of (DualNumber ℂ))) :
    firstOrderParameterPoint x = seedBasePoint := by
  rw [firstOrderPoint_eq_closedPoint x]
  change (firstOrderClosedPoint ≫ firstOrderParameterPoint)
      (default : Spec (CommRingCat.of ℂ)) =
    seedPointMorphism (default : Spec (CommRingCat.of ℂ))
  rw [firstOrderParameterPoint_at_seed]

def firstOrderToSeedBase :
    Spec (CommRingCat.of (DualNumber ℂ)) ⟶ seedSmoothBase.toScheme :=
  IsOpenImmersion.lift seedSmoothBase.ι firstOrderParameterPoint (by
    rintro x ⟨a, rfl⟩
    refine ⟨⟨firstOrderParameterPoint a, ?_⟩, rfl⟩
    rw [firstOrderParameterPoint_apply]
    exact seed_mem_seedSmoothBase)

theorem firstOrderToSeedBase_fac :
    firstOrderToSeedBase ≫ seedSmoothBase.ι = firstOrderParameterPoint :=
  IsOpenImmersion.lift_fac _ _ _

end CycleQ2FirstOrderNeighborhood

end

#print axioms CycleQ2FirstOrderNeighborhood.dualNumber_prime_ideal
#print axioms CycleQ2FirstOrderNeighborhood.firstOrderParameterPoint_apply
#print axioms CycleQ2FirstOrderNeighborhood.firstOrderToSeedBase_fac
