import Proposal.GeometricIncidenceSeedFiber
import Proposal.GeometricSeedSurfaceGradient

/-!
# Transport of a polynomial prime over the original seed

Status: source-only proof draft. No elaboration or kernel replay was run.

A prime containing the source equations and the seed coefficient kernel
induces a complex polynomial prime by contraction along the canonical
complex coefficient inclusion. Modulo the original prime, specializing
coefficients and then including them again is the identity. This follows
from polynomial ring-homomorphism extensionality, without a polynomial
kernel calculation or a new geometric assumption.

The original seed coordinate cover therefore supplies a weight-one
coordinate outside every relevant source prime over the seed. The
coefficient-kernel condition still has to be obtained from the actual
surface structure morphism when this lemma is used on scheme points.

The geometric strategy is due to Ben Diamond and the collaborators cited
in solution.md. Prepared for fqlx with OpenAI ChatGPT assistance.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2IncidenceSeedPrimeTransport

open MvPolynomial
open CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations
  CycleQ2IncidenceEtaleParameter CycleQ2GeometricIncidenceProj
  CycleQ2IncidenceSeedFiber

/-- The original complex coefficient inclusion, fixing all geometric variables. -/
def coefficientLift : Poly ℂ →+* Poly ParameterAlgebra :=
  MvPolynomial.map (algebraMap ℂ ParameterAlgebra)

def specializedPrime (P : Ideal (Poly ParameterAlgebra)) : Ideal (Poly ℂ) :=
  P.comap coefficientLift

instance specializedPrime_isPrime (P : Ideal (Poly ParameterAlgebra)) [P.IsPrime] :
    (specializedPrime P).IsPrime :=
  Ideal.IsPrime.comap coefficientLift

@[simp] theorem coordinate_mem_specializedPrime_iff
    (P : Ideal (Poly ParameterAlgebra)) (j : Fin 5) :
    (X j : Poly ℂ) ∈ specializedPrime P ↔ (X j : Poly ParameterAlgebra) ∈ P := by
  change MvPolynomial.map (algebraMap ℂ ParameterAlgebra) (X j) ∈ P ↔ _
  rw [MvPolynomial.map_X]

/-- Specialization followed by coefficient inclusion is the identity
after quotienting by any ideal containing the actual seed coefficient kernel. -/
theorem quotient_specialization (P : Ideal (Poly ParameterAlgebra))
    (hcoeff : ∀ a : ParameterAlgebra, seedMap a = 0 → C a ∈ P)
    (p : Poly ParameterAlgebra) :
    Ideal.Quotient.mk P (coefficientLift (MvPolynomial.map seedMap p)) =
      Ideal.Quotient.mk P p := by
  have h : (Ideal.Quotient.mk P).comp
      (coefficientLift.comp (MvPolynomial.map seedMap)) = Ideal.Quotient.mk P := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp only [RingHom.comp_apply, coefficientLift, MvPolynomial.map_C]
      apply Ideal.Quotient.eq.mpr
      have hz : seedMap (algebraMap ℂ ParameterAlgebra (seedMap a) - a) = 0 := by
        rw [map_sub, seedMap_complex, sub_self]
      simpa only [map_sub] using
        hcoeff (algebraMap ℂ ParameterAlgebra (seedMap a) - a) hz
    · intro j
      simp only [RingHom.comp_apply, coefficientLift, MvPolynomial.map_X]
  exact RingHom.congr_fun h p

theorem specialization_mem (P : Ideal (Poly ParameterAlgebra))
    (hcoeff : ∀ a : ParameterAlgebra, seedMap a = 0 → C a ∈ P)
    (p : Poly ParameterAlgebra) (hp : p ∈ P) :
    MvPolynomial.map seedMap p ∈ specializedPrime P := by
  change coefficientLift (MvPolynomial.map seedMap p) ∈ P
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  rw [quotient_specialization P hcoeff]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr hp

/-- Every relevant prime over the original coefficient seed misses a
weight-one coordinate. The hypotheses are the exact source equations,
coefficient-fiber condition, and relevance condition. -/
theorem seed_fiber_prime_coordinate_cover
    (P : Ideal (Poly ParameterAlgebra)) [P.IsPrime]
    (hcoeff : ∀ a : ParameterAlgebra, seedMap a = 0 → C a ∈ P)
    (hH : pointEquationH incidencePoint ∈ P)
    (hF : pointEquationF incidencePoint ∈ P)
    (hx : ∃ j : Fin 5, (X j : Poly ParameterAlgebra) ∉ P) :
    ∃ i : Fin 4, (X i.castSucc : Poly ParameterAlgebra) ∉ P := by
  have hHseed : smoothH Complex.I ∈ specializedPrime P := by
    simpa only [CycleQ2EtaleIncidenceCurve.seed_cubic] using
      specialization_mem P hcoeff (pointEquationH incidencePoint) hH
  have hFseed : smoothF (57 : ℂ) Complex.I ∈ specializedPrime P := by
    simpa only [CycleQ2EtaleIncidenceCurve.seed_sextic] using
      specialization_mem P hcoeff (pointEquationF incidencePoint) hF
  have hxseed : ∃ j : Fin 5, (X j : Poly ℂ) ∉ specializedPrime P := by
    obtain ⟨j, hj⟩ := hx
    exact ⟨j, by simpa only [coordinate_mem_specializedPrime_iff] using hj⟩
  rcases CycleQ2SeedCoordinateCover.seedPrime_coordinate_cover
      (57 : ℂ) Complex.I (specializedPrime P) hHseed hFseed hxseed with h₁ | h₂ | h₃
  · exact ⟨1, by simpa only [coordinate_mem_specializedPrime_iff] using h₁⟩
  · exact ⟨2, by simpa only [coordinate_mem_specializedPrime_iff] using h₂⟩
  · exact ⟨3, by simpa only [coordinate_mem_specializedPrime_iff] using h₃⟩

end CycleQ2IncidenceSeedPrimeTransport

end

#print axioms CycleQ2IncidenceSeedPrimeTransport.quotient_specialization
#print axioms CycleQ2IncidenceSeedPrimeTransport.seed_fiber_prime_coordinate_cover
