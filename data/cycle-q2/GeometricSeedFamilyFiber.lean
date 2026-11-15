import Proposal.GeometricSeedProjectiveFamilyProper
import Proposal.GeometricSeedProjectiveSpecialization
import Proposal.GeometricSeedFermatDimension

/-!
# A complex point on the actual zero fiber of the full projective family

Properness of the full projective family gives properness of its genuine
scheme-theoretic zero fiber. The already constructed complex point on the
original seed maps canonically into this fiber. Both projection identities
are preserved, and the resulting point is a section of the actual fiber
structure morphism.

The source seed is smooth of relative dimension three. Identifying it
isomorphically with the full zero fiber is still a separate obligation;
no smoothness assertion about that fiber is inferred from this map.
Status: source-only proof draft; no elaboration, compilation, or kernel
replay has been run. Prepared for `fqlx` with OpenAI ChatGPT assistance,
following Ben Diamond and the project's geometric argument.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2SeedFamilyFiber

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CycleQ2SeedFermatProj CycleQ2SeedFermatPoint
  CycleQ2SeedProjectiveFamily CycleQ2SeedProjectiveFamilyProper
  CycleQ2SeedProjectiveSpecialization

/-- The actual projection from the scheme-theoretic zero fiber to `Spec ℂ`. -/
def zeroFiberToComplex (r : ℂ) : ZeroFiber r ⟶ Spec (CommRingCat.of ℂ) :=
  pullback.fst zeroParameterMorphism (familyToParameters r)

/-- Properness follows by the actual base change of the full family. -/
theorem zeroFiber_proper (r : ℂ) : IsProper (zeroFiberToComplex r) := by
  letI := familyToParameters_proper r
  dsimp only [zeroFiberToComplex]
  infer_instance

/-- The original seed point, carried into the genuine zero fiber by the
constructed coefficient-specialization morphism. -/
def zeroFiberPoint (r : ℂ) (hr : r ^ 3 = 2) :
    Spec (CommRingCat.of ℂ) ⟶ ZeroFiber r :=
  seedPoint r hr ≫ seedToZeroFiber r

/-- The point respects the actual complex base of the fiber. -/
theorem zeroFiberPoint_overComplex (r : ℂ) (hr : r ^ 3 = 2) :
    zeroFiberPoint r hr ≫ zeroFiberToComplex r =
      𝟙 (Spec (CommRingCat.of ℂ)) := by
  rw [zeroFiberPoint, Category.assoc, zeroFiberToComplex,
    seedToZeroFiber_fst, seedPoint_overComplex]

/-- Its projection to the total family is exactly the original seed point
followed by the canonical global specialization morphism. -/
theorem zeroFiberPoint_toFamily (r : ℂ) (hr : r ^ 3 = 2) :
    zeroFiberPoint r hr ≫ pullback.snd zeroParameterMorphism (familyToParameters r) =
      seedPoint r hr ≫ seedToFamily r := by
  rw [zeroFiberPoint, Category.assoc, seedToZeroFiber_snd]

theorem zeroFiber_nonempty (r : ℂ) (hr : r ^ 3 = 2) : Nonempty (ZeroFiber r) :=
  ⟨zeroFiberPoint r hr (default : Spec (CommRingCat.of ℂ))⟩

/-- The full proper parameter family has a nonempty proper zero fiber,
with its parameter and point supplied by the constructed seed. -/
theorem exists_nonempty_proper_zeroFiber :
    ∃ r : ℂ, r ^ 3 = 2 ∧ IsProper (familyToParameters r) ∧
      Nonempty (ZeroFiber r) ∧ IsProper (zeroFiberToComplex r) := by
  obtain ⟨r, hr, _, _, _⟩ :=
    CycleQ2SeedFermatDimension.exists_nonempty_smoothOfRelativeDimension_proper
  exact ⟨r, hr, familyToParameters_proper r,
    zeroFiber_nonempty r hr, zeroFiber_proper r⟩

end CycleQ2SeedFamilyFiber

end

#print axioms CycleQ2SeedFamilyFiber.zeroFiber_proper
#print axioms CycleQ2SeedFamilyFiber.zeroFiberPoint_overComplex
#print axioms CycleQ2SeedFamilyFiber.zeroFiberPoint_toFamily
#print axioms CycleQ2SeedFamilyFiber.exists_nonempty_proper_zeroFiber
