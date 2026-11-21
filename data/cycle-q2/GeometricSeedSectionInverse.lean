import Proposal.GeometricSectionInverseIdeal
import Proposal.GeometricSeedImageTwistedDuality

/-!
# Actual seed image sections and their inverse-ideal transition

For the original linkage matrix, a Bezout identity in the three rows of
M*t produces a unique inverse in the ORIGINAL left ideal. The established
degree-four image-dual comparison forces its inverse transition to have
degree minus four. The complex seed specialization uses the existing
chartFactorData and the original constant vector t.

Source-only draft, 15 November 2026. Not elaborated or kernel-replayed.
The conversion from emptiness to chart Bezout identities and the final
negative-degree gluing application are supplied in the accompanying
written proof, not formalized here. This file does not assert the final
certificate or a closed Lean nonemptiness theorem.
Prepared for fqlx with OpenAI ChatGPT assistance, following the geometric
construction attributed in solution.md.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace CycleQ2SeedSectionInverse

open Matrix
open CycleQ2SegreFactorSequence CycleQ2SegreLinkageDuality
  CycleQ2SeedProjectiveImageTwist CycleQ2SeedImageTwistedDuality

variable {R : Type*} [CommRing R]

/-- The same section vector in the actual matrix range. -/
def matrixSection (F : FactorData R) (t : Fin 3 → R) : Regrading.Image F :=
  ⟨F.matrix *ᵥ t, ⟨t, rfl⟩⟩

def sectionFunctional (F : FactorData R) (t : Fin 3 → R) : F.leftIdeal →ₗ[R] R :=
  Regrading.imageDual F (matrixSection F t)

/-- Its three generator values are precisely the three original rows. -/
theorem sectionFunctional_left (F : FactorData R) (t : Fin 3 → R) (a : Fin 3) :
    sectionFunctional F t (leftElement F a) = (F.matrix *ᵥ t) a :=
  Regrading.imageDual_selected F (matrixSection F t) a

/-- This is a construction from the actual row Bezout coefficients,
not an assumed inverse or a new replacement ideal. -/
theorem exists_unique_inverse_of_rows (F : FactorData R) (t c : Fin 3 → R)
    (h : (∑ a, c a * (F.matrix *ᵥ t) a) = 1) :
    ∃! x : F.leftIdeal, sectionFunctional F t x = 1 := by
  apply CycleQ2SectionInverseIdeal.exists_unique_inverse_of_bezout
    F.leftIdeal (sectionFunctional F t) (leftElement F) c
  simpa only [sectionFunctional_left] using h

theorem matrixSection_transition (F G : FactorData R) (u : Rˣ)
    (hM : G.matrix = (u : R) ^ 14 • F.matrix) (t : Fin 3 → R) :
    matrixSection G t = imageTransition F G u hM (matrixSection F t) := by
  apply Subtype.ext
  change G.matrix *ᵥ t = (u : R) ^ 14 • (F.matrix *ᵥ t)
  rw [hM, Matrix.smul_mulVec]

/-- All matrix and ideal scalings are retained in the actual functional. -/
theorem sectionFunctional_transition (F G : FactorData R) (u : Rˣ)
    (hM : G.matrix = (u : R) ^ 14 • F.matrix)
    (hL : ∀ a, G.left a = (u : R) ^ 10 * F.left a)
    (t : Fin 3 → R) (x : G.leftIdeal) :
    sectionFunctional G t x = (u : R) ^ 4 *
      sectionFunctional F t ((idealEquiv F G u hL).symm x) := by
  change Regrading.imageDual G (matrixSection G t) x = _
  rw [matrixSection_transition F G u hM t]
  exact imageDual_transition_apply F G u hM hL (matrixSection F t) x

/-- The inverse uses the NEGATIVE fourth power, the crucial sign for
negative-degree gluing. It is independent of the Bezout choices. -/
theorem sectionInverse_transition (F G : FactorData R) (u : Rˣ)
    (hM : G.matrix = (u : R) ^ 14 • F.matrix)
    (hL : ∀ a, G.left a = (u : R) ^ 10 * F.left a)
    (t : Fin 3 → R) (a : F.leftIdeal) (b : G.leftIdeal)
    (ha : sectionFunctional F t a = 1)
    (hb : sectionFunctional G t b = 1) :
    b = (((u⁻¹ : Rˣ) : R) ^ 4) • idealEquiv F G u hL a :=
  CycleQ2SectionInverseIdeal.inverse_rescales_of_equiv
    F.leftIdeal G.leftIdeal (idealEquiv F G u hL)
    (sectionFunctional F t) (sectionFunctional G t) u 4
    (sectionFunctional_transition F G u hM hL t) a b ha hb

open CycleQ2SeedProjectiveImageChart

/-- Specialization to the original literal r=57, theta=1 projective
chart and the same complex section vector. Its Bezout premise is explicit. -/
theorem seedChart_inverse_of_rows (i : Fin 3) (t : Fin 3 → ℂ)
    (c : Fin 3 → AffineRing i)
    (h : (∑ a, c a * ((chartFactorData i).matrix *ᵥ
      (fun j => algebraMap ℂ (AffineRing i) (t j))) a) = 1) :
    ∃! x : OrbitIdeal i,
      sectionFunctional (chartFactorData i)
        (fun j => algebraMap ℂ (AffineRing i) (t j)) x = 1 :=
  exists_unique_inverse_of_rows (chartFactorData i)
    (fun j => algebraMap ℂ (AffineRing i) (t j)) c h

end CycleQ2SeedSectionInverse

end

#print axioms CycleQ2SeedSectionInverse.exists_unique_inverse_of_rows
#print axioms CycleQ2SeedSectionInverse.sectionInverse_transition
#print axioms CycleQ2SeedSectionInverse.seedChart_inverse_of_rows
