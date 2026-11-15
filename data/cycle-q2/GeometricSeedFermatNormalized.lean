import Proposal.GeometricSeedFermatChartRetract

/-!
# Literal normalized coordinate rings of the weighted projective seed

On the degree-one coordinate chart indexed by `i`, set the original
coordinate `z_i` equal to one. The ring below is the original polynomial
ring modulo the two explicit relations `seedFamily r 0` and `z_i - 1`.
It retains all five generators so its presentation has five variables
and two equations; no reindexing or replacement of the seed is implicit.

The next modules identify this literal quotient with the native degree-zero
Proj chart and prove its relative dimension. Status: source-only proof
draft; no Lean elaboration, compilation, or kernel replay was run.
Prepared for `fqlx` with OpenAI ChatGPT assistance, following Ben Diamond's
geometric seed construction.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2SeedFermatNormalized

open MvPolynomial CycleQ2GeometricSeedSmooth

/-- The original seed equation and the actual coordinate normalization. -/
def normalizedRelation (r : ℂ) (i : Fin 4) : Fin 2 → SeedPolynomial :=
  ![seedFamily r 0, X i.castSucc - 1]

def normalizedIdeal (r : ℂ) (i : Fin 4) : Ideal SeedPolynomial :=
  Ideal.span (Set.range (normalizedRelation r i))

/-- The literal normalized quotient, with its inherited complex algebra. -/
abbrev NormalizedRing (r : ℂ) (i : Fin 4) :=
  SeedPolynomial ⧸ normalizedIdeal r i

def normalizedQuotient (r : ℂ) (i : Fin 4) :
    SeedPolynomial →+* NormalizedRing r i :=
  Ideal.Quotient.mk (normalizedIdeal r i)

def normalizedCoordinate (r : ℂ) (i : Fin 4) (j : Fin 5) :
    NormalizedRing r i :=
  normalizedQuotient r i (X j)

@[simp] theorem normalizedQuotient_C (r : ℂ) (i : Fin 4) (c : ℂ) :
    normalizedQuotient r i (C c) = algebraMap ℂ (NormalizedRing r i) c := rfl

theorem normalizedQuotient_relation (r : ℂ) (i : Fin 4) (j : Fin 2) :
    normalizedQuotient r i (normalizedRelation r i j) = 0 := by
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact Ideal.subset_span ⟨j, rfl⟩

/-- The defining sextic vanishes in the literal normalized ring. -/
theorem normalizedEquation (r : ℂ) (i : Fin 4) :
    normalizedQuotient r i (seedFamily r 0) = 0 :=
  normalizedQuotient_relation r i 0

/-- The chosen degree-one coordinate is exactly one. -/
@[simp] theorem normalizedCoordinate_self (r : ℂ) (i : Fin 4) :
    normalizedCoordinate r i i.castSucc = 1 := by
  have h := normalizedQuotient_relation r i 1
  change normalizedQuotient r i (X i.castSucc - 1) = 0 at h
  rw [map_sub, map_one] at h
  exact sub_eq_zero.mp h

/-- The Fermat relation remains an identity in this exact quotient. -/
theorem normalizedFermatRelation (r : ℂ) (hr : r ^ 3 = 2) (i : Fin 4) :
    normalizedCoordinate r i 0 ^ 6 + normalizedCoordinate r i 1 ^ 6 +
      normalizedCoordinate r i 2 ^ 6 + normalizedCoordinate r i 3 ^ 6 +
      normalizedCoordinate r i 4 ^ 3 = 0 := by
  have h := normalizedEquation r i
  rw [seedFamily_zero_of_cube_two r hr] at h
  simpa only [map_add, map_pow, normalizedCoordinate] using h

end CycleQ2SeedFermatNormalized

end

#print axioms CycleQ2SeedFermatNormalized.normalizedEquation
#print axioms CycleQ2SeedFermatNormalized.normalizedCoordinate_self
#print axioms CycleQ2SeedFermatNormalized.normalizedFermatRelation
