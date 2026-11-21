import Proposal.GeometricSeedProjectiveFamily

/-!
# Normalized coordinate rings of the full cubic parameter family

Each degree-one projective chart is represented by the original polynomial
ring over ParameterRing with the two relations `familyEquation r` and
`z_i - 1`. The coefficient algebra is the original full cubic parameter
ring. Subsequent modules construct its native Proj chart isomorphism and
its relative Jacobian patches.

Status: source-only proof draft; no elaboration, compilation, or kernel
replay has been run. Prepared for `fqlx` with OpenAI ChatGPT assistance,
following Ben Diamond and the project's geometric construction.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2SeedFamilyNormalized

open MvPolynomial CategoryTheory AlgebraicGeometry
open CycleQ2SeedCubicFamily CycleQ2SeedProjectiveFamily

def normalizedRelation (r : ℂ) (i : Fin 4) : Fin 2 → FamilyPolynomial :=
  ![familyEquation r, X i.castSucc - 1]

def normalizedIdeal (r : ℂ) (i : Fin 4) : Ideal FamilyPolynomial :=
  Ideal.span (Set.range (normalizedRelation r i))

abbrev NormalizedRing (r : ℂ) (i : Fin 4) :=
  FamilyPolynomial ⧸ normalizedIdeal r i

def normalizedQuotient (r : ℂ) (i : Fin 4) :
    FamilyPolynomial →+* NormalizedRing r i :=
  Ideal.Quotient.mk (normalizedIdeal r i)

def normalizedCoordinate (r : ℂ) (i : Fin 4) (j : Fin 5) : NormalizedRing r i :=
  normalizedQuotient r i (X j)

@[simp] theorem normalizedQuotient_C (r : ℂ) (i : Fin 4) (c : ParameterRing) :
    normalizedQuotient r i (C c) = algebraMap ParameterRing (NormalizedRing r i) c := rfl

theorem normalizedQuotient_relation (r : ℂ) (i : Fin 4) (j : Fin 2) :
    normalizedQuotient r i (normalizedRelation r i j) = 0 := by
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact Ideal.subset_span ⟨j, rfl⟩

theorem normalizedEquation (r : ℂ) (i : Fin 4) :
    normalizedQuotient r i (familyEquation r) = 0 :=
  normalizedQuotient_relation r i 0

@[simp] theorem normalizedCoordinate_self (r : ℂ) (i : Fin 4) :
    normalizedCoordinate r i i.castSucc = 1 := by
  have h := normalizedQuotient_relation r i 1
  change normalizedQuotient r i (X i.castSucc - 1) = 0 at h
  rw [map_sub, map_one] at h
  exact sub_eq_zero.mp h

def normalizedScheme (r : ℂ) (i : Fin 4) : Scheme :=
  Spec (CommRingCat.of (NormalizedRing r i))

/-- The normalized affine scheme retains the original coefficient base. -/
def normalizedToParameters (r : ℂ) (i : Fin 4) :
    normalizedScheme r i ⟶ parameterScheme :=
  Spec.map (CommRingCat.ofHom (algebraMap ParameterRing (NormalizedRing r i)))

end CycleQ2SeedFamilyNormalized

end

#print axioms CycleQ2SeedFamilyNormalized.normalizedEquation
#print axioms CycleQ2SeedFamilyNormalized.normalizedCoordinate_self
