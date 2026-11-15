import Proposal.GeometricSeedFermatCone
import Proposal.GeometricSurfaceBindings
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper

/-!
# The actual weighted projective zero-cubic seed

This file equips the existing literal cone quotient with its inherited
weighted grading and forms its native projective spectrum. The coefficient
map and structural morphism use the same complex algebra structure as the
affine cone. The four degree-one coordinate classes and the Fermat relation
are exported for the chart retraction and global smoothness construction.

Source-only draft: no Lean elaboration, compilation, or kernel replay has
been run. Prepared for `fqlx` with OpenAI ChatGPT assistance, following the
geometric seed in Ben Diamond's surface-section argument.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2SeedFermatProj

open CategoryTheory AlgebraicGeometry MvPolynomial
open CycleQ2GeometricSeedSmooth CycleQ2SeedFermatCone
open CycleQ2GeometricIncidenceProj

attribute [local instance] MvPolynomial.weightedGradedAlgebra

/-- The zero-cubic defining equation has its actual weighted degree six. -/
theorem seedEquation_homogeneous (r : ℂ) :
    (seedFamily r 0).IsWeightedHomogeneous geometricWeight 6 := by
  apply homogeneous_of_character
  exact seedFamily_homogeneous r 0 (by intro e he; simp at he)

theorem coneIdeal_homogeneous (r : ℂ) :
    (Ideal.span {seedFamily r 0}).IsHomogeneous (PolynomialGrade ℂ) := by
  apply Ideal.homogeneous_span
  intro p hp
  obtain rfl := Set.mem_singleton_iff.mp hp
  exact ⟨6, seedEquation_homogeneous r⟩

/-- The degree pieces are the images of the original weighted polynomials. -/
abbrev coneGrade (r : ℂ) (n : ℕ) : Submodule ℂ (ConeRing r) :=
  CycleQ2GeometricProjectiveCurve.HomogeneousQuotient.grade
    (PolynomialGrade ℂ) (Ideal.span {seedFamily r 0}) n

instance coneGradedRing (r : ℂ) : GradedRing (coneGrade r) :=
  CycleQ2GeometricProjectiveCurve.HomogeneousQuotient.gradedRing
    (PolynomialGrade ℂ) (Ideal.span {seedFamily r 0}) (coneIdeal_homogeneous r)

theorem coneQuotient_mem_grade (r : ℂ) {n : ℕ} {p : SeedPolynomial}
    (hp : p.IsWeightedHomogeneous geometricWeight n) :
    coneQuotient r p ∈ coneGrade r n :=
  ⟨p, hp, rfl⟩

theorem coordinate_mem_grade_weight (r : ℂ) (j : Fin 5) :
    coordinateClass r j ∈ coneGrade r (geometricWeight j) :=
  coneQuotient_mem_grade r (isWeightedHomogeneous_X ℂ geometricWeight j)

@[simp] theorem geometricWeight_castSucc (i : Fin 4) :
    geometricWeight i.castSucc = 1 := by
  fin_cases i <;> rfl

theorem coordinate_mem_grade (r : ℂ) (i : Fin 4) :
    coordinateClass r i.castSucc ∈ coneGrade r 1 := by
  simpa only [geometricWeight_castSucc] using coordinate_mem_grade_weight r i.castSucc

/-- The coefficient homomorphism into the actual degree-zero piece. -/
def coefficient (r : ℂ) : ℂ →+* coneGrade r 0 :=
  algebraMap ℂ (coneGrade r 0)

@[simp] theorem coefficient_coe (r : ℂ) (c : ℂ) :
    (coefficient r c : ConeRing r) = coneQuotient r (C c) := rfl

/-- The weighted projective hypersurface of the literal cone quotient. -/
def threefold (r : ℂ) : Scheme := Proj (coneGrade r)

/-- Its structure map is the canonical projective-spectrum structure map
followed by the original complex coefficient map. -/
def threefoldToComplex (r : ℂ) :
    threefold r ⟶ Spec (CommRingCat.of ℂ) :=
  Proj.toSpecZero (coneGrade r) ≫ Spec.map (CommRingCat.ofHom (coefficient r))

theorem coneEquation (r : ℂ) :
    coneQuotient r (seedFamily r 0) = 0 := by
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact Ideal.subset_span (by simp)

/-- The exact relation that excludes the weighted vertex when r³ = 2. -/
theorem fermatRelation (r : ℂ) (hr : r ^ 3 = 2) :
    coordinateClass r 0 ^ 6 + coordinateClass r 1 ^ 6 +
      coordinateClass r 2 ^ 6 + coordinateClass r 3 ^ 6 +
      coordinateClass r 4 ^ 3 = 0 := by
  have h := coneEquation r
  rw [seedFamily_zero_of_cube_two r hr] at h
  simpa only [map_add, map_pow, coordinateClass] using h

#print axioms seedEquation_homogeneous
#print axioms coneGradedRing
#print axioms coneEquation
#print axioms fermatRelation

end CycleQ2SeedFermatProj

end
