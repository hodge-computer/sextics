import Proposal.GeometricCofactorResidue
import Mathlib.RingTheory.Ideal.Operations

/-!
# A global residue frame from the actual Jacobian ideal

If the three signed minors generate the unit ideal, their Bezout combination
gives a frame on the entire affine curve chart. No single minor is required
to be invertible. The polynomial Cramer identity proves reconstruction, so
the resulting frame is uniquely characterized by residue coefficient one
and does not depend on the chosen Bezout coefficients.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace CycleQ2GeometricGlobalResidue

open CycleQ2GeometricCofactorResidue

variable {R : Type*} [CommRing R] (a b : Coordinates R)

def minorIdeal : Ideal R := Ideal.span (Set.range (cofactor a b))

theorem exists_bezout (h : minorIdeal a b = ⊤) :
    ∃ w : Fin 3 → R, ∑ k, w k * cofactor a b k = 1 := by
  apply Ideal.mem_span_range_iff_exists_fun.mp
  change (1 : R) ∈ minorIdeal a b
  rw [h]
  trivial

def bezoutWeights (h : minorIdeal a b = ⊤) : Fin 3 → R :=
  Classical.choose (exists_bezout a b h)

theorem bezoutWeights_spec (h : minorIdeal a b = ⊤) :
    ∑ k, bezoutWeights a b h k * cofactor a b k = 1 :=
  Classical.choose_spec (exists_bezout a b h)

/-- A frame on the whole affine chart, chosen using its unit Jacobian ideal. -/
def globalResidue (h : minorIdeal a b = ⊤) : ResidueModule a b :=
  ∑ k, bezoutWeights a b h k • toResidue a b (coordinateVector k)

@[simp] theorem residueFunctional_globalResidue (h : minorIdeal a b = ⊤) :
    residueFunctional a b (globalResidue a b h) = 1 := by
  simp only [globalResidue, map_sum, map_smul, residueFunctional_toResidue,
    coefficient_coordinateVector, smul_eq_mul]
  exact bezoutWeights_spec a b h

theorem scaled_reconstruction_quotient (η : ResidueModule a b) (k : Fin 3) :
    cofactor a b k • η =
      residueFunctional a b η • toResidue a b (coordinateVector k) := by
  refine Quotient.inductionOn' η (fun v => ?_)
  exact scaled_reconstruction a b v k

/-- Reconstruction holds globally by summing the three Cramer identities. -/
theorem global_reconstruction (h : minorIdeal a b = ⊤) (η : ResidueModule a b) :
    η = residueFunctional a b η • globalResidue a b h := by
  calc
    η = (∑ k, bezoutWeights a b h k * cofactor a b k) • η := by
      rw [bezoutWeights_spec, one_smul]
    _ = ∑ k, bezoutWeights a b h k • (cofactor a b k • η) := by
      simp only [Finset.sum_smul, smul_smul]
    _ = ∑ k, bezoutWeights a b h k •
        (residueFunctional a b η • toResidue a b (coordinateVector k)) := by
      simp only [scaled_reconstruction_quotient]
    _ = residueFunctional a b η • globalResidue a b h := by
      simp only [globalResidue, Finset.smul_sum]
      exact Finset.sum_congr rfl (fun k _ =>
        smul_comm (bezoutWeights a b h k) (residueFunctional a b η) _)

theorem residueFunctional_injective (h : minorIdeal a b = ⊤) :
    Function.Injective (residueFunctional a b) := by
  intro η ζ heq
  rw [global_reconstruction a b h η, global_reconstruction a b h ζ, heq]

theorem residueFunctional_surjective (h : minorIdeal a b = ⊤) :
    Function.Surjective (residueFunctional a b) := by
  intro r
  refine ⟨r • globalResidue a b h, ?_⟩
  simp only [map_smul, residueFunctional_globalResidue, smul_eq_mul, mul_one]

/-- The cofactor functional itself is the global affine trivialization. -/
def residueEquiv (h : minorIdeal a b = ⊤) : ResidueModule a b ≃ₗ[R] R :=
  LinearEquiv.ofBijective (residueFunctional a b)
    ⟨residueFunctional_injective a b h, residueFunctional_surjective a b h⟩

@[simp] theorem residueEquiv_apply (h : minorIdeal a b = ⊤) (η : ResidueModule a b) :
    residueEquiv a b h η = residueFunctional a b η := rfl

@[simp] theorem residueEquiv_symm_one (h : minorIdeal a b = ⊤) :
    (residueEquiv a b h).symm 1 = globalResidue a b h := by
  apply (residueEquiv a b h).injective
  rw [LinearEquiv.apply_symm_apply, residueEquiv_apply, residueFunctional_globalResidue]

/-- Uniqueness makes all choices of Bezout coefficients give the same frame. -/
theorem globalResidue_unique (h : minorIdeal a b = ⊤) (η : ResidueModule a b)
    (hη : residueFunctional a b η = 1) : η = globalResidue a b h := by
  rw [global_reconstruction a b h η, hη, one_smul]

/-- On any invertible-minor patch the global frame agrees with the usual
normalized coordinate differential in the gradient cokernel. -/
theorem globalResidue_eq_normalized (h : minorIdeal a b = ⊤)
    (k : Fin 3) (u : Rˣ) (hu : cofactor a b k = (u : R)) :
    globalResidue a b h = normalizedResidue a b k u :=
  (globalResidue_unique a b h _ (residueFunctional_normalized a b k u hu)).symm

#print axioms residueEquiv
#print axioms global_reconstruction
#print axioms globalResidue_unique
#print axioms globalResidue_eq_normalized

end CycleQ2GeometricGlobalResidue
end
