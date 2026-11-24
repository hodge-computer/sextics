import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.RingTheory.Trace.Basic

/-!
# The finite etale generic parameter has a separable primitive polynomial

For a finite characteristic-zero field extension L/K, the primitive element
theorem produces a monic separable polynomial F over K, a root alpha generating
L, and a nonzero derivative F'(alpha). These are the algebraic ingredients
needed to clear denominators and spread a finite etale point from the generic
fiber to an open curve.

The field trace has an explicit normalized retraction of K -> L. This
constructs an *actual field trace*, unlike the previous abstract
cohomological transfer module.

The localization, discriminant inversion, finite etale model over the curve,
and the morphism to the original flag-Hilbert parameter space are not
constructed here. The protected residue statement is unchanged.
-/

set_option autoImplicit false

noncomputable section

open Polynomial

namespace CycleQ2FinitePrimitivePolynomial

variable (K L : Type*) [Field K] [Field L] [Algebra K L]
variable [FiniteDimensional K L] [CharZero K]

/-- Finite extensions in characteristic zero are separable, with the same
minpoly argument used for the previously compiled finite-etale point. -/
private theorem separable_extension : Algebra.IsSeparable K L :=
  ⟨fun x => (minpoly.irreducible (Algebra.IsIntegral.isIntegral x)).separable⟩

/-- A single polynomial model for the finite generic parameter extension:
the generator, monic separable polynomial, full degree, root equation,
and invertible derivative are derived, not assumed. -/
theorem exists_primitive_model :
    ∃ α : L,
      Algebra.adjoin K {α} = ⊤ ∧
      (minpoly K α).Monic ∧
      (minpoly K α).Separable ∧
      (minpoly K α).natDegree = Module.finrank K L ∧
      aeval α (minpoly K α) = 0 ∧
      aeval α (derivative (minpoly K α)) ≠ 0 := by
  letI : Algebra.IsSeparable K L := separable_extension K L
  let pb : PowerBasis K L := Field.powerBasisOfFiniteOfSeparable K L
  have hgen : Algebra.adjoin K {pb.gen} = ⊤ := pb.adjoin_gen_eq_top
  have hmonic : (minpoly K pb.gen).Monic :=
    minpoly.monic (Algebra.IsIntegral.isIntegral pb.gen)
  have hsep : (minpoly K pb.gen).Separable :=
    (minpoly.irreducible (Algebra.IsIntegral.isIntegral pb.gen)).separable
  have hdeg : (minpoly K pb.gen).natDegree = Module.finrank K L := by
    have hfield : IntermediateField.adjoin K {pb.gen} = ⊤ :=
      IntermediateField.adjoin_eq_top_of_algebra K {pb.gen} hgen
    exact (Field.primitive_element_iff_minpoly_natDegree_eq K pb.gen).mp hfield
  have hroot : aeval pb.gen (minpoly K pb.gen) = 0 :=
    minpoly.aeval K pb.gen
  have hder : aeval pb.gen (derivative (minpoly K pb.gen)) ≠ 0 :=
    (Algebra.IsSeparable.isSeparable K pb.gen).aeval_derivative_ne_zero hroot
  exact ⟨pb.gen, hgen, hmonic, hsep, hdeg, hroot, hder⟩

/-- Degree of the actual finite field extension, not a chosen numerator. -/
def extensionDegree : ℕ := Module.finrank K L

private theorem extensionDegree_ne_zero :
    (extensionDegree K L : K) ≠ 0 := by
  have hpos : 0 < Module.finrank K L := Module.finrank_pos
  exact Nat.cast_ne_zero.mpr (Nat.ne_of_gt hpos)

/-- Actual normalized field trace for the finite extension. -/
def normalizedFieldTrace : L →ₗ[K] K :=
  ((extensionDegree K L : K)⁻¹) • Algebra.trace K L

/-- The field trace identity gives a genuine retraction of the original
scalar inclusion. Characteristic zero ensures its degree is invertible. -/
theorem normalizedFieldTrace_algebraMap (a : K) :
    normalizedFieldTrace K L (algebraMap K L a) = a := by
  change ((extensionDegree K L : K)⁻¹) •
    Algebra.trace K L (algebraMap K L a) = a
  rw [Algebra.trace_algebraMap]
  simp only [extensionDegree, nsmul_eq_mul, smul_eq_mul]
  have hn : (Module.finrank K L : K) ≠ 0 := extensionDegree_ne_zero K L
  rw [← mul_assoc, inv_mul_cancel₀ hn, one_mul]

/-- Nondegeneracy of the *actual* field trace pairing. -/
theorem traceForm_nondegenerate :
    (Algebra.traceForm K L).Nondegenerate := by
  letI : Algebra.IsSeparable K L := separable_extension K L
  exact _root_.traceForm_nondegenerate K L

end CycleQ2FinitePrimitivePolynomial

end

#print axioms CycleQ2FinitePrimitivePolynomial.exists_primitive_model
#print axioms CycleQ2FinitePrimitivePolynomial.normalizedFieldTrace_algebraMap
#print axioms CycleQ2FinitePrimitivePolynomial.traceForm_nondegenerate
