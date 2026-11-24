import Proposal.GeometricSeparableStandardEtale
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.RingTheory.Localization.Away.Basic

/-!
# An etale polynomial model over the open where the resultant is invertible

For a monic f in R[X], the derivative resultant r = Res(f,f') detects
the étale locus. If R is a domain and r != 0, the principal localization
R[1/r] is a nonzero ring. The image of f becomes separable there, because
the resultant is a unit, hence f and f' are coprime.

The previously compiled standard-etale construction then gives an
actual etale R[1/r]-algebra and a specified polynomial equation.

The theorem proves the algebraic spread once an R-polynomial is in hand;
it does not yet bind the result to a specific parameter morphism into the
cycle-q2 flag-Hilbert scheme or prove projector-class specialization.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
open Polynomial

namespace CycleQ2ResultantEtaleSpreading

variable {R : Type*} [CommRing R] [IsDomain R]

/-- The resultant of a polynomial and its actual derivative commutes with
the injective structure map to a principal localization. -/
theorem resultant_derivative_map (f : Polynomial R) (s : R) (hs : s ≠ 0) :
    resultant (f.map (algebraMap R (Localization.Away s)))
      (derivative (f.map (algebraMap R (Localization.Away s)))) =
    algebraMap R (Localization.Away s) (resultant f (derivative f)) := by
  let φ : R →+* Localization.Away s := algebraMap R _
  have hinj : Function.Injective φ :=
    IsLocalization.injective (Localization.Away s)
      (powers_le_nonZeroDivisors_of_noZeroDivisors hs)
  have H := resultant_map_map f (derivative f)
    f.natDegree (derivative f).natDegree φ
  change resultant (f.map φ) (derivative (f.map φ)) =
    φ (resultant f (derivative f))
  rw [derivative_map, natDegree_map_eq_of_injective hinj f,
    natDegree_map_eq_of_injective hinj (derivative f)]
  exact H

/-- The monic polynomial becomes separable after the real localization
at its nonzero derivative resultant, not by assuming separability there. -/
theorem separable_after_inverting_resultant
    (f : Polynomial R) (hf : f.Monic)
    (hr : resultant f (derivative f) ≠ 0) :
    (f.map (algebraMap R (Localization.Away (resultant f (derivative f))))).Separable := by
  let r : R := resultant f (derivative f)
  let φ : R →+* Localization.Away r := algebraMap R _
  have hunit : IsUnit (φ r) := IsLocalization.Away.algebraMap_isUnit r
  have hres : resultant (f.map φ) (derivative (f.map φ)) = φ r :=
    resultant_derivative_map f r hr
  have hmonic : (f.map φ).Monic := hf.map φ
  apply (isUnit_resultant_iff_isCoprime hmonic).mp
  change IsUnit (resultant (f.map φ) (derivative (f.map φ)))
  rw [hres]
  exact hunit

/-- The constructed standard-etale pair uses the actual derivative
resultant principal open and the polynomial obtained from f. -/
theorem exists_etale_model_after_resultant
    (f : Polynomial R) (hf : f.Monic)
    (hr : resultant f (derivative f) ≠ 0) :
    ∃ P : StandardEtalePair (Localization.Away (resultant f (derivative f))),
      P.f = f.map (algebraMap R (Localization.Away (resultant f (derivative f)))) ∧
      Algebra.Etale (Localization.Away (resultant f (derivative f))) P.Ring := by
  let φ : R →+* Localization.Away (resultant f (derivative f)) := algebraMap R _
  have hm : (f.map φ).Monic := hf.map φ
  have hs : (f.map φ).Separable := separable_after_inverting_resultant f hf hr
  exact ⟨CycleQ2SeparableStandardEtale.pair (f.map φ) hm hs, rfl, inferInstance⟩

end CycleQ2ResultantEtaleSpreading

end

#print axioms CycleQ2ResultantEtaleSpreading.resultant_derivative_map
#print axioms CycleQ2ResultantEtaleSpreading.separable_after_inverting_resultant
#print axioms CycleQ2ResultantEtaleSpreading.exists_etale_model_after_resultant
