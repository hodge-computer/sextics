import Proposal.GeometricMonicGenericFiber
import Proposal.GeometricResultantEtaleSpreading

/-!
# From the exact generic polynomial to an etale algebra over a principal open

The original monic separable generic polynomial p in Frac(R)[X] first gets
a monic equation f over R[1/d] with *literal* generic fiber p. The
derivative resultant of f is shown nonzero using the real generic map,
not supplied as a new hypothesis. Inverting this resultant then yields
the genuine standard-etale algebra built from f.

The geometric parameter map into the flag-Hilbert space, its spreading,
cycle-class comparison, and protected residue exactness remain unproved.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
open Polynomial
open CycleQ2MonicGenericFiber
open CycleQ2ResultantEtaleSpreading

namespace CycleQ2GenericEtaleBridge

variable {R : Type*} [CommRing R] [IsDomain R]

/-- The canonical localization-to-fraction-field hom is injective.
No comparison is inferred merely from identifying two abstract fields. -/
theorem genericMap_injective (d : R) (hd : d ≠ 0) :
    Function.Injective (genericMap d hd) := by
  apply (IsLocalization.injective_iff_map_algebraMap_eq
    (M := Submonoid.powers d) (f := genericMap d hd)).mpr
  intro x y
  constructor
  · intro h
    have hh := congrArg (genericMap d hd) h
    simpa only [genericMap_algebraMap] using hh
  · intro h
    apply congrArg (algebraMap R (Localization.Away d))
    apply IsFractionRing.injective R (FractionRing R)
    simpa only [genericMap_algebraMap] using h

/-- The derivative resultant specializes to its literal field resultant
under the injective generic map. -/
theorem resultant_map_generic (d : R) (hd : d ≠ 0)
    (f : Polynomial (Localization.Away d)) :
    resultant (f.map (genericMap d hd))
        (derivative (f.map (genericMap d hd))) =
      genericMap d hd (resultant f (derivative f)) := by
  let φ := genericMap d hd
  have hinj : Function.Injective φ := genericMap_injective d hd
  have H := resultant_map_map f (derivative f)
    f.natDegree (derivative f).natDegree φ
  change resultant (f.map φ) (derivative (f.map φ)) =
    φ (resultant f (derivative f))
  rw [derivative_map, natDegree_map_eq_of_injective hinj f,
    natDegree_map_eq_of_injective hinj (derivative f)]
  exact H

/-- Generic separability itself forces a nonzero resultant on the
localized coefficient ring. This is the precise nonempty-open input. -/
theorem resultant_ne_zero_of_generic_separable
    (d : R) (hd : d ≠ 0) (f : Polynomial (Localization.Away d))
    (hsep : (f.map (genericMap d hd)).Separable) :
    resultant f (derivative f) ≠ 0 := by
  have hk : resultant (f.map (genericMap d hd))
      (derivative (f.map (genericMap d hd))) ≠ 0 :=
    resultant_ne_zero _ _ hsep
  intro h
  apply hk
  rw [resultant_map_generic d hd f, h, map_zero]

/-- A *single* geometric-spreading input is reduced to the original
monic, separable fraction-field polynomial: the denominator, the monic
localized equation, its generic-fiber equality, a nonzero resultant,
and a standard-etale algebra over the further principal localization are
all supplied by conclusions, not by caller-supplied witnesses. -/
theorem exists_etale_polynomial_model
    (p : Polynomial (FractionRing R))
    (hp : p.Monic) (hsep : p.Separable) :
    ∃ (d : R) (hd : d ≠ 0),
      ∃ f : Polynomial (Localization.Away d),
        f.Monic ∧ f.map (genericMap d hd) = p ∧
        ∃ (r : Localization.Away d), r ≠ 0 ∧
          ∃ P : StandardEtalePair (Localization.Away r),
            P.f = f.map (algebraMap (Localization.Away d) (Localization.Away r)) ∧
            Algebra.Etale (Localization.Away r) P.Ring := by
  obtain ⟨d, hd, f, hf, hgeneric⟩ :=
    exists_monic_model_with_generic_fiber p hp
  letI : IsDomain (Localization.Away d) := Localization.Away.isDomain hd
  have hsepF : (f.map (genericMap d hd)).Separable := by
    rw [hgeneric]
    exact hsep
  let r : Localization.Away d := resultant f (derivative f)
  have hr : r ≠ 0 :=
    resultant_ne_zero_of_generic_separable d hd f hsepF
  obtain ⟨P, hP, hEtale⟩ := exists_etale_model_after_resultant f hf hr
  exact ⟨d, hd, f, hf, hgeneric, r, hr, P, hP, hEtale⟩

end CycleQ2GenericEtaleBridge

end

#print axioms CycleQ2GenericEtaleBridge.genericMap_injective
#print axioms CycleQ2GenericEtaleBridge.resultant_ne_zero_of_generic_separable
#print axioms CycleQ2GenericEtaleBridge.exists_etale_polynomial_model
