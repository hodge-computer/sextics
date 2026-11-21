import Proposal.GeometricMonicPolynomialSpreading

/-!
# Exact generic-fiber identity for the monic polynomial on R[1/d]

The polynomial constructed over the actual principal localization must
base-change to the literal generic polynomial, not just an unnamed isomorphic
model. The earlier coefficient-clearing identity is used verbatim. No
statement about the geometric flag-Hilbert family, etaleness over the open,
or the protected residue is made here.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Polynomial
namespace CycleQ2MonicGenericFiber
variable {R : Type*} [CommRing R] [IsDomain R]

/-- The canonical map from a principal localization into the original
fraction ring, using the nonzero denominator. -/
def genericMap (d : R) (hd : d ≠ 0) :
    Localization.Away d →+* FractionRing R := by
  have inj : Function.Injective (algebraMap R (FractionRing R)) :=
    IsFractionRing.injective R (FractionRing R)
  have hne : algebraMap R (FractionRing R) d ≠ 0 := by
    simpa only [map_zero] using inj.ne hd
  exact IsLocalization.Away.lift (S := Localization.Away d)
    (g := algebraMap R (FractionRing R)) d (isUnit_iff_ne_zero.mpr hne)

@[simp] theorem genericMap_algebraMap (d : R) (hd : d ≠ 0) (a : R) :
    genericMap d hd (algebraMap R (Localization.Away d) a) =
      algebraMap R (FractionRing R) a := by
  simp only [genericMap, IsLocalization.Away.lift_eq]

/-- The actual inverse of the denominator maps to the field inverse. -/
theorem genericMap_invSelf (d : R) (hd : d ≠ 0) :
    genericMap d hd (IsLocalization.Away.invSelf (S := Localization.Away d) d) =
      (algebraMap R (FractionRing R) d)⁻¹ := by
  have hmul : algebraMap R (FractionRing R) d *
      genericMap d hd (IsLocalization.Away.invSelf (S := Localization.Away d) d) = 1 := by
    have hh := congrArg (genericMap d hd)
      (IsLocalization.Away.mul_invSelf (S := Localization.Away d) d)
    simpa only [map_mul, map_one, genericMap_algebraMap] using hh
  exact eq_inv_of_mul_eq_one_right hmul

@[simp] theorem genericMap_comp_algebraMap (d : R) (hd : d ≠ 0) :
    (genericMap d hd).comp (algebraMap R (Localization.Away d)) =
      algebraMap R (FractionRing R) := by
  ext a
  exact genericMap_algebraMap d hd a

def localModel (d : R) (q : Polynomial R) :
    Polynomial (Localization.Away d) :=
  q.map (algebraMap R (Localization.Away d)) *
    C (IsLocalization.Away.invSelf (S := Localization.Away d) d)

/-- Generic base change recovers p exactly, with no identification axiom. -/
theorem localModel_generic (d : R) (hd : d ≠ 0)
    (p : Polynomial (FractionRing R)) (q : Polynomial R)
    (hq : p * C (algebraMap R (FractionRing R) d) =
      q.map (algebraMap R (FractionRing R))) :
    (localModel d q).map (genericMap d hd) = p := by
  have inj : Function.Injective (algebraMap R (FractionRing R)) :=
    IsFractionRing.injective R (FractionRing R)
  have hne : algebraMap R (FractionRing R) d ≠ 0 := by
    simpa only [map_zero] using inj.ne hd
  calc
    (localModel d q).map (genericMap d hd) =
        (q.map (algebraMap R (FractionRing R))) *
        C ((algebraMap R (FractionRing R) d)⁻¹) := by
      simp only [localModel, Polynomial.map_mul, Polynomial.map_map,
        Polynomial.map_C, genericMap_invSelf, genericMap_comp_algebraMap]
    _ = (p * C (algebraMap R (FractionRing R) d)) *
        C ((algebraMap R (FractionRing R) d)⁻¹) := by rw [hq]
    _ = p := by
      rw [mul_assoc, ← C_mul, mul_inv_cancel₀ hne, map_one, mul_one]

/-- An actual monic polynomial over a principal open and an exact
identification of its generic fiber with the input monic polynomial. -/
theorem exists_monic_model_with_generic_fiber
    (p : Polynomial (FractionRing R)) (hp : p.Monic) :
    ∃ (d : R) (hd : d ≠ 0), ∃ f : Polynomial (Localization.Away d),
      f.Monic ∧ f.map (genericMap d hd) = p := by
  obtain ⟨d, hd, q, hlead, hq⟩ :=
    CycleQ2MonicPolynomialSpreading.exists_cleared_monic p hp
  have inj : Function.Injective (algebraMap R (Localization.Away d)) :=
    IsLocalization.injective (Localization.Away d)
      (powers_le_nonZeroDivisors_of_noZeroDivisors hd)
  refine ⟨d, hd, localModel d q, ?_, ?_⟩
  · change (q.map (algebraMap R (Localization.Away d)) *
      C (IsLocalization.Away.invSelf (S := Localization.Away d) d)).Monic
    apply monic_mul_C_of_leadingCoeff_mul_eq_one
    rw [leadingCoeff_map_of_injective inj q, hlead]
    exact IsLocalization.Away.mul_invSelf (S := Localization.Away d) d
  · exact localModel_generic d hd p q hq

end CycleQ2MonicGenericFiber
end

#print axioms CycleQ2MonicGenericFiber.genericMap_invSelf
#print axioms CycleQ2MonicGenericFiber.localModel_generic
#print axioms CycleQ2MonicGenericFiber.exists_monic_model_with_generic_fiber
