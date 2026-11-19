import Proposal.GeometricUniversalWeightedChart
import HodgeComputer.Constructions.HoldoutCover.FiniteDifferentials
import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Pole-three reduction for the actual weighted source

The normal derivation differentiates the chart equation to one.
Subtracting the specified rational differential reduces the source
from a triple pole to a simple pole. Its coefficient is regular when
the normal derivative of the equation is invertible, and evaluates
on the hypersurface to the existing source density.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false

noncomputable section

namespace CycleQ2WeightedPoleThree

section NormalAlgebra

variable {R T : Type*} [CommRing R] [Field T] [CharZero T] [Algebra R T]

/-- A rational correction for a triple pole in a coordinate differentiating to one. -/
def correction (D : Derivation R T T) (f φ : T) : T :=
  -(φ / (2 * f^2)) - D φ / (2*f)

theorem reduce (D : Derivation R T T) (f φ : T) (hf : f ≠ 0) (hD : D f = 1) :
    φ / f^3 = D (correction D f φ) + (D (D φ) / 2) / f := by
  have htwo : D 2 = 0 := D.map_natCast 2
  simp only [correction, map_sub, map_neg, Derivation.leibniz_div,
    Derivation.leibniz, htwo, Derivation.leibniz_pow, smul_eq_mul, hD,
    mul_zero, add_zero]
  norm_num
  field_simp
  ring

variable (D : Derivation R T T) (n : T)
open SplitHigherResidue (normalSourceTwo)

omit [CharZero T] in
private theorem normal_apply (a : T) : (n⁻¹ • D) a = D a / n := by
  rw [Derivation.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]

theorem second_coefficient (a : T) (hn : n ≠ 0) :
    ((n⁻¹ • D) ((n⁻¹ • D) (a / n)) / 2) =
      normalSourceTwo a (D a) (D (D a)) n (D n) (D (D n)) / n := by
  simp only [normal_apply, Derivation.leibniz_div, Derivation.leibniz,
    smul_eq_mul, map_sub, Derivation.leibniz_inv, Derivation.leibniz_pow, normalSourceTwo]
  norm_num
  field_simp
  ring

end NormalAlgebra

open MvPolynomial
open CycleQ2MonicWeightedAffineEquation (Coeff separate)
open CycleQ2MonicWeightedPrimitiveIdentity (Pol normal sourceNumerator density b)
open CycleQ2MonicWeightedPrimitiveSpecialization (Fld fieldValue)
open CycleQ2GenericWeightedSpatialDenominator (universalAffine)
open CycleQ2UniversalWeightedTransfer (universal_normal_ne_zero separate_universal)

abbrev PolynomialRing := Pol Coeff
abbrev Ambient := FractionRing PolynomialRing
abbrev W := Fld universalAffine

private abbrev f := universalAffine
private abbrev n := normal f
private abbrev v := fieldValue f
private abbrev ι := algebraMap PolynomialRing Ambient

private theorem n_ne : n ≠ 0 := by
  intro hn
  exact universal_normal_ne_zero ((congrArg v hn).trans v.map_zero)

private theorem f_ne : f ≠ 0 := by
  intro h
  exact n_ne ((congrArg normal h).trans (pderiv (0 : Fin 4)).map_zero)

private theorem f_ambient_ne : ι f ≠ 0 :=
  fun h => f_ne ((IsFractionRing.injective PolynomialRing Ambient) (h.trans ι.map_zero.symm))

private theorem n_ambient_ne : ι n ≠ 0 :=
  fun h => n_ne ((IsFractionRing.injective PolynomialRing Ambient) (h.trans ι.map_zero.symm))

local instance polynomialInt : Algebra ℤ PolynomialRing := Ring.toIntAlgebra _
local instance ambientInt : Algebra ℤ Ambient := Ring.toIntAlgebra _

private def polynomialPartial : Derivation ℤ PolynomialRing PolynomialRing :=
  (pderiv (0 : Fin 4) : Derivation Coeff PolynomialRing PolynomialRing).restrictScalars ℤ

/-- The initial affine-coordinate derivative extends to the ambient rational ring. -/
def ambientPartial : Derivation ℤ Ambient Ambient :=
  HoldoutConstruction.extendRingDerivation (P := PolynomialRing) (L := Ambient) polynomialPartial

private theorem ambientPartial_polynomial (p : PolynomialRing) : ambientPartial (ι p) = ι (normal p) :=
  HoldoutConstruction.extendRingDerivation_apply (L := Ambient) polynomialPartial p

/-- The rational normal direction for the chart equation (f=0). -/
def normalDirection : Derivation ℤ Ambient Ambient :=
  (ι n)⁻¹ • ambientPartial

theorem normalDirection_equation : normalDirection (ι f) = 1 := by
  simp only [normalDirection, Derivation.smul_apply, smul_eq_mul, ambientPartial_polynomial]
  exact inv_mul_cancel₀ n_ambient_ne

theorem normalDirection_free (i : Fin 3) :
    normalDirection (ι (X i.succ)) = 0 := by
  simp only [normalDirection, Derivation.smul_apply, smul_eq_mul, ambientPartial_polynomial, normal,
    pderiv_X_of_ne (Fin.succ_ne_zero i), map_zero, mul_zero]

/-- The coefficient of the wedge of free coordinate forms in the rational two-pole correction. -/
def sourceCorrection : Ambient := correction normalDirection (ι f) (ι b / ι n)

abbrev NormalOpen := Localization.Away n

private def unitOf (F : Type*) [Field F] (h : PolynomialRing →+* F)
    (hn : h n ≠ 0) : NormalOpen →+* F :=
  Localization.awayLift h n (isUnit_iff_ne_zero.mpr hn)

private theorem unitOf_apply (F : Type*) [Field F] (h : PolynomialRing →+* F)
    (hn : h n ≠ 0) (p : PolynomialRing) (k : ℕ) :
    unitOf F h hn (Localization.mk p ⟨n^k, k, rfl⟩) = h p / (h n)^k := by
  have he : h n * (h n)⁻¹ = 1 := mul_inv_cancel₀ hn
  change Localization.awayLift h n (isUnit_iff_exists_inv.mpr ⟨(h n)⁻¹, he⟩)
    (Localization.mk p ⟨n^k, k, rfl⟩) = _
  rw [Localization.awayLift_mk h n p _ he k, inv_pow, div_eq_mul_inv]

/-- The reduced coefficient, before division by the defining equation.
It is a function on the actual open on which the normal does not vanish. -/
def regularCoefficient : NormalOpen :=
  Localization.mk (sourceNumerator f) (⟨n^5, 5, rfl⟩ : Submonoid.powers n) *
    algebraMap PolynomialRing NormalOpen
      (MvPolynomial.C (MvPolynomial.C ((2 : ℂ)⁻¹)))

private theorem coefficient_scalar (T : Type*) [Field T]
    (h : PolynomialRing →+* T) (hn : h n ≠ 0) :
    unitOf T h hn regularCoefficient =
      (h (sourceNumerator f) / (h n)^5) / 2 := by
  unfold regularCoefficient
  rw [map_mul, unitOf_apply]
  let H : ℂ →+* T := h.comp ((MvPolynomial.C : Coeff →+* PolynomialRing).comp MvPolynomial.C)
  have hc : unitOf T h hn (algebraMap PolynomialRing NormalOpen
      (MvPolynomial.C (MvPolynomial.C ((2 : ℂ)⁻¹)))) = H ((2 : ℂ)⁻¹) :=
    IsLocalization.Away.lift_eq n (isUnit_iff_ne_zero.mpr hn) _
  rw [hc, map_inv₀, map_ofNat, div_eq_mul_inv (h (sourceNumerator f) / (h n)^5)]

private theorem coefficient_eq_density (T : Type*) [Field T] [CharZero T]
    (h : PolynomialRing →+* T) (hn : h n ≠ 0) :
    unitOf T h hn regularCoefficient = density h f := by
  rw [coefficient_scalar]
  unfold density sourceNumerator SplitHigherResidue.normalSourceTwo
  simp only [map_add, map_sub, map_mul, map_pow, map_ofNat]
  field_simp

/-- The normal-open evaluations in the ambient and hypersurface fields. -/
def toAmbient : NormalOpen →+* Ambient := unitOf Ambient ι n_ambient_ne

def toFiber : NormalOpen →+* W := unitOf W v universal_normal_ne_zero

theorem regularCoefficient_fiber : toFiber regularCoefficient = density v f :=
  coefficient_eq_density W v universal_normal_ne_zero

private theorem regularCoefficient_ambient :
    toAmbient regularCoefficient = normalDirection (normalDirection (ι b / ι n)) / 2 := by
  have hc := coefficient_eq_density Ambient ι n_ambient_ne
  have he := second_coefficient ambientPartial (ι n) (ι b) n_ambient_ne
  exact hc.trans (by
    unfold density at ⊢
    simp only [ambientPartial_polynomial] at he
    exact he.symm)

/-- The coefficient identity for the actual pole-three numerator. After
subtracting the specified exact normal derivative, the only pole is
simple and its coefficient is regular on the original normal open. -/
theorem pole_three_reduction :
    (ι b / ι n) / (ι f)^3 =
      normalDirection sourceCorrection + toAmbient regularCoefficient / ι f := by
  rw [regularCoefficient_ambient]
  exact reduce normalDirection (ι f) (ι b / ι n) f_ambient_ne normalDirection_equation

end CycleQ2WeightedPoleThree

#print axioms CycleQ2WeightedPoleThree.pole_three_reduction
#print axioms CycleQ2WeightedPoleThree.regularCoefficient_fiber
