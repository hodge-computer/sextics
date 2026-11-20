import Proposal.GeometricUniversalWeightedDeRham
import Proposal.GeometricExteriorSheaf
import HodgeComputer.Constructions.HoldoutCover.FiniteDifferentials
import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Pole-three reduction for the actual weighted source

The normal derivation differentiates the chart equation to one.
Subtracting the specified rational differential reduces the source
from a triple pole to a simple pole. Its coefficient is regular when
the normal derivative of the equation is invertible, and evaluates
on the hypersurface to the existing source density. The ordinary affine\nKähler map then transports local exterior boundaries to the universal\nfunction field.

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

section Exterior

abbrev AmbientOne := Ω[Ambient⁄Coeff]
abbrev AmbientFour := ⋀[Ambient]^4 AmbientOne

private abbrev dA := KaehlerDifferential.D Coeff Ambient
private abbrev acoord (i : Fin 4) : AmbientOne := dA (ι (X i))

/-- Inserting a one-form before the three exact free coordinate forms. -/
def freeWedge : AmbientOne →ₗ[Ambient] AmbientFour :=
  (exteriorPower.ιMulti Ambient 4).toMultilinearMap.toLinearMap acoord 0

private theorem freeWedge_apply (ω : AmbientOne) :
    freeWedge ω = exteriorPower.ιMulti Ambient 4 (Fin.cons ω (fun j => acoord j.succ)) := by
  classical
  change exteriorPower.ιMulti Ambient 4 (Function.update acoord 0 ω) = _
  apply congrArg (exteriorPower.ιMulti Ambient 4)
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp
  · simp [Fin.succ_ne_zero]

/-- The ordered coordinate volume on the ambient affine chart. -/
def ambientVolume : AmbientFour := exteriorPower.ιMulti Ambient 4 acoord

private theorem freeWedge_coordinate (i : Fin 4) :
    freeWedge (acoord i) = ambientPartial (ι (X i)) • ambientVolume := by
  refine Fin.cases ?_ (fun j => ?_) i
  · rw [ambientPartial_polynomial, normal, pderiv_X_self, map_one, one_smul]
    change exteriorPower.ιMulti Ambient 4 (Function.update acoord 0 (acoord 0)) = _
    exact congrArg (exteriorPower.ιMulti Ambient 4) (Function.update_eq_self 0 acoord)
  · have hzero := (exteriorPower.ιMulti Ambient 4).map_eq_zero_of_eq
      (Fin.cons (acoord j.succ) fun k => acoord k.succ)
      (i := 0) (j := j.succ) (by simp) (Fin.succ_ne_zero j).symm
    rw [freeWedge_apply, hzero, ambientPartial_polynomial, normal,
      pderiv_X_of_ne (Fin.succ_ne_zero j), map_zero, zero_smul]

private theorem freeWedge_polynomial (p : PolynomialRing) :
    freeWedge (dA (ι p)) = ambientPartial (ι p) • ambientVolume := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    have h : ι (MvPolynomial.C a) = algebraMap Coeff Ambient a :=
      (IsScalarTower.algebraMap_apply Coeff PolynomialRing Ambient a).symm
    rw [h, dA.map_algebraMap, map_zero]
    rw [← h, ambientPartial_polynomial, normal, pderiv_C, map_zero, zero_smul]
  | add p q hp hq =>
    simp only [map_add, add_smul, hp, hq]
  | mul_X p j hp =>
    have hq := freeWedge_coordinate j
    simp only [map_mul, Derivation.leibniz, map_add, map_smul, hp, hq,
      smul_eq_mul, smul_smul, add_smul]

/-- The exterior derivative of a coefficient times the wedge of the
three free exact forms has just the normal partial as its coefficient. -/
theorem freeWedge_exact (a : Ambient) :
    freeWedge (dA a) = ambientPartial a • ambientVolume := by
  obtain ⟨p, q, _, h⟩ := IsFractionRing.div_surjective PolynomialRing a
  change ι p / ι q = a at h
  rw [← h, Derivation.leibniz_div, Derivation.leibniz_div]
  simp only [map_sub, map_smul, freeWedge_polynomial, smul_eq_mul,
    smul_smul]
  rw [← sub_smul, smul_smul]

/-- The two meromorphic four-forms in the pole reduction. -/
def poleThreeForm : AmbientFour := (ι b / (ι f)^3) • ambientVolume

def simplePoleForm : AmbientFour := (toAmbient regularCoefficient / ι f) • freeWedge (dA (ι f))

/-- The rational four-form changes by the exterior derivative of the
specified scalar times the wedge of the free coordinate differentials. -/
theorem pole_three_form_reduction :
    poleThreeForm = freeWedge (dA sourceCorrection) + simplePoleForm := by
  have h := congrArg (fun c : Ambient => c * ι n) pole_three_reduction
  have hL : ((ι b / ι n) / (ι f)^3) * ι n = ι b / (ι f)^3 := by
    simp only [div_eq_mul_inv]
    calc
      ι b * (ι n)⁻¹ * ((ι f)^3)⁻¹ * ι n =
          ι b * ((ι f)^3)⁻¹ * ((ι n)⁻¹ * ι n) := by ring
      _ = _ := by rw [inv_mul_cancel₀ n_ambient_ne, mul_one]
  have hN : normalDirection sourceCorrection * ι n = ambientPartial sourceCorrection := by
    simp only [normalDirection, Derivation.smul_apply, smul_eq_mul]
    rw [mul_comm (ι n)⁻¹, mul_assoc, inv_mul_cancel₀ n_ambient_ne, mul_one]
  rw [hL, add_mul, hN] at h
  unfold poleThreeForm simplePoleForm
  rw [freeWedge_exact, freeWedge_exact, ambientPartial_polynomial, smul_smul, ← add_smul, h]

open CycleQ2UniversalWeightedDeRham
open CycleQ2WeightedCoordinateExterior (Form volume)

def simplePoleResidue : Form K W 3 :=
  toFiber regularCoefficient •
    exteriorPower.ιMulti W 3 (KaehlerDifferential.D K W ∘ coordinate)

theorem simplePoleResidue_eq_source : simplePoleResidue = sourceForm := by
  unfold simplePoleResidue sourceForm volume
  rw [regularCoefficient_fiber]
  apply congrArg (fun x : Form K W 3 => density v f • x)
  apply congrArg (exteriorPower.ιMulti W 3)
  funext i
  exact (coordinateBasis_apply i).symm

end Exterior

end CycleQ2WeightedPoleThree

#print axioms CycleQ2WeightedPoleThree.pole_three_reduction
#print axioms CycleQ2WeightedPoleThree.regularCoefficient_fiber
#print axioms CycleQ2WeightedPoleThree.pole_three_form_reduction
#print axioms CycleQ2WeightedPoleThree.simplePoleResidue_eq_source

namespace CycleQ2WeightedRationalRestriction

open CycleQ2UniversalWeightedDeRham
open CycleQ2WeightedCoordinateExterior (Form)
open CycleQ2GeometricExteriorSheaf (exteriorMap exteriorMap_wedge)

variable {A : Type} [CommRing A] [Algebra K A] (φ : A →ₐ[K] W)

private abbrev AffineForm (n : ℕ) := ⋀[A]^n Ω[A⁄K]

local notation "dA" => KaehlerDifferential.D K A
local notation "dW" => KaehlerDifferential.D K W

/-- The ordinary affine Kähler map with its given evaluation on coefficients. -/
def oneForm : Ω[A⁄K] →ₛₗ[φ.toRingHom] Ω[W⁄K] := by
  letI : Algebra A W := φ.toRingHom.toAlgebra
  letI : IsScalarTower K A W := IsScalarTower.of_algHom φ
  let l := KaehlerDifferential.map K K A W
  exact
    { toFun := l
      map_add' := l.map_add
      map_smul' := by
        intro a x
        exact (l.map_smul a x).trans (IsScalarTower.algebraMap_smul W a (l x)).symm }

theorem oneForm_d (a : A) : oneForm φ (dA a) = dW (φ a) := by
  let _ : Algebra A W := φ.toRingHom.toAlgebra
  let _ : IsScalarTower K A W := IsScalarTower.of_algHom φ
  exact KaehlerDifferential.map_D K K A W a

def evaluate (n : ℕ) : AffineForm (A := A) n →ₛₗ[φ.toRingHom] Form K W n :=
  exteriorMap φ.toRingHom (oneForm φ) n

theorem evaluate_wedge (n : ℕ) (a : Fin n → A) :
    evaluate φ n (exteriorPower.ιMulti A n (dA ∘ a)) =
      exteriorPower.ιMulti W n (dW ∘ (φ ∘ a)) := by
  rw [evaluate, exteriorMap_wedge]
  apply congrArg (exteriorPower.ιMulti W n)
  funext i
  exact oneForm_d φ (a i)

variable (δ : AffineForm (A := A) 2 →+ AffineForm (A := A) 3)

def ExactWedgeRule : Prop :=
  ∀ a b c : A, δ (a • exteriorPower.ιMulti A 2 (fun i => dA (![b,c] i))) =
    exteriorPower.ιMulti A 3 (fun i => dA (![a,b,c] i))

variable (hδ : ExactWedgeRule δ)

set_option maxHeartbeats 8000000 in
include hδ in
/-- Exterior differentiation commutes with restriction to the generic point
as soon as the source derivative has the ordinary exact-wedge rule. -/
theorem evaluate_d (η : AffineForm (A := A) 2) :
    exteriorDerivative (evaluate φ 2 η) = evaluate φ 3 (δ η) := by
  let S : Set (AffineForm (A := A) 2) :=
    exteriorPower.ιMulti A 2 '' {v : Fin 2 → Ω[A⁄K] | Set.range v ⊆ Set.range dA}
  have hS : Submodule.span A S = ⊤ :=
    exteriorPower.ιMulti_span_of_span A 2 Ω[A⁄K] (KaehlerDifferential.span_range_derivation K A)
  have hη : η ∈ Submodule.span A S := hS.symm ▸ Submodule.mem_top
  have he (ω : AffineForm (A := A) 2) (hω : ω ∈ Submodule.span A S) (a : A) :
      exteriorDerivative (evaluate φ 2 (a • ω)) = evaluate φ 3 (δ (a • ω)) := by
    induction hω using Submodule.span_induction generalizing a with
    | mem x hx =>
      obtain ⟨v,hv,rfl⟩ := hx
      obtain ⟨b,hb⟩ := hv (Set.mem_range_self 0)
      obtain ⟨c,hc⟩ := hv (Set.mem_range_self 1)
      have h : v = dA ∘ ![b,c] := by
        funext i
        fin_cases i
        · exact hb.symm
        · exact hc.symm
      have hd : δ (a • exteriorPower.ιMulti A 2 (dA ∘ ![b,c])) =
          exteriorPower.ιMulti A 3 (dA ∘ ![a,b,c]) := hδ a b c
      rw [h]
      refine Eq.trans ?_ (congrArg (evaluate φ 3) hd).symm
      rw [map_smulₛₗ, evaluate_wedge, evaluate_wedge]
      have hB : (fun i : Fin 2 => φ (![b,c] i)) = ![φ b, φ c] := by
        funext i
        fin_cases i <;> rfl
      have hC : (fun i : Fin 3 => φ (![a,b,c] i)) = ![φ a, φ b, φ c] := by
        funext i
        fin_cases i <;> rfl
      change exteriorDerivative (φ a • exteriorPower.ιMulti W 2 (dW ∘
        (fun i : Fin 2 => φ (![b,c] i)))) =
          exteriorPower.ιMulti W 3 (dW ∘ (fun i : Fin 3 => φ (![a,b,c] i)))
      rw [hB, hC]
      exact exteriorDerivative_exact_pair (φ a) (φ b) (φ c)
    | zero => simp only [smul_zero, map_zero]
    | add x y _ _ hx hy => simp only [smul_add, map_add, hx, hy]
    | smul r x _ hx =>
      rw [smul_smul]
      exact hx (a * r)
  simpa only [one_smul] using he η hη 1

include hδ in
/-- Exactness of the specified source on any affine restriction certifies
exactness of the protected four-form through the universal field. -/
theorem protected_exact_of_affine_boundary (ω : AffineForm (A := A) 3)
    (hω : evaluate φ 3 ω = sourceForm) (η : AffineForm (A := A) 2) (hη : δ η = ω) :
    ∃ η : CycleQ2AffineExterior.Form 3, CycleQ2AffineExterior.exteriorD3 η =
      CycleQ2AffineExactness.residueSourceForm CycleQ2AffineClearing.affineA :=
  protected_exact_of_source_exact
    ⟨evaluate φ 2 η, (evaluate_d φ δ hδ η).trans
      ((congrArg (evaluate φ 3) hη).trans hω)⟩

end CycleQ2WeightedRationalRestriction

#print axioms CycleQ2WeightedRationalRestriction.protected_exact_of_affine_boundary
#print axioms CycleQ2WeightedRationalRestriction.ExactWedgeRule
