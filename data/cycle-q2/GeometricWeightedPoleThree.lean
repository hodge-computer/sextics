import Proposal.GeometricUniversalWeightedDeRham
import Proposal.GeometricExteriorSheaf
import HodgeComputer.Constructions.HoldoutCover.FiniteDifferentials
import HodgeComputer.Constructions.HoldoutCover.PolynomialCalculus
import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Pole-three reduction for the actual weighted source

The normal derivation differentiates the chart equation to one.
For arbitrary pole order, coefficient differentiation commutes with the
normal residue rule and preserves rational exterior boundaries.
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

namespace CycleQ2WeightedPoleJets

section Algebra
variable {A : Type*} [Field A] [CharZero A] (f : A) (dx δ : Derivation ℤ A A)

/-- Differentiation in the equation, with all free coordinates held fixed. -/
private abbrev N := (dx f)⁻¹ • dx
/-- Infinitesimal change of parameters at fixed value of the equation. -/
def tangent := δ - δ f • N f dx

omit [CharZero A] in
private theorem N_apply (u : A) : N f dx u = dx u / dx f := by
  rw [Derivation.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]

omit [CharZero A] in
theorem tangent_apply (u : A) : tangent f dx δ u = δ u - δ f * (dx u / dx f) := by
  simp only [tangent, Derivation.sub_apply, Derivation.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm (dx u)]

omit [CharZero A] in
theorem commutes (hn : dx f ≠ 0) (h : Function.Commute δ dx) :
    Function.Commute (tangent f dx δ) (N f dx) := by
  intro u
  simp only [tangent_apply,N_apply,Derivation.leibniz_div,map_sub,Derivation.leibniz,
    smul_eq_mul,h f,h u]
  field_simp
  ring

omit [CharZero A] in
private theorem tangent_density (hn : dx f ≠ 0) (h : Function.Commute δ dx) (u : A) :
    tangent f dx δ (u / dx f) = δ u / dx f - N f dx (δ f * u / dx f) := by
  simp only [tangent_apply,N_apply,Derivation.leibniz_div,Derivation.leibniz,
    smul_eq_mul,h f]
  field_simp
  ring

omit [CharZero A] in
private theorem iterate_sub (d : Derivation ℤ A A) (k : ℕ) (x y : A) :
    d^[k] (x-y) = d^[k] x - d^[k] y := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [Function.iterate_succ_apply',ih,map_sub]

/-- The iterated normal residue coefficient before factorial normalization. -/
def jet (k : ℕ) (u : A) : A := (N f dx)^[k] (u / dx f)

omit [CharZero A] in
theorem tangent_jet (hn : dx f ≠ 0) (h : Function.Commute δ dx) (k : ℕ) (u : A) :
    tangent f dx δ (jet f dx k u) =
      jet f dx k (δ u) - jet f dx (k+1) (δ f * u) := by
  unfold jet
  rw [(commutes f dx δ hn h).iterate_right k (u / dx f),tangent_density f dx δ hn h,
    iterate_sub,Function.iterate_succ_apply]

/-- The simple-pole coefficient coming from a pole of order k+1. -/
def residue (k : ℕ) (u : A) : A := jet f dx k u / k.factorial

theorem tangent_residue (hn : dx f ≠ 0) (h : Function.Commute δ dx) (k : ℕ) (u : A) :
    tangent f dx δ (residue f dx k u) =
      residue f dx k (δ u) - ((k+1:ℕ):A) * residue f dx (k+1) (δ f * u) := by
  simp only [residue,Derivation.leibniz_div,Derivation.map_natCast,smul_eq_mul,mul_zero,sub_zero,
    tangent_jet f dx δ hn h,Nat.factorial_succ,Nat.cast_mul]
  have hn' : (k.factorial : A) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  have hs : ((k+1 : ℕ) : A) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero k)
  field_simp
end Algebra

section Chart
open MvPolynomial
open CycleQ2MonicWeightedAffineEquation (Coeff)
open CycleQ2GenericWeightedSpatialDenominator (universalAffine)
open CycleQ2MonicWeightedPrimitiveIdentity (normal b density)
open CycleQ2MonicWeightedPrimitiveSpecialization (projection projection_kernel projection_surjective fieldValue direction)
open CycleQ2UniversalWeightedTransfer (universal_normal_ne_zero)
open CycleQ2WeightedPoleThree (PolynomialRing Ambient W ambientPartial normalDirection)

local instance : Algebra ℤ PolynomialRing := Ring.toIntAlgebra _
local instance : Algebra ℤ Ambient := Ring.toIntAlgebra _
local instance : Algebra ℤ W := Ring.toIntAlgebra _

private abbrev F := universalAffine
private abbrev n := normal F
private abbrev v := fieldValue F
private abbrev ι := algebraMap PolynomialRing Ambient
private abbrev dx := HoldoutConstruction.integerPartial (R := Coeff) (0 : Fin 4)

private theorem hnAmbient : ι n ≠ 0 := by
  intro h
  have hz : n = 0 := (IsFractionRing.injective PolynomialRing Ambient) (h.trans (map_zero ι).symm)
  exact universal_normal_ne_zero ((congrArg v hz).trans v.map_zero)

private abbrev ambientLift (Δ : Derivation ℤ PolynomialRing PolynomialRing) :=
  HoldoutConstruction.extendRingDerivation (L := Ambient) Δ

/-- The ambient parameter derivative at fixed value of the actual weighted equation. -/
def ambientTangent (Δ : Derivation ℤ PolynomialRing PolynomialRing) : Derivation ℤ Ambient Ambient :=
  tangent (ι F) ambientPartial (ambientLift Δ)

private theorem ambientDx (p : PolynomialRing) : ambientPartial (ι p) = ι (dx p) :=
  HoldoutConstruction.extendRingDerivation_apply (L := Ambient) dx p

theorem ambient_commutes (Δ : Derivation ℤ PolynomialRing PolynomialRing) (h : Function.Commute Δ dx) :
    Function.Commute (ambientTangent Δ) normalDirection := by
  have hn : ambientPartial (ι F) ≠ 0 := (ambientDx F).symm ▸ hnAmbient
  have he : N (ι F) ambientPartial = normalDirection := by
    unfold N normalDirection
    rw [ambientDx]
    rfl
  rw [← he]
  exact commutes _ _ _ hn (HoldoutConstruction.extendRingDerivation_commute Δ dx h)

/-- Quotient descent of a parameter or coordinate tangent to the actual hypersurface field. -/
def fiberTangent (Δ : Derivation ℤ PolynomialRing PolynomialRing) : Derivation ℤ W W :=
  HoldoutConstruction.residueTangent (projection F) (projection_surjective F) dx Δ F
    (projection_kernel F) universal_normal_ne_zero

private theorem fiberTangent_poly (Δ : Derivation ℤ PolynomialRing PolynomialRing) (p : PolynomialRing) :
    fiberTangent Δ (v p) = v (Δ p) - v (Δ F) / v n * v (dx p) :=
  HoldoutConstruction.residueTangent_apply _ _ dx Δ F _ _ p

private theorem ambientTangent_poly (Δ : Derivation ℤ PolynomialRing PolynomialRing) (p : PolynomialRing) :
    ambientTangent Δ (ι p) = ι (Δ p) - ι (Δ F) / ι n * ι (dx p) := by
  rw [ambientTangent,tangent_apply,ambientDx,ambientDx]
  simp only [ambientLift,HoldoutConstruction.extendRingDerivation_apply,div_eq_mul_inv]
  change _ - _ * (_ * (ι n)⁻¹) = _
  ring

/-- A polynomial numerator divided by a power of the chart normal. -/
private structure Fraction where
  num : PolynomialRing
  power : ℕ

private def atField {L : Type*} [Field L] (φ : PolynomialRing →+* L) (a : Fraction) : L :=
  φ a.num / (φ n)^a.power

private def minus (a b : Fraction) : Fraction :=
  ⟨a.num * n^b.power - b.num * n^a.power, a.power + b.power⟩

private theorem minus_at {L : Type*} [Field L] (φ : PolynomialRing →+* L) (hn : φ n ≠ 0) (a b : Fraction) :
    atField φ (minus a b) = atField φ a - atField φ b := by
  simp only [atField,minus,map_sub,map_mul,map_pow,pow_add]
  field_simp

private theorem specialize {a b : Fraction} (h : atField ι a = atField ι b) :
    atField v a = atField v b := by
  have e := (div_eq_div_iff (pow_ne_zero a.power hnAmbient) (pow_ne_zero b.power hnAmbient)).mp h
  have ep : a.num * n^b.power = b.num * n^a.power := (IsFractionRing.injective PolynomialRing Ambient)
    (by simpa only [map_mul,map_pow] using e)
  apply (div_eq_div_iff (pow_ne_zero a.power universal_normal_ne_zero) (pow_ne_zero b.power universal_normal_ne_zero)).mpr
  simpa only [map_mul,map_pow] using congrArg v ep

private def normalStep (a : Fraction) : Fraction :=
  ⟨n * dx a.num - a.power * a.num * dx n, a.power+2⟩

private def tangentStep (Δ : Derivation ℤ PolynomialRing PolynomialRing) (a : Fraction) : Fraction :=
  let T := fun g => n * Δ g - Δ F * dx g
  ⟨n * T a.num - a.power * a.num * T n, a.power+2⟩

private theorem quotient_rule {L : Type*} [Field L] (d : Derivation ℤ L L) (u v : L)
    (hv : v ≠ 0) (k : ℕ) :
    d (u/v^k) = (v*d u - k*u*d v)/v^(k+1) := by
  induction k with
  | zero => simp [hv]
  | succ k ih =>
    rw [pow_succ v k,← div_div,Derivation.leibniz_div,ih]
    simp only [smul_eq_mul,Nat.cast_succ,pow_succ]
    field_simp
    ring

private theorem normalStep_at (a : Fraction) :
    atField ι (normalStep a) = normalDirection (atField ι a) := by
  rw [normalDirection,Derivation.smul_apply,smul_eq_mul,atField,atField,
    quotient_rule ambientPartial _ _ hnAmbient]
  simp only [normalStep,map_sub,map_mul,map_natCast,ambientDx]
  rw [pow_succ (ι n) (a.power+1)]
  ring

private theorem tangentStep_at {L : Type*} [Field L] (φ : PolynomialRing →+* L) (hn : φ n ≠ 0)
    (Δ : Derivation ℤ PolynomialRing PolynomialRing) (d : Derivation ℤ L L)
    (hp : ∀ p, d (φ p) = φ (Δ p) - φ (Δ F) / φ n * φ (dx p)) (a : Fraction) :
    atField φ (tangentStep Δ a) = d (atField φ a) := by
  simp only [atField,tangentStep,map_sub,map_mul,map_natCast,quotient_rule d _ _ hn,hp]
  simp only [pow_succ]
  field_simp

private def normalFraction (k : ℕ) (p : PolynomialRing) : Fraction := normalStep^[k] ⟨p,1⟩

private theorem normalFraction_at (k : ℕ) (p : PolynomialRing) :
    atField ι (normalFraction k p) = jet (ι F) ambientPartial k (ι p) := by
  have h : N (ι F) ambientPartial = normalDirection := by
    unfold N normalDirection
    rw [ambientDx]
    rfl
  unfold jet
  rw [h]
  induction k with
  | zero => simp [atField,normalFraction,ambientDx,normal]
  | succ k ih => change atField ι (normalStep^[k+1] _) = _
                 rw [Function.iterate_succ_apply',Function.iterate_succ_apply',normalStep_at]
                 exact congrArg normalDirection ih

/-- The actual field residue coming from an affine numerator and pole of order k+1. -/
def fiberResidue (k : ℕ) (p : PolynomialRing) : W := atField v (normalFraction k p) / k.factorial

theorem fiberTangent_residue (Δ : Derivation ℤ PolynomialRing PolynomialRing) (h : Function.Commute Δ dx)
    (k : ℕ) (p : PolynomialRing) :
    fiberTangent Δ (fiberResidue k p) = fiberResidue k (Δ p) - ((k+1:ℕ):W) * fiberResidue (k+1) (Δ F*p) := by
  have hn : ambientPartial (ι F) ≠ 0 := (ambientDx F).symm ▸ hnAmbient
  have heA : atField ι (tangentStep Δ (normalFraction k p)) =
      atField ι (minus (normalFraction k (Δ p)) (normalFraction (k+1) (Δ F*p))) := by
    rw [tangentStep_at ι hnAmbient Δ (ambientTangent Δ) (ambientTangent_poly Δ),minus_at ι hnAmbient]
    simp only [normalFraction_at,ambientTangent,map_mul]
    simpa only [ambientLift,HoldoutConstruction.extendRingDerivation_apply,map_mul] using
      tangent_jet (ι F) ambientPartial (ambientLift Δ) hn
        (HoldoutConstruction.extendRingDerivation_commute Δ dx h) k (ι p)
  have he := specialize heA
  rw [tangentStep_at v universal_normal_ne_zero Δ (fiberTangent Δ) (fiberTangent_poly Δ),
    minus_at v universal_normal_ne_zero] at he
  simp only [fiberResidue,Derivation.leibniz_div,Derivation.map_natCast,smul_eq_mul,mul_zero,sub_zero,he,
    Nat.factorial_succ,Nat.cast_mul]
  have hk : (k.factorial : W) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  have hs : ((k+1:ℕ):W) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero k)
  field_simp

open CycleQ2IncidenceNormalForm (FullSexticTailIndex normalizedFullSextic)
open CycleQ2PolynomialCoefficientDerivation (coefficientDerivation coefficientDerivation_C
  coefficientDerivation_X coefficientDerivation_monomial)
open CycleQ2MonicWeightedAffineEquation (chart)

/-- The literal partial derivative in one coefficient of the monic family; it fixes all four chart variables. -/
abbrev coefficientPartial (e : FullSexticTailIndex) : Derivation ℤ PolynomialRing PolynomialRing :=
  coefficientDerivation (HoldoutConstruction.integerPartial (R := ℂ) e)

private theorem coefficient_commutes (e : FullSexticTailIndex) (i : Fin 4) :
    Function.Commute (coefficientPartial e) (HoldoutConstruction.integerPartial i) := by
  let D := coefficientPartial e
  let E : Derivation ℤ PolynomialRing PolynomialRing := HoldoutConstruction.integerPartial i
  intro p
  change D (E p) = E (D p)
  induction p using MvPolynomial.induction_on with
  | C a =>
    change D ((pderiv i) (C a)) = (pderiv i) (coefficientDerivation _ (C a))
    rw [pderiv_C,map_zero,coefficientDerivation_C,pderiv_C]
  | add p q hp hq => rw [map_add,map_add,map_add,map_add,hp,hq]
  | mul_X p j hp =>
    have hX : D (X j) = 0 := coefficientDerivation_X _ _
    have hE : D (E (X j)) = 0 := by
      change D ((pderiv i) (X j)) = _
      by_cases h : j = i
      · subst j; rw [pderiv_X_self,Derivation.map_one_eq_zero]
      · rw [pderiv_X_of_ne h,map_zero]
    simp only [Derivation.leibniz,smul_eq_mul,map_add,hX,hE,mul_zero,add_zero,zero_add,hp]
    ring

private theorem coefficient_chart (e : FullSexticTailIndex) (p : MvPolynomial (Fin 5) Coeff) :
    coefficientPartial e (chart p) =
      chart (coefficientDerivation (HoldoutConstruction.integerPartial (R := ℂ) e) p) := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    simp only [chart,aeval_C,coefficientPartial,coefficientDerivation_C]
    exact coefficientDerivation_C (σ := Fin 4) _ _
  | add p q hp hq => rw [map_add,map_add,map_add,map_add,hp,hq]
  | mul_X p j hp =>
    have hz : coefficientPartial e (chart (X j)) = 0 := by
      refine Fin.cases ?_ (fun j => ?_) j
      · rw [show chart (X (0:Fin 5) : MvPolynomial (Fin 5) Coeff) = 1 by simp [chart], Derivation.map_one_eq_zero]
      · rw [show chart (X j.succ : MvPolynomial (Fin 5) Coeff) = X j by simp [chart]]
        exact coefficientDerivation_X _ _
    simp only [map_mul,Derivation.leibniz,smul_eq_mul,coefficientDerivation_X,
      hz,mul_zero,zero_add,hp]

/-- The velocity of the displayed monic chart equation is the chosen dehomogenized sextic monomial. -/
theorem coefficient_equation (e : FullSexticTailIndex) :
    coefficientPartial e F = chart (monomial (CycleQ2IncidenceNormalForm.fullExponentOf e.val.val) 1) := by
  classical
  change coefficientPartial e (chart _) = _
  rw [coefficient_chart]
  congr 1
  simp only [normalizedFullSextic,map_add,map_sum,coefficientDerivation_monomial,
    Derivation.map_one_eq_zero,map_zero,zero_add]
  rw [Finset.sum_eq_single e]
  · rw [HoldoutConstruction.integerPartial_X_self]
  · intro j _ hje
    rw [HoldoutConstruction.integerPartial_X_of_ne _ _ hje,map_zero]
  · simp

theorem coefficient_residue (e : FullSexticTailIndex) (k : ℕ) (p : PolynomialRing) :
    fiberTangent (coefficientPartial e) (fiberResidue k p) =
      fiberResidue k (coefficientPartial e p) -
        ((k+1:ℕ):W)*fiberResidue (k+1) (chart (monomial
          (CycleQ2IncidenceNormalForm.fullExponentOf e.val.val) 1)*p) := by
  rw [← coefficient_equation]
  exact fiberTangent_residue _ (coefficient_commutes e 0) k p

/-- On the hypersurface, the two homogeneous pole terms differ by the actual spatial derivative. -/
theorem spatial_residue (j : Fin 3) (k : ℕ) (p : PolynomialRing) :
    direction F universal_normal_ne_zero j (fiberResidue k p) =
      fiberResidue k (pderiv j.succ p) - ((k+1:ℕ):W) * fiberResidue (k+1) (pderiv j.succ F * p) :=
  fiberTangent_residue (HoldoutConstruction.integerPartial j.succ)
    (HoldoutConstruction.integerPartials_commute j.succ 0) k p

/-- The two normal derivatives at the protected pole give the original rational source density. -/
theorem fiberResidue_two : fiberResidue 2 b = density v F := by
  unfold fiberResidue
  rw [show normalFraction 2 b = normalStep (normalStep ⟨b,1⟩) from rfl]
  simp only [atField,normalStep,density]
  change _ = SplitHigherResidue.normalSourceTwo (v b) (v (dx b)) (v (dx (dx b)))
      (v n) (v (dx n)) (v (dx (dx n))) / v n
  norm_num only [Nat.factorial_succ,Nat.factorial_zero,Nat.cast_one,Nat.cast_ofNat,
    Nat.reduceAdd,Nat.reduceMul,Nat.cast_mul,mul_one]
  simp only [one_mul,map_sub,Derivation.leibniz,smul_eq_mul,map_mul,map_add,map_ofNat,
    SplitHigherResidue.normalSourceTwo]
  field_simp [universal_normal_ne_zero]
  ring

/-- A numerator derivative in the normal variable has no residual divergence term. -/
theorem normal_residue (k : ℕ) (p : PolynomialRing) :
    fiberResidue k (normal p) = ((k+1:ℕ):W) * fiberResidue (k+1) (n*p) := by
  have hz : fiberTangent dx = 0 := by
    apply HoldoutConstruction.FieldValuedFraction.derivation_ext (P := CycleQ2MonicWeightedPrimitiveSpecialization.ChartRing F)
    intro a
    obtain ⟨q,rfl⟩ := projection_surjective F a
    change fiberTangent dx (v q) = 0
    refine (fiberTangent_poly dx q).trans ?_
    have hz' (a z : W) (hn : z ≠ 0) : a-z/z*a=0 := by rw [div_self hn,one_mul,sub_self]
    exact hz' (v (dx q)) (v n) universal_normal_ne_zero
  have e := fiberTangent_residue dx (Function.Commute.refl _) k p
  rw [hz] at e
  exact sub_eq_zero.mp e.symm

private def times (c : PolynomialRing) (a : Fraction) : Fraction := ⟨c*a.num,a.power⟩

private theorem times_at {L : Type*} [Field L] (φ : PolynomialRing →+* L) (c : PolynomialRing) (a : Fraction) :
    atField φ (times c a) = φ c * atField φ a := by simp only [atField,times,map_mul,mul_div_assoc]

private theorem product_derivative {L : Type*} [Field L] (d : Derivation ℤ L L) (x u : L) (hx : d x = 1) (k : ℕ) :
    d^[k+1] (x*u) = x*d^[k+1] u + ((k+1:ℕ):L)*d^[k] u := by
  induction k with
  | zero =>
    simp [Derivation.leibniz,hx]
  | succ k ih =>
    have hd : d ((k+1:ℕ):L) = 0 := d.map_natCast _
    have h₁ : d (d^[k] u) = d^[k+1] u := (Function.iterate_succ_apply' _ _ _).symm
    have h₂ : d (d^[k+1] u) = d^[(k+1)+1] u := (Function.iterate_succ_apply' _ _ _).symm
    rw [Function.iterate_succ_apply' _ (k+1) (x*u),ih,map_add,Derivation.leibniz,Derivation.leibniz]
    simp only [hx,smul_eq_mul,hd,mul_zero,add_zero,mul_one,h₁,h₂]
    change _ = x*d^[(k+1)+1] u + (((k+1)+1:ℕ):L)*d^[k+1] u
    rw [show (((k+1)+1:ℕ):L) = ((k+1:ℕ):L)+1 from Nat.cast_succ _,add_mul,one_mul]
    abel

/-- Multiplying the numerator by the defining equation cancels a pole in the actual hypersurface field. -/
theorem cancel_equation (k : ℕ) (p : PolynomialRing) : fiberResidue (k+1) (F*p) = fiberResidue k p := by
  have hN : N (ι F) ambientPartial = normalDirection := by unfold N normalDirection; rw [ambientDx]; rfl
  have he : atField ι (minus (normalFraction (k+1) (F*p)) (times ((k+1:ℕ):PolynomialRing) (normalFraction k p))) =
      atField ι (times F (normalFraction (k+1) p)) := by
    rw [minus_at ι hnAmbient,times_at,times_at,normalFraction_at,normalFraction_at,normalFraction_at]
    simp only [map_mul,map_natCast,jet,hN,mul_div_assoc]
    rw [product_derivative normalDirection (ι F) _ CycleQ2WeightedPoleThree.normalDirection_equation]
    exact add_sub_cancel_right _ _
  have hF : v F = 0 := by
    change algebraMap (CycleQ2MonicWeightedPrimitiveSpecialization.ChartRing F) W (projection F F) = 0
    rw [(projection_kernel F F).mpr (dvd_refl F),map_zero]
  have h := specialize he
  rw [minus_at v universal_normal_ne_zero,times_at,times_at,map_natCast,hF,zero_mul] at h
  simp only [fiberResidue,sub_eq_zero.mp h,Nat.factorial_succ,Nat.cast_mul]
  have hk : ((k+1:ℕ):W) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero k)
  field_simp

theorem coefficient_commutes_spatial (e : FullSexticTailIndex) (j : Fin 3) :
    Function.Commute (fiberTangent (coefficientPartial e)) (direction F universal_normal_ne_zero j) :=
  HoldoutConstruction.residueTangent_commute (projection F) (projection_surjective F)
    dx (coefficientPartial e) (HoldoutConstruction.integerPartial j.succ) F (projection_kernel F)
    universal_normal_ne_zero (coefficient_commutes e 0) (HoldoutConstruction.integerPartials_commute _ 0)
    (coefficient_commutes e j.succ)

open CycleQ2UniversalWeightedDeRham (K coordinateBasis coordinateDerivation exteriorDerivative sourceForm)
open CycleQ2WeightedCoordinateExterior (Form volume exact_volume_iff_divergence)

theorem weighted_source : fiberResidue 2 b • volume coordinateBasis = sourceForm := by
  rw [fiberResidue_two]; rfl

/-- The spatial pole-reduction relation gives a genuine rational exterior boundary on the weighted threefold. -/
theorem spatial_exact (j : Fin 3) (k : ℕ) (p : PolynomialRing) :
    ∃ η : Form K W 2, exteriorDerivative η =
      (fiberResidue k (pderiv j.succ p) - ((k+1:ℕ):W) * fiberResidue (k+1) (pderiv j.succ F * p)) •
        volume coordinateBasis := by
  rw [← spatial_residue]
  apply (exact_volume_iff_divergence coordinateBasis coordinateDerivation _).mpr
  refine ⟨fun i => if i = j then fiberResidue k p else 0,?_⟩
  calc
    _ = coordinateDerivation j (if j = j then fiberResidue k p else 0) :=
      Finset.sum_eq_single j (fun i _ hij => by simp [hij]) (by simp)
    _ = _ := by rw [if_pos rfl]; rfl

/-- Every coefficient derivative takes a rationally exact density times the
three free-coordinate differentials to another exact rational three-form. -/
theorem coefficient_preserves_exact (e : FullSexticTailIndex) (u : W)
    (h : ∃ η : Form K W 2, exteriorDerivative η = u • volume coordinateBasis) :
    ∃ η : Form K W 2, exteriorDerivative η = fiberTangent (coefficientPartial e) u • volume coordinateBasis := by
  obtain ⟨w,hw⟩ := (exact_volume_iff_divergence coordinateBasis coordinateDerivation u).mp h
  let D := fiberTangent (coefficientPartial e)
  apply (exact_volume_iff_divergence coordinateBasis coordinateDerivation (D u)).mpr
  refine ⟨fun j => D (w j),?_⟩
  rw [← hw,map_sum]
  exact Finset.sum_congr rfl fun j _ => (coefficient_commutes_spatial e j (w j)).symm

end Chart
end CycleQ2WeightedPoleJets
#print axioms CycleQ2WeightedPoleJets.fiberTangent_residue

#print axioms CycleQ2WeightedPoleJets.coefficient_residue
#print axioms CycleQ2WeightedPoleJets.spatial_residue
#print axioms CycleQ2WeightedPoleJets.weighted_source
#print axioms CycleQ2WeightedPoleJets.coefficient_preserves_exact

#print axioms CycleQ2WeightedPoleJets.cancel_equation
