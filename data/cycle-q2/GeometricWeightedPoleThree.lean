import Proposal.GeometricUniversalWeightedDeRham
import Proposal.GeometricUniversalJacobianFrames
import Proposal.GeometricFermatPoleReduction
import Proposal.GeometricExteriorSheaf
import HodgeComputer.Constructions.HoldoutCover.FiniteDifferentials
import HodgeComputer.Constructions.HoldoutCover.PolynomialCalculus
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.Module

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

/-- The actual coefficient derivative commutes with dehomogenizing a polynomial numerator. -/
theorem coefficient_chart (e : FullSexticTailIndex) (p : MvPolynomial (Fin 5) Coeff) :
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

/-- Removing the normal component from the normal coordinate derivative gives zero on the fiber. -/
theorem fiberTangent_normal : fiberTangent dx = 0 := by
  apply HoldoutConstruction.FieldValuedFraction.derivation_ext (P := CycleQ2MonicWeightedPrimitiveSpecialization.ChartRing F)
  intro a
  obtain ⟨q,rfl⟩ := projection_surjective F a
  change fiberTangent dx (v q) = 0
  refine (fiberTangent_poly dx q).trans ?_
  have hz (a z : W) (hn : z ≠ 0) : a-z/z*a=0 := by rw [div_self hn,one_mul,sub_self]
  exact hz (v (dx q)) (v n) universal_normal_ne_zero

/-- A numerator derivative in the normal variable has no residual divergence term. -/
theorem normal_residue (k : ℕ) (p : PolynomialRing) :
    fiberResidue k (normal p) = ((k+1:ℕ):W) * fiberResidue (k+1) (n*p) := by
  have e := fiberTangent_residue dx (Function.Commute.refl _) k p
  rw [fiberTangent_normal] at e
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

/-- The actual residue with the factorial convention of polynomial pole symbols:
the summand indexed by `k` represents `k!` times a pole of order `k+1`. -/
def normalizedFiberResidue (k : ℕ) (p : PolynomialRing) : W :=
  atField v (normalFraction k p)

theorem normalizedFiberResidue_eq (k : ℕ) (p : PolynomialRing) :
    normalizedFiberResidue k p = (k.factorial : W) * fiberResidue k p := by
  have hk : (k.factorial : W) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  simp only [normalizedFiberResidue,fiberResidue]
  field_simp

theorem normalizedFiberResidue_sub (k : ℕ) (p q : PolynomialRing) :
    normalizedFiberResidue k (p-q) = normalizedFiberResidue k p - normalizedFiberResidue k q := by
  have h : atField ι (normalFraction k (p-q)) =
      atField ι (minus (normalFraction k p) (normalFraction k q)) := by
    rw [minus_at ι hnAmbient]
    simp only [normalFraction_at,jet,map_sub,sub_div,iterate_sub]
  exact (specialize h).trans (minus_at v universal_normal_ne_zero _ _)

@[simp] theorem normalizedFiberResidue_zero (k : ℕ) : normalizedFiberResidue k 0 = 0 := by
  simpa only [sub_self] using normalizedFiberResidue_sub k 0 0

theorem normalizedFiberResidue_add (k : ℕ) (p q : PolynomialRing) :
    normalizedFiberResidue k (p+q) = normalizedFiberResidue k p + normalizedFiberResidue k q := by
  have h := normalizedFiberResidue_sub k (p+q) q
  rw [add_sub_cancel_right] at h
  exact (eq_sub_iff_add_eq.mp h).symm

/-- Additivity takes place in the actual hypersurface field, before quotienting by boundaries. -/
def normalizedFiberResidueAdd (k : ℕ) : PolynomialRing →+ W where
  toFun := normalizedFiberResidue k
  map_zero' := normalizedFiberResidue_zero k
  map_add' := normalizedFiberResidue_add k

private theorem iterate_mul_constant {L : Type*} [Field L] (d : Derivation ℤ L L)
    (c u : L) (hc : d c = 0) (k : ℕ) : d^[k] (c*u) = c*d^[k] u := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply',ih,Derivation.leibniz]
    simp only [smul_eq_mul,hc,mul_zero,add_zero,Function.iterate_succ_apply']

/-- A factor constant in the chosen normal coordinate passes through every normalized residue. -/
theorem normalizedFiberResidue_mul_constant (k : ℕ) (c p : PolynomialRing) (hc : normal c = 0) :
    normalizedFiberResidue k (c*p) = v c * normalizedFiberResidue k p := by
  have hz : N (ι F) ambientPartial (ι c) = 0 := by
    rw [N_apply,ambientDx]
    change ι (normal c) / _ = 0
    rw [hc,map_zero,zero_div]
  have h : atField ι (normalFraction k (c*p)) =
      atField ι (times c (normalFraction k p)) := by
    simp only [times_at,normalFraction_at,jet,map_mul,mul_div_assoc]
    exact iterate_mul_constant _ _ _ hz k
  exact (specialize h).trans (times_at v c _)

theorem normalizedFiberResidue_C_mul (k : ℕ) (c : Coeff) (p : PolynomialRing) :
    normalizedFiberResidue k (C c*p) = v (C c) * normalizedFiberResidue k p :=
  normalizedFiberResidue_mul_constant k (C c) p (by simp only [normal,pderiv_C])

/-- Coefficient or coordinate differentiation has precisely the factorial-free
connection formula used by the normalized polynomial pole quotient. -/
theorem normalized_tangent_residue (Δ : Derivation ℤ PolynomialRing PolynomialRing)
    (h : Function.Commute Δ dx) (k : ℕ) (p : PolynomialRing) :
    fiberTangent Δ (normalizedFiberResidue k p) =
      normalizedFiberResidue k (Δ p) - normalizedFiberResidue (k+1) (Δ F*p) := by
  simp only [normalizedFiberResidue_eq,Derivation.leibniz,Derivation.map_natCast,
    smul_eq_mul,mul_zero,add_zero,fiberTangent_residue Δ h,Nat.factorial_succ,Nat.cast_mul]
  ring

theorem normalized_coefficient_residue (e : FullSexticTailIndex) (k : ℕ) (p : PolynomialRing) :
    fiberTangent (coefficientPartial e) (normalizedFiberResidue k p) =
      normalizedFiberResidue k (coefficientPartial e p) -
        normalizedFiberResidue (k+1) (chart (monomial
          (CycleQ2IncidenceNormalForm.fullExponentOf e.val.val) 1)*p) := by
  rw [← coefficient_equation]
  exact normalized_tangent_residue _ (coefficient_commutes e 0) k p

theorem normalized_spatial_residue (j : Fin 3) (k : ℕ) (p : PolynomialRing) :
    direction F universal_normal_ne_zero j (normalizedFiberResidue k p) =
      normalizedFiberResidue k (pderiv j.succ p) -
        normalizedFiberResidue (k+1) (pderiv j.succ F*p) :=
  normalized_tangent_residue (HoldoutConstruction.integerPartial j.succ)
    (HoldoutConstruction.integerPartials_commute j.succ 0) k p

theorem normalized_normal_residue (k : ℕ) (p : PolynomialRing) :
    normalizedFiberResidue (k+1) (n*p) = normalizedFiberResidue k (normal p) := by
  simp only [normalizedFiberResidue_eq,normal_residue,Nat.factorial_succ,Nat.cast_mul]
  ring

theorem normalized_cancel_equation (k : ℕ) (p : PolynomialRing) :
    normalizedFiberResidue (k+1) (F*p) = ((k+1:ℕ):W) * normalizedFiberResidue k p := by
  simp only [normalizedFiberResidue_eq,cancel_equation,Nat.factorial_succ,Nat.cast_mul]
  ring

open CycleQ2GeometricIncidenceProj (geometricWeight homogeneous_of_character)

private abbrev homogeneousEquation : MvPolynomial (Fin 5) Coeff :=
  normalizedFullSextic (fun e : FullSexticTailIndex => (X e : Coeff))

private theorem chart_weighted_euler (p : MvPolynomial (Fin 5) Coeff) (d : ℕ)
    (hp : p.IsWeightedHomogeneous geometricWeight d) :
    chart (pderiv (0 : Fin 5) p) +
      ∑ i : Fin 4, geometricWeight i.succ • (X i * pderiv i (chart p)) = d • chart p := by
  have h := congrArg (chart (R := Coeff)) hp.sum_weight_X_mul_pderiv
  rw [Fin.sum_univ_succ] at h
  have hx0 : chart (X (0 : Fin 5) : MvPolynomial (Fin 5) Coeff) = 1 := by simp [chart]
  have hx (i : Fin 4) : chart (X i.succ : MvPolynomial (Fin 5) Coeff) = X i := by simp [chart]
  simpa only [map_add,map_sum,map_nsmul,map_mul,hx0,hx,
    show geometricWeight (0 : Fin 5) = 1 from rfl,one_nsmul,one_mul,
    ← CycleQ2WeightedAffineChartJets.pderiv_chart] using h

private theorem normalized_affine_coordinate_residue (i : Fin 4) (k : ℕ) (p : PolynomialRing) :
    normalizedFiberResidue (k+1) ((X i*pderiv i F)*p) =
      normalizedFiberResidue k p + normalizedFiberResidue k (X i*pderiv i p) -
        fiberTangent (HoldoutConstruction.integerPartial i) (normalizedFiberResidue k (X i*p)) := by
  have h := normalized_tangent_residue (HoldoutConstruction.integerPartial i)
    (HoldoutConstruction.integerPartials_commute i 0) k (X i*p)
  change fiberTangent (HoldoutConstruction.integerPartial i) (normalizedFiberResidue k (X i*p)) =
    normalizedFiberResidue k (pderiv i (X i*p)) -
      normalizedFiberResidue (k+1) (pderiv i F*(X i*p)) at h
  have hd : pderiv i (X i*p) = p+X i*pderiv i p := by
    rw [pderiv_mul,pderiv_X_self]
    ring
  have hm : pderiv i F*(X i*p) = (X i*pderiv i F)*p := by ring
  rw [hd,hm,normalizedFiberResidue_add] at h
  rw [h]
  ring

private theorem normalized_chart_zero_residue (k : ℕ) (p : MvPolynomial (Fin 5) Coeff)
    (hp : p.IsWeightedHomogeneous geometricWeight (6*k+1)) :
    normalizedFiberResidue (k+1) (chart (pderiv (0 : Fin 5) homogeneousEquation)*chart p) -
      normalizedFiberResidue k (chart (pderiv (0 : Fin 5) p)) =
        ∑ i : Fin 4, (geometricWeight i.succ : W) *
          fiberTangent (HoldoutConstruction.integerPartial i)
            (normalizedFiberResidue k (X i*chart p)) := by
  have hF : homogeneousEquation.IsWeightedHomogeneous geometricWeight 6 :=
    homogeneous_of_character (CycleQ2IncidenceNormalForm.normalizedFullSextic_homogeneous _)
  have hf := congrArg (fun q : PolynomialRing => normalizedFiberResidueAdd (k+1) (q*chart p))
    (chart_weighted_euler homogeneousEquation 6 hF)
  simp only [add_mul,Finset.sum_mul,smul_mul_assoc,map_add,map_sum,map_nsmul] at hf
  change normalizedFiberResidue (k+1) (chart (pderiv (0 : Fin 5) homogeneousEquation)*chart p) +
    (∑ i : Fin 4, geometricWeight i.succ • normalizedFiberResidue (k+1) ((X i*pderiv i F)*chart p)) =
      6 • normalizedFiberResidue (k+1) (F*chart p) at hf
  rw [normalized_cancel_equation] at hf
  have hg := congrArg (normalizedFiberResidueAdd k) (chart_weighted_euler p (6*k+1) hp)
  simp only [map_add,map_sum,map_nsmul] at hg
  change normalizedFiberResidue k (chart (pderiv (0 : Fin 5) p)) +
    (∑ i : Fin 4, geometricWeight i.succ • normalizedFiberResidue k (X i*pderiv i (chart p))) =
      (6*k+1) • normalizedFiberResidue k (chart p) at hg
  simp only [nsmul_eq_mul] at hf hg
  simp_rw [normalized_affine_coordinate_residue] at hf
  have hw : (∑ i : Fin 4, (geometricWeight i.succ : W)) = 5 := by
    norm_num [geometricWeight,Fin.sum_univ_succ]
  simp only [mul_add,mul_sub,Finset.sum_add_distrib,Finset.sum_sub_distrib,
    ← Finset.sum_mul,hw] at hf
  have hs : (∑ i : Fin 4, (geometricWeight i.succ : W) *
      normalizedFiberResidue k (X i*pderiv i (chart p))) =
      ((6*k+1 : ℕ) : W)*normalizedFiberResidue k (chart p) -
        normalizedFiberResidue k (chart (pderiv (0 : Fin 5) p)) :=
    eq_sub_iff_add_eq.mpr ((add_comm _ _).trans hg)
  rw [hs] at hf
  apply sub_eq_zero.mp
  calc
    _ = (normalizedFiberResidue (k+1) (chart (pderiv (0 : Fin 5) homogeneousEquation)*chart p) +
        (5*normalizedFiberResidue k (chart p) +
          (((6*k+1 : ℕ) : W)*normalizedFiberResidue k (chart p) -
            normalizedFiberResidue k (chart (pderiv (0 : Fin 5) p))) -
          ∑ i : Fin 4, (geometricWeight i.succ : W) *
            fiberTangent (HoldoutConstruction.integerPartial i)
              (normalizedFiberResidue k (X i*chart p)))) -
        6*(((k+1 : ℕ) : W)*normalizedFiberResidue k (chart p)) := by
      simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_one,Nat.cast_ofNat]
      ring
    _ = 0 := sub_eq_zero.mpr hf

/-- Weighted Euler supplies the projective-coordinate relation omitted by the
affine chart. Its residue is the displayed divergence in the three free coordinates. -/
theorem normalized_zero_residue (k : ℕ) (p : MvPolynomial (Fin 5) Coeff)
    (hp : p.IsWeightedHomogeneous geometricWeight (6*k+1)) :
    normalizedFiberResidue (k+1) (chart (pderiv (0 : Fin 5) homogeneousEquation)*chart p) -
      normalizedFiberResidue k (chart (pderiv (0 : Fin 5) p)) =
        ∑ j : Fin 3, direction F universal_normal_ne_zero j
          ((geometricWeight j.succ.succ : W)*normalizedFiberResidue k (X j.succ*chart p)) := by
  have h := normalized_chart_zero_residue k p hp
  rw [Fin.sum_univ_succ,fiberTangent_normal] at h
  simp only [Derivation.zero_apply,mul_zero,zero_add] at h
  calc
    _ = ∑ j : Fin 3, (geometricWeight j.succ.succ : W) *
        direction F universal_normal_ne_zero j (normalizedFiberResidue k (X j.succ*chart p)) := h
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      simp only [Derivation.leibniz,Derivation.map_natCast,smul_eq_mul,mul_zero,add_zero]

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

/-- The signed normalized polynomial-pole relation is an actual exterior boundary;
its primitive has the single free-coordinate coefficient `-normalizedFiberResidue k p`. -/
theorem normalized_spatial_exact (j : Fin 3) (k : ℕ) (p : PolynomialRing) :
    ∃ η : Form K W 2, exteriorDerivative η =
      (normalizedFiberResidue (k+1) (pderiv j.succ F*p) -
        normalizedFiberResidue k (pderiv j.succ p)) • volume coordinateBasis := by
  apply (exact_volume_iff_divergence coordinateBasis coordinateDerivation _).mpr
  refine ⟨fun i => if i = j then -normalizedFiberResidue k p else 0,?_⟩
  calc
    _ = coordinateDerivation j (if j = j then -normalizedFiberResidue k p else 0) :=
      Finset.sum_eq_single j (fun i _ hij => by simp [hij]) (by simp)
    _ = _ := by
      rw [if_pos rfl,map_neg]
      change -direction F universal_normal_ne_zero j (normalizedFiberResidue k p) = _
      rw [normalized_spatial_residue]
      ring

/-- Every degree-compatible homogeneous polynomial-pole relation is a genuine
rational exterior boundary, including the coordinate set to one in this chart. -/
theorem normalized_homogeneous_exact (i : Fin 5) (k : ℕ) (p : MvPolynomial (Fin 5) Coeff)
    (hp : p.IsWeightedHomogeneous geometricWeight (6*k+geometricWeight i)) :
    ∃ η : Form K W 2, exteriorDerivative η =
      (normalizedFiberResidue (k+1) (chart (pderiv i homogeneousEquation*p)) -
        normalizedFiberResidue k (chart (pderiv i p))) • volume coordinateBasis := by
  revert hp
  refine Fin.cases ?_ (fun i => ?_) i
  · intro hp
    apply (exact_volume_iff_divergence coordinateBasis coordinateDerivation _).mpr
    refine ⟨fun j => (geometricWeight j.succ.succ : W)*
      normalizedFiberResidue k (X j.succ*chart p),?_⟩
    simpa only [map_mul] using (normalized_zero_residue k p hp).symm
  · intro _
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [map_mul,← CycleQ2WeightedAffineChartJets.pderiv_chart]
      change ∃ η : Form K W 2, exteriorDerivative η =
        (normalizedFiberResidue (k+1) (n*chart p) -
          normalizedFiberResidue k (normal (chart p))) • volume coordinateBasis
      rw [normalized_normal_residue,sub_self,zero_smul]
      exact ⟨0,map_zero _⟩
    · simpa only [map_mul,← CycleQ2WeightedAffineChartJets.pderiv_chart] using
        normalized_spatial_exact j k (chart p)

/-- Projection and a coordinate derivative commute with the corresponding shift
in weighted degree. Zero variable weights are allowed. -/
theorem component_pderiv {R σ : Type*} [CommRing R] (w : σ → ℕ) (d : ℕ)
    (i : σ) (p : MvPolynomial σ R) :
    weightedHomogeneousComponent w d (pderiv i p) =
      pderiv i (weightedHomogeneousComponent w (d+w i) p) := by
  classical
  ext m
  simp only [coeff_weightedHomogeneousComponent,coeff_pderiv,map_add,
    Finsupp.weight_single,one_smul]
  by_cases hm : Finsupp.weight w m = d
  · have hs : Finsupp.weight w m+w i = d+w i := congrArg (fun a => a+w i) hm
    rw [if_pos hm,if_pos hs]
  · have hs : Finsupp.weight w m+w i ≠ d+w i := fun h => hm (Nat.add_right_cancel h)
    rw [if_neg hm,if_neg hs,zero_mul]

/-- A gradient factor shifts the numerator projection by exactly its weighted degree. -/
theorem component_gradient_mul (k : ℕ) (i : Fin 5) (p : MvPolynomial (Fin 5) Coeff) :
    weightedHomogeneousComponent geometricWeight (6*(k+1)) (p*pderiv i homogeneousEquation) =
      weightedHomogeneousComponent geometricWeight (6*k+geometricWeight i) p *
        pderiv i homogeneousEquation := by
  have hF : homogeneousEquation.IsWeightedHomogeneous geometricWeight 6 :=
    homogeneous_of_character (CycleQ2IncidenceNormalForm.normalizedFullSextic_homogeneous _)
  have hi : geometricWeight i ≤ 6 := by fin_cases i <;> decide
  have hpartial : (pderiv i homogeneousEquation).IsWeightedHomogeneous geometricWeight
      (6-geometricWeight i) := hF.pderiv (Nat.sub_add_cancel hi)
  have hd : (6*k+geometricWeight i)+(6-geometricWeight i) = 6*(k+1) := by omega
  simpa only [hd] using CycleQ2WeightedComponent.component_mul geometricWeight p
    (pderiv i homogeneousEquation) (6*k+geometricWeight i) (6-geometricWeight i) hpartial

/-- The underlying module of the normalized polynomial pole presentation. -/
abbrev RawPoles := ℕ →₀ MvPolynomial (Fin 5) Coeff

/-- In pole summand `k`, retain precisely the homogeneous numerator of weight `6*k`. -/
def degreeProjection : RawPoles →ₗ[Coeff] RawPoles :=
  Finsupp.lsum Coeff (fun k => (Finsupp.lsingle k).comp
    (weightedHomogeneousComponent geometricWeight (6*k)))

theorem degreeProjection_single (k : ℕ) (p : MvPolynomial (Fin 5) Coeff) :
    degreeProjection (Finsupp.single k p) =
      Finsupp.single k (weightedHomogeneousComponent geometricWeight (6*k) p) := by
  rw [degreeProjection,Finsupp.lsum_single]
  rfl

/-- An arbitrary raw relation projects to the same relation with the uniquely
appropriate homogeneous component of its multiplier. -/
theorem degreeProjection_relation (k : ℕ) (i : Fin 5) (p : MvPolynomial (Fin 5) Coeff) :
    degreeProjection (Finsupp.single (k+1) (p*pderiv i homogeneousEquation) -
      Finsupp.single k (pderiv i p)) =
        Finsupp.single (k+1)
          (weightedHomogeneousComponent geometricWeight (6*k+geometricWeight i) p *
            pderiv i homogeneousEquation) -
        Finsupp.single k
          (pderiv i (weightedHomogeneousComponent geometricWeight (6*k+geometricWeight i) p)) := by
  rw [map_sub,degreeProjection_single,degreeProjection_single,component_gradient_mul,component_pderiv]

theorem degreeProjection_idempotent (p : RawPoles) : degreeProjection (degreeProjection p) = degreeProjection p := by
  induction p using Finsupp.induction_linear with
  | zero => simp
  | add p q hp hq => simp only [map_add,hp,hq]
  | single k p =>
    simp only [degreeProjection_single]
    exact congrArg (Finsupp.single k)
      (weightedHomogeneousComponent_eq_self (weightedHomogeneousComponent_isWeightedHomogeneous _ _))

private def rawPoleResidue : RawPoles →+ W :=
  Finsupp.liftAddHom (fun k => (normalizedFiberResidueAdd k).comp
    (chart (R := Coeff)).toLinearMap.toAddMonoidHom)

private theorem rawPoleResidue_single (k : ℕ) (p : MvPolynomial (Fin 5) Coeff) :
    rawPoleResidue (Finsupp.single k p) = normalizedFiberResidue k (chart p) := by
  rw [rawPoleResidue,Finsupp.liftAddHom_apply_single]
  rfl

/-- The actual additive residue realization of raw poles after the necessary
degree projection. Boundary descent is established on arbitrary raw relations below. -/
def projectedPoleResidue : RawPoles →+ W :=
  rawPoleResidue.comp degreeProjection.toAddMonoidHom

theorem projectedPoleResidue_single (k : ℕ) (p : MvPolynomial (Fin 5) Coeff) :
    projectedPoleResidue (Finsupp.single k p) =
      normalizedFiberResidue k (chart (weightedHomogeneousComponent geometricWeight (6*k) p)) := by
  change rawPoleResidue (degreeProjection (Finsupp.single k p)) = _
  rw [degreeProjection_single,rawPoleResidue_single]

/-- No homogeneity hypothesis is imposed on the raw multiplier: projection
selects the correct component, whose relation is an actual rational boundary. -/
theorem projectedPoleResidue_relation_exact (k : ℕ) (i : Fin 5) (p : MvPolynomial (Fin 5) Coeff) :
    ∃ η : Form K W 2, exteriorDerivative η =
      projectedPoleResidue (Finsupp.single (k+1) (p*pderiv i homogeneousEquation) -
        Finsupp.single k (pderiv i p)) • volume coordinateBasis := by
  rw [map_sub,projectedPoleResidue_single,projectedPoleResidue_single,
    component_gradient_mul,component_pderiv]
  simpa only [mul_comm] using normalized_homogeneous_exact i k
    (weightedHomogeneousComponent geometricWeight (6*k+geometricWeight i) p)
    (weightedHomogeneousComponent_isWeightedHomogeneous _ _)

/-- Multiplication by a monic-family coefficient is multiplication by its actual
constant value on the hypersurface, in every pole summand. -/
theorem projectedPoleResidue_smul (a : Coeff) (p : RawPoles) :
    projectedPoleResidue (a • p) = v (C a) * projectedPoleResidue p := by
  induction p using Finsupp.induction_linear with
  | zero => simp
  | add p q hp hq => simp only [smul_add,map_add,hp,hq,mul_add]
  | single k p =>
    rw [Finsupp.smul_single,projectedPoleResidue_single,projectedPoleResidue_single,
      map_smul,map_smul,smul_eq_C_mul,normalizedFiberResidue_C_mul]

/-- The fraction-field coefficient embedding agrees with literal polynomial evaluation. -/
theorem coefficient_fieldValue (a : Coeff) :
    algebraMap K W (algebraMap Coeff K a) = v (C a) := by
  change CycleQ2UniversalWeightedDeRham.coefficients (algebraMap Coeff K a) = _
  exact IsFractionRing.lift_algebraMap _ a

/-- Restriction of scalars on the existing relative Kähler exterior powers. -/
instance coefficientFormModule (p : ℕ) : Module Coeff (Form K W p) :=
  Module.compHom (Form K W p) (algebraMap Coeff K)

instance coefficientFormTower (p : ℕ) : IsScalarTower Coeff K (Form K W p) where
  smul_assoc a c ω := by
    change (a • c) • ω = algebraMap Coeff K a • (c • ω)
    rw [Algebra.smul_def,mul_smul]

theorem coefficient_form_smul (a : Coeff) {p : ℕ} (ω : Form K W p) :
    a • ω = v (C a) • ω := by
  change algebraMap Coeff K a • ω = _
  rw [← IsScalarTower.algebraMap_smul W (algebraMap Coeff K a),coefficient_fieldValue]

/-- Actual rational exterior boundaries, viewed over the monic coefficient ring. -/
def rationalBoundaries : Submodule Coeff (Form K W 3) :=
  (LinearMap.range exteriorDerivative).restrictScalars Coeff

/-- Rational top forms modulo the range of the actual exterior derivative. -/
abbrev RationalResidueClasses := Form K W 3 ⧸ rationalBoundaries

/-- The degree-projected raw polynomial poles as actual rational top forms. -/
def rawResidueForm : RawPoles →ₗ[Coeff] Form K W 3 where
  toFun p := projectedPoleResidue p • volume coordinateBasis
  map_add' p q := by rw [map_add,add_smul]
  map_smul' a p := by
    rw [projectedPoleResidue_smul,mul_smul,coefficient_form_smul]

def rawResidueClass : RawPoles →ₗ[Coeff] RationalResidueClasses :=
  rationalBoundaries.mkQ.comp rawResidueForm

theorem rawResidueClass_relation_zero (k : ℕ) (i : Fin 5) (p : MvPolynomial (Fin 5) Coeff) :
    rawResidueClass (Finsupp.single (k+1) (p*pderiv i homogeneousEquation) -
      Finsupp.single k (pderiv i p)) = 0 := by
  change rationalBoundaries.mkQ
    (projectedPoleResidue (Finsupp.single (k+1) (p*pderiv i homogeneousEquation) -
      Finsupp.single k (pderiv i p)) • volume coordinateBasis) = 0
  rw [Submodule.mkQ_apply,Submodule.Quotient.mk_eq_zero]
  exact projectedPoleResidue_relation_exact k i p

open CycleQ2PolynomialPoleSymbols (Symbols symbol relations monicFamily connection connection_symbol)

/-- Every coefficient-linear combination of the raw polynomial relations has
zero image in actual rational top forms modulo boundaries. -/
theorem relations_le_residue_kernel :
    relations Coeff (monicFamily ℂ) ≤ LinearMap.ker rawResidueClass := by
  apply Submodule.span_le.mpr
  rintro _ ⟨k,i,p,rfl⟩
  change rawResidueClass _ = 0
  exact rawResidueClass_relation_zero k i p

/-- The normalized polynomial pole quotient of the literal 44-coefficient monic
family maps coefficient-linearly to actual rational top forms modulo boundaries. -/
def residueRealization : Symbols Coeff (monicFamily ℂ) →ₗ[Coeff] RationalResidueClasses :=
  (relations Coeff (monicFamily ℂ)).liftQ rawResidueClass relations_le_residue_kernel

theorem residueRealization_mkQ (p : RawPoles) :
    residueRealization ((relations Coeff (monicFamily ℂ)).mkQ p) = rawResidueClass p := rfl

theorem residueRealization_symbol (k : ℕ) (p : MvPolynomial (Fin 5) Coeff) :
    residueRealization (symbol Coeff (monicFamily ℂ) k p) =
      rationalBoundaries.mkQ
        (normalizedFiberResidue k (chart (weightedHomogeneousComponent geometricWeight (6*k) p)) •
          volume coordinateBasis) := by
  change rationalBoundaries.mkQ
    (projectedPoleResidue (Finsupp.single k p) • volume coordinateBasis) = _
  rw [projectedPoleResidue_single]

theorem residueRealization_symbol_eq_zero_iff (k : ℕ) (p : MvPolynomial (Fin 5) Coeff) :
    residueRealization (symbol Coeff (monicFamily ℂ) k p) = 0 ↔
      ∃ η : Form K W 2, exteriorDerivative η =
        normalizedFiberResidue k (chart (weightedHomogeneousComponent geometricWeight (6*k) p)) •
          volume coordinateBasis := by
  rw [residueRealization_symbol,Submodule.mkQ_apply,Submodule.Quotient.mk_eq_zero]
  rfl

/-- The same actual rational quotient with its coefficient fraction-field scalar action. -/
abbrev FieldResidueClasses := Form K W 3 ⧸ LinearMap.range exteriorDerivative

def residueClassesEquiv : RationalResidueClasses ≃ₗ[Coeff] FieldResidueClasses :=
  Submodule.Quotient.restrictScalarsEquiv Coeff (LinearMap.range exteriorDerivative)

def fieldResidueRealization : Symbols Coeff (monicFamily ℂ) →ₗ[Coeff] FieldResidueClasses :=
  residueClassesEquiv.toLinearMap.comp residueRealization

theorem fieldResidueRealization_eq_zero_iff (x : Symbols Coeff (monicFamily ℂ)) :
    fieldResidueRealization x = 0 ↔ residueRealization x = 0 := by
  change residueClassesEquiv (residueRealization x) = 0 ↔ residueRealization x = 0
  constructor
  · intro h
    exact residueClassesEquiv.injective (h.trans residueClassesEquiv.map_zero.symm)
  · intro h
    rw [h,map_zero]

theorem coefficient_derivation_map {A B : Type*} [CommRing A] [CommRing B]
    [Algebra ℤ A] [Algebra ℤ B] (θ : A →+* B) (D : Derivation ℤ A A) (E : Derivation ℤ B B)
    (h : ∀ a, E (θ a) = θ (D a)) (p : MvPolynomial (Fin 5) A) :
    coefficientDerivation E (MvPolynomial.map θ p) = MvPolynomial.map θ (coefficientDerivation D p) := by
  induction p using MvPolynomial.induction_on' with
  | monomial m c => simp only [map_monomial,coefficientDerivation_monomial,h]
  | add p q hp hq => simp only [map_add,hp,hq]

/-- A compatible coefficient derivation commutes with changing the coefficients
of the actual normalized polynomial pole quotient. -/
theorem connection_specialize {A B : Type*} [CommRing A] [CommRing B]
    [Algebra ℤ A] [Algebra ℤ B] (θ : A →+* B) (D : Derivation ℤ A A) (E : Derivation ℤ B B)
    (h : ∀ a, E (θ a) = θ (D a)) (G : MvPolynomial (Fin 5) A) (x : Symbols A G) :
    connection E (MvPolynomial.map θ G) (CycleQ2PolynomialPoleSymbols.specialize θ G x) =
      CycleQ2PolynomialPoleSymbols.specialize θ G (connection D G x) := by
  refine Submodule.Quotient.induction_on _ x (fun p => ?_)
  induction p using Finsupp.induction_linear with
  | zero => simp
  | add p q hp hq => simp only [map_add,hp,hq]
  | single k p =>
    change connection E (MvPolynomial.map θ G)
      (CycleQ2PolynomialPoleSymbols.specialize θ G (symbol A G k p)) =
        CycleQ2PolynomialPoleSymbols.specialize θ G (connection D G (symbol A G k p))
    simp only [CycleQ2PolynomialPoleSymbols.specialize_symbol,connection_symbol,map_sub,
      coefficient_derivation_map θ D E h,map_mul]

private theorem coefficient_change_base (e : FullSexticTailIndex) (p : MvPolynomial (Fin 5) Coeff) :
    coefficientDerivation (HoldoutConstruction.integerPartial (R := ℂ) e) p =
      coefficientDerivation (pderiv e) p := by
  induction p using MvPolynomial.induction_on' with
  | monomial m c => rw [coefficientDerivation_monomial,coefficientDerivation_monomial]; rfl
  | add p q hp hq => simp only [map_add,hp,hq]

theorem integer_connection_eq (e : FullSexticTailIndex) :
    connection (HoldoutConstruction.integerPartial (R := ℂ) e) (monicFamily ℂ) =
      connection (pderiv e) (monicFamily ℂ) := by
  apply AddMonoidHom.ext
  intro x
  refine Submodule.Quotient.induction_on _ x (fun p => ?_)
  induction p using Finsupp.induction_linear with
  | zero => simp
  | add p q hp hq => simp only [map_add,hp,hq]
  | single k p =>
    change connection (HoldoutConstruction.integerPartial (R := ℂ) e) (monicFamily ℂ)
      (symbol Coeff (monicFamily ℂ) k p) =
        connection (pderiv e) (monicFamily ℂ) (symbol Coeff (monicFamily ℂ) k p)
    simp only [connection_symbol,coefficient_change_base]

/-- Coefficient differentiation preserves each weighted numerator component. -/
theorem component_coefficient (e : FullSexticTailIndex) (d : ℕ) (p : MvPolynomial (Fin 5) Coeff) :
    weightedHomogeneousComponent geometricWeight d (coefficientDerivation (pderiv e) p) =
      coefficientDerivation (pderiv e) (weightedHomogeneousComponent geometricWeight d p) := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial m c =>
    rw [coefficientDerivation_monomial,
      weightedHomogeneousComponent_of_mem (isWeightedHomogeneous_monomial geometricWeight m (pderiv e c) rfl),
      weightedHomogeneousComponent_of_mem (isWeightedHomogeneous_monomial geometricWeight m c rfl)]
    split_ifs <;> simp only [coefficientDerivation_monomial,map_zero]
  | add p q hp hq => simp only [map_add,hp,hq]

private abbrev coefficientVelocity (e : FullSexticTailIndex) : MvPolynomial (Fin 5) Coeff :=
  monomial (CycleQ2IncidenceNormalForm.fullExponentOf e.val.val) 1

private theorem component_velocity_mul (e : FullSexticTailIndex) (k : ℕ)
    (p : MvPolynomial (Fin 5) Coeff) :
    weightedHomogeneousComponent geometricWeight (6*(k+1)) (coefficientVelocity e*p) =
      coefficientVelocity e*weightedHomogeneousComponent geometricWeight (6*k) p := by
  have hm : (coefficientVelocity e).IsWeightedHomogeneous geometricWeight 6 :=
    homogeneous_of_character (isWeightedHomogeneous_monomial
      CycleQ2IncidenceNormalForm.fullGrading _ _ (CycleQ2IncidenceNormalForm.fullGrading_of_invariant e.val))
  have hd : 6+6*k = 6*(k+1) := by omega
  simpa only [hd] using CycleQ2WeightedComponent.component_mul_left geometricWeight
    (coefficientVelocity e) p 6 (6*k) hm

/-- The literal coefficient connection on raw normalized polynomial poles. -/
def rawPoleConnection (e : FullSexticTailIndex) : RawPoles →+ RawPoles :=
  Finsupp.liftAddHom (fun k =>
    (Finsupp.lsingle k : MvPolynomial (Fin 5) Coeff →ₗ[Coeff] RawPoles).toAddMonoidHom.comp
      (coefficientDerivation (pderiv e)).toAddMonoidHom -
    (Finsupp.lsingle (k+1) : MvPolynomial (Fin 5) Coeff →ₗ[Coeff] RawPoles).toAddMonoidHom.comp
      (AddMonoidHom.mulLeft (coefficientVelocity e)))

theorem rawPoleConnection_single (e : FullSexticTailIndex) (k : ℕ) (p : MvPolynomial (Fin 5) Coeff) :
    rawPoleConnection e (Finsupp.single k p) =
      Finsupp.single k (coefficientDerivation (pderiv e) p) -
        Finsupp.single (k+1) (coefficientVelocity e*p) := by
  rw [rawPoleConnection,Finsupp.liftAddHom_apply_single]
  rfl

/-- The formal coefficient connection is realized by the actual tangent
derivation on the rational hypersurface field, before passing to boundaries. -/
theorem projectedPoleResidue_connection (e : FullSexticTailIndex) (p : RawPoles) :
    fiberTangent (coefficientPartial e) (projectedPoleResidue p) =
      projectedPoleResidue (rawPoleConnection e p) := by
  induction p using Finsupp.induction_linear with
  | zero => simp
  | add p q hp hq => simp only [map_add,hp,hq]
  | single k p =>
    rw [rawPoleConnection_single,map_sub,projectedPoleResidue_single,projectedPoleResidue_single,
      projectedPoleResidue_single,normalized_coefficient_residue,coefficient_chart,
      coefficient_change_base,component_coefficient,component_velocity_mul,map_mul]

theorem connection_mkQ (e : FullSexticTailIndex) (p : RawPoles) :
    connection (pderiv e) (monicFamily ℂ) ((relations Coeff (monicFamily ℂ)).mkQ p) =
      (relations Coeff (monicFamily ℂ)).mkQ (rawPoleConnection e p) := by
  induction p using Finsupp.induction_linear with
  | zero => simp
  | add p q hp hq => simp only [map_add,hp,hq]
  | single k p =>
    rw [rawPoleConnection_single,map_sub]
    change connection (pderiv e) (monicFamily ℂ) (symbol Coeff (monicFamily ℂ) k p) =
      symbol Coeff (monicFamily ℂ) k (coefficientDerivation (pderiv e) p) -
        symbol Coeff (monicFamily ℂ) (k+1) (coefficientVelocity e*p)
    rw [connection_symbol,CycleQ2PolynomialPoleSymbols.monic_velocity]

/-- The actual rational-exactness kernel in the full polynomial pole quotient.
Its restriction to the degree-compatible character frame is the relevant geometric kernel. -/
def residueKernel : Submodule Coeff (Symbols Coeff (monicFamily ℂ)) := LinearMap.ker residueRealization

/-- The actual residue kernel is stable under every monic coefficient connection. -/
theorem residueKernel_coefficient_stable (e : FullSexticTailIndex)
    (x : Symbols Coeff (monicFamily ℂ)) (hx : x ∈ residueKernel) :
    connection (pderiv e) (monicFamily ℂ) x ∈ residueKernel := by
  revert hx
  refine Submodule.Quotient.induction_on _ x (fun p => ?_)
  intro hp
  change rawResidueClass p = 0 at hp
  change rationalBoundaries.mkQ (projectedPoleResidue p • volume coordinateBasis) = 0 at hp
  rw [Submodule.mkQ_apply,Submodule.Quotient.mk_eq_zero] at hp
  have h := coefficient_preserves_exact e (projectedPoleResidue p) hp
  change residueRealization (connection (pderiv e) (monicFamily ℂ)
    ((relations Coeff (monicFamily ℂ)).mkQ p)) = 0
  rw [connection_mkQ,residueRealization_mkQ]
  change rationalBoundaries.mkQ
    (projectedPoleResidue (rawPoleConnection e p) • volume coordinateBasis) = 0
  rw [Submodule.mkQ_apply,Submodule.Quotient.mk_eq_zero]
  rw [projectedPoleResidue_connection] at h
  exact h

/-- The literal monic equation after adjoining coefficient denominators. -/
abbrev genericPoleEquation : MvPolynomial (Fin 5) K :=
  MvPolynomial.map (algebraMap Coeff K) (monicFamily ℂ)

abbrev GenericPoleSymbols := Symbols K genericPoleEquation

local instance fieldResidueClasses_isLocalizedModule :
    IsLocalizedModule (nonZeroDivisors Coeff)
      (LinearMap.id : FieldResidueClasses →ₗ[Coeff] FieldResidueClasses) :=
  isLocalizedModule_id (nonZeroDivisors Coeff) FieldResidueClasses K

/-- The actual rational residue realization after coefficient localization.
The codomain is still the quotient by actual exterior boundaries. -/
def genericResidueRealization : GenericPoleSymbols →ₗ[K] FieldResidueClasses :=
  IsLocalizedModule.mapExtendScalars (nonZeroDivisors Coeff)
    (CycleQ2PoleSymbolLocalization.localize K (nonZeroDivisors Coeff) (monicFamily ℂ))
    (LinearMap.id : FieldResidueClasses →ₗ[Coeff] FieldResidueClasses)
    K fieldResidueRealization

theorem genericResidueRealization_specialize (x : Symbols Coeff (monicFamily ℂ)) :
    genericResidueRealization
      (CycleQ2PolynomialPoleSymbols.specialize (algebraMap Coeff K) (monicFamily ℂ) x) =
        fieldResidueRealization x := by
  rw [← CycleQ2PoleSymbolLocalization.localize_eq_specialize K (nonZeroDivisors Coeff)
    (monicFamily ℂ) x]
  change IsLocalizedModule.map (nonZeroDivisors Coeff)
    (CycleQ2PoleSymbolLocalization.localize K (nonZeroDivisors Coeff) (monicFamily ℂ))
    (LinearMap.id : FieldResidueClasses →ₗ[Coeff] FieldResidueClasses)
    fieldResidueRealization
    (CycleQ2PoleSymbolLocalization.localize K (nonZeroDivisors Coeff) (monicFamily ℂ) x) = _
  exact IsLocalizedModule.map_apply _ _ _ _ _

/-- The coefficient partial on the actual coefficient fraction field. -/
def fractionCoefficientPartial (e : FullSexticTailIndex) : Derivation ℤ K K :=
  HoldoutConstruction.extendRingDerivation (L := K)
    (HoldoutConstruction.integerPartial (R := ℂ) e)

theorem fractionCoefficientPartial_apply (e : FullSexticTailIndex) (a : Coeff) :
    fractionCoefficientPartial e (algebraMap Coeff K a) =
      algebraMap Coeff K (HoldoutConstruction.integerPartial (R := ℂ) e a) :=
  HoldoutConstruction.extendRingDerivation_apply _ _

def genericResidueKernel : Submodule K GenericPoleSymbols :=
  LinearMap.ker genericResidueRealization

/-- Clearing one coefficient denominator transfers the proved integral kernel
stability to the generic coefficient field. -/
theorem genericResidueKernel_coefficient_stable (e : FullSexticTailIndex)
    (x : GenericPoleSymbols) (hx : x ∈ genericResidueKernel) :
    connection (fractionCoefficientPartial e) genericPoleEquation x ∈ genericResidueKernel := by
  change genericResidueRealization x = 0 at hx
  obtain ⟨a, ha, y, hy⟩ :=
    CycleQ2PoleSymbolLocalization.exists_nonzero_denominator (monicFamily ℂ) x
  have hy0 : residueRealization y = 0 := by
    apply (fieldResidueRealization_eq_zero_iff y).mp
    rw [← genericResidueRealization_specialize y,hy,map_smul,hx,smul_zero]
  have hy1 : genericResidueRealization
      (CycleQ2PolynomialPoleSymbols.specialize (algebraMap Coeff K) (monicFamily ℂ)
        (connection (HoldoutConstruction.integerPartial (R := ℂ) e) (monicFamily ℂ) y)) = 0 := by
    rw [genericResidueRealization_specialize,fieldResidueRealization_eq_zero_iff,
      integer_connection_eq]
    exact residueKernel_coefficient_stable e y hy0
  have hd := congrArg (fun z => genericResidueRealization
    (connection (fractionCoefficientPartial e) genericPoleEquation z)) hy
  rw [connection_specialize (algebraMap Coeff K)
    (HoldoutConstruction.integerPartial (R := ℂ) e) (fractionCoefficientPartial e)
    (fractionCoefficientPartial_apply e),hy1,CycleQ2PolynomialPoleSymbols.connection_smul,
    map_add,map_smul,map_smul,hx,smul_zero,add_zero] at hd
  have haK : algebraMap Coeff K a ≠ 0 := by
    intro h
    exact ha (IsFractionRing.injective Coeff K
      (h.trans (map_zero (algebraMap Coeff K)).symm))
  change genericResidueRealization (connection (fractionCoefficientPartial e) genericPoleEquation x) = 0
  exact (smul_eq_zero.mp hd.symm).resolve_left haK

open CycleQ2UniversalPoleFrame (Label vectorRealize)
open CycleQ2MonicFermatCoefficientOpen (genericCoefficientMap generic_equation_monic generic_frame_units)

/-- The universal-frame equation and the literal monic equation have the same
coefficient localization; this map only identifies their quotient presentations. -/
def genericFrameEquationEquiv :
    Symbols K (CycleQ2UniversalPoleFrame.equation genericCoefficientMap) ≃ₗ[K] GenericPoleSymbols :=
  Submodule.quotEquivOfEq _ _ (congrArg (relations K) generic_equation_monic)

theorem genericFrameEquationEquiv_symbol (k : ℕ) (p : MvPolynomial (Fin 5) K) :
    genericFrameEquationEquiv
      (symbol K (CycleQ2UniversalPoleFrame.equation genericCoefficientMap) k p) =
        symbol K genericPoleEquation k p := rfl

theorem genericFrameEquationEquiv_connection (D : Derivation ℤ K K)
    (x : Symbols K (CycleQ2UniversalPoleFrame.equation genericCoefficientMap)) :
    genericFrameEquationEquiv
      (connection D (CycleQ2UniversalPoleFrame.equation genericCoefficientMap) x) =
        connection D genericPoleEquation (genericFrameEquationEquiv x) := by
  refine Submodule.Quotient.induction_on _ x (fun p => ?_)
  induction p using Finsupp.induction_linear with
  | zero => simp
  | add p q hp hq => simp only [map_add,hp,hq]
  | single k p =>
    change genericFrameEquationEquiv
      (connection D (CycleQ2UniversalPoleFrame.equation genericCoefficientMap)
        (symbol K (CycleQ2UniversalPoleFrame.equation genericCoefficientMap) k p)) =
      connection D genericPoleEquation
        (genericFrameEquationEquiv
          (symbol K (CycleQ2UniversalPoleFrame.equation genericCoefficientMap) k p))
    simp only [connection_symbol,map_sub,genericFrameEquationEquiv_symbol]
    rw [generic_equation_monic]

/-- The actual independent 66-symbol frame, in the monic quotient presentation. -/
def genericSymbolFrame : (Label → K) →ₗ[K] GenericPoleSymbols :=
  genericFrameEquationEquiv.toLinearMap.comp (vectorRealize genericCoefficientMap)

theorem genericSymbolFrame_injective : Function.Injective genericSymbolFrame := by
  intro u v h
  exact CycleQ2MonicFermatCoefficientOpen.generic_vectorRealize_injective
    (genericFrameEquationEquiv.injective h)

/-- The rational de Rham realization of the actual 66-dimensional frame. -/
def genericFrameRealization : (Label → K) →ₗ[K] FieldResidueClasses :=
  genericResidueRealization.comp genericSymbolFrame

def genericFrameKernel : Submodule K (Label → K) := LinearMap.ker genericFrameRealization

private theorem genericFrameConnection_exists (e : FullSexticTailIndex) :
    ∃ B : Matrix Label Label K, ∀ u : Label → K,
      vectorRealize genericCoefficientMap (fun i => fractionCoefficientPartial e (u i) + B.mulVec u i) =
        connection (fractionCoefficientPartial e)
          (CycleQ2UniversalPoleFrame.equation genericCoefficientMap)
          (vectorRealize genericCoefficientMap u) :=
  CycleQ2UniversalPoleFrame.exists_vector_connection genericCoefficientMap
    generic_frame_units.1 generic_frame_units.2.1 generic_frame_units.2.2 (fractionCoefficientPartial e)

/-- Matrices obtained by the proved pole reduction for the actual monic family. -/
def genericFrameConnection (e : FullSexticTailIndex) : Matrix Label Label K :=
  (genericFrameConnection_exists e).choose

theorem genericSymbolFrame_connection (e : FullSexticTailIndex) (u : Label → K) :
    genericSymbolFrame
      (fun i => fractionCoefficientPartial e (u i) + (genericFrameConnection e).mulVec u i) =
        connection (fractionCoefficientPartial e) genericPoleEquation (genericSymbolFrame u) := by
  change genericFrameEquationEquiv
    (vectorRealize genericCoefficientMap
      (fun i => fractionCoefficientPartial e (u i) + (genericFrameConnection e).mulVec u i)) =
    connection (fractionCoefficientPartial e) genericPoleEquation
      (genericFrameEquationEquiv (vectorRealize genericCoefficientMap u))
  rw [(genericFrameConnection_exists e).choose_spec u,genericFrameEquationEquiv_connection]

/-- Restricting the actual residue kernel to the independent frame gives a
66-vector submodule stable under all 44 coefficient connections. -/
theorem genericFrameKernel_coefficient_stable (e : FullSexticTailIndex)
    (u : Label → K) (hu : u ∈ genericFrameKernel) :
    (fun i => fractionCoefficientPartial e (u i) + (genericFrameConnection e).mulVec u i) ∈
      genericFrameKernel := by
  change genericResidueRealization (genericSymbolFrame
    (fun i => fractionCoefficientPartial e (u i) + (genericFrameConnection e).mulVec u i)) = 0
  rw [genericSymbolFrame_connection]
  exact genericResidueKernel_coefficient_stable e (genericSymbolFrame u) hu

/-- Differentiating an exact normalized residue gives the exact literal
polynomial-pole connection expression, with no extra pole-order factor. -/
theorem normalized_coefficient_preserves_exact (e : FullSexticTailIndex) (k : ℕ)
    (p : PolynomialRing)
    (h : ∃ η : Form K W 2, exteriorDerivative η =
      normalizedFiberResidue k p • volume coordinateBasis) :
    ∃ η : Form K W 2, exteriorDerivative η =
      (normalizedFiberResidue k (coefficientPartial e p) -
        normalizedFiberResidue (k+1) (chart (monomial
          (CycleQ2IncidenceNormalForm.fullExponentOf e.val.val) 1)*p)) • volume coordinateBasis := by
  simpa only [normalized_coefficient_residue] using
    coefficient_preserves_exact e (normalizedFiberResidue k p) h

theorem normalized_weighted_source :
    normalizedFiberResidue 2 b • volume coordinateBasis = (2 : W) • sourceForm := by
  rw [normalizedFiberResidue_eq,mul_smul,weighted_source]
  norm_num

/-- The protected degree-twelve numerator realizes as exactly twice the
previously constructed universal rational source form. -/
theorem residueRealization_protected_source :
    residueRealization (symbol Coeff (monicFamily ℂ) 2
      (CycleQ2UniversalPoleFrame.protectedNumerator (K := Coeff))) =
        rationalBoundaries.mkQ ((2 : W) • sourceForm) := by
  rw [residueRealization_symbol]
  have hp : (CycleQ2UniversalPoleFrame.protectedNumerator (K := Coeff)).IsWeightedHomogeneous
      geometricWeight 12 := homogeneous_of_character CycleQ2UniversalPoleFrame.protected_homogeneous
  rw [weightedHomogeneousComponent_eq_self hp]
  have hc : chart (CycleQ2UniversalPoleFrame.protectedNumerator (K := Coeff)) = b := by
    simp [CycleQ2UniversalPoleFrame.protectedNumerator,chart,b]
  rw [hc,normalized_weighted_source]

theorem genericResidueRealization_protected_source :
    genericResidueRealization (symbol K genericPoleEquation 2
      (CycleQ2UniversalPoleFrame.protectedNumerator (K := K))) =
        (LinearMap.range exteriorDerivative).mkQ ((2 : W) • sourceForm) := by
  have hm : MvPolynomial.map (algebraMap Coeff K)
      (CycleQ2UniversalPoleFrame.protectedNumerator (K := Coeff)) =
        CycleQ2UniversalPoleFrame.protectedNumerator (K := K) := by
    simp only [CycleQ2UniversalPoleFrame.protectedNumerator,map_mul,map_pow,map_X]
  have hs := CycleQ2PolynomialPoleSymbols.specialize_symbol (algebraMap Coeff K)
    (monicFamily ℂ) 2 (CycleQ2UniversalPoleFrame.protectedNumerator (K := Coeff))
  rw [hm] at hs
  rw [← hs,genericResidueRealization_specialize]
  change residueClassesEquiv
    (residueRealization (symbol Coeff (monicFamily ℂ) 2
      (CycleQ2UniversalPoleFrame.protectedNumerator (K := Coeff)))) = _
  rw [residueRealization_protected_source]
  rfl

/-- The protected source belongs to the actual rational realization of the
independent 66-symbol frame, with its exact factorial normalization. -/
theorem protected_source_in_genericFrame :
    ∃ u : Label → K, genericFrameRealization u =
      (LinearMap.range exteriorDerivative).mkQ ((2 : W) • sourceForm) := by
  obtain ⟨u,hu⟩ := CycleQ2UniversalPoleFrame.protected_in_frame genericCoefficientMap
    generic_frame_units.1 generic_frame_units.2.1 generic_frame_units.2.2
  refine ⟨u,?_⟩
  rw [CycleQ2UniversalPoleFrame.realize_eq_vectorRealize] at hu
  change genericResidueRealization
    (genericFrameEquationEquiv (vectorRealize genericCoefficientMap u)) = _
  rw [hu]
  change genericResidueRealization
    (genericFrameEquationEquiv (symbol K (CycleQ2UniversalPoleFrame.equation genericCoefficientMap)
      2 (CycleQ2UniversalPoleFrame.protectedNumerator (K := K)))) = _
  rw [genericFrameEquationEquiv_symbol,genericResidueRealization_protected_source]

end Chart
end CycleQ2WeightedPoleJets
#print axioms CycleQ2WeightedPoleJets.fiberTangent_residue

#print axioms CycleQ2WeightedPoleJets.coefficient_residue
#print axioms CycleQ2WeightedPoleJets.spatial_residue
#print axioms CycleQ2WeightedPoleJets.weighted_source
#print axioms CycleQ2WeightedPoleJets.coefficient_preserves_exact

#print axioms CycleQ2WeightedPoleJets.cancel_equation
#print axioms CycleQ2WeightedPoleJets.normalized_spatial_exact
#print axioms CycleQ2WeightedPoleJets.normalized_homogeneous_exact
#print axioms CycleQ2WeightedPoleJets.degreeProjection_relation
#print axioms CycleQ2WeightedPoleJets.projectedPoleResidue_relation_exact
#print axioms CycleQ2WeightedPoleJets.residueRealization
#print axioms CycleQ2WeightedPoleJets.residueRealization_protected_source
#print axioms CycleQ2WeightedPoleJets.projectedPoleResidue_connection
#print axioms CycleQ2WeightedPoleJets.residueKernel_coefficient_stable
#print axioms CycleQ2WeightedPoleJets.genericResidueRealization
#print axioms CycleQ2WeightedPoleJets.genericResidueKernel_coefficient_stable
#print axioms CycleQ2WeightedPoleJets.genericSymbolFrame_injective
#print axioms CycleQ2WeightedPoleJets.genericFrameKernel_coefficient_stable
#print axioms CycleQ2WeightedPoleJets.protected_source_in_genericFrame
#print axioms CycleQ2WeightedPoleJets.normalized_coefficient_preserves_exact
