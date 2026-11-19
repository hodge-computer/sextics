import Proposal.GeometricUniversalWeightedChart
import Mathlib.Algebra.MvPolynomial.PDeriv
import HodgeComputer.Constructions.HigherResidues.HigherResidue
import Proposal.GeometricNormalizedPencilCoordinates
import Proposal.GeometricGenericWeightedSource
import Proposal.GeometricGenericWeightedTransfer

section
/-!
# Evaluation and normal jets on the affine weighted chart

Setting the first coordinate to one commutes with every partial derivative
in the other four coordinates. This identifies affine iterated normal jets
with the corresponding homogeneous-coordinate jets.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace CycleQ2WeightedAffineChartJets

open MvPolynomial
open CycleQ2MonicWeightedAffineEquation (chart)

variable {R K : Type} [CommRing R] [CommRing K]

theorem eval_chart (f : R →+* K) (x : Fin 4 → K) (p : MvPolynomial (Fin 5) R) :
    eval₂Hom f x (chart p) = eval₂Hom f (Fin.cases 1 x) p := by
  have h : (eval₂Hom f x).comp chart.toRingHom = eval₂Hom f (Fin.cases 1 x) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [chart]
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [chart]
      · simp [chart]
  exact RingHom.congr_fun h p

theorem map_chart (f : R →+* K) (p : MvPolynomial (Fin 5) R) :
    MvPolynomial.map f (chart p) = chart (MvPolynomial.map f p) := by
  have h : (MvPolynomial.map f).comp chart.toRingHom =
      chart.toRingHom.comp (MvPolynomial.map f) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [chart]
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i <;> simp [chart]
  exact RingHom.congr_fun h p

private theorem pderiv_chart_X (i : Fin 4) (k : Fin 5) :
    pderiv i (chart (R := R) (X k)) = chart (pderiv i.succ (X k)) := by
  refine Fin.cases ?_ (fun j => ?_) k
  · simp [chart, pderiv_X_of_ne (Ne.symm (Fin.succ_ne_zero i))]
  · by_cases h : j = i
    · subst j
      simp [chart]
    · simp [chart, pderiv_X_of_ne h, pderiv_X_of_ne ((Fin.succ_injective _).ne h)]

theorem pderiv_chart (i : Fin 4) (p : MvPolynomial (Fin 5) R) :
    pderiv i (chart p) = chart (pderiv i.succ p) := by
  induction p using MvPolynomial.induction_on with
  | C c => simp [chart]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p j hp =>
    simp only [map_mul, pderiv_mul, pderiv_chart_X, hp, map_add]

theorem iterate_pderiv_chart (i : Fin 4) (n : ℕ) (p : MvPolynomial (Fin 5) R) :
    (pderiv i)^[n] (chart p) = chart ((pderiv i.succ)^[n] p) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, pderiv_chart, Function.iterate_succ_apply']

theorem eval_rename_succ (f : R →+* K) (x : Fin 4 → K) (p : MvPolynomial (Fin 4) R) :
    eval₂Hom f (Fin.cases 1 x) (rename Fin.succ p) = eval₂Hom f x p := by
  exact eval₂Hom_rename _ _ _ _

end CycleQ2WeightedAffineChartJets

end

#print axioms CycleQ2WeightedAffineChartJets.eval_chart
#print axioms CycleQ2WeightedAffineChartJets.iterate_pderiv_chart
end

section
/-!
# Rescaling the defining equation of a cubic-pole density

Scaling the equation by a nonzero constant scales its first three normal
jets by the same constant. With the numerator jets fixed, the residue
density of the third-order pole scales by the inverse cube. Relative
derivations that annihilate the scalar carry this scaling through the
ordinary divergence of the three primitive coefficients.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace CycleQ2WeightedDensityNormalization

open SplitHigherResidue

variable {K : Type*} [Field K] [CharZero K]

theorem normalDensity_scale (b b₁ b₂ n n₁ n₂ k : K) (hn : n ≠ 0) (hk : k ≠ 0) :
    normalSourceTwo b b₁ b₂ (k * n) (k * n₁) (k * n₂) / (k * n) =
      (k ^ 3)⁻¹ * (normalSourceTwo b b₁ b₂ n n₁ n₂ / n) := by
  unfold normalSourceTwo
  field_simp [hk, hn]

variable {R : Type*} [CommRing R] [Algebra R K]

theorem normalDensity_scale_equation (δ : Derivation R K K) (b G k : K)
    (hG : δ G ≠ 0) (hk : k ≠ 0) (hδ : δ k = 0) :
    normalSourceTwo b (δ b) (δ (δ b)) (δ (k * G)) (δ (δ (k * G)))
        (δ (δ (δ (k * G)))) / δ (k * G) =
      (k ^ 3)⁻¹ * (normalSourceTwo b (δ b) (δ (δ b)) (δ G) (δ (δ G))
        (δ (δ (δ G))) / δ G) := by
  have scale (x : K) : δ (k * x) = k * δ x := by
    rw [Derivation.leibniz, hδ, smul_zero, add_zero, smul_eq_mul]
  simp only [scale]
  exact normalDensity_scale _ _ _ _ _ _ _ hG hk

variable {ι : Type*} [Fintype ι] (D : ι → Derivation R K K)

omit [CharZero K] in
theorem divergence_mul_constant (u : ι → K) (c : K) (hc : ∀ j, D j c = 0) :
    (∑ j, D j (c * u j)) = c * ∑ j, D j (u j) := by
  simp only [Derivation.leibniz, hc, smul_eq_mul, mul_zero, add_zero,
    Finset.mul_sum]

/-- Ordinary relative primitives for the original and scaled equations
determine one another by multiplication by the inverse scaling factors. -/
theorem normalDensity_primitive_iff (b b₁ b₂ n n₁ n₂ k : K)
    (hn : n ≠ 0) (hk : k ≠ 0) (hD : ∀ j, D j k = 0) :
    (∃ u : ι → K, (∑ j, D j (u j)) =
      normalSourceTwo b b₁ b₂ (k * n) (k * n₁) (k * n₂) / (k * n)) ↔
    ∃ u : ι → K, (∑ j, D j (u j)) = normalSourceTwo b b₁ b₂ n n₁ n₂ / n := by
  rw [normalDensity_scale b b₁ b₂ n n₁ n₂ k hn hk]
  have h₃ (j : ι) : D j (k ^ 3) = 0 := by
    simp only [Derivation.leibniz_pow, hD, smul_zero]
  constructor
  · rintro ⟨u, hu⟩
    refine ⟨fun j => k ^ 3 * u j, ?_⟩
    rw [divergence_mul_constant D u _ h₃, hu, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hk),
      one_mul]
  · rintro ⟨u, hu⟩
    refine ⟨fun j => (k ^ 3)⁻¹ * u j, ?_⟩
    rw [divergence_mul_constant D u _ (fun j => by
      rw [Derivation.leibniz_inv, h₃, smul_zero]), hu]

end CycleQ2WeightedDensityNormalization

end

#print axioms CycleQ2WeightedDensityNormalization.normalDensity_scale
#print axioms CycleQ2WeightedDensityNormalization.normalDensity_primitive_iff
end

section
/-!
# The normalized affine sextic in the deformed function field

On the first weight-one chart, the leading coefficient scales every normal
jet of the monic equation to the corresponding jet of the actual pencil.
The three tangent operators agree after this normalization and the cubic-pole
densities differ by the cube of the leading coefficient.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CycleQ2GenericWeightedMonicDensity

open MvPolynomial CycleQ2GenericSpecialization CycleQ2GenericPencilLift
  CycleQ2GenericWeightedCoordinates CycleQ2GenericWeightedPencilEquation
  CycleQ2GenericWeightedChainRule CycleQ2GenericWeightedSource
  CycleQ2GenericWeightedMonicOpen CycleQ2GenericWeightedMonicCoefficients
  CycleQ2GenericWeightedOpen CycleQ2IncidenceNormalForm
  CycleQ2MonicWeightedPrimitiveIdentity CycleQ2WeightedAffineChartJets
open CycleQ2MonicWeightedAffineEquation (chart)
open CycleQ2AffineWeightedTransfer (weightedSource)
open CycleQ2Bridge (polynomialMap)
open CycleQ2GenericPencilOpen (ParameterIndex)
open scoped BigOperators

abbrev affinePoint (i : Fin 4) : RF := weightedPoint i.succ

def value (d : Direction) : Pol (coefficientField d) →+* RF :=
  eval₂Hom (algebraMap (coefficientField d) RF) affinePoint

def monicEquation (d : Direction) (c : ParameterIndex → ℂ) : Pol (coefficientField d) :=
  chart (normalizedFullSextic (coefficients d c))

private theorem lift_point : Fin.cases 1 affinePoint = weightedPoint := by
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

private theorem value_rename (d : Direction) (q : Pol (coefficientField d)) :
    eval₂Hom (algebraMap (coefficientField d) RF) weightedPoint (rename Fin.succ q) = value d q := by
  rw [← lift_point, eval_rename_succ]
  rfl

private theorem map_normalized (d : Direction) (c : ParameterIndex → ℂ) :
    MvPolynomial.map (algebraMap (coefficientField d) RF) (normalizedFullSextic (coefficients d c)) =
      normalizedFullSextic (normalizedCoefficientPoint d c) := by
  simp only [normalizedFullSextic, map_add, map_sum, map_monomial, map_one]
  rfl

private theorem normal_b {R : Type} [CommRing R] :
    normal (b : Pol R) = 2 * X 0 * X 1 ^ 2 * X 2 ^ 2 * X 3 ^ 2 := by
  norm_num [normal, b, pderiv_mul, pderiv_pow, pderiv_X, Pi.single_apply, show (2 : Fin 4) ≠ 0 by decide, show (3 : Fin 4) ≠ 0 by decide]
  ring

private theorem normal_normal_b {R : Type} [CommRing R] :
    normal (normal (b : Pol R)) = 2 * X 1 ^ 2 * X 2 ^ 2 * X 3 ^ 2 := by
  have h₂ : pderiv 0 (2 : Pol R) = 0 := (pderiv 0).map_natCast 2
  rw [normal_b]
  norm_num [normal, pderiv_mul, pderiv_pow, pderiv_X, Pi.single_apply, show (2 : Fin 4) ≠ 0 by decide, show (3 : Fin 4) ≠ 0 by decide, h₂]
  ring

variable (c : ParameterIndex → ℂ) (hc : endpointDifference c ≠ 0)
local notation "ep" => endpointDirection c hc
local notation "L" => coefficientPoint ep c fullSexticLeadingIndex
local notation "Fₘ" => monicEquation ep c

variable (hL : coefficientPoint (endpointDirection c hc) c fullSexticLeadingIndex ≠ 0)
include hL

private theorem jet_polynomial (i : Fin 4) (k : ℕ) :
    (pderiv i.succ)^[k] (endpointEquation c hc) =
      C L * MvPolynomial.map (algebraMap (coefficientField ep) RF)
        ((pderiv i.succ)^[k] (normalizedFullSextic (coefficients ep c))) := by
  induction k with
  | zero =>
    exact (equation_eq_leading_mul_normalized ep c hL).trans
      (congrArg (fun p => C L * p) (map_normalized ep c).symm)
  | succ k ih => simp only [Function.iterate_succ_apply', ih, pderiv_C_mul, pderiv_map]

theorem jet_scale (i : Fin 4) (k : ℕ) :
    eval weightedPoint ((pderiv i.succ)^[k] (endpointEquation c hc)) =
      L * value ep ((pderiv i)^[k] Fₘ) := by
  rw [jet_polynomial c hc hL, map_mul, eval_C, eval_map]
  congr 1
  change _ = eval₂Hom _ affinePoint ((pderiv i)^[k] (chart _))
  rw [iterate_pderiv_chart, eval_chart, lift_point]
  rfl

theorem value_equation : value ep Fₘ = 0 := by
  have h := (jet_scale c hc hL 0 0).symm.trans (endpoint_equation c hc)
  exact (mul_eq_zero.mp h).resolve_left hL

theorem normal_jet_scale (k : ℕ) :
    familyNormalJet ep k = L * value ep ((pderiv 0)^[k+1] Fₘ) :=
  (endpoint_normalJet c hc k).symm.trans (jet_scale c hc hL 0 (k+1))

theorem normal_ne_zero : value ep (normal Fₘ) ≠ 0 := by
  exact right_ne_zero_of_mul ((normal_jet_scale c hc hL 0).symm.trans_ne
    (familyPartial_zero_ne_zero ep))

/-- The three actual relative derivations act on every evaluated four-variable
polynomial by implicit differentiation of the normalized sextic equation. -/
theorem tangent_apply (j : Fin 3) (q : Pol (coefficientField ep)) :
    relativeDerivation ep j (value ep q) = value ep (pderiv j.succ q) -
      value ep (pderiv j.succ Fₘ) / value ep (normal Fₘ) * value ep (normal q) := by
  have h := weighted_derivative c hc j (algebraMap (coefficientField ep) RF)
    (deriv_coefficientField ep j) (rename Fin.succ q)
  have hn := jet_scale c hc hL 0 1
  have ht := jet_scale c hc hL j.succ 1
  change eval weightedPoint (pderiv 1 (endpointEquation c hc)) = L * value ep (normal Fₘ) at hn
  change eval weightedPoint (pderiv j.succ.succ (endpointEquation c hc)) =
    L * value ep (pderiv j.succ Fₘ) at ht
  have hrename (i : Fin 4) :
      pderiv i.succ (rename Fin.succ q) = rename Fin.succ (pderiv i q) :=
    pderiv_rename (Fin.succ_injective _) i q
  have hnq : pderiv 1 (rename Fin.succ q) = rename Fin.succ (normal q) := hrename 0
  rw [value_rename, hrename j.succ, hnq, value_rename, value_rename, ht, hn] at h
  rw [h, mul_div_assoc, mul_div_mul_left _ _ hL, mul_comm (value ep (normal q))]

/-- The monic density is the cube of the leading coefficient times the
density in the original deformed field, including both numerator jets. -/
theorem density_eq :
    density (value ep) Fₘ = L ^ 3 * genericDensity ep weightedSource := by
  have hb : value ep b = polynomialMap 4 weightedSource := by
    rw [weightedSource_value]
    simp only [value, b, map_mul, map_pow, eval₂Hom_X']
    rfl
  have hb₁ : value ep (normal b) = polynomialMap 4 (pderiv 0 weightedSource) := by
    rw [weightedSource_firstJet_value, normal_b]
    simp only [value, map_mul, map_pow, map_ofNat, eval₂Hom_X']
    rfl
  have hb₂ : value ep (normal (normal b)) = polynomialMap 4 (pderiv 0 (pderiv 0 weightedSource)) := by
    rw [weightedSource_secondJet_value, normal_normal_b]
    simp only [value, map_mul, map_pow, map_ofNat, eval₂Hom_X']
    rfl
  have hscaled : genericDensity ep weightedSource = (L ^ 3)⁻¹ * density (value ep) Fₘ := by
    unfold genericDensity density
    rw [← hb, ← hb₁, ← hb₂, normal_jet_scale c hc hL 0, normal_jet_scale c hc hL 1,
      normal_jet_scale c hc hL 2]
    exact CycleQ2WeightedDensityNormalization.normalDensity_scale _ _ _ _ _ _ _
      (normal_ne_zero c hc hL) hL
  rw [hscaled, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hL), one_mul]

theorem primitive_of_monic
    (h : ∃ v : Fin 3 → RF, (∑ j, relativeDerivation ep j (v j)) = density (value ep) Fₘ) :
    ∃ v : Fin 3 → RF, (∑ j, relativeDerivation ep j (v j)) = genericDensity ep weightedSource := by
  obtain ⟨v,hv⟩ := h
  have hconst (j : Fin 3) : relativeDerivation ep j ((L ^ 3)⁻¹) = 0 := by
    rw [Derivation.leibniz_inv, Derivation.leibniz_pow, deriv_leading]
    simp
  refine ⟨fun j => (L ^ 3)⁻¹ * v j, ?_⟩
  rw [CycleQ2WeightedDensityNormalization.divergence_mul_constant _ _ _ hconst, hv,
    density_eq c hc hL, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hL), one_mul]

end CycleQ2GenericWeightedMonicDensity
end

#print axioms CycleQ2GenericWeightedMonicDensity.tangent_apply
#print axioms CycleQ2GenericWeightedMonicDensity.density_eq
#print axioms CycleQ2GenericWeightedMonicDensity.primitive_of_monic
end

section
/-!
# Spatial denominators on the actual deformed pencil

A multiple in the three free spatial coordinates detects a denominator in the
monic chart ring. If one coefficient of the multiple survives the chosen pencil,
algebraic independence makes its evaluation and hence the denominator nonzero.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CycleQ2GenericWeightedSpatialDenominator

open MvPolynomial CycleQ2IncidenceNormalForm CycleQ2GenericPencilLift
  CycleQ2GenericSpecialization CycleQ2GenericWeightedCoordinates
  CycleQ2GenericWeightedMonicOpen CycleQ2GenericWeightedMonicCoefficients
  CycleQ2GenericWeightedMonicDensity CycleQ2MonicWeightedAffineEquation
  CycleQ2MonicWeightedPrimitiveIdentity CycleQ2MonicWeightedPrimitiveSpecialization
open CycleQ2GenericPencilOpen (ParameterIndex)
open CycleQ2GenericWeightedOpen (coefficientPoint)

variable (c : ParameterIndex → ℂ) (hc : endpointDifference c ≠ 0)
local notation "ep" => endpointDirection c hc

/-- The universal monic coefficients specialized to the two-parameter field. -/
def coefficientSpecialization : Coeff →+* coefficientField ep :=
  (aeval (coefficients ep c)).toRingHom

theorem coe_coefficientSpecialization (p : Coeff) :
    (coefficientSpecialization c hc p : RF) =
      eval₂Hom (algebraMap ℂ RF) (normalizedCoefficientPoint ep c) p := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    simp only [coefficientSpecialization, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      aeval_C, eval₂Hom_C]
    rfl
  | add p q hp hq => simp only [map_add, IntermediateField.coe_add, hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, IntermediateField.coe_mul, hp, eval₂Hom_X']
    simp only [coefficientSpecialization, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      aeval_X, coefficients_coe]

theorem map_universal_affine :
    MvPolynomial.map (coefficientSpecialization c hc) universalAffine = monicEquation ep c := by
  rw [universalAffine, CycleQ2WeightedAffineChartJets.map_chart,
    CycleQ2UniversalSurfaceCoefficientMap.map_sextic]
  simp only [coefficientSpecialization, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    aeval_X, monicEquation]

theorem spatial_multiple_eval
    (hL : coefficientPoint ep c fullSexticLeadingIndex ≠ 0)
    {d : Pol Coeff} {q : Coords Coeff}
    (hdiv : projection universalAffine d ∣ AdjoinRoot.of (separate universalAffine) q)
    (hq : MvPolynomial.map (coefficientSpecialization c hc) q ≠ 0) :
    value ep (MvPolynomial.map (coefficientSpecialization c hc) d) ≠ 0 := by
  let φ := coefficientSpecialization c hc
  let v := (value ep).comp (MvPolynomial.map φ)
  have hf : v universalAffine = 0 := by
    change value ep (MvPolynomial.map (coefficientSpecialization c hc) universalAffine) = 0
    rw [map_universal_affine]
    exact value_equation c hc hL
  apply evaluated_denominator_ne_zero hdiv φ hq v hf (![z 0, z 2, z 3] : Fin 3 → RF)
    (CycleQ2GenericWeightedSpatialIndependence.spatial_independent c hc hL)
  · intro a
    change value ep (MvPolynomial.map φ (C a)) = _
    rw [MvPolynomial.map_C]
    exact eval₂Hom_C _ _ _
  · intro j
    change value ep (MvPolynomial.map φ (X j.castSucc)) = _
    rw [MvPolynomial.map_X]
    change eval₂Hom _ affinePoint (X j.castSucc) = _
    rw [eval₂Hom_X']
    fin_cases j <;> rfl

end CycleQ2GenericWeightedSpatialDenominator
end

#print axioms CycleQ2GenericWeightedSpatialDenominator.coe_coefficientSpecialization
#print axioms CycleQ2GenericWeightedSpatialDenominator.map_universal_affine
#print axioms CycleQ2GenericWeightedSpatialDenominator.spatial_multiple_eval
end

section
/-!
# Evaluating a cleared primitive on the actual protected deformation

A divisibility identity on the normalized affine weighted equation yields
the protected exterior primitive whenever its common spatial denominator
survives evaluation in the deformed function field.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CycleQ2GenericWeightedCleared

open MvPolynomial CycleQ2GenericSpecialization CycleQ2GenericPencilLift
  CycleQ2GenericPencilOpen CycleQ2IncidenceNormalForm CycleQ2GenericWeightedOpen
  CycleQ2GenericWeightedCoordinates CycleQ2GenericWeightedMonicCoefficients
  CycleQ2GenericWeightedMonicDensity CycleQ2GenericWeightedTransfer CycleQ2AffineClearing
open CycleQ2MonicWeightedPrimitiveIdentity (Pol cleared divergence_iff_cleared)
open scoped BigOperators

variable (c : ParameterIndex → ℂ) (hc : endpointDifference c ≠ 0)
local notation "ep" => endpointDirection c hc

/-- A primitive for the normalized monic density on this single deformed pencil
specializes to a three-form whose exterior derivative is the protected four-form. -/
theorem exact_form_of_monic_primitive
    (hL : coefficientPoint ep c fullSexticLeadingIndex ≠ 0)
    (h : ∃ v : Fin 3 → RF, (∑ j, relativeDerivation ep j (v j)) =
      CycleQ2MonicWeightedPrimitiveIdentity.density (value ep) (monicEquation ep c)) :
    ∃ η : CycleQ2AffineExterior.Form 3, CycleQ2AffineExterior.exteriorD3 η =
      CycleQ2AffineExactness.residueSourceForm affineA :=
  exact_form_of_weighted_primitive ep (primitive_of_monic c hc hL h)

/-- Only the specified common denominator is evaluated. The cleared equation passes to
the actual rational-function field by the polynomial evaluation homomorphism. -/
theorem exact_form_of_monic_divisibility
    (hL : coefficientPoint ep c fullSexticLeadingIndex ≠ 0)
    (d : Pol (coefficientField ep)) (p : Fin 3 → Pol (coefficientField ep))
    (hd : value ep d ≠ 0)
    (h : monicEquation ep c ∣ cleared (monicEquation ep c) d p) :
    ∃ η : CycleQ2AffineExterior.Form 3, CycleQ2AffineExterior.exteriorD3 η =
      CycleQ2AffineExactness.residueSourceForm affineA := by
  have he : value ep (cleared (monicEquation ep c) d p) = 0 := by
    obtain ⟨q, hq⟩ := h
    rw [hq, map_mul, value_equation c hc hL, zero_mul]
  apply exact_form_of_monic_primitive c hc hL
  exact ⟨fun j => value ep (p j) / value ep d,
    (divergence_iff_cleared (value ep) (relativeDerivation ep) (monicEquation ep c) d p
      (CycleQ2GenericWeightedMonicDensity.normal_ne_zero c hc hL) hd
      (CycleQ2GenericWeightedMonicDensity.tangent_apply c hc hL)).mpr he⟩

/-- Every nonempty principal open of the normalized coefficient space admits an
actual deformed direction where the normalized primitive equation suffices. -/
theorem exists_monic_direction_with_transfer
    (f : MvPolynomial FullSexticTailIndex ℂ) (hf : f ≠ 0) :
    ∃ (s : ParameterIndex → ℂ) (hs : endpointDifference s ≠ 0),
      s fullSexticLeadingIndex = 1 ∧
      eval (fun e : FullSexticTailIndex => s e.val) f ≠ 0 ∧
      coefficientPoint (endpointDirection s hs) s fullSexticLeadingIndex ≠ 0 ∧
      eval₂Hom (algebraMap ℂ RF)
        (CycleQ2GenericWeightedMonicOpen.normalizedCoefficientPoint (endpointDirection s hs) s) f ≠ 0 ∧
      ((∃ v : Fin 3 → RF, (∑ j, relativeDerivation (endpointDirection s hs) j (v j)) =
          CycleQ2MonicWeightedPrimitiveIdentity.density
            (value (endpointDirection s hs)) (monicEquation (endpointDirection s hs) s)) →
        ∃ η : CycleQ2AffineExterior.Form 3, CycleQ2AffineExterior.exteriorD3 η =
          CycleQ2AffineExactness.residueSourceForm affineA) := by
  obtain ⟨s, hs, hm, he, hL, hgood⟩ :=
    CycleQ2GenericWeightedMonicOpen.exists_direction_in_monic_open f hf
  exact ⟨s, hs, hm, he, hL, hgood, exact_form_of_monic_primitive s hs hL⟩

end CycleQ2GenericWeightedCleared
end

#print axioms CycleQ2GenericWeightedCleared.exact_form_of_monic_primitive
#print axioms CycleQ2GenericWeightedCleared.exact_form_of_monic_divisibility

#print axioms CycleQ2GenericWeightedCleared.exists_monic_direction_with_transfer
end

section
/-!
# From a universal weighted primitive to the protected exterior form

A rational three-direction primitive in the universal normalized weighted
chart has polynomial numerators and a common spatial denominator. A nonzero
spatial multiple of the denominator chooses a principal open of the
coefficient space. On a protected deformation meeting that open the three
spatial coordinates remain algebraically independent, so the denominator
survives. The specialized identity supplies an exterior primitive on the
original protected hypersurface through Laurent coefficient extraction.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CycleQ2UniversalWeightedTransfer

open MvPolynomial
  CycleQ2IncidenceNormalForm CycleQ2MonicWeightedAffineEquation
  CycleQ2MonicWeightedPrimitiveSpecialization CycleQ2GenericPencilLift
  CycleQ2GenericWeightedMonicOpen CycleQ2GenericWeightedSpatialDenominator
  CycleQ2GenericWeightedCleared CycleQ2AffineClearing
open CycleQ2MonicWeightedPrimitiveIdentity (map_cleared)
open scoped BigOperators

/-- A rational primitive over the entire normalized coefficient function field suffices
for the original protected exterior form; the primitive may have poles in the deformation. -/
theorem exact_form_of_universal_weighted_primitive (hp : UniversalWeightedPrimitiveExists) :
    ∃ η : CycleQ2AffineExterior.Form 3, CycleQ2AffineExterior.exteriorD3 η =
      CycleQ2AffineExactness.residueSourceForm affineA := by
  obtain ⟨v, hv⟩ := hp
  have hm : (separate universalAffine).Monic := by rw [separate_universal]; exact monic _
  have h₃ : (separate universalAffine).natDegree = 3 := by rw [separate_universal]; exact natDegree _
  obtain ⟨a, d, p, q, ha, _, hdiv, hmul, hspec⟩ :=
    spread_with_spatial_multiple hm h₃ universal_normal_ne_zero v hv
  obtain ⟨c, hc, _, _, hL, hgood⟩ := exists_direction_in_monic_open a ha
  let φ := coefficientSpecialization c hc
  have hφ : φ a ≠ 0 := by
    intro hz
    apply hgood
    rw [← coe_coefficientSpecialization c hc a]
    exact congrArg
      (fun x : CycleQ2GenericWeightedMonicCoefficients.coefficientField (endpointDirection c hc) =>
        (x : CycleQ2GenericSpecialization.RF)) hz
  have hd := spatial_multiple_eval c hc hL hmul (hspec φ hφ).1
  apply exact_form_of_monic_divisibility c hc hL (MvPolynomial.map φ d) (fun j => MvPolynomial.map φ (p j)) hd
  simpa only [φ, map_cleared, map_universal_affine] using map_dvd (MvPolynomial.map φ) hdiv

theorem certificate_of_universal_weighted_primitive (h : UniversalWeightedPrimitiveExists) :
    HodgeComputer.HasCertificate HodgeSubmission.F HodgeSubmission.q HodgeSubmission.A :=
  CycleQ2AffineExactness.protected_certificate_of_exact_residueSourceForm
    (exact_form_of_universal_weighted_primitive h)

end CycleQ2UniversalWeightedTransfer
end

#print axioms CycleQ2UniversalWeightedTransfer.exact_form_of_universal_weighted_primitive
#print axioms CycleQ2UniversalWeightedTransfer.certificate_of_universal_weighted_primitive
end
