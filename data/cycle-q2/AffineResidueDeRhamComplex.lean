import Proposal.AffineChartResiduePrimitive

/-! # Relative transfer, pole reduction and the affine de Rham complex -/

set_option Elab.async false

/- Component: continuation_2/AffineWeightedTransfer.lean -/
section
/-!
# Actual paired-sign relative residue transfer

All coordinates and derivations below belong to the already constructed
function field of the protected chart X0=1.  The parameter is lambda=Y2/X2
and the weighted coordinate is X2^2.  An explicit change of divergence
coefficients transfers a three-direction relative primitive to the actual
four-direction affine residue equation.  No relative primitive, geometric
family, Leray statement, or cohomological vanishing is assumed to exist.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section

namespace CycleQ2AffineWeightedTransfer

open MvPolynomial HodgeComputer CycleQ2AffineClearing CycleQ2AffineHypersurface
  CycleQ2AffineResidueClosure CycleQ2AffineDifferentials HoldoutConstruction
open scoped BigOperators

abbrev K := AffineFunctionField
abbrev Poly := AmbientPoly 4

local instance coefficientCharZero : CharZero K :=
  charZero_of_injective_algebraMap (algebraMap ℂ K).injective
local instance coefficientIntAlgebra : Algebra ℤ K := Ring.toIntAlgebra _

/-- Coordinates are (X1,X2,Y0,Y1,Y2) in the protected X0=1 chart. -/
def z (i : Fin 5) : K := affineMap (X i)
def u : K := z 1
def v : K := z 4
def parameter : K := v / u

def E (i : Fin 4) : Derivation ℂ K K := complexTangent i

@[simp] theorem E_apply (i : Fin 4) (x : K) : E i x = affineTangent i x := rfl

@[simp] theorem E_u (i : Fin 4) : E i u = if i = 0 then 1 else 0 := by
  simpa [E, u, z, eq_comm] using affineTangent_coordinate i 0

@[simp] theorem E_v (i : Fin 4) : E i v = if i = 3 then 1 else 0 := by
  simpa [E, v, z, eq_comm] using affineTangent_coordinate i 3

/-- Nonvanishing is proved in the actual quotient field by differentiating
an alleged zero coordinate; no additional divisibility premise is used. -/
theorem u_ne_zero : u ≠ 0 := by
  intro hu
  have h : E 0 u = 1 := by simp only [E_u, if_true]
  rw [hu, map_zero] at h
  exact zero_ne_one h

@[simp] theorem E_two (i : Fin 4) : E i (2 : K) = 0 := (E i).map_natCast 2

@[simp] theorem E_parameter_zero : E 0 parameter = -parameter / u := by
  rw [parameter, Derivation.leibniz_div]
  simp only [E_u, E_v, Fin.reduceEq, if_false, if_true, smul_eq_mul, mul_zero,
    zero_sub, mul_one]
  ring

@[simp] theorem E_parameter_one : E 1 parameter = 0 := by
  rw [parameter, Derivation.leibniz_div]
  simp only [E_u, E_v, Fin.reduceEq, if_false, smul_eq_mul, mul_zero, sub_self]

@[simp] theorem E_parameter_two : E 2 parameter = 0 := by
  rw [parameter, Derivation.leibniz_div]
  simp only [E_u, E_v, Fin.reduceEq, if_false, smul_eq_mul, mul_zero, sub_self]

@[simp] theorem E_parameter_three : E 3 parameter = 1 / u := by
  rw [parameter, Derivation.leibniz_div]
  simp only [E_u, E_v, Fin.reduceEq, if_false, if_true, smul_eq_mul, mul_zero,
    sub_zero, mul_one]
  field_simp [u_ne_zero]

/-- Actual relative derivations in the Y0, Y1, X2^2 directions. -/
def relativeDerivation : Fin 3 → Derivation ℂ K K :=
  ![E 1, E 2, (2 * u)⁻¹ • (E 0 + parameter • E 3)]

@[simp] theorem relativeDerivation_zero (x : K) : relativeDerivation 0 x = E 1 x := rfl
@[simp] theorem relativeDerivation_one (x : K) : relativeDerivation 1 x = E 2 x := rfl
@[simp] theorem relativeDerivation_two (x : K) :
    relativeDerivation 2 x = (E 0 x + parameter * E 3 x) / (2 * u) := by
  change ((2 * u)⁻¹ • (E 0 + parameter • E 3)) x = _
  simp only [Derivation.smul_apply, Derivation.add_apply, smul_eq_mul]
  ring

/-- Every relative direction fixes the actual quotient parameter. -/
theorem relative_parameter (j : Fin 3) : relativeDerivation j parameter = 0 := by
  fin_cases j
  · exact E_parameter_one
  · exact E_parameter_two
  · change relativeDerivation 2 parameter = 0
    rw [relativeDerivation_two, E_parameter_zero, E_parameter_three]
    ring

/-- The radial relative direction has zero ordinary coordinate divergence. -/
theorem radial_divergence : E 0 (1 / (2 * u)) + E 3 (parameter / (2 * u)) = 0 := by
  simp only [Derivation.leibniz_div, Derivation.leibniz, Derivation.map_one_eq_zero,
    E_two, E_u, E_parameter_three, smul_eq_mul, Fin.reduceEq, if_false,
    if_true, mul_zero, add_zero, mul_one]
  field_simp [u_ne_zero]
  ring

/-- The actual weighted numerator before multiplying by lambda. -/
def weightedSource : Poly := X 0 ^ 2 * X 1 ^ 4 * X 2 ^ 2 * X 3 ^ 2

theorem parameter_mul_u : parameter * u = v := by
  unfold parameter
  exact div_mul_cancel₀ v u_ne_zero

/-- The actual polynomial equation in the weighted coordinate X2^2 and
the quotient parameter Y2/X2. -/
def weightedEquation (a c d w l : K) : K :=
  1 + a ^ 6 + c ^ 6 + d ^ 6 + (1 + l ^ 6) * w ^ 3 +
    (a * c * d) / 2 + (l * a ^ 3 * d * w) / 2 + (l * c * w ^ 2) / 2

theorem weighted_equation : weightedEquation (z 0) (z 2) (z 3) (u ^ 2) parameter = 0 := by
  have hhalf : affineMap (C (1 / 2 : ℂ)) = (1 / 2 : K) := by
    change (algebraMap ℂ K) (1 / 2 : ℂ) = (1 / 2 : K)
    simp only [map_div₀, map_one, map_ofNat]
  have hf := (congrArg affineMap CycleQ2AffineGeometry.affineF_formula).symm.trans
    affineMap_F
  simp only [map_add, map_mul, map_pow, map_one, hhalf] at hf
  change 1 + z 0 ^ 6 + u ^ 6 + z 2 ^ 6 + z 3 ^ 6 + v ^ 6 +
    (1 / 2 : K) * (z 0 * z 2 * z 3 + z 0 ^ 3 * u * z 3 * v +
      u ^ 3 * v * z 2) = 0 at hf
  rw [← parameter_mul_u] at hf
  calc
    weightedEquation (z 0) (z 2) (z 3) (u ^ 2) parameter =
      1 + z 0 ^ 6 + u ^ 6 + z 2 ^ 6 + z 3 ^ 6 + (parameter * u) ^ 6 +
        (1 / 2 : K) * (z 0 * z 2 * z 3 + z 0 ^ 3 * u * z 3 * (parameter * u) +
          u ^ 3 * (parameter * u) * z 2) := by
            unfold weightedEquation
            ring
    _ = 0 := hf

/-- The actual weighted numerator is a²c²d²w². -/
theorem weighted_source_value :
    affineMap weightedSource = z 0 ^ 2 * z 2 ^ 2 * z 3 ^ 2 * (u ^ 2) ^ 2 := by
  simp only [weightedSource, map_mul, map_pow]
  change z 0 ^ 2 * u ^ 4 * z 2 ^ 2 * z 3 ^ 2 = _
  ring

theorem affineA_formula : affineA =
    X 0 ^ 2 * X 1 ^ 3 * X 2 ^ 2 * X 3 ^ 2 * X 4 := by
  have h1 : Fin.cases (1 : Poly) X (1 : Fin 6) = X (0 : Fin 5) := rfl
  have h2 : Fin.cases (1 : Poly) X (2 : Fin 6) = X (1 : Fin 5) := rfl
  have h3 : Fin.cases (1 : Poly) X (3 : Fin 6) = X (2 : Fin 5) := rfl
  have h4 : Fin.cases (1 : Poly) X (4 : Fin 6) = X (3 : Fin 5) := rfl
  have h5 : Fin.cases (1 : Poly) X (5 : Fin 6) = X (4 : Fin 5) := rfl
  simp [affineA, CycleQ2AffineChart.dehomogenize, HodgeSubmission.A, h1, h2, h3, h4, h5]

theorem source_product : affineA * X 1 = weightedSource * X 4 := by
  rw [affineA_formula]
  unfold weightedSource
  ring

private theorem normal_partial_product_coordinate (P : Poly) (j : Fin 5) (hj : j ≠ 0) :
    pderiv 0 (P * X j) = pderiv 0 P * X j := by
  simp [pderiv_X, hj, mul_comm]

theorem source_first_jet_product : pderiv 0 affineA * X 1 = pderiv 0 weightedSource * X 4 := by
  have h := congrArg (pderiv (0 : Fin 5)) source_product
  simpa only [normal_partial_product_coordinate _ _ (by decide : (1 : Fin 5) ≠ 0),
    normal_partial_product_coordinate _ _ (by decide : (4 : Fin 5) ≠ 0)] using h

theorem source_second_jet_product :
    pderiv 0 (pderiv 0 affineA) * X 1 = pderiv 0 (pderiv 0 weightedSource) * X 4 := by
  have h := congrArg (pderiv (0 : Fin 5)) source_first_jet_product
  simpa only [normal_partial_product_coordinate _ _ (by decide : (1 : Fin 5) ≠ 0),
    normal_partial_product_coordinate _ _ (by decide : (4 : Fin 5) ≠ 0)] using h

private theorem mapped_source_ratio (P Q : Poly) (h : P * X 1 = Q * X 4) :
    affineMap P = parameter * affineMap Q := by
  have hm := congrArg affineMap h
  simp only [map_mul] at hm
  change affineMap P * u = affineMap Q * v at hm
  rw [(eq_div_iff u_ne_zero).mpr hm]
  unfold parameter
  ring

theorem affine_source_ratio : affineMap affineA = parameter * affineMap weightedSource :=
  mapped_source_ratio _ _ source_product

/-- The literal normal jets prove the normal-source scaling for the exact
protected numerator; the normal variable is not changed. -/
theorem normal_source_ratio :
    affineNormalSource affineA = parameter * affineNormalSource weightedSource := by
  have h0 := mapped_source_ratio _ _ source_product
  have h1 := mapped_source_ratio _ _ source_first_jet_product
  have h2 := mapped_source_ratio _ _ source_second_jet_product
  simp only [affineNormalSource, SplitHigherResidue.normalSourceTwo, h0, h1, h2]
  ring

/-- The actual coefficient transfer in the (X2,Y0,Y1,Y2) directions. -/
def transferVector (w : Fin 3 → K) : Fin 4 → K :=
  ![parameter * w 2 / (2 * u), parameter * w 0, parameter * w 1,
    parameter ^ 2 * w 2 / (2 * u)]

def normalDensity : K := affineMap (pderiv 0 affineF)

def relativeResidueExpression (w : Fin 3 → K) : K :=
  affineNormalSource weightedSource +
    (∑ j, relativeDerivation j (w j)) -
    (∑ j, w j * relativeDerivation j normalDensity) / normalDensity

private theorem sum_three (f : Fin 3 → K) : (∑ i, f i) = f 0 + f 1 + f 2 := by
  have h : (∑ i, f i) = f 0 + (f 1 + f 2) := by
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    rfl
  rw [h]
  ring

private theorem sum_four (f : Fin 4 → K) : (∑ i, f i) = f 0 + f 1 + f 2 + f 3 := by
  have h : (∑ i, f i) = f 0 + (f 1 + (f 2 + f 3)) := by
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    rfl
  rw [h]
  ring

@[simp] theorem transferVector_zero (w : Fin 3 → K) :
    transferVector w 0 = parameter * w 2 / (2 * u) := rfl
@[simp] theorem transferVector_one (w : Fin 3 → K) :
    transferVector w 1 = parameter * w 0 := rfl
@[simp] theorem transferVector_two (w : Fin 3 → K) :
    transferVector w 2 = parameter * w 1 := rfl
@[simp] theorem transferVector_three (w : Fin 3 → K) :
    transferVector w 3 = parameter ^ 2 * w 2 / (2 * u) := rfl

/-- The product-rule terms cancel because the radial direction has zero
divergence and fixes lambda. All derivatives are the actual field operators. -/
theorem transferred_divergence (w : Fin 3 → K) :
    (∑ i, E i (transferVector w i)) =
      parameter * ∑ j, relativeDerivation j (w j) := by
  rw [sum_four, sum_three]
  simp only [transferVector_zero, transferVector_one, transferVector_two,
    transferVector_three, relativeDerivation_zero,
    relativeDerivation_one, relativeDerivation_two, Derivation.leibniz_div,
    Derivation.leibniz, Derivation.leibniz_pow, E_parameter_zero, E_parameter_one,
    E_parameter_two, E_parameter_three, E_two, E_u, smul_eq_mul, nsmul_eq_mul,
    Fin.reduceEq, if_true, if_false, Nat.cast_ofNat, Nat.reduceSub, pow_one]
  field_simp [u_ne_zero]
  ring

/-- The logarithmic normal-density term undergoes the same transfer. -/
theorem transferred_density_term (w : Fin 3 → K) :
    (∑ i, transferVector w i * E i normalDensity) =
      parameter * ∑ j, w j * relativeDerivation j normalDensity := by
  rw [sum_four, sum_three]
  simp only [transferVector_zero, transferVector_one, transferVector_two,
    transferVector_three, relativeDerivation_zero,
    relativeDerivation_one, relativeDerivation_two]
  ring

/-- Exact actual-field relative-PDE transfer for the protected source. -/
theorem affine_residue_transfer (w : Fin 3 → K) :
    affineResidueExpression affineA (transferVector w) =
      parameter * relativeResidueExpression w := by
  unfold affineResidueExpression residueDivergence fieldDivergence
  rw [normal_source_ratio]
  change parameter * affineNormalSource weightedSource +
    ((∑ i, E i (transferVector w i)) -
      (∑ i, transferVector w i * E i normalDensity) / normalDensity) = _
  rw [transferred_divergence, transferred_density_term]
  unfold relativeResidueExpression
  ring

/-- An actual relative three-direction primitive suffices for the original
protected certificate. Its existence is not asserted in this module. -/
theorem protected_certificate_of_relative_primitive
    (h : ∃ w : Fin 3 → K, relativeResidueExpression w = 0) :
    HasCertificate HodgeSubmission.F HodgeSubmission.q HodgeSubmission.A := by
  obtain ⟨w, hw⟩ := h
  apply protected_certificate_of_affine_residue_primitive
  refine ⟨transferVector w, ?_⟩
  rw [affine_residue_transfer, hw, mul_zero]

end CycleQ2AffineWeightedTransfer

#print axioms CycleQ2AffineWeightedTransfer.u_ne_zero
#print axioms CycleQ2AffineWeightedTransfer.normal_source_ratio
#print axioms CycleQ2AffineWeightedTransfer.weighted_equation
#print axioms CycleQ2AffineWeightedTransfer.affine_residue_transfer
#print axioms CycleQ2AffineWeightedTransfer.protected_certificate_of_relative_primitive
end
end


/- Uncompiled continuation: PoleReduction.lean (2026-11-12). -/
section Q2UncompiledPoleReduction

/-!
# Explicit pole-three reduction for the actual Q2 affine chart

Source-only draft against the 8d88f06e782704e301a6e817195f907e816f46d8
project tree. This file has deliberately NOT been compiled.

The calculations use the existing ambient rational-function field, its
complex-linear coordinate derivation, the actual protected polynomial,
and the existing regular-subring specialization map. They introduce no
new existence assumption.

On the ambient open where `g = partial_0 f` is invertible, put
`D_t = g^(-1) partial_0` and `b = a/g`. The rational coefficient

  `psi = -b/(2*f^2) - D_t(b)/(2*f)`

satisfies

  `D_t(psi) = b/f^3 - (D_t(D_t(b))/2)/f`.

For `vol = dx1 wedge ... wedge dx4`, this is the coefficient identity
behind `omega - d(psi * vol) = (D_t^2(b)/2) * (df/f) wedge vol`.
This module proves the coefficient identity and binds the resulting
regular simple-pole coefficient to the existing `residueSourceForm`.
It does not define a cohomological residue map or prove that the source
form has a primitive. Those geometric steps remain separate obligations.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace CycleQ2ExplicitPoleReduction

open MvPolynomial HodgeComputer CycleQ2Bridge CycleQ2ComplexDerivations
open CycleQ2AffineClearing CycleQ2AffineGeometry CycleQ2ActualResidueClosure
open CycleQ2AffineResidue CycleQ2AffineResidueClosure
open HoldoutConstruction SplitHigherResidue

section FieldCalculus

variable {R K : Type*} [CommRing R] [Field K] [CharZero K] [Algebra R K]

/-- The normalized normal derivation. Its normalization is proved for the
actual Q2 equation below; it is not supplied as an existence hypothesis. -/
def normalized (D : Derivation R K K) (g : K) : Derivation R K K :=
  g⁻¹ • D

theorem normalized_apply (D : Derivation R K K) (g x : K) :
    normalized D g x = D x / g := by
  simp only [normalized, Derivation.smul_apply, smul_eq_mul, div_eq_mul_inv]
  ring

/-- Two elementary integrations in the normal direction lower a third
order pole to a first order pole. This is an identity of actual field
derivations, with the equation and its nonzero denominator explicit. -/
theorem triple_pole_identity (D : Derivation R K K) (f b : K)
    (hf : f ≠ 0) (hDf : D f = 1) :
    D (-b / (2 * f ^ 2) - D b / (2 * f)) =
      b / f ^ 3 - (D (D b) / 2) / f := by
  have htwo : D (2 : K) = 0 := D.map_natCast 2
  simp only [map_sub, map_neg, Derivation.leibniz_div,
    Derivation.leibniz, Derivation.leibniz_pow, htwo, hDf,
    smul_eq_mul, nsmul_eq_mul]
  field_simp [hf]
  ring

/-- The second normalized derivative is the existing normal-source
coefficient divided by the normal Jacobian. -/
theorem second_normal_coefficient (D : Derivation R K K) (a g : K)
    (hg : g ≠ 0) :
    normalized D g (normalized D g (a / g)) / 2 =
      normalSourceTwo a (D a) (D (D a)) g (D g) (D (D g)) / g := by
  simp only [normalized_apply, normalSourceTwo,
    Derivation.leibniz_div, Derivation.leibniz_inv,
    Derivation.leibniz, Derivation.leibniz_pow,
    map_sub, map_add, map_neg, smul_eq_mul, nsmul_eq_mul]
  ring_nf
  field_simp [hg]
  ring

end FieldCalculus

/-- The existing ambient function field, before imposing the equation. -/
abbrev RF := RationalFunction 4

def ambientEquation : RF := polynomialMap 4 affineF

def normalGradient : RF := polynomialMap 4 (pderiv 0 affineF)

/-- The genuine complex-linear partial derivative of the ambient field. -/
def coordinateDerivative : Derivation ℂ RF RF := complexRationalPartial 4 0

theorem coordinateDerivative_polynomial (P : AmbientPoly 4) :
    coordinateDerivative (polynomialMap 4 P) = polynomialMap 4 (pderiv 0 P) :=
  complexRationalPartial_map 4 0 P

theorem ambientEquation_ne_zero : ambientEquation ≠ 0 :=
  polynomialMap_ne_zero affineF_ne_zero

theorem normalGradient_ne_zero : normalGradient ≠ 0 :=
  polynomialMap_ne_zero affine_normal_ne_zero

theorem coordinateDerivative_equation :
    coordinateDerivative ambientEquation = normalGradient :=
  coordinateDerivative_polynomial affineF

/-- This is `g^(-1) partial_0` on the actual ambient rational functions. -/
def normalDerivative : Derivation ℂ RF RF :=
  normalized coordinateDerivative normalGradient

theorem normalDerivative_apply (z : RF) :
    normalDerivative z = coordinateDerivative z / normalGradient :=
  normalized_apply coordinateDerivative normalGradient z

theorem normalDerivative_equation : normalDerivative ambientEquation = 1 := by
  rw [normalDerivative_apply, coordinateDerivative_equation,
    div_self normalGradient_ne_zero]

def density (A : AmbientPoly 4) : RF := polynomialMap 4 A / normalGradient

/-- The coefficient of the explicit ambient four-form correction. -/
def poleCorrection (A : AmbientPoly 4) : RF :=
  -density A / (2 * ambientEquation ^ 2) -
    normalDerivative (density A) / (2 * ambientEquation)

/-- The coefficient of `(df/f) wedge vol` after the explicit reduction. -/
def simpleCoefficient (A : AmbientPoly 4) : RF :=
  normalDerivative (normalDerivative (density A)) / 2

theorem simpleCoefficient_eq_actualNormalSource (A : AmbientPoly 4) :
    simpleCoefficient A = actualNormalSource affineF A / normalGradient := by
  change normalized coordinateDerivative normalGradient
      (normalized coordinateDerivative normalGradient
        (polynomialMap 4 A / normalGradient)) / 2 = _
  rw [second_normal_coefficient coordinateDerivative
    (polynomialMap 4 A) normalGradient normalGradient_ne_zero]
  simp only [coordinateDerivative, normalGradient,
    complexRationalPartial_map, actualNormalSource]

/-- Pole reduction for the literal protected equation, with all
normalization and nonvanishing side conditions already discharged. -/
theorem actual_normal_pole_reduction (A : AmbientPoly 4) :
    normalDerivative (poleCorrection A) =
      density A / ambientEquation ^ 3 - simpleCoefficient A / ambientEquation := by
  simpa only [poleCorrection, simpleCoefficient] using
    triple_pole_identity normalDerivative ambientEquation (density A)
      ambientEquation_ne_zero normalDerivative_equation

/-- The same identity expressed relative to the original coordinate
volume, instead of the normal-coordinate volume. -/
theorem actual_coordinate_pole_reduction (A : AmbientPoly 4) :
    coordinateDerivative (poleCorrection A) =
      polynomialMap 4 A / ambientEquation ^ 3 -
        actualNormalSource affineF A / ambientEquation := by
  have h := actual_normal_pole_reduction A
  rw [normalDerivative_apply, density, simpleCoefficient_eq_actualNormalSource] at h
  have hmul := (eq_div_iff normalGradient_ne_zero).mp h.symm
  calc
    coordinateDerivative (poleCorrection A) =
        ((polynomialMap 4 A / normalGradient) / ambientEquation ^ 3 -
          (actualNormalSource affineF A / normalGradient) / ambientEquation) *
          normalGradient := hmul.symm
    _ = _ := by
      field_simp [ambientEquation_ne_zero, normalGradient_ne_zero]

/-- A regular-subring representative of the simple-pole coefficient.
The zero vector here merely selects the already-constructed normal
source from `residueExpressionRegular`; it is not asserted to solve
the residue PDE. -/
def simpleCoefficientRegular (A : AmbientPoly 4) : RegularAtF :=
  residueExpressionRegular A (fun _ : Fin 4 => 0) * normalInverse

theorem simpleCoefficientRegular_val (A : AmbientPoly 4) :
    ((simpleCoefficientRegular A : RegularAtF) : RF) = simpleCoefficient A := by
  rw [simpleCoefficient_eq_actualNormalSource]
  change ((residueExpressionRegular A (fun _ : Fin 4 => 0) : RegularAtF) : RF) *
    (normalInverse : RF) = _
  rw [residueExpressionRegular_val, normalInverse_val]
  simp [actualResidueExpression, residueDivergence,
    HoldoutConstruction.fieldDivergence, normalGradient, div_eq_mul_inv]

/-- The first-order residue coefficient has no pole along the protected
equation. Its possible auxiliary poles are already legal. -/
theorem simpleCoefficient_regular (A : AmbientPoly 4) :
    CycleQ2Regularity.RegularAlong affineF (simpleCoefficient A) := by
  rw [← simpleCoefficientRegular_val A]
  exact (simpleCoefficientRegular A).property

/-- This is the existing algebraic specialization of a regular rational
coefficient modulo `affineF`, not an assumed cohomological residue map. -/
theorem residue_simpleCoefficientRegular (A : AmbientPoly 4) :
    residue (simpleCoefficientRegular A) =
      affineNormalSource A / CycleQ2AffineExactness.normalDensity := by
  rw [simpleCoefficientRegular, map_mul,
    residue_residueExpressionRegular, residue_normalInverse]
  simp [affineResidueExpression, residueDivergence,
    HoldoutConstruction.fieldDivergence,
    CycleQ2AffineExactness.normalDensity, div_eq_mul_inv]

/-- The simple-pole coefficient gives exactly the already-defined top
exterior form on the actual hypersurface function field. No exactness
or vanishing of this form is assumed or concluded. -/
theorem simple_residue_form_eq_source (A : AmbientPoly 4) :
    residue (simpleCoefficientRegular A) • CycleQ2AffineExterior.volume =
      CycleQ2AffineExactness.residueSourceForm A := by
  rw [residue_simpleCoefficientRegular]
  rfl

/-- Specialization to the unchanged protected Q2 numerator. -/
theorem protected_simple_residue_form_eq_source :
    residue (simpleCoefficientRegular affineA) • CycleQ2AffineExterior.volume =
      CycleQ2AffineExactness.residueSourceForm affineA :=
  simple_residue_form_eq_source affineA

end CycleQ2ExplicitPoleReduction

end

end Q2UncompiledPoleReduction


/- Uncompiled continuation: TopDeRham.lean (2026-11-12). -/
section Q2UncompiledTopDeRham

/-!
# The actual generic-point top de Rham quotient

Development continuation. Compilation status is recorded in `solution.md`.

This module takes the quotient of the existing genuine fourth exterior power
by the image of the existing complex-linear exterior differential. It supplies
the precise target for a future comparison theorem. It does not assert that
the protected residue class is zero, introduce a cohomological vanishing
assumption as an axiom, or prove divisor support.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace CycleQ2AffineTopCohomology

open CycleQ2AffineDifferentials CycleQ2AffineExterior

/-- There are no fifth exterior forms: the actual relative Kähler module
has the already constructed four-element coordinate basis. -/
instance formFiveSubsingleton : Subsingleton (Form 5) := by
  refine ⟨?_⟩
  intro η ξ
  apply (coordinateBasis.exteriorPower 5).repr.injective
  apply Finsupp.ext
  intro s
  have hcard : (s : Finset (Fin 4)).card ≤ 4 := by
    simpa using Finset.card_le_univ (s : Finset (Fin 4))
  have hs : (s : Finset (Fin 4)).card = 5 := s.property
  exact False.elim (by omega)

/-- Any possible outgoing differential in top degree is zero. This
statement does not require constructing the lower-degree de Rham complex. -/
theorem to_formFive_eq_zero (δ : Form 4 →ₗ[ℂ] Form 5) : δ = 0 := by
  apply LinearMap.ext
  intro ω
  exact Subsingleton.elim _ _

/-- Exact fourth forms form a complex subspace. They are not being treated
as a subspace over the full function field. -/
def exactTopForms : Submodule ℂ (Form 4) :=
  LinearMap.range exteriorD3

/-- The actual top-degree algebraic de Rham quotient at the generic point.
All fourth forms are closed because the fifth exterior power vanishes. -/
abbrev TopDeRham := (Form 4) ⧸ exactTopForms

/-- The quotient map on actual rational fourth forms. -/
def classOf : Form 4 →ₗ[ℂ] TopDeRham :=
  exactTopForms.mkQ

/-- Zero in this quotient means existence of an actual rational three-form
primitive, with the original exterior derivative and the original sign. -/
theorem classOf_eq_zero_iff (ω : Form 4) :
    classOf ω = 0 ↔ ∃ η : Form 3, exteriorD3 η = ω := by
  change (Submodule.Quotient.mk ω : TopDeRham) = 0 ↔ _
  rw [Submodule.Quotient.mk_eq_zero]
  change ω ∈ LinearMap.range exteriorD3 ↔ _
  exact LinearMap.mem_range

@[simp] theorem classOf_exteriorD3 (η : Form 3) :
    classOf (exteriorD3 η) = 0 :=
  (classOf_eq_zero_iff _).mpr ⟨η, rfl⟩

/-- Adding an actual exact form preserves the class. -/
theorem classOf_add_exteriorD3 (ω : Form 4) (η : Form 3) :
    classOf (ω + exteriorD3 η) = classOf ω := by
  calc
    classOf (ω + exteriorD3 η) =
        classOf ω + classOf (exteriorD3 η) := classOf.map_add ω (exteriorD3 η)
    _ = classOf ω + 0 :=
      congrArg (fun c : TopDeRham => classOf ω + c) (classOf_exteriorD3 η)
    _ = classOf ω := add_zero _

/-- The class of the already defined positive residue source form. -/
def residueClass (A : HodgeComputer.AmbientPoly 4) : TopDeRham :=
  classOf (CycleQ2AffineExactness.residueSourceForm A)

theorem residueClass_eq_zero_iff (A : HodgeComputer.AmbientPoly 4) :
    residueClass A = 0 ↔
      ∃ η : Form 3,
        exteriorD3 η = CycleQ2AffineExactness.residueSourceForm A :=
  classOf_eq_zero_iff _

/-- The quotient criterion is bound to the existing four-function
equation. Neither vanishing nor existence is asserted here. -/
theorem residueClass_eq_zero_iff_primitive
    (A : HodgeComputer.AmbientPoly 4) :
    residueClass A = 0 ↔
      ∃ w : Fin 4 → CycleQ2AffineHypersurface.AffineFunctionField,
        CycleQ2AffineResidueClosure.affineResidueExpression A w = 0 :=
  (residueClass_eq_zero_iff A).trans
    (CycleQ2AffineExactness.exact_residueSourceForm_iff A)

section UniversalProperty

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- A complex-linear map on forms that kills actual differentials factors
through the quotient. This is an algebraic universal property, not a
constructed Betti or sheaf-cohomology comparison map. -/
def descend (Φ : Form 4 →ₗ[ℂ] V)
    (hΦ : ∀ η : Form 3, Φ (exteriorD3 η) = 0) :
    TopDeRham →ₗ[ℂ] V :=
  exactTopForms.liftQ Φ (by
    rintro ω ⟨η, rfl⟩
    exact hΦ η)

@[simp] theorem descend_classOf (Φ : Form 4 →ₗ[ℂ] V)
    (hΦ : ∀ η : Form 3, Φ (exteriorD3 η) = 0) (ω : Form 4) :
    descend Φ hΦ (classOf ω) = Φ ω :=
  rfl

/-- Once an injective comparison map is actually constructed, vanishing
of its image yields an actual primitive. The comparison map, its
injectivity, and vanishing remain explicit hypotheses. -/
theorem exact_of_injective_comparison (comparison : TopDeRham →ₗ[ℂ] V)
    (hinj : Function.Injective comparison) (ω : Form 4)
    (hzero : comparison (classOf ω) = 0) :
    ∃ η : Form 3, exteriorD3 η = ω := by
  apply (classOf_eq_zero_iff ω).mp
  apply hinj
  simpa only [map_zero] using hzero

end UniversalProperty

/-- The already established homogeneous certificate constructor can be
applied to a proved zero class. This theorem does not prove that class
zero and is not a replacement for missing_geometric_existence. -/
theorem protected_certificate_of_residueClass_eq_zero
    (h : residueClass CycleQ2AffineClearing.affineA = 0) :
    HodgeComputer.HasCertificate
      HodgeSubmission.F HodgeSubmission.q HodgeSubmission.A :=
  CycleQ2AffineExactness.protected_certificate_of_exact_residueSourceForm
    ((residueClass_eq_zero_iff CycleQ2AffineClearing.affineA).mp h)

end CycleQ2AffineTopCohomology

end

end Q2UncompiledTopDeRham


/- Component: continuation_20261112/AffineDeRhamComplex.lean -/
section Q2UncompiledAffineDeRhamComplex

/-!
# The lower exterior differentials on the protected affine function field

Development continuation, 12 November 2026. Compilation status is recorded
in `solution.md`.
All the forms below
are exterior powers of the existing actual Kaehler differential module.
The differential in degree three is the existing residue differential.

The coordinate construction uses the four already constructed commuting
tangent derivations of the protected function field. The scalar-times-wedge
identities identify the new maps with exterior differentiation; the three
successive-composition identities supply the actual complex identities.
No comparison with singular cohomology or geometric vanishing is asserted.
-/

section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2AffineDeRhamComplex

open CycleQ2AffineHypersurface CycleQ2AffineDifferentials CycleQ2AffineExterior
open scoped BigOperators

/-- The six increasing pairs, in lexicographic order. -/
def pairLeft : Fin 6 → Fin 4 := ![0, 0, 0, 1, 1, 2]

def pairRight : Fin 6 → Fin 4 := ![1, 2, 3, 2, 3, 3]

def pairCoordinates (k : Fin 6) : Fin 2 → Fin 4 :=
  ![pairLeft k, pairRight k]

def pairIndex : Fin 6 → Set.powersetCard (Fin 4) 2 :=
  ![⟨{0, 1}, by change ({0, 1} : Finset (Fin 4)).card = 2; decide⟩,
    ⟨{0, 2}, by change ({0, 2} : Finset (Fin 4)).card = 2; decide⟩,
    ⟨{0, 3}, by change ({0, 3} : Finset (Fin 4)).card = 2; decide⟩,
    ⟨{1, 2}, by change ({1, 2} : Finset (Fin 4)).card = 2; decide⟩,
    ⟨{1, 3}, by change ({1, 3} : Finset (Fin 4)).card = 2; decide⟩,
    ⟨{2, 3}, by change ({2, 3} : Finset (Fin 4)).card = 2; decide⟩]

theorem pairIndex_bijective : Function.Bijective pairIndex := by
  constructor
  · decide
  · rintro ⟨s, hs⟩
    obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hs
    -- Only Fin 4 and equality of explicit finsets are enumerated here.
    -- This avoids reducing the transported Fintype of powersetCard.
    fin_cases a <;> fin_cases b <;> first
      | exact (hab rfl).elim
      | (refine ⟨0, ?_⟩; apply Subtype.ext; dsimp only [pairIndex] <;> decide)
      | (refine ⟨1, ?_⟩; apply Subtype.ext; dsimp only [pairIndex] <;> decide)
      | (refine ⟨2, ?_⟩; apply Subtype.ext; dsimp only [pairIndex] <;> decide)
      | (refine ⟨3, ?_⟩; apply Subtype.ext; dsimp only [pairIndex] <;> decide)
      | (refine ⟨4, ?_⟩; apply Subtype.ext; dsimp only [pairIndex] <;> decide)
      | (refine ⟨5, ?_⟩; apply Subtype.ext; dsimp only [pairIndex] <;> decide)

def pairEquiv : Fin 6 ≃ Set.powersetCard (Fin 4) 2 :=
  Equiv.ofBijective pairIndex pairIndex_bijective

theorem pairCoordinates_orderEmb (k : Fin 6) :
    pairCoordinates k =
      (pairIndex k : Finset (Fin 4)).orderEmbOfFin (pairIndex k).property := by
  apply Finset.orderEmbOfFin_unique (pairIndex k).property
  · intro j
    fin_cases k <;> fin_cases j <;> decide
  · fin_cases k <;> decide

/-- A basis of the genuine second exterior power, not a replacement module
of formal coefficient vectors. -/
def secondBasis : Module.Basis (Fin 6) K (Form 2) :=
  (coordinateBasis.exteriorPower 2).reindex pairEquiv.symm

theorem secondBasis_apply (k : Fin 6) :
    secondBasis k = exteriorPower.ιMulti K 2
      (coordinateDifferential ∘ pairCoordinates k) := by
  rw [secondBasis, Module.Basis.reindex_apply, Equiv.symm_symm]
  change coordinateBasis.exteriorPower 2 (pairIndex k) = _
  rw [exteriorPower.basis_apply]
  unfold exteriorPower.ιMulti_family
  congr 1
  funext j
  simp only [Function.comp_apply, coordinateBasis_apply,
    Set.powersetCard.ofFinEmbEquiv_symm_apply, ← pairCoordinates_orderEmb]

/-- The actual two-by-two minor formula for exterior coordinates. -/
theorem secondBasis_repr_wedge (v : Fin 2 → Omega) (k : Fin 6) :
    secondBasis.repr (exteriorPower.ιMulti K 2 v) k =
      coordinateBasis.repr (v 0) (pairLeft k) *
        coordinateBasis.repr (v 1) (pairRight k) -
      coordinateBasis.repr (v 0) (pairRight k) *
        coordinateBasis.repr (v 1) (pairLeft k) := by
  rw [secondBasis, Module.Basis.repr_reindex_apply, Equiv.symm_symm]
  change (coordinateBasis.exteriorPower 2).repr _ (pairIndex k) = _
  rw [exteriorPower.basis_repr_apply, exteriorPower.ιMultiDual_apply_ιMulti]
  simp only [Set.powersetCard.ofFinEmbEquiv_symm_apply,
    ← pairCoordinates_orderEmb, Matrix.det_fin_two, Matrix.of_apply,
    Module.Basis.coord_apply, pairCoordinates,
    Matrix.cons_val_zero, Matrix.cons_val_one]

/-- The corresponding determinant formula in degree three, using the
existing basis indexed by the omitted coordinate. -/
theorem thirdBasis_repr_wedge (v : Fin 3 → Omega) (i : Fin 4) :
    thirdBasis.repr (exteriorPower.ιMulti K 3 v) i =
      (Matrix.of fun j k => coordinateBasis.repr (v j) (i.succAbove k)).det := by
  rw [thirdBasis, Module.Basis.repr_reindex_apply, Equiv.symm_symm]
  change (coordinateBasis.exteriorPower 3).repr _ (omitIndex i) = _
  rw [exteriorPower.basis_repr_apply, exteriorPower.ιMultiDual_apply_ιMulti]
  simp only [Set.powersetCard.ofFinEmbEquiv_symm_apply, omitIndex,
    Finset.orderEmbOfFin_compl_singleton_eq_succAboveOrderEmb,
    Module.Basis.coord_apply] <;> rfl

def wedgeOneOne (a b : Omega) : Form 2 :=
  exteriorPower.ιMulti K 2 ![a, b]

/-- Canonical exterior multiplication in degrees one and two. -/
def wedgeOneTwo : Omega →ₗ[K] (Form 2 →ₗ[K] Form 3) :=
  exteriorPower.alternatingMapLinearEquiv.toLinearMap.comp
    (exteriorPower.ιMulti K 3).curryLeft

@[simp] theorem wedgeOneTwo_wedge (a : Omega) (v : Fin 2 → Omega) :
    wedgeOneTwo a (exteriorPower.ιMulti K 2 v) =
      exteriorPower.ιMulti K 3 (Matrix.vecCons a v) := by
  simp [wedgeOneTwo]

theorem wedgeOneTwo_basis (a : Omega) (k : Fin 6) :
    wedgeOneTwo a (secondBasis k) = exteriorPower.ιMulti K 3
      (Matrix.vecCons a (coordinateDifferential ∘ pairCoordinates k)) := by
  rw [secondBasis_apply, wedgeOneTwo_wedge]

def firstCoordinateDerivative (i j : Fin 4) : Omega →ₗ[ℂ] K :=
  (complexTangent i).toLinearMap.comp ((coordinateBasis.coord j).restrictScalars ℂ)

def firstCoefficients (k : Fin 6) : Omega →ₗ[ℂ] K :=
  firstCoordinateDerivative (pairLeft k) (pairRight k) -
    firstCoordinateDerivative (pairRight k) (pairLeft k)

/-- Exterior differentiation of actual one-forms. Complex linearity is
built in; the coordinate partial derivatives are not K-linear. -/
def exteriorD1 : Omega →ₗ[ℂ] Form 2 :=
  (secondBasis.equivFun.symm.toLinearMap.restrictScalars ℂ).comp
    (LinearMap.pi firstCoefficients)

@[simp] theorem exteriorD1_repr (ω : Omega) (k : Fin 6) :
    secondBasis.repr (exteriorD1 ω) k =
      affineTangent (pairLeft k) (coordinateBasis.repr ω (pairRight k)) -
      affineTangent (pairRight k) (coordinateBasis.repr ω (pairLeft k)) := by
  change secondBasis.coord k (secondBasis.equivFun.symm _) = _
  rw [Module.Basis.coord_equivFun_symm] <;> rfl

def secondCoordinateDerivative (i : Fin 4) (k : Fin 6) : Form 2 →ₗ[ℂ] K :=
  (complexTangent i).toLinearMap.comp ((secondBasis.coord k).restrictScalars ℂ)

def secondCoefficients : Fin 4 → (Form 2 →ₗ[ℂ] K) :=
  ![secondCoordinateDerivative 1 5 - secondCoordinateDerivative 2 4 +
      secondCoordinateDerivative 3 3,
    secondCoordinateDerivative 0 5 - secondCoordinateDerivative 2 2 +
      secondCoordinateDerivative 3 1,
    secondCoordinateDerivative 0 4 - secondCoordinateDerivative 1 2 +
      secondCoordinateDerivative 3 0,
    secondCoordinateDerivative 0 3 - secondCoordinateDerivative 1 1 +
      secondCoordinateDerivative 2 0]

/-- Exterior differentiation of actual two-forms, with the increasing
triple convention of `CycleQ2AffineExterior.thirdBasis`. -/
def exteriorD2 : Form 2 →ₗ[ℂ] Form 3 :=
  (thirdBasis.equivFun.symm.toLinearMap.restrictScalars ℂ).comp
    (LinearMap.pi secondCoefficients)

set_option maxHeartbeats 1000000 in
@[simp] theorem exteriorD2_repr (η : Form 2) (i : Fin 4) :
    thirdBasis.repr (exteriorD2 η) i =
      ![affineTangent 1 (secondBasis.repr η 5) -
          affineTangent 2 (secondBasis.repr η 4) +
          affineTangent 3 (secondBasis.repr η 3),
        affineTangent 0 (secondBasis.repr η 5) -
          affineTangent 2 (secondBasis.repr η 2) +
          affineTangent 3 (secondBasis.repr η 1),
        affineTangent 0 (secondBasis.repr η 4) -
          affineTangent 1 (secondBasis.repr η 2) +
          affineTangent 3 (secondBasis.repr η 0),
        affineTangent 0 (secondBasis.repr η 3) -
          affineTangent 1 (secondBasis.repr η 1) +
          affineTangent 2 (secondBasis.repr η 0)] i := by
  calc
    thirdBasis.repr (exteriorD2 η) i = secondCoefficients i η :=
      thirdBasis.coord_equivFun_symm i (fun j => secondCoefficients j η)
    _ = _ := by fin_cases i <;> rfl

/-- Differentiating a scalar times an exact coordinate one-form gives the
actual exterior product of its differential and that coordinate one-form. -/
theorem exteriorD1_smul_coordinate (a : K) (i : Fin 4) :
    exteriorD1 (a • coordinateDifferential i) =
      wedgeOneOne (d a) (coordinateDifferential i) := by
  apply secondBasis.repr.injective
  ext k
  rw [exteriorD1_repr, wedgeOneOne, secondBasis_repr_wedge]
  fin_cases i <;> fin_cases k <;>
    simp [pairLeft, pairRight, ← coordinateBasis_apply, coordinateBasis_repr_d]

set_option maxHeartbeats 1000000 in
/-- The degree-two map differentiates scalar coefficients of actual closed
coordinate wedges, with the standard exterior sign. -/
theorem exteriorD2_smul_basis (a : K) (k : Fin 6) :
    exteriorD2 (a • secondBasis k) = wedgeOneTwo (d a) (secondBasis k) := by
  have hrepr (j : Fin 6) :
      secondBasis.repr (a • secondBasis k) j = if k = j then a else 0 := by
    rw [LinearEquiv.map_smul, Finsupp.smul_apply, Module.Basis.repr_self_apply]
    simp only [smul_eq_mul, mul_ite, mul_one, mul_zero]
  have hcoord (j l : Fin 4) :
      coordinateBasis.repr (coordinateDifferential j) l =
        if j = l then 1 else 0 := by
    simpa only [coordinateBasis_apply] using coordinateBasis.repr_self_apply j l
  apply thirdBasis.repr.injective
  apply Finsupp.ext
  intro i
  rw [exteriorD2_repr, wedgeOneTwo_basis, thirdBasis_repr_wedge]
  -- Resolve the actual module coordinates once, before the finite scalar cases.
  simp only [hrepr, apply_ite, map_zero, Matrix.det_fin_three, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.vecHead, Matrix.vecTail, Function.comp_apply, Fin.succ_zero_eq_one,
    pairCoordinates, coordinateBasis_repr_d, hcoord]
  fin_cases k <;> fin_cases i <;>
    simp [pairLeft, pairRight, Fin.succAbove]

theorem exteriorD1_eq_sum_wedge (ω : Omega) :
    exteriorD1 ω = ∑ i : Fin 4,
      wedgeOneOne (d (coordinateBasis.repr ω i)) (coordinateDifferential i) := by
  calc
    exteriorD1 ω = exteriorD1
        (∑ i : Fin 4, coordinateBasis.repr ω i • coordinateBasis i) :=
      congrArg exteriorD1 (coordinateBasis.sum_repr ω).symm
    _ = _ := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [coordinateBasis_apply, exteriorD1_smul_coordinate]

theorem exteriorD2_eq_sum_wedge (η : Form 2) :
    exteriorD2 η = ∑ k : Fin 6,
      wedgeOneTwo (d (secondBasis.repr η k)) (secondBasis k) := by
  calc
    exteriorD2 η = exteriorD2
        (∑ k : Fin 6, secondBasis.repr η k • secondBasis k) :=
      congrArg exteriorD2 (secondBasis.sum_repr η).symm
    _ = _ := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro k hk
      exact exteriorD2_smul_basis _ k

/-- The first complex identity follows from the already constructed
commuting derivations on the actual hypersurface function field. -/
@[simp] theorem exteriorD1_d (a : K) : exteriorD1 (d a) = 0 := by
  apply secondBasis.repr.injective
  ext k
  rw [exteriorD1_repr]
  simp only [coordinateBasis_repr_d, map_zero, Finsupp.zero_apply]
  exact sub_eq_zero.mpr (affineTangents_commute (pairLeft k) (pairRight k) a)

@[simp] theorem exteriorD2_exteriorD1 (ω : Omega) :
    exteriorD2 (exteriorD1 ω) = 0 := by
  have h10 (a : K) : affineTangent 1 (affineTangent 0 a) =
      affineTangent 0 (affineTangent 1 a) := affineTangents_commute 1 0 a
  have h20 (a : K) : affineTangent 2 (affineTangent 0 a) =
      affineTangent 0 (affineTangent 2 a) := affineTangents_commute 2 0 a
  have h30 (a : K) : affineTangent 3 (affineTangent 0 a) =
      affineTangent 0 (affineTangent 3 a) := affineTangents_commute 3 0 a
  have h21 (a : K) : affineTangent 2 (affineTangent 1 a) =
      affineTangent 1 (affineTangent 2 a) := affineTangents_commute 2 1 a
  have h31 (a : K) : affineTangent 3 (affineTangent 1 a) =
      affineTangent 1 (affineTangent 3 a) := affineTangents_commute 3 1 a
  have h32 (a : K) : affineTangent 3 (affineTangent 2 a) =
      affineTangent 2 (affineTangent 3 a) := affineTangents_commute 3 2 a
  apply thirdBasis.repr.injective
  ext i
  fin_cases i <;>
    simp [exteriorD2_repr, exteriorD1_repr, pairLeft, pairRight,
      map_add, map_sub, h10, h20, h30, h21, h31, h32] <;> abel

/-- The top differential already used in the protected existence statement
composes to zero with the genuine new degree-two exterior differential. -/
@[simp] theorem exteriorD3_exteriorD2 (η : Form 2) :
    exteriorD3 (exteriorD2 η) = 0 := by
  have h10 (a : K) : affineTangent 1 (affineTangent 0 a) =
      affineTangent 0 (affineTangent 1 a) := affineTangents_commute 1 0 a
  have h20 (a : K) : affineTangent 2 (affineTangent 0 a) =
      affineTangent 0 (affineTangent 2 a) := affineTangents_commute 2 0 a
  have h30 (a : K) : affineTangent 3 (affineTangent 0 a) =
      affineTangent 0 (affineTangent 3 a) := affineTangents_commute 3 0 a
  have h21 (a : K) : affineTangent 2 (affineTangent 1 a) =
      affineTangent 1 (affineTangent 2 a) := affineTangents_commute 2 1 a
  have h31 (a : K) : affineTangent 3 (affineTangent 1 a) =
      affineTangent 1 (affineTangent 3 a) := affineTangents_commute 3 1 a
  have h32 (a : K) : affineTangent 3 (affineTangent 2 a) =
      affineTangent 2 (affineTangent 3 a) := affineTangents_commute 3 2 a
  rw [exteriorD3_apply]
  suffices (∑ i : Fin 4, (-1 : K) ^ i.val *
      affineTangent i (thirdBasis.repr (exteriorD2 η) i)) = 0 by
    rw [this, zero_smul]
  simp [Fin.sum_univ_succ, exteriorD2_repr, map_add, map_sub, pow_succ,
    h10, h20, h30, h21, h31, h32] <;> abel

theorem exteriorD2_comp_exteriorD1 : exteriorD2.comp exteriorD1 = 0 := by
  apply LinearMap.ext
  intro ω
  simpa only [LinearMap.comp_apply, LinearMap.zero_apply] using exteriorD2_exteriorD1 ω

theorem exteriorD3_comp_exteriorD2 : exteriorD3.comp exteriorD2 = 0 := by
  apply LinearMap.ext
  intro η
  simpa only [LinearMap.comp_apply, LinearMap.zero_apply] using exteriorD3_exteriorD2 η

end CycleQ2AffineDeRhamComplex
end
end

end Q2UncompiledAffineDeRhamComplex
