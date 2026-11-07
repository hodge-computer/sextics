import Proposal.SymmetricCertificateTransport
import HodgeComputer.Constructions.ResidueTransport.CoefficientBalance
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

/-!
# Four coefficient directions give a strict physical certificate

The ordinary affine game transports through the proved reflection chart
without first normalizing its contraction or imposing a zero lambda
component. A field in the four `(lambda,b,c,d)` directions satisfying
`W(f)=P+h*f` and `div(W)=h` therefore gives the literal protected q=1
certificate. Its denominator is arbitrary subject to legality, so additional
coefficient-space divisors are allowed. The component numerators and `h`
may depend on the normal variable; only the base-denominator endpoint
requires its common denominator to be independent of that variable.

All conclusions are conditional on explicit polynomial matching and
divergence identities. No primitive existence or geometry is assumed.
-/

noncomputable section

namespace SymmetricBalancedTransport

open MvPolynomial HoldoutConstruction SymmetricPiolaTransport
open SymmetricChartField SymmetricChartClearing SymmetricCertificateTransport
open scoped BigOperators

set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

section FieldTransport

variable {K : Type*} [Field K] [CharZero K]

/-- The chart transports contraction and divergence before any normalization.
The determinant density is independent of the four coefficient coordinates. -/
theorem ordinary_current_transport
    (D : Fin 6 → Derivation ℤ K K) (x : Fin 6 → K)
    (hx : ∀ i j, D i (x j) = if i = j then 1 else 0)
    (ha : x 0 ≠ 0) (hv : x 5 ≠ 0) (H : K) (w : Fin 5 → K) :
    let E := physicalDerivative D (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)
    let V := physicalCurrent (x 0) (x 1) (x 5) w
    (∑ j, V j*E j ((x 0)^6*H)) =
        (x 0)^6*(∑ i : Fin 5, w i*D i.succ H)/(4*x 5) ∧
      fieldDivergence E V = (∑ i : Fin 5, D i.succ (w i))/(4*x 5) := by
  dsimp only
  have hradial : ∀ i : Fin 5, D i.succ (x 0) = 0 := by
    intro i
    simp [hx]
  have hdet : (jacobian (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)).det ≠ 0 := by
    rw [jacobian_det]
    exact mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ ha)) hv
  rw [physicalCurrent_eq_piola (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) w ha hv]
  constructor
  · rw [piola_contraction D _ _ _
      (inverse_mul_jacobian _ _ _ _ _ _ ha hv)
      (physicalDerivative_apply D _ _ _ _ _ _),
      volumeCurrent_contraction D _ _ _ hradial, jacobian_det]
    field_simp
  · rw [piola_divergence D _ _ _
      (jacobian_mul_inverse _ _ _ _ _ _ ha hv)
      (inverse_mul_jacobian _ _ _ _ _ _ ha hv) hdet
      (physicalDerivative_apply D _ _ _ _ _ _)
      (jacobian_mixed D x hx),
      volumeCurrent_divergence D _ _ hradial, jacobian_det]
    field_simp

end FieldTransport

abbrev ChartPoly := WeightedPrimitiveTransport.Poly

open WeightedPrimitiveTransport in
/-- Substituting the square of the normal coordinate fixes every polynomial
in the four coefficient coordinates. -/
theorem squareLift_of_base (D : ChartPoly) (hbase : (4 : Fin 5) ∉ D.vars) :
    squareLift D = D := by
  change squareLift D = RingHom.id ChartPoly D
  apply MvPolynomial.hom_congr_vars ?_ ?_ rfl
  · ext c
    simp
  · intro i hi _
    have hne : i ≠ 4 := fun h => hbase (h ▸ hi)
    simp [hne]

open WeightedPrimitiveTransport in
/-- Any nonzero coefficient-space denominator is legal. No selected divisor
or degree bound is built into this statement. -/
theorem base_denominator_legal (D : ChartPoly) (hD : D ≠ 0)
    (hbase : (4 : Fin 5) ∉ D.vars) :
    IsRelPrime chartEquation (squareLift D) := by
  rw [squareLift_of_base D hbase]
  apply SymmetricAffinePrime.chart_irreducible.isRelPrime_iff_not_dvd.mpr
  rintro ⟨Q, hQ⟩
  have hQ0 : Q ≠ 0 := by
    intro hz
    apply hD
    simpa [hz] using hQ
  have hFvar : (4 : Fin 5) ∈ chartEquation.vars := by
    by_contra hv
    have hz := pderiv_eq_zero_of_notMem_vars hv
    apply SymmetricAffineField.normal_nonzero
    rw [hz, map_zero]
  have hFdeg : degreeOf (4 : Fin 5) chartEquation ≠ 0 :=
    mem_vars_iff_degreeOf_ne_zero.mp hFvar
  have hDdeg : degreeOf (4 : Fin 5) D = 0 := by
    by_contra hn
    exact hbase (mem_vars_iff_degreeOf_ne_zero.mpr hn)
  have hdegrees := degreeOf_mul_eq (n := (4 : Fin 5))
    SymmetricAffinePrime.chart_irreducible.ne_zero hQ0
  rw [← hQ, hDdeg] at hdegrees
  omega

/-- The full cleared affine game, rather than two stronger normalized
equations, suffices for the existing homogeneous polynomial transport. -/
theorem transported_game
    (D : ChartPoly) (N : Fin 5 → ChartPoly) (L : ℕ)
    (hD : D ≠ 0) (hLD : D.totalDegree ≤ L)
    (hLN : ∀ i, (N i).totalDegree ≤ L)
    (hlegal : IsRelPrime WeightedPrimitiveTransport.chartEquation D)
    (hgame : HodgeTestbed.clearedDefect WeightedPrimitiveTransport.chartEquation
      WeightedPrimitiveTransport.chartSource D N = 0) :
    HodgeTestbed.clearedDefect HodgeSubmission.F HodgeSubmission.A
      (certificateDenominator D L) (certificateNumerator N L) = 0 := by
  have hd : affineMap D ≠ 0 := fun h => hD (affineMap_injective (by simpa using h))
  have hfield : affineMap WeightedPrimitiveTransport.chartSource -
      (∑ i : Fin 5, (affineMap (N i)/affineMap D)*
        delta i.succ (affineMap WeightedPrimitiveTransport.chartEquation)) +
      affineMap WeightedPrimitiveTransport.chartEquation *
        fieldDivergence (fun i : Fin 5 => delta i.succ)
          (fun i => affineMap (N i)/affineMap D) = 0 := by
    rw [quotient_contraction affineMap (fun i : Fin 5 => delta i.succ)
        delta_affineMap,
      quotient_divergence affineMap (fun i : Fin 5 => delta i.succ) delta_affineMap]
    have h := congrArg affineMap hgame
    simp only [HodgeTestbed.clearedDefect, map_add, map_sub, map_mul,
      map_pow, map_zero] at h
    field_simp
    linear_combination h
  have hp := ordinary_current_transport delta x delta_coordinate
    (coordinate_ne_zero 0) (coordinate_ne_zero 5)
    (affineMap WeightedPrimitiveTransport.chartEquation)
    (fun i => affineMap (N i)/affineMap D)
  change
    (∑ j, physicalCurrent (x 0) (x 1) (x 5)
      (fun i => affineMap (N i)/affineMap D) j * theta j
      ((x 0)^6*affineMap WeightedPrimitiveTransport.chartEquation)) = _ ∧
      fieldDivergence theta (physicalCurrent (x 0) (x 1) (x 5)
        (fun i => affineMap (N i)/affineMap D)) = _ at hp
  rw [← physicalMap_F] at hp
  have hs : physicalMap HodgeSubmission.A =
      (x 0)^6*affineMap WeightedPrimitiveTransport.chartSource/(4*x 5) := by
    rw [← physicalMap_A]
    field_simp [coordinate_ne_zero 5]
  have hg : physicalMap HodgeSubmission.A -
      (∑ j, physicalCurrent (x 0) (x 1) (x 5)
        (fun i => affineMap (N i)/affineMap D) j * theta j
          (physicalMap HodgeSubmission.F)) +
      physicalMap HodgeSubmission.F *
        fieldDivergence theta (physicalCurrent (x 0) (x 1) (x 5)
          (fun i => affineMap (N i)/affineMap D)) = 0 := by
    rw [hs, hp.1, hp.2, physicalMap_F]
    simp only [fieldDivergence] at hfield
    linear_combination ((x 0)^6/(4*x 5))*hfield
  rw [← certificateCurrent_map D N L hD hLD hLN,
    quotient_contraction physicalMap theta theta_physicalMap,
    quotient_divergence physicalMap theta theta_physicalMap] at hg
  have hden : physicalMap (certificateDenominator D L) ≠ 0 := fun h =>
    certificateDenominator_ne_zero D L hLD hlegal
      (physicalMap_injective (by simpa using h))
  apply physicalMap_injective
  simp only [HodgeTestbed.clearedDefect, map_add, map_sub, map_mul,
    map_pow, map_zero]
  field_simp at hg
  linear_combination hg

/-- The displayed witnesses satisfy the unchanged protected verifier with
zero quotient. Homogeneity and denominator legality are proved here. -/
theorem explicit_verify_game
    (D : ChartPoly) (N : Fin 5 → ChartPoly) (L : ℕ)
    (hD : D ≠ 0) (hLD : D.totalDegree ≤ L)
    (hLN : ∀ i, (N i).totalDegree ≤ L)
    (hlegal : IsRelPrime WeightedPrimitiveTransport.chartEquation D)
    (hgame : HodgeTestbed.clearedDefect WeightedPrimitiveTransport.chartEquation
      WeightedPrimitiveTransport.chartSource D N = 0) :
    HodgeComputer.Verify HodgeSubmission.F HodgeSubmission.A 6 1
      (certificateDenominator D L) (certificateNumerator N L) 0 := by
  have hg := transported_game D N L hD hLD hLN hlegal hgame
  have hden := certificateDenominator_ne_zero D L hLD hlegal
  have hhom := certificateDenominator_homogeneous D L hLD
  refine ⟨SymmetricSmoothness.target_ne_zero, SymmetricSmoothness.target_homogeneous,
    ?_, hden, ?_, ?_, certificateDenominator_legal D L hLD hlegal, ?_⟩
  · simpa using HodgeComputer.Homogeneous.of_isHomogeneous SymmetricSmoothness.source_homogeneous
  · rw [hhom.totalDegree hden]
    exact hhom
  · intro i
    rw [hhom.totalDegree hden]
    convert HodgeComputer.Homogeneous.of_isHomogeneous
      (certificateNumerator_homogeneous N L hLN i) using 1
    push_cast
    omega
  · simpa only [HodgeComputer.defect, HodgeTestbed.clearedDefect,
      Nat.cast_one, one_mul, mul_zero] using hg

theorem certificate_of_affine_game
    (D : ChartPoly) (N : Fin 5 → ChartPoly) (hD : D ≠ 0)
    (hlegal : IsRelPrime WeightedPrimitiveTransport.chartEquation D)
    (hgame : HodgeTestbed.clearedDefect WeightedPrimitiveTransport.chartEquation
      WeightedPrimitiveTransport.chartSource D N = 0) :
    HodgeComputer.HasCertificate HodgeSubmission.F 1 HodgeSubmission.A := by
  let L := max D.totalDegree (Finset.univ.sup (fun i => (N i).totalDegree))
  have hLD : D.totalDegree ≤ L := Nat.le_max_left _ _
  have hLN : ∀ i, (N i).totalDegree ≤ L := by
    intro i
    exact (Finset.le_sup (f := fun j => (N j).totalDegree)
      (Finset.mem_univ i)).trans (Nat.le_max_right _ _)
  exact (explicit_verify_game D N L hD hLD hLN hlegal hgame).hasCertificate

open WeightedPrimitiveTransport in
/-- The weighted coefficient field has four components and no normal
component. The Jacobian density contributes exactly `4*v`. -/
def balancedNumerator (Z : Fin 4 → ChartPoly) : Fin 5 → ChartPoly :=
  mergeNumerators 0 (fun i => C 4*X 4*squareLift (Z i))

open WeightedPrimitiveTransport in
theorem balancedNumerator_castSucc (Z : Fin 4 → ChartPoly) (i : Fin 4) :
    balancedNumerator Z i.castSucc = C 4*X 4*squareLift (Z i) := by
  fin_cases i <;> rfl

theorem balancedNumerator_last (Z : Fin 4 → ChartPoly) :
    balancedNumerator Z (Fin.last 4) = 0 := rfl

open WeightedPrimitiveTransport in
theorem balanced_directional (f : ChartPoly) (Z : Fin 4 → ChartPoly) :
    HodgeTestbed.directional (squareLift f) (balancedNumerator Z) =
      C 4*X 4*squareLift (∑ i : Fin 4, Z i*pderiv i.castSucc f) := by
  simp only [balancedNumerator, mergeNumerators_directional, zero_mul,
    zero_add, tangent_squareLift, map_sum, map_mul, Finset.mul_sum, mul_assoc]

open WeightedPrimitiveTransport in
theorem balanced_divergence (Z : Fin 4 → ChartPoly) :
    HodgeTestbed.divergence (balancedNumerator Z) =
      C 4*X 4*squareLift (∑ i : Fin 4, pderiv i.castSucc (Z i)) := by
  unfold HodgeTestbed.divergence
  rw [Fin.sum_univ_castSucc]
  simp only [balancedNumerator_castSucc, balancedNumerator_last,
    map_zero, add_zero, map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hne : (4 : Fin 5) ≠ i.castSucc := (Fin.castSucc_ne_last i).symm
  simp [pderiv_X_of_ne hne, tangent_squareLift]

open WeightedPrimitiveTransport in
/-- Polynomial matching and divergence balance in all four coefficient
directions imply the exact ordinary affine game. `D` is an arbitrary common
denominator: it need not be a power of the older coefficient determinant. -/
theorem balanced_affine_game
    (D H : ChartPoly) (Z : Fin 4 → ChartPoly)
    (hmatch : (∑ i : Fin 4, Z i*pderiv i.castSucc rawWeighted) =
      D*rawSource+H*rawWeighted)
    (hdiv : D*(∑ i : Fin 4, pderiv i.castSucc (Z i)) -
      (∑ i : Fin 4, Z i*pderiv i.castSucc D) = D*H) :
    HodgeTestbed.clearedDefect chartEquation chartSource
      (squareLift D) (balancedNumerator Z) = 0 := by
  have hn := balanced_directional rawWeighted Z
  rw [hmatch] at hn
  have hh := congrArg squareLift hdiv
  simp only [map_sub, map_mul] at hh
  simp only [HodgeTestbed.clearedDefect, HodgeTestbed.divergenceNumerator,
    chartEquation, chartSource, reflectedSource]
  rw [hn, balanced_divergence, balanced_directional]
  simp only [map_add, map_mul]
  linear_combination (C 4*X 4*squareLift rawWeighted)*hh

open WeightedPrimitiveTransport in
/-- A four-component coefficient-field solution gives the exact protected
target. The nonvanishing and legality hypotheses concern the reflected
common denominator, including any additional coefficient-space divisors. -/
theorem certificate_of_balanced_coefficients
    (D H : ChartPoly) (Z : Fin 4 → ChartPoly)
    (hD : squareLift D ≠ 0) (hlegal : IsRelPrime chartEquation (squareLift D))
    (hmatch : (∑ i : Fin 4, Z i*pderiv i.castSucc rawWeighted) =
      D*rawSource+H*rawWeighted)
    (hdiv : D*(∑ i : Fin 4, pderiv i.castSucc (Z i)) -
      (∑ i : Fin 4, Z i*pderiv i.castSucc D) = D*H) :
    HodgeComputer.HasCertificate HodgeSubmission.F 1 HodgeSubmission.A := by
  exact certificate_of_affine_game (squareLift D) (balancedNumerator Z) hD hlegal
    (balanced_affine_game D H Z hmatch hdiv)

open WeightedPrimitiveTransport in
/-- For coefficient-space denominators, nonvanishing alone is the remaining
denominator condition; legality follows from the normal degree. -/
theorem certificate_of_base_coefficients
    (D H : ChartPoly) (Z : Fin 4 → ChartPoly)
    (hD : D ≠ 0) (hbase : (4 : Fin 5) ∉ D.vars)
    (hmatch : (∑ i : Fin 4, Z i*pderiv i.castSucc rawWeighted) =
      D*rawSource+H*rawWeighted)
    (hdiv : D*(∑ i : Fin 4, pderiv i.castSucc (Z i)) -
      (∑ i : Fin 4, Z i*pderiv i.castSucc D) = D*H) :
    HodgeComputer.HasCertificate HodgeSubmission.F 1 HodgeSubmission.A := by
  apply certificate_of_balanced_coefficients D H Z
    (by simpa only [squareLift_of_base D hbase] using hD)
    (base_denominator_legal D hD hbase) hmatch hdiv

open WeightedPrimitiveTransport in
/-- The same endpoint accepts rational coefficient identities in any
faithful differential-field realization of the weighted polynomial ring. -/
theorem certificate_of_balanced_field {L : Type*} [Field L]
    (φ : ChartPoly →+* L) (hinj : Function.Injective φ)
    (E : Fin 4 → Derivation ℤ L L)
    (compatible : ∀ i p, E i (φ p) = φ (pderiv i.castSucc p))
    (D H : ChartPoly) (Z : Fin 4 → ChartPoly)
    (hD : squareLift D ≠ 0) (hlegal : IsRelPrime chartEquation (squareLift D))
    (hmatch : CoefficientBalance.action E (fun i => φ (Z i)/φ D) (φ rawWeighted) =
      φ rawSource+(φ H/φ D)*φ rawWeighted)
    (hdiv : fieldDivergence E (fun i => φ (Z i)/φ D) = φ H/φ D) :
    HodgeComputer.HasCertificate HodgeSubmission.F 1 HodgeSubmission.A := by
  have hd : φ D ≠ 0 := by
    intro hz
    have hd0 : D = 0 := hinj (by simpa using hz)
    exact hD (by simp [hd0])
  obtain ⟨hm, hv⟩ := CoefficientBalance.clear_balance
    (fun i : Fin 4 => integerPartial i.castSucc) E φ hinj compatible
    D H rawWeighted rawSource Z hd hmatch hdiv
  exact certificate_of_balanced_coefficients D H Z hD hlegal hm hv

open WeightedPrimitiveTransport in
/-- A solution of the scalar coefficient-fiber equation, together with its
literal common-denominator representation, reaches the protected target.
The scalar and its denominator may contain arbitrary extra base divisors.
The hypotheses on `c` are identities still to be checked for a chosen
coefficient-fiber construction, not additional existence assumptions. -/
theorem certificate_of_scalar_correction {L : Type*} [Field L]
    (φ : ChartPoly →+* L) (hinj : Function.Injective φ)
    (E : Fin 4 → Derivation ℤ L L)
    (compatible : ∀ i p, E i (φ p) = φ (pderiv i.castSucc p))
    (D H : ChartPoly) (Z : Fin 4 → ChartPoly)
    (hD : D ≠ 0) (hbase : (4 : Fin 5) ∉ D.vars)
    (w c : Fin 4 → L) (ell a s : L)
    (hell0 : ell ≠ 0) (hell : CoefficientBalance.action E c ell = a*ell)
    (hcdiv : fieldDivergence E c = 4*a)
    (hw : CoefficientBalance.action E w (φ rawWeighted) = φ rawSource)
    (hc : CoefficientBalance.action E c (φ rawWeighted) = a*φ rawWeighted)
    (hs : CoefficientBalance.action E c s = -(ell^3)*fieldDivergence E w)
    (hZ : (fun i => φ (Z i)/φ D) = CoefficientBalance.correctedField w c ell s 3)
    (hH : φ H/φ D = a*s/ell^3) :
    HodgeComputer.HasCertificate HodgeSubmission.F 1 HodgeSubmission.A := by
  apply certificate_of_balanced_field φ hinj E compatible D H Z
    (by simpa only [squareLift_of_base D hbase] using hD)
    (base_denominator_legal D hD hbase)
  · rw [hZ, hH]
    exact CoefficientBalance.corrected_matching E w c (φ rawWeighted)
      (φ rawSource) a ell s 3 hw hc
  · rw [hZ, hH]
    apply (CoefficientBalance.balanced_iff E w c ell a s 3 hell0 hell ?_).mpr hs
    simpa using hcdiv

#print axioms ordinary_current_transport
#print axioms transported_game
#print axioms explicit_verify_game
#print axioms certificate_of_affine_game
#print axioms certificate_of_balanced_coefficients
#print axioms base_denominator_legal
#print axioms certificate_of_base_coefficients
#print axioms certificate_of_scalar_correction

end SymmetricBalancedTransport
