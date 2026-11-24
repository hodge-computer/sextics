import Proposal.AffineChartResiduePrimitive
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.HahnSeries.Multiplication
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.HahnSeries.PowerSeries
import Mathlib.RingTheory.HahnSeries.Summable

/-! # The formal normal coordinate, its derivations and the pole-three residue -/

set_option Elab.async false

/- Component: continuation_2/AffineFormalSpecialization.lean -/
section
/-!
An actual formal neighborhood of the protected affine hypersurface.

The normal derivative is already proved nonzero in its function field. Hensel's
lemma therefore solves the exact one-parameter deformation in that function
field's power series ring. This is a specialization tool: it does not turn a
formal primitive at the Fermat member into a rational primitive of the family.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section

namespace CycleQ2FormalSpecialization

open scoped PowerSeries

/-- Hensel lifting written with the actual constant-coefficient specialization.
No algebraicity or rationality of the resulting power series is inferred. -/
theorem simple_root_lifts {k : Type*} [Field k]
    (p : Polynomial (PowerSeries k)) (hp : p.Monic) (a : k)
    (ha : p.eval₂ (PowerSeries.constantCoeff (R := k)) a = 0)
    (hderiv : p.derivative.eval₂ (PowerSeries.constantCoeff (R := k)) a ≠ 0) :
    ∃ z : PowerSeries k, p.eval z = 0 ∧ z.constantCoeff = a := by
  let I : Ideal (PowerSeries k) := Ideal.span {PowerSeries.X}
  have hmem : p.eval (PowerSeries.C a) ∈ I := by
    rw [Ideal.mem_span_singleton, PowerSeries.X_dvd_iff]
    simpa only [← Polynomial.eval₂_at_apply, PowerSeries.constantCoeff_C] using ha
  have hu : IsUnit (p.derivative.eval (PowerSeries.C a)) := by
    apply PowerSeries.isUnit_iff_constantCoeff.mpr
    apply isUnit_iff_ne_zero.mpr
    simpa only [← Polynomial.eval₂_at_apply, PowerSeries.constantCoeff_C] using hderiv
  obtain ⟨z, hz, hza⟩ := HenselianRing.is_henselian p hp (PowerSeries.C a)
    hmem (hu.map (Ideal.Quotient.mk I))
  refine ⟨z, hz, ?_⟩
  rw [Ideal.mem_span_singleton, PowerSeries.X_dvd_iff] at hza
  simpa only [map_sub, PowerSeries.constantCoeff_C, sub_eq_zero] using hza

open MvPolynomial CycleQ2AffineClearing CycleQ2AffineGeometry
  CycleQ2AffineHypersurface

abbrev K := AffineFunctionField

def fieldCoordinate (i : Fin 5) : K := affineMap (MvPolynomial.X i)

/-- The family parameter is zero at the protected target and minus one at
the Fermat polynomial. The eliminated coordinate is the polynomial variable;
the other four coordinates are constants in the actual function field. -/
def targetFamily : Polynomial (PowerSeries K) :=
  Polynomial.X ^ 6 +
    Polynomial.C (PowerSeries.C (1 + fieldCoordinate 1 ^ 6 +
      fieldCoordinate 2 ^ 6 + fieldCoordinate 3 ^ 6 + fieldCoordinate 4 ^ 6)) +
    Polynomial.C (PowerSeries.C (1 / 2 : K) * (1 + PowerSeries.X)) *
      (Polynomial.X * Polynomial.C (PowerSeries.C (fieldCoordinate 2 * fieldCoordinate 3)) +
        Polynomial.X ^ 3 * Polynomial.C (PowerSeries.C
          (fieldCoordinate 1 * fieldCoordinate 3 * fieldCoordinate 4)) +
        Polynomial.C (PowerSeries.C
          (fieldCoordinate 1 ^ 3 * fieldCoordinate 4 * fieldCoordinate 2)))

theorem targetFamily_monic : targetFamily.Monic := by
  unfold targetFamily
  rw [add_assoc]
  apply Polynomial.monic_X_pow_add
  compute_degree!

theorem targetFamily_specializes :
    targetFamily.eval₂ (PowerSeries.constantCoeff (R := K)) (fieldCoordinate 0) = 0 := by
  have hc (c : ℂ) : affineMap (MvPolynomial.C c) = algebraMap ℂ K c := rfl
  have h := congrArg affineMap affineF_formula
  simp only [affineMap_F, map_add, map_mul, map_pow, map_one, hc] at h
  norm_num only [map_div₀, map_one, map_ofNat] at h
  convert h.symm using 1 <;> norm_num only [targetFamily, fieldCoordinate,
    Polynomial.eval₂_add, Polynomial.eval₂_mul,
    Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C, Polynomial.eval₂_one, map_add, map_mul,
    map_one, map_zero, map_pow, map_ofNat, PowerSeries.constantCoeff_C,
    PowerSeries.constantCoeff_X] <;> ring

theorem targetFamily_simple :
    targetFamily.derivative.eval₂ (PowerSeries.constantCoeff (R := K))
      (fieldCoordinate 0) ≠ 0 := by
  have hc (c : ℂ) : affineMap (MvPolynomial.C c) = algebraMap ℂ K c := rfl
  have h := congrArg (fun P => affineMap (MvPolynomial.pderiv 0 P)) affineF_formula
  norm_num [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_pow,
    MvPolynomial.pderiv_X, Pi.single_apply, Fin.ext_iff, hc] at h
  have hn := normal_ne_zero
  rw [h] at hn
  convert hn using 1 <;>
    norm_num [targetFamily, fieldCoordinate, Polynomial.derivative_add,
      Polynomial.derivative_mul, Polynomial.derivative_pow,
      Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_pow,
      Polynomial.eval₂_X, Polynomial.eval₂_C] <;> simp only [map_ofNat] <;> ring

/-- The protected hypersurface has a genuine formal solution along the
specified deformation, with its original coordinate as constant coefficient. -/
theorem exists_target_formal_coordinate :
    ∃ z : PowerSeries K, targetFamily.eval z = 0 ∧
      z.constantCoeff = fieldCoordinate 0 :=
  simple_root_lifts targetFamily targetFamily_monic (fieldCoordinate 0)
    targetFamily_specializes targetFamily_simple

end CycleQ2FormalSpecialization

#print axioms CycleQ2FormalSpecialization.simple_root_lifts
#print axioms CycleQ2FormalSpecialization.exists_target_formal_coordinate
end
end


/- Component: continuation_2/LaurentCoefficientDerivations.lean -/
section
/-!
Coefficientwise derivations and exactness under formal Laurent extension.

The exponent is a deformation parameter, not a coordinate to differentiate.
The actual Hahn-series multiplication is used in the Leibniz proof. Taking
any Laurent coefficient commutes with these derivations, including for
series with negative powers. Consequently a Laurent primitive specializes
coefficientwise; no converse from formal deformation to a rational primitive
of a generic algebraic family is asserted.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace CycleQ2LaurentDerivation

open scoped BigOperators

variable {C K : Type*} [CommRing C] [CommRing K] [Algebra C K]

abbrev Series := HahnSeries ℤ K

/-- Use the coefficient algebra explicitly. The power-series imports also
provide a compatible algebra through the power-series embedding; fixing
this instance keeps the scalar action definitionally coefficientwise. -/
local instance coefficientAlgebra : Algebra C (Series (K := K)) :=
  HahnSeries.instAlgebra

def coefficientwise (D : Derivation C K K) (s : Series (K := K)) : Series (K := K) where
  coeff n := D (s.coeff n)
  isPWO_support' := s.isPWO_support.mono (by
    intro n hn hzero
    exact hn (by simp only [hzero, map_zero]))

@[simp] theorem coefficientwise_coeff (D : Derivation C K K) (s : Series (K := K)) (n : ℤ) :
    (coefficientwise D s).coeff n = D (s.coeff n) := rfl

theorem support_coefficientwise_subset (D : Derivation C K K) (s : Series (K := K)) :
    (coefficientwise D s).support ⊆ s.support := by
  intro n hn hzero
  exact hn (by simp only [coefficientwise_coeff, hzero, map_zero])

theorem coefficientwise_mul (D : Derivation C K K) (s t : Series (K := K)) :
    coefficientwise D (s * t) = s * coefficientwise D t + t * coefficientwise D s := by
  ext n
  rw [coefficientwise_coeff, HahnSeries.coeff_mul, map_sum, HahnSeries.coeff_add,
    HahnSeries.coeff_mul_right' t.isPWO_support (support_coefficientwise_subset D t),
    mul_comm t (coefficientwise D s),
    HahnSeries.coeff_mul_left' s.isPWO_support (support_coefficientwise_subset D s)]
  simp only [Derivation.leibniz, smul_eq_mul, coefficientwise_coeff, Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro ij hij
  exact mul_comm _ _

/-- An actual derivation of the Laurent-series ring, obtained by applying the
coefficient derivation while keeping the formal parameter constant. -/
def extend (D : Derivation C K K) : Derivation C (Series (K := K)) (Series (K := K)) where
  toFun := coefficientwise D
  map_add' s t := by
    ext n
    simp
  map_smul' c s := by
    ext n
    simp only [coefficientwise_coeff, HahnSeries.coeff_smul,
      RingHom.id_apply, Derivation.map_smul]
  map_one_eq_zero' := by
    ext n
    by_cases hn : n = 0 <;> simp [HahnSeries.coeff_one, hn]
  leibniz' s t := by
    change coefficientwise D (s * t) = s * coefficientwise D t + t * coefficientwise D s
    exact coefficientwise_mul D s t

@[simp] theorem extend_coeff (D : Derivation C K K) (s : Series (K := K)) (n : ℤ) :
    (extend D s).coeff n = D (s.coeff n) := rfl

theorem extend_commute (D E : Derivation C K K) (h : Function.Commute D E) :
    Function.Commute (extend D) (extend E) := by
  intro s
  ext n
  exact h (s.coeff n)

@[simp] theorem extend_single (D : Derivation C K K) (n : ℤ) (a : K) :
    extend D (HahnSeries.single n a) = HahnSeries.single n (D a) := by
  ext j
  by_cases hj : j = n <;> simp [hj]

/-- Coefficient extraction is a left inverse on exactness, even when a
primitive has a pole in the deformation parameter. -/
theorem divergence_coefficient {ι : Type*} [Fintype ι]
    (D : ι → Derivation C K K) (v : ι → Series (K := K)) (b : Series (K := K))
    (h : (∑ i, extend (D i) (v i)) = b) (n : ℤ) :
    (∑ i, D i ((v i).coeff n)) = b.coeff n := by
  have hc := congrArg (fun s : Series (K := K) => s.coeff n) h
  simpa only [HahnSeries.coeff_sum, extend_coeff] using hc

/-- Extending the coefficient field to formal Laurent series cannot make a
constant source exact unless it was already exact over the original ring. -/
theorem exists_divergence_constant_iff {ι : Type*} [Fintype ι]
    (D : ι → Derivation C K K) (b : K) :
    (∃ v : ι → Series (K := K), ∑ i, extend (D i) (v i) = HahnSeries.single 0 b) ↔
      ∃ v : ι → K, ∑ i, D i (v i) = b := by
  constructor
  · rintro ⟨v, hv⟩
    refine ⟨fun i => (v i).coeff 0, ?_⟩
    simpa using divergence_coefficient D v _ hv 0
  · rintro ⟨v, hv⟩
    refine ⟨fun i => HahnSeries.single 0 (v i), ?_⟩
    simp_rw [extend_single]
    change (∑ i, HahnSeries.single.addMonoidHom 0 (D i (v i))) =
      HahnSeries.single.addMonoidHom 0 b
    rw [← map_sum (HahnSeries.single.addMonoidHom 0), hv]

end CycleQ2LaurentDerivation

#print axioms CycleQ2LaurentDerivation.extend
#print axioms CycleQ2LaurentDerivation.divergence_coefficient
#print axioms CycleQ2LaurentDerivation.exists_divergence_constant_iff
end
end


/- Component: continuation_2/AffineNormalExpansion.lean -/
section
/-!
The actual normal formal coordinate at the generic point of f=0.

We solve f(x0(T),x1,...,x4)=T in K[[T]], prove that its constant-coefficient
map is the actual residue map on polynomials, and prove injectivity of the
resulting polynomial substitution. The formal derivative satisfies the
actual normal chain rule. These are local algebraic facts, independent of
any assertion that the target residue is exact.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section

namespace CycleQ2NormalExpansion

open MvPolynomial HodgeComputer CycleQ2AffineClearing CycleQ2AffineGeometry
  CycleQ2AffineHypersurface CycleQ2FormalSpecialization

abbrev K := AffineFunctionField
abbrev S := PowerSeries K

def normalEquation : Polynomial S :=
  Polynomial.X ^ 6 +
    (Polynomial.C (PowerSeries.C (1 + fieldCoordinate 1 ^ 6 +
      fieldCoordinate 2 ^ 6 + fieldCoordinate 3 ^ 6 + fieldCoordinate 4 ^ 6)) +
      Polynomial.C (PowerSeries.C (1 / 2 : K)) *
        (Polynomial.X * Polynomial.C (PowerSeries.C (fieldCoordinate 2 * fieldCoordinate 3)) +
          Polynomial.X ^ 3 * Polynomial.C (PowerSeries.C
            (fieldCoordinate 1 * fieldCoordinate 3 * fieldCoordinate 4)) +
          Polynomial.C (PowerSeries.C
            (fieldCoordinate 1 ^ 3 * fieldCoordinate 4 * fieldCoordinate 2))) -
      Polynomial.C PowerSeries.X)

theorem normalEquation_monic : normalEquation.Monic := by
  unfold normalEquation
  apply Polynomial.monic_X_pow_add
  compute_degree!

theorem normalEquation_specializes :
    normalEquation.eval₂ (PowerSeries.constantCoeff (R := K)) (fieldCoordinate 0) = 0 := by
  convert targetFamily_specializes using 1 <;>
    simp [normalEquation, targetFamily] <;> ring

theorem normalEquation_simple :
    normalEquation.derivative.eval₂ (PowerSeries.constantCoeff (R := K))
      (fieldCoordinate 0) ≠ 0 := by
  convert targetFamily_simple using 1 <;>
    simp [normalEquation, targetFamily, Polynomial.derivative_pow]

theorem normal_root_exists :
    ∃ z : S, normalEquation.eval z = 0 ∧ z.constantCoeff = fieldCoordinate 0 :=
  simple_root_lifts normalEquation normalEquation_monic (fieldCoordinate 0)
    normalEquation_specializes normalEquation_simple

def normalRoot : S := Classical.choose normal_root_exists

theorem normalRoot_equation : normalEquation.eval normalRoot = 0 :=
  (Classical.choose_spec normal_root_exists).1

@[simp] theorem normalRoot_constantCoeff :
    normalRoot.constantCoeff = fieldCoordinate 0 :=
  (Classical.choose_spec normal_root_exists).2

def normalCoordinates : Fin 5 → S :=
  Fin.cases normalRoot (fun j => PowerSeries.C (fieldCoordinate j.succ))

def normalExpansion : AmbientPoly 4 →+* S :=
  MvPolynomial.eval₂Hom (PowerSeries.C.comp (affineMap.comp MvPolynomial.C)) normalCoordinates

@[simp] theorem normalExpansion_C (c : ℂ) :
    normalExpansion (MvPolynomial.C c) = PowerSeries.C (affineMap (MvPolynomial.C c)) := by
  simp [normalExpansion]

@[simp] theorem normalExpansion_X_zero :
    normalExpansion (MvPolynomial.X (0 : Fin 5)) = normalRoot := by
  simp [normalExpansion, normalCoordinates]

@[simp] theorem normalExpansion_X_succ (j : Fin 4) :
    normalExpansion (MvPolynomial.X j.succ) = PowerSeries.C (fieldCoordinate j.succ) := by
  simp [normalExpansion, normalCoordinates]

/-- The constant coefficient is exactly the previously constructed quotient
map into the protected hypersurface function field, on every polynomial. -/
theorem constantCoeff_normalExpansion (P : AmbientPoly 4) :
    (normalExpansion P).constantCoeff = affineMap P := by
  have h : (PowerSeries.constantCoeff (R := K)).comp normalExpansion = affineMap := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [fieldCoordinate]
      · simp [fieldCoordinate]
  exact RingHom.congr_fun h P

/-- The normal parameter is the actual protected equation f. -/
theorem normalExpansion_F : normalExpansion affineF = PowerSeries.X := by
  have hf := congrArg normalExpansion affineF_formula
  have hr := normalRoot_equation
  have hc : normalExpansion (MvPolynomial.C (1 / 2 : ℂ)) =
      PowerSeries.C (1 / 2 : K) := by
    rw [normalExpansion_C]
    congr 1
    change (affineMap.comp MvPolynomial.C) (1 / 2 : ℂ) = _
    rw [map_div₀, map_one, map_ofNat]
  norm_num [normalEquation, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C] at hr
  simp only [map_add, map_mul, map_pow, map_one, hc] at hf
  have h1 : normalExpansion (MvPolynomial.X (1 : Fin 5)) =
      PowerSeries.C (fieldCoordinate 1) := normalExpansion_X_succ 0
  have h2 : normalExpansion (MvPolynomial.X (2 : Fin 5)) =
      PowerSeries.C (fieldCoordinate 2) := normalExpansion_X_succ 1
  have h3 : normalExpansion (MvPolynomial.X (3 : Fin 5)) =
      PowerSeries.C (fieldCoordinate 3) := normalExpansion_X_succ 2
  have h4 : normalExpansion (MvPolynomial.X (4 : Fin 5)) =
      PowerSeries.C (fieldCoordinate 4) := normalExpansion_X_succ 3
  rw [hf]
  simp only [normalExpansion_X_zero, h1, h2, h3, h4]
  change 1 + normalRoot ^ 6 + PowerSeries.C (fieldCoordinate 1) ^ 6 +
    PowerSeries.C (fieldCoordinate 2) ^ 6 + PowerSeries.C (fieldCoordinate 3) ^ 6 +
    PowerSeries.C (fieldCoordinate 4) ^ 6 +
      PowerSeries.C (1 / 2 : K) *
        (normalRoot * PowerSeries.C (fieldCoordinate 2) * PowerSeries.C (fieldCoordinate 3) +
          normalRoot ^ 3 * PowerSeries.C (fieldCoordinate 1) *
            PowerSeries.C (fieldCoordinate 3) * PowerSeries.C (fieldCoordinate 4) +
          PowerSeries.C (fieldCoordinate 1) ^ 3 * PowerSeries.C (fieldCoordinate 4) *
            PowerSeries.C (fieldCoordinate 2)) = _
  simp only [one_div]
  linear_combination hr

theorem normalExpansion_injective : Function.Injective normalExpansion := by
  have hnonzero (P : AmbientPoly 4) (hP : P ≠ 0) : normalExpansion P ≠ 0 := by
    obtain ⟨m, U, hFU, hfactor⟩ := WfDvdMonoid.max_power_factor hP affineF_irreducible
    have hU : normalExpansion U ≠ 0 := by
      intro h
      have hc := congrArg (PowerSeries.constantCoeff (R := K)) h
      rw [constantCoeff_normalExpansion, map_zero] at hc
      exact hFU ((affineMap_kernel U).mp hc)
    rw [hfactor, map_mul, map_pow, normalExpansion_F]
    exact mul_ne_zero (pow_ne_zero _ PowerSeries.X_ne_zero) hU
  intro P Q h
  by_contra hn
  exact hnonzero (P - Q) (sub_ne_zero.mpr hn) (by rw [map_sub, h, sub_self])

abbrev Dt : Derivation K S S := PowerSeries.derivative K

def normalVelocity : S := Dt normalRoot

/-- Chain rule for every polynomial under the actual formal normal chart. -/
theorem normalExpansion_chain_rule (P : AmbientPoly 4) :
    Dt (normalExpansion P) = normalExpansion (pderiv 0 P) * normalVelocity := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [Dt]
  | add P Q ihP ihQ =>
      simp only [map_add, ihP, ihQ, add_mul]
  | mul_X P i ih =>
      refine Fin.cases ?_ (fun j => ?_) i
      · simp only [map_mul, Derivation.leibniz, normalExpansion_X_zero, ih,
          normalVelocity, pderiv_mul, pderiv_X_self, mul_one, map_add,
          smul_eq_mul]
        ring
      · simp only [map_mul, Derivation.leibniz, normalExpansion_X_succ, ih,
          pderiv_mul, pderiv_X, Pi.single_apply, Fin.succ_ne_zero,
          if_false, mul_zero, add_zero, map_add, map_zero, smul_eq_mul,
          PowerSeries.derivative_C, mul_zero, zero_add]
        ring

theorem normal_velocity_identity :
    normalExpansion (pderiv 0 affineF) * normalVelocity = 1 := by
  have h := normalExpansion_chain_rule affineF
  rw [normalExpansion_F, PowerSeries.derivative_X] at h
  exact h.symm

end CycleQ2NormalExpansion

#print axioms CycleQ2NormalExpansion.normalExpansion_F
#print axioms CycleQ2NormalExpansion.normalExpansion_injective
#print axioms CycleQ2NormalExpansion.normalExpansion_chain_rule
#print axioms CycleQ2NormalExpansion.normal_velocity_identity
end
end


/- Component: continuation_2/AffineFormalResidue.lean -/
section
/-!
The actual pole-three residue coefficient in a genuine formal normal chart.

The normal chart sends f to T and holds the four other coordinates fixed.
Its Jacobian in the normal direction is dx0/dT. We prove that the T^(-1)
coefficient of A(x(T)) (dx0/dT) / T^3 is precisely the previously defined
normal source divided by g. This supplies the local residue calculation;
it does not assert geometric support or global de Rham vanishing.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
noncomputable section

namespace CycleQ2FormalResidue

open MvPolynomial HodgeComputer CycleQ2AffineClearing CycleQ2AffineHypersurface
  CycleQ2AffineResidueClosure CycleQ2NormalExpansion HoldoutConstruction
open SplitHigherResidue

abbrev K := AffineFunctionField
abbrev S := PowerSeries K

local instance coefficientCharZero : CharZero K :=
  charZero_of_injective_algebraMap (algebraMap ℂ K).injective

def normalG : K := affineMap (pderiv 0 affineF)
def normalG1 : K := affineMap (pderiv 0 (pderiv 0 affineF))
def normalG2 : K := affineMap (pderiv 0 (pderiv 0 (pderiv 0 affineF)))

theorem normalG_ne_zero : normalG ≠ 0 := normal_ne_zero

theorem velocity_first_identity :
    normalExpansion (pderiv 0 (pderiv 0 affineF)) * normalVelocity ^ 2 +
      normalExpansion (pderiv 0 affineF) * Dt normalVelocity = 0 := by
  have h := congrArg Dt normal_velocity_identity
  simp only [Derivation.leibniz, normalExpansion_chain_rule,
    smul_eq_mul, Derivation.map_one_eq_zero] at h
  linear_combination h

theorem velocity_second_identity :
    normalExpansion (pderiv 0 (pderiv 0 (pderiv 0 affineF))) * normalVelocity ^ 3 +
      3 * normalExpansion (pderiv 0 (pderiv 0 affineF)) * normalVelocity * Dt normalVelocity +
      normalExpansion (pderiv 0 affineF) * Dt (Dt normalVelocity) = 0 := by
  have h := congrArg Dt velocity_first_identity
  simp only [map_add, Derivation.leibniz, normalExpansion_chain_rule,
    Derivation.leibniz_pow, smul_eq_mul, map_zero] at h
  norm_num only [Nat.cast_ofNat, pow_one, Nat.reduceSub] at h
  linear_combination h

theorem velocity_constant : normalVelocity.constantCoeff = 1 / normalG := by
  have h := congrArg (PowerSeries.constantCoeff (R := K)) normal_velocity_identity
  simp only [map_mul, constantCoeff_normalExpansion, map_one] at h
  apply (eq_div_iff normalG_ne_zero).mpr
  simpa only [normalG, mul_comm] using h

theorem velocity_first_constant :
    (Dt normalVelocity).constantCoeff = -normalG1 / normalG ^ 3 := by
  have h := congrArg (PowerSeries.constantCoeff (R := K)) velocity_first_identity
  simp only [map_add, map_mul, map_pow, constantCoeff_normalExpansion, map_zero,
    velocity_constant] at h
  change normalG1 * (1 / normalG) ^ 2 +
    normalG * (Dt normalVelocity).constantCoeff = 0 at h
  apply (eq_div_iff (pow_ne_zero _ normalG_ne_zero)).mpr
  field_simp [normalG_ne_zero] at h
  linear_combination h

theorem velocity_second_constant :
    (Dt (Dt normalVelocity)).constantCoeff =
      (3 * normalG1 ^ 2 - normalG * normalG2) / normalG ^ 5 := by
  have h := congrArg (PowerSeries.constantCoeff (R := K)) velocity_second_identity
  simp only [map_add, map_mul, map_pow, map_ofNat, constantCoeff_normalExpansion,
    map_zero, velocity_constant, velocity_first_constant] at h
  change normalG2 * (1 / normalG) ^ 3 +
    3 * normalG1 * (1 / normalG) * (-normalG1 / normalG ^ 3) +
    normalG * (Dt (Dt normalVelocity)).constantCoeff = 0 at h
  apply (eq_div_iff (pow_ne_zero _ normalG_ne_zero)).mpr
  field_simp [normalG_ne_zero] at h
  linear_combination h

def densityStream (A : AmbientPoly 4) : S := normalExpansion A * normalVelocity

theorem densityStream_second_derivative (A : AmbientPoly 4) :
    Dt (Dt (densityStream A)) =
      normalExpansion (pderiv 0 (pderiv 0 A)) * normalVelocity ^ 3 +
        3 * normalExpansion (pderiv 0 A) * normalVelocity * Dt normalVelocity +
        normalExpansion A * Dt (Dt normalVelocity) := by
  simp only [densityStream, Derivation.leibniz, map_add, normalExpansion_chain_rule,
    smul_eq_mul]
  ring

/-- The normal Taylor coefficient is the actual residue density used in
the protected affine exactness criterion. -/
theorem densityStream_coefficient_two (A : AmbientPoly 4) :
    PowerSeries.coeff 2 (densityStream A) = affineNormalSource A / normalG := by
  have hcoef := PowerSeries.constantCoeff_iterate_derivative (densityStream A) 2
  norm_num only [Function.iterate_succ_apply', Function.iterate_zero_apply,
    Nat.factorial_succ, Nat.factorial_zero, Nat.cast_mul, Nat.cast_ofNat,
    Nat.cast_one, mul_one] at hcoef
  have hderiv := congrArg (PowerSeries.constantCoeff (R := K))
    (densityStream_second_derivative A)
  simp only [map_add, map_mul, map_pow, map_ofNat, constantCoeff_normalExpansion,
    velocity_constant, velocity_first_constant, velocity_second_constant] at hderiv
  have he : PowerSeries.coeff 2 (densityStream A) =
      (affineMap (pderiv 0 (pderiv 0 A)) * (1 / normalG) ^ 3 +
        3 * affineMap (pderiv 0 A) * (1 / normalG) * (-normalG1 / normalG ^ 3) +
        affineMap A * ((3 * normalG1 ^ 2 - normalG * normalG2) / normalG ^ 5)) / 2 := by
    rw [hcoef] at hderiv
    apply (eq_div_iff (by norm_num : (2 : K) ≠ 0)).mpr
    simpa only [mul_comm] using hderiv
  rw [he]
  unfold affineNormalSource normalSourceTwo normalG normalG1 normalG2
  field_simp [normal_ne_zero]
  ring

/-- The density of the actual pulled-back pole-three form in the genuine
normal chart. Its denominator is the image of f, not a formal replacement. -/
def poleThreeDensity (A : AmbientPoly 4) : HahnSeries ℤ K :=
  HahnSeries.ofPowerSeries ℤ K (normalExpansion A) /
      (HahnSeries.ofPowerSeries ℤ K (normalExpansion affineF)) ^ 3 *
    HahnSeries.ofPowerSeries ℤ K normalVelocity

theorem poleThreeDensity_expansion (A : AmbientPoly 4) :
    poleThreeDensity A = HahnSeries.ofPowerSeries ℤ K (densityStream A) *
      HahnSeries.single (-3) 1 := by
  simp only [poleThreeDensity, normalExpansion_F, HahnSeries.ofPowerSeries_X,
    div_eq_mul_inv, HahnSeries.single_pow, nsmul_eq_mul, one_pow,
    HahnSeries.inv_single, inv_one, densityStream, map_mul]
  norm_num
  ring

/-- The Laurent residue of the actual pole-three normal pullback is c/g. -/
theorem poleThreeDensity_residue (A : AmbientPoly 4) :
    (poleThreeDensity A).coeff (-1) = affineNormalSource A / normalG := by
  rw [poleThreeDensity_expansion, HahnSeries.coeff_mul_single]
  norm_num only [Int.reduceSub, mul_one]
  change (HahnSeries.ofPowerSeries ℤ K (densityStream A)).coeff ((2 : ℕ) : ℤ) = _
  rw [HahnSeries.ofPowerSeries_apply_coeff, densityStream_coefficient_two]

/-- Binding to the genuine exterior form used by the certificate theorem.
The coefficient is computed from the actual normal pullback, not postulated. -/
theorem residueSourceForm_eq_formalResidue (A : AmbientPoly 4) :
    CycleQ2AffineExactness.residueSourceForm A =
      (poleThreeDensity A).coeff (-1) • CycleQ2AffineExterior.volume := by
  rw [poleThreeDensity_residue]
  rfl

end CycleQ2FormalResidue

#print axioms CycleQ2FormalResidue.densityStream_coefficient_two
#print axioms CycleQ2FormalResidue.poleThreeDensity_residue
#print axioms CycleQ2FormalResidue.residueSourceForm_eq_formalResidue
end
end


/- Component: continuation_2/NormalChartDerivations.lean -/
section
/-!+# Actual coordinate derivations and Jacobian of the formal normal chart

The coefficient derivations are the actual complex tangent derivations of
the protected affine function field, extended coefficient by coefficient.
The formal parameter is held constant.  The normal derivative and the four
tangent derivations therefore give the implicit-coordinate Jacobian of the
faithful chart already constructed from `f ↦ T`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section

namespace CycleQ2PowerSeriesTangents

variable {C K : Type*} [CommRing C] [CommRing K] [Algebra C K]

def coefficientwise (D : Derivation C K K) (f : PowerSeries K) : PowerSeries K :=
  PowerSeries.mk fun n => D (PowerSeries.coeff n f)

@[simp] theorem coefficientwise_coeff (D : Derivation C K K) (f : PowerSeries K) (n : ℕ) :
    PowerSeries.coeff n (coefficientwise D f) = D (PowerSeries.coeff n f) := by
  simp [coefficientwise]

theorem coefficientwise_mul (D : Derivation C K K) (f g : PowerSeries K) :
    coefficientwise D (f * g) = f * coefficientwise D g + g * coefficientwise D f := by
  rw [mul_comm g (coefficientwise D f)]
  ext n
  simp only [coefficientwise_coeff, PowerSeries.coeff_mul, map_sum, map_add,
    Derivation.leibniz, smul_eq_mul, Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro ij hij
  ring

/-- Coefficientwise extension as an actual complex-linear derivation. -/
def extend (D : Derivation C K K) : Derivation C (PowerSeries K) (PowerSeries K) where
  toFun := coefficientwise D
  map_add' f g := by
    ext n
    simp
  map_smul' c f := by
    ext n
    simp only [coefficientwise_coeff, PowerSeries.coeff_smul, Derivation.map_smul,
      RingHom.id_apply]
  map_one_eq_zero' := by
    ext n
    by_cases hn : n = 0 <;> simp [PowerSeries.coeff_one, hn]
  leibniz' f g := by
    change coefficientwise D (f * g) = f * coefficientwise D g + g * coefficientwise D f
    exact coefficientwise_mul D f g

@[simp] theorem extend_coeff (D : Derivation C K K) (f : PowerSeries K) (n : ℕ) :
    PowerSeries.coeff n (extend D f) = D (PowerSeries.coeff n f) :=
  coefficientwise_coeff D f n

@[simp] theorem extend_C (D : Derivation C K K) (a : K) :
    extend D (PowerSeries.C a) = PowerSeries.C (D a) := by
  ext n
  by_cases hn : n = 0 <;> simp [PowerSeries.coeff_C, hn]

@[simp] theorem extend_X (D : Derivation C K K) : extend D PowerSeries.X = 0 := by
  ext n
  by_cases hn : n = 1 <;> simp [PowerSeries.coeff_X, hn]

theorem extend_commute (D E : Derivation C K K) (h : Function.Commute D E) :
    Function.Commute (extend D) (extend E) := by
  intro f
  ext n
  simpa only [extend_coeff] using h (PowerSeries.coeff n f)

theorem derivative_extend_commute (D : Derivation C K K) :
    Function.Commute (PowerSeries.derivative K) (extend D) := by
  intro f
  ext n
  simp [PowerSeries.coeff_derivative, Derivation.leibniz, smul_eq_mul, mul_comm]

end CycleQ2PowerSeriesTangents

namespace CycleQ2PolynomialChainRule

open MvPolynomial

variable {R B M σ : Type*} [CommRing R] [CommRing B] [Algebra R B]
  [Fintype σ] [DecidableEq σ] [AddCommGroup M] [Module B M] [Module R M]

/-- The genuine derivation chain rule for any polynomial algebra map. -/
theorem apply (φ : MvPolynomial σ R →ₐ[R] B) (δ : Derivation R B M)
    (P : MvPolynomial σ R) :
    δ (φ P) = ∑ i : σ, φ (pderiv i P) • δ (φ (X i)) := by
  induction P using MvPolynomial.induction_on with
  | C c =>
      have hc : φ (MvPolynomial.C c) = algebraMap R B c := φ.commutes c
      rw [hc, Derivation.map_algebraMap]
      simp
  | add P Q ihP ihQ =>
      simp only [map_add, ihP, ihQ, add_smul, Finset.sum_add_distrib]
  | mul_X P i ih =>
      have hs :
          (∑ j : σ, (φ (pderiv j P) * φ (X i)) • δ (φ (X j))) =
          φ (X i) • ∑ j : σ, φ (pderiv j P) • δ (φ (X j)) := by
        rw [Finset.smul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        rw [smul_smul]
        congr 1
        ring
      have hd :
          (∑ j : σ, (φ P * φ (pderiv j (X i))) • δ (φ (X j))) =
          φ P • δ (φ (X i)) := by
        simp [pderiv_X, Pi.single_apply, apply_ite]
      rw [map_mul, Derivation.leibniz, ih]
      simp only [pderiv_mul, map_add, map_mul, add_smul, Finset.sum_add_distrib]
      rw [hs, hd]
      exact add_comm _ _

end CycleQ2PolynomialChainRule

namespace CycleQ2NormalChart

open MvPolynomial HodgeComputer CycleQ2AffineClearing CycleQ2AffineHypersurface
  CycleQ2AffineDifferentials CycleQ2FormalSpecialization CycleQ2NormalExpansion

abbrev K := AffineFunctionField
abbrev S := PowerSeries K

def normalAlgHom : AmbientPoly 4 →ₐ[ℂ] S where
  toRingHom := normalExpansion
  commutes' c := by
    change normalExpansion (MvPolynomial.C c) = algebraMap ℂ S c
    rw [normalExpansion_C, PowerSeries.algebraMap_apply]
    rfl

def tangent (j : Fin 4) : Derivation ℂ S S :=
  CycleQ2PowerSeriesTangents.extend (complexTangent j)

def parameterDerivative : Derivation ℂ S S :=
  (PowerSeries.derivative K).restrictScalars ℂ

@[simp] theorem parameterDerivative_apply (f : S) : parameterDerivative f = Dt f := rfl

@[simp] theorem tangent_C (j : Fin 4) (a : K) :
    tangent j (PowerSeries.C a) = PowerSeries.C (affineTangent j a) := by
  exact CycleQ2PowerSeriesTangents.extend_C (complexTangent j) a

@[simp] theorem tangent_X (j : Fin 4) : tangent j PowerSeries.X = 0 :=
  CycleQ2PowerSeriesTangents.extend_X (complexTangent j)

@[simp] theorem tangent_coordinate (j i : Fin 4) :
    tangent j (PowerSeries.C (fieldCoordinate i.succ)) = if i = j then 1 else 0 := by
  rw [tangent_C]
  simp only [fieldCoordinate, affineTangent_coordinate]
  split_ifs <;> simp

theorem tangent_normalExpansion_chain (j : Fin 4) (P : AmbientPoly 4) :
    tangent j (normalExpansion P) =
      normalExpansion (pderiv 0 P) * tangent j normalRoot +
        normalExpansion (pderiv j.succ P) := by
  have h := CycleQ2PolynomialChainRule.apply normalAlgHom (tangent j) P
  change tangent j (normalExpansion P) =
    ∑ i : Fin 5, normalExpansion (pderiv i P) * tangent j (normalExpansion (X i)) at h
  rw [Fin.sum_univ_succ] at h
  simpa only [normalExpansion_X_zero, normalExpansion_X_succ, tangent_coordinate,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] using h

theorem tangent_normalRoot (j : Fin 4) :
    tangent j normalRoot = -normalVelocity * normalExpansion (pderiv j.succ affineF) := by
  have h := tangent_normalExpansion_chain j affineF
  rw [normalExpansion_F, tangent_X] at h
  calc
    tangent j normalRoot =
        (normalExpansion (pderiv 0 affineF) * normalVelocity) * tangent j normalRoot := by
      rw [normal_velocity_identity, one_mul]
    _ = -normalVelocity * normalExpansion (pderiv j.succ affineF) := by
      linear_combination -normalVelocity * h

/-- The actual implicit-coordinate derivative with `f` held equal to the
formal parameter.  Its reciprocal normal derivative is the proved velocity. -/
theorem tangent_normalExpansion (j : Fin 4) (P : AmbientPoly 4) :
    tangent j (normalExpansion P) = normalExpansion (pderiv j.succ P) -
      normalVelocity * normalExpansion (pderiv j.succ affineF) *
        normalExpansion (pderiv 0 P) := by
  rw [tangent_normalExpansion_chain, tangent_normalRoot]
  ring

theorem tangents_commute (i j : Fin 4) : Function.Commute (tangent i) (tangent j) := by
  apply CycleQ2PowerSeriesTangents.extend_commute
  exact affineTangents_commute i j

theorem parameter_tangent_commute (j : Fin 4) :
    Function.Commute parameterDerivative (tangent j) :=
  CycleQ2PowerSeriesTangents.derivative_extend_commute (complexTangent j)

/-- The coordinate derivations are ordered `(∂T,E₁,E₂,E₃,E₄)`. -/
def coordinateDerivative : Fin 5 → Derivation ℂ S S :=
  Fin.cases parameterDerivative tangent

/-- Rows are coordinate derivations; columns are the five original affine
coordinate functions after the actual normal substitution. -/
def jacobian : Matrix (Fin 5) (Fin 5) S :=
  fun i j => coordinateDerivative i (normalExpansion (X j))

theorem jacobian_zero_row (i : Fin 5) :
    jacobian 0 i = if i = 0 then normalVelocity else 0 := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [jacobian, coordinateDerivative, normalVelocity]
  · simp [jacobian, coordinateDerivative, Dt]

theorem jacobian_succ_zero (j : Fin 4) :
    jacobian j.succ 0 = -normalVelocity * normalExpansion (pderiv j.succ affineF) := by
  simpa [jacobian, coordinateDerivative] using tangent_normalRoot j

theorem jacobian_succ_succ (i j : Fin 4) :
    jacobian i.succ j.succ = if j = i then 1 else 0 := by
  change tangent i (normalExpansion (X j.succ)) = _
  rw [normalExpansion_X_succ, tangent_coordinate]

/-- The determinant is the actual normal velocity, with positive sign in
the stipulated parameter-first coordinate order. -/
theorem jacobian_det : Matrix.det jacobian = normalVelocity := by
  have hminor : jacobian.submatrix Fin.succ Fin.succ =
      (1 : Matrix (Fin 4) (Fin 4) S) := by
    ext i j
    simp [Matrix.submatrix, jacobian_succ_succ, Matrix.one_apply, eq_comm]
  rw [Matrix.det_succ_row_zero]
  simp [jacobian_zero_row, hminor]

/-! The algebraic Kähler module of a power-series ring need not be generated
by these five coordinate differentials.  The following argument instead
differentiates the actual polynomial relation inside that entire module. -/

abbrev Omega := Ω[S⁄ℂ]
abbrev universalD : Derivation ℂ S Omega := KaehlerDifferential.D ℂ S
abbrev TopForm := ⋀[S]^5 Omega

theorem normalExpansion_complex_constant (c : ℂ) :
    normalExpansion (MvPolynomial.C c) = algebraMap ℂ S c := by
  rw [normalExpansion_C, PowerSeries.algebraMap_apply]
  rfl

/-- The universal polynomial chain rule in the full algebraic Kähler module
of the power-series ring; no finite-rank or continuity assertion is used. -/
theorem universal_polynomial_differential (P : AmbientPoly 4) :
    universalD (normalExpansion P) =
      ∑ i : Fin 5, normalExpansion (pderiv i P) • universalD (normalExpansion (X i)) := by
  exact CycleQ2PolynomialChainRule.apply normalAlgHom universalD P

def tangentDifferential (j : Fin 4) : Omega :=
  universalD (PowerSeries.C (fieldCoordinate j.succ))

theorem universal_normal_differential :
    universalD normalRoot = normalVelocity • universalD PowerSeries.X -
      ∑ j : Fin 4, (normalVelocity * normalExpansion (pderiv j.succ affineF)) •
        tangentDifferential j := by
  have h := universal_polynomial_differential affineF
  rw [normalExpansion_F, Fin.sum_univ_succ] at h
  simp only [normalExpansion_X_zero, normalExpansion_X_succ] at h
  have hm := congrArg (fun η : Omega => normalVelocity • η) h
  have hv : normalVelocity * normalExpansion (pderiv 0 affineF) = 1 := by
    rw [mul_comm, normal_velocity_identity]
  simp only [smul_add, Finset.smul_sum, smul_smul, hv, one_smul] at hm
  exact (eq_sub_iff_add_eq).mpr hm.symm

private def wedgeWithTangents : Omega →ₗ[S] TopForm where
  toFun a := exteriorPower.ιMulti S 5 (Matrix.vecCons a tangentDifferential)
  map_add' a b := (exteriorPower.ιMulti S 5).map_vecCons_add tangentDifferential a b
  map_smul' c a := (exteriorPower.ιMulti S 5).map_vecCons_smul tangentDifferential c a

private theorem wedgeWithTangents_tangent (j : Fin 4) :
    wedgeWithTangents (tangentDifferential j) = 0 := by
  apply (exteriorPower.ιMulti S 5).map_eq_zero_of_eq
    (Matrix.vecCons (tangentDifferential j) tangentDifferential)
    (i := 0) (j := j.succ)
  · simp
  · exact (Fin.succ_ne_zero j).symm

/-- The ordered coordinate volume `dT ∧ dx₁ ∧ ... ∧ dx₄` in the actual
universal exterior power of the formal chart ring. -/
def normalVolume : TopForm :=
  exteriorPower.ιMulti S 5 (Matrix.vecCons (universalD PowerSeries.X) tangentDifferential)

/-- The wedge of the actual universal differentials of the substituted
five affine coordinates: the coordinate-generator exterior pullback. -/
def pulledBackCoordinateVolume : TopForm :=
  exteriorPower.ιMulti S 5 (fun i : Fin 5 => universalD (normalExpansion (X i)))

/-- The Jacobian factor also holds in genuine universal exterior forms,
not merely after evaluating against the five coordinate derivations. -/
theorem pulledBackCoordinateVolume_eq :
    pulledBackCoordinateVolume = normalVelocity • normalVolume := by
  have ht : (fun i : Fin 5 => universalD (normalExpansion (X i))) =
      Matrix.vecCons (universalD normalRoot) tangentDifferential := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · simp [tangentDifferential]
  unfold pulledBackCoordinateVolume
  rw [ht]
  change wedgeWithTangents (universalD normalRoot) = _
  rw [universal_normal_differential, map_sub, map_smul, map_sum]
  simp only [map_smul, wedgeWithTangents_tangent, smul_zero,
    Finset.sum_const_zero, sub_zero]
  rfl

section UniversalExteriorPullback

abbrev AmbientOmega := Ω[(AmbientPoly 4)⁄ℂ]

local instance normalAlgebra : Algebra (AmbientPoly 4) S :=
  normalAlgHom.toRingHom.toAlgebra

local instance normalOmegaModule : Module (AmbientPoly 4) Omega :=
  Module.compHom Omega normalAlgHom.toRingHom

local instance normalTopModule : Module (AmbientPoly 4) TopForm :=
  Module.compHom TopForm normalAlgHom.toRingHom

local instance normalOmegaTower : IsScalarTower (AmbientPoly 4) S Omega where
  smul_assoc a b η := by
    change (normalAlgHom a * b) • η = normalAlgHom a • (b • η)
    exact mul_smul _ _ _

local instance normalTopTower : IsScalarTower (AmbientPoly 4) S TopForm where
  smul_assoc a b η := by
    change (normalAlgHom a * b) • η = normalAlgHom a • (b • η)
    exact mul_smul _ _ _

local instance normalComplexOmegaTower : IsScalarTower ℂ (AmbientPoly 4) Omega where
  smul_assoc c a η := by
    change normalAlgHom (c • a) • η = c • (normalAlgHom a • η)
    rw [map_smul]
    exact smul_assoc _ _ _

/-- The actual map of universal one-forms induced by the normal chart. -/
def oneFormPullback : AmbientOmega →ₗ[AmbientPoly 4] Omega :=
  (universalD.compAlgebraMap (AmbientPoly 4)).liftKaehlerDifferential

@[simp] theorem oneFormPullback_D (P : AmbientPoly 4) :
    oneFormPullback (KaehlerDifferential.D ℂ (AmbientPoly 4) P) =
      universalD (normalExpansion P) := by
  rw [oneFormPullback, Derivation.liftKaehlerDifferential_comp_D]
  rfl

private def targetWedgeOverAmbient :
    Omega [⋀^Fin 5]→ₗ[AmbientPoly 4] TopForm where
  toMultilinearMap := (exteriorPower.ιMulti S 5).toMultilinearMap.restrictScalars (AmbientPoly 4)
  map_eq_zero_of_eq' := (exteriorPower.ιMulti S 5).map_eq_zero_of_eq

/-- The induced exterior pullback, defined by the universal alternating
property and the genuine one-form pullback. -/
def exteriorPullback : (⋀[AmbientPoly 4]^5 AmbientOmega) →ₗ[AmbientPoly 4] TopForm :=
  exteriorPower.alternatingMapLinearEquiv
    (targetWedgeOverAmbient.compLinearMap oneFormPullback)

def ambientCoordinateVolume : ⋀[AmbientPoly 4]^5 AmbientOmega :=
  exteriorPower.ιMulti (AmbientPoly 4) 5
    (fun i : Fin 5 => KaehlerDifferential.D ℂ (AmbientPoly 4) (X i))

theorem exteriorPullback_ambientCoordinateVolume :
    exteriorPullback ambientCoordinateVolume = normalVelocity • normalVolume := by
  rw [exteriorPullback, ambientCoordinateVolume,
    exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
    AlternatingMap.compLinearMap_apply]
  simp only [oneFormPullback_D]
  exact pulledBackCoordinateVolume_eq

end UniversalExteriorPullback

end CycleQ2NormalChart

#print axioms CycleQ2PowerSeriesTangents.extend
#print axioms CycleQ2NormalChart.tangent_normalExpansion
#print axioms CycleQ2NormalChart.jacobian_det
#print axioms CycleQ2NormalChart.universal_normal_differential
#print axioms CycleQ2NormalChart.pulledBackCoordinateVolume_eq
#print axioms CycleQ2NormalChart.exteriorPullback_ambientCoordinateVolume
end
end
