import Proposal.GeometricNormalizedCartierClass
import Proposal.GeometricSurfaceBindings
import Proposal.GeometricSurfaceCoordinates
import Proposal.GeometricTarget01Part01
import Proposal.GeometricSeedConormalBases

/-! Continuation of GeometricTarget01.lean; complete source components and declarations. -/

set_option Elab.async false

/- Component: continuation_3/IncidenceNormalForm.lean -/
section
/-!
# Normal forms for the two equations of the Segre incidence chart

This file proves the product criterion needed here from the division algorithm.
It does not take a Groebner basis as a hypothesis.  The coefficient ring may have
zero divisors: the two leading coefficients are normalized to one.
-/

noncomputable section

open MvPolynomial
open scoped MonomialOrder

namespace CycleQ2IncidenceNormalForm

variable {σ R : Type*} [CommRing R]


/-- Reduction preserves every grading for which the two defining equations
are homogeneous.  Taking the grading monoid to be `ℕ × ZMod 3` preserves the
ordinary weighted degree and the order-three character simultaneously. -/
theorem reduced_isWeightedHomogeneous
    {M : Type*} [AddCommMonoid M] (w : σ → M)
    (m : MonomialOrder σ) {h F p r a b : MvPolynomial σ R} {dh dF d : M}
    (hh : m.Monic h) (hF : m.Monic F)
    (hcop : ∀ i, m.degree h i = 0 ∨ m.degree F i = 0)
    (hhhom : h.IsWeightedHomogeneous w dh) (hFhom : F.IsWeightedHomogeneous w dF)
    (hphom : p.IsWeightedHomogeneous w d) (hr : Reduced m h F r)
    (heq : p = a * h + b * F + r) : r.IsWeightedHomogeneous w d := by
  classical
  letI := MvPolynomial.weightedGradedAlgebra R w
  have hI : (equationsIdeal h F).IsHomogeneous (weightedHomogeneousSubmodule R w) := by
    apply Ideal.homogeneous_span
    intro q hq
    rcases hq with rfl | hq
    · exact ⟨dh, hhhom⟩
    · obtain rfl := hq
      exact ⟨dF, hFhom⟩
  have hpr : p - r ∈ equationsIdeal h F := by
    apply Ideal.mem_span_pair.mpr
    exact ⟨a, b, by rw [heq]; ring⟩
  have hprojected := weightedHomogeneousComponent_mem_of_mem R w hI hpr d
  rw [map_sub, weightedHomogeneousComponent_eq_self hphom] at hprojected
  obtain ⟨a', b', heq'⟩ := Ideal.mem_span_pair.mp hprojected
  have hr' : Reduced m h F (weightedHomogeneousComponent w d r) := by
    intro e he
    rw [support_weightedHomogeneousComponent] at he
    exact hr e (Finset.mem_filter.mp he).1
  have hrep' : p = a' * h + b' * F + weightedHomogeneousComponent w d r := by
    linear_combination -heq'
  have hequal : r = weightedHomogeneousComponent w d r :=
    reduced_unique m hh hF hcop hr hr' heq hrep'
  rw [hequal]
  exact weightedHomogeneousComponent_isWeightedHomogeneous (w := w) d r

theorem reduced_isHomogeneous
    (m : MonomialOrder σ) {h F p r a b : MvPolynomial σ R} {dh dF d : ℕ}
    (hh : m.Monic h) (hF : m.Monic F)
    (hcop : ∀ i, m.degree h i = 0 ∨ m.degree F i = 0)
    (hhhom : h.IsHomogeneous dh) (hFhom : F.IsHomogeneous dF)
    (hphom : p.IsHomogeneous d) (hr : Reduced m h F r)
    (heq : p = a * h + b * F + r) : r.IsHomogeneous d :=
  reduced_isWeightedHomogeneous (1 : σ → ℕ) m hh hF hcop hhhom hFhom hphom hr heq

/-! ## The concrete auxiliary order

The coefficient ring in this presentation contains `x₁,x₂,x₃`.  The two
polynomial variables are `x₀,w`, with auxiliary weights `3,7`.  This is enough
to prove the rank-nine freeness over that coefficient ring; the ordinary
weighted degree and character gradings can subsequently be taken componentwise.
-/

def cubicTailExponent (i : Fin 4) : Exponent :=
  ![0, Finsupp.single 0 1, Finsupp.single 0 2, Finsupp.single 1 1] i

/-- The invariant cubic has no `x₀ w` term.  Its only term involving `w` is
`w x₃`, whose coefficient is absorbed into the coefficient ring here. -/
def normalizedCubic (c : Fin 4 → R) : MvPolynomial (Fin 2) R :=
  monomial (Finsupp.single 0 3) 1 + ∑ i, monomial (cubicTailExponent i) (c i)

abbrev SexticTailIndex :=
  {ij : Fin 7 × Fin 3 // ij.1.val + 2 * ij.2.val ≤ 6}

def sexticTailExponent (i : SexticTailIndex) : Exponent :=
  Finsupp.single 0 i.val.1.val + Finsupp.single 1 i.val.2.val

/-- Every term of the weighted sextic other than `w³` has `w` exponent at most
two and satisfies `x₀` exponent plus twice `w` exponent at most six. -/
def normalizedSextic (c : SexticTailIndex → R) : MvPolynomial (Fin 2) R :=
  monomial (Finsupp.single 1 3) 1 + ∑ i, monomial (sexticTailExponent i) (c i)

theorem normalizedCubic_leading_data [Nontrivial R] (c : Fin 4 → R) :
    auxiliaryOrder.degree (normalizedCubic c) = Finsupp.single 0 3 ∧
      auxiliaryOrder.Monic (normalizedCubic c) := by
  apply degree_monic_add_sum auxiliaryOrder
  · apply auxiliaryOrder_lt_of_weight_lt
    norm_num [auxiliaryWeight]
  · intro i
    apply auxiliaryOrder_lt_of_weight_lt
    fin_cases i <;> norm_num [auxiliaryWeight, cubicTailExponent]

theorem normalizedSextic_leading_data [Nontrivial R] (c : SexticTailIndex → R) :
    auxiliaryOrder.degree (normalizedSextic c) = Finsupp.single 1 3 ∧
      auxiliaryOrder.Monic (normalizedSextic c) := by
  apply degree_monic_add_sum auxiliaryOrder
  · apply auxiliaryOrder_lt_of_weight_lt
    norm_num [auxiliaryWeight]
  · intro i
    apply auxiliaryOrder_lt_of_weight_lt
    have hi := i.property
    have hj := i.val.2.isLt
    simp only [auxiliaryWeight, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
      sexticTailExponent, Finsupp.add_apply, Finsupp.single_apply]
    norm_num
    omega

/-- Standard monomials for the actual incidence chart have both distinguished
exponents strictly less than three. -/
def Standard (p : MvPolynomial (Fin 2) R) : Prop :=
  ∀ d ∈ p.support, d 0 < 3 ∧ d 1 < 3

theorem reduced_iff_standard [Nontrivial R]
    (hcoeff : Fin 4 → R) (Fcoeff : SexticTailIndex → R)
    (p : MvPolynomial (Fin 2) R) :
    Reduced auxiliaryOrder (normalizedCubic hcoeff) (normalizedSextic Fcoeff) p ↔
      Standard p := by
  simp only [Reduced, Standard, (normalizedCubic_leading_data hcoeff).1,
    (normalizedSextic_leading_data Fcoeff).1, single_three_le_iff, not_le]

/-- The actual two-variable coefficient chart has unique standard remainders.
The assumptions here are just the coefficients of its normalized cubic and
sextic; no basis, confluence, Groebner, or rank hypothesis is supplied. -/
theorem existsUnique_standard_representative [Nontrivial R]
    (hcoeff : Fin 4 → R) (Fcoeff : SexticTailIndex → R)
    (p : MvPolynomial (Fin 2) R) :
    ∃! r, Standard r ∧ ∃ a b,
      p = a * normalizedCubic hcoeff + b * normalizedSextic Fcoeff + r := by
  obtain ⟨hd, hm⟩ := normalizedCubic_leading_data hcoeff
  obtain ⟨Fd, Fm⟩ := normalizedSextic_leading_data Fcoeff
  have hcop : ∀ i, auxiliaryOrder.degree (normalizedCubic hcoeff) i = 0 ∨
      auxiliaryOrder.degree (normalizedSextic Fcoeff) i = 0 := by
    intro i
    rw [hd, Fd]
    fin_cases i <;> simp
  simpa only [reduced_iff_standard] using
    existsUnique_reduced_representative auxiliaryOrder
      (normalizedCubic hcoeff) (normalizedSextic Fcoeff) p hm Fm hcop

noncomputable def standardRemainder [Nontrivial R]
    (hcoeff : Fin 4 → R) (Fcoeff : SexticTailIndex → R)
    (p : MvPolynomial (Fin 2) R) : MvPolynomial (Fin 2) R :=
  (existsUnique_standard_representative hcoeff Fcoeff p).choose

theorem standardRemainder_spec [Nontrivial R]
    (hcoeff : Fin 4 → R) (Fcoeff : SexticTailIndex → R)
    (p : MvPolynomial (Fin 2) R) :
    Standard (standardRemainder hcoeff Fcoeff p) ∧ ∃ a b,
      p = a * normalizedCubic hcoeff + b * normalizedSextic Fcoeff +
        standardRemainder hcoeff Fcoeff p :=
  (existsUnique_standard_representative hcoeff Fcoeff p).choose_spec.1

theorem eq_standardRemainder [Nontrivial R]
    (hcoeff : Fin 4 → R) (Fcoeff : SexticTailIndex → R)
    (p r : MvPolynomial (Fin 2) R)
    (hr : Standard r) (hp : ∃ a b,
      p = a * normalizedCubic hcoeff + b * normalizedSextic Fcoeff + r) :
    r = standardRemainder hcoeff Fcoeff p :=
  (existsUnique_standard_representative hcoeff Fcoeff p).choose_spec.2 r ⟨hr, hp⟩

lemma standard_map {S : Type*} [CommRing S] (φ : R →+* S)
    {p : MvPolynomial (Fin 2) R} (hp : Standard p) :
    Standard (MvPolynomial.map φ p) := by
  intro d hd
  exact hp d (MvPolynomial.support_map_subset φ p hd)

@[simp] theorem map_normalizedCubic {S : Type*} [CommRing S]
    (φ : R →+* S) (c : Fin 4 → R) :
    MvPolynomial.map φ (normalizedCubic c) = normalizedCubic (φ ∘ c) := by
  simp [normalizedCubic]

@[simp] theorem map_normalizedSextic {S : Type*} [CommRing S]
    (φ : R →+* S) (c : SexticTailIndex → R) :
    MvPolynomial.map φ (normalizedSextic c) = normalizedSextic (φ ∘ c) := by
  simp [normalizedSextic]

/-- Normal reduction commutes with every coefficient specialization.  In
particular, it commutes with maps from the localized universal coefficient ring
to the residue field or to the generic lifted field. -/
theorem standardRemainder_map [Nontrivial R] {S : Type*} [CommRing S] [Nontrivial S]
    (φ : R →+* S) (hcoeff : Fin 4 → R) (Fcoeff : SexticTailIndex → R)
    (p : MvPolynomial (Fin 2) R) :
    MvPolynomial.map φ (standardRemainder hcoeff Fcoeff p) =
      standardRemainder (φ ∘ hcoeff) (φ ∘ Fcoeff) (MvPolynomial.map φ p) := by
  obtain ⟨hr, a, b, hp⟩ := standardRemainder_spec hcoeff Fcoeff p
  apply eq_standardRemainder _ _ _ _ (standard_map φ hr)
  refine ⟨MvPolynomial.map φ a, MvPolynomial.map φ b, ?_⟩
  simpa only [map_add, map_mul, map_normalizedCubic, map_normalizedSextic] using
    congrArg (MvPolynomial.map φ) hp

theorem standardRemainder_eq_zero_iff [Nontrivial R]
    (hcoeff : Fin 4 → R) (Fcoeff : SexticTailIndex → R)
    (p : MvPolynomial (Fin 2) R) :
    standardRemainder hcoeff Fcoeff p = 0 ↔
      p ∈ equationsIdeal (normalizedCubic hcoeff) (normalizedSextic Fcoeff) := by
  constructor
  · intro hr
    obtain ⟨_, a, b, hp⟩ := standardRemainder_spec hcoeff Fcoeff p
    apply Ideal.mem_span_pair.mpr
    exact ⟨a, b, by simpa [hr] using hp.symm⟩
  · intro hp
    obtain ⟨a, b, hp⟩ := Ideal.mem_span_pair.mp hp
    symm
    apply eq_standardRemainder _ _ _ _ (by simp [Standard])
    exact ⟨a, b, by simpa using hp.symm⟩

lemma concrete_coprime [Nontrivial R]
    (hcoeff : Fin 4 → R) (Fcoeff : SexticTailIndex → R) :
    ∀ i, auxiliaryOrder.degree (normalizedCubic hcoeff) i = 0 ∨
      auxiliaryOrder.degree (normalizedSextic Fcoeff) i = 0 := by
  intro i
  rw [(normalizedCubic_leading_data hcoeff).1, (normalizedSextic_leading_data Fcoeff).1]
  fin_cases i <;> simp

noncomputable def concreteExponentEquiv [Nontrivial R]
    (hcoeff : Fin 4 → R) (Fcoeff : SexticTailIndex → R) :
    reducedExponents auxiliaryOrder (normalizedCubic hcoeff) (normalizedSextic Fcoeff) ≃
      Fin 3 × Fin 3 where
  toFun d :=
    (⟨d.val 0, by
      have hd := d.property.1
      rw [(normalizedCubic_leading_data hcoeff).1, single_three_le_iff] at hd
      omega⟩,
     ⟨d.val 1, by
      have hd := d.property.2
      rw [(normalizedSextic_leading_data Fcoeff).1, single_three_le_iff] at hd
      omega⟩)
  invFun ij := ⟨Finsupp.single 0 ij.1.val + Finsupp.single 1 ij.2.val, by
    constructor
    · rw [(normalizedCubic_leading_data hcoeff).1, single_three_le_iff]
      simpa using Nat.not_le_of_lt ij.1.isLt
    · rw [(normalizedSextic_leading_data Fcoeff).1, single_three_le_iff]
      simpa using Nat.not_le_of_lt ij.2.isLt⟩
  left_inv d := by
    apply Subtype.ext
    ext i
    fin_cases i <;> simp
  right_inv ij := by
    apply Prod.ext <;> apply Fin.ext <;> simp

/-- Rank-nine quotient basis for the normalized incidence chart, indexed by
the exponents `0 ≤ i,j < 3` of `x₀ⁱ wʲ`. -/
noncomputable def incidenceBasis [Nontrivial R]
    (hcoeff : Fin 4 → R) (Fcoeff : SexticTailIndex → R) :
    Module.Basis (Fin 3 × Fin 3) R
      (MvPolynomial (Fin 2) R ⧸ equationsIdeal
        (normalizedCubic hcoeff) (normalizedSextic Fcoeff)) :=
  (quotientBasis auxiliaryOrder (normalizedCubic hcoeff) (normalizedSextic Fcoeff)
    (normalizedCubic_leading_data hcoeff).2 (normalizedSextic_leading_data Fcoeff).2
    (concrete_coprime hcoeff Fcoeff)).reindex (concreteExponentEquiv hcoeff Fcoeff)

theorem incidenceBasis_apply [Nontrivial R]
    (hcoeff : Fin 4 → R) (Fcoeff : SexticTailIndex → R) (ij : Fin 3 × Fin 3) :
    incidenceBasis hcoeff Fcoeff ij =
      Ideal.Quotient.mk (equationsIdeal (normalizedCubic hcoeff) (normalizedSextic Fcoeff))
        (X 0 ^ ij.1.val * X 1 ^ ij.2.val) := by
  rw [incidenceBasis, Module.Basis.reindex_apply, quotientBasis_apply]
  congr 1
  change monomial (Finsupp.single 0 ij.1.val + Finsupp.single 1 ij.2.val) 1 = _
  rw [MvPolynomial.monomial_single_add, ← MvPolynomial.X_pow_eq_monomial]

/-- Scaling either defining equation by a unit does not change which polynomial
is its standard remainder.  This is the precise passage from a localization
chart with invertible leading coefficients to the monic presentation. -/
theorem existsUnique_standard_unit_scaled [Nontrivial R]
    (hcoeff : Fin 4 → R) (Fcoeff : SexticTailIndex → R) (u v : Rˣ)
    (p : MvPolynomial (Fin 2) R) :
    ∃! r, Standard r ∧ ∃ a b,
      p = a * (C (u : R) * normalizedCubic hcoeff) +
        b * (C (v : R) * normalizedSextic Fcoeff) + r := by
  apply (existsUnique_congr (fun r ↦ and_congr_right (fun _ ↦
    unit_scaled_representation_iff u v (normalizedCubic hcoeff)
      (normalizedSextic Fcoeff) p r))).mp
  exact existsUnique_standard_representative hcoeff Fcoeff p

/-- Grouping the eight non-leading invariant cubic coefficients by powers of
`x₀` gives the exact cubic family used by the incidence chart.  The three
coefficient-ring variables are `x₁,x₂,x₃`, in that order. -/
def invariantCubicTailCoefficients (c : Fin 8 → R) : Fin 4 → MvPolynomial (Fin 3) R :=
  ![C (c 2) * X 0 ^ 3 + C (c 4) * X 0 * X 1 * X 2 +
      C (c 5) * X 1 ^ 3 + C (c 6) * X 2 ^ 3,
    C (c 1) * X 0 ^ 2 + C (c 3) * X 1 * X 2,
    C (c 0) * X 0,
    C (c 7) * X 2]

noncomputable def invariantIncidenceBasis [Nontrivial R]
    (hcoeff : Fin 8 → R) (Fcoeff : SexticTailIndex → MvPolynomial (Fin 3) R) :
    Module.Basis (Fin 3 × Fin 3) (MvPolynomial (Fin 3) R)
      (MvPolynomial (Fin 2) (MvPolynomial (Fin 3) R) ⧸ equationsIdeal
        (normalizedCubic (invariantCubicTailCoefficients hcoeff))
        (normalizedSextic Fcoeff)) :=
  incidenceBasis (invariantCubicTailCoefficients hcoeff) Fcoeff

/-! ## Full-variable weighted order and invariant polynomial family -/


def fullAuxiliaryWeight : FullExponent →+ ℕ where
  toFun e := 3 * e 0 + e 1 + e 2 + e 3 + 7 * e 4
  map_zero' := by simp
  map_add' a b := by
    simp only [Finsupp.add_apply]
    omega

noncomputable def fullAuxiliaryOrder : MonomialOrder (Fin 5) :=
  weightedOrder MonomialOrder.lex fullAuxiliaryWeight






theorem normalizedFullCubic_leading_data [Nontrivial R] (c : FullCubicTailIndex → R) :
    fullAuxiliaryOrder.degree (normalizedFullCubic c) = Finsupp.single 0 3 ∧
      fullAuxiliaryOrder.Monic (normalizedFullCubic c) := by
  apply degree_monic_add_sum fullAuxiliaryOrder
  · apply weightedOrder_lt_of_weight_lt
    norm_num [fullAuxiliaryWeight]
  · intro e
    apply weightedOrder_lt_of_weight_lt
    have hd := e.val.property.1
    have hc := e.val.property.2
    have h0 := e.property
    simp only [fullDegree, fullCharacter] at hd hc
    simp [fullAuxiliaryWeight]
    have h4 : (e.val.val 4).val ≤ 1 := by omega
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h4 with h4 | h4
    · omega
    · have hc_lt : 2 * (e.val.val 0).val + 2 * (e.val.val 1).val +
          (e.val.val 2).val < 3 := by omega
      rw [Nat.mod_eq_of_lt hc_lt] at hc
      omega

theorem normalizedFullSextic_leading_data [Nontrivial R] (c : FullSexticTailIndex → R) :
    fullAuxiliaryOrder.degree (normalizedFullSextic c) = Finsupp.single 4 3 ∧
      fullAuxiliaryOrder.Monic (normalizedFullSextic c) := by
  apply degree_monic_add_sum fullAuxiliaryOrder
  · apply weightedOrder_lt_of_weight_lt
    norm_num [fullAuxiliaryWeight]
  · intro e
    apply weightedOrder_lt_of_weight_lt
    have hd := e.val.property.1
    have h4 := e.property
    simp only [fullDegree] at hd
    simp [fullAuxiliaryWeight]
    omega

def FullStandard (p : MvPolynomial (Fin 5) R) : Prop :=
  ∀ e ∈ p.support, e 0 < 3 ∧ e 4 < 3

theorem full_reduced_iff_standard [Nontrivial R]
    (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R)
    (p : MvPolynomial (Fin 5) R) :
    Reduced fullAuxiliaryOrder (normalizedFullCubic hcoeff) (normalizedFullSextic Fcoeff) p ↔
      FullStandard p := by
  simp only [Reduced, FullStandard, (normalizedFullCubic_leading_data hcoeff).1,
    (normalizedFullSextic_leading_data Fcoeff).1, single_three_le_iff, not_le]

lemma full_coprime [Nontrivial R]
    (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R) :
    ∀ i, fullAuxiliaryOrder.degree (normalizedFullCubic hcoeff) i = 0 ∨
      fullAuxiliaryOrder.degree (normalizedFullSextic Fcoeff) i = 0 := by
  intro i
  rw [(normalizedFullCubic_leading_data hcoeff).1, (normalizedFullSextic_leading_data Fcoeff).1]
  fin_cases i <;> simp

theorem existsUnique_full_standard_representative [Nontrivial R]
    (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R)
    (p : MvPolynomial (Fin 5) R) :
    ∃! r, FullStandard r ∧ ∃ a b,
      p = a * normalizedFullCubic hcoeff + b * normalizedFullSextic Fcoeff + r := by
  simpa only [full_reduced_iff_standard] using
    existsUnique_reduced_representative fullAuxiliaryOrder
      (normalizedFullCubic hcoeff) (normalizedFullSextic Fcoeff) p
      (normalizedFullCubic_leading_data hcoeff).2 (normalizedFullSextic_leading_data Fcoeff).2
      (full_coprime hcoeff Fcoeff)


theorem normalizedFullCubic_homogeneous (c : FullCubicTailIndex → R) :
    (normalizedFullCubic c).IsWeightedHomogeneous fullGrading (3, 0) := by
  apply (weightedHomogeneousSubmodule R fullGrading (3, 0)).add_mem
  · apply isWeightedHomogeneous_monomial
    rw [Finsupp.weight_single]
    decide
  · apply (weightedHomogeneousSubmodule R fullGrading (3, 0)).sum_mem
    intro e _
    exact isWeightedHomogeneous_monomial fullGrading _ _ (fullGrading_of_invariant e.val)

theorem normalizedFullSextic_homogeneous (c : FullSexticTailIndex → R) :
    (normalizedFullSextic c).IsWeightedHomogeneous fullGrading (6, 0) := by
  apply (weightedHomogeneousSubmodule R fullGrading (6, 0)).add_mem
  · apply isWeightedHomogeneous_monomial
    rw [Finsupp.weight_single]
    decide
  · apply (weightedHomogeneousSubmodule R fullGrading (6, 0)).sum_mem
    intro e _
    exact isWeightedHomogeneous_monomial fullGrading _ _ (fullGrading_of_invariant e.val)















/-- This applies directly over the localized universal coefficient ring: the
inverted leading coefficients are units, and no inverse equations are asserted
in an unconstrained polynomial ring. -/
theorem existsUnique_full_standard_unit_leading [Nontrivial R]
    (u v : Rˣ) (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R)
    (p : MvPolynomial (Fin 5) R) :
    ∃! r, FullStandard r ∧ ∃ a b,
      p = a * rawFullCubic (u : R) hcoeff + b * rawFullSextic (v : R) Fcoeff + r := by
  rw [rawFullCubic_eq_unit_mul, rawFullSextic_eq_unit_mul]
  apply (existsUnique_congr (fun r ↦ and_congr_right (fun _ ↦
    unit_scaled_representation_iff u v
      (normalizedFullCubic (fun e ↦ (↑u⁻¹ : R) * hcoeff e))
      (normalizedFullSextic (fun e ↦ (↑v⁻¹ : R) * Fcoeff e)) p r))).mp
  exact existsUnique_full_standard_representative
    (fun e ↦ (↑u⁻¹ : R) * hcoeff e) (fun e ↦ (↑v⁻¹ : R) * Fcoeff e) p

/-- The normal-form chart for the entire invariant cubic/sextic coefficient
space.  Its only open conditions are invertibility of the two indicated
leading coefficients. -/
theorem existsUnique_full_invariant_representative [Nontrivial R]
    (hcoeff : FullInvariantIndex 3 → R) (Fcoeff : FullInvariantIndex 6 → R)
    (hu : IsUnit (hcoeff fullCubicLeadingIndex))
    (Fu : IsUnit (Fcoeff fullSexticLeadingIndex)) (p : MvPolynomial (Fin 5) R) :
    ∃! r, FullStandard r ∧ ∃ a b,
      p = a * fullInvariantPolynomial 3 hcoeff + b * fullInvariantPolynomial 6 Fcoeff + r := by
  rw [fullInvariantPolynomial_cubic, fullInvariantPolynomial_sextic]
  simpa only [hu.unit_spec, Fu.unit_spec] using
    existsUnique_full_standard_unit_leading hu.unit Fu.unit
      (fun e ↦ hcoeff e.val) (fun e ↦ Fcoeff e.val) p

theorem full_standard_preserves_grading [Nontrivial R]
    (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R)
    {p r a b : MvPolynomial (Fin 5) R} {d : ℕ} {χ : ZMod 3}
    (hp : p.IsWeightedHomogeneous fullGrading (d, χ)) (hr : FullStandard r)
    (heq : p = a * normalizedFullCubic hcoeff + b * normalizedFullSextic Fcoeff + r) :
    r.IsWeightedHomogeneous fullGrading (d, χ) := by
  exact reduced_isWeightedHomogeneous fullGrading fullAuxiliaryOrder
    (normalizedFullCubic_leading_data hcoeff).2 (normalizedFullSextic_leading_data Fcoeff).2
    (full_coprime hcoeff Fcoeff) (normalizedFullCubic_homogeneous hcoeff)
    (normalizedFullSextic_homogeneous Fcoeff) hp
    ((full_reduced_iff_standard hcoeff Fcoeff r).mpr hr) heq

theorem full_invariant_standard_preserves_grading [Nontrivial R]
    (hcoeff : FullInvariantIndex 3 → R) (Fcoeff : FullInvariantIndex 6 → R)
    (hu : IsUnit (hcoeff fullCubicLeadingIndex))
    (Fu : IsUnit (Fcoeff fullSexticLeadingIndex))
    {p r a b : MvPolynomial (Fin 5) R} {d : ℕ} {χ : ZMod 3}
    (hp : p.IsWeightedHomogeneous fullGrading (d, χ)) (hr : FullStandard r)
    (heq : p = a * fullInvariantPolynomial 3 hcoeff +
      b * fullInvariantPolynomial 6 Fcoeff + r) :
    r.IsWeightedHomogeneous fullGrading (d, χ) := by
  let hc : FullCubicTailIndex → R := fun e ↦ (↑hu.unit⁻¹ : R) * hcoeff e.val
  let Fc : FullSexticTailIndex → R := fun e ↦ (↑Fu.unit⁻¹ : R) * Fcoeff e.val
  have hh : fullInvariantPolynomial 3 hcoeff = C (hu.unit : R) * normalizedFullCubic hc := by
    rw [fullInvariantPolynomial_cubic]
    exact (congrArg (fun z ↦ rawFullCubic z (fun e ↦ hcoeff e.val)) hu.unit_spec.symm).trans
      (rawFullCubic_eq_unit_mul hu.unit _)
  have hF : fullInvariantPolynomial 6 Fcoeff = C (Fu.unit : R) * normalizedFullSextic Fc := by
    rw [fullInvariantPolynomial_sextic]
    exact (congrArg (fun z ↦ rawFullSextic z (fun e ↦ Fcoeff e.val)) Fu.unit_spec.symm).trans
      (rawFullSextic_eq_unit_mul Fu.unit _)
  rw [hh, hF] at heq
  exact full_standard_preserves_grading hc Fc hp hr
    (a := a * C (hu.unit : R)) (b := b * C (Fu.unit : R))
    (by simpa only [mul_assoc] using heq)

noncomputable def fullRemainder [Nontrivial R]
    (hcoeff : FullInvariantIndex 3 → R) (Fcoeff : FullInvariantIndex 6 → R)
    (hu : IsUnit (hcoeff fullCubicLeadingIndex))
    (Fu : IsUnit (Fcoeff fullSexticLeadingIndex)) (p : MvPolynomial (Fin 5) R) :
    MvPolynomial (Fin 5) R :=
  (existsUnique_full_invariant_representative hcoeff Fcoeff hu Fu p).choose

theorem fullRemainder_spec [Nontrivial R]
    (hcoeff : FullInvariantIndex 3 → R) (Fcoeff : FullInvariantIndex 6 → R)
    (hu : IsUnit (hcoeff fullCubicLeadingIndex))
    (Fu : IsUnit (Fcoeff fullSexticLeadingIndex)) (p : MvPolynomial (Fin 5) R) :
    FullStandard (fullRemainder hcoeff Fcoeff hu Fu p) ∧ ∃ a b,
      p = a * fullInvariantPolynomial 3 hcoeff + b * fullInvariantPolynomial 6 Fcoeff +
        fullRemainder hcoeff Fcoeff hu Fu p :=
  (existsUnique_full_invariant_representative hcoeff Fcoeff hu Fu p).choose_spec.1

theorem fullRemainder_preserves_grading [Nontrivial R]
    (hcoeff : FullInvariantIndex 3 → R) (Fcoeff : FullInvariantIndex 6 → R)
    (hu : IsUnit (hcoeff fullCubicLeadingIndex))
    (Fu : IsUnit (Fcoeff fullSexticLeadingIndex))
    {p : MvPolynomial (Fin 5) R} {d : ℕ} {χ : ZMod 3}
    (hp : p.IsWeightedHomogeneous fullGrading (d, χ)) :
    (fullRemainder hcoeff Fcoeff hu Fu p).IsWeightedHomogeneous fullGrading (d, χ) := by
  obtain ⟨hr, a, b, heq⟩ := fullRemainder_spec hcoeff Fcoeff hu Fu p
  exact full_invariant_standard_preserves_grading hcoeff Fcoeff hu Fu hp hr heq

lemma fullStandard_map {S : Type*} [CommRing S] (φ : R →+* S)
    {p : MvPolynomial (Fin 5) R} (hp : FullStandard p) :
    FullStandard (MvPolynomial.map φ p) := by
  intro d hd
  exact hp d (MvPolynomial.support_map_subset φ p hd)

/-- Actual full-family coefficient specialization, including the leading-unit
chart, commutes with reduction. -/
theorem fullRemainder_map [Nontrivial R] {S : Type*} [CommRing S] [Nontrivial S]
    (φ : R →+* S) (hcoeff : FullInvariantIndex 3 → R) (Fcoeff : FullInvariantIndex 6 → R)
    (hu : IsUnit (hcoeff fullCubicLeadingIndex))
    (Fu : IsUnit (Fcoeff fullSexticLeadingIndex)) (p : MvPolynomial (Fin 5) R) :
    MvPolynomial.map φ (fullRemainder hcoeff Fcoeff hu Fu p) =
      fullRemainder (φ ∘ hcoeff) (φ ∘ Fcoeff) (hu.map φ) (Fu.map φ) (MvPolynomial.map φ p) := by
  obtain ⟨hr, a, b, hp⟩ := fullRemainder_spec hcoeff Fcoeff hu Fu p
  apply (existsUnique_full_invariant_representative
    (φ ∘ hcoeff) (φ ∘ Fcoeff) (hu.map φ) (Fu.map φ) (MvPolynomial.map φ p)).choose_spec.2
  refine ⟨fullStandard_map φ hr, MvPolynomial.map φ a, MvPolynomial.map φ b, ?_⟩
  simpa only [map_add, map_mul, map_fullInvariantPolynomial] using congrArg (MvPolynomial.map φ) hp

theorem fullRemainder_eq_zero_iff [Nontrivial R]
    (hcoeff : FullInvariantIndex 3 → R) (Fcoeff : FullInvariantIndex 6 → R)
    (hu : IsUnit (hcoeff fullCubicLeadingIndex))
    (Fu : IsUnit (Fcoeff fullSexticLeadingIndex)) (p : MvPolynomial (Fin 5) R) :
    fullRemainder hcoeff Fcoeff hu Fu p = 0 ↔
      p ∈ equationsIdeal (fullInvariantPolynomial 3 hcoeff) (fullInvariantPolynomial 6 Fcoeff) := by
  constructor
  · intro hr
    obtain ⟨_, a, b, hp⟩ := fullRemainder_spec hcoeff Fcoeff hu Fu p
    apply Ideal.mem_span_pair.mpr
    exact ⟨a, b, by simpa [hr] using hp.symm⟩
  · intro hp
    obtain ⟨a, b, hp⟩ := Ideal.mem_span_pair.mp hp
    symm
    apply (existsUnique_full_invariant_representative hcoeff Fcoeff hu Fu p).choose_spec.2
    exact ⟨by simp [FullStandard], a, b, by simpa using hp.symm⟩

end CycleQ2IncidenceNormalForm

#print axioms CycleQ2IncidenceNormalForm.reduced_eq_zero_of_representation
#print axioms CycleQ2IncidenceNormalForm.quotientBasis_apply
#print axioms CycleQ2IncidenceNormalForm.fullInvariantPolynomial_of_homogeneous
#print axioms CycleQ2IncidenceNormalForm.existsUnique_full_invariant_representative
#print axioms CycleQ2IncidenceNormalForm.fullRemainder_map
#print axioms CycleQ2IncidenceNormalForm.fullRemainder_preserves_grading
#print axioms CycleQ2IncidenceNormalForm.fullRemainder_eq_zero_iff
end
end


/- Component: continuation_3/LinearAnnihilatorKernel.lean -/
section
/-! Exactness forced by a small annihilator and dimension bounds. The proof
uses only the actual entry image, the full image, and the restricted detector.
No preselected entry correction or large invertible matrix is assumed.
-/

noncomputable section
set_option maxHeartbeats 300000

namespace CycleQ2LinearAnnihilatorKernel

variable {K V W X : Type*} [Field K]
  [AddCommGroup V] [Module K V] [Module.Finite K V]
  [AddCommGroup W] [Module K W] [AddCommGroup X] [Module K X]

theorem annihilator_kernel_eq_entry_range
    (E : W →ₗ[K] V) (J : X →ₗ[K] V) (r s : ℕ) (L : V →ₗ[K] (Fin s → K))
    (hEJ : LinearMap.range E≤LinearMap.range J)
    (hJ : Module.finrank K (LinearMap.range J)≤r+s)
    (hE : r≤Module.finrank K (LinearMap.range E))
    (hLE : L.comp E=0)
    (hsurj : Function.Surjective (L.domRestrict (LinearMap.range J))) :
    LinearMap.range J ⊓ LinearMap.ker L=LinearMap.range E := by
  let U : Submodule K V := LinearMap.range J
  let P : Submodule K U := (LinearMap.range E).comap U.subtype
  let T : U →ₗ[K] (Fin s → K) := L.domRestrict U
  have hPK : P≤LinearMap.ker T := by
    intro y hy
    change (y:V)∈LinearMap.range E at hy
    obtain ⟨w,hw⟩ := hy
    change L (y:V)=0
    rw [←hw]
    exact LinearMap.congr_fun hLE w
  have hPdim : Module.finrank K P=Module.finrank K (LinearMap.range E) :=
    (Submodule.comapSubtypeEquivOfLe hEJ).finrank_eq
  have hPbound : r≤Module.finrank K P := by
    rw [hPdim]
    exact hE
  have hTsurj : Function.Surjective T := hsurj
  have hTdim : Module.finrank K (LinearMap.range T)=s := by
    rw [LinearMap.range_eq_top.mpr hTsurj]
    simp only [finrank_top,Module.finrank_fintype_fun_eq_card,Fintype.card_fin]
  have hUbound : Module.finrank K U≤r+s := hJ
  have hnull := T.finrank_range_add_finrank_ker
  rw [hTdim] at hnull
  have hKbound : Module.finrank K (LinearMap.ker T)≤r := by omega
  have heq : P=LinearMap.ker T :=
    Submodule.eq_of_le_of_finrank_eq hPK
      (Nat.le_antisymm (Submodule.finrank_mono hPK) (hKbound.trans hPbound))
  ext y
  constructor
  · intro hy
    let q : U := ⟨y,hy.1⟩
    have hq : q∈LinearMap.ker T := by
      change L y=0
      exact hy.2
    have hp : q∈P := by rw [heq]; exact hq
    change y∈LinearMap.range E at hp
    exact hp
  · intro hy
    refine ⟨hEJ hy,?_⟩
    obtain ⟨w,rfl⟩ := hy
    change L (E w)=0
    exact LinearMap.congr_fun hLE w

theorem exists_entry_correction
    (E : W →ₗ[K] V) (J : X →ₗ[K] V) (r s : ℕ) (L : V →ₗ[K] (Fin s → K))
    (hEJ : LinearMap.range E≤LinearMap.range J)
    (hJ : Module.finrank K (LinearMap.range J)≤r+s)
    (hE : r≤Module.finrank K (LinearMap.range E))
    (hLE : L.comp E=0)
    (hsurj : Function.Surjective (L.domRestrict (LinearMap.range J)))
    (y : V) (hy : y∈LinearMap.range J) (hLy : L y=0) :
    ∃ w : W, E w=y := by
  change y∈LinearMap.range E
  rw [←annihilator_kernel_eq_entry_range E J r s L hEJ hJ hE hLE hsurj]
  exact ⟨hy,hLy⟩

end CycleQ2LinearAnnihilatorKernel

#print axioms CycleQ2LinearAnnihilatorKernel.annihilator_kernel_eq_entry_range
#print axioms CycleQ2LinearAnnihilatorKernel.exists_entry_correction
end
end


/- Component: continuation_3/LinearAnnihilatorRank.lean -/
section
/-! # Rank gained by directions detected by an annihilator of an existing image -/

noncomputable section
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace CycleQ2LinearAnnihilatorRank

variable {K X Z V Y W : Type*} [Field K]
  [AddCommGroup X] [Module K X] [AddCommGroup Z] [Module K Z]
  [AddCommGroup V] [Module K V] [AddCommGroup Y] [Module K Y]
  [AddCommGroup W] [Module K W] [FiniteDimensional K Y]

/-- The old image lies in the kernel of the restricted detector, while the
new detected image lies in its range. Rank-nullity gives the sum bound. -/
theorem rank_add_le_of_annihilator (f : X →ₗ[K] Y) (g : Z →ₗ[K] Y)
    (H : V →ₗ[K] Y) (L : Y →ₗ[K] W)
    (hf : LinearMap.range f≤LinearMap.range H)
    (hg : LinearMap.range g≤LinearMap.range H) (hLf : L.comp f=0) :
    Module.finrank K (LinearMap.range f)+Module.finrank K (LinearMap.range (L.comp g))≤
      Module.finrank K (LinearMap.range H) := by
  let R := LinearMap.range H
  let T : R →ₗ[K] W := L.comp R.subtype
  have hzero (y : LinearMap.range f) : L y.val=0 := by
    obtain ⟨x,hx⟩ := y.property
    rw [←hx]
    exact LinearMap.congr_fun hLf x
  let inclusion : LinearMap.range f →ₗ[K] LinearMap.ker T :=
    { toFun := fun y => ⟨⟨y.val,hf y.property⟩,hzero y⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hinj : Function.Injective inclusion := by
    intro a b hab
    apply Subtype.ext
    exact congrArg (fun y : LinearMap.ker T => y.val.val) hab
  have h1 : Module.finrank K (LinearMap.range f)≤Module.finrank K (LinearMap.ker T) :=
    LinearMap.finrank_le_finrank_of_injective hinj
  have h2 : LinearMap.range (L.comp g)≤LinearMap.range T := by
    rintro z ⟨x,rfl⟩
    exact ⟨⟨g x,hg ⟨x,rfl⟩⟩,rfl⟩
  have h3 := Submodule.finrank_mono h2
  have h4 := T.finrank_range_add_finrank_ker
  change Module.finrank K (LinearMap.range T)+Module.finrank K (LinearMap.ker T)=
    Module.finrank K (LinearMap.range H) at h4
  omega

variable {m n a b k : Type*} [Fintype m] [Fintype n] [Fintype a] [Fintype b] [Fintype k]

theorem selected_columns_range_le (H : Matrix m n K) (c : a → n) :
    LinearMap.range (Matrix.mulVecLin (H.submatrix id c))≤
      LinearMap.range (Matrix.mulVecLin H) := by
  rw [Matrix.range_mulVecLin,Matrix.range_mulVecLin]
  apply Submodule.span_mono
  rintro _ ⟨j,rfl⟩
  exact ⟨c j,rfl⟩

/-- A checked left-annihilator of one selected column block detects new
independent columns without any assumption about an unchecked large minor. -/
theorem selected_column_rank_add_le (H : Matrix m n K) (c0 : a → n) (c1 : b → n)
    (L : Matrix k m K) (hL : L*H.submatrix id c0=0) :
    (H.submatrix id c0).rank+(L*H.submatrix id c1).rank≤H.rank := by
  simp only [Matrix.rank]
  rw [Matrix.mulVecLin_mul L (H.submatrix id c1)]
  apply rank_add_le_of_annihilator (Matrix.mulVecLin (H.submatrix id c0))
    (Matrix.mulVecLin (H.submatrix id c1)) (Matrix.mulVecLin H) (Matrix.mulVecLin L)
    (selected_columns_range_le H c0) (selected_columns_range_le H c1)
  rw [←Matrix.mulVecLin_mul,hL]
  ext x
  simp

end CycleQ2LinearAnnihilatorRank

#print axioms CycleQ2LinearAnnihilatorRank.rank_add_le_of_annihilator
#print axioms CycleQ2LinearAnnihilatorRank.selected_column_rank_add_le
end
end


/- Component: continuation_3/LinearExactSequenceSplit.lean -/
section
/-! # Compatible nonconstructive coordinates for an exact Jacobian sequence

The equation space is split into the image of the Jacobian and a complement
detected by the actual relation matrix.  Both square seed blocks become the
identity in these coordinates.  The coordinate changes are selected from
proved exactness; no numerical pivot or inverse is an extra premise.
-/

noncomputable section
set_option maxHeartbeats 600000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace CycleQ2LinearExactSequenceSplit

open Matrix

variable {K X Y Z : Type*} [Field K]
  [AddCommGroup X] [Module K X] [AddCommGroup Y] [Module K Y]
  [AddCommGroup Z] [Module K Z]

/-- A compatible splitting, including an extension of the relation-coordinate
projection from the actual image to the whole relation space. -/
theorem exists_split (f : X →ₗ[K] Y) (g : Y →ₗ[K] Z)
    (hexact : LinearMap.range f = LinearMap.ker g) :
    ∃ (B : LinearMap.ker g →ₗ[K] X)
      (S : LinearMap.range g →ₗ[K] Y)
      (P : Y →ₗ[K] LinearMap.ker g)
      (T : Z →ₗ[K] LinearMap.range g),
      f.comp B = (LinearMap.ker g).subtype ∧
      g.rangeRestrict.comp S = LinearMap.id ∧
      (LinearMap.ker g).subtype.comp P + S.comp g.rangeRestrict = LinearMap.id ∧
      P.comp (LinearMap.ker g).subtype = LinearMap.id ∧
      P.comp S = 0 ∧
      T.comp (LinearMap.range g).subtype = LinearMap.id := by
  let f' : X →ₗ[K] LinearMap.ker g :=
    f.codRestrict (LinearMap.ker g) (fun x => hexact ▸ LinearMap.mem_range_self f x)
  have hf' : Function.Surjective f' := by
    intro y
    obtain ⟨x,hx⟩ := (show y.val ∈ LinearMap.range f from hexact.symm ▸ y.property)
    exact ⟨x,Subtype.ext hx⟩
  obtain ⟨B,hB⟩ := f'.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hf')
  obtain ⟨S,hS⟩ := g.rangeRestrict.exists_rightInverse_of_surjective g.range_rangeRestrict
  obtain ⟨T,hT⟩ := (LinearMap.range g).subtype.exists_leftInverse_of_injective
    (LinearMap.range g).ker_subtype
  have hSval (z : LinearMap.range g) : g (S z)=z.val := by
    exact congrArg Subtype.val (LinearMap.congr_fun hS z)
  let P : Y →ₗ[K] LinearMap.ker g :=
    (LinearMap.id - S.comp g.rangeRestrict).codRestrict (LinearMap.ker g) (by
      intro y
      change g (y-S (g.rangeRestrict y))=0
      rw [map_sub,hSval]
      exact sub_self _)
  refine ⟨B,S,P,T,?_,hS,?_,?_,?_,hT⟩
  · ext y
    exact congrArg Subtype.val (LinearMap.congr_fun hB y)
  · ext y
    change y-S (g.rangeRestrict y)+S (g.rangeRestrict y)=y
    exact sub_add_cancel _ _
  · ext y
    change y.val-S (g.rangeRestrict y.val)=y.val
    have hz : g.rangeRestrict y.val=0 := Subtype.ext y.property
    rw [hz,map_zero,sub_zero]
  · ext z
    change S z-S (g.rangeRestrict (S z))=0
    have hsz := LinearMap.congr_fun hS z
    change g.rangeRestrict (S z)=z at hsz
    rw [hsz,sub_self]

variable {m n l : Type*} [Fintype m] [Fintype n] [Fintype l] [DecidableEq m]

/-- Compatible square blocks for an exact pair of literal matrices.  The
first block is the Jacobian on chosen parameter directions; the second
is the relation matrix on complementary equation coordinates. -/
theorem exists_matrix_split (J : Matrix m n K) (R : Matrix l m K)
    (hexact : LinearMap.range (Matrix.mulVecLin J)=LinearMap.ker (Matrix.mulVecLin R)) :
    ∃ (P : Matrix (Fin J.rank) m K)
      (Q : Matrix m (Fin J.rank) K)
      (V : Matrix m (Fin R.rank) K)
      (W : Matrix (Fin R.rank) m K)
      (T : Matrix (Fin R.rank) l K)
      (B : Matrix n (Fin J.rank) K),
      Q*P+V*W=1 ∧ P*J*B=1 ∧ T*R*V=1 ∧ R*Q=0 ∧ P*V=0 := by
  classical
  let f := Matrix.mulVecLin J
  let g := Matrix.mulVecLin R
  obtain ⟨B,S,P,T,hB,hS,hdecomp,hP,hPS,hT⟩ := exists_split f g hexact
  have hdim : Module.finrank K (LinearMap.ker g)=J.rank := by
    rw [←hexact]
    rfl
  let bU : Module.Basis (Fin J.rank) K (LinearMap.ker g) :=
    (Module.finBasis K (LinearMap.ker g)).reindex (finCongr hdim)
  let bV := Module.finBasis K (LinearMap.range g)
  let P0 := bU.equivFun.toLinearMap.comp P
  let Q0 := (LinearMap.ker g).subtype.comp bU.equivFun.symm.toLinearMap
  let V0 := S.comp bV.equivFun.symm.toLinearMap
  let W0 := bV.equivFun.toLinearMap.comp g.rangeRestrict
  let T0 := bV.equivFun.toLinearMap.comp T
  let B0 := B.comp bU.equivFun.symm.toLinearMap
  refine ⟨LinearMap.toMatrix' P0,LinearMap.toMatrix' Q0,LinearMap.toMatrix' V0,
    LinearMap.toMatrix' W0,LinearMap.toMatrix' T0,LinearMap.toMatrix' B0,?_,?_,?_,?_,?_⟩
  · apply Matrix.toLin'.injective
    simp only [map_add,Matrix.toLin'_mul,Matrix.toLin'_toMatrix',Matrix.toLin'_one]
    apply LinearMap.ext
    intro y
    change (bU.equivFun.symm (bU.equivFun (P y))).val+
      S (bV.equivFun.symm (bV.equivFun (g.rangeRestrict y)))=y
    simp only [LinearEquiv.symm_apply_apply]
    exact LinearMap.congr_fun hdecomp y
  · apply Matrix.toLin'.injective
    simp only [Matrix.toLin'_mul,Matrix.toLin'_toMatrix',Matrix.toLin'_one]
    apply LinearMap.ext
    intro x
    change bU.equivFun (P (f (B (bU.equivFun.symm x))))=x
    have hb := LinearMap.congr_fun hB (bU.equivFun.symm x)
    change f (B (bU.equivFun.symm x))=(bU.equivFun.symm x).val at hb
    have hp := LinearMap.congr_fun hP (bU.equivFun.symm x)
    change P (bU.equivFun.symm x).val=bU.equivFun.symm x at hp
    rw [hb,hp,LinearEquiv.apply_symm_apply]
  · apply Matrix.toLin'.injective
    simp only [Matrix.toLin'_mul,Matrix.toLin'_toMatrix',Matrix.toLin'_one]
    apply LinearMap.ext
    intro x
    change bV.equivFun (T (g (S (bV.equivFun.symm x))))=x
    have hSv := congrArg Subtype.val (LinearMap.congr_fun hS (bV.equivFun.symm x))
    change g (S (bV.equivFun.symm x))=(bV.equivFun.symm x).val at hSv
    have ht := LinearMap.congr_fun hT (bV.equivFun.symm x)
    change T (bV.equivFun.symm x).val=bV.equivFun.symm x at ht
    rw [hSv,ht,LinearEquiv.apply_symm_apply]
  · apply Matrix.toLin'.injective
    simp only [Matrix.toLin'_mul,Matrix.toLin'_toMatrix',map_zero]
    apply LinearMap.ext
    intro x
    exact (bU.equivFun.symm x).property
  · apply Matrix.toLin'.injective
    simp only [Matrix.toLin'_mul,Matrix.toLin'_toMatrix',map_zero]
    apply LinearMap.ext
    intro x
    change bU.equivFun (P (S (bV.equivFun.symm x)))=0
    have hps := LinearMap.congr_fun hPS (bV.equivFun.symm x)
    change P (S (bV.equivFun.symm x))=0 at hps
    rw [hps,map_zero]

end CycleQ2LinearExactSequenceSplit

#print axioms CycleQ2LinearExactSequenceSplit.exists_split
#print axioms CycleQ2LinearExactSequenceSplit.exists_matrix_split
end
end


/- Component: continuation_3/LinearKernelProjection.lean -/
section
/-! # A projection from a kernel with a compensating family

If every value of a linear map can be produced using directions killed by a
parameter projection, every parameter direction lifts to its kernel. This is
pure linear algebra; it makes no assertion about nonlinear integration.
-/

noncomputable section

namespace CycleQ2LinearKernelProjection

variable {K U V W T : Type*} [Ring K]
  [AddCommGroup U] [Module K U]
  [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]
  [AddCommGroup T] [Module K T]

theorem exists_kernel_correction
    (f : V →ₗ[K] W) (i : U →ₗ[K] V) (p : V →ₗ[K] T)
    (hip : p.comp i=0)
    (hrange : LinearMap.range f≤LinearMap.range (f.comp i)) (v : V) :
    ∃u : U, f (v-i u)=0 ∧ p (v-i u)=p v := by
  obtain ⟨u,hu⟩ := hrange (LinearMap.mem_range_self f v)
  refine ⟨u,?_,?_⟩
  · change f (i u)=f v at hu
    rw [map_sub,hu,sub_self]
  · have hpu : p (i u)=0 := congrArg (fun q : U →ₗ[K] T => q u) hip
    rw [map_sub,hpu,sub_zero]

theorem kernel_projection_surjective
    (f : V →ₗ[K] W) (i : U →ₗ[K] V) (p : V →ₗ[K] T)
    (hip : p.comp i=0)
    (hrange : LinearMap.range f≤LinearMap.range (f.comp i))
    (hp : Function.Surjective p) :
    Function.Surjective (p.comp (LinearMap.ker f).subtype) := by
  intro t
  obtain ⟨v,hv⟩ := hp t
  obtain ⟨u,hu,hup⟩ := exists_kernel_correction f i p hip hrange v
  exact ⟨⟨v-i u,hu⟩,hup.trans hv⟩

end CycleQ2LinearKernelProjection

#print axioms CycleQ2LinearKernelProjection.kernel_projection_surjective
end
end


/- Component: continuation_3/LinearKernelTrace.lean -/
section
/-! A strict rank increase after adjoining a scalar row is equivalent to a
kernel direction with nonzero scalar value. Over a field that direction can
be normalized to any prescribed value. Both directions use finite-dimensional
linear algebra and require no chosen matrix minor or explicit kernel vector.
-/

noncomputable section
set_option maxHeartbeats 300000

namespace CycleQ2LinearKernelTrace

variable {K V W U : Type*} [Field K]
  [AddCommGroup V] [Module K V] [Module.Finite K V]
  [AddCommGroup W] [Module K W] [AddCommGroup U] [Module K U]

theorem rank_le_of_kernel_le (f : V →ₗ[K] W) (g : V →ₗ[K] U)
    (hker : LinearMap.ker f≤LinearMap.ker g) :
    Module.finrank K (LinearMap.range g)≤Module.finrank K (LinearMap.range f) := by
  have hk := Submodule.finrank_mono hker
  have hf := f.finrank_range_add_finrank_ker
  have hg := g.finrank_range_add_finrank_ker
  omega

theorem exists_kernel_trace_one_of_rank_lt (f : V →ₗ[K] W) (ℓ : V →ₗ[K] K)
    (hrank : Module.finrank K (LinearMap.range f)<
      Module.finrank K (LinearMap.range (f.prod ℓ))) :
    ∃ v : V, f v=0 ∧ ℓ v=1 := by
  classical
  have hex : ∃ v : V, f v=0 ∧ ℓ v≠0 := by
    by_contra hn
    push_neg at hn
    have hk : LinearMap.ker f≤LinearMap.ker (f.prod ℓ) := by
      intro v hv
      change f v=0 at hv
      change (f v,ℓ v)=(0,0)
      exact Prod.ext hv (hn v hv)
    exact not_lt_of_ge (rank_le_of_kernel_le f (f.prod ℓ) hk) hrank
  obtain ⟨v,hv,hℓ⟩ := hex
  refine ⟨(ℓ v)⁻¹ • v,?_,?_⟩
  · simp only [map_smul,hv,smul_zero]
  · simp only [map_smul,smul_eq_mul,inv_mul_cancel₀ hℓ]

theorem rank_add_one_le_of_kernel_trace_one (f : V →ₗ[K] W) (ℓ : V →ₗ[K] K)
    (hex : ∃ v : V, f v=0 ∧ ℓ v=1) :
    Module.finrank K (LinearMap.range f)+1≤
      Module.finrank K (LinearMap.range (f.prod ℓ)) := by
  obtain ⟨v,hv,hℓ⟩ := hex
  have hle : LinearMap.ker (f.prod ℓ)≤LinearMap.ker f := by
    intro w hw
    change (f.prod ℓ) w=0 at hw
    change f w=0
    exact congrArg Prod.fst hw
  have hn : ¬LinearMap.ker f≤LinearMap.ker (f.prod ℓ) := by
    intro hk
    have hz := hk (show v∈LinearMap.ker f from hv)
    change (f.prod ℓ) v=0 at hz
    have hzero : ℓ v=0 := congrArg Prod.snd hz
    exact one_ne_zero (hℓ.symm.trans hzero)
  have hd := Submodule.finrank_lt_finrank_of_lt (lt_of_le_not_ge hle hn)
  have hf := f.finrank_range_add_finrank_ker
  have hg := (f.prod ℓ).finrank_range_add_finrank_ker
  omega

theorem exists_kernel_trace_value_of_rank_lt (f : V →ₗ[K] W) (ℓ : V →ₗ[K] K)
    (hrank : Module.finrank K (LinearMap.range f)<
      Module.finrank K (LinearMap.range (f.prod ℓ))) (a : K) :
    ∃ v : V, f v=0 ∧ ℓ v=a := by
  obtain ⟨v,hv,hℓ⟩ := exists_kernel_trace_one_of_rank_lt f ℓ hrank
  refine ⟨a • v,?_,?_⟩
  · simp only [map_smul,hv,smul_zero]
  · simp only [map_smul,hℓ,smul_eq_mul,mul_one]

end CycleQ2LinearKernelTrace

#print axioms CycleQ2LinearKernelTrace.exists_kernel_trace_one_of_rank_lt
#print axioms CycleQ2LinearKernelTrace.rank_add_one_le_of_kernel_trace_one
end
end


/- Component: continuation_3/cylinder_bridge/LinearRangeDescent.lean -/
section
/-! # Linear descent to the actual range

A linear map that kills the kernel of another map descends to that map's
actual range. The generic construction keeps the quotient universal
property separate from the concrete localized coefficient rings.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2LinearRangeDescent

variable {R M N P : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup P] [Module R P]

def descendRange (f : M →ₗ[R] N) (g : M →ₗ[R] P)
    (h : LinearMap.ker f ≤ LinearMap.ker g) : LinearMap.range f →ₗ[R] P :=
  ((LinearMap.ker f).liftQ g h).comp f.quotKerEquivRange.symm.toLinearMap

theorem descendRange_apply_image (f : M →ₗ[R] N) (g : M →ₗ[R] P)
    (h : LinearMap.ker f ≤ LinearMap.ker g) (x : M) :
    descendRange f g h ⟨f x,⟨x,rfl⟩⟩=g x := by
  unfold descendRange
  rw [LinearMap.comp_apply,LinearEquiv.coe_coe,
    LinearMap.quotKerEquivRange_symm_apply_image]
  rfl

def kernelQuotientInjection (g : M →ₗ[R] P) (K : Submodule R M)
    (h : LinearMap.ker g=K) : (M ⧸ K) →ₗ[R] P :=
  K.liftQ g (le_of_eq h.symm)

theorem kernelQuotientInjection_injective (g : M →ₗ[R] P) (K : Submodule R M)
    (h : LinearMap.ker g=K) : Function.Injective (kernelQuotientInjection g K h) := by
  apply LinearMap.ker_eq_bot.mp
  exact Submodule.ker_liftQ_eq_bot' K g h.symm

end CycleQ2LinearRangeDescent

#print axioms CycleQ2LinearRangeDescent.descendRange_apply_image
#print axioms CycleQ2LinearRangeDescent.kernelQuotientInjection_injective
end
end


/- Component: continuation_3/LinkageIdealPrincipal.lean -/
section
/-!
# Local principality from a regular linkage pairing

If I*J is contained in (p), p is regular, and a selected pairing a*b is
p times a unit, the selected sections generate I and J. The argument
works in arbitrary commutative rings, including reducible seed rings.
-/

noncomputable section
set_option maxHeartbeats 1000000

namespace CycleQ2LinkageIdealPrincipal

variable {R : Type*} [CommRing R]

theorem factors_regular (p a b u : R)
    (hp : Function.Injective (fun x : R => p*x)) (hu : IsUnit u)
    (hab : a*b=p*u) :
    Function.Injective (fun x : R => a*x) ∧
      Function.Injective (fun x : R => b*x) := by
  constructor
  · intro x y h
    apply hu.mul_right_injective
    apply hp
    calc
      p*(u*x) = b*(a*x) := by rw [← mul_assoc, ← hab]; ring
      _ = b*(a*y) := congrArg (b*·) h
      _ = p*(u*y) := by linear_combination y * hab
  · intro x y h
    apply hu.mul_right_injective
    apply hp
    calc
      p*(u*x) = a*(b*x) := by rw [← mul_assoc, ← hab]; ring
      _ = a*(b*y) := congrArg (a*·) h
      _ = p*(u*y) := by linear_combination y * hab

theorem ideal_eq_selected (I J : Ideal R) (p a b u : R)
    (hp : Function.Injective (fun x : R => p*x)) (hu : IsUnit u)
    (ha : a∈I) (hb : b∈J) (hab : a*b=p*u)
    (hpair : ∀ x∈I, ∀ y∈J, p ∣ x*y) : I=Ideal.span {a} := by
  rcases hu with ⟨v,rfl⟩
  have hbinj := (factors_regular p a b (v:R) hp v.isUnit hab).2
  apply le_antisymm
  · intro x hx
    obtain ⟨q,hq⟩ := hpair x hx b hb
    apply Ideal.mem_span_singleton.mpr
    refine ⟨(↑(v⁻¹):R)*q, ?_⟩
    apply hbinj
    calc
      b*x = p*q := by simpa only [mul_comm] using hq
      _ = b*(a*((↑(v⁻¹):R)*q)) := by
        calc
          p*q = (p*(v:R))*(↑(v⁻¹):R)*q := by simp [mul_assoc]
          _ = b*(a*((↑(v⁻¹):R)*q)) := by rw [← hab]; ring
  · exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr ha)

/-- Both actual factor ideals become principal on every chart where
one selected product has unit quotient by the linkage element. -/
theorem ideals_principal (I J : Ideal R) (p a b u : R)
    (hp : Function.Injective (fun x : R => p*x)) (hu : IsUnit u)
    (ha : a∈I) (hb : b∈J) (hab : a*b=p*u)
    (hpair : ∀ x∈I, ∀ y∈J, p ∣ x*y) :
    I=Ideal.span {a} ∧ J=Ideal.span {b} := by
  refine ⟨ideal_eq_selected I J p a b u hp hu ha hb hab hpair, ?_⟩
  apply ideal_eq_selected J I p b a u hp hu hb ha (by simpa [mul_comm] using hab)
  intro y hy x hx
  simpa only [mul_comm] using hpair x hx y hy

/-- Regularity survives every localization, without requiring that the
localization map itself be injective. -/
theorem localization_mul_injective (M : Submonoid R) (S : Type*)
    [CommRing S] [Algebra R S] [IsLocalization M S]
    (p : R) (hp : Function.Injective (fun x : R => p*x)) :
    Function.Injective (fun x : S => algebraMap R S p*x) := by
  have hpn : p ∈ nonZeroDivisors R := by
    apply mem_nonZeroDivisors_iff_left.mpr
    intro x hx
    apply hp
    simpa only [mul_zero] using hx
  have hsn : algebraMap R S p ∈ nonZeroDivisors S :=
    IsLocalization.nonZeroDivisors_le_comap M S hpn
  intro x y h
  change algebraMap R S p*x=algebraMap R S p*y at h
  apply sub_eq_zero.mp
  apply (mem_nonZeroDivisors_iff_left.mp hsn)
  rw [mul_sub, h, sub_self]

end CycleQ2LinkageIdealPrincipal

#print axioms CycleQ2LinkageIdealPrincipal.ideals_principal
#print axioms CycleQ2LinkageIdealPrincipal.localization_mul_injective
end
end


