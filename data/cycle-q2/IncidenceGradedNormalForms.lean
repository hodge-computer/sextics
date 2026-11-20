import Proposal.GeometricNormalizedCartierClass
import Mathlib.Data.Finsupp.MonomialOrder.DegLex
import Mathlib.RingTheory.MvPolynomial.Groebner
import Mathlib.Tactic

/-! # Graded normal forms and dimension counts for the incidence quotient -/

set_option Elab.async false

/- Component: continuation_3/HomogeneousComponentProduct.lean -/
section
/-!
# Homogeneous projection of ideal-membership coefficients

An arbitrary polynomial coefficient multiplying a homogeneous equation can
be projected to the unique degree contributing to a prescribed homogeneous
component.  This is used to turn polynomial ideal-membership witnesses into
homogeneous Čech cochains, including witnesses of unbounded degree.
-/

namespace CycleQ2HomogeneousComponent

open MvPolynomial

variable {σ R : Type*} [CommSemiring R]

theorem component_mul_of_homogeneous (p q : MvPolynomial σ R)
    {d e : ℕ} (hq : q.IsHomogeneous e) (hed : e ≤ d) :
    homogeneousComponent d (p * q) = homogeneousComponent (d - e) p * q := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial a c =>
    have hm : (monomial a c : MvPolynomial σ R).IsHomogeneous a.degree :=
      isHomogeneous_monomial c rfl
    rw [homogeneousComponent_of_mem (hm.mul hq), homogeneousComponent_of_mem hm]
    by_cases h : d = a.degree + e
    · have h' : d - e = a.degree := by omega
      simp [h, h']
    · have h' : d - e ≠ a.degree := by omega
      simp [h, h']
  | add p s hp hs =>
    simp only [add_mul, map_add, hp, hs]

theorem component_mul_of_homogeneous_left (p q : MvPolynomial σ R)
    {d e : ℕ} (hp : p.IsHomogeneous e) (hed : e ≤ d) :
    homogeneousComponent d (p * q) = p * homogeneousComponent (d - e) q := by
  rw [mul_comm p q, component_mul_of_homogeneous q p hp hed, mul_comm]

theorem component_mul_add (p q : MvPolynomial σ R)
    (d : ℕ) {e : ℕ} (hq : q.IsHomogeneous e) :
    homogeneousComponent (d + e) (p * q) = homogeneousComponent d p * q := by
  simpa using component_mul_of_homogeneous p q hq (Nat.le_add_left e d)

end CycleQ2HomogeneousComponent

#print axioms CycleQ2HomogeneousComponent.component_mul_of_homogeneous
end

/- Component: continuation_3/IncidenceMonomialCounts.lean -/
section
/-!
# Exact monomial counts for the invariant incidence quotient

The small finite index determines the x3 exponent from the weighted degree.
Its equivalence with the complete exponent set proves exhaustiveness; the
cardinality calculations use the ordinary kernel decision procedure.
-/

namespace CycleQ2IncidenceMonomials


def coordinates {d xBound wBound : ℕ} (q : Index d xBound wBound) : Fin 5 → ℕ :=
  ![q.val.1.1.val, q.val.2.1.val, q.val.2.2.val,
    d - (q.val.1.1.val + q.val.2.1.val + q.val.2.2.val + 2 * q.val.1.2.val),
    q.val.1.2.val]

abbrev Exponents (d xBound wBound : ℕ) :=
  {e : Fin 5 → ℕ // e 0 < xBound ∧ e 4 < wBound ∧
    e 0 + e 1 + e 2 + e 3 + 2 * e 4 = d ∧
    (2 * e 0 + 2 * e 1 + e 2) % 3 = 0}

def exponentEquiv (d xBound wBound : ℕ) :
    Index d xBound wBound ≃ Exponents d xBound wBound where
  toFun q := ⟨coordinates q, by
    have hw := q.property.1
    have hc := q.property.2
    change q.val.1.1.val < xBound ∧ q.val.1.2.val < wBound ∧
      q.val.1.1.val + q.val.2.1.val + q.val.2.2.val +
        (d - (q.val.1.1.val + q.val.2.1.val + q.val.2.2.val + 2 * q.val.1.2.val)) +
        2 * q.val.1.2.val = d ∧
      (2 * q.val.1.1.val + 2 * q.val.2.1.val + q.val.2.2.val) % 3 = 0
    exact ⟨q.val.1.1.isLt, q.val.1.2.isLt, by omega, hc⟩⟩
  invFun e := ⟨((⟨e.val 0, e.property.1⟩, ⟨e.val 4, e.property.2.1⟩),
    (⟨e.val 1, by have := e.property.2.2.1; omega⟩,
     ⟨e.val 2, by have := e.property.2.2.1; omega⟩)), by
      constructor
      · have := e.property.2.2.1
        dsimp
        omega
      · exact e.property.2.2.2⟩
  left_inv q := by
    apply Subtype.ext
    rfl
  right_inv e := by
    apply Subtype.ext
    funext i
    fin_cases i
    · rfl
    · rfl
    · rfl
    · change d - (e.val 0 + e.val 1 + e.val 2 + 2 * e.val 4) = e.val 3
      have := e.property.2.2.1
      omega
    · rfl

abbrev FullIndex (d : ℕ) := Index d (d + 1) (d / 2 + 1)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem invariant_cubic_count : Fintype.card (FullIndex 3) = 9 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem invariant_sextic_count : Fintype.card (FullIndex 6) = 45 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem standard_degree14_count : Fintype.card (StandardIndex 14) = 239 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem standard_degree28_count : Fintype.card (StandardIndex 28) = 1058 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem standard_degree42_count : Fintype.card (StandardIndex 42) = 2465 := by decide

/-- There are nine degree-fourteen matrix entries and nine raw cubic-section
coefficients. The scalar direction of the cubic remains present. -/
theorem incidence_variable_count :
    9 * Fintype.card (StandardIndex 14) + Fintype.card (FullIndex 3) = 2160 := by
  rw [standard_degree14_count, invariant_cubic_count]

theorem cofactor_equation_count : 9 * Fintype.card (StandardIndex 28) = 9522 := by
  rw [standard_degree28_count]

theorem coefficient_relation_count : 16 * Fintype.card (StandardIndex 42) = 39440 := by
  rw [standard_degree42_count]

end CycleQ2IncidenceMonomials

#print axioms CycleQ2IncidenceMonomials.exponentEquiv
#print axioms CycleQ2IncidenceMonomials.invariant_sextic_count
#print axioms CycleQ2IncidenceMonomials.standard_degree42_count
end

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

/- Component: continuation_3/WeightedComponentProduct.lean -/
section
/-! # Homogeneous projection for the actual degree-and-character grading -/

namespace CycleQ2WeightedComponent

open MvPolynomial

variable {σ R M : Type*} [CommSemiring R] [AddCancelCommMonoid M]

theorem component_mul (w : σ → M) (p q : MvPolynomial σ R)
    (d e : M) (hq : q.IsWeightedHomogeneous w e) :
    weightedHomogeneousComponent w (d+e) (p*q) =
      weightedHomogeneousComponent w d p*q := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial a c =>
    have hm : (monomial a c : MvPolynomial σ R).IsWeightedHomogeneous w (Finsupp.weight w a) :=
      isWeightedHomogeneous_monomial w a c rfl
    rw [weightedHomogeneousComponent_of_mem (hm.mul hq),
      weightedHomogeneousComponent_of_mem hm]
    simp only [add_left_inj]
    split_ifs <;> simp_all
  | add p s hp hs =>
    simp only [add_mul, map_add, hp, hs]

theorem component_mul_left (w : σ → M) (p q : MvPolynomial σ R)
    (d e : M) (hp : p.IsWeightedHomogeneous w d) :
    weightedHomogeneousComponent w (d+e) (p*q) =
      p*weightedHomogeneousComponent w e q := by
  rw [mul_comm p q, add_comm d e, component_mul w q p e d hp, mul_comm]

end CycleQ2WeightedComponent

#print axioms CycleQ2WeightedComponent.component_mul
#print axioms CycleQ2WeightedComponent.component_mul_left
end

/- Component: continuation_3/IncidenceFullIndexCounts.lean -/
section
/-! The literal cubic and sextic coefficient indices have the cardinalities
already proved for the efficient exhaustive monomial enumeration. -/

namespace CycleQ2IncidenceFullIndexCounts

open CycleQ2IncidenceNormalForm CycleQ2IncidenceMonomials

def fullExponentEquiv (d : ℕ) :
    FullInvariantIndex d ≃ Exponents d (d+1) (d/2+1) where
  toFun e := ⟨fun i => (e.val i).val,by
    have hd := e.property.1
    change (e.val 0).val+(e.val 1).val+(e.val 2).val+(e.val 3).val+
      2*(e.val 4).val=d at hd
    refine ⟨(e.val 0).isLt,?_,hd,e.property.2⟩
    change (e.val 4).val<d/2+1
    omega⟩
  invFun e := ⟨fun i => ⟨e.val i,by
    have hd := e.property.2.2.1
    fin_cases i
    · change e.val 0<d+1
      omega
    · change e.val 1<d+1
      omega
    · change e.val 2<d+1
      omega
    · change e.val 3<d+1
      omega
    · change e.val 4<d+1
      omega⟩,e.property.2.2.1,e.property.2.2.2⟩
  left_inv e := by
    apply Subtype.ext
    funext i
    apply Fin.ext
    rfl
  right_inv e := by
    apply Subtype.ext
    rfl

def fullIndexEquiv (d : ℕ) : FullInvariantIndex d ≃ FullIndex d :=
  (fullExponentEquiv d).trans (exponentEquiv d (d+1) (d/2+1)).symm

theorem cubic_count : Fintype.card (FullInvariantIndex 3)=9 :=
  (Fintype.card_congr (fullIndexEquiv 3)).trans invariant_cubic_count

theorem sextic_count : Fintype.card (FullInvariantIndex 6)=45 :=
  (Fintype.card_congr (fullIndexEquiv 6)).trans invariant_sextic_count

end CycleQ2IncidenceFullIndexCounts

#print axioms CycleQ2IncidenceFullIndexCounts.sextic_count
end

/- Component: continuation_3/IncidenceGradedBasis.lean -/
section
/-!
# The actual graded quotient basis in the incidence chart

The homogeneous piece is the image of the genuine weighted-homogeneous
polynomial submodule under the quotient map. Its basis is constructed using
the proved reduction theorem, with no dimension or flatness hypothesis.
-/

noncomputable section

namespace CycleQ2IncidenceGradedBasis

open MvPolynomial CycleQ2IncidenceNormalForm

variable {σ R M : Type*} [CommRing R] [AddCommMonoid M]

def gradedExponents (w : σ → M) (m : MonomialOrder σ)
    (h F : MvPolynomial σ R) (d : M) : Set (σ →₀ ℕ) :=
  {e | e ∈ reducedExponents m h F ∧ Finsupp.weight w e = d}

def gradedReduced (w : σ → M) (m : MonomialOrder σ)
    (h F : MvPolynomial σ R) (d : M) : Submodule R (MvPolynomial σ R) :=
  restrictSupport R (gradedExponents w m h F d)

theorem mem_gradedReduced (w : σ → M) (m : MonomialOrder σ)
    (h F p : MvPolynomial σ R) (d : M) :
    p ∈ gradedReduced w m h F d ↔ Reduced m h F p ∧ p.IsWeightedHomogeneous w d := by
  constructor
  · intro hp
    constructor
    · intro e he
      exact (hp he).1
    · intro e he
      exact (hp (mem_support_iff.mpr he)).2
  · rintro ⟨hr, hh⟩ e he
    exact ⟨hr e he, hh (mem_support_iff.mp he)⟩

/-- The genuine degree-d piece of the quotient; its definition does not
mention a proposed basis or a normal form. -/
def quotientPiece (w : σ → M) (h F : MvPolynomial σ R) (d : M) :
    Submodule R (MvPolynomial σ R ⧸ equationsIdeal h F) :=
  (weightedHomogeneousSubmodule R w d).map
    (Ideal.Quotient.mkₐ R (equationsIdeal h F)).toLinearMap

def gradedQuotientMap (w : σ → M) (m : MonomialOrder σ)
    (h F : MvPolynomial σ R) (d : M) :
    gradedReduced w m h F d →ₗ[R] quotientPiece w h F d :=
  (((Ideal.Quotient.mkₐ R (equationsIdeal h F)).toLinearMap.comp
    (gradedReduced w m h F d).subtype).codRestrict (quotientPiece w h F d)
      (fun p => Submodule.mem_map.mpr
        ⟨p.val, ((mem_gradedReduced w m h F p.val d).mp p.property).2, rfl⟩))

theorem gradedQuotientMap_bijective
    (w : σ → M) (m : MonomialOrder σ) (h F : MvPolynomial σ R) (d : M)
    (hh : m.Monic h) (hF : m.Monic F)
    (hcop : ∀ i, m.degree h i = 0 ∨ m.degree F i = 0)
    {dh dF : M} (hhhom : h.IsWeightedHomogeneous w dh)
    (hFhom : F.IsWeightedHomogeneous w dF) :
    Function.Bijective (gradedQuotientMap w m h F d) := by
  constructor
  · intro p q hpq
    apply Subtype.ext
    have hpq' := congrArg Subtype.val hpq
    change Ideal.Quotient.mk (equationsIdeal h F) p.val =
      Ideal.Quotient.mk (equationsIdeal h F) q.val at hpq'
    obtain ⟨a, b, heq⟩ := Ideal.mem_span_pair.mp (Ideal.Quotient.eq.mp hpq')
    apply sub_eq_zero.mp
    exact reduced_eq_zero_of_representation m hh hF hcop
      (reduced_sub m
        ((mem_gradedReduced w m h F p.val d).mp p.property).1
        ((mem_gradedReduced w m h F q.val d).mp q.property).1) heq.symm
  · intro q
    obtain ⟨p, hp, hpq⟩ := Submodule.mem_map.mp q.property
    obtain ⟨a, b, r, hrep, hr⟩ := exists_reduced_representation m h F p hh hF
    have hrhom : r.IsWeightedHomogeneous w d :=
      reduced_isWeightedHomogeneous w m hh hF hcop hhhom hFhom hp hr hrep
    refine ⟨⟨r, (mem_gradedReduced w m h F r d).mpr ⟨hr, hrhom⟩⟩, ?_⟩
    apply Subtype.ext
    change Ideal.Quotient.mk (equationsIdeal h F) r = q.val
    calc
      _ = Ideal.Quotient.mk (equationsIdeal h F) p := by
        apply Ideal.Quotient.eq.mpr
        apply Ideal.mem_span_pair.mpr
        refine ⟨-a, -b, ?_⟩
        rw [hrep]
        ring
      _ = q.val := hpq

def gradedQuotientEquiv
    (w : σ → M) (m : MonomialOrder σ) (h F : MvPolynomial σ R) (d : M)
    (hh : m.Monic h) (hF : m.Monic F)
    (hcop : ∀ i, m.degree h i = 0 ∨ m.degree F i = 0)
    {dh dF : M} (hhhom : h.IsWeightedHomogeneous w dh)
    (hFhom : F.IsWeightedHomogeneous w dF) :
    gradedReduced w m h F d ≃ₗ[R] quotientPiece w h F d :=
  LinearEquiv.ofBijective (gradedQuotientMap w m h F d)
    (gradedQuotientMap_bijective w m h F d hh hF hcop hhhom hFhom)

def basis
    (w : σ → M) (m : MonomialOrder σ) (h F : MvPolynomial σ R) (d : M)
    (hh : m.Monic h) (hF : m.Monic F)
    (hcop : ∀ i, m.degree h i = 0 ∨ m.degree F i = 0)
    {dh dF : M} (hhhom : h.IsWeightedHomogeneous w dh)
    (hFhom : F.IsWeightedHomogeneous w dF) :
    Module.Basis (gradedExponents w m h F d) R (quotientPiece w h F d) :=
  (MvPolynomial.basisRestrictSupport R (gradedExponents w m h F d)).map
    (gradedQuotientEquiv w m h F d hh hF hcop hhhom hFhom)

theorem basis_apply
    (w : σ → M) (m : MonomialOrder σ) (h F : MvPolynomial σ R) (d : M)
    (hh : m.Monic h) (hF : m.Monic F)
    (hcop : ∀ i, m.degree h i = 0 ∨ m.degree F i = 0)
    {dh dF : M} (hhhom : h.IsWeightedHomogeneous w dh)
    (hFhom : F.IsWeightedHomogeneous w dF)
    (e : gradedExponents w m h F d) :
    (basis w m h F d hh hF hcop hhhom hFhom e :
        MvPolynomial σ R ⧸ equationsIdeal h F) =
      Ideal.Quotient.mk (equationsIdeal h F) (monomial e.val 1) := by
  change Ideal.Quotient.mk (equationsIdeal h F)
    (AddMonoidAlgebra.ofCoeff
      (((Finsupp.supportedEquivFinsupp (R := R) (gradedExponents w m h F d)).symm
        (Finsupp.single e 1) : Finsupp.supported R R (gradedExponents w m h F d)) :
        (σ →₀ ℕ) →₀ R)) = _
  rw [Finsupp.supportedEquivFinsupp_symm_single]
  rfl

section FullIncidence

variable [Nontrivial R]

/-- Identifies every standard invariant exponent, rather than only a displayed
list of monomials, with the finite index used by the checked counts. -/
def fullExponentEquiv (d : ℕ)
    (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R) :
    gradedExponents fullGrading fullAuxiliaryOrder
      (normalizedFullCubic hcoeff) (normalizedFullSextic Fcoeff) (d, 0) ≃
      CycleQ2IncidenceMonomials.Exponents d 3 3 where
  toFun e := ⟨e.val, by
    have hb := e.property.1
    change (¬ fullAuxiliaryOrder.degree (normalizedFullCubic hcoeff) ≤ e.val) ∧
      (¬ fullAuxiliaryOrder.degree (normalizedFullSextic Fcoeff) ≤ e.val) at hb
    rw [(normalizedFullCubic_leading_data hcoeff).1,
      (normalizedFullSextic_leading_data Fcoeff).1,
      single_three_le_iff, single_three_le_iff] at hb
    have hg := e.property.2
    rw [fullGrading_weight] at hg
    have hd := congrArg Prod.fst hg
    have hc := congrArg Prod.snd hg
    refine ⟨Nat.lt_of_not_ge hb.1, Nat.lt_of_not_ge hb.2, hd, ?_⟩
    exact Nat.mod_eq_zero_of_dvd ((ZMod.natCast_eq_zero_iff _ _).mp hc)⟩
  invFun e := ⟨Finsupp.equivFunOnFinite.symm e.val, by
    constructor
    · change (¬ fullAuxiliaryOrder.degree (normalizedFullCubic hcoeff) ≤
          Finsupp.equivFunOnFinite.symm e.val) ∧
        (¬ fullAuxiliaryOrder.degree (normalizedFullSextic Fcoeff) ≤
          Finsupp.equivFunOnFinite.symm e.val)
      rw [(normalizedFullCubic_leading_data hcoeff).1,
        (normalizedFullSextic_leading_data Fcoeff).1,
        single_three_le_iff, single_three_le_iff]
      exact ⟨Nat.not_le_of_lt e.property.1, Nat.not_le_of_lt e.property.2.1⟩
    · rw [fullGrading_weight]
      apply Prod.ext
      · exact e.property.2.2.1
      · apply (ZMod.natCast_eq_zero_iff _ _).mpr
        exact Nat.dvd_of_mod_eq_zero e.property.2.2.2⟩
  left_inv e := by
    apply Subtype.ext
    exact Finsupp.equivFunOnFinite.symm_apply_apply e.val
  right_inv e := by
    apply Subtype.ext
    rfl

/-- Basis of the actual invariant weighted-degree piece of the full incidence
quotient. Its index is the completely enumerated standard monomial set. -/
def fullBasis (d : ℕ)
    (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R) :
    Module.Basis (CycleQ2IncidenceMonomials.StandardIndex d) R
      (quotientPiece fullGrading (normalizedFullCubic hcoeff)
        (normalizedFullSextic Fcoeff) (d, 0)) :=
  (basis fullGrading fullAuxiliaryOrder
    (normalizedFullCubic hcoeff) (normalizedFullSextic Fcoeff) (d, 0)
    (normalizedFullCubic_leading_data hcoeff).2 (normalizedFullSextic_leading_data Fcoeff).2
    (full_coprime hcoeff Fcoeff) (normalizedFullCubic_homogeneous hcoeff)
    (normalizedFullSextic_homogeneous Fcoeff)).reindex
      ((fullExponentEquiv d hcoeff Fcoeff).trans
        (CycleQ2IncidenceMonomials.exponentEquiv d 3 3).symm)

theorem fullBasis_apply (d : ℕ)
    (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R)
    (e : CycleQ2IncidenceMonomials.StandardIndex d) :
    (fullBasis d hcoeff Fcoeff e : MvPolynomial (Fin 5) R ⧸
        equationsIdeal (normalizedFullCubic hcoeff) (normalizedFullSextic Fcoeff)) =
      Ideal.Quotient.mk (equationsIdeal (normalizedFullCubic hcoeff)
        (normalizedFullSextic Fcoeff))
        (monomial (Finsupp.equivFunOnFinite.symm
          (CycleQ2IncidenceMonomials.coordinates e)) 1) := by
  rw [fullBasis, Module.Basis.reindex_apply, basis_apply]
  rfl

theorem fullPiece_finrank [StrongRankCondition R] (d : ℕ)
    (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R) :
    Module.finrank R (quotientPiece fullGrading (normalizedFullCubic hcoeff)
      (normalizedFullSextic Fcoeff) (d, 0)) =
        Fintype.card (CycleQ2IncidenceMonomials.StandardIndex d) :=
  Module.finrank_eq_card_basis (fullBasis d hcoeff Fcoeff)

theorem fullPiece_degree14_finrank [StrongRankCondition R]
    (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R) :
    Module.finrank R (quotientPiece fullGrading (normalizedFullCubic hcoeff)
      (normalizedFullSextic Fcoeff) (14, 0)) = 239 := by
  rw [fullPiece_finrank, CycleQ2IncidenceMonomials.standard_degree14_count]

theorem fullPiece_degree28_finrank [StrongRankCondition R]
    (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R) :
    Module.finrank R (quotientPiece fullGrading (normalizedFullCubic hcoeff)
      (normalizedFullSextic Fcoeff) (28, 0)) = 1058 := by
  rw [fullPiece_finrank, CycleQ2IncidenceMonomials.standard_degree28_count]

theorem fullPiece_degree42_finrank [StrongRankCondition R]
    (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R) :
    Module.finrank R (quotientPiece fullGrading (normalizedFullCubic hcoeff)
      (normalizedFullSextic Fcoeff) (42, 0)) = 2465 := by
  rw [fullPiece_finrank, CycleQ2IncidenceMonomials.standard_degree42_count]

end FullIncidence

end CycleQ2IncidenceGradedBasis

#print axioms CycleQ2IncidenceGradedBasis.gradedQuotientMap_bijective
#print axioms CycleQ2IncidenceGradedBasis.basis_apply
#print axioms CycleQ2IncidenceGradedBasis.fullBasis_apply
#print axioms CycleQ2IncidenceGradedBasis.fullPiece_degree42_finrank
end
end
