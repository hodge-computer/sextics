import Proposal.GeometricSeedNormalIdeals
import Mathlib.RingTheory.MvPolynomial.Groebner
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Tactic.LinearCombination

/-!
# Existing equation-class bases of the actual seed conormal modules

This module extracts the previously supplied polynomial division,
regular-sequence, and conormal-basis proofs, preserving their namespaces,
statements, definitions, and proof bodies.  The literal equations have
pairwise coprime monic leading terms, so their conormal equation classes
form bases on every actual curve algebra, including both localization
charts and their overlap.  No Jacobian or basis hypothesis is introduced.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
open MvPolynomial
open scoped BigOperators TensorProduct MonomialOrder

namespace CycleQ2IncidenceNormalForm
variable {σ R : Type*} [CommRing R]

/-- No monomial of `p` is divisible by either distinguished leading monomial. -/
def Reduced (m : MonomialOrder σ) (h F p : MvPolynomial σ R) : Prop :=
  ∀ d ∈ p.support, ¬ m.degree h ≤ d ∧ ¬ m.degree F ≤ d

lemma degree_mul_monic (m : MonomialOrder σ) {p q : MvPolynomial σ R}
    (hp : p ≠ 0) (hq : m.Monic q) :
    m.degree (p * q) = m.degree p + m.degree q := by
  apply m.degree_mul_of_mul_leadingCoeff_ne_zero
  simpa [hq.leadingCoeff_eq_one] using m.leadingCoeff_ne_zero_iff.mpr hp

/-- Existence of a reduced representative uses the library's ordinary
multivariate division theorem. -/
theorem exists_reduced_representation
    (m : MonomialOrder σ) (h F p : MvPolynomial σ R)
    (hh : m.Monic h) (hF : m.Monic F) :
    ∃ a b r, p = a * h + b * F + r ∧ Reduced m h F r := by
  let equations : Fin 2 → MvPolynomial σ R := ![h, F]
  have he : ∀ i, IsUnit (m.leadingCoeff (equations i)) := by
    intro i
    fin_cases i
    · change IsUnit (m.leadingCoeff h)
      rw [hh.leadingCoeff_eq_one]
      exact isUnit_one
    · change IsUnit (m.leadingCoeff F)
      rw [hF.leadingCoeff_eq_one]
      exact isUnit_one
  obtain ⟨q, r, hp, _, hr⟩ := m.div he p
  refine ⟨q 0, q 1, r, ?_, ?_⟩
  · simpa [Finsupp.linearCombination_apply, Finsupp.sum_fintype, equations,
      Fin.sum_univ_two, smul_eq_mul] using hp
  · intro d hd
    exact ⟨hr d hd 0, hr d hd 1⟩

lemma degree_monic_add_sum [Nontrivial R] {ι : Type*} [Fintype ι]
    (m : MonomialOrder σ) (d : σ →₀ ℕ) (e : ι → σ →₀ ℕ) (c : ι → R)
    (hd : 0 ≺[m] d) (he : ∀ i, e i ≺[m] d) :
    m.degree (monomial d 1 + ∑ i, monomial (e i) (c i)) = d ∧
      m.Monic (monomial d 1 + ∑ i, monomial (e i) (c i)) := by
  classical
  have htail : m.degree (∑ i, monomial (e i) (c i)) ≺[m] d := by
    apply lt_of_le_of_lt m.degree_sum_le
    apply (Finset.sup_lt_iff (by simpa using hd)).mpr
    intro i _
    exact lt_of_le_of_lt (m.degree_monomial_le _) (he i)
  have hlead : m.degree (monomial d (1 : R)) = d := by
    rw [m.degree_monomial, if_neg one_ne_zero]
  have htail' : m.degree (∑ i, monomial (e i) (c i)) ≺[m]
      m.degree (monomial d (1 : R)) := by
    rwa [hlead]
  exact ⟨(m.degree_add_of_lt htail').trans hlead,
    m.monic_monomial_one.add_of_lt htail'⟩

/-- Adding an additive natural-valued weight in front of a monomial order gives
another monomial order.  The old order breaks ties, so zero weights are allowed. -/
def WeightedExponent (m : MonomialOrder σ) (W : (σ →₀ ℕ) →+ ℕ) := σ →₀ ℕ

def toWeighted (m : MonomialOrder σ) (W : (σ →₀ ℕ) →+ ℕ) :
    (σ →₀ ℕ) ≃ WeightedExponent m W := Equiv.refl _
def ofWeighted (m : MonomialOrder σ) (W : (σ →₀ ℕ) →+ ℕ) :
    WeightedExponent m W ≃ (σ →₀ ℕ) := Equiv.refl _

noncomputable instance (m : MonomialOrder σ) (W : (σ →₀ ℕ) →+ ℕ) :
    AddCommMonoid (WeightedExponent m W) := (ofWeighted m W).addCommMonoid

lemma ofWeighted_add (m : MonomialOrder σ) (W : (σ →₀ ℕ) →+ ℕ)
    (a b : WeightedExponent m W) :
    ofWeighted m W (a + b) = ofWeighted m W a + ofWeighted m W b := rfl

def weightedKey (m : MonomialOrder σ) (W : (σ →₀ ℕ) →+ ℕ)
    (a : WeightedExponent m W) : Lex (ℕ × m.syn) :=
  toLex (W (ofWeighted m W a), m.toSyn (ofWeighted m W a))

lemma weightedKey_injective (m : MonomialOrder σ) (W : (σ →₀ ℕ) →+ ℕ) :
    Function.Injective (weightedKey m W) := by
  intro a b hab
  exact (ofWeighted m W).injective (m.toSyn.injective (Prod.mk.inj (toLex.injective hab)).2)

noncomputable instance (m : MonomialOrder σ) (W : (σ →₀ ℕ) →+ ℕ) :
    LinearOrder (WeightedExponent m W) :=
  LinearOrder.lift' (weightedKey m W) (weightedKey_injective m W)

noncomputable instance (m : MonomialOrder σ) (W : (σ →₀ ℕ) →+ ℕ) :
    IsOrderedCancelAddMonoid (WeightedExponent m W) where
  le_of_add_le_add_left a b c h := by
    change weightedKey m W b ≤ weightedKey m W c
    change weightedKey m W (a + b) ≤ weightedKey m W (a + c) at h
    simpa only [weightedKey, ofWeighted_add, map_add,
      Prod.Lex.toLex_le_toLex, add_lt_add_iff_left, add_right_inj,
      add_le_add_iff_left] using h
  add_le_add_left a b h c := by
    change weightedKey m W a ≤ weightedKey m W b at h
    change weightedKey m W (a + c) ≤ weightedKey m W (b + c)
    simpa only [weightedKey, ofWeighted_add, map_add,
      Prod.Lex.toLex_le_toLex, add_lt_add_iff_right, add_left_inj,
      add_le_add_iff_right] using h

noncomputable instance (m : MonomialOrder σ) (W : (σ →₀ ℕ) →+ ℕ) :
    WellFoundedLT (WeightedExponent m W) :=
  ⟨InvImage.wf (weightedKey m W) wellFounded_lt⟩

noncomputable def weightedOrder (m : MonomialOrder σ) (W : (σ →₀ ℕ) →+ ℕ) :
    MonomialOrder σ where
  syn := WeightedExponent m W
  toSyn := { toEquiv := toWeighted m W, map_add' _ _ := rfl }
  toSyn_monotone a b hab := by
    change toLex (W a, m.toSyn a) ≤ toLex (W b, m.toSyn b)
    rw [Prod.Lex.toLex_le_toLex]
    have hw : W a ≤ W b := by
      rw [← add_tsub_cancel_of_le hab, map_add]
      exact Nat.le_add_right _ _
    rcases lt_or_eq_of_le hw with hw | hw
    · exact Or.inl hw
    · exact Or.inr ⟨hw, m.toSyn_monotone hab⟩

lemma weightedOrder_lt_of_weight_lt
    (m : MonomialOrder σ) (W : (σ →₀ ℕ) →+ ℕ) {a b : σ →₀ ℕ}
    (h : W a < W b) : a ≺[weightedOrder m W] b := by
  change toLex (W a, m.toSyn a) < toLex (W b, m.toSyn b)
  exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl h)

end CycleQ2IncidenceNormalForm

section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace CycleQ2ConormalJacobian
variable {k R S : Type*} [CommRing k] [CommRing R] [CommRing S]
  [Algebra k R] [Algebra R S] [Algebra k S] [IsScalarTower k R S]
variable (I : Ideal R) (hI : ∀ x ∈ I, algebraMap R S x = 0)
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (f : ι → R) (hf : Ideal.span (Set.range f)=I)

def generator (i : ι) : S ⊗[R] I.Cotangent :=
  1 ⊗ₜ[R] I.toCotangent ⟨f i, hf ▸ Ideal.subset_span ⟨i,rfl⟩⟩

theorem generators_span :
    Submodule.span S (Set.range (generator (S := S) I f hf))=⊤ := by
  apply top_unique
  intro z hzTop
  clear hzTop
  induction z using TensorProduct.induction_on with
  | zero => exact Submodule.zero_mem _
  | add z w hz hw => exact Submodule.add_mem _ hz hw
  | tmul s m =>
    obtain ⟨x,rfl⟩ := I.toCotangent_surjective m
    suffices hx : (1:S) ⊗ₜ[R] I.toCotangent x ∈
        Submodule.span S (Set.range (generator (S := S) I f hf)) by
      simpa only [TensorProduct.smul_tmul',smul_eq_mul,mul_one] using
        Submodule.smul_mem _ s hx
    have hgen : ∀ y (hy : y∈Ideal.span (Set.range f)),
        (1:S) ⊗ₜ[R] I.toCotangent ⟨y,hf ▸ hy⟩ ∈
          Submodule.span S (Set.range (generator (S := S) I f hf)) := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨i,rfl⟩ := hy
        exact Submodule.subset_span ⟨i,rfl⟩
      | zero =>
        change (1:S) ⊗ₜ[R] I.toCotangent (0:I) ∈ _
        rw [map_zero,TensorProduct.tmul_zero]
        exact Submodule.zero_mem _
      | add a b ha hb iha ihb =>
        change (1:S) ⊗ₜ[R] I.toCotangent
          ((⟨a,hf ▸ ha⟩ : I)+⟨b,hf ▸ hb⟩) ∈ _
        rw [map_add,TensorProduct.tmul_add]
        exact Submodule.add_mem _ iha ihb
      | smul c a ha iha =>
        change (1:S) ⊗ₜ[R] I.toCotangent (c • (⟨a,hf ▸ ha⟩ : I)) ∈ _
        rw [map_smul,TensorProduct.tmul_smul]
        simpa only [algebraMap_smul] using
          Submodule.smul_mem _ (algebraMap R S c) iha
    exact hgen x.val (hf.symm ▸ x.property)

end CycleQ2ConormalJacobian

namespace CycleQ2ConormalRegular

section Finite
variable {R S ι : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [Fintype ι] [DecidableEq ι]
variable (I : Ideal R) (f : ι → R) (hf : Ideal.span (Set.range f) = I)

include hf in
theorem coefficients_exist (x : I) : ∃ c : ι → R, ∑ i, c i * f i = (x : R) := by
  have hx : (x : R) ∈ Submodule.span R (Set.range f) := hf.symm ▸ x.property
  simpa only [smul_eq_mul] using
    (Submodule.mem_span_range_iff_exists_fun (R := R)).mp hx

def coefficients (x : I) : ι → R := Classical.choose (coefficients_exist I f hf x)

theorem coefficients_spec (x : I) : ∑ i, coefficients I f hf x i * f i = (x : R) :=
  Classical.choose_spec (coefficients_exist I f hf x)

variable (hI : ∀ x ∈ I, algebraMap R S x = 0)
variable (hrel : ∀ c : ι → R, (∑ i, c i * f i) = 0 → ∀ i, c i ∈ I)

include hI hrel in
theorem coefficient_maps_unique (c d : ι → R)
    (h : (∑ i, c i * f i) = ∑ i, d i * f i) (i : ι) :
    algebraMap R S (c i) = algebraMap R S (d i) := by
  have hz : (∑ j, (c j - d j) * f j) = 0 := by
    simp only [sub_mul, Finset.sum_sub_distrib, h, sub_self]
  have hh := hI _ (hrel (fun j => c j - d j) hz i)
  simpa only [map_sub, sub_eq_zero] using hh

/-- The chosen polynomial coefficients give a canonical linear functional
after passing to any algebra that annihilates the ideal. -/
def idealCoordinate (i : ι) : I →ₗ[R] S where
  toFun x := algebraMap R S (coefficients I f hf x i)
  map_add' x y := by
    have hh := coefficient_maps_unique I f hI hrel
      (coefficients I f hf (x+y))
      (fun j => coefficients I f hf x j + coefficients I f hf y j) (by
        simp only [add_mul, Finset.sum_add_distrib, coefficients_spec]
        rfl) i
    simpa only [map_add] using hh
  map_smul' a x := by
    have hh := coefficient_maps_unique I f hI hrel
      (coefficients I f hf (a • x))
      (fun j => a * coefficients I f hf x j) (by
        simp only [mul_assoc, ← Finset.mul_sum, coefficients_spec]
        rfl) i
    simpa only [map_mul, Algebra.smul_def, RingHom.id_apply] using hh

theorem idealCoordinate_generator (i j : ι) :
    idealCoordinate I f hf hI hrel i
      ⟨f j, hf ▸ Ideal.subset_span ⟨j,rfl⟩⟩ = if i=j then 1 else 0 := by
  have hh := coefficient_maps_unique I f hI hrel
    (coefficients I f hf ⟨f j, hf ▸ Ideal.subset_span ⟨j,rfl⟩⟩)
    (Pi.single j 1) (by simp [coefficients_spec, Pi.single_apply]) i
  simpa [idealCoordinate, Pi.single_apply, eq_comm] using hh

theorem idealCoordinate_product (i : ι) (x y : I) :
    idealCoordinate I f hf hI hrel i (x*y) = 0 := by
  change idealCoordinate I f hf hI hrel i ((x:R) • y) = 0
  rw [map_smul, Algebra.smul_def, hI _ x.property, zero_mul]

def conormalCoordinate (i : ι) : S ⊗[R] I.Cotangent →ₗ[S] S :=
  (Ideal.Cotangent.lift (idealCoordinate I f hf hI hrel i)
    (idealCoordinate_product I f hf hI hrel i)).liftBaseChange S

@[simp] theorem conormalCoordinate_generator (i j : ι) :
    conormalCoordinate I f hf hI hrel i
      (CycleQ2ConormalJacobian.generator (S := S) I f hf j) =
      if i=j then 1 else 0 := by
  simp [conormalCoordinate, CycleQ2ConormalJacobian.generator,
    idealCoordinate_generator]

include hI hrel in
theorem generators_independent : LinearIndependent S
    (CycleQ2ConormalJacobian.generator (S := S) I f hf) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have hh := congrArg (conormalCoordinate I f hf hI hrel i) hc
  simp only [map_sum, map_smul, map_zero, conormalCoordinate_generator] at hh
  simpa using hh

/-- The actual base-changed ideal cotangent module is free on the given
equation classes whenever all relations have coefficients in the ideal. -/
def conormalBasis : Module.Basis ι S (S ⊗[R] I.Cotangent) :=
  Module.Basis.mk (generators_independent I f hf hI hrel)
    (by rw [CycleQ2ConormalJacobian.generators_span I f hf])

@[simp] theorem conormalBasis_apply (i : ι) :
    conormalBasis I f hf hI hrel i =
      CycleQ2ConormalJacobian.generator (S := S) I f hf i :=
  Module.Basis.mk_apply _ _ _

end Finite

section Regular
variable {R : Type*} [CommRing R]

/-- Degree-one regular-sequence consequence for two equations. The second
hypothesis is precisely cancellation modulo the first equation. -/
theorem pair_relation_coefficients (a b : R)
    (ha : ∀ x : R, a*x=0 → x=0)
    (hb : ∀ x : R, b*x ∈ Ideal.span ({a}:Set R) → x ∈ Ideal.span ({a}:Set R))
    (u v : R) (h : a*u+b*v=0) :
    u ∈ Ideal.span ({a,b}:Set R) ∧ v ∈ Ideal.span ({a,b}:Set R) := by
  have hv : v ∈ Ideal.span ({a}:Set R) := hb v (by
    rw [Ideal.mem_span_singleton']
    exact ⟨-u, by linear_combination -h⟩)
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp hv
  have hu : u+b*t=0 := ha _ (by linear_combination h + b*ht)
  constructor
  · exact Ideal.mem_span_pair.mpr ⟨0,-t,by linear_combination -hu⟩
  · exact Ideal.mem_span_pair.mpr ⟨t,0,by simpa using ht⟩

/-- Degree-one regular-sequence consequence for three equations. -/
theorem triple_relation_coefficients (a b c : R)
    (ha : ∀ x : R, a*x=0 → x=0)
    (hb : ∀ x : R, b*x ∈ Ideal.span ({a}:Set R) → x ∈ Ideal.span ({a}:Set R))
    (hc : ∀ x : R, c*x ∈ Ideal.span ({a,b}:Set R) → x ∈ Ideal.span ({a,b}:Set R))
    (u v w : R) (h : a*u+b*v+c*w=0) :
    u ∈ Ideal.span ({a,b,c}:Set R) ∧
    v ∈ Ideal.span ({a,b,c}:Set R) ∧ w ∈ Ideal.span ({a,b,c}:Set R) := by
  have hw : w ∈ Ideal.span ({a,b}:Set R) := hc w (by
    exact Ideal.mem_span_pair.mpr ⟨-u,-v,by linear_combination -h⟩)
  obtain ⟨s,t,hst⟩ := Ideal.mem_span_pair.mp hw
  have hp : a*(u+c*s)+b*(v+c*t)=0 := by
    linear_combination h + c*hst
  obtain ⟨hu,hv⟩ := pair_relation_coefficients a b ha hb (u+c*s) (v+c*t) hp
  have hab : Ideal.span ({a,b}:Set R) ≤ Ideal.span ({a,b,c}:Set R) :=
    Ideal.span_mono (by intro x hx; simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at *; tauto)
  have hcm : c ∈ Ideal.span ({a,b,c}:Set R) := Ideal.subset_span (by simp)
  refine ⟨?_,?_,hab hw⟩
  · simpa using (Ideal.span ({a,b,c}:Set R)).sub_mem (hab hu)
      ((Ideal.span ({a,b,c}:Set R)).mul_mem_right s hcm)
  · simpa using (Ideal.span ({a,b,c}:Set R)).sub_mem (hab hv)
      ((Ideal.span ({a,b,c}:Set R)).mul_mem_right t hcm)

end Regular
end CycleQ2ConormalRegular

end

section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2MonicRegular
open CycleQ2IncidenceNormalForm

variable {σ R : Type*} [CommRing R]

theorem mul_monic_ne_zero (m : MonomialOrder σ) {p q : MvPolynomial σ R}
    (hp : p ≠ 0) (hq : m.Monic q) : p*q ≠ 0 := by
  have hc : m.leadingCoeff p * m.leadingCoeff q ≠ 0 := by
    simpa [hq.leadingCoeff_eq_one] using m.leadingCoeff_ne_zero_iff.mpr hp
  intro hz
  have he := m.leadingCoeff_mul_of_mul_leadingCoeff_ne_zero hc
  rw [hz] at he
  exact hc (by simpa using he.symm)

theorem monic_regular (m : MonomialOrder σ) {p : MvPolynomial σ R}
    (hp : m.Monic p) (x : MvPolynomial σ R) (hx : p*x=0) : x=0 := by
  by_contra hn
  exact mul_monic_ne_zero m hn hp (by simpa [mul_comm] using hx)

/-- Cancellation of the second monic equation modulo the first. -/
theorem pair_regular_mod_first (m : MonomialOrder σ) {h F : MvPolynomial σ R}
    (hh : m.Monic h) (hF : m.Monic F)
    (hcop : ∀ i, m.degree h i=0 ∨ m.degree F i=0)
    (x : MvPolynomial σ R) (hFx : F*x ∈ Ideal.span ({h}:Set _)) :
    x ∈ Ideal.span ({h}:Set _) := by
  obtain ⟨a,ha⟩ := Ideal.mem_span_singleton'.mp hFx
  obtain ⟨q,r,hx,_,hr⟩ := m.div_single
    (show IsUnit (m.leadingCoeff h) by rw [hh.leadingCoeff_eq_one]; exact isUnit_one) x
  have hp : r*F=(a-q*F)*h := by linear_combination -ha-F*hx
  have hr0 : r=0 := by
    by_contra hn
    have hs : a-q*F≠0 := by
      intro hz
      apply mul_monic_ne_zero m hn hF
      simpa [hz] using hp
    have hd := congrArg m.degree hp
    rw [degree_mul_monic m hn hF, degree_mul_monic m hs hh] at hd
    have hle : m.degree h ≤ m.degree r+m.degree F := by
      rw [hd]
      intro i
      simp only [Finsupp.add_apply]
      omega
    apply hr (m.degree r) (m.degree_mem_support hn)
    intro i
    rcases hcop i with hi | hi
    · simp [hi]
    · simpa only [Finsupp.add_apply,hi,add_zero] using hle i
  apply Ideal.mem_span_singleton'.mpr
  exact ⟨q,by simpa [hr0] using hx.symm⟩

/-- The concrete two-equation Groebner consequence needed for the third
regularity step: a nonzero element of the ideal has divisible leading term. -/
theorem leading_of_pair_representation
    (m : MonomialOrder σ) {h F p a b : MvPolynomial σ R}
    (hh : m.Monic h) (hF : m.Monic F)
    (hcop : ∀ i, m.degree h i=0 ∨ m.degree F i=0)
    (hp0 : p≠0) (heq : p=a*h+b*F) :
    m.degree h ≤ m.degree p ∨ m.degree F ≤ m.degree p := by
  obtain ⟨q,r,ha,_,hr⟩ := m.div_single
    (show IsUnit (m.leadingCoeff F) by rw [hF.leadingCoeff_eq_one]; exact isUnit_one) a
  let s := b+q*h
  have hp : p=r*h+s*F := by rw [heq,ha]; dsimp [s]; ring
  by_cases hr0 : r=0
  · have hs0 : s≠0 := by intro hz; apply hp0; simpa [hr0,hz] using hp
    right
    rw [hp,hr0,zero_mul,zero_add,degree_mul_monic m hs0 hF]
    intro i
    simp only [Finsupp.add_apply]
    omega
  have hrd : m.degree (r*h)=m.degree r+m.degree h := degree_mul_monic m hr0 hh
  have hrn : ¬ m.degree F ≤ m.degree (r*h) := by
    intro hd
    apply hr (m.degree r) (m.degree_mem_support hr0)
    rw [hrd] at hd
    intro i
    rcases hcop i with hi | hi
    · simpa only [Finsupp.add_apply,hi,add_zero] using hd i
    · simp [hi]
  have hhd : m.degree h ≤ m.degree (r*h) := by
    rw [hrd]
    intro i
    simp only [Finsupp.add_apply]
    omega
  by_cases hs0 : s=0
  · left
    simpa only [hp,hs0,zero_mul,add_zero] using hhd
  have hFd : m.degree F ≤ m.degree (s*F) := by
    rw [degree_mul_monic m hs0 hF]
    intro i
    simp only [Finsupp.add_apply]
    omega
  have hne : m.toSyn (m.degree (r*h))≠m.toSyn (m.degree (s*F)) := by
    intro he
    apply hrn
    rwa [m.toSyn.injective he]
  rcases lt_or_gt_of_ne hne with hd | hd
  · right
    rwa [hp,m.degree_add_eq_right_of_lt hd]
  · left
    rwa [hp,m.degree_add_of_lt hd]

/-- Cancellation of a third monic equation modulo the first two. -/
theorem triple_regular_mod_pair (m : MonomialOrder σ)
    {a b c : MvPolynomial σ R} (ha : m.Monic a) (hb : m.Monic b) (hc : m.Monic c)
    (hab : ∀ i, m.degree a i=0 ∨ m.degree b i=0)
    (hac : ∀ i, m.degree a i=0 ∨ m.degree c i=0)
    (hbc : ∀ i, m.degree b i=0 ∨ m.degree c i=0)
    (x : MvPolynomial σ R) (hcx : c*x ∈ Ideal.span ({a,b}:Set _)) :
    x ∈ Ideal.span ({a,b}:Set _) := by
  obtain ⟨u,v,huv⟩ := Ideal.mem_span_pair.mp hcx
  obtain ⟨q,t,r,hx,hr⟩ := exists_reduced_representation m a b x ha hb
  have hp : r*c=(u-q*c)*a+(v-t*c)*b := by linear_combination -huv-c*hx
  have hr0 : r=0 := by
    by_contra hn
    have hd := leading_of_pair_representation m ha hb hab
      (mul_monic_ne_zero m hn hc) hp
    rw [degree_mul_monic m hn hc] at hd
    have hred := hr (m.degree r) (m.degree_mem_support hn)
    rcases hd with hd | hd
    · apply hred.1
      intro i
      rcases hac i with hi | hi
      · simp [hi]
      · simpa only [Finsupp.add_apply,hi,add_zero] using hd i
    · apply hred.2
      intro i
      rcases hbc i with hi | hi
      · simp [hi]
      · simpa only [Finsupp.add_apply,hi,add_zero] using hd i
  exact Ideal.mem_span_pair.mpr ⟨q,t,by simpa [hr0] using hx.symm⟩

theorem pair_relation_coefficients (m : MonomialOrder σ) (a b : MvPolynomial σ R)
    (ha : m.Monic a) (hb : m.Monic b)
    (hab : ∀ i, m.degree a i=0 ∨ m.degree b i=0)
    (v : Fin 2 → MvPolynomial σ R) (hv : (∑ i, v i * (![a,b] i))=0) :
    ∀ i, v i ∈ Ideal.span (Set.range ![a,b]) := by
  have hset : Set.range ![a,b] = ({a,b}:Set _) := by
    ext x
    simp [Set.mem_range,Fin.exists_fin_succ,eq_comm,or_comm]
  rw [hset]
  have hp := CycleQ2ConormalRegular.pair_relation_coefficients a b
    (monic_regular m ha) (pair_regular_mod_first m ha hb hab) (v 0) (v 1)
    (by simpa [Fin.sum_univ_two,mul_comm] using hv)
  intro i
  fin_cases i
  · exact hp.1
  · exact hp.2

theorem triple_relation_coefficients (m : MonomialOrder σ) (a b c : MvPolynomial σ R)
    (ha : m.Monic a) (hb : m.Monic b) (hc : m.Monic c)
    (hab : ∀ i, m.degree a i=0 ∨ m.degree b i=0)
    (hac : ∀ i, m.degree a i=0 ∨ m.degree c i=0)
    (hbc : ∀ i, m.degree b i=0 ∨ m.degree c i=0)
    (v : Fin 3 → MvPolynomial σ R) (hv : (∑ i, v i * (![a,b,c] i))=0) :
    ∀ i, v i ∈ Ideal.span (Set.range ![a,b,c]) := by
  have hset : Set.range ![a,b,c] = ({a,b,c}:Set _) := by
    ext x
    simp [Set.mem_range,Fin.exists_fin_succ,eq_comm,or_assoc,or_comm,or_left_comm]
  rw [hset]
  have hp := CycleQ2ConormalRegular.triple_relation_coefficients a b c
    (monic_regular m ha) (pair_regular_mod_first m ha hb hab)
    (triple_regular_mod_pair m ha hb hc hab hac hbc) (v 0) (v 1) (v 2)
    (by simpa [Fin.sum_univ_three,mul_comm,add_assoc] using hv)
  intro i
  fin_cases i
  · exact hp.1
  · exact hp.2.1
  · exact hp.2.2

end CycleQ2MonicRegular

end

section
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2SeedRegularLeading

open MvPolynomial CycleQ2SeedTrace CycleQ2NormalConnecting
  CycleQ2IncidenceNormalForm
open scoped BigOperators MonomialOrder

abbrev Exponent := Fin 5 →₀ ℕ

def exponent (a b c d e : ℕ) : Exponent :=
  Finsupp.single 0 a + Finsupp.single 1 b + Finsupp.single 2 c +
    Finsupp.single 3 d + Finsupp.single 4 e

def auxiliaryWeight : Exponent →+ ℕ where
  toFun e := 3 * e 0 + e 1 + 4 * e 2 + e 3 + 9 * e 4
  map_zero' := by simp
  map_add' a b := by simp only [Finsupp.add_apply]; omega

def auxiliaryOrder : MonomialOrder (Fin 5) :=
  weightedOrder MonomialOrder.lex auxiliaryWeight

@[simp] theorem auxiliaryWeight_exponent (a b c d e : ℕ) :
    auxiliaryWeight (exponent a b c d e) = 3*a+b+4*c+d+9*e := by
  norm_num [auxiliaryWeight, exponent, Finsupp.single_apply, Fin.ext_iff]

theorem monomial_exponent (a b c d e : ℕ) (z : ℂ) :
    monomial (exponent a b c d e) z =
      C z * X 0^a * X 1^b * X 2^c * X 3^d * X 4^e := by
  simp only [exponent, monomial_add_single, ←C_mul_X_pow_eq_monomial]

theorem f1_shape (r : ℂ) :
    originalF1 r = monomial (exponent 2 0 0 0 0) 1 +
      ∑ _i : Fin 1, monomial (exponent 0 1 0 1 0) (-r) := by
  simp only [Fin.sum_univ_one, monomial_exponent]
  simp [originalF1, sub_eq_add_neg]

theorem f2_shape :
    originalF2 = monomial (exponent 0 0 0 0 1) 1 +
      ∑ _i : Fin 1, monomial (exponent 0 0 2 0 0) 1 := by
  simp only [Fin.sum_univ_one, monomial_exponent]
  simp [originalF2]

def cubicTailExponent (i : Fin 6) : Exponent :=
  ![exponent 0 0 0 3 0, exponent 0 1 1 1 0, exponent 1 0 1 1 0,
    exponent 1 2 0 0 0, exponent 0 3 0 0 0, exponent 3 0 0 0 0] i

def hTailCoefficient (θ : ℂ) (i : Fin 6) : ℂ :=
  ![1-Complex.I, 1, 1, 1, -Complex.I, θ] i

def kTailCoefficient (θ : ℂ) (i : Fin 6) : ℂ :=
  ![1+Complex.I, 1, 1, 1, Complex.I, θ] i

theorem h_shape (θ : ℂ) :
    thetaH θ = monomial (exponent 0 0 3 0 0) 1 +
      ∑ i : Fin 6, monomial (cubicTailExponent i) (hTailCoefficient θ i) := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, cubicTailExponent,
    hTailCoefficient, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, monomial_exponent]
  norm_num [thetaH, originalH, originalB]
  ring

theorem k_shape (θ : ℂ) :
    thetaK θ = monomial (exponent 0 0 3 0 0) 1 +
      ∑ i : Fin 6, monomial (cubicTailExponent i) (kTailCoefficient θ i) := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, cubicTailExponent,
    kTailCoefficient, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, monomial_exponent]
  norm_num [thetaK, originalK, originalB]
  ring

def g1TailExponent (i : Fin 2) : Exponent :=
  ![exponent 2 1 0 1 0, exponent 0 2 0 2 0] i

def g1TailCoefficient (r : ℂ) (i : Fin 2) : ℂ := ![r,r^2] i

theorem g1_shape (r : ℂ) :
    originalG1 r = monomial (exponent 4 0 0 0 0) 1 +
      ∑ i : Fin 2, monomial (g1TailExponent i) (g1TailCoefficient r i) := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, g1TailExponent,
    g1TailCoefficient, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, monomial_exponent]
  norm_num [originalG1]
  ring

def g2TailExponent (i : Fin 2) : Exponent :=
  ![exponent 0 0 2 0 1, exponent 0 0 4 0 0] i

def g2TailCoefficient (i : Fin 2) : ℂ := ![-1,1] i

theorem g2_shape :
    originalG2 = monomial (exponent 0 0 0 0 2) 1 +
      ∑ i : Fin 2, monomial (g2TailExponent i) (g2TailCoefficient i) := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, g2TailExponent,
    g2TailCoefficient, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, monomial_exponent]
  norm_num [originalG2]
  ring

theorem f1_leading_data (r : ℂ) :
    auxiliaryOrder.degree (originalF1 r) = Finsupp.single 0 2 ∧
      auxiliaryOrder.Monic (originalF1 r) := by
  rw [f1_shape]
  have h := degree_monic_add_sum auxiliaryOrder (exponent 2 0 0 0 0)
    (fun _i : Fin 1 => exponent 0 1 0 1 0) (fun _ => -r) (by
      apply weightedOrder_lt_of_weight_lt
      norm_num [auxiliaryWeight, exponent, Fin.ext_iff]) (by
      intro i
      apply weightedOrder_lt_of_weight_lt
      norm_num [auxiliaryWeight, exponent, Fin.ext_iff])
  simpa [exponent] using h

theorem f2_leading_data :
    auxiliaryOrder.degree originalF2 = Finsupp.single 4 1 ∧
      auxiliaryOrder.Monic originalF2 := by
  rw [f2_shape]
  have h := degree_monic_add_sum auxiliaryOrder (exponent 0 0 0 0 1)
    (fun _i : Fin 1 => exponent 0 0 2 0 0) (fun _ => (1 : ℂ)) (by
      apply weightedOrder_lt_of_weight_lt
      norm_num [auxiliaryWeight, exponent, Fin.ext_iff]) (by
      intro i
      apply weightedOrder_lt_of_weight_lt
      norm_num [auxiliaryWeight, exponent, Fin.ext_iff])
  simpa [exponent] using h

private theorem cubic_tail_lt (i : Fin 6) :
    cubicTailExponent i ≺[auxiliaryOrder] exponent 0 0 3 0 0 := by
  apply weightedOrder_lt_of_weight_lt
  fin_cases i <;> norm_num [auxiliaryWeight, cubicTailExponent, exponent,
    Matrix.cons_val_succ, Fin.reduceSucc, Fin.ext_iff]

theorem h_leading_data (θ : ℂ) :
    auxiliaryOrder.degree (thetaH θ) = Finsupp.single 2 3 ∧
      auxiliaryOrder.Monic (thetaH θ) := by
  rw [h_shape]
  have h := degree_monic_add_sum auxiliaryOrder (exponent 0 0 3 0 0)
    cubicTailExponent (hTailCoefficient θ) (by
      apply weightedOrder_lt_of_weight_lt
      norm_num [auxiliaryWeight, exponent, Fin.ext_iff]) cubic_tail_lt
  simpa [exponent] using h

theorem k_leading_data (θ : ℂ) :
    auxiliaryOrder.degree (thetaK θ) = Finsupp.single 2 3 ∧
      auxiliaryOrder.Monic (thetaK θ) := by
  rw [k_shape]
  have h := degree_monic_add_sum auxiliaryOrder (exponent 0 0 3 0 0)
    cubicTailExponent (kTailCoefficient θ) (by
      apply weightedOrder_lt_of_weight_lt
      norm_num [auxiliaryWeight, exponent, Fin.ext_iff]) cubic_tail_lt
  simpa [exponent] using h

theorem g1_leading_data (r : ℂ) :
    auxiliaryOrder.degree (originalG1 r) = Finsupp.single 0 4 ∧
      auxiliaryOrder.Monic (originalG1 r) := by
  rw [g1_shape]
  have h := degree_monic_add_sum auxiliaryOrder (exponent 4 0 0 0 0)
    g1TailExponent (g1TailCoefficient r) (by
      apply weightedOrder_lt_of_weight_lt
      norm_num [auxiliaryWeight, exponent, Fin.ext_iff]) (by
      intro i
      apply weightedOrder_lt_of_weight_lt
      fin_cases i <;> norm_num [auxiliaryWeight, g1TailExponent, exponent,
        Matrix.cons_val_succ, Fin.reduceSucc, Fin.ext_iff])
  simpa [exponent] using h

theorem g2_leading_data :
    auxiliaryOrder.degree originalG2 = Finsupp.single 4 2 ∧
      auxiliaryOrder.Monic originalG2 := by
  rw [g2_shape]
  have h := degree_monic_add_sum auxiliaryOrder (exponent 0 0 0 0 2)
    g2TailExponent g2TailCoefficient (by
      apply weightedOrder_lt_of_weight_lt
      norm_num [auxiliaryWeight, exponent, Fin.ext_iff]) (by
      intro i
      apply weightedOrder_lt_of_weight_lt
      fin_cases i <;> norm_num [auxiliaryWeight, g2TailExponent, exponent,
        Matrix.cons_val_succ, Fin.reduceSucc, Fin.ext_iff])
  simpa [exponent] using h

theorem F_leading_data (r θ : ℂ) :
    auxiliaryOrder.degree (actualSeedEquation r θ) = Finsupp.single 4 3 ∧
      auxiliaryOrder.Monic (actualSeedEquation r θ) := by
  have hA : auxiliaryOrder.degree (originalF1 r * originalG1 r) =
      Finsupp.single 0 6 := by
    rw [auxiliaryOrder.degree_mul (f1_leading_data r).2.ne_zero
      (g1_leading_data r).2.ne_zero, (f1_leading_data r).1,
      (g1_leading_data r).1, ←Finsupp.single_add]
  have hB : auxiliaryOrder.degree (originalF2 * originalG2) =
      Finsupp.single 4 3 := by
    rw [auxiliaryOrder.degree_mul f2_leading_data.2.ne_zero
      g2_leading_data.2.ne_zero, f2_leading_data.1,
      g2_leading_data.1, ←Finsupp.single_add]
  have hC : auxiliaryOrder.degree (thetaH θ * thetaK θ) =
      Finsupp.single 2 6 := by
    rw [auxiliaryOrder.degree_mul (h_leading_data θ).2.ne_zero
      (k_leading_data θ).2.ne_zero, (h_leading_data θ).1,
      (k_leading_data θ).1, ←Finsupp.single_add]
  have hAB : auxiliaryOrder.degree (originalF1 r * originalG1 r) ≺[auxiliaryOrder]
      auxiliaryOrder.degree (originalF2 * originalG2) := by
    rw [hA,hB]
    apply weightedOrder_lt_of_weight_lt
    norm_num [auxiliaryWeight, Fin.ext_iff]
  have hCB : auxiliaryOrder.degree (thetaH θ * thetaK θ) ≺[auxiliaryOrder]
      auxiliaryOrder.degree (originalF2 * originalG2) := by
    rw [hC,hB]
    apply weightedOrder_lt_of_weight_lt
    norm_num [auxiliaryWeight, Fin.ext_iff]
  have hBA := auxiliaryOrder.degree_add_of_lt hAB
  have hCBA : auxiliaryOrder.degree (thetaH θ * thetaK θ) ≺[auxiliaryOrder]
      auxiliaryOrder.degree (originalF2 * originalG2 + originalF1 r * originalG1 r) := by
    rw [hBA]
    exact hCB
  unfold actualSeedEquation
  rw [add_comm (originalF1 r * originalG1 r) (originalF2 * originalG2)]
  exact ⟨(auxiliaryOrder.degree_add_of_lt hCBA).trans (hBA.trans hB),
    ((f2_leading_data.2.mul g2_leading_data.2).add_of_lt hAB).add_of_lt hCBA⟩

theorem f1_f2_coprime (r : ℂ) (i : Fin 5) :
    auxiliaryOrder.degree (originalF1 r) i = 0 ∨
      auxiliaryOrder.degree originalF2 i = 0 := by
  rw [(f1_leading_data r).1, f2_leading_data.1]
  fin_cases i <;> simp

theorem f1_h_coprime (r θ : ℂ) (i : Fin 5) :
    auxiliaryOrder.degree (originalF1 r) i = 0 ∨
      auxiliaryOrder.degree (thetaH θ) i = 0 := by
  rw [(f1_leading_data r).1, (h_leading_data θ).1]
  fin_cases i <;> simp

theorem f2_h_coprime (θ : ℂ) (i : Fin 5) :
    auxiliaryOrder.degree originalF2 i = 0 ∨
      auxiliaryOrder.degree (thetaH θ) i = 0 := by
  rw [f2_leading_data.1, (h_leading_data θ).1]
  fin_cases i <;> simp

theorem F_h_coprime (r θ : ℂ) (i : Fin 5) :
    auxiliaryOrder.degree (actualSeedEquation r θ) i = 0 ∨
      auxiliaryOrder.degree (thetaH θ) i = 0 := by
  rw [(F_leading_data r θ).1, (h_leading_data θ).1]
  fin_cases i <;> simp

end CycleQ2SeedRegularLeading

end

section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace CycleQ2SeedGlobalConormal
open CycleQ2SeedTrace CycleQ2NormalConnecting CycleQ2ConormalJacobian
  CycleQ2SeedRegularLeading CycleQ2NaturalNormalMap

theorem source_relation_coefficients (r θ : ℂ) (v : Fin 3 → WeightedPoly)
    (hv : (∑ i, v i * curveEquations r θ i)=0) :
    ∀ i, v i ∈ ambientCurveIdeal r θ := by
  simpa only [ambientCurveIdeal,curveEquations] using
    CycleQ2MonicRegular.triple_relation_coefficients auxiliaryOrder
      (originalF1 r) originalF2 (thetaH θ)
      (f1_leading_data r).2 f2_leading_data.2 (h_leading_data θ).2
      (f1_f2_coprime r) (f1_h_coprime r θ) (f2_h_coprime θ) v hv

theorem target_relation_coefficients (r θ : ℂ) (v : Fin 2 → WeightedPoly)
    (hv : (∑ i, v i * surfaceEquations r θ i)=0) :
    ∀ i, v i ∈ surfaceIdeal r θ := by
  simpa only [surfaceIdeal,surfaceEquations] using
    CycleQ2MonicRegular.pair_relation_coefficients auxiliaryOrder
      (actualSeedEquation r θ) (thetaH θ)
      (F_leading_data r θ).2 (h_leading_data θ).2
      (F_h_coprime r θ) v hv

section ScalarExtension
variable {S : Type*} [CommRing S] [Algebra WeightedPoly S]

/-- The three original equation classes form a basis on any scalar
extension of the actual curve quotient, including the whole quotient. -/
def seedConormalBasis (r θ : ℂ)
    (hI : ∀ p ∈ ambientCurveIdeal r θ, algebraMap WeightedPoly S p=0) :
    Module.Basis (Fin 3) S (S ⊗[WeightedPoly] (ambientCurveIdeal r θ).Cotangent) :=
  CycleQ2ConormalRegular.conormalBasis (ambientCurveIdeal r θ)
    (curveEquations r θ) rfl hI (source_relation_coefficients r θ)

@[simp] theorem seedConormalBasis_apply (r θ : ℂ)
    (hI : ∀ p ∈ ambientCurveIdeal r θ, algebraMap WeightedPoly S p=0) (i : Fin 3) :
    seedConormalBasis r θ hI i = (1:S) ⊗ₜ[WeightedPoly] conormalGenerator r θ i :=
  CycleQ2ConormalRegular.conormalBasis_apply _ _ _ _ _ _

/-- The two target equation classes also form a global basis after
restriction to the curve. No g1- or g2-unit condition is needed. -/
def surfaceConormalBasis (r θ : ℂ)
    (hI : ∀ p ∈ ambientCurveIdeal r θ, algebraMap WeightedPoly S p=0) :
    Module.Basis (Fin 2) S (S ⊗[WeightedPoly] (surfaceIdeal r θ).Cotangent) :=
  CycleQ2ConormalRegular.conormalBasis (surfaceIdeal r θ)
    (surfaceEquations r θ) rfl
    (fun p hp => hI p (surfaceIdeal_le_curveIdeal r θ hp))
    (target_relation_coefficients r θ)

@[simp] theorem surfaceConormalBasis_apply (r θ : ℂ)
    (hI : ∀ p ∈ ambientCurveIdeal r θ, algebraMap WeightedPoly S p=0) (j : Fin 2) :
    surfaceConormalBasis r θ hI j =
      generator (S := S) (surfaceIdeal r θ) (surfaceEquations r θ) rfl j :=
  CycleQ2ConormalRegular.conormalBasis_apply _ _ _ _ _ _

end ScalarExtension
end CycleQ2SeedGlobalConormal
end
