import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Proposal.GeometricVariation
import Proposal.IncidenceBasepointCharts

set_option autoImplicit false

/-!
# Monomial and Jacobian columns over the full invariant sextic base

For a fixed weighted degree and character, keep every Fermat standard
monomial and replace each remaining monomial by one multiple of a partial
derivative of the universal polynomial. The full square coefficient matrix
specializes to the identity for the literal Fermat coefficients. Its
determinant defines a principal open of the full coefficient space.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

noncomputable section
namespace CycleQ2HiggsJacobianFrames

open MvPolynomial Matrix CycleQ2IncidenceNormalForm
open CycleQ2GenericSexticGradient (CoeffRing universalF seedEvaluation universalF_seed)
open CycleQ2FermatJacobian (cutoff derivativeScalar derivativeScalar_ne_zero)

abbrev Index (n : ℕ) (χ : ZMod 3) :=
  {e : Fin 5 → Fin (n + 1) // Finsupp.weight fullGrading (fullExponentOf e) = (n, χ)}

def exp {n : ℕ} {χ : ZMod 3} (e : Index n χ) : Fin 5 →₀ ℕ := fullExponentOf e.val

theorem exp_injective {n : ℕ} {χ : ZMod 3} :
    Function.Injective (exp (n := n) (χ := χ)) := by
  intro a b h
  apply Subtype.ext
  funext i
  apply Fin.ext
  simpa only [exp, fullExponentOf_apply] using congrArg (fun x : Fin 5 →₀ ℕ => x i) h

theorem exists_index {n : ℕ} {χ : ZMod 3} (x : Fin 5 →₀ ℕ)
    (hx : Finsupp.weight fullGrading x = (n, χ)) : ∃ e : Index n χ, exp e = x := by
  have hd : fullDegree x = n := congrArg Prod.fst ((fullGrading_weight x).symm.trans hx)
  have hb (i : Fin 5) : x i < n + 1 := by
    unfold fullDegree at hd
    fin_cases i
    · change x 0 < n + 1
      omega
    · change x 1 < n + 1
      omega
    · change x 2 < n + 1
      omega
    · change x 3 < n + 1
      omega
    · change x 4 < n + 1
      omega
  let e (i : Fin 5) : Fin (n + 1) := ⟨x i, hb i⟩
  have he : fullExponentOf e = x := by ext i; exact fullExponentOf_apply e i
  exact ⟨⟨e, he ▸ hx⟩, he⟩

def Standard {n : ℕ} {χ : ZMod 3} (e : Index n χ) : Prop := ∀ i, exp e i < cutoff i

abbrev Bounded (n : ℕ) (χ : ZMod 3) := {e : Index n χ // Standard e}

theorem exists_pivot {n : ℕ} {χ : ZMod 3} {e : Index n χ} (h : ¬ Standard e) :
    ∃ i, Finsupp.single i (cutoff i) ≤ exp e := by
  classical
  unfold Standard at h
  push Not at h
  obtain ⟨i, hi⟩ := h
  exact ⟨i, Finsupp.single_le_iff.mpr hi⟩

def pivot {n : ℕ} {χ : ZMod 3} {e : Index n χ} (h : ¬ Standard e) := (exists_pivot h).choose

theorem pivot_le {n : ℕ} {χ : ZMod 3} {e : Index n χ} (h : ¬ Standard e) :
    Finsupp.single (pivot h) (cutoff (pivot h)) ≤ exp e := (exists_pivot h).choose_spec

def column {n : ℕ} {χ : ZMod 3} (e : Index n χ) : MvPolynomial (Fin 5) CoeffRing := by
  classical
  exact if h : Standard e then monomial (exp e) 1 else
    let i := pivot h
    monomial (exp e - Finsupp.single i (cutoff i)) (C (derivativeScalar i)⁻¹) *
      pderiv i universalF

theorem seed_column {n : ℕ} {χ : ZMod 3} (e : Index n χ) :
    MvPolynomial.map seedEvaluation (column e) = monomial (exp e) (1 : ℂ) := by
  classical
  unfold column
  split_ifs with h
  · simp
  · simp only [map_mul, map_monomial, CycleQ2GenericSexticGradient.seedEvaluation, eval_C,
      ← pderiv_map]
    rw [show MvPolynomial.map (eval CycleQ2GenericSexticGradient.fermatCoefficients) universalF =
          CycleQ2FermatJacobian.fermat from universalF_seed,
      CycleQ2FermatJacobian.derivative_eq, CycleQ2FermatJacobian.generator, X_pow_eq_monomial,
      C_mul_monomial, mul_one, monomial_mul, inv_mul_cancel₀ (derivativeScalar_ne_zero _),
      tsub_add_cancel_of_le (pivot_le h)]

def frameMatrix (n : ℕ) (χ : ZMod 3) : Matrix (Index n χ) (Index n χ) CoeffRing :=
  fun i j => coeff (exp i) (column j)

theorem seed_frameMatrix (n : ℕ) (χ : ZMod 3) :
    (frameMatrix n χ).map seedEvaluation = 1 := by
  classical
  ext i j
  change seedEvaluation (coeff (exp i) (column j)) = (1 : Matrix (Index n χ) _ ℂ) i j
  rw [← coeff_map, seed_column, coeff_monomial, Matrix.one_apply]
  simp [exp_injective.eq_iff, eq_comm]

def frameDet (n : ℕ) (χ : ZMod 3) : CoeffRing := (frameMatrix n χ).det

@[simp] theorem seed_frameDet (n : ℕ) (χ : ZMod 3) : seedEvaluation (frameDet n χ) = 1 := by
  rw [frameDet, RingHom.map_det]
  change ((frameMatrix n χ).map seedEvaluation).det = 1
  rw [seed_frameMatrix, Matrix.det_one]

def jacobian {R : Type*} [CommRing R] (φ : CoeffRing →+* R) :
    Ideal (MvPolynomial (Fin 5) R) := Ideal.span (Set.range fun i =>
      pderiv i (MvPolynomial.map φ universalF))

theorem nonstandard_column_mem {R : Type*} [CommRing R] (φ : CoeffRing →+* R)
    {n : ℕ} {χ : ZMod 3} {e : Index n χ} (h : ¬ Standard e) :
    MvPolynomial.map φ (column e) ∈ jacobian φ := by
  classical
  simp only [column, dif_neg h, map_mul, ← pderiv_map]
  apply Ideal.mul_mem_left
  exact Ideal.subset_span ⟨pivot h, rfl⟩

end CycleQ2HiggsJacobianFrames
end

#print axioms CycleQ2HiggsJacobianFrames.seed_frameDet

/-!
# Degree and character in the Jacobian ideal of the invariant sextic

On every coefficient specialization, project an arbitrary ideal-membership
witness onto the unique multiplier bidegree that can contribute to the
given component. A partial derivative of weight greater than the target
weight contributes zero.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

noncomputable section

namespace CycleQ2HiggsJacobianMembership

open MvPolynomial CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations
open CycleQ2GenericSexticGradient

variable {K : Type*} [CommRing K]

theorem partial_homogeneous (φ : CoeffRing →+* K) (i : Fin 5) :
    HG (pderiv i (MvPolynomial.map φ universalF))
      (6 - (fullGrading i).1, -(fullGrading i).2) := by
  have hF : HG (MvPolynomial.map φ universalF) (6, 0) := by
    rw [universalF, map_fullInvariantPolynomial]
    exact fullInvariantPolynomial_homogeneous _ _
  apply hF.pderiv
  apply Prod.ext
  · have hi : (fullGrading i).1 ≤ 6 := by fin_cases i <;> decide
    exact Nat.sub_add_cancel hi
  · exact neg_add_cancel _

private def multiplier (N : ℕ) (χ : ZMod 3) (e : ℕ) (κ : ZMod 3) (u : Poly K) :
    Poly K :=
  if e ≤ N then weightedHomogeneousComponent fullGrading (N - e, χ - κ) u else 0

private theorem multiplier_homogeneous (N : ℕ) (χ : ZMod 3) (e : ℕ) (κ : ZMod 3)
    (u : Poly K) : HG (multiplier N χ e κ u) (N - e, χ - κ) := by
  unfold multiplier
  split
  · exact weightedHomogeneousComponent_isWeightedHomogeneous _ _
  · exact (weightedHomogeneousSubmodule K fullGrading _).zero_mem

private theorem component_mul_below (N : ℕ) (χ : ZMod 3) (e : ℕ) (κ : ZMod 3)
    (u q : Poly K) (hq : HG q (e, κ)) (h : N < e) :
    weightedHomogeneousComponent fullGrading (N, χ) (u * q) = 0 := by
  induction u using MvPolynomial.induction_on' with
  | monomial a c =>
    have hm : HG (monomial a c : Poly K) (Finsupp.weight fullGrading a) :=
      isWeightedHomogeneous_monomial fullGrading a c rfl
    apply (hm.mul hq).weightedHomogeneousComponent_ne
    intro heq
    have hd := congrArg Prod.fst heq
    change N = (Finsupp.weight fullGrading a).1 + e at hd
    omega
  | add a b ha hb =>
    rw [add_mul, map_add, ha, hb, add_zero]

private theorem component_mul (N : ℕ) (χ : ZMod 3) (e : ℕ) (κ : ZMod 3)
    (u q : Poly K) (hq : HG q (e, κ)) :
    weightedHomogeneousComponent fullGrading (N, χ) (u * q) =
      multiplier N χ e κ u * q := by
  by_cases h : e ≤ N
  · have hgrade : (N - e, χ - κ) + (e, κ) = (N, χ) :=
      Prod.ext (Nat.sub_add_cancel h) (sub_add_cancel _ _)
    simpa only [multiplier, if_pos h, hgrade] using
      CycleQ2WeightedComponent.component_mul fullGrading u q (N - e, χ - κ) (e, κ) hq
  · rw [component_mul_below N χ e κ u q hq (Nat.lt_of_not_ge h), multiplier, if_neg h, zero_mul]

/-- Project an arbitrary Jacobian ideal representation onto one bidegree. -/
theorem component_multipliers (φ : CoeffRing →+* K) (N : ℕ) (χ : ZMod 3)
    (p : Poly K)
    (hmem : p ∈ Ideal.span (Set.range (fun i : Fin 5 => pderiv i (MvPolynomial.map φ universalF)))) :
    ∃ h : Fin 5 → Poly K,
      (∀ i, HG (h i) (N - (6 - (fullGrading i).1), χ + (fullGrading i).2)) ∧
      (∀ i, N < 6 - (fullGrading i).1 → h i = 0) ∧
      weightedHomogeneousComponent fullGrading (N, χ) p =
        ∑ i, h i * pderiv i (MvPolynomial.map φ universalF) := by
  obtain ⟨u, hu⟩ := Ideal.mem_span_range_iff_exists_fun.mp hmem
  refine ⟨fun i => multiplier N χ (6 - (fullGrading i).1) (-(fullGrading i).2) (u i),
    fun i => ?_, fun i hi => ?_, ?_⟩
  · simpa only [sub_neg_eq_add] using multiplier_homogeneous N χ
      (6 - (fullGrading i).1) (-(fullGrading i).2) (u i)
  · exact if_neg (Nat.not_le_of_lt hi)
  · have hproj := congrArg (weightedHomogeneousComponent fullGrading (N, χ)) hu
    rw [map_sum] at hproj
    exact hproj.symm.trans (Finset.sum_congr rfl (fun i _ =>
      component_mul N χ _ _ (u i) _ (partial_homogeneous φ i)))

theorem component_mem (φ : CoeffRing →+* K) (N : ℕ) (χ : ZMod 3) {p : Poly K}
    (hmem : p ∈ Ideal.span (Set.range (fun i : Fin 5 => pderiv i (MvPolynomial.map φ universalF)))) :
    weightedHomogeneousComponent fullGrading (N, χ) p ∈
      Ideal.span (Set.range (fun i : Fin 5 => pderiv i (MvPolynomial.map φ universalF))) := by
  obtain ⟨h, _, _, heq⟩ := component_multipliers φ N χ p hmem
  exact Ideal.mem_span_range_iff_exists_fun.mpr ⟨h, heq.symm⟩

/-- The Jacobian multipliers have their prescribed degree and character.
Every partial of weight above the target can be omitted entirely. -/
theorem membership_iff (φ : CoeffRing →+* K) (N : ℕ) (χ : ZMod 3)
    (p : Poly K) (hp : HG p (N, χ)) :
    p ∈ Ideal.span (Set.range (fun i : Fin 5 => pderiv i (MvPolynomial.map φ universalF))) ↔
      ∃ h : Fin 5 → Poly K,
        (∀ i, HG (h i) (N - (6 - (fullGrading i).1), χ + (fullGrading i).2)) ∧
        (∀ i, N < 6 - (fullGrading i).1 → h i = 0) ∧
        p = ∑ i, h i * pderiv i (MvPolynomial.map φ universalF) := by
  constructor
  · intro hmem
    simpa only [hp.weightedHomogeneousComponent_same] using component_multipliers φ N χ p hmem
  · rintro ⟨h, _, _, hsum⟩
    exact Ideal.mem_span_range_iff_exists_fun.mpr ⟨h, hsum.symm⟩

end CycleQ2HiggsJacobianMembership
end

#print axioms CycleQ2HiggsJacobianMembership.membership_iff

/-!
# Spanning the genuine graded Jacobian quotient on the Fermat open

In each degree and character the unit frame determinant expresses every
homogeneous polynomial as a combination of the standard monomials and
the actual partial-derivative multiples. Passing to the quotient by the
Jacobian ideal removes the latter columns.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/


noncomputable section
namespace CycleQ2HiggsJacobianFrames

open MvPolynomial Matrix CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations
open CycleQ2GenericSexticGradient (CoeffRing universalF seedEvaluation)
open CycleQ2FermatJacobian (cutoff)
open CycleQ2HiggsJacobianMembership (partial_homogeneous)

variable {R : Type} [CommRing R] (φ : CoeffRing →+* R)

theorem cutoff_weight (i : Fin 5) :
    Finsupp.weight fullGrading (Finsupp.single i (cutoff i)) =
      (6 - (fullGrading i).1, -(fullGrading i).2) := by
  rw [Finsupp.weight_single]
  fin_cases i <;> decide

theorem mapped_column_homogeneous {n : ℕ} {χ : ZMod 3} (e : Index n χ) :
    HG (MvPolynomial.map φ (column e)) (n, χ) := by
  classical
  unfold column
  split_ifs with h
  · rw [map_monomial]
    exact isWeightedHomogeneous_monomial fullGrading _ _ e.property
  · simp only [map_mul, map_monomial, ← pderiv_map]
    let i := pivot h
    let a := exp e - Finsupp.single i (cutoff i)
    have hg : Finsupp.weight fullGrading a + (6 - (fullGrading i).1, -(fullGrading i).2) =
        (n,χ) := by
      rw [← cutoff_weight, ← map_add, tsub_add_cancel_of_le (pivot_le h)]
      exact e.property
    rw [← hg]
    exact (isWeightedHomogeneous_monomial fullGrading a _ rfl).mul (partial_homogeneous φ i)

theorem exists_column_expansion {n : ℕ} {χ : ZMod 3} (hd : IsUnit (φ (frameDet n χ)))
    (p : MvPolynomial (Fin 5) R) (hp : HG p (n,χ)) :
    ∃ c : Index n χ → R, ∑ j, c j • MvPolynomial.map φ (column j) = p := by
  classical
  let A := (frameMatrix n χ).map φ
  have hA : IsUnit A.det := by
    rw [frameDet, RingHom.map_det] at hd
    exact hd
  obtain ⟨c, hc⟩ := (Matrix.mulVec_surjective_iff_isUnit.mpr
    (A.isUnit_iff_isUnit_det.mpr hA)) (fun j => p.coeff (exp j))
  refine ⟨c, ?_⟩
  let r := ∑ j, c j • MvPolynomial.map φ (column j)
  have hr : HG r (n,χ) := (weightedHomogeneousSubmodule R fullGrading (n,χ)).sum_mem
    fun j _ => (weightedHomogeneousSubmodule R fullGrading (n,χ)).smul_mem _ (mapped_column_homogeneous φ j)
  apply MvPolynomial.ext
  intro v
  by_cases hv : Finsupp.weight fullGrading v = (n,χ)
  · obtain ⟨e, rfl⟩ := exists_index v hv
    simpa only [A, Matrix.mulVec, dotProduct, frameMatrix, Matrix.map_apply, coeff_sum,
      coeff_smul, smul_eq_mul, coeff_map, mul_comm] using congrFun hc e
  · have zero {t : MvPolynomial (Fin 5) R} (ht : HG t (n,χ)) : coeff v t = 0 := by
      by_contra h
      exact hv (ht h)
    exact (zero hr).trans (zero hp).symm

abbrev QuotientRing := MvPolynomial (Fin 5) R ⧸ jacobian φ

def quotientMap : MvPolynomial (Fin 5) R →ₐ[R] QuotientRing φ := Ideal.Quotient.mkₐ R _

def gradedPiece (n : ℕ) (χ : ZMod 3) : Submodule R (QuotientRing φ) :=
  (weightedHomogeneousSubmodule R fullGrading (n,χ)).map (quotientMap φ).toLinearMap

def boundedClass {n : ℕ} {χ : ZMod 3} (e : Bounded n χ) : QuotientRing φ :=
  quotientMap φ (monomial (exp e.val) 1)

/-- The quotient submodule is defined by the bigrading of actual polynomials.
The nonvanishing frame determinant makes its standard monomials span. -/
theorem gradedPiece_eq_span {n : ℕ} {χ : ZMod 3} (hd : IsUnit (φ (frameDet n χ))) :
    gradedPiece φ n χ = Submodule.span R (Set.range (boundedClass φ (n := n) (χ := χ))) := by
  classical
  apply le_antisymm
  · rintro _ ⟨p, hp, rfl⟩
    obtain ⟨c,hc⟩ := exists_column_expansion φ hd p hp
    change quotientMap φ p ∈ _
    rw [← hc, map_sum]
    apply Submodule.sum_mem
    intro j _
    rw [map_smul]
    apply Submodule.smul_mem
    by_cases hj : Standard j
    · have he : quotientMap φ (MvPolynomial.map φ (column j)) = boundedClass φ ⟨j,hj⟩ := by
        simp [column, hj, boundedClass]
      rw [he]
      exact Submodule.subset_span (Set.mem_range_self _)
    · have hz : quotientMap φ (MvPolynomial.map φ (column j)) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr (nonstandard_column_mem φ hj)
      rw [hz]
      exact zero_mem _
  · apply Submodule.span_le.mpr
    rintro _ ⟨e,rfl⟩
    exact ⟨monomial (exp e.val) 1,
      isWeightedHomogeneous_monomial fullGrading _ _ e.val.property, rfl⟩

end CycleQ2HiggsJacobianFrames
end

#print axioms CycleQ2HiggsJacobianFrames.gradedPiece_eq_span

/-!
# Indices of the three graded Fermat monomial bases

The 33 upper, 35 tangent and 33 lower monomials used in the finite Higgs
calculation label exactly the bounded columns of the corresponding graded
Jacobian frames. The lower label retains its complementary socle exponent.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/


noncomputable section
namespace CycleQ2GeometricHiggsGradedIndices

open CycleQ2HiggsJacobianFrames CycleQ2IncidenceNormalForm CycleQ2FermatHiggs
open CycleQ2FermatJacobian (Exp BoundedExp exponent bounded)
open CycleQ2FermatVariationAlgebra (lowerExponent lowerExponent_properties)

/-- The previous natural-number character is the canonical residue of the
character in the full grading. -/
theorem weight_eq_iff (e : Exp) (n : ℕ) (χ : ZMod 3) :
    Finsupp.weight fullGrading e = (n, χ) ↔
      weightedDegree e = n ∧ character e = χ.val := by
  rw [fullGrading_weight, Prod.mk.injEq]
  apply and_congr Iff.rfl
  constructor
  · intro he
    exact (ZMod.val_natCast 3 _).symm.trans (congrArg ZMod.val he)
  · intro he
    apply ZMod.val_injective
    exact (ZMod.val_natCast 3 _).trans he

private def label {n : ℕ} {χ : ZMod 3} (e : BoundedExp)
    (hw : Finsupp.weight fullGrading e.val = (n, χ)) : Bounded n χ := by
  let h := exists_index e.val hw
  refine ⟨h.choose, ?_⟩
  intro i
  rw [h.choose_spec]
  exact Nat.lt_succ_of_le (e.property i)

private theorem exp_label {n : ℕ} {χ : ZMod 3} (e : BoundedExp)
    (hw : Finsupp.weight fullGrading e.val = (n, χ)) :
    exp (label e hw).val = e.val :=
  (exists_index e.val hw).choose_spec

private def enumeration {ι : Type} (n : ℕ) (χ : ZMod 3)
    (v : ι → BoundedExp) (hinj : Function.Injective v)
    (hw : ∀ i, weightedDegree (v i).val = n ∧ character (v i).val = χ.val)
    (hall : ∀ e : Exp, e ∈ bounded → weightedDegree e = n → character e = χ.val →
      ∃ i, (v i).val = e) : ι ≃ Bounded n χ :=
  Equiv.ofBijective (fun i => label (v i) ((weight_eq_iff _ _ _).mpr (hw i))) (by
    constructor
    · intro i j hij
      apply hinj
      apply Subtype.ext
      simpa only [exp_label] using congrArg (fun e : Bounded n χ => exp e.val) hij
    · intro e
      have he := (weight_eq_iff (exp e.val) n χ).mp e.val.property
      obtain ⟨i, hi⟩ := hall (exp e.val) (fun k => Nat.le_of_lt_succ (e.property k)) he.1 he.2
      refine ⟨i, Subtype.ext (exp_injective ?_)⟩
      exact (exp_label _ _).trans hi)

/-- Upper degree-six character-one classes in the matrix order. -/
def upperIndex : Fin 33 ≃ Bounded 6 1 :=
  enumeration 6 1 CycleQ2FermatJacobian.basisIndex CycleQ2FermatJacobian.basisIndex_injective
    (fun i => ⟨(basis_properties i).1, (basis_properties i).2.1⟩)
    CycleQ2FermatJacobian.basis_complete_bounded

/-- Character-zero tangent directions in the matrix order. -/
def tangentIndex : Fin 35 ≃ Bounded 6 0 :=
  enumeration 6 0 CycleQ2FermatJacobian.tangentIndex CycleQ2FermatJacobian.tangentIndex_injective
    (fun i => ⟨(tangent_properties i).1, (tangent_properties i).2.1⟩)
    CycleQ2FermatJacobian.tangent_complete_bounded

/-- Complementary lower degree-twelve character-one classes in the dual upper order. -/
def lowerIndex : Fin 33 ≃ Bounded 12 1 :=
  enumeration 12 1 CycleQ2FermatVariationAlgebra.lowerIndex
    CycleQ2FermatVariationAlgebra.lowerIndex_injective
    (fun i => ⟨(lowerExponent_properties i).1, (lowerExponent_properties i).2.1⟩)
    CycleQ2FermatVariationAlgebra.lower_complete_bounded

@[simp] theorem exp_upperIndex (i : Fin 33) :
    exp (upperIndex i).val = exponent (basisMonomial i) :=
  exp_label (CycleQ2FermatJacobian.basisIndex i)
    ((weight_eq_iff _ 6 1).mpr ⟨(basis_properties i).1, (basis_properties i).2.1⟩)

@[simp] theorem exp_tangentIndex (m : Fin 35) :
    exp (tangentIndex m).val = exponent (tangentMonomial m) :=
  exp_label (CycleQ2FermatJacobian.tangentIndex m)
    ((weight_eq_iff _ 6 0).mpr ⟨(tangent_properties m).1, (tangent_properties m).2.1⟩)

@[simp] theorem exp_lowerIndex (i : Fin 33) :
    exp (lowerIndex i).val = exponent (lowerExponent i) :=
  exp_label (CycleQ2FermatVariationAlgebra.lowerIndex i)
    ((weight_eq_iff _ 12 1).mpr ⟨(lowerExponent_properties i).1, (lowerExponent_properties i).2.1⟩)

theorem exp_lowerIndex_eq_sub (i : Fin 33) :
    exp (lowerIndex i).val = exponent socle - exponent (basisMonomial i) := by
  rw [exp_lowerIndex]
  ext k
  rfl

end CycleQ2GeometricHiggsGradedIndices
end

#print axioms CycleQ2GeometricHiggsGradedIndices.upperIndex
#print axioms CycleQ2GeometricHiggsGradedIndices.tangentIndex
#print axioms CycleQ2GeometricHiggsGradedIndices.exp_lowerIndex_eq_sub
