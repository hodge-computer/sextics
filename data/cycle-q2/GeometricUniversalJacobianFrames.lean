import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Proposal.GeometricVariation
import Proposal.IncidenceBasepointCharts
import Proposal.IncidenceKodairaSpencerMap

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

noncomputable section

namespace CycleQ2PolynomialPoleSymbols
open MvPolynomial
section
variable (K : Type*) [CommRing K]

/-- The summand at n denotes n! times the form at pole order n+1. -/
abbrev Poles := ℕ →₀ MvPolynomial (Fin 5) K

/-- Normalized polynomial pole relations for the five partial derivatives. -/
def relations (F : MvPolynomial (Fin 5) K) : Submodule K (Poles K) := Submodule.span K
  {z | ∃ (n : ℕ) (i : Fin 5) (G : MvPolynomial (Fin 5) K),
    z = Finsupp.single (n+1) (G * pderiv i F) - Finsupp.single n (pderiv i G)}

abbrev Symbols (F : MvPolynomial (Fin 5) K) := Poles K ⧸ relations K F

/-- A normalized homogeneous polynomial pole, indexed by the pole order minus one. -/
def symbol (F : MvPolynomial (Fin 5) K) (n : ℕ) : MvPolynomial (Fin 5) K →ₗ[K] Symbols K F :=
  (relations K F).mkQ.comp (Finsupp.lsingle n)

theorem divergence (F : MvPolynomial (Fin 5) K) (n : ℕ) (i : Fin 5) (G : MvPolynomial (Fin 5) K) :
    symbol K F (n+1) (G * pderiv i F) = symbol K F n (pderiv i G) := by
  apply sub_eq_zero.mp
  change (relations K F).mkQ (Finsupp.single (n+1) (G * pderiv i F)) -
      (relations K F).mkQ (Finsupp.single n (pderiv i G)) = 0
  rw [← map_sub, Submodule.mkQ_apply,Submodule.Quotient.mk_eq_zero]
  exact Submodule.subset_span ⟨n,i,G,rfl⟩

end

/-- Multiplying by the equation and raising the pole yields the same
homogeneous pole, with the factorial ratio coming from normalization. -/
theorem multiply_equation (K : Type*) [Field K] [CharZero K] (F P : MvPolynomial (Fin 5) K) (w : Fin 5 → ℕ)
    (d n : ℕ) (hd : d ≠ 0) (hw : ∑ i, w i = d)
    (hF : F.IsWeightedHomogeneous w d) (hP : P.IsWeightedHomogeneous w (d*n)) :
    symbol K F (n+1) (F*P) = (n+1) • symbol K F n P := by
  have hleft : ∑ i, w i • ((X i * P) * pderiv i F) = d • (F*P) := by
    rw [← smul_mul_assoc,← hF.sum_weight_X_mul_pderiv,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [smul_mul_assoc]
    congr 1
    ring
  have hright : ∑ i, w i • (pderiv i (X i * P)) = (d*n+d) • P := by
    simp_rw [Derivation.leibniz,pderiv_X_self,smul_eq_mul,mul_one,smul_add]
    rw [Finset.sum_add_distrib,hP.sum_weight_X_mul_pderiv,← Finset.sum_smul,hw,add_smul]
  have eq : d • symbol K F (n+1) (F*P) = (d*n+d) • symbol K F n P := by
    calc
      _ = symbol K F (n+1) (∑ i, w i • ((X i * P) * pderiv i F)) := by rw [hleft,map_nsmul]
      _ = symbol K F n (∑ i, w i • (pderiv i (X i * P))) := by simp only [map_sum,map_nsmul,divergence]
      _ = _ := by rw [hright,map_nsmul]
  apply smul_right_injective (M := Symbols K F) (show (d : K) ≠ 0 by exact_mod_cast hd)
  simpa only [Nat.cast_smul_eq_nsmul,smul_smul,Nat.mul_add,Nat.mul_one] using eq

end CycleQ2PolynomialPoleSymbols

namespace CycleQ2PolynomialPoleSymbols

open MvPolynomial CycleQ2PolynomialCoefficientDerivation

variable {k K : Type*} [CommRing k] [CommRing K] [Algebra k K]
    (D : Derivation k K K) (F : MvPolynomial (Fin 5) K)

private abbrev dP := coefficientDerivation (σ := Fin 5) D

private theorem deriv_partial (i : Fin 5) (P : MvPolynomial (Fin 5) K) :
    dP D (pderiv i P) = pderiv i (dP D P) := by
  induction P using MvPolynomial.induction_on' with
  | monomial a c =>
    simp only [pderiv_monomial, dP, coefficientDerivation_monomial, D.leibniz,
      D.map_natCast, smul_eq_mul, mul_zero, zero_add, mul_comm]
  | add p q hp hq => simp only [map_add, hp, hq]

private def rawD : Poles K →+ Symbols K F :=
  Finsupp.liftAddHom fun n =>
    (symbol K F n).toAddMonoidHom.comp (dP D).toAddMonoidHom -
      (symbol K F (n+1)).toAddMonoidHom.comp (AddMonoidHom.mulLeft (dP D F))

private theorem rawD_single (n : ℕ) (P : MvPolynomial (Fin 5) K) :
    rawD D F (Finsupp.single n P) =
      symbol K F n (dP D P) - symbol K F (n+1) (dP D F * P) := by
  rw [rawD, Finsupp.liftAddHom_apply_single]
  rfl

private theorem rawD_smul (a : K) (x : Poles K) :
    rawD D F (a • x) = a • rawD D F x + D a • (relations K F).mkQ x := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]; abel
  | single n P =>
    have h : dP D (a • P) = a • dP D P + D a • P := by
      rw [smul_eq_C_mul, (dP D).leibniz, dP, coefficientDerivation_C,
        smul_eq_mul, smul_eq_mul, mul_comm P, ← smul_eq_C_mul, ← smul_eq_C_mul]
    rw [Finsupp.smul_single, rawD_single, h, mul_smul_comm, map_add, map_smul,
      map_smul, map_smul, rawD_single, smul_sub]
    change _ = _ + D a • symbol K F n P
    abel

private theorem rawD_relation (n : ℕ) (i : Fin 5) (G : MvPolynomial (Fin 5) K) :
    rawD D F (Finsupp.single (n+1) (G * pderiv i F) - Finsupp.single n (pderiv i G)) = 0 := by
  let m := dP D F
  have h : dP D (G * pderiv i F) = dP D G * pderiv i F + G * pderiv i m := by
    rw [(dP D).leibniz, deriv_partial]
    simp only [m, smul_eq_mul]; ring
  have h' : symbol K F ((n+1)+1) (m * (G * pderiv i F)) =
      symbol K F (n+1) (m * pderiv i G) + symbol K F (n+1) (G * pderiv i m) := by
    rw [← mul_assoc,divergence,(pderiv i).leibniz,smul_eq_mul,smul_eq_mul,map_add]
  rw [map_sub, rawD_single, rawD_single, h, deriv_partial, map_add, divergence]
  change _ - symbol K F ((n+1)+1) (m * (G * pderiv i F)) - _ = 0
  rw [h']
  dsimp only [m]
  abel

private theorem rawD_kills : (relations K F).toAddSubgroup ≤ (rawD D F).ker := by
  intro x hx
  change x ∈ relations K F at hx
  change rawD D F x = 0
  induction hx using Submodule.span_induction with
  | mem y hy => obtain ⟨n,i,G,rfl⟩ := hy; exact rawD_relation D F n i G
  | zero => exact map_zero _
  | add x y _ _ hx hy => simp [hx,hy]
  | smul a x hx h =>
    have hq : (relations K F).mkQ x = 0 := Submodule.Quotient.mk_eq_zero _ |>.mpr hx
    rw [rawD_smul,hq,h,smul_zero,smul_zero,add_zero]

/-- The coefficient connection on normalized polynomial pole classes.
Both summands use the actual coefficientwise derivative on polynomials. -/
def connection : Symbols K F →+ Symbols K F :=
  QuotientAddGroup.lift (relations K F).toAddSubgroup (rawD D F) (rawD_kills D F)

theorem connection_symbol (n : ℕ) (P : MvPolynomial (Fin 5) K) :
    connection D F (symbol K F n P) =
      symbol K F n (coefficientDerivation D P) -
      symbol K F (n+1) (coefficientDerivation D F * P) := rawD_single D F n P

theorem connection_smul (a : K) (x : Symbols K F) :
    connection D F (a • x) = a • connection D F x + D a • x :=
  Submodule.Quotient.induction_on _ x (fun y => rawD_smul D F a y)

end CycleQ2PolynomialPoleSymbols

namespace CycleQ2PolynomialPoleSymbols

open MvPolynomial CycleQ2PolynomialCoefficientDerivation

variable {k K : Type*} [CommRing k] [CommRing K] [Algebra k K]
    (D : Derivation k K K) (F P : MvPolynomial (Fin 5) K)

/-- Repeated differentiation in a linear coefficient direction raises the
normalized pole at each step and multiplies the numerator by the direction. -/
theorem iterate_connection_symbol (n : ℕ) (hP : coefficientDerivation D P = 0)
    (hF : coefficientDerivation D (coefficientDerivation D F) = 0) (r : ℕ) :
    (connection D F)^[r] (symbol K F n P) =
      (-1 : K)^r • symbol K F (n+r) ((coefficientDerivation D F)^r * P) := by
  induction r with
  | zero => simp
  | succ r ih =>
    let m := coefficientDerivation D F
    have hm : coefficientDerivation D (m^r * P) = 0 := by
      rw [Derivation.leibniz, hP, Derivation.leibniz_pow, hF]
      simp
    rw [Function.iterate_succ_apply', ih, connection_smul, connection_symbol, hm, map_zero, zero_sub]
    simp only [Derivation.leibniz_pow, map_neg, Derivation.map_one_eq_zero, neg_zero,
      smul_zero, zero_smul, add_zero, smul_neg, Nat.add_succ, pow_succ, mul_neg_one, neg_smul]
    rw [mul_left_comm, mul_assoc]

section Specialization

variable {L : Type*} [CommRing L] (θ : K →+* L) (F : MvPolynomial (Fin 5) K)

private def pushPoles :
    Poles K →+ Symbols L (MvPolynomial.map θ F) :=
  Finsupp.liftAddHom fun n =>
    (symbol L (MvPolynomial.map θ F) n).toAddMonoidHom.comp (MvPolynomial.map θ).toAddMonoidHom

private theorem pushPoles_single (n : ℕ) (P : MvPolynomial (Fin 5) K) :
    pushPoles θ F (Finsupp.single n P) =
      symbol L (MvPolynomial.map θ F) n (MvPolynomial.map θ P) := by
  rw [pushPoles, Finsupp.liftAddHom_apply_single]
  rfl

private theorem pushPoles_smul (a : K) (x : Poles K) :
    pushPoles θ F (a • x) = θ a • pushPoles θ F x := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [smul_add,map_add,hx,hy]
  | single n P =>
    rw [Finsupp.smul_single, pushPoles_single, pushPoles_single, smul_eq_C_mul,
      map_mul, map_C, ← smul_eq_C_mul, map_smul]

private theorem pushPoles_kills :
    (relations K F).toAddSubgroup ≤ (pushPoles θ F).ker := by
  intro x hx
  change x ∈ relations K F at hx
  change pushPoles θ F x = 0
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨n, i, G, rfl⟩ := hy
    rw [map_sub, pushPoles_single, pushPoles_single,map_mul, ← pderiv_map, ← pderiv_map,
      divergence, sub_self]
  | zero => exact map_zero _
  | add x y _ _ hx hy => simp [hx,hy]
  | smul a x _ hx => rw [pushPoles_smul,hx,smul_zero]

/-- Change coefficients in the defining equation and every polynomial
numerator of the normalized symbols. -/
def specialize : Symbols K F →ₛₗ[θ] Symbols L (MvPolynomial.map θ F) where
  __ := QuotientAddGroup.lift (relations K F).toAddSubgroup (pushPoles θ F) (pushPoles_kills θ F)
  map_smul' a x := Submodule.Quotient.induction_on _ x (fun y => pushPoles_smul θ F a y)

theorem specialize_symbol (n : ℕ) (P : MvPolynomial (Fin 5) K) :
    specialize θ F (symbol K F n P) =
      symbol L (MvPolynomial.map θ F) n (MvPolynomial.map θ P) := pushPoles_single θ F n P

theorem specialize_iterate (n r : ℕ)
    (hP : coefficientDerivation D P = 0)
    (hF : coefficientDerivation D (coefficientDerivation D F) = 0) :
    specialize θ F ((connection D F)^[r] (symbol K F n P)) =
      (-1 : L)^r • symbol L (MvPolynomial.map θ F) (n+r)
        ((MvPolynomial.map θ (coefficientDerivation D F))^r * MvPolynomial.map θ P) := by
  rw [iterate_connection_symbol D F P n hP hF r, map_smulₛₗ, specialize_symbol]
  simp only [map_pow, map_neg, map_one, map_mul]

end Specialization
end CycleQ2PolynomialPoleSymbols

namespace CycleQ2PolynomialPoleSymbols

open MvPolynomial CycleQ2PolynomialCoefficientDerivation CycleQ2IncidenceNormalForm

variable (R : Type*) [CommRing R]

abbrev TailRing := MvPolynomial FullSexticTailIndex R

/-- The universal family on the monic sextic coefficient chart. -/
abbrev monicFamily : MvPolynomial (Fin 5) (TailRing R) :=
  normalizedFullSextic (fun e => X e)

/-- The velocity of the universal family in a monic tail coordinate. -/
theorem monic_velocity (a : FullSexticTailIndex) :
    coefficientDerivation (pderiv a) (monicFamily R) = monomial (fullExponentOf a.val.val) 1 := by
  classical
  simp only [monicFamily, normalizedFullSextic, map_add, map_sum, coefficientDerivation_monomial,
    Derivation.map_one_eq_zero, map_zero, zero_add]
  rw [Finset.sum_eq_single a]
  · rw [pderiv_X_self]
  · intro j _ hja
    rw [pderiv_X_of_ne hja,map_zero]
  · simp

variable {L : Type*} [CommRing L]

/-- Coordinate derivatives of a fixed numerator followed by arbitrary base change. -/
theorem specialize_monic_iterate (θ : TailRing R →+* L) (a : FullSexticTailIndex)
    (s : Fin 5 →₀ ℕ) (n r : ℕ) :
    specialize θ (monicFamily R)
      ((connection (pderiv a) (monicFamily R))^[r]
        (symbol (TailRing R) (monicFamily R) n (monomial s 1))) =
      (-1 : L)^r • symbol L (MvPolynomial.map θ (monicFamily R)) (n+r)
        (monomial (r • fullExponentOf a.val.val + s) 1) := by
  rw [specialize_iterate (pderiv a), monic_velocity]
  · simp only [map_monomial,map_one,monomial_pow,one_pow,monomial_mul,one_mul]
  · simp only [coefficientDerivation_monomial,Derivation.map_one_eq_zero,map_zero]
  · rw [monic_velocity]
    simp only [coefficientDerivation_monomial,Derivation.map_one_eq_zero,map_zero]

/-- Use the actual coefficients of a monic homogeneous sextic to evaluate the parameter ring. -/
def monicEvaluation (t : R →+* L) (G : MvPolynomial (Fin 5) L) : TailRing R →+* L :=
  eval₂Hom t (fun a => G.coeff (fullExponentOf a.val.val))

theorem map_monicFamily (t : R →+* L) (G : MvPolynomial (Fin 5) L)
    (hG : G.IsWeightedHomogeneous fullGrading (6,0)) (h1 : G.coeff (Finsupp.single 4 3) = 1) :
    MvPolynomial.map (monicEvaluation R t G) (monicFamily R) = G := by
  rw [monicFamily,CycleQ2UniversalSurfaceCoefficientMap.map_sextic]
  have h := fullInvariantPolynomial_of_homogeneous hG
  rw [fullInvariantPolynomial_sextic, fullSexticLeadingIndex_exponent, h1] at h
  simpa only [monicEvaluation,eval₂Hom_X', normalizedFullSextic, rawFullSextic] using h

end CycleQ2PolynomialPoleSymbols

namespace CycleQ2UniversalPoleFrame
open MvPolynomial CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations
open CycleQ2HiggsJacobianFrames
open CycleQ2GenericSexticGradient (CoeffRing universalF)
open CycleQ2FermatJacobian (cutoff derivativeScalar)
open CycleQ2PolynomialPoleSymbols (Symbols symbol divergence)

variable {K : Type} [CommRing K] (φ : CoeffRing →+* K)
abbrev equation := MvPolynomial.map φ universalF
abbrev pole (s : ℕ) := symbol K (equation φ) s

def boundedPoles (s n : ℕ) : Submodule K (Symbols K (equation φ)) :=
  Submodule.span K (Set.range fun e : Bounded n 1 => pole φ s (monomial (exp e.val) 1))

def homogeneousPoles (s n : ℕ) : Submodule K (Symbols K (equation φ)) :=
  (weightedHomogeneousSubmodule K fullGrading (n,(1:ZMod 3))).map (pole φ s)

private theorem derivative_multiplier {n : ℕ} {j : Index (n+6) 1} (h : ¬Standard j) (c : K) :
    HG (pderiv (pivot h) (monomial (exp j - Finsupp.single (pivot h) (cutoff (pivot h))) c)) (n,1) := by
  let i := pivot h
  let a := exp j - Finsupp.single i (cutoff i)
  have hw : Finsupp.weight fullGrading a + (6 - (fullGrading i).1, -(fullGrading i).2) = (n+6,1) := by
    rw [← cutoff_weight,← map_add,tsub_add_cancel_of_le (pivot_le h)]
    exact j.property
  apply (isWeightedHomogeneous_monomial fullGrading a c rfl).pderiv
  have small (j : Fin 5) : (fullGrading j).1 ≤ 6 := by fin_cases j <;> decide
  have hi := small i
  apply Prod.ext
  · have hn := congrArg Prod.fst hw
    change (Finsupp.weight fullGrading a).1 + (6-(fullGrading i).1) = n+6 at hn
    change n + (fullGrading i).1 = (Finsupp.weight fullGrading a).1
    omega
  · have hc := congrArg Prod.snd hw
    change (Finsupp.weight fullGrading a).2 + -(fullGrading i).2 = 1 at hc
    change 1 + (fullGrading i).2 = (Finsupp.weight fullGrading a).2
    rw [← hc]; abel

theorem lower_pole (s n : ℕ) (hd : IsUnit (φ (frameDet (n+6) 1))) :
    homogeneousPoles φ (s+1) (n+6) ≤ boundedPoles φ (s+1) (n+6) ⊔ homogeneousPoles φ s n := by
  classical
  rintro _ ⟨P,hP,rfl⟩
  obtain ⟨c,hc⟩ := exists_column_expansion φ hd P hP
  rw [← hc,map_sum]
  apply Submodule.sum_mem
  intro j _
  rw [map_smul]
  apply Submodule.smul_mem
  by_cases h : Standard j
  · apply Submodule.mem_sup_left
    apply Submodule.subset_span
    refine ⟨⟨j,h⟩,?_⟩
    simp [column,h]
  · apply Submodule.mem_sup_right
    let i := pivot h
    let a := exp j - Finsupp.single i (cutoff i)
    let u : K := φ (C (derivativeScalar i)⁻¹)
    let G := monomial a u
    refine ⟨pderiv i G,derivative_multiplier h u,?_⟩
    have he : MvPolynomial.map φ (column j) = G * pderiv i (equation φ) := by
      simp only [column,dif_neg h,map_mul,map_monomial,← pderiv_map]
      rfl
    rw [he]
    exact (divergence K (equation φ) s i G).symm

private theorem empty_degree_zero (e : Index 0 1) : False := by
  have h := (CycleQ2GeometricHiggsGradedIndices.weight_eq_iff (exp e) _ _).mp e.property
  have hz (i : Fin 5) : exp e i = 0 := by
    rw [exp,fullExponentOf_apply]
    omega
  have hc := h.2
  rw [show (1 : ZMod 3).val = 1 by decide] at hc
  norm_num [CycleQ2FermatHiggs.character,hz] at hc

private theorem empty_standard_top (j : Bounded 18 1) : False := by
  have hw := (CycleQ2GeometricHiggsGradedIndices.weight_eq_iff (exp j.val) _ _).mp j.val.property
  have hb (i : Fin 5) := j.property i
  have h0 : exp j.val 0 < 5 := hb 0
  have h1 : exp j.val 1 < 5 := hb 1
  have h2 : exp j.val 2 < 5 := hb 2
  have h3 : exp j.val 3 < 5 := hb 3
  have h4 : exp j.val 4 < 2 := hb 4
  have hn := hw.1
  change exp j.val 0 + exp j.val 1 + exp j.val 2 + exp j.val 3 + 2 * exp j.val 4 = 18 at hn
  have hc := hw.2
  rw [show (1 : ZMod 3).val = 1 by decide] at hc
  change (2*exp j.val 0 + 2*exp j.val 1 + exp j.val 2) % 3 = 1 at hc
  have e0 : exp j.val 0 = 4 := by omega
  have e1 : exp j.val 1 = 4 := by omega
  have e2 : exp j.val 2 = 4 := by omega
  norm_num [e0,e1,e2] at hc

private theorem no_degree_zero (s : ℕ) : homogeneousPoles φ s 0 ≤ ⊥ := by
  rintro _ ⟨P,hP,rfl⟩
  have hP' : P = 0 := by
    ext a
    rw [coeff_zero]
    by_contra h
    exact empty_degree_zero (exists_index a (hP h)).choose
  simp [hP']

private theorem no_standard_top (s : ℕ) : boundedPoles φ s 18 ≤ ⊥ :=
  Submodule.span_le.mpr (by rintro _ ⟨j,rfl⟩; exact (empty_standard_top j).elim)

def frame : Submodule K (Symbols K (equation φ)) := boundedPoles φ 1 6 ⊔ boundedPoles φ 2 12

/-- Every residue numerator of pole two, three or four and character one reduces
to the standard 33 upper and 33 lower labels in the normalized pole quotient. -/
theorem reductions
    (h6 : IsUnit (φ (frameDet 6 1))) (h12 : IsUnit (φ (frameDet 12 1)))
    (h18 : IsUnit (φ (frameDet 18 1))) :
    homogeneousPoles φ 1 6 ≤ frame φ ∧ homogeneousPoles φ 2 12 ≤ frame φ ∧
      homogeneousPoles φ 3 18 ≤ frame φ := by
  have h₁ : homogeneousPoles φ 1 6 ≤ frame φ := (lower_pole φ 0 0 h6).trans (sup_le le_sup_left ((no_degree_zero φ 0).trans bot_le))
  have h₂ : homogeneousPoles φ 2 12 ≤ frame φ := (lower_pole φ 1 6 h12).trans (sup_le le_sup_right h₁)
  exact ⟨h₁,h₂,(lower_pole φ 2 12 h18).trans (sup_le ((no_standard_top φ 3).trans bot_le) h₂)⟩

open CycleQ2GeometricHiggsGradedIndices (upperIndex lowerIndex)

abbrev Label := Fin 33 ⊕ Fin 33

def basisSymbol : Label → Symbols K (equation φ)
  | .inl i => pole φ 1 (monomial (exp (upperIndex i).val) 1)
  | .inr i => pole φ 2 (monomial (exp (lowerIndex i).val) 1)

def realize := Finsupp.linearCombination K (basisSymbol φ)

theorem frame_eq_range : frame φ = LinearMap.range (realize φ) := by
  rw [realize,Finsupp.range_linearCombination]
  apply le_antisymm
  · refine sup_le (Submodule.span_le.mpr ?_) (Submodule.span_le.mpr ?_)
    · rintro _ ⟨e,rfl⟩
      obtain ⟨i,rfl⟩ := upperIndex.surjective e
      exact Submodule.subset_span (Set.mem_range_self (f := basisSymbol φ) (Sum.inl i))
    · rintro _ ⟨e,rfl⟩
      obtain ⟨i,rfl⟩ := lowerIndex.surjective e
      exact Submodule.subset_span (Set.mem_range_self (f := basisSymbol φ) (Sum.inr i))
  · apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    cases i with
    | inl i => exact Submodule.mem_sup_left (Submodule.subset_span (Set.mem_range_self (upperIndex i)))
    | inr i => exact Submodule.mem_sup_right (Submodule.subset_span (Set.mem_range_self (lowerIndex i)))

/-- Differentiating a constant numerator raises the pole by one and multiplies
it by minus the variation of the defining sextic, in normalized coordinates. -/
def raised (m : Poly K) : Label → Symbols K (equation φ)
  | .inl i => -pole φ 2 (m * monomial (exp (upperIndex i).val) 1)
  | .inr i => -pole φ 3 (m * monomial (exp (lowerIndex i).val) 1)

/-- Every invariant sextic direction has a matrix over the very same coefficient
ring as the three unit minors. Its columns give the specified polynomial symbols. -/
theorem exists_matrix (h6 : IsUnit (φ (frameDet 6 1))) (h12 : IsUnit (φ (frameDet 12 1)))
    (h18 : IsUnit (φ (frameDet 18 1))) (m : Poly K) (hm : HG m (6,0)) :
    ∃ A : Label → (Label →₀ K), ∀ i, realize φ (A i) = raised φ m i := by
  have h := reductions φ h6 h12 h18
  have col (i : Label) : raised φ m i ∈ LinearMap.range (realize φ) := by
    rw [← frame_eq_range]
    cases i with
    | inl i =>
      apply Submodule.neg_mem
      apply h.2.1
      refine ⟨_,?_,rfl⟩
      exact hm.mul (isWeightedHomogeneous_monomial fullGrading _ _ (upperIndex i).val.property)
    | inr i =>
      apply Submodule.neg_mem
      apply h.2.2
      refine ⟨_,?_,rfl⟩
      exact hm.mul (isWeightedHomogeneous_monomial fullGrading _ _ (lowerIndex i).val.property)
  exact ⟨fun i => (col i).choose,fun i => (col i).choose_spec⟩

def protectedNumerator : Poly K := X 0^2 * X 1^2 * X 2^2 * X 3^2 * X 4^2

theorem protected_homogeneous : HG (protectedNumerator (K := K)) (12,1) := by
  unfold protectedNumerator
  let h (i : Fin 5) := (isWeightedHomogeneous_X (R := K) fullGrading i).pow 2
  exact ((((h 0).mul (h 1)).mul (h 2)).mul (h 3)).mul (h 4)

theorem protected_in_frame (h6 : IsUnit (φ (frameDet 6 1))) (h12 : IsUnit (φ (frameDet 12 1)))
    (h18 : IsUnit (φ (frameDet 18 1))) :
    ∃ x : Label →₀ K, realize φ x = pole φ 2 protectedNumerator := by
  apply (frame_eq_range φ).le
  exact (reductions φ h6 h12 h18).2.1 ⟨_,protected_homogeneous,rfl⟩

end CycleQ2UniversalPoleFrame

end

#print axioms CycleQ2PolynomialPoleSymbols.specialize_monic_iterate
#print axioms CycleQ2UniversalPoleFrame.exists_matrix
#print axioms CycleQ2UniversalPoleFrame.protected_in_frame
