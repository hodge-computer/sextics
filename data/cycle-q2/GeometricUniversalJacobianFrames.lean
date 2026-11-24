import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.RingTheory.Localization.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.Algebra.Module.NatInt
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.LinearAlgebra.Matrix.ToLin
import HodgeComputer.Constructions.ResidueTransport.CoordinateIndependence
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

/-!
# Differential ideals on the coefficient open

An ideal in a characteristic-zero polynomial ring that is preserved by all
coordinate partials is either zero or the whole ring. Clearing one denominator
extends this fact to every localization. For a submodule preserved by a regular
connection, the ideal generated by its coordinates is preserved by the same
coefficient derivations. Consequently, if all of its vectors specialize to zero
at one point, the submodule is zero. This last argument does not need finite
generation or a choice of a generic basis.
-/

noncomputable section
namespace CycleQ2DifferentialCoefficientIdeals

open MvPolynomial

section Polynomial

variable {k σ : Type*} [Field k] [CharZero k] [Fintype σ] [DecidableEq σ]

/-- Degree descent forces a nonzero ideal stable under every coordinate partial
to contain a nonzero constant, and hence to contain one. -/
theorem polynomial_eq_top (I : Ideal (MvPolynomial σ k)) (hI : I ≠ ⊥)
    (stable : ∀ i p, p ∈ I → pderiv i p ∈ I) : I = ⊤ := by
  classical
  by_contra htop
  have hz : ∀ p : MvPolynomial σ k, p ∈ I → p = 0 := by
    intro p
    induction hn : p.totalDegree using Nat.strong_induction_on generalizing p with
    | h n ih =>
      intro hp
      have hconst : p = C (coeff 0 p) := by
        by_cases hn0 : n = 0
        · exact totalDegree_eq_zero_iff_eq_C.mp (hn.trans hn0)
        · apply ResidueCoordinateIndependence.constant_of_partials_zero
          intro i
          apply ih (pderiv i p).totalDegree
          · rw [← hn]
            exact ResidueCoordinateIndependence.pderiv_degree_lt p i (by omega)
          · rfl
          · exact stable i p hp
      have hc : coeff 0 p = 0 := by
        by_contra hc
        apply htop
        apply (Ideal.eq_top_iff_one I).mpr
        have hcp : C (coeff 0 p) ∈ I := hconst ▸ hp
        have hunit := I.mul_mem_left (C ((coeff 0 p)⁻¹)) hcp
        simpa only [← map_mul, inv_mul_cancel₀ hc, map_one] using hunit
      rw [hconst, hc, map_zero]
  obtain ⟨p, hp, hp0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  exact hp0 (hz p hp)

/-- A nonzero differential ideal in a localization contracts to a nonzero
differential ideal of the polynomial ring. No restriction is imposed on the
denominator submonoid. -/
theorem localization_eq_top
    (M : Submonoid (MvPolynomial σ k)) (S : Type*) [CommRing S]
    [Algebra (MvPolynomial σ k) S] [IsLocalization M S]
    (D : σ → Derivation ℤ S S)
    (compatible : ∀ i p, D i (algebraMap (MvPolynomial σ k) S p) =
      algebraMap (MvPolynomial σ k) S (pderiv i p))
    (I : Ideal S) (hI : I ≠ ⊥)
    (stable : ∀ i x, x ∈ I → D i x ∈ I) : I = ⊤ := by
  let J := I.comap (algebraMap (MvPolynomial σ k) S)
  obtain ⟨z, hz, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  obtain ⟨p, s, rfl⟩ := IsLocalization.exists_mk'_eq M z
  have hp : p ∈ J := by
    change algebraMap (MvPolynomial σ k) S p ∈ I
    rw [← IsLocalization.mk'_spec S p s]
    exact I.mul_mem_right _ hz
  have hp0 : p ≠ 0 := by
    intro h
    subst p
    exact hz0 (IsLocalization.mk'_zero s)
  have hJ : J ≠ ⊥ := by
    intro h
    exact hp0 (by simpa only [h, Submodule.mem_bot] using hp)
  have htop : J = ⊤ := polynomial_eq_top J hJ (by
    intro i q hq
    change algebraMap (MvPolynomial σ k) S (pderiv i q) ∈ I
    rw [← compatible]
    exact stable i _ hq)
  exact Ideal.comap_eq_top_iff.mp htop

end Polynomial

section Coordinates

variable {R ι σ : Type*} [CommRing R] [Fintype ι]

/-- All coordinates of all vectors of a submodule, without selecting generators. -/
def coordinateIdeal (N : Submodule R (ι → R)) : Ideal R :=
  Ideal.span (Set.range fun x : N × ι => x.1.val x.2)

theorem coordinate_mem (N : Submodule R (ι → R)) {v : ι → R}
    (hv : v ∈ N) (j : ι) : v j ∈ coordinateIdeal N :=
  Ideal.subset_span ⟨(⟨v, hv⟩, j), rfl⟩

/-- If `D + B` preserves a submodule, `D` preserves its coordinate ideal. -/
theorem coordinateIdeal_stable (D : Derivation ℤ R R) (B : Matrix ι ι R)
    (N : Submodule R (ι → R))
    (stable : ∀ v ∈ N, (fun j => D (v j) + B.mulVec v j) ∈ N)
    (x : R) (hx : x ∈ coordinateIdeal N) : D x ∈ coordinateIdeal N := by
  classical
  have hgen (v : ι → R) (hv : v ∈ N) (j : ι) : D (v j) ∈ coordinateIdeal N := by
    have hB : B.mulVec v j ∈ coordinateIdeal N := by
      change (∑ l, B j l * v l) ∈ coordinateIdeal N
      exact (coordinateIdeal N).sum_mem fun l _ =>
        (coordinateIdeal N).mul_mem_left _ (coordinate_mem N hv l)
    have hw := coordinate_mem N (stable v hv) j
    have h := (coordinateIdeal N).sub_mem hw hB
    simpa only [add_sub_cancel_right] using h
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨⟨v, j⟩, rfl⟩ := hy
    exact hgen v.val v.property j
  | zero => simpa only [map_zero] using (coordinateIdeal N).zero_mem
  | add x y _ _ hx hy =>
    rw [map_add]
    exact (coordinateIdeal N).add_mem hx hy
  | smul a x hx h =>
    change D (a * x) ∈ coordinateIdeal N
    rw [D.leibniz]
    exact (coordinateIdeal N).add_mem
      ((coordinateIdeal N).smul_mem a h)
      ((coordinateIdeal N).mul_mem_right (D a) hx)

/-- Over a differentially simple coefficient ring, a connection-stable
submodule of a finite free module cannot have every coordinate vanish at a
single field-valued point unless the submodule itself is zero. -/
theorem eq_bot_of_specializes_zero
    (D : σ → Derivation ℤ R R)
    (simple : ∀ I : Ideal R, I ≠ ⊥ →
      (∀ i x, x ∈ I → D i x ∈ I) → I = ⊤)
    (B : σ → Matrix ι ι R) (N : Submodule R (ι → R))
    (stable : ∀ i v, v ∈ N → (fun j => D i (v j) + (B i).mulVec v j) ∈ N)
    {L : Type*} [CommRing L] [Nontrivial L] (ρ : R →+* L)
    (vanishes : ∀ v ∈ N, ∀ j, ρ (v j) = 0) : N = ⊥ := by
  have hker : coordinateIdeal N ≤ RingHom.ker ρ := by
    apply Ideal.span_le.mpr
    rintro _ ⟨⟨v, j⟩, rfl⟩
    exact vanishes v.val v.property j
  have hzero : coordinateIdeal N = ⊥ := by
    by_contra hn
    have htop := simple (coordinateIdeal N) hn
      (fun i x hx => coordinateIdeal_stable (D i) (B i) N (stable i) x hx)
    have h1 : (1 : R) ∈ coordinateIdeal N := by rw [htop]; trivial
    have hbad : ρ 1 = 0 := hker h1
    exact one_ne_zero (by simpa only [map_one] using hbad)
  apply le_antisymm _ bot_le
  intro v hv
  apply Submodule.mem_bot.mpr
  funext j
  have hj := coordinate_mem N hv j
  simpa only [hzero, Submodule.mem_bot] using hj

end Coordinates
end CycleQ2DifferentialCoefficientIdeals
end

#print axioms CycleQ2DifferentialCoefficientIdeals.polynomial_eq_top
#print axioms CycleQ2DifferentialCoefficientIdeals.localization_eq_top
#print axioms CycleQ2DifferentialCoefficientIdeals.coordinateIdeal_stable
#print axioms CycleQ2DifferentialCoefficientIdeals.eq_bot_of_specializes_zero

noncomputable section
namespace CycleQ2UniversalPoleFrame

open MvPolynomial CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations
open CycleQ2GenericSexticGradient (CoeffRing universalF)
open CycleQ2HiggsJacobianFrames (frameDet)
open CycleQ2PolynomialCoefficientDerivation
open CycleQ2PolynomialPoleSymbols (Symbols connection connection_symbol connection_smul specialize)

variable {R : Type} [CommRing R] (φ : CoeffRing →+* R)

/-- The same 66-symbol realization, written on coordinate vectors so that
its regular connection can be expressed by ordinary matrices. -/
def vectorRealize : (Label → R) →ₗ[R] Symbols R (equation φ) where
  toFun v := ∑ i, v i • basisSymbol φ i
  map_add' v w := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' a v := by
    simp only [Pi.smul_apply, RingHom.id_apply, Finset.smul_sum, smul_smul]

theorem realize_eq_vectorRealize (v : Label →₀ R) :
    realize φ v = vectorRealize φ v := by
  simp only [realize, Finsupp.linearCombination_apply, Finsupp.sum_fintype,
    zero_smul, vectorRealize, LinearMap.coe_mk, AddHom.coe_mk]

theorem coefficient_velocity_homogeneous (D : Derivation ℤ R R) :
    HG (coefficientDerivation D (equation φ)) (6, 0) := by
  have h (c : FullInvariantIndex 6 → R) :
      coefficientDerivation D (fullInvariantPolynomial 6 c) =
        fullInvariantPolynomial 6 (fun i => D (c i)) := by
    unfold fullInvariantPolynomial
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => coefficientDerivation_monomial D _ _
  rw [equation, universalF, map_fullInvariantPolynomial, h]
  exact fullInvariantPolynomial_homogeneous _ _

theorem connection_basisSymbol (D : Derivation ℤ R R) (i : Label) :
    connection D (equation φ) (basisSymbol φ i) =
      raised φ (coefficientDerivation D (equation φ)) i := by
  cases i <;>
    simp [basisSymbol, raised, pole, connection_symbol, coefficientDerivation_monomial]

/-- Pole reduction constructs a regular connection matrix on the coordinate
module before asserting independence of the symbols. The actual quotient
connection intertwines with this matrix on every vector. -/
theorem exists_vector_connection
    (h6 : IsUnit (φ (frameDet 6 1))) (h12 : IsUnit (φ (frameDet 12 1)))
    (h18 : IsUnit (φ (frameDet 18 1))) (D : Derivation ℤ R R) :
    ∃ B : Matrix Label Label R, ∀ v : Label → R,
      vectorRealize φ (fun i => D (v i) + B.mulVec v i) =
        connection D (equation φ) (vectorRealize φ v) := by
  classical
  obtain ⟨A, hA⟩ := exists_matrix φ h6 h12 h18
    (coefficientDerivation D (equation φ)) (coefficient_velocity_homogeneous φ D)
  let B : Matrix Label Label R := fun i j => A j i
  have hcol (j : Label) : vectorRealize φ (fun i => B i j) =
      connection D (equation φ) (basisSymbol φ j) := by
    exact (realize_eq_vectorRealize φ (A j)).symm.trans
      ((hA j).trans (connection_basisSymbol φ D j).symm)
  have hB (v : Label → R) : vectorRealize φ (B.mulVec v) =
      ∑ j, v j • connection D (equation φ) (basisSymbol φ j) := by
    change (∑ i, (∑ j, B i j * v j) • basisSymbol φ i) = _
    simp only [Finset.sum_smul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [← hcol j]
    change (∑ i, (B i j * v j) • basisSymbol φ i) =
      v j • (∑ i, B i j • basisSymbol φ i)
    simp only [Finset.smul_sum, smul_smul, mul_comm]
  refine ⟨B, fun v => ?_⟩
  change vectorRealize φ ((fun i => D (v i)) + B.mulVec v) = _
  rw [map_add, hB]
  change (∑ i, D (v i) • basisSymbol φ i) +
    (∑ i, v i • connection D (equation φ) (basisSymbol φ i)) =
      connection D (equation φ) (∑ i, v i • basisSymbol φ i)
  simp only [map_sum, connection_smul, Finset.sum_add_distrib, add_comm]

/-- A single independent specialization rules out every kernel vector of
the regular polynomial-pole frame on a differentially simple coefficient
open. The construction of the connection matrices does not use the conclusion. -/
theorem vectorRealize_injective_of_specialized_independent
    (h6 : IsUnit (φ (frameDet 6 1))) (h12 : IsUnit (φ (frameDet 12 1)))
    (h18 : IsUnit (φ (frameDet 18 1)))
    {σ : Type*} (D : σ → Derivation ℤ R R)
    (simple : ∀ I : Ideal R, I ≠ ⊥ →
      (∀ i x, x ∈ I → D i x ∈ I) → I = ⊤)
    {L : Type*} [CommRing L] [Nontrivial L] (ρ : R →+* L)
    (independent : LinearIndependent L
      (fun i => specialize ρ (equation φ) (basisSymbol φ i))) :
    Function.Injective (vectorRealize φ) := by
  classical
  choose B hB using fun i => exists_vector_connection φ h6 h12 h18 (D i)
  apply LinearMap.ker_eq_bot.mp
  apply CycleQ2DifferentialCoefficientIdeals.eq_bot_of_specializes_zero D simple B
    (LinearMap.ker (vectorRealize φ)) _ ρ
  · intro i v hv
    change vectorRealize φ (fun j => D i (v j) + (B i).mulVec v j) = 0
    rw [hB]
    change vectorRealize φ v = 0 at hv
    rw [hv, map_zero]
  · intro v hv j
    change vectorRealize φ v = 0 at hv
    have h := congrArg (specialize ρ (equation φ)) hv
    change specialize ρ (equation φ) (∑ i, v i • basisSymbol φ i) =
      specialize ρ (equation φ) 0 at h
    simp only [map_sum, map_smulₛₗ, map_zero] at h
    exact (Fintype.linearIndependent_iff.mp independent) (fun i => ρ (v i)) h j

end CycleQ2UniversalPoleFrame
end

#print axioms CycleQ2UniversalPoleFrame.exists_vector_connection
#print axioms CycleQ2UniversalPoleFrame.vectorRealize_injective_of_specialized_independent

/-!
# Prime iterates of the actual coefficient connection

The prime-entry calculation acts on a whole specialized subspace only after
the prime iterate of the connection is scalar-linear. This follows from the
iterated Leibniz formula and the vanishing of a coordinate partial raised to
the characteristic. The latter statement survives arbitrary localization;
no inverse of a prime-dependent integer is introduced.
-/

noncomputable section
namespace CycleQ2PrimeConnection

open Finset Nat

section Connection

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- The full Leibniz formula for an additive connection, before reduction
to prime characteristic. -/
theorem iterate_smul (D : R →+ R) (T : M →+ M)
    (h : ∀ a x, T (a • x) = a • T x + D a • x)
    (n : ℕ) (a : R) (x : M) :
    T^[n] (a • x) =
      ∑ ij ∈ antidiagonal n, n.choose ij.1 • (D^[ij.1] a • T^[ij.2] x) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_antidiagonal_choose_succ_nsmul (M := M)
      (fun i j => D^[i] a • T^[j] x) n]
    simp only [Function.iterate_succ_apply', ih, map_sum, map_nsmul, h,
      smul_add, sum_add_distrib, add_right_inj]
    refine sum_congr rfl fun ⟨i,j⟩ hij => ?_
    rw [n.choose_symm_of_eq_add (mem_antidiagonal.1 hij).symm]

/-- In characteristic `p`, only the two endpoint terms of the prime
binomial sum remain. The statement also includes `p = 2`. -/
theorem prime_antidiagonal_sum (p : ℕ) (hp : p.Prime) [CharP R p]
    (f : ℕ → ℕ → M) :
    (∑ ij ∈ antidiagonal p, p.choose ij.1 • f ij.1 ij.2) = f 0 p + f p 0 := by
  classical
  have hsub : ({(0,p),(p,0)} : Finset (ℕ × ℕ)) ⊆ antidiagonal p := by
    intro ij hij
    simp only [mem_insert, mem_singleton] at hij
    rcases hij with rfl | rfl <;> simp
  have hsum := Finset.sum_subset hsub (f := fun ij : ℕ × ℕ =>
      p.choose ij.1 • f ij.1 ij.2) (by
    rintro ⟨i,j⟩ hij hnot
    have heq : i + j = p := mem_antidiagonal.1 hij
    have hi0 : i ≠ 0 := by
      intro hi
      have hj : j = p := by omega
      exact hnot (by simp [hi,hj])
    have hip : i < p := by
      by_contra hi
      have hieq : i = p := by omega
      have hjeq : j = 0 := by omega
      exact hnot (by simp [hieq,hjeq])
    have hc : (p.choose i : R) = 0 :=
      (CharP.cast_eq_zero_iff R p _).2 (hp.dvd_choose_self hi0 hip)
    rw [← Nat.cast_smul_eq_nsmul R, hc, zero_smul])
  rw [← hsum]
  simp [hp.ne_zero, Ne.symm hp.ne_zero]

/-- The prime iterate of a connection has the Leibniz rule for `D^[p]`. -/
theorem iterate_prime_smul (D : R →+ R) (T : M →+ M)
    (h : ∀ a x, T (a • x) = a • T x + D a • x)
    (p : ℕ) (hp : p.Prime) [CharP R p] (a : R) (x : M) :
    T^[p] (a • x) = a • T^[p] x + D^[p] a • x := by
  rw [iterate_smul D T h, prime_antidiagonal_sum (R := R) p hp]
  rfl

theorem iterate_add (T : M →+ M) (n : ℕ) (x y : M) :
    T^[n] (x + y) = T^[n] x + T^[n] y := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Function.iterate_succ_apply', ih, map_add]

/-- When the scalar derivation has zero prime iterate, the prime iterate
of the connection is an actual linear endomorphism. -/
def linearMap (D : R →+ R) (T : M →+ M)
    (h : ∀ a x, T (a • x) = a • T x + D a • x)
    (p : ℕ) (hp : p.Prime) [CharP R p] (hD : ∀ a, D^[p] a = 0) : M →ₗ[R] M where
  toFun := T^[p]
  map_add' := iterate_add T p
  map_smul' a x := by
    change T^[p] (a • x) = a • T^[p] x
    rw [iterate_prime_smul D T h p hp, hD, zero_smul, add_zero]

@[simp]
theorem linearMap_apply (D : R →+ R) (T : M →+ M)
    (h : ∀ a x, T (a • x) = a • T x + D a • x)
    (p : ℕ) (hp : p.Prime) [CharP R p] (hD : ∀ a, D^[p] a = 0) (x : M) :
    linearMap D T h p hp hD x = T^[p] x := rfl

theorem iterate_mem (T : M →+ M) (N : Submodule R M)
    (hN : ∀ x, x ∈ N → T x ∈ N) (n : ℕ) (x : M) (hx : x ∈ N) :
    T^[n] x ∈ N := by
  induction n with
  | zero => exact hx
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact hN _ ih

end Connection

/-- The prime iterate of a derivation is again a derivation. -/
def primeIterate {k R : Type*} [CommRing k] [CommRing R] [Algebra k R]
    (D : Derivation k R R) (p : ℕ) (hp : p.Prime) [CharP R p] :
    Derivation k R R :=
  Derivation.mk' (D.toLinearMap ^ p) (by
    intro a b
    simp only [Module.End.pow_apply]
    have h (a b : R) : D (a • b) = a • D b + D a • b := by
      simpa only [smul_eq_mul, mul_comm] using D.leibniz a b
    simpa only [smul_eq_mul, mul_comm] using
      iterate_prime_smul D.toAddMonoidHom D.toAddMonoidHom h p hp a b)

@[simp]
theorem primeIterate_apply {k R : Type*} [CommRing k] [CommRing R] [Algebra k R]
    (D : Derivation k R R) (p : ℕ) (hp : p.Prime) [CharP R p] (a : R) :
    primeIterate D p hp a = D^[p] a := Module.End.pow_apply D.toLinearMap p a

/-- A polynomial coordinate partial has zero prime iterate in the prime
characteristic, with no restriction on the number of variables. -/
theorem pderiv_prime_zero {k σ : Type*} [CommRing k] (i : σ)
    (p : ℕ) (hp : p.Prime) [CharP k p] (f : MvPolynomial σ k) :
    (MvPolynomial.pderiv i)^[p] f = 0 := by
  have hz : primeIterate (MvPolynomial.pderiv i :
      Derivation k (MvPolynomial σ k) (MvPolynomial σ k)) p hp = 0 := by
    apply MvPolynomial.derivation_ext
    intro j
    change ((MvPolynomial.pderiv i).toLinearMap ^ p) (MvPolynomial.X j) = 0
    apply Module.End.pow_map_zero_of_le hp.two_le
    change MvPolynomial.pderiv i (MvPolynomial.pderiv i (MvPolynomial.X j)) = 0
    by_cases hj : j = i
    · subst j
      simp
    · rw [MvPolynomial.pderiv_X_of_ne hj, map_zero]
  have h := congrArg (fun D : Derivation k (MvPolynomial σ k) (MvPolynomial σ k) => D f) hz
  simpa only [primeIterate_apply, Derivation.zero_apply] using h

/-- The same nilpotence holds for every extension of a coordinate partial
to a localization. The proof differentiates a cleared denominator identity
and cancels its unit; it does not impose a degree bound on denominators. -/
theorem localizedPartial_prime_zero {k σ S : Type*} [CommRing k] [CommRing S]
    [Algebra (MvPolynomial σ k) S] (M : Submonoid (MvPolynomial σ k))
    [IsLocalization M S] (i : σ) (D : Derivation ℤ S S)
    (hD : ∀ f : MvPolynomial σ k,
      D (algebraMap (MvPolynomial σ k) S f) =
        algebraMap (MvPolynomial σ k) S (MvPolynomial.pderiv i f))
    (p : ℕ) (hp : p.Prime) [CharP k p] [CharP S p] (z : S) : D^[p] z = 0 := by
  have hi (n : ℕ) (f : MvPolynomial σ k) :
      D^[n] (algebraMap (MvPolynomial σ k) S f) =
        algebraMap (MvPolynomial σ k) S ((MvPolynomial.pderiv i)^[n] f) := by
    induction n with
    | zero => rfl
    | succ n ih => rw [Function.iterate_succ_apply', ih, hD,
        Function.iterate_succ_apply']
  let E := primeIterate D p hp
  have hbase (f : MvPolynomial σ k) : E (algebraMap (MvPolynomial σ k) S f) = 0 := by
    dsimp only [E]
    rw [primeIterate_apply, hi, pderiv_prime_zero i p hp, map_zero]
  have he : E z = 0 := by
    obtain ⟨⟨a,s⟩,hs⟩ := IsLocalization.surj M z
    have hz := congrArg E hs
    simp only [Derivation.leibniz, hbase, smul_zero, zero_add, smul_eq_mul] at hz
    exact (IsLocalization.map_units S s).mul_left_cancel
      (by simpa only [mul_zero] using hz)
  simpa only [E, primeIterate_apply] using he

section Matrices

variable {R L n : Type*} [CommRing R] [CommRing L] [Fintype n]

/-- The actual coordinate connection `D + B` on a finite free module. -/
def matrixConnection (D : Derivation ℤ R R) (B : Matrix n n R) :
    (n → R) →+ (n → R) where
  toFun v := fun i => D (v i) + B.mulVec v i
  map_zero' := by ext i; simp
  map_add' v w := by
    ext i
    change D (v i + w i) + B.mulVec (v + w) i =
      (D (v i) + B.mulVec v i) + (D (w i) + B.mulVec w i)
    rw [map_add, Matrix.mulVec_add]
    change (D (v i) + D (w i)) + (B.mulVec v i + B.mulVec w i) = _
    abel

theorem matrixConnection_smul (D : Derivation ℤ R R) (B : Matrix n n R)
    (a : R) (v : n → R) :
    matrixConnection D B (a • v) = a • matrixConnection D B v + D a • v := by
  ext i
  have hB := congrFun (map_smul B.mulVecLin a v) i
  change B.mulVec (a • v) i = a * B.mulVec v i at hB
  change D (a * v i) + B.mulVec (a • v) i =
    a * (D (v i) + B.mulVec v i) + D a * v i
  rw [hB,D.leibniz]
  simp only [smul_eq_mul]
  ring

theorem derivation_mulVec {s : Type*} [Fintype s]
    (D : Derivation ℤ R R) (P : Matrix n s R) (w : s → R) :
    (fun i => D (P.mulVec w i)) =
      (P.map D).mulVec w + P.mulVec (fun j => D (w j)) := by
  classical
  ext i
  change D (∑ j, P i j * w j) =
    (∑ j, D (P i j) * w j) + ∑ j, P i j * D (w j)
  rw [map_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [D.leibniz]
  simp only [smul_eq_mul]
  ring

/-- The descended generator identity gives the genuine connection on
every linear combination of its columns. -/
theorem matrixConnection_mulVec {s : Type*} [Fintype s]
    (D : Derivation ℤ R R) (B : Matrix n n R) (P : Matrix n s R)
    (C : Matrix s s R) (hP : P.map D = P * C - B * P) (w : s → R) :
    matrixConnection D B (P.mulVec w) =
      P.mulVec ((fun j => D (w j)) + C.mulVec w) := by
  change (fun i => D (P.mulVec w i)) + B.mulVec (P.mulVec w) = _
  rw [derivation_mulVec D P w,hP,Matrix.sub_mulVec,
    ← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec,Matrix.mulVec_add]
  abel

theorem matrixConnection_range_stable {s : Type*} [Fintype s]
    (D : Derivation ℤ R R) (B : Matrix n n R) (P : Matrix n s R)
    (C : Matrix s s R) (hP : P.map D = P * C - B * P)
    (v : n → R) (hv : v ∈ LinearMap.range P.mulVecLin) :
    matrixConnection D B v ∈ LinearMap.range P.mulVecLin := by
  obtain ⟨w,rfl⟩ := hv
  exact ⟨(fun j => D (w j)) + C.mulVec w,
    (matrixConnection_mulVec D B P C hP w).symm⟩

/-- Coordinate matrix of the prime iterate of `D + B`. -/
def primeMatrix [DecidableEq n] (D : Derivation ℤ R R) (B : Matrix n n R)
    (p : ℕ) (hp : p.Prime) [CharP R p] (hD : ∀ a, D^[p] a = 0) : Matrix n n R :=
  LinearMap.toMatrix' (linearMap D.toAddMonoidHom (matrixConnection D B)
    (matrixConnection_smul D B) p hp hD)

theorem primeMatrix_mulVec [DecidableEq n] (D : Derivation ℤ R R) (B : Matrix n n R)
    (p : ℕ) (hp : p.Prime) [CharP R p] (hD : ∀ a, D^[p] a = 0) (v : n → R) :
    (primeMatrix D B p hp hD).mulVec v = (matrixConnection D B)^[p] v :=
  LinearMap.toMatrix'_mulVec _ v

/-- A linear map preserving a finitely generated column space admits a
matrix on those generators, without any independence assumption. -/
theorem linearMap_generator_matrix [DecidableEq n] {s : Type*} [Fintype s]
    (T : (n → R) →ₗ[R] (n → R)) (P : Matrix n s R)
    (stable : ∀ v, v ∈ LinearMap.range P.mulVecLin →
      T v ∈ LinearMap.range P.mulVecLin) :
    ∃ Q : Matrix s s R, LinearMap.toMatrix' T * P = P * Q := by
  classical
  have hcol (j : s) : (fun i => P i j) ∈ LinearMap.range P.mulVecLin := by
    rw [Matrix.range_mulVecLin]
    exact Submodule.subset_span ⟨j,rfl⟩
  choose c hc using fun j => stable (fun i => P i j) (hcol j)
  let Q : Matrix s s R := fun i j => c j i
  refine ⟨Q,?_⟩
  ext i j
  have hT := congrFun (LinearMap.toMatrix'_mulVec T (fun k => P k j)) i
  exact hT.trans (congrFun (hc j) i).symm

/-- A witnessed matrix-invariance identity survives every ring-valued
point, including points at which the generator matrix loses rank. -/
theorem specialized_range_stable {s : Type*} [Fintype s]
    (ρ : R →+* L) (A : Matrix n n R) (P : Matrix n s R) (Q : Matrix s s R)
    (h : A * P = P * Q) (v : n → L)
    (hv : v ∈ LinearMap.range (P.map ρ).mulVecLin) :
    (A.map ρ).mulVec v ∈ LinearMap.range (P.map ρ).mulVecLin := by
  classical
  have hm : A.map ρ * P.map ρ = P.map ρ * Q.map ρ := by
    ext i j
    have he := congrArg ρ (congrFun (congrFun h i) j)
    simpa only [Matrix.mul_apply,Matrix.map_apply,map_sum,map_mul] using he
  obtain ⟨w,rfl⟩ := hv
  refine ⟨(Q.map ρ).mulVec w,?_⟩
  change (P.map ρ).mulVec ((Q.map ρ).mulVec w) =
    (A.map ρ).mulVec ((P.map ρ).mulVec w)
  rw [Matrix.mulVec_mulVec,Matrix.mulVec_mulVec,hm]

/-- An actual connection-stable lattice has a prime-iterate-stable fiber.
Evaluation need not commute with the scalar derivative: it is applied only
after the prime iterate has been proved scalar-linear. -/
theorem primeMatrix_specialized_range_stable [DecidableEq n] {s : Type*} [Fintype s]
    (D : Derivation ℤ R R) (B : Matrix n n R) (P : Matrix n s R)
    (stable : ∀ v, v ∈ LinearMap.range P.mulVecLin →
      matrixConnection D B v ∈ LinearMap.range P.mulVecLin)
    (p : ℕ) (hp : p.Prime) [CharP R p] (hD : ∀ a, D^[p] a = 0)
    (ρ : R →+* L) (v : n → L) (hv : v ∈ LinearMap.range (P.map ρ).mulVecLin) :
    ((primeMatrix D B p hp hD).map ρ).mulVec v ∈
      LinearMap.range (P.map ρ).mulVecLin := by
  let T := linearMap D.toAddMonoidHom (matrixConnection D B)
    (matrixConnection_smul D B) p hp hD
  obtain ⟨Q,hQ⟩ := linearMap_generator_matrix T P (fun x hx =>
    iterate_mem (matrixConnection D B) (LinearMap.range P.mulVecLin) stable p x hx)
  exact specialized_range_stable ρ (primeMatrix D B p hp hD) P Q hQ v hv

end Matrices

end CycleQ2PrimeConnection

namespace CycleQ2PolynomialPoleSymbols

variable {k R : Type*} [CommRing k] [CommRing R] [Algebra k R]

/-- The prime power of the actual polynomial-pole connection, bundled as
an `R`-linear endomorphism when its scalar partial has zero prime power. -/
def primeConnection (D : Derivation k R R) (F : MvPolynomial (Fin 5) R)
    (p : ℕ) (hp : p.Prime) [CharP R p] (hD : ∀ a, D^[p] a = 0) :
    Symbols R F →ₗ[R] Symbols R F :=
  CycleQ2PrimeConnection.linearMap D.toAddMonoidHom (connection D F)
    (connection_smul D F) p hp hD

@[simp]
theorem primeConnection_apply (D : Derivation k R R) (F : MvPolynomial (Fin 5) R)
    (p : ℕ) (hp : p.Prime) [CharP R p] (hD : ∀ a, D^[p] a = 0)
    (x : Symbols R F) : primeConnection D F p hp hD x = (connection D F)^[p] x := rfl

end CycleQ2PolynomialPoleSymbols
end

#print axioms CycleQ2PrimeConnection.iterate_prime_smul
#print axioms CycleQ2PrimeConnection.pderiv_prime_zero
#print axioms CycleQ2PrimeConnection.localizedPartial_prime_zero
#print axioms CycleQ2PrimeConnection.primeMatrix_specialized_range_stable
#print axioms CycleQ2PolynomialPoleSymbols.primeConnection
