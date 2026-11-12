import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Tactic
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Tactic.FinCases
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.Dual.Defs
import HodgeTarget
import Proposal.GeometricTarget
import Proposal.GeometricSeed
import Proposal.GeometricFormalInputs
import Proposal.Normalization

/-! Source partition of Solution.lean. See solution.md for verification status. -/

set_option Elab.async false

/- Component: continuation_3/cylinder_bridge/SegreRelationsSeedCharts.lean -/
section
/-! # Actual linear-map exactness on the smooth seed's nine pivot charts -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 20000

namespace CycleQ2SegreRelationsLocal

open Matrix CycleQ2IncidenceFirstOrder CycleQ2SegreTangentLocal

variable {R : Type*} [CommRing R]

def vectorLinear : Matrix (Fin 3) (Fin 3) R →ₗ[R] (Fin 9 → R) where
  toFun := vector
  map_add' := by
    intro A B
    funext k
    fin_cases k <;> rfl
  map_smul' := by
    intro a A
    funext k
    fin_cases k <;> rfl

def relationsLinear (M : Matrix (Fin 3) (Fin 3) R) :
    Matrix (Fin 3) (Fin 3) R →ₗ[R] (Fin 16 → R) :=
  (Matrix.mulVecLin (CycleQ2SegreRelations.relations M)).comp vectorLinear

/-- Equality of the actual kernel and image submodules on any unit pivot. -/
theorem ker_relationsLinear_eq_range (M : Matrix (Fin 3) (Fin 3) R)
    (hM : CycleQ2SegreLocal.cofactors M=0)
    (i0 j0 : Fin 3) (u : Rˣ) (hu : (u : R)=M i0 j0) :
    LinearMap.ker (relationsLinear M)=LinearMap.range (cofactorDifferentialLinear M) := by
  ext C
  exact unit_pivot_relations_exact M C hM i0 j0 u hu

/-- The actual seed quotient localized at one of its nine matrix entries. -/
abbrev SeedChart (r ι : R) (i0 j0 : Fin 3) :=
  Localization.Away (seedQuotientMatrix r ι i0 j0)

def seedChartMatrix (r ι : R) (i0 j0 : Fin 3) :
    Matrix (Fin 3) (Fin 3) (SeedChart r ι i0 j0) :=
  (algebraMap (SeedRing r ι) (SeedChart r ι i0 j0)).mapMatrix (seedQuotientMatrix r ι)

def seedChartUnit (r ι : R) (i0 j0 : Fin 3) : (SeedChart r ι i0 j0)ˣ :=
  (IsLocalization.Away.algebraMap_isUnit (S := SeedChart r ι i0 j0)
    (seedQuotientMatrix r ι i0 j0)).unit

theorem seedChartUnit_coe (r ι : R) (i0 j0 : Fin 3) :
    (seedChartUnit r ι i0 j0 : SeedChart r ι i0 j0)=seedChartMatrix r ι i0 j0 i0 j0 :=
  IsUnit.unit_spec _

theorem seedChartMatrix_cofactors (r ι : R) (i0 j0 : Fin 3) :
    CycleQ2SegreLocal.cofactors (seedChartMatrix r ι i0 j0)=0 := by
  rw [seedChartMatrix,← map_cofactors,seedQuotientMatrix_cofactors]
  ext i j
  change algebraMap (SeedRing r ι) (SeedChart r ι i0 j0) 0=0
  exact map_zero _

/-- Exactness on every actual seed pivot chart, with both cofactor vanishing
and the pivot unit proved from its explicit construction. -/
theorem seed_chart_relations_exact (r ι : R) (i0 j0 : Fin 3)
    (C : Matrix (Fin 3) (Fin 3) (SeedChart r ι i0 j0)) :
    CycleQ2SegreRelations.relations (seedChartMatrix r ι i0 j0) *ᵥ vector C=0 ↔
      ∃ N : Matrix (Fin 3) (Fin 3) (SeedChart r ι i0 j0),
        cofactorDifferential (seedChartMatrix r ι i0 j0) N=C :=
  unit_pivot_relations_exact _ _ (seedChartMatrix_cofactors r ι i0 j0)
    i0 j0 (seedChartUnit r ι i0 j0) (seedChartUnit_coe r ι i0 j0)

theorem seed_chart_ker_eq_range (r ι : R) (i0 j0 : Fin 3) :
    LinearMap.ker (relationsLinear (seedChartMatrix r ι i0 j0))=
      LinearMap.range (cofactorDifferentialLinear (seedChartMatrix r ι i0 j0)) :=
  ker_relationsLinear_eq_range _ (seedChartMatrix_cofactors r ι i0 j0)
    i0 j0 (seedChartUnit r ι i0 j0) (seedChartUnit_coe r ι i0 j0)

end CycleQ2SegreRelationsLocal

#print axioms CycleQ2SegreRelationsLocal.ker_relationsLinear_eq_range
#print axioms CycleQ2SegreRelationsLocal.seed_chart_relations_exact
#print axioms CycleQ2SegreRelationsLocal.seed_chart_ker_eq_range
end
end


/- Component: continuation_3/SparseGaussianFastNormalForm.lean -/
section
/-! Skip empty coefficient layers before computing their monic normal forms.
The original scalar normalizer and its semantic theorem are unchanged. -/

set_option maxHeartbeats 500000
set_option maxRecDepth 20000
set_option Elab.async false

namespace CycleQ2SparseGaussianPolynomial

def fastNormalizeBlock (a₀ a₁ b₀ : Layers) (fuel b : ℕ) : ℕ → Blocks → Towers
  | _, [] => []
  | a, []::p => fastNormalizeBlock a₀ a₁ b₀ fuel b (a+1) p
  | a, (c::cs)::p =>
      addTowers (scaleTower (c::cs) (normalCore a₀ a₁ b₀ fuel a b))
        (fastNormalizeBlock a₀ a₁ b₀ fuel b (a+1) p)

def fastNormalizeTowerFrom (a₀ a₁ b₀ : Layers) (fuel : ℕ) : ℕ → Towers → Towers
  | _, [] => []
  | b, []::p => fastNormalizeTowerFrom a₀ a₁ b₀ fuel (b+1) p
  | b, (c::cs)::p => addTowers (fastNormalizeBlock a₀ a₁ b₀ fuel b 0 (c::cs))
      (fastNormalizeTowerFrom a₀ a₁ b₀ fuel (b+1) p)

def fastNormalizeTower (a₀ a₁ b₀ : Layers) (fuel : ℕ) (p : Towers) : Towers :=
  fastNormalizeTowerFrom a₀ a₁ b₀ fuel 0 p

section Soundness
variable {R : Type*} [CommRing R]
variable (φ : GaussianInt →+* R) (x : Fin 5 → R) (w z v : R)
variable (a₀ a₁ b₀ : Layers)
variable (hz : z^3=evalLayers φ x v a₀+evalLayers φ x v a₁*z)
variable (hw : w^3=evalLayers φ x v b₀-z^6)
include hz hw

theorem eval_fastNormalizeBlock (fuel b a : ℕ) (p : Blocks) :
    evalTowers φ x w z v (fastNormalizeBlock a₀ a₁ b₀ fuel b a p)=
      z^a*w^b*evalBlocks φ x z v p := by
  induction p generalizing a with
  | nil => simp only [fastNormalizeBlock,evalTowers,evalBlocks,mul_zero]
  | cons c p ih =>
    cases c with
    | nil =>
      simp only [fastNormalizeBlock,ih,evalBlocks,evalLayers,zero_add,pow_succ]
      ring
    | cons c cs =>
      simp only [fastNormalizeBlock,eval_addTowers,eval_scaleTower,
        eval_normalCore φ x w z v a₀ a₁ b₀ hz hw,ih,evalBlocks,pow_succ]
      ring

theorem eval_fastNormalizeTowerFrom (fuel b : ℕ) (p : Towers) :
    evalTowers φ x w z v (fastNormalizeTowerFrom a₀ a₁ b₀ fuel b p)=
      w^b*evalTowers φ x w z v p := by
  induction p generalizing b with
  | nil => simp only [fastNormalizeTowerFrom,evalTowers,mul_zero]
  | cons q p ih =>
    cases q with
    | nil =>
      simp only [fastNormalizeTowerFrom,ih,evalTowers,evalBlocks,zero_add,pow_succ]
      ring
    | cons c cs =>
      simp only [fastNormalizeTowerFrom,eval_addTowers,
        eval_fastNormalizeBlock φ x w z v a₀ a₁ b₀ hz hw,ih,
        evalTowers,pow_zero,one_mul,pow_succ]
      ring

theorem eval_fastNormalizeTower (fuel : ℕ) (p : Towers) :
    evalTowers φ x w z v (fastNormalizeTower a₀ a₁ b₀ fuel p)=
      evalTowers φ x w z v p := by
  simpa only [fastNormalizeTower,pow_zero,one_mul] using
    eval_fastNormalizeTowerFrom φ x w z v a₀ a₁ b₀ hz hw fuel 0 p

theorem monomial_action_of_fast_normal_error_check (fuel : ℕ)
    (p q : Towers) (a b : ℕ)
    (h : checkTowers (addTowers
      (fastNormalizeTower a₀ a₁ b₀ fuel (mulTowers p (monomialTower oneLayers a b)))
      (negTowers q))=true) :
    evalTowers φ x w z v q=evalTowers φ x w z v p*z^a*w^b := by
  have hzero := evalTowers_eq_zero_of_checkTowers φ x w z v _ h
  rw [eval_addTowers,eval_negTowers,
    eval_fastNormalizeTower φ x w z v a₀ a₁ b₀ hz hw,
    eval_mulTowers,eval_monomialTower,eval_oneLayers,mul_one] at hzero
  linear_combination -hzero

end Soundness
end CycleQ2SparseGaussianPolynomial

#print axioms CycleQ2SparseGaussianPolynomial.eval_fastNormalizeTower
#print axioms CycleQ2SparseGaussianPolynomial.monomial_action_of_fast_normal_error_check
end


/- Component: continuation_3/ArithmeticRankTransfer.lean -/
section
/-! # Nonconstructive rank transfer from a residue field

A matrix of rank r over a field admits a finite retraction C*A*B=1_r.
Lifting the two auxiliary matrices through a surjective coefficient map
produces an r-by-r determinant that is nonzero in every faithful field
specialization. No particular pivot list or large inverse is required.
-/

noncomputable section
set_option maxHeartbeats 500000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace CycleQ2ArithmeticRankTransfer

open Matrix

variable {K : Type*} [Field K] {m n : Type*} [Fintype m] [Fintype n]

theorem exists_rank_retraction (A : Matrix m n K) :
    ∃ (C : Matrix (Fin A.rank) m K) (B : Matrix n (Fin A.rank) K), C*A*B=1 := by
  classical
  let V := LinearMap.range (Matrix.mulVecLin A)
  let b := Module.finBasis K V
  obtain ⟨s,hs⟩ := (Matrix.mulVecLin A).rangeRestrict.exists_rightInverse_of_surjective
    (Matrix.mulVecLin A).range_rangeRestrict
  obtain ⟨t,ht⟩ := V.subtype.exists_leftInverse_of_injective V.ker_subtype
  let C : (m → K) →ₗ[K] (Fin A.rank → K) := b.equivFun.toLinearMap.comp t
  let B : (Fin A.rank → K) →ₗ[K] (n → K) := s.comp b.equivFun.symm.toLinearMap
  refine ⟨LinearMap.toMatrix' C,LinearMap.toMatrix' B,?_⟩
  apply Matrix.toLin'.injective
  rw [Matrix.toLin'_mul,Matrix.toLin'_mul,Matrix.toLin'_toMatrix',Matrix.toLin'_toMatrix',
    Matrix.toLin'_one]
  apply LinearMap.ext
  intro x
  change b.equivFun (t (Matrix.mulVecLin A (s (b.equivFun.symm x))))=x
  have hpre := congrArg Subtype.val (LinearMap.congr_fun hs (b.equivFun.symm x))
  change Matrix.mulVecLin A (s (b.equivFun.symm x))=(b.equivFun.symm x).val at hpre
  rw [hpre]
  have hpost := LinearMap.congr_fun ht (b.equivFun.symm x)
  change t (b.equivFun.symm x).val=b.equivFun.symm x at hpost
  rw [hpost,LinearEquiv.apply_symm_apply]

variable {R L : Type*} [CommRing R] [Field L]

/-- Rank cannot decrease when a residue-field computation is transported
through the same integral matrix to a faithful characteristic-zero field. -/
theorem rank_reduction_le_faithful (f : R →+* K) (hf : Function.Surjective f)
    (g : R →+* L) (hg : Function.Injective g) (A : Matrix m n R) :
    (A.map f).rank≤(A.map g).rank := by
  classical
  obtain ⟨C,B,hCB⟩ := exists_rank_retraction (A.map f)
  choose c0 hC using fun i j => hf (C i j)
  choose b0 hB using fun i j => hf (B i j)
  let C0 : Matrix (Fin (A.map f).rank) m R := c0
  let B0 : Matrix n (Fin (A.map f).rank) R := b0
  have hC0 : C0.map f=C := by
    ext i j
    exact hC i j
  have hB0 : B0.map f=B := by
    ext i j
    exact hB i j
  let T : Matrix (Fin (A.map f).rank) (Fin (A.map f).rank) R := C0*A*B0
  have hTf : T.map f=1 := by
    simp only [T,Matrix.map_mul]
    rw [hC0,hB0,hCB]
  have hdet : T.det≠0 := by
    intro hz
    have hh := congrArg Matrix.det hTf
    change (f.mapMatrix T).det=Matrix.det (1:Matrix (Fin (A.map f).rank) (Fin (A.map f).rank) K) at hh
    rw [←f.map_det,hz,map_zero,Matrix.det_one] at hh
    exact zero_ne_one hh
  have hdetg : (T.map g).det≠0 := by
    change (g.mapMatrix T).det≠0
    rw [←g.map_det]
    exact fun hz => hdet (hg (hz.trans (map_zero g).symm))
  have ht : (T.map g).rank=(A.map f).rank := by
    rw [Matrix.rank_of_det_ne_zero hdetg,Fintype.card_fin]
  have hTg : T.map g=(C0.map g)*(A.map g)*(B0.map g) := by
    simp only [T,Matrix.map_mul]
  rw [←ht,hTg]
  exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)

theorem gaussian_reduction_surjective :
    Function.Surjective CycleQ2IncidenceGaussianArithmetic.reduction := by
  intro x
  refine ⟨(x.val:GaussianInt),?_⟩
  rw [map_natCast]
  exact ZMod.natCast_zmod_val x

/-- The literal Gaussian integral family transfers a proved modular rank
bound without requiring an evaluated list of pivot rows or columns. -/
theorem gaussian_rank_transfer (A : Matrix m n GaussianInt) :
    (A.map CycleQ2IncidenceGaussianArithmetic.reduction).rank≤
      (A.map GaussianInt.toComplex).rank :=
  rank_reduction_le_faithful _ gaussian_reduction_surjective _
    GaussianInt.toComplex_injective A

end CycleQ2ArithmeticRankTransfer

#print axioms CycleQ2ArithmeticRankTransfer.exists_rank_retraction
#print axioms CycleQ2ArithmeticRankTransfer.rank_reduction_le_faithful
#print axioms CycleQ2ArithmeticRankTransfer.gaussian_rank_transfer
end
end


/- Component: continuation_3/ArithmeticSurjectivity.lean -/
section
/-!
# Surjectivity transfer from an arithmetic reduction

A right inverse over a quotient coefficient ring can be lifted entry by
entry. The square product has determinant reducing to one, hence has
nonzero determinant in every faithful field specialization. This proves
surjectivity of the original rectangular matrix in characteristic zero,
without assuming that a particular modular solution lifts.
-/

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2ArithmeticSurjectivity

open Matrix

variable {R S K m n : Type*} [CommRing R] [CommRing S] [Nontrivial S]
  [Field K] [Fintype m] [DecidableEq m] [Fintype n]

theorem transfer (f : R →+* S) (hf : Function.Surjective f)
    (g : R →+* K) (hg : Function.Injective g) (A : Matrix m n R)
    (hA : Function.Surjective (A.map f).mulVec) :
    Function.Surjective (A.map g).mulVec := by
  classical
  obtain ⟨B, hB⟩ := mulVec_surjective_iff_exists_right_inverse.mp hA
  choose liftB hlift using fun i j => hf (B i j)
  let B₀ : Matrix n m R := Matrix.of liftB
  have hmap : B₀.map f = B := by
    ext i j
    exact hlift i j
  have hproduct : f.mapMatrix (A * B₀) = 1 := by
    change (A * B₀).map f = 1
    rw [Matrix.map_mul, hmap]
    exact hB
  have hdet : (A * B₀).det ≠ 0 := by
    intro hz
    have he := congrArg Matrix.det hproduct
    rw [← f.map_det, hz, map_zero, Matrix.det_one] at he
    exact zero_ne_one he
  have hgdet : (g.mapMatrix (A * B₀)).det ≠ 0 := by
    rw [← g.map_det]
    exact fun hz => hdet (hg (by simpa using hz))
  have hu : IsUnit (g.mapMatrix (A * B₀)) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hgdet)
  have hs := mulVec_surjective_iff_isUnit.mpr hu
  intro y
  obtain ⟨x, hx⟩ := hs y
  refine ⟨B₀.map g *ᵥ x, ?_⟩
  rw [mulVec_mulVec]
  change (g.mapMatrix (A * B₀)) *ᵥ x = y at hx
  simpa only [RingHom.mapMatrix_apply, Matrix.map_mul] using hx

/-- This applies to any finite rectangular matrix of Gaussian integers,
with the actual i↦33 modulo109 and i↦Complex.I specializations. -/
theorem gaussian (A : Matrix m n GaussianInt)
    (hA : Function.Surjective
      (A.map CycleQ2IncidenceGaussianArithmetic.reduction).mulVec) :
    Function.Surjective (A.map GaussianInt.toComplex).mulVec :=
  transfer CycleQ2IncidenceGaussianArithmetic.reduction
    (ZMod.ringHom_surjective _) GaussianInt.toComplex
    GaussianInt.toComplex_injective A hA

end CycleQ2ArithmeticSurjectivity

#print axioms CycleQ2ArithmeticSurjectivity.transfer
#print axioms CycleQ2ArithmeticSurjectivity.gaussian
end
end


/- Component: continuation_3/CurveCechLocalization.lean -/
section
/-!
# Identifying the coordinate localizations with bounded Laurent sections

The map from the two-coordinate polynomial ring to Laurent polynomials is
injective. Its localization at any product of coordinate variables has image
exactly the Laurent polynomials whose poles occur only in those coordinates.
-/

noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2CurveCechLocalization

open MvPolynomial CycleQ2CurveQuotientFiniteFree CycleQ2CurveCechTwoOpen
open scoped BigOperators

variable (R : Type*) [CommRing R]

abbrev NatExponent := Fin 2 →₀ ℕ

def castExponent : NatExponent →+ LaurentExponent where
  toFun e i := e i
  map_zero' := by ext i; simp
  map_add' a b := by ext i; simp

@[simp] theorem castExponent_apply (e : NatExponent) (i : Fin 2) :
    castExponent e i = (e i : ℤ) := rfl

theorem castExponent_injective : Function.Injective castExponent := by
  intro a b hab
  ext i
  exact Nat.cast_injective (congrFun hab i)

theorem mem_range_castExponent (e : LaurentExponent) :
    e ∈ Set.range castExponent ↔ ∀ i, 0 ≤ e i := by
  constructor
  · rintro ⟨a, rfl⟩ i
    exact Nat.cast_nonneg _
  · intro he
    refine ⟨Finsupp.equivFunOnFinite.symm (fun i ↦ (e i).toNat), ?_⟩
    ext i
    exact Int.toNat_of_nonneg (he i)

def baseToLaurent : Base R →ₐ[R] Laurent (R := R) :=
  AddMonoidAlgebra.mapDomainAlgHom R R castExponent

theorem baseToLaurent_injective : Function.Injective (baseToLaurent R) :=
  AddMonoidAlgebra.mapDomain_injective castExponent_injective

@[simp] theorem baseToLaurent_monomial (e : NatExponent) (c : R) :
    baseToLaurent R (monomial e c) = AddMonoidAlgebra.single (castExponent e) c :=
  AddMonoidAlgebra.mapDomain_single

theorem baseToLaurent_hasPoles (p : Base R) : HasPoles ∅ (baseToLaurent R p) := by
  intro e i _ hi
  change Finsupp.mapDomain castExponent (AddMonoidAlgebra.coeff p) e = 0
  apply Finsupp.mapDomain_of_notMem_range
  intro he
  exact (not_le.mpr hi) ((mem_range_castExponent e).mp he i)

theorem mem_range_baseToLaurent (p : Laurent (R := R)) :
    p ∈ Set.range (baseToLaurent R) ↔ HasPoles ∅ p := by
  constructor
  · rintro ⟨p, rfl⟩
    exact baseToLaurent_hasPoles R p
  · intro hp
    have hs : ↑p.coeff.support ⊆ Set.range castExponent := by
      intro e he
      apply (mem_range_castExponent e).mpr
      intro i
      by_contra hi
      exact (Finsupp.mem_support_iff.mp he) (hp e i (by simp) (lt_of_not_ge hi))
    exact ⟨AddMonoidAlgebra.comapDomain castExponent castExponent_injective p,
      AddMonoidAlgebra.mapDomain_comapDomain hs castExponent_injective⟩

def T (e : LaurentExponent) : Laurent (R := R) := AddMonoidAlgebra.single e 1

@[simp] theorem T_zero : T R 0 = 1 := rfl
@[simp] theorem T_mul (a b : LaurentExponent) : T R a * T R b = T R (a + b) := by
  simp [T, AddMonoidAlgebra.single_mul_single]
@[simp] theorem T_pow (e : LaurentExponent) (n : ℕ) : (T R e)^n = T R (n • e) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, ih, T_mul, succ_nsmul]

theorem T_isUnit (e : LaurentExponent) : IsUnit (T R e) := by
  refine ⟨⟨T R e, T R (-e), ?_, ?_⟩, rfl⟩ <;> simp

@[simp] theorem coeff_mul_T (p : Laurent (R := R)) (a e : LaurentExponent) :
    (p * T R a).coeff e = p.coeff (e - a) := by
  simp [T, AddMonoidAlgebra.coeff_mul_single_apply, sub_eq_add_neg]

def openExponent (s : Finset (Fin 2)) : LaurentExponent := fun i ↦ if i ∈ s then 1 else 0

@[simp] theorem openExponent_empty : openExponent ∅ = 0 := by
  ext i
  simp [openExponent]

def baseProduct (s : Finset (Fin 2)) : Base R := ∏ i ∈ s, X i

@[simp] theorem castExponent_single (i : Fin 2) :
    castExponent (Finsupp.single i 1) = openExponent {i} := by
  ext j
  by_cases h : j = i
  · subst j; simp [openExponent]
  · simp [openExponent, h]

@[simp] theorem baseToLaurent_X (i : Fin 2) :
    baseToLaurent R (X i) = T R (openExponent {i}) := by
  change baseToLaurent R (monomial (Finsupp.single i 1) 1) = _
  simp [T]

theorem openExponent_insert (i : Fin 2) (s : Finset (Fin 2)) (hi : i ∉ s) :
    openExponent (insert i s) = openExponent {i} + openExponent s := by
  ext j
  by_cases h : j = i
  · subst j; simp [openExponent, hi]
  · simp [openExponent, h]

@[simp] theorem baseToLaurent_baseProduct (s : Finset (Fin 2)) :
    baseToLaurent R (baseProduct R s) = T R (openExponent s) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [baseProduct]
  | @insert i s hi ih =>
      rw [baseProduct, Finset.prod_insert hi, map_mul]
      change baseToLaurent R (X i) * baseToLaurent R (baseProduct R s) = _
      rw [baseToLaurent_X, ih, T_mul, openExponent_insert i s hi]

def coordinateLocalization (s : Finset (Fin 2)) := Localization.Away (baseProduct R s)

instance (s : Finset (Fin 2)) : CommRing (coordinateLocalization R s) :=
  inferInstanceAs (CommRing (Localization.Away (baseProduct R s)))
instance (s : Finset (Fin 2)) : Algebra (Base R) (coordinateLocalization R s) :=
  inferInstanceAs (Algebra (Base R) (Localization.Away (baseProduct R s)))
instance (s : Finset (Fin 2)) : IsLocalization.Away (baseProduct R s) (coordinateLocalization R s) :=
  inferInstanceAs (IsLocalization.Away (baseProduct R s) (Localization.Away (baseProduct R s)))

def localizationToLaurent (s : Finset (Fin 2)) :
    coordinateLocalization R s →+* Laurent (R := R) :=
  IsLocalization.Away.lift (baseProduct R s)
    (show IsUnit ((baseToLaurent R).toRingHom (baseProduct R s)) by
      change IsUnit (baseToLaurent R (baseProduct R s))
      rw [baseToLaurent_baseProduct]
      exact T_isUnit R _)

@[simp] theorem localizationToLaurent_algebraMap (s : Finset (Fin 2)) (p : Base R) :
    localizationToLaurent R s (algebraMap (Base R) (coordinateLocalization R s) p) =
      baseToLaurent R p := IsLocalization.Away.lift_eq _ _ _

theorem localizationToLaurent_injective (s : Finset (Fin 2)) :
    Function.Injective (localizationToLaurent R s) := by
  apply (IsLocalization.injective_iff_map_algebraMap_eq
    (Submonoid.powers (baseProduct R s)) (localizationToLaurent R s)).mpr
  intro p q
  constructor
  · intro h
    exact congrArg (localizationToLaurent R s) h
  · intro h
    simp only [localizationToLaurent_algebraMap] at h
    exact congrArg (algebraMap (Base R) (coordinateLocalization R s))
      (baseToLaurent_injective R h)

theorem localizationToLaurent_hasPoles (s : Finset (Fin 2))
    (z : coordinateLocalization R s) : HasPoles s (localizationToLaurent R s z) := by
  obtain ⟨n, p, hp⟩ := IsLocalization.Away.surj (baseProduct R s) z
  have hh := congrArg (localizationToLaurent R s) hp
  simp only [map_mul, map_pow, localizationToLaurent_algebraMap,
    baseToLaurent_baseProduct, T_pow] at hh
  have hrep : localizationToLaurent R s z =
      baseToLaurent R p * T R (-(n • openExponent s)) := by
    have hm := congrArg (fun t ↦ t * T R (-(n • openExponent s))) hh
    simpa only [mul_assoc, T_mul, add_neg_cancel, T_zero, mul_one] using hm
  rw [hrep]
  intro e i hi hneg
  rw [coeff_mul_T]
  apply baseToLaurent_hasPoles R p _ i (by simp)
  simpa [Pi.sub_apply, Pi.neg_apply, Pi.smul_apply, openExponent, hi] using hneg

/-- A single common monomial denominator clears the poles of any finite
Laurent sum; its existence is proved from the finite coefficient support. -/
theorem exists_clear_poles (s : Finset (Fin 2)) (p : Laurent (R := R))
    (hp : HasPoles s p) :
    ∃ n : ℕ, HasPoles ∅ (p * T R (n • openExponent s)) := by
  classical
  let n := p.coeff.support.sup (fun e ↦ Finset.univ.sup (fun i : Fin 2 ↦ (-e i).toNat))
  refine ⟨n, ?_⟩
  intro e i _ hneg
  rw [coeff_mul_T]
  by_contra hne
  have hs : e - n • openExponent s ∈ p.coeff.support := Finsupp.mem_support_iff.mpr hne
  by_cases hi : i ∈ s
  · have hbound : (-((e - n • openExponent s) i)).toNat ≤ n :=
      (Finset.le_sup (f := fun i : Fin 2 ↦ (-((e - n • openExponent s) i)).toNat)
        (Finset.mem_univ i)).trans
          (Finset.le_sup (f := fun e : LaurentExponent ↦
            Finset.univ.sup (fun i : Fin 2 ↦ (-e i).toNat)) hs)
    have hcast : ((-((e - n • openExponent s) i)).toNat : ℤ) ≤ (n : ℤ) := by
      exact_mod_cast hbound
    have hle := (Int.self_le_toNat (-((e - n • openExponent s) i))).trans hcast
    have hexp : (n • openExponent s) i = (n : ℤ) := by
      change n • (openExponent s i) = (n : ℤ)
      simp [openExponent, hi]
    change -(e i - (n • openExponent s) i) ≤ (n : ℤ) at hle
    rw [hexp] at hle
    omega
  · apply hne
    apply hp _ i hi
    simpa [Pi.sub_apply, Pi.smul_apply, openExponent, hi] using hneg

theorem mem_range_localizationToLaurent (s : Finset (Fin 2)) (p : Laurent (R := R)) :
    p ∈ Set.range (localizationToLaurent R s) ↔ HasPoles s p := by
  constructor
  · rintro ⟨z, rfl⟩
    exact localizationToLaurent_hasPoles R s z
  · intro hp
    obtain ⟨n, hn⟩ := exists_clear_poles R s p hp
    obtain ⟨a, ha⟩ := (mem_range_baseToLaurent R _).mpr hn
    let den : Submonoid.powers (baseProduct R s) := ⟨baseProduct R s ^ n, n, rfl⟩
    let z := IsLocalization.mk' (coordinateLocalization R s) a den
    refine ⟨z, ?_⟩
    have hz : z * algebraMap (Base R) (coordinateLocalization R s) (baseProduct R s ^ n) =
        algebraMap (Base R) (coordinateLocalization R s) a :=
      IsLocalization.mk'_spec (coordinateLocalization R s) a den
    have hh := congrArg (localizationToLaurent R s) hz
    simp only [map_mul, localizationToLaurent_algebraMap, map_pow,
      baseToLaurent_baseProduct, T_pow] at hh
    rw [ha] at hh
    have hm := congrArg (fun t ↦ t * T R (-(n • openExponent s))) hh
    simpa only [mul_assoc, T_mul, add_neg_cancel, T_zero, mul_one] using hm

end CycleQ2CurveCechLocalization

#print axioms CycleQ2CurveCechLocalization.mem_range_localizationToLaurent
end
end


/- Component: continuation_3/SeedCechLocalizedBasis.lean -/
section
/-! # The actual localized seed quotient in the nine Laurent coordinates -/

noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2SeedCechLocalizedBasis

open MvPolynomial CycleQ2SegreTangentLocal CycleQ2SeedQuotientFiniteFree
  CycleQ2SeedCechThreeOpen CycleQ2SeedCechLocalization

variable (R : Type*) [CommRing R]

abbrev SeedLocal (r ι : R) (s : Finset (Fin 3)) :=
  Localization (Algebra.algebraMapSubmonoid (SeedRing r ι)
    (Submonoid.powers (baseProduct R s)))

instance seedLocalBaseAlgebra (r ι : R) (s : Finset (Fin 3)) :
    Algebra (coordinateLocalization R s) (SeedLocal R r ι s) :=
  localizationAlgebra (Rₘ := coordinateLocalization R s) (Sₘ := SeedLocal R r ι s)
    (Submonoid.powers (baseProduct R s)) (SeedRing r ι)

instance seedLocalBaseTower (r ι : R) (s : Finset (Fin 3)) :
    IsScalarTower (Base R) (coordinateLocalization R s) (SeedLocal R r ι s) :=
  isScalarTower_localizationAlgebra (Rₘ := coordinateLocalization R s)
    (Sₘ := SeedLocal R r ι s) (Submonoid.powers (baseProduct R s)) (SeedRing r ι)

def localizedBasis [Nontrivial R] (r ι : R) (s : Finset (Fin 3)) :
    Module.Basis ShiftIndex (coordinateLocalization R s) (SeedLocal R r ι s) :=
  (seedBasis R r ι).localizationLocalization (coordinateLocalization R s)
    (Submonoid.powers (baseProduct R s)) (SeedLocal R r ι s)

@[simp] theorem localizedBasis_apply [Nontrivial R] (r ι : R)
    (s : Finset (Fin 3)) (ab : ShiftIndex) :
    localizedBasis R r ι s ab = algebraMap (SeedRing r ι) (SeedLocal R r ι s)
      (seedBasis R r ι ab) := by
  exact Module.Basis.localizationLocalization_apply _ _ _ _ _

@[simp] theorem localizedBasis_repr_algebraMap [Nontrivial R] (r ι : R)
    (s : Finset (Fin 3)) (p : SeedRing r ι) (ab : ShiftIndex) :
    (localizedBasis R r ι s).repr (algebraMap (SeedRing r ι) (SeedLocal R r ι s) p) ab =
      algebraMap (Base R) (coordinateLocalization R s) ((seedBasis R r ι).repr p ab) := by
  exact Module.Basis.localizationLocalization_repr_algebraMap _ _ _ _ _ _

def localizedCoordinates [Nontrivial R] (r ι : R) (s : Finset (Fin 3)) :
    SeedLocal R r ι s →+ (ShiftIndex → Laurent (R := R)) where
  toFun p ab := localizationToLaurent R s ((localizedBasis R r ι s).repr p ab)
  map_zero' := by ext ab; simp
  map_add' p q := by ext ab; simp

theorem localizedCoordinates_injective [Nontrivial R] (r ι : R) (s : Finset (Fin 3)) :
    Function.Injective (localizedCoordinates R r ι s) := by
  intro p q hpq
  apply (localizedBasis R r ι s).repr.injective
  ext ab
  exact localizationToLaurent_injective R s (congrFun hpq ab)

theorem localizedCoordinates_hasPoles [Nontrivial R] (r ι : R) (s : Finset (Fin 3))
    (p : SeedLocal R r ι s) (ab : ShiftIndex) :
    HasPoles s (localizedCoordinates R r ι s p ab) :=
  localizationToLaurent_hasPoles R s _

theorem mem_range_localizedCoordinates [Nontrivial R] (r ι : R) (s : Finset (Fin 3))
    (p : ShiftIndex → Laurent (R := R)) :
    p ∈ Set.range (localizedCoordinates R r ι s) ↔ ∀ ab, HasPoles s (p ab) := by
  constructor
  · rintro ⟨p, rfl⟩ ab
    exact localizedCoordinates_hasPoles R r ι s p ab
  · intro hp
    choose a ha using fun ab ↦ (mem_range_localizationToLaurent R s (p ab)).mpr (hp ab)
    refine ⟨(localizedBasis R r ι s).repr.symm (Finsupp.equivFunOnFinite.symm a), ?_⟩
    funext ab
    change localizationToLaurent R s
      ((localizedBasis R r ι s).repr ((localizedBasis R r ι s).repr.symm
        (Finsupp.equivFunOnFinite.symm a)) ab) = p ab
    simpa using ha ab

@[simp] theorem localizedCoordinates_algebraMap [Nontrivial R] (r ι : R)
    (s : Finset (Fin 3)) (p : SeedRing r ι) (ab : ShiftIndex) :
    localizedCoordinates R r ι s (algebraMap (SeedRing r ι) (SeedLocal R r ι s) p) ab =
      baseToLaurent R ((seedBasis R r ι).repr p ab) := by
  simp [localizedCoordinates]

@[simp] theorem localizedCoordinates_smul [Nontrivial R] (r ι : R)
    (s : Finset (Fin 3)) (a : coordinateLocalization R s) (p : SeedLocal R r ι s)
    (ab : ShiftIndex) :
    localizedCoordinates R r ι s (a • p) ab =
      localizationToLaurent R s a * localizedCoordinates R r ι s p ab := by
  simp [localizedCoordinates, Finsupp.smul_apply, smul_eq_mul]

/-- Exactness of the three-open complex on actual localized seed rings,
expressed through their injective common Laurent coordinates. -/
theorem localized_nineSummand_kernel [Nontrivial R] (r ι : R) (g : LaurentGrade)
    (p01 : SeedLocal R r ι {0, 1}) (p02 : SeedLocal R r ι {0, 2})
    (p12 : SeedLocal R r ι {1, 2})
    (hg01 : ∀ ab, HasGrade ab g (localizedCoordinates R r ι {0, 1} p01 ab))
    (hg02 : ∀ ab, HasGrade ab g (localizedCoordinates R r ι {0, 2} p02 ab))
    (hg12 : ∀ ab, HasGrade ab g (localizedCoordinates R r ι {1, 2} p12 ab))
    (hc : ∀ ab, localizedCoordinates R r ι {0, 1} p01 ab -
      localizedCoordinates R r ι {0, 2} p02 ab +
      localizedCoordinates R r ι {1, 2} p12 ab = 0) :
    ∃ (q0 : SeedLocal R r ι {0}) (q1 : SeedLocal R r ι {1})
      (q2 : SeedLocal R r ι {2}),
      (∀ ab, HasGrade ab g (localizedCoordinates R r ι {0} q0 ab)) ∧
      (∀ ab, HasGrade ab g (localizedCoordinates R r ι {1} q1 ab)) ∧
      (∀ ab, HasGrade ab g (localizedCoordinates R r ι {2} q2 ab)) ∧
      (∀ ab, localizedCoordinates R r ι {0, 1} p01 ab =
        localizedCoordinates R r ι {1} q1 ab - localizedCoordinates R r ι {0} q0 ab) ∧
      (∀ ab, localizedCoordinates R r ι {0, 2} p02 ab =
        localizedCoordinates R r ι {2} q2 ab - localizedCoordinates R r ι {0} q0 ab) ∧
      (∀ ab, localizedCoordinates R r ι {1, 2} p12 ab =
        localizedCoordinates R r ι {2} q2 ab - localizedCoordinates R r ι {1} q1 ab) := by
  obtain ⟨q0, q1, q2, h0, h1, h2, hg0, hg1, hg2, he01, he02, he12⟩ :=
    nineSummand_kernel g
      (localizedCoordinates R r ι {0, 1} p01)
      (localizedCoordinates R r ι {0, 2} p02)
      (localizedCoordinates R r ι {1, 2} p12)
      (localizedCoordinates_hasPoles R r ι {0, 1} p01)
      (localizedCoordinates_hasPoles R r ι {0, 2} p02)
      (localizedCoordinates_hasPoles R r ι {1, 2} p12)
      hg01 hg02 hg12 hc
  obtain ⟨q0', hq0⟩ := (mem_range_localizedCoordinates R r ι {0} q0).mpr h0
  obtain ⟨q1', hq1⟩ := (mem_range_localizedCoordinates R r ι {1} q1).mpr h1
  obtain ⟨q2', hq2⟩ := (mem_range_localizedCoordinates R r ι {2} q2).mpr h2
  refine ⟨q0', q1', q2', ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [hq0, hq1, hq2] <;> assumption

end CycleQ2SeedCechLocalizedBasis

#print axioms CycleQ2SeedCechLocalizedBasis.mem_range_localizedCoordinates

#print axioms CycleQ2SeedCechLocalizedBasis.localized_nineSummand_kernel
end
end


/- Component: continuation_3/cylinder_bridge/SeedCechThetaResidue.lean -/
section
/-! The smooth incidence trace row is an actual all-poles Čech functional.
The nine coefficients are computed from quotient-ring Laurent charts, not
assumed from the saved numerical array. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000

namespace CycleQ2SeedCechTheta
open MvPolynomial CycleQ2SeedTrace CycleQ2CechLinearCubic
open CycleQ2SeedCech (PS LS firstJet seriesMap)

theorem false_derivative_residue (r θ : ℂ) (p : Poly) :
    fractionResidue r θ false (derivativeNumerator p) 2 4 = 0 := by
  rw [derivative_fractionResidue]
  have hh : firstJet (powerCoefficient r θ false (derivativeIntegral r θ false p)) = 0 := by
    rw [firstJet_powerCoefficient, false_jet_derivativeIntegral, map_zero]
  exact congrArg TrivSqZeroExt.snd hh

theorem true_derivative_column_residue (r θ : ℂ) (j : Fin 9) :
    fractionResidue r θ true (derivativeNumerator (cubicColumn j)) 2 4 =
      (trueJetVector r θ j).snd := by
  rw [derivative_fractionResidue]
  have hh := firstJet_powerCoefficient r θ true (derivativeIntegral r θ true (cubicColumn j))
  rw [true_jet_derivative_columns] at hh
  exact congrArg TrivSqZeroExt.snd hh

/-- The ordering is exactly the nine h-monomials of the Segre incidence
Jacobian.  The x₃³ entry varies with θ; the sparse and smooth rows differ. -/
def derivativeTraceCoefficients (θ : ℂ) : Fin 9 → ℂ :=
  ![0, θ*Complex.I/6, 0, 0, 0, 0, 0, 0, -(1+Complex.I)/6]

theorem negative_trueJetVector_snd (r θ : ℂ) (j : Fin 9) :
    -(trueJetVector r θ j).snd = (3*r) * derivativeTraceCoefficients θ j := by
  fin_cases j <;>
    norm_num [trueJetVector, derivativeTraceCoefficients, firstJet, kappa,
      Matrix.cons_val_zero', Matrix.cons_val_succ', smul_eq_mul, op_smul_eq_smul] <;>
    ring_nf <;> norm_num [Complex.I_sq]

/-- Direct actual Laurent-residue computation for all nine cubic columns
and every θ, including θ=1 from the smooth incidence seed. -/
theorem derivative_column_residue (r θ : ℂ) (j : Fin 9) :
    cechResidue r θ (derivativeNumerator (cubicColumn j)) 2 4 =
      (3*r) * derivativeTraceCoefficients θ j := by
  rw [cechResidue, false_derivative_residue, true_derivative_column_residue,
    zero_sub, negative_trueJetVector_snd]

theorem endpointResidue_scalar (r θ : ℂ) (e : Bool) (c : ℂ) (z : LaurentChart r θ e) :
    endpointResidue r θ e (laurentBase r θ e (seriesMap (PowerSeries.C c)) * z) =
      c * endpointResidue r θ e z := by
  change (laurentCoefficient r θ e
    (laurentBase r θ e (seriesMap (PowerSeries.C c)) * z)).coeff (-1) = _
  unfold laurentCoefficient laurentBase
  rw [coefficient_base_mul]
  change (seriesMap (PowerSeries.C c) * laurentCoefficient r θ e z).coeff (-1) = _
  rw [show seriesMap (PowerSeries.C c) = HahnSeries.single (0 : ℤ) c from
    HahnSeries.ofPowerSeries_C c, HahnSeries.coeff_single_zero_mul]
  rfl

theorem cechResidue_C_mul (r θ : ℂ) (c : ℂ) (p : Poly) (n m : ℕ) :
    cechResidue r θ (C c * p) n m = c * cechResidue r θ p n m := by
  have he (e : Bool) : fraction r θ e (C c * p) n m =
      laurentBase r θ e (seriesMap (PowerSeries.C c)) * fraction r θ e p n m := by
    simp [fraction, laurentEval, powerEval, chartEmbedding, laurentBase, powerBase, mul_assoc]
  simp only [cechResidue, fractionResidue_eq_endpointResidue, he, endpointResidue_scalar]
  ring

def cubicDeformation (v : Fin 9 → ℂ) : Poly := ∑ j : Fin 9, C (v j) * cubicColumn j

def derivativeTrace (θ : ℂ) (v : Fin 9 → ℂ) : ℂ :=
  ∑ j : Fin 9, derivativeTraceCoefficients θ j * v j

theorem deformation_residue (r θ : ℂ) (v : Fin 9 → ℂ) :
    cechResidue r θ (derivativeNumerator (cubicDeformation v)) 2 4 =
      (3*r) * derivativeTrace θ v := by
  have he : derivativeNumerator (cubicDeformation v) =
      ∑ j : Fin 9, C (v j) * derivativeNumerator (cubicColumn j) := by
    unfold derivativeNumerator cubicDeformation
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [he, cechResidue_sum]
  simp only [cechResidue_C_mul, derivative_column_residue, derivativeTrace, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem derivativeTrace_explicit (θ : ℂ) (v : Fin 9 → ℂ) :
    derivativeTrace θ v = (θ*Complex.I*v 1-(1+Complex.I)*v 8)/6 := by
  norm_num [derivativeTrace, derivativeTraceCoefficients, Fin.sum_univ_succ,
    Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.head_cons, Matrix.tail_cons,
    Fin.reduceSucc]
  rw [show ((Fin.succ (2 : Fin 3)).succ.succ.succ.succ.succ : Fin 9) = 8 from rfl]
  ring

/-- Exact characteristic-zero version of the two-entry functional used in
segre_trace_tangent.py.  No sparse-matrix invariance is assumed. -/
theorem smooth_derivativeTrace_explicit (v : Fin 9 → ℂ) :
    derivativeTrace 1 v = (Complex.I*v 1-(1+Complex.I)*v 8)/6 := by
  simpa using derivativeTrace_explicit 1 v

theorem normalized_deformation_residue (r θ : ℂ) (hr : r ≠ 0) (v : Fin 9 → ℂ) :
    cechResidue r θ (derivativeNumerator (cubicDeformation v)) 2 4 / (3*r) =
      derivativeTrace θ v := by
  rw [deformation_residue]
  exact mul_div_cancel_left₀ _ (mul_ne_zero (by norm_num) hr)

/-- A nonzero smooth incidence trace is now an actual non-coboundary, even
when arbitrary larger denominator powers are permitted. -/
theorem nonboundary_of_derivativeTrace_ne_zero (r θ : ℂ) (hr : r ≠ 0)
    (v : Fin 9 → ℂ) (hv : derivativeTrace θ v ≠ 0) :
    ¬ CechBoundary r θ (derivativeNumerator (cubicDeformation v)) 2 4 := by
  intro hb
  have hz := cechResidue_zero_of_boundary r θ _ 2 4 hb
  rw [deformation_residue] at hz
  exact (mul_ne_zero (mul_ne_zero (by norm_num) hr) hv) hz

def selectedTangent : Fin 9 → ℂ := ![0,0,0,0,0,0,0,Complex.I,Complex.I-1]

theorem selectedTangent_trace (θ : ℂ) : derivativeTrace θ selectedTangent = 1/3 := by
  rw [derivativeTrace_explicit]
  change (θ*Complex.I*0-(1+Complex.I)*(Complex.I-1))/6 = 1/3
  simp only [mul_zero, zero_sub]
  ring_nf
  norm_num [Complex.I_sq]

theorem selectedTangent_residue (r θ : ℂ) :
    cechResidue r θ (derivativeNumerator (cubicDeformation selectedTangent)) 2 4 = r := by
  rw [deformation_residue, selectedTangent_trace]
  ring

theorem selectedTangent_not_boundary (r θ : ℂ) (hr : r ≠ 0) :
    ¬ CechBoundary r θ (derivativeNumerator (cubicDeformation selectedTangent)) 2 4 := by
  apply nonboundary_of_derivativeTrace_ne_zero r θ hr
  rw [selectedTangent_trace]
  norm_num

end CycleQ2SeedCechTheta

#print axioms CycleQ2SeedCechTheta.derivative_column_residue
#print axioms CycleQ2SeedCechTheta.deformation_residue
#print axioms CycleQ2SeedCechTheta.nonboundary_of_derivativeTrace_ne_zero
end
end


/- Component: continuation_3/SegreGaussianActionChecks22.lean -/
section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
namespace CycleQ2SegreGaussianActionData
open CycleQ2SparseGaussianPolynomial CycleQ2SegreGaussianTangentData
def actionError22 (a b : ℕ) : Towers :=
  addTowers (fastNormalizeTower a0 a1 b0 32 (mulTowers m22 (monomialTower oneLayers a b)))
    (negTowers (action22 a b))
private theorem checked_22_0_0 : checkTowers (actionError22 0 0) = true := by
  decide +kernel

private theorem checked_22_0_1 : checkTowers (actionError22 0 1) = true := by
  decide +kernel

private theorem checked_22_0_2 : checkTowers (actionError22 0 2) = true := by
  decide +kernel

private theorem checked_22_1_0 : checkTowers (actionError22 1 0) = true := by
  decide +kernel

private theorem checked_22_1_1 : checkTowers (actionError22 1 1) = true := by
  decide +kernel

private theorem checked_22_1_2 : checkTowers (actionError22 1 2) = true := by
  decide +kernel

private theorem checked_22_2_0 : checkTowers (actionError22 2 0) = true := by
  decide +kernel

private theorem checked_22_2_1 : checkTowers (actionError22 2 1) = true := by
  decide +kernel

private theorem checked_22_2_2 : checkTowers (actionError22 2 2) = true := by
  decide +kernel

theorem action_check22 (a b : Fin 3) : checkTowers (actionError22 a b) = true := by
  fin_cases a <;> fin_cases b
  · exact checked_22_0_0
  · exact checked_22_0_1
  · exact checked_22_0_2
  · exact checked_22_1_0
  · exact checked_22_1_1
  · exact checked_22_1_2
  · exact checked_22_2_0
  · exact checked_22_2_1
  · exact checked_22_2_2
end CycleQ2SegreGaussianActionData
#print axioms CycleQ2SegreGaussianActionData.action_check22
end


/- Component: continuation_3/SegreModularActionFlat.lean -/
section
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
set_option Elab.async false

namespace CycleQ2SegreModularDetectorExpressions
open CycleQ2SparseModularFunctional CycleQ2SparseGaussianPolynomial CycleQ2SegreGaussianActionData

def actionTable : Fin 3 → Fin 3 → ℕ → ℕ → Towers :=
  ![![action00, action01, action02], ![action10, action11, action12], ![action20, action21, action22]]

def flatIndexed : Fin 3 → Fin 3 → Fin 3 → Fin 3 → Sparse :=
  ![![![![flat00_00, flat00_01, flat00_02], ![flat00_10, flat00_11, flat00_12], ![flat00_20, flat00_21, flat00_22]], ![![flat01_00, flat01_01, flat01_02], ![flat01_10, flat01_11, flat01_12], ![flat01_20, flat01_21, flat01_22]], ![![flat02_00, flat02_01, flat02_02], ![flat02_10, flat02_11, flat02_12], ![flat02_20, flat02_21, flat02_22]]], ![![![flat10_00, flat10_01, flat10_02], ![flat10_10, flat10_11, flat10_12], ![flat10_20, flat10_21, flat10_22]], ![![flat11_00, flat11_01, flat11_02], ![flat11_10, flat11_11, flat11_12], ![flat11_20, flat11_21, flat11_22]], ![![flat12_00, flat12_01, flat12_02], ![flat12_10, flat12_11, flat12_12], ![flat12_20, flat12_21, flat12_22]]], ![![![flat20_00, flat20_01, flat20_02], ![flat20_10, flat20_11, flat20_12], ![flat20_20, flat20_21, flat20_22]], ![![flat21_00, flat21_01, flat21_02], ![flat21_10, flat21_11, flat21_12], ![flat21_20, flat21_21, flat21_22]], ![![flat22_00, flat22_01, flat22_02], ![flat22_10, flat22_11, flat22_12], ![flat22_20, flat22_21, flat22_22]]]]

theorem flatIndexed_eq (i j a b : Fin 3) :
    flatIndexed i j a b=flattenTowersData (actionTable i j a b) := by
  fin_cases i <;> fin_cases j <;> fin_cases a <;> fin_cases b
  · exact flat00_00_eq
  · exact flat00_01_eq
  · exact flat00_02_eq
  · exact flat00_10_eq
  · exact flat00_11_eq
  · exact flat00_12_eq
  · exact flat00_20_eq
  · exact flat00_21_eq
  · exact flat00_22_eq
  · exact flat01_00_eq
  · exact flat01_01_eq
  · exact flat01_02_eq
  · exact flat01_10_eq
  · exact flat01_11_eq
  · exact flat01_12_eq
  · exact flat01_20_eq
  · exact flat01_21_eq
  · exact flat01_22_eq
  · exact flat02_00_eq
  · exact flat02_01_eq
  · exact flat02_02_eq
  · exact flat02_10_eq
  · exact flat02_11_eq
  · exact flat02_12_eq
  · exact flat02_20_eq
  · exact flat02_21_eq
  · exact flat02_22_eq
  · exact flat10_00_eq
  · exact flat10_01_eq
  · exact flat10_02_eq
  · exact flat10_10_eq
  · exact flat10_11_eq
  · exact flat10_12_eq
  · exact flat10_20_eq
  · exact flat10_21_eq
  · exact flat10_22_eq
  · exact flat11_00_eq
  · exact flat11_01_eq
  · exact flat11_02_eq
  · exact flat11_10_eq
  · exact flat11_11_eq
  · exact flat11_12_eq
  · exact flat11_20_eq
  · exact flat11_21_eq
  · exact flat11_22_eq
  · exact flat12_00_eq
  · exact flat12_01_eq
  · exact flat12_02_eq
  · exact flat12_10_eq
  · exact flat12_11_eq
  · exact flat12_12_eq
  · exact flat12_20_eq
  · exact flat12_21_eq
  · exact flat12_22_eq
  · exact flat20_00_eq
  · exact flat20_01_eq
  · exact flat20_02_eq
  · exact flat20_10_eq
  · exact flat20_11_eq
  · exact flat20_12_eq
  · exact flat20_20_eq
  · exact flat20_21_eq
  · exact flat20_22_eq
  · exact flat21_00_eq
  · exact flat21_01_eq
  · exact flat21_02_eq
  · exact flat21_10_eq
  · exact flat21_11_eq
  · exact flat21_12_eq
  · exact flat21_20_eq
  · exact flat21_21_eq
  · exact flat21_22_eq
  · exact flat22_00_eq
  · exact flat22_01_eq
  · exact flat22_02_eq
  · exact flat22_10_eq
  · exact flat22_11_eq
  · exact flat22_12_eq
  · exact flat22_20_eq
  · exact flat22_21_eq
  · exact flat22_22_eq

def flatActionTable (i j : Fin 3) (a b : ℕ) : Sparse :=
  if ha : a<3 then if hb : b<3 then flatIndexed i j ⟨a,ha⟩ ⟨b,hb⟩
    else flattenTowersData (actionTable i j a b)
  else flattenTowersData (actionTable i j a b)

theorem flatActionTable_eq (i j : Fin 3) (a b : ℕ) :
    flatActionTable i j a b=flattenTowersData (actionTable i j a b) := by
  unfold flatActionTable
  split_ifs with ha hb
  · exact flatIndexed_eq i j ⟨a,ha⟩ ⟨b,hb⟩
  · rfl
  · rfl

end CycleQ2SegreModularDetectorExpressions
#print axioms CycleQ2SegreModularDetectorExpressions.flatActionTable_eq
end


/- Component: continuation_3/SegreModularCubicChecks0.lean -/
section
set_option maxHeartbeats 2000000000
set_option maxRecDepth 100000
set_option Elab.async false
namespace CycleQ2SegreModularCubicData
open CycleQ2SparseGaussianPolynomial CycleQ2SegreGaussianTangentData

def kqError0 : Towers := addTowers (normalizeTower a0 a1 b0 32 (mulTowers k q00)) (negTowers kq0)
theorem kq_check0 : checkTowers kqError0=true := by decide +kernel

theorem eval_kq0 {R : Type*} [CommRing R]
    (φ : GaussianInt →+* R) (x : Fin 5 → R) (w z v : R)
    (hz : z^3=evalLayers φ x v a0+evalLayers φ x v a1*z)
    (hw : w^3=evalLayers φ x v b0-z^6) :
    evalTowers φ x w z v kq0=evalTowers φ x w z v k * evalTowers φ x w z v q00 := by
  rw [evaluation_of_normal_error_check φ x w z v a0 a1 b0 hz hw 32 (mulTowers k q00) kq0 kq_check0,eval_mulTowers]

def cubicError0_0 : Towers := addTowers
  (normalizeTower a0 a1 b0 32 (mulTowers monomialCubic0 kq0)) (negTowers cubic0_0)
theorem cubic_check0_0 : checkTowers cubicError0_0=true := by decide +kernel

theorem eval_cubic0_0 {R : Type*} [CommRing R]
    (φ : GaussianInt →+* R) (x : Fin 5 → R) (w z v : R)
    (hz : z^3=evalLayers φ x v a0+evalLayers φ x v a1*z)
    (hw : w^3=evalLayers φ x v b0-z^6) :
    evalTowers φ x w z v cubic0_0=evalTowers φ x w z v monomialCubic0 *
      evalTowers φ x w z v k * evalTowers φ x w z v q00 := by
  rw [evaluation_of_normal_error_check φ x w z v a0 a1 b0 hz hw 32
    (mulTowers monomialCubic0 kq0) cubic0_0 cubic_check0_0,
    eval_mulTowers,eval_kq0 φ x w z v hz hw,mul_assoc]

def cubicError0_1 : Towers := addTowers
  (normalizeTower a0 a1 b0 32 (mulTowers monomialCubic1 kq0)) (negTowers cubic0_1)
theorem cubic_check0_1 : checkTowers cubicError0_1=true := by decide +kernel

theorem eval_cubic0_1 {R : Type*} [CommRing R]
    (φ : GaussianInt →+* R) (x : Fin 5 → R) (w z v : R)
    (hz : z^3=evalLayers φ x v a0+evalLayers φ x v a1*z)
    (hw : w^3=evalLayers φ x v b0-z^6) :
    evalTowers φ x w z v cubic0_1=evalTowers φ x w z v monomialCubic1 *
      evalTowers φ x w z v k * evalTowers φ x w z v q00 := by
  rw [evaluation_of_normal_error_check φ x w z v a0 a1 b0 hz hw 32
    (mulTowers monomialCubic1 kq0) cubic0_1 cubic_check0_1,
    eval_mulTowers,eval_kq0 φ x w z v hz hw,mul_assoc]

def cubicError0_2 : Towers := addTowers
  (normalizeTower a0 a1 b0 32 (mulTowers monomialCubic2 kq0)) (negTowers cubic0_2)
theorem cubic_check0_2 : checkTowers cubicError0_2=true := by decide +kernel

theorem eval_cubic0_2 {R : Type*} [CommRing R]
    (φ : GaussianInt →+* R) (x : Fin 5 → R) (w z v : R)
    (hz : z^3=evalLayers φ x v a0+evalLayers φ x v a1*z)
    (hw : w^3=evalLayers φ x v b0-z^6) :
    evalTowers φ x w z v cubic0_2=evalTowers φ x w z v monomialCubic2 *
      evalTowers φ x w z v k * evalTowers φ x w z v q00 := by
  rw [evaluation_of_normal_error_check φ x w z v a0 a1 b0 hz hw 32
    (mulTowers monomialCubic2 kq0) cubic0_2 cubic_check0_2,
    eval_mulTowers,eval_kq0 φ x w z v hz hw,mul_assoc]

def cubicError0_3 : Towers := addTowers
  (normalizeTower a0 a1 b0 32 (mulTowers monomialCubic3 kq0)) (negTowers cubic0_3)
theorem cubic_check0_3 : checkTowers cubicError0_3=true := by decide +kernel

theorem eval_cubic0_3 {R : Type*} [CommRing R]
    (φ : GaussianInt →+* R) (x : Fin 5 → R) (w z v : R)
    (hz : z^3=evalLayers φ x v a0+evalLayers φ x v a1*z)
    (hw : w^3=evalLayers φ x v b0-z^6) :
    evalTowers φ x w z v cubic0_3=evalTowers φ x w z v monomialCubic3 *
      evalTowers φ x w z v k * evalTowers φ x w z v q00 := by
  rw [evaluation_of_normal_error_check φ x w z v a0 a1 b0 hz hw 32
    (mulTowers monomialCubic3 kq0) cubic0_3 cubic_check0_3,
    eval_mulTowers,eval_kq0 φ x w z v hz hw,mul_assoc]

def cubicError0_4 : Towers := addTowers
  (normalizeTower a0 a1 b0 32 (mulTowers monomialCubic4 kq0)) (negTowers cubic0_4)
theorem cubic_check0_4 : checkTowers cubicError0_4=true := by decide +kernel

theorem eval_cubic0_4 {R : Type*} [CommRing R]
    (φ : GaussianInt →+* R) (x : Fin 5 → R) (w z v : R)
    (hz : z^3=evalLayers φ x v a0+evalLayers φ x v a1*z)
    (hw : w^3=evalLayers φ x v b0-z^6) :
    evalTowers φ x w z v cubic0_4=evalTowers φ x w z v monomialCubic4 *
      evalTowers φ x w z v k * evalTowers φ x w z v q00 := by
  rw [evaluation_of_normal_error_check φ x w z v a0 a1 b0 hz hw 32
    (mulTowers monomialCubic4 kq0) cubic0_4 cubic_check0_4,
    eval_mulTowers,eval_kq0 φ x w z v hz hw,mul_assoc]

def cubicError0_5 : Towers := addTowers
  (normalizeTower a0 a1 b0 32 (mulTowers monomialCubic5 kq0)) (negTowers cubic0_5)
theorem cubic_check0_5 : checkTowers cubicError0_5=true := by decide +kernel

theorem eval_cubic0_5 {R : Type*} [CommRing R]
    (φ : GaussianInt →+* R) (x : Fin 5 → R) (w z v : R)
    (hz : z^3=evalLayers φ x v a0+evalLayers φ x v a1*z)
    (hw : w^3=evalLayers φ x v b0-z^6) :
    evalTowers φ x w z v cubic0_5=evalTowers φ x w z v monomialCubic5 *
      evalTowers φ x w z v k * evalTowers φ x w z v q00 := by
  rw [evaluation_of_normal_error_check φ x w z v a0 a1 b0 hz hw 32
    (mulTowers monomialCubic5 kq0) cubic0_5 cubic_check0_5,
    eval_mulTowers,eval_kq0 φ x w z v hz hw,mul_assoc]

def cubicError0_6 : Towers := addTowers
  (normalizeTower a0 a1 b0 32 (mulTowers monomialCubic6 kq0)) (negTowers cubic0_6)
theorem cubic_check0_6 : checkTowers cubicError0_6=true := by decide +kernel

theorem eval_cubic0_6 {R : Type*} [CommRing R]
    (φ : GaussianInt →+* R) (x : Fin 5 → R) (w z v : R)
    (hz : z^3=evalLayers φ x v a0+evalLayers φ x v a1*z)
    (hw : w^3=evalLayers φ x v b0-z^6) :
    evalTowers φ x w z v cubic0_6=evalTowers φ x w z v monomialCubic6 *
      evalTowers φ x w z v k * evalTowers φ x w z v q00 := by
  rw [evaluation_of_normal_error_check φ x w z v a0 a1 b0 hz hw 32
    (mulTowers monomialCubic6 kq0) cubic0_6 cubic_check0_6,
    eval_mulTowers,eval_kq0 φ x w z v hz hw,mul_assoc]

def cubicError0_7 : Towers := addTowers
  (normalizeTower a0 a1 b0 32 (mulTowers monomialCubic7 kq0)) (negTowers cubic0_7)
theorem cubic_check0_7 : checkTowers cubicError0_7=true := by decide +kernel

theorem eval_cubic0_7 {R : Type*} [CommRing R]
    (φ : GaussianInt →+* R) (x : Fin 5 → R) (w z v : R)
    (hz : z^3=evalLayers φ x v a0+evalLayers φ x v a1*z)
    (hw : w^3=evalLayers φ x v b0-z^6) :
    evalTowers φ x w z v cubic0_7=evalTowers φ x w z v monomialCubic7 *
      evalTowers φ x w z v k * evalTowers φ x w z v q00 := by
  rw [evaluation_of_normal_error_check φ x w z v a0 a1 b0 hz hw 32
    (mulTowers monomialCubic7 kq0) cubic0_7 cubic_check0_7,
    eval_mulTowers,eval_kq0 φ x w z v hz hw,mul_assoc]

def cubicError0_8 : Towers := addTowers
  (normalizeTower a0 a1 b0 32 (mulTowers monomialCubic8 kq0)) (negTowers cubic0_8)
theorem cubic_check0_8 : checkTowers cubicError0_8=true := by decide +kernel

theorem eval_cubic0_8 {R : Type*} [CommRing R]
    (φ : GaussianInt →+* R) (x : Fin 5 → R) (w z v : R)
    (hz : z^3=evalLayers φ x v a0+evalLayers φ x v a1*z)
    (hw : w^3=evalLayers φ x v b0-z^6) :
    evalTowers φ x w z v cubic0_8=evalTowers φ x w z v monomialCubic8 *
      evalTowers φ x w z v k * evalTowers φ x w z v q00 := by
  rw [evaluation_of_normal_error_check φ x w z v a0 a1 b0 hz hw 32
    (mulTowers monomialCubic8 kq0) cubic0_8 cubic_check0_8,
    eval_mulTowers,eval_kq0 φ x w z v hz hw,mul_assoc]

end CycleQ2SegreModularCubicData
#print axioms CycleQ2SegreModularCubicData.eval_cubic0_8
end


/- Component: continuation_3/SegreModularCubicChecks1.lean -/
section
set_option maxHeartbeats 2000000000
set_option maxRecDepth 100000
set_option Elab.async false
namespace CycleQ2SegreModularCubicData
open CycleQ2SparseGaussianPolynomial CycleQ2SegreGaussianTangentData

def kqError1 : Towers := addTowers (normalizeTower a0 a1 b0 32 (mulTowers k q01)) (negTowers kq1)
theorem kq_check1 : checkTowers kqError1=true := by decide +kernel

theorem eval_kq1 {R : Type*} [CommRing R]
    (φ : GaussianInt →+* R) (x : Fin 5 → R) (w z v : R)
    (hz : z^3=evalLayers φ x v a0+evalLayers φ x v a1*z)
    (hw : w^3=evalLayers φ x v b0-z^6) :
    evalTowers φ x w z v kq1=evalTowers φ x w z v k * evalTowers φ x w z v q01 := by
  rw [evaluation_of_normal_error_check φ x w z v a0 a1 b0 hz hw 32 (mulTowers k q01) kq1 kq_check1,eval_mulTowers]

def cubicError1_0 : Towers := addTowers
  (normalizeTower a0 a1 b0 32 (mulTowers monomialCubic0 kq1)) (negTowers cubic1_0)
theorem cubic_check1_0 : checkTowers cubicError1_0=true := by decide +kernel

theorem eval_cubic1_0 {R : Type*} [CommRing R]
    (φ : GaussianInt →+* R) (x : Fin 5 → R) (w z v : R)
    (hz : z^3=evalLayers φ x v a0+evalLayers φ x v a1*z)
    (hw : w^3=evalLayers φ x v b0-z^6) :
    evalTowers φ x w z v cubic1_0=evalTowers φ x w z v monomialCubic0 *
      evalTowers φ x w z v k * evalTowers φ x w z v q01 := by
  rw [evaluation_of_normal_error_check φ x w z v a0 a1 b0 hz hw 32
    (mulTowers monomialCubic0 kq1) cubic1_0 cubic_check1_0,
    eval_mulTowers,eval_kq1 φ x w z v hz hw,mul_assoc]

def cubicError1_1 : Towers := addTowers
  (normalizeTower a0 a1 b0 32 (mulTowers monomialCubic1 kq1)) (negTowers cubic1_1)
theorem cubic_check1_1 : checkTowers cubicError1_1=true := by decide +kernel

theorem eval_cubic1_1 {R : Type*} [CommRing R]
    (φ : GaussianInt →+* R) (x : Fin 5 → R) (w z v : R)
    (hz : z^3=evalLayers φ x v a0+evalLayers φ x v a1*z)
    (hw : w^3=evalLayers φ x v b0-z^6) :
    evalTowers φ x w z v cubic1_1=evalTowers φ x w z v monomialCubic1 *
      evalTowers φ x w z v k * evalTowers φ x w z v q01 := by
  rw [evaluation_of_normal_error_check φ x w z v a0 a1 b0 hz hw 32
    (mulTowers monomialCubic1 kq1) cubic1_1 cubic_check1_1,
    eval_mulTowers,eval_kq1 φ x w z v hz hw,mul_assoc]

def cubicError1_2 : Towers := addTowers
  (normalizeTower a0 a1 b0 32 (mulTowers monomialCubic2 kq1)) (negTowers cubic1_2)
theorem cubic_check1_2 : checkTowers cubicError1_2=true := by decide +kernel

theorem eval_cubic1_2 {R : Type*} [CommRing R]
    (φ : GaussianInt →+* R) (x : Fin 5 → R) (w z v : R)
    (hz : z^3=evalLayers φ x v a0+evalLayers φ x v a1*z)
    (hw : w^3=evalLayers φ x v b0-z^6) :
    evalTowers φ x w z v cubic1_2=evalTowers φ x w z v monomialCubic2 *
      evalTowers φ x w z v k * evalTowers φ x w z v q01 := by
  rw [evaluation_of_normal_error_check φ x w z v a0 a1 b0 hz hw 32
    (mulTowers monomialCubic2 kq1) cubic1_2 cubic_check1_2,
    eval_mulTowers,eval_kq1 φ x w z v hz hw,mul_assoc]

def cubicError1_3 : Towers := addTowers
  (normalizeTower a0 a1 b0 32 (mulTowers monomialCubic3 kq1)) (negTowers cubic1_3)
theorem cubic_check1_3 : checkTowers cubicError1_3=true := by decide +kernel

theorem eval_cubic1_3 {R : Type*} [CommRing R]
    (φ : GaussianInt →+* R) (x : Fin 5 → R) (w z v : R)
    (hz : z^3=evalLayers φ x v a0+evalLayers φ x v a1*z)
    (hw : w^3=evalLayers φ x v b0-z^6) :
    evalTowers φ x w z v cubic1_3=evalTowers φ x w z v monomialCubic3 *
      evalTowers φ x w z v k * evalTowers φ x w z v q01 := by
  rw [evaluation_of_normal_error_check φ x w z v a0 a1 b0 hz hw 32
    (mulTowers monomialCubic3 kq1) cubic1_3 cubic_check1_3,
    eval_mulTowers,eval_kq1 φ x w z v hz hw,mul_assoc]

def cubicError1_4 : Towers := addTowers
  (normalizeTower a0 a1 b0 32 (mulTowers monomialCubic4 kq1)) (negTowers cubic1_4)
theorem cubic_check1_4 : checkTowers cubicError1_4=true := by decide +kernel

theorem eval_cubic1_4 {R : Type*} [CommRing R]
    (φ : GaussianInt →+* R) (x : Fin 5 → R) (w z v : R)
    (hz : z^3=evalLayers φ x v a0+evalLayers φ x v a1*z)
    (hw : w^3=evalLayers φ x v b0-z^6) :
    evalTowers φ x w z v cubic1_4=evalTowers φ x w z v monomialCubic4 *
      evalTowers φ x w z v k * evalTowers φ x w z v q01 := by
  rw [evaluation_of_normal_error_check φ x w z v a0 a1 b0 hz hw 32
    (mulTowers monomialCubic4 kq1) cubic1_4 cubic_check1_4,
    eval_mulTowers,eval_kq1 φ x w z v hz hw,mul_assoc]

def cubicError1_5 : Towers := addTowers
  (normalizeTower a0 a1 b0 32 (mulTowers monomialCubic5 kq1)) (negTowers cubic1_5)
theorem cubic_check1_5 : checkTowers cubicError1_5=true := by decide +kernel

theorem eval_cubic1_5 {R : Type*} [CommRing R]
    (φ : GaussianInt →+* R) (x : Fin 5 → R) (w z v : R)
    (hz : z^3=evalLayers φ x v a0+evalLayers φ x v a1*z)
    (hw : w^3=evalLayers φ x v b0-z^6) :
    evalTowers φ x w z v cubic1_5=evalTowers φ x w z v monomialCubic5 *
      evalTowers φ x w z v k * evalTowers φ x w z v q01 := by
  rw [evaluation_of_normal_error_check φ x w z v a0 a1 b0 hz hw 32
    (mulTowers monomialCubic5 kq1) cubic1_5 cubic_check1_5,
    eval_mulTowers,eval_kq1 φ x w z v hz hw,mul_assoc]

def cubicError1_6 : Towers := addTowers
  (normalizeTower a0 a1 b0 32 (mulTowers monomialCubic6 kq1)) (negTowers cubic1_6)
theorem cubic_check1_6 : checkTowers cubicError1_6=true := by decide +kernel

theorem eval_cubic1_6 {R : Type*} [CommRing R]
    (φ : GaussianInt →+* R) (x : Fin 5 → R) (w z v : R)
    (hz : z^3=evalLayers φ x v a0+evalLayers φ x v a1*z)
    (hw : w^3=evalLayers φ x v b0-z^6) :
    evalTowers φ x w z v cubic1_6=evalTowers φ x w z v monomialCubic6 *
      evalTowers φ x w z v k * evalTowers φ x w z v q01 := by
  rw [evaluation_of_normal_error_check φ x w z v a0 a1 b0 hz hw 32
    (mulTowers monomialCubic6 kq1) cubic1_6 cubic_check1_6,
    eval_mulTowers,eval_kq1 φ x w z v hz hw,mul_assoc]

def cubicError1_7 : Towers := addTowers
  (normalizeTower a0 a1 b0 32 (mulTowers monomialCubic7 kq1)) (negTowers cubic1_7)
theorem cubic_check1_7 : checkTowers cubicError1_7=true := by decide +kernel

theorem eval_cubic1_7 {R : Type*} [CommRing R]
    (φ : GaussianInt →+* R) (x : Fin 5 → R) (w z v : R)
    (hz : z^3=evalLayers φ x v a0+evalLayers φ x v a1*z)
    (hw : w^3=evalLayers φ x v b0-z^6) :
    evalTowers φ x w z v cubic1_7=evalTowers φ x w z v monomialCubic7 *
      evalTowers φ x w z v k * evalTowers φ x w z v q01 := by
  rw [evaluation_of_normal_error_check φ x w z v a0 a1 b0 hz hw 32
    (mulTowers monomialCubic7 kq1) cubic1_7 cubic_check1_7,
    eval_mulTowers,eval_kq1 φ x w z v hz hw,mul_assoc]

def cubicError1_8 : Towers := addTowers
  (normalizeTower a0 a1 b0 32 (mulTowers monomialCubic8 kq1)) (negTowers cubic1_8)
theorem cubic_check1_8 : checkTowers cubicError1_8=true := by decide +kernel

theorem eval_cubic1_8 {R : Type*} [CommRing R]
    (φ : GaussianInt →+* R) (x : Fin 5 → R) (w z v : R)
    (hz : z^3=evalLayers φ x v a0+evalLayers φ x v a1*z)
    (hw : w^3=evalLayers φ x v b0-z^6) :
    evalTowers φ x w z v cubic1_8=evalTowers φ x w z v monomialCubic8 *
      evalTowers φ x w z v k * evalTowers φ x w z v q01 := by
  rw [evaluation_of_normal_error_check φ x w z v a0 a1 b0 hz hw 32
    (mulTowers monomialCubic8 kq1) cubic1_8 cubic_check1_8,
    eval_mulTowers,eval_kq1 φ x w z v hz hw,mul_assoc]

end CycleQ2SegreModularCubicData
#print axioms CycleQ2SegreModularCubicData.eval_cubic1_8
end


/- Component: continuation_3/SegreModularCubicChecks2.lean -/
section
set_option maxHeartbeats 2000000000
set_option maxRecDepth 100000
set_option Elab.async false
namespace CycleQ2SegreModularCubicData
open CycleQ2SparseGaussianPolynomial CycleQ2SegreGaussianTangentData

def kqError2 : Towers := addTowers (normalizeTower a0 a1 b0 32 (mulTowers k q02)) (negTowers kq2)
private theorem kq_length2 : kqError2.length≤3 := by decide +kernel
private theorem kq_inner2 : ∀ b : Fin 3, (kqError2[b.val]?.getD []).length≤3 := by
  decide +kernel
private theorem kq_block2_0_0 : checkTowerBlock kqError2 0 0=true := by
  decide +kernel
private theorem kq_block2_0_1 : checkTowerBlock kqError2 0 1=true := by
  decide +kernel
private theorem kq_block2_0_2 : checkTowerBlock kqError2 0 2=true := by
  decide +kernel
private theorem kq_block2_1_0 : checkTowerBlock kqError2 1 0=true := by
  decide +kernel
private theorem kq_block2_1_1 : checkTowerBlock kqError2 1 1=true := by
  decide +kernel
private theorem kq_block2_1_2 : checkTowerBlock kqError2 1 2=true := by
  decide +kernel
private theorem kq_block2_2_0 : checkTowerBlock kqError2 2 0=true := by
  decide +kernel
private theorem kq_block2_2_1 : checkTowerBlock kqError2 2 1=true := by
  decide +kernel
private theorem kq_block2_2_2 : checkTowerBlock kqError2 2 2=true := by
  decide +kernel
private theorem kq_blocks2 (b a : Fin 3) : checkTowerBlock kqError2 b a=true := by
  fin_cases b <;> fin_cases a
  · exact kq_block2_0_0
  · exact kq_block2_0_1
  · exact kq_block2_0_2
  · exact kq_block2_1_0
  · exact kq_block2_1_1
  · exact kq_block2_1_2
  · exact kq_block2_2_0
  · exact kq_block2_2_1
  · exact kq_block2_2_2

theorem eval_kq2 {R : Type*} [CommRing R]
    (φ : GaussianInt →+* R) (x : Fin 5 → R) (w z v : R)
    (hz : z^3=evalLayers φ x v a0+evalLayers φ x v a1*z)
    (hw : w^3=evalLayers φ x v b0-z^6) :
    evalTowers φ x w z v kq2=evalTowers φ x w z v k * evalTowers φ x w z v q02 := by
  have he := evalTowers_eq_zero_of_block_checks φ x w z v 3 3 kqError2
    kq_length2 kq_inner2 kq_blocks2
  rw [kqError2,eval_addTowers,eval_negTowers,
    eval_normalizeTower φ x w z v a0 a1 b0 hz hw,eval_mulTowers] at he
  exact (sub_eq_zero.mp (by simpa only [sub_eq_add_neg] using he)).symm

def cubicError2_0 : Towers := addTowers
  (normalizeTower a0 a1 b0 32 (mulTowers monomialCubic0 kq2)) (negTowers cubic2_0)
theorem cubic_check2_0 : checkTowers cubicError2_0=true := by decide +kernel

theorem eval_cubic2_0 {R : Type*} [CommRing R]
    (φ : GaussianInt →+* R) (x : Fin 5 → R) (w z v : R)
    (hz : z^3=evalLayers φ x v a0+evalLayers φ x v a1*z)
    (hw : w^3=evalLayers φ x v b0-z^6) :
    evalTowers φ x w z v cubic2_0=evalTowers φ x w z v monomialCubic0 *
      evalTowers φ x w z v k * evalTowers φ x w z v q02 := by
  rw [evaluation_of_normal_error_check φ x w z v a0 a1 b0 hz hw 32
    (mulTowers monomialCubic0 kq2) cubic2_0 cubic_check2_0,
    eval_mulTowers,eval_kq2 φ x w z v hz hw,mul_assoc]

def cubicError2_1 : Towers := addTowers
  (normalizeTower a0 a1 b0 32 (mulTowers monomialCubic1 kq2)) (negTowers cubic2_1)
theorem cubic_check2_1 : checkTowers cubicError2_1=true := by decide +kernel

theorem eval_cubic2_1 {R : Type*} [CommRing R]
    (φ : GaussianInt →+* R) (x : Fin 5 → R) (w z v : R)
    (hz : z^3=evalLayers φ x v a0+evalLayers φ x v a1*z)
    (hw : w^3=evalLayers φ x v b0-z^6) :
    evalTowers φ x w z v cubic2_1=evalTowers φ x w z v monomialCubic1 *
      evalTowers φ x w z v k * evalTowers φ x w z v q02 := by
  rw [evaluation_of_normal_error_check φ x w z v a0 a1 b0 hz hw 32
    (mulTowers monomialCubic1 kq2) cubic2_1 cubic_check2_1,
    eval_mulTowers,eval_kq2 φ x w z v hz hw,mul_assoc]

def cubicError2_2 : Towers := addTowers
  (normalizeTower a0 a1 b0 32 (mulTowers monomialCubic2 kq2)) (negTowers cubic2_2)
theorem cubic_check2_2 : checkTowers cubicError2_2=true := by decide +kernel

theorem eval_cubic2_2 {R : Type*} [CommRing R]
    (φ : GaussianInt →+* R) (x : Fin 5 → R) (w z v : R)
    (hz : z^3=evalLayers φ x v a0+evalLayers φ x v a1*z)
    (hw : w^3=evalLayers φ x v b0-z^6) :
    evalTowers φ x w z v cubic2_2=evalTowers φ x w z v monomialCubic2 *
      evalTowers φ x w z v k * evalTowers φ x w z v q02 := by
  rw [evaluation_of_normal_error_check φ x w z v a0 a1 b0 hz hw 32
    (mulTowers monomialCubic2 kq2) cubic2_2 cubic_check2_2,
    eval_mulTowers,eval_kq2 φ x w z v hz hw,mul_assoc]

def cubicError2_3 : Towers := addTowers
  (normalizeTower a0 a1 b0 32 (mulTowers monomialCubic3 kq2)) (negTowers cubic2_3)
theorem cubic_check2_3 : checkTowers cubicError2_3=true := by decide +kernel

theorem eval_cubic2_3 {R : Type*} [CommRing R]
    (φ : GaussianInt →+* R) (x : Fin 5 → R) (w z v : R)
    (hz : z^3=evalLayers φ x v a0+evalLayers φ x v a1*z)
    (hw : w^3=evalLayers φ x v b0-z^6) :
    evalTowers φ x w z v cubic2_3=evalTowers φ x w z v monomialCubic3 *
      evalTowers φ x w z v k * evalTowers φ x w z v q02 := by
  rw [evaluation_of_normal_error_check φ x w z v a0 a1 b0 hz hw 32
    (mulTowers monomialCubic3 kq2) cubic2_3 cubic_check2_3,
    eval_mulTowers,eval_kq2 φ x w z v hz hw,mul_assoc]

def cubicError2_4 : Towers := addTowers
  (normalizeTower a0 a1 b0 32 (mulTowers monomialCubic4 kq2)) (negTowers cubic2_4)
theorem cubic_check2_4 : checkTowers cubicError2_4=true := by decide +kernel

theorem eval_cubic2_4 {R : Type*} [CommRing R]
    (φ : GaussianInt →+* R) (x : Fin 5 → R) (w z v : R)
    (hz : z^3=evalLayers φ x v a0+evalLayers φ x v a1*z)
    (hw : w^3=evalLayers φ x v b0-z^6) :
    evalTowers φ x w z v cubic2_4=evalTowers φ x w z v monomialCubic4 *
      evalTowers φ x w z v k * evalTowers φ x w z v q02 := by
  rw [evaluation_of_normal_error_check φ x w z v a0 a1 b0 hz hw 32
    (mulTowers monomialCubic4 kq2) cubic2_4 cubic_check2_4,
    eval_mulTowers,eval_kq2 φ x w z v hz hw,mul_assoc]

def cubicError2_5 : Towers := addTowers
  (normalizeTower a0 a1 b0 32 (mulTowers monomialCubic5 kq2)) (negTowers cubic2_5)
theorem cubic_check2_5 : checkTowers cubicError2_5=true := by decide +kernel

theorem eval_cubic2_5 {R : Type*} [CommRing R]
    (φ : GaussianInt →+* R) (x : Fin 5 → R) (w z v : R)
    (hz : z^3=evalLayers φ x v a0+evalLayers φ x v a1*z)
    (hw : w^3=evalLayers φ x v b0-z^6) :
    evalTowers φ x w z v cubic2_5=evalTowers φ x w z v monomialCubic5 *
      evalTowers φ x w z v k * evalTowers φ x w z v q02 := by
  rw [evaluation_of_normal_error_check φ x w z v a0 a1 b0 hz hw 32
    (mulTowers monomialCubic5 kq2) cubic2_5 cubic_check2_5,
    eval_mulTowers,eval_kq2 φ x w z v hz hw,mul_assoc]

def cubicError2_6 : Towers := addTowers
  (normalizeTower a0 a1 b0 32 (mulTowers monomialCubic6 kq2)) (negTowers cubic2_6)
theorem cubic_check2_6 : checkTowers cubicError2_6=true := by decide +kernel

theorem eval_cubic2_6 {R : Type*} [CommRing R]
    (φ : GaussianInt →+* R) (x : Fin 5 → R) (w z v : R)
    (hz : z^3=evalLayers φ x v a0+evalLayers φ x v a1*z)
    (hw : w^3=evalLayers φ x v b0-z^6) :
    evalTowers φ x w z v cubic2_6=evalTowers φ x w z v monomialCubic6 *
      evalTowers φ x w z v k * evalTowers φ x w z v q02 := by
  rw [evaluation_of_normal_error_check φ x w z v a0 a1 b0 hz hw 32
    (mulTowers monomialCubic6 kq2) cubic2_6 cubic_check2_6,
    eval_mulTowers,eval_kq2 φ x w z v hz hw,mul_assoc]

def cubicError2_7 : Towers := addTowers
  (normalizeTower a0 a1 b0 32 (mulTowers monomialCubic7 kq2)) (negTowers cubic2_7)
theorem cubic_check2_7 : checkTowers cubicError2_7=true := by decide +kernel

theorem eval_cubic2_7 {R : Type*} [CommRing R]
    (φ : GaussianInt →+* R) (x : Fin 5 → R) (w z v : R)
    (hz : z^3=evalLayers φ x v a0+evalLayers φ x v a1*z)
    (hw : w^3=evalLayers φ x v b0-z^6) :
    evalTowers φ x w z v cubic2_7=evalTowers φ x w z v monomialCubic7 *
      evalTowers φ x w z v k * evalTowers φ x w z v q02 := by
  rw [evaluation_of_normal_error_check φ x w z v a0 a1 b0 hz hw 32
    (mulTowers monomialCubic7 kq2) cubic2_7 cubic_check2_7,
    eval_mulTowers,eval_kq2 φ x w z v hz hw,mul_assoc]

def cubicError2_8 : Towers := addTowers
  (normalizeTower a0 a1 b0 32 (mulTowers monomialCubic8 kq2)) (negTowers cubic2_8)
theorem cubic_check2_8 : checkTowers cubicError2_8=true := by decide +kernel

theorem eval_cubic2_8 {R : Type*} [CommRing R]
    (φ : GaussianInt →+* R) (x : Fin 5 → R) (w z v : R)
    (hz : z^3=evalLayers φ x v a0+evalLayers φ x v a1*z)
    (hw : w^3=evalLayers φ x v b0-z^6) :
    evalTowers φ x w z v cubic2_8=evalTowers φ x w z v monomialCubic8 *
      evalTowers φ x w z v k * evalTowers φ x w z v q02 := by
  rw [evaluation_of_normal_error_check φ x w z v a0 a1 b0 hz hw 32
    (mulTowers monomialCubic8 kq2) cubic2_8 cubic_check2_8,
    eval_mulTowers,eval_kq2 φ x w z v hz hw,mul_assoc]

end CycleQ2SegreModularCubicData
#print axioms CycleQ2SegreModularCubicData.eval_cubic2_8
end


/- Component: continuation_3/SegreModularCubicData.lean -/
section
namespace CycleQ2SegreModularCubicData
open CycleQ2SparseGaussianPolynomial

def kqTable : Fin 3 → Towers := ![kq0, kq1, kq2]

def cubicTable : Fin 3 → Fin 9 → Towers :=
  ![![cubic0_0, cubic0_1, cubic0_2, cubic0_3, cubic0_4, cubic0_5, cubic0_6, cubic0_7, cubic0_8], ![cubic1_0, cubic1_1, cubic1_2, cubic1_3, cubic1_4, cubic1_5, cubic1_6, cubic1_7, cubic1_8], ![cubic2_0, cubic2_1, cubic2_2, cubic2_3, cubic2_4, cubic2_5, cubic2_6, cubic2_7, cubic2_8]]
end CycleQ2SegreModularCubicData
end


/- Component: continuation_3/SegreModularCubicStandard0.lean -/
section
/-! Ordinary-kernel support and degree checks for one actual cubic-table row. -/

set_option maxHeartbeats 1000000000
set_option maxRecDepth 1000000
set_option Elab.async false

namespace CycleQ2SegreModularCubicStandard

open CycleQ2SparseGaussianPolynomial CycleQ2SegreModularCubicData

theorem good0_0 : goodTowers 28 cubic0_0=true := by decide +kernel

theorem good0_1 : goodTowers 28 cubic0_1=true := by decide +kernel

theorem good0_2 : goodTowers 28 cubic0_2=true := by decide +kernel

theorem good0_3 : goodTowers 28 cubic0_3=true := by decide +kernel

theorem good0_4 : goodTowers 28 cubic0_4=true := by decide +kernel

theorem good0_5 : goodTowers 28 cubic0_5=true := by decide +kernel

theorem good0_6 : goodTowers 28 cubic0_6=true := by decide +kernel

theorem good0_7 : goodTowers 28 cubic0_7=true := by decide +kernel

theorem good0_8 : goodTowers 28 cubic0_8=true := by decide +kernel

end CycleQ2SegreModularCubicStandard

#print axioms CycleQ2SegreModularCubicStandard.good0_8
end


/- Component: continuation_3/SegreModularCubicStandard1.lean -/
section
/-! Ordinary-kernel support and degree checks for one actual cubic-table row. -/

set_option maxHeartbeats 1000000000
set_option maxRecDepth 1000000
set_option Elab.async false

namespace CycleQ2SegreModularCubicStandard

open CycleQ2SparseGaussianPolynomial CycleQ2SegreModularCubicData

theorem good1_0 : goodTowers 28 cubic1_0=true := by decide +kernel

theorem good1_1 : goodTowers 28 cubic1_1=true := by decide +kernel

theorem good1_2 : goodTowers 28 cubic1_2=true := by decide +kernel

theorem good1_3 : goodTowers 28 cubic1_3=true := by decide +kernel

theorem good1_4 : goodTowers 28 cubic1_4=true := by decide +kernel

theorem good1_5 : goodTowers 28 cubic1_5=true := by decide +kernel

theorem good1_6 : goodTowers 28 cubic1_6=true := by decide +kernel

theorem good1_7 : goodTowers 28 cubic1_7=true := by decide +kernel

theorem good1_8 : goodTowers 28 cubic1_8=true := by decide +kernel

end CycleQ2SegreModularCubicStandard

#print axioms CycleQ2SegreModularCubicStandard.good1_8
end


/- Component: continuation_3/SegreModularCubicStandard2.lean -/
section
/-! Ordinary-kernel support and degree checks for one actual cubic-table row. -/

set_option maxHeartbeats 1000000000
set_option maxRecDepth 1000000
set_option Elab.async false

namespace CycleQ2SegreModularCubicStandard

open CycleQ2SparseGaussianPolynomial CycleQ2SegreModularCubicData

theorem good2_0 : goodTowers 28 cubic2_0=true := by decide +kernel

theorem good2_1 : goodTowers 28 cubic2_1=true := by decide +kernel

theorem good2_2 : goodTowers 28 cubic2_2=true := by decide +kernel

theorem good2_3 : goodTowers 28 cubic2_3=true := by decide +kernel

theorem good2_4 : goodTowers 28 cubic2_4=true := by decide +kernel

theorem good2_5 : goodTowers 28 cubic2_5=true := by decide +kernel

theorem good2_6 : goodTowers 28 cubic2_6=true := by decide +kernel

theorem good2_7 : goodTowers 28 cubic2_7=true := by decide +kernel

theorem good2_8 : goodTowers 28 cubic2_8=true := by decide +kernel

end CycleQ2SegreModularCubicStandard

#print axioms CycleQ2SegreModularCubicStandard.good2_8
end


/- Component: continuation_3/SegreModularFastActions10.lean -/
section
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
set_option Elab.async false
namespace CycleQ2SegreModularFastActions
open CycleQ2SparseModularFastDot CycleQ2SegreModularDetectorExpressions

def fast10_00 : List FastBlock := [
  (0,0,[(348,103),(261,57),(174,69),(291,49),(204,72),(117,0),(30,3),(321,97),(234,12),(147,39),(60,102),(264,49),(177,104),(90,51),(3,3),(294,101),(207,80),(120,13),(33,52),(237,25),(150,75),(63,33),(180,97),(93,99),(6,59),(210,26),(123,87),(36,100),(153,35),(66,19),(96,39),(9,59),(126,7),(39,50),(69,104),(12,4)]),
  (0,1,[(377,4),(290,63),(203,79),(116,50),(320,8),(233,55),(146,63),(59,22),(263,91),(176,94),(89,18),(293,63),(206,65),(119,12),(32,44),(236,14),(149,68),(62,43),(179,39),(92,102),(5,22),(209,93),(122,87),(35,54),(152,89),(65,84),(95,21),(8,58),(125,69),(38,63),(68,106),(11,89)]),
  (0,2,[(319,8),(232,50),(145,41),(262,8),(175,26),(88,24),(1,53),(292,8),(205,46),(118,8),(31,58),(235,52),(148,85),(61,104),(178,60),(91,6),(4,20),(208,40),(121,10),(34,81),(151,24),(64,105),(94,100),(7,73),(124,100),(37,80),(67,5),(10,105)]),
  (1,0,[(174,2),(87,90),(0,86),(291,57),(204,57),(117,57),(30,90),(234,5),(147,63),(60,90),(177,57),(90,86),(3,78),(207,49),(120,86),(33,23),(150,45),(63,38),(180,105),(93,34),(6,44),(123,90),(36,92),(66,42),(96,46),(9,54),(39,50),(12,4)]),
  (1,1,[(203,1),(116,81),(29,90),(233,5),(146,59),(59,4),(176,57),(89,84),(2,90),(206,5),(119,77),(32,90),(149,52),(62,83),(92,79),(5,6),(122,41),(35,5),(65,77),(95,103),(8,55),(38,63),(11,89)]),
  (1,2,[(232,108),(145,1),(58,2),(175,62),(118,53),(31,4),(148,5),(178,4),(91,31),(4,88),(121,61),(34,38),(64,105),(94,86),(7,26),(37,80),(10,105)]),
  (2,0,[(174,2),(87,90),(0,86),(204,108),(117,4),(30,90),(147,5),(60,90),(90,86),(3,78),(120,1),(33,86),(63,104),(6,107)]),
  (2,1,[(203,107),(116,68),(29,90),(146,107),(59,4),(89,4),(2,90),(119,66),(32,90),(92,57),(5,6),(35,57),(8,81)]),
  (2,2,[(232,108),(145,107),(58,2),(175,5),(88,2),(1,52),(118,107),(31,4),(4,2),(34,57),(7,57)])]
theorem fast10_00_eq : flattenGrouped fast10_00=encode flat10_00 := by rfl

def fast10_01 : List FastBlock := [
  (0,0,[(435,107),(348,9),(261,36),(174,45),(87,16),(0,8),(378,8),(291,58),(204,91),(117,38),(30,2),(408,107),(321,17),(234,25),(147,60),(60,104),(351,29),(264,70),(177,7),(90,16),(3,53),(294,70),(207,20),(120,99),(33,29),(324,23),(237,55),(150,59),(63,46),(267,19),(180,6),(93,101),(6,103),(210,24),(123,62),(36,47),(240,2),(153,11),(66,59),(183,52),(96,94),(9,103),(126,13),(39,82),(69,95),(99,50),(12,25),(42,35),(15,47)]),
  (0,1,[(377,1),(290,38),(203,3),(116,38),(29,108),(320,22),(233,23),(146,24),(59,80),(350,103),(263,60),(176,3),(89,102),(2,108),(293,79),(206,31),(119,29),(32,74),(323,106),(236,7),(149,36),(62,93),(266,96),(179,43),(92,83),(5,55),(209,23),(122,4),(35,0),(239,99),(152,60),(65,47),(182,53),(95,1),(8,67),(125,49),(38,76),(68,102),(98,72),(11,98),(41,63),(14,78)]),
  (0,2,[(406,2),(319,52),(232,79),(145,47),(58,29),(349,101),(262,52),(175,57),(88,29),(1,53),(292,105),(205,6),(118,93),(31,7),(322,43),(235,103),(148,61),(61,66),(265,43),(178,55),(91,47),(4,72),(208,49),(121,84),(34,68),(238,107),(151,4),(64,34),(94,35),(7,6),(124,35),(37,77),(67,17),(97,59),(10,93),(40,22),(13,10)]),
  (1,0,[(348,103),(261,57),(174,69),(291,49),(204,72),(117,0),(30,3),(321,97),(234,12),(147,39),(60,102),(264,49),(177,104),(90,51),(3,3),(294,101),(207,80),(120,13),(33,52),(237,25),(150,75),(63,33),(180,97),(93,99),(6,59),(210,26),(123,87),(36,100),(153,35),(66,19),(96,39),(9,59),(126,7),(39,50),(69,104),(12,4)]),
  (1,1,[(377,4),(290,63),(203,79),(116,50),(320,8),(233,55),(146,63),(59,22),(263,91),(176,94),(89,18),(293,63),(206,65),(119,12),(32,44),(236,14),(149,68),(62,43),(179,39),(92,102),(5,22),(209,93),(122,87),(35,54),(152,89),(65,84),(95,21),(8,58),(125,69),(38,63),(68,106),(11,89)]),
  (1,2,[(319,8),(232,50),(145,41),(262,8),(175,26),(88,24),(1,53),(292,8),(205,46),(118,8),(31,58),(235,52),(148,85),(61,104),(178,60),(91,6),(4,20),(208,40),(121,10),(34,81),(151,24),(64,105),(94,100),(7,73),(124,100),(37,80),(67,5),(10,105)]),
  (2,0,[(174,2),(87,90),(0,86),(291,57),(204,57),(117,57),(30,90),(234,5),(147,63),(60,90),(177,57),(90,86),(3,78),(207,49),(120,86),(33,23),(150,45),(63,38),(180,105),(93,34),(6,44),(123,90),(36,92),(66,42),(96,46),(9,54),(39,50),(12,4)]),
  (2,1,[(203,1),(116,81),(29,90),(233,5),(146,59),(59,4),(176,57),(89,84),(2,90),(206,5),(119,77),(32,90),(149,52),(62,83),(92,79),(5,6),(122,41),(35,5),(65,77),(95,103),(8,55),(38,63),(11,89)]),
  (2,2,[(232,108),(145,1),(58,2),(175,62),(118,53),(31,4),(148,5),(178,4),(91,31),(4,88),(121,61),(34,38),(64,105),(94,86),(7,26),(37,80),(10,105)])]
theorem fast10_01_eq : flattenGrouped fast10_01=encode flat10_01 := by rfl

def fast10_02 : List FastBlock := [
  (0,0,[(435,107),(348,18),(261,5),(174,105),(87,16),(0,8),(465,104),(378,62),(291,42),(204,14),(117,101),(30,108),(408,92),(321,23),(234,40),(147,95),(60,2),(351,96),(264,69),(177,61),(90,74),(3,50),(381,75),(294,86),(207,30),(120,4),(33,100),(324,57),(237,86),(150,48),(63,55),(354,16),(267,14),(180,74),(93,7),(6,58),(297,72),(210,11),(123,7),(36,95),(240,40),(153,21),(66,71),(270,51),(183,8),(96,102),(9,41),(213,14),(126,68),(39,71),(156,32),(69,67),(186,43),(99,106),(12,36),(129,25),(42,16),(72,101),(102,81),(15,87),(45,20),(18,18)]),
  (0,1,[(377,104),(290,107),(203,104),(116,24),(29,108),(407,94),(320,107),(233,5),(146,26),(59,58),(350,73),(263,0),(176,66),(89,103),(2,108),(380,94),(293,99),(206,34),(119,3),(32,30),(323,59),(236,45),(149,14),(62,81),(266,10),(179,25),(92,3),(5,33),(296,20),(209,74),(122,108),(35,8),(239,36),(152,71),(65,71),(269,32),(182,51),(95,47),(8,40),(212,104),(125,104),(38,28),(155,105),(68,17),(185,22),(98,90),(11,92),(128,77),(41,33),(71,62),(101,37),(14,13),(44,67),(17,75)]),
  (0,2,[(406,2),(319,40),(232,4),(145,96),(58,29),(349,29),(262,74),(175,71),(88,5),(292,73),(205,31),(118,59),(31,58),(322,8),(235,50),(148,26),(61,71),(352,101),(265,102),(178,93),(91,0),(4,37),(295,21),(208,11),(121,95),(34,76),(238,42),(151,10),(64,27),(268,92),(181,98),(94,85),(7,61),(211,47),(124,74),(37,13),(154,1),(67,86),(184,40),(97,99),(10,45),(127,100),(40,100),(70,15),(100,51),(13,106),(43,88),(16,85)]),
  (1,0,[(435,107),(348,9),(261,36),(174,45),(87,16),(0,8),(378,8),(291,58),(204,91),(117,38),(30,2),(408,107),(321,17),(234,25),(147,60),(60,104),(351,29),(264,70),(177,7),(90,16),(3,53),(294,70),(207,20),(120,99),(33,29),(324,23),(237,55),(150,59),(63,46),(267,19),(180,6),(93,101),(6,103),(210,24),(123,62),(36,47),(240,2),(153,11),(66,59),(183,52),(96,94),(9,103),(126,13),(39,82),(69,95),(99,50),(12,25),(42,35),(15,47)]),
  (1,1,[(377,1),(290,38),(203,3),(116,38),(29,108),(320,22),(233,23),(146,24),(59,80),(350,103),(263,60),(176,3),(89,102),(2,108),(293,79),(206,31),(119,29),(32,74),(323,106),(236,7),(149,36),(62,93),(266,96),(179,43),(92,83),(5,55),(209,23),(122,4),(35,0),(239,99),(152,60),(65,47),(182,53),(95,1),(8,67),(125,49),(38,76),(68,102),(98,72),(11,98),(41,63),(14,78)]),
  (1,2,[(406,2),(319,52),(232,79),(145,47),(58,29),(349,101),(262,52),(175,57),(88,29),(1,53),(292,105),(205,6),(118,93),(31,7),(322,43),(235,103),(148,61),(61,66),(265,43),(178,55),(91,47),(4,72),(208,49),(121,84),(34,68),(238,107),(151,4),(64,34),(94,35),(7,6),(124,35),(37,77),(67,17),(97,59),(10,93),(40,22),(13,10)]),
  (2,0,[(348,103),(261,57),(174,69),(291,49),(204,72),(117,0),(30,3),(321,97),(234,12),(147,39),(60,102),(264,49),(177,104),(90,51),(3,3),(294,101),(207,80),(120,13),(33,52),(237,25),(150,75),(63,33),(180,97),(93,99),(6,59),(210,26),(123,87),(36,100),(153,35),(66,19),(96,39),(9,59),(126,7),(39,50),(69,104),(12,4)]),
  (2,1,[(377,4),(290,63),(203,79),(116,50),(320,8),(233,55),(146,63),(59,22),(263,91),(176,94),(89,18),(293,63),(206,65),(119,12),(32,44),(236,14),(149,68),(62,43),(179,39),(92,102),(5,22),(209,93),(122,87),(35,54),(152,89),(65,84),(95,21),(8,58),(125,69),(38,63),(68,106),(11,89)]),
  (2,2,[(319,8),(232,50),(145,41),(262,8),(175,26),(88,24),(1,53),(292,8),(205,46),(118,8),(31,58),(235,52),(148,85),(61,104),(178,60),(91,6),(4,20),(208,40),(121,10),(34,81),(151,24),(64,105),(94,100),(7,73),(124,100),(37,80),(67,5),(10,105)])]
theorem fast10_02_eq : flattenGrouped fast10_02=encode flat10_02 := by rfl

def fast10_10 : List FastBlock := [
  (0,0,[(406,101),(319,97),(232,33),(145,4),(349,93),(262,71),(175,4),(88,61),(1,61),(379,101),(292,93),(205,21),(118,65),(31,59),(322,95),(235,22),(148,37),(265,43),(178,71),(91,97),(4,100),(295,6),(208,3),(121,61),(34,17),(238,17),(151,79),(64,62),(181,3),(94,59),(7,53),(211,21),(124,80),(37,37),(154,33),(67,57),(97,29),(10,101),(127,30),(40,28),(70,56),(13,86)]),
  (0,1,[(348,95),(261,7),(174,28),(291,41),(204,46),(117,85),(30,59),(321,81),(234,25),(147,99),(60,44),(264,98),(177,102),(90,32),(3,59),(294,93),(207,83),(120,108),(33,83),(237,42),(150,89),(63,66),(180,13),(93,97),(6,39),(210,95),(123,86),(36,55),(153,20),(66,52),(96,43),(9,95),(126,16),(39,83),(69,99),(12,8)]),
  (0,2,[(377,4),(290,63),(203,79),(116,50),(320,8),(233,55),(146,63),(59,22),(263,91),(176,94),(89,18),(293,63),(206,65),(119,12),(32,44),(236,14),(149,68),(62,43),(179,39),(92,102),(5,22),(209,93),(122,87),(35,54),(152,89),(65,84),(95,21),(8,58),(125,69),(38,63),(68,106),(11,89)]),
  (1,0,[(319,1),(232,76),(145,30),(58,64),(262,48),(175,21),(88,107),(205,103),(118,57),(31,19),(235,71),(148,31),(61,62),(265,105),(178,67),(91,32),(4,91),(208,44),(121,35),(34,61),(151,108),(64,52),(181,46),(94,47),(7,30),(124,103),(37,82),(67,6),(97,8),(10,76),(40,28),(13,86)]),
  (1,1,[(261,1),(174,1),(87,88),(0,86),(291,57),(204,104),(117,57),(30,90),(234,6),(147,9),(60,84),(177,99),(90,86),(3,78),(207,45),(120,2),(33,40),(150,88),(63,0),(180,101),(93,7),(6,65),(123,52),(36,28),(66,75),(96,69),(9,28),(39,83),(12,8)]),
  (1,2,[(203,1),(116,81),(29,90),(233,5),(146,59),(59,4),(176,57),(89,84),(2,90),(206,5),(119,77),(32,90),(149,52),(62,83),(92,79),(5,6),(122,41),(35,5),(65,77),(95,103),(8,55),(38,63),(11,89)]),
  (2,0,[(319,1),(232,79),(145,43),(58,64),(262,105),(175,51),(88,10),(1,29),(205,106),(118,39),(31,76),(235,76),(148,45),(61,62),(178,56),(91,64),(4,36),(121,95),(34,101),(64,52),(94,52),(7,37),(37,80),(10,28)]),
  (2,1,[(261,1),(174,4),(87,88),(0,86),(204,103),(117,2),(30,38),(234,1),(147,9),(60,84),(177,104),(90,84),(3,26),(120,3),(33,80),(63,47),(6,105),(36,104),(9,52)]),
  (2,2,[(203,107),(116,68),(29,90),(146,107),(59,4),(89,4),(2,90),(119,66),(32,90),(92,57),(5,6),(35,57),(8,81)])]
theorem fast10_10_eq : flattenGrouped fast10_10=encode flat10_10 := by rfl

def fast10_11 : List FastBlock := [
  (0,0,[(493,107),(406,12),(319,59),(232,83),(145,58),(58,56),(436,6),(349,76),(262,2),(175,4),(88,83),(1,61),(379,12),(292,32),(205,42),(118,106),(31,62),(409,23),(322,50),(235,59),(148,74),(61,10),(352,86),(265,100),(178,45),(91,34),(4,20),(295,103),(208,101),(121,83),(34,46),(325,4),(238,12),(151,61),(64,37),(268,4),(181,32),(94,15),(7,61),(211,56),(124,74),(37,15),(241,43),(154,80),(67,63),(184,50),(97,99),(10,13),(127,93),(40,100),(70,103),(100,84),(13,10),(43,62),(16,3)]),
  (0,1,[(435,105),(348,66),(261,66),(174,107),(87,96),(0,8),(378,16),(291,6),(204,34),(117,9),(30,58),(408,105),(321,78),(234,49),(147,29),(60,68),(351,103),(264,24),(177,107),(90,30),(3,0),(294,31),(207,68),(120,68),(33,59),(324,89),(237,12),(150,23),(63,21),(267,87),(180,56),(93,20),(6,31),(210,84),(123,52),(36,82),(240,4),(153,81),(66,57),(183,52),(96,42),(9,97),(126,28),(39,21),(69,56),(99,100),(12,41),(42,3),(15,37)]),
  (0,2,[(377,1),(290,38),(203,3),(116,38),(29,108),(320,22),(233,23),(146,24),(59,80),(350,103),(263,60),(176,3),(89,102),(2,108),(293,79),(206,31),(119,29),(32,74),(323,106),(236,7),(149,36),(62,93),(266,96),(179,43),(92,83),(5,55),(209,23),(122,4),(35,0),(239,99),(152,60),(65,47),(182,53),(95,1),(8,67),(125,49),(38,76),(68,102),(98,72),(11,98),(41,63),(14,78)]),
  (1,0,[(406,101),(319,97),(232,33),(145,4),(349,93),(262,71),(175,4),(88,61),(1,61),(379,101),(292,93),(205,21),(118,65),(31,59),(322,95),(235,22),(148,37),(265,43),(178,71),(91,97),(4,100),(295,6),(208,3),(121,61),(34,17),(238,17),(151,79),(64,62),(181,3),(94,59),(7,53),(211,21),(124,80),(37,37),(154,33),(67,57),(97,29),(10,101),(127,30),(40,28),(70,56),(13,86)]),
  (1,1,[(348,95),(261,7),(174,28),(291,41),(204,46),(117,85),(30,59),(321,81),(234,25),(147,99),(60,44),(264,98),(177,102),(90,32),(3,59),(294,93),(207,83),(120,108),(33,83),(237,42),(150,89),(63,66),(180,13),(93,97),(6,39),(210,95),(123,86),(36,55),(153,20),(66,52),(96,43),(9,95),(126,16),(39,83),(69,99),(12,8)]),
  (1,2,[(377,4),(290,63),(203,79),(116,50),(320,8),(233,55),(146,63),(59,22),(263,91),(176,94),(89,18),(293,63),(206,65),(119,12),(32,44),(236,14),(149,68),(62,43),(179,39),(92,102),(5,22),(209,93),(122,87),(35,54),(152,89),(65,84),(95,21),(8,58),(125,69),(38,63),(68,106),(11,89)]),
  (2,0,[(319,1),(232,76),(145,30),(58,64),(262,48),(175,21),(88,107),(205,103),(118,57),(31,19),(235,71),(148,31),(61,62),(265,105),(178,67),(91,32),(4,91),(208,44),(121,35),(34,61),(151,108),(64,52),(181,46),(94,47),(7,30),(124,103),(37,82),(67,6),(97,8),(10,76),(40,28),(13,86)]),
  (2,1,[(261,1),(174,1),(87,88),(0,86),(291,57),(204,104),(117,57),(30,90),(234,6),(147,9),(60,84),(177,99),(90,86),(3,78),(207,45),(120,2),(33,40),(150,88),(63,0),(180,101),(93,7),(6,65),(123,52),(36,28),(66,75),(96,69),(9,28),(39,83),(12,8)]),
  (2,2,[(203,1),(116,81),(29,90),(233,5),(146,59),(59,4),(176,57),(89,84),(2,90),(206,5),(119,77),(32,90),(149,52),(62,83),(92,79),(5,6),(122,41),(35,5),(65,77),(95,103),(8,55),(38,63),(11,89)])]
theorem fast10_11_eq : flattenGrouped fast10_11=encode flat10_11 := by rfl

def fast10_12 : List FastBlock := [
  (0,0,[(493,107),(406,24),(319,77),(232,32),(145,100),(58,56),(436,78),(349,51),(262,4),(175,100),(88,22),(379,7),(292,51),(205,99),(118,81),(31,3),(409,58),(322,36),(235,40),(148,55),(61,10),(439,8),(352,46),(265,4),(178,61),(91,57),(4,94),(382,96),(295,25),(208,97),(121,6),(34,58),(325,92),(238,30),(151,75),(64,79),(355,80),(268,66),(181,6),(94,16),(7,12),(298,9),(211,60),(124,64),(37,29),(241,30),(154,93),(67,33),(271,53),(184,54),(97,65),(10,74),(214,103),(127,102),(40,96),(157,27),(70,57),(187,70),(100,91),(13,81),(130,0),(43,15),(73,80),(103,72),(16,5),(46,94),(19,80)]),
  (0,1,[(435,105),(348,87),(261,1),(174,9),(87,96),(0,8),(465,104),(378,33),(291,77),(204,52),(117,96),(30,108),(408,90),(321,19),(234,5),(147,49),(60,24),(351,59),(264,54),(177,73),(90,107),(3,50),(381,83),(294,20),(207,15),(120,54),(33,5),(324,28),(237,25),(150,36),(63,17),(354,24),(267,88),(180,80),(93,89),(6,21),(297,68),(210,11),(123,45),(36,67),(240,60),(153,46),(66,31),(270,68),(183,18),(96,40),(9,89),(213,36),(126,4),(39,13),(156,40),(69,99),(186,3),(99,101),(12,100),(129,92),(42,28),(72,107),(102,30),(15,90),(45,65),(18,42)]),
  (0,2,[(377,104),(290,107),(203,104),(116,24),(29,108),(407,94),(320,107),(233,5),(146,26),(59,58),(350,73),(263,0),(176,66),(89,103),(2,108),(380,94),(293,99),(206,34),(119,3),(32,30),(323,59),(236,45),(149,14),(62,81),(266,10),(179,25),(92,3),(5,33),(296,20),(209,74),(122,108),(35,8),(239,36),(152,71),(65,71),(269,32),(182,51),(95,47),(8,40),(212,104),(125,104),(38,28),(155,105),(68,17),(185,22),(98,90),(11,92),(128,77),(41,33),(71,62),(101,37),(14,13),(44,67),(17,75)]),
  (1,0,[(493,107),(406,12),(319,59),(232,83),(145,58),(58,56),(436,6),(349,76),(262,2),(175,4),(88,83),(1,61),(379,12),(292,32),(205,42),(118,106),(31,62),(409,23),(322,50),(235,59),(148,74),(61,10),(352,86),(265,100),(178,45),(91,34),(4,20),(295,103),(208,101),(121,83),(34,46),(325,4),(238,12),(151,61),(64,37),(268,4),(181,32),(94,15),(7,61),(211,56),(124,74),(37,15),(241,43),(154,80),(67,63),(184,50),(97,99),(10,13),(127,93),(40,100),(70,103),(100,84),(13,10),(43,62),(16,3)]),
  (1,1,[(435,105),(348,66),(261,66),(174,107),(87,96),(0,8),(378,16),(291,6),(204,34),(117,9),(30,58),(408,105),(321,78),(234,49),(147,29),(60,68),(351,103),(264,24),(177,107),(90,30),(3,0),(294,31),(207,68),(120,68),(33,59),(324,89),(237,12),(150,23),(63,21),(267,87),(180,56),(93,20),(6,31),(210,84),(123,52),(36,82),(240,4),(153,81),(66,57),(183,52),(96,42),(9,97),(126,28),(39,21),(69,56),(99,100),(12,41),(42,3),(15,37)]),
  (1,2,[(377,1),(290,38),(203,3),(116,38),(29,108),(320,22),(233,23),(146,24),(59,80),(350,103),(263,60),(176,3),(89,102),(2,108),(293,79),(206,31),(119,29),(32,74),(323,106),(236,7),(149,36),(62,93),(266,96),(179,43),(92,83),(5,55),(209,23),(122,4),(35,0),(239,99),(152,60),(65,47),(182,53),(95,1),(8,67),(125,49),(38,76),(68,102),(98,72),(11,98),(41,63),(14,78)]),
  (2,0,[(406,101),(319,97),(232,33),(145,4),(349,93),(262,71),(175,4),(88,61),(1,61),(379,101),(292,93),(205,21),(118,65),(31,59),(322,95),(235,22),(148,37),(265,43),(178,71),(91,97),(4,100),(295,6),(208,3),(121,61),(34,17),(238,17),(151,79),(64,62),(181,3),(94,59),(7,53),(211,21),(124,80),(37,37),(154,33),(67,57),(97,29),(10,101),(127,30),(40,28),(70,56),(13,86)]),
  (2,1,[(348,95),(261,7),(174,28),(291,41),(204,46),(117,85),(30,59),(321,81),(234,25),(147,99),(60,44),(264,98),(177,102),(90,32),(3,59),(294,93),(207,83),(120,108),(33,83),(237,42),(150,89),(63,66),(180,13),(93,97),(6,39),(210,95),(123,86),(36,55),(153,20),(66,52),(96,43),(9,95),(126,16),(39,83),(69,99),(12,8)]),
  (2,2,[(377,4),(290,63),(203,79),(116,50),(320,8),(233,55),(146,63),(59,22),(263,91),(176,94),(89,18),(293,63),(206,65),(119,12),(32,44),(236,14),(149,68),(62,43),(179,39),(92,102),(5,22),(209,93),(122,87),(35,54),(152,89),(65,84),(95,21),(8,58),(125,69),(38,63),(68,106),(11,89)])]
theorem fast10_12_eq : flattenGrouped fast10_12=encode flat10_12 := by rfl

def fast10_20 : List FastBlock := [
  (0,0,[(464,105),(377,65),(290,84),(203,80),(116,74),(407,97),(320,29),(233,92),(146,91),(59,50),(350,10),(263,38),(176,93),(89,9),(380,69),(293,15),(206,3),(119,10),(32,100),(323,78),(236,59),(149,58),(62,96),(266,7),(179,38),(92,87),(5,50),(296,24),(209,90),(122,81),(35,106),(239,62),(152,16),(65,20),(182,87),(95,81),(8,75),(212,57),(125,90),(38,34),(155,37),(68,106),(98,62),(11,75),(128,97),(41,28),(71,10),(14,103)]),
  (0,1,[(406,97),(319,34),(232,63),(145,63),(349,85),(262,16),(175,50),(88,39),(1,61),(379,97),(292,48),(205,66),(118,106),(31,59),(322,24),(235,11),(148,71),(61,43),(265,47),(178,18),(91,36),(4,100),(295,52),(208,8),(121,56),(34,60),(238,19),(151,33),(64,74),(181,93),(94,91),(7,31),(211,37),(124,81),(37,34),(154,93),(67,19),(97,11),(10,43),(127,70),(40,94),(70,59),(13,106)]),
  (0,2,[(348,95),(261,7),(174,28),(291,41),(204,46),(117,85),(30,59),(321,81),(234,25),(147,99),(60,44),(264,98),(177,102),(90,32),(3,59),(294,93),(207,83),(120,108),(33,83),(237,42),(150,89),(63,66),(180,13),(93,97),(6,39),(210,95),(123,86),(36,55),(153,20),(66,52),(96,43),(9,95),(126,16),(39,83),(69,99),(12,8)]),
  (1,0,[(290,108),(203,60),(116,104),(29,46),(320,104),(233,100),(146,59),(59,38),(263,47),(176,46),(89,87),(2,46),(293,104),(206,59),(119,58),(32,92),(236,108),(149,72),(62,82),(179,6),(92,88),(5,1),(209,15),(122,63),(35,72),(152,72),(65,75),(182,6),(95,103),(8,105),(125,97),(38,55),(68,80),(98,40),(11,85),(41,28),(14,103)]),
  (1,1,[(319,1),(232,75),(145,58),(58,83),(262,43),(175,71),(88,103),(205,45),(118,1),(31,57),(235,61),(148,4),(61,77),(265,105),(178,67),(91,83),(4,1),(208,39),(121,97),(34,74),(151,15),(64,73),(181,46),(94,0),(7,24),(124,68),(37,22),(67,84),(97,14),(10,21),(40,94),(13,106)]),
  (1,2,[(261,1),(174,1),(87,88),(0,86),(291,57),(204,104),(117,57),(30,90),(234,6),(147,9),(60,84),(177,99),(90,86),(3,78),(207,45),(120,2),(33,40),(150,88),(63,0),(180,101),(93,7),(6,65),(123,52),(36,28),(66,75),(96,69),(9,28),(39,83),(12,8)]),
  (2,0,[(290,2),(203,86),(116,15),(29,46),(233,4),(146,82),(59,38),(176,107),(89,34),(2,46),(206,86),(119,11),(32,92),(149,86),(62,42),(179,52),(92,97),(5,1),(122,102),(35,101),(65,52),(95,56),(8,65),(38,56),(11,57)]),
  (2,1,[(319,1),(232,81),(145,84),(58,83),(262,105),(175,53),(88,6),(1,29),(205,108),(118,76),(31,5),(235,76),(148,90),(61,77),(178,56),(91,60),(4,55),(121,81),(34,5),(64,104),(94,104),(7,31),(37,51),(10,56)]),
  (2,2,[(261,1),(174,4),(87,88),(0,86),(204,103),(117,2),(30,38),(234,1),(147,9),(60,84),(177,104),(90,84),(3,26),(120,3),(33,80),(63,47),(6,105),(36,104),(9,52)])]
theorem fast10_20_eq : flattenGrouped fast10_20=encode flat10_20 := by rfl

def fast10_21 : List FastBlock := [
  (0,0,[(464,108),(377,103),(290,14),(203,58),(116,18),(29,77),(407,86),(320,98),(233,55),(146,105),(59,54),(437,6),(350,53),(263,41),(176,79),(89,24),(2,77),(380,69),(293,94),(206,78),(119,44),(32,47),(410,3),(323,108),(236,44),(149,78),(62,92),(353,36),(266,97),(179,48),(92,97),(5,92),(296,90),(209,77),(122,21),(35,98),(326,20),(239,46),(152,5),(65,104),(269,73),(182,2),(95,41),(8,35),(212,3),(125,97),(38,76),(242,106),(155,85),(68,52),(185,42),(98,66),(11,6),(128,65),(41,66),(71,33),(101,9),(14,62),(44,39),(17,67)]),
  (0,1,[(493,107),(406,11),(319,21),(232,80),(145,20),(58,57),(436,6),(349,54),(262,88),(175,89),(88,3),(1,61),(379,17),(292,43),(205,36),(118,75),(31,64),(409,23),(322,58),(235,5),(148,21),(61,74),(352,95),(265,33),(178,6),(91,57),(4,21),(295,37),(208,27),(121,80),(34,26),(325,7),(238,91),(151,21),(64,53),(268,27),(181,38),(94,103),(7,6),(211,89),(124,69),(37,57),(241,53),(154,80),(67,49),(184,106),(97,105),(10,55),(127,81),(40,35),(70,47),(100,12),(13,21),(43,30),(16,34)]),
  (0,2,[(435,105),(348,66),(261,66),(174,107),(87,96),(0,8),(378,16),(291,6),(204,34),(117,9),(30,58),(408,105),(321,78),(234,49),(147,29),(60,68),(351,103),(264,24),(177,107),(90,30),(3,0),(294,31),(207,68),(120,68),(33,59),(324,89),(237,12),(150,23),(63,21),(267,87),(180,56),(93,20),(6,31),(210,84),(123,52),(36,82),(240,4),(153,81),(66,57),(183,52),(96,42),(9,97),(126,28),(39,21),(69,56),(99,100),(12,41),(42,3),(15,37)]),
  (1,0,[(464,105),(377,65),(290,84),(203,80),(116,74),(407,97),(320,29),(233,92),(146,91),(59,50),(350,10),(263,38),(176,93),(89,9),(380,69),(293,15),(206,3),(119,10),(32,100),(323,78),(236,59),(149,58),(62,96),(266,7),(179,38),(92,87),(5,50),(296,24),(209,90),(122,81),(35,106),(239,62),(152,16),(65,20),(182,87),(95,81),(8,75),(212,57),(125,90),(38,34),(155,37),(68,106),(98,62),(11,75),(128,97),(41,28),(71,10),(14,103)]),
  (1,1,[(406,97),(319,34),(232,63),(145,63),(349,85),(262,16),(175,50),(88,39),(1,61),(379,97),(292,48),(205,66),(118,106),(31,59),(322,24),(235,11),(148,71),(61,43),(265,47),(178,18),(91,36),(4,100),(295,52),(208,8),(121,56),(34,60),(238,19),(151,33),(64,74),(181,93),(94,91),(7,31),(211,37),(124,81),(37,34),(154,93),(67,19),(97,11),(10,43),(127,70),(40,94),(70,59),(13,106)]),
  (1,2,[(348,95),(261,7),(174,28),(291,41),(204,46),(117,85),(30,59),(321,81),(234,25),(147,99),(60,44),(264,98),(177,102),(90,32),(3,59),(294,93),(207,83),(120,108),(33,83),(237,42),(150,89),(63,66),(180,13),(93,97),(6,39),(210,95),(123,86),(36,55),(153,20),(66,52),(96,43),(9,95),(126,16),(39,83),(69,99),(12,8)]),
  (2,0,[(290,108),(203,60),(116,104),(29,46),(320,104),(233,100),(146,59),(59,38),(263,47),(176,46),(89,87),(2,46),(293,104),(206,59),(119,58),(32,92),(236,108),(149,72),(62,82),(179,6),(92,88),(5,1),(209,15),(122,63),(35,72),(152,72),(65,75),(182,6),(95,103),(8,105),(125,97),(38,55),(68,80),(98,40),(11,85),(41,28),(14,103)]),
  (2,1,[(319,1),(232,75),(145,58),(58,83),(262,43),(175,71),(88,103),(205,45),(118,1),(31,57),(235,61),(148,4),(61,77),(265,105),(178,67),(91,83),(4,1),(208,39),(121,97),(34,74),(151,15),(64,73),(181,46),(94,0),(7,24),(124,68),(37,22),(67,84),(97,14),(10,21),(40,94),(13,106)]),
  (2,2,[(261,1),(174,1),(87,88),(0,86),(291,57),(204,104),(117,57),(30,90),(234,6),(147,9),(60,84),(177,99),(90,86),(3,78),(207,45),(120,2),(33,40),(150,88),(63,0),(180,101),(93,7),(6,65),(123,52),(36,28),(66,75),(96,69),(9,28),(39,83),(12,8)])]
theorem fast10_21_eq : flattenGrouped fast10_21=encode flat10_21 := by rfl

def fast10_22 : List FastBlock := [
  (0,0,[(464,5),(377,60),(290,50),(203,34),(116,6),(29,77),(494,15),(407,72),(320,42),(233,30),(146,96),(59,4),(437,51),(350,49),(263,38),(176,21),(89,78),(2,77),(467,15),(380,55),(293,16),(206,91),(119,101),(32,56),(410,6),(323,43),(236,31),(149,23),(62,7),(353,51),(266,32),(179,18),(92,2),(5,42),(383,30),(296,8),(209,87),(122,56),(35,14),(326,38),(239,94),(152,48),(65,32),(356,77),(269,68),(182,50),(95,75),(8,80),(299,88),(212,56),(125,59),(38,30),(242,107),(155,23),(68,25),(272,53),(185,12),(98,71),(11,13),(215,63),(128,105),(41,35),(158,56),(71,5),(188,35),(101,46),(14,73),(131,39),(44,59),(74,17),(104,56),(17,104),(47,65),(20,77)]),
  (0,1,[(493,107),(406,29),(319,79),(232,37),(145,76),(58,57),(436,93),(349,53),(262,108),(175,74),(88,73),(379,48),(292,53),(205,38),(118,63),(31,5),(409,88),(322,48),(235,1),(148,26),(61,31),(439,8),(352,23),(265,68),(178,90),(91,91),(4,95),(382,2),(295,25),(208,38),(121,0),(34,104),(325,13),(238,20),(151,62),(64,99),(355,80),(268,20),(181,19),(94,51),(7,88),(298,66),(211,44),(124,18),(37,90),(241,108),(154,27),(67,43),(271,21),(184,7),(97,1),(10,34),(214,86),(127,17),(40,85),(157,63),(70,7),(187,48),(100,48),(13,98),(130,104),(43,78),(73,60),(103,35),(16,101),(46,61),(19,5)]),
  (0,2,[(435,105),(348,87),(261,1),(174,9),(87,96),(0,8),(465,104),(378,33),(291,77),(204,52),(117,96),(30,108),(408,90),(321,19),(234,5),(147,49),(60,24),(351,59),(264,54),(177,73),(90,107),(3,50),(381,83),(294,20),(207,15),(120,54),(33,5),(324,28),(237,25),(150,36),(63,17),(354,24),(267,88),(180,80),(93,89),(6,21),(297,68),(210,11),(123,45),(36,67),(240,60),(153,46),(66,31),(270,68),(183,18),(96,40),(9,89),(213,36),(126,4),(39,13),(156,40),(69,99),(186,3),(99,101),(12,100),(129,92),(42,28),(72,107),(102,30),(15,90),(45,65),(18,42)]),
  (1,0,[(464,108),(377,103),(290,14),(203,58),(116,18),(29,77),(407,86),(320,98),(233,55),(146,105),(59,54),(437,6),(350,53),(263,41),(176,79),(89,24),(2,77),(380,69),(293,94),(206,78),(119,44),(32,47),(410,3),(323,108),(236,44),(149,78),(62,92),(353,36),(266,97),(179,48),(92,97),(5,92),(296,90),(209,77),(122,21),(35,98),(326,20),(239,46),(152,5),(65,104),(269,73),(182,2),(95,41),(8,35),(212,3),(125,97),(38,76),(242,106),(155,85),(68,52),(185,42),(98,66),(11,6),(128,65),(41,66),(71,33),(101,9),(14,62),(44,39),(17,67)]),
  (1,1,[(493,107),(406,11),(319,21),(232,80),(145,20),(58,57),(436,6),(349,54),(262,88),(175,89),(88,3),(1,61),(379,17),(292,43),(205,36),(118,75),(31,64),(409,23),(322,58),(235,5),(148,21),(61,74),(352,95),(265,33),(178,6),(91,57),(4,21),(295,37),(208,27),(121,80),(34,26),(325,7),(238,91),(151,21),(64,53),(268,27),(181,38),(94,103),(7,6),(211,89),(124,69),(37,57),(241,53),(154,80),(67,49),(184,106),(97,105),(10,55),(127,81),(40,35),(70,47),(100,12),(13,21),(43,30),(16,34)]),
  (1,2,[(435,105),(348,66),(261,66),(174,107),(87,96),(0,8),(378,16),(291,6),(204,34),(117,9),(30,58),(408,105),(321,78),(234,49),(147,29),(60,68),(351,103),(264,24),(177,107),(90,30),(3,0),(294,31),(207,68),(120,68),(33,59),(324,89),(237,12),(150,23),(63,21),(267,87),(180,56),(93,20),(6,31),(210,84),(123,52),(36,82),(240,4),(153,81),(66,57),(183,52),(96,42),(9,97),(126,28),(39,21),(69,56),(99,100),(12,41),(42,3),(15,37)]),
  (2,0,[(464,105),(377,65),(290,84),(203,80),(116,74),(407,97),(320,29),(233,92),(146,91),(59,50),(350,10),(263,38),(176,93),(89,9),(380,69),(293,15),(206,3),(119,10),(32,100),(323,78),(236,59),(149,58),(62,96),(266,7),(179,38),(92,87),(5,50),(296,24),(209,90),(122,81),(35,106),(239,62),(152,16),(65,20),(182,87),(95,81),(8,75),(212,57),(125,90),(38,34),(155,37),(68,106),(98,62),(11,75),(128,97),(41,28),(71,10),(14,103)]),
  (2,1,[(406,97),(319,34),(232,63),(145,63),(349,85),(262,16),(175,50),(88,39),(1,61),(379,97),(292,48),(205,66),(118,106),(31,59),(322,24),(235,11),(148,71),(61,43),(265,47),(178,18),(91,36),(4,100),(295,52),(208,8),(121,56),(34,60),(238,19),(151,33),(64,74),(181,93),(94,91),(7,31),(211,37),(124,81),(37,34),(154,93),(67,19),(97,11),(10,43),(127,70),(40,94),(70,59),(13,106)]),
  (2,2,[(348,95),(261,7),(174,28),(291,41),(204,46),(117,85),(30,59),(321,81),(234,25),(147,99),(60,44),(264,98),(177,102),(90,32),(3,59),(294,93),(207,83),(120,108),(33,83),(237,42),(150,89),(63,66),(180,13),(93,97),(6,39),(210,95),(123,86),(36,55),(153,20),(66,52),(96,43),(9,95),(126,16),(39,83),(69,99),(12,8)])]
theorem fast10_22_eq : flattenGrouped fast10_22=encode flat10_22 := by rfl

def fast10 : Fin 3 → Fin 3 → List FastBlock :=
  ![![fast10_00, fast10_01, fast10_02], ![fast10_10, fast10_11, fast10_12], ![fast10_20, fast10_21, fast10_22]]
end CycleQ2SegreModularFastActions
#print axioms CycleQ2SegreModularFastActions.fast10_22_eq
end


/- Component: continuation_3/SegreModularFastActions11.lean -/
section
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
set_option Elab.async false
namespace CycleQ2SegreModularFastActions
open CycleQ2SparseModularFastDot CycleQ2SegreModularDetectorExpressions

def fast11_00 : List FastBlock := [
  (0,0,[(261,107),(174,19),(87,23),(204,48),(117,41),(30,3),(234,86),(147,82),(60,16),(177,14),(90,16),(3,3),(294,105),(207,62),(120,71),(33,74),(237,103),(150,79),(63,5),(180,106),(93,53),(6,13),(210,89),(123,97),(36,59),(153,48),(66,35),(96,68),(9,5),(126,5),(39,24),(69,47),(42,43)]),
  (0,1,[(203,106),(116,96),(320,52),(233,80),(146,101),(59,22),(263,52),(176,82),(89,21),(119,47),(32,44),(236,24),(149,38),(62,79),(179,103),(92,64),(5,22),(209,103),(122,16),(35,86),(152,81),(65,100),(95,23),(8,84),(125,46),(38,97),(68,94),(41,4)]),
  (0,2,[(232,1),(145,44),(58,43),(262,52),(175,7),(88,46),(1,53),(205,78),(118,94),(31,58),(235,52),(148,64),(61,34),(178,107),(91,16),(4,43),(121,69),(34,100),(151,103),(64,17),(94,29),(7,104),(124,105),(37,96),(67,20),(40,99)]),
  (1,0,[(348,1),(261,45),(174,43),(291,2),(204,74),(117,53),(234,58),(147,57),(60,32),(264,43),(177,98),(90,108),(207,15),(120,47),(33,32),(150,53),(63,32),(180,108),(93,88),(6,18),(123,52),(36,12),(9,39)]),
  (1,1,[(290,2),(203,47),(116,13),(29,43),(233,58),(146,93),(59,45),(263,2),(176,49),(89,80),(206,102),(119,11),(32,39),(149,91),(62,41),(179,43),(92,28),(122,53),(35,86),(8,88)]),
  (1,2,[(232,1),(145,2),(58,77),(175,56),(88,1),(205,2),(118,55),(31,45),(148,4),(61,78),(178,1),(91,52),(34,43)]),
  (2,0,[(204,107),(117,32),(234,1),(147,76),(60,88),(177,1),(120,33),(150,76)]),
  (2,1,[(176,1),(2,21),(119,108),(149,2),(62,77),(92,1),(5,29),(35,57),(65,76),(8,81)]),
  (2,2,[(232,107),(145,32),(175,108),(148,33),(91,1),(34,57),(64,1),(7,57)])]
theorem fast11_00_eq : flattenGrouped fast11_00=encode flat11_00 := by rfl

def fast11_01 : List FastBlock := [
  (0,0,[(435,105),(348,102),(261,92),(174,27),(378,103),(291,102),(204,23),(117,41),(408,103),(321,11),(234,18),(147,100),(60,13),(351,98),(264,51),(177,39),(90,94),(294,107),(207,23),(120,32),(33,73),(324,26),(237,6),(150,14),(63,0),(267,89),(180,53),(93,48),(6,91),(210,26),(123,67),(36,43),(240,15),(153,49),(66,55),(183,5),(96,46),(9,11),(126,2),(39,26),(156,106),(69,5),(99,92),(12,35),(42,35),(72,106),(15,47)]),
  (0,1,[(377,103),(290,70),(203,89),(320,104),(146,86),(350,93),(263,9),(176,30),(89,21),(2,78),(293,61),(206,89),(119,20),(32,36),(323,97),(236,70),(149,71),(62,74),(266,10),(179,85),(92,32),(5,5),(209,10),(122,54),(35,91),(239,82),(152,37),(65,16),(182,21),(95,23),(8,6),(125,9),(38,100),(155,14),(68,33),(98,5),(11,38),(41,63),(71,53),(14,78)]),
  (0,2,[(406,4),(319,24),(232,95),(145,41),(349,6),(262,72),(175,97),(292,104),(205,97),(118,88),(31,36),(322,20),(235,85),(148,39),(61,67),(265,47),(178,28),(91,89),(4,36),(208,83),(121,37),(34,95),(238,96),(151,17),(64,45),(181,41),(94,12),(7,28),(124,95),(37,14),(154,36),(67,0),(97,99),(10,79),(40,22),(70,4),(13,10)]),
  (1,0,[(261,107),(174,19),(87,23),(204,48),(117,41),(30,3),(234,86),(147,82),(60,16),(177,14),(90,16),(3,3),(294,105),(207,62),(120,71),(33,74),(237,103),(150,79),(63,5),(180,106),(93,53),(6,13),(210,89),(123,97),(36,59),(153,48),(66,35),(96,68),(9,5),(126,5),(39,24),(69,47),(42,43)]),
  (1,1,[(203,106),(116,96),(320,52),(233,80),(146,101),(59,22),(263,52),(176,82),(89,21),(119,47),(32,44),(236,24),(149,38),(62,79),(179,103),(92,64),(5,22),(209,103),(122,16),(35,86),(152,81),(65,100),(95,23),(8,84),(125,46),(38,97),(68,94),(41,4)]),
  (1,2,[(232,1),(145,44),(58,43),(262,52),(175,7),(88,46),(1,53),(205,78),(118,94),(31,58),(235,52),(148,64),(61,34),(178,107),(91,16),(4,43),(121,69),(34,100),(151,103),(64,17),(94,29),(7,104),(124,105),(37,96),(67,20),(40,99)]),
  (2,0,[(348,1),(261,45),(174,43),(291,2),(204,74),(117,53),(234,58),(147,57),(60,32),(264,43),(177,98),(90,108),(207,15),(120,47),(33,32),(150,53),(63,32),(180,108),(93,88),(6,18),(123,52),(36,12),(9,39)]),
  (2,1,[(290,2),(203,47),(116,13),(29,43),(233,58),(146,93),(59,45),(263,2),(176,49),(89,80),(206,102),(119,11),(32,39),(149,91),(62,41),(179,43),(92,28),(122,53),(35,86),(8,88)]),
  (2,2,[(232,1),(145,2),(58,77),(175,56),(88,1),(205,2),(118,55),(31,45),(148,4),(61,78),(178,1),(91,52),(34,43)])]
theorem fast11_01_eq : flattenGrouped fast11_01=encode flat11_01 := by rfl

def fast11_02 : List FastBlock := [
  (0,0,[(522,107),(435,87),(348,103),(261,73),(174,84),(87,14),(465,103),(378,21),(291,80),(204,97),(117,70),(408,0),(321,10),(234,99),(147,49),(60,42),(438,89),(351,77),(264,73),(177,58),(90,8),(381,94),(294,78),(207,69),(120,9),(33,28),(324,30),(237,25),(150,47),(63,40),(354,11),(267,72),(180,52),(93,42),(6,98),(297,58),(210,98),(123,18),(36,76),(240,48),(153,58),(66,71),(270,40),(183,80),(96,104),(9,19),(213,78),(126,51),(39,65),(156,81),(69,20),(186,104),(99,87),(12,41),(129,47),(42,46),(15,78)]),
  (0,1,[(464,103),(377,13),(290,88),(203,3),(116,76),(29,4),(407,92),(320,82),(233,61),(146,38),(59,54),(437,103),(350,4),(263,11),(176,10),(89,19),(380,7),(293,79),(206,82),(119,14),(32,25),(323,10),(236,63),(149,48),(62,37),(353,26),(266,87),(179,21),(92,78),(296,67),(209,93),(122,48),(35,69),(239,37),(152,81),(65,14),(269,17),(182,29),(95,90),(8,93),(212,13),(125,38),(38,83),(155,23),(68,81),(185,30),(98,15),(11,34),(128,50),(41,43),(14,25)]),
  (0,2,[(406,102),(319,50),(232,38),(145,106),(58,95),(349,91),(262,80),(175,35),(88,49),(379,95),(292,37),(205,79),(118,91),(31,54),(322,29),(235,52),(148,6),(61,73),(352,102),(265,35),(178,97),(91,40),(295,12),(208,106),(121,35),(34,95),(238,55),(151,11),(64,99),(268,69),(181,22),(94,29),(211,64),(124,103),(37,65),(154,93),(67,53),(184,7),(97,53),(10,55),(127,67),(40,77),(13,101)]),
  (1,0,[(435,105),(348,102),(261,92),(174,27),(378,103),(291,102),(204,23),(117,41),(408,103),(321,11),(234,18),(147,100),(60,13),(351,98),(264,51),(177,39),(90,94),(294,107),(207,23),(120,32),(33,73),(324,26),(237,6),(150,14),(63,0),(267,89),(180,53),(93,48),(6,91),(210,26),(123,67),(36,43),(240,15),(153,49),(66,55),(183,5),(96,46),(9,11),(126,2),(39,26),(156,106),(69,5),(99,92),(12,35),(42,35),(72,106),(15,47)]),
  (1,1,[(377,103),(290,70),(203,89),(320,104),(146,86),(350,93),(263,9),(176,30),(89,21),(2,78),(293,61),(206,89),(119,20),(32,36),(323,97),(236,70),(149,71),(62,74),(266,10),(179,85),(92,32),(5,5),(209,10),(122,54),(35,91),(239,82),(152,37),(65,16),(182,21),(95,23),(8,6),(125,9),(38,100),(155,14),(68,33),(98,5),(11,38),(41,63),(71,53),(14,78)]),
  (1,2,[(406,4),(319,24),(232,95),(145,41),(349,6),(262,72),(175,97),(292,104),(205,97),(118,88),(31,36),(322,20),(235,85),(148,39),(61,67),(265,47),(178,28),(91,89),(4,36),(208,83),(121,37),(34,95),(238,96),(151,17),(64,45),(181,41),(94,12),(7,28),(124,95),(37,14),(154,36),(67,0),(97,99),(10,79),(40,22),(70,4),(13,10)]),
  (2,0,[(261,107),(174,19),(87,23),(204,48),(117,41),(30,3),(234,86),(147,82),(60,16),(177,14),(90,16),(3,3),(294,105),(207,62),(120,71),(33,74),(237,103),(150,79),(63,5),(180,106),(93,53),(6,13),(210,89),(123,97),(36,59),(153,48),(66,35),(96,68),(9,5),(126,5),(39,24),(69,47),(42,43)]),
  (2,1,[(203,106),(116,96),(320,52),(233,80),(146,101),(59,22),(263,52),(176,82),(89,21),(119,47),(32,44),(236,24),(149,38),(62,79),(179,103),(92,64),(5,22),(209,103),(122,16),(35,86),(152,81),(65,100),(95,23),(8,84),(125,46),(38,97),(68,94),(41,4)]),
  (2,2,[(232,1),(145,44),(58,43),(262,52),(175,7),(88,46),(1,53),(205,78),(118,94),(31,58),(235,52),(148,64),(61,34),(178,107),(91,16),(4,43),(121,69),(34,100),(151,103),(64,17),(94,29),(7,104),(124,105),(37,96),(67,20),(40,99)])]
theorem fast11_02_eq : flattenGrouped fast11_02=encode flat11_02 := by rfl

def fast11_10 : List FastBlock := [
  (0,0,[(319,108),(232,97),(145,57),(58,68),(349,57),(262,21),(175,25),(88,68),(1,61),(292,88),(205,106),(118,70),(31,59),(322,57),(235,29),(148,102),(61,51),(265,31),(178,87),(91,100),(4,73),(208,0),(121,71),(34,57),(238,87),(151,90),(64,40),(181,20),(94,27),(7,60),(211,4),(124,62),(37,55),(154,4),(67,15),(97,65),(10,53),(127,96),(40,14),(70,16),(43,106)]),
  (0,1,[(261,106),(174,84),(87,89),(291,57),(204,41),(117,104),(30,59),(234,7),(147,53),(60,24),(264,5),(177,52),(90,45),(3,59),(294,105),(207,95),(120,70),(33,82),(237,51),(150,55),(63,89),(180,5),(93,20),(6,79),(210,89),(123,108),(36,73),(153,58),(66,31),(96,19),(9,10),(126,9),(39,37),(69,37),(42,53)]),
  (0,2,[(203,106),(116,96),(320,52),(233,80),(146,101),(59,22),(263,52),(176,82),(89,21),(119,47),(32,44),(236,24),(149,38),(62,79),(179,103),(92,64),(5,22),(209,103),(122,16),(35,86),(152,81),(65,100),(95,23),(8,84),(125,46),(38,97),(68,94),(41,4)]),
  (1,0,[(319,108),(232,30),(145,96),(58,66),(262,52),(175,45),(88,64),(292,107),(205,62),(118,79),(31,23),(235,27),(148,61),(61,87),(265,108),(178,80),(91,93),(208,65),(121,85),(34,27),(151,23),(64,24),(181,33),(94,81),(37,2)]),
  (1,1,[(348,1),(261,44),(174,41),(87,32),(291,2),(204,18),(117,52),(234,55),(147,0),(60,19),(264,43),(177,38),(90,29),(207,12),(120,49),(33,96),(150,49),(63,20),(180,107),(93,36),(6,18),(123,52),(36,78),(9,39)]),
  (1,2,[(290,2),(203,47),(116,13),(29,43),(233,58),(146,93),(59,45),(263,2),(176,49),(89,80),(206,102),(119,11),(32,39),(149,91),(62,41),(179,43),(92,28),(122,53),(35,86),(8,88)]),
  (2,0,[(319,2),(232,13),(145,43),(262,3),(175,45),(205,1),(235,10),(148,41),(178,42),(91,32),(121,51),(34,80),(151,107),(64,84),(94,84),(7,80),(37,80),(67,33),(10,28)]),
  (2,1,[(261,2),(174,77),(204,108),(117,32),(234,3),(147,44),(60,88),(177,78),(120,32),(150,43),(63,52),(93,107),(36,104),(66,108),(9,52)]),
  (2,2,[(176,1),(2,21),(119,108),(149,2),(62,77),(92,1),(5,29),(35,57),(65,76),(8,81)])]
theorem fast11_10_eq : flattenGrouped fast11_10=encode flat11_10 := by rfl

def fast11_11 : List FastBlock := [
  (0,0,[(493,105),(406,104),(319,19),(232,56),(145,4),(436,99),(349,96),(262,41),(175,11),(379,108),(292,107),(205,85),(118,55),(31,62),(409,3),(322,44),(235,51),(148,48),(61,37),(352,22),(265,61),(178,45),(91,20),(4,62),(295,32),(208,15),(121,89),(34,50),(325,19),(238,0),(151,5),(64,68),(268,106),(181,27),(94,87),(7,13),(211,96),(124,93),(37,67),(241,80),(154,92),(67,54),(184,19),(97,106),(10,73),(127,71),(40,106),(157,94),(70,106),(100,92),(13,93),(43,62),(73,23),(16,3)]),
  (0,1,[(435,101),(348,78),(261,106),(174,95),(378,97),(291,30),(204,35),(117,41),(408,99),(321,101),(234,44),(147,80),(60,86),(351,72),(264,3),(177,12),(90,27),(294,65),(207,7),(120,73),(33,1),(324,6),(237,56),(150,47),(63,56),(267,55),(180,8),(93,23),(6,55),(210,11),(123,18),(36,29),(240,28),(153,46),(66,105),(183,37),(96,34),(9,92),(126,26),(39,42),(156,70),(69,92),(99,98),(12,65),(42,3),(72,102),(15,37)]),
  (0,2,[(377,103),(290,70),(203,89),(320,104),(146,86),(350,93),(263,9),(176,30),(89,21),(2,78),(293,61),(206,89),(119,20),(32,36),(323,97),(236,70),(149,71),(62,74),(266,10),(179,85),(92,32),(5,5),(209,10),(122,54),(35,91),(239,82),(152,37),(65,16),(182,21),(95,23),(8,6),(125,9),(38,100),(155,14),(68,33),(98,5),(11,38),(41,63),(71,53),(14,78)]),
  (1,0,[(319,108),(232,97),(145,57),(58,68),(349,57),(262,21),(175,25),(88,68),(1,61),(292,88),(205,106),(118,70),(31,59),(322,57),(235,29),(148,102),(61,51),(265,31),(178,87),(91,100),(4,73),(208,0),(121,71),(34,57),(238,87),(151,90),(64,40),(181,20),(94,27),(7,60),(211,4),(124,62),(37,55),(154,4),(67,15),(97,65),(10,53),(127,96),(40,14),(70,16),(43,106)]),
  (1,1,[(261,106),(174,84),(87,89),(291,57),(204,41),(117,104),(30,59),(234,7),(147,53),(60,24),(264,5),(177,52),(90,45),(3,59),(294,105),(207,95),(120,70),(33,82),(237,51),(150,55),(63,89),(180,5),(93,20),(6,79),(210,89),(123,108),(36,73),(153,58),(66,31),(96,19),(9,10),(126,9),(39,37),(69,37),(42,53)]),
  (1,2,[(203,106),(116,96),(320,52),(233,80),(146,101),(59,22),(263,52),(176,82),(89,21),(119,47),(32,44),(236,24),(149,38),(62,79),(179,103),(92,64),(5,22),(209,103),(122,16),(35,86),(152,81),(65,100),(95,23),(8,84),(125,46),(38,97),(68,94),(41,4)]),
  (2,0,[(319,108),(232,30),(145,96),(58,66),(262,52),(175,45),(88,64),(292,107),(205,62),(118,79),(31,23),(235,27),(148,61),(61,87),(265,108),(178,80),(91,93),(208,65),(121,85),(34,27),(151,23),(64,24),(181,33),(94,81),(37,2)]),
  (2,1,[(348,1),(261,44),(174,41),(87,32),(291,2),(204,18),(117,52),(234,55),(147,0),(60,19),(264,43),(177,38),(90,29),(207,12),(120,49),(33,96),(150,49),(63,20),(180,107),(93,36),(6,18),(123,52),(36,78),(9,39)]),
  (2,2,[(290,2),(203,47),(116,13),(29,43),(233,58),(146,93),(59,45),(263,2),(176,49),(89,80),(206,102),(119,11),(32,39),(149,91),(62,41),(179,43),(92,28),(122,53),(35,86),(8,88)])]
theorem fast11_11_eq : flattenGrouped fast11_11=encode flat11_11 := by rfl

def fast11_12 : List FastBlock := [
  (0,0,[(493,7),(406,53),(319,36),(232,20),(145,27),(58,97),(436,25),(349,57),(262,89),(175,93),(88,56),(466,14),(379,78),(292,44),(205,4),(118,84),(31,93),(409,81),(322,91),(235,108),(148,38),(61,76),(439,7),(352,99),(265,14),(178,71),(91,99),(382,78),(295,47),(208,90),(121,64),(34,26),(325,18),(238,89),(151,89),(64,32),(355,27),(268,16),(181,50),(94,78),(298,45),(211,80),(124,106),(37,92),(241,23),(154,22),(67,102),(271,90),(184,41),(97,38),(10,16),(214,76),(127,72),(40,85),(157,59),(70,37),(187,13),(100,13),(13,33),(130,31),(43,42),(16,63)]),
  (0,1,[(522,107),(435,94),(348,53),(261,35),(174,87),(87,28),(465,103),(378,39),(291,0),(204,62),(117,21),(408,21),(321,32),(234,91),(147,70),(60,2),(438,89),(351,66),(264,50),(177,17),(90,104),(381,6),(294,6),(207,2),(120,96),(33,83),(324,98),(237,85),(150,6),(63,90),(354,18),(267,91),(180,53),(93,12),(6,98),(297,86),(210,79),(123,63),(36,90),(240,38),(153,53),(66,16),(270,80),(183,74),(96,22),(9,19),(213,7),(126,4),(39,54),(156,30),(69,108),(186,97),(99,34),(12,95),(129,89),(42,86),(15,86)]),
  (0,2,[(464,103),(377,13),(290,88),(203,3),(116,76),(29,4),(407,92),(320,82),(233,61),(146,38),(59,54),(437,103),(350,4),(263,11),(176,10),(89,19),(380,7),(293,79),(206,82),(119,14),(32,25),(323,10),(236,63),(149,48),(62,37),(353,26),(266,87),(179,21),(92,78),(296,67),(209,93),(122,48),(35,69),(239,37),(152,81),(65,14),(269,17),(182,29),(95,90),(8,93),(212,13),(125,38),(38,83),(155,23),(68,81),(185,30),(98,15),(11,34),(128,50),(41,43),(14,25)]),
  (1,0,[(493,105),(406,104),(319,19),(232,56),(145,4),(436,99),(349,96),(262,41),(175,11),(379,108),(292,107),(205,85),(118,55),(31,62),(409,3),(322,44),(235,51),(148,48),(61,37),(352,22),(265,61),(178,45),(91,20),(4,62),(295,32),(208,15),(121,89),(34,50),(325,19),(238,0),(151,5),(64,68),(268,106),(181,27),(94,87),(7,13),(211,96),(124,93),(37,67),(241,80),(154,92),(67,54),(184,19),(97,106),(10,73),(127,71),(40,106),(157,94),(70,106),(100,92),(13,93),(43,62),(73,23),(16,3)]),
  (1,1,[(435,101),(348,78),(261,106),(174,95),(378,97),(291,30),(204,35),(117,41),(408,99),(321,101),(234,44),(147,80),(60,86),(351,72),(264,3),(177,12),(90,27),(294,65),(207,7),(120,73),(33,1),(324,6),(237,56),(150,47),(63,56),(267,55),(180,8),(93,23),(6,55),(210,11),(123,18),(36,29),(240,28),(153,46),(66,105),(183,37),(96,34),(9,92),(126,26),(39,42),(156,70),(69,92),(99,98),(12,65),(42,3),(72,102),(15,37)]),
  (1,2,[(377,103),(290,70),(203,89),(320,104),(146,86),(350,93),(263,9),(176,30),(89,21),(2,78),(293,61),(206,89),(119,20),(32,36),(323,97),(236,70),(149,71),(62,74),(266,10),(179,85),(92,32),(5,5),(209,10),(122,54),(35,91),(239,82),(152,37),(65,16),(182,21),(95,23),(8,6),(125,9),(38,100),(155,14),(68,33),(98,5),(11,38),(41,63),(71,53),(14,78)]),
  (2,0,[(319,108),(232,97),(145,57),(58,68),(349,57),(262,21),(175,25),(88,68),(1,61),(292,88),(205,106),(118,70),(31,59),(322,57),(235,29),(148,102),(61,51),(265,31),(178,87),(91,100),(4,73),(208,0),(121,71),(34,57),(238,87),(151,90),(64,40),(181,20),(94,27),(7,60),(211,4),(124,62),(37,55),(154,4),(67,15),(97,65),(10,53),(127,96),(40,14),(70,16),(43,106)]),
  (2,1,[(261,106),(174,84),(87,89),(291,57),(204,41),(117,104),(30,59),(234,7),(147,53),(60,24),(264,5),(177,52),(90,45),(3,59),(294,105),(207,95),(120,70),(33,82),(237,51),(150,55),(63,89),(180,5),(93,20),(6,79),(210,89),(123,108),(36,73),(153,58),(66,31),(96,19),(9,10),(126,9),(39,37),(69,37),(42,53)]),
  (2,2,[(203,106),(116,96),(320,52),(233,80),(146,101),(59,22),(263,52),(176,82),(89,21),(119,47),(32,44),(236,24),(149,38),(62,79),(179,103),(92,64),(5,22),(209,103),(122,16),(35,86),(152,81),(65,100),(95,23),(8,84),(125,46),(38,97),(68,94),(41,4)])]
theorem fast11_12_eq : flattenGrouped fast11_12=encode flat11_12 := by rfl

def fast11_20 : List FastBlock := [
  (0,0,[(290,3),(203,26),(116,20),(407,57),(320,58),(233,64),(146,62),(59,50),(350,5),(263,85),(176,104),(89,105),(293,57),(206,99),(119,29),(32,100),(323,57),(236,100),(149,63),(62,49),(266,63),(179,14),(92,24),(5,50),(296,6),(209,16),(122,60),(35,40),(239,63),(152,24),(65,53),(182,25),(95,48),(8,35),(212,83),(125,27),(38,81),(155,26),(68,107),(98,11),(11,47),(128,97),(41,59),(71,46),(44,23)]),
  (0,1,[(319,108),(232,100),(145,70),(58,68),(349,5),(262,50),(175,33),(88,46),(1,61),(292,36),(205,27),(118,62),(31,59),(322,5),(235,58),(148,63),(61,94),(265,64),(178,76),(91,0),(4,73),(208,6),(121,69),(34,100),(238,69),(151,36),(64,93),(181,54),(94,81),(7,38),(211,10),(124,23),(37,103),(154,95),(67,36),(97,57),(10,78),(127,50),(40,26),(70,27),(43,102)]),
  (0,2,[(261,106),(174,84),(87,89),(291,57),(204,41),(117,104),(30,59),(234,7),(147,53),(60,24),(264,5),(177,52),(90,45),(3,59),(294,105),(207,95),(120,70),(33,82),(237,51),(150,55),(63,89),(180,5),(93,20),(6,79),(210,89),(123,108),(36,73),(153,58),(66,31),(96,19),(9,10),(126,9),(39,37),(69,37),(42,53)]),
  (1,0,[(377,107),(290,17),(203,74),(116,46),(29,68),(320,49),(233,81),(146,84),(59,89),(350,107),(263,66),(176,87),(89,8),(293,71),(206,68),(119,8),(32,51),(236,86),(149,43),(62,33),(266,23),(179,40),(92,7),(209,0),(122,92),(35,6),(152,7),(65,68),(182,2),(95,73),(8,91),(125,5),(38,25),(11,70)]),
  (1,1,[(319,106),(232,92),(145,83),(58,23),(262,103),(175,61),(88,19),(292,103),(205,75),(118,95),(31,89),(235,85),(148,66),(61,3),(265,106),(178,49),(91,81),(208,29),(121,46),(34,97),(151,97),(64,6),(181,99),(94,53),(124,56),(37,46),(10,21)]),
  (1,2,[(348,1),(261,44),(174,41),(87,32),(291,2),(204,18),(117,52),(234,55),(147,0),(60,19),(264,43),(177,38),(90,29),(207,12),(120,49),(33,96),(150,49),(63,20),(180,107),(93,36),(6,18),(123,52),(36,78),(9,39)]),
  (2,0,[(263,108),(176,32),(89,88),(2,18),(119,77),(32,88),(236,107),(149,97),(62,66),(179,30),(92,35),(5,95),(122,18),(35,51),(152,99),(65,11),(95,94),(8,61),(38,56),(68,1),(11,57)]),
  (2,1,[(319,2),(232,13),(145,43),(262,3),(175,45),(31,88),(235,10),(148,42),(178,39),(91,64),(4,88),(121,51),(34,51),(151,105),(64,59),(94,7),(7,51),(37,51),(67,66),(10,56)]),
  (2,2,[(261,2),(174,77),(204,108),(117,32),(234,3),(147,44),(60,88),(177,78),(120,32),(150,43),(63,52),(93,107),(36,104),(66,108),(9,52)])]
theorem fast11_20_eq : flattenGrouped fast11_20=encode flat11_20 := by rfl

def fast11_21 : List FastBlock := [
  (0,0,[(464,6),(377,65),(290,80),(203,14),(407,11),(320,97),(233,43),(146,27),(437,16),(350,29),(263,40),(176,90),(89,49),(2,98),(380,84),(293,22),(206,67),(119,38),(32,93),(410,12),(323,83),(236,9),(149,2),(62,43),(353,19),(266,26),(179,10),(92,3),(5,9),(296,31),(209,66),(122,85),(35,62),(326,67),(239,91),(152,78),(65,29),(269,9),(182,38),(95,26),(8,30),(212,82),(125,94),(38,93),(242,76),(155,101),(68,67),(185,20),(98,85),(11,106),(128,11),(41,46),(158,82),(71,106),(101,34),(14,44),(44,39),(74,5),(17,67)]),
  (0,1,[(493,105),(406,1),(319,58),(232,76),(145,4),(436,99),(349,101),(262,41),(175,34),(379,21),(292,28),(205,75),(118,34),(31,93),(409,3),(322,97),(235,71),(148,51),(61,1),(352,50),(265,91),(178,53),(91,34),(4,93),(295,70),(208,59),(121,37),(34,9),(325,31),(238,29),(151,98),(64,12),(268,14),(181,14),(94,39),(7,8),(211,65),(124,16),(37,79),(241,107),(154,46),(67,47),(184,93),(97,50),(10,67),(127,57),(40,77),(157,80),(70,10),(100,34),(13,55),(43,30),(73,79),(16,34)]),
  (0,2,[(435,101),(348,78),(261,106),(174,95),(378,97),(291,30),(204,35),(117,41),(408,99),(321,101),(234,44),(147,80),(60,86),(351,72),(264,3),(177,12),(90,27),(294,65),(207,7),(120,73),(33,1),(324,6),(237,56),(150,47),(63,56),(267,55),(180,8),(93,23),(6,55),(210,11),(123,18),(36,29),(240,28),(153,46),(66,105),(183,37),(96,34),(9,92),(126,26),(39,42),(156,70),(69,92),(99,98),(12,65),(42,3),(72,102),(15,37)]),
  (1,0,[(290,3),(203,26),(116,20),(407,57),(320,58),(233,64),(146,62),(59,50),(350,5),(263,85),(176,104),(89,105),(293,57),(206,99),(119,29),(32,100),(323,57),(236,100),(149,63),(62,49),(266,63),(179,14),(92,24),(5,50),(296,6),(209,16),(122,60),(35,40),(239,63),(152,24),(65,53),(182,25),(95,48),(8,35),(212,83),(125,27),(38,81),(155,26),(68,107),(98,11),(11,47),(128,97),(41,59),(71,46),(44,23)]),
  (1,1,[(319,108),(232,100),(145,70),(58,68),(349,5),(262,50),(175,33),(88,46),(1,61),(292,36),(205,27),(118,62),(31,59),(322,5),(235,58),(148,63),(61,94),(265,64),(178,76),(91,0),(4,73),(208,6),(121,69),(34,100),(238,69),(151,36),(64,93),(181,54),(94,81),(7,38),(211,10),(124,23),(37,103),(154,95),(67,36),(97,57),(10,78),(127,50),(40,26),(70,27),(43,102)]),
  (1,2,[(261,106),(174,84),(87,89),(291,57),(204,41),(117,104),(30,59),(234,7),(147,53),(60,24),(264,5),(177,52),(90,45),(3,59),(294,105),(207,95),(120,70),(33,82),(237,51),(150,55),(63,89),(180,5),(93,20),(6,79),(210,89),(123,108),(36,73),(153,58),(66,31),(96,19),(9,10),(126,9),(39,37),(69,37),(42,53)]),
  (2,0,[(377,107),(290,17),(203,74),(116,46),(29,68),(320,49),(233,81),(146,84),(59,89),(350,107),(263,66),(176,87),(89,8),(293,71),(206,68),(119,8),(32,51),(236,86),(149,43),(62,33),(266,23),(179,40),(92,7),(209,0),(122,92),(35,6),(152,7),(65,68),(182,2),(95,73),(8,91),(125,5),(38,25),(11,70)]),
  (2,1,[(319,106),(232,92),(145,83),(58,23),(262,103),(175,61),(88,19),(292,103),(205,75),(118,95),(31,89),(235,85),(148,66),(61,3),(265,106),(178,49),(91,81),(208,29),(121,46),(34,97),(151,97),(64,6),(181,99),(94,53),(124,56),(37,46),(10,21)]),
  (2,2,[(348,1),(261,44),(174,41),(87,32),(291,2),(204,18),(117,52),(234,55),(147,0),(60,19),(264,43),(177,38),(90,29),(207,12),(120,49),(33,96),(150,49),(63,20),(180,107),(93,36),(6,18),(123,52),(36,78),(9,39)])]
theorem fast11_21_eq : flattenGrouped fast11_21=encode flat11_21 := by rfl

def fast11_22 : List FastBlock := [
  (0,0,[(551,6),(464,13),(377,1),(290,88),(203,20),(116,30),(29,19),(494,23),(407,15),(320,77),(233,58),(146,105),(59,89),(524,6),(437,39),(350,35),(263,63),(176,45),(89,9),(467,19),(380,25),(293,107),(206,83),(119,78),(32,60),(410,76),(323,50),(236,84),(149,14),(62,107),(440,103),(353,104),(266,11),(179,4),(92,34),(383,29),(296,102),(209,54),(122,107),(35,90),(326,8),(239,37),(152,81),(65,74),(356,78),(269,79),(182,33),(95,6),(8,33),(299,1),(212,39),(125,11),(38,44),(242,95),(155,20),(68,28),(272,95),(185,26),(98,65),(11,15),(215,22),(128,71),(41,48),(158,55),(71,14),(188,9),(101,34),(14,69),(131,15),(44,86),(17,62)]),
  (0,1,[(493,13),(406,40),(319,57),(232,17),(145,60),(58,93),(436,42),(349,84),(262,28),(175,55),(88,2),(466,26),(379,61),(292,54),(205,100),(118,98),(31,89),(409,91),(322,39),(235,74),(148,95),(61,106),(439,13),(352,85),(265,49),(178,13),(91,43),(382,45),(295,99),(208,96),(121,81),(34,1),(325,50),(238,42),(151,102),(64,35),(355,1),(268,1),(181,57),(94,95),(298,70),(211,67),(124,77),(37,39),(241,82),(154,12),(67,5),(271,73),(184,98),(97,85),(10,32),(214,33),(127,19),(40,77),(157,95),(70,22),(187,92),(100,107),(13,108),(130,90),(43,83),(16,38)]),
  (0,2,[(522,107),(435,94),(348,53),(261,35),(174,87),(87,28),(465,103),(378,39),(291,0),(204,62),(117,21),(408,21),(321,32),(234,91),(147,70),(60,2),(438,89),(351,66),(264,50),(177,17),(90,104),(381,6),(294,6),(207,2),(120,96),(33,83),(324,98),(237,85),(150,6),(63,90),(354,18),(267,91),(180,53),(93,12),(6,98),(297,86),(210,79),(123,63),(36,90),(240,38),(153,53),(66,16),(270,80),(183,74),(96,22),(9,19),(213,7),(126,4),(39,54),(156,30),(69,108),(186,97),(99,34),(12,95),(129,89),(42,86),(15,86)]),
  (1,0,[(464,6),(377,65),(290,80),(203,14),(407,11),(320,97),(233,43),(146,27),(437,16),(350,29),(263,40),(176,90),(89,49),(2,98),(380,84),(293,22),(206,67),(119,38),(32,93),(410,12),(323,83),(236,9),(149,2),(62,43),(353,19),(266,26),(179,10),(92,3),(5,9),(296,31),(209,66),(122,85),(35,62),(326,67),(239,91),(152,78),(65,29),(269,9),(182,38),(95,26),(8,30),(212,82),(125,94),(38,93),(242,76),(155,101),(68,67),(185,20),(98,85),(11,106),(128,11),(41,46),(158,82),(71,106),(101,34),(14,44),(44,39),(74,5),(17,67)]),
  (1,1,[(493,105),(406,1),(319,58),(232,76),(145,4),(436,99),(349,101),(262,41),(175,34),(379,21),(292,28),(205,75),(118,34),(31,93),(409,3),(322,97),(235,71),(148,51),(61,1),(352,50),(265,91),(178,53),(91,34),(4,93),(295,70),(208,59),(121,37),(34,9),(325,31),(238,29),(151,98),(64,12),(268,14),(181,14),(94,39),(7,8),(211,65),(124,16),(37,79),(241,107),(154,46),(67,47),(184,93),(97,50),(10,67),(127,57),(40,77),(157,80),(70,10),(100,34),(13,55),(43,30),(73,79),(16,34)]),
  (1,2,[(435,101),(348,78),(261,106),(174,95),(378,97),(291,30),(204,35),(117,41),(408,99),(321,101),(234,44),(147,80),(60,86),(351,72),(264,3),(177,12),(90,27),(294,65),(207,7),(120,73),(33,1),(324,6),(237,56),(150,47),(63,56),(267,55),(180,8),(93,23),(6,55),(210,11),(123,18),(36,29),(240,28),(153,46),(66,105),(183,37),(96,34),(9,92),(126,26),(39,42),(156,70),(69,92),(99,98),(12,65),(42,3),(72,102),(15,37)]),
  (2,0,[(290,3),(203,26),(116,20),(407,57),(320,58),(233,64),(146,62),(59,50),(350,5),(263,85),(176,104),(89,105),(293,57),(206,99),(119,29),(32,100),(323,57),(236,100),(149,63),(62,49),(266,63),(179,14),(92,24),(5,50),(296,6),(209,16),(122,60),(35,40),(239,63),(152,24),(65,53),(182,25),(95,48),(8,35),(212,83),(125,27),(38,81),(155,26),(68,107),(98,11),(11,47),(128,97),(41,59),(71,46),(44,23)]),
  (2,1,[(319,108),(232,100),(145,70),(58,68),(349,5),(262,50),(175,33),(88,46),(1,61),(292,36),(205,27),(118,62),(31,59),(322,5),(235,58),(148,63),(61,94),(265,64),(178,76),(91,0),(4,73),(208,6),(121,69),(34,100),(238,69),(151,36),(64,93),(181,54),(94,81),(7,38),(211,10),(124,23),(37,103),(154,95),(67,36),(97,57),(10,78),(127,50),(40,26),(70,27),(43,102)]),
  (2,2,[(261,106),(174,84),(87,89),(291,57),(204,41),(117,104),(30,59),(234,7),(147,53),(60,24),(264,5),(177,52),(90,45),(3,59),(294,105),(207,95),(120,70),(33,82),(237,51),(150,55),(63,89),(180,5),(93,20),(6,79),(210,89),(123,108),(36,73),(153,58),(66,31),(96,19),(9,10),(126,9),(39,37),(69,37),(42,53)])]
theorem fast11_22_eq : flattenGrouped fast11_22=encode flat11_22 := by rfl

def fast11 : Fin 3 → Fin 3 → List FastBlock :=
  ![![fast11_00, fast11_01, fast11_02], ![fast11_10, fast11_11, fast11_12], ![fast11_20, fast11_21, fast11_22]]
end CycleQ2SegreModularFastActions
#print axioms CycleQ2SegreModularFastActions.fast11_22_eq
end


/- Component: continuation_3/SegreModularFastActions12.lean -/
section
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
set_option Elab.async false
namespace CycleQ2SegreModularFastActions
open CycleQ2SparseModularFastDot CycleQ2SegreModularDetectorExpressions

def fast12_00 : List FastBlock := [
  (0,0,[(261,108),(174,65),(87,2),(0,43),(204,108),(117,2),(30,88),(234,52),(147,57),(60,78),(264,52),(177,94),(90,4),(3,39),(207,52),(120,107),(33,37),(63,74),(180,28),(6,31),(36,64),(9,33)]),
  (0,1,[(203,107),(116,66),(29,45),(59,47),(176,108),(89,3),(2,88),(206,52),(119,68),(32,26),(149,57),(62,43),(179,52),(5,82),(35,83),(8,107)]),
  (0,2,[(145,108),(58,1),(262,52),(175,57),(88,1),(205,57),(31,47),(61,4),(91,1),(4,46),(34,46),(7,43)]),
  (1,0,[(234,1),(147,77),(90,32),(207,1),(120,76),(150,25),(63,52),(93,85),(123,76)]),
  (1,1,[(290,1),(203,76),(116,32),(146,31),(206,76),(119,32),(149,35),(92,108),(122,1),(65,52)]),
  (1,2,[(232,1),(145,108),(175,107),(88,1),(118,32),(148,107),(121,33)]),
  (2,0,[(93,1),(6,77),(36,1),(9,76)]),
  (2,1,[(35,1),(8,1)]),
  (2,2,[(91,1),(4,108),(34,108)])]
theorem fast12_00_eq : flattenGrouped fast12_00=encode flat12_00 := by rfl

def fast12_01 : List FastBlock := [
  (0,0,[(294,2),(207,88),(120,105),(33,23),(237,2),(150,105),(63,42),(180,106),(93,70),(6,91),(210,84),(123,74),(36,49),(153,107),(66,67),(96,83),(9,78),(126,90),(39,53),(69,28),(99,2),(12,26),(42,16),(15,43)]),
  (0,1,[(236,3),(149,10),(62,96),(92,93),(209,2),(122,101),(35,63),(152,4),(65,41),(182,108),(95,78),(8,76),(125,103),(38,35),(68,69),(98,99),(11,87),(41,86),(14,4)]),
  (0,2,[(265,107),(178,67),(91,1),(4,43),(121,1),(34,88),(151,1),(64,30),(181,66),(94,108),(7,39),(124,106),(37,53),(67,24),(97,108),(10,94),(40,84),(13,99)]),
  (1,0,[(261,108),(174,65),(87,2),(0,43),(204,108),(117,2),(30,88),(234,52),(147,57),(60,78),(264,52),(177,94),(90,4),(3,39),(207,52),(120,107),(33,37),(63,74),(180,28),(6,31),(36,64),(9,33)]),
  (1,1,[(203,107),(116,66),(29,45),(59,47),(176,108),(89,3),(2,88),(206,52),(119,68),(32,26),(149,57),(62,43),(179,52),(5,82),(35,83),(8,107)]),
  (1,2,[(145,108),(58,1),(262,52),(175,57),(88,1),(205,57),(31,47),(61,4),(91,1),(4,46),(34,46),(7,43)]),
  (2,0,[(234,1),(147,77),(90,32),(207,1),(120,76),(150,25),(63,52),(93,85),(123,76)]),
  (2,1,[(290,1),(203,76),(116,32),(146,31),(206,76),(119,32),(149,35),(92,108),(122,1),(65,52)]),
  (2,2,[(232,1),(145,108),(175,107),(88,1),(118,32),(148,107),(121,33)])]
theorem fast12_01_eq : flattenGrouped fast12_01=encode flat12_01 := by rfl

def fast12_02 : List FastBlock := [
  (0,0,[(435,3),(348,23),(261,103),(174,89),(378,1),(291,15),(204,67),(117,86),(408,2),(321,35),(234,89),(147,13),(351,16),(264,14),(177,91),(90,18),(381,108),(294,30),(207,37),(120,26),(324,31),(237,82),(150,85),(63,53),(267,40),(180,102),(93,33),(297,23),(210,101),(123,82),(240,3),(153,86),(66,43),(183,91),(96,12),(213,7),(126,4),(156,0),(69,23),(99,8),(129,86),(72,28)]),
  (0,1,[(464,107),(377,25),(290,47),(203,107),(116,41),(407,107),(320,65),(233,31),(146,74),(350,6),(263,1),(176,66),(380,23),(293,39),(206,101),(119,104),(323,64),(236,72),(149,6),(266,91),(179,93),(92,91),(209,9),(122,60),(239,57),(152,23),(65,2),(182,63),(95,87),(212,13),(125,106),(155,33),(68,96),(98,40),(128,7),(71,104)]),
  (0,2,[(406,105),(319,88),(232,5),(145,20),(262,47),(175,45),(88,66),(379,107),(292,71),(205,69),(118,82),(322,91),(235,34),(148,48),(265,43),(178,17),(91,70),(295,66),(208,104),(121,74),(238,15),(151,18),(181,81),(94,78),(211,106),(124,103),(154,6),(67,6),(97,16),(127,56),(70,53)]),
  (1,0,[(294,2),(207,88),(120,105),(33,23),(237,2),(150,105),(63,42),(180,106),(93,70),(6,91),(210,84),(123,74),(36,49),(153,107),(66,67),(96,83),(9,78),(126,90),(39,53),(69,28),(99,2),(12,26),(42,16),(15,43)]),
  (1,1,[(236,3),(149,10),(62,96),(92,93),(209,2),(122,101),(35,63),(152,4),(65,41),(182,108),(95,78),(8,76),(125,103),(38,35),(68,69),(98,99),(11,87),(41,86),(14,4)]),
  (1,2,[(265,107),(178,67),(91,1),(4,43),(121,1),(34,88),(151,1),(64,30),(181,66),(94,108),(7,39),(124,106),(37,53),(67,24),(97,108),(10,94),(40,84),(13,99)]),
  (2,0,[(261,108),(174,65),(87,2),(0,43),(204,108),(117,2),(30,88),(234,52),(147,57),(60,78),(264,52),(177,94),(90,4),(3,39),(207,52),(120,107),(33,37),(63,74),(180,28),(6,31),(36,64),(9,33)]),
  (2,1,[(203,107),(116,66),(29,45),(59,47),(176,108),(89,3),(2,88),(206,52),(119,68),(32,26),(149,57),(62,43),(179,52),(5,82),(35,83),(8,107)]),
  (2,2,[(145,108),(58,1),(262,52),(175,57),(88,1),(205,57),(31,47),(61,4),(91,1),(4,46),(34,46),(7,43)])]
theorem fast12_02_eq : flattenGrouped fast12_02=encode flat12_02 := by rfl

def fast12_10 : List FastBlock := [
  (0,0,[(232,1),(145,76),(58,32),(349,57),(262,81),(175,80),(88,31),(205,23),(118,61),(31,87),(235,52),(148,72),(61,5),(265,81),(178,27),(91,15),(4,55),(208,28),(121,62),(34,34),(64,86),(94,99),(7,60),(37,58),(10,2)]),
  (0,1,[(261,108),(174,66),(87,1),(0,43),(291,57),(204,51),(117,1),(30,88),(234,104),(147,58),(60,30),(177,37),(90,108),(3,39),(207,104),(120,106),(33,53),(63,24),(180,28),(93,108),(6,94),(36,84),(9,99)]),
  (0,2,[(203,107),(116,66),(29,45),(59,47),(176,108),(89,3),(2,88),(206,52),(119,68),(32,26),(149,57),(62,43),(179,52),(5,82),(35,83),(8,107)]),
  (1,0,[(319,108),(232,33),(145,77),(262,1),(175,45),(88,32),(205,79),(118,42),(235,35),(148,89),(178,45),(91,33),(208,76),(121,41),(151,10),(124,108)]),
  (1,1,[(261,108),(174,1),(204,2),(117,108),(147,46),(177,4),(90,31),(207,1),(120,44),(150,103),(63,52),(93,85),(123,43)]),
  (1,2,[(290,1),(203,76),(116,32),(146,31),(206,76),(119,32),(149,35),(92,108),(122,1),(65,52)]),
  (2,0,[(178,108),(91,33),(4,77),(34,78),(64,1),(94,33),(7,76),(37,76)]),
  (2,1,[(120,108),(33,1),(63,1),(6,78),(36,2),(9,76)]),
  (2,2,[(35,1),(8,1)])]
theorem fast12_10_eq : flattenGrouped fast12_10=encode flat12_10 := by rfl

def fast12_11 : List FastBlock := [
  (0,0,[(352,2),(265,87),(178,72),(91,98),(4,68),(295,2),(208,41),(121,52),(34,48),(238,108),(151,1),(268,86),(181,72),(94,41),(7,51),(211,46),(124,103),(37,92),(154,12),(67,70),(184,108),(97,35),(10,44),(127,36),(40,92),(70,54),(100,86),(13,57),(43,57),(16,106)]),
  (0,1,[(294,4),(207,21),(120,104),(33,89),(237,2),(150,104),(63,63),(267,2),(180,38),(93,39),(6,48),(210,18),(123,74),(36,31),(66,93),(183,43),(96,60),(9,39),(126,94),(39,15),(69,29),(99,3),(12,41),(42,51),(15,53)]),
  (0,2,[(236,3),(149,10),(62,96),(92,93),(209,2),(122,101),(35,63),(152,4),(65,41),(182,108),(95,78),(8,76),(125,103),(38,35),(68,69),(98,99),(11,87),(41,86),(14,4)]),
  (1,0,[(232,1),(145,76),(58,32),(349,57),(262,81),(175,80),(88,31),(205,23),(118,61),(31,87),(235,52),(148,72),(61,5),(265,81),(178,27),(91,15),(4,55),(208,28),(121,62),(34,34),(64,86),(94,99),(7,60),(37,58),(10,2)]),
  (1,1,[(261,108),(174,66),(87,1),(0,43),(291,57),(204,51),(117,1),(30,88),(234,104),(147,58),(60,30),(177,37),(90,108),(3,39),(207,104),(120,106),(33,53),(63,24),(180,28),(93,108),(6,94),(36,84),(9,99)]),
  (1,2,[(203,107),(116,66),(29,45),(59,47),(176,108),(89,3),(2,88),(206,52),(119,68),(32,26),(149,57),(62,43),(179,52),(5,82),(35,83),(8,107)]),
  (2,0,[(319,108),(232,33),(145,77),(262,1),(175,45),(88,32),(205,79),(118,42),(235,35),(148,89),(178,45),(91,33),(208,76),(121,41),(151,10),(124,108)]),
  (2,1,[(261,108),(174,1),(204,2),(117,108),(147,46),(177,4),(90,31),(207,1),(120,44),(150,103),(63,52),(93,85),(123,43)]),
  (2,2,[(290,1),(203,76),(116,32),(146,31),(206,76),(119,32),(149,35),(92,108),(122,1),(65,52)])]
theorem fast12_11_eq : flattenGrouped fast12_11=encode flat12_11 := by rfl

def fast12_12 : List FastBlock := [
  (0,0,[(493,4),(406,2),(319,86),(232,31),(145,95),(436,4),(349,83),(262,37),(175,46),(88,41),(466,2),(379,83),(292,85),(205,10),(118,51),(409,106),(322,43),(235,46),(148,43),(352,84),(265,42),(178,58),(91,58),(382,86),(295,57),(208,64),(121,99),(325,88),(238,63),(151,15),(268,15),(181,5),(94,10),(298,1),(211,100),(124,101),(241,56),(154,23),(67,83),(184,35),(97,28),(214,63),(127,52),(157,89),(70,41),(100,39),(130,104),(73,5)]),
  (0,1,[(435,7),(348,44),(261,98),(174,69),(378,1),(291,77),(204,22),(117,20),(408,8),(321,94),(234,15),(147,20),(351,34),(264,42),(177,107),(90,61),(381,1),(294,25),(207,60),(120,92),(324,92),(237,53),(150,72),(63,53),(267,91),(180,67),(93,72),(297,66),(210,25),(123,39),(240,100),(153,74),(66,43),(183,4),(96,37),(213,10),(126,103),(156,47),(69,17),(99,48),(129,30),(72,84)]),
  (0,2,[(464,107),(377,25),(290,47),(203,107),(116,41),(407,107),(320,65),(233,31),(146,74),(350,6),(263,1),(176,66),(380,23),(293,39),(206,101),(119,104),(323,64),(236,72),(149,6),(266,91),(179,93),(92,91),(209,9),(122,60),(239,57),(152,23),(65,2),(182,63),(95,87),(212,13),(125,106),(155,33),(68,96),(98,40),(128,7),(71,104)]),
  (1,0,[(352,2),(265,87),(178,72),(91,98),(4,68),(295,2),(208,41),(121,52),(34,48),(238,108),(151,1),(268,86),(181,72),(94,41),(7,51),(211,46),(124,103),(37,92),(154,12),(67,70),(184,108),(97,35),(10,44),(127,36),(40,92),(70,54),(100,86),(13,57),(43,57),(16,106)]),
  (1,1,[(294,4),(207,21),(120,104),(33,89),(237,2),(150,104),(63,63),(267,2),(180,38),(93,39),(6,48),(210,18),(123,74),(36,31),(66,93),(183,43),(96,60),(9,39),(126,94),(39,15),(69,29),(99,3),(12,41),(42,51),(15,53)]),
  (1,2,[(236,3),(149,10),(62,96),(92,93),(209,2),(122,101),(35,63),(152,4),(65,41),(182,108),(95,78),(8,76),(125,103),(38,35),(68,69),(98,99),(11,87),(41,86),(14,4)]),
  (2,0,[(232,1),(145,76),(58,32),(349,57),(262,81),(175,80),(88,31),(205,23),(118,61),(31,87),(235,52),(148,72),(61,5),(265,81),(178,27),(91,15),(4,55),(208,28),(121,62),(34,34),(64,86),(94,99),(7,60),(37,58),(10,2)]),
  (2,1,[(261,108),(174,66),(87,1),(0,43),(291,57),(204,51),(117,1),(30,88),(234,104),(147,58),(60,30),(177,37),(90,108),(3,39),(207,104),(120,106),(33,53),(63,24),(180,28),(93,108),(6,94),(36,84),(9,99)]),
  (2,2,[(203,107),(116,66),(29,45),(59,47),(176,108),(89,3),(2,88),(206,52),(119,68),(32,26),(149,57),(62,43),(179,52),(5,82),(35,83),(8,107)])]
theorem fast12_12_eq : flattenGrouped fast12_12=encode flat12_12 := by rfl

def fast12_20 : List FastBlock := [
  (0,0,[(290,2),(203,88),(116,105),(29,23),(233,2),(146,105),(59,42),(263,1),(176,74),(89,70),(2,91),(293,57),(206,5),(119,74),(32,49),(149,78),(62,67),(266,57),(179,48),(92,83),(5,78),(209,29),(122,90),(35,53),(152,28),(65,28),(182,81),(95,2),(8,26),(38,16),(11,43)]),
  (0,1,[(232,3),(145,10),(58,96),(349,57),(262,81),(175,80),(88,93),(205,26),(118,101),(31,63),(148,4),(61,41),(265,81),(178,80),(91,78),(4,76),(208,33),(121,103),(34,35),(151,52),(64,69),(181,57),(94,99),(7,87),(37,86),(10,4)]),
  (0,2,[(261,108),(174,66),(87,1),(0,43),(291,57),(204,51),(117,1),(30,88),(234,104),(147,58),(60,30),(177,37),(90,108),(3,39),(207,104),(120,106),(33,53),(63,24),(180,28),(93,108),(6,94),(36,84),(9,99)]),
  (1,0,[(377,108),(290,65),(203,2),(116,43),(320,108),(233,2),(146,88),(176,78),(293,66),(206,3),(119,9),(236,107),(149,40),(179,75),(92,77),(122,108),(152,12),(65,29),(95,24),(125,33),(68,81)]),
  (1,1,[(319,107),(232,66),(145,45),(262,1),(175,14),(88,32),(292,108),(205,3),(118,10),(235,68),(148,26),(178,10),(91,33),(121,10),(151,83),(94,58),(124,107),(67,57)]),
  (1,2,[(261,108),(174,1),(204,2),(117,108),(147,46),(177,4),(90,31),(207,1),(120,44),(150,103),(63,52),(93,85),(123,43)]),
  (2,0,[(122,108),(35,32),(65,108),(95,108),(8,32),(38,32),(11,33)]),
  (2,1,[(178,108),(91,33),(4,77),(34,78),(94,33),(7,76),(37,74),(10,108)]),
  (2,2,[(120,108),(33,1),(63,1),(6,78),(36,2),(9,76)])]
theorem fast12_20_eq : flattenGrouped fast12_20=encode flat12_20 := by rfl

def fast12_21 : List FastBlock := [
  (0,0,[(323,106),(236,86),(149,6),(62,20),(266,106),(179,6),(92,46),(296,107),(209,72),(122,24),(35,54),(239,93),(152,98),(65,57),(269,1),(182,104),(95,107),(8,34),(212,73),(125,85),(38,71),(155,69),(68,38),(185,86),(98,27),(11,60),(128,53),(41,5),(71,11),(101,102),(14,56),(44,0),(17,23)]),
  (0,1,[(352,2),(265,84),(178,62),(91,2),(4,68),(295,2),(208,41),(121,68),(34,48),(238,103),(151,108),(64,59),(268,86),(181,68),(94,16),(7,51),(211,45),(124,33),(37,62),(154,14),(67,103),(97,106),(10,77),(127,52),(40,79),(70,8),(100,96),(13,79),(43,76),(16,102)]),
  (0,2,[(294,4),(207,21),(120,104),(33,89),(237,2),(150,104),(63,63),(267,2),(180,38),(93,39),(6,48),(210,18),(123,74),(36,31),(66,93),(183,43),(96,60),(9,39),(126,94),(39,15),(69,29),(99,3),(12,41),(42,51),(15,53)]),
  (1,0,[(290,2),(203,88),(116,105),(29,23),(233,2),(146,105),(59,42),(263,1),(176,74),(89,70),(2,91),(293,57),(206,5),(119,74),(32,49),(149,78),(62,67),(266,57),(179,48),(92,83),(5,78),(209,29),(122,90),(35,53),(152,28),(65,28),(182,81),(95,2),(8,26),(38,16),(11,43)]),
  (1,1,[(232,3),(145,10),(58,96),(349,57),(262,81),(175,80),(88,93),(205,26),(118,101),(31,63),(148,4),(61,41),(265,81),(178,80),(91,78),(4,76),(208,33),(121,103),(34,35),(151,52),(64,69),(181,57),(94,99),(7,87),(37,86),(10,4)]),
  (1,2,[(261,108),(174,66),(87,1),(0,43),(291,57),(204,51),(117,1),(30,88),(234,104),(147,58),(60,30),(177,37),(90,108),(3,39),(207,104),(120,106),(33,53),(63,24),(180,28),(93,108),(6,94),(36,84),(9,99)]),
  (2,0,[(377,108),(290,65),(203,2),(116,43),(320,108),(233,2),(146,88),(176,78),(293,66),(206,3),(119,9),(236,107),(149,40),(179,75),(92,77),(122,108),(152,12),(65,29),(95,24),(125,33),(68,81)]),
  (2,1,[(319,107),(232,66),(145,45),(262,1),(175,14),(88,32),(292,108),(205,3),(118,10),(235,68),(148,26),(178,10),(91,33),(121,10),(151,83),(94,58),(124,107),(67,57)]),
  (2,2,[(261,108),(174,1),(204,2),(117,108),(147,46),(177,4),(90,31),(207,1),(120,44),(150,103),(63,52),(93,85),(123,43)])]
theorem fast12_21_eq : flattenGrouped fast12_21=encode flat12_21 := by rfl

def fast12_22 : List FastBlock := [
  (0,0,[(551,2),(464,20),(377,99),(290,89),(203,4),(116,4),(494,4),(407,64),(320,40),(233,48),(146,38),(437,105),(350,17),(263,44),(176,76),(467,20),(380,99),(293,81),(206,53),(119,103),(410,65),(323,49),(236,59),(149,23),(353,43),(266,55),(179,43),(92,78),(383,105),(296,97),(209,89),(122,29),(326,93),(239,26),(152,0),(65,64),(269,49),(182,70),(95,8),(299,96),(212,108),(125,53),(242,91),(155,87),(68,86),(185,44),(98,22),(215,95),(128,85),(158,106),(71,65),(101,17),(131,13),(74,53)]),
  (0,1,[(493,6),(406,86),(319,39),(232,33),(145,54),(436,6),(349,18),(262,6),(175,81),(88,41),(466,4),(379,52),(292,37),(205,55),(118,10),(409,85),(322,48),(235,23),(148,83),(352,14),(265,78),(178,95),(91,58),(382,63),(295,36),(208,88),(121,13),(325,24),(238,91),(151,58),(268,85),(181,107),(94,26),(298,1),(211,28),(124,63),(241,95),(154,3),(67,81),(184,48),(97,63),(214,50),(127,15),(157,49),(70,54),(100,4),(130,97),(73,10)]),
  (0,2,[(435,7),(348,44),(261,98),(174,69),(378,1),(291,77),(204,22),(117,20),(408,8),(321,94),(234,15),(147,20),(351,34),(264,42),(177,107),(90,61),(381,1),(294,25),(207,60),(120,92),(324,92),(237,53),(150,72),(63,53),(267,91),(180,67),(93,72),(297,66),(210,25),(123,39),(240,100),(153,74),(66,43),(183,4),(96,37),(213,10),(126,103),(156,47),(69,17),(99,48),(129,30),(72,84)]),
  (1,0,[(323,106),(236,86),(149,6),(62,20),(266,106),(179,6),(92,46),(296,107),(209,72),(122,24),(35,54),(239,93),(152,98),(65,57),(269,1),(182,104),(95,107),(8,34),(212,73),(125,85),(38,71),(155,69),(68,38),(185,86),(98,27),(11,60),(128,53),(41,5),(71,11),(101,102),(14,56),(44,0),(17,23)]),
  (1,1,[(352,2),(265,84),(178,62),(91,2),(4,68),(295,2),(208,41),(121,68),(34,48),(238,103),(151,108),(64,59),(268,86),(181,68),(94,16),(7,51),(211,45),(124,33),(37,62),(154,14),(67,103),(97,106),(10,77),(127,52),(40,79),(70,8),(100,96),(13,79),(43,76),(16,102)]),
  (1,2,[(294,4),(207,21),(120,104),(33,89),(237,2),(150,104),(63,63),(267,2),(180,38),(93,39),(6,48),(210,18),(123,74),(36,31),(66,93),(183,43),(96,60),(9,39),(126,94),(39,15),(69,29),(99,3),(12,41),(42,51),(15,53)]),
  (2,0,[(290,2),(203,88),(116,105),(29,23),(233,2),(146,105),(59,42),(263,1),(176,74),(89,70),(2,91),(293,57),(206,5),(119,74),(32,49),(149,78),(62,67),(266,57),(179,48),(92,83),(5,78),(209,29),(122,90),(35,53),(152,28),(65,28),(182,81),(95,2),(8,26),(38,16),(11,43)]),
  (2,1,[(232,3),(145,10),(58,96),(349,57),(262,81),(175,80),(88,93),(205,26),(118,101),(31,63),(148,4),(61,41),(265,81),(178,80),(91,78),(4,76),(208,33),(121,103),(34,35),(151,52),(64,69),(181,57),(94,99),(7,87),(37,86),(10,4)]),
  (2,2,[(261,108),(174,66),(87,1),(0,43),(291,57),(204,51),(117,1),(30,88),(234,104),(147,58),(60,30),(177,37),(90,108),(3,39),(207,104),(120,106),(33,53),(63,24),(180,28),(93,108),(6,94),(36,84),(9,99)])]
theorem fast12_22_eq : flattenGrouped fast12_22=encode flat12_22 := by rfl

def fast12 : Fin 3 → Fin 3 → List FastBlock :=
  ![![fast12_00, fast12_01, fast12_02], ![fast12_10, fast12_11, fast12_12], ![fast12_20, fast12_21, fast12_22]]
end CycleQ2SegreModularFastActions
#print axioms CycleQ2SegreModularFastActions.fast12_22_eq
end


/- Component: continuation_3/SegreModularFastActions20.lean -/
section
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
set_option Elab.async false
namespace CycleQ2SegreModularFastActions
open CycleQ2SparseModularFastDot CycleQ2SegreModularDetectorExpressions

def fast20_00 : List FastBlock := [
  (0,0,[(261,5),(174,39),(87,63),(291,10),(204,14),(117,18),(30,38),(234,31),(147,25),(60,97),(264,10),(177,55),(90,75),(3,38),(207,77),(120,84),(33,7),(150,104),(63,35),(180,51),(93,33),(6,82),(123,101),(36,22),(66,57),(96,38),(9,44),(39,12),(12,108)]),
  (0,1,[(290,107),(203,72),(116,60),(233,80),(146,27),(59,90),(176,54),(89,70),(206,101),(119,34),(32,26),(149,20),(62,15),(179,72),(92,41),(5,93),(122,26),(35,34),(65,108),(95,106),(8,94),(38,49),(11,57)]),
  (0,2,[(232,103),(145,86),(58,23),(262,104),(175,12),(88,36),(1,5),(205,97),(118,29),(31,8),(148,65),(61,19),(178,108),(91,50),(4,30),(121,42),(34,53),(64,1),(94,95),(7,7),(37,92),(10,82)]),
  (1,0,[(261,106),(174,9),(87,95),(0,4),(204,97),(117,10),(30,50),(234,2),(147,40),(60,90),(177,5),(90,102),(3,71),(207,1),(120,88),(33,88),(150,39),(63,62),(93,6),(6,46),(123,76),(36,28),(66,56),(9,86)]),
  (1,1,[(290,107),(203,58),(116,97),(29,50),(233,8),(146,107),(59,29),(176,4),(89,13),(2,50),(206,66),(119,84),(32,14),(149,66),(62,80),(92,103),(5,33),(122,2),(35,26),(65,99),(8,36)]),
  (1,2,[(232,107),(145,59),(58,85),(175,8),(88,53),(205,107),(118,63),(31,61),(148,74),(61,27),(91,1),(4,85),(121,66),(34,6),(64,106),(7,32)]),
  (2,0,[(261,105),(174,41),(87,95),(0,4),(204,101),(117,11),(30,21),(60,33),(177,46),(90,52),(3,42),(120,74),(33,59),(63,11),(93,8),(6,74),(36,28),(9,86)]),
  (2,1,[(203,101),(116,63),(29,50),(146,97),(59,4),(176,101),(89,63),(2,50),(119,57),(32,9),(62,75),(92,69),(5,5),(35,83),(8,8)]),
  (2,2,[(145,103),(58,87),(88,51),(1,81),(118,97),(31,9),(61,77),(91,103),(4,59),(34,63),(7,89)])]
theorem fast20_00_eq : flattenGrouped fast20_00=encode flat20_00 := by rfl

def fast20_01 : List FastBlock := [
  (0,0,[(435,8),(348,78),(261,52),(174,65),(87,91),(0,46),(378,24),(291,58),(204,58),(117,102),(30,106),(321,69),(234,49),(147,27),(60,94),(351,80),(264,92),(177,86),(90,9),(3,99),(294,107),(207,47),(120,34),(33,79),(237,54),(150,28),(63,9),(267,53),(180,37),(93,79),(6,68),(210,30),(123,74),(36,66),(153,26),(66,60),(183,70),(96,22),(9,54),(126,21),(39,21),(69,85),(99,72),(12,100),(42,94),(15,80)]),
  (0,1,[(377,24),(290,88),(203,89),(116,5),(29,68),(320,64),(233,55),(146,25),(59,76),(350,24),(263,58),(176,103),(89,107),(2,68),(293,23),(206,77),(119,65),(32,63),(236,23),(149,95),(62,94),(266,68),(179,70),(92,83),(5,96),(209,56),(122,56),(35,27),(152,74),(65,32),(182,3),(95,62),(8,35),(125,56),(38,50),(68,1),(98,30),(11,61),(41,65),(14,42)]),
  (0,2,[(319,32),(232,65),(145,49),(58,0),(262,67),(175,47),(88,55),(1,5),(292,64),(205,43),(118,20),(31,71),(235,57),(148,88),(61,62),(265,32),(178,45),(91,8),(4,7),(208,7),(121,80),(34,80),(151,28),(64,15),(181,22),(94,101),(7,10),(124,3),(37,16),(67,57),(97,37),(10,31),(40,67),(13,75)]),
  (1,0,[(261,5),(174,39),(87,63),(291,10),(204,14),(117,18),(30,38),(234,31),(147,25),(60,97),(264,10),(177,55),(90,75),(3,38),(207,77),(120,84),(33,7),(150,104),(63,35),(180,51),(93,33),(6,82),(123,101),(36,22),(66,57),(96,38),(9,44),(39,12),(12,108)]),
  (1,1,[(290,107),(203,72),(116,60),(233,80),(146,27),(59,90),(176,54),(89,70),(206,101),(119,34),(32,26),(149,20),(62,15),(179,72),(92,41),(5,93),(122,26),(35,34),(65,108),(95,106),(8,94),(38,49),(11,57)]),
  (1,2,[(232,103),(145,86),(58,23),(262,104),(175,12),(88,36),(1,5),(205,97),(118,29),(31,8),(148,65),(61,19),(178,108),(91,50),(4,30),(121,42),(34,53),(64,1),(94,95),(7,7),(37,92),(10,82)]),
  (2,0,[(261,106),(174,9),(87,95),(0,4),(204,97),(117,10),(30,50),(234,2),(147,40),(60,90),(177,5),(90,102),(3,71),(207,1),(120,88),(33,88),(150,39),(63,62),(93,6),(6,46),(123,76),(36,28),(66,56),(9,86)]),
  (2,1,[(290,107),(203,58),(116,97),(29,50),(233,8),(146,107),(59,29),(176,4),(89,13),(2,50),(206,66),(119,84),(32,14),(149,66),(62,80),(92,103),(5,33),(122,2),(35,26),(65,99),(8,36)]),
  (2,2,[(232,107),(145,59),(58,85),(175,8),(88,53),(205,107),(118,63),(31,61),(148,74),(61,27),(91,1),(4,85),(121,66),(34,6),(64,106),(7,32)])]
theorem fast20_01_eq : flattenGrouped fast20_01=encode flat20_01 := by rfl

def fast20_02 : List FastBlock := [
  (0,0,[(348,68),(261,31),(174,95),(87,28),(0,46),(378,44),(291,11),(204,96),(117,7),(30,68),(408,93),(321,25),(234,30),(147,16),(60,106),(351,17),(264,96),(177,69),(90,107),(3,61),(381,101),(294,11),(207,89),(120,34),(33,72),(324,32),(237,15),(150,64),(63,65),(267,81),(180,37),(93,56),(6,95),(297,6),(210,23),(123,14),(36,53),(240,0),(153,31),(66,101),(183,74),(96,33),(9,69),(213,19),(126,45),(39,92),(156,17),(69,41),(99,7),(12,66),(129,96),(42,59),(72,65),(15,33)]),
  (0,1,[(464,4),(377,81),(290,6),(203,105),(116,43),(29,68),(407,97),(320,1),(233,4),(146,108),(59,22),(350,65),(263,18),(176,101),(89,89),(2,68),(380,63),(293,20),(206,3),(119,78),(32,37),(323,102),(236,77),(149,31),(62,27),(266,57),(179,30),(92,77),(5,22),(296,89),(209,58),(122,10),(35,95),(239,86),(152,58),(65,40),(182,8),(95,39),(8,5),(212,29),(125,64),(38,10),(155,29),(68,58),(98,69),(11,75),(128,12),(41,2),(71,49),(14,73)]),
  (0,2,[(406,8),(319,56),(232,66),(145,63),(58,86),(349,85),(262,35),(175,104),(88,71),(379,8),(292,5),(205,102),(118,93),(31,63),(322,102),(235,108),(148,7),(61,95),(265,38),(178,85),(91,26),(4,86),(295,17),(208,82),(121,34),(34,20),(238,72),(151,95),(64,36),(181,27),(94,70),(7,105),(211,92),(124,32),(37,19),(154,97),(67,28),(97,27),(10,88),(127,79),(40,45),(70,41),(13,65)]),
  (1,0,[(435,8),(348,78),(261,52),(174,65),(87,91),(0,46),(378,24),(291,58),(204,58),(117,102),(30,106),(321,69),(234,49),(147,27),(60,94),(351,80),(264,92),(177,86),(90,9),(3,99),(294,107),(207,47),(120,34),(33,79),(237,54),(150,28),(63,9),(267,53),(180,37),(93,79),(6,68),(210,30),(123,74),(36,66),(153,26),(66,60),(183,70),(96,22),(9,54),(126,21),(39,21),(69,85),(99,72),(12,100),(42,94),(15,80)]),
  (1,1,[(377,24),(290,88),(203,89),(116,5),(29,68),(320,64),(233,55),(146,25),(59,76),(350,24),(263,58),(176,103),(89,107),(2,68),(293,23),(206,77),(119,65),(32,63),(236,23),(149,95),(62,94),(266,68),(179,70),(92,83),(5,96),(209,56),(122,56),(35,27),(152,74),(65,32),(182,3),(95,62),(8,35),(125,56),(38,50),(68,1),(98,30),(11,61),(41,65),(14,42)]),
  (1,2,[(319,32),(232,65),(145,49),(58,0),(262,67),(175,47),(88,55),(1,5),(292,64),(205,43),(118,20),(31,71),(235,57),(148,88),(61,62),(265,32),(178,45),(91,8),(4,7),(208,7),(121,80),(34,80),(151,28),(64,15),(181,22),(94,101),(7,10),(124,3),(37,16),(67,57),(97,37),(10,31),(40,67),(13,75)]),
  (2,0,[(261,5),(174,39),(87,63),(291,10),(204,14),(117,18),(30,38),(234,31),(147,25),(60,97),(264,10),(177,55),(90,75),(3,38),(207,77),(120,84),(33,7),(150,104),(63,35),(180,51),(93,33),(6,82),(123,101),(36,22),(66,57),(96,38),(9,44),(39,12),(12,108)]),
  (2,1,[(290,107),(203,72),(116,60),(233,80),(146,27),(59,90),(176,54),(89,70),(206,101),(119,34),(32,26),(149,20),(62,15),(179,72),(92,41),(5,93),(122,26),(35,34),(65,108),(95,106),(8,94),(38,49),(11,57)]),
  (2,2,[(232,103),(145,86),(58,23),(262,104),(175,12),(88,36),(1,5),(205,97),(118,29),(31,8),(148,65),(61,19),(178,108),(91,50),(4,30),(121,42),(34,53),(64,1),(94,95),(7,7),(37,92),(10,82)])]
theorem fast20_02_eq : flattenGrouped fast20_02=encode flat20_02 := by rfl

def fast20_10 : List FastBlock := [
  (0,0,[(319,6),(232,49),(145,4),(58,82),(349,5),(262,52),(175,44),(88,34),(1,51),(292,17),(205,11),(118,12),(31,33),(235,76),(148,74),(61,51),(265,54),(178,31),(91,14),(4,35),(208,108),(121,18),(34,77),(151,31),(64,61),(181,90),(94,104),(7,15),(124,0),(37,108),(67,50),(97,1),(10,21),(40,11),(13,90)]),
  (0,1,[(261,11),(174,62),(87,40),(291,15),(204,2),(117,91),(30,33),(234,49),(147,19),(60,66),(264,15),(177,87),(90,20),(3,33),(207,90),(120,5),(33,78),(150,106),(63,72),(180,52),(93,91),(6,52),(123,73),(36,71),(66,73),(96,52),(9,37),(39,56),(12,26)]),
  (0,2,[(290,107),(203,72),(116,60),(233,80),(146,27),(59,90),(176,54),(89,70),(206,101),(119,34),(32,26),(149,20),(62,15),(179,72),(92,41),(5,93),(122,26),(35,34),(65,108),(95,106),(8,94),(38,49),(11,57)]),
  (1,0,[(319,2),(232,95),(145,59),(58,104),(262,103),(175,35),(88,85),(292,2),(205,83),(118,49),(31,99),(235,80),(148,83),(61,11),(178,80),(91,34),(4,104),(208,86),(121,42),(34,49),(151,90),(64,26),(94,4),(7,14),(124,107),(37,57),(67,10),(10,75)]),
  (1,1,[(261,108),(174,59),(87,10),(0,4),(204,89),(117,66),(30,50),(234,6),(147,27),(60,53),(177,32),(90,22),(3,71),(207,3),(120,24),(33,51),(150,8),(63,29),(93,8),(6,70),(123,10),(36,99),(66,59),(9,54)]),
  (1,2,[(290,107),(203,58),(116,97),(29,50),(233,8),(146,107),(59,29),(176,4),(89,13),(2,50),(206,66),(119,84),(32,14),(149,66),(62,80),(92,103),(5,33),(122,2),(35,26),(65,99),(8,36)]),
  (2,0,[(232,6),(145,48),(58,59),(175,64),(88,47),(1,85),(205,12),(118,101),(31,98),(148,64),(61,94),(178,6),(91,47),(4,92),(121,92),(34,74),(64,80),(94,40),(7,108),(37,28),(10,103)]),
  (2,1,[(261,105),(174,47),(87,8),(0,4),(204,101),(117,69),(30,49),(147,18),(60,46),(177,46),(90,33),(3,70),(120,92),(33,100),(63,89),(93,14),(6,15),(36,94),(9,106)]),
  (2,2,[(203,101),(116,63),(29,50),(146,97),(59,4),(176,101),(89,63),(2,50),(119,57),(32,9),(62,75),(92,69),(5,5),(35,83),(8,8)])]
theorem fast20_10_eq : flattenGrouped fast20_10=encode flat20_10 := by rfl

def fast20_11 : List FastBlock := [
  (0,0,[(406,77),(319,87),(232,69),(145,42),(58,0),(349,10),(262,70),(175,92),(88,11),(1,51),(379,45),(292,85),(205,1),(118,78),(31,87),(322,63),(235,23),(148,100),(61,60),(352,77),(265,81),(178,61),(91,40),(4,62),(295,2),(208,101),(121,80),(34,100),(238,102),(151,108),(64,48),(268,53),(181,98),(94,92),(7,6),(211,97),(124,3),(37,90),(154,101),(67,14),(184,35),(97,69),(10,14),(127,104),(40,25),(70,70),(100,56),(13,44),(43,65),(16,77)]),
  (0,1,[(435,8),(348,46),(261,96),(174,16),(87,91),(0,46),(378,24),(291,100),(204,11),(117,47),(30,101),(321,82),(234,50),(147,67),(60,23),(351,80),(264,77),(177,60),(90,1),(3,94),(294,11),(207,68),(120,6),(33,1),(237,99),(150,78),(63,85),(267,21),(180,73),(93,56),(6,61),(210,1),(123,2),(36,85),(153,104),(66,29),(183,48),(96,82),(9,44),(126,90),(39,83),(69,70),(99,35),(12,69),(42,61),(15,5)]),
  (0,2,[(377,24),(290,88),(203,89),(116,5),(29,68),(320,64),(233,55),(146,25),(59,76),(350,24),(263,58),(176,103),(89,107),(2,68),(293,23),(206,77),(119,65),(32,63),(236,23),(149,95),(62,94),(266,68),(179,70),(92,83),(5,96),(209,56),(122,56),(35,27),(152,74),(65,32),(182,3),(95,62),(8,35),(125,56),(38,50),(68,1),(98,30),(11,61),(41,65),(14,42)]),
  (1,0,[(319,6),(232,49),(145,4),(58,82),(349,5),(262,52),(175,44),(88,34),(1,51),(292,17),(205,11),(118,12),(31,33),(235,76),(148,74),(61,51),(265,54),(178,31),(91,14),(4,35),(208,108),(121,18),(34,77),(151,31),(64,61),(181,90),(94,104),(7,15),(124,0),(37,108),(67,50),(97,1),(10,21),(40,11),(13,90)]),
  (1,1,[(261,11),(174,62),(87,40),(291,15),(204,2),(117,91),(30,33),(234,49),(147,19),(60,66),(264,15),(177,87),(90,20),(3,33),(207,90),(120,5),(33,78),(150,106),(63,72),(180,52),(93,91),(6,52),(123,73),(36,71),(66,73),(96,52),(9,37),(39,56),(12,26)]),
  (1,2,[(290,107),(203,72),(116,60),(233,80),(146,27),(59,90),(176,54),(89,70),(206,101),(119,34),(32,26),(149,20),(62,15),(179,72),(92,41),(5,93),(122,26),(35,34),(65,108),(95,106),(8,94),(38,49),(11,57)]),
  (2,0,[(319,2),(232,95),(145,59),(58,104),(262,103),(175,35),(88,85),(292,2),(205,83),(118,49),(31,99),(235,80),(148,83),(61,11),(178,80),(91,34),(4,104),(208,86),(121,42),(34,49),(151,90),(64,26),(94,4),(7,14),(124,107),(37,57),(67,10),(10,75)]),
  (2,1,[(261,108),(174,59),(87,10),(0,4),(204,89),(117,66),(30,50),(234,6),(147,27),(60,53),(177,32),(90,22),(3,71),(207,3),(120,24),(33,51),(150,8),(63,29),(93,8),(6,70),(123,10),(36,99),(66,59),(9,54)]),
  (2,2,[(290,107),(203,58),(116,97),(29,50),(233,8),(146,107),(59,29),(176,4),(89,13),(2,50),(206,66),(119,84),(32,14),(149,66),(62,80),(92,103),(5,33),(122,2),(35,26),(65,99),(8,36)])]
theorem fast20_11_eq : flattenGrouped fast20_11=encode flat20_11 := by rfl

def fast20_12 : List FastBlock := [
  (0,0,[(493,101),(406,91),(319,91),(232,87),(145,77),(58,27),(436,16),(349,13),(262,78),(175,33),(88,6),(466,101),(379,57),(292,23),(205,15),(118,8),(31,54),(409,45),(322,94),(235,75),(148,44),(61,38),(352,49),(265,107),(178,15),(91,51),(4,27),(382,29),(295,44),(208,94),(121,78),(34,17),(325,7),(238,23),(151,40),(64,16),(268,65),(181,16),(94,14),(7,94),(298,33),(211,32),(124,95),(37,73),(241,7),(154,75),(67,103),(184,4),(97,6),(10,68),(214,14),(127,24),(40,17),(157,29),(70,11),(100,22),(13,79),(130,100),(43,3),(73,45),(16,74)]),
  (0,1,[(435,101),(348,12),(261,74),(174,32),(87,51),(0,46),(378,68),(291,85),(204,101),(117,45),(30,68),(408,77),(321,73),(234,80),(147,78),(60,66),(351,48),(264,62),(177,67),(90,50),(3,61),(381,93),(294,77),(207,11),(120,24),(33,32),(324,22),(237,43),(150,23),(63,59),(267,80),(180,75),(93,103),(6,9),(297,98),(210,23),(123,19),(36,37),(240,54),(153,13),(66,46),(183,59),(96,44),(9,73),(213,36),(126,95),(39,94),(156,59),(69,77),(99,48),(12,87),(129,17),(42,58),(72,24),(15,77)]),
  (0,2,[(464,4),(377,81),(290,6),(203,105),(116,43),(29,68),(407,97),(320,1),(233,4),(146,108),(59,22),(350,65),(263,18),(176,101),(89,89),(2,68),(380,63),(293,20),(206,3),(119,78),(32,37),(323,102),(236,77),(149,31),(62,27),(266,57),(179,30),(92,77),(5,22),(296,89),(209,58),(122,10),(35,95),(239,86),(152,58),(65,40),(182,8),(95,39),(8,5),(212,29),(125,64),(38,10),(155,29),(68,58),(98,69),(11,75),(128,12),(41,2),(71,49),(14,73)]),
  (1,0,[(406,77),(319,87),(232,69),(145,42),(58,0),(349,10),(262,70),(175,92),(88,11),(1,51),(379,45),(292,85),(205,1),(118,78),(31,87),(322,63),(235,23),(148,100),(61,60),(352,77),(265,81),(178,61),(91,40),(4,62),(295,2),(208,101),(121,80),(34,100),(238,102),(151,108),(64,48),(268,53),(181,98),(94,92),(7,6),(211,97),(124,3),(37,90),(154,101),(67,14),(184,35),(97,69),(10,14),(127,104),(40,25),(70,70),(100,56),(13,44),(43,65),(16,77)]),
  (1,1,[(435,8),(348,46),(261,96),(174,16),(87,91),(0,46),(378,24),(291,100),(204,11),(117,47),(30,101),(321,82),(234,50),(147,67),(60,23),(351,80),(264,77),(177,60),(90,1),(3,94),(294,11),(207,68),(120,6),(33,1),(237,99),(150,78),(63,85),(267,21),(180,73),(93,56),(6,61),(210,1),(123,2),(36,85),(153,104),(66,29),(183,48),(96,82),(9,44),(126,90),(39,83),(69,70),(99,35),(12,69),(42,61),(15,5)]),
  (1,2,[(377,24),(290,88),(203,89),(116,5),(29,68),(320,64),(233,55),(146,25),(59,76),(350,24),(263,58),(176,103),(89,107),(2,68),(293,23),(206,77),(119,65),(32,63),(236,23),(149,95),(62,94),(266,68),(179,70),(92,83),(5,96),(209,56),(122,56),(35,27),(152,74),(65,32),(182,3),(95,62),(8,35),(125,56),(38,50),(68,1),(98,30),(11,61),(41,65),(14,42)]),
  (2,0,[(319,6),(232,49),(145,4),(58,82),(349,5),(262,52),(175,44),(88,34),(1,51),(292,17),(205,11),(118,12),(31,33),(235,76),(148,74),(61,51),(265,54),(178,31),(91,14),(4,35),(208,108),(121,18),(34,77),(151,31),(64,61),(181,90),(94,104),(7,15),(124,0),(37,108),(67,50),(97,1),(10,21),(40,11),(13,90)]),
  (2,1,[(261,11),(174,62),(87,40),(291,15),(204,2),(117,91),(30,33),(234,49),(147,19),(60,66),(264,15),(177,87),(90,20),(3,33),(207,90),(120,5),(33,78),(150,106),(63,72),(180,52),(93,91),(6,52),(123,73),(36,71),(66,73),(96,52),(9,37),(39,56),(12,26)]),
  (2,2,[(290,107),(203,72),(116,60),(233,80),(146,27),(59,90),(176,54),(89,70),(206,101),(119,34),(32,26),(149,20),(62,15),(179,72),(92,41),(5,93),(122,26),(35,34),(65,108),(95,106),(8,94),(38,49),(11,57)])]
theorem fast20_12_eq : flattenGrouped fast20_12=encode flat20_12 := by rfl

def fast20_20 : List FastBlock := [
  (0,0,[(377,2),(290,82),(203,64),(116,67),(320,31),(233,63),(146,60),(59,46),(263,84),(176,105),(89,79),(293,51),(206,70),(119,29),(32,69),(236,12),(149,65),(62,45),(266,37),(179,101),(92,26),(5,33),(209,74),(122,26),(35,0),(152,90),(65,102),(182,90),(95,74),(8,82),(125,49),(38,89),(68,27),(98,62),(11,21),(41,34),(14,28)]),
  (0,1,[(319,8),(232,86),(145,53),(58,82),(349,5),(262,81),(175,17),(88,53),(1,51),(292,19),(205,103),(118,100),(31,33),(235,4),(148,13),(61,44),(265,54),(178,66),(91,38),(4,35),(208,44),(121,52),(34,67),(151,94),(64,12),(181,18),(94,64),(7,31),(124,86),(37,89),(67,2),(97,4),(10,36),(40,14),(13,33)]),
  (0,2,[(261,11),(174,62),(87,40),(291,15),(204,2),(117,91),(30,33),(234,49),(147,19),(60,66),(264,15),(177,87),(90,20),(3,33),(207,90),(120,5),(33,78),(150,106),(63,72),(180,52),(93,91),(6,52),(123,73),(36,71),(66,73),(96,52),(9,37),(39,56),(12,26)]),
  (1,0,[(377,2),(290,96),(203,15),(116,2),(29,74),(320,103),(233,91),(146,28),(59,6),(263,97),(176,8),(89,10),(2,74),(293,86),(206,14),(119,85),(32,86),(236,23),(149,29),(62,15),(179,72),(92,15),(5,90),(209,105),(122,91),(35,62),(152,6),(65,5),(95,103),(8,61),(125,66),(38,59),(68,106),(11,98)]),
  (1,1,[(319,4),(232,37),(145,71),(58,54),(262,95),(175,37),(88,56),(292,4),(205,21),(118,48),(31,108),(235,6),(148,1),(61,77),(178,10),(91,50),(4,54),(208,20),(121,73),(34,2),(151,22),(64,29),(94,20),(7,90),(124,105),(37,104),(67,20),(10,39)]),
  (1,2,[(261,108),(174,59),(87,10),(0,4),(204,89),(117,66),(30,50),(234,6),(147,27),(60,53),(177,32),(90,22),(3,71),(207,3),(120,24),(33,51),(150,8),(63,29),(93,8),(6,70),(123,10),(36,99),(66,59),(9,54)]),
  (2,0,[(290,8),(203,8),(116,4),(29,74),(233,20),(146,94),(59,78),(263,8),(176,20),(89,0),(2,74),(206,14),(119,16),(32,35),(149,17),(62,16),(179,103),(92,65),(5,66),(122,94),(35,5),(65,103),(95,89),(8,94),(38,6),(11,46)]),
  (2,1,[(232,14),(145,94),(58,9),(175,76),(88,43),(1,85),(205,28),(118,84),(31,107),(148,19),(61,81),(178,14),(91,18),(4,42),(121,75),(34,60),(64,31),(94,80),(7,103),(37,46),(10,95)]),
  (2,2,[(261,105),(174,47),(87,8),(0,4),(204,101),(117,69),(30,49),(147,18),(60,46),(177,46),(90,33),(3,70),(120,92),(33,100),(63,89),(93,14),(6,15),(36,94),(9,106)])]
theorem fast20_20_eq : flattenGrouped fast20_20=encode flat20_20 := by rfl

def fast20_21 : List FastBlock := [
  (0,0,[(464,85),(377,26),(290,2),(203,9),(116,92),(29,105),(407,21),(320,52),(233,11),(146,65),(59,75),(437,85),(350,101),(263,63),(176,3),(89,10),(2,105),(380,91),(293,17),(206,1),(119,4),(32,50),(323,104),(236,90),(149,0),(62,3),(353,70),(266,73),(179,11),(92,2),(5,84),(296,90),(209,65),(122,12),(35,13),(239,84),(152,74),(65,66),(269,61),(182,90),(95,78),(8,37),(212,45),(125,40),(38,58),(155,96),(68,57),(185,69),(98,1),(11,55),(128,9),(41,72),(71,77),(101,76),(14,87),(44,32),(17,78)]),
  (0,1,[(406,53),(319,108),(232,89),(145,37),(58,41),(349,55),(262,15),(175,67),(88,44),(1,51),(379,106),(292,48),(205,27),(118,75),(31,60),(322,85),(235,0),(148,10),(61,30),(352,53),(265,0),(178,81),(91,57),(4,103),(295,20),(208,63),(121,41),(34,50),(238,23),(151,66),(64,36),(268,94),(181,63),(94,86),(7,19),(211,38),(124,103),(37,28),(154,80),(67,41),(184,32),(97,6),(10,88),(127,18),(40,23),(70,4),(100,26),(13,92),(43,67),(16,35)]),
  (0,2,[(435,8),(348,46),(261,96),(174,16),(87,91),(0,46),(378,24),(291,100),(204,11),(117,47),(30,101),(321,82),(234,50),(147,67),(60,23),(351,80),(264,77),(177,60),(90,1),(3,94),(294,11),(207,68),(120,6),(33,1),(237,99),(150,78),(63,85),(267,21),(180,73),(93,56),(6,61),(210,1),(123,2),(36,85),(153,104),(66,29),(183,48),(96,82),(9,44),(126,90),(39,83),(69,70),(99,35),(12,69),(42,61),(15,5)]),
  (1,0,[(377,2),(290,82),(203,64),(116,67),(320,31),(233,63),(146,60),(59,46),(263,84),(176,105),(89,79),(293,51),(206,70),(119,29),(32,69),(236,12),(149,65),(62,45),(266,37),(179,101),(92,26),(5,33),(209,74),(122,26),(35,0),(152,90),(65,102),(182,90),(95,74),(8,82),(125,49),(38,89),(68,27),(98,62),(11,21),(41,34),(14,28)]),
  (1,1,[(319,8),(232,86),(145,53),(58,82),(349,5),(262,81),(175,17),(88,53),(1,51),(292,19),(205,103),(118,100),(31,33),(235,4),(148,13),(61,44),(265,54),(178,66),(91,38),(4,35),(208,44),(121,52),(34,67),(151,94),(64,12),(181,18),(94,64),(7,31),(124,86),(37,89),(67,2),(97,4),(10,36),(40,14),(13,33)]),
  (1,2,[(261,11),(174,62),(87,40),(291,15),(204,2),(117,91),(30,33),(234,49),(147,19),(60,66),(264,15),(177,87),(90,20),(3,33),(207,90),(120,5),(33,78),(150,106),(63,72),(180,52),(93,91),(6,52),(123,73),(36,71),(66,73),(96,52),(9,37),(39,56),(12,26)]),
  (2,0,[(377,2),(290,96),(203,15),(116,2),(29,74),(320,103),(233,91),(146,28),(59,6),(263,97),(176,8),(89,10),(2,74),(293,86),(206,14),(119,85),(32,86),(236,23),(149,29),(62,15),(179,72),(92,15),(5,90),(209,105),(122,91),(35,62),(152,6),(65,5),(95,103),(8,61),(125,66),(38,59),(68,106),(11,98)]),
  (2,1,[(319,4),(232,37),(145,71),(58,54),(262,95),(175,37),(88,56),(292,4),(205,21),(118,48),(31,108),(235,6),(148,1),(61,77),(178,10),(91,50),(4,54),(208,20),(121,73),(34,2),(151,22),(64,29),(94,20),(7,90),(124,105),(37,104),(67,20),(10,39)]),
  (2,2,[(261,108),(174,59),(87,10),(0,4),(204,89),(117,66),(30,50),(234,6),(147,27),(60,53),(177,32),(90,22),(3,71),(207,3),(120,24),(33,51),(150,8),(63,29),(93,8),(6,70),(123,10),(36,99),(66,59),(9,54)])]
theorem fast20_21_eq : flattenGrouped fast20_21=encode flat20_21 := by rfl

def fast20_22 : List FastBlock := [
  (0,0,[(551,105),(464,47),(377,79),(290,87),(203,47),(116,0),(29,105),(494,8),(407,79),(320,22),(233,24),(146,12),(59,91),(437,56),(350,99),(263,35),(176,92),(89,33),(2,105),(467,69),(380,26),(293,54),(206,3),(119,83),(32,90),(410,93),(323,39),(236,55),(149,91),(62,27),(353,24),(266,22),(179,43),(92,11),(5,5),(383,28),(296,14),(209,62),(122,106),(35,97),(326,30),(239,54),(152,104),(65,5),(269,43),(182,59),(95,38),(8,14),(299,74),(212,45),(125,40),(38,71),(242,55),(155,104),(68,5),(185,57),(98,92),(11,58),(215,73),(128,27),(41,101),(158,24),(71,101),(101,84),(14,15),(131,69),(44,102),(74,91),(17,11)]),
  (0,1,[(493,97),(406,10),(319,85),(232,91),(145,34),(58,68),(436,28),(349,12),(262,74),(175,34),(88,93),(466,97),(379,20),(292,108),(205,27),(118,94),(31,27),(409,103),(322,73),(235,68),(148,76),(61,88),(352,100),(265,12),(178,101),(91,44),(4,68),(382,75),(295,76),(208,61),(121,32),(34,67),(325,34),(238,106),(151,108),(64,3),(268,31),(181,37),(94,6),(7,72),(298,53),(211,75),(124,46),(37,82),(241,1),(154,62),(67,53),(184,76),(97,18),(10,63),(214,94),(127,0),(40,41),(157,97),(70,60),(100,13),(13,4),(130,88),(43,37),(73,105),(16,1)]),
  (0,2,[(435,101),(348,12),(261,74),(174,32),(87,51),(0,46),(378,68),(291,85),(204,101),(117,45),(30,68),(408,77),(321,73),(234,80),(147,78),(60,66),(351,48),(264,62),(177,67),(90,50),(3,61),(381,93),(294,77),(207,11),(120,24),(33,32),(324,22),(237,43),(150,23),(63,59),(267,80),(180,75),(93,103),(6,9),(297,98),(210,23),(123,19),(36,37),(240,54),(153,13),(66,46),(183,59),(96,44),(9,73),(213,36),(126,95),(39,94),(156,59),(69,77),(99,48),(12,87),(129,17),(42,58),(72,24),(15,77)]),
  (1,0,[(464,85),(377,26),(290,2),(203,9),(116,92),(29,105),(407,21),(320,52),(233,11),(146,65),(59,75),(437,85),(350,101),(263,63),(176,3),(89,10),(2,105),(380,91),(293,17),(206,1),(119,4),(32,50),(323,104),(236,90),(149,0),(62,3),(353,70),(266,73),(179,11),(92,2),(5,84),(296,90),(209,65),(122,12),(35,13),(239,84),(152,74),(65,66),(269,61),(182,90),(95,78),(8,37),(212,45),(125,40),(38,58),(155,96),(68,57),(185,69),(98,1),(11,55),(128,9),(41,72),(71,77),(101,76),(14,87),(44,32),(17,78)]),
  (1,1,[(406,53),(319,108),(232,89),(145,37),(58,41),(349,55),(262,15),(175,67),(88,44),(1,51),(379,106),(292,48),(205,27),(118,75),(31,60),(322,85),(235,0),(148,10),(61,30),(352,53),(265,0),(178,81),(91,57),(4,103),(295,20),(208,63),(121,41),(34,50),(238,23),(151,66),(64,36),(268,94),(181,63),(94,86),(7,19),(211,38),(124,103),(37,28),(154,80),(67,41),(184,32),(97,6),(10,88),(127,18),(40,23),(70,4),(100,26),(13,92),(43,67),(16,35)]),
  (1,2,[(435,8),(348,46),(261,96),(174,16),(87,91),(0,46),(378,24),(291,100),(204,11),(117,47),(30,101),(321,82),(234,50),(147,67),(60,23),(351,80),(264,77),(177,60),(90,1),(3,94),(294,11),(207,68),(120,6),(33,1),(237,99),(150,78),(63,85),(267,21),(180,73),(93,56),(6,61),(210,1),(123,2),(36,85),(153,104),(66,29),(183,48),(96,82),(9,44),(126,90),(39,83),(69,70),(99,35),(12,69),(42,61),(15,5)]),
  (2,0,[(377,2),(290,82),(203,64),(116,67),(320,31),(233,63),(146,60),(59,46),(263,84),(176,105),(89,79),(293,51),(206,70),(119,29),(32,69),(236,12),(149,65),(62,45),(266,37),(179,101),(92,26),(5,33),(209,74),(122,26),(35,0),(152,90),(65,102),(182,90),(95,74),(8,82),(125,49),(38,89),(68,27),(98,62),(11,21),(41,34),(14,28)]),
  (2,1,[(319,8),(232,86),(145,53),(58,82),(349,5),(262,81),(175,17),(88,53),(1,51),(292,19),(205,103),(118,100),(31,33),(235,4),(148,13),(61,44),(265,54),(178,66),(91,38),(4,35),(208,44),(121,52),(34,67),(151,94),(64,12),(181,18),(94,64),(7,31),(124,86),(37,89),(67,2),(97,4),(10,36),(40,14),(13,33)]),
  (2,2,[(261,11),(174,62),(87,40),(291,15),(204,2),(117,91),(30,33),(234,49),(147,19),(60,66),(264,15),(177,87),(90,20),(3,33),(207,90),(120,5),(33,78),(150,106),(63,72),(180,52),(93,91),(6,52),(123,73),(36,71),(66,73),(96,52),(9,37),(39,56),(12,26)])]
theorem fast20_22_eq : flattenGrouped fast20_22=encode flat20_22 := by rfl

def fast20 : Fin 3 → Fin 3 → List FastBlock :=
  ![![fast20_00, fast20_01, fast20_02], ![fast20_10, fast20_11, fast20_12], ![fast20_20, fast20_21, fast20_22]]
end CycleQ2SegreModularFastActions
#print axioms CycleQ2SegreModularFastActions.fast20_22_eq
end


/- Component: continuation_3/SegreModularFastActions21.lean -/
section
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
set_option Elab.async false
namespace CycleQ2SegreModularFastActions
open CycleQ2SparseModularFastDot CycleQ2SegreModularDetectorExpressions

def fast21_00 : List FastBlock := [
  (0,0,[(348,4),(261,4),(174,2),(87,37),(291,15),(204,24),(117,7),(30,38),(321,4),(234,25),(147,7),(60,53),(264,12),(177,73),(90,23),(3,38),(207,19),(120,93),(33,53),(237,106),(150,105),(63,1),(180,97),(93,46),(6,1),(123,68),(36,26),(153,99),(66,108),(96,92),(9,59),(39,62),(69,23),(12,3)]),
  (0,1,[(290,7),(203,48),(116,27),(233,22),(146,30),(59,13),(263,14),(176,67),(89,34),(206,84),(119,81),(32,26),(236,7),(149,102),(62,6),(179,102),(92,58),(5,13),(122,79),(35,60),(152,40),(65,82),(95,98),(8,61),(38,3),(68,102),(11,37)]),
  (0,2,[(319,107),(232,24),(145,5),(58,2),(262,105),(175,46),(88,36),(1,5),(205,4),(118,45),(31,8),(235,23),(148,91),(61,19),(178,48),(91,7),(4,7),(121,70),(34,91),(151,7),(64,31),(94,5),(7,33),(37,63),(67,53),(10,78)]),
  (1,0,[(261,2),(174,13),(87,43),(204,3),(117,45),(234,6),(147,7),(60,95),(177,20),(90,2),(207,4),(120,40),(33,52),(150,4),(63,4),(93,65),(123,96),(36,47),(66,16),(39,106)]),
  (1,1,[(290,105),(203,86),(116,59),(29,2),(233,103),(146,41),(59,105),(176,5),(89,65),(206,89),(119,73),(32,90),(149,57),(62,19),(92,18),(5,80),(122,9),(35,87),(65,70),(8,28),(38,53)]),
  (1,2,[(232,105),(145,84),(58,100),(175,103),(88,72),(205,103),(118,39),(31,25),(148,81),(61,22),(91,22),(121,46),(34,83),(64,93),(7,52),(37,4)]),
  (2,0,[(174,107),(87,32),(204,57),(117,28),(147,57),(60,88),(90,33),(120,79),(33,32),(63,108),(36,33)]),
  (2,1,[(146,57),(89,87),(2,39),(119,57),(32,88),(5,39),(35,108)]),
  (2,2,[(31,88),(4,88)])]
theorem fast21_00_eq : flattenGrouped fast21_00=encode flat21_00 := by rfl

def fast21_01 : List FastBlock := [
  (0,0,[(348,4),(261,26),(174,63),(87,41),(378,104),(291,56),(204,50),(117,81),(321,99),(234,83),(147,88),(60,29),(264,20),(177,76),(90,42),(294,7),(207,17),(120,101),(33,37),(237,18),(150,73),(63,1),(180,106),(93,71),(6,107),(210,30),(123,79),(36,66),(153,96),(66,87),(96,14),(9,103),(126,48),(39,9),(69,62),(12,63),(42,66)]),
  (0,1,[(290,4),(203,26),(116,86),(320,99),(233,107),(146,40),(263,33),(176,69),(89,97),(2,67),(293,99),(206,104),(119,84),(32,20),(236,48),(149,88),(62,36),(179,34),(92,103),(5,72),(209,65),(122,7),(35,84),(152,50),(65,20),(95,44),(8,28),(125,73),(38,6),(68,15),(11,86),(41,105)]),
  (0,2,[(232,2),(145,77),(262,47),(175,23),(205,28),(118,49),(31,20),(235,94),(148,32),(61,68),(178,50),(91,70),(4,20),(208,47),(121,4),(34,71),(151,3),(64,32),(94,74),(7,3),(124,88),(37,68),(67,89),(10,25),(40,10)]),
  (1,0,[(348,4),(261,4),(174,2),(87,37),(291,15),(204,24),(117,7),(30,38),(321,4),(234,25),(147,7),(60,53),(264,12),(177,73),(90,23),(3,38),(207,19),(120,93),(33,53),(237,106),(150,105),(63,1),(180,97),(93,46),(6,1),(123,68),(36,26),(153,99),(66,108),(96,92),(9,59),(39,62),(69,23),(12,3)]),
  (1,1,[(290,7),(203,48),(116,27),(233,22),(146,30),(59,13),(263,14),(176,67),(89,34),(206,84),(119,81),(32,26),(236,7),(149,102),(62,6),(179,102),(92,58),(5,13),(122,79),(35,60),(152,40),(65,82),(95,98),(8,61),(38,3),(68,102),(11,37)]),
  (1,2,[(319,107),(232,24),(145,5),(58,2),(262,105),(175,46),(88,36),(1,5),(205,4),(118,45),(31,8),(235,23),(148,91),(61,19),(178,48),(91,7),(4,7),(121,70),(34,91),(151,7),(64,31),(94,5),(7,33),(37,63),(67,53),(10,78)]),
  (2,0,[(261,2),(174,13),(87,43),(204,3),(117,45),(234,6),(147,7),(60,95),(177,20),(90,2),(207,4),(120,40),(33,52),(150,4),(63,4),(93,65),(123,96),(36,47),(66,16),(39,106)]),
  (2,1,[(290,105),(203,86),(116,59),(29,2),(233,103),(146,41),(59,105),(176,5),(89,65),(206,89),(119,73),(32,90),(149,57),(62,19),(92,18),(5,80),(122,9),(35,87),(65,70),(8,28),(38,53)]),
  (2,2,[(232,105),(145,84),(58,100),(175,103),(88,72),(205,103),(118,39),(31,25),(148,81),(61,22),(91,22),(121,46),(34,83),(64,93),(7,52),(37,4)])]
theorem fast21_01_eq : flattenGrouped fast21_01=encode flat21_01 := by rfl

def fast21_02 : List FastBlock := [
  (0,0,[(435,93),(348,15),(261,42),(174,72),(87,38),(378,61),(291,103),(204,32),(117,7),(408,69),(321,103),(234,11),(147,94),(60,106),(351,47),(264,76),(177,4),(90,62),(381,85),(294,18),(207,102),(120,71),(33,68),(324,73),(237,6),(150,10),(63,15),(267,100),(180,53),(93,62),(297,87),(210,52),(123,29),(36,19),(240,43),(153,61),(66,59),(183,63),(96,63),(9,59),(213,91),(126,7),(39,11),(156,59),(69,61),(99,90),(12,74),(129,15),(42,51),(72,99),(15,62),(45,93)]),
  (0,1,[(464,8),(377,97),(290,60),(203,91),(116,10),(29,23),(407,20),(320,41),(233,63),(146,2),(59,82),(350,45),(263,25),(176,29),(89,99),(380,103),(293,90),(206,62),(119,36),(32,85),(323,58),(236,106),(149,4),(62,27),(266,59),(179,11),(92,56),(5,48),(296,45),(209,56),(122,89),(35,0),(239,62),(152,12),(65,12),(182,85),(95,2),(8,36),(212,53),(125,85),(38,41),(155,68),(68,95),(98,4),(11,71),(128,84),(41,13),(71,15),(14,31),(44,57)]),
  (0,2,[(406,16),(319,14),(232,14),(145,77),(58,79),(349,40),(262,36),(175,48),(88,101),(379,20),(292,81),(205,105),(118,89),(31,34),(322,36),(235,71),(148,42),(61,97),(265,41),(178,97),(91,103),(295,51),(208,8),(121,87),(34,37),(238,99),(151,75),(64,22),(181,27),(94,12),(7,50),(211,39),(124,58),(37,25),(154,64),(67,40),(97,53),(10,30),(127,94),(40,89),(70,71),(13,99),(43,21)]),
  (1,0,[(348,4),(261,26),(174,63),(87,41),(378,104),(291,56),(204,50),(117,81),(321,99),(234,83),(147,88),(60,29),(264,20),(177,76),(90,42),(294,7),(207,17),(120,101),(33,37),(237,18),(150,73),(63,1),(180,106),(93,71),(6,107),(210,30),(123,79),(36,66),(153,96),(66,87),(96,14),(9,103),(126,48),(39,9),(69,62),(12,63),(42,66)]),
  (1,1,[(290,4),(203,26),(116,86),(320,99),(233,107),(146,40),(263,33),(176,69),(89,97),(2,67),(293,99),(206,104),(119,84),(32,20),(236,48),(149,88),(62,36),(179,34),(92,103),(5,72),(209,65),(122,7),(35,84),(152,50),(65,20),(95,44),(8,28),(125,73),(38,6),(68,15),(11,86),(41,105)]),
  (1,2,[(232,2),(145,77),(262,47),(175,23),(205,28),(118,49),(31,20),(235,94),(148,32),(61,68),(178,50),(91,70),(4,20),(208,47),(121,4),(34,71),(151,3),(64,32),(94,74),(7,3),(124,88),(37,68),(67,89),(10,25),(40,10)]),
  (2,0,[(348,4),(261,4),(174,2),(87,37),(291,15),(204,24),(117,7),(30,38),(321,4),(234,25),(147,7),(60,53),(264,12),(177,73),(90,23),(3,38),(207,19),(120,93),(33,53),(237,106),(150,105),(63,1),(180,97),(93,46),(6,1),(123,68),(36,26),(153,99),(66,108),(96,92),(9,59),(39,62),(69,23),(12,3)]),
  (2,1,[(290,7),(203,48),(116,27),(233,22),(146,30),(59,13),(263,14),(176,67),(89,34),(206,84),(119,81),(32,26),(236,7),(149,102),(62,6),(179,102),(92,58),(5,13),(122,79),(35,60),(152,40),(65,82),(95,98),(8,61),(38,3),(68,102),(11,37)]),
  (2,2,[(319,107),(232,24),(145,5),(58,2),(262,105),(175,46),(88,36),(1,5),(205,4),(118,45),(31,8),(235,23),(148,91),(61,19),(178,48),(91,7),(4,7),(121,70),(34,91),(151,7),(64,31),(94,5),(7,33),(37,63),(67,53),(10,78)])]
theorem fast21_02_eq : flattenGrouped fast21_02=encode flat21_02 := by rfl

def fast21_10 : List FastBlock := [
  (0,0,[(406,2),(319,21),(232,0),(145,49),(58,64),(349,6),(262,20),(175,14),(88,55),(1,51),(292,0),(205,37),(118,88),(31,33),(322,20),(235,16),(148,70),(61,12),(265,15),(178,13),(91,78),(4,62),(208,14),(121,30),(34,8),(238,98),(151,74),(64,2),(181,46),(94,0),(7,88),(124,62),(37,81),(154,69),(67,40),(97,34),(10,97),(40,39),(70,5),(13,67)]),
  (0,1,[(348,6),(261,89),(174,106),(87,35),(291,19),(204,87),(117,80),(30,33),(321,6),(234,106),(147,66),(60,43),(264,102),(177,45),(90,77),(3,33),(207,76),(120,41),(33,38),(237,83),(150,53),(63,0),(180,42),(93,8),(6,103),(123,102),(36,11),(153,92),(66,14),(96,34),(9,26),(39,30),(69,79),(12,34)]),
  (0,2,[(290,7),(203,48),(116,27),(233,22),(146,30),(59,13),(263,14),(176,67),(89,34),(206,84),(119,81),(32,26),(236,7),(149,102),(62,6),(179,102),(92,58),(5,13),(122,79),(35,60),(152,40),(65,82),(95,98),(8,61),(38,3),(68,102),(11,37)]),
  (1,0,[(319,4),(232,6),(145,81),(58,39),(262,10),(175,88),(88,24),(292,6),(205,102),(118,61),(31,37),(235,11),(148,71),(61,55),(178,26),(91,6),(208,83),(121,38),(34,102),(151,27),(64,22),(94,36),(7,29),(124,97),(37,90),(67,13),(10,81),(40,23)]),
  (1,1,[(261,6),(174,38),(87,52),(204,9),(117,82),(234,16),(147,102),(60,79),(177,54),(90,17),(207,10),(120,88),(33,27),(150,95),(63,8),(93,59),(123,50),(36,21),(66,28),(9,57),(39,102)]),
  (1,2,[(290,105),(203,86),(116,59),(29,2),(233,103),(146,41),(59,105),(176,5),(89,65),(206,89),(119,73),(32,90),(149,57),(62,19),(92,18),(5,80),(122,9),(35,87),(65,70),(8,28),(38,53)]),
  (2,0,[(118,21),(31,91),(61,21),(91,21),(4,91),(34,91),(7,70)]),
  (2,1,[(174,107),(87,32),(204,57),(117,28),(147,57),(90,33),(120,79),(33,74),(63,108),(6,21),(36,33)]),
  (2,2,[(146,57),(89,87),(2,39),(119,57),(32,88),(5,39),(35,108)])]
theorem fast21_10_eq : flattenGrouped fast21_10=encode flat21_10 := by rfl

def fast21_11 : List FastBlock := [
  (0,0,[(319,107),(232,96),(145,66),(349,62),(262,62),(175,5),(292,34),(205,61),(118,22),(31,95),(322,15),(235,71),(148,69),(61,85),(265,99),(178,77),(91,81),(4,95),(295,62),(208,85),(121,78),(34,78),(238,0),(151,26),(64,36),(181,47),(94,65),(7,102),(211,46),(124,81),(37,47),(154,31),(67,21),(97,39),(10,27),(127,60),(40,32),(70,93),(13,62),(43,3)]),
  (0,1,[(348,4),(261,24),(174,95),(87,41),(378,104),(291,9),(204,27),(117,81),(321,99),(234,53),(147,71),(60,9),(264,97),(177,21),(90,83),(294,7),(207,48),(120,91),(33,106),(237,95),(150,37),(63,80),(180,53),(93,78),(6,87),(210,92),(123,1),(36,101),(153,5),(66,96),(96,69),(9,100),(126,69),(39,25),(69,72),(12,38),(42,56)]),
  (0,2,[(290,4),(203,26),(116,86),(320,99),(233,107),(146,40),(263,33),(176,69),(89,97),(2,67),(293,99),(206,104),(119,84),(32,20),(236,48),(149,88),(62,36),(179,34),(92,103),(5,72),(209,65),(122,7),(35,84),(152,50),(65,20),(95,44),(8,28),(125,73),(38,6),(68,15),(11,86),(41,105)]),
  (1,0,[(406,2),(319,21),(232,0),(145,49),(58,64),(349,6),(262,20),(175,14),(88,55),(1,51),(292,0),(205,37),(118,88),(31,33),(322,20),(235,16),(148,70),(61,12),(265,15),(178,13),(91,78),(4,62),(208,14),(121,30),(34,8),(238,98),(151,74),(64,2),(181,46),(94,0),(7,88),(124,62),(37,81),(154,69),(67,40),(97,34),(10,97),(40,39),(70,5),(13,67)]),
  (1,1,[(348,6),(261,89),(174,106),(87,35),(291,19),(204,87),(117,80),(30,33),(321,6),(234,106),(147,66),(60,43),(264,102),(177,45),(90,77),(3,33),(207,76),(120,41),(33,38),(237,83),(150,53),(63,0),(180,42),(93,8),(6,103),(123,102),(36,11),(153,92),(66,14),(96,34),(9,26),(39,30),(69,79),(12,34)]),
  (1,2,[(290,7),(203,48),(116,27),(233,22),(146,30),(59,13),(263,14),(176,67),(89,34),(206,84),(119,81),(32,26),(236,7),(149,102),(62,6),(179,102),(92,58),(5,13),(122,79),(35,60),(152,40),(65,82),(95,98),(8,61),(38,3),(68,102),(11,37)]),
  (2,0,[(319,4),(232,6),(145,81),(58,39),(262,10),(175,88),(88,24),(292,6),(205,102),(118,61),(31,37),(235,11),(148,71),(61,55),(178,26),(91,6),(208,83),(121,38),(34,102),(151,27),(64,22),(94,36),(7,29),(124,97),(37,90),(67,13),(10,81),(40,23)]),
  (2,1,[(261,6),(174,38),(87,52),(204,9),(117,82),(234,16),(147,102),(60,79),(177,54),(90,17),(207,10),(120,88),(33,27),(150,95),(63,8),(93,59),(123,50),(36,21),(66,28),(9,57),(39,102)]),
  (2,2,[(290,105),(203,86),(116,59),(29,2),(233,103),(146,41),(59,105),(176,5),(89,65),(206,89),(119,73),(32,90),(149,57),(62,19),(92,18),(5,80),(122,9),(35,87),(65,70),(8,28),(38,53)])]
theorem fast21_11_eq : flattenGrouped fast21_11=encode flat21_11 := by rfl

def fast21_12 : List FastBlock := [
  (0,0,[(493,93),(406,62),(319,107),(232,44),(145,96),(58,21),(436,53),(349,31),(262,0),(175,50),(88,101),(466,89),(379,83),(292,53),(205,62),(118,97),(31,107),(409,36),(322,45),(235,80),(148,102),(61,9),(352,44),(265,43),(178,74),(91,101),(382,64),(295,5),(208,49),(121,22),(34,17),(325,57),(238,87),(151,80),(64,53),(268,28),(181,54),(94,5),(7,74),(298,9),(211,10),(124,3),(37,9),(241,3),(154,65),(67,19),(184,11),(97,60),(10,103),(214,103),(127,93),(40,46),(157,94),(70,15),(100,53),(13,16),(130,29),(43,22),(73,33),(16,106),(46,39)]),
  (0,1,[(435,77),(348,1),(261,28),(174,104),(87,68),(378,21),(291,67),(204,93),(117,15),(408,33),(321,8),(234,1),(147,37),(60,102),(351,80),(264,78),(177,23),(90,82),(381,65),(294,5),(207,9),(120,97),(33,34),(324,95),(237,36),(150,99),(63,99),(267,69),(180,99),(93,46),(297,36),(210,17),(123,39),(36,41),(240,14),(153,37),(66,12),(183,81),(96,11),(9,9),(213,52),(126,5),(39,65),(156,10),(69,41),(99,75),(12,44),(129,30),(42,81),(72,7),(15,72),(45,72)]),
  (0,2,[(464,8),(377,97),(290,60),(203,91),(116,10),(29,23),(407,20),(320,41),(233,63),(146,2),(59,82),(350,45),(263,25),(176,29),(89,99),(380,103),(293,90),(206,62),(119,36),(32,85),(323,58),(236,106),(149,4),(62,27),(266,59),(179,11),(92,56),(5,48),(296,45),(209,56),(122,89),(35,0),(239,62),(152,12),(65,12),(182,85),(95,2),(8,36),(212,53),(125,85),(38,41),(155,68),(68,95),(98,4),(11,71),(128,84),(41,13),(71,15),(14,31),(44,57)]),
  (1,0,[(319,107),(232,96),(145,66),(349,62),(262,62),(175,5),(292,34),(205,61),(118,22),(31,95),(322,15),(235,71),(148,69),(61,85),(265,99),(178,77),(91,81),(4,95),(295,62),(208,85),(121,78),(34,78),(238,0),(151,26),(64,36),(181,47),(94,65),(7,102),(211,46),(124,81),(37,47),(154,31),(67,21),(97,39),(10,27),(127,60),(40,32),(70,93),(13,62),(43,3)]),
  (1,1,[(348,4),(261,24),(174,95),(87,41),(378,104),(291,9),(204,27),(117,81),(321,99),(234,53),(147,71),(60,9),(264,97),(177,21),(90,83),(294,7),(207,48),(120,91),(33,106),(237,95),(150,37),(63,80),(180,53),(93,78),(6,87),(210,92),(123,1),(36,101),(153,5),(66,96),(96,69),(9,100),(126,69),(39,25),(69,72),(12,38),(42,56)]),
  (1,2,[(290,4),(203,26),(116,86),(320,99),(233,107),(146,40),(263,33),(176,69),(89,97),(2,67),(293,99),(206,104),(119,84),(32,20),(236,48),(149,88),(62,36),(179,34),(92,103),(5,72),(209,65),(122,7),(35,84),(152,50),(65,20),(95,44),(8,28),(125,73),(38,6),(68,15),(11,86),(41,105)]),
  (2,0,[(406,2),(319,21),(232,0),(145,49),(58,64),(349,6),(262,20),(175,14),(88,55),(1,51),(292,0),(205,37),(118,88),(31,33),(322,20),(235,16),(148,70),(61,12),(265,15),(178,13),(91,78),(4,62),(208,14),(121,30),(34,8),(238,98),(151,74),(64,2),(181,46),(94,0),(7,88),(124,62),(37,81),(154,69),(67,40),(97,34),(10,97),(40,39),(70,5),(13,67)]),
  (2,1,[(348,6),(261,89),(174,106),(87,35),(291,19),(204,87),(117,80),(30,33),(321,6),(234,106),(147,66),(60,43),(264,102),(177,45),(90,77),(3,33),(207,76),(120,41),(33,38),(237,83),(150,53),(63,0),(180,42),(93,8),(6,103),(123,102),(36,11),(153,92),(66,14),(96,34),(9,26),(39,30),(69,79),(12,34)]),
  (2,2,[(290,7),(203,48),(116,27),(233,22),(146,30),(59,13),(263,14),(176,67),(89,34),(206,84),(119,81),(32,26),(236,7),(149,102),(62,6),(179,102),(92,58),(5,13),(122,79),(35,60),(152,40),(65,82),(95,98),(8,61),(38,3),(68,102),(11,37)])]
theorem fast21_12_eq : flattenGrouped fast21_12=encode flat21_12 := by rfl

def fast21_20 : List FastBlock := [
  (0,0,[(377,102),(290,67),(203,92),(116,101),(320,80),(233,81),(146,48),(59,89),(350,95),(263,32),(176,9),(89,94),(293,24),(206,91),(119,44),(32,69),(323,102),(236,1),(149,25),(62,50),(266,26),(179,83),(92,16),(5,89),(209,84),(122,69),(35,40),(239,82),(152,16),(65,37),(182,67),(95,2),(8,92),(125,108),(38,53),(155,19),(68,81),(98,43),(11,36),(41,62),(71,96),(14,22)]),
  (0,1,[(406,2),(319,14),(232,61),(145,22),(58,64),(349,6),(262,107),(175,93),(88,42),(1,51),(292,88),(205,31),(118,27),(31,33),(322,20),(235,19),(148,68),(61,82),(265,103),(178,62),(91,38),(4,62),(208,46),(121,0),(34,78),(238,91),(151,2),(64,45),(181,13),(94,78),(7,75),(124,103),(37,69),(154,29),(67,64),(97,52),(10,36),(40,108),(70,12),(13,30)]),
  (0,2,[(348,6),(261,89),(174,106),(87,35),(291,19),(204,87),(117,80),(30,33),(321,6),(234,106),(147,66),(60,43),(264,102),(177,45),(90,77),(3,33),(207,76),(120,41),(33,38),(237,83),(150,53),(63,0),(180,42),(93,8),(6,103),(123,102),(36,11),(153,92),(66,14),(96,34),(9,26),(39,30),(69,79),(12,34)]),
  (1,0,[(377,4),(290,4),(203,77),(116,33),(29,64),(320,10),(233,8),(146,58),(59,88),(263,1),(176,54),(89,13),(293,106),(206,49),(119,95),(32,3),(236,92),(149,33),(62,59),(179,90),(92,6),(5,53),(209,94),(122,85),(35,6),(152,58),(65,55),(95,60),(8,48),(125,26),(38,70),(68,77),(11,52),(41,5)]),
  (1,1,[(319,8),(232,29),(145,22),(58,37),(262,16),(175,47),(88,28),(292,10),(205,11),(118,46),(31,35),(235,37),(148,66),(61,78),(178,73),(91,31),(208,103),(121,56),(34,41),(151,70),(64,25),(94,57),(7,58),(124,88),(37,84),(67,108),(10,53),(40,79)]),
  (1,2,[(261,6),(174,38),(87,52),(204,9),(117,82),(234,16),(147,102),(60,79),(177,54),(90,17),(207,10),(120,88),(33,27),(150,95),(63,8),(93,59),(123,50),(36,21),(66,28),(9,57),(39,102)]),
  (2,0,[(233,52),(146,80),(176,74),(89,20),(2,49),(206,52),(119,14),(32,52),(149,80),(62,21),(92,107),(5,28),(122,29),(35,108),(65,1),(8,88),(38,76)]),
  (2,1,[(175,52),(118,43),(31,52),(148,104),(61,42),(91,43),(4,52),(121,52),(34,73),(64,1),(7,31),(37,1)]),
  (2,2,[(174,107),(87,32),(204,57),(117,28),(147,57),(90,33),(120,79),(33,74),(63,108),(6,21),(36,33)])]
theorem fast21_20_eq : flattenGrouped fast21_20=encode flat21_20 := by rfl

def fast21_21 : List FastBlock := [
  (0,0,[(377,105),(290,102),(203,92),(116,27),(407,10),(320,5),(233,88),(146,104),(350,86),(263,8),(176,0),(89,94),(2,73),(380,10),(293,2),(206,0),(119,68),(32,28),(323,68),(236,79),(149,92),(62,42),(266,26),(179,13),(92,67),(5,46),(296,41),(209,21),(122,84),(35,6),(239,52),(152,8),(65,0),(182,47),(95,72),(8,2),(212,1),(125,10),(38,102),(155,36),(68,44),(98,43),(11,79),(128,15),(41,93),(71,63),(14,4),(44,86)]),
  (0,1,[(319,103),(232,70),(145,89),(349,72),(262,64),(175,74),(292,106),(205,75),(118,57),(31,28),(322,35),(235,78),(148,54),(61,65),(265,18),(178,29),(91,57),(4,28),(295,72),(208,56),(121,0),(34,95),(238,105),(151,40),(64,25),(181,72),(94,51),(7,30),(211,90),(124,30),(37,44),(154,17),(67,104),(97,89),(10,108),(127,96),(40,49),(70,82),(13,85),(43,7)]),
  (0,2,[(348,4),(261,24),(174,95),(87,41),(378,104),(291,9),(204,27),(117,81),(321,99),(234,53),(147,71),(60,9),(264,97),(177,21),(90,83),(294,7),(207,48),(120,91),(33,106),(237,95),(150,37),(63,80),(180,53),(93,78),(6,87),(210,92),(123,1),(36,101),(153,5),(66,96),(96,69),(9,100),(126,69),(39,25),(69,72),(12,38),(42,56)]),
  (1,0,[(377,102),(290,67),(203,92),(116,101),(320,80),(233,81),(146,48),(59,89),(350,95),(263,32),(176,9),(89,94),(293,24),(206,91),(119,44),(32,69),(323,102),(236,1),(149,25),(62,50),(266,26),(179,83),(92,16),(5,89),(209,84),(122,69),(35,40),(239,82),(152,16),(65,37),(182,67),(95,2),(8,92),(125,108),(38,53),(155,19),(68,81),(98,43),(11,36),(41,62),(71,96),(14,22)]),
  (1,1,[(406,2),(319,14),(232,61),(145,22),(58,64),(349,6),(262,107),(175,93),(88,42),(1,51),(292,88),(205,31),(118,27),(31,33),(322,20),(235,19),(148,68),(61,82),(265,103),(178,62),(91,38),(4,62),(208,46),(121,0),(34,78),(238,91),(151,2),(64,45),(181,13),(94,78),(7,75),(124,103),(37,69),(154,29),(67,64),(97,52),(10,36),(40,108),(70,12),(13,30)]),
  (1,2,[(348,6),(261,89),(174,106),(87,35),(291,19),(204,87),(117,80),(30,33),(321,6),(234,106),(147,66),(60,43),(264,102),(177,45),(90,77),(3,33),(207,76),(120,41),(33,38),(237,83),(150,53),(63,0),(180,42),(93,8),(6,103),(123,102),(36,11),(153,92),(66,14),(96,34),(9,26),(39,30),(69,79),(12,34)]),
  (2,0,[(377,4),(290,4),(203,77),(116,33),(29,64),(320,10),(233,8),(146,58),(59,88),(263,1),(176,54),(89,13),(293,106),(206,49),(119,95),(32,3),(236,92),(149,33),(62,59),(179,90),(92,6),(5,53),(209,94),(122,85),(35,6),(152,58),(65,55),(95,60),(8,48),(125,26),(38,70),(68,77),(11,52),(41,5)]),
  (2,1,[(319,8),(232,29),(145,22),(58,37),(262,16),(175,47),(88,28),(292,10),(205,11),(118,46),(31,35),(235,37),(148,66),(61,78),(178,73),(91,31),(208,103),(121,56),(34,41),(151,70),(64,25),(94,57),(7,58),(124,88),(37,84),(67,108),(10,53),(40,79)]),
  (2,2,[(261,6),(174,38),(87,52),(204,9),(117,82),(234,16),(147,102),(60,79),(177,54),(90,17),(207,10),(120,88),(33,27),(150,95),(63,8),(93,59),(123,50),(36,21),(66,28),(9,57),(39,102)])]
theorem fast21_21_eq : flattenGrouped fast21_21=encode flat21_21 := by rfl

def fast21_22 : List FastBlock := [
  (0,0,[(551,101),(464,50),(377,101),(290,85),(203,68),(116,79),(29,82),(494,81),(407,66),(320,99),(233,70),(146,81),(59,94),(437,44),(350,66),(263,54),(176,64),(89,34),(467,52),(380,40),(293,86),(206,17),(119,99),(32,100),(410,63),(323,70),(236,64),(149,22),(62,106),(353,60),(266,89),(179,50),(92,79),(5,10),(383,84),(296,44),(209,32),(122,56),(35,32),(326,63),(239,73),(152,88),(65,76),(269,56),(182,17),(95,11),(8,11),(299,15),(212,104),(125,55),(38,77),(242,72),(155,103),(68,16),(185,8),(98,28),(11,81),(215,30),(128,26),(41,63),(158,74),(71,5),(101,86),(14,65),(131,99),(44,42),(74,2),(17,42),(47,28)]),
  (0,1,[(493,85),(406,74),(319,47),(232,62),(145,86),(58,107),(436,33),(349,99),(262,46),(175,48),(88,19),(466,81),(379,50),(292,77),(205,51),(118,97),(31,84),(409,22),(322,23),(235,64),(148,64),(61,60),(352,50),(265,21),(178,41),(91,84),(382,70),(295,74),(208,85),(121,39),(34,102),(325,63),(238,34),(151,96),(64,26),(268,16),(181,31),(94,46),(7,26),(298,73),(211,87),(124,21),(37,82),(241,106),(154,77),(67,75),(184,76),(97,72),(10,67),(214,50),(127,4),(40,43),(157,51),(70,16),(100,34),(13,54),(130,54),(43,87),(73,70),(16,75),(46,91)]),
  (0,2,[(435,77),(348,1),(261,28),(174,104),(87,68),(378,21),(291,67),(204,93),(117,15),(408,33),(321,8),(234,1),(147,37),(60,102),(351,80),(264,78),(177,23),(90,82),(381,65),(294,5),(207,9),(120,97),(33,34),(324,95),(237,36),(150,99),(63,99),(267,69),(180,99),(93,46),(297,36),(210,17),(123,39),(36,41),(240,14),(153,37),(66,12),(183,81),(96,11),(9,9),(213,52),(126,5),(39,65),(156,10),(69,41),(99,75),(12,44),(129,30),(42,81),(72,7),(15,72),(45,72)]),
  (1,0,[(377,105),(290,102),(203,92),(116,27),(407,10),(320,5),(233,88),(146,104),(350,86),(263,8),(176,0),(89,94),(2,73),(380,10),(293,2),(206,0),(119,68),(32,28),(323,68),(236,79),(149,92),(62,42),(266,26),(179,13),(92,67),(5,46),(296,41),(209,21),(122,84),(35,6),(239,52),(152,8),(65,0),(182,47),(95,72),(8,2),(212,1),(125,10),(38,102),(155,36),(68,44),(98,43),(11,79),(128,15),(41,93),(71,63),(14,4),(44,86)]),
  (1,1,[(319,103),(232,70),(145,89),(349,72),(262,64),(175,74),(292,106),(205,75),(118,57),(31,28),(322,35),(235,78),(148,54),(61,65),(265,18),(178,29),(91,57),(4,28),(295,72),(208,56),(121,0),(34,95),(238,105),(151,40),(64,25),(181,72),(94,51),(7,30),(211,90),(124,30),(37,44),(154,17),(67,104),(97,89),(10,108),(127,96),(40,49),(70,82),(13,85),(43,7)]),
  (1,2,[(348,4),(261,24),(174,95),(87,41),(378,104),(291,9),(204,27),(117,81),(321,99),(234,53),(147,71),(60,9),(264,97),(177,21),(90,83),(294,7),(207,48),(120,91),(33,106),(237,95),(150,37),(63,80),(180,53),(93,78),(6,87),(210,92),(123,1),(36,101),(153,5),(66,96),(96,69),(9,100),(126,69),(39,25),(69,72),(12,38),(42,56)]),
  (2,0,[(377,102),(290,67),(203,92),(116,101),(320,80),(233,81),(146,48),(59,89),(350,95),(263,32),(176,9),(89,94),(293,24),(206,91),(119,44),(32,69),(323,102),(236,1),(149,25),(62,50),(266,26),(179,83),(92,16),(5,89),(209,84),(122,69),(35,40),(239,82),(152,16),(65,37),(182,67),(95,2),(8,92),(125,108),(38,53),(155,19),(68,81),(98,43),(11,36),(41,62),(71,96),(14,22)]),
  (2,1,[(406,2),(319,14),(232,61),(145,22),(58,64),(349,6),(262,107),(175,93),(88,42),(1,51),(292,88),(205,31),(118,27),(31,33),(322,20),(235,19),(148,68),(61,82),(265,103),(178,62),(91,38),(4,62),(208,46),(121,0),(34,78),(238,91),(151,2),(64,45),(181,13),(94,78),(7,75),(124,103),(37,69),(154,29),(67,64),(97,52),(10,36),(40,108),(70,12),(13,30)]),
  (2,2,[(348,6),(261,89),(174,106),(87,35),(291,19),(204,87),(117,80),(30,33),(321,6),(234,106),(147,66),(60,43),(264,102),(177,45),(90,77),(3,33),(207,76),(120,41),(33,38),(237,83),(150,53),(63,0),(180,42),(93,8),(6,103),(123,102),(36,11),(153,92),(66,14),(96,34),(9,26),(39,30),(69,79),(12,34)])]
theorem fast21_22_eq : flattenGrouped fast21_22=encode flat21_22 := by rfl

def fast21 : Fin 3 → Fin 3 → List FastBlock :=
  ![![fast21_00, fast21_01, fast21_02], ![fast21_10, fast21_11, fast21_12], ![fast21_20, fast21_21, fast21_22]]
end CycleQ2SegreModularFastActions
#print axioms CycleQ2SegreModularFastActions.fast21_22_eq
end


/- Component: continuation_3/SegreModularFastActions22.lean -/
section
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
set_option Elab.async false
namespace CycleQ2SegreModularFastActions
open CycleQ2SparseModularFastDot CycleQ2SegreModularDetectorExpressions

def fast22_00 : List FastBlock := [
  (0,0,[(348,2),(261,86),(174,28),(87,100),(0,2),(291,2),(204,92),(117,2),(30,27),(234,108),(147,58),(60,78),(264,86),(177,29),(90,45),(3,90),(207,46),(120,101),(33,20),(150,64),(63,92),(180,108),(93,92),(6,75),(123,36),(36,47),(66,54),(96,86),(9,90),(39,57),(12,106)]),
  (0,1,[(290,4),(203,19),(116,61),(29,25),(233,2),(146,104),(59,1),(263,2),(176,37),(89,42),(2,27),(206,18),(119,90),(32,57),(62,27),(179,43),(92,60),(5,12),(122,94),(35,98),(65,86),(95,3),(8,39),(38,51),(11,53)]),
  (0,2,[(232,3),(145,9),(58,97),(88,94),(205,2),(118,101),(31,1),(148,4),(61,45),(178,108),(91,79),(4,13),(121,103),(34,81),(64,69),(94,99),(7,21),(37,86),(10,4)]),
  (1,0,[(147,108),(60,32),(90,108),(63,33),(93,108),(6,32),(36,108),(9,33)]),
  (1,1,[(89,108),(62,108),(35,108),(8,108)]),
  (1,2,[(145,108),(58,1),(88,1),(91,108),(4,1),(34,1)]),
  (2,1,[(146,57),(59,52),(89,52)]),
  (2,2,[(61,52)])]
theorem fast22_00_eq : flattenGrouped fast22_00=encode flat22_00 := by rfl

def fast22_01 : List FastBlock := [
  (0,0,[(291,57),(204,81),(117,80),(147,23),(177,98),(90,54),(207,71),(120,67),(237,52),(150,92),(63,83),(180,46),(93,85),(123,106),(153,84),(66,41),(96,36),(69,5)]),
  (0,1,[(320,104),(233,4),(146,57),(59,53),(176,57),(89,2),(206,57),(119,75),(236,56),(149,52),(62,43),(179,47),(92,78),(122,60),(152,52),(65,17),(95,101),(68,84)]),
  (0,2,[(262,104),(175,56),(88,58),(118,63),(148,62),(61,2),(178,61),(91,65),(121,53),(64,96),(94,44),(67,104)]),
  (1,0,[(348,2),(261,86),(174,28),(87,100),(0,2),(291,2),(204,92),(117,2),(30,27),(234,108),(147,58),(60,78),(264,86),(177,29),(90,45),(3,90),(207,46),(120,101),(33,20),(150,64),(63,92),(180,108),(93,92),(6,75),(123,36),(36,47),(66,54),(96,86),(9,90),(39,57),(12,106)]),
  (1,1,[(290,4),(203,19),(116,61),(29,25),(233,2),(146,104),(59,1),(263,2),(176,37),(89,42),(2,27),(206,18),(119,90),(32,57),(62,27),(179,43),(92,60),(5,12),(122,94),(35,98),(65,86),(95,3),(8,39),(38,51),(11,53)]),
  (1,2,[(232,3),(145,9),(58,97),(88,94),(205,2),(118,101),(31,1),(148,4),(61,45),(178,108),(91,79),(4,13),(121,103),(34,81),(64,69),(94,99),(7,21),(37,86),(10,4)]),
  (2,0,[(147,108),(60,32),(90,108),(63,33),(93,108),(6,32),(36,108),(9,33)]),
  (2,1,[(89,108),(62,108),(35,108),(8,108)]),
  (2,2,[(145,108),(58,1),(88,1),(91,108),(4,1),(34,1)])]
theorem fast22_01_eq : flattenGrouped fast22_01=encode flat22_01 := by rfl

def fast22_02 : List FastBlock := [
  (0,0,[(348,107),(261,21),(174,4),(87,86),(291,107),(204,4),(117,67),(234,3),(147,39),(60,18),(264,25),(177,35),(90,60),(294,107),(207,23),(120,46),(33,86),(237,107),(150,30),(63,98),(180,22),(93,95),(6,18),(210,25),(123,7),(36,60),(66,16),(96,10),(9,31),(126,19),(39,56),(69,38),(99,107),(12,83),(42,93),(15,66)]),
  (0,1,[(290,106),(203,99),(116,13),(146,16),(263,107),(176,8),(89,46),(206,105),(119,68),(236,107),(149,21),(62,46),(179,6),(92,90),(209,107),(122,48),(35,46),(152,6),(65,90),(182,1),(95,54),(8,33),(125,6),(38,74),(68,36),(98,10),(11,22),(41,23),(14,105)]),
  (0,2,[(319,2),(232,42),(145,108),(58,66),(175,108),(88,21),(205,108),(118,79),(235,43),(148,1),(61,70),(265,2),(178,45),(91,55),(4,66),(121,84),(34,21),(64,94),(181,43),(94,26),(7,70),(124,3),(37,56),(67,95),(97,1),(10,15),(40,25),(13,10)]),
  (1,0,[(291,57),(204,81),(117,80),(147,23),(177,98),(90,54),(207,71),(120,67),(237,52),(150,92),(63,83),(180,46),(93,85),(123,106),(153,84),(66,41),(96,36),(69,5)]),
  (1,1,[(320,104),(233,4),(146,57),(59,53),(176,57),(89,2),(206,57),(119,75),(236,56),(149,52),(62,43),(179,47),(92,78),(122,60),(152,52),(65,17),(95,101),(68,84)]),
  (1,2,[(262,104),(175,56),(88,58),(118,63),(148,62),(61,2),(178,61),(91,65),(121,53),(64,96),(94,44),(67,104)]),
  (2,0,[(348,2),(261,86),(174,28),(87,100),(0,2),(291,2),(204,92),(117,2),(30,27),(234,108),(147,58),(60,78),(264,86),(177,29),(90,45),(3,90),(207,46),(120,101),(33,20),(150,64),(63,92),(180,108),(93,92),(6,75),(123,36),(36,47),(66,54),(96,86),(9,90),(39,57),(12,106)]),
  (2,1,[(290,4),(203,19),(116,61),(29,25),(233,2),(146,104),(59,1),(263,2),(176,37),(89,42),(2,27),(206,18),(119,90),(32,57),(62,27),(179,43),(92,60),(5,12),(122,94),(35,98),(65,86),(95,3),(8,39),(38,51),(11,53)]),
  (2,2,[(232,3),(145,9),(58,97),(88,94),(205,2),(118,101),(31,1),(148,4),(61,45),(178,108),(91,79),(4,13),(121,103),(34,81),(64,69),(94,99),(7,21),(37,86),(10,4)])]
theorem fast22_02_eq : flattenGrouped fast22_02=encode flat22_02 := by rfl

def fast22_10 : List FastBlock := [
  (0,0,[(319,106),(232,87),(145,82),(58,52),(262,106),(175,6),(88,77),(292,107),(205,72),(118,85),(31,32),(235,93),(148,61),(61,62),(265,1),(178,103),(91,13),(4,89),(208,73),(121,38),(34,105),(151,69),(64,15),(181,86),(94,17),(7,11),(124,53),(37,63),(67,11),(97,102),(10,58),(40,0),(13,23)]),
  (0,1,[(348,2),(261,83),(174,19),(87,3),(0,2),(291,2),(204,92),(117,17),(30,27),(234,103),(147,57),(60,89),(264,86),(177,25),(90,15),(3,90),(207,45),(120,30),(33,6),(150,66),(63,75),(93,53),(6,62),(123,52),(36,54),(66,8),(96,96),(9,69),(39,76),(12,102)]),
  (0,2,[(290,4),(203,19),(116,61),(29,25),(233,2),(146,104),(59,1),(263,2),(176,37),(89,42),(2,27),(206,18),(119,90),(32,57),(62,27),(179,43),(92,60),(5,12),(122,94),(35,98),(65,86),(95,3),(8,39),(38,51),(11,53)]),
  (1,0,[(232,1),(145,76),(58,32),(88,31),(118,108),(148,76),(61,33),(178,1),(4,32),(34,31),(64,108),(94,76),(7,33),(37,33)]),
  (1,1,[(174,1),(87,108),(117,108),(60,31),(90,107),(120,1),(33,108),(63,32),(6,31),(36,107),(9,33)]),
  (1,2,[(89,108),(62,108),(35,108),(8,108)]),
  (2,0,[(148,57),(61,29),(91,57),(64,81)]),
  (2,1,[(90,57),(63,57)]),
  (2,2,[(146,57),(59,52),(89,52)])]
theorem fast22_10_eq : flattenGrouped fast22_10=encode flat22_10 := by rfl

def fast22_11 : List FastBlock := [
  (0,0,[(349,5),(262,2),(175,99),(88,3),(292,5),(205,99),(118,105),(235,47),(148,66),(61,64),(265,101),(178,76),(91,68),(208,104),(121,4),(151,44),(64,86),(181,7),(94,78),(124,70),(154,5),(67,65),(97,40),(70,53)]),
  (0,1,[(291,62),(204,25),(117,22),(147,69),(264,5),(177,89),(90,103),(207,10),(120,48),(237,52),(150,86),(63,81),(180,94),(93,33),(123,9),(153,84),(66,54),(96,106),(69,10)]),
  (0,2,[(320,104),(233,4),(146,57),(59,53),(176,57),(89,2),(206,57),(119,75),(236,56),(149,52),(62,43),(179,47),(92,78),(122,60),(152,52),(65,17),(95,101),(68,84)]),
  (1,0,[(319,106),(232,87),(145,82),(58,52),(262,106),(175,6),(88,77),(292,107),(205,72),(118,85),(31,32),(235,93),(148,61),(61,62),(265,1),(178,103),(91,13),(4,89),(208,73),(121,38),(34,105),(151,69),(64,15),(181,86),(94,17),(7,11),(124,53),(37,63),(67,11),(97,102),(10,58),(40,0),(13,23)]),
  (1,1,[(348,2),(261,83),(174,19),(87,3),(0,2),(291,2),(204,92),(117,17),(30,27),(234,103),(147,57),(60,89),(264,86),(177,25),(90,15),(3,90),(207,45),(120,30),(33,6),(150,66),(63,75),(93,53),(6,62),(123,52),(36,54),(66,8),(96,96),(9,69),(39,76),(12,102)]),
  (1,2,[(290,4),(203,19),(116,61),(29,25),(233,2),(146,104),(59,1),(263,2),(176,37),(89,42),(2,27),(206,18),(119,90),(32,57),(62,27),(179,43),(92,60),(5,12),(122,94),(35,98),(65,86),(95,3),(8,39),(38,51),(11,53)]),
  (2,0,[(232,1),(145,76),(58,32),(88,31),(118,108),(148,76),(61,33),(178,1),(4,32),(34,31),(64,108),(94,76),(7,33),(37,33)]),
  (2,1,[(174,1),(87,108),(117,108),(60,31),(90,107),(120,1),(33,108),(63,32),(6,31),(36,107),(9,33)]),
  (2,2,[(89,108),(62,108),(35,108),(8,108)])]
theorem fast22_11_eq : flattenGrouped fast22_11=encode flat22_11 := by rfl

def fast22_12 : List FastBlock := [
  (0,0,[(406,107),(319,22),(232,37),(145,11),(58,41),(349,107),(262,68),(175,57),(88,61),(292,1),(205,108),(322,23),(235,37),(148,68),(61,58),(352,107),(265,85),(178,43),(91,28),(4,41),(295,107),(208,56),(121,96),(34,61),(238,2),(151,73),(64,65),(268,23),(181,1),(94,85),(7,58),(211,63),(124,61),(37,17),(154,11),(67,91),(184,1),(97,17),(10,65),(127,73),(40,17),(70,58),(100,23),(13,52),(43,52),(16,3)]),
  (0,1,[(348,105),(261,88),(174,5),(87,20),(291,107),(204,5),(117,46),(321,107),(234,71),(147,70),(60,61),(264,91),(177,35),(90,78),(294,105),(207,88),(120,21),(33,20),(237,64),(150,54),(63,7),(267,107),(180,86),(93,55),(6,61),(210,91),(123,6),(36,78),(153,106),(66,84),(183,66),(96,107),(9,70),(126,15),(39,94),(69,27),(99,106),(12,68),(42,58),(15,56)]),
  (0,2,[(290,106),(203,99),(116,13),(146,16),(263,107),(176,8),(89,46),(206,105),(119,68),(236,107),(149,21),(62,46),(179,6),(92,90),(209,107),(122,48),(35,46),(152,6),(65,90),(182,1),(95,54),(8,33),(125,6),(38,74),(68,36),(98,10),(11,22),(41,23),(14,105)]),
  (1,0,[(349,5),(262,2),(175,99),(88,3),(292,5),(205,99),(118,105),(235,47),(148,66),(61,64),(265,101),(178,76),(91,68),(208,104),(121,4),(151,44),(64,86),(181,7),(94,78),(124,70),(154,5),(67,65),(97,40),(70,53)]),
  (1,1,[(291,62),(204,25),(117,22),(147,69),(264,5),(177,89),(90,103),(207,10),(120,48),(237,52),(150,86),(63,81),(180,94),(93,33),(123,9),(153,84),(66,54),(96,106),(69,10)]),
  (1,2,[(320,104),(233,4),(146,57),(59,53),(176,57),(89,2),(206,57),(119,75),(236,56),(149,52),(62,43),(179,47),(92,78),(122,60),(152,52),(65,17),(95,101),(68,84)]),
  (2,0,[(319,106),(232,87),(145,82),(58,52),(262,106),(175,6),(88,77),(292,107),(205,72),(118,85),(31,32),(235,93),(148,61),(61,62),(265,1),(178,103),(91,13),(4,89),(208,73),(121,38),(34,105),(151,69),(64,15),(181,86),(94,17),(7,11),(124,53),(37,63),(67,11),(97,102),(10,58),(40,0),(13,23)]),
  (2,1,[(348,2),(261,83),(174,19),(87,3),(0,2),(291,2),(204,92),(117,17),(30,27),(234,103),(147,57),(60,89),(264,86),(177,25),(90,15),(3,90),(207,45),(120,30),(33,6),(150,66),(63,75),(93,53),(6,62),(123,52),(36,54),(66,8),(96,96),(9,69),(39,76),(12,102)]),
  (2,2,[(290,4),(203,19),(116,61),(29,25),(233,2),(146,104),(59,1),(263,2),(176,37),(89,42),(2,27),(206,18),(119,90),(32,57),(62,27),(179,43),(92,60),(5,12),(122,94),(35,98),(65,86),(95,3),(8,39),(38,51),(11,53)])]
theorem fast22_12_eq : flattenGrouped fast22_12=encode flat22_12 := by rfl

def fast22_20 : List FastBlock := [
  (0,0,[(377,105),(290,0),(203,2),(116,74),(29,37),(320,103),(233,50),(146,105),(59,7),(350,107),(263,25),(176,57),(89,8),(2,101),(293,3),(206,95),(119,107),(32,6),(236,48),(149,45),(62,77),(266,23),(179,30),(92,106),(5,76),(209,21),(122,43),(35,100),(152,38),(65,57),(182,108),(95,98),(8,9),(125,105),(38,31),(68,62),(98,46),(11,40),(41,104),(14,5)]),
  (0,1,[(319,102),(232,68),(145,21),(58,27),(262,104),(175,11),(88,76),(292,101),(205,16),(118,91),(31,89),(235,73),(148,85),(61,4),(265,108),(178,66),(91,53),(4,62),(208,12),(121,106),(34,36),(151,84),(64,108),(181,43),(94,89),(7,108),(124,65),(37,35),(67,92),(97,99),(10,19),(40,5),(13,79)]),
  (0,2,[(348,2),(261,83),(174,19),(87,3),(0,2),(291,2),(204,92),(117,17),(30,27),(234,103),(147,57),(60,89),(264,86),(177,25),(90,15),(3,90),(207,45),(120,30),(33,6),(150,66),(63,75),(93,53),(6,62),(123,52),(36,54),(66,8),(96,96),(9,69),(39,76),(12,102)]),
  (1,0,[(176,1),(89,77),(119,1),(149,1),(62,77),(92,77),(122,1),(35,77),(65,77),(95,1),(8,77),(38,77),(11,76)]),
  (1,1,[(232,1),(145,76),(58,32),(88,31),(148,76),(61,33),(178,1),(91,2),(4,32),(34,31),(64,1),(94,76),(7,33),(37,35),(10,1)]),
  (1,2,[(174,1),(87,108),(117,108),(60,31),(90,107),(120,1),(33,108),(63,32),(6,31),(36,107),(9,33)]),
  (2,0,[(233,52),(146,28),(59,29),(89,86),(119,57),(149,28),(62,81),(92,81)]),
  (2,1,[(175,52),(88,57),(118,57),(61,86),(91,5),(64,81)]),
  (2,2,[(90,57),(63,57)])]
theorem fast22_20_eq : flattenGrouped fast22_20=encode flat22_20 := by rfl

def fast22_21 : List FastBlock := [
  (0,0,[(407,5),(320,54),(233,71),(146,27),(59,61),(350,5),(263,48),(176,21),(89,11),(293,52),(206,57),(323,106),(236,71),(149,48),(62,73),(266,6),(179,94),(92,12),(209,30),(122,66),(239,52),(152,33),(65,1),(182,90),(95,12),(125,26),(155,106),(68,88),(98,88),(71,47)]),
  (0,1,[(349,10),(262,107),(175,42),(88,59),(292,5),(205,42),(118,103),(322,5),(235,95),(148,43),(61,11),(265,45),(178,76),(91,23),(121,69),(238,53),(151,41),(64,43),(181,17),(94,92),(124,18),(154,62),(67,48),(97,73),(70,78)]),
  (0,2,[(291,62),(204,25),(117,22),(147,69),(264,5),(177,89),(90,103),(207,10),(120,48),(237,52),(150,86),(63,81),(180,94),(93,33),(123,9),(153,84),(66,54),(96,106),(69,10)]),
  (1,0,[(377,105),(290,0),(203,2),(116,74),(29,37),(320,103),(233,50),(146,105),(59,7),(350,107),(263,25),(176,57),(89,8),(2,101),(293,3),(206,95),(119,107),(32,6),(236,48),(149,45),(62,77),(266,23),(179,30),(92,106),(5,76),(209,21),(122,43),(35,100),(152,38),(65,57),(182,108),(95,98),(8,9),(125,105),(38,31),(68,62),(98,46),(11,40),(41,104),(14,5)]),
  (1,1,[(319,102),(232,68),(145,21),(58,27),(262,104),(175,11),(88,76),(292,101),(205,16),(118,91),(31,89),(235,73),(148,85),(61,4),(265,108),(178,66),(91,53),(4,62),(208,12),(121,106),(34,36),(151,84),(64,108),(181,43),(94,89),(7,108),(124,65),(37,35),(67,92),(97,99),(10,19),(40,5),(13,79)]),
  (1,2,[(348,2),(261,83),(174,19),(87,3),(0,2),(291,2),(204,92),(117,17),(30,27),(234,103),(147,57),(60,89),(264,86),(177,25),(90,15),(3,90),(207,45),(120,30),(33,6),(150,66),(63,75),(93,53),(6,62),(123,52),(36,54),(66,8),(96,96),(9,69),(39,76),(12,102)]),
  (2,0,[(176,1),(89,77),(119,1),(149,1),(62,77),(92,77),(122,1),(35,77),(65,77),(95,1),(8,77),(38,77),(11,76)]),
  (2,1,[(232,1),(145,76),(58,32),(88,31),(148,76),(61,33),(178,1),(91,2),(4,32),(34,31),(64,1),(94,76),(7,33),(37,35),(10,1)]),
  (2,2,[(174,1),(87,108),(117,108),(60,31),(90,107),(120,1),(33,108),(63,32),(6,31),(36,107),(9,33)])]
theorem fast22_21_eq : flattenGrouped fast22_21=encode flat22_21 := by rfl

def fast22_22 : List FastBlock := [
  (0,0,[(377,3),(290,23),(203,103),(116,89),(320,3),(233,103),(146,63),(350,2),(263,37),(176,85),(89,55),(293,16),(206,11),(119,52),(323,2),(236,28),(149,105),(62,55),(266,39),(179,18),(92,101),(296,2),(209,77),(122,47),(35,55),(239,39),(152,93),(65,101),(269,108),(182,61),(95,106),(8,75),(212,36),(125,13),(38,38),(155,47),(68,15),(185,23),(98,82),(11,49),(128,56),(41,104),(71,75),(101,7),(14,53),(44,0),(17,86)]),
  (0,1,[(406,107),(319,25),(232,47),(145,107),(58,41),(349,107),(262,68),(175,41),(88,61),(292,6),(205,1),(118,50),(322,23),(235,41),(148,93),(61,58),(352,107),(265,89),(178,14),(91,45),(4,41),(295,107),(208,54),(121,47),(34,61),(238,6),(151,4),(64,82),(268,23),(181,98),(94,14),(7,58),(211,64),(124,68),(37,47),(154,108),(67,36),(97,36),(10,32),(127,57),(40,30),(70,108),(100,13),(13,30),(43,33),(16,7)]),
  (0,2,[(348,105),(261,88),(174,5),(87,20),(291,107),(204,5),(117,46),(321,107),(234,71),(147,70),(60,61),(264,91),(177,35),(90,78),(294,105),(207,88),(120,21),(33,20),(237,64),(150,54),(63,7),(267,107),(180,86),(93,55),(6,61),(210,91),(123,6),(36,78),(153,106),(66,84),(183,66),(96,107),(9,70),(126,15),(39,94),(69,27),(99,106),(12,68),(42,58),(15,56)]),
  (1,0,[(407,5),(320,54),(233,71),(146,27),(59,61),(350,5),(263,48),(176,21),(89,11),(293,52),(206,57),(323,106),(236,71),(149,48),(62,73),(266,6),(179,94),(92,12),(209,30),(122,66),(239,52),(152,33),(65,1),(182,90),(95,12),(125,26),(155,106),(68,88),(98,88),(71,47)]),
  (1,1,[(349,10),(262,107),(175,42),(88,59),(292,5),(205,42),(118,103),(322,5),(235,95),(148,43),(61,11),(265,45),(178,76),(91,23),(121,69),(238,53),(151,41),(64,43),(181,17),(94,92),(124,18),(154,62),(67,48),(97,73),(70,78)]),
  (1,2,[(291,62),(204,25),(117,22),(147,69),(264,5),(177,89),(90,103),(207,10),(120,48),(237,52),(150,86),(63,81),(180,94),(93,33),(123,9),(153,84),(66,54),(96,106),(69,10)]),
  (2,0,[(377,105),(290,0),(203,2),(116,74),(29,37),(320,103),(233,50),(146,105),(59,7),(350,107),(263,25),(176,57),(89,8),(2,101),(293,3),(206,95),(119,107),(32,6),(236,48),(149,45),(62,77),(266,23),(179,30),(92,106),(5,76),(209,21),(122,43),(35,100),(152,38),(65,57),(182,108),(95,98),(8,9),(125,105),(38,31),(68,62),(98,46),(11,40),(41,104),(14,5)]),
  (2,1,[(319,102),(232,68),(145,21),(58,27),(262,104),(175,11),(88,76),(292,101),(205,16),(118,91),(31,89),(235,73),(148,85),(61,4),(265,108),(178,66),(91,53),(4,62),(208,12),(121,106),(34,36),(151,84),(64,108),(181,43),(94,89),(7,108),(124,65),(37,35),(67,92),(97,99),(10,19),(40,5),(13,79)]),
  (2,2,[(348,2),(261,83),(174,19),(87,3),(0,2),(291,2),(204,92),(117,17),(30,27),(234,103),(147,57),(60,89),(264,86),(177,25),(90,15),(3,90),(207,45),(120,30),(33,6),(150,66),(63,75),(93,53),(6,62),(123,52),(36,54),(66,8),(96,96),(9,69),(39,76),(12,102)])]
theorem fast22_22_eq : flattenGrouped fast22_22=encode flat22_22 := by rfl

def fast22 : Fin 3 → Fin 3 → List FastBlock :=
  ![![fast22_00, fast22_01, fast22_02], ![fast22_10, fast22_11, fast22_12], ![fast22_20, fast22_21, fast22_22]]
end CycleQ2SegreModularFastActions
#print axioms CycleQ2SegreModularFastActions.fast22_22_eq
end


/- Component: continuation_3/SegreModularGaussianBinding.lean -/
section
/-! # Gaussian sparse data in the actual modular seed quotient

The saved Gaussian monomial-action data specialize to the literal seed
at r=57 and i=33 in F109. The normalizing x0 and w equations are proved
in the actual polynomial quotient used by the incidence normal form.
-/

noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false

namespace CycleQ2SegreModularGaussianBinding

open MvPolynomial CycleQ2SparseGaussianPolynomial CycleQ2IncidenceNormalForm
  CycleQ2IncidenceMonomials CycleQ2IncidenceEquations CycleQ2IncidenceFirstOrder
  CycleQ2IncidenceJacobian CycleQ2IncidenceGaussianArithmetic

abbrev P := MvPolynomial (Fin 5) F109
def coeffHom : GaussianInt →+* P := MvPolynomial.C.comp reduction
def value (p : Towers) : P := evalTowers coeffHom X (X 4) (X 0) (X 1) p
def layerValue (c : Layers) : P := evalLayers coeffHom X (X 1) c

theorem value_add (p q : Towers) : value (addTowers p q) = value p + value q :=
  eval_addTowers coeffHom X (X 4) (X 0) (X 1) p q
 theorem value_mul (p q : Towers) : value (mulTowers p q) = value p * value q :=
  eval_mulTowers coeffHom X (X 4) (X 0) (X 1) p q
 theorem value_neg (p : Towers) : value (negTowers p) = -value p :=
  eval_negTowers coeffHom X (X 4) (X 0) (X 1) p
 theorem value_scale (c : Layers) (p : Towers) :
    value (scaleTower c p) = layerValue c * value p :=
  eval_scaleTower coeffHom X (X 4) (X 0) (X 1) c p

def matrixTowers : Matrix (Fin 3) (Fin 3) Towers :=
  ![![CycleQ2SegreGaussianTangentData.m00, CycleQ2SegreGaussianTangentData.m01, CycleQ2SegreGaussianTangentData.m02],
    ![CycleQ2SegreGaussianTangentData.m10, CycleQ2SegreGaussianTangentData.m11, CycleQ2SegreGaussianTangentData.m12],
    ![CycleQ2SegreGaussianTangentData.m20, CycleQ2SegreGaussianTangentData.m21, CycleQ2SegreGaussianTangentData.m22]]

def quotientTowers : Matrix (Fin 3) (Fin 3) Towers :=
  ![![CycleQ2SegreGaussianTangentData.q00, CycleQ2SegreGaussianTangentData.q01, CycleQ2SegreGaussianTangentData.q02],
    ![CycleQ2SegreGaussianTangentData.q10, CycleQ2SegreGaussianTangentData.q11, CycleQ2SegreGaussianTangentData.q12],
    ![CycleQ2SegreGaussianTangentData.q20, CycleQ2SegreGaussianTangentData.q21, CycleQ2SegreGaussianTangentData.q22]]

theorem value_rawMatrix (i j : Fin 3) : value (matrixTowers i j) =
    rawSeedMatrix (57 : F109) i j := by
  fin_cases i <;> fin_cases j <;>
    simp only [
    matrixTowers, CycleQ2SegreGaussianTangentData.m00, CycleQ2SegreGaussianTangentData.m01, CycleQ2SegreGaussianTangentData.m02,
    CycleQ2SegreGaussianTangentData.m10, CycleQ2SegreGaussianTangentData.m11, CycleQ2SegreGaussianTangentData.m12, CycleQ2SegreGaussianTangentData.m20,
    CycleQ2SegreGaussianTangentData.m21, CycleQ2SegreGaussianTangentData.m22, value, coeffHom,
    evalTowers, evalBlocks, evalLayers, CycleQ2SparseGaussianPolynomial.eval,
    CycleQ2SparseGaussianPolynomial.termValue, CycleQ2SparseGaussianPolynomial.monomial, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, RingHom.comp_apply, reduction, Zsqrtd.lift_apply_apply,
    map_add, map_mul, map_intCast, map_ofNat,
    map_zero, map_one, map_neg, Int.cast_ofNat,
    Int.cast_neg, Nat.cast_ofNat, pow_zero, pow_one,
    mul_zero, mul_one, zero_mul, zero_add,
    add_zero, rawSeedMatrix, CycleQ2SegreSeed.rawMatrix, CycleQ2SegreSeed.leftCoeff0,
    CycleQ2SegreSeed.leftCoeff1, CycleQ2SegreSeed.baseRow0, CycleQ2SegreSeed.baseRow1, CycleQ2SegreSeed.coreRight0,
    CycleQ2SegreSeed.coreRight1, CycleQ2SegreSeed.rightCoeff0, CycleQ2SegreSeed.rightCoeff2, CycleQ2SegreSeed.rightCoeff3,
    Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  all_goals
    norm_num only [map_ofNat, map_zero, map_one, map_add, map_mul, map_neg, map_sub]
    ring

theorem value_rawQuotient (i j : Fin 3) : value (quotientTowers i j) =
    CycleQ2IncidenceFirstOrder.rawCofactorQuotient (57 : F109) i j := by
  fin_cases i <;> fin_cases j <;>
    simp only [
    quotientTowers, CycleQ2SegreGaussianTangentData.q00, CycleQ2SegreGaussianTangentData.q01, CycleQ2SegreGaussianTangentData.q02,
    CycleQ2SegreGaussianTangentData.q10, CycleQ2SegreGaussianTangentData.q11, CycleQ2SegreGaussianTangentData.q12, CycleQ2SegreGaussianTangentData.q20,
    CycleQ2SegreGaussianTangentData.q21, CycleQ2SegreGaussianTangentData.q22, value, coeffHom,
    evalTowers, evalBlocks, evalLayers, CycleQ2SparseGaussianPolynomial.eval,
    CycleQ2SparseGaussianPolynomial.termValue, CycleQ2SparseGaussianPolynomial.monomial, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, RingHom.comp_apply, reduction, Zsqrtd.lift_apply_apply,
    map_add, map_mul, map_intCast, map_ofNat,
    map_zero, map_one, map_neg, Int.cast_ofNat,
    Int.cast_neg, Nat.cast_ofNat, pow_zero, pow_one,
    mul_zero, mul_one, zero_mul, zero_add,
    add_zero, CycleQ2IncidenceFirstOrder.rawCofactorQuotient, CycleQ2SegreSeed.rawCofactorQuotient, CycleQ2SegreSeed.cross,
    CycleQ2SegreSeed.leftCoeff0, CycleQ2SegreSeed.leftCoeff1, CycleQ2SegreSeed.rightCrossQuotient, CycleQ2SegreSeed.rightMinorQuotient,
    CycleQ2SegreSeed.coreMinorQuotient, CycleQ2SegreSeed.rightCoeff0, CycleQ2SegreSeed.rightCoeff2, CycleQ2SegreSeed.rightCoeff3,
    Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  all_goals
    norm_num only [map_ofNat, map_zero, map_one, map_add, map_mul, map_neg, map_sub]
    ring

theorem value_h : value CycleQ2SegreGaussianTangentData.h = smoothH (33:F109) := by
  simp only [
    CycleQ2SegreGaussianTangentData.h, value, coeffHom, evalTowers,
    evalBlocks, evalLayers, CycleQ2SparseGaussianPolynomial.eval, CycleQ2SparseGaussianPolynomial.termValue,
    CycleQ2SparseGaussianPolynomial.monomial, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, RingHom.comp_apply, reduction, Zsqrtd.lift_apply_apply, map_add,
    map_mul, map_intCast, map_ofNat, map_zero,
    map_one, map_neg, Int.cast_ofNat, Int.cast_neg,
    Nat.cast_ofNat, pow_zero, pow_one, mul_zero,
    mul_one, zero_mul, zero_add, add_zero,
    smoothH, smoothB, smoothA]
  norm_num only [map_ofNat, map_zero, map_one, map_add, map_mul, map_neg, map_sub]
  ring

theorem value_k : value CycleQ2SegreGaussianTangentData.k = smoothK (33:F109) := by
  simp only [
    CycleQ2SegreGaussianTangentData.k, value, coeffHom, evalTowers,
    evalBlocks, evalLayers, CycleQ2SparseGaussianPolynomial.eval, CycleQ2SparseGaussianPolynomial.termValue,
    CycleQ2SparseGaussianPolynomial.monomial, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, RingHom.comp_apply, reduction, Zsqrtd.lift_apply_apply, map_add,
    map_mul, map_intCast, map_ofNat, map_zero,
    map_one, map_neg, Int.cast_ofNat, Int.cast_neg,
    Nat.cast_ofNat, pow_zero, pow_one, mul_zero,
    mul_one, zero_mul, zero_add, add_zero,
    smoothK, smoothB, smoothA]
  norm_num only [map_ofNat, map_zero, map_one, map_add, map_mul, map_neg, map_sub]
  ring

theorem value_g : value CycleQ2SegreGaussianTangentData.g = seedG (57 : F109) := by
  simp only [
    CycleQ2SegreGaussianTangentData.g, value, coeffHom, evalTowers,
    evalBlocks, evalLayers, CycleQ2SparseGaussianPolynomial.eval, CycleQ2SparseGaussianPolynomial.termValue,
    CycleQ2SparseGaussianPolynomial.monomial, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, RingHom.comp_apply, reduction, Zsqrtd.lift_apply_apply, map_add,
    map_mul, map_intCast, map_ofNat, map_zero,
    map_one, map_neg, Int.cast_ofNat, Int.cast_neg,
    Nat.cast_ofNat, pow_zero, pow_one, mul_zero,
    mul_one, zero_mul, zero_add, add_zero,
    seedG, CycleQ2SegreSeed.seedG, CycleQ2SegreSeed.linkageG]
  norm_num only [map_ofNat, map_zero, map_one, map_add, map_mul, map_neg, map_sub]
  ring

 theorem polynomial_z_relation : (X 0 : P)^3 =
    layerValue CycleQ2SegreGaussianTangentData.a0 + layerValue CycleQ2SegreGaussianTangentData.a1 * X 0 + smoothH (33:F109) := by
  simp only [
    layerValue, CycleQ2SegreGaussianTangentData.a0, CycleQ2SegreGaussianTangentData.a1, value,
    coeffHom, evalTowers, evalBlocks, evalLayers,
    CycleQ2SparseGaussianPolynomial.eval, CycleQ2SparseGaussianPolynomial.termValue, CycleQ2SparseGaussianPolynomial.monomial, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, RingHom.comp_apply,
    reduction, Zsqrtd.lift_apply_apply, map_add, map_mul, map_intCast,
    map_ofNat, map_zero, map_one, map_neg,
    Int.cast_ofNat, Int.cast_neg, Nat.cast_ofNat, pow_zero,
    pow_one, mul_zero, mul_one, zero_mul,
    zero_add, add_zero, smoothH, smoothB,
    smoothA]
  norm_num only [map_ofNat, map_zero, map_one, map_add, map_mul, map_neg, map_sub]
  ring

theorem polynomial_w_relation : (X 4 : P)^3 =
    layerValue CycleQ2SegreGaussianTangentData.b0 - X 0^6 + seedG (57 : F109) := by
  simp only [
    layerValue, CycleQ2SegreGaussianTangentData.b0, value, coeffHom,
    evalTowers, evalBlocks, evalLayers, CycleQ2SparseGaussianPolynomial.eval,
    CycleQ2SparseGaussianPolynomial.termValue, CycleQ2SparseGaussianPolynomial.monomial, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, RingHom.comp_apply, reduction, Zsqrtd.lift_apply_apply,
    map_add, map_mul, map_intCast, map_ofNat,
    map_zero, map_one, map_neg, Int.cast_ofNat,
    Int.cast_neg, Nat.cast_ofNat, pow_zero, pow_one,
    mul_zero, mul_one, zero_mul, zero_add,
    add_zero, seedG, CycleQ2SegreSeed.seedG, CycleQ2SegreSeed.linkageG]
  norm_num only [map_ofNat, map_zero, map_one, map_add, map_mul, map_neg, map_sub]
  ring

def pointIdeal : Ideal P := Ideal.span {smoothH (33:F109), seedG (57 : F109)}
abbrev PointQuotient := P ⧸ pointIdeal
def quotientMap : P →+* PointQuotient := Ideal.Quotient.mk pointIdeal
def quotientCoeffHom : GaussianInt →+* PointQuotient := quotientMap.comp coeffHom
def quotientVariables (j : Fin 5) : PointQuotient := quotientMap (X j)
def quotientValue (p : Towers) : PointQuotient :=
  evalTowers quotientCoeffHom quotientVariables (quotientVariables 4)
    (quotientVariables 0) (quotientVariables 1) p
def quotientLayerValue (p : Layers) : PointQuotient :=
  evalLayers quotientCoeffHom quotientVariables (quotientVariables 1) p
 theorem map_value (p : Towers) : quotientMap (value p) = quotientValue p :=
  map_evalTowers coeffHom quotientMap X (X 4) (X 0) (X 1) p
 theorem map_layerValue (p : Layers) : quotientMap (layerValue p) = quotientLayerValue p :=
  map_evalLayers coeffHom quotientMap X (X 1) p
 theorem quotient_h_zero : quotientMap (smoothH (33:F109)) = 0 := by
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  apply Ideal.subset_span
  simp
 theorem quotient_g_zero : quotientMap (seedG (57 : F109)) = 0 := by
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  apply Ideal.subset_span
  simp
theorem quotient_z_relation : (quotientVariables 0)^3 =
    quotientLayerValue CycleQ2SegreGaussianTangentData.a0 + quotientLayerValue CycleQ2SegreGaussianTangentData.a1 * quotientVariables 0 := by
  have hh := congrArg quotientMap polynomial_z_relation
  simpa only [map_pow, map_add, map_mul, map_layerValue, quotient_h_zero, add_zero,
    quotientVariables] using hh
 theorem quotient_w_relation : (quotientVariables 4)^3 =
    quotientLayerValue CycleQ2SegreGaussianTangentData.b0 - (quotientVariables 0)^6 := by
  have hh := congrArg quotientMap polynomial_w_relation
  simpa only [map_pow, map_add, map_sub, map_layerValue, quotient_g_zero, add_zero,
    quotientVariables] using hh


theorem pointIdeal_eq_equationsIdeal :
    pointIdeal = equationsIdeal (smoothH (33:F109)) (smoothF (57:F109) 33) := by
  ext p
  rw [smoothSeed_mem_iff_linkage]
  exact Ideal.mem_span_pair

end CycleQ2SegreModularGaussianBinding

#print axioms CycleQ2SegreModularGaussianBinding.value_rawMatrix
#print axioms CycleQ2SegreModularGaussianBinding.value_rawQuotient
#print axioms CycleQ2SegreModularGaussianBinding.quotient_z_relation
#print axioms CycleQ2SegreModularGaussianBinding.quotient_w_relation
#print axioms CycleQ2SegreModularGaussianBinding.pointIdeal_eq_equationsIdeal
end
end


/- Component: continuation_3/cylinder_bridge/SegreRelationsUnimodular.lean -/
section
/-! # Global algebraic Segre exactness when the entries generate the unit ideal

The denominator-free pivot lift reproduces the pivot entry times the proposed
cofactor variation. A Bézout identity among the nine entries combines those
nine lifts into a global lift. This is an algebraic exactness theorem over an
arbitrary commutative ring; it does not require a chosen invertible entry.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000

namespace CycleQ2SegreRelationsLocal

open Matrix CycleQ2IncidenceFirstOrder CycleQ2SegreTangentLocal
open scoped BigOperators

variable {R : Type*} [CommRing R]

/-- Every matrix entry annihilates either scalar appearing in the sixteen
relation equations. The proof uses a different row or column and a literal
vanishing two-by-two minor. -/
theorem entries_annihilate_scalars (M C : Matrix (Fin 3) (Fin 3) R)
    (hM : CycleQ2SegreLocal.cofactors M=0) (a b : R)
    (hl : ∀ i j, leftProduct M C i j=if i=j then a else 0)
    (hr : ∀ i j, rightProduct M C i j=if i=j then b else 0) :
    (∀ i j, M i j*a=0) ∧ (∀ i j, M i j*b=0) := by
  constructor
  · intro i0 j0
    obtain ⟨i1,hi1⟩ : ∃ i1 : Fin 3, i1≠i0 := exists_ne i0
    have hh : M i0 j0*leftProduct M C i1 i1=
        M i1 j0*leftProduct M C i0 i1 := by
      simp only [leftProduct,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      have hm := CycleQ2SegreLocal.minors_of_cofactors_zero M hM i0 j0 i1 k
      linear_combination C i1 k*hm
    rw [hl i1 i1,hl i0 i1] at hh
    simpa [Ne.symm hi1] using hh
  · intro i0 j0
    obtain ⟨j1,hj1⟩ : ∃ j1 : Fin 3, j1≠j0 := exists_ne j0
    have hh : M i0 j0*rightProduct M C j1 j1=
        M i0 j1*rightProduct M C j0 j1 := by
      simp only [rightProduct,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      have hm := CycleQ2SegreLocal.minors_of_cofactors_zero M hM i0 j0 k j1
      linear_combination C k j1*hm
    rw [hr j1 j1,hr j0 j1] at hh
    simpa [Ne.symm hj1] using hh

theorem products_zero_of_entry_bezout (M C : Matrix (Fin 3) (Fin 3) R)
    (hM : CycleQ2SegreLocal.cofactors M=0) (hs : ScalarProducts M C)
    (ξ : Fin 3 × Fin 3 → R) (hξ : ∑ q, ξ q*M q.1 q.2=1) :
    (∀ i j, leftProduct M C i j=0) ∧ (∀ i j, rightProduct M C i j=0) := by
  obtain ⟨a,b,hl,hr⟩ := hs
  obtain ⟨ha,hb⟩ := entries_annihilate_scalars M C hM a b hl hr
  have hzero (x : R) (hx : ∀ i j, M i j*x=0) : x=0 := by
    have hh : (∑ q, ξ q*M q.1 q.2)*x=0 := by
      rw [Finset.sum_mul]
      apply Finset.sum_eq_zero
      intro q _
      rw [mul_assoc,hx,mul_zero]
    simpa only [hξ,one_mul] using hh
  have haz := hzero a ha
  have hbz := hzero b hb
  constructor
  · intro i j
    simp [hl,haz]
  · intro i j
    simp [hr,hbz]

/-- Removing the denominator from the pivot lift multiplies its image by
the pivot entry; the entry need not be a unit or a nonzero divisor. -/
theorem pivotLift_differential_scaled (M C : Matrix (Fin 3) (Fin 3) R)
    (hl : ∀ i j, leftProduct M C i j=0)
    (hr : ∀ i j, rightProduct M C i j=0) :
    cofactorDifferential M (pivotLift (1 : Rˣ) C)=M 0 0 • C := by
  have h01 := hl 0 1
  have h02 := hl 0 2
  have h11 := hl 1 1
  have h22 := hl 2 2
  have k00 := hr 0 0
  have k01 := hr 0 1
  have k02 := hr 0 2
  norm_num [leftProduct,rightProduct,Fin.sum_univ_succ] at h01 h02 h11 h22 k00 k01 k02
  have hfin2 (h : 2<3) : (⟨2,h⟩ : Fin 3)=2 := rfl
  have hn01 : (0 : Fin 3)≠1 := by decide
  have hn02 : (0 : Fin 3)≠2 := by decide
  have hn12 : (1 : Fin 3)≠2 := by decide
  have hn21 : (2 : Fin 3)≠1 := by decide
  rw [cofactorDifferential_fin_three]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [pivotLift,Matrix.cons_val_succ,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,
      Fin.reduceFinMk,hfin2,hn01,hn02,hn12,hn21] <;> solve
    | linear_combination h11+h22-k00
    | linear_combination -k01
    | linear_combination -k02
    | linear_combination -h01
    | linear_combination -h02

/-- The scaled lift on an arbitrary pivot, without inverting that entry. -/
theorem unitChartLift_differential_scaled (M C : Matrix (Fin 3) (Fin 3) R)
    (hl : ∀ i j, leftProduct M C i j=0)
    (hr : ∀ i j, rightProduct M C i j=0) (i0 j0 : Fin 3) :
    cofactorDifferential M (unitChartLift i0 j0 (1 : Rˣ) C)=M i0 j0 • C := by
  have hL (i j : Fin 3) :
      leftProduct (M.submatrix (rotation i0) (rotation j0))
        (C.submatrix (rotation i0) (rotation j0)) i j=0 := by
    rw [leftProduct_submatrix,hl]
  have hR (i j : Fin 3) :
      rightProduct (M.submatrix (rotation i0) (rotation j0))
        (C.submatrix (rotation i0) (rotation j0)) i j=0 := by
    rw [rightProduct_submatrix,hr]
  have hh := pivotLift_differential_scaled _ _ hL hR
  have hrot := differential_rotate M (unitChartLift i0 j0 (1 : Rˣ) C) i0 j0
  have hback : (unitChartLift i0 j0 (1 : Rˣ) C).submatrix (rotation i0) (rotation j0)=
      pivotLift (1 : Rˣ) (C.submatrix (rotation i0) (rotation j0)) := by
    ext i j
    simp [unitChartLift]
  rw [hback,hh] at hrot
  ext i j
  have hij := congrArg (fun A : Matrix (Fin 3) (Fin 3) R =>
    A ((rotation i0).symm i) ((rotation j0).symm j)) hrot
  simpa only [Matrix.submatrix_apply,Matrix.smul_apply,smul_eq_mul,
    rotation_zero,Equiv.apply_symm_apply] using hij.symm

def entryBezoutLift (ξ : Fin 3 × Fin 3 → R) (C : Matrix (Fin 3) (Fin 3) R) :
    Matrix (Fin 3) (Fin 3) R :=
  ∑ q, ξ q • unitChartLift q.1 q.2 (1 : Rˣ) C

/-- A Bézout combination of the nine denominator-free lifts is an actual
preimage under the cofactor differential. -/
theorem entryBezoutLift_differential (M C : Matrix (Fin 3) (Fin 3) R)
    (hl : ∀ i j, leftProduct M C i j=0)
    (hr : ∀ i j, rightProduct M C i j=0)
    (ξ : Fin 3 × Fin 3 → R) (hξ : ∑ q, ξ q*M q.1 q.2=1) :
    cofactorDifferential M (entryBezoutLift ξ C)=C := by
  change cofactorDifferentialLinear M (∑ q, ξ q • unitChartLift q.1 q.2 (1 : Rˣ) C)=C
  rw [map_sum]
  simp only [map_smul,cofactorDifferentialLinear,LinearMap.coe_mk,AddHom.coe_mk,
    unitChartLift_differential_scaled M C hl hr,smul_smul]
  rw [← Finset.sum_smul,hξ,one_smul]

/-- Global exactness from an explicit unity combination of the entries. -/
theorem entry_bezout_relations_exact (M C : Matrix (Fin 3) (Fin 3) R)
    (hM : CycleQ2SegreLocal.cofactors M=0)
    (ξ : Fin 3 × Fin 3 → R) (hξ : ∑ q, ξ q*M q.1 q.2=1) :
    CycleQ2SegreRelations.relations M *ᵥ vector C=0 ↔
      ∃ N : Matrix (Fin 3) (Fin 3) R, cofactorDifferential M N=C := by
  constructor
  · intro h
    obtain ⟨hl,hr⟩ := products_zero_of_entry_bezout M C hM
      ((relations_zero_iff_scalarProducts M C).mp h) ξ hξ
    exact ⟨entryBezoutLift ξ C,entryBezoutLift_differential M C hl hr ξ hξ⟩
  · rintro ⟨N,rfl⟩
    exact relations_cofactorDifferential M N hM

/-- The ideal formulation requires only that the nine actual matrix entries
span the unit ideal. It produces the Bézout coefficients, not a chosen pivot. -/
theorem entry_ideal_relations_exact (M C : Matrix (Fin 3) (Fin 3) R)
    (hM : CycleQ2SegreLocal.cofactors M=0)
    (hspan : Ideal.span (Set.range (fun q : Fin 3 × Fin 3 => M q.1 q.2))=⊤) :
    CycleQ2SegreRelations.relations M *ᵥ vector C=0 ↔
      ∃ N : Matrix (Fin 3) (Fin 3) R, cofactorDifferential M N=C := by
  have hmem : (1 : R) ∈ Ideal.span (Set.range (fun q : Fin 3 × Fin 3 => M q.1 q.2)) := by
    rw [hspan]
    exact Submodule.mem_top
  obtain ⟨ξ,hξ⟩ := Ideal.mem_span_range_iff_exists_fun.mp hmem
  exact entry_bezout_relations_exact M C hM ξ hξ

theorem entry_ideal_ker_eq_range (M : Matrix (Fin 3) (Fin 3) R)
    (hM : CycleQ2SegreLocal.cofactors M=0)
    (hspan : Ideal.span (Set.range (fun q : Fin 3 × Fin 3 => M q.1 q.2))=⊤) :
    LinearMap.ker (relationsLinear M)=LinearMap.range (cofactorDifferentialLinear M) := by
  ext C
  exact entry_ideal_relations_exact M C hM hspan

end CycleQ2SegreRelationsLocal

#print axioms CycleQ2SegreRelationsLocal.entries_annihilate_scalars
#print axioms CycleQ2SegreRelationsLocal.entry_bezout_relations_exact
#print axioms CycleQ2SegreRelationsLocal.entry_ideal_ker_eq_range
end
end


/- Component: continuation_3/SparseModularFunctional.lean -/
section
/-! Computable sparse coefficient functionals and their exact polynomial semantics.
The lookup tree is merely a function: no ordering or exhaustiveness assumption is used. -/
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2SparseModularFunctional
open MvPolynomial CycleQ2SparseGaussianPolynomial
abbrev F := ZMod 109
abbrev P := MvPolynomial (Fin 5) F

noncomputable section

def polyWeight (W : WeightData) (i j : Fin 3) (e : Fin 5 →₀ ℕ) : F :=
  (slot (W i j (e 4) (e 0)) (e 1 + 29 * e 2) : ℕ)

def functional (W : WeightData) (i j : Fin 3) : P →ₗ[F] F :=
  (Finsupp.linearCombination F (polyWeight W i j)).comp
    (AddMonoidAlgebra.coeffLinearEquiv F).toLinearMap

theorem cast_gmod (z : GaussianInt) :
    (gmod z : F) = CycleQ2IncidenceGaussianArithmetic.reduction z := by
  have hn : 0 ≤ (z.re + 33*z.im) % 109 := Int.emod_nonneg _ (by decide)
  rw [gmod, ← Int.cast_natCast, Int.toNat_of_nonneg hn]
  calc
    (((z.re + 33*z.im) % 109 : ℤ) : F) = ((z.re + 33*z.im : ℤ) : F) :=
      ZMod.intCast_mod _ 109
    _ = CycleQ2IncidenceGaussianArithmetic.reduction z := by
      simp [CycleQ2IncidenceGaussianArithmetic.reduction, Zsqrtd.lift_apply_apply]
      ring

theorem functional_monomial (W : WeightData) (i j : Fin 3)
    (e : Exponent) (c : F) :
    functional W i j (MvPolynomial.monomial (tupleExponent e) c) =
      c * (weight W i j e : F) := by
  change Finsupp.linearCombination F (polyWeight W i j)
    (Finsupp.single (tupleExponent e) c) = _
  rw [Finsupp.linearCombination_single]
  rfl

theorem cast_dot (W : WeightData) (i j : Fin 3) (s : Exponent) (p : Sparse) :
    (dot W i j s p : F) = functional W i j
      (eval (MvPolynomial.C.comp CycleQ2IncidenceGaussianArithmetic.reduction)
        (MvPolynomial.X : Fin 5 → P) (shift s p)) := by
  induction p with
  | nil => simp [dot,shift]
  | cons t p ih =>
    rw [dot]
    split_ifs with hc
    · rw [ih]
      simp only [shift,List.map_cons,eval_cons,map_add,termValue_variables,functional_monomial,
        hc,Nat.cast_zero,mul_zero,zero_add]
    · rw [ZMod.natCast_mod,Nat.cast_add,Nat.cast_mul,cast_gmod,ih]
      simp only [shift,List.map_cons,eval_cons,map_add,termValue_variables,functional_monomial]

 theorem cast_dot_product (W : WeightData) (i j : Fin 3) (s : Exponent) (p : Sparse) :
    (dot W i j s p : F) = functional W i j
      (MvPolynomial.monomial (tupleExponent s) 1 *
        eval (MvPolynomial.C.comp CycleQ2IncidenceGaussianArithmetic.reduction)
          (MvPolynomial.X : Fin 5 → P) p) := by
  rw [cast_dot,eval_shift,monomial_variables]

theorem flattenLayersData_eq (p : Layers) : flattenLayersData p=flattenLayers p := by
  induction p with
  | nil => rfl
  | cons a p ih => simp only [flattenLayersData,flattenLayers,ih]; rfl

theorem flattenBlocksData_eq (p : Blocks) : flattenBlocksData p=flattenBlocks p := by
  induction p with
  | nil => rfl
  | cons a p ih => simp only [flattenBlocksData,flattenBlocks,flattenLayersData_eq,ih]; rfl

theorem flattenTowersData_eq (p : Towers) : flattenTowersData p=flattenTowers p := by
  induction p with
  | nil => rfl
  | cons a p ih => simp only [flattenTowersData,flattenTowers,flattenBlocksData_eq,ih]; rfl

end
end CycleQ2SparseModularFunctional
#print axioms CycleQ2SparseModularFunctional.cast_dot_product
end


/- Component: continuation_3/CurveCechLocalizedBasis.lean -/
section
/-! # The actual localized curve quotients in six Laurent coordinates -/

noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2CurveCechLocalizedBasis

open MvPolynomial CycleQ2CurveRestriction CycleQ2CurveQuotientFiniteFree
  CycleQ2CurveCechTwoOpen CycleQ2CurveCechLocalization

variable (R : Type*) [CommRing R]

abbrev CurveLocal (side : Side) (r ι : R) (s : Finset (Fin 2)) :=
  Localization (Algebra.algebraMapSubmonoid (CurveRing side r ι)
    (Submonoid.powers (baseProduct R s)))

instance curveLocalBaseAlgebra (side : Side) (r ι : R) (s : Finset (Fin 2)) :
    Algebra (coordinateLocalization R s) (CurveLocal R side r ι s) :=
  localizationAlgebra (Rₘ := coordinateLocalization R s) (Sₘ := CurveLocal R side r ι s)
    (Submonoid.powers (baseProduct R s)) (CurveRing side r ι)

instance curveLocalBaseTower (side : Side) (r ι : R) (s : Finset (Fin 2)) :
    IsScalarTower (Base R) (coordinateLocalization R s) (CurveLocal R side r ι s) :=
  isScalarTower_localizationAlgebra (Rₘ := coordinateLocalization R s)
    (Sₘ := CurveLocal R side r ι s) (Submonoid.powers (baseProduct R s)) (CurveRing side r ι)

def localizedBasis [Nontrivial R] (side : Side) (r ι : R) (s : Finset (Fin 2)) :
    Module.Basis (ShiftIndex side) (coordinateLocalization R s) (CurveLocal R side r ι s) :=
  (curveBasis R side r ι).localizationLocalization (coordinateLocalization R s)
    (Submonoid.powers (baseProduct R s)) (CurveLocal R side r ι s)

@[simp] theorem localizedBasis_apply [Nontrivial R] (side : Side) (r ι : R)
    (s : Finset (Fin 2)) (ab : (ShiftIndex side)) :
    localizedBasis R side r ι s ab = algebraMap (CurveRing side r ι) (CurveLocal R side r ι s)
      (curveBasis R side r ι ab) := by
  exact Module.Basis.localizationLocalization_apply _ _ _ _ _

@[simp] theorem localizedBasis_repr_algebraMap [Nontrivial R] (side : Side) (r ι : R)
    (s : Finset (Fin 2)) (p : CurveRing side r ι) (ab : (ShiftIndex side)) :
    (localizedBasis R side r ι s).repr (algebraMap (CurveRing side r ι) (CurveLocal R side r ι s) p) ab =
      algebraMap (Base R) (coordinateLocalization R s) ((curveBasis R side r ι).repr p ab) := by
  exact Module.Basis.localizationLocalization_repr_algebraMap _ _ _ _ _ _

def localizedCoordinates [Nontrivial R] (side : Side) (r ι : R) (s : Finset (Fin 2)) :
    CurveLocal R side r ι s →+ ((ShiftIndex side) → Laurent (R := R)) where
  toFun p ab := localizationToLaurent R s ((localizedBasis R side r ι s).repr p ab)
  map_zero' := by ext ab; simp
  map_add' p q := by ext ab; simp

theorem localizedCoordinates_injective [Nontrivial R] (side : Side) (r ι : R) (s : Finset (Fin 2)) :
    Function.Injective (localizedCoordinates R side r ι s) := by
  intro p q hpq
  apply (localizedBasis R side r ι s).repr.injective
  ext ab
  exact localizationToLaurent_injective R s (congrFun hpq ab)

theorem localizedCoordinates_hasPoles [Nontrivial R] (side : Side) (r ι : R) (s : Finset (Fin 2))
    (p : CurveLocal R side r ι s) (ab : (ShiftIndex side)) :
    HasPoles s (localizedCoordinates R side r ι s p ab) :=
  localizationToLaurent_hasPoles R s _

theorem mem_range_localizedCoordinates [Nontrivial R] (side : Side) (r ι : R) (s : Finset (Fin 2))
    (p : (ShiftIndex side) → Laurent (R := R)) :
    p ∈ Set.range (localizedCoordinates R side r ι s) ↔ ∀ ab, HasPoles s (p ab) := by
  constructor
  · rintro ⟨p, rfl⟩ ab
    exact localizedCoordinates_hasPoles R side r ι s p ab
  · intro hp
    choose a ha using fun ab ↦ (mem_range_localizationToLaurent R s (p ab)).mpr (hp ab)
    refine ⟨(localizedBasis R side r ι s).repr.symm (Finsupp.equivFunOnFinite.symm a), ?_⟩
    funext ab
    change localizationToLaurent R s
      ((localizedBasis R side r ι s).repr ((localizedBasis R side r ι s).repr.symm
        (Finsupp.equivFunOnFinite.symm a)) ab) = p ab
    simpa using ha ab

@[simp] theorem localizedCoordinates_algebraMap [Nontrivial R] (side : Side) (r ι : R)
    (s : Finset (Fin 2)) (p : CurveRing side r ι) (ab : (ShiftIndex side)) :
    localizedCoordinates R side r ι s (algebraMap (CurveRing side r ι) (CurveLocal R side r ι s) p) ab =
      baseToLaurent R ((curveBasis R side r ι).repr p ab) := by
  simp [localizedCoordinates]

@[simp] theorem localizedCoordinates_smul [Nontrivial R] (side : Side) (r ι : R)
    (s : Finset (Fin 2)) (a : coordinateLocalization R s) (p : CurveLocal R side r ι s)
    (ab : (ShiftIndex side)) :
    localizedCoordinates R side r ι s (a • p) ab =
      localizationToLaurent R s a * localizedCoordinates R side r ι s p ab := by
  simp [localizedCoordinates, Finsupp.smul_apply, smul_eq_mul]

/-- All positive-degree overlap classes are actual coboundaries. -/
theorem localized_sixSummand_exact [Nontrivial R] (side : Side) (r ι : R)
    (d : ℤ) (hd : 2≤d) (p : CurveLocal R side r ι {0,1})
    (hg : ∀ ab,HasDegree ab d (localizedCoordinates R side r ι {0,1} p ab)) :
    ∃ (q0 : CurveLocal R side r ι {0}) (q1 : CurveLocal R side r ι {1}),
      (∀ ab,HasDegree ab d (localizedCoordinates R side r ι {0} q0 ab)) ∧
      (∀ ab,HasDegree ab d (localizedCoordinates R side r ι {1} q1 ab)) ∧
      localizedCoordinates R side r ι {0,1} p=
        localizedCoordinates R side r ι {1} q1-localizedCoordinates R side r ι {0} q0 := by
  obtain ⟨q0,q1,h0,h1,hg0,hg1,he⟩ :=
    sixSummand_exact side d hd (localizedCoordinates R side r ι {0,1} p) hg
  obtain ⟨q0',hq0⟩ := (mem_range_localizedCoordinates R side r ι {0} q0).mpr h0
  obtain ⟨q1',hq1⟩ := (mem_range_localizedCoordinates R side r ι {1} q1).mpr h1
  exact ⟨q0',q1',by simpa only [hq0] using hg0,by simpa only [hq1] using hg1,
    by simpa only [hq0,hq1] using he⟩

end CycleQ2CurveCechLocalizedBasis

#print axioms CycleQ2CurveCechLocalizedBasis.localized_sixSummand_exact
end
end


/- Component: continuation_3/CurveRestrictionSurjectivity.lean -/
section
/-! A proved nonzero minor of the actual normal-form coefficient map gives
surjectivity of the actual homogeneous curve restriction. -/

set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2CurveRestriction

open MvPolynomial CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations
  CycleQ2CurveRestrictionReflection

abbrev SourceTuple := CycleQ2SparseModularPolynomial.Exponent

def sourceGood (d ch : ℕ) (e : SourceTuple) : Bool :=
  decide (e.1+e.2.1+e.2.2.1+e.2.2.2.1+2*e.2.2.2.2=d ∧
    (2*e.1+2*e.2.1+e.2.2.1)%3=ch ∧ e.1<3 ∧ e.2.2.2.2<3)

def targetTuple {s : Side} {d : ℕ} (q : TargetIndex s d) : CurveTuple :=
  (targetCoordinates q 0,targetCoordinates q 1,targetCoordinates q 2,targetCoordinates q 3)

noncomputable section
variable {R : Type*} [CommRing R]

theorem tupleExponent_targetTuple {s : Side} {d : ℕ} (q : TargetIndex s d) :
    tupleExponent (targetTuple q)=targetExponent q := by
  ext i
  fin_cases i <;> rfl

theorem sourceGood_evaluation (d ch : ℕ) (e : SourceTuple) (he : sourceGood d ch e=true) :
    FullStandard (sourceMonomial e : MvPolynomial (Fin 5) R) ∧
      (sourceMonomial e : MvPolynomial (Fin 5) R).IsWeightedHomogeneous fullGrading (d,(ch:ZMod 3)) := by
  have h : e.1+e.2.1+e.2.2.1+e.2.2.2.1+2*e.2.2.2.2=d ∧
      (2*e.1+2*e.2.1+e.2.2.1)%3=ch ∧ e.1<3 ∧ e.2.2.2.2<3 := of_decide_eq_true he
  rw [sourceMonomial_eq_monomial]
  constructor
  · intro f hf
    obtain rfl := Finset.mem_singleton.mp (support_monomial_subset hf)
    exact h.2.2
  · apply isWeightedHomogeneous_monomial
    rw [fullGrading_weight]
    apply Prod.ext
    · exact h.1
    · have hc := congrArg (fun n : ℕ => (n:ZMod 3)) h.2.1
      change ((2*e.1+2*e.2.1+e.2.2.1:ℕ):ZMod 3)=(ch:ZMod 3)
      simpa using hc

theorem curve_standard_zero_of_coefficients {s : Side} {d : ℕ} {p : CurvePoly R}
    (hs : Standard s p) (hp : p.IsHomogeneous d)
    (hc : ∀ q : TargetIndex s d, p.coeff (targetExponent q)=0) : p=0 := by
  ext e
  simp only [coeff_zero]
  by_contra he
  have hb := hs e (mem_support_iff.mpr he)
  have hd : e.degree=d := by
    simpa only [Finsupp.degree_eq_weight_one,Pi.one_def] using hp he
  have hsum : e 0+e 1+e 2+e 3=d := by
    simpa [Finsupp.degree_eq_sum,Fin.sum_univ_succ,add_assoc] using hd
  let v : TargetExponents s d := ⟨e,hb.1,hb.2,hsum⟩
  let q : TargetIndex s d := (targetExponentEquiv s d).symm v
  have hq : targetExponent q=e := by
    ext i
    exact congrArg (fun z : TargetExponents s d => z.val i)
      ((targetExponentEquiv s d).apply_symm_apply v)
  exact he (hq ▸ hc q)

theorem standard_sub {s : Side} {p q : CurvePoly R}
    (hp : Standard s p) (hq : Standard s q) : Standard s (p-q) := by
  simpa only [map_neg,map_one,neg_one_mul,sub_eq_add_neg] using
    standard_add hp (standard_C_mul hq (-1))

theorem curve_standard_ext {s : Side} {d : ℕ} {p q : CurvePoly R}
    (hsp : Standard s p) (hsq : Standard s q)
    (hp : p.IsHomogeneous d) (hq : q.IsHomogeneous d)
    (hc : ∀ j : TargetIndex s d, p.coeff (targetExponent j)=q.coeff (targetExponent j)) : p=q := by
  apply sub_eq_zero.mp
  apply curve_standard_zero_of_coefficients (standard_sub hsp hsq) (hp.sub hq)
  intro j
  rw [coeff_sub,hc,sub_self]

section Field
variable {K : Type*} [Field K]

theorem polynomial_preimage_of_minor (s : Side) (r ι : K) (d ch n : ℕ)
    (rows : Fin n → CurveTuple) (columns : Fin n → SourceTuple)
    (hcover : ∀ q : TargetIndex s d, ∃ i, rows i=targetTuple q)
    (hcolumns : ∀ j, sourceGood d ch (columns j)=true)
    (hdet : Matrix.det (fun i j : Fin n => matrixCoefficient s r ι (rows i) (columns j))≠0)
    (p : CurvePoly K) (hp : p.IsHomogeneous d) :
    ∃ P : MvPolynomial (Fin 5) K, FullStandard P ∧
      P.IsWeightedHomogeneous fullGrading (d,(ch:ZMod 3)) ∧
      substitution s r P-p ∈ curveIdeal s r ι := by
  classical
  let A : Matrix (Fin n) (Fin n) K := fun i j => matrixCoefficient s r ι (rows i) (columns j)
  have hA : Function.Surjective A.mulVec :=
    Matrix.mulVec_surjective_iff_isUnit.mpr
      (A.isUnit_iff_isUnit_det.mpr ((isUnit_iff_ne_zero).mpr hdet))
  obtain ⟨v,hv⟩ := hA (fun i => (normal s r ι p).coeff (tupleExponent (rows i)))
  let P : MvPolynomial (Fin 5) K := ∑ j, v j • sourceMonomial (columns j)
  have hPstd : FullStandard P := by
    change P ∈ restrictSupport K {e : FullExponent | e 0<3 ∧ e 4<3}
    apply Submodule.sum_mem
    intro j hj
    exact Submodule.smul_mem _ _ (sourceGood_evaluation d ch (columns j) (hcolumns j)).1
  have hPgrade : P.IsWeightedHomogeneous fullGrading (d,(ch:ZMod 3)) := by
    apply (weightedHomogeneousSubmodule K fullGrading (d,(ch:ZMod 3))).sum_mem
    intro j hj
    exact Submodule.smul_mem _ _ (sourceGood_evaluation d ch (columns j) (hcolumns j)).2
  have hcoeff (i : Fin n) :
      (restrictionNormal s r ι P).coeff (tupleExponent (rows i))=
        (normal s r ι p).coeff (tupleExponent (rows i)) := by
    have hsum : (restrictionNormal s r ι P).coeff (tupleExponent (rows i))=
        A.mulVec v i := by
      simp only [P,map_sum,map_smul,coeff_sum,coeff_smul,RingHom.id_apply,
        Matrix.mulVec,dotProduct,A,matrixCoefficient]
      apply Finset.sum_congr rfl
      intro j hj
      exact mul_comm _ _
    exact hsum.trans (congrFun hv i)
  have hnormal : restrictionNormal s r ι P=normal s r ι p := by
    apply curve_standard_ext (normal_spec s r ι (substitution s r P)).1
      (normal_spec s r ι p).1
      (normal_homogeneous s r ι (substitution_homogeneous s r hPgrade))
      (normal_homogeneous s r ι hp)
    intro q
    obtain ⟨i,hi⟩ := hcover q
    have he : tupleExponent (rows i)=targetExponent q := by
      rw [hi,tupleExponent_targetTuple]
    rw [←he]
    exact hcoeff i
  refine ⟨P,hPstd,hPgrade,?_⟩
  have hsub := (curveIdeal s r ι).sub_mem
    (normal_sub_mem s r ι (substitution s r P)) (normal_sub_mem s r ι p)
  change normal s r ι (substitution s r P)=normal s r ι p at hnormal
  rw [hnormal] at hsub
  convert hsub using 1 <;> ring

theorem seedRestrictionPiece_surjective_of_minor (s : Side) (r ι : K) (d ch n : ℕ)
    (rows : Fin n → CurveTuple) (columns : Fin n → SourceTuple)
    (hcover : ∀ q : TargetIndex s d, ∃ i, rows i=targetTuple q)
    (hcolumns : ∀ j, sourceGood d ch (columns j)=true)
    (hdet : Matrix.det (fun i j : Fin n => matrixCoefficient s r ι (rows i) (columns j))≠0) :
    Function.Surjective (seedRestrictionPiece s r ι d ch) := by
  intro q
  obtain ⟨p,hp,hpq⟩ := Submodule.mem_map.mp q.property
  obtain ⟨P,_,hP,hcong⟩ := polynomial_preimage_of_minor s r ι d ch n rows columns hcover hcolumns hdet p hp
  let qP : SeedPiece r ι d ch := ⟨Ideal.Quotient.mk (equationsIdeal (smoothH ι) (smoothF r ι)) P,
    Submodule.mem_map.mpr ⟨P,hP,rfl⟩⟩
  refine ⟨qP,Subtype.ext ?_⟩
  change seedRestriction s r ι (Ideal.Quotient.mk (equationsIdeal (smoothH ι) (smoothF r ι)) P)=q.val
  rw [seedRestriction_mk]
  exact (Ideal.Quotient.eq.mpr hcong).trans hpq

end Field
end
end CycleQ2CurveRestriction

#print axioms CycleQ2CurveRestriction.polynomial_preimage_of_minor
#print axioms CycleQ2CurveRestriction.seedRestrictionPiece_surjective_of_minor
end


/- Component: continuation_3/HomogeneousIdealArithmetic.lean -/
section
/-!
# Finite coefficient maps for homogeneous ideal membership

The actual full weighted-degree/character pieces are used throughout.
Homogeneous projection removes any bound assumption on the original ideal
membership witnesses. Coefficient-map naturality then permits arithmetic
surjectivity transfer for the complete finite multiplication map.
-/

noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2HomogeneousIdealArithmetic

open MvPolynomial Matrix CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations
open scoped BigOperators

variable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι]

abbrev Column (N : ℕ) (degree : ι → ℕ) := (j : ι) × FullInvariantIndex (N-degree j)

def generatorIdeal (g : ι → Poly R) : Ideal (Poly R) := Ideal.span (Set.range g)

theorem homogeneous_map {S : Type*} [CommRing S] (φ : R →+* S)
    {p : Poly R} {d : Grade} (hp : HG p d) : HG (MvPolynomial.map φ p) d := by
  intro e he
  apply hp
  intro hz
  exact he (by rw [coeff_map, hz, map_zero])

theorem homogeneous_membership (g : ι → Poly R) (degree : ι → ℕ)
    (hgen : ∀ j, HG (g j) (degree j,0)) (N : ℕ) (hle : ∀ j, degree j ≤ N)
    (p : Poly R) (hp : HG p (N,0)) (hmem : p ∈ generatorIdeal g) :
    ∃ u : ι → Poly R, (∀ j, HG (u j) (N-degree j,0)) ∧
      p = ∑ j, g j*u j := by
  classical
  obtain ⟨u, hu⟩ := Ideal.mem_span_range_iff_exists_fun.mp hmem
  let v : ι → Poly R := fun j => weightedHomogeneousComponent fullGrading (N-degree j,0) (u j)
  refine ⟨v, fun j => weightedHomogeneousComponent_isWeightedHomogeneous _ _, ?_⟩
  have hh := congrArg (weightedHomogeneousComponent fullGrading (N,0)) hu
  rw [hp.weightedHomogeneousComponent_same, map_sum] at hh
  have hc (j : ι) : weightedHomogeneousComponent fullGrading (N,0) (u j*g j) = g j*v j := by
    have hd : (N, (0 : ZMod 3)) = (N-degree j,0)+(degree j,0) := by
      apply Prod.ext <;> simp [Nat.sub_add_cancel (hle j)]
    rw [hd, CycleQ2WeightedComponent.component_mul _ _ _ _ _ (hgen j)]
    exact mul_comm _ _
  simpa only [hc] using hh.symm

def multiplicationMatrix (g : ι → Poly R) (degree : ι → ℕ) (N : ℕ) :
    Matrix (FullInvariantIndex N) (Column N degree) R :=
  Matrix.of fun e q => (g q.1 * monomial (fullExponentOf q.2.val) 1).coeff
    (fullExponentOf e.val)

def multiplierPolynomial (g : ι → Poly R) (degree : ι → ℕ) (N : ℕ)
    (c : Column N degree → R) : Poly R :=
  ∑ j, g j * fullInvariantPolynomial (N-degree j) (fun e => c ⟨j,e⟩)

theorem coeff_mul_monomial_scalar (p : Poly R) (a e : FullExponent) (c : R) :
    (p*monomial a c).coeff e = (p*monomial a 1).coeff e*c := by
  have hm : (monomial a c : Poly R) = C c * monomial a 1 := by
    simp only [C_mul_monomial, mul_one]
  rw [hm, ← mul_assoc, mul_comm p (C c), mul_assoc, coeff_C_mul]
  exact mul_comm _ _

theorem multiplicationMatrix_mulVec (g : ι → Poly R) (degree : ι → ℕ) (N : ℕ)
    (c : Column N degree → R) (e : FullInvariantIndex N) :
    (multiplicationMatrix g degree N *ᵥ c) e =
      (multiplierPolynomial g degree N c).coeff (fullExponentOf e.val) := by
  classical
  simp only [Matrix.mulVec, dotProduct, multiplicationMatrix, Matrix.of_apply,
    Fintype.sum_sigma, multiplierPolynomial, coeff_sum, fullInvariantPolynomial,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro a _
  exact (coeff_mul_monomial_scalar _ _ _ _).symm

theorem multiplierPolynomial_homogeneous (g : ι → Poly R) (degree : ι → ℕ)
    (hgen : ∀ j, HG (g j) (degree j,0)) (N : ℕ) (hle : ∀ j, degree j ≤ N)
    (c : Column N degree → R) : HG (multiplierPolynomial g degree N c) (N,0) := by
  apply (weightedHomogeneousSubmodule R fullGrading (N,0)).sum_mem
  intro j _
  change HG (g j * fullInvariantPolynomial (N-degree j) (fun e => c ⟨j,e⟩)) (N,0)
  have h := (hgen j).mul (fullInvariantPolynomial_homogeneous (N-degree j) (fun e => c ⟨j,e⟩))
  simpa only [Prod.mk_add_mk, add_zero, Nat.add_sub_of_le (hle j)] using h

theorem multiplication_surjective_of_membership (g : ι → Poly R) (degree : ι → ℕ)
    (hgen : ∀ j, HG (g j) (degree j,0)) (N : ℕ) (hle : ∀ j, degree j ≤ N)
    (hmem : ∀ p : Poly R, HG p (N,0) → p ∈ generatorIdeal g) :
    Function.Surjective (multiplicationMatrix g degree N).mulVec := by
  classical
  intro b
  let p := fullInvariantPolynomial N b
  have hp := fullInvariantPolynomial_homogeneous N b
  obtain ⟨u, hu, heq⟩ := homogeneous_membership g degree hgen N hle p hp (hmem p hp)
  let c : Column N degree → R := fun q => (u q.1).coeff (fullExponentOf q.2.val)
  have hc : multiplierPolynomial g degree N c = p := by
    rw [heq]
    apply Finset.sum_congr rfl
    intro j _
    rw [fullInvariantPolynomial_of_homogeneous (hu j)]
  refine ⟨c, ?_⟩
  funext e
  rw [multiplicationMatrix_mulVec, hc]
  exact fullInvariantPolynomial_coeff N b e

theorem membership_of_multiplication_surjective (g : ι → Poly R) (degree : ι → ℕ)
    (hgen : ∀ j, HG (g j) (degree j,0)) (N : ℕ) (hle : ∀ j, degree j ≤ N)
    (hs : Function.Surjective (multiplicationMatrix g degree N).mulVec)
    (p : Poly R) (hp : HG p (N,0)) : p ∈ generatorIdeal g := by
  classical
  obtain ⟨c, hc⟩ := hs (fun e => p.coeff (fullExponentOf e.val))
  have heq : multiplierPolynomial g degree N c = p := by
    rw [← fullInvariantPolynomial_of_homogeneous
      (multiplierPolynomial_homogeneous g degree hgen N hle c),
      ← fullInvariantPolynomial_of_homogeneous hp]
    congr 1
    funext e
    rw [← multiplicationMatrix_mulVec]
    exact congrFun hc e
  rw [← heq]
  apply Ideal.sum_mem
  intro j _
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_range_self j))

theorem multiplicationMatrix_map {S : Type*} [CommRing S] (φ : R →+* S)
    (g : ι → Poly R) (degree : ι → ℕ) (N : ℕ) :
    (multiplicationMatrix g degree N).map φ =
      multiplicationMatrix (fun j => MvPolynomial.map φ (g j)) degree N := by
  ext e q
  simp only [multiplicationMatrix, Matrix.map_apply, Matrix.of_apply,
    ← coeff_map, map_mul, map_monomial, map_one]

/-- Complete homogeneous-piece membership transfers from a proved modular
surjectivity statement to a faithful characteristic-zero specialization. -/
theorem gaussian_membership_transfer (g : ι → Poly GaussianInt) (degree : ι → ℕ)
    (hgen : ∀ j, HG (g j) (degree j,0)) (N : ℕ) (hle : ∀ j, degree j ≤ N)
    (hmod : ∀ p : Poly (ZMod 109), HG p (N,0) → p ∈ generatorIdeal
      (fun j => MvPolynomial.map CycleQ2IncidenceGaussianArithmetic.reduction (g j)))
    (p : Poly ℂ) (hp : HG p (N,0)) :
    p ∈ generatorIdeal (fun j => MvPolynomial.map GaussianInt.toComplex (g j)) := by
  classical
  have hs := multiplication_surjective_of_membership _ degree
    (fun j => homogeneous_map _ (hgen j)) N hle hmod
  rw [← multiplicationMatrix_map] at hs
  have ht := CycleQ2ArithmeticSurjectivity.gaussian (multiplicationMatrix g degree N) hs
  rw [multiplicationMatrix_map] at ht
  exact membership_of_multiplication_surjective _ degree
    (fun j => homogeneous_map _ (hgen j)) N hle ht p hp

end CycleQ2HomogeneousIdealArithmetic

#print axioms CycleQ2HomogeneousIdealArithmetic.homogeneous_membership
#print axioms CycleQ2HomogeneousIdealArithmetic.multiplication_surjective_of_membership
#print axioms CycleQ2HomogeneousIdealArithmetic.gaussian_membership_transfer
end
end


/- Component: continuation_3/SeedCechRestrictions.lean -/
section
/-! # Canonical restriction maps and the actual coordinate Čech kernel -/

noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2SeedCechRestrictions

open MvPolynomial CycleQ2SegreTangentLocal CycleQ2SeedQuotientFiniteFree
  CycleQ2SeedCechThreeOpen CycleQ2SeedCechLocalization CycleQ2SeedCechLocalizedBasis

variable (R : Type*) [CommRing R]

instance seedLocalAway (r ι : R) (s : Finset (Fin 3)) :
    IsLocalization.Away (algebraMap (Base R) (SeedRing r ι) (baseProduct R s))
      (SeedLocal R r ι s) := by
  have hh : Algebra.algebraMapSubmonoid (SeedRing r ι)
      (Submonoid.powers (baseProduct R s)) =
      Submonoid.powers (algebraMap (Base R) (SeedRing r ι) (baseProduct R s)) := by
    exact Submonoid.map_powers _ _
  rw [IsLocalization.Away, ← hh]
  infer_instance

theorem baseProduct_dvd {s t : Finset (Fin 3)} (hst : s ⊆ t) :
    baseProduct R s ∣ baseProduct R t :=
  Finset.prod_dvd_prod_of_subset s t (fun i ↦ X i) hst

theorem seedProduct_isUnit (r ι : R) {s t : Finset (Fin 3)} (hst : s ⊆ t) :
    IsUnit (algebraMap (SeedRing r ι) (SeedLocal R r ι t)
      (algebraMap (Base R) (SeedRing r ι) (baseProduct R s))) := by
  apply IsLocalization.Away.isUnit_of_dvd (S := SeedLocal R r ι t)
    (algebraMap (Base R) (SeedRing r ι) (baseProduct R t))
  exact map_dvd (algebraMap (Base R) (SeedRing r ι)) (baseProduct_dvd R hst)

/-- The universal localization map, with no chosen Laurent inverse. -/
def restriction (r ι : R) {s t : Finset (Fin 3)} (hst : s ⊆ t) :
    SeedLocal R r ι s →+* SeedLocal R r ι t :=
  IsLocalization.Away.lift
    (S := SeedLocal R r ι s)
    (P := SeedLocal R r ι t)
    (g := algebraMap (SeedRing r ι) (SeedLocal R r ι t))
    (algebraMap (Base R) (SeedRing r ι) (baseProduct R s))
    (seedProduct_isUnit R r ι hst)

@[simp] theorem restriction_algebraMap (r ι : R) {s t : Finset (Fin 3)} (hst : s ⊆ t)
    (p : SeedRing r ι) :
    restriction R r ι hst (algebraMap (SeedRing r ι) (SeedLocal R r ι s) p) =
      algebraMap (SeedRing r ι) (SeedLocal R r ι t) p :=
  IsLocalization.Away.lift_eq (S := SeedLocal R r ι s)
    (P := SeedLocal R r ι t) _ (seedProduct_isUnit R r ι hst) p

theorem coordinates_mul_base [Nontrivial R] (r ι : R) (s : Finset (Fin 3))
    (p : SeedLocal R r ι s) (c : Base R) (ab : ShiftIndex) :
    localizedCoordinates R r ι s
      (p * algebraMap (SeedRing r ι) (SeedLocal R r ι s)
        (algebraMap (Base R) (SeedRing r ι) c)) ab =
      baseToLaurent R c * localizedCoordinates R r ι s p ab := by
  rw [← IsScalarTower.algebraMap_apply (Base R) (SeedRing r ι) (SeedLocal R r ι s) c,
    IsScalarTower.algebraMap_apply (Base R) (coordinateLocalization R s) (SeedLocal R r ι s) c,
    mul_comm p, ← Algebra.smul_def]
  rw [localizedCoordinates_smul, localizationToLaurent_algebraMap]

/-- Canonical restriction becomes literal inclusion in common Laurent coordinates. -/
theorem coordinates_restriction [Nontrivial R] (r ι : R)
    {s t : Finset (Fin 3)} (hst : s ⊆ t) (z : SeedLocal R r ι s) (ab : ShiftIndex) :
    localizedCoordinates R r ι t (restriction R r ι hst z) ab =
      localizedCoordinates R r ι s z ab := by
  obtain ⟨n, p, hp⟩ := IsLocalization.Away.surj
    (algebraMap (Base R) (SeedRing r ι) (baseProduct R s)) z
  have hp' : z * algebraMap (SeedRing r ι) (SeedLocal R r ι s)
      (algebraMap (Base R) (SeedRing r ι) (baseProduct R s ^ n)) =
      algebraMap (SeedRing r ι) (SeedLocal R r ι s) p := by
    simpa only [map_pow] using hp
  have hs := congrArg (fun z ↦ localizedCoordinates R r ι s z ab) hp'
  simp only [coordinates_mul_base, localizedCoordinates_algebraMap] at hs
  have ht := congrArg (restriction R r ι hst) hp'
  simp only [map_mul, restriction_algebraMap] at ht
  have ht' := congrArg (fun z ↦ localizedCoordinates R r ι t z ab) ht
  simp only [coordinates_mul_base, localizedCoordinates_algebraMap] at ht'
  have hu : IsUnit (baseToLaurent R (baseProduct R s ^ n)) := by
    rw [map_pow, baseToLaurent_baseProduct]
    exact (T_isUnit R _).pow n
  exact hu.mul_right_injective (ht'.trans hs.symm)

/-- Every graded one-cocycle for the canonical three-coordinate localization
complex of the actual seed quotient is an actual coboundary. -/
theorem coordinateCech_exact [Nontrivial R] (r ι : R) (g : LaurentGrade)
    (p01 : SeedLocal R r ι {0, 1}) (p02 : SeedLocal R r ι {0, 2})
    (p12 : SeedLocal R r ι {1, 2})
    (hg01 : ∀ ab, HasGrade ab g (localizedCoordinates R r ι {0, 1} p01 ab))
    (hg02 : ∀ ab, HasGrade ab g (localizedCoordinates R r ι {0, 2} p02 ab))
    (hg12 : ∀ ab, HasGrade ab g (localizedCoordinates R r ι {1, 2} p12 ab))
    (hc : restriction R r ι (show ({0, 1} : Finset (Fin 3)) ⊆ Finset.univ by decide) p01 -
      restriction R r ι (show ({0, 2} : Finset (Fin 3)) ⊆ Finset.univ by decide) p02 +
      restriction R r ι (show ({1, 2} : Finset (Fin 3)) ⊆ Finset.univ by decide) p12 = 0) :
    ∃ (q0 : SeedLocal R r ι {0}) (q1 : SeedLocal R r ι {1})
      (q2 : SeedLocal R r ι {2}),
      (∀ ab, HasGrade ab g (localizedCoordinates R r ι {0} q0 ab)) ∧
      (∀ ab, HasGrade ab g (localizedCoordinates R r ι {1} q1 ab)) ∧
      (∀ ab, HasGrade ab g (localizedCoordinates R r ι {2} q2 ab)) ∧
      p01 = restriction R r ι (show ({1} : Finset (Fin 3)) ⊆ {0, 1} by decide) q1 -
        restriction R r ι (show ({0} : Finset (Fin 3)) ⊆ {0, 1} by decide) q0 ∧
      p02 = restriction R r ι (show ({2} : Finset (Fin 3)) ⊆ {0, 2} by decide) q2 -
        restriction R r ι (show ({0} : Finset (Fin 3)) ⊆ {0, 2} by decide) q0 ∧
      p12 = restriction R r ι (show ({2} : Finset (Fin 3)) ⊆ {1, 2} by decide) q2 -
        restriction R r ι (show ({1} : Finset (Fin 3)) ⊆ {1, 2} by decide) q1 := by
  have hc' (ab : ShiftIndex) : localizedCoordinates R r ι {0, 1} p01 ab -
      localizedCoordinates R r ι {0, 2} p02 ab +
      localizedCoordinates R r ι {1, 2} p12 ab = 0 := by
    have hh := congrArg (fun z ↦ localizedCoordinates R r ι Finset.univ z ab) hc
    simpa only [map_add, map_sub, map_zero, Pi.add_apply, Pi.sub_apply, Pi.zero_apply,
      coordinates_restriction] using hh
  obtain ⟨q0, q1, q2, hg0, hg1, hg2, he01, he02, he12⟩ :=
    localized_nineSummand_kernel R r ι g p01 p02 p12 hg01 hg02 hg12 hc'
  refine ⟨q0, q1, q2, hg0, hg1, hg2, ?_, ?_, ?_⟩
  · apply localizedCoordinates_injective R r ι {0, 1}
    funext ab
    simpa only [map_sub, Pi.sub_apply, coordinates_restriction] using he01 ab
  · apply localizedCoordinates_injective R r ι {0, 2}
    funext ab
    simpa only [map_sub, Pi.sub_apply, coordinates_restriction] using he02 ab
  · apply localizedCoordinates_injective R r ι {1, 2}
    funext ab
    simpa only [map_sub, Pi.sub_apply, coordinates_restriction] using he12 ab

end CycleQ2SeedCechRestrictions

#print axioms CycleQ2SeedCechRestrictions.coordinateCech_exact
end
end


/- Component: continuation_3/SeedCechTopCohomology.lean -/
section
/-!
# The seven-dimensional top coordinate Čech quotient

The quotient by the three pair-open images keeps exactly the monomials whose
three base exponents are all negative. In total degree zero and invariant
character, the actual nine shifts leave precisely seven such monomials.
-/

noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2SeedCechTopCohomology

open CycleQ2SeedCechThreeOpen
open scoped BigOperators

abbrev SmallExponents := Fin 4 × Fin 4 × Fin 4

def topExponent (e : SmallExponents) : LaurentExponent :=
  ![-((e.1.val : ℤ) + 1), -((e.2.1.val : ℤ) + 1), -((e.2.2.val : ℤ) + 1)]

abbrev TopIndex := {q : ShiftIndex × SmallExponents // shiftedGrade q.1 (topExponent q.2) = 0}

theorem topIndex_count : Fintype.card TopIndex = 7 := by decide

theorem topExponent_negative (e : SmallExponents) (i : Fin 3) : topExponent e i < 0 := by
  fin_cases i
  · change -((e.1.val : ℤ) + 1) < 0; omega
  · change -((e.2.1.val : ℤ) + 1) < 0; omega
  · change -((e.2.2.val : ℤ) + 1) < 0; omega

theorem topExponent_injective : Function.Injective topExponent := by
  intro a b hab
  have h0 := congrFun hab 0
  have h1 := congrFun hab 1
  have h2 := congrFun hab 2
  change -((a.1.val : ℤ) + 1) = -((b.1.val : ℤ) + 1) at h0
  change -((a.2.1.val : ℤ) + 1) = -((b.2.1.val : ℤ) + 1) at h1
  change -((a.2.2.val : ℤ) + 1) = -((b.2.2.val : ℤ) + 1) at h2
  apply Prod.ext
  · apply Fin.ext; omega
  · apply Prod.ext <;> apply Fin.ext <;> omega

def topCoordinate (q : TopIndex) : ShiftIndex × LaurentExponent := (q.val.1, topExponent q.val.2)

theorem topCoordinate_injective : Function.Injective topCoordinate := by
  intro a b hab
  apply Subtype.ext
  apply Prod.ext
  · exact congrArg (fun q : ShiftIndex × LaurentExponent ↦ q.1) hab
  · exact topExponent_injective
      (congrArg (fun q : ShiftIndex × LaurentExponent ↦ q.2) hab)

/-- Completeness of the finite index, derived from actual degree zero. -/
theorem exists_topIndex (ab : ShiftIndex) (e : LaurentExponent)
    (he : ∀ i, e i < 0) (hg : shiftedGrade ab e = 0) :
    ∃ q : TopIndex, topCoordinate q = (ab, e) := by
  have hd := congrArg Prod.fst hg
  change (ab.1.val : ℤ) + 2 * ab.2.val + ∑ i, e i = 0 at hd
  rw [Fin.sum_univ_three] at hd
  have ha := ab.1.isLt
  have hb := ab.2.isLt
  have h0 := he 0
  have h1 := he 1
  have h2 := he 2
  have bounds (i : Fin 3) : (-e i - 1).toNat < 4 := by
    fin_cases i
    · change (-e 0 - 1).toNat < 4; omega
    · change (-e 1 - 1).toNat < 4; omega
    · change (-e 2 - 1).toNat < 4; omega
  let v : SmallExponents :=
    (⟨(-e 0 - 1).toNat, bounds 0⟩,
     ⟨(-e 1 - 1).toNat, bounds 1⟩,
     ⟨(-e 2 - 1).toNat, bounds 2⟩)
  have hv : topExponent v = e := by
    ext i
    fin_cases i
    · change -(((-e 0 - 1).toNat : ℤ) + 1) = e 0; omega
    · change -(((-e 1 - 1).toNat : ℤ) + 1) = e 1; omega
    · change -(((-e 2 - 1).toNat : ℤ) + 1) = e 2; omega
  refine ⟨⟨(ab, v), ?_⟩, ?_⟩
  · simpa only [hv] using hg
  · exact Prod.ext rfl hv

variable (R : Type*) [CommRing R]

abbrev Family := ShiftIndex → Laurent (R := R)

def gradedFamilies : Submodule R (Family R) where
  carrier := {p | ∀ ab, HasGrade ab 0 (p ab)}
  zero_mem' := by intro ab e he; simp
  add_mem' hp hq ab := hasGrade_add ab 0 (hp ab) (hq ab)
  smul_mem' c p hp ab := by
    intro e he
    simp [AddMonoidAlgebra.coeff_smul, Finsupp.smul_apply, hp ab e he]

def topProjection : gradedFamilies R →ₗ[R] (TopIndex →₀ R) where
  toFun p := Finsupp.equivFunOnFinite.symm
    (fun q ↦ (p.val q.val.1).coeff (topExponent q.val.2))
  map_add' p q := by ext i; simp [AddMonoidAlgebra.coeff_add]
  map_smul' c p := by ext i; simp [AddMonoidAlgebra.coeff_smul]

@[simp] theorem topProjection_apply (p : gradedFamilies R) (q : TopIndex) :
    topProjection R p q = (p.val q.val.1).coeff (topExponent q.val.2) := rfl

def basisFamily (q : TopIndex) : Family R := fun ab ↦
  if ab = q.val.1 then AddMonoidAlgebra.single (topExponent q.val.2) 1 else 0

@[simp] theorem basisFamily_coeff (q : TopIndex) (ab : ShiftIndex) (e : LaurentExponent) :
    (basisFamily R q ab).coeff e = if topCoordinate q = (ab, e) then 1 else 0 := by
  classical
  by_cases ha : ab = q.val.1
  · subst ab
    by_cases he : e = topExponent q.val.2
    · subst e; simp [basisFamily, topCoordinate]
    · simp [basisFamily, topCoordinate, he, Ne.symm he]
  · have ha' : q.val.1 ≠ ab := Ne.symm ha
    simp [basisFamily, topCoordinate, ha, ha']

def basisSection (q : TopIndex) : gradedFamilies R := ⟨basisFamily R q, by
  intro ab e he
  rw [basisFamily_coeff]
  split
  · next h =>
      have ha : q.val.1 = ab := congrArg Prod.fst h
      have h_exp : topExponent q.val.2 = e := congrArg Prod.snd h
      exact False.elim (he (ha ▸ h_exp ▸ q.property))
  · rfl⟩

@[simp] theorem topProjection_basisSection (q : TopIndex) :
    topProjection R (basisSection R q) = Finsupp.single q 1 := by
  ext j
  change (basisFamily R q j.val.1).coeff (topExponent j.val.2) = _
  rw [basisFamily_coeff]
  change (if topCoordinate q = topCoordinate j then 1 else 0) = _
  simp only [topCoordinate_injective.eq_iff, Finsupp.single_apply]

theorem topProjection_surjective : Function.Surjective (topProjection R) := by
  intro p
  refine ⟨∑ q : TopIndex, p q • basisSection R q, ?_⟩
  ext q
  simp

def poleSubmodule (s : Finset (Fin 3)) : Submodule R (gradedFamilies R) where
  carrier := {p | ∀ ab, HasPoles s (p.val ab)}
  zero_mem' := by intro ab e i hi hneg; simp
  add_mem' hp hq := by
    intro ab e i hi hneg
    simp [AddMonoidAlgebra.coeff_add, hp ab e i hi hneg, hq ab e i hi hneg]
  smul_mem' c p hp := by
    intro ab e i hi hneg
    simp [AddMonoidAlgebra.coeff_smul, hp ab e i hi hneg]

/-- The sum of the three pair-open images in the triple-open graded space. -/
def topBoundary : Submodule R (gradedFamilies R) :=
  poleSubmodule R {0, 1} ⊔ poleSubmodule R {0, 2} ⊔ poleSubmodule R {1, 2}

theorem topProjection_zero_iff (p : gradedFamilies R) :
    topProjection R p = 0 ↔
      ∀ ab e, (∀ i, e i < 0) → (p.val ab).coeff e = 0 := by
  constructor
  · intro hp ab e he
    by_cases hg : shiftedGrade ab e = 0
    · obtain ⟨q, hq⟩ := exists_topIndex ab e he hg
      have ha : q.val.1 = ab := congrArg Prod.fst hq
      have hx : topExponent q.val.2 = e := congrArg Prod.snd hq
      have hh := congrArg (fun f : TopIndex →₀ R ↦ f q) hp
      simpa only [topProjection_apply, ha, hx, Finsupp.zero_apply] using hh
    · exact p.property ab e hg
  · intro hp
    ext q
    exact hp q.val.1 (topExponent q.val.2) (topExponent_negative q.val.2)

theorem poleSubmodule_le_ker (s : Finset (Fin 3)) (i : Fin 3) (hi : i ∉ s) :
    poleSubmodule R s ≤ LinearMap.ker (topProjection R) := by
  intro p hp
  rw [LinearMap.mem_ker, topProjection_zero_iff]
  intro ab e he
  exact hp ab e i hi (he i)

theorem topBoundary_le_ker : topBoundary R ≤ LinearMap.ker (topProjection R) :=
  sup_le (sup_le (poleSubmodule_le_ker R {0, 1} 2 (by decide))
    (poleSubmodule_le_ker R {0, 2} 1 (by decide)))
      (poleSubmodule_le_ker R {1, 2} 0 (by decide))

def filterSection (P : LaurentExponent → Prop) [DecidablePred P]
    (p : gradedFamilies R) : gradedFamilies R :=
  ⟨fun ab ↦ AddMonoidAlgebra.ofCoeff ((p.val ab).coeff.filter P), by
    intro ab e he
    change (if P e then (p.val ab).coeff e else 0) = 0
    split <;> simp [p.property ab e he]⟩

@[simp] theorem filterSection_coeff (P : LaurentExponent → Prop) [DecidablePred P]
    (p : gradedFamilies R) (ab : ShiftIndex) (e : LaurentExponent) :
    ((filterSection R P p).val ab).coeff e = if P e then (p.val ab).coeff e else 0 := rfl

theorem filterSection_mem_poleSubmodule (P : LaurentExponent → Prop) [DecidablePred P]
    (s : Finset (Fin 3))
    (hP : ∀ e, P e → ∀ i, i ∉ s → 0 ≤ e i) (p : gradedFamilies R) :
    filterSection R P p ∈ poleSubmodule R s := by
  intro ab e i hi hneg
  rw [filterSection_coeff]
  split
  · next he => exact False.elim ((not_le.mpr hneg) (hP e he i hi))
  · rfl

/-- Projection onto negative exponents loses exactly the three pair-open images. -/
theorem topBoundary_eq_ker : topBoundary R = LinearMap.ker (topProjection R) := by
  apply le_antisymm (topBoundary_le_ker R)
  intro p hp
  have hz := (topProjection_zero_iff R p).mp hp
  let p01 := filterSection R (fun e ↦ 0 ≤ e 2) p
  let p02 := filterSection R (fun e ↦ e 2 < 0 ∧ 0 ≤ e 1) p
  let p12 := filterSection R (fun e ↦ e 2 < 0 ∧ e 1 < 0 ∧ 0 ≤ e 0) p
  have h01 : p01 ∈ poleSubmodule R {0, 1} := by
    apply filterSection_mem_poleSubmodule
    intro e he i hi
    fin_cases i
    · simp at hi
    · simp at hi
    · exact he
  have h02 : p02 ∈ poleSubmodule R {0, 2} := by
    apply filterSection_mem_poleSubmodule
    intro e he i hi
    fin_cases i
    · simp at hi
    · exact he.2
    · simp at hi
  have h12 : p12 ∈ poleSubmodule R {1, 2} := by
    apply filterSection_mem_poleSubmodule
    intro e he i hi
    fin_cases i
    · exact he.2.2
    · simp at hi
    · simp at hi
  have heq : p = p01 + p02 + p12 := by
    apply Subtype.ext
    funext ab
    apply AddMonoidAlgebra.ext
    ext e
    change (p.val ab).coeff e =
      ((p01.val ab + p02.val ab + p12.val ab).coeff e)
    simp only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
      p01, p02, p12, filterSection_coeff]
    by_cases h2 : 0 ≤ e 2
    · simp [h2, not_lt.mpr h2]
    · by_cases h1 : 0 ≤ e 1
      · simp [lt_of_not_ge h2, h1, not_lt.mpr h1]
      · by_cases h0 : 0 ≤ e 0
        · simp [h2, h1, lt_of_not_ge h2, lt_of_not_ge h1, h0]
        · have hn : ∀ i, e i < 0 := by
            intro i
            fin_cases i
            · exact lt_of_not_ge h0
            · exact lt_of_not_ge h1
            · exact lt_of_not_ge h2
          simp [lt_of_not_ge h2, lt_of_not_ge h1, h0, hz ab e hn]
  rw [heq]
  apply Submodule.add_mem
  · apply Submodule.add_mem
    · exact (show poleSubmodule R {0, 1} ≤ topBoundary R from
        le_sup_of_le_left le_sup_left) h01
    · exact (show poleSubmodule R {0, 2} ≤ topBoundary R from
        le_sup_of_le_left le_sup_right) h02
  · exact (show poleSubmodule R {1, 2} ≤ topBoundary R from le_sup_right) h12

abbrev TopCechQuotient := gradedFamilies R ⧸ topBoundary R

def topCechEquiv : TopCechQuotient R ≃ₗ[R] (TopIndex →₀ R) :=
  (Submodule.quotEquivOfEq _ _ (topBoundary_eq_ker R)).trans
    ((topProjection R).quotKerEquivOfSurjective (topProjection_surjective R))

@[simp] theorem topCechEquiv_mk (p : gradedFamilies R) :
    topCechEquiv R (Submodule.Quotient.mk p) = topProjection R p := by
  simp [topCechEquiv]

def topCechBasis : Module.Basis TopIndex R (TopCechQuotient R) :=
  Finsupp.basisSingleOne.map (topCechEquiv R).symm

@[simp] theorem topCechBasis_apply (q : TopIndex) :
    topCechBasis R q = Submodule.Quotient.mk (basisSection R q) := by
  apply (topCechEquiv R).injective
  simp [topCechBasis]

theorem topCech_rank_seven [Nontrivial R] : Module.finrank R (TopCechQuotient R) = 7 := by
  rw [Module.finrank_eq_card_basis (topCechBasis R), topIndex_count]

end CycleQ2SeedCechTopCohomology

#print axioms CycleQ2SeedCechTopCohomology.topIndex_count
#print axioms CycleQ2SeedCechTopCohomology.topProjection_surjective

#print axioms CycleQ2SeedCechTopCohomology.topCechBasis_apply
#print axioms CycleQ2SeedCechTopCohomology.topCech_rank_seven
end
end


/- Component: continuation_3/cylinder_bridge/SeedNormalConnecting.lean -/
section
/-! # The actual equation-normal connecting cocycle

The equation map is the dual of the displayed conormal relation for
`F=f₁g₁+f₂g₂+hk`.  Its two explicit local splittings have difference
`(kL-A)/(g₁g₂)` times `(g₂,-g₁,0)`.  The coefficients are then bound to the
literal smooth seed and its already constructed Laurent quotient charts.

The sign convention is fixed: normal fields follow `F+εA,h+εL`, hence their
images are `(-A,-L)`, and the overlap difference is first chart minus second
chart.  For fixed h the paired numerator is `-Aσ`, the negative of the
previously checked derivative numerator after substituting `w=-x₂²`.
No identification with a sheaf connecting morphism or an Abel--Jacobi map is
asserted here.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2NormalConnecting

section EquationMap

variable {R : Type*} [CommRing R]

def equationMap (g₁ g₂ k : R) : (Fin 3 → R) →ₗ[R] (Fin 2 → R) where
  toFun u := ![g₁*u 0+g₂*u 1+k*u 2, u 2]
  map_add' u v := by ext i; fin_cases i <;> simp <;> ring
  map_smul' c u := by ext i; fin_cases i <;> simp [smul_eq_mul] <;> ring

def kernelVector (g₁ g₂ : R) : Fin 3 → R := ![g₂,-g₁,0]

theorem equationMap_kernelVector (g₁ g₂ k : R) :
    equationMap g₁ g₂ k (kernelVector g₁ g₂) = 0 := by
  ext i
  fin_cases i <;> simp [equationMap, kernelVector] <;> ring

def firstLift (g₁ : Rˣ) (k A L : R) : Fin 3 → R :=
  ![(k*L-A)*(↑(g₁⁻¹) : R),0,-L]

def secondLift (g₂ : Rˣ) (k A L : R) : Fin 3 → R :=
  ![0,(k*L-A)*(↑(g₂⁻¹) : R),-L]

theorem equationMap_firstLift (g₁ : Rˣ) (g₂ k A L : R) :
    equationMap (g₁ : R) g₂ k (firstLift g₁ k A L) = ![-A,-L] := by
  ext i
  fin_cases i
  · change (g₁ : R)*((k*L-A)*(↑(g₁⁻¹) : R))+g₂*0+k*(-L)= -A
    linear_combination (k*L-A)*g₁.mul_inv
  · rfl

theorem equationMap_secondLift (g₂ : Rˣ) (g₁ k A L : R) :
    equationMap g₁ (g₂ : R) k (secondLift g₂ k A L) = ![-A,-L] := by
  ext i
  fin_cases i
  · change g₁*0+(g₂ : R)*((k*L-A)*(↑(g₂⁻¹) : R))+k*(-L)= -A
    linear_combination (k*L-A)*g₂.mul_inv
  · rfl

/-- Exactness on a first-denominator chart, without a field hypothesis. -/
theorem equationMap_kernel_first (g₁ : Rˣ) (g₂ k : R) (u : Fin 3 → R) :
    equationMap (g₁ : R) g₂ k u = 0 ↔
      ∃ c : R, u = c • kernelVector (g₁ : R) g₂ := by
  constructor
  · intro hu
    have h₀ := congrFun hu 0
    have h₂ := congrFun hu 1
    change g₁*u 0+g₂*u 1+k*u 2=0 at h₀
    change u 2=0 at h₂
    refine ⟨-(u 1*(↑(g₁⁻¹) : R)), ?_⟩
    ext i
    fin_cases i
    · change u 0 = -(u 1*(↑(g₁⁻¹) : R))*g₂
      rw [h₂] at h₀
      linear_combination (↑(g₁⁻¹) : R)*h₀-u 0*g₁.inv_mul
    · simp [kernelVector, smul_eq_mul, mul_assoc]
    · simpa [kernelVector] using h₂
  · rintro ⟨c,rfl⟩
    rw [map_smul, equationMap_kernelVector, smul_zero]

def overlapCoefficient (g₁ g₂ : Rˣ) (k A L : R) : R :=
  (k*L-A)*(↑(g₁⁻¹) : R)*(↑(g₂⁻¹) : R)

/-- The two actual lift formulas differ by the kernel generator with this
literal scalar.  This is the equation-normal Čech connecting expression. -/
theorem local_lift_difference (g₁ g₂ : Rˣ) (k A L : R) :
    firstLift g₁ k A L-secondLift g₂ k A L =
      overlapCoefficient g₁ g₂ k A L • kernelVector (g₁ : R) (g₂ : R) := by
  ext i
  fin_cases i
  · simp only [Pi.sub_apply, firstLift, secondLift, Pi.smul_apply, kernelVector,
      overlapCoefficient, Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.head_cons, Matrix.tail_cons, sub_zero, smul_eq_mul]
    rw [mul_assoc _ _ (g₂ : R), g₂.inv_mul, mul_one]
  · simp only [Pi.sub_apply, firstLift, secondLift, Pi.smul_apply, kernelVector,
      overlapCoefficient, Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.head_cons, Matrix.tail_cons, zero_sub, smul_eq_mul]
    calc
      _ = -((k*L-A)*(↑(g₂⁻¹) : R)*
          ((↑(g₁⁻¹) : R)*(g₁ : R))) := by rw [g₁.inv_mul]; ring
      _ = _ := by ring
  · simp [firstLift, secondLift, kernelVector]

end EquationMap

section Seed

open MvPolynomial CycleQ2SeedTrace
open CycleQ2SeedCechTheta
open CycleQ2SeedCech (curveA curveB)

def thetaH (θ : ℂ) : WeightedPoly := originalH+C θ*X 0^3
def thetaK (θ : ℂ) : WeightedPoly := originalK+C θ*X 0^3
def thetaEquation (θ : ℂ) : WeightedPoly :=
  X 0^6+X 1^6+X 2^6+X 3^6+X 4^3+(originalB+C θ*X 0^3)^2

theorem thetaEquation_decomposition (r θ : ℂ) (hr : r^3=2) :
    thetaEquation θ = originalF1 r*originalG1 r+originalF2*originalG2+
      thetaH θ*thetaK θ := by
  have hh := seedEquation_decomposition r hr
  unfold thetaEquation thetaH thetaK seedEquation originalH originalK at *
  linear_combination hh

theorem smoothH_eq_thetaH : CycleQ2IncidenceEquations.smoothH Complex.I = thetaH 1 := by
  simp [CycleQ2IncidenceEquations.smoothH, CycleQ2IncidenceEquations.smoothB,
    CycleQ2IncidenceEquations.smoothA, thetaH, originalH, originalB]
  ring

theorem smoothF_eq_thetaEquation (r : ℂ) (hr : r^3=2) :
    CycleQ2IncidenceEquations.smoothF r Complex.I = thetaEquation 1 := by
  rw [thetaEquation_decomposition r 1 hr]
  unfold CycleQ2IncidenceEquations.smoothF
  rw [smoothH_eq_thetaH]
  have hk : CycleQ2IncidenceEquations.smoothK Complex.I = thetaK 1 := by
    simp [CycleQ2IncidenceEquations.smoothK, CycleQ2IncidenceEquations.smoothB,
      CycleQ2IncidenceEquations.smoothA, thetaK, originalK, originalB]
    ring
  rw [hk]
  apply congrArg (fun q : WeightedPoly => q+thetaH 1*thetaK 1)
  unfold CycleQ2IncidenceEquations.seedG
  rw [CycleQ2SegreSeed.seedG_expanded]
  unfold originalF1 originalG1 originalF2 originalG2
  simp only [map_pow]
  ring

theorem substitute_thetaH (θ : ℂ) : substitute (thetaH θ) = curveH θ := by
  simp [thetaH, curveH, originalH, originalB, h, b, substitute]

abbrev CurveRing (r θ : ℂ) := Poly ⧸ curveIdeal r θ

def curveMap (r θ : ℂ) : Poly →+* CurveRing r θ := Ideal.Quotient.mk _
def ambientCurveMap (r θ : ℂ) : WeightedPoly →+* CurveRing r θ :=
  (curveMap r θ).comp substitute.toRingHom

@[simp] theorem curveMap_f1 (r θ : ℂ) : curveMap r θ (relation r 0)=0 := by
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact Ideal.subset_span (by simp)

@[simp] theorem curveMap_h (r θ : ℂ) : curveMap r θ (curveH θ)=0 := by
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact Ideal.subset_span (by simp)

@[simp] theorem ambientCurveMap_f1 (r θ : ℂ) : ambientCurveMap r θ (originalF1 r)=0 := by
  change curveMap r θ (substitute (originalF1 r))=0
  have hh : substitute (originalF1 r)=relation r 0 := by
    simpa only [originalRelations, Matrix.cons_val_zero] using substitute_relations r 0
  rw [hh, curveMap_f1]

@[simp] theorem ambientCurveMap_f2 (r θ : ℂ) : ambientCurveMap r θ originalF2=0 := by
  simp [ambientCurveMap, originalF2, substitute]

@[simp] theorem ambientCurveMap_h (r θ : ℂ) : ambientCurveMap r θ (thetaH θ)=0 := by
  change curveMap r θ (substitute (thetaH θ))=0
  rw [substitute_thetaH, curveMap_h]

@[simp] theorem ambientCurveMap_F (r θ : ℂ) (hr : r^3=2) :
    ambientCurveMap r θ (thetaEquation θ)=0 := by
  rw [thetaEquation_decomposition r θ hr]
  simp

theorem ambientCurveMap_g1 (r θ : ℂ) :
    ambientCurveMap r θ (originalG1 r)=
      curveMap r θ (C (3*r^2)*curveA^2) := by
  have hh := substitute_relations r 1
  change substitute (originalG1 r)=
    relation r 0*(X 0^2+C (2*r)*X 1*X 3)+C (3*r^2)*relation r 1 at hh
  change curveMap r θ (substitute (originalG1 r)) = _
  rw [hh]
  simp only [map_add, map_mul, curveMap_f1, zero_mul, zero_add]
  have he : relation r 1=curveA^2 := by
    change X 1^2*X 3^2=(X 1*X 3)^2
    ring
  rw [he]

theorem ambientCurveMap_g2 (r θ : ℂ) :
    ambientCurveMap r θ originalG2=curveMap r θ (C 3*curveB^4) := by
  have hc : (C (3 : ℂ) : Poly) = 3 := map_ofNat C 3
  rw [hc]
  norm_num [ambientCurveMap, originalG2, substitute, curveB]
  rw [map_ofNat (curveMap r θ) 3]
  ring

/-- This is the actual equation-normal map on the curve quotient. -/
def seedEquationMap (r θ : ℂ) :
    (Fin 3 → CurveRing r θ) →ₗ[CurveRing r θ] (Fin 2 → CurveRing r θ) :=
  equationMap (ambientCurveMap r θ (originalG1 r))
    (ambientCurveMap r θ originalG2) (ambientCurveMap r θ (thetaK θ))

def derivativeA : WeightedPoly := X 2*X 3^3*X 4

theorem substitute_derivativeA (p : Poly) :
    substitute derivativeA*p=derivativeNumerator p := by
  simp only [derivativeA, substitute, derivativeNumerator, map_mul, map_pow,
    aeval_X, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons]
  ring

/-- The fixed-h normal cocycle has the opposite sign to the previously
defined derivative numerator.  The source `A=x₂x₃³w` is unchanged. -/
theorem fixed_h_paired_numerator (p : Poly) :
    -(substitute derivativeA)*p= -derivativeNumerator p := by
  rw [neg_mul, substitute_derivativeA]

def curveEquations (r θ : ℂ) : Fin 3 → WeightedPoly :=
  ![originalF1 r, originalF2, thetaH θ]

def ambientCurveIdeal (r θ : ℂ) : Ideal WeightedPoly :=
  Ideal.span (Set.range (curveEquations r θ))

theorem curveEquation_mem (r θ : ℂ) (i : Fin 3) :
    curveEquations r θ i ∈ ambientCurveIdeal r θ := Ideal.subset_span ⟨i,rfl⟩

theorem thetaEquation_mem (r θ : ℂ) (hr : r^3=2) :
    thetaEquation θ ∈ ambientCurveIdeal r θ := by
  rw [thetaEquation_decomposition r θ hr]
  exact Ideal.add_mem _ (Ideal.add_mem _
    (Ideal.mul_mem_right _ _ (curveEquation_mem r θ 0))
    (Ideal.mul_mem_right _ _ (curveEquation_mem r θ 1)))
    (Ideal.mul_mem_right _ _ (curveEquation_mem r θ 2))

def conormalGenerator (r θ : ℂ) (i : Fin 3) : (ambientCurveIdeal r θ).Cotangent :=
  (ambientCurveIdeal r θ).toCotangent ⟨curveEquations r θ i,curveEquation_mem r θ i⟩

/-- The equation map uses the literal class of F in the actual ideal modulo
its square.  No abstract normal-bundle presentation is supplied as a premise. -/
theorem conormal_relation (r θ : ℂ) (hr : r^3=2) :
    (ambientCurveIdeal r θ).toCotangent ⟨thetaEquation θ,thetaEquation_mem r θ hr⟩ =
      originalG1 r • conormalGenerator r θ 0+
      originalG2 • conormalGenerator r θ 1+thetaK θ • conormalGenerator r θ 2 := by
  have hh : (⟨thetaEquation θ,thetaEquation_mem r θ hr⟩ : ambientCurveIdeal r θ) =
      originalG1 r • ⟨curveEquations r θ 0,curveEquation_mem r θ 0⟩+
      originalG2 • ⟨curveEquations r θ 1,curveEquation_mem r θ 1⟩+
      thetaK θ • ⟨curveEquations r θ 2,curveEquation_mem r θ 2⟩ := by
    apply Subtype.ext
    change thetaEquation θ = originalG1 r*originalF1 r+originalG2*originalF2+
      thetaK θ*thetaH θ
    rw [thetaEquation_decomposition r θ hr]
    ring
  rw [hh, map_add, map_add, map_smul, map_smul, map_smul]
  rfl

def curveG1 (r θ : ℂ) : CurveRing r θ := ambientCurveMap r θ (originalG1 r)
def curveG2 (r θ : ℂ) : CurveRing r θ := ambientCurveMap r θ originalG2

abbrev FirstOpen (r θ : ℂ) := Localization.Away (curveG1 r θ)
abbrev SecondOpen (r θ : ℂ) := Localization.Away (curveG2 r θ)
abbrev Overlap (r θ : ℂ) := Localization.Away (curveG1 r θ*curveG2 r θ)

def firstOpenUnit (r θ : ℂ) : (FirstOpen r θ)ˣ :=
  (IsLocalization.Away.algebraMap_isUnit (S := FirstOpen r θ) (curveG1 r θ)).unit
def secondOpenUnit (r θ : ℂ) : (SecondOpen r θ)ˣ :=
  (IsLocalization.Away.algebraMap_isUnit (S := SecondOpen r θ) (curveG2 r θ)).unit

def firstRestriction (r θ : ℂ) : FirstOpen r θ →+* Overlap r θ :=
  IsLocalization.Away.awayToAwayRight (curveG1 r θ) (curveG2 r θ)
def secondRestriction (r θ : ℂ) : SecondOpen r θ →+* Overlap r θ :=
  IsLocalization.Away.awayToAwayLeft (curveG2 r θ) (curveG1 r θ)

def firstOverlapUnit (r θ : ℂ) : (Overlap r θ)ˣ :=
  Units.map (firstRestriction r θ).toMonoidHom (firstOpenUnit r θ)
def secondOverlapUnit (r θ : ℂ) : (Overlap r θ)ˣ :=
  Units.map (secondRestriction r θ).toMonoidHom (secondOpenUnit r θ)

@[simp] theorem coe_firstOverlapUnit (r θ : ℂ) :
    (firstOverlapUnit r θ : Overlap r θ)=algebraMap (CurveRing r θ) (Overlap r θ) (curveG1 r θ) := by
  change firstRestriction r θ (firstOpenUnit r θ : FirstOpen r θ)=_
  rw [show (firstOpenUnit r θ : FirstOpen r θ)=
    algebraMap (CurveRing r θ) (FirstOpen r θ) (curveG1 r θ) from IsUnit.unit_spec _]
  exact IsLocalization.Away.awayToAwayRight_eq _ _ _

@[simp] theorem coe_secondOverlapUnit (r θ : ℂ) :
    (secondOverlapUnit r θ : Overlap r θ)=algebraMap (CurveRing r θ) (Overlap r θ) (curveG2 r θ) := by
  change secondRestriction r θ (secondOpenUnit r θ : SecondOpen r θ)=_
  rw [show (secondOpenUnit r θ : SecondOpen r θ)=
    algebraMap (CurveRing r θ) (SecondOpen r θ) (curveG2 r θ) from IsUnit.unit_spec _]
  exact IsLocalization.Away.awayToAwayLeft_eq _ _ _

def overlapAmbient (r θ : ℂ) : WeightedPoly →+* Overlap r θ :=
  (algebraMap (CurveRing r θ) (Overlap r θ)).comp (ambientCurveMap r θ)

def firstOpenAmbient (r θ : ℂ) : WeightedPoly →+* FirstOpen r θ :=
  (algebraMap (CurveRing r θ) (FirstOpen r θ)).comp (ambientCurveMap r θ)
def secondOpenAmbient (r θ : ℂ) : WeightedPoly →+* SecondOpen r θ :=
  (algebraMap (CurveRing r θ) (SecondOpen r θ)).comp (ambientCurveMap r θ)

def firstNormalLift (r θ : ℂ) (A L : WeightedPoly) : Fin 3 → FirstOpen r θ :=
  firstLift (firstOpenUnit r θ) (firstOpenAmbient r θ (thetaK θ))
    (firstOpenAmbient r θ A) (firstOpenAmbient r θ L)
def secondNormalLift (r θ : ℂ) (A L : WeightedPoly) : Fin 3 → SecondOpen r θ :=
  secondLift (secondOpenUnit r θ) (secondOpenAmbient r θ (thetaK θ))
    (secondOpenAmbient r θ A) (secondOpenAmbient r θ L)

theorem firstNormalLift_equations (r θ : ℂ) (A L : WeightedPoly) :
    equationMap (firstOpenAmbient r θ (originalG1 r)) (firstOpenAmbient r θ originalG2)
      (firstOpenAmbient r θ (thetaK θ)) (firstNormalLift r θ A L)=
        ![-firstOpenAmbient r θ A,-firstOpenAmbient r θ L] := by
  have hu : (firstOpenUnit r θ : FirstOpen r θ)=firstOpenAmbient r θ (originalG1 r) :=
    IsUnit.unit_spec _
  rw [← hu]
  exact equationMap_firstLift _ _ _ _ _

theorem secondNormalLift_equations (r θ : ℂ) (A L : WeightedPoly) :
    equationMap (secondOpenAmbient r θ (originalG1 r)) (secondOpenAmbient r θ originalG2)
      (secondOpenAmbient r θ (thetaK θ)) (secondNormalLift r θ A L)=
        ![-secondOpenAmbient r θ A,-secondOpenAmbient r θ L] := by
  have hu : (secondOpenUnit r θ : SecondOpen r θ)=secondOpenAmbient r θ originalG2 :=
    IsUnit.unit_spec _
  rw [← hu]
  exact equationMap_secondLift _ _ _ _ _

theorem firstNormalLift_restriction (r θ : ℂ) (A L : WeightedPoly) :
    (fun i => firstRestriction r θ (firstNormalLift r θ A L i))=
      firstLift (firstOverlapUnit r θ) (overlapAmbient r θ (thetaK θ))
        (overlapAmbient r θ A) (overlapAmbient r θ L) := by
  ext i
  fin_cases i <;>
    simp [firstNormalLift, firstLift, firstOpenAmbient, overlapAmbient, firstOverlapUnit,
      firstRestriction, IsLocalization.Away.awayToAwayRight_eq, Units.coe_map_inv]

theorem secondNormalLift_restriction (r θ : ℂ) (A L : WeightedPoly) :
    (fun i => secondRestriction r θ (secondNormalLift r θ A L i))=
      secondLift (secondOverlapUnit r θ) (overlapAmbient r θ (thetaK θ))
        (overlapAmbient r θ A) (overlapAmbient r θ L) := by
  ext i
  fin_cases i <;>
    simp [secondNormalLift, secondLift, secondOpenAmbient, overlapAmbient, secondOverlapUnit,
      secondRestriction, IsLocalization.Away.awayToAwayLeft_eq, Units.coe_map_inv]

/-- The connecting coefficient is now an element of the actual overlap
localization, with both inverses constructed from the two chart restrictions. -/
def normalOverlapCoefficient (r θ : ℂ) (A L : WeightedPoly) : Overlap r θ :=
  overlapCoefficient (firstOverlapUnit r θ) (secondOverlapUnit r θ)
    (overlapAmbient r θ (thetaK θ)) (overlapAmbient r θ A) (overlapAmbient r θ L)

theorem actual_overlap_lift_difference (r θ : ℂ) (A L : WeightedPoly) :
    firstLift (firstOverlapUnit r θ) (overlapAmbient r θ (thetaK θ))
        (overlapAmbient r θ A) (overlapAmbient r θ L)-
      secondLift (secondOverlapUnit r θ) (overlapAmbient r θ (thetaK θ))
        (overlapAmbient r θ A) (overlapAmbient r θ L)=
      normalOverlapCoefficient r θ A L •
        kernelVector (overlapAmbient r θ (originalG1 r)) (overlapAmbient r θ originalG2) := by
  rw [local_lift_difference]
  simp only [normalOverlapCoefficient, coe_firstOverlapUnit, coe_secondOverlapUnit,
    curveG1, curveG2, overlapAmbient, RingHom.comp_apply]

theorem restricted_local_lifts_difference (r θ : ℂ) (A L : WeightedPoly) :
    (fun i => firstRestriction r θ (firstNormalLift r θ A L i))-
      (fun i => secondRestriction r θ (secondNormalLift r θ A L i))=
      normalOverlapCoefficient r θ A L •
        kernelVector (overlapAmbient r θ (originalG1 r)) (overlapAmbient r θ originalG2) := by
  rw [firstNormalLift_restriction, secondNormalLift_restriction, actual_overlap_lift_difference]

end Seed

end CycleQ2NormalConnecting

#print axioms CycleQ2NormalConnecting.local_lift_difference
#print axioms CycleQ2NormalConnecting.smoothF_eq_thetaEquation
#print axioms CycleQ2NormalConnecting.ambientCurveMap_g1
#print axioms CycleQ2NormalConnecting.conormal_relation
#print axioms CycleQ2NormalConnecting.restricted_local_lifts_difference
end
end


/- Component: continuation_3/cylinder_bridge/SegreFactorExact.lean -/
section
/-! # Denominator-free exactness of the Segre factor sequence

For a regular linkage pairing `a_i*b_j=p*M_ij`, entries of `M` generating
the unit ideal give factor lifts and the unique scalar gauge ambiguity.
The proof uses scaled lifts followed by a Bezout sum and works in arbitrary
commutative rings, without choosing an invertible matrix entry.
-/

noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2SegreFactorExact

open Matrix CycleQ2IncidenceFirstOrder CycleQ2SegreTangentLocal
open scoped BigOperators

variable {A : Type*} [CommRing A]

def scaledLeftLift (a : Fin 3 → A) (N : Matrix (Fin 3) (Fin 3) A)
    (i0 j0 i : Fin 3) : A := a i0*N i j0-a i*N i0 j0

def scaledRightLift (b : Fin 3 → A) (N : Matrix (Fin 3) (Fin 3) A)
    (i0 j0 j : Fin 3) : A := b j0*N i0 j

theorem scaled_factor_lift (p : A) (M N : Matrix (Fin 3) (Fin 3) A)
    (a b : Fin 3 → A) (hab : ∀ i j, a i*b j=p*M i j)
    (hM : CycleQ2SegreLocal.cofactors M=0) (hN : cofactorDifferential M N=0)
    (i0 j0 i j : Fin 3) :
    scaledLeftLift a N i0 j0 i*b j+a i*scaledRightLift b N i0 j0 j=
      p*M i0 j0*N i j := by
  have hlin := linearized_minors_of_cofactorDifferential_zero M N hM hN i j i0 j0
  calc
    _ = (a i0*b j)*N i j0-(a i*b j)*N i0 j0+(a i*b j0)*N i0 j := by
      unfold scaledLeftLift scaledRightLift
      ring
    _ = p*M i0 j*N i j0-p*M i j*N i0 j0+p*M i j0*N i0 j := by
      rw [hab,hab,hab]
    _ = p*M i0 j0*N i j := by linear_combination -p*hlin

def bezoutLeftLift (a : Fin 3 → A) (N : Matrix (Fin 3) (Fin 3) A)
    (ξ : Fin 3 × Fin 3 → A) (i : Fin 3) : A :=
  ∑ q, ξ q*scaledLeftLift a N q.1 q.2 i

def bezoutRightLift (b : Fin 3 → A) (N : Matrix (Fin 3) (Fin 3) A)
    (ξ : Fin 3 × Fin 3 → A) (j : Fin 3) : A :=
  ∑ q, ξ q*scaledRightLift b N q.1 q.2 j

theorem bezout_factor_lift (p : A) (M N : Matrix (Fin 3) (Fin 3) A)
    (a b : Fin 3 → A) (hab : ∀ i j, a i*b j=p*M i j)
    (hM : CycleQ2SegreLocal.cofactors M=0) (hN : cofactorDifferential M N=0)
    (ξ : Fin 3 × Fin 3 → A) (hξ : ∑ q, ξ q*M q.1 q.2=1) (i j : Fin 3) :
    bezoutLeftLift a N ξ i*b j+a i*bezoutRightLift b N ξ j=p*N i j := by
  calc
    _ = ∑ q, ξ q*(scaledLeftLift a N q.1 q.2 i*b j+
        a i*scaledRightLift b N q.1 q.2 j) := by
      unfold bezoutLeftLift bezoutRightLift
      rw [Finset.sum_mul,Finset.mul_sum,← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro q hq
      ring
    _ = ∑ q, ξ q*(p*M q.1 q.2*N i j) := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [scaled_factor_lift p M N a b hab hM hN]
    _ = (∑ q, ξ q*M q.1 q.2)*(p*N i j) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro q hq
      ring
    _ = p*N i j := by rw [hξ,one_mul]

theorem bezoutLeftLift_mem (I : Ideal A) (a : Fin 3 → A)
    (ha : ∀ i, a i∈I) (N : Matrix (Fin 3) (Fin 3) A)
    (ξ : Fin 3 × Fin 3 → A) (i : Fin 3) : bezoutLeftLift a N ξ i∈I := by
  apply Ideal.sum_mem
  intro q hq
  exact I.mul_mem_left _ (I.sub_mem (I.mul_mem_right _ (ha q.1)) (I.mul_mem_right _ (ha i)))

theorem bezoutRightLift_mem (J : Ideal A) (b : Fin 3 → A)
    (hb : ∀ j, b j∈J) (N : Matrix (Fin 3) (Fin 3) A)
    (ξ : Fin 3 × Fin 3 → A) (j : Fin 3) : bezoutRightLift b N ξ j∈J := by
  apply Ideal.sum_mem
  intro q hq
  exact J.mul_mem_left _ (J.mul_mem_right _ (hb q.2))

/-- Every cofactor-kernel section has actual ideal-valued factor lifts on
any chart where the matrix entries generate the unit ideal. -/
theorem exists_factor_lift (I J : Ideal A) (p : A)
    (M N : Matrix (Fin 3) (Fin 3) A) (a b : Fin 3 → A)
    (ha : ∀ i, a i∈I) (hb : ∀ j, b j∈J)
    (hab : ∀ i j, a i*b j=p*M i j)
    (hM : CycleQ2SegreLocal.cofactors M=0) (hN : cofactorDifferential M N=0)
    (hspan : Ideal.span (Set.range (fun q : Fin 3 × Fin 3 => M q.1 q.2))=⊤) :
    ∃ v w : Fin 3 → A, (∀ i, v i∈I) ∧ (∀ j, w j∈J) ∧
      ∀ i j, v i*b j+a i*w j=p*N i j := by
  have hmem : (1 : A) ∈ Ideal.span (Set.range (fun q : Fin 3 × Fin 3 => M q.1 q.2)) := by
    rw [hspan]
    exact Submodule.mem_top
  obtain ⟨ξ,hξ⟩ := Ideal.mem_span_range_iff_exists_fun.mp hmem
  exact ⟨bezoutLeftLift a N ξ,bezoutRightLift b N ξ,
    bezoutLeftLift_mem I a ha N ξ,bezoutRightLift_mem J b hb N ξ,
    bezout_factor_lift p M N a b hab hM hN ξ hξ⟩

/-- The vanishing numerator has only the scalar gauge ambiguity. This uses
regularity of the actual linkage element, not that the entire ring is a domain. -/
theorem factor_gauge (I J : Ideal A) (p : A)
    (hp : Function.Injective (fun z : A => p*z))
    (M : Matrix (Fin 3) (Fin 3) A) (a b v w : Fin 3 → A)
    (hb : ∀ j, b j∈J) (hv : ∀ i, v i∈I)
    (hab : ∀ i j, a i*b j=p*M i j)
    (hpair : I*J≤Ideal.span {p})
    (hspan : Ideal.span (Set.range (fun q : Fin 3 × Fin 3 => M q.1 q.2))=⊤)
    (hzero : ∀ i j, v i*b j+a i*w j=0) :
    ∃ c : A, (∀ i, v i=c*a i) ∧ (∀ j, w j=-(c*b j)) := by
  have hdiv (q : Fin 3 × Fin 3) : p ∣ v q.1*b q.2 :=
    Ideal.mem_span_singleton.mp (hpair (Ideal.mul_mem_mul (hv q.1) (hb q.2)))
  choose c hc using hdiv
  have hl (i j k : Fin 3) : M i j*v k=a k*c (i,j) := by
    apply hp
    linear_combination -v k*hab i j+a k*hc (i,j)+a i*hzero k j-a k*hzero i j
  have hr (i j l : Fin 3) : M i j*w l=-(b l*c (i,j)) := by
    apply hp
    linear_combination -w l*hab i j-b l*hc (i,j)+b j*hzero i l
  have hmem : (1 : A) ∈ Ideal.span (Set.range (fun q : Fin 3 × Fin 3 => M q.1 q.2)) := by
    rw [hspan]
    exact Submodule.mem_top
  obtain ⟨ξ,hξ⟩ := Ideal.mem_span_range_iff_exists_fun.mp hmem
  refine ⟨∑ q, ξ q*c q,?_,?_⟩
  · intro k
    calc
      v k = (∑ q, ξ q*M q.1 q.2)*v k := by rw [hξ,one_mul]
      _ = ∑ q, ξ q*(M q.1 q.2*v k) := by simp only [Finset.sum_mul,mul_assoc]
      _ = ∑ q, ξ q*(a k*c q) := by simp only [hl]
      _ = (∑ q, ξ q*c q)*a k := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro q hq
        ring
  · intro l
    calc
      w l = (∑ q, ξ q*M q.1 q.2)*w l := by rw [hξ,one_mul]
      _ = ∑ q, ξ q*(M q.1 q.2*w l) := by simp only [Finset.sum_mul,mul_assoc]
      _ = ∑ q, ξ q*(-(b l*c q)) := by simp only [hr]
      _ = -((∑ q, ξ q*c q)*b l) := by
        rw [Finset.sum_mul,← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro q hq
        ring

theorem gauge_scalar_unique (p : A) (hp : Function.Injective (fun z : A => p*z))
    (M : Matrix (Fin 3) (Fin 3) A) (a b : Fin 3 → A)
    (hab : ∀ i j, a i*b j=p*M i j)
    (hspan : Ideal.span (Set.range (fun q : Fin 3 × Fin 3 => M q.1 q.2))=⊤)
    (c d : A) (h : ∀ i, c*a i=d*a i) : c=d := by
  have hM (q : Fin 3 × Fin 3) : M q.1 q.2*c=M q.1 q.2*d := by
    apply hp
    linear_combination (d-c)*hab q.1 q.2+b q.2*h q.1
  have hmem : (1 : A) ∈ Ideal.span (Set.range (fun q : Fin 3 × Fin 3 => M q.1 q.2)) := by
    rw [hspan]
    exact Submodule.mem_top
  obtain ⟨ξ,hξ⟩ := Ideal.mem_span_range_iff_exists_fun.mp hmem
  calc
    c = (∑ q, ξ q*M q.1 q.2)*c := by rw [hξ,one_mul]
    _ = ∑ q, ξ q*(M q.1 q.2*c) := by simp only [Finset.sum_mul,mul_assoc]
    _ = ∑ q, ξ q*(M q.1 q.2*d) := by simp only [hM]
    _ = (∑ q, ξ q*M q.1 q.2)*d := by
      simp only [Finset.sum_mul,mul_assoc]
    _ = d := by rw [hξ,one_mul]

theorem differential_comm (M N : Matrix (Fin 3) (Fin 3) A) :
    cofactorDifferential M N=cofactorDifferential N M := by
  unfold cofactorDifferential
  rw [add_comm M N]
  abel

theorem differential_left_smul (c : A) (M N : Matrix (Fin 3) (Fin 3) A) :
    cofactorDifferential (c • M) N=c • cofactorDifferential M N := by
  rw [differential_comm]
  have h := map_smul (cofactorDifferentialLinear N) c M
  change cofactorDifferential N (c • M)=c • cofactorDifferential N M at h
  rw [h,differential_comm N M]

/-- Actual ideal-valued factor variations are in the cofactor kernel. -/
theorem factor_lift_in_kernel (p : A) (hp : Function.Injective (fun z : A => p*z))
    (M N : Matrix (Fin 3) (Fin 3) A) (a b v w : Fin 3 → A)
    (hab : ∀ i j, a i*b j=p*M i j)
    (hN : ∀ i j, v i*b j+a i*w j=p*N i j) :
    cofactorDifferential M N=0 := by
  have hM' : p • M=(fun i j => a i*b j) := by funext i j; exact (hab i j).symm
  have hN' : p • N=(fun i j => v i*b j+a i*w j) := by funext i j; exact (hN i j).symm
  have hz : cofactorDifferential (p • M) (p • N)=0 := by
    rw [hM',hN']
    exact cofactorDifferential_factor_variation a b v w
  have hlin := map_smul (cofactorDifferentialLinear (p • M)) p N
  change cofactorDifferential (p • M) (p • N)=p • cofactorDifferential (p • M) N at hlin
  rw [hlin,differential_left_smul] at hz
  funext i j
  change cofactorDifferential M N i j = 0
  apply hp
  apply hp
  have hh := congrArg (fun T => T i j) hz
  change p*(p*cofactorDifferential M N i j)=0 at hh
  simpa only [mul_zero] using hh

end CycleQ2SegreFactorExact

#print axioms CycleQ2SegreFactorExact.exists_factor_lift
#print axioms CycleQ2SegreFactorExact.factor_gauge
#print axioms CycleQ2SegreFactorExact.gauge_scalar_unique
#print axioms CycleQ2SegreFactorExact.factor_lift_in_kernel
end
end


/- Component: continuation_3/SegreGaussianActionBinding.lean -/
section
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
set_option Elab.async false
namespace CycleQ2SegreGaussianActionData
open CycleQ2SparseGaussianPolynomial CycleQ2SegreGaussianTangentData
variable {R : Type*} [CommRing R]
variable (φ : GaussianInt →+* R) (x : Fin 5 → R) (w z v : R)
variable (hz : z^3 = evalLayers φ x v a0 + evalLayers φ x v a1*z)
variable (hw : w^3 = evalLayers φ x v b0-z^6)
include hz hw

theorem eval_action00 (a b : ℕ) :
    evalTowers φ x w z v (action00 a b) = evalTowers φ x w z v m00 * z^a * w^b := by
  by_cases h : a<3 ∧ b<3
  · exact monomial_action_of_normal_error_check φ x w z v a0 a1 b0 hz hw 32
      m00 (action00 a b) a b (action_check00 ⟨a,h.1⟩ ⟨b,h.2⟩)
  · have hf : action00 a b = normalizeTower a0 a1 b0 32
        (mulTowers m00 (monomialTower oneLayers a b)) := by
      unfold action00
      split <;> first | omega | rfl
    rw [hf, eval_normalizeTower φ x w z v a0 a1 b0 hz hw,
      eval_mulTowers,eval_monomialTower,eval_oneLayers]
    ring

theorem eval_action01 (a b : ℕ) :
    evalTowers φ x w z v (action01 a b) = evalTowers φ x w z v m01 * z^a * w^b := by
  by_cases h : a<3 ∧ b<3
  · exact monomial_action_of_normal_error_check φ x w z v a0 a1 b0 hz hw 32
      m01 (action01 a b) a b (action_check01 ⟨a,h.1⟩ ⟨b,h.2⟩)
  · have hf : action01 a b = normalizeTower a0 a1 b0 32
        (mulTowers m01 (monomialTower oneLayers a b)) := by
      unfold action01
      split <;> first | omega | rfl
    rw [hf, eval_normalizeTower φ x w z v a0 a1 b0 hz hw,
      eval_mulTowers,eval_monomialTower,eval_oneLayers]
    ring

theorem eval_action02 (a b : ℕ) :
    evalTowers φ x w z v (action02 a b) = evalTowers φ x w z v m02 * z^a * w^b := by
  by_cases h : a<3 ∧ b<3
  · exact monomial_action_of_normal_error_check φ x w z v a0 a1 b0 hz hw 32
      m02 (action02 a b) a b (action_check02 ⟨a,h.1⟩ ⟨b,h.2⟩)
  · have hf : action02 a b = normalizeTower a0 a1 b0 32
        (mulTowers m02 (monomialTower oneLayers a b)) := by
      unfold action02
      split <;> first | omega | rfl
    rw [hf, eval_normalizeTower φ x w z v a0 a1 b0 hz hw,
      eval_mulTowers,eval_monomialTower,eval_oneLayers]
    ring

theorem eval_action10 (a b : ℕ) :
    evalTowers φ x w z v (action10 a b) = evalTowers φ x w z v m10 * z^a * w^b := by
  by_cases h : a<3 ∧ b<3
  · exact monomial_action_of_normal_error_check φ x w z v a0 a1 b0 hz hw 32
      m10 (action10 a b) a b (action_check10 ⟨a,h.1⟩ ⟨b,h.2⟩)
  · have hf : action10 a b = normalizeTower a0 a1 b0 32
        (mulTowers m10 (monomialTower oneLayers a b)) := by
      unfold action10
      split <;> first | omega | rfl
    rw [hf, eval_normalizeTower φ x w z v a0 a1 b0 hz hw,
      eval_mulTowers,eval_monomialTower,eval_oneLayers]
    ring

theorem eval_action11 (a b : ℕ) :
    evalTowers φ x w z v (action11 a b) = evalTowers φ x w z v m11 * z^a * w^b := by
  by_cases h : a<3 ∧ b<3
  · exact monomial_action_of_normal_error_check φ x w z v a0 a1 b0 hz hw 32
      m11 (action11 a b) a b (action_check11 ⟨a,h.1⟩ ⟨b,h.2⟩)
  · have hf : action11 a b = normalizeTower a0 a1 b0 32
        (mulTowers m11 (monomialTower oneLayers a b)) := by
      unfold action11
      split <;> first | omega | rfl
    rw [hf, eval_normalizeTower φ x w z v a0 a1 b0 hz hw,
      eval_mulTowers,eval_monomialTower,eval_oneLayers]
    ring

theorem eval_action12 (a b : ℕ) :
    evalTowers φ x w z v (action12 a b) = evalTowers φ x w z v m12 * z^a * w^b := by
  by_cases h : a<3 ∧ b<3
  · exact monomial_action_of_normal_error_check φ x w z v a0 a1 b0 hz hw 32
      m12 (action12 a b) a b (action_check12 ⟨a,h.1⟩ ⟨b,h.2⟩)
  · have hf : action12 a b = normalizeTower a0 a1 b0 32
        (mulTowers m12 (monomialTower oneLayers a b)) := by
      unfold action12
      split <;> first | omega | rfl
    rw [hf, eval_normalizeTower φ x w z v a0 a1 b0 hz hw,
      eval_mulTowers,eval_monomialTower,eval_oneLayers]
    ring

theorem eval_action20 (a b : ℕ) :
    evalTowers φ x w z v (action20 a b) = evalTowers φ x w z v m20 * z^a * w^b := by
  by_cases h : a<3 ∧ b<3
  · exact monomial_action_of_normal_error_check φ x w z v a0 a1 b0 hz hw 32
      m20 (action20 a b) a b (action_check20 ⟨a,h.1⟩ ⟨b,h.2⟩)
  · have hf : action20 a b = normalizeTower a0 a1 b0 32
        (mulTowers m20 (monomialTower oneLayers a b)) := by
      unfold action20
      split <;> first | omega | rfl
    rw [hf, eval_normalizeTower φ x w z v a0 a1 b0 hz hw,
      eval_mulTowers,eval_monomialTower,eval_oneLayers]
    ring

theorem eval_action21 (a b : ℕ) :
    evalTowers φ x w z v (action21 a b) = evalTowers φ x w z v m21 * z^a * w^b := by
  by_cases h : a<3 ∧ b<3
  · exact monomial_action_of_normal_error_check φ x w z v a0 a1 b0 hz hw 32
      m21 (action21 a b) a b (action_check21 ⟨a,h.1⟩ ⟨b,h.2⟩)
  · have hf : action21 a b = normalizeTower a0 a1 b0 32
        (mulTowers m21 (monomialTower oneLayers a b)) := by
      unfold action21
      split <;> first | omega | rfl
    rw [hf, eval_normalizeTower φ x w z v a0 a1 b0 hz hw,
      eval_mulTowers,eval_monomialTower,eval_oneLayers]
    ring

theorem eval_action22 (a b : ℕ) :
    evalTowers φ x w z v (action22 a b) = evalTowers φ x w z v m22 * z^a * w^b := by
  by_cases h : a<3 ∧ b<3
  · exact monomial_action_of_fast_normal_error_check φ x w z v a0 a1 b0 hz hw 32
      m22 (action22 a b) a b (action_check22 ⟨a,h.1⟩ ⟨b,h.2⟩)
  · have hf : action22 a b = normalizeTower a0 a1 b0 32
        (mulTowers m22 (monomialTower oneLayers a b)) := by
      unfold action22
      split <;> first | omega | rfl
    rw [hf, eval_normalizeTower φ x w z v a0 a1 b0 hz hw,
      eval_mulTowers,eval_monomialTower,eval_oneLayers]
    ring
end CycleQ2SegreGaussianActionData
#print axioms CycleQ2SegreGaussianActionData.eval_action00
end


/- Component: continuation_3/SegreModularChartExact.lean -/
section
/-!
# Exactness on the actual coordinate opens of the modular seed

The five explicit basepoint identities and the general entry-ideal exactness
theorem apply to the same coordinate localizations used in the seed Čech
complex. This proves local existence of matrix lifts on every nonempty
coordinate open, including all overlaps. Global homogeneous lifting still
requires the connecting-obstruction argument.
-/

noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2SegreModularChartExact

open MvPolynomial Matrix CycleQ2SegreModularBasepoint CycleQ2SegreTangentLocal
  CycleQ2IncidenceFirstOrder CycleQ2SegreRelationsLocal CycleQ2SeedQuotientFiniteFree
  CycleQ2SeedCechLocalization CycleQ2SeedCechLocalizedBasis

variable {R : Type*} [CommRing R] [CharP R 109]

theorem coordinate_remaining (j : Fin 3) :
    coordinate (R := R) (remainingIndex j) =
      algebraMap (Base R) (ActualSeedRing (R := R)) (X j) := by
  change Ideal.Quotient.mk _ (X (remainingIndex j)) =
    Ideal.Quotient.mk _ (remainingInclusion R (X j))
  simp [remainingInclusion]

theorem base_coordinate_unit (s : Finset (Fin 3)) (j : Fin 3) (hj : j ∈ s) :
    IsUnit (algebraMap (Base R) (coordinateLocalization R s) (X j)) := by
  have hd : (X j : Base R) ∣ baseProduct R s := Finset.dvd_prod_of_mem X hj
  exact isUnit_of_dvd_unit ((algebraMap (Base R) (coordinateLocalization R s)).map_dvd hd)
    (IsLocalization.Away.algebraMap_isUnit (S := coordinateLocalization R s) _)

theorem seed_coordinate_unit (s : Finset (Fin 3)) (j : Fin 3) (hj : j ∈ s) :
    IsUnit (algebraMap (ActualSeedRing (R := R)) (SeedLocal R 57 33 s)
      (coordinate (remainingIndex j))) := by
  rw [coordinate_remaining, ← IsScalarTower.algebraMap_apply (Base R)
    (ActualSeedRing (R := R)) (SeedLocal R 57 33 s)]
  rw [IsScalarTower.algebraMap_apply (Base R) (coordinateLocalization R s)
    (SeedLocal R 57 33 s)]
  exact (base_coordinate_unit s j hj).map
    (algebraMap (coordinateLocalization R s) (SeedLocal R 57 33 s))

def chartMatrix (s : Finset (Fin 3)) : Matrix (Fin 3) (Fin 3) (SeedLocal R 57 33 s) :=
  (algebraMap (ActualSeedRing (R := R)) (SeedLocal R 57 33 s)).mapMatrix
    (matrix (R := R))

theorem chartMatrix_cofactors (s : Finset (Fin 3)) :
    CycleQ2SegreLocal.cofactors (chartMatrix (R := R) s) = 0 := by
  rw [chartMatrix, ← map_cofactors]
  change (algebraMap (ActualSeedRing (R := R)) (SeedLocal R 57 33 s)).mapMatrix
    (CycleQ2SegreLocal.cofactors (seedQuotientMatrix (57 : R) 33)) = 0
  rw [seedQuotientMatrix_cofactors]
  ext i j
  change algebraMap (ActualSeedRing (R := R)) (SeedLocal R 57 33 s) 0 = 0
  exact map_zero _

theorem chartMatrix_entries_generate (s : Finset (Fin 3)) (hs : s.Nonempty) :
    Ideal.span (Set.range (fun ij : Fin 3 × Fin 3 =>
      chartMatrix (R := R) s ij.1 ij.2)) = ⊤ := by
  obtain ⟨j, hj⟩ := hs
  let φ := algebraMap (ActualSeedRing (R := R)) (SeedLocal R 57 33 s)
  have hm := Ideal.mem_map_of_mem φ
    (seed_coordinate_power_mem (R := R) (remainingIndex j))
  have hu : IsUnit (φ (coordinate (remainingIndex j) ^
      CycleQ2SegreModularBasepoint.degrees (remainingIndex j))) := by
    rw [map_pow]
    exact (seed_coordinate_unit (R := R) s j hj).pow _
  have ht := Ideal.eq_top_of_isUnit_mem _ hm hu
  simpa only [entryIdeal, Ideal.map_span, ← Set.range_comp, Function.comp_def, φ, chartMatrix,
    RingHom.mapMatrix_apply, Matrix.map_apply]
    using ht

/-- The literal relation kernel equals the image of the actual cofactor
differential on every nonempty open in the three-coordinate Čech cover. -/
theorem coordinate_chart_relations_exact (s : Finset (Fin 3)) (hs : s.Nonempty)
    (C : Matrix (Fin 3) (Fin 3) (SeedLocal R 57 33 s)) :
    CycleQ2SegreRelations.relations (chartMatrix (R := R) s) *ᵥ vector C = 0 ↔
      ∃ N : Matrix (Fin 3) (Fin 3) (SeedLocal R 57 33 s),
        cofactorDifferential (chartMatrix (R := R) s) N = C :=
  entry_ideal_relations_exact _ _ (chartMatrix_cofactors s) (chartMatrix_entries_generate s hs)

theorem coordinate_chart_ker_eq_range (s : Finset (Fin 3)) (hs : s.Nonempty) :
    LinearMap.ker (relationsLinear (chartMatrix (R := R) s)) =
      LinearMap.range (cofactorDifferentialLinear (chartMatrix (R := R) s)) :=
  entry_ideal_ker_eq_range _ (chartMatrix_cofactors s) (chartMatrix_entries_generate s hs)

end CycleQ2SegreModularChartExact

#print axioms CycleQ2SegreModularChartExact.chartMatrix_entries_generate
#print axioms CycleQ2SegreModularChartExact.coordinate_chart_relations_exact
#print axioms CycleQ2SegreModularChartExact.coordinate_chart_ker_eq_range
end
end


/- Component: continuation_3/SegreModularCubicChecks.lean -/
section
set_option maxHeartbeats 2000000000
set_option maxRecDepth 100000
set_option Elab.async false
namespace CycleQ2SegreModularCubicData
open CycleQ2SparseGaussianPolynomial CycleQ2SegreGaussianTangentData

theorem eval_cubicTable {R : Type*} [CommRing R]
    (φ : GaussianInt →+* R) (x : Fin 5 → R) (w z v : R)
    (hz : z^3=evalLayers φ x v a0+evalLayers φ x v a1*z)
    (hw : w^3=evalLayers φ x v b0-z^6) (s : Fin 3) (q : Fin 9) :
    evalTowers φ x w z v (cubicTable s q)=evalTowers φ x w z v (monomialCubic q) *
      evalTowers φ x w z v k * evalTowers φ x w z v (literalQ s) := by
  fin_cases s <;> fin_cases q
  · exact eval_cubic0_0 φ x w z v hz hw
  · exact eval_cubic0_1 φ x w z v hz hw
  · exact eval_cubic0_2 φ x w z v hz hw
  · exact eval_cubic0_3 φ x w z v hz hw
  · exact eval_cubic0_4 φ x w z v hz hw
  · exact eval_cubic0_5 φ x w z v hz hw
  · exact eval_cubic0_6 φ x w z v hz hw
  · exact eval_cubic0_7 φ x w z v hz hw
  · exact eval_cubic0_8 φ x w z v hz hw
  · exact eval_cubic1_0 φ x w z v hz hw
  · exact eval_cubic1_1 φ x w z v hz hw
  · exact eval_cubic1_2 φ x w z v hz hw
  · exact eval_cubic1_3 φ x w z v hz hw
  · exact eval_cubic1_4 φ x w z v hz hw
  · exact eval_cubic1_5 φ x w z v hz hw
  · exact eval_cubic1_6 φ x w z v hz hw
  · exact eval_cubic1_7 φ x w z v hz hw
  · exact eval_cubic1_8 φ x w z v hz hw
  · exact eval_cubic2_0 φ x w z v hz hw
  · exact eval_cubic2_1 φ x w z v hz hw
  · exact eval_cubic2_2 φ x w z v hz hw
  · exact eval_cubic2_3 φ x w z v hz hw
  · exact eval_cubic2_4 φ x w z v hz hw
  · exact eval_cubic2_5 φ x w z v hz hw
  · exact eval_cubic2_6 φ x w z v hz hw
  · exact eval_cubic2_7 φ x w z v hz hw
  · exact eval_cubic2_8 φ x w z v hz hw
end CycleQ2SegreModularCubicData
#print axioms CycleQ2SegreModularCubicData.eval_cubicTable
end


/- Component: continuation_3/SegreModularCubicMonomialBinding.lean -/
section
/-! The nine supplied cubic towers are the actual indexed monomials. -/

noncomputable section
set_option maxHeartbeats 300000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2SegreModularCubicMonomialBinding

open MvPolynomial CycleQ2SparseGaussianPolynomial CycleQ2SparseModularFunctional
  CycleQ2SegreModularCubicData CycleQ2SegreModularDetectorData
  CycleQ2SegreModularGaussianBinding CycleQ2IncidenceGaussianArithmetic

theorem monomialCubic_flatten (q : Fin 9) :
    flattenTowersData (monomialCubic q)=[(cubicExponents q,1)] := by
  fin_cases q <;> rfl

theorem flatten_value (p : Towers) :
    eval coeffHom (MvPolynomial.X : Fin 5 → CycleQ2SegreModularGaussianBinding.P)
      (flattenTowersData p)=value p := by
  rw [flattenTowersData_eq,eval_flattenTowers]
  rfl

theorem value_monomialCubic (q : Fin 9) :
    value (monomialCubic q)=
      MvPolynomial.monomial (tupleExponent (cubicExponents q)) (1:F109) := by
  rw [←flatten_value,monomialCubic_flatten]
  change eval (MvPolynomial.C.comp reduction)
    (MvPolynomial.X : Fin 5 → CycleQ2SegreModularGaussianBinding.P)
      [(cubicExponents q,1)]=_
  simp only [eval_cons,eval_nil,termValue_variables,map_one,add_zero]

end CycleQ2SegreModularCubicMonomialBinding

#print axioms CycleQ2SegreModularCubicMonomialBinding.value_monomialCubic
end
end


/- Component: continuation_3/SegreModularCubicPairingExpressions.lean -/
section
namespace CycleQ2SegreModularCubicPairing
open CycleQ2SparseModularFunctional CycleQ2SegreModularCubicData

def cubicDot (W : WeightData) (c : Fin 9) : ℕ :=
  (dot W 0 0 (0,0,0,0,0) (flattenTowersData (cubicTable 0 c)) +
   dot W 0 1 (0,0,0,0,0) (flattenTowersData (cubicTable 1 c)) +
   dot W 0 2 (0,0,0,0,0) (flattenTowersData (cubicTable 2 c))) % 109

end CycleQ2SegreModularCubicPairing
end


