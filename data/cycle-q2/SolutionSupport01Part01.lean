import Proposal.GeometricIncidenceCechTrace
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
import Proposal.GeometricRankRetraction
import Proposal.GeometricFormalInputs
import Proposal.Normalization

/-! Components extracted from SolutionSupport01.lean, in their original order.
See solution.md for the mathematical and verification status. -/

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

-- `exists_rank_retraction` is shared with the cube-root specialization proof
-- through `GeometricRankRetraction`.

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


