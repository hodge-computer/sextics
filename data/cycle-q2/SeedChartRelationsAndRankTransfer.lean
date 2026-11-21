import Mathlib.LinearAlgebra.Dual.Defs
import Proposal.GeometricCartierOrbit
import Proposal.GeometricRankRetraction
import Proposal.SegreModularCubicThirdRow
import Proposal.CurveRestrictionLeftMinor
import Proposal.PointedIncidenceLifts

/-!
# Exactness on the seed charts and transfer of rank
-/

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

/- Component: continuation_3/CurveRestrictionComplex.lean -/
section
/-! The actual complex restriction maps are surjective.  The two nonzero
minors come from independently checked modular polynomial identities and
inverse products, transported through the Gaussian integral family. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2CurveRestriction

open CycleQ2CurveRestrictionReflection CycleQ2CurveRestrictionModularData
  CycleQ2CurveRestrictionModularChecks CycleQ2IncidenceGaussianArithmetic

/-- Every standard monomial of the full left curve piece occurs as a row. -/
theorem left_rows_cover : ∀ q : TargetIndex .left 10,
    ∃ i : Fin 57, leftRows i=targetTuple q := by decide +kernel

/-- Every standard monomial of the full right curve piece occurs as a row. -/
theorem right_rows_cover : ∀ q : TargetIndex .right 8,
    ∃ i : Fin 45, rightRows i=targetTuple q := by decide +kernel

theorem left_sources_good : ∀ j : Fin 57, sourceGood 10 0 (leftSources j)=true := by decide +kernel

theorem right_sources_good : ∀ j : Fin 45, sourceGood 8 1 (rightSources j)=true := by decide +kernel

noncomputable section

theorem complex_minor_nonzero_of_modular (s : Side) {n : ℕ}
    (rows : Fin n → CurveTuple) (columns : Fin n → SourceTuple)
    (hmod : Matrix.det (fun i j : Fin n =>
      matrixCoefficient s (57:F109) 33 (rows i) (columns j))≠0) :
    Matrix.det (fun i j : Fin n => matrixCoefficient s (57:ℂ) Complex.I (rows i) (columns j))≠0 := by
  let A : Matrix (Fin n) (Fin n) GaussianInt :=
    fun i j => matrixCoefficient s 57 gaussianI (rows i) (columns j)
  have hm : A.map reduction =
      (fun i j : Fin n => matrixCoefficient s (57:F109) 33 (rows i) (columns j)) := by
    ext i j
    change reduction (matrixCoefficient s (57:GaussianInt) gaussianI (rows i) (columns j))=_
    simpa only [map_ofNat,reduction_I] using
      matrixCoefficient_map reduction s (57:GaussianInt) gaussianI (rows i) (columns j)
  have hc : A.map GaussianInt.toComplex =
      (fun i j : Fin n => matrixCoefficient s (57:ℂ) Complex.I (rows i) (columns j)) := by
    ext i j
    change GaussianInt.toComplex (matrixCoefficient s (57:GaussianInt) gaussianI (rows i) (columns j))=_
    simpa only [map_ofNat,complex_I] using
      matrixCoefficient_map GaussianInt.toComplex s (57:GaussianInt) gaussianI (rows i) (columns j)
  have hA := determinant_nonzero_of_reduction A (by rw [hm]; exact hmod)
  rwa [hc] at hA

theorem left_complex_minor_nonzero :
    Matrix.det (fun i j : Fin 57 => matrixCoefficient .left (57:ℂ) Complex.I (leftRows i) (leftSources j))≠0 :=
  complex_minor_nonzero_of_modular .left leftRows leftSources (left_minor_det_ne_zero (R:=F109))

theorem right_complex_minor_nonzero :
    Matrix.det (fun i j : Fin 45 => matrixCoefficient .right (57:ℂ) Complex.I (rightRows i) (rightSources j))≠0 :=
  complex_minor_nonzero_of_modular .right rightRows rightSources (right_minor_det_ne_zero (R:=F109))

/-- Restriction from the actual degree10 invariant seed piece to the actual
left complete-intersection curve is onto over the complex numbers. -/
theorem left_restriction_surjective :
    Function.Surjective (seedRestrictionPiece .left (57:ℂ) Complex.I 10 0) :=
  seedRestrictionPiece_surjective_of_minor .left 57 Complex.I 10 0 57
    leftRows leftSources left_rows_cover left_sources_good left_complex_minor_nonzero

/-- Restriction from the actual degree8 character-one seed piece to the actual
right complete-intersection curve is onto over the complex numbers. -/
theorem right_restriction_surjective :
    Function.Surjective (seedRestrictionPiece .right (57:ℂ) Complex.I 8 1) :=
  seedRestrictionPiece_surjective_of_minor .right 57 Complex.I 8 1 45
    rightRows rightSources right_rows_cover right_sources_good right_complex_minor_nonzero

theorem left_restriction_kernel_rank :
    Module.finrank ℂ (LinearMap.ker (seedRestrictionPiece .left (57:ℂ) Complex.I 10 0))=56 := by
  letI : FiniteDimensional ℂ (SeedPiece (57:ℂ) Complex.I 10 0) :=
    Module.Finite.of_basis (seedPieceBasis (57:ℂ) Complex.I 10 0 (by decide))
  have h := (seedRestrictionPiece .left (57:ℂ) Complex.I 10 0).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr left_restriction_surjective,finrank_top,
    left_seedPiece_rank,left_curvePiece_rank] at h
  omega

theorem right_restriction_kernel_rank :
    Module.finrank ℂ (LinearMap.ker (seedRestrictionPiece .right (57:ℂ) Complex.I 8 1))=23 := by
  letI : FiniteDimensional ℂ (SeedPiece (57:ℂ) Complex.I 8 1) :=
    Module.Finite.of_basis (seedPieceBasis (57:ℂ) Complex.I 8 1 (by decide))
  have h := (seedRestrictionPiece .right (57:ℂ) Complex.I 8 1).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr right_restriction_surjective,finrank_top,
    right_seedPiece_rank,right_curvePiece_rank] at h
  omega

end
end CycleQ2CurveRestriction

#print axioms CycleQ2CurveRestriction.left_restriction_surjective
#print axioms CycleQ2CurveRestriction.right_restriction_surjective
#print axioms CycleQ2CurveRestriction.left_restriction_kernel_rank
#print axioms CycleQ2CurveRestriction.right_restriction_kernel_rank
end

/- Component: continuation_3/HomogeneousIdealOpen.lean -/
section
/-! A finite homogeneous multiplication map is surjective on one actual
polynomial open whenever its seed specialization generates the entire
homogeneous piece. The degree and all finite indices remain symbolic in
this proof. Concrete large-degree applications use the theorem directly.
-/

noncomputable section
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace CycleQ2HomogeneousIdealOpen

open MvPolynomial Matrix CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations
  CycleQ2HomogeneousIdealArithmetic

variable {R K : Type*} [CommRing R] [CommRing K]
  {ι : Type*} [Fintype ι]

theorem exists_multiplication_open (f : R →+* K) (c : K →+* R)
    (hfc : ∀ x, f (c x)=x) (g : ι → Poly R) (degree : ι → ℕ)
    (hgen : ∀ j, HG (g j) (degree j,0)) (N : ℕ) (hle : ∀ j, degree j≤N)
    (hseed : ∀ p : Poly K, HG p (N,0) →
      p∈generatorIdeal (fun j => map f (g j))) :
    ∃ s : R, f s=1 ∧
      ∀ (S : Type*) [CommRing S] (φ : R →+* S), IsUnit (φ s) →
        Function.Surjective ((multiplicationMatrix g degree N).map φ).mulVec := by
  classical
  have hA : Function.Surjective ((multiplicationMatrix g degree N).map f).mulVec := by
    rw [multiplicationMatrix_map]
    exact multiplication_surjective_of_membership (fun j => map f (g j)) degree
      (fun j => homogeneous_map f (hgen j)) N hle hseed
  obtain ⟨B,s,hsdet,hsseed,hs⟩ :=
    CycleQ2PolynomialSurjectivityOpen.exists_surjectivity_open
      (m:=FullInvariantIndex N) (n:=Column N degree) f c hfc
      (multiplicationMatrix g degree N) hA
  exact ⟨s,hsseed,hs⟩

theorem exists_homogeneous_open (f : R →+* K) (c : K →+* R)
    (hfc : ∀ x, f (c x)=x) (g : ι → Poly R) (degree : ι → ℕ)
    (hgen : ∀ j, HG (g j) (degree j,0)) (N : ℕ) (hle : ∀ j, degree j≤N)
    (hseed : ∀ p : Poly K, HG p (N,0) →
      p∈generatorIdeal (fun j => map f (g j))) :
    ∃ s : R, f s=1 ∧
      ∀ (S : Type*) [CommRing S] (φ : R →+* S), IsUnit (φ s) →
        ∀ p : Poly S, HG p (N,0) → p∈generatorIdeal (fun j => map φ (g j)) := by
  obtain ⟨s,hsseed,hs⟩ := exists_multiplication_open f c hfc g degree hgen N hle hseed
  refine ⟨s,hsseed,?_⟩
  intro S _ φ hφ p hp
  have hsurj := hs S φ hφ
  rw [multiplicationMatrix_map] at hsurj
  exact membership_of_multiplication_surjective (fun j => map φ (g j)) degree
    (fun j => homogeneous_map φ (hgen j)) N hle hsurj p hp

end CycleQ2HomogeneousIdealOpen

#print axioms CycleQ2HomogeneousIdealOpen.exists_multiplication_open
#print axioms CycleQ2HomogeneousIdealOpen.exists_homogeneous_open
end
end

/- Component: continuation_3/SegreComplexBasepoint.lean -/
section
/-!
# Characteristic-zero basepoint freeness of the actual Segre seed

The checked modular coordinate-power identities imply that the entire
weighted-degree120 invariant polynomial piece lies in the generator ideal:
every such monomial is divisible by one of the five checked powers.
Homogeneous projection turns this into surjectivity of a finite coefficient
matrix. Arithmetic surjectivity transfer proves the corresponding complex
membership statement, hence coordinate-power membership for the actual
complex seed quotient. No modular solution is asserted to lift individually.
-/

noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2SegreComplexBasepoint

open MvPolynomial Matrix CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations
  CycleQ2IncidenceJacobianNaturality CycleQ2IncidenceGaussianArithmetic
  CycleQ2HomogeneousIdealArithmetic CycleQ2SegreTangentLocal

def seedGenerators {R : Type*} [CommRing R] (r ι : R) : Fin 11 → Poly R :=
  ![rawSeedMatrix r 0 0, rawSeedMatrix r 0 1, rawSeedMatrix r 0 2,
    rawSeedMatrix r 1 0, rawSeedMatrix r 1 1, rawSeedMatrix r 1 2,
    rawSeedMatrix r 2 0, rawSeedMatrix r 2 1, rawSeedMatrix r 2 2,
    smoothH ι, seedG r]

def generatorDegree : Fin 11 → ℕ := ![14,14,14,14,14,14,14,14,14,3,6]

theorem generators_homogeneous {R : Type*} [CommRing R] (r ι : R) (j : Fin 11) :
    HG (seedGenerators r ι j) (generatorDegree j,0) := by
  fin_cases j
  · exact rawSeedMatrix_homogeneous r 0 0
  · exact rawSeedMatrix_homogeneous r 0 1
  · exact rawSeedMatrix_homogeneous r 0 2
  · exact rawSeedMatrix_homogeneous r 1 0
  · exact rawSeedMatrix_homogeneous r 1 1
  · exact rawSeedMatrix_homogeneous r 1 2
  · exact rawSeedMatrix_homogeneous r 2 0
  · exact rawSeedMatrix_homogeneous r 2 1
  · exact rawSeedMatrix_homogeneous r 2 2
  · exact smoothH_homogeneous ι
  · exact seedG_homogeneous r

theorem generatorDegree_le (j : Fin 11) : generatorDegree j ≤ 120 := by
  fin_cases j <;> decide

theorem seedGenerators_map {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (r ι : R) :
    (fun j => MvPolynomial.map φ (seedGenerators r ι j)) = seedGenerators (φ r) (φ ι) := by
  have hm (a b : Fin 3) : map φ (rawSeedMatrix r a b) = rawSeedMatrix (φ r) a b := by
    have h := congrArg (fun M : Matrix (Fin 3) (Fin 3) (Poly S) => M a b)
      (map_rawSeedMatrix φ r)
    simpa only [RingHom.mapMatrix_apply, Matrix.map_apply] using h
  funext j
  fin_cases j <;> simp [seedGenerators, hm, map_smoothH, map_seedG]

theorem high_degree_divisible (e : FullInvariantIndex 120) :
    ∃ j : Fin 5, CycleQ2SegreModularBasepoint.degrees j ≤ fullExponentOf e.val j := by
  by_contra h
  push Not at h
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  have h4 := h 4
  have hd := e.property.1
  rw [fullExponentOf_apply,
    show CycleQ2SegreModularBasepoint.degrees 0 = 24 by decide] at h0
  rw [fullExponentOf_apply,
    show CycleQ2SegreModularBasepoint.degrees 1 = 24 by decide] at h1
  rw [fullExponentOf_apply,
    show CycleQ2SegreModularBasepoint.degrees 2 = 24 by decide] at h2
  rw [fullExponentOf_apply,
    show CycleQ2SegreModularBasepoint.degrees 3 = 24 by decide] at h3
  rw [fullExponentOf_apply,
    show CycleQ2SegreModularBasepoint.degrees 4 = 12 by decide] at h4
  simp only [fullDegree] at hd
  omega

theorem modular_monomial_mem (e : FullInvariantIndex 120) :
    (monomial (fullExponentOf e.val) 1 : Poly F109) ∈
      generatorIdeal (seedGenerators (57 : F109) 33) := by
  obtain ⟨j, hj⟩ := high_degree_divisible e
  have he : Finsupp.single j (CycleQ2SegreModularBasepoint.degrees j) ≤
      fullExponentOf e.val := Finsupp.single_le_iff.mpr hj
  have hh := CycleQ2SegreModularBasepoint.coordinate_power_mem (R := F109) j
  change (X j : Poly F109)^CycleQ2SegreModularBasepoint.degrees j ∈
    generatorIdeal (seedGenerators (57 : F109) 33) at hh
  have hm : (monomial (fullExponentOf e.val) 1 : Poly F109) =
      X j^CycleQ2SegreModularBasepoint.degrees j *
        monomial (fullExponentOf e.val-Finsupp.single j
          (CycleQ2SegreModularBasepoint.degrees j)) 1 := by
    rw [X_pow_eq_monomial, monomial_mul, one_mul, add_tsub_cancel_of_le he]
  rw [hm]
  exact Ideal.mul_mem_right _ _ hh

theorem modular_homogeneous_mem (p : Poly F109) (hp : HG p (120,0)) :
    p ∈ generatorIdeal (seedGenerators (57 : F109) 33) := by
  rw [← fullInvariantPolynomial_of_homogeneous hp]
  apply Ideal.sum_mem
  intro e _
  simpa only [C_mul_monomial, mul_one] using
    Ideal.mul_mem_left (generatorIdeal (seedGenerators (57 : F109) 33))
      (C (p.coeff (fullExponentOf e.val))) (modular_monomial_mem e)

/-- The complete complex degree120 invariant piece lies in the ideal of
the actual raw matrix entries, h and G at r=57, i=Complex.I. -/
theorem complex_homogeneous_mem (p : Poly ℂ) (hp : HG p (120,0)) :
    p ∈ generatorIdeal (seedGenerators (57 : ℂ) Complex.I) := by
  have hmod : ∀ p : Poly F109, HG p (120,0) → p ∈ generatorIdeal
      (fun j => map reduction (seedGenerators (57 : GaussianInt) gaussianI j)) := by
    rw [seedGenerators_map, reduction_I, map_ofNat]
    exact modular_homogeneous_mem
  have h := gaussian_membership_transfer (seedGenerators (57 : GaussianInt) gaussianI)
    generatorDegree (generators_homogeneous _ _) 120 generatorDegree_le hmod p hp
  simpa only [seedGenerators_map, complex_I, map_ofNat] using h

def coordinatePower : Fin 5 → ℕ := ![120,120,120,120,60]

theorem coordinate_power_homogeneous (j : Fin 5) :
    HG (X j^coordinatePower j : Poly ℂ) (120,0) := by
  rw [X_pow_eq_monomial]
  apply isWeightedHomogeneous_monomial
  rw [Finsupp.weight_single]
  fin_cases j <;> decide

theorem complex_coordinate_power_mem (j : Fin 5) :
    (X j : Poly ℂ)^coordinatePower j ∈
      generatorIdeal (seedGenerators (57 : ℂ) Complex.I) :=
  complex_homogeneous_mem _ (coordinate_power_homogeneous j)

abbrev ComplexSeedRing := SeedRing (57 : ℂ) Complex.I

def coordinate (j : Fin 5) : ComplexSeedRing := Ideal.Quotient.mk _ (X j)
def matrix : Matrix (Fin 3) (Fin 3) ComplexSeedRing := seedQuotientMatrix 57 Complex.I
def entryIdeal : Ideal ComplexSeedRing :=
  Ideal.span (Set.range (fun ij : Fin 3 × Fin 3 => matrix ij.1 ij.2))

theorem quotient_h :
    Ideal.Quotient.mk (equationsIdeal (smoothH Complex.I) (smoothF (57 : ℂ) Complex.I))
      (smoothH Complex.I) = 0 := by
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp [equationsIdeal]))

theorem quotient_g :
    Ideal.Quotient.mk (equationsIdeal (smoothH Complex.I) (smoothF (57 : ℂ) Complex.I))
      (seedG (57 : ℂ)) = 0 := by
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  apply (CycleQ2IncidenceFirstOrder.smoothSeed_mem_iff_linkage (57 : ℂ) Complex.I).mpr
  exact ⟨0,1,by simp⟩

theorem generator_quotient_mem (j : Fin 11) :
    Ideal.Quotient.mk (equationsIdeal (smoothH Complex.I) (smoothF (57 : ℂ) Complex.I))
      (seedGenerators (57 : ℂ) Complex.I j) ∈ entryIdeal := by
  have hm (a b : Fin 3) : matrix a b ∈ entryIdeal :=
    Ideal.subset_span (Set.mem_range_self (a,b))
  fin_cases j
  · exact hm 0 0
  · exact hm 0 1
  · exact hm 0 2
  · exact hm 1 0
  · exact hm 1 1
  · exact hm 1 2
  · exact hm 2 0
  · exact hm 2 1
  · exact hm 2 2
  · change Ideal.Quotient.mk _ (smoothH Complex.I) ∈ _
    rw [quotient_h]
    exact Ideal.zero_mem _
  · change Ideal.Quotient.mk _ (seedG (57 : ℂ)) ∈ _
    rw [quotient_g]
    exact Ideal.zero_mem _

/-- Characteristic-zero coordinate-power membership in the actual seed
quotient, obtained nonconstructively from the verified modular certificate. -/
theorem seed_coordinate_power_mem (j : Fin 5) : coordinate j^coordinatePower j ∈ entryIdeal := by
  let φ := Ideal.Quotient.mk (equationsIdeal (smoothH Complex.I) (smoothF (57 : ℂ) Complex.I))
  have hle : generatorIdeal (seedGenerators (57 : ℂ) Complex.I) ≤ entryIdeal.comap φ := by
    apply Ideal.span_le.mpr
    rintro _ ⟨j,rfl⟩
    exact generator_quotient_mem j
  have h := hle (complex_coordinate_power_mem j)
  change φ ((X j : Poly ℂ)^coordinatePower j) ∈ entryIdeal at h
  simpa only [map_pow, φ, coordinate] using h

theorem prime_pivot_cover (P : Ideal ComplexSeedRing) [P.IsPrime]
    (hx : ∃ j, coordinate j ∉ P) : ∃ i j, matrix i j ∉ P := by
  classical
  by_contra! hzero
  have hle : entryIdeal ≤ P := by
    apply Ideal.span_le.mpr
    rintro _ ⟨ij,rfl⟩
    exact hzero ij.1 ij.2
  obtain ⟨j,hj⟩ := hx
  exact hj ((inferInstance : P.IsPrime).mem_of_pow_mem _ (hle (seed_coordinate_power_mem j)))

theorem field_pivot_cover {K : Type*} [Field K] (φ : ComplexSeedRing →+* K)
    (hx : ∃ j, φ (coordinate j) ≠ 0) : ∃ i j, IsUnit (φ (matrix i j)) :=
  CycleQ2SegreImage.exists_unit_entry_of_coordinate_powers
    matrix coordinate coordinatePower seed_coordinate_power_mem φ hx

theorem entries_generate_if_coordinate_unit {S : Type*} [CommRing S]
    (φ : ComplexSeedRing →+* S) (j : Fin 5) (hu : IsUnit (φ (coordinate j))) :
    Ideal.span (Set.range (fun ij : Fin 3 × Fin 3 => φ (matrix ij.1 ij.2))) = ⊤ := by
  have hm := Ideal.mem_map_of_mem φ (seed_coordinate_power_mem j)
  have hunit : IsUnit (φ (coordinate j^coordinatePower j)) := by
    rw [map_pow]
    exact hu.pow _
  have ht := Ideal.eq_top_of_isUnit_mem _ hm hunit
  simpa only [entryIdeal, Ideal.map_span, ← Set.range_comp, Function.comp_def] using ht

end CycleQ2SegreComplexBasepoint

#print axioms CycleQ2SegreComplexBasepoint.complex_homogeneous_mem
#print axioms CycleQ2SegreComplexBasepoint.seed_coordinate_power_mem
#print axioms CycleQ2SegreComplexBasepoint.prime_pivot_cover
#print axioms CycleQ2SegreComplexBasepoint.entries_generate_if_coordinate_unit
end
end

/- Component: continuation_3/cylinder_bridge/SegreFactorSequence.lean -/
section
/-! # The actual linear factor sequence

The factor map divides the literal numerator `v_i*b_j+a_i*w_j` by the
regular linkage element. Divisibility follows from the two factor ideals;
regularity makes the quotient unique and the map linear.
-/

noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2SegreFactorSequence

open Matrix CycleQ2IncidenceFirstOrder CycleQ2SegreTangentLocal
  CycleQ2SegreFactorExact

variable {A : Type*} [CommRing A]

structure FactorData (A : Type*) [CommRing A] where
  leftIdeal : Ideal A
  rightIdeal : Ideal A
  linkage : A
  matrix : Matrix (Fin 3) (Fin 3) A
  left : Fin 3 → A
  right : Fin 3 → A
  left_mem : ∀ i, left i ∈ leftIdeal
  right_mem : ∀ j, right j ∈ rightIdeal
  product : ∀ i j, left i*right j=linkage*matrix i j
  ideals_product : leftIdeal*rightIdeal≤Ideal.span {linkage}
  regular : Function.Injective (fun z : A => linkage*z)
  cofactors_zero : CycleQ2SegreLocal.cofactors matrix=0
  entries_generate : Ideal.span (Set.range (fun q : Fin 3 × Fin 3 => matrix q.1 q.2))=⊤

variable (F : FactorData A)

abbrev FactorDomain := (Fin 3 → F.leftIdeal) × (Fin 3 → F.rightIdeal)

theorem numerator_divisible (v : FactorDomain F) (i j : Fin 3) :
    F.linkage ∣ (v.1 i : A)*F.right j+F.left i*(v.2 j : A) := by
  apply Ideal.mem_span_singleton.mp
  apply (Ideal.span {F.linkage}).add_mem
  · exact F.ideals_product (Ideal.mul_mem_mul (v.1 i).property (F.right_mem j))
  · exact F.ideals_product (Ideal.mul_mem_mul (F.left_mem i) (v.2 j).property)

def factorValue (v : FactorDomain F) : Matrix (Fin 3) (Fin 3) A :=
  fun i j => Classical.choose (numerator_divisible F v i j)

theorem linkage_factorValue (v : FactorDomain F) (i j : Fin 3) :
    F.linkage*factorValue F v i j=(v.1 i : A)*F.right j+F.left i*(v.2 j : A) :=
  (Classical.choose_spec (numerator_divisible F v i j)).symm

def factorMap : FactorDomain F →ₗ[A] Matrix (Fin 3) (Fin 3) A where
  toFun := factorValue F
  map_add' v w := by
    funext i j
    apply F.regular
    change F.linkage*factorValue F (v+w) i j=
      F.linkage*(factorValue F v i j+factorValue F w i j)
    rw [mul_add,linkage_factorValue,linkage_factorValue,linkage_factorValue]
    change ((v.1 i:A)+(w.1 i:A))*F.right j+F.left i*((v.2 j:A)+(w.2 j:A))=
      ((v.1 i:A)*F.right j+F.left i*(v.2 j:A))+
      ((w.1 i:A)*F.right j+F.left i*(w.2 j:A))
    ring
  map_smul' c v := by
    funext i j
    apply F.regular
    change F.linkage*factorValue F (c • v) i j=F.linkage*(c*factorValue F v i j)
    rw [show F.linkage*(c*factorValue F v i j)=c*(F.linkage*factorValue F v i j) by ring]
    rw [linkage_factorValue,linkage_factorValue]
    change (c*(v.1 i:A))*F.right j+F.left i*(c*(v.2 j:A))=
      c*((v.1 i:A)*F.right j+F.left i*(v.2 j:A))
    ring

theorem linkage_factorMap (v : FactorDomain F) (i j : Fin 3) :
    F.linkage*factorMap F v i j=(v.1 i:A)*F.right j+F.left i*(v.2 j:A) :=
  linkage_factorValue F v i j

def gaugeMap : A →ₗ[A] FactorDomain F where
  toFun c := (fun i => ⟨c*F.left i,F.leftIdeal.mul_mem_left c (F.left_mem i)⟩,
    fun j => ⟨-(c*F.right j),F.rightIdeal.neg_mem
      (F.rightIdeal.mul_mem_left c (F.right_mem j))⟩)
  map_add' c d := by
    apply Prod.ext
    · funext i
      apply Subtype.ext
      change (c+d)*F.left i=c*F.left i+d*F.left i
      ring
    · funext j
      apply Subtype.ext
      change -((c+d)*F.right j)=-(c*F.right j)+-(d*F.right j)
      ring
  map_smul' c d := by
    apply Prod.ext
    · funext i
      apply Subtype.ext
      change (c*d)*F.left i=c*(d*F.left i)
      ring
    · funext j
      apply Subtype.ext
      change -((c*d)*F.right j)=c*(-(d*F.right j))
      ring

theorem factorMap_gaugeMap (c : A) : factorMap F (gaugeMap F c)=0 := by
  funext i j
  change factorMap F (gaugeMap F c) i j=0
  apply F.regular
  calc
    F.linkage*factorMap F (gaugeMap F c) i j =
        ((gaugeMap F c).1 i:A)*F.right j+F.left i*((gaugeMap F c).2 j:A) :=
      linkage_factorMap F (gaugeMap F c) i j
    _ = F.linkage*0 := by
      change (c*F.left i)*F.right j+F.left i*(-(c*F.right j))=F.linkage*0
      ring

theorem gaugeMap_injective : Function.Injective (gaugeMap F) := by
  intro c d h
  apply gauge_scalar_unique F.linkage F.regular F.matrix F.left F.right
    F.product F.entries_generate c d
  intro i
  exact congrArg (fun v : FactorDomain F => (v.1 i : A)) h

theorem ker_factorMap_eq_range_gaugeMap :
    LinearMap.ker (factorMap F)=LinearMap.range (gaugeMap F) := by
  apply le_antisymm
  · intro v hv
    have hz : ∀ i j, (v.1 i:A)*F.right j+F.left i*(v.2 j:A)=0 := by
      intro i j
      have hh := linkage_factorMap F v i j
      have he : factorMap F v=0 := hv
      have hij : factorMap F v i j=0 :=
        congrArg (fun N : Matrix (Fin 3) (Fin 3) A => N i j) he
      rw [hij,mul_zero] at hh
      exact hh.symm
    obtain ⟨c,hc,hc'⟩ := factor_gauge F.leftIdeal F.rightIdeal F.linkage F.regular
      F.matrix F.left F.right (fun i => (v.1 i:A)) (fun j => (v.2 j:A))
      F.right_mem (fun i => (v.1 i).property) F.product F.ideals_product
      F.entries_generate hz
    refine ⟨c,?_⟩
    apply Prod.ext
    · funext i
      apply Subtype.ext
      exact (hc i).symm
    · funext j
      apply Subtype.ext
      exact (hc' j).symm
  · rintro v ⟨c,rfl⟩
    exact factorMap_gaugeMap F c

theorem range_factorMap_eq_ker_differential :
    LinearMap.range (factorMap F)=LinearMap.ker (cofactorDifferentialLinear F.matrix) := by
  apply le_antisymm
  · rintro N ⟨v,rfl⟩
    apply factor_lift_in_kernel F.linkage F.regular F.matrix (factorMap F v)
      F.left F.right (fun i => (v.1 i:A)) (fun j => (v.2 j:A)) F.product
    intro i j
    exact (linkage_factorMap F v i j).symm
  · intro N hN
    obtain ⟨v,w,hv,hw,he⟩ := exists_factor_lift F.leftIdeal F.rightIdeal F.linkage
      F.matrix N F.left F.right F.left_mem F.right_mem F.product
      F.cofactors_zero hN F.entries_generate
    let V : FactorDomain F := (fun i => ⟨v i,hv i⟩,fun j => ⟨w j,hw j⟩)
    refine ⟨V,?_⟩
    funext i j
    apply F.regular
    calc
      F.linkage*factorMap F V i j = (V.1 i:A)*F.right j+F.left i*(V.2 j:A) :=
        linkage_factorMap F V i j
      _ = F.linkage*N i j := he i j

end CycleQ2SegreFactorSequence

#print axioms CycleQ2SegreFactorSequence.gaugeMap_injective
#print axioms CycleQ2SegreFactorSequence.ker_factorMap_eq_range_gaugeMap
#print axioms CycleQ2SegreFactorSequence.range_factorMap_eq_ker_differential
end
end

/- Component: continuation_3/CurveRestrictionCoordinates.lean -/
section
/-! The right normal-form chart is an explicit coordinate algebra equivalence
of the original complete-intersection curve, not merely a parametrization. -/

noncomputable section
set_option maxHeartbeats 1000000
set_option Elab.async false
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2CurveRestriction
open MvPolynomial CycleQ2IncidenceEquations

abbrev CP := CurvePoly ℂ

def originalCubic (ι : ℂ) : CP :=
  X 0^3+X 2^3+X 1*X 2*X 3+X 0*X 2*X 3+X 0*X 1^2+
    C (1-ι)*X 3^3-C ι*X 1^3

def originalQuadric (s : Side) (r : ℂ) : CP :=
  match s with
  | .left => X 0^2-C r*X 1*X 3
  | .right => X 0^2+X 2^2

def originalCurveIdeal (s : Side) (r ι : ℂ) : Ideal CP :=
  Ideal.span {originalQuadric s r,originalCubic ι}

def coordinateValues (s : Side) : Fin 4 → CP :=
  match s with
  | .left => X
  | .right => ![X 0+X 2,2*X 1,X 0-X 2,2*X 3]

def inverseCoordinateValues (s : Side) : Fin 4 → CP :=
  match s with
  | .left => X
  | .right => ![C ((2:ℂ)⁻¹)*(X 0+X 2),C ((2:ℂ)⁻¹)*X 1,
      C ((2:ℂ)⁻¹)*(X 0-X 2),C ((2:ℂ)⁻¹)*X 3]

def coordinateMap (s : Side) : CP →ₐ[ℂ] CP := aeval (coordinateValues s)
def inverseCoordinateMap (s : Side) : CP →ₐ[ℂ] CP := aeval (inverseCoordinateValues s)

private theorem half_relation : (C ((2:ℂ)⁻¹) : CP)*2=1 := by
  rw [←map_ofNat (C : ℂ →+* CP) 2,←map_mul]
  norm_num

theorem coordinateMap_inverse (s : Side) :
    (coordinateMap s).comp (inverseCoordinateMap s)=AlgHom.id ℂ CP := by
  apply MvPolynomial.algHom_ext
  intro i
  cases s
  · simp [coordinateMap,inverseCoordinateMap,coordinateValues,inverseCoordinateValues]
  · fin_cases i <;>
      simp [coordinateMap,inverseCoordinateMap,coordinateValues,inverseCoordinateValues,
        Matrix.cons_val_succ,Fin.reduceSucc,map_ofNat]
    · linear_combination (X 0:CP)*half_relation
    · linear_combination (X 1:CP)*half_relation
    · linear_combination (X 2:CP)*half_relation
    · linear_combination (X 3:CP)*half_relation

theorem inverse_coordinateMap (s : Side) :
    (inverseCoordinateMap s).comp (coordinateMap s)=AlgHom.id ℂ CP := by
  apply MvPolynomial.algHom_ext
  intro i
  cases s
  · simp [coordinateMap,inverseCoordinateMap,coordinateValues,inverseCoordinateValues]
  · fin_cases i <;>
      simp [coordinateMap,inverseCoordinateMap,coordinateValues,inverseCoordinateValues,
        Matrix.cons_val_succ,Fin.reduceSucc,map_ofNat]
    · linear_combination (X 0:CP)*half_relation
    · linear_combination (X 1:CP)*half_relation
    · linear_combination (X 2:CP)*half_relation
    · linear_combination (X 3:CP)*half_relation

def coordinateEquiv (s : Side) : CP ≃ₐ[ℂ] CP :=
  AlgEquiv.ofAlgHom (coordinateMap s) (inverseCoordinateMap s)
    (coordinateMap_inverse s) (inverse_coordinateMap s)

theorem coordinateMap_originalQuadric_left (r : ℂ) :
    coordinateMap .left (originalQuadric .left r)=quadric .left r := by
  simp [coordinateMap,coordinateValues,originalQuadric,quadric]

theorem coordinateMap_originalQuadric_right (r : ℂ) :
    coordinateMap .right (originalQuadric .right r)=2*quadric .right r := by
  simp [coordinateMap,coordinateValues,originalQuadric,quadric,
    Matrix.cons_val_succ,Fin.reduceSucc]
  ring

theorem coordinateMap_originalCubic_left (r ι : ℂ) :
    coordinateMap .left (originalCubic ι)=cubic .left r ι+X 0*quadric .left r := by
  simp [coordinateMap,coordinateValues,originalCubic,cubic,quadric]
  ring

theorem coordinateMap_originalCubic_right (r ι : ℂ) :
    coordinateMap .right (originalCubic ι)=
      -4*cubic .right r ι+(6*X 0-2*X 3)*quadric .right r := by
  simp [coordinateMap,coordinateValues,originalCubic,cubic,quadric,map_ofNat,
    Matrix.cons_val_succ,Fin.reduceSucc]
  ring

private theorem span_pair_scale_first {A : Type*} [CommRing A]
    (q h u : A) (hu : IsUnit u) : Ideal.span {u*q,h}=Ideal.span {q,h} := by
  rw [Ideal.span_insert,Ideal.span_singleton_mul_left_unit hu,←Ideal.span_insert]

private theorem span_pair_scale_second {A : Type*} [CommRing A]
    (q h u : A) (hu : IsUnit u) : Ideal.span {q,u*h}=Ideal.span {q,h} := by
  rw [Ideal.span_pair_comm,span_pair_scale_first _ _ _ hu,Ideal.span_pair_comm]

theorem originalCurveIdeal_map (s : Side) (r ι : ℂ) :
    curveIdeal s r ι=(originalCurveIdeal s r ι).map (coordinateEquiv s).toRingHom := by
  simp only [originalCurveIdeal,Ideal.map_span,Set.image_insert_eq,Set.image_singleton]
  change Ideal.span {quadric s r,cubic s r ι}=
    Ideal.span {coordinateMap s (originalQuadric s r),coordinateMap s (originalCubic ι)}
  cases s
  · rw [coordinateMap_originalQuadric_left,coordinateMap_originalCubic_left,
      Ideal.span_pair_add_mul_left]
  · rw [coordinateMap_originalQuadric_right,coordinateMap_originalCubic_right]
    have htwo : IsUnit (2:CP) := by
      simpa only [map_ofNat] using (isUnit_iff_ne_zero.mpr (by norm_num : (2:ℂ)≠0)).map (C : ℂ →+* CP)
    have hfour : IsUnit (-4:CP) := by
      simpa only [map_neg,map_ofNat] using (isUnit_iff_ne_zero.mpr (by norm_num : (-4:ℂ)≠0)).map (C : ℂ →+* CP)
    rw [span_pair_scale_first _ _ _ htwo,Ideal.span_pair_add_mul_left,
      span_pair_scale_second _ _ _ hfour]

/-- An explicit algebra equivalence with the original curve quotient. -/
def originalCurveEquiv (s : Side) (r ι : ℂ) :
    (CP ⧸ originalCurveIdeal s r ι) ≃ₐ[ℂ] CurveRing s r ι :=
  Ideal.quotientEquivAlg _ _ (coordinateEquiv s) (originalCurveIdeal_map s r ι)

theorem originalCurveEquiv_mk (s : Side) (r ι : ℂ) (p : CP) :
    originalCurveEquiv s r ι (Ideal.Quotient.mk (originalCurveIdeal s r ι) p)=
      Ideal.Quotient.mk (curveIdeal s r ι) (coordinateMap s p) := rfl

def originalRestrictionValues (s : Side) (r : ℂ) : Fin 5 → CP :=
  match s with
  | .left => ![X 0,X 1,X 2,X 3,-X 2^2]
  | .right => ![X 0,X 1,X 2,X 3,C r*X 1*X 3]

def originalSubstitution (s : Side) (r : ℂ) : MvPolynomial (Fin 5) ℂ →ₐ[ℂ] CP :=
  aeval (originalRestrictionValues s r)

theorem coordinateMap_substitution (s : Side) (r : ℂ) :
    (coordinateMap s).comp (originalSubstitution s r)=substitution s r := by
  apply MvPolynomial.algHom_ext
  intro i
  cases s <;> fin_cases i <;>
    simp [coordinateMap,coordinateValues,originalSubstitution,originalRestrictionValues,
      substitution,restrictionValues,Matrix.cons_val_succ,Fin.reduceSucc,map_ofNat] <;> ring

theorem originalSubstitution_h (s : Side) (r ι : ℂ) :
    originalSubstitution s r (smoothH ι)=originalCubic ι := by
  cases s <;>
    simp [originalSubstitution,originalRestrictionValues,smoothH,smoothB,smoothA,
      originalCubic,Matrix.cons_val_succ,Fin.reduceSucc] <;> ring

end CycleQ2CurveRestriction

#print axioms CycleQ2CurveRestriction.originalCurveEquiv
#print axioms CycleQ2CurveRestriction.coordinateMap_substitution
end
end

/- Component: continuation_3/SegreComplexChartExact.lean -/
section
/-! # Actual complex Segre exactness on the coordinate Čech cover -/

noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2SegreComplexChartExact

open MvPolynomial Matrix CycleQ2SegreComplexBasepoint CycleQ2SegreTangentLocal
  CycleQ2IncidenceFirstOrder CycleQ2SegreRelationsLocal CycleQ2SeedQuotientFiniteFree
  CycleQ2SeedCechLocalization CycleQ2SeedCechLocalizedBasis

abbrev Chart (s : Finset (Fin 3)) := SeedLocal ℂ 57 Complex.I s

theorem coordinate_remaining (j : Fin 3) :
    coordinate (remainingIndex j) = algebraMap (Base ℂ) ComplexSeedRing (X j) := by
  change Ideal.Quotient.mk _ (X (remainingIndex j)) =
    Ideal.Quotient.mk _ (remainingInclusion ℂ (X j))
  simp [remainingInclusion]

theorem base_coordinate_unit (s : Finset (Fin 3)) (j : Fin 3) (hj : j ∈ s) :
    IsUnit (algebraMap (Base ℂ) (coordinateLocalization ℂ s) (X j)) := by
  have hd : (X j : Base ℂ) ∣ baseProduct ℂ s := Finset.dvd_prod_of_mem X hj
  exact isUnit_of_dvd_unit ((algebraMap (Base ℂ) (coordinateLocalization ℂ s)).map_dvd hd)
    (IsLocalization.Away.algebraMap_isUnit (S := coordinateLocalization ℂ s) _)

theorem seed_coordinate_unit (s : Finset (Fin 3)) (j : Fin 3) (hj : j ∈ s) :
    IsUnit (algebraMap ComplexSeedRing (Chart s) (coordinate (remainingIndex j))) := by
  rw [coordinate_remaining, ← IsScalarTower.algebraMap_apply (Base ℂ) ComplexSeedRing (Chart s)]
  rw [IsScalarTower.algebraMap_apply (Base ℂ) (coordinateLocalization ℂ s) (Chart s)]
  exact (base_coordinate_unit s j hj).map
    (algebraMap (coordinateLocalization ℂ s) (Chart s))

def chartMatrix (s : Finset (Fin 3)) : Matrix (Fin 3) (Fin 3) (Chart s) :=
  (algebraMap ComplexSeedRing (Chart s)).mapMatrix matrix

theorem chartMatrix_cofactors (s : Finset (Fin 3)) :
    CycleQ2SegreLocal.cofactors (chartMatrix s) = 0 := by
  rw [chartMatrix, ← map_cofactors]
  change (algebraMap ComplexSeedRing (Chart s)).mapMatrix
    (CycleQ2SegreLocal.cofactors (seedQuotientMatrix (57 : ℂ) Complex.I)) = 0
  rw [seedQuotientMatrix_cofactors]
  ext i j
  change algebraMap ComplexSeedRing (Chart s) 0 = 0
  exact map_zero _

theorem chartMatrix_entries_generate (s : Finset (Fin 3)) (hs : s.Nonempty) :
    Ideal.span (Set.range (fun ij : Fin 3 × Fin 3 => chartMatrix s ij.1 ij.2)) = ⊤ := by
  obtain ⟨j,hj⟩ := hs
  let φ := algebraMap ComplexSeedRing (Chart s)
  have hm := Ideal.mem_map_of_mem φ (seed_coordinate_power_mem (remainingIndex j))
  have hu : IsUnit (φ (coordinate (remainingIndex j)^coordinatePower (remainingIndex j))) := by
    rw [map_pow]
    exact (seed_coordinate_unit s j hj).pow _
  have ht := Ideal.eq_top_of_isUnit_mem _ hm hu
  simpa only [entryIdeal, Ideal.map_span, ← Set.range_comp, Function.comp_def, φ,
    chartMatrix, RingHom.mapMatrix_apply, Matrix.map_apply] using ht

/-- Actual complex local exactness with its basepoint-freeness premise
discharged by the nonconstructive arithmetic argument. -/
theorem coordinate_chart_relations_exact (s : Finset (Fin 3)) (hs : s.Nonempty)
    (C : Matrix (Fin 3) (Fin 3) (Chart s)) :
    CycleQ2SegreRelations.relations (chartMatrix s) *ᵥ vector C = 0 ↔
      ∃ N : Matrix (Fin 3) (Fin 3) (Chart s), cofactorDifferential (chartMatrix s) N = C :=
  entry_ideal_relations_exact _ _ (chartMatrix_cofactors s) (chartMatrix_entries_generate s hs)

theorem coordinate_chart_ker_eq_range (s : Finset (Fin 3)) (hs : s.Nonempty) :
    LinearMap.ker (relationsLinear (chartMatrix s)) =
      LinearMap.range (cofactorDifferentialLinear (chartMatrix s)) :=
  entry_ideal_ker_eq_range _ (chartMatrix_cofactors s) (chartMatrix_entries_generate s hs)

end CycleQ2SegreComplexChartExact

#print axioms CycleQ2SegreComplexChartExact.chartMatrix_entries_generate
#print axioms CycleQ2SegreComplexChartExact.coordinate_chart_relations_exact
#print axioms CycleQ2SegreComplexChartExact.coordinate_chart_ker_eq_range
end
end
