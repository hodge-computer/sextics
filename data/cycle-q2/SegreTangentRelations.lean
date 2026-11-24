import Mathlib.Algebra.TrivSqZeroExt.Basic
import Proposal.SegreGenericLifting
import Proposal.SegreIncidencePresentation

/-! # Local tangent relations, graded projection and the finite free seed quotient -/

set_option Elab.async false

/- Component: continuation_3/SegreTangentLocal.lean -/
section
/-! # Local exactness of factor variations for the actual Segre tangent map

The entry differential kernel is computed on every unit-entry chart, including
the corresponding charts of the actual seed quotient.  Global section dimensions
and any global rank conclusion are deliberately separate obligations.
-/

noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2SegreTangentLocal

open CycleQ2SegreLocal CycleQ2IncidenceFirstOrder

variable {A : Type*} [CommRing A]

private lemma dual_snd_mul (x y : TrivSqZeroExt A A) :
    TrivSqZeroExt.snd (x*y) = x.fst*y.snd+x.snd*y.fst := rfl

def dualMatrix (M N : Matrix (Fin 3) (Fin 3) A) :
    Matrix (Fin 3) (Fin 3) (TrivSqZeroExt A A) := fun i j ↦ (M i j, N i j)

theorem dualMatrix_cofactors (M N : Matrix (Fin 3) (Fin 3) A) :
    cofactors (dualMatrix M N) =
      fun i j ↦ (cofactors M i j, cofactorDifferential M N i j) := by
  funext i j
  apply TrivSqZeroExt.ext
  · exact congrArg (fun T : Matrix (Fin 3) (Fin 3) A ↦ T j i)
      ((TrivSqZeroExt.fstHom A A A).map_adjugate (dualMatrix M N))
  · rw [cofactorDifferential_fin_three]
    simp only [cofactors, Matrix.adjugate_fin_three]
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.transpose_apply, Matrix.of_apply, Matrix.cons_val_zero',
        Matrix.cons_val_succ', dualMatrix, TrivSqZeroExt.snd_mk,
        TrivSqZeroExt.snd_sub, TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_neg,
        dual_snd_mul, TrivSqZeroExt.fst_mk] <;> ring

theorem linearized_minors_of_cofactorDifferential_zero (M N : Matrix (Fin 3) (Fin 3) A)
    (hM : cofactors M = 0) (hD : cofactorDifferential M N = 0) (i j k l : Fin 3) :
    M i j * N k l + N i j * M k l = M i l * N k j + N i l * M k j := by
  have hd : cofactors (dualMatrix M N) = 0 := by
    rw [dualMatrix_cofactors, hM, hD]
    rfl
  have hh := congrArg TrivSqZeroExt.snd
    (minors_of_cofactors_zero (dualMatrix M N) hd i j k l)
  simpa only [dual_snd_mul, dualMatrix, TrivSqZeroExt.fst_mk,
    TrivSqZeroExt.snd_mk] using hh


theorem cofactorDifferential_factor_variation (a b v w : Fin 3 → A) :
    cofactorDifferential (fun i j ↦ a i * b j)
      (fun i j ↦ v i * b j + a i * w j) = 0 := by
  rw [cofactorDifferential_fin_three]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.of_apply, Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.zero_apply] <;> ring

/-- The normalized factor variation is explicit, with zero variation in the
pivot coordinate of the normalized column. -/
theorem unit_pivot_tangent_factorization
    (M N : Matrix (Fin 3) (Fin 3) A) (hM : cofactors M = 0)
    (hD : cofactorDifferential M N = 0) (i0 j0 : Fin 3)
    (u : Aˣ) (hu : (u : A) = M i0 j0) :
    ∃ a v : Fin 3 → A,
      a i0 = 1 ∧ v i0 = 0 ∧
      (∀ i j, M i j = a i * M i0 j) ∧
      (∀ i j, N i j = v i * M i0 j + a i * N i0 j) := by
  let a : Fin 3 → A := fun i ↦ M i j0 * (↑(u⁻¹) : A)
  let v : Fin 3 → A := fun i ↦ (N i j0 - a i * N i0 j0) * (↑(u⁻¹) : A)
  have ha : a i0 = 1 := by
    dsimp [a]
    rw [← hu, u.mul_inv]
  have hv : v i0 = 0 := by
    dsimp [v]
    rw [ha, one_mul, sub_self, zero_mul]
  have hfac (i j : Fin 3) : M i j = a i * M i0 j :=
    unit_pivot_factorization M hM i0 j0 u hu i j
  refine ⟨a, v, ha, hv, hfac, ?_⟩
  intro i j
  have hlin := linearized_minors_of_cofactorDifferential_zero M N hM hD i j i0 j0
  rw [hfac i j, ← hu] at hlin
  dsimp [v, a] at hlin ⊢
  have hunit : (u : A) * (↑(u⁻¹) : A) = 1 := u.mul_inv
  linear_combination (↑(u⁻¹) : A) * hlin - N i j * hunit

/-- The ambiguity of unnormalized factor variations is exactly scalar
rescaling; this is the one-dimensional gauge term in the prospective global
section calculation. -/
theorem factor_variation_kernel (a b v w : Fin 3 → A)
    (i0 j0 : Fin 3) (ha : a i0 = 1) (u : Aˣ) (hu : (u : A) = b j0) :
    (∀ i j, v i * b j + a i * w j = 0) ↔
      ∃ c : A, (∀ i, v i = c * a i) ∧ (∀ j, w j = -(c * b j)) := by
  constructor
  · intro h
    have hw (j : Fin 3) : w j = -(v i0 * b j) := by
      have hj := h i0 j
      rw [ha, one_mul] at hj
      linear_combination hj
    refine ⟨v i0, ?_, hw⟩
    intro i
    have hz : (v i - v i0 * a i) * (u : A) = 0 := by
      have hi := h i j0
      rw [hw j0, ← hu] at hi
      linear_combination hi
    apply sub_eq_zero.mp
    calc
      v i - v i0 * a i = ((v i - v i0 * a i) * (u : A)) * (↑(u⁻¹) : A) := by
        rw [mul_assoc, u.mul_inv, mul_one]
      _ = 0 := by rw [hz, zero_mul]
  · rintro ⟨c, hv, hw⟩ i j
    rw [hv i, hw j]
    ring

section Maps

variable {B : Type*} [CommRing B]

theorem map_cofactors (f : A →+* B) (M : Matrix (Fin 3) (Fin 3) A) :
    f.mapMatrix (cofactors M) = cofactors (f.mapMatrix M) := by
  ext i j
  exact congrArg (fun T : Matrix (Fin 3) (Fin 3) B ↦ T j i) (f.map_adjugate M)

theorem map_cofactorDifferential (f : A →+* B) (M N : Matrix (Fin 3) (Fin 3) A) :
    f.mapMatrix (cofactorDifferential M N) =
      cofactorDifferential (f.mapMatrix M) (f.mapMatrix N) := by
  simp only [cofactorDifferential, map_sub, map_cofactors, map_add]

end Maps

section ActualSeed

open MvPolynomial CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations

variable {R : Type*} [CommRing R]


def seedQuotientMatrix (r ι : R) : Matrix (Fin 3) (Fin 3) (SeedRing r ι) :=
  (Ideal.Quotient.mk _).mapMatrix (rawSeedMatrix r)

theorem seedQuotientMatrix_cofactors (r ι : R) : cofactors (seedQuotientMatrix r ι) = 0 := by
  rw [seedQuotientMatrix, ← map_cofactors]
  ext i j
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (rawSeedMatrix_cofactor_mem r ι i j)

/-- This applies the local exactness theorem to the literal seed quotient,
with cofactor vanishing proved from the published polynomial factorization. -/
theorem seed_quotient_tangent_factorization (r ι : R)
    (N : Matrix (Fin 3) (Fin 3) (Poly R))
    (hN : ∀ i j, cofactorDifferential (rawSeedMatrix r) N i j ∈
      equationsIdeal (smoothH ι) (smoothF r ι))
    (i0 j0 : Fin 3) (u : (SeedRing r ι)ˣ)
    (hu : (u : SeedRing r ι) = seedQuotientMatrix r ι i0 j0) :
    ∃ a v : Fin 3 → SeedRing r ι,
      a i0 = 1 ∧ v i0 = 0 ∧
      (∀ i j, seedQuotientMatrix r ι i j = a i * seedQuotientMatrix r ι i0 j) ∧
      (∀ i j, Ideal.Quotient.mk _ (N i j) =
        v i * seedQuotientMatrix r ι i0 j + a i * Ideal.Quotient.mk _ (N i0 j)) := by
  apply unit_pivot_tangent_factorization (seedQuotientMatrix r ι)
    ((Ideal.Quotient.mk _).mapMatrix N) (seedQuotientMatrix_cofactors r ι) _ i0 j0 u hu
  rw [seedQuotientMatrix, ← map_cofactorDifferential]
  ext i j
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (hN i j)

end ActualSeed

end CycleQ2SegreTangentLocal

#print axioms CycleQ2SegreTangentLocal.unit_pivot_tangent_factorization
#print axioms CycleQ2SegreTangentLocal.factor_variation_kernel
#print axioms CycleQ2SegreTangentLocal.seed_quotient_tangent_factorization
end
end

/- Component: continuation_3/cylinder_bridge/SegreWeightedProjection.lean -/
section
/-! # Homogeneous projection for the literal Segre cofactor differential -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000

namespace CycleQ2SegreWeightedProjection

open MvPolynomial Matrix CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations
  CycleQ2IncidenceFirstOrder CycleQ2WeightedComponent

variable {R : Type*} [CommRing R]

def matrixComponent (d : Grade) (P : Matrix (Fin 3) (Fin 3) (Poly R)) :
    Matrix (Fin 3) (Fin 3) (Poly R) :=
  fun i j => weightedHomogeneousComponent fullGrading d (P i j)

/-- Projection of the actual cofactor differential is obtained by projecting
the input to the corresponding shifted degree and cubic character. -/
theorem cofactorDifferential_component (M P : Matrix (Fin 3) (Fin 3) (Poly R))
    (hM : ∀ i j, HG (M i j) (14,0)) (d : Grade) :
    matrixComponent (d+(28,0)) (cofactorDifferential M P)=
      cofactorDifferential M (matrixComponent (d+(14,0)) P) := by
  have hleft (i j k l : Fin 3) :
      weightedHomogeneousComponent fullGrading (d+(28,0)) (M i j*P k l)=
        M i j*weightedHomogeneousComponent fullGrading (d+(14,0)) (P k l) := by
    have heq : d+(28,0)=(14,0)+(d+(14,0)) := by
      apply Prod.ext
      · change d.1+28=14+(d.1+14); omega
      · change d.2+0=0+(d.2+0); simp
    rw [heq,component_mul_left fullGrading _ _ (14,0) (d+(14,0)) (hM i j)]
  have hright (i j k l : Fin 3) :
      weightedHomogeneousComponent fullGrading (d+(28,0)) (P i j*M k l)=
        weightedHomogeneousComponent fullGrading (d+(14,0)) (P i j)*M k l := by
    rw [mul_comm (P i j) (M k l),hleft,mul_comm]
  rw [cofactorDifferential_fin_three,cofactorDifferential_fin_three]
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp only [matrixComponent,Matrix.of_apply,Matrix.cons_val_zero',Matrix.cons_val_succ',
      neg_mul,map_add,map_sub,map_neg,hleft,hright]

/-- The equations ideal of the actual smooth seed is homogeneous in both
its weighted degree and its cubic character. -/
local instance : GradedAlgebra (weightedHomogeneousSubmodule R fullGrading) :=
  MvPolynomial.weightedGradedAlgebra R fullGrading

theorem equationsIdeal_homogeneous (r ι : R) :
    (equationsIdeal (smoothH ι) (smoothF r ι)).IsHomogeneous
      (weightedHomogeneousSubmodule R fullGrading) := by
  apply Ideal.homogeneous_span
  intro p hp
  rcases hp with (rfl|rfl)
  · exact ⟨(3,0),smoothH_homogeneous ι⟩
  · exact ⟨(6,0),smoothF_homogeneous r ι⟩

/-- Any exact polynomial cofactor equation modulo the actual seed ideal
remains exact after the corresponding homogeneous projection. -/
theorem projected_residual_mem (r ι : R)
    (M P C : Matrix (Fin 3) (Fin 3) (Poly R))
    (hM : ∀ i j, HG (M i j) (14,0)) (d : Grade)
    (hC : ∀ i j, HG (C i j) (d+(28,0)))
    (h : ∀ i j, cofactorDifferential M P i j-C i j ∈
      equationsIdeal (smoothH ι) (smoothF r ι)) :
    ∀ i j, cofactorDifferential M (matrixComponent (d+(14,0)) P) i j-C i j ∈
      equationsIdeal (smoothH ι) (smoothF r ι) := by
  intro i j
  have hh := weightedHomogeneousComponent_mem_of_mem R fullGrading
    (equationsIdeal_homogeneous r ι) (h i j) (d+(28,0))
  rw [map_sub,(hC i j).weightedHomogeneousComponent_same] at hh
  have hm := congrArg (fun A => A i j) (cofactorDifferential_component M P hM d)
  change weightedHomogeneousComponent fullGrading (d+(28,0)) (cofactorDifferential M P i j)=_ at hm
  rw [hm] at hh
  exact hh

end CycleQ2SegreWeightedProjection

#print axioms CycleQ2SegreWeightedProjection.cofactorDifferential_component
#print axioms CycleQ2SegreWeightedProjection.projected_residual_mem
end
end

/- Component: continuation_3/SeedQuotientFiniteFree.lean -/
section
/-! # The actual seed quotient is finite free over the three remaining coordinates

The quotient remains `Poly R / (smoothH,smoothF)`.  Regrouping variables is used
only to construct its basis over `R[x₁,x₂,x₃]`; the resulting basis vectors are
the actual classes of `x₀^a*w^b` for `a,b<3`.
-/

noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2SeedQuotientFiniteFree

open MvPolynomial CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations
  CycleQ2IncidenceFirstOrder CycleQ2SegreTangentLocal
open scoped MonomialOrder

variable (R : Type*) [CommRing R]

/-- The nine basis vectors have their actual weighted degree and character.
The coefficient variables all have weighted degree one, so the degree shifts
of the free summands are `a + 2*b`. -/
theorem basisMonomial_homogeneous (ij : Fin 3 × Fin 3) :
    ((X 0 : Poly R) ^ ij.1.val * X 4 ^ ij.2.val).IsWeightedHomogeneous
      fullGrading (ij.1.val + 2 * ij.2.val, ((2 * ij.1.val : ℕ) : ZMod 3)) := by
  have hh := ((isWeightedHomogeneous_X R fullGrading 0).pow ij.1.val).mul
    ((isWeightedHomogeneous_X R fullGrading 4).pow ij.2.val)
  have hg : ij.1.val • fullGrading 0 + ij.2.val • fullGrading 4 =
      (ij.1.val + 2 * ij.2.val, ((2 * ij.1.val : ℕ) : ZMod 3)) := by
    simp [fullGrading, nsmul_eq_mul, mul_comm]
  exact hg ▸ hh

theorem seedBasis_mem_gradedPiece [Nontrivial R] (r ι : R) (ij : Fin 3 × Fin 3) :
    seedBasis R r ι ij ∈ CycleQ2IncidenceGradedBasis.quotientPiece fullGrading
      (smoothH ι) (smoothF r ι)
      (ij.1.val + 2 * ij.2.val, ((2 * ij.1.val : ℕ) : ZMod 3)) := by
  rw [seedBasis_apply]
  exact Submodule.mem_map.mpr ⟨_, basisMonomial_homogeneous R ij, rfl⟩

end CycleQ2SeedQuotientFiniteFree

#print axioms CycleQ2SeedQuotientFiniteFree.seedBasis_apply
#print axioms CycleQ2SeedQuotientFiniteFree.seedQuotient_rank_nine
#print axioms CycleQ2SeedQuotientFiniteFree.seedBasis_mem_gradedPiece
end
end

/- Component: continuation_3/cylinder_bridge/SegreRelationsLocal.lean -/
section
/-! # Local exactness at the actual sixteen Segre relations

The literal relation rows first identify two scalar matrix products.  On a
unit-entry chart of the rank-one locus both scalars vanish.  A concrete lift
then proves exactness at the cofactor-variation term over an arbitrary
commutative ring.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000

namespace CycleQ2SegreRelationsLocal

open Matrix CycleQ2IncidenceFirstOrder CycleQ2SegreTangentLocal
open scoped BigOperators

variable {R : Type*} [CommRing R]

/-- The same row-major order as the nine published cofactor equations. -/
def vector (C : Matrix (Fin 3) (Fin 3) R) : Fin 9 → R :=
  ![C 0 0,C 0 1,C 0 2,C 1 0,C 1 1,C 1 2,C 2 0,C 2 1,C 2 2]

def leftProduct (M C : Matrix (Fin 3) (Fin 3) R) (i j : Fin 3) : R :=
  ∑ k, M i k*C j k

def rightProduct (M C : Matrix (Fin 3) (Fin 3) R) (i j : Fin 3) : R :=
  ∑ k, M k i*C k j

def ScalarProducts (M C : Matrix (Fin 3) (Fin 3) R) : Prop :=
  ∃ a b : R, (∀ i j, leftProduct M C i j=if i=j then a else 0) ∧
    (∀ i j, rightProduct M C i j=if i=j then b else 0)

theorem relations_mul_vector (M C : Matrix (Fin 3) (Fin 3) R) :
    CycleQ2SegreRelations.relations M *ᵥ vector C=
      ![leftProduct M C 0 1,
        leftProduct M C 0 2,
        leftProduct M C 1 0,
        leftProduct M C 1 2,
        leftProduct M C 2 0,
        leftProduct M C 2 1,
        rightProduct M C 1 0,
        rightProduct M C 2 0,
        rightProduct M C 0 1,
        rightProduct M C 2 1,
        rightProduct M C 0 2,
        rightProduct M C 1 2,
        leftProduct M C 1 1-leftProduct M C 0 0,
        leftProduct M C 2 2-leftProduct M C 0 0,
        rightProduct M C 1 1-rightProduct M C 0 0,
        rightProduct M C 2 2-rightProduct M C 0 0] := by
  funext k
  fin_cases k <;>
    norm_num [CycleQ2SegreRelations.relations,vector,Matrix.mulVec,dotProduct,
      leftProduct,rightProduct,Fin.sum_univ_succ,Matrix.cons_val_succ] <;> ring

/-- The sixteen concrete rows are exactly the off-diagonal vanishing and
same-diagonal identities for `M*Cᵀ` and `Mᵀ*C`. -/
theorem relations_zero_iff_scalarProducts (M C : Matrix (Fin 3) (Fin 3) R) :
    CycleQ2SegreRelations.relations M *ᵥ vector C=0 ↔ ScalarProducts M C := by
  constructor
  · intro h
    rw [relations_mul_vector] at h
    have h0 : leftProduct M C 0 1=0 := congrFun h 0
    have h1 : leftProduct M C 0 2=0 := congrFun h 1
    have h2 : leftProduct M C 1 0=0 := congrFun h 2
    have h3 : leftProduct M C 1 2=0 := congrFun h 3
    have h4 : leftProduct M C 2 0=0 := congrFun h 4
    have h5 : leftProduct M C 2 1=0 := congrFun h 5
    have h6 : rightProduct M C 1 0=0 := congrFun h 6
    have h7 : rightProduct M C 2 0=0 := congrFun h 7
    have h8 : rightProduct M C 0 1=0 := congrFun h 8
    have h9 : rightProduct M C 2 1=0 := congrFun h 9
    have h10 : rightProduct M C 0 2=0 := congrFun h 10
    have h11 : rightProduct M C 1 2=0 := congrFun h 11
    have h12 : leftProduct M C 1 1-leftProduct M C 0 0=0 := congrFun h 12
    have h13 : leftProduct M C 2 2-leftProduct M C 0 0=0 := congrFun h 13
    have h14 : rightProduct M C 1 1-rightProduct M C 0 0=0 := congrFun h 14
    have h15 : rightProduct M C 2 2-rightProduct M C 0 0=0 := congrFun h 15
    refine ⟨leftProduct M C 0 0,rightProduct M C 0 0,?_,?_⟩
    · intro i j
      fin_cases i <;> fin_cases j <;> norm_num <;> solve
        | exact h0 | exact h1 | exact h2 | exact h3 | exact h4 | exact h5
        | exact sub_eq_zero.mp h12 | exact sub_eq_zero.mp h13
    · intro i j
      fin_cases i <;> fin_cases j <;> norm_num <;> solve
        | exact h6 | exact h7 | exact h8 | exact h9 | exact h10 | exact h11
        | exact sub_eq_zero.mp h14 | exact sub_eq_zero.mp h15
  · rintro ⟨a,b,hl,hr⟩
    rw [relations_mul_vector]
    funext k
    fin_cases k <;>
      simp [hl,hr]

/-- Rank-one factorization with a unit pivot forces both scalar products to
vanish; no invertibility of 2 or 3 is used. -/
theorem products_zero_of_scalarProducts (M C : Matrix (Fin 3) (Fin 3) R)
    (hM : CycleQ2SegreLocal.cofactors M=0) (hs : ScalarProducts M C)
    (i0 j0 : Fin 3) (u : Rˣ) (hu : (u : R)=M i0 j0) :
    (∀ i j, leftProduct M C i j=0) ∧ (∀ i j, rightProduct M C i j=0) := by
  obtain ⟨a,b,hl,hr⟩ := hs
  have hlf (i j : Fin 3) : leftProduct M C i j=
      (M i j0*(↑(u⁻¹) : R))*leftProduct M C i0 j := by
    simp only [leftProduct,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [CycleQ2SegreLocal.unit_pivot_factorization M hM i0 j0 u hu i k]
    ring
  have hrf (i j : Fin 3) : rightProduct M C i j=
      (M i0 i*(↑(u⁻¹) : R))*rightProduct M C j0 j := by
    simp only [rightProduct,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [CycleQ2SegreLocal.unit_pivot_factorization M hM i0 j0 u hu k i]
    ring
  obtain ⟨i1,hi1⟩ : ∃ i1 : Fin 3, i1≠i0 := exists_ne i0
  obtain ⟨j1,hj1⟩ : ∃ j1 : Fin 3, j1≠j0 := exists_ne j0
  have ha : a=0 := by
    have hh := hlf i1 i1
    rw [hl i1 i1,hl i0 i1] at hh
    simpa [Ne.symm hi1] using hh
  have hb : b=0 := by
    have hh := hrf j1 j1
    rw [hr j1 j1,hr j0 j1] at hh
    simpa [Ne.symm hj1] using hh
  constructor
  · intro i j
    simp [hl,ha]
  · intro i j
    simp [hr,hb]

/-- On a unit chart the literal sixteen relations are equivalent to the two
actual annihilator identities. -/
theorem relations_zero_iff_products_zero (M C : Matrix (Fin 3) (Fin 3) R)
    (hM : CycleQ2SegreLocal.cofactors M=0)
    (i0 j0 : Fin 3) (u : Rˣ) (hu : (u : R)=M i0 j0) :
    CycleQ2SegreRelations.relations M *ᵥ vector C=0 ↔
      (∀ i j, leftProduct M C i j=0) ∧ (∀ i j, rightProduct M C i j=0) := by
  rw [relations_zero_iff_scalarProducts]
  constructor
  · exact fun hs => products_zero_of_scalarProducts M C hM hs i0 j0 u hu
  · rintro ⟨hl,hr⟩
    exact ⟨0,0,by simpa using hl,by simpa using hr⟩

/-- An explicit lift at the `(0,0)` pivot. -/
def pivotLift (u : Rˣ) (C : Matrix (Fin 3) (Fin 3) R) : Matrix (Fin 3) (Fin 3) R :=
  fun i j => if i=1 then
    if j=1 then (↑(u⁻¹) : R)*C 2 2 else if j=2 then -((↑(u⁻¹) : R)*C 2 1) else 0
  else if i=2 then
    if j=1 then -((↑(u⁻¹) : R)*C 1 2) else if j=2 then (↑(u⁻¹) : R)*C 1 1 else 0
  else 0

theorem pivotLift_differential (M C : Matrix (Fin 3) (Fin 3) R)
    (hl : ∀ i j, leftProduct M C i j=0)
    (hr : ∀ i j, rightProduct M C i j=0)
    (u : Rˣ) (hu : (u : R)=M 0 0) :
    cofactorDifferential M (pivotLift u C)=C := by
  have h01 := hl 0 1
  have h02 := hl 0 2
  have h11 := hl 1 1
  have h22 := hl 2 2
  have k00 := hr 0 0
  have k01 := hr 0 1
  have k02 := hr 0 2
  norm_num [leftProduct,rightProduct,Fin.sum_univ_succ,← hu] at h01 h02 h11 h22 k00 k01 k02
  have hunit : (u : R)*(↑(u⁻¹) : R)=1 := u.mul_inv
  have hfin2 (h : 2<3) : (⟨2,h⟩ : Fin 3)=2 := rfl
  have hn01 : (0 : Fin 3)≠1 := by decide
  have hn02 : (0 : Fin 3)≠2 := by decide
  have hn12 : (1 : Fin 3)≠2 := by decide
  have hn21 : (2 : Fin 3)≠1 := by decide
  rw [cofactorDifferential_fin_three]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [pivotLift,Matrix.cons_val_succ,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Fin.reduceFinMk,hfin2,hn01,hn02,hn12,hn21,← hu] <;> solve
    | linear_combination (↑(u⁻¹) : R)*(h11+h22-k00)+C 0 0*hunit
    | linear_combination -(↑(u⁻¹) : R)*k01+C 0 1*hunit
    | linear_combination -(↑(u⁻¹) : R)*k02+C 0 2*hunit
    | linear_combination -(↑(u⁻¹) : R)*h01+C 1 0*hunit
    | linear_combination C 1 1*hunit
    | linear_combination C 1 2*hunit
    | linear_combination -(↑(u⁻¹) : R)*h02+C 2 0*hunit

end CycleQ2SegreRelationsLocal
end
end
