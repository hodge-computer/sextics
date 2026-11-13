import Proposal.GeometricTarget08Part02

/-! Continuation of GeometricTarget08.lean; complete source components and declarations. -/

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

abbrev SeedRing (r ι : R) := Poly R ⧸ equationsIdeal (smoothH ι) (smoothF r ι)

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


/- Component: continuation_3/SparseGaussianNaturality.lean -/
section
set_option maxHeartbeats 1000000
set_option Elab.async false

namespace CycleQ2SparseGaussianPolynomial
variable {R S : Type*} [CommRing R] [CommRing S]
variable (φ : GaussianInt →+* R) (ψ : R →+* S)

theorem map_eval (x : Fin 5 → R) (p : Sparse) :
    ψ (eval φ x p) = eval (ψ.comp φ) (fun j => ψ (x j)) p := by
  induction p with
  | nil => simp
  | cons a p ih =>
    simp only [eval_cons, map_add, ih, termValue, monomial,
      map_mul, map_pow, RingHom.comp_apply]

theorem map_evalLayers (x : Fin 5 → R) (z : R) (p : Layers) :
    ψ (evalLayers φ x z p) =
      evalLayers (ψ.comp φ) (fun j => ψ (x j)) (ψ z) p := by
  induction p with
  | nil => simp [evalLayers]
  | cons a p ih => simp only [evalLayers, map_add, map_mul, map_eval, ih]

theorem map_evalBlocks (x : Fin 5 → R) (z w : R) (p : Blocks) :
    ψ (evalBlocks φ x z w p) =
      evalBlocks (ψ.comp φ) (fun j => ψ (x j)) (ψ z) (ψ w) p := by
  induction p with
  | nil => simp [evalBlocks]
  | cons a p ih => simp only [evalBlocks, map_add, map_mul, map_evalLayers, ih]

theorem map_evalTowers (x : Fin 5 → R) (z w v : R) (p : Towers) :
    ψ (evalTowers φ x z w v p) =
      evalTowers (ψ.comp φ) (fun j => ψ (x j)) (ψ z) (ψ w) (ψ v) p := by
  induction p with
  | nil => simp [evalTowers]
  | cons a p ih => simp only [evalTowers, map_add, map_mul, map_evalBlocks, ih]

end CycleQ2SparseGaussianPolynomial

#print axioms CycleQ2SparseGaussianPolynomial.map_evalTowers
end


/- Component: continuation_3/SparseGaussianNormalForm.lean -/
section
/-! A sparse reducer for the actual two monic seed equations.

The semantic statement holds for every fuel bound, because exhaustion retains
the unreduced monomial. Concrete zero checks therefore do not need to trust a
termination estimate, an externally supplied quotient, or a normal-form oracle.
-/

set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
set_option Elab.async false

namespace CycleQ2SparseGaussianPolynomial

def oneLayers : Layers := [[((0,0,0,0,0),1)]]

def monomialTower (c : Layers) (a b : ℕ) : Towers :=
  List.replicate b [] ++ [List.replicate a [] ++ [c]]

def scaleTower (c : Layers) (p : Towers) : Towers :=
  p.map (fun q => q.map (mulLayers c))

/-- The intended relations are z³=a₀+a₁*z and w³=b₀−z⁶. -/
def normalCore (a₀ a₁ b₀ : Layers) : ℕ → ℕ → ℕ → Towers
  | 0, a, b => monomialTower oneLayers a b
  | n+1, a, b =>
      if 3 ≤ b then
        addTowers (scaleTower b₀ (normalCore a₀ a₁ b₀ n a (b-3)))
          (negTowers (normalCore a₀ a₁ b₀ n (a+6) (b-3)))
      else if 3 ≤ a then
        addTowers (scaleTower a₀ (normalCore a₀ a₁ b₀ n (a-3) b))
          (scaleTower a₁ (normalCore a₀ a₁ b₀ n (a-2) b))
      else monomialTower oneLayers a b

def normalizeBlock (a₀ a₁ b₀ : Layers) (fuel b : ℕ) : ℕ → Blocks → Towers
  | _, [] => []
  | a, c::p =>
      addTowers (scaleTower c (normalCore a₀ a₁ b₀ fuel a b))
        (normalizeBlock a₀ a₁ b₀ fuel b (a+1) p)

def normalizeTowerFrom (a₀ a₁ b₀ : Layers) (fuel : ℕ) : ℕ → Towers → Towers
  | _, [] => []
  | b, q::p => addTowers (normalizeBlock a₀ a₁ b₀ fuel b 0 q)
      (normalizeTowerFrom a₀ a₁ b₀ fuel (b+1) p)

def normalizeTower (a₀ a₁ b₀ : Layers) (fuel : ℕ) (p : Towers) : Towers :=
  normalizeTowerFrom a₀ a₁ b₀ fuel 0 p

section Soundness
variable {R : Type*} [CommRing R]
variable (φ : GaussianInt →+* R) (x : Fin 5 → R) (w z v : R)

theorem eval_oneLayers : evalLayers φ x v oneLayers = 1 := by
  simp [oneLayers, evalLayers, eval, termValue, monomial]

theorem evalBlocks_shift (n : ℕ) (p : Blocks) :
    evalBlocks φ x z v (List.replicate n [] ++ p) = z^n * evalBlocks φ x z v p := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [List.replicate_succ, List.cons_append, evalBlocks, evalLayers, ih, pow_succ]
    ring

theorem evalTowers_shift (n : ℕ) (p : Towers) :
    evalTowers φ x w z v (List.replicate n [] ++ p) =
      w^n * evalTowers φ x w z v p := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [List.replicate_succ, List.cons_append, evalTowers, evalBlocks, ih, pow_succ]
    ring

theorem eval_monomialTower (c : Layers) (a b : ℕ) :
    evalTowers φ x w z v (monomialTower c a b) =
      z^a * w^b * evalLayers φ x v c := by
  simp only [monomialTower, evalTowers_shift, evalTowers, evalBlocks_shift,
    evalBlocks, mul_zero, add_zero]
  ring

theorem eval_scaleTower (c : Layers) (p : Towers) :
    evalTowers φ x w z v (scaleTower c p) =
      evalLayers φ x v c * evalTowers φ x w z v p := by
  induction p with
  | nil => simp [scaleTower, evalTowers]
  | cons q p ih =>
    simp only [scaleTower, List.map_cons, evalTowers, eval_scaleBlocks] at ⊢ ih
    rw [ih]
    ring

variable (a₀ a₁ b₀ : Layers)
variable (hz : z^3 = evalLayers φ x v a₀ + evalLayers φ x v a₁ * z)
variable (hw : w^3 = evalLayers φ x v b₀ - z^6)

include hz hw

theorem eval_normalCore (n a b : ℕ) :
    evalTowers φ x w z v (normalCore a₀ a₁ b₀ n a b) = z^a * w^b := by
  induction n generalizing a b with
  | zero => rw [normalCore, eval_monomialTower, eval_oneLayers, mul_one]
  | succ n ih =>
    by_cases hb : 3 ≤ b
    · simp only [normalCore, if_pos hb, eval_addTowers, eval_scaleTower, eval_negTowers, ih]
      calc
        evalLayers φ x v b₀ * (z^a * w^(b-3)) + -(z^(a+6) * w^(b-3)) =
            z^a * w^(b-3) * (evalLayers φ x v b₀-z^6) := by rw [pow_add]; ring
        _ = z^a * w^(b-3) * w^3 := by rw [hw]
        _ = z^a * w^b := by rw [mul_assoc, ← pow_add, Nat.sub_add_cancel hb]
    · by_cases ha : 3 ≤ a
      · simp only [normalCore, if_neg hb, if_pos ha, eval_addTowers, eval_scaleTower, ih]
        have haa : a-2 = a-3+1 := by omega
        calc
          evalLayers φ x v a₀ * (z^(a-3)*w^b) +
              evalLayers φ x v a₁ * (z^(a-2)*w^b) =
              z^(a-3) * w^b * (evalLayers φ x v a₀ + evalLayers φ x v a₁*z) := by
                rw [haa, pow_succ]
                ring
          _ = z^(a-3) * w^b * z^3 := by rw [hz]
          _ = z^a * w^b := by
            rw [mul_right_comm, ← pow_add, Nat.sub_add_cancel ha]
      · rw [normalCore, if_neg hb, if_neg ha, eval_monomialTower, eval_oneLayers, mul_one]

theorem eval_normalizeBlock (fuel b a : ℕ) (p : Blocks) :
    evalTowers φ x w z v (normalizeBlock a₀ a₁ b₀ fuel b a p) =
      z^a * w^b * evalBlocks φ x z v p := by
  induction p generalizing a with
  | nil => simp [normalizeBlock, evalTowers, evalBlocks]
  | cons c p ih =>
    simp only [normalizeBlock, eval_addTowers, eval_scaleTower,
      eval_normalCore φ x w z v a₀ a₁ b₀ hz hw, ih, evalBlocks, pow_succ]
    ring

theorem eval_normalizeTowerFrom (fuel b : ℕ) (p : Towers) :
    evalTowers φ x w z v (normalizeTowerFrom a₀ a₁ b₀ fuel b p) =
      w^b * evalTowers φ x w z v p := by
  induction p generalizing b with
  | nil => simp [normalizeTowerFrom, evalTowers]
  | cons q p ih =>
    simp only [normalizeTowerFrom, eval_addTowers,
      eval_normalizeBlock φ x w z v a₀ a₁ b₀ hz hw, ih, evalTowers, pow_zero, pow_succ]
    ring

/-- Exact semantic preservation under the two actual monic seed relations. -/
theorem eval_normalizeTower (fuel : ℕ) (p : Towers) :
    evalTowers φ x w z v (normalizeTower a₀ a₁ b₀ fuel p) =
      evalTowers φ x w z v p := by
  simpa only [normalizeTower, pow_zero, one_mul] using
    eval_normalizeTowerFrom φ x w z v a₀ a₁ b₀ hz hw fuel 0 p

end Soundness
end CycleQ2SparseGaussianPolynomial

#print axioms CycleQ2SparseGaussianPolynomial.eval_normalizeTower
end


/- Component: continuation_3/SparseModularFunctionalCore.lean -/
section
/-! Executable coefficient functionals. Each natural number stores8-bit
coefficient slots; its lookup defines the functional without any data invariant. -/
namespace CycleQ2SparseModularFunctional
open CycleQ2SparseGaussianPolynomial

abbrev WeightData := Fin 3 → Fin 3 → ℕ → ℕ → ℕ

def slot (n k : ℕ) : ℕ :=
  if n=0 then 0 else (n / CycleQ2BinaryNaturalPower.power 256 10 k) % 256

theorem slot_eq (n k : ℕ) : slot n k=(n / 256^k)%256 := by
  unfold slot
  rw [CycleQ2BinaryNaturalPower.power_eq]
  split_ifs with h
  · subst n; simp
  · rfl

def weight (W : WeightData) (i j : Fin 3) (e : Exponent) : ℕ :=
  slot (W i j e.2.2.2.2 e.1) (e.2.1+29*e.2.2.1)

def gmod (z : GaussianInt) : ℕ := ((z.re+33*z.im)%109).toNat

def dot (W : WeightData) (i j : Fin 3) (s : Exponent) : Sparse → ℕ
  | [] => 0
  | t::p =>
    let c := weight W i j (exponentAdd s t.1)
    if c=0 then dot W i j s p else (gmod t.2*c+dot W i j s p)%109

def shiftData (e : Exponent) (p : Sparse) : Sparse :=
  p.map (fun a => (exponentAdd e a.1,a.2))
def flattenLayersData : Layers → Sparse
  | [] => []
  | a::p => a ++ shiftData (0,1,0,0,0) (flattenLayersData p)
def flattenBlocksData : Blocks → Sparse
  | [] => []
  | a::p => flattenLayersData a ++ shiftData (1,0,0,0,0) (flattenBlocksData p)
def flattenTowersData : Towers → Sparse
  | [] => []
  | a::p => flattenBlocksData a ++ shiftData (0,0,0,0,1) (flattenTowersData p)

end CycleQ2SparseModularFunctional
end


/- Component: continuation_3/CurveRestrictionMatrixCheck.lean -/
section
/-! Structural-recursion checking of the two small modular inverse matrices. -/

set_option maxHeartbeats 1000000
set_option maxRecDepth 20000
set_option Elab.async false

namespace CycleQ2CurveRestrictionMatrixCheck

/-- A dot product computed entirely with natural-number residues. -/
def dotMod : List ℕ → List ℕ → ℕ
  | [], _ => 0
  | _, [] => 0
  | a::p, b::q => (a*b+dotMod p q)%109

section Soundness
variable {R : Type*} [CommRing R] [CharP R 109]

theorem dotMod_ofFn {n : ℕ} (a b : Fin n → ℕ) :
    (dotMod (List.ofFn a) (List.ofFn b) : R)=∑ i, (a i:R)*(b i:R) := by
  induction n with
  | zero => simp [dotMod]
  | succ n ih =>
    rw [List.ofFn_succ,List.ofFn_succ,dotMod,←CharP.cast_eq_mod R 109,
      Nat.cast_add,Nat.cast_mul,Fin.sum_univ_succ,ih]

theorem ofFn_getD (p : List ℕ) (n : ℕ) (hp : p.length=n) :
    List.ofFn (fun i : Fin n => p.getD i.val 0)=p := by
  subst n
  simpa only [List.getD_eq_getElem _ _ (Fin.isLt _)] using (List.ofFn_getElem (xs:=p))

theorem dotMod_cast (p q : List ℕ) (n : ℕ) (hp : p.length=n) (hq : q.length=n) :
    (dotMod p q:R)=∑ i : Fin n, (p.getD i.val 0:R)*(q.getD i.val 0:R) := by
  have h := dotMod_ofFn (R:=R) (fun i : Fin n => p.getD i.val 0)
    (fun i : Fin n => q.getD i.val 0)
  rw [ofFn_getD p n hp,ofFn_getD q n hq] at h
  exact h

def matrixOfRows {n : ℕ} (rows : Fin n → List ℕ) : Matrix (Fin n) (Fin n) R :=
  fun i j => ((rows i).getD j.val 0:R)

def matrixOfColumns {n : ℕ} (columns : Fin n → List ℕ) : Matrix (Fin n) (Fin n) R :=
  fun i j => ((columns j).getD i.val 0:R)

theorem product_eq_one_of_dot_checks {n : ℕ} (rows columns : Fin n → List ℕ)
    (hrows : ∀ i, (rows i).length=n) (hcolumns : ∀ j, (columns j).length=n)
    (hcheck : ∀ i j, dotMod (rows i) (columns j)=if i=j then 1 else 0) :
    matrixOfRows (R:=R) rows * matrixOfColumns columns = 1 := by
  ext i j
  rw [Matrix.mul_apply]
  have h := dotMod_cast (R:=R) (rows i) (columns j) n (hrows i) (hcolumns j)
  rw [hcheck] at h
  change (∑ k : Fin n, ((rows i).getD k.val 0:R)*((columns j).getD k.val 0:R))=_
  rw [←h]
  by_cases hij : i=j <;> simp [hij,Matrix.one_apply]

theorem determinant_ne_zero_of_dot_checks [Nontrivial R] {n : ℕ}
    (rows columns : Fin n → List ℕ)
    (hrows : ∀ i, (rows i).length=n) (hcolumns : ∀ j, (columns j).length=n)
    (hcheck : ∀ i j, dotMod (rows i) (columns j)=if i=j then 1 else 0) :
    (matrixOfRows (R:=R) rows).det≠0 := by
  have h := congrArg Matrix.det (product_eq_one_of_dot_checks (R:=R) rows columns hrows hcolumns hcheck)
  intro hz
  rw [Matrix.det_mul,hz,zero_mul,Matrix.det_one] at h
  exact zero_ne_one h

end Soundness
end CycleQ2CurveRestrictionMatrixCheck

#print axioms CycleQ2CurveRestrictionMatrixCheck.determinant_ne_zero_of_dot_checks
end


