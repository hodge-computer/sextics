import Proposal.GeometricFormalInputs03Part02

/-! Continuation of GeometricFormalInputs03.lean; complete source components and declarations. -/

set_option Elab.async false

/- Component: continuation_2/SegreSyzygyElimination.lean -/
section
/-!
# The actual nonlinear Segre relations and complementary-equation elimination

The sixteen rows are the twelve off-diagonal adjugate relations and four
diagonal differences. They are polynomial identities for every three by
three matrix, not identities only at the geometric seed.

The last two theorems justify dropping redundant equations after adjoining
an inverse of the complementary relation minor. They do not assume that a
selected square system has a solution; that input is supplied separately by
the trusted generic lifting theorem.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace CycleQ2SegreRelations
open Matrix

variable {R : Type*} [CommRing R]

def cofactors (M : Matrix (Fin 3) (Fin 3) R) : Fin 9 → R :=
  ![M 1 1*M 2 2-M 1 2*M 2 1,
    M 1 2*M 2 0-M 1 0*M 2 2,
    M 1 0*M 2 1-M 1 1*M 2 0,
    M 0 2*M 2 1-M 0 1*M 2 2,
    M 0 0*M 2 2-M 0 2*M 2 0,
    M 0 1*M 2 0-M 0 0*M 2 1,
    M 0 1*M 1 2-M 0 2*M 1 1,
    M 0 2*M 1 0-M 0 0*M 1 2,
    M 0 0*M 1 1-M 0 1*M 1 0]

def cofactorMatrix (M : Matrix (Fin 3) (Fin 3) R) : Matrix (Fin 3) (Fin 3) R :=
  !![cofactors M 0, cofactors M 1, cofactors M 2;
     cofactors M 3, cofactors M 4, cofactors M 5;
     cofactors M 6, cofactors M 7, cofactors M 8]

theorem cofactorMatrix_eq_transpose_adjugate (M : Matrix (Fin 3) (Fin 3) R) :
    cofactorMatrix M = M.adjugate.transpose := by
  rw [adjugate_fin_three]
  ext i j
  fin_cases i <;> fin_cases j
  · change M 1 1*M 2 2-M 1 2*M 2 1 = M 1 1*M 2 2-M 1 2*M 2 1
    ring
  · change M 1 2*M 2 0-M 1 0*M 2 2 = -(M 1 0*M 2 2)+M 1 2*M 2 0
    ring
  · change M 1 0*M 2 1-M 1 1*M 2 0 = M 1 0*M 2 1-M 1 1*M 2 0
    ring
  · change M 0 2*M 2 1-M 0 1*M 2 2 = -(M 0 1*M 2 2)+M 0 2*M 2 1
    ring
  · change M 0 0*M 2 2-M 0 2*M 2 0 = M 0 0*M 2 2-M 0 2*M 2 0
    ring
  · change M 0 1*M 2 0-M 0 0*M 2 1 = -(M 0 0*M 2 1)+M 0 1*M 2 0
    ring
  · change M 0 1*M 1 2-M 0 2*M 1 1 = M 0 1*M 1 2-M 0 2*M 1 1
    ring
  · change M 0 2*M 1 0-M 0 0*M 1 2 = -(M 0 0*M 1 2)+M 0 2*M 1 0
    ring
  · change M 0 0*M 1 1-M 0 1*M 1 0 = M 0 0*M 1 1-M 0 1*M 1 0
    ring

def relations (M : Matrix (Fin 3) (Fin 3) R) : Matrix (Fin 16) (Fin 9) R :=
  !![0,0,0, M 0 0,M 0 1,M 0 2, 0,0,0;
     0,0,0, 0,0,0, M 0 0,M 0 1,M 0 2;
     M 1 0,M 1 1,M 1 2, 0,0,0, 0,0,0;
     0,0,0, 0,0,0, M 1 0,M 1 1,M 1 2;
     M 2 0,M 2 1,M 2 2, 0,0,0, 0,0,0;
     0,0,0, M 2 0,M 2 1,M 2 2, 0,0,0;
     M 0 1,0,0, M 1 1,0,0, M 2 1,0,0;
     M 0 2,0,0, M 1 2,0,0, M 2 2,0,0;
     0,M 0 0,0, 0,M 1 0,0, 0,M 2 0,0;
     0,M 0 2,0, 0,M 1 2,0, 0,M 2 2,0;
     0,0,M 0 0, 0,0,M 1 0, 0,0,M 2 0;
     0,0,M 0 1, 0,0,M 1 1, 0,0,M 2 1;
     -M 0 0,-M 0 1,-M 0 2, M 1 0,M 1 1,M 1 2, 0,0,0;
     -M 0 0,-M 0 1,-M 0 2, 0,0,0, M 2 0,M 2 1,M 2 2;
     -M 0 0,M 0 1,0, -M 1 0,M 1 1,0, -M 2 0,M 2 1,0;
     -M 0 0,0,M 0 2, -M 1 0,0,M 1 2, -M 2 0,0,M 2 2]

/-- The sixteen genuine nonlinear polynomial relations on the nine cofactors. -/
theorem relations_cofactors (M : Matrix (Fin 3) (Fin 3) R) :
    relations M *ᵥ cofactors M = 0 := by
  funext i
  fin_cases i <;>
    norm_num [relations, cofactors, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> ring

variable {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n]

/-- At any point where the chosen complementary relation block is a unit,
vanishing of the selected equations forces all residual equations to vanish. -/
theorem residual_eq_zero_of_relation_block
    (A : Matrix n n R) (B : Matrix n m R) (v : n → R) (e : m → R)
    (hrel : A *ᵥ v + B *ᵥ e = 0) (he : e = 0) (hdet : IsUnit A.det) : v = 0 := by
  have hv : A *ᵥ v = 0 := by simpa [he] using hrel
  calc
    v = (A⁻¹ * A) *ᵥ v := by rw [nonsing_inv_mul A hdet, one_mulVec]
    _ = A⁻¹ *ᵥ (A *ᵥ v) := (mulVec_mulVec v A⁻¹ A).symm
    _ = 0 := by rw [hv, mulVec_zero]

/-- The elimination lemma after arbitrary coefficient evaluation, as needed
at the generic algebraic point produced by square-system lifting. -/
theorem evaluated_residual_eq_zero
    {S : Type*} [CommRing S] (f : R →+* S)
    (A : Matrix n n R) (B : Matrix n m R) (v : n → R) (e : m → R)
    (hrel : A *ᵥ v + B *ᵥ e = 0)
    (he : f ∘ e = 0) (hdet : IsUnit (f A.det)) : f ∘ v = 0 := by
  apply residual_eq_zero_of_relation_block (A.map f) (B.map f) (f ∘ v) (f ∘ e)
  · funext i
    change (A.map f *ᵥ (f ∘ v)) i + (B.map f *ᵥ (f ∘ e)) i = 0
    rw [← RingHom.map_mulVec, ← RingHom.map_mulVec, ← map_add]
    have hz := congrArg (fun z : n → R => z i) hrel
    change (A *ᵥ v) i + (B *ᵥ e) i = 0 at hz
    rw [hz, map_zero]
  · exact he
  · change IsUnit (f.mapMatrix A).det
    rw [← f.map_det]
    exact hdet

end CycleQ2SegreRelations

#print axioms CycleQ2SegreRelations.relations_cofactors
#print axioms CycleQ2SegreRelations.residual_eq_zero_of_relation_block
#print axioms CycleQ2SegreRelations.evaluated_residual_eq_zero
end


/- Component: continuation_2/SegreLocalFactorization.lean -/
section
/-!
# Local factorization of the actual three-by-three Segre equations

The nine equations are the row-major cofactors, i.e. the transpose of
mathlib's actual adjugate. Their vanishing is equivalent to all two-by-two
minors vanishing. On every chart where one entry is a unit, the matrix has
an explicit outer-product factorization. Its image has a generator whose
pivot coordinate is one, with the coordinate projection as a left inverse.
No global line-bundle, deformation, or geometric existence claim is made.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

noncomputable section
namespace CycleQ2SegreLocal

open Matrix
open scoped BigOperators

variable {R : Type*} [CommRing R]

/-- Row-major signed cofactors; the equation index is `(row,column)`. -/
def cofactors (M : Matrix (Fin 3) (Fin 3) R) : Matrix (Fin 3) (Fin 3) R :=
  M.adjugate.transpose

/-- The actual nine cofactor equations imply every two-by-two minor. -/
theorem minors_of_cofactors_zero (M : Matrix (Fin 3) (Fin 3) R)
    (h : cofactors M = 0) (i j k l : Fin 3) :
    M i j * M k l = M i l * M k j := by
  have ha : M.adjugate = 0 := by
    simpa [cofactors] using congrArg Matrix.transpose h
  rw [Matrix.adjugate_fin_three] at ha
  have h00 : M 1 1 * M 2 2 - M 1 2 * M 2 1 = 0 :=
    congrArg (fun A : Matrix (Fin 3) (Fin 3) R => A 0 0) ha
  have h01 : -(M 0 1 * M 2 2) + M 0 2 * M 2 1 = 0 :=
    congrArg (fun A : Matrix (Fin 3) (Fin 3) R => A 0 1) ha
  have h02 : M 0 1 * M 1 2 - M 0 2 * M 1 1 = 0 :=
    congrArg (fun A : Matrix (Fin 3) (Fin 3) R => A 0 2) ha
  have h10 : -(M 1 0 * M 2 2) + M 1 2 * M 2 0 = 0 :=
    congrArg (fun A : Matrix (Fin 3) (Fin 3) R => A 1 0) ha
  have h11 : M 0 0 * M 2 2 - M 0 2 * M 2 0 = 0 :=
    congrArg (fun A : Matrix (Fin 3) (Fin 3) R => A 1 1) ha
  have h12 : -(M 0 0 * M 1 2) + M 0 2 * M 1 0 = 0 :=
    congrArg (fun A : Matrix (Fin 3) (Fin 3) R => A 1 2) ha
  have h20 : M 1 0 * M 2 1 - M 1 1 * M 2 0 = 0 :=
    congrArg (fun A : Matrix (Fin 3) (Fin 3) R => A 2 0) ha
  have h21 : -(M 0 0 * M 2 1) + M 0 1 * M 2 0 = 0 :=
    congrArg (fun A : Matrix (Fin 3) (Fin 3) R => A 2 1) ha
  have h22 : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 0 :=
    congrArg (fun A : Matrix (Fin 3) (Fin 3) R => A 2 2) ha
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;> dsimp at * <;>
    solve
    | ring1
    | linear_combination h00
    | linear_combination -h00
    | linear_combination h01
    | linear_combination -h01
    | linear_combination h02
    | linear_combination -h02
    | linear_combination h10
    | linear_combination -h10
    | linear_combination h11
    | linear_combination -h11
    | linear_combination h12
    | linear_combination -h12
    | linear_combination h20
    | linear_combination -h20
    | linear_combination h21
    | linear_combination -h21
    | linear_combination h22
    | linear_combination -h22

/-- A unit entry gives a normalized column and the actual pivot row. -/
theorem unit_pivot_factorization (M : Matrix (Fin 3) (Fin 3) R)
    (h : cofactors M = 0) (i0 j0 : Fin 3) (u : Rˣ)
    (hu : (u : R) = M i0 j0) (i j : Fin 3) :
    M i j = (M i j0 * (↑(u⁻¹) : R)) * M i0 j := by
  have hm := minors_of_cofactors_zero M h i j i0 j0
  calc
    M i j = (M i j * M i0 j0) * (↑(u⁻¹) : R) := by
      rw [← hu, mul_assoc, Units.mul_inv, mul_one]
    _ = (M i j0 * M i0 j) * (↑(u⁻¹) : R) := by rw [hm]
    _ = (M i j0 * (↑(u⁻¹) : R)) * M i0 j := by ring

/-- Conversely, every literal outer product satisfies all nine equations. -/
theorem cofactors_outerProduct (a b : Fin 3 → R) :
    cofactors (fun i j => a i * b j) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cofactors, Matrix.adjugate_fin_three, Matrix.transpose_apply] <;> ring

/-- No field hypothesis is needed for the pivot chart. -/
theorem normalized_factorization (M : Matrix (Fin 3) (Fin 3) R)
    (h : cofactors M = 0) (i0 j0 : Fin 3) (hu : IsUnit (M i0 j0)) :
    ∃ a b : Fin 3 → R, a i0 = 1 ∧ b = M i0 ∧
      (∀ i j, M i j = a i * b j) := by
  obtain ⟨u, hu⟩ := hu
  refine ⟨fun i => M i j0 * (↑(u⁻¹) : R), M i0, ?_, rfl, ?_⟩
  · change M i0 j0 * (↑(u⁻¹) : R) = 1
    rw [← hu, Units.mul_inv]
  · exact unit_pivot_factorization M h i0 j0 u hu

/-- The normalized column generates the image. Its pivot coordinate gives
an explicit left inverse, so this local image is a free rank-one summand. -/
theorem image_generator_with_retraction (M : Matrix (Fin 3) (Fin 3) R)
    (h : cofactors M = 0) (i0 j0 : Fin 3) (hu : IsUnit (M i0 j0)) :
    ∃ a : Fin 3 → R,
      a i0 = 1 ∧
      (∀ x : Fin 3 → R, M *ᵥ x = (∑ j, M i0 j * x j) • a) ∧
      (∀ r : R, (r • a) i0 = r) ∧
      (∀ r : R, ∃ x : Fin 3 → R, M *ᵥ x = r • a) := by
  obtain ⟨u, hunit⟩ := hu
  let a : Fin 3 → R := fun i => M i j0 * (↑(u⁻¹) : R)
  have ha : a i0 = 1 := by
    dsimp [a]
    rw [← hunit, Units.mul_inv]
  have hf (i j : Fin 3) : M i j = a i * M i0 j :=
    unit_pivot_factorization M h i0 j0 u hunit i j
  have hmul (x : Fin 3 → R) : M *ᵥ x = (∑ j, M i0 j * x j) • a := by
    funext i
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j hj
    rw [hf]
    ring
  refine ⟨a, ha, hmul, ?_, ?_⟩
  · intro r
    simp [ha]
  · intro r
    refine ⟨Pi.single j0 ((↑(u⁻¹) : R) * r), ?_⟩
    rw [hmul]
    simp [Pi.single_apply, ← hunit]

end CycleQ2SegreLocal

#print axioms CycleQ2SegreLocal.minors_of_cofactors_zero
#print axioms CycleQ2SegreLocal.normalized_factorization
#print axioms CycleQ2SegreLocal.image_generator_with_retraction
end
end


/- Component: continuation_2/SegreImageLine.lean -/
section
/-!
# The actual image module on a Segre pivot chart

A vanishing cofactor matrix and a unit entry give an explicit linear
isomorphism from the coefficient ring to the matrix image. The separate
basepoint lemma shows how actual ideal-membership witnesses provide a
pivot after evaluation in a field. Neither theorem assumes a line bundle.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace CycleQ2SegreImage

open Matrix
open scoped BigOperators

variable {R : Type*} [CommRing R]

/-- The image submodule of the actual matrix map is a free line on any
unit-entry chart. The isomorphism is proved directly from the equations. -/
theorem image_linearEquiv (M : Matrix (Fin 3) (Fin 3) R)
    (h : CycleQ2SegreLocal.cofactors M = 0)
    (i0 j0 : Fin 3) (hu : IsUnit (M i0 j0)) :
    Nonempty (R ≃ₗ[R] LinearMap.range M.mulVecLin) := by
  obtain ⟨a, ha, hmul, hret, hsurj⟩ :=
    CycleQ2SegreLocal.image_generator_with_retraction M h i0 j0 hu
  let f : R →ₗ[R] LinearMap.range M.mulVecLin :=
    { toFun := fun r => ⟨r • a, hsurj r⟩
      map_add' := by
        intro r s
        apply Subtype.ext
        exact add_smul r s a
      map_smul' := by
        intro r s
        apply Subtype.ext
        exact mul_smul r s a }
  have hinj : Function.Injective f := by
    intro r s hrs
    have hval := congrArg (fun v : LinearMap.range M.mulVecLin => v.val i0) hrs
    change (r • a) i0 = (s • a) i0 at hval
    simpa only [hret] using hval
  have honto : Function.Surjective f := by
    intro y
    obtain ⟨x, hx⟩ := y.property
    refine ⟨∑ j, M i0 j * x j, ?_⟩
    apply Subtype.ext
    change (∑ j, M i0 j * x j) • a = y.val
    rw [← hmul]
    exact hx
  exact ⟨LinearEquiv.ofBijective f ⟨hinj, honto⟩⟩

/-- Ideal membership is enough to exclude a common zero of the matrix
entries wherever one of the tested coordinates is nonzero. -/
theorem exists_nonzero_entry_of_coordinate_powers
    {ι K : Type*} [Field K] (M : Matrix (Fin 3) (Fin 3) R)
    (coordinates : ι → R) (degrees : ι → ℕ)
    (hmem : ∀ i, coordinates i ^ degrees i ∈
      Ideal.span (Set.range (fun p : Fin 3 × Fin 3 => M p.1 p.2)))
    (φ : R →+* K) (hpoint : ∃ i, φ (coordinates i) ≠ 0) :
    ∃ i j, φ (M i j) ≠ 0 := by
  by_contra! hzero
  have hker : Ideal.span (Set.range (fun p : Fin 3 × Fin 3 => M p.1 p.2)) ≤
      RingHom.ker φ := by
    apply Ideal.span_le.mpr
    rintro z ⟨p, rfl⟩
    exact hzero p.1 p.2
  obtain ⟨i, hi⟩ := hpoint
  have hz : φ (coordinates i ^ degrees i) = 0 := hker (hmem i)
  rw [map_pow] at hz
  exact pow_ne_zero _ hi hz

/-- The same basepoint witnesses yield an actual unit-entry chart in any
field-valued point satisfying the nonzero-coordinate condition. -/
theorem exists_unit_entry_of_coordinate_powers
    {ι K : Type*} [Field K] (M : Matrix (Fin 3) (Fin 3) R)
    (coordinates : ι → R) (degrees : ι → ℕ)
    (hmem : ∀ i, coordinates i ^ degrees i ∈
      Ideal.span (Set.range (fun p : Fin 3 × Fin 3 => M p.1 p.2)))
    (φ : R →+* K) (hpoint : ∃ i, φ (coordinates i) ≠ 0) :
    ∃ i j, IsUnit (φ (M i j)) := by
  obtain ⟨i, j, hij⟩ := exists_nonzero_entry_of_coordinate_powers
    M coordinates degrees hmem φ hpoint
  exact ⟨i, j, isUnit_iff_ne_zero.mpr hij⟩

end CycleQ2SegreImage

#print axioms CycleQ2SegreImage.image_linearEquiv
#print axioms CycleQ2SegreImage.exists_nonzero_entry_of_coordinate_powers
#print axioms CycleQ2SegreImage.exists_unit_entry_of_coordinate_powers
end
end


/- Component: continuation_2/SegreCechDlog.lean -/
section
/-!
# Explicit overlap units and the Kähler Čech cocycle of a rank-one matrix

The common coefficient ring in these theorems may be the coordinate ring of
any overlap of unit-entry charts. No field hypothesis is used. The transition
units are calculated from the actual matrix entries and chosen pivot units.
The additive cocycle takes values in mathlib's universal Kähler module.

The first-column equations generate the same ideal on overlaps. A separate
nonzerodivisor hypothesis is needed to call their zero scheme an effective
Cartier divisor. This file does not construct a cycle class, a Gysin map, an
Abel--Jacobi map, or a rational primitive.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

noncomputable section
namespace CycleQ2SegreCech

open Matrix

variable {R : Type*} [CommRing R]

abbrev Chart := Fin 3 × Fin 3

/-- The image generator normalized to one at the pivot row. -/
def column (M : Matrix (Fin 3) (Fin 3) R) (p : Chart) (up : Rˣ) : Fin 3 → R :=
  fun i => M i p.2 * (↑(up⁻¹) : R)

private theorem transition_mul_reverse
    (M : Matrix (Fin 3) (Fin 3) R) (hM : CycleQ2SegreLocal.cofactors M = 0)
    (p q : Chart) (up uq : Rˣ)
    (hp : (up : R) = M p.1 p.2) (hq : (uq : R) = M q.1 q.2) :
    (M q.1 p.2 * (↑(up⁻¹) : R)) * (M p.1 q.2 * (↑(uq⁻¹) : R)) = 1 := by
  have hm := CycleQ2SegreLocal.minors_of_cofactors_zero M hM q.1 p.2 p.1 q.2
  calc
    _ = (M q.1 p.2 * M p.1 q.2) * ((↑(up⁻¹) : R) * (↑(uq⁻¹) : R)) := by ring
    _ = (M q.1 q.2 * M p.1 p.2) * ((↑(up⁻¹) : R) * (↑(uq⁻¹) : R)) := by rw [hm]
    _ = ((up : R) * ↑(up⁻¹)) * ((uq : R) * ↑(uq⁻¹)) := by rw [← hp, ← hq]; ring
    _ = 1 := by rw [Units.mul_inv, Units.mul_inv, mul_one]

/-- The unit carrying the normalized image generator on chart `q` to the
one on chart `p`. Its inverse is another explicit matrix-entry ratio. -/
def transition
    (M : Matrix (Fin 3) (Fin 3) R) (hM : CycleQ2SegreLocal.cofactors M = 0)
    (p q : Chart) (up uq : Rˣ)
    (hp : (up : R) = M p.1 p.2) (hq : (uq : R) = M q.1 q.2) : Rˣ where
  val := M q.1 p.2 * (↑(up⁻¹) : R)
  inv := M p.1 q.2 * (↑(uq⁻¹) : R)
  val_inv := transition_mul_reverse M hM p q up uq hp hq
  inv_val := transition_mul_reverse M hM q p uq up hq hp

@[simp] theorem transition_val
    (M : Matrix (Fin 3) (Fin 3) R) (hM : CycleQ2SegreLocal.cofactors M = 0)
    (p q : Chart) (up uq : Rˣ)
    (hp : (up : R) = M p.1 p.2) (hq : (uq : R) = M q.1 q.2) :
    (transition M hM p q up uq hp hq : R) = column M p up q.1 := rfl

theorem column_pivot
    (M : Matrix (Fin 3) (Fin 3) R) (p : Chart) (up : Rˣ)
    (hp : (up : R) = M p.1 p.2) : column M p up p.1 = 1 := by
  simp [column, ← hp]

/-- The explicit normalized columns glue by the displayed transition unit. -/
theorem column_overlap
    (M : Matrix (Fin 3) (Fin 3) R) (hM : CycleQ2SegreLocal.cofactors M = 0)
    (p q : Chart) (up uq : Rˣ)
    (hp : (up : R) = M p.1 p.2) (hq : (uq : R) = M q.1 q.2)
    (i : Fin 3) :
    column M p up i = (transition M hM p q up uq hp hq : R) * column M q uq i := by
  change M i p.2 * (↑(up⁻¹) : R) =
    (M q.1 p.2 * (↑(up⁻¹) : R)) * (M i q.2 * (↑(uq⁻¹) : R))
  rw [CycleQ2SegreLocal.unit_pivot_factorization M hM q.1 q.2 uq hq i p.2]
  ring

@[simp] theorem transition_self
    (M : Matrix (Fin 3) (Fin 3) R) (hM : CycleQ2SegreLocal.cofactors M = 0)
    (p : Chart) (up : Rˣ) (hp : (up : R) = M p.1 p.2) :
    transition M hM p p up up hp hp = 1 := by
  apply Units.ext
  exact column_pivot M p up hp

theorem transition_reverse
    (M : Matrix (Fin 3) (Fin 3) R) (hM : CycleQ2SegreLocal.cofactors M = 0)
    (p q : Chart) (up uq : Rˣ)
    (hp : (up : R) = M p.1 p.2) (hq : (uq : R) = M q.1 q.2) :
    transition M hM q p uq up hq hp = (transition M hM p q up uq hp hq)⁻¹ := by
  apply Units.ext
  rfl

/-- The multiplicative Čech cocycle on every triple overlap. -/
theorem transition_cocycle
    (M : Matrix (Fin 3) (Fin 3) R) (hM : CycleQ2SegreLocal.cofactors M = 0)
    (p q r : Chart) (up uq ur : Rˣ)
    (hp : (up : R) = M p.1 p.2) (hq : (uq : R) = M q.1 q.2)
    (hr : (ur : R) = M r.1 r.2) :
    transition M hM p q up uq hp hq * transition M hM q r uq ur hq hr =
      transition M hM p r up ur hp hr := by
  apply Units.ext
  exact (column_overlap M hM p q up uq hp hq r.1).symm

/-- The pivot row gives the local first-column equation. The same transition
unit relates its equations on different charts. -/
theorem row_overlap
    (M : Matrix (Fin 3) (Fin 3) R) (hM : CycleQ2SegreLocal.cofactors M = 0)
    (p q : Chart) (up uq : Rˣ)
    (hp : (up : R) = M p.1 p.2) (hq : (uq : R) = M q.1 q.2)
    (j : Fin 3) :
    M q.1 j = (transition M hM p q up uq hp hq : R) * M p.1 j :=
  CycleQ2SegreLocal.unit_pivot_factorization M hM p.1 p.2 up hp q.1 j

theorem first_column_ideal_overlap
    (M : Matrix (Fin 3) (Fin 3) R) (hM : CycleQ2SegreLocal.cofactors M = 0)
    (p q : Chart) (up uq : Rˣ)
    (hp : (up : R) = M p.1 p.2) (hq : (uq : R) = M q.1 q.2) :
    Ideal.span ({M q.1 0} : Set R) = Ideal.span ({M p.1 0} : Set R) := by
  rw [row_overlap M hM p q up uq hp hq 0]
  exact Ideal.span_singleton_mul_left_unit (transition M hM p q up uq hp hq).isUnit _

/-- Passing to an overlap ring preserves the actual cofactor equations. -/
theorem cofactors_map_zero
    {S : Type*} [CommRing S] (f : R →+* S)
    (M : Matrix (Fin 3) (Fin 3) R) (hM : CycleQ2SegreLocal.cofactors M = 0) :
    CycleQ2SegreLocal.cofactors (f.mapMatrix M) = 0 := by
  unfold CycleQ2SegreLocal.cofactors
  rw [← f.map_adjugate]
  change f.mapMatrix (CycleQ2SegreLocal.cofactors M) = 0
  rw [hM]
  ext i j
  exact f.map_zero

/-- Restriction of an overlap unit is the unit computed from the restricted
matrix. In particular the displayed cocycle is compatible with localization. -/
theorem transition_map
    {S : Type*} [CommRing S] (f : R →+* S)
    (M : Matrix (Fin 3) (Fin 3) R) (hM : CycleQ2SegreLocal.cofactors M = 0)
    (p q : Chart) (up uq : Rˣ)
    (hp : (up : R) = M p.1 p.2) (hq : (uq : R) = M q.1 q.2) :
    Units.map f.toMonoidHom (transition M hM p q up uq hp hq) =
      transition (f.mapMatrix M) (cofactors_map_zero f M hM) p q
        (Units.map f.toMonoidHom up) (Units.map f.toMonoidHom uq)
        (congrArg f hp) (congrArg f hq) := by
  apply Units.ext
  exact f.map_mul _ _

/-- A homogeneous matrix of degree `d` needs the ambient `O(d)` transition
as well as the normalized-image transition. Here `xp,xq` trivialize `O(1)`
on the chosen projective coordinate charts. -/
def twistedTransition
    (M : Matrix (Fin 3) (Fin 3) R) (hM : CycleQ2SegreLocal.cofactors M = 0)
    (p q : Chart) (up uq : Rˣ)
    (hp : (up : R) = M p.1 p.2) (hq : (uq : R) = M q.1 q.2)
    (xp xq : Rˣ) (d : ℕ) : Rˣ :=
  (xp * xq⁻¹)^d * transition M hM p q up uq hp hq

theorem twistedTransition_cocycle
    (M : Matrix (Fin 3) (Fin 3) R) (hM : CycleQ2SegreLocal.cofactors M = 0)
    (p q r : Chart) (up uq ur : Rˣ)
    (hp : (up : R) = M p.1 p.2) (hq : (uq : R) = M q.1 q.2)
    (hr : (ur : R) = M r.1 r.2) (xp xq xr : Rˣ) (d : ℕ) :
    twistedTransition M hM p q up uq hp hq xp xq d *
      twistedTransition M hM q r uq ur hq hr xq xr d =
        twistedTransition M hM p r up ur hp hr xp xr d := by
  have ha : (xp * xq⁻¹)^d * (xq * xr⁻¹)^d = (xp * xr⁻¹)^d := by
    rw [← mul_pow]
    congr 1
    group
  dsimp [twistedTransition]
  calc
    _ = ((xp * xq⁻¹)^d * (xq * xr⁻¹)^d) *
        (transition M hM p q up uq hp hq * transition M hM q r uq ur hq hr) := by
      ac_rfl
    _ = _ := by rw [ha, transition_cocycle]

/-- The degree-`d` local first-column equations transform by the twisted
unit, so their local principal ideals agree. -/
theorem homogeneous_first_column_overlap
    (M : Matrix (Fin 3) (Fin 3) R) (hM : CycleQ2SegreLocal.cofactors M = 0)
    (p q : Chart) (up uq : Rˣ)
    (hp : (up : R) = M p.1 p.2) (hq : (uq : R) = M q.1 q.2)
    (xp xq : Rˣ) (d : ℕ) :
    M q.1 0 * (↑(xq⁻¹) : R)^d =
      (twistedTransition M hM p q up uq hp hq xp xq d : R) *
        (M p.1 0 * (↑(xp⁻¹) : R)^d) := by
  have ha : ((xp * xq⁻¹)^d : Rˣ) * (xp⁻¹)^d = (xq⁻¹)^d := by
    rw [← mul_pow]
    congr 1
    calc
      _ = (xp * xp⁻¹) * xq⁻¹ := by ac_rfl
      _ = xq⁻¹ := by rw [mul_inv_cancel, one_mul]
  have hb : (↑(xp * xq⁻¹) : R)^d * (↑(xp⁻¹) : R)^d = (↑(xq⁻¹) : R)^d :=
    congrArg (fun u : Rˣ => (u : R)) ha
  rw [row_overlap M hM p q up uq hp hq 0]
  change ((transition M hM p q up uq hp hq : R) * M p.1 0) * (↑(xq⁻¹) : R)^d =
    ((↑(xp * xq⁻¹) : R)^d * (transition M hM p q up uq hp hq : R)) *
      (M p.1 0 * (↑(xp⁻¹) : R)^d)
  rw [← hb]
  ring

section Differential

variable (K : Type*) [CommRing K] [Algebra K R]

/-- Logarithmic differential in the actual universal Kähler module. -/
def unitDlog (u : Rˣ) : Ω[R⁄K] :=
  (↑(u⁻¹) : R) • KaehlerDifferential.D K R (u : R)

@[simp] theorem unitDlog_one : unitDlog K (1 : Rˣ) = 0 := by
  simp [unitDlog]

theorem unitDlog_mul (u v : Rˣ) :
    unitDlog K (u * v) = unitDlog K u + unitDlog K v := by
  simp only [unitDlog, _root_.mul_inv_rev, Units.val_mul, Derivation.leibniz,
    smul_add, smul_smul]
  have hu : ((↑(v⁻¹) : R) * ↑(u⁻¹)) * ↑u = ↑(v⁻¹) := by simp [mul_assoc]
  have hv : ((↑(v⁻¹) : R) * ↑(u⁻¹)) * ↑v = ↑(u⁻¹) := by
    calc
      _ = (↑(u⁻¹) : R) * (↑(v⁻¹) * ↑v) := by ring
      _ = ↑(u⁻¹) := by rw [Units.inv_mul, mul_one]
  rw [hu, hv, add_comm]

theorem unitDlog_inv (u : Rˣ) : unitDlog K u⁻¹ = -unitDlog K u := by
  have h := unitDlog_mul K u u⁻¹
  simp only [mul_inv_cancel, unitDlog_one] at h
  exact eq_neg_of_add_eq_zero_right h.symm

theorem unitDlog_pow (u : Rˣ) (n : ℕ) : unitDlog K (u^n) = n • unitDlog K u := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, unitDlog_mul, ih, succ_nsmul]

/-- Evaluation by any derivation gives the ordinary logarithmic derivative;
the construction is genuinely universal, rather than an assumed trace. -/
theorem unitDlog_apply
    {V : Type*} [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower K R V]
    (d : Derivation K R V) (u : Rˣ) :
    d.liftKaehlerDifferential (unitDlog K u) = (↑(u⁻¹) : R) • d (u : R) := by
  simp [unitDlog]

/-- The universal logarithmic differential commutes with restriction to an
algebra, including every further localization of a chart overlap. -/
theorem unitDlog_map
    {S : Type*} [CommRing S] [Algebra K S] [Algebra R S] [IsScalarTower K R S]
    (u : Rˣ) :
    KaehlerDifferential.map K K R S (unitDlog K u) =
      unitDlog K (Units.map (algebraMap R S).toMonoidHom u) := by
  simp only [unitDlog, map_smul, KaehlerDifferential.map_D,
    Units.coe_map_inv, Units.coe_map]
  exact (algebraMap_smul S (↑(u⁻¹) : R) _).symm

/-- The ambient twist is retained in the Kähler cocycle. The actual Segre
entries have `d=14`; identifying the seed divisor class is a separate binding. -/
theorem twistedTransition_dlog
    (M : Matrix (Fin 3) (Fin 3) R) (hM : CycleQ2SegreLocal.cofactors M = 0)
    (p q : Chart) (up uq : Rˣ)
    (hp : (up : R) = M p.1 p.2) (hq : (uq : R) = M q.1 q.2)
    (xp xq : Rˣ) (d : ℕ) :
    unitDlog K (twistedTransition M hM p q up uq hp hq xp xq d) =
      d • (unitDlog K xp - unitDlog K xq) +
        unitDlog K (transition M hM p q up uq hp hq) := by
  rw [twistedTransition, unitDlog_mul, unitDlog_pow, unitDlog_mul, unitDlog_inv,
    sub_eq_add_neg]

/-- The actual Kähler Čech one-cocycle of the normalized image generators. -/
theorem transition_dlog_cocycle
    (M : Matrix (Fin 3) (Fin 3) R) (hM : CycleQ2SegreLocal.cofactors M = 0)
    (p q r : Chart) (up uq ur : Rˣ)
    (hp : (up : R) = M p.1 p.2) (hq : (uq : R) = M q.1 q.2)
    (hr : (ur : R) = M r.1 r.2) :
    unitDlog K (transition M hM p q up uq hp hq) +
      unitDlog K (transition M hM q r uq ur hq hr) =
        unitDlog K (transition M hM p r up ur hp hr) := by
  rw [← unitDlog_mul, transition_cocycle]

theorem transition_dlog_reverse
    (M : Matrix (Fin 3) (Fin 3) R) (hM : CycleQ2SegreLocal.cofactors M = 0)
    (p q : Chart) (up uq : Rˣ)
    (hp : (up : R) = M p.1 p.2) (hq : (uq : R) = M q.1 q.2) :
    unitDlog K (transition M hM q p uq up hq hp) =
      -unitDlog K (transition M hM p q up uq hp hq) := by
  rw [transition_reverse, unitDlog_inv]

end Differential
end CycleQ2SegreCech

#print axioms CycleQ2SegreCech.transition_cocycle
#print axioms CycleQ2SegreCech.first_column_ideal_overlap
#print axioms CycleQ2SegreCech.transition_dlog_cocycle
#print axioms CycleQ2SegreCech.unitDlog_apply
end
end


/- Component: continuation_2/OpenSquareLifting.lean -/
section
/-!
A nonsingular square polynomial system has a finite separable generic point
inside any principal open containing the seed.  The open condition is imposed
by an actual additional equation u * c(x) - 1, whose Jacobian is block triangular.
This is an algebraic existence statement, not a formal-series lifting premise.
It creates no particular incidence seed or rank certificate.
-/

noncomputable section

set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2OpenSquareLifting

open MvPolynomial HoldoutConstruction

variable {R T : Type*} [CommRing R] [CommRing T] [Algebra R T]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The inverse coordinate is the left summand; the original coordinates are
in the right summand. -/
def extendedPoint (x : ι → T) (u : T) : Unit ⊕ ι → T :=
  Sum.elim (fun _ => u) x

/-- Actual polynomial equations for the chosen square system on the principal
open defined by c. -/
def openSystem (equations : ι → MvPolynomial ι R) (c : MvPolynomial ι R) :
    Unit ⊕ ι → MvPolynomial (Unit ⊕ ι) R :=
  Sum.elim (fun _ => X (Sum.inl ()) * rename Sum.inr c - 1)
    (fun i => rename Sum.inr (equations i))

@[simp] theorem aeval_extended_rename (x : ι → T) (u : T)
    (p : MvPolynomial ι R) :
    aeval (extendedPoint x u) (rename (Sum.inr : ι → Unit ⊕ ι) p) = aeval x p := by
  rw [aeval_rename]
  rfl

@[simp] theorem pderiv_inverse_rename (p : MvPolynomial ι R) :
    pderiv (Sum.inl ()) (rename (Sum.inr : ι → Unit ⊕ ι) p) = 0 := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [pderiv_mul, hp, pderiv_X, Pi.single_apply]

@[simp] theorem pderiv_original_rename (i : ι) (p : MvPolynomial ι R) :
    pderiv (Sum.inr i) (rename (Sum.inr : ι → Unit ⊕ ι) p) =
      rename Sum.inr (pderiv i p) :=
  pderiv_rename Sum.inr_injective i p

/-- An actual solution with an inverse for c evaluates every augmented
polynomial equation to zero. -/
theorem openSystem_seed (equations : ι → MvPolynomial ι R)
    (c : MvPolynomial ι R) (x : ι → T) (u : T)
    (hx : ∀ i, aeval x (equations i) = 0) (hu : u * aeval x c = 1) :
    ∀ i, aeval (extendedPoint x u) (openSystem equations c i) = 0 := by
  intro i
  cases i with
  | inl z => cases z; simpa [openSystem, aeval_rename, extendedPoint, Function.comp_def] using sub_eq_zero.mpr hu
  | inr i => simpa [openSystem] using hx i

/-- The full augmented Jacobian is a triangular block matrix.  This equality
holds at every point, independently of the polynomial equations. -/
theorem openSystem_jacobian_det (equations : ι → MvPolynomial ι R)
    (c : MvPolynomial ι R) (x : ι → T) (u : T) :
    Matrix.det (fun i j => aeval (extendedPoint x u)
      (pderiv i (openSystem equations c j))) =
    aeval x c * Matrix.det (fun i j => aeval x (pderiv i (equations j))) := by
  have hmatrix :
      (fun i j => aeval (extendedPoint x u) (pderiv i (openSystem equations c j))) =
      Matrix.fromBlocks (fun (_ _ : Unit) => aeval x c)
        (0 : Matrix Unit ι T)
        (fun i (_ : Unit) => u * aeval x (pderiv i c))
        (fun i j => aeval x (pderiv i (equations j))) := by
    ext i j
    cases i with
    | inl z =>
      cases z
      cases j with
      | inl w => cases w; simp [openSystem, aeval_rename, extendedPoint, Function.comp_def, Matrix.fromBlocks]
      | inr j => simp [openSystem, Matrix.fromBlocks]
    | inr i =>
      cases j with
      | inl w =>
        cases w
        simp [openSystem, aeval_rename, extendedPoint, Function.comp_def, Matrix.fromBlocks, pderiv_X]
      | inr j => simp [openSystem, Matrix.fromBlocks]
  rw [hmatrix, Matrix.det_fromBlocks_zero₁₂, Matrix.det_unique]

/-- Every solution of the augmented system solves the original system, and
its value of c is a unit. -/
theorem solution_on_open (equations : ι → MvPolynomial ι R)
    (c : MvPolynomial ι R) (z : Unit ⊕ ι → T)
    (hz : ∀ i, aeval z (openSystem equations c i) = 0) :
    (∀ i, aeval (fun i => z (Sum.inr i)) (equations i) = 0) ∧
      IsUnit (aeval (fun i => z (Sum.inr i)) c) := by
  have hrename (p : MvPolynomial ι R) :
      aeval z (rename (Sum.inr : ι → Unit ⊕ ι) p) =
        aeval (fun i => z (Sum.inr i)) p := by rw [aeval_rename]; rfl
  constructor
  · intro i
    simpa only [openSystem, Sum.elim_inr, hrename] using hz (Sum.inr i)
  · have hi := hz (Sum.inl ())
    simp only [openSystem, Sum.elim_inl, map_sub, map_mul, aeval_X, map_one,
      hrename, sub_eq_zero] at hi
    refine ⟨⟨aeval (fun i => z (Sum.inr i)) c, z (Sum.inl ()), ?_, hi⟩, rfl⟩
    exact (mul_comm (aeval (fun i => z (Sum.inr i)) c) (z (Sum.inl ()))).trans hi

section GenericPoint

set_option backward.isDefEq.respectTransparency false

variable {K : Type*} [Field K] [Algebra R K] [Nontrivial T]

/-- A genuine finite separable generic solution inside the specified open
locus, obtained from a nonsingular special-fiber seed.  Coefficients must
embed in K; the special-fiber coefficient map need not be injective. -/
theorem square_system_generic_lift_on_open
    (equations : ι → MvPolynomial ι R) (c : MvPolynomial ι R)
    (seed : ι → T)
    (hseed : ∀ i, aeval seed (equations i) = 0)
    (hjac : IsUnit (Matrix.det
      (fun i j => aeval seed (pderiv i (equations j)))))
    (hc : IsUnit (aeval seed c))
    (hinj : Function.Injective (algebraMap R K)) :
    ∃ I : Ideal (SquareGenericAlgebra K (openSystem equations c)), I.IsMaximal ∧
      Module.Finite K ((SquareGenericAlgebra K (openSystem equations c)) ⧸ I) ∧
      Algebra.IsSeparable K ((SquareGenericAlgebra K (openSystem equations c)) ⧸ I) ∧
      ∃ x : ι → ((SquareGenericAlgebra K (openSystem equations c)) ⧸ I),
        (∀ i, aeval x (equations i) = 0) ∧ IsUnit (aeval x c) := by
  obtain ⟨u, hu⟩ := hc.exists_left_inv
  have haug := openSystem_seed equations c seed u hseed hu
  have hjaug : IsUnit (Matrix.det (fun i j => aeval (extendedPoint seed u)
      (pderiv i (openSystem equations c j)))) := by
    rw [openSystem_jacobian_det]
    exact hc.mul hjac
  obtain ⟨I, hI, hfinite, hsep, hsol, hj⟩ :=
    ReflectionCoupledFano.square_system_generic_lift (K := K)
      (openSystem equations c) (extendedPoint seed u) haug hjaug hinj
  clear hj
  generalize hcoords : squareGenericCoordinates (K := K) (openSystem equations c) I = z at hsol
  refine ⟨I, hI, hfinite, hsep, (fun i => z (Sum.inr i)), ?_, ?_⟩
  · intro i
    have hi := hsol (Sum.inr i)
    change aeval z (rename (Sum.inr : ι → Unit ⊕ ι) (equations i)) = 0 at hi
    rw [aeval_rename] at hi
    exact hi
  · have hi := hsol (Sum.inl ())
    change aeval z (X (Sum.inl ()) * rename (Sum.inr : ι → Unit ⊕ ι) c - 1) = 0 at hi
    simp only [map_sub, map_mul, aeval_X, map_one, aeval_rename, sub_eq_zero] at hi
    refine ⟨⟨aeval (fun i => z (Sum.inr i)) c, z (Sum.inl ()), ?_, hi⟩, rfl⟩
    exact (mul_comm (aeval (fun i => z (Sum.inr i)) c) (z (Sum.inl ()))).trans hi

end GenericPoint

end CycleQ2OpenSquareLifting

#print axioms CycleQ2OpenSquareLifting.openSystem_jacobian_det
#print axioms CycleQ2OpenSquareLifting.square_system_generic_lift_on_open
end
end


/- Component: continuation_2/SquareAdicLifting.lean -/
section
/-!
Actual adic lifting of square polynomial systems with invertible seed Jacobian.
The proof uses the established étale Jacobian localization and mathlib's
compatible infinitesimal lifts into an adically complete ring.  The seed is
preserved.  No existence of a formal solution is assumed.
-/

noncomputable section

set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2SquareAdicLifting

open MvPolynomial HoldoutConstruction

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The actual polynomial presentation map into its Jacobian localization. -/
def polynomialToEtale (equations : ι → MvPolynomial ι R) :
    MvPolynomial ι R →ₐ[R] SquareEtaleRing equations :=
  (IsScalarTower.toAlgHom R (SquareSystemRing equations) (SquareEtaleRing equations)).comp
    (Ideal.Quotient.mkₐ R (Ideal.span (Set.range equations)))

@[simp] theorem polynomialToEtale_equation (equations : ι → MvPolynomial ι R) (i : ι) :
    polynomialToEtale equations (equations i) = 0 := by
  have hz : Ideal.Quotient.mk (Ideal.span (Set.range equations)) (equations i) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_range_self i))
  change algebraMap (SquareSystemRing equations) (SquareEtaleRing equations)
    (Ideal.Quotient.mk _ (equations i)) = 0
  rw [hz, map_zero]

/-- The square system lifts from the residue ring into any complete adic
algebra, while retaining its specified residue coordinates. -/
theorem square_system_adic_lift (equations : ι → MvPolynomial ι R)
    (I : Ideal S) [IsAdicComplete I S] (seed : ι → S ⧸ I)
    (hseed : ∀ i, aeval seed (equations i) = 0)
    (hjac : IsUnit (Matrix.det
      (fun i j => aeval seed (pderiv i (equations j))))) :
    ∃ x : ι → S,
      (∀ i, Ideal.Quotient.mk I (x i) = seed i) ∧
      (∀ i, aeval x (equations i) = 0) := by
  letI : Algebra.Etale R (SquareEtaleRing equations) :=
    square_system_jacobian_etale equations
  let f : SquareEtaleRing equations →ₐ[R] S ⧸ I :=
    squareSystemEtaleEval equations seed hseed hjac
  obtain ⟨g, hg⟩ := Algebra.FormallySmooth.exists_mkₐ_comp_eq_of_isAdicComplete f
  let x : ι → S := fun i => g (polynomialToEtale equations (X i))
  have heval : aeval x = g.comp (polynomialToEtale equations) := by
    ext i
    simp [x]
  have hres : f.comp (polynomialToEtale equations) = aeval seed := by
    ext i
    simp [f, polynomialToEtale, squareSystemEtaleEval, squareSystemEval,
      IsLocalization.Away.liftAlgHom, Ideal.Quotient.lift_mk]
  refine ⟨x, ?_, ?_⟩
  · intro i
    have h := AlgHom.congr_fun hg (polynomialToEtale equations (X i))
    change Ideal.Quotient.mk I (x i) = f (polynomialToEtale equations (X i)) at h
    rw [h]
    have hs := AlgHom.congr_fun hres (X i)
    simpa only [AlgHom.comp_apply, aeval_X] using hs
  · intro i
    rw [heval, AlgHom.comp_apply, polynomialToEtale_equation, map_zero]

section PowerSeries

variable {K : Type*} [CommRing K]

/-- Square equations with arbitrary formal coefficients have an actual
formal solution through each nonsingular constant seed.  The hypotheses
are polynomial evaluation and the actual partial-derivative Jacobian. -/
theorem square_system_powerSeries_lift
    (equations : ι → MvPolynomial ι (PowerSeries K)) (seed : ι → K)
    (hseed : ∀ i, eval₂ PowerSeries.constantCoeff seed (equations i) = 0)
    (hjac : IsUnit (Matrix.det (fun i j =>
      eval₂ PowerSeries.constantCoeff seed (pderiv i (equations j))))) :
    ∃ x : ι → PowerSeries K,
      (∀ i, PowerSeries.constantCoeff (x i) = seed i) ∧
      (∀ i, aeval x (equations i) = 0) := by
  letI : Algebra (PowerSeries K) K := PowerSeries.constantCoeff.toAlgebra
  let cc : PowerSeries K →ₐ[PowerSeries K] K :=
    { PowerSeries.constantCoeff with commutes' := by intro r; rfl }
  let I : Ideal (PowerSeries K) := RingHom.ker cc
  have hI : I = Ideal.span {PowerSeries.X} := by
    ext z
    simp only [I, RingHom.mem_ker, Ideal.mem_span_singleton, PowerSeries.X_dvd_iff]
    rfl
  letI : IsAdicComplete I (PowerSeries K) := by
    rw [hI]
    infer_instance
  let e : ((PowerSeries K) ⧸ I) ≃ₐ[PowerSeries K] K :=
    Ideal.quotientKerAlgEquivOfSurjective (f := cc) PowerSeries.constantCoeff_surj
  let seed' : ι → (PowerSeries K) ⧸ I := fun i => e.symm (seed i)
  have heval (p : MvPolynomial ι (PowerSeries K)) :
      aeval seed' p = e.symm (eval₂ PowerSeries.constantCoeff seed p) := by
    exact (MvPolynomial.comp_aeval_apply seed e.symm.toAlgHom p).symm
  have hs : ∀ i, aeval seed' (equations i) = 0 := by
    intro i
    rw [heval, hseed i, map_zero]
  have hj : IsUnit (Matrix.det (fun i j => aeval seed' (pderiv i (equations j)))) := by
    simp only [heval]
    have hd :
        Matrix.det (fun i j => e.symm
          (eval₂ PowerSeries.constantCoeff seed (pderiv i (equations j)))) =
        e.symm (Matrix.det (fun i j =>
          eval₂ PowerSeries.constantCoeff seed (pderiv i (equations j)))) :=
      (e.symm.toAlgHom.map_det (fun i j =>
        eval₂ PowerSeries.constantCoeff seed (pderiv i (equations j)))).symm
    rw [hd]
    exact hjac.map e.symm.toRingEquiv.toRingHom
  obtain ⟨x, hx, heq⟩ := square_system_adic_lift equations I seed' hs hj
  refine ⟨x, ?_, heq⟩
  intro i
  have hi := congrArg e (hx i)
  change cc (x i) = e (e.symm (seed i)) at hi
  have hcc (z : PowerSeries K) : cc z = PowerSeries.constantCoeff z := rfl
  simpa only [AlgEquiv.apply_symm_apply, hcc] using hi

end PowerSeries

end CycleQ2SquareAdicLifting

#print axioms CycleQ2SquareAdicLifting.square_system_adic_lift
#print axioms CycleQ2SquareAdicLifting.square_system_powerSeries_lift
end
end


/- Component: continuation_2/SegreFormalLifting.lean -/
section
/-!
# Formal lifting with genuine redundant polynomial equations

A nonsingular square subsystem lifts through its seed. If the residual
polynomials satisfy actual polynomial relations whose complementary block
is invertible at the seed, every omitted equation vanishes along that lift.
All coefficient series may vary: the theorem is not a tangent-only statement.
No seed or minor of the particular large incidence system is assumed proved.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section

namespace CycleQ2SegreFormalLifting

open MvPolynomial Matrix

variable {K ι κ : Type*} [CommRing K]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- The complete nonlinear system has a seed-preserving formal solution.
The premises concern polynomial identities and the two actual seed minors;
none assumes a formal solution of either the full or square system. -/
theorem lift_all_equations
    (equations : ι → MvPolynomial ι (PowerSeries K))
    (residual : κ → MvPolynomial ι (PowerSeries K))
    (A : Matrix κ κ (MvPolynomial ι (PowerSeries K)))
    (B : Matrix κ ι (MvPolynomial ι (PowerSeries K)))
    (hrelations : A *ᵥ residual + B *ᵥ equations = 0)
    (seed : ι → K)
    (hseed : ∀ i, eval₂ PowerSeries.constantCoeff seed (equations i) = 0)
    (hjac : IsUnit (Matrix.det (fun i j =>
      eval₂ PowerSeries.constantCoeff seed (pderiv i (equations j)))))
    (hcomplement : IsUnit (eval₂ PowerSeries.constantCoeff seed A.det)) :
    ∃ x : ι → PowerSeries K,
      (∀ i, PowerSeries.constantCoeff (x i) = seed i) ∧
      (∀ i, aeval x (equations i) = 0) ∧
      (∀ j, aeval x (residual j) = 0) := by
  obtain ⟨x, hx, heq⟩ :=
    CycleQ2SquareAdicLifting.square_system_powerSeries_lift equations seed hseed hjac
  have hcc (p : MvPolynomial ι (PowerSeries K)) :
      PowerSeries.constantCoeff (aeval x p) = eval₂ PowerSeries.constantCoeff seed p := by
    induction p using MvPolynomial.induction_on with
    | C c => simp
    | add p q hp hq => simp only [map_add, eval₂_add, hp, hq]
    | mul_X p i hp => simp only [map_mul, aeval_X, eval₂_mul, eval₂_X, hp, hx]
  have hunit : IsUnit (aeval x A.det) := by
    apply PowerSeries.isUnit_iff_constantCoeff.mpr
    rw [hcc]
    exact hcomplement
  let φ : MvPolynomial ι (PowerSeries K) →+* PowerSeries K :=
    (aeval x).toRingHom
  have heq' : φ ∘ equations = 0 := by
    funext i
    exact heq i
  have hr : φ ∘ residual = 0 :=
    CycleQ2SegreRelations.evaluated_residual_eq_zero
      φ A B residual equations hrelations heq' hunit
  refine ⟨x, hx, heq, ?_⟩
  intro j
  exact congrFun hr j

end CycleQ2SegreFormalLifting

#print axioms CycleQ2SegreFormalLifting.lift_all_equations
end
end


