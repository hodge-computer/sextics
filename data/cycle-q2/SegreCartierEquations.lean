import Proposal.GeometricSurfaceCoordinates
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Ideal.Span
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.Tactic

/-! # Cartier and Segre matrix factorizations on the incidence charts -/

set_option Elab.async false

/- Component: continuation_2/CartierMatrixFactorization.lean -/
section
/-!
# Actual polynomial resolution data for the invariant Cartier curve

All entries below are literal polynomials over an arbitrary commutative ring.
The six by six matrices factor the actual cubic a^3-b^3+c^3+d^3.
The augmentation is the previously constructed elliptic-sextic residual ideal.
The two original second syzygies alone do not give the full hypersurface
resolution: the four columns of H0 are necessary.

No geometric deformation theorem or characteristic-zero rank lifting is
asserted in this file.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace CycleQ2CartierResolution

variable {R : Type*} [CommRing R] (a b c d : R)

def cubic : R := a ^ 3 - b ^ 3 + c ^ 3 + d ^ 3

def first : Matrix (Fin 4) (Fin 6) R :=
  !![a^2, b^2, -c^2, d^2, a*d, -b*c;
     c, -d, a, -b, 0, 0;
     b, a, 0, 0, c, -d;
     0, 0, d, c, b, a]

def second : Matrix (Fin 6) (Fin 2) R :=
  !![d, 0; c, 0; 0, b; 0, a; -a, -d; b, -c]

def homotopy0 : Matrix (Fin 6) (Fin 4) R :=
  !![a, c^2, -b^2, b*c;
     -b, -d^2, a^2, a*d;
     -c, a^2, a*d, d^2;
     d, b^2, -b*c, c^2;
     0, -b*c, c^2, -b^2;
     0, -a*d, -d^2, a^2]

def homotopy1 : Matrix (Fin 2) (Fin 6) R :=
  !![d^2, c^2, -b*c, -a*d, -a^2, -b^2;
     -a*d, b*c, -b^2, a^2, -d^2, -c^2]

def even : Matrix (Fin 6) (Fin 6) R :=
  !![d, 0, a, c^2, -b^2, b*c;
     c, 0, -b, -d^2, a^2, a*d;
     0, b, -c, a^2, a*d, d^2;
     0, a, d, b^2, -b*c, c^2;
     -a, -d, 0, -b*c, c^2, -b^2;
     b, -c, 0, -a*d, -d^2, a^2]

def odd : Matrix (Fin 6) (Fin 6) R :=
  !![d^2, c^2, -b*c, -a*d, -a^2, -b^2;
     -a*d, b*c, -b^2, a^2, -d^2, -c^2;
     a^2, b^2, -c^2, d^2, a*d, -b*c;
     c, -d, a, -b, 0, 0;
     b, a, 0, 0, c, -d;
     0, 0, d, c, b, a]

def generators : Matrix (Fin 1) (Fin 4) R :=
  !![a^2*b - c*d^2 + 2*c*(a*c+b*d),
     -2*a^3*c+a^2*d^2+a*b*c^2+2*b^3*c-b^2*c*d,
     -2*a^2*c*d-a*b^3+a*d^3-2*b^2*c^2+b*c^2*d,
     a*b^2*c-2*a*c*d^2-b^3*d+2*b*c^3+d^4]

def cubicColumn : Matrix (Fin 1) (Fin 6) R :=
  !![-a*b, 0, 2*a*c-d^2, -2*b*c, -b*d, 0]

theorem first_second : first a b c d * second a b c d = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [first, second, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

theorem first_homotopy0 : first a b c d * homotopy0 a b c d =
    cubic a b c d • (1 : Matrix (Fin 4) (Fin 4) R) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [first, homotopy0, cubic, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

theorem homotopy_identity :
    second a b c d * homotopy1 a b c d + homotopy0 a b c d * first a b c d =
      cubic a b c d • (1 : Matrix (Fin 6) (Fin 6) R) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [first, second, homotopy0, homotopy1, cubic,
      Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

theorem homotopy1_second : homotopy1 a b c d * second a b c d =
    cubic a b c d • (1 : Matrix (Fin 2) (Fin 2) R) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [homotopy1, second, cubic, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

theorem homotopy1_homotopy0 : homotopy1 a b c d * homotopy0 a b c d = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [homotopy1, homotopy0, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

theorem even_odd : even a b c d * odd a b c d =
    cubic a b c d • (1 : Matrix (Fin 6) (Fin 6) R) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [even, odd, cubic, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

theorem odd_even : odd a b c d * even a b c d =
    cubic a b c d • (1 : Matrix (Fin 6) (Fin 6) R) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [even, odd, cubic, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

theorem augmentation_first :
    generators a b c d * first a b c d + cubic a b c d • cubicColumn a b c d = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [generators, first, cubicColumn, cubic,
      Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

theorem cubicColumn_second : cubicColumn a b c d * second a b c d = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [cubicColumn, second, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

theorem cubicColumn_homotopy0 :
    cubicColumn a b c d * homotopy0 a b c d + generators a b c d = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [cubicColumn, homotopy0, generators,
      Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

end CycleQ2CartierResolution

#print axioms CycleQ2CartierResolution.even_odd
#print axioms CycleQ2CartierResolution.odd_even
#print axioms CycleQ2CartierResolution.homotopy_identity
#print axioms CycleQ2CartierResolution.augmentation_first
#print axioms CycleQ2CartierResolution.cubicColumn_homotopy0
end


/- Component: continuation_2/CartierMatrixFactorizationExactness.lean -/
section
/-!
# Genuine exactness of the actual periodic complex modulo the cubic

A matrix factorization over a domain gives an exact two-periodic complex
after quotienting by its nonzero scalar. The proof lifts a kernel vector,
uses divisibility by the scalar, and cancels that scalar in the domain.
The resulting theorem is applied to the actual six by six cubic matrices.

This proves quotient-module exactness. It does not assert saturation,
base change through the cubic section, or nonlinear geometric lifting.
-/

set_option autoImplicit false

noncomputable section
namespace CycleQ2CartierResolution

open Matrix

variable {R : Type*} [CommRing R] [IsDomain R]

theorem matrixFactorization_exact_mod
    {n : Type*} [Fintype n] [DecidableEq n]
    (g : R) (hg : g ≠ 0) (A B : Matrix n n R)
    (hAB : A * B = g • (1 : Matrix n n R))
    (hBA : B * A = g • (1 : Matrix n n R))
    (x : n → R ⧸ Ideal.span ({g} : Set R)) :
    A.map (Ideal.Quotient.mk (Ideal.span ({g} : Set R))) *ᵥ x = 0 ↔
      ∃ y, B.map (Ideal.Quotient.mk (Ideal.span ({g} : Set R))) *ᵥ y = x := by
  let I : Ideal R := Ideal.span ({g} : Set R)
  let q : R →+* R ⧸ I := Ideal.Quotient.mk I
  change A.map q *ᵥ x = 0 ↔ ∃ y, B.map q *ᵥ y = x
  have hqg : q g = 0 := by
    apply (Ideal.Quotient.eq_zero_iff_mem).mpr
    exact Ideal.subset_span (Set.mem_singleton g)
  have hqAB : A.map q * B.map q = 0 := by
    rw [← Matrix.map_mul, hAB]
    ext i j
    simp [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, hqg]
  constructor
  · intro hx
    choose z hz using fun i => Ideal.Quotient.mk_surjective (x i)
    have hqz : q ∘ z = x := funext hz
    have hdiv : ∀ i, g ∣ (A *ᵥ z) i := by
      intro i
      apply Ideal.mem_span_singleton.mp
      apply (Ideal.Quotient.eq_zero_iff_mem).mp
      change q ((A *ᵥ z) i) = 0
      rw [RingHom.map_mulVec, hqz, hx]
      rfl
    choose y hy using hdiv
    have hAz : A *ᵥ z = g • y := by
      funext i
      exact hy i
    have hcancel : g • z = g • (B *ᵥ y) := by
      calc
        g • z = (B * A) *ᵥ z := by
          rw [hBA, smul_mulVec, one_mulVec]
        _ = B *ᵥ (A *ᵥ z) := (mulVec_mulVec z B A).symm
        _ = B *ᵥ (g • y) := by rw [hAz]
        _ = g • (B *ᵥ y) := mulVec_smul B g y
    have hzy : z = B *ᵥ y := by
      funext i
      apply mul_left_cancel₀ hg
      exact congrArg (fun v : n → R => v i) hcancel
    refine ⟨q ∘ y, ?_⟩
    funext i
    rw [← RingHom.map_mulVec, ← hzy]
    exact hz i
  · rintro ⟨y, rfl⟩
    rw [mulVec_mulVec, hqAB, zero_mulVec]

abbrev cubicQuotient (a b c d : R) := R ⧸ Ideal.span ({cubic a b c d} : Set R)

def cubicQuotientMap (a b c d : R) : R →+* cubicQuotient a b c d :=
  Ideal.Quotient.mk (Ideal.span ({cubic a b c d} : Set R))

theorem even_exact_mod_cubic (a b c d : R) (hg : cubic a b c d ≠ 0)
    (x : Fin 6 → cubicQuotient a b c d) :
    (even a b c d).map (cubicQuotientMap a b c d) *ᵥ x = 0 ↔
      ∃ y, (odd a b c d).map (cubicQuotientMap a b c d) *ᵥ y = x :=
  matrixFactorization_exact_mod (cubic a b c d) hg (even a b c d) (odd a b c d)
    (even_odd a b c d) (odd_even a b c d) x

theorem odd_exact_mod_cubic (a b c d : R) (hg : cubic a b c d ≠ 0)
    (x : Fin 6 → cubicQuotient a b c d) :
    (odd a b c d).map (cubicQuotientMap a b c d) *ᵥ x = 0 ↔
      ∃ y, (even a b c d).map (cubicQuotientMap a b c d) *ᵥ y = x :=
  matrixFactorization_exact_mod (cubic a b c d) hg (odd a b c d) (even a b c d)
    (odd_even a b c d) (even_odd a b c d) x

end CycleQ2CartierResolution

#print axioms CycleQ2CartierResolution.matrixFactorization_exact_mod
#print axioms CycleQ2CartierResolution.even_exact_mod_cubic
#print axioms CycleQ2CartierResolution.odd_exact_mod_cubic
end
end


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


/- Component: continuation_2/SegreSeedPolynomials.lean -/
section
/-!
# Literal polynomial identities for the chosen Segre seed

All coefficients and sections come from the explicit seed and its 25 linkage
pairings.  Every theorem is a universal identity over a commutative ring,
proved by ordinary ring normalization or by smaller proved identities.
In particular, no relation r^3=2 is needed here: r is an arbitrary coefficient.
The nine cofactors are divisible by the actual G before imposing h.
This module asserts no rank bound, projective basepoint freeness, deformation
existence, residue primitive, or protected certificate.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false

noncomputable section
namespace CycleQ2SegreSeed

open Matrix

variable {R : Type*} [CommRing R]

def linkageP (a b c d : R) : R := a * c + b * d

def linkageE (a b c d : R) : Fin 5 → R :=
  ![a * c + b * d,
  a ^ 3 - b ^ 3,
  a ^ 2 * d + b ^ 2 * c,
  a * d ^ 2 - b * c ^ 2,
  c ^ 3 + d ^ 3]

def linkageEprime (a b c d : R) : Fin 5 → R :=
  ![a * c + b * d,
  a ^ 3 + d ^ 3,
  a ^ 2 * b - c * d ^ 2,
  a * b ^ 2 + c ^ 2 * d,
  -b ^ 3 + c ^ 3]

def linkageQ (a b c d : R) : Matrix (Fin 5) (Fin 5) R :=
  ![![a * c + b * d,
  a ^ 3 + d ^ 3,
  a ^ 2 * b - c * d ^ 2,
  a * b ^ 2 + c ^ 2 * d,
  -b ^ 3 + c ^ 3],
  ![a ^ 3 - b ^ 3,
  -a ^ 2 * c ^ 2 + a * b * c * d - b ^ 2 * d ^ 2,
  -a ^ 2 * d ^ 2 - a * b * c ^ 2 + b ^ 2 * c * d,
  a ^ 2 * c * d - a * b * d ^ 2 - b ^ 2 * c ^ 2,
  a ^ 2 * c ^ 2 - a * b * c * d + b ^ 2 * d ^ 2],
  ![a ^ 2 * d + b ^ 2 * c,
  a ^ 2 * b ^ 2 - a * c ^ 2 * d + b * c * d ^ 2,
  a * b ^ 3 - a * d ^ 3 - b * c ^ 2 * d,
  a * c * d ^ 2 + b ^ 4 - b * d ^ 3,
  -a ^ 2 * b ^ 2 + a * c ^ 2 * d - b * c * d ^ 2],
  ![a * d ^ 2 - b * c ^ 2,
  -a ^ 2 * b * c + a * b ^ 2 * d - c ^ 2 * d ^ 2,
  -a * b ^ 2 * c + b ^ 3 * d - d ^ 4,
  a ^ 2 * b * d - b ^ 3 * c + c * d ^ 3,
  a ^ 2 * b * c - a * b ^ 2 * d + c ^ 2 * d ^ 2],
  ![c ^ 3 + d ^ 3,
  a ^ 2 * c ^ 2 - a * b * c * d + b ^ 2 * d ^ 2,
  a ^ 2 * d ^ 2 + a * b * c ^ 2 - b ^ 2 * c * d,
  -a ^ 2 * c * d + a * b * d ^ 2 + b ^ 2 * c ^ 2,
  -a ^ 2 * c ^ 2 + a * b * c * d - b ^ 2 * d ^ 2]]

def linkageT (a b c d : R) : Matrix (Fin 5) (Fin 5) R :=
  ![![0,
  0,
  0,
  0,
  0],
  ![0,
  a ^ 3,
  a ^ 2 * b,
  a * b ^ 2,
  -b ^ 3],
  ![0,
  a ^ 2 * d,
  a * b * d,
  b ^ 2 * d,
  b ^ 2 * c],
  ![0,
  a * d ^ 2,
  b * d ^ 2,
  -b * c * d,
  -b * c ^ 2],
  ![0,
  d ^ 3,
  -c * d ^ 2,
  c ^ 2 * d,
  c ^ 3]]

/-- All 25 exact linkage pairings, with their literal polynomial quotients. -/
theorem linkage_pairing (a b c d : R) (i j : Fin 5) :
    linkageE a b c d i * linkageEprime a b c d j =
      linkageP a b c d * linkageQ a b c d i j +
      linkageG a b c d * linkageT a b c d i j := by
  fin_cases i <;> fin_cases j <;>
    simp only [linkageE, linkageEprime, linkageP, linkageG, linkageQ, linkageT,
      Matrix.of_apply, Matrix.cons_val_zero', Matrix.cons_val_succ',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons] <;> ring

/-- The ordinary signed cross product, used only as a polynomial expression. -/
def cross (u v : Fin 3 → R) : Fin 3 → R :=
  ![u 1 * v 2 - u 2 * v 1, u 2 * v 0 - u 0 * v 2, u 0 * v 1 - u 1 * v 0]

/-- A small Cauchy--Binet identity, proved directly over a commutative ring. -/
theorem cofactors_rank_two (u v s t : Fin 3 → R) :
    (Matrix.adjugate (fun i j => u i * s j + v i * t j)).transpose =
      fun i j => cross u v i * cross s t j := by
  rw [Matrix.adjugate_fin_three]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.transpose_apply, cross, Matrix.of_apply,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;> ring

def coreRight0 (a b c d u0 u1 u2 : R) : R :=
  (a*c+b*d)*u0 + (a^2*b-c*d^2)*u1 + (a*b^2+c^2*d)*u2

def coreRight1 (a b c d u0 u1 u2 : R) : R :=
  (a^3-b^3)*u0 + (-a^2*d^2-a*b*c^2+b^2*c*d)*u1 +
    (a^2*c*d-a*b*d^2-b^2*c^2)*u2

def coreMinorQuotient (a b c d u0 u1 u2 v0 v1 v2 : R) : R :=
  -(a^2*b)*(u0*v1-v0*u1) - (a*b^2)*(u0*v2-v0*u2) +
    (a*b*c*d)*(u1*v2-v1*u2)

/-- The three central two-by-two minors have their actual common factor G. -/
theorem coreRight_minor (a b c d u0 u1 u2 v0 v1 v2 : R) :
    coreRight0 a b c d u0 u1 u2 * coreRight1 a b c d v0 v1 v2 -
      coreRight0 a b c d v0 v1 v2 * coreRight1 a b c d u0 u1 u2 =
      linkageG a b c d * coreMinorQuotient a b c d u0 u1 u2 v0 v1 v2 := by
  unfold coreRight0 coreRight1 linkageG coreMinorQuotient
  ring

def coreProductCorrection (a b u1 v1 v2 : R) : R :=
  u1 * (v1 * (a^2*b) + v2 * (a*b^2))

theorem core_product (a b c d u0 u1 v0 v1 v2 : R) :
    (u0*linkageP a b c d + u1*(a^3-b^3)) * coreRight0 a b c d v0 v1 v2 =
      linkageP a b c d * (u0*coreRight0 a b c d v0 v1 v2 +
        u1*coreRight1 a b c d v0 v1 v2) +
      linkageG a b c d * coreProductCorrection a b u1 v1 v2 := by
  unfold coreRight0 coreRight1 linkageG linkageP coreProductCorrection
  ring

def seedP (r x0 x1 x2 x3 w : R) : R := linkageP (x0^2) (r*x1*x3) w (x2^2)
def leftCoeff0 (x0 x1 x2 x3 w : R) : Fin 3 → R :=
  ![-w ^ 2 * x1 * x3 + x1 ^ 2 * x2 ^ 4,
  -w * x1 ^ 4 + x0 ^ 2 * x2 ^ 4 + x1 * x2 ^ 3 * x3 ^ 2,
  -w ^ 2 * x0 * x3 + x1 ^ 4 * x3 ^ 2 + x2 ^ 2 * x3 ^ 4]

def leftCoeff1 (x0 x1 x2 x3 w : R) : Fin 3 → R :=
  ![x0 * x1 * x2 ^ 2 - x0 * x2 * x3 ^ 2,
  x3 ^ 4,
  x3 ^ 4]

def rightCoeff0 (x0 x1 x2 x3 w : R) : Fin 3 → R :=
  ![2 * w ^ 2 + 2 * w * x3 ^ 2,
  w * x0 * x2 + x0 ^ 2 * x2 ^ 2,
  x0 * x1 ^ 2 * x3 + x1 * x2 * x3 ^ 2 - x2 ^ 3 * x3 + x3 ^ 4]

def rightCoeff2 (x0 x1 x2 x3 w : R) : Fin 3 → R :=
  ![w + x3 ^ 2,
  w,
  0]

def rightCoeff3 (x0 x1 x2 x3 w : R) : Fin 3 → R :=
  ![0,
  x0 * x3,
  0]

def baseRow0 (r x0 x1 x2 x3 w : R) (j : Fin 3) : R :=
  coreRight0 (x0^2) (r*x1*x3) w (x2^2)
    (rightCoeff0 x0 x1 x2 x3 w j) (rightCoeff2 x0 x1 x2 x3 w j)
    (rightCoeff3 x0 x1 x2 x3 w j)

def baseRow1 (r x0 x1 x2 x3 w : R) (j : Fin 3) : R :=
  coreRight1 (x0^2) (r*x1*x3) w (x2^2)
    (rightCoeff0 x0 x1 x2 x3 w j) (rightCoeff2 x0 x1 x2 x3 w j)
    (rightCoeff3 x0 x1 x2 x3 w j)

def rightMinorQuotient (r x0 x1 x2 x3 w : R) (j k : Fin 3) : R :=
  coreMinorQuotient (x0^2) (r*x1*x3) w (x2^2)
    (rightCoeff0 x0 x1 x2 x3 w j) (rightCoeff2 x0 x1 x2 x3 w j)
    (rightCoeff3 x0 x1 x2 x3 w j)
    (rightCoeff0 x0 x1 x2 x3 w k) (rightCoeff2 x0 x1 x2 x3 w k)
    (rightCoeff3 x0 x1 x2 x3 w k)

def rightCrossQuotient (r x0 x1 x2 x3 w : R) : Fin 3 → R :=
  ![rightMinorQuotient r x0 x1 x2 x3 w 1 2,
    rightMinorQuotient r x0 x1 x2 x3 w 2 0,
    rightMinorQuotient r x0 x1 x2 x3 w 0 1]

theorem baseRow_minor (r x0 x1 x2 x3 w : R) (j k : Fin 3) :
    baseRow0 r x0 x1 x2 x3 w j * baseRow1 r x0 x1 x2 x3 w k -
      baseRow0 r x0 x1 x2 x3 w k * baseRow1 r x0 x1 x2 x3 w j =
      seedG r x0 x1 x2 x3 w * rightMinorQuotient r x0 x1 x2 x3 w j k := by
  exact coreRight_minor _ _ _ _ _ _ _ _ _ _

theorem baseRow_cross (r x0 x1 x2 x3 w : R) :
    cross (baseRow0 r x0 x1 x2 x3 w) (baseRow1 r x0 x1 x2 x3 w) =
      fun j => seedG r x0 x1 x2 x3 w * rightCrossQuotient r x0 x1 x2 x3 w j := by
  ext j
  fin_cases j
  · exact baseRow_minor r x0 x1 x2 x3 w 1 2
  · exact baseRow_minor r x0 x1 x2 x3 w 2 0
  · exact baseRow_minor r x0 x1 x2 x3 w 0 1

/-- The actual raw matrix, written without expanding its chosen section coefficients. -/
def rawMatrix (r x0 x1 x2 x3 w : R) : Matrix (Fin 3) (Fin 3) R :=
  fun i j => leftCoeff0 x0 x1 x2 x3 w i * baseRow0 r x0 x1 x2 x3 w j +
    leftCoeff1 x0 x1 x2 x3 w i * baseRow1 r x0 x1 x2 x3 w j

def rawCofactorQuotient (r x0 x1 x2 x3 w : R) : Matrix (Fin 3) (Fin 3) R :=
  fun i j => cross (leftCoeff0 x0 x1 x2 x3 w) (leftCoeff1 x0 x1 x2 x3 w) i *
    rightCrossQuotient r x0 x1 x2 x3 w j

def productCorrection (r x0 x1 x2 x3 w : R) (i j : Fin 3) : R :=
  coreProductCorrection (x0^2) (r*x1*x3) (leftCoeff1 x0 x1 x2 x3 w i)
    (rightCoeff2 x0 x1 x2 x3 w j) (rightCoeff3 x0 x1 x2 x3 w j)

def leftSection (r x0 x1 x2 x3 w : R) (i : Fin 3) : R :=
  leftCoeff0 x0 x1 x2 x3 w i * seedP r x0 x1 x2 x3 w +
    leftCoeff1 x0 x1 x2 x3 w i * ((x0^2)^3-(r*x1*x3)^3)

def rightSectionNumerator (r x0 x1 x2 x3 w : R) : Fin 3 → R :=
  baseRow0 r x0 x1 x2 x3 w

/-- Each raw entry is exactly the product built from the chosen linkage sections. -/
theorem rawMatrix_factorization (r x0 x1 x2 x3 w : R) :
    rawMatrix r x0 x1 x2 x3 w =
      fun i j => leftCoeff0 x0 x1 x2 x3 w i * baseRow0 r x0 x1 x2 x3 w j +
        leftCoeff1 x0 x1 x2 x3 w i * baseRow1 r x0 x1 x2 x3 w j := rfl

/-- The literal quotient polynomials agree with the smaller factored expressions. -/
theorem rawCofactorQuotient_factorization (r x0 x1 x2 x3 w : R) :
    rawCofactorQuotient r x0 x1 x2 x3 w =
      fun i j => cross (leftCoeff0 x0 x1 x2 x3 w) (leftCoeff1 x0 x1 x2 x3 w) i *
        rightCrossQuotient r x0 x1 x2 x3 w j := rfl

/-- All nine cofactors of the actual raw seed matrix are divisible by G, before h. -/
theorem rawMatrix_cofactor_identity (r x0 x1 x2 x3 w : R) :
    (rawMatrix r x0 x1 x2 x3 w).adjugate.transpose =
      fun i j => seedG r x0 x1 x2 x3 w * rawCofactorQuotient r x0 x1 x2 x3 w i j := by
  rw [rawMatrix_factorization, cofactors_rank_two, rawCofactorQuotient_factorization]
  ext i j
  rw [baseRow_cross]
  ring

/-- The actual selected L and M sections multiply to p times the raw entry modulo G. -/
theorem selected_product_identity (r x0 x1 x2 x3 w : R) (i j : Fin 3) :
    leftSection r x0 x1 x2 x3 w i * rightSectionNumerator r x0 x1 x2 x3 w j =
      seedP r x0 x1 x2 x3 w * rawMatrix r x0 x1 x2 x3 w i j +
      seedG r x0 x1 x2 x3 w * productCorrection r x0 x1 x2 x3 w i j := by
  exact core_product _ _ _ _ _ _ _ _ _

/-- The chosen first M section is the original Gamma4 numerator. -/
theorem first_rightSection (r x0 x1 x2 x3 w : R) :
    rightSectionNumerator r x0 x1 x2 x3 w 0 =
      (w+x3^2) * (2*w*seedP r x0 x1 x2 x3 w +
        (x0^2)^2*(r*x1*x3)-w*(x2^2)^2) := by
  simp only [rightSectionNumerator, baseRow0, coreRight0, rightCoeff0, rightCoeff2,
    rightCoeff3, seedP, linkageP, Matrix.cons_val_zero]
  ring

end CycleQ2SegreSeed

#print axioms CycleQ2SegreSeed.linkage_pairing
#print axioms CycleQ2SegreSeed.rawMatrix_cofactor_identity
#print axioms CycleQ2SegreSeed.selected_product_identity
#print axioms CycleQ2SegreSeed.first_rightSection

set_option linter.unusedSimpArgs true
end
end
