import Proposal.GeometricFermatStrictGrowth
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# An invertible Fermat Higgs combination

The integer inverse certifies a seven-direction combination of the
ordered Fermat Higgs matrices over every field.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false

namespace CycleQ2FermatHiggsInvertible

open CycleQ2FermatStrictGrowth

def directions : List (Fin 35) := [7, 13, 14, 21, 24, 26, 27]

def combined {R : Type*} [AddMonoid R] (M : Fin 35 → Matrix (Fin 33) (Fin 33) R) :
    Matrix (Fin 33) (Fin 33) R :=
  (directions.map M).sum

private def inverse : Matrix (Fin 33) (Fin 33) ℤ := ![
  ![0, -1, 0, -1, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 1, -1, 0, 0, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, -1, 0, -1, 1, 0],
  ![0, -2, 2, 0, 2, 1, 1, 0, 0, -1, 0, -1, 1, 0, 0, -1, 0, -1, 1, 0, -1, 0, 1, 1, 0, -1, -1, 0, 1, 0, 1, -1, 0],
  ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, -1, 1, 0, 1, 1, 1, 0, 0, 0, 0, -1, 0, 0, 0, -1, 0, -1, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 1, 0, 1, -1, 0],
  ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![-1, 1, 0, 1, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0],
  ![0, 1, -1, 0, -1, -1, -1, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1, -1, 0, 0, 0, -1, -1, 0, 1, 0, 0, -1, 0, -1, 1, 0],
  ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![-1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 1, 0, 0],
  ![0, -1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 1, 0, 1, -1, 0],
  ![0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0],
  ![0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 1, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 1, -1, 0, -1, 0, -1, 0, 1],
  ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, -1, 0, -1, 1, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 1, -1, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -1, 0, -1, 1, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 1, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 1, 0, 1, -1, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0, 1, -1, 0, 0, 1, 0, 2, 0, -1],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1],
  ![0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, -1, 0, 0, -1, 0, 0, 1, 1, 0, 0, -1, 0, 0, 1, 0, 2, -1, 0],
  ![0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 1, 0, 0, -1, -1, 0, 0, 1, 1, 1, -1, 0, -2, 1, -1],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, -1, 0, 0, 1, 0, 0, 0]
]

private theorem inverse_eq :
    combined (ordered ℤ) * inverse = 1 := by
  ext i j
  revert j
  fin_cases i <;> decide +kernel

theorem combined_map {R S : Type*} [Semiring R] [Semiring S] (f : R →+* S)
    (M : Fin 35 → Matrix (Fin 33) (Fin 33) R) :
    (combined M).map f = combined (fun m => (M m).map f) := by
  unfold combined
  generalize directions = ms
  induction ms with
  | nil => simp
  | cons m ms ih =>
    simp only [List.map_cons, List.sum_cons]
    change f.mapMatrix (M m + (List.map M ms).sum) = _
    rw [map_add]
    exact congrArg ((M m).map f + ·) ih

theorem det_ne_zero (K : Type*) [Field K] : (combined (ordered K)).det ≠ 0 := by
  apply Matrix.det_ne_zero_of_right_inverse (B := inverse.map (Int.castRingHom K))
  have h := congrArg (fun M : Matrix (Fin 33) (Fin 33) ℤ => M.map (Int.castRingHom K)) inverse_eq
  rw [Matrix.map_mul, combined_map, Matrix.map_one _ (map_zero _) (map_one _)] at h
  have hm (m : Fin 35) : (ordered ℤ m).map (Int.castRingHom K) = ordered K m := by
    ext i j
    change (Int.castRingHom K) (ordered ℤ m i j) = ordered K m i j
    unfold ordered CycleQ2FermatHiggs.higgsMatrix
    split <;> simp
  simpa only [hm] using h

end CycleQ2FermatHiggsInvertible

#print axioms CycleQ2FermatHiggsInvertible.det_ne_zero
