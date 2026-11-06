import HodgeComputer.Constructions.FiniteAlgebra.AdjoinRootSpecialization
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

noncomputable section
open scoped BigOperators
namespace QuadricContact
open Module

variable {R E : Type*} [CommRing R] [CommRing E] [Algebra R E]

/-- The first eight power-basis coordinates of the eight source coefficients. -/
def sourceMinor (b : Basis (Fin 27) R E) (s : Fin 8 → E) :
    Matrix (Fin 8) (Fin 8) R := fun i j => b.repr (s i) (Fin.castAdd 19 j)

/-- Extend the selected inverse column by zero on the unused coordinates. -/
def sourceWeights (M : Matrix (Fin 8) (Fin 8) R) : Fin 27 → R :=
  fun j => Fin.addCases (motive := fun _ => R)
    (fun i : Fin 8 => M⁻¹ i 3) (fun _ : Fin 19 => 0) j

theorem sourceMinor_map {S : Type*} [CommRing S] (f : R →+* S)
    (p : Polynomial R) (hp : p.Monic) (hn : p.natDegree = 27)
    (hm : (p.map f).natDegree = 27) (s : Fin 8 → AdjoinRoot p) :
    (sourceMinor (AdjoinRootSpecialization.basis p hp hn) s).map f =
      sourceMinor (AdjoinRootSpecialization.basis (p.map f) (hp.map f) hm)
        (fun i => AdjoinRootSpecialization.specialize f p (s i)) := by
  ext i j
  simp only [Matrix.map_apply, sourceMinor, AdjoinRootSpecialization.basis_repr]
  exact AdjoinRootSpecialization.map_coordinate f p hp (s i) _

theorem sourceWeights_pairing (b : Basis (Fin 27) R E) (s : Fin 8 → E)
    (h : IsUnit (sourceMinor b s).det) (i : Fin 8) :
    (∑ j : Fin 27, sourceWeights (sourceMinor b s) j * b.repr (s i) j) =
      if i = 3 then 1 else 0 := by
  have hm := congrArg (fun M : Matrix (Fin 8) (Fin 8) R => M i 3)
    (Matrix.mul_nonsing_inv (sourceMinor b s) h)
  rw [Matrix.mul_apply, Matrix.one_apply] at hm
  rw [Fin.sum_univ_add (a := 8) (b := 19)]
  simp only [sourceWeights, Fin.addCases_left, Fin.addCases_right, zero_mul,
    Finset.sum_const_zero, add_zero]
  simpa only [sourceMinor, mul_comm] using hm

theorem sourceWeights_matrix (b : Basis (Fin 27) R E) (s : Fin 8 → E)
    (h : IsUnit (sourceMinor b s).det) (hb : b 0 = 1) (i : Fin 8) :
    (∑ j : Fin 27, sourceWeights (sourceMinor b s) j *
      Algebra.leftMulMatrix b (s i) j 0) = if i = 3 then 1 else 0 := by
  simpa only [Algebra.leftMulMatrix_eq_repr_mul, hb, mul_one] using
    sourceWeights_pairing b s h i

end QuadricContact

#print axioms QuadricContact.sourceWeights_matrix
