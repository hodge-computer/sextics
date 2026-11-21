import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Existing sparse curve coordinates and localization maps

These declarations are moved from the earlier aggregate modules, preserving
all namespaces, types, and definition bodies. The actual degree-one Cech
objects can therefore depend on their coordinate rings without importing
the unrelated residue and analytic constructions. The proof of the first
quartic's quotient formula is made local to these literal polynomials.
-/

set_option autoImplicit false

noncomputable section

namespace CycleQ2SeedTrace
open MvPolynomial

abbrev Poly := MvPolynomial (Fin 4) ℂ

def b : Poly := X 3 ^ 3 + X 2 ^ 3 + X 1 * X 2 * X 3 + X 0 * X 2 * X 3 + X 0 * X 1 ^ 2

def h : Poly := b - C Complex.I * (X 1 ^ 3 + X 3 ^ 3)

def relation (r : ℂ) : Fin 4 → Poly := ![
  X 0 ^ 2 - C r * X 1 * X 3,
  X 1 ^ 2 * X 3 ^ 2,
  X 2 ^ 4,
  h]

def reducedIdeal (r : ℂ) : Ideal Poly := Ideal.span (Set.range (relation r))

abbrev WeightedPoly := MvPolynomial (Fin 5) ℂ

def originalG1 (r : ℂ) : WeightedPoly :=
  X 0 ^ 4 + C r * X 0 ^ 2 * X 1 * X 3 + C (r ^ 2) * X 1 ^ 2 * X 3 ^ 2

def originalG2 : WeightedPoly := X 4 ^ 2 - X 4 * X 2 ^ 2 + X 2 ^ 4

def substitute : WeightedPoly →ₐ[ℂ] Poly :=
  MvPolynomial.aeval ![X 0, X 1, X 2, X 3, -(X 2 ^ 2)]

end CycleQ2SeedTrace

namespace CycleQ2SeedCech
open MvPolynomial CycleQ2SeedTrace

def curveA : Poly := X 1 * X 3

def curveB : Poly := X 2

end CycleQ2SeedCech

namespace CycleQ2SeedCechTheta
open MvPolynomial CycleQ2SeedTrace

def curveH (θ : ℂ) : Poly := h + C θ * X 0 ^ 3

def curveIdeal (r θ : ℂ) : Ideal Poly := Ideal.span {relation r 0, curveH θ}

end CycleQ2SeedCechTheta

namespace CycleQ2NormalConnecting
open MvPolynomial CycleQ2SeedTrace CycleQ2SeedCechTheta
open CycleQ2SeedCech (curveA curveB)

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

theorem ambientCurveMap_g1 (r θ : ℂ) :
    ambientCurveMap r θ (originalG1 r) =
      curveMap r θ (C (3 * r ^ 2) * curveA ^ 2) := by
  change curveMap r θ (substitute (originalG1 r)) = _
  have hh : substitute (originalG1 r) =
      relation r 0 * (X 0 ^ 2 + C (2 * r) * X 1 * X 3) +
        C (3 * r ^ 2) * curveA ^ 2 := by
    simp only [substitute, originalG1, relation, curveA, Matrix.cons_val_zero,
      map_add, map_mul, map_pow, MvPolynomial.aeval_X, MvPolynomial.aeval_C]
    simp only [map_ofNat, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_three,
      Matrix.head_cons, Matrix.tail_cons, MvPolynomial.algebraMap_eq]
    ring
  rw [hh]
  simp only [map_add, map_mul, curveMap_f1, zero_mul, zero_add]

theorem ambientCurveMap_g2 (r θ : ℂ) :
    ambientCurveMap r θ originalG2=curveMap r θ (C 3*curveB^4) := by
  change curveMap r θ (substitute originalG2) = curveMap r θ (C 3 * curveB ^ 4)
  apply congrArg (curveMap r θ)
  simp only [substitute, originalG2, curveB, map_sub, map_add, map_mul, map_pow,
    MvPolynomial.aeval_X, Matrix.cons_val_two, Matrix.cons_val_four,
    Matrix.head_cons, Matrix.tail_cons, map_ofNat]
  ring

def curveG1 (r θ : ℂ) : CurveRing r θ := ambientCurveMap r θ (originalG1 r)

def curveG2 (r θ : ℂ) : CurveRing r θ := ambientCurveMap r θ originalG2

abbrev FirstOpen (r θ : ℂ) := Localization.Away (curveG1 r θ)

abbrev SecondOpen (r θ : ℂ) := Localization.Away (curveG2 r θ)

abbrev Overlap (r θ : ℂ) := Localization.Away (curveG1 r θ*curveG2 r θ)

def firstRestriction (r θ : ℂ) : FirstOpen r θ →+* Overlap r θ :=
  IsLocalization.Away.awayToAwayRight (curveG1 r θ) (curveG2 r θ)

def secondRestriction (r θ : ℂ) : SecondOpen r θ →+* Overlap r θ :=
  IsLocalization.Away.awayToAwayLeft (curveG2 r θ) (curveG1 r θ)

end CycleQ2NormalConnecting

end
