import Mathlib.RingTheory.AdjoinRoot
import Mathlib.LinearAlgebra.Matrix.ToLin
import HodgeComputer.Constructions.FiniteAlgebra.RegularSpecialization

/-! Reusable finite-algebra and contact calculus extracted from `HeadOfNaps`’
accepted quadric-contact-broken (#122) and holdout-q2 (#124) proofs.
See this directory’s README for hypotheses, entry points, and attribution. -/

namespace AdjoinRootSpecialization

open Polynomial Module
variable {R S : Type*} [CommRing R] [CommRing S]

/-- The quotient algebra under coefficient specialization. -/
noncomputable def specialize (f : R →+* S) (p : R[X]) :
    AdjoinRoot p →+* AdjoinRoot (p.map f) :=
  AdjoinRoot.map f p (p.map f) (dvd_refl _)

@[simp] theorem specialize_root (f : R →+* S) (p : R[X]) :
    specialize f p (AdjoinRoot.root p) = AdjoinRoot.root (p.map f) := by
  simp [specialize]

@[simp] theorem specialize_of (f : R →+* S) (p : R[X]) (r : R) :
    specialize f p (AdjoinRoot.of p r) = AdjoinRoot.of (p.map f) (f r) := by
  simp [specialize]

@[simp] theorem specialize_mk (f : R →+* S) (p g : R[X]) :
    specialize f p (AdjoinRoot.mk p g) = AdjoinRoot.mk (p.map f) (g.map f) := by
  simp only [specialize, AdjoinRoot.map, AdjoinRoot.lift_mk]
  rw [← AdjoinRoot.aeval_eq, Polynomial.aeval_def, Polynomial.eval₂_map]
  rfl

/-- Normal forms commute with specialization for a monic defining polynomial. -/
theorem map_normalForm (f : R →+* S) (p : R[X]) (hp : p.Monic)
    (x : AdjoinRoot p) :
    (AdjoinRoot.modByMonicHom hp x).map f =
      AdjoinRoot.modByMonicHom (hp.map f) (specialize f p x) := by
  induction x using AdjoinRoot.induction_on p with
  | ih g =>
      simp only [AdjoinRoot.modByMonicHom_mk, specialize_mk]
      exact Polynomial.map_modByMonic f hp

/-- In particular, each power-basis coordinate specializes correctly. -/
theorem map_coordinate (f : R →+* S) (p : R[X]) (hp : p.Monic)
    (x : AdjoinRoot p) (i : ℕ) :
    f ((AdjoinRoot.modByMonicHom hp x).coeff i) =
      (AdjoinRoot.modByMonicHom (hp.map f) (specialize f p x)).coeff i := by
  rw [← Polynomial.coeff_map, map_normalForm]

/-- Reindex the standard power basis to a chosen explicit dimension. -/
noncomputable def basis (p : R[X]) (hp : p.Monic) {n : ℕ} (hn : p.natDegree = n) :
    Basis (Fin n) R (AdjoinRoot p) :=
  (AdjoinRoot.powerBasisAux' hp).reindex (finCongr hn)

@[simp] theorem basis_repr (p : R[X]) (hp : p.Monic) {n : ℕ} (hn : p.natDegree = n)
    (x : AdjoinRoot p) (i : Fin n) :
    (basis p hp hn).repr x i = (AdjoinRoot.modByMonicHom hp x).coeff i.val := by
  subst n
  rfl

@[simp] theorem basis_apply (p : R[X]) (hp : p.Monic) {n : ℕ} (hn : p.natDegree = n)
    (i : Fin n) : basis p hp hn i = AdjoinRoot.root p ^ i.val := by
  subst n
  exact (AdjoinRoot.powerBasis' hp).basis_eq_pow i

/-- Matrix entries of multiplication in the power basis are normal-form coefficients. -/
theorem leftMulMatrix_entry (p : R[X]) (hp : p.Monic) {n : ℕ}
    (hn : p.natDegree = n) (x : AdjoinRoot p) (i j : Fin n) :
    Algebra.leftMulMatrix (basis p hp hn) x i j =
      (AdjoinRoot.modByMonicHom hp (x * AdjoinRoot.root p ^ j.val)).coeff i.val := by
  rw [Algebra.leftMulMatrix_eq_repr_mul, basis_repr, basis_apply]

/-- This is the link from generic multiplication matrices to exact specialized data. -/
theorem map_leftMulMatrix (f : R →+* S) (p : R[X]) (hp : p.Monic) {n : ℕ}
    (hn : p.natDegree = n) (hm : (p.map f).natDegree = n) (x : AdjoinRoot p) :
    (Algebra.leftMulMatrix (basis p hp hn) x).map f =
      Algebra.leftMulMatrix (basis (p.map f) (hp.map f) hm) (specialize f p x) := by
  ext i j
  simp only [Matrix.map_apply, leftMulMatrix_entry]
  rw [map_coordinate]
  simp only [map_mul, map_pow, specialize_root]

end AdjoinRootSpecialization

