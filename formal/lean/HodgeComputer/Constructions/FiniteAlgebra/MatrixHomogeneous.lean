import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Tactic.Ring

/-! Reusable finite-algebra and contact calculus extracted from `HeadOfNaps`’
accepted quadric-contact-broken (#122) and holdout-q2 (#124) proofs.
See this directory’s README for hypotheses, entry points, and attribution. -/

noncomputable section
open scoped BigOperators
namespace QuadricContact
open MvPolynomial

variable {K σ n : Type*} [CommRing K] [Fintype n] [DecidableEq n]

/-- Rowwise homogeneous matrices have homogeneous determinants. -/
theorem determinant_homogeneous_rows
    (M : Matrix n n (MvPolynomial σ K)) (d : n → ℕ)
    (h : ∀ a b, (M a b).IsHomogeneous (d a)) :
    M.det.IsHomogeneous (∑ a, d a) := by
  classical
  rw [Matrix.det_apply]
  apply IsHomogeneous.sum
  intro p _
  have hp : (∏ a, M (p a) a).IsHomogeneous (∑ a, d (p a)) :=
    IsHomogeneous.prod Finset.univ (fun a => M (p a) a) (fun a => d (p a))
      (fun a _ => h (p a) a)
  rw [Equiv.sum_comp p d] at hp
  rcases Int.units_eq_one_or (Equiv.Perm.sign p) with hs | hs
  · simpa [hs] using hp
  · simpa [hs] using hp.neg

 theorem determinant_homogeneous
    (M : Matrix n n (MvPolynomial σ K)) (d : ℕ)
    (h : ∀ a b, (M a b).IsHomogeneous d) :
    M.det.IsHomogeneous (Fintype.card n * d) := by
  simpa using determinant_homogeneous_rows M (fun _ => d) h

 theorem adjugate_homogeneous
    (M : Matrix n n (MvPolynomial σ K)) (d : ℕ)
    (h : ∀ a b, (M a b).IsHomogeneous d) (i j : n) :
    (M.adjugate i j).IsHomogeneous ((Fintype.card n - 1) * d) := by
  classical
  rw [Matrix.adjugate_apply]
  have hh : ∀ a b, ((M.updateRow j (Pi.single i 1)) a b).IsHomogeneous
      (if a = j then 0 else d) := by
    intro a b
    by_cases ha : a = j
    · subst a
      by_cases hb : b = i
      · subst b
        simpa using (isHomogeneous_one σ K : (1 : MvPolynomial σ K).IsHomogeneous 0)
      · simpa [hb] using (isHomogeneous_zero σ K 0 : (0 : MvPolynomial σ K).IsHomogeneous 0)
    · simpa [Matrix.updateRow_apply, ha] using h a b
  have hh' := determinant_homogeneous_rows (M.updateRow j (Pi.single i 1))
    (fun a => if a = j then 0 else d) hh
  have hdegree : (∑ a : n, if a = j then 0 else d) = (Fintype.card n - 1) * d := by
    rw [Finset.sum_ite]
    simp
    left
    have hf : (Finset.univ.filter fun a : n => ¬ a = j) = Finset.univ.erase j := by
      ext a
      simp [ne_comm]
    rw [hf]
    simp
  simpa only [hdegree] using hh'

 theorem matrix_mul_homogeneous
    (A B : Matrix n n (MvPolynomial σ K)) (a b : ℕ)
    (hA : ∀ i j, (A i j).IsHomogeneous a)
    (hB : ∀ i j, (B i j).IsHomogeneous b) (i j : n) :
    ((A * B) i j).IsHomogeneous (a + b) := by
  rw [Matrix.mul_apply]
  exact IsHomogeneous.sum Finset.univ _ _ (fun k _ => (hA i k).mul (hB k j))

 theorem matrix_trace_homogeneous
    (A : Matrix n n (MvPolynomial σ K)) (a : ℕ)
    (hA : ∀ i j, (A i j).IsHomogeneous a) : A.trace.IsHomogeneous a := by
  exact IsHomogeneous.sum Finset.univ _ _ (fun i _ => hA i i)

/-- Evaluation at any point where the matrix is invertible proves that its
polynomial determinant is nonzero. -/
theorem determinant_ne_zero_of_map_eq_one
    {R S : Type*} [CommRing R] [CommRing S] [Nontrivial S]
    (M : Matrix n n R) (f : R →+* S)
    (h : M.map f = (1 : Matrix n n S)) : M.det ≠ 0 := by
  intro hzero
  have hh := congrArg Matrix.det h
  change (f.mapMatrix M).det = Matrix.det 1 at hh
  rw [← f.map_det, hzero, map_zero, Matrix.det_one] at hh
  exact zero_ne_one hh

/-- Homogeneity of determinant-cleared numerators with constant coefficient
weights; no expansion of the adjugate or determinant is needed. -/
theorem column_contact_numerator_homogeneous
    (L U : Matrix n n (MvPolynomial σ K)) (w : n → K) (j : n) (d : ℕ)
    (hL : ∀ a b, (L a b).IsHomogeneous d)
    (hU : ∀ a b, (U a b).IsHomogeneous d) :
    (∑ a, MvPolynomial.C (w a) * (U * L.adjugate) a j).IsHomogeneous
      (d + (Fintype.card n - 1) * d) := by
  exact IsHomogeneous.sum Finset.univ _ _ (fun a _ =>
    (matrix_mul_homogeneous U L.adjugate d ((Fintype.card n - 1) * d)
      hU (adjugate_homogeneous L d hL) a j).C_mul (w a))

end QuadricContact

#print axioms QuadricContact.adjugate_homogeneous
#print axioms QuadricContact.determinant_ne_zero_of_map_eq_one

#print axioms QuadricContact.column_contact_numerator_homogeneous

