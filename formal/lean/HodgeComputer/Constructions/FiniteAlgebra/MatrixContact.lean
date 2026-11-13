import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel

/-! Reusable finite-algebra and contact calculus extracted from `HeadOfNaps`’
accepted quadric-contact-broken (#122) and holdout-q2 (#124) proofs.
See this directory’s README for hypotheses, entry points, and attribution. -/

/-!
Polynomial determinant/trace contact certificates.  All differential expressions
below use bundled algebraic derivations; `pderiv_contact` specializes them to
actual formal partial derivatives. No existence of line data is assumed globally.
-/
noncomputable section
open scoped BigOperators

namespace QuadricContact

variable {k R n ι : Type*}
variable [CommRing k] [CommRing R] [Algebra k R]
variable [Fintype n] [DecidableEq n]

/-- Apply a base-ring derivation entrywise to a matrix. -/
def matrixDeriv (δ : Derivation k R R) :
    Matrix n n R →ₗ[k] Matrix n n R where
  toFun M := fun a b => δ (M a b)
  map_add' A B := by ext a b; exact map_add δ _ _
  map_smul' c A := by ext a b; exact δ.toLinearMap.map_smul c _

omit [Fintype n] [DecidableEq n] in
@[simp] theorem matrixDeriv_apply (δ : Derivation k R R)
    (M : Matrix n n R) (a b : n) : matrixDeriv δ M a b = δ (M a b) := rfl

omit [Fintype n] in
@[simp] theorem matrixDeriv_one (δ : Derivation k R R) :
    matrixDeriv δ (1 : Matrix n n R) = 0 := by
  ext a b
  by_cases h : a = b
  · subst b; simp
  · simp [h]

 omit [DecidableEq n] in
 theorem matrixDeriv_mul (δ : Derivation k R R) (A B : Matrix n n R) :
    matrixDeriv δ (A * B) = matrixDeriv δ A * B + A * matrixDeriv δ B := by
  ext a b
  simp only [matrixDeriv_apply, Matrix.mul_apply, map_sum, Derivation.leibniz,
    smul_eq_mul, Matrix.add_apply, Finset.sum_add_distrib]
  rw [add_comm]
  apply congrArg₂ (· + ·)
  · apply Finset.sum_congr rfl
    intro j _
    ring
  · apply Finset.sum_congr rfl
    intro j _
    ring

 omit [Fintype n] [DecidableEq n] in
 theorem matrixDeriv_smul (δ : Derivation k R R) (c : R) (A : Matrix n n R) :
    matrixDeriv δ (c • A) = δ c • A + c • matrixDeriv δ A := by
  ext a b
  simp only [matrixDeriv_apply, Matrix.smul_apply, Matrix.add_apply,
    smul_eq_mul, Derivation.leibniz]
  ring

 omit [DecidableEq n] in
 theorem deriv_trace (δ : Derivation k R R) (A : Matrix n n R) :
    δ A.trace = (matrixDeriv δ A).trace := by
  simp [Matrix.trace]

/-- This is the differentiated adjugate identity, with no division by `D`. -/
theorem deriv_comatrix (δ : Derivation k R R) (L C : Matrix n n R) (D : R)
    (hLC : L * C = D • 1) (hCL : C * L = D • 1) :
    D • matrixDeriv δ C = δ D • C - C * matrixDeriv δ L * C := by
  have h := congrArg (matrixDeriv δ) hLC
  rw [matrixDeriv_mul, matrixDeriv_smul, matrixDeriv_one] at h
  simp only [smul_zero, add_zero] at h
  have h' := congrArg (fun X : Matrix n n R => C * X) h
  simp only [mul_add, ← mul_assoc, hCL, Matrix.smul_mul,
    Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one] at h'
  exact eq_sub_iff_add_eq.mpr (by simpa only [add_comm] using h')

/-- Commutation with an invertible-over-the-fraction-field matrix implies
commutation with its polynomial adjugate. Only regularity of the determinant
is required; no inverse or fraction-field derivation is used. -/
theorem commute_adjugate_of_regular_det (L U : Matrix n n R)
    (hdet : IsLeftRegular L.det) (hcomm : U * L = L * U) :
    U * L.adjugate = L.adjugate * U := by
  apply (Matrix.isRegular_of_isLeftRegular_det hdet).left
  calc
    L * (U * L.adjugate) = (U * L) * L.adjugate := by
      rw [← mul_assoc, ← hcomm]
    _ = L.det • U := by
      rw [mul_assoc, Matrix.mul_adjugate, Matrix.mul_smul, Matrix.mul_one]
    _ = L * (L.adjugate * U) := by
      rw [← mul_assoc, Matrix.mul_adjugate, Matrix.smul_mul, Matrix.one_mul]

variable [Fintype ι]

/-- The matrix contact cancellation; the derivatives are actual derivations. -/
theorem comatrix_contact_divergence
    (δ : ι → Derivation k R R) (L C : Matrix n n R) (D : R)
    (U : ι → Matrix n n R)
    (hLC : L * C = D • 1) (hCL : C * L = D • 1)
    (hcomm : ∀ i, U i * C = C * U i)
    (hdiv : ∑ i, matrixDeriv (δ i) (U i) = 0)
    (htan : ∑ i, U i * matrixDeriv (δ i) L = 0) :
    D • (∑ i, matrixDeriv (δ i) (U i * C)) =
      ∑ i, δ i D • (U i * C) := by
  have hterm (i : ι) :
      D • matrixDeriv (δ i) (U i * C) =
        D • (matrixDeriv (δ i) (U i) * C) +
        δ i D • (U i * C) - C * (U i * matrixDeriv (δ i) L) * C := by
    rw [matrixDeriv_mul, smul_add]
    rw [show D • (U i * matrixDeriv (δ i) C) =
        U i * (D • matrixDeriv (δ i) C) by rw [Matrix.mul_smul]]
    rw [deriv_comatrix (δ i) L C D hLC hCL, mul_sub, Matrix.mul_smul]
    have hswap : U i * (C * matrixDeriv (δ i) L * C) =
        C * (U i * matrixDeriv (δ i) L) * C := by
      simp only [← mul_assoc]
      rw [hcomm i]
    rw [hswap]
    abel
  calc
    D • (∑ i, matrixDeriv (δ i) (U i * C)) =
        ∑ i, D • matrixDeriv (δ i) (U i * C) := by rw [Finset.smul_sum]
    _ = (∑ i, D • (matrixDeriv (δ i) (U i) * C)) +
        (∑ i, δ i D • (U i * C)) -
        ∑ i, C * (U i * matrixDeriv (δ i) L) * C := by
      simp_rw [hterm]
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
    _ = D • ((∑ i, matrixDeriv (δ i) (U i)) * C) +
        (∑ i, δ i D • (U i * C)) -
        C * (∑ i, U i * matrixDeriv (δ i) L) * C := by
      simp only [Finset.smul_sum, Finset.sum_mul, Finset.mul_sum]
    _ = ∑ i, δ i D • (U i * C) := by rw [hdiv, htan]; simp

/-- Descent by a constant matrix weight. -/
theorem trace_contact_divergence
    (δ : ι → Derivation k R R) (L C H : Matrix n n R) (D : R)
    (U : ι → Matrix n n R)
    (hLC : L * C = D • 1) (hCL : C * L = D • 1)
    (hcomm : ∀ i, U i * C = C * U i)
    (hH : ∀ i, matrixDeriv (δ i) H = 0)
    (hdiv : ∑ i, matrixDeriv (δ i) (U i) = 0)
    (htan : ∑ i, U i * matrixDeriv (δ i) L = 0) :
    D * (∑ i, δ i (H * (U i * C)).trace) =
      ∑ i, (H * (U i * C)).trace * δ i D := by
  have h := comatrix_contact_divergence δ L C D U hLC hCL hcomm hdiv htan
  have h' := congrArg (fun X : Matrix n n R => (H * X).trace) h
  simp only [Matrix.mul_smul, Matrix.trace_smul, Finset.mul_sum, Matrix.trace_sum,
    smul_eq_mul] at h'
  have hd (i : ι) : δ i (H * (U i * C)).trace =
      (H * matrixDeriv (δ i) (U i * C)).trace := by
    rw [deriv_trace, matrixDeriv_mul, hH i, zero_mul, zero_add]
  simpa only [hd, mul_comm, Finset.mul_sum] using h'

 theorem trace_contact_source (L C H J : Matrix n n R) (D : R)
    (U : ι → Matrix n n R) (g : ι → R)
    (hLC : L * C = D • 1)
    (hsource : ∑ i, g i • U i = J * L) :
    (∑ i, (H * (U i * C)).trace * g i) = D * (H * J).trace := by
  have h := congrArg (fun X : Matrix n n R => (H * (X * C)).trace) hsource
  simp only [Finset.sum_mul, Finset.mul_sum, Matrix.trace_sum, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul] at h
  rw [mul_assoc J L C, hLC, Matrix.mul_smul, Matrix.mul_one,
    Matrix.mul_smul, Matrix.trace_smul] at h
  simpa only [smul_eq_mul, mul_comm] using h

/-- Specialization to a polynomial determinant and actual partial derivatives. -/
theorem pderiv_contact {K σ : Type*} [CommRing K] [Fintype σ]
    (L H J : Matrix n n (MvPolynomial σ K))
    (U : σ → Matrix n n (MvPolynomial σ K)) (G A : MvPolynomial σ K)
    (hcomm : ∀ i, U i * L.adjugate = L.adjugate * U i)
    (hH : ∀ i, matrixDeriv (MvPolynomial.pderiv i) H = 0)
    (hdiv : ∑ i, matrixDeriv (MvPolynomial.pderiv i) (U i) = 0)
    (htan : ∑ i, U i * matrixDeriv (MvPolynomial.pderiv i) L = 0)
    (hsource : ∑ i, MvPolynomial.pderiv i G • U i = J * L)
    (htarget : (H * J).trace = A) :
    let D := L.det
    let N := fun i => (H * (U i * L.adjugate)).trace
    (∑ i, N i * MvPolynomial.pderiv i G) = D * A ∧
      D * (∑ i, MvPolynomial.pderiv i (N i)) =
        ∑ i, N i * MvPolynomial.pderiv i D := by
  dsimp
  constructor
  · rw [← htarget]
    exact trace_contact_source L L.adjugate H J L.det U
      (fun i => MvPolynomial.pderiv i G) (Matrix.mul_adjugate L) hsource
  · exact trace_contact_divergence (fun i => MvPolynomial.pderiv i)
      L L.adjugate H L.det U (Matrix.mul_adjugate L) (Matrix.adjugate_mul L)
      hcomm hH hdiv htan

/-- Any linear coefficient functional descends a matrix contact certificate. -/
theorem functional_contact_divergence
    (δ : ι → Derivation k R R) (L C : Matrix n n R) (D : R)
    (U : ι → Matrix n n R) (τ : Matrix n n R →ₗ[R] R)
    (hτ : ∀ i M, δ i (τ M) = τ (matrixDeriv (δ i) M))
    (hLC : L * C = D • 1) (hCL : C * L = D • 1)
    (hcomm : ∀ i, U i * C = C * U i)
    (hdiv : ∑ i, matrixDeriv (δ i) (U i) = 0)
    (htan : ∑ i, U i * matrixDeriv (δ i) L = 0) :
    D * (∑ i, δ i (τ (U i * C))) = ∑ i, τ (U i * C) * δ i D := by
  have h := congrArg τ
    (comatrix_contact_divergence δ L C D U hLC hCL hcomm hdiv htan)
  simpa only [hτ, map_smul, map_sum, smul_eq_mul, mul_comm] using h

 theorem functional_contact_source
    (L C J : Matrix n n R) (D : R) (U : ι → Matrix n n R) (g : ι → R)
    (τ : Matrix n n R →ₗ[R] R) (hLC : L * C = D • 1)
    (hsource : ∑ i, g i • U i = J * L) :
    (∑ i, τ (U i * C) * g i) = D * τ J := by
  have h := congrArg (fun X : Matrix n n R => τ (X * C)) hsource
  rw [mul_assoc J L C, hLC, Matrix.mul_smul, Matrix.mul_one] at h
  simpa only [Finset.sum_mul, Matrix.smul_mul, map_sum, map_smul,
    smul_eq_mul, mul_comm] using h

/-- A coefficient functional on the column representing the element 1.
For the regular representation in basis (1,r,...), set `j=0`. -/
def columnFunctional (w : n → R) (j : n) : Matrix n n R →ₗ[R] R where
  toFun M := ∑ a, w a * M a j
  map_add' A B := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' c A := by simp [Finset.mul_sum, mul_left_comm]

 omit [DecidableEq n] in
 theorem deriv_columnFunctional (δ : Derivation k R R) (w : n → R) (j : n)
    (hw : ∀ a, δ (w a) = 0) (M : Matrix n n R) :
    δ (columnFunctional w j M) = columnFunctional w j (matrixDeriv δ M) := by
  simp only [columnFunctional, LinearMap.coe_mk, AddHom.coe_mk, map_sum,
    Derivation.leibniz, hw, mul_zero, add_zero, smul_eq_mul, matrixDeriv_apply]

 theorem pderiv_contact_column {K σ : Type*} [CommRing K] [Fintype σ]
    (L J : Matrix n n (MvPolynomial σ K))
    (U : σ → Matrix n n (MvPolynomial σ K)) (w : n → K) (j : n)
    (G A : MvPolynomial σ K)
    (hcomm : ∀ i, U i * L.adjugate = L.adjugate * U i)
    (hdiv : ∑ i, matrixDeriv (MvPolynomial.pderiv i) (U i) = 0)
    (htan : ∑ i, U i * matrixDeriv (MvPolynomial.pderiv i) L = 0)
    (hsource : ∑ i, MvPolynomial.pderiv i G • U i = J * L)
    (htarget : columnFunctional (fun a => MvPolynomial.C (w a)) j J = A) :
    let D := L.det
    let N := fun i => columnFunctional (fun a => MvPolynomial.C (w a)) j
      (U i * L.adjugate)
    (∑ i, N i * MvPolynomial.pderiv i G) = D * A ∧
      D * (∑ i, MvPolynomial.pderiv i (N i)) =
        ∑ i, N i * MvPolynomial.pderiv i D := by
  dsimp
  constructor
  · rw [← htarget]
    exact functional_contact_source L L.adjugate J L.det U
      (fun i => MvPolynomial.pderiv i G)
      (columnFunctional (fun a => MvPolynomial.C (w a)) j)
      (Matrix.mul_adjugate L) hsource
  · apply functional_contact_divergence (fun i => MvPolynomial.pderiv i)
      L L.adjugate L.det U
      (columnFunctional (fun a => MvPolynomial.C (w a)) j)
      _ (Matrix.mul_adjugate L) (Matrix.adjugate_mul L) hcomm hdiv htan
    intro i M
    exact deriv_columnFunctional (MvPolynomial.pderiv i) _ j
      (fun a => MvPolynomial.pderiv_C) M

end QuadricContact

#print axioms QuadricContact.pderiv_contact

#print axioms QuadricContact.pderiv_contact_column

