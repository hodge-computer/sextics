import HodgeComputer.Constructions.FiniteAlgebra.MatrixContact
import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-! Reusable finite-algebra and contact calculus extracted from `HeadOfNaps`’
accepted quadric-contact-broken (#122) and holdout-q2 (#124) proofs.
See this directory’s README for hypotheses, entry points, and attribution. -/

noncomputable section
open scoped BigOperators IsMulCommutative
namespace QuadricContact

variable {K E σ n : Type*} [CommRing K] [CommRing E]
variable [Fintype n] [DecidableEq n]

/-- The commutative subalgebra generated over the active polynomial ring by
coefficient matrices. This allows the usual multivariate universal property. -/
abbrev coefficientAlgebra (ρ : E →+* Matrix n n (MvPolynomial σ K)) :=
  Algebra.adjoin (MvPolynomial σ K) (Set.range ρ)

instance coefficientAlgebra_comm (ρ : E →+* Matrix n n (MvPolynomial σ K)) :
    IsMulCommutative (coefficientAlgebra ρ) := by
  apply Algebra.isMulCommutative_adjoin
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
  rw [← map_mul, ← map_mul, mul_comm a b]

 def coefficientLift (ρ : E →+* Matrix n n (MvPolynomial σ K)) :
    E →+* coefficientAlgebra ρ where
  toFun a := ⟨ρ a, Algebra.subset_adjoin ⟨a, rfl⟩⟩
  map_zero' := Subtype.ext (map_zero ρ)
  map_one' := Subtype.ext (map_one ρ)
  map_add' a b := Subtype.ext (map_add ρ a b)
  map_mul' a b := Subtype.ext (map_mul ρ a b)

 def commutingPolynomialEval (ρ : E →+* Matrix n n (MvPolynomial σ K)) :
    MvPolynomial σ E →+* Matrix n n (MvPolynomial σ K) :=
  (coefficientAlgebra ρ).val.toRingHom.comp
    (MvPolynomial.eval₂Hom (coefficientLift ρ)
      (fun i => algebraMap (MvPolynomial σ K) (coefficientAlgebra ρ) (MvPolynomial.X i)))

@[simp] theorem commutingPolynomialEval_C
    (ρ : E →+* Matrix n n (MvPolynomial σ K)) (a : E) :
    commutingPolynomialEval ρ (MvPolynomial.C a) = ρ a := by
  simp [commutingPolynomialEval, coefficientLift]

@[simp] theorem commutingPolynomialEval_X
    (ρ : E →+* Matrix n n (MvPolynomial σ K)) (i : σ) :
    commutingPolynomialEval ρ (MvPolynomial.X i) =
      (MvPolynomial.X i : MvPolynomial σ K) • (1 : Matrix n n (MvPolynomial σ K)) := by
  simp [commutingPolynomialEval, Algebra.algebraMap_eq_smul_one]

 def polynomialMatrixMap (ρ : E →+* Matrix n n K) :
    MvPolynomial σ E →+* Matrix n n (MvPolynomial σ K) :=
  commutingPolynomialEval (MvPolynomial.C.mapMatrix.comp ρ)

@[simp] theorem polynomialMatrixMap_C (ρ : E →+* Matrix n n K) (a : E) :
    polynomialMatrixMap (σ := σ) ρ (MvPolynomial.C a) =
      (ρ a).map MvPolynomial.C := by
  simp [polynomialMatrixMap]

@[simp] theorem polynomialMatrixMap_X (ρ : E →+* Matrix n n K) (i : σ) :
    polynomialMatrixMap ρ (MvPolynomial.X i) =
      (MvPolynomial.X i : MvPolynomial σ K) • (1 : Matrix n n (MvPolynomial σ K)) := by
  exact commutingPolynomialEval_X _ _

 theorem polynomialMatrixMap_deriv (ρ : E →+* Matrix n n K) (i : σ)
    (p : MvPolynomial σ E) :
    polynomialMatrixMap ρ (MvPolynomial.pderiv i p) =
      matrixDeriv (MvPolynomial.pderiv i) (polynomialMatrixMap ρ p) := by
  classical
  have hC (a : E) :
      polynomialMatrixMap ρ (MvPolynomial.pderiv i (MvPolynomial.C a)) =
      matrixDeriv (MvPolynomial.pderiv i) (polynomialMatrixMap ρ (MvPolynomial.C a)) := by
    rw [MvPolynomial.pderiv_C, map_zero, polynomialMatrixMap_C]
    ext a b
    simp [matrixDeriv_apply, Matrix.map_apply, MvPolynomial.pderiv_C]
  have hX (j : σ) :
      polynomialMatrixMap ρ (MvPolynomial.pderiv i (MvPolynomial.X j)) =
      matrixDeriv (MvPolynomial.pderiv i) (polynomialMatrixMap ρ (MvPolynomial.X j)) := by
    rw [polynomialMatrixMap_X, matrixDeriv_smul, matrixDeriv_one]
    by_cases hij : j = i
    · subst j
      simp
    · simp [MvPolynomial.pderiv_X_of_ne hij]
  induction p using MvPolynomial.induction_on with
  | C a => exact hC a
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p j hp =>
      simp only [MvPolynomial.pderiv_mul, map_add, map_mul, matrixDeriv_mul, hp, hX]

 theorem polynomialMatrixMap_commute (ρ : E →+* Matrix n n K)
    (p q : MvPolynomial σ E) :
    polynomialMatrixMap ρ p * polynomialMatrixMap ρ q =
      polynomialMatrixMap ρ q * polynomialMatrixMap ρ p := by
  rw [← map_mul, ← map_mul, mul_comm p q]

 theorem polynomialMatrixMap_base [Algebra K E]
    (ρ : E →ₐ[K] Matrix n n K) (p : MvPolynomial σ K) :
    polynomialMatrixMap ρ.toRingHom (MvPolynomial.map (algebraMap K E) p) =
      p • (1 : Matrix n n (MvPolynomial σ K)) := by
  have hh : (polynomialMatrixMap ρ.toRingHom).comp
      (MvPolynomial.map (algebraMap K E)) =
      algebraMap (MvPolynomial σ K) (Matrix n n (MvPolynomial σ K)) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp only [RingHom.comp_apply, MvPolynomial.map_C, polynomialMatrixMap_C]
      change (ρ (algebraMap K E a)).map MvPolynomial.C = _
      rw [ρ.commutes]
      ext i j
      by_cases hij : i = j
      · subst j
        simp [Matrix.algebraMap_eq_diagonal, Matrix.map_apply]
      · simp [Matrix.algebraMap_eq_diagonal, Matrix.map_apply, hij]
    · intro i
      simp [Algebra.algebraMap_eq_smul_one]
  simpa only [RingHom.comp_apply, Algebra.algebraMap_eq_smul_one] using
    RingHom.congr_fun hh p

 theorem polynomialMatrixMap_divergence [Fintype σ]
    (ρ : E →+* Matrix n n K) (u : σ → MvPolynomial σ E)
    (h : ∑ i, MvPolynomial.pderiv i (u i) = 0) :
    (∑ i, matrixDeriv (MvPolynomial.pderiv i) (polynomialMatrixMap ρ (u i))) = 0 := by
  have hh := congrArg (polynomialMatrixMap ρ) h
  simpa only [map_sum, map_zero, polynomialMatrixMap_deriv] using hh

 theorem polynomialMatrixMap_tangency [Fintype σ]
    (ρ : E →+* Matrix n n K) (u : σ → MvPolynomial σ E) (l : MvPolynomial σ E)
    (h : ∑ i, u i * MvPolynomial.pderiv i l = 0) :
    (∑ i, polynomialMatrixMap ρ (u i) *
      matrixDeriv (MvPolynomial.pderiv i) (polynomialMatrixMap ρ l)) = 0 := by
  have hh := congrArg (polynomialMatrixMap ρ) h
  simpa only [map_sum, map_mul, map_zero, polynomialMatrixMap_deriv] using hh

 theorem polynomialMatrixMap_source [Fintype σ] [Algebra K E]
    (ρ : E →ₐ[K] Matrix n n K) (u : σ → MvPolynomial σ E)
    (l j : MvPolynomial σ E) (G : MvPolynomial σ K)
    (h : ∑ i, u i * MvPolynomial.pderiv i (MvPolynomial.map (algebraMap K E) G) = j * l) :
    (∑ i, MvPolynomial.pderiv i G • polynomialMatrixMap ρ.toRingHom (u i)) =
      polynomialMatrixMap ρ.toRingHom j * polynomialMatrixMap ρ.toRingHom l := by
  have hh := congrArg (polynomialMatrixMap ρ.toRingHom) h
  simpa only [MvPolynomial.pderiv_map, map_sum, map_mul, polynomialMatrixMap_base,
    Matrix.mul_smul, Matrix.mul_one] using hh

 theorem polynomialMatrixMap_monomial [Algebra K E]
    (ρ : E →ₐ[K] Matrix n n K) (s : σ →₀ ℕ) (a : E) (i j : n) :
    polynomialMatrixMap ρ.toRingHom (MvPolynomial.monomial s a) i j =
      MvPolynomial.monomial s (ρ a i j) := by
  have hm : MvPolynomial.monomial s a =
      MvPolynomial.C a * MvPolynomial.map (algebraMap K E)
        (MvPolynomial.monomial s (1 : K)) := by
    simp [MvPolynomial.C_mul_monomial]
  rw [hm, map_mul, polynomialMatrixMap_C, polynomialMatrixMap_base,
    Matrix.mul_smul, Matrix.mul_one]
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.map_apply]
  rw [mul_comm, MvPolynomial.C_mul_monomial, mul_one]
  rfl

 theorem polynomialMatrixMap_homogeneous [Algebra K E]
    (ρ : E →ₐ[K] Matrix n n K) (p : MvPolynomial σ E) (d : ℕ)
    (hp : p.IsHomogeneous d) (i j : n) :
    (polynomialMatrixMap ρ.toRingHom p i j).IsHomogeneous d := by
  classical
  have heq : polynomialMatrixMap ρ.toRingHom p i j =
      ∑ s ∈ p.support, MvPolynomial.monomial s (ρ (p.coeff s) i j) := by
    conv_lhs => rw [p.as_sum, map_sum]
    rw [Matrix.sum_apply]
    apply Finset.sum_congr rfl
    intro s hs
    exact polynomialMatrixMap_monomial ρ s (p.coeff s) i j
  rw [heq]
  apply MvPolynomial.IsHomogeneous.sum
  intro s hs
  apply MvPolynomial.isHomogeneous_monomial
  simpa only [Finsupp.degree_apply] using (hp.degree_eq_sum_deg_support hs).symm

end QuadricContact
#print axioms QuadricContact.polynomialMatrixMap_deriv

#print axioms QuadricContact.polynomialMatrixMap_source

#print axioms QuadricContact.polynomialMatrixMap_homogeneous

