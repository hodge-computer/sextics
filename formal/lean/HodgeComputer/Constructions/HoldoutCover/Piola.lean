import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/- Source component: RationalPiola -/
section
/-!
Algebraic divergence under a change of coordinates.

These generic identities are intermediate construction lemmas. They do not
assume or assert a certificate for the holdout instance.
-/

noncomputable section

namespace HoldoutConstruction

open scoped BigOperators

section Products

variable {R : Type*} [CommRing R] {ι : Type*} [DecidableEq ι]

theorem derivation_prod_update (D : Derivation ℤ R R) (s : Finset ι) (f : ι → R) :
    D (∏ i ∈ s, f i) = ∑ i ∈ s, ∏ j ∈ s, Function.update f i (D (f i)) j := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, D.leibniz, ih, Finset.sum_insert ha]
    simp only [smul_eq_mul, Finset.mul_sum]
    have hfirst : (∏ j ∈ insert a s, Function.update f a (D (f a)) j) =
        D (f a) * ∏ j ∈ s, f j := by
      rw [Finset.prod_insert ha, Function.update_self,
        Finset.prod_update_of_notMem ha]
    rw [hfirst, add_comm]
    congr 1
    · exact mul_comm _ _
    apply Finset.sum_congr rfl
    intro i hi
    have hai : a ≠ i := by intro h; exact ha (h ▸ hi)
    rw [Finset.prod_insert ha, Function.update_of_ne hai]

end Products

section Determinants

variable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem derivation_det_columns (D : Derivation ℤ R R) (M : Matrix ι ι R) :
    D M.det = ∑ i, (M.updateCol i (fun j => D (M j i))).det := by
  classical
  simp only [Matrix.det_apply', map_sum, D.leibniz, D.map_intCast,
    smul_eq_mul, mul_zero, add_zero, derivation_prod_update, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro σ _
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  by_cases h : j = i
  · subst j; simp
  · simp [Matrix.updateCol, h]

theorem derivation_det_inverse (D : Derivation ℤ R R) (M N : Matrix ι ι R)
    (hMN : M*N = 1) :
    D M.det = M.det * ∑ i, ∑ j, N i j * D (M j i) := by
  rw [derivation_det_columns, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hcol : (fun j => D (M j i)) =
      fun j => ∑ k, (∑ l, N k l * D (M l i)) * M j k := by
    have hh := congrArg (fun v : ι → R => v)
      (Matrix.mulVec_mulVec (fun j => D (M j i)) M N)
    rw [hMN, Matrix.one_mulVec] at hh
    ext j
    have hj := congrFun hh j
    simpa only [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_comm] using hj.symm
  rw [hcol]
  simpa only [smul_eq_mul, mul_comm] using
    (Matrix.det_updateCol_sum M i (fun k => ∑ l, N k l * D (M l i)))

end Determinants

section Divergence

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι]

def fieldDivergence (D : ι → Derivation ℤ K K) (v : ι → K) : K :=
  ∑ i, D i (v i)

omit [DecidableEq ι] in
theorem fieldDivergence_smul (D : ι → Derivation ℤ K K) (a : K) (v : ι → K) :
    fieldDivergence D (fun i => a*v i) =
      (∑ i, v i * D i a) + a*fieldDivergence D v := by
  simp only [fieldDivergence, Derivation.leibniz, smul_eq_mul,
    Finset.sum_add_distrib, Finset.mul_sum]
  ring

omit [DecidableEq ι] in
theorem fieldDivergence_sum {κ : Type*} [Fintype κ]
    (D : ι → Derivation ℤ K K) (v : κ → ι → K) :
    fieldDivergence D (fun i => ∑ k, v k i) = ∑ k, fieldDivergence D (v k) := by
  simp only [fieldDivergence, map_sum]
  rw [Finset.sum_comm]

theorem column_directional
    (D E : ι → Derivation ℤ K K) (M N : Matrix ι ι K)
    (hNM : N*M = 1)
    (chain : ∀ j x, E j x = ∑ k, N k j * D k x) (i : ι) (x : K) :
    ∑ j, M j i * E j x = D i x := by
  simp_rw [chain, Finset.mul_sum]
  rw [Finset.sum_comm]
  have hinner : ∀ k, (∑ j, M j i * (N k j * D k x)) =
      (N*M) k i * D k x := by
    intro k
    simp only [Matrix.mul_apply, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp_rw [hinner, hNM]
  simp [Matrix.one_apply]

theorem column_divergence
    (D E : ι → Derivation ℤ K K) (M N : Matrix ι ι K)
    (hMN : M*N = 1) (hdet : M.det ≠ 0)
    (chain : ∀ j x, E j x = ∑ k, N k j * D k x)
    (mixed : ∀ i j k, D k (M j i) = D i (M j k)) (i : ι) :
    fieldDivergence E (fun j => M j i) = D i M.det / M.det := by
  rw [derivation_det_inverse (D i) M N hMN]
  unfold fieldDivergence
  simp_rw [chain, mixed]
  rw [Finset.sum_comm]
  field_simp

theorem piola_divergence
    (D E : ι → Derivation ℤ K K) (M N : Matrix ι ι K)
    (hMN : M*N = 1) (hNM : N*M = 1) (hdet : M.det ≠ 0)
    (chain : ∀ j x, E j x = ∑ k, N k j * D k x)
    (mixed : ∀ i j k, D k (M j i) = D i (M j k)) (w : ι → K) :
    fieldDivergence E (fun j => ∑ i, (w i/M.det)*M j i) =
      fieldDivergence D w / M.det := by
  rw [fieldDivergence_sum]
  simp_rw [fieldDivergence_smul,
    column_directional D E M N hNM chain,
    column_divergence D E M N hMN hdet chain mixed]
  unfold fieldDivergence
  conv_rhs => rw [div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  simp only [div_eq_mul_inv, Derivation.leibniz, Derivation.leibniz_inv, smul_eq_mul]
  field_simp
  ring

end Divergence

end HoldoutConstruction

#print axioms HoldoutConstruction.derivation_det_inverse
#print axioms HoldoutConstruction.piola_divergence
end
end

/- Source component: WeightedPiola -/
section
/-!
The algebraic change-of-coordinates formula for a residue volume, followed
by integration of polynomial densities along one rational parameter.

These are intermediate construction lemmas, not a holdout certificate.
-/

noncomputable section

namespace HoldoutConstruction

open scoped BigOperators

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι]

def residueDivergence (E : ι → Derivation ℤ K K) (g : K) (v : ι → K) : K :=
  fieldDivergence E v - (∑ j, v j * E j g) / g

theorem residueDivergence_add (E : ι → Derivation ℤ K K) (g : K) (v w : ι → K) :
    residueDivergence E g (v+w) = residueDivergence E g v + residueDivergence E g w := by
  simp only [residueDivergence, fieldDivergence, Pi.add_apply, map_add,
    add_mul, Finset.sum_add_distrib]
  ring

theorem residueDivergence_sub (E : ι → Derivation ℤ K K) (g : K) (v w : ι → K) :
    residueDivergence E g (v-w) = residueDivergence E g v - residueDivergence E g w := by
  simp only [residueDivergence, fieldDivergence, Pi.sub_apply, map_sub,
    sub_mul, Finset.sum_sub_distrib]
  ring

theorem residueDivergence_smul (E : ι → Derivation ℤ K K) (g s : K) (w : ι → K) :
    residueDivergence E g (fun i => s*w i) =
      s*residueDivergence E g w + ∑ i, w i * E i s := by
  simp only [residueDivergence, fieldDivergence, Derivation.leibniz, smul_eq_mul,
    Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
  ring

theorem residueDivergence_cancel_density (E : ι → Derivation ℤ K K)
    (g : K) (hg : g ≠ 0) (v : ι → K) :
    residueDivergence E g (fun j => g*v j) = g*fieldDivergence E v := by
  rw [residueDivergence, fieldDivergence_smul]
  simp only [mul_assoc, ← Finset.mul_sum]
  field_simp
  ring

variable [DecidableEq ι]

/-- The determinant of the coordinate matrix is `g*J`, where `J` is the
coefficient of the pulled-back residue volume. -/
theorem residue_piola
    (D E : ι → Derivation ℤ K K) (M N : Matrix ι ι K)
    (g J : K) (hg : g ≠ 0) (hJ : J ≠ 0)
    (hdet : M.det = g*J) (hMN : M*N = 1) (hNM : N*M = 1)
    (chain : ∀ j x, E j x = ∑ k, N k j * D k x)
    (mixed : ∀ i j k, D k (M j i) = D i (M j k)) (u : ι → K) :
    residueDivergence E g (fun j => ∑ i, (u i/J)*M j i) =
      fieldDivergence D u / J := by
  have hd : M.det ≠ 0 := hdet ▸ mul_ne_zero hg hJ
  have heq : (fun j => ∑ i, (u i/J)*M j i) =
      fun j => g*(∑ i, (u i/M.det)*M j i) := by
    funext j
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [hdet]
    field_simp
  rw [heq, residueDivergence_cancel_density E g hg,
    piola_divergence D E M N hMN hNM hd chain mixed, hdet]
  field_simp

/-- An antiderivative in the curve parameter cancels an arbitrary prescribed
residue divergence when its pulled-back density is polynomial. -/
theorem residue_solution_of_antiderivative
    (D E : ι → Derivation ℤ K K) (M N : Matrix ι ι K)
    (g J : K) (hg : g ≠ 0) (hJ : J ≠ 0)
    (hdet : M.det = g*J) (hMN : M*N = 1) (hNM : N*M = 1)
    (chain : ∀ j x, E j x = ∑ k, N k j * D k x)
    (mixed : ∀ i j k, D k (M j i) = D i (M j k))
    (v : ι → K) (r p h : K) (t : ι)
    (hp : p = J*(r+residueDivergence E g v)) (hh : D t h = p) :
    ∃ w : ι → K, residueDivergence E g w = -r := by
  let u : ι → K := Pi.single t (-h)
  have hu : fieldDivergence D u = -p := by
    simp [fieldDivergence, u, Pi.single_apply, apply_ite, hh]
  let z : ι → K := fun j => ∑ i, (u i/J)*M j i
  refine ⟨v+z, ?_⟩
  rw [residueDivergence_add]
  have hz := residue_piola D E M N g J hg hJ hdet hMN hNM chain mixed u
  change residueDivergence E g z = _ at hz
  rw [hz, hu, hp]
  field_simp
  ring

section PolynomialIntegration

variable {R : Type*} [CommRing R] [CharZero K]

/-- The integral is finite. Only coefficients in the kernel of `T` are
integrated, and `T t = 1`; no integration of arbitrary rational functions
is asserted. -/
theorem exists_polynomial_antiderivative (T : Derivation ℤ K K)
    (φ : R →+* K) (hφ : ∀ a, T (φ a) = 0) (t : K) (ht : T t = 1)
    (P : Polynomial R) : ∃ h : K, T h = P.eval₂ φ t := by
  refine ⟨∑ n ∈ P.support, φ (P.coeff n) / (n+1:K) * t^(n+1), ?_⟩
  rw [map_sum, Polynomial.eval₂_eq_sum]
  apply Finset.sum_congr rfl
  intro n _
  have hn : (n+1:K) ≠ 0 := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n) : ((n+1:ℕ):K) ≠ 0)
  have hc : T (φ (P.coeff n)/(n+1:K)) = 0 := by
    rw [Derivation.leibniz_div]
    simp [hφ]
  rw [Derivation.leibniz, hc, Derivation.leibniz_pow]
  simp only [ht, smul_eq_mul, mul_zero, add_zero,
    Nat.add_sub_cancel, nsmul_eq_mul, Nat.cast_add, Nat.cast_one, mul_one]
  field_simp

end PolynomialIntegration

end HoldoutConstruction

#print axioms HoldoutConstruction.residue_piola
#print axioms HoldoutConstruction.residue_solution_of_antiderivative
#print axioms HoldoutConstruction.exists_polynomial_antiderivative
end
end
