import Proposal.ContactPolynomialBounds

/-!
# Finite certificates for an actual sparse polynomial zero

All hypotheses of `exists_zero_of_certificate` are finite coefficient or matrix
bounds.  The conclusion is an actual complex zero, proved using the complete
closed-ball contraction theorem.
-/

noncomputable section

namespace ContactPolynomialBounds

open Metric Set
open scoped BigOperators Matrix

set_option backward.isDefEq.respectTransparency false

def matrixCLM {n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ) : Space n →L[ℂ] Space n :=
  (Matrix.toLin' B).toContinuousLinearMap

@[simp] theorem matrixCLM_apply {n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ) (v : Space n) :
    matrixCLM B v = B *ᵥ v := Matrix.toLin'_apply B v

theorem matrixCLM_eq_of_entries {n : ℕ} (J : Matrix (Fin n) (Fin n) ℂ)
    (A : Space n →L[ℂ] Space n)
    (hJ : ∀ i j, J i j = A (Pi.single j 1) i) : matrixCLM J = A := by
  have hm : J = LinearMap.toMatrix' A.toLinearMap := by
    ext i j
    exact hJ i j
  subst J
  apply ContinuousLinearMap.ext
  intro v
  change Matrix.toLin' (LinearMap.toMatrix' A.toLinearMap) v = A v
  rw [Matrix.toLin'_toMatrix']
  rfl

theorem matrixCLM_systemDeriv {n : ℕ} (p : Fin n → Polynomial n) (c : Space n)
    (J : Matrix (Fin n) (Fin n) ℂ)
    (hJ : ∀ i j, J i j = polyDeriv (p i) c (Pi.single j 1)) :
    matrixCLM J = systemDeriv p c :=
  matrixCLM_eq_of_entries J (systemDeriv p c) hJ

theorem matrixCLM_norm_le {n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ) {b : ℝ}
    (hb : 0 ≤ b) (hB : ∀ i, ∑ j, complexMass (B i j) ≤ b) :
    ‖matrixCLM B‖ ≤ b := by
  apply ContinuousLinearMap.opNorm_le_bound _ hb
  intro v
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hb (norm_nonneg _))).mpr
  intro i
  change ‖∑ j, B i j * v j‖ ≤ b * ‖v‖
  calc
    _ ≤ ∑ j, ‖B i j * v j‖ := norm_sum_le _ _
    _ ≤ ∑ j, complexMass (B i j) * ‖v‖ := by
      apply Finset.sum_le_sum
      intro j _
      rw [norm_mul]
      exact mul_le_mul (norm_le_complexMass _) (norm_le_pi_norm v j)
        (norm_nonneg _) (complexMass_nonneg _)
    _ = (∑ j, complexMass (B i j)) * ‖v‖ := (Finset.sum_mul ..).symm
    _ ≤ b * ‖v‖ := mul_le_mul_of_nonneg_right (hB i) (norm_nonneg _)

theorem matrixCLM_defect {n : ℕ} (B J : Matrix (Fin n) (Fin n) ℂ) :
    matrixCLM (1 - B * J) =
      ContinuousLinearMap.id ℂ (Space n) - (matrixCLM B).comp (matrixCLM J) := by
  ext v i
  simp [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_mulVec]

theorem matrix_defect_norm_le {n : ℕ} (B J : Matrix (Fin n) (Fin n) ℂ)
    {d : ℝ} (hd : 0 ≤ d)
    (hdefect : ∀ i, ∑ j, complexMass ((1 - B * J) i j) ≤ d) :
    ‖ContinuousLinearMap.id ℂ (Space n) - (matrixCLM B).comp (matrixCLM J)‖ ≤ d := by
  rw [← matrixCLM_defect]
  exact matrixCLM_norm_le _ hd hdefect

theorem norm_le_of_complexMass_le {n : ℕ} (v : Space n) {b : ℝ}
    (hb : 0 ≤ b) (hv : ∀ i, complexMass (v i) ≤ b) : ‖v‖ ≤ b :=
  (pi_norm_le_iff_of_nonneg hb).mpr (fun i => (norm_le_complexMass _).trans (hv i))

theorem norm_le_of_mem_closedBall {n : ℕ} (c x : Space n) {r M : ℝ}
    (hM : 0 ≤ M) (hc : ∀ i, complexMass (c i) + r ≤ M)
    (hx : x ∈ closedBall c r) : ‖x‖ ≤ M := by
  apply (pi_norm_le_iff_of_nonneg hM).mpr
  intro i
  have hxc : ‖x - c‖ ≤ r := by simpa [dist_eq_norm] using hx
  calc
    ‖x i‖ ≤ ‖x i - c i‖ + ‖c i‖ := norm_le_norm_sub_add _ _
    _ ≤ r + complexMass (c i) := add_le_add
      ((norm_le_pi_norm (x - c) i).trans hxc) (norm_le_complexMass _)
    _ ≤ M := by simpa [add_comm] using hc i

/-- Exact finite bounds control the Newton derivative throughout the closed ball. -/
theorem newton_derivative_bound {n : ℕ}
    (p : Fin n → Polynomial n) (c : Space n) (B J : Matrix (Fin n) (Fin n) ℂ)
    (r M H b d : ℝ)
    (hr : 0 < r) (hM : 0 ≤ M) (hH : 0 ≤ H) (hb : 0 ≤ b) (hd : 0 ≤ d)
    (hcoordinates : ∀ i, complexMass (c i) + r ≤ M)
    (hhessian : ∀ i, hessianMass (p i) M ≤ H)
    (hB : ∀ i, ∑ j, complexMass (B i j) ≤ b)
    (hJ : ∀ i j, J i j = polyDeriv (p i) c (Pi.single j 1))
    (hdefect : ∀ i, ∑ j, complexMass ((1 - B * J) i j) ≤ d)
    (hsmall : d + b * H * r ≤ (1 / 2 : ℝ)) :
    ∀ x ∈ closedBall c r,
      ‖ContinuousLinearMap.id ℂ (Space n) - (matrixCLM B).comp (systemDeriv p x)‖ ≤
        (1 / 2 : ℝ) := by
  have hc : c ∈ closedBall c r := mem_closedBall_self hr.le
  have hcM : ‖c‖ ≤ M := norm_le_of_mem_closedBall c c hM hcoordinates hc
  have hBM : ‖matrixCLM B‖ ≤ b := matrixCLM_norm_le B hb hB
  have hJM : matrixCLM J = systemDeriv p c := matrixCLM_systemDeriv p c J hJ
  have hcenterDefect :
      ‖ContinuousLinearMap.id ℂ (Space n) - (matrixCLM B).comp (systemDeriv p c)‖ ≤ d := by
    rw [← hJM]
    exact matrix_defect_norm_le B J hd hdefect
  have hlocal : ∀ x ∈ closedBall c r,
      ‖ContinuousLinearMap.id ℂ (Space n) - (matrixCLM B).comp (systemDeriv p x)‖ ≤
        (1 / 2 : ℝ) := by
    intro x hx
    have hxM : ‖x‖ ≤ M := norm_le_of_mem_closedBall c x hM hcoordinates hx
    have hdelta : ‖systemDeriv p c - systemDeriv p x‖ ≤ H * r := by
      apply (systemDeriv_lipschitz p c x hM hH hhessian hcM hxM).trans
      apply mul_le_mul_of_nonneg_left _ hH
      simpa [dist_eq_norm, norm_sub_rev] using hx
    have heq : ContinuousLinearMap.id ℂ (Space n) - (matrixCLM B).comp (systemDeriv p x) =
        (ContinuousLinearMap.id ℂ (Space n) - (matrixCLM B).comp (systemDeriv p c)) +
        (matrixCLM B).comp (systemDeriv p c - systemDeriv p x) := by
      ext v i
      simp only [sub_apply, add_apply, ContinuousLinearMap.comp_apply, map_sub,
        Pi.sub_apply, Pi.add_apply]
      abel
    rw [heq]
    calc
      _ ≤ ‖ContinuousLinearMap.id ℂ (Space n) - (matrixCLM B).comp (systemDeriv p c)‖ +
          ‖(matrixCLM B).comp (systemDeriv p c - systemDeriv p x)‖ := norm_add_le _ _
      _ ≤ d + b * (H * r) := by
        apply add_le_add hcenterDefect
        exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul hBM hdelta (norm_nonneg _) hb)
      _ ≤ (1 / 2 : ℝ) := by simpa [mul_assoc] using hsmall
  exact hlocal

/-- The fully analytic consequence of finite rational checks for a square sparse
system.  `J` must be the derivative of the actual equations at the actual center;
its entries are checked on the coordinate vectors. -/
theorem exists_zero_of_certificate {n : ℕ}
    (p : Fin n → Polynomial n) (c : Space n) (B J : Matrix (Fin n) (Fin n) ℂ)
    (r M H b d : ℝ)
    (hr : 0 < r) (hM : 0 ≤ M) (hH : 0 ≤ H) (hb : 0 ≤ b) (hd : 0 ≤ d)
    (hcoordinates : ∀ i, complexMass (c i) + r ≤ M)
    (hhessian : ∀ i, hessianMass (p i) M ≤ H)
    (hB : ∀ i, ∑ j, complexMass (B i j) ≤ b)
    (hJ : ∀ i j, J i j = polyDeriv (p i) c (Pi.single j 1))
    (hdefect : ∀ i, ∑ j, complexMass ((1 - B * J) i j) ≤ d)
    (hresidual : ∀ i, complexMass ((B *ᵥ system p c) i) ≤ r / 2)
    (hsmall : d + b * H * r ≤ (1 / 2 : ℝ)) :
    ∃ x ∈ closedBall c r, system p x = 0 := by
  have hc : c ∈ closedBall c r := mem_closedBall_self hr.le
  have hlocal := newton_derivative_bound p c B J r M H b d hr hM hH hb hd
    hcoordinates hhessian hB hJ hdefect hsmall
  apply ContactBanachExistence.exists_zero_in_closedBall (system p)
    (matrixCLM B).toLinearMap (systemDeriv p c).toLinearMap c r hr
  · exact norm_le_of_complexMass_le _ (by positivity) hresidual
  · exact ContactBanachExistence.newton_half_lipschitz_of_derivative (system p) (matrixCLM B)
      (systemDeriv p) c r (fun x _ => system_hasFDerivAt p x) hlocal
  · intro v
    exact (ContinuousLinearMap.id ℂ (Space n) - (matrixCLM B).comp (systemDeriv p c)).le_of_opNorm_le
      (hlocal c hc) v


/-- A square derivative with a Newton defect at most one half is bijective. -/
theorem bijective_of_newton_half_defect {n : ℕ}
    (B A : Space n →L[ℂ] Space n)
    (hdefect : ‖ContinuousLinearMap.id ℂ (Space n) - B.comp A‖ ≤ (1 / 2 : ℝ)) :
    Function.Bijective A := by
  have hinj : Function.Injective A := by
    intro u v huv
    have h := (ContinuousLinearMap.id ℂ (Space n) - B.comp A).le_of_opNorm_le hdefect (u - v)
    have hzero : A (u - v) = 0 := by simp only [map_sub, huv, sub_self]
    simp only [sub_apply, ContinuousLinearMap.id_apply, ContinuousLinearMap.comp_apply,
      hzero, map_zero, sub_zero] at h
    have hn : ‖u - v‖ = 0 := by
      have := norm_nonneg (u - v)
      linarith
    exact sub_eq_zero.mp (norm_eq_zero.mp hn)
  exact ⟨hinj, (LinearMap.injective_iff_surjective (f := A.toLinearMap)).mp hinj⟩

/-- The actual polynomial Jacobian is invertible everywhere in the certified ball. -/
theorem jacobian_bijective_of_certificate_at {n : ℕ}
    (p : Fin n → Polynomial n) (c : Space n) (B J : Matrix (Fin n) (Fin n) ℂ)
    (r M H b d : ℝ)
    (hr : 0 < r) (hM : 0 ≤ M) (hH : 0 ≤ H) (hb : 0 ≤ b) (hd : 0 ≤ d)
    (hcoordinates : ∀ i, complexMass (c i) + r ≤ M)
    (hhessian : ∀ i, hessianMass (p i) M ≤ H)
    (hB : ∀ i, ∑ j, complexMass (B i j) ≤ b)
    (hJ : ∀ i j, J i j = polyDeriv (p i) c (Pi.single j 1))
    (hdefect : ∀ i, ∑ j, complexMass ((1 - B * J) i j) ≤ d)
    (hsmall : d + b * H * r ≤ (1 / 2 : ℝ)) :
    ∀ x ∈ closedBall c r, Function.Bijective (systemDeriv p x) := by
  intro x hx
  exact bijective_of_newton_half_defect (matrixCLM B) (systemDeriv p x)
    (newton_derivative_bound p c B J r M H b d hr hM hH hb hd
      hcoordinates hhessian hB hJ hdefect hsmall x hx)

/-- A certificate gives an actual zero and an invertible Jacobian at that zero. -/
theorem exists_regular_zero_of_certificate {n : ℕ}
    (p : Fin n → Polynomial n) (c : Space n) (B J : Matrix (Fin n) (Fin n) ℂ)
    (r M H b d : ℝ)
    (hr : 0 < r) (hM : 0 ≤ M) (hH : 0 ≤ H) (hb : 0 ≤ b) (hd : 0 ≤ d)
    (hcoordinates : ∀ i, complexMass (c i) + r ≤ M)
    (hhessian : ∀ i, hessianMass (p i) M ≤ H)
    (hB : ∀ i, ∑ j, complexMass (B i j) ≤ b)
    (hJ : ∀ i j, J i j = polyDeriv (p i) c (Pi.single j 1))
    (hdefect : ∀ i, ∑ j, complexMass ((1 - B * J) i j) ≤ d)
    (hresidual : ∀ i, complexMass ((B *ᵥ system p c) i) ≤ r / 2)
    (hsmall : d + b * H * r ≤ (1 / 2 : ℝ)) :
    ∃ x ∈ closedBall c r, system p x = 0 ∧ Function.Bijective (systemDeriv p x) := by
  obtain ⟨x, hx, hzero⟩ := exists_zero_of_certificate p c B J r M H b d hr hM hH hb hd
    hcoordinates hhessian hB hJ hdefect hresidual hsmall
  exact ⟨x, hx, hzero, jacobian_bijective_of_certificate_at p c B J r M H b d hr hM hH hb hd
    hcoordinates hhessian hB hJ hdefect hsmall x hx⟩

end ContactPolynomialBounds
