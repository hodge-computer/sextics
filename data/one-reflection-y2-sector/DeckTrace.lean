/- Adapted for the instance `one-reflection-y2-sector` from the accepted holdout proof by `fqlx` (prepared with OpenAI ChatGPT assistance); the target-specific source, companion and trace data are replaced, all other modules are unchanged. Adaptation prepared with Claude Code assistance for `DiamondJM`. -/
import Mathlib.FieldTheory.NormalizedTrace
import Mathlib.Tactic

/- Source component: DeckTrace -/
section
/-!
Removing the nontrivial fourth inverse-power character in the holdout
finite-cover source. The deck homomorphism is an explicit hypothesis here;
its construction on the common cover is a separate obligation.
Prepared with OpenAI ChatGPT assistance for a contribution through GitHub
account fqlx. Normalized trace and its functoriality are due to the credited
Lean/mathlib authors.
-/

noncomputable section

namespace HoldoutConstruction

variable {K L : Type*} [Field K] [Field L] [CharZero K]
variable [Algebra K L] [FiniteDimensional K L]

/-- A nontrivial eigencharacter of any base-preserving self-embedding has
zero normalized trace. -/
theorem normalizedTrace_eigen_zero (σ : L →ₐ[K] L) (c : K) (hc : c ≠ 1)
    (x : L) (eigen : σ x = algebraMap K L c * x) :
    Algebra.normalizedTrace K L x = 0 := by
  have hσ := Algebra.normalizedTrace_map K L σ x
  have hlinear : Algebra.normalizedTrace K L (algebraMap K L c * x) =
      c * Algebra.normalizedTrace K L x := by
    calc
      _ = Algebra.normalizedTrace K L (c • x) := by rw [Algebra.smul_def]
      _ = c • Algebra.normalizedTrace K L x := map_smul _ _ _
      _ = c * Algebra.normalizedTrace K L x := rfl
  rw [eigen, hlinear] at hσ
  have hzero : (c - 1) * Algebra.normalizedTrace K L x = 0 := by
    linear_combination hσ
  exact (mul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr hc)

/-- A deck homomorphism scaling T by a scalar with nontrivial fourth power
kills T^(-4) under normalized trace. No exact extension-rank hypothesis is
needed beyond finiteness. -/
theorem normalizedTrace_inv_fourth_zero
    (σ : L →ₐ[K] L) (zeta : K) (hzeta : zeta^4 ≠ 1)
    (T : L) (scale : σ T = algebraMap K L zeta * T) :
    Algebra.normalizedTrace K L ((T^4)⁻¹) = 0 := by
  apply normalizedTrace_eigen_zero σ ((zeta^4)⁻¹)
  · intro h
    apply hzeta
    have hi := congrArg (fun x : K => x⁻¹) h
    simpa only [inv_inv, inv_one] using hi
  · simp only [map_inv₀, map_pow, scale, mul_pow, mul_inv_rev]
    ring

/-- The original source and its distinguished normal derivative both have
this form. The nontrivial deck term disappears exactly. -/
theorem normalizedTrace_deck_correction
    (σ : L →ₐ[K] L) (zeta : K) (hzeta : zeta^4 ≠ 1)
    (T : L) (scale : σ T = algebraMap K L zeta * T) (A c : K) :
    Algebra.normalizedTrace K L
      (algebraMap K L A * (1 - algebraMap K L c * (T^4)⁻¹)) = A := by
  have hT := normalizedTrace_inv_fourth_zero σ zeta hzeta T scale
  have hlin : Algebra.normalizedTrace K L
      (algebraMap K L A * algebraMap K L c * (T^4)⁻¹) = 0 := by
    have heq : algebraMap K L A * algebraMap K L c * (T^4)⁻¹ =
        (A * c) • (T^4)⁻¹ := by
      simp only [Algebra.smul_def, map_mul]
    rw [heq, map_smul, hT, smul_zero]
  rw [mul_sub, mul_one, ← mul_assoc, map_sub, Algebra.normalizedTrace_algebraMap_apply_eq_self,
    hlin, sub_zero]

/-- A deck homomorphism scaling T by a scalar whose n-th power is nontrivial
kills T^(-n) under normalized trace. -/
theorem normalizedTrace_inv_pow_zero
    (σ : L →ₐ[K] L) (zeta : K) (n : ℕ) (hzeta : zeta^n ≠ 1)
    (T : L) (scale : σ T = algebraMap K L zeta * T) :
    Algebra.normalizedTrace K L ((T^n)⁻¹) = 0 := by
  apply normalizedTrace_eigen_zero σ ((zeta^n)⁻¹)
  · intro h
    apply hzeta
    have hi := congrArg (fun x : K => x⁻¹) h
    simpa only [inv_inv, inv_one] using hi
  · simp only [map_inv₀, map_pow, scale, mul_pow, mul_inv_rev]
    ring

/-- The same deck homomorphism kills the positive power T^n. -/
theorem normalizedTrace_pow_zero
    (σ : L →ₐ[K] L) (zeta : K) (n : ℕ) (hzeta : zeta^n ≠ 1)
    (T : L) (scale : σ T = algebraMap K L zeta * T) :
    Algebra.normalizedTrace K L (T^n) = 0 := by
  apply normalizedTrace_eigen_zero σ (zeta^n) hzeta
  simp only [map_pow, scale, mul_pow]

/-- A source of the form r - c*E with trace-free E has normalized trace r. -/
theorem normalizedTrace_deck_difference
    (E : L) (hE : Algebra.normalizedTrace K L E = 0) (r c : K) :
    Algebra.normalizedTrace K L (algebraMap K L r - algebraMap K L c * E) = r := by
  have hlin : Algebra.normalizedTrace K L (algebraMap K L c * E) = 0 := by
    have heq : algebraMap K L c * E = c • E := by
      simp only [Algebra.smul_def]
    rw [heq, map_smul, hE, smul_zero]
  rw [map_sub, Algebra.normalizedTrace_algebraMap_apply_eq_self, hlin, sub_zero]

end HoldoutConstruction

#print axioms HoldoutConstruction.normalizedTrace_eigen_zero
#print axioms HoldoutConstruction.normalizedTrace_inv_fourth_zero
#print axioms HoldoutConstruction.normalizedTrace_deck_correction
end
end
