import HodgeComputer.Constructions.ResidueTransport.PiolaContraction

/- Source component: ResiduePiolaPullback -/
section
/-!
Inverse residue Piola transport when the two coordinate systems use the
same distinguished normal derivative. This is the situation of the holdout
finite cover: X0 is fixed and the other coordinate functions are independent
of X0. Prepared with OpenAI ChatGPT assistance for a contribution through
GitHub account fqlx, building on the checked generic Piola identities from
this collaboration.
-/

noncomputable section

namespace HoldoutConstruction

open scoped BigOperators

section Maps

variable {R K ι : Type*} [Field R] [Field K] [Fintype ι]

/-- Residue divergence is compatible with any field embedding that
intertwines the specified derivations. No finite-extension hypothesis is
needed for this direction of transport. -/
theorem residueDivergence_map (φ : R →+* K)
    (D : ι → Derivation ℤ R R) (E : ι → Derivation ℤ K K)
    (compatible : ∀ i x, E i (φ x) = φ (D i x)) (g : R) (w : ι → R) :
    residueDivergence E (φ g) (fun i => φ (w i)) =
      φ (residueDivergence D g w) := by
  simp only [residueDivergence, fieldDivergence, compatible, map_sub,
    map_sum, map_div₀, map_mul]

end Maps

section PassiveCoordinate

variable {K : Type*} [Field K] {n : ℕ}

/-- Appending a zero component creates no derivative in the new passive
coordinate, even when the other components depend on that coordinate. -/
theorem residueDivergence_append_zero
    (E : Fin (n+1) → Derivation ℤ K K) (g : K) (w : Fin n → K) :
    residueDivergence E g (Fin.lastCases 0 w) =
      residueDivergence (fun i => E i.castSucc) g w := by
  simp [residueDivergence, fieldDivergence, Fin.sum_univ_castSucc]

end PassiveCoordinate

variable {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]

/-- `D` are the original coordinate derivations, `E` the new ones, and
`M` is the Jacobian of the new coordinates with respect to the original
coordinates. A residue vector pulls back as `det(M) * M⁻¹ * w`. -/
theorem residue_piola_pullback
    (D E : ι → Derivation ℤ K K) (M N : Matrix ι ι K)
    (hMN : M*N = 1) (hNM : N*M = 1) (hdet : M.det ≠ 0)
    (chain : ∀ j x, E j x = ∑ k, N k j * D k x)
    (mixed : ∀ i j k, D k (M j i) = D i (M j k))
    (g : K) (w : ι → K) :
    residueDivergence D g (fun i => M.det * (N.mulVec w) i) =
      M.det * residueDivergence E g w := by
  let v : ι → K := fun i => M.det * (N.mulVec w) i
  have hpush : (fun j => ∑ i, (v i/M.det)*M j i) = w := by
    have hv (i : ι) : v i / M.det = (N.mulVec w) i := by
      dsimp [v]
      field_simp
    simp_rw [hv]
    have hm := Matrix.mulVec_mulVec w M N
    rw [hMN, Matrix.one_mulVec] at hm
    ext j
    have hj := congrFun hm j
    simpa only [Matrix.mulVec, dotProduct, mul_comm] using hj
  have hp := piola_divergence D E M N hMN hNM hdet chain mixed v
  rw [hpush] at hp
  have hdiv : fieldDivergence D v = M.det * fieldDivergence E w := by
    have h := (eq_div_iff hdet).mp hp
    simpa only [mul_comm] using h.symm
  have hdir : (∑ i, v i * D i g) = M.det * ∑ j, w j * E j g := by
    have h := piola_contraction D E M N hNM chain v g
    simp_rw [congrFun hpush] at h
    simpa only [mul_comm] using ((eq_div_iff hdet).mp h).symm
  change residueDivergence D g v = _
  rw [residueDivergence, hdiv, hdir, residueDivergence]
  ring

/-- The source multiplier of the pullback is the same determinant. This
form directly carries a solved residue divergence equation to new
coordinates, before any finite-field trace is taken. -/
theorem residue_solution_piola_pullback
    (D E : ι → Derivation ℤ K K) (M N : Matrix ι ι K)
    (hMN : M*N = 1) (hNM : N*M = 1) (hdet : M.det ≠ 0)
    (chain : ∀ j x, E j x = ∑ k, N k j * D k x)
    (mixed : ∀ i j k, D k (M j i) = D i (M j k))
    (g r : K) (w : ι → K)
    (equation : r + residueDivergence E g w = 0) :
    M.det * r +
      residueDivergence D g (fun i => M.det * (N.mulVec w) i) = 0 := by
  rw [residue_piola_pullback D E M N hMN hNM hdet chain mixed g w,
    ← mul_add, equation, mul_zero]

end HoldoutConstruction

#print axioms HoldoutConstruction.residue_piola_pullback
#print axioms HoldoutConstruction.residue_solution_piola_pullback
#print axioms HoldoutConstruction.residueDivergence_map
#print axioms HoldoutConstruction.residueDivergence_append_zero
end
end
