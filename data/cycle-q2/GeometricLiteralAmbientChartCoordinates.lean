import Proposal.GeometricLiteralAbelJacobiContraction

/-! The shifted affine coordinates of the literal incidence threefold on a weight-one chart.
Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace CycleQ2LiteralAmbientChartCoordinates

open MvPolynomial CycleQ2IncidenceEquations CycleQ2IncidenceDehomogenizedChart
  CycleQ2LiteralAbelJacobiEquations CycleQ2LiteralAbelJacobiContraction

abbrev normalizedIdeal (i : Fin 4) : Ideal (MvPolynomial (Fin 5) ℂ) :=
  Ideal.span {smoothF (57 : ℂ) Complex.I, X i.castSucc - 1}

abbrev NormalizedRing (i : Fin 4) := MvPolynomial (Fin 5) ℂ ⧸ normalizedIdeal i

/-- Return to the five homogeneous variables on the section Xi = 1.
The fourth affine coordinate is the shifted weight-two variable. -/
def representative (i : Fin 4) : ChartPolynomial ℂ →ₐ[ℂ] MvPolynomial (Fin 5) ℂ :=
  aeval (fun j => match j with
    | none => X (Fin.last 4) + X (2 : Fin 4).castSucc ^ 2
    | some k => X (i.succAbove k).castSucc)

private theorem dehomogenize_representative (i : Fin 4) (p : ChartPolynomial ℂ) :
    dehomogenize i (representative i p) = p := by
  have h : (dehomogenize i).comp (representative i) = AlgHom.id ℂ (ChartPolynomial ℂ) := by
    apply MvPolynomial.algHom_ext
    intro j
    cases j with
    | none => simpa only [AlgHom.comp_apply, representative, aeval_X, AlgHom.id_apply] using
        dehomogenize_normal (S := ℂ) i
    | some k => simpa only [AlgHom.comp_apply, representative, aeval_X, AlgHom.id_apply] using
        dehomogenize_succAbove (S := ℂ) i k
  exact AlgHom.congr_fun h p

private theorem normalized_self (i : Fin 4) :
    Ideal.Quotient.mk (normalizedIdeal i) (X i.castSucc) = 1 := by
  apply sub_eq_zero.mp
  rw [← map_one (Ideal.Quotient.mk (normalizedIdeal i)), ← map_sub]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))

private theorem polynomial_recovery (i : Fin 4) (p : MvPolynomial (Fin 5) ℂ) :
    Ideal.Quotient.mk (normalizedIdeal i) (representative i (dehomogenize i p)) =
      Ideal.Quotient.mk (normalizedIdeal i) p := by
  let q := Ideal.Quotient.mkₐ ℂ (normalizedIdeal i)
  have hlin (j : Fin 4) : q (representative i (linearCoordinate i j)) = q (X j.castSucc) := by
    rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨k, rfl⟩
    · simpa only [linearCoordinate_self, map_one, q, Ideal.Quotient.mkₐ_eq_mk] using
        (normalized_self _).symm
    · simp [representative]
  have h : (q.comp (representative i)).comp (dehomogenize i) = q := by
    apply MvPolynomial.algHom_ext
    intro j
    induction j using Fin.lastCases with
    | last =>
      simp only [AlgHom.comp_apply, dehomogenize_last, map_sub, map_pow, hlin]
      simp [representative]
    | cast j => simpa only [AlgHom.comp_apply, dehomogenize_castSucc] using hlin j
  exact AlgHom.congr_fun h p

private theorem dehomogenize_incidence (i : Fin 4) :
    dehomogenize i (smoothF (57 : ℂ) Complex.I) = seedF i := by
  unfold seedF
  rw [← CycleQ2IncidenceChartSeedFiber.literal_pointEquationF]

private def toFixed (i : Fin 4) : NormalizedRing i →ₐ[ℂ] T i :=
  Ideal.Quotient.liftₐ (normalizedIdeal i) ((Ideal.Quotient.mkₐ ℂ (fixedIdeal i)).comp
    (dehomogenize i)) (by
    change normalizedIdeal i ≤ RingHom.ker ((Ideal.Quotient.mkₐ ℂ (fixedIdeal i)).comp
      (dehomogenize i)).toRingHom
    apply Ideal.span_le.mpr
    intro p hp
    rcases Set.mem_insert_iff.mp hp with rfl | hp
    · change Ideal.Quotient.mk (fixedIdeal i) (dehomogenize i (smoothF (57 : ℂ) Complex.I)) = 0
      rw [dehomogenize_incidence]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
    · obtain rfl := Set.mem_singleton_iff.mp hp
      change Ideal.Quotient.mk _ (dehomogenize i (X i.castSucc - 1)) = 0
      simp)

private def fromFixed (i : Fin 4) : T i →ₐ[ℂ] NormalizedRing i :=
  Ideal.Quotient.liftₐ (fixedIdeal i) ((Ideal.Quotient.mkₐ ℂ (normalizedIdeal i)).comp
    (representative i)) (by
    change fixedIdeal i ≤ RingHom.ker ((Ideal.Quotient.mkₐ ℂ (normalizedIdeal i)).comp
      (representative i)).toRingHom
    apply (Ideal.span_singleton_le_iff_mem _).mpr
    change Ideal.Quotient.mk (normalizedIdeal i) (representative i (seedF i)) = 0
    rw [← dehomogenize_incidence, polynomial_recovery]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp)))

/-- The normalized incidence hypersurface and the fixed chart used for contraction
have the same complex coordinate algebra. -/
def normalizedEquiv (i : Fin 4) : NormalizedRing i ≃ₐ[ℂ] T i :=
  AlgEquiv.ofAlgHom (toFixed i) (fromFixed i) (by
    apply AlgHom.ext
    intro x
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact congrArg (Ideal.Quotient.mk (fixedIdeal i)) (dehomogenize_representative i p)) (by
    apply AlgHom.ext
    intro x
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact polynomial_recovery i p)

@[simp] theorem normalizedEquiv_mk (i : Fin 4) (p : MvPolynomial (Fin 5) ℂ) :
    normalizedEquiv i (Ideal.Quotient.mk _ p) =
      Ideal.Quotient.mk (fixedIdeal i) (dehomogenize i p) := rfl

@[simp] theorem normalizedEquiv_symm_mk (i : Fin 4) (p : ChartPolynomial ℂ) :
    (normalizedEquiv i).symm (Ideal.Quotient.mk _ p) =
      Ideal.Quotient.mk (normalizedIdeal i) (representative i p) := rfl

end CycleQ2LiteralAmbientChartCoordinates

#print axioms CycleQ2LiteralAmbientChartCoordinates.normalizedEquiv
