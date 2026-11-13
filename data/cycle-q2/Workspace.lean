import HodgeTarget

/-!
The original target and elementary fixed-denominator operations.
This module does not assert that the original target has a certificate.
Compilation is a separate, explicitly recorded step.
-/

noncomputable section
namespace CycleQ2Workspace
open MvPolynomial HodgeComputer

abbrev Poly := HodgeComputer.AmbientPoly 5

abbrev originalF : Poly := HodgeSubmission.F
abbrev originalA : Poly := HodgeSubmission.A

def OriginalGoal : Prop :=
  HasCertificate HodgeSubmission.F HodgeSubmission.q HodgeSubmission.A

lemma originalF_homogeneous : originalF.IsHomogeneous 6 := by
  have hx (i : Fin 6) : (X i : Poly).IsHomogeneous 1 := isHomogeneous_X ℂ i
  have hm0 : ((X 0 : Poly)^3 * X 1 * X 3 * X 4).IsHomogeneous 6 := by
    simpa using ((((hx 0).pow 3).mul (hx 1)).mul (hx 3)).mul (hx 4)
  have hm1 : ((X 1 : Poly)^3 * X 2 * X 4 * X 5).IsHomogeneous 6 := by
    simpa using ((((hx 1).pow 3).mul (hx 2)).mul (hx 4)).mul (hx 5)
  have hm2 : ((X 2 : Poly)^3 * X 0 * X 5 * X 3).IsHomogeneous 6 := by
    simpa using ((((hx 2).pow 3).mul (hx 0)).mul (hx 5)).mul (hx 3)
  have h := ((((((isHomogeneous_X_pow (0 : Fin 6) 6).add
    (isHomogeneous_X_pow 1 6)).add (isHomogeneous_X_pow 2 6)).add
    (isHomogeneous_X_pow 3 6)).add (isHomogeneous_X_pow 4 6)).add
    (isHomogeneous_X_pow 5 6)).add (((hm0.add hm1).add hm2).C_mul (1 / 2 : ℂ))
  convert h using 1
  unfold originalF HodgeSubmission.F
  ring

lemma originalA_homogeneous : originalA.IsHomogeneous 12 := by
  have hx (i : Fin 6) : (X i : Poly).IsHomogeneous 1 := isHomogeneous_X ℂ i
  simpa only [originalA, HodgeSubmission.A, mul_assoc] using
    ((((((hx 0).pow 2).mul ((hx 1).pow 2)).mul ((hx 2).pow 3)).mul
      ((hx 3).pow 2)).mul ((hx 4).pow 2)).mul (hx 5)

lemma originalF_ne_zero : originalF ≠ 0 := by
  intro h
  have hh := congrArg (MvPolynomial.eval
    (fun _ : Fin 6 => (1 : ℂ))) h
  norm_num [originalF, HodgeSubmission.F] at hh

lemma originalF_totalDegree : originalF.totalDegree = 6 :=
  originalF_homogeneous.totalDegree originalF_ne_zero

/-- The fixed-D linear part of the exact original equation. -/
def fixedOperator (F D : Poly) (N : Fin 6 → Poly) (Q : Poly) : Poly :=
  -(2 : Poly) * D * HodgeTestbed.directional F N +
    F * HodgeTestbed.divergenceNumerator D N - F ^ 3 * Q

theorem defect_decomposition (F A D : Poly) (N : Fin 6 → Poly) (Q : Poly) :
    defect F A D 2 N - F ^ 3 * Q = A * D ^ 2 + fixedOperator F D N Q := by
  unfold defect fixedOperator
  ring

theorem directional_add (F : Poly) (N M : Fin 6 → Poly) :
    HodgeTestbed.directional F (fun i => N i + M i) =
      HodgeTestbed.directional F N + HodgeTestbed.directional F M := by
  simp [HodgeTestbed.directional, mul_add, Finset.sum_add_distrib]

theorem divergence_add (N M : Fin 6 → Poly) :
    HodgeTestbed.divergence (fun i => N i + M i) =
      HodgeTestbed.divergence N + HodgeTestbed.divergence M := by
  simp [HodgeTestbed.divergence, map_add, Finset.sum_add_distrib]

theorem divergenceNumerator_add (D : Poly) (N M : Fin 6 → Poly) :
    HodgeTestbed.divergenceNumerator D (fun i => N i + M i) =
      HodgeTestbed.divergenceNumerator D N + HodgeTestbed.divergenceNumerator D M := by
  unfold HodgeTestbed.divergenceNumerator
  rw [divergence_add, directional_add]
  ring

theorem fixedOperator_add (F D : Poly) (N M : Fin 6 → Poly) (Q R : Poly) :
    fixedOperator F D (fun i => N i + M i) (Q + R) =
      fixedOperator F D N Q + fixedOperator F D M R := by
  unfold fixedOperator
  rw [directional_add, divergenceNumerator_add]
  ring

/-- Denominator rescaling preserves the current, but does not remove its defect. -/
theorem defect_scale (F A D H : Poly) (N : Fin 6 → Poly) :
    defect F A (H * D) 2 (fun i => H * N i) = H ^ 2 * defect F A D 2 N := by
  unfold defect
  rw [HodgeTestbed.directional_mul, HodgeTestbed.divergenceNumerator_mul]
  ring

end CycleQ2Workspace
