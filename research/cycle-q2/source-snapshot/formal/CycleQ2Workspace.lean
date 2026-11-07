import HodgeComputer.Verify

/-!
The original target and elementary fixed-denominator operations.
This module does not assert that the original target has a certificate.
Compilation is a separate, explicitly recorded step.
-/

noncomputable section
namespace CycleQ2Workspace
open MvPolynomial HodgeComputer

abbrev z (i : Fin 6) : Poly := X i

def originalF : Poly :=
  z 0 ^ 6 + z 1 ^ 6 + z 2 ^ 6 + z 3 ^ 6 + z 4 ^ 6 + z 5 ^ 6 +
  C (1 / 2 : ℂ) *
    (z 0 ^ 3 * z 1 * z 3 * z 4 +
     z 1 ^ 3 * z 2 * z 4 * z 5 +
     z 2 ^ 3 * z 0 * z 5 * z 3)

def originalA : Poly := z 0 ^ 2 * z 1 ^ 2 * z 2 ^ 3 * z 3 ^ 2 * z 4 ^ 2 * z 5

def OriginalGoal : Prop := HasCertificate originalF originalA 2

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

#check OriginalGoal
#check HodgeComputer.Verify
#print axioms defect_decomposition
#print axioms fixedOperator_add
#print axioms defect_scale

end CycleQ2Workspace
