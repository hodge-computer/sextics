import HodgeTestbed.RowCertificate
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.FinCases

/-!
# A concrete two-row obstruction

These integer rows occur in the cyclic-triple-fano cubic-direction
experiment, fixed mixed case 05. The source-to-row identification is
independently reconstructed in rbajaj5/hodge-lab, not proved here.
The two equations are x_119 = 0 and -756*x_119 = -5; the integer
functional (756, 1) therefore pairs to zero on all correction columns
and to -5 on the target. This proves inconsistency of the literal rows
over every characteristic-zero field, not HasCertificate or a complete
instance exclusion. Developed with OpenAI Codex assistance.

Reproduce: lake build HodgeTestbed.RowCertificateExample
Kernel replay: lake env leanchecker HodgeTestbed.RowCertificateExample
All 175 columns are included; unspecified entries are zero.
The correspondence to the polynomial coefficient rows is checked separately.
-/

open scoped BigOperators

namespace HodgeTestbed.RowCertificateExample

def matrix (row : Fin 2) (column : Fin 175) : ℤ :=
  match row.val, column.val with
  | 0, 119 => 1
  | 1, 119 => -756
  | _, _ => 0

def target (row : Fin 2) : ℤ :=
  match row.val with
  | 0 => 0
  | 1 => -5
  | _ => 0

def dual (row : Fin 2) : ℤ :=
  match row.val with
  | 0 => 756
  | 1 => 1
  | _ => 0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem annihilates : ∀ column : Fin 175,
    ∑ row, dual row * matrix row column = 0 := by
  intro column
  fin_cases column <;> decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem separates : ∑ row, dual row * target row ≠ 0 := by decide

/-- Inconsistency of the actual encoded integer rows over every
characteristic-zero field. Source-coefficient identification is external. -/
theorem no_solution {K : Type*} [Field K] [CharZero K] :
    ¬ ∃ coefficients : Fin 175 → K,
      ∀ row : Fin 2, ∑ column, (matrix row column : K) * coefficients column =
        (target row : K) :=
  HodgeTestbed.no_solution_of_integer_row_certificate matrix target dual annihilates separates

end HodgeTestbed.RowCertificateExample
