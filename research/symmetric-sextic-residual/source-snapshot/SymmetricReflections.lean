import HodgeTarget
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.Ring

/-!
Exact algebraic hypotheses for `symmetric-sextic-residual` at sextics commit
ca173aad142bd5f6bf5dd156b6798223a45df54f.

`HodgeTarget` is the unmodified output of the repository's protected
`scripts/proposals/check.py::target_source` generator on `instance.rec`.
These results establish compact formulas and reflection symmetries of that
exact target. They make no assertion of a certificate, smoothness, or any
geometric support theorem.
-/

noncomputable section

namespace SymmetricReflections

open MvPolynomial

set_option maxHeartbeats 2000000

abbrev Poly := MvPolynomial (Fin 6) ℂ

def QX : Poly := X 0 * X 1 + X 0 * X 2 + X 1 * X 2

def QY : Poly := X 3 * X 4 + X 3 * X 5 + X 4 * X 5

def compactF : Poly :=
  X 0 ^ 6 + X 1 ^ 6 + X 2 ^ 6 + X 3 ^ 6 + X 4 ^ 6 + X 5 ^ 6 +
    C (1 / 7 : ℂ) * (5 * QX ^ 2 * QY + 10 * QX * QY ^ 2)

def compactA : Poly := X 0 * X 1 * X 2 * X 3 * X 4 * X 5

/-- The compact sextic is exactly the protected polynomial, without a hypothesis. -/
theorem exactF_compact : HodgeSubmission.F = compactF := by
  unfold HodgeSubmission.F compactF QX QY
  ring

theorem exactA_compact : HodgeSubmission.A = compactA := by
  rfl

def evaluateF (x0 x1 x2 y0 y1 y2 : ℂ) : ℂ :=
  MvPolynomial.eval ![x0, x1, x2, y0, y1, y2] HodgeSubmission.F

def evaluateA (x0 x1 x2 y0 y1 y2 : ℂ) : ℂ :=
  MvPolynomial.eval ![x0, x1, x2, y0, y1, y2] HodgeSubmission.A

theorem evaluateF_eq (x0 x1 x2 y0 y1 y2 : ℂ) :
    evaluateF x0 x1 x2 y0 y1 y2 =
      x0 ^ 6 + x1 ^ 6 + x2 ^ 6 + y0 ^ 6 + y1 ^ 6 + y2 ^ 6 +
        (1 / 7 : ℂ) *
          (5 * (x0*x1 + x0*x2 + x1*x2)^2 * (y0*y1 + y0*y2 + y1*y2) +
           10 * (x0*x1 + x0*x2 + x1*x2) * (y0*y1 + y0*y2 + y1*y2)^2) := by
  rw [evaluateF, exactF_compact]
  simp [compactF, QX, QY]

theorem evaluateA_eq (x0 x1 x2 y0 y1 y2 : ℂ) :
    evaluateA x0 x1 x2 y0 y1 y2 = x0*x1*x2*y0*y1*y2 := by
  rw [evaluateA, exactA_compact]
  simp [compactA]

theorem exactF_swapX (x0 x1 x2 y0 y1 y2 : ℂ) :
    evaluateF x1 x0 x2 y0 y1 y2 = evaluateF x0 x1 x2 y0 y1 y2 := by
  simp only [evaluateF_eq]
  ring

theorem exactF_swapY (x0 x1 x2 y0 y1 y2 : ℂ) :
    evaluateF x0 x1 x2 y1 y0 y2 = evaluateF x0 x1 x2 y0 y1 y2 := by
  simp only [evaluateF_eq]
  ring

theorem exactA_swapX (x0 x1 x2 y0 y1 y2 : ℂ) :
    evaluateA x1 x0 x2 y0 y1 y2 = evaluateA x0 x1 x2 y0 y1 y2 := by
  simp only [evaluateA_eq]
  ring

theorem exactA_swapY (x0 x1 x2 y0 y1 y2 : ℂ) :
    evaluateA x0 x1 x2 y1 y0 y2 = evaluateA x0 x1 x2 y0 y1 y2 := by
  simp only [evaluateA_eq]
  ring

/-- Global block parity of the exact sextic. -/
theorem exactF_evenY (x0 x1 x2 y0 y1 y2 : ℂ) :
    evaluateF x0 x1 x2 (-y0) (-y1) (-y2) =
      evaluateF x0 x1 x2 y0 y1 y2 := by
  simp only [evaluateF_eq]
  ring

/-- The source polynomial has the opposite block parity. -/
theorem exactA_oddY (x0 x1 x2 y0 y1 y2 : ℂ) :
    evaluateA x0 x1 x2 (-y0) (-y1) (-y2) =
      -evaluateA x0 x1 x2 y0 y1 y2 := by
  simp only [evaluateA_eq]
  ring

/-- Coordinates X=(a+s,a-s,b), Y=(c+t,c-t,d). -/
def transformedF (a b c d s t : ℂ) : ℂ :=
  evaluateF (a+s) (a-s) b (c+t) (c-t) d

def transformedA (a b c d s t : ℂ) : ℂ :=
  evaluateA (a+s) (a-s) b (c+t) (c-t) d

theorem transformedF_formula (a b c d s t : ℂ) :
    transformedF a b c d s t =
      2*a^6 + 30*a^4*s^2 + 30*a^2*s^4 + 2*s^6 + b^6 +
      2*c^6 + 30*c^4*t^2 + 30*c^2*t^4 + 2*t^6 + d^6 +
      (1 / 7 : ℂ) *
        (5 * (a^2-s^2+2*a*b)^2 * (c^2-t^2+2*c*d) +
         10 * (a^2-s^2+2*a*b) * (c^2-t^2+2*c*d)^2) := by
  rw [transformedF, evaluateF_eq]
  ring

theorem transformedA_formula (a b c d s t : ℂ) :
    transformedA a b c d s t = (a^2-s^2)*b*(c^2-t^2)*d := by
  rw [transformedA, evaluateA_eq]
  ring

theorem transformedF_evenS (a b c d s t : ℂ) :
    transformedF a b c d (-s) t = transformedF a b c d s t := by
  simp only [transformedF_formula]
  ring

theorem transformedF_evenT (a b c d s t : ℂ) :
    transformedF a b c d s (-t) = transformedF a b c d s t := by
  simp only [transformedF_formula]
  ring

theorem transformedF_evenY (a b c d s t : ℂ) :
    transformedF a b (-c) (-d) s (-t) = transformedF a b c d s t := by
  simp only [transformedF_formula]
  ring

theorem transformedA_evenS (a b c d s t : ℂ) :
    transformedA a b c d (-s) t = transformedA a b c d s t := by
  simp only [transformedA_formula]
  ring

theorem transformedA_evenT (a b c d s t : ℂ) :
    transformedA a b c d s (-t) = transformedA a b c d s t := by
  simp only [transformedA_formula]
  ring

theorem transformedA_oddY (a b c d s t : ℂ) :
    transformedA a b (-c) (-d) s (-t) = -transformedA a b c d s t := by
  simp only [transformedA_formula]
  ring

/-- The sum/difference substitution covers every original coordinate tuple. -/
theorem transformedF_recover (x0 x1 x2 y0 y1 y2 : ℂ) :
    transformedF ((x0+x1)/2) x2 ((y0+y1)/2) y2 ((x0-x1)/2) ((y0-y1)/2) =
      evaluateF x0 x1 x2 y0 y1 y2 := by
  unfold transformedF
  congr 1 <;> ring

/-- Exactly the three polynomial symmetries used by the two-reflection theorem. -/
theorem exact_reflection_hypotheses (a b c d s t : ℂ) :
    transformedF a b (-c) (-d) s (-t) = transformedF a b c d s t ∧
    transformedF a b c d (-s) t = transformedF a b c d s t ∧
    transformedF a b c d s (-t) = transformedF a b c d s t :=
  ⟨transformedF_evenY a b c d s t,
   transformedF_evenS a b c d s t,
   transformedF_evenT a b c d s t⟩

end SymmetricReflections

#print axioms SymmetricReflections.exactF_compact
#print axioms SymmetricReflections.exactF_swapX
#print axioms SymmetricReflections.exactF_swapY
#print axioms SymmetricReflections.transformedF_formula
#print axioms SymmetricReflections.transformedF_evenS
#print axioms SymmetricReflections.transformedF_evenT
#print axioms SymmetricReflections.transformedF_evenY
#print axioms SymmetricReflections.transformedF_recover
#print axioms SymmetricReflections.exact_reflection_hypotheses
