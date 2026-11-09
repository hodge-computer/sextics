import Proposal.CubicResidueTrace
import Proposal.WeightedPrimitiveTransportCore

/-!
# Binding cubic trace cancellation to the protected symmetric sextic

All coefficients below are derived from the unchanged protected equation
and source through `WeightedPrimitiveTransport.rawWeighted` and `rawSource`.
The cubic matrix includes the `ell^-2` factor from the actual residue.
The matrix trace and the three-sheet trace vanish identically. This does
not produce a relative primitive: the cubic pair cover is the same cover
via the complementary root, and its source is minus the original source.
-/

noncomputable section

namespace SymmetricCubicTrace

open MvPolynomial CubicResidueTrace
open WeightedPrimitiveTransport
open scoped Matrix

set_option maxHeartbeats 4000000

def ell (lam : ℂ) : ℂ := 2+2*lam^6-(5/7:ℂ)*lam^2-(10/7:ℂ)*lam^4
def leftBase (b : ℂ) : ℂ := 1+2*b
def rightBase (c d : ℂ) : ℂ := c^2+2*c*d

def f0 (lam b c d : ℂ) : ℂ :=
  2+b^6+2*c^6+d^6+(5/7:ℂ)*(leftBase b)^2*rightBase c d+
    (10/7:ℂ)*leftBase b*(rightBase c d)^2

def f1 (lam b c d : ℂ) : ℂ :=
  30+30*lam^2*c^4+(5/7:ℂ)*(-lam^2*(leftBase b)^2-2*leftBase b*rightBase c d)+
    (10/7:ℂ)*(-2*lam^2*leftBase b*rightBase c d-(rightBase c d)^2)

def f2 (lam b c d : ℂ) : ℂ :=
  30+30*lam^4*c^2+(5/7:ℂ)*(rightBase c d+2*lam^2*leftBase b)+
    (10/7:ℂ)*(lam^4*leftBase b+2*lam^2*rightBase c d)

def p0 (b c d : ℂ) : ℂ := b*d*c^2
def p1 (lam b c d : ℂ) : ℂ := -b*d*(c^2+lam^2)
def p2 (lam b d : ℂ) : ℂ := b*d*lam^2

theorem raw_equation_coefficients (lam b c d u : ℂ) :
    eval ![lam,b,c,d,u] rawWeighted =
      ell lam*u^3+f2 lam b c d*u^2+f1 lam b c d*u+f0 lam b c d := by
  simp [rawWeighted, leftQuadric, rightQuadric, ell, f0, f1, f2,
    leftBase, rightBase, Fin.ext_iff, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four]
  ring

theorem raw_source_coefficients (lam b c d u : ℂ) :
    eval ![lam,b,c,d,u] rawSource = p0 b c d+p1 lam b c d*u+p2 lam b d*u^2 := by
  simp [rawSource, p0, p1, p2, Fin.ext_iff, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four]
  ring

theorem first_derivative_coefficients (lam b c d u : ℂ) :
    eval ![lam,b,c,d,u] (pderiv 4 rawWeighted) =
      3*ell lam*u^2+2*f2 lam b c d*u+f1 lam b c d := by
  simp [rawWeighted, leftQuadric, rightQuadric, ell, f1, f2,
    leftBase, rightBase, pderiv_mul, pderiv_pow, pderiv_X, Pi.single_apply,
    Fin.ext_iff, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four]
  ring

theorem second_derivative_coefficients (lam b c d u : ℂ) :
    eval ![lam,b,c,d,u] (pderiv 4 (pderiv 4 rawWeighted)) =
      6*ell lam*u+2*f2 lam b c d := by
  have htwo : (pderiv 4 : Derivation ℂ Poly Poly) 2 = 0 :=
    (pderiv 4 : Derivation ℂ Poly Poly).map_natCast 2
  have hthree : (pderiv 4 : Derivation ℂ Poly Poly) 3 = 0 :=
    (pderiv 4 : Derivation ℂ Poly Poly).map_natCast 3
  simp [rawWeighted, leftQuadric, rightQuadric, ell, f2,
    leftBase, rightBase, pderiv_mul, pderiv_pow, pderiv_X, Pi.single_apply,
    Fin.ext_iff, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
    htwo, hthree]
  ring

theorem source_derivative_coefficients (lam b c d u : ℂ) :
    eval ![lam,b,c,d,u] (pderiv 4 rawSource) = p1 lam b c d+2*p2 lam b d*u := by
  simp [rawSource, p1, p2, pderiv_mul, pderiv_pow, pderiv_X, Pi.single_apply,
    Fin.ext_iff, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four]
  ring

/-- Direct binding to the protected six-variable equation. -/
theorem protected_equation_coefficients (lam b c d v : ℂ) :
    eval ![1+v,1-v,b,c+lam*v,c-lam*v,d] HodgeSubmission.F =
      ell lam*v^6+f2 lam b c d*v^4+f1 lam b c d*v^2+f0 lam b c d := by
  rw [← exact_chart_equation]
  simp [chartEquation, rawWeighted, leftQuadric, rightQuadric, squareLift,
    ell, f0, f1, f2, leftBase, rightBase, Fin.ext_iff,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four]
  ring

/-- Cleared minus-discriminant of the nonmonic protected cubic. -/
def clearedDiscriminant (lam b c d : ℂ) : ℂ :=
  4*(f2 lam b c d)^3*f0 lam b c d-(f2 lam b c d)^2*(f1 lam b c d)^2-
    18*ell lam*f2 lam b c d*f1 lam b c d*f0 lam b c d+
    4*ell lam*(f1 lam b c d)^3+27*(ell lam)^2*(f0 lam b c d)^2

theorem normalized_discriminant (lam b c d : ℂ) (h : ell lam ≠ 0) :
    discriminantDenominator (f2 lam b c d/ell lam)
      (f1 lam b c d/ell lam) (f0 lam b c d/ell lam) =
      clearedDiscriminant lam b c d/(ell lam)^4 := by
  unfold discriminantDenominator clearedDiscriminant
  field_simp
  <;> ring

/-- This exact specialization proves that the generic discriminant is nonzero. -/
theorem nonsingular_specialization :
    ell 0 = 2 ∧ clearedDiscriminant 0 0 0 0 = -442368 := by
  norm_num [ell, clearedDiscriminant, f0, f1, f2, leftBase, rightBase]

def residueMatrix (lam b c d : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  companionResidue (ell lam) (f2 lam b c d/ell lam)
    (f1 lam b c d/ell lam) (f0 lam b c d/ell lam)
    (p0 b c d) (p1 lam b c d) (p2 lam b d)

theorem protected_companion_trace_zero (lam b c d : ℂ) :
    Matrix.trace (residueMatrix lam b c d) = 0 :=
  companion_residue_trace_zero _ _ _ _ _ _ _

/-- The exact scalar residue coefficient before choosing any primitive. -/
def rawDensity (lam b c d u : ℂ) : ℂ :=
  2*(eval ![lam,b,c,d,u] (pderiv 4 rawWeighted)*
      eval ![lam,b,c,d,u] (pderiv 4 rawSource)-
    eval ![lam,b,c,d,u] (pderiv 4 (pderiv 4 rawWeighted))*
      eval ![lam,b,c,d,u] rawSource)/
    (eval ![lam,b,c,d,u] (pderiv 4 rawWeighted))^3

theorem eval_squareLift (p : Poly) (lam b c d v : ℂ) :
    eval ![lam,b,c,d,v] (squareLift p) = eval ![lam,b,c,d,v^2] p := by
  induction p using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p j hp =>
    simp only [map_mul, hp, squareLift_X]
    fin_cases j <;> simp

/-- The coefficient in the existing primitive endpoint is exactly the
coefficient whose three-sheet trace is computed here. -/
theorem actual_reflection_density (lam b c d v : ℂ) :
    residueCoefficient (eval ![lam,b,c,d,v]) rawWeighted rawSource =
      rawDensity lam b c d (v^2) := by
  simp only [residueCoefficient, rawDensity, eval_squareLift]

theorem raw_density_at_sheet (lam b c d x y z : ℂ)
    (hell : ell lam ≠ 0) (hxy : x ≠ y) (hxz : x ≠ z)
    (hf2 : f2 lam b c d = -ell lam*(x+y+z))
    (hf1 : f1 lam b c d = ell lam*(x*y+x*z+y*z)) :
    rawDensity lam b c d x =
      sheetResidue (ell lam) (p0 b c d) (p1 lam b c d) (p2 lam b d) x y z := by
  have hxy' := sub_ne_zero.mpr hxy
  have hxz' := sub_ne_zero.mpr hxz
  have hderiv : 3*ell lam*x^2+2*f2 lam b c d*x+f1 lam b c d =
      ell lam*(x-y)*(x-z) := by rw [hf2, hf1]; ring
  have hsecond : 6*ell lam*x+2*f2 lam b c d =
      2*ell lam*(2*x-y-z) := by rw [hf2]; ring
  simp only [rawDensity, first_derivative_coefficients,
    second_derivative_coefficients, source_derivative_coefficients,
    raw_source_coefficients, hderiv, hsecond, sheetResidue]
  field_simp
  <;> ring

/-- On any three distinct sheets of the actual cubic, the pair source is
the negative source on the complementary sheet. No primitive is assumed. -/
theorem protected_complementary_pair_source (lam b c d x y z : ℂ)
    (hell : ell lam ≠ 0) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hf2 : f2 lam b c d = -ell lam*(x+y+z))
    (hf1 : f1 lam b c d = ell lam*(x*y+x*z+y*z)) :
    rawDensity lam b c d x+rawDensity lam b c d y = -rawDensity lam b c d z := by
  have hf2y : f2 lam b c d = -ell lam*(y+x+z) := by rw [hf2]; ring
  have hf1y : f1 lam b c d = ell lam*(y*x+y*z+x*z) := by rw [hf1]; ring
  have hf2z : f2 lam b c d = -ell lam*(z+x+y) := by rw [hf2]; ring
  have hf1z : f1 lam b c d = ell lam*(z*x+z*y+x*y) := by rw [hf1]; ring
  rw [raw_density_at_sheet lam b c d x y z hell hxy hxz hf2 hf1,
    raw_density_at_sheet lam b c d y x z hell hxy.symm hyz hf2y hf1y,
    raw_density_at_sheet lam b c d z x y hell hxz.symm hyz.symm hf2z hf1z]
  exact complementary_pair_source _ _ _ _ _ _ _ hell hxy hxz hyz

#print axioms raw_equation_coefficients
#print axioms raw_source_coefficients
#print axioms first_derivative_coefficients
#print axioms second_derivative_coefficients
#print axioms source_derivative_coefficients
#print axioms protected_equation_coefficients
#print axioms normalized_discriminant
#print axioms nonsingular_specialization
#print axioms protected_companion_trace_zero
#print axioms eval_squareLift
#print axioms actual_reflection_density
#print axioms raw_density_at_sheet
#print axioms protected_complementary_pair_source

end SymmetricCubicTrace

set_option autoImplicit false
set_option maxHeartbeats 4000000

/-- Exact coefficient and canonical source identities for the symmetric sextic chart.
This algebraic packet does not assert existence of a rational primitive.
The reflection chart and conditional trace endpoint are due to the contributors
credited in fqlx's PR #222 at d0919c2 and benediamond's PR #223.  This exact
coefficient calculation was prepared for kmehltretter82 with OpenAI Codex
assistance. -/
theorem HodgeComputer.SymmetricSexticResidual.canonical_trace_source
    (lam b c d u : ℂ) :
    let L := 1 + 2*b
    let R := c^2 + 2*c*d
    let ell := 2 + 2*lam^6 - (5/7 : ℂ)*lam^2 - (10/7 : ℂ)*lam^4
    let B := 30 + 30*lam^4*c^2 + (5/7 : ℂ)*(R + 2*lam^2*L) +
      (10/7 : ℂ)*(lam^4*L + 2*lam^2*R)
    let C := 30 + 30*lam^2*c^4 + (5/7 : ℂ)*(-lam^2*L^2 - 2*L*R) +
      (10/7 : ℂ)*(-2*lam^2*L*R - R^2)
    let D := 2 + b^6 + 2*c^6 + d^6 + (5/7 : ℂ)*L^2*R + (10/7 : ℂ)*L*R^2
    let P := b*d*(1-u)*(c^2-lam^2*u)
    let Pu := b*d*(-c^2-lam^2+2*lam^2*u)
    let g := 3*ell*u^2 + 2*B*u + C
    let gu := 6*ell*u + 2*B
    let T0 := b*d*c^2 - b*d*lam^2*C/(3*ell)
    let T1 := -b*d*(c^2+lam^2) - 2*b*d*lam^2*B/(3*ell)
    ell ≠ 0 →
      (2 + b^6 + 2*c^6 + d^6 + 30*u + 30*u^2 + 2*u^3 +
        30*lam^2*c^4*u + 30*lam^4*c^2*u^2 + 2*lam^6*u^3 +
        (5/7 : ℂ)*(L-u)^2*(R-lam^2*u) +
        (10/7 : ℂ)*(L-u)*(R-lam^2*u)^2 = ell*u^3+B*u^2+C*u+D) ∧
      (P - (b*d*lam^2/(3*ell))*g = T0+T1*u) ∧
      (Pu - (b*d*lam^2/(3*ell))*gu = T1) ∧
      (g*Pu-gu*P = g*T1-gu*(T0+T1*u)) := by
  intro L R ell B C D P Pu g gu T0 T1 hell
  refine ⟨?_, ?_, ?_, ?_⟩
  · dsimp only [ell, B, C, D]
    ring
  all_goals dsimp only [P, Pu, g, gu, T0, T1]
  all_goals field_simp [hell]
  all_goals ring

#print axioms HodgeComputer.SymmetricSexticResidual.canonical_trace_source
