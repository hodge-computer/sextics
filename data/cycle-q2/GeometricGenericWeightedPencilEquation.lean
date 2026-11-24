import Proposal.GeometricGenericWeightedCoordinates
import Proposal.GeometricGenericPencilLift

/-!
# The weighted equation and its normal jets on the deformed generic pencil

In the chart (Z_0=1), the normal coordinate is the second weighted
coordinate. Substitution into a polynomial in this one coordinate keeps
both the deformation parameter and the pencil ratio fixed while computing
all normal derivatives.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace CycleQ2GenericWeightedPencilEquation

open MvPolynomial HodgeComputer CycleQ2Bridge CycleQ2AffineClearing CycleQ2AffineGeometry
  CycleQ2IncidenceNormalForm CycleQ2GenericPencilLift CycleQ2GenericSpecialization
  CycleQ2GenericWeightedCoordinates

abbrev P := MvPolynomial (Fin 5) RF

/-- The quotient coordinates in the original chart, with the first coordinate normalized to one. -/
def weightedPoint : Fin 5 → RF := ![1, z 0, z 2, z 3, u ^ 2]

/-- The weighted sextic obtained by imposing the pencil ratio and adding the actual direction. -/
def equation (tau l : RF) (h : CycleQ2GenericPencilLift.WeightedPoly) : P :=
  X 0 ^ 6 + X 1 ^ 6 + X 2 ^ 6 + X 3 ^ 6 + C (1 + l ^ 6) * X 4 ^ 3 +
    C (1 / 2 : RF) * (X 0 ^ 3 * X 1 * X 2 * X 3 +
      C l * X 1 ^ 3 * X 3 * X 4 + C l * X 0 * X 2 * X 4 ^ 2) +
    C tau * MvPolynomial.map (algebraMap ℂ RF) h

private def line {R : Type} [CommRing R] (f : R →+* RF) (j : Fin 5) (x : Fin 5 → RF) :
    MvPolynomial (Fin 5) R →+* Polynomial RF :=
  eval₂Hom (Polynomial.C.comp f) (fun k => if k = j then Polynomial.X else Polynomial.C (x k))

private theorem eval_line {R : Type} [CommRing R] (f : R →+* RF) (j : Fin 5)
    (x : Fin 5 → RF) (p : MvPolynomial (Fin 5) R) :
    (line f j x p).eval (x j) = eval₂Hom f x p := by
  have he : (Polynomial.evalRingHom (x j)).comp (line f j x) = eval₂Hom f x := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [line]
    · intro k
      by_cases hk : k = j <;> simp [line, hk]
  exact RingHom.congr_fun he p

private theorem derivative_line {R : Type} [CommRing R] (f : R →+* RF) (j : Fin 5)
    (x : Fin 5 → RF) (p : MvPolynomial (Fin 5) R) :
    Polynomial.derivative (line f j x p) = line f j x (pderiv j p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [line]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p k hp =>
    by_cases hk : k = j
    · subst k
      simp only [map_mul, Polynomial.derivative_mul, hp, pderiv_mul, pderiv_X_self,
        mul_one, map_add]
      simp [line]
    · simp only [map_mul, Polynomial.derivative_mul, hp, pderiv_mul, pderiv_X_of_ne hk,
        mul_zero, add_zero]
      simp [line, hk]

private abbrev affineLine := line (algebraMap ℂ RF) 0 z
private abbrev weightedLine := line (RingHom.id RF) 1 weightedPoint

private theorem affineLine_lift (h : CycleQ2GenericPencilLift.WeightedPoly) :
    affineLine (affineLift h) = weightedLine (MvPolynomial.map (algebraMap ℂ RF) h) := by
  have he : affineLine.comp affineLift.toRingHom =
      weightedLine.comp (MvPolynomial.map (algebraMap ℂ RF)) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [affineLift_eq, affineLine, weightedLine, line]
    · intro i
      fin_cases i <;> simp [affineLift_eq, affineLine, weightedLine, line, weightedPoint, u]
  exact RingHom.congr_fun he h

private theorem equation_line (tau : RF) (h : CycleQ2GenericPencilLift.WeightedPoly) :
    weightedLine (equation tau lambda h) =
      affineLine affineF + Polynomial.C tau * affineLine (affineLift h) := by
  have hv : z 4 = lambda * u := lambda_mul_u.symm
  have htwo : (algebraMap ℂ RF) (2 : ℂ) = 2 := map_ofNat _ _
  rw [affineLine_lift, affineF_formula]
  simp [equation, affineLine, weightedLine, line, weightedPoint, hv, ← show z 1 = u from rfl,
    htwo, one_div, map_add, map_mul, map_pow]
  ring

private theorem equation_jet_line (tau : RF) (h : CycleQ2GenericPencilLift.WeightedPoly) (n : ℕ) :
    weightedLine ((pderiv 1)^[n] (equation tau lambda h)) =
      affineLine ((pderiv 0)^[n] affineF) + Polynomial.C tau * affineLine ((pderiv 0)^[n] (affineLift h)) := by
  induction n with
  | zero => exact equation_line tau h
  | succ n ih =>
    simp only [Function.iterate_succ_apply', ← derivative_line, ih, map_add, Polynomial.derivative_C_mul]

private theorem eval_z (p : HodgeComputer.AmbientPoly 4) :
    eval₂Hom (algebraMap ℂ RF) z p = polynomialMap 4 p := by
  have he : eval₂Hom (algebraMap ℂ RF) z = polynomialMap 4 := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp only [eval₂Hom_C]
      rfl
    · intro i
      simp [z]
  exact RingHom.congr_fun he p

/-- All derivatives in the affine normal direction, with both parameters held fixed. -/
theorem equation_jet (tau : RF) (h : CycleQ2GenericPencilLift.WeightedPoly) (n : ℕ) :
    eval weightedPoint ((pderiv 1)^[n] (equation tau lambda h)) =
      polynomialMap 4 ((pderiv 0)^[n] affineF) +
        tau * polynomialMap 4 ((pderiv 0)^[n] (affineLift h)) := by
  have he := congrArg (Polynomial.eval (z 0)) (equation_jet_line tau h n)
  have hw (p : P) : (weightedLine p).eval (z 0) = eval weightedPoint p :=
    eval_line (RingHom.id RF) 1 weightedPoint p
  have ha (p : HodgeComputer.AmbientPoly 4) : (affineLine p).eval (z 0) = polynomialMap 4 p :=
    (eval_line (algebraMap ℂ RF) 0 z p).trans (eval_z p)
  simpa only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, hw, ha] using he

variable (c : FullInvariantIndex 6 → ℂ) (hc : endpointDifference c ≠ 0)

theorem endpoint_equation :
    eval weightedPoint (equation (parameter (endpointDirection c hc)) lambda (endpointDifference c)) = 0 := by
  exact (equation_jet _ _ 0).trans (generic_pencil_equation (endpointDirection c hc))

/-- The weighted normal jets agree with the actual normal jets in the protected residue density. -/
theorem endpoint_normalJet (n : ℕ) :
    eval weightedPoint ((pderiv 1)^[n+1]
      (equation (parameter (endpointDirection c hc)) lambda (endpointDifference c))) =
      familyNormalJet (endpointDirection c hc) n :=
  equation_jet _ _ _

theorem endpoint_normal_ne_zero :
    eval weightedPoint (pderiv 1
      (equation (parameter (endpointDirection c hc)) lambda (endpointDifference c))) ≠ 0 := by
  exact (endpoint_normalJet c hc 0).trans_ne (familyPartial_zero_ne_zero (endpointDirection c hc))

end CycleQ2GenericWeightedPencilEquation
end

#print axioms CycleQ2GenericWeightedPencilEquation.endpoint_normalJet
#print axioms CycleQ2GenericWeightedPencilEquation.endpoint_equation
