import Proposal.GeometricTarget01Part01
import Proposal.GeometricCartierOrbit
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Algebra.MvPolynomial.Funext

/-!
# Lifting the full invariant weighted family to a protected deformation

Status: source-only proof draft. Compilation and independent kernel replay
are deferred at the user's request. No new axioms or admissions are used.

The original homogeneous coordinates are (Z0,Z1,Z2,Z3,Z4,Z5). The weighted
quotient coordinates are (s0,s1,s2,s3,w) = (Z0,Z1,Z3,Z4,Z2^2), and the pencil
parameter is lambda = Z5/Z2. Thus h(s,w) lifts to a polynomial independent of
Z5. Its restriction to Z5 = lambda*Z2 is the same h for every lambda.

The lift preserves weighted degree and the actual beta/gamma invariances.
Every nonzero weighted homogeneous h gives a genuine Direction: its affine
lift has degree zero in Z5, whereas the protected equation has positive
degree in that variable. The deformation can therefore pass, at (tau,lambda)
= (1,0), through any specified member of the full invariant weighted family.

These algebraic statements do not construct a supported correspondence or a
generic relative primitive. Once that primitive has been proved for the
Direction constructed here, the existing
CycleQ2GenericSpecialization.protected_certificate_of_generic_relative_primitive
already returns the unchanged protected certificate, allowing Laurent poles
in tau. No specialization theorem for every smooth weighted sextic is needed
for that implication.

The geometric strategy is due to Ben Diamond and the cited work of Claire
Voisin. Prepared for fqlx with OpenAI ChatGPT assistance.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace CycleQ2GenericPencilLift

open MvPolynomial HodgeComputer
open CycleQ2IncidenceNormalForm CycleQ2GeometricIncidenceProj
open scoped BigOperators

abbrev WeightedPoly := MvPolynomial (Fin 5) ℂ
abbrev HomogeneousPoly := AmbientPoly 5
abbrev PencilPoly := MvPolynomial (Fin 5) ℂ

/-- The weight-two variable is the square of the original Z2. -/
def liftValues : Fin 5 → HomogeneousPoly :=
  ![X 0, X 1, X 3, X 4, X 2 ^ 2]

def weightedLift : WeightedPoly →ₐ[ℂ] HomogeneousPoly := aeval liftValues

def quotientCoordinates (z : Fin 6 → ℂ) : Fin 5 → ℂ :=
  ![z 0, z 1, z 3, z 4, z 2 ^ 2]

theorem eval_weightedLift (p : WeightedPoly) (z : Fin 6 → ℂ) :
    eval z (weightedLift p) = eval (quotientCoordinates z) p := by
  have h : (eval z).comp weightedLift.toRingHom = eval (quotientCoordinates z) := by
    ext i
    fin_cases i <;> simp [weightedLift, liftValues, quotientCoordinates]
  exact RingHom.congr_fun h p

theorem weightedLift_injective : Function.Injective weightedLift := by
  intro p q hpq
  apply MvPolynomial.funext
  intro z
  obtain ⟨u, hu⟩ := IsAlgClosed.exists_pow_nat_eq (z 4) (show 0 < (2 : ℕ) by decide)
  let z' : Fin 6 → ℂ := ![z 0, z 1, u, z 2, z 3, 0]
  have hz : quotientCoordinates z' = z := by
    funext i
    fin_cases i <;> simp [quotientCoordinates, z', hu]
  have h := congrArg (eval z') hpq
  simpa only [eval_weightedLift, hz] using h

private theorem liftValues_homogeneous (i : Fin 5) :
    (liftValues i).IsHomogeneous (geometricWeight i) := by
  fin_cases i
  · exact isHomogeneous_X ℂ 0
  · exact isHomogeneous_X ℂ 1
  · exact isHomogeneous_X ℂ 3
  · exact isHomogeneous_X ℂ 4
  · exact isHomogeneous_X_pow (2 : Fin 6) 2

/-- Weighted degree becomes ordinary degree under the actual double cover. -/
theorem weightedLift_homogeneous {d : ℕ} {p : WeightedPoly}
    (hp : p.IsWeightedHomogeneous geometricWeight d) :
    (weightedLift p).IsHomogeneous d := by
  induction hp using IsWeightedHomogeneous.induction_on with
  | zero => simpa only [map_zero] using isHomogeneous_zero (Fin 6) ℂ d
  | add p q hp hq ihp ihq => simpa only [map_add] using ihp.add ihq
  | monomial e c he =>
    rw [weightedLift, aeval_monomial]
    change (C c * ∏ i ∈ e.support, liftValues i ^ e i).IsHomogeneous d
    have hprod := (IsHomogeneous.prod e.support
      (fun i => liftValues i ^ e i) (fun i => geometricWeight i * e i)
      (fun i _ => (liftValues_homogeneous i).pow (e i))).C_mul c
    have hdegree : (∑ i ∈ e.support, geometricWeight i * e i) = d := by
      simpa only [Finsupp.weight_apply, Finsupp.sum, smul_eq_mul, Nat.mul_comm] using he
    exact hdegree ▸ hprod

def betaAction : HomogeneousPoly →ₐ[ℂ] HomogeneousPoly :=
  aeval ![X 0, X 1, -X 2, X 3, X 4, -X 5]

def gammaAction (ω : ℂ) : HomogeneousPoly →ₐ[ℂ] HomogeneousPoly :=
  aeval ![C (ω ^ 2) * X 0, C (ω ^ 2) * X 1, X 2,
    C ω * X 3, X 4, X 5]

theorem betaAction_weightedLift : betaAction.comp weightedLift = weightedLift := by
  ext i
  fin_cases i <;> simp [betaAction, weightedLift, liftValues]

theorem gammaAction_weightedLift (ω : ℂ) :
    (gammaAction ω).comp weightedLift =
      weightedLift.comp (CycleQ2SeedCyclicAction.polynomialAction ω) := by
  ext i
  fin_cases i <;>
    simp [gammaAction, weightedLift, liftValues,
      CycleQ2SeedCyclicAction.polynomialAction, CycleQ2SeedCyclicAction.actionValues]

theorem eval_betaAction (p : HomogeneousPoly) (z : Fin 6 → ℂ) :
    eval z (betaAction p) = eval (CycleQ2GeometricTarget.beta z) p := by
  have h : (eval z).comp betaAction.toRingHom =
      eval (CycleQ2GeometricTarget.beta z) := by
    ext i
    fin_cases i <;> simp [betaAction, CycleQ2GeometricTarget.beta]
  exact RingHom.congr_fun h p

theorem eval_gammaAction (ω : ℂ) (p : HomogeneousPoly) (z : Fin 6 → ℂ) :
    eval z (gammaAction ω p) = eval (CycleQ2GeometricTarget.gamma ω z) p := by
  have h : (eval z).comp (gammaAction ω).toRingHom =
      eval (CycleQ2GeometricTarget.gamma ω z) := by
    ext i
    fin_cases i <;> simp [gammaAction, CycleQ2GeometricTarget.gamma]
  exact RingHom.congr_fun h p

theorem weightedLift_beta (p : WeightedPoly) (z : Fin 6 → ℂ) :
    eval (CycleQ2GeometricTarget.beta z) (weightedLift p) = eval z (weightedLift p) := by
  rw [← eval_betaAction]
  exact congrArg (eval z) (AlgHom.congr_fun betaAction_weightedLift p)

theorem weightedLift_gamma {d : ℕ} (p : WeightedPoly)
    (hp : p.IsWeightedHomogeneous fullGrading (d, 0))
    (ω : ℂ) (hω : ω ^ 3 = 1) (z : Fin 6 → ℂ) :
    eval (CycleQ2GeometricTarget.gamma ω z) (weightedLift p) = eval z (weightedLift p) := by
  have haction : CycleQ2SeedCyclicAction.polynomialAction ω p = p := by
    simpa using CycleQ2SeedCyclicAction.polynomialAction_homogeneous ω hω p d 0 hp
  rw [← eval_gammaAction]
  have h := AlgHom.congr_fun (gammaAction_weightedLift ω) p
  simpa only [AlgHom.comp_apply, haction] using congrArg (eval z) h

/-- Variables in the target are (s0,s1,s2,s3,u); v is lambda*u. -/
def pencilRestriction (lambda : ℂ) : HomogeneousPoly →ₐ[ℂ] PencilPoly :=
  aeval ![X 0, X 1, X 4, X 2, X 3, C lambda * X 4]

def doubleCover : WeightedPoly →ₐ[ℂ] PencilPoly :=
  aeval ![X 0, X 1, X 2, X 3, X 4 ^ 2]

theorem pencilRestriction_weightedLift (lambda : ℂ) :
    (pencilRestriction lambda).comp weightedLift = doubleCover := by
  ext i
  fin_cases i <;> simp [pencilRestriction, weightedLift, liftValues, doubleCover]

/-- The exact quotient of the original protected equation, before deformation. -/
def weightedPencil (lambda : ℂ) : WeightedPoly :=
  X 0 ^ 6 + X 1 ^ 6 + X 2 ^ 6 + X 3 ^ 6 + C (1 + lambda ^ 6) * X 4 ^ 3 +
    C (1 / 2 : ℂ) * (X 0 ^ 3 * X 1 * X 2 * X 3 +
      C lambda * X 1 ^ 3 * X 3 * X 4 + C lambda * X 0 * X 2 * X 4 ^ 2)

theorem pencilRestriction_protected_F (lambda : ℂ) :
    pencilRestriction lambda HodgeSubmission.F = doubleCover (weightedPencil lambda) := by
  norm_num [pencilRestriction, HodgeSubmission.F, doubleCover, weightedPencil]
  ring

theorem weightedPencil_homogeneous (lambda : ℂ) :
    (weightedPencil lambda).IsWeightedHomogeneous fullGrading (6, 0) := by
  have h0 : (X 0 : WeightedPoly).IsWeightedHomogeneous fullGrading (1, 2) :=
    isWeightedHomogeneous_X ℂ fullGrading 0
  have h1 : (X 1 : WeightedPoly).IsWeightedHomogeneous fullGrading (1, 2) :=
    isWeightedHomogeneous_X ℂ fullGrading 1
  have h2 : (X 2 : WeightedPoly).IsWeightedHomogeneous fullGrading (1, 1) :=
    isWeightedHomogeneous_X ℂ fullGrading 2
  have h3 : (X 3 : WeightedPoly).IsWeightedHomogeneous fullGrading (1, 0) :=
    isWeightedHomogeneous_X ℂ fullGrading 3
  have h4 : (X 4 : WeightedPoly).IsWeightedHomogeneous fullGrading (2, 0) :=
    isWeightedHomogeneous_X ℂ fullGrading 4
  have hs0 : (X 0 ^ 6 : WeightedPoly).IsWeightedHomogeneous fullGrading (6, 0) := by
    convert h0.pow 6 using 1 <;> norm_num
  have hs1 : (X 1 ^ 6 : WeightedPoly).IsWeightedHomogeneous fullGrading (6, 0) := by
    convert h1.pow 6 using 1 <;> norm_num
  have hs2 : (X 2 ^ 6 : WeightedPoly).IsWeightedHomogeneous fullGrading (6, 0) := by
    convert h2.pow 6 using 1 <;> norm_num
  have hs3 : (X 3 ^ 6 : WeightedPoly).IsWeightedHomogeneous fullGrading (6, 0) := by
    convert h3.pow 6 using 1 <;> norm_num
  have hw : (X 4 ^ 3 : WeightedPoly).IsWeightedHomogeneous fullGrading (6, 0) := by
    convert h4.pow 3 using 1 <;> norm_num
  have hm0 : (X 0 ^ 3 * X 1 * X 2 * X 3 : WeightedPoly).
      IsWeightedHomogeneous fullGrading (6, 0) := by
    convert (((h0.pow 3).mul h1).mul h2).mul h3 using 1 <;> norm_num
  have hm1 : (X 1 ^ 3 * X 3 * X 4 : WeightedPoly).
      IsWeightedHomogeneous fullGrading (6, 0) := by
    convert ((h1.pow 3).mul h3).mul h4 using 1 <;> norm_num
  have hm2 : (X 0 * X 2 * X 4 ^ 2 : WeightedPoly).
      IsWeightedHomogeneous fullGrading (6, 0) := by
    convert (h0.mul h2).mul (h4.pow 2) using 1 <;> norm_num
  simpa only [weightedPencil, mul_assoc] using
    ((((hs0.add hs1).add hs2).add hs3).add (hw.C_mul (1 + lambda ^ 6))).add
      (((hm0.add (hm1.C_mul lambda)).add (hm2.C_mul lambda)).C_mul (1 / 2 : ℂ))

def deformation (tau : ℂ) (h : WeightedPoly) : HomogeneousPoly :=
  HodgeSubmission.F + C tau * weightedLift h

def quotientDeformation (tau lambda : ℂ) (h : WeightedPoly) : WeightedPoly :=
  weightedPencil lambda + C tau * h

theorem pencilRestriction_deformation (tau lambda : ℂ) (h : WeightedPoly) :
    pencilRestriction lambda (deformation tau h) =
      doubleCover (quotientDeformation tau lambda h) := by
  have hlift := AlgHom.congr_fun (pencilRestriction_weightedLift lambda) h
  simp only [deformation, quotientDeformation, map_add, map_mul,
    AlgHom.comp_apply] at hlift ⊢
  rw [pencilRestriction_protected_F, hlift]
  simp [pencilRestriction, doubleCover]

/-- Any chosen weighted endpoint is reached at (tau,lambda)=(1,0). -/
theorem quotientDeformation_endpoint (p : WeightedPoly) :
    quotientDeformation 1 0 (p - weightedPencil 0) = p := by
  simp only [quotientDeformation, map_one, one_mul]
  ring

theorem deformation_homogeneous (tau : ℂ) (h : WeightedPoly)
    (hh : h.IsWeightedHomogeneous fullGrading (6, 0)) :
    (deformation tau h).IsHomogeneous 6 :=
  CycleQ2Workspace.originalF_homogeneous.add
    ((weightedLift_homogeneous (homogeneous_of_character hh)).C_mul tau)

theorem deformation_beta (tau : ℂ) (h : WeightedPoly) (z : Fin 6 → ℂ) :
    eval (CycleQ2GeometricTarget.beta z) (deformation tau h) =
      eval z (deformation tau h) := by
  simp only [deformation, map_add, map_mul, eval_C]
  rw [CycleQ2GeometricTarget.beta_F, weightedLift_beta]

theorem deformation_gamma (tau : ℂ) (h : WeightedPoly)
    (hh : h.IsWeightedHomogeneous fullGrading (6, 0))
    (ω : ℂ) (hω : ω ^ 3 = 1) (z : Fin 6 → ℂ) :
    eval (CycleQ2GeometricTarget.gamma ω z) (deformation tau h) =
      eval z (deformation tau h) := by
  simp only [deformation, map_add, map_mul, eval_C]
  rw [CycleQ2GeometricTarget.gamma_F ω hω, weightedLift_gamma h hh ω hω]

@[simp] theorem deformation_zero (h : WeightedPoly) :
    deformation 0 h = HodgeSubmission.F := by
  simp [deformation]

/-- The affine coordinates remain the original (Z1,Z2,Z3,Z4,Z5). -/
def affineLift : WeightedPoly →ₐ[ℂ] AmbientPoly 4 :=
  CycleQ2AffineChart.dehomogenize.comp weightedLift

theorem affineLift_eq : affineLift = aeval ![1, X 0, X 2, X 3, X 1 ^ 2] := by
  ext i
  fin_cases i <;>
    simp [affineLift, CycleQ2AffineChart.dehomogenize, weightedLift, liftValues]

theorem affineLift_ne_zero {d : ℕ} {h : WeightedPoly}
    (hh : h.IsWeightedHomogeneous geometricWeight d) (h0 : h ≠ 0) :
    affineLift h ≠ 0 := by
  intro hz
  have hchart := CycleQ2AffineClearing.homogeneous_chart (weightedLift_homogeneous hh)
  have hz' : CycleQ2AffineChart.dehomogenize (weightedLift h) = 0 := hz
  rw [hz', map_zero, map_zero, mul_zero] at hchart
  have hlift : weightedLift h = weightedLift 0 := by
    apply CycleQ2Bridge.polynomialMap_injective (n := 5)
    simpa only [map_zero] using hchart
  exact h0 (weightedLift_injective hlift)

private theorem affineLift_X_degree_last (i : Fin 5) :
    degreeOf (4 : Fin 5) (affineLift (X i)) = 0 := by
  rw [affineLift_eq, aeval_X]
  fin_cases i
  · exact degreeOf_one 4
  · norm_num [degreeOf_X]
  · norm_num [degreeOf_X]
  · norm_num [degreeOf_X]
  · exact degreeOf_X_pow_of_ne 2 (by decide)

/-- The affine lift is independent of the original Z5. -/
theorem affineLift_degree_last (h : WeightedPoly) :
    degreeOf (4 : Fin 5) (affineLift h) = 0 := by
  induction h using MvPolynomial.induction_on with
  | C c => simp [affineLift_eq]
  | add p q hp hq =>
      rw [map_add]
      apply Nat.eq_zero_of_le_zero
      simpa only [hp, hq, max_self] using degreeOf_add_le 4 (affineLift p) (affineLift q)
  | mul_X p i hp =>
      rw [map_mul]
      apply Nat.eq_zero_of_le_zero
      simpa only [hp, affineLift_X_degree_last, add_zero] using
        degreeOf_mul_le 4 (affineLift p) (affineLift (X i))

private theorem affineF_degree_last_pos :
    0 < degreeOf (4 : Fin 5) CycleQ2AffineClearing.affineF := by
  by_contra h
  have hz := Nat.eq_zero_of_not_pos h
  have hnot : (4 : Fin 5) ∉ CycleQ2AffineClearing.affineF.vars := by
    simpa only [mem_vars_iff_degreeOf_ne_zero, hz, ne_eq, not_true_eq_false, not_false_eq_true]
  have he : eval₂Hom (RingHom.id ℂ) (fun _ : Fin 5 => 0)
      CycleQ2AffineClearing.affineF =
      eval₂Hom (RingHom.id ℂ) ![0, 0, 0, 0, 1] CycleQ2AffineClearing.affineF := by
    apply eval₂Hom_congr' rfl _ rfl
    intro i hi _
    fin_cases i
    · rfl
    · rfl
    · rfl
    · rfl
    · exact (hnot hi).elim
  norm_num [CycleQ2AffineGeometry.affineF_formula] at he

theorem affineF_not_dvd_affineLift {d : ℕ} {h : WeightedPoly}
    (hh : h.IsWeightedHomogeneous geometricWeight d) (h0 : h ≠ 0) :
    ¬ CycleQ2AffineClearing.affineF ∣ affineLift h := by
  rintro ⟨q, hq⟩
  have hq0 : q ≠ 0 := by
    intro hz
    exact affineLift_ne_zero hh h0 (by simpa only [hz, mul_zero] using hq)
  have hd := congrArg (degreeOf (4 : Fin 5)) hq
  rw [affineLift_degree_last,
    degreeOf_mul_eq CycleQ2AffineClearing.affineF_ne_zero hq0] at hd
  have hf := affineF_degree_last_pos
  omega

/-- Every nonzero homogeneous weighted lift supplies the precise existing
generic-specialization Direction, with no nonvanishing assumption left over. -/
def direction {d : ℕ} (h : WeightedPoly)
    (hh : h.IsWeightedHomogeneous geometricWeight d) (h0 : h ≠ 0) :
    CycleQ2GenericSpecialization.Direction where
  polynomial := affineLift h
  residue_ne_zero := by
    intro hz
    exact affineF_not_dvd_affineLift hh h0
      ((CycleQ2AffineHypersurface.affineMap_kernel (affineLift h)).mp hz)

/-- Actual coefficient parameters of the full invariant sextic family. -/
def endpointDifference (c : FullInvariantIndex 6 → ℂ) : WeightedPoly :=
  fullInvariantPolynomial 6 c - weightedPencil 0

theorem endpointDifference_homogeneous (c : FullInvariantIndex 6 → ℂ) :
    (endpointDifference c).IsWeightedHomogeneous fullGrading (6, 0) :=
  (fullInvariantPolynomial_homogeneous 6 c).sub (weightedPencil_homogeneous 0)

def endpointDirection (c : FullInvariantIndex 6 → ℂ) (hc : endpointDifference c ≠ 0) :
    CycleQ2GenericSpecialization.Direction :=
  direction (endpointDifference c)
    (homogeneous_of_character (endpointDifference_homogeneous c)) hc

@[simp] theorem endpointDirection_polynomial (c : FullInvariantIndex 6 → ℂ)
    (hc : endpointDifference c ≠ 0) :
    (endpointDirection c hc).polynomial = affineLift (endpointDifference c) := rfl

theorem fullInvariant_endpoint (c : FullInvariantIndex 6 → ℂ) :
    quotientDeformation 1 0 (endpointDifference c) = fullInvariantPolynomial 6 c :=
  quotientDeformation_endpoint _

theorem dehomogenize_deformation (tau : ℂ) (h : WeightedPoly) :
    CycleQ2AffineChart.dehomogenize (deformation tau h) =
      CycleQ2AffineClearing.affineF + C tau * affineLift h := by
  simp [deformation, affineLift, CycleQ2AffineClearing.affineF]

end CycleQ2GenericPencilLift

end
