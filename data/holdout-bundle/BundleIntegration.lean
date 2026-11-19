import Proposal.BundleCalculus
import Proposal.BundleFlow
import HodgeComputer.Constructions.HoldoutCover.PolynomialFamilyBridge
import HodgeComputer.Constructions.HoldoutCover.FiniteTrace

/-!
Effective integration on the actual conic and normalized trace back to the
relative quotient field. The shared polynomial-family theorem builds the
coefficientwise antiderivative. This wrapper discharges its normal,
determinant, polynomiality, and source-coordinate obligations from our conic.
The finite target-field extension and coefficient derivations remain explicit
arguments until the concrete field construction is inserted.
-/

noncomputable section

namespace HoldoutBundle.ConicFamily
open Polynomial HoldoutConstruction MvPolynomial
open scoped BigOperators

variable {R B K E : Type*}
variable [CommRing R] [CommRing B] [IsDomain B]
variable [Field K] [CharZero K] [Algebra B K] [IsFractionRing B K]
variable [Field E] [CharZero E] [Algebra R E]
variable [Algebra K (CurveFunctionField E)] [FiniteDimensional K (CurveFunctionField E)]

local instance : Algebra ℤ (CurveFunctionField E) := Ring.toIntAlgebra _

theorem residue_solution_from_conic
    (π : MvPolynomial (Fin 5) R →+* B) (hπ : Function.Surjective π)
    (a b : R) (A : MvPolynomial (Fin 5) R)
    (k : Fin 4 → E)
    (p : HoldoutBundle.ConicFamily (algebraMap R E a) (algebraMap R E b) k)
    (D : Fin 3 → Derivation ℤ E E)
    (hDcommute : ∀ i j, Function.Commute (D i) (D j))
    (hDk : ∀ i j : Fin 3, D i (k j.succ) = if j = i then 1 else 0)
    (hDbase : ∀ i r, D i (algebraMap R E r) = 0)
    (Dq : Fin 4 → Derivation ℤ K K)
    (hg0 : algebraMap B K (π (pderiv 0 (kPoly a b))) ≠ 0)
    (hDq : ∀ i f, Dq i (algebraMap B K (π f)) =
      algebraMap B K (π (pderiv i.succ f)) -
        algebraMap B K (π (pderiv i.succ (kPoly a b))) /
          algebraMap B K (π (pderiv 0 (kPoly a b))) *
            algebraMap B K (π (pderiv 0 f)))
    (hρ : ∀ f,
      finiteQuotientEvaluation (K := K) (L := CurveFunctionField E) π f =
        MvPolynomial.eval₂Hom (algebraMap R (CurveFunctionField E))
          (fun i => algebraMap (Polynomial E) (CurveFunctionField E) (p.curve i)) f) :
    ∃ w : Fin 4 → K,
      residueDivergence Dq (algebraMap B K (π (pderiv 0 (kPoly a b)))) w =
        -(algebraMap B K (π (pderiv 0 A)) /
            algebraMap B K (π (pderiv 0 (kPoly a b))) -
          algebraMap B K (π A) *
            algebraMap B K (π (pderiv 0 (pderiv 0 (kPoly a b)))) /
              (algebraMap B K (π (pderiv 0 (kPoly a b))))^2) := by
  let ρ := finiteQuotientEvaluation (K := K) (L := (CurveFunctionField E)) π
  let E' : Fin 4 → Derivation ℤ (CurveFunctionField E) (CurveFunctionField E) := fun i => extendFiniteDerivation (L := (CurveFunctionField E)) (Dq i)
  have hρC (r : R) : ρ (MvPolynomial.C r) =
      algebraMap E (CurveFunctionField E) (algebraMap R E r) := by
    rw [hρ]
    simp only [MvPolynomial.eval₂Hom_C]
    rfl
  have hρX (i : Fin 5) : ρ (MvPolynomial.X i) =
      algebraMap (Polynomial E) (CurveFunctionField E) (p.curve i) := by
    rw [hρ]
    simp only [MvPolynomial.eval₂Hom_X']
  have hρgrad (i : Fin 5) : ρ (pderiv i (kPoly a b)) =
      algebraMap (Polynomial E) (CurveFunctionField E)
        (gradient (Polynomial.C (algebraMap R E a))
          (Polynomial.C (algebraMap R E b)) p.curve i) := by
    rw [hρ, kPoly_pderiv_eval]
    rw [gradient_map]
    rfl
  have hf : ρ (kPoly a b) = 0 := by
    rw [hρ, kPoly_eval]
    have h := congrArg (algebraMap (Polynomial E) (CurveFunctionField E)) p.curve_equation
    rw [K_map, map_zero] at h
    exact h
  have hg : ρ (pderiv 0 (kPoly a b)) ≠ 0 :=
    (map_ne_zero (algebraMap K (CurveFunctionField E))).mpr hg0
  have hE (i : Fin 4) (f : MvPolynomial (Fin 5) R) :
      E' i (ρ f) = ρ (pderiv i.succ f) -
        ρ (pderiv i.succ (kPoly a b)) / ρ (pderiv 0 (kPoly a b)) * ρ (pderiv 0 f) := by
    change extendFiniteDerivation (L := (CurveFunctionField E)) (Dq i)
      (algebraMap K (CurveFunctionField E) (algebraMap B K (π f))) = _
    rw [extendFiniteDerivation_apply, hDq]
    simp only [map_sub, map_mul, map_div₀]
    rfl
  obtain ⟨w, hw⟩ := residue_solution_from_polynomial_curve (K := K) (L := (CurveFunctionField E))
    π hπ (kPoly a b) A (sourceDerivation D) E' (p.evaluationMatrix D)
    (fun i => algebraMap (Polynomial E) (CurveFunctionField E) (p.normal i))
    (algebraMap E (CurveFunctionField E)) (curveTime (E := E)) 0
    (sourceDerivation_time_constant D) (sourceDerivation_time D) hf hg
    (p.evaluationMatrix_det_ne_zero D hDk) (p.evaluationMatrix_normal D)
    (fun i j => by rw [hρX]; exact p.evaluationMatrix_tangent D i j)
    (by
      change (∑ j, ρ (pderiv j (kPoly a b)) *
        algebraMap (Polynomial E) (CurveFunctionField E) (p.normal j)) = 1
      simp_rw [hρgrad]
      exact p.normal_field_pairing)
    (fun i r => by
      change sourceDerivation D i (ρ (MvPolynomial.C r)) = 0
      rw [hρC]
      refine Fin.cases ?_ (fun j => ?_) i
      · exact sourceDerivation_time_constant D _
      · rw [sourceDerivation_coefficient, hDbase, map_zero])
    (sourceDerivations_commute D hDcommute) hE
    (fun r => by rw [hρC]; exact coefficient_polynomial _)
    (fun i => by rw [hρX]; exact polynomial_image _)
    (fun i => polynomial_image (p.normal i))
    (sourceDerivation_eval_range D)
  let g : K := algebraMap B K (π (pderiv 0 (kPoly a b)))
  let r : K := -(algebraMap B K (π (pderiv 0 A)) / g -
    algebraMap B K (π A) * algebraMap B K (π (pderiv 0 (pderiv 0 (kPoly a b)))) / g^2)
  have heq : residueDivergence E' (algebraMap K (CurveFunctionField E) g) w = algebraMap K (CurveFunctionField E) r := by
    simpa only [g, r, ρ, finiteQuotientEvaluation, RingHom.comp_apply,
      map_neg, map_sub, map_div₀, map_mul, map_pow] using hw
  exact residue_solution_descends_finite Dq E'
    (fun i x => extendFiniteDerivation_apply (Dq i) x) g r ⟨w, heq⟩

end HoldoutBundle.ConicFamily

#print axioms HoldoutBundle.ConicFamily.residue_solution_from_conic
