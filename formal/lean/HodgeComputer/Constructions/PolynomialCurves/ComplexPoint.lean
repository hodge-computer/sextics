import HodgeComputer.Constructions.HoldoutCover.GenericIncidence
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
Extracted from hodgepodgeconjecture's PR #151. The declaration namespace
is retained for compatibility; this theorem applies to any integral square system.

Lift the exact mod-five point to characteristic zero using the shared
Jacobian-localized incidence algebra of fqlx's accepted construction.
No continuity in the deformation coefficient is assumed: it remains 1/14.
Prepared with OpenAI Codex assistance for hodgepodgeconjecture.
-/
noncomputable section
set_option maxHeartbeats 800000
namespace DeformedConic
open HoldoutConstruction

/-- A nonsingular integral square system with a point in some characteristic
has a nonsingular complex point. Flatness supplies the generic-fiber step;
algebraic closedness then embeds the finite field factor in the complexes. -/
theorem complex_point_of_etale_nontrivial {n : ℕ}
    (eqs : Fin n → MvPolynomial (Fin n) ℤ)
    [Nontrivial (SquareEtaleRing eqs)] :
    ∃ v : Fin n → ℂ, (∀ i, MvPolynomial.aeval v (eqs i)=0) ∧
      IsUnit (Matrix.det (fun i j => MvPolynomial.aeval v (MvPolynomial.pderiv i (eqs j)))) := by
  obtain ⟨I,hI,hfin,hsep,heq,hjac⟩ :=
    squareGeneric_exists_fieldFactor (K := ℂ) eqs
      (show Function.Injective (algebraMap ℤ ℂ) from Int.cast_injective)
  letI := hI
  let E := (SquareGenericAlgebra ℂ eqs) ⧸ I
  letI : Field E := Ideal.Quotient.field I
  letI : Module.Finite ℂ E := hfin
  let f : E →ₐ[ℂ] ℂ := IsAlgClosed.lift
  let v : Fin n → ℂ := fun i => f (squareGenericCoordinates eqs I i)
  have hm (P : MvPolynomial (Fin n) ℤ) :
      f (MvPolynomial.aeval (squareGenericCoordinates eqs I) P)=MvPolynomial.aeval v P := by
    have hh : f.toRingHom.comp (MvPolynomial.aeval (R := ℤ) (squareGenericCoordinates eqs I)).toRingHom =
        (MvPolynomial.aeval (R := ℤ) v).toRingHom := by
      apply MvPolynomial.ringHom_ext
      · intro r
        simp
      · intro i
        simp [v]
        change f ((MvPolynomial.aeval (R := ℤ) (squareGenericCoordinates eqs I))
          (MvPolynomial.X i)) = f (squareGenericCoordinates eqs I i)
        rw [MvPolynomial.aeval_X]
    exact congrArg (fun g : MvPolynomial (Fin n) ℤ →+* ℂ => g P) hh
  refine ⟨v,fun i => ?_,?_⟩
  · rw [← hm,heq,map_zero]
  · have hu := hjac.map f.toRingHom
    rw [RingHom.map_det] at hu
    change IsUnit (Matrix.det (fun i j => f (MvPolynomial.aeval
      (squareGenericCoordinates eqs I) (MvPolynomial.pderiv i (eqs j))))) at hu
    simpa only [hm] using hu


end DeformedConic
