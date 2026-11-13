import HodgeComputer.Constructions.HoldoutCover.GenericIncidence
import HodgeComputer.Constructions.HoldoutCover.PolynomialFieldMap

/-!
Extracted from fqlx's accepted PR #150. The original declaration namespace
is retained for compatibility; the hypotheses are independent of its target.

Arithmetic lifting and anchored dominance for polynomial curve constructions.

The first theorem records precisely why a nonsingular finite-characteristic
point of an integral square incidence supplies a characteristic-zero generic
point.  The coefficient ring must embed in the desired characteristic-zero
field; a finite-field solution alone is not enough.

The second theorem permits an arbitrary nonzero anchored curve coordinate,
not only the linear coordinate used in the original Holdout construction.
Prepared with OpenAI ChatGPT assistance for fqlx, using the maintained
HoldoutConstruction machinery and its original attribution.
-/

noncomputable section

namespace ReflectionCoupledFano

open HoldoutConstruction

section ArithmeticLift

variable {R K T : Type*} [CommRing R] [Field K] [CommRing T]
variable [Algebra R K] [Algebra R T] [Nontrivial T]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A nonsingular special-fiber point proves that the very same integral
square system has a finite separable solution over an injective generic
coefficient field.  No conclusion is drawn from modular rank alone. -/
theorem square_system_generic_lift
    (equations : ι → MvPolynomial ι R) (seed : ι → T)
    (hseed : ∀ i, MvPolynomial.aeval seed (equations i) = 0)
    (hjac : IsUnit (Matrix.det
      (fun i j => MvPolynomial.aeval seed (MvPolynomial.pderiv i (equations j)))))
    (hinj : Function.Injective (algebraMap R K)) :
    ∃ I : Ideal (SquareGenericAlgebra K equations), I.IsMaximal ∧
      Module.Finite K ((SquareGenericAlgebra K equations) ⧸ I) ∧
      Algebra.IsSeparable K ((SquareGenericAlgebra K equations) ⧸ I) ∧
      (∀ i, MvPolynomial.aeval (squareGenericCoordinates equations I)
        (equations i) = 0) ∧
      IsUnit (Matrix.det (fun i j => MvPolynomial.aeval
        (squareGenericCoordinates equations I)
          (MvPolynomial.pderiv i (equations j)))) := by
  let : Nontrivial (SquareEtaleRing equations) :=
    square_system_jacobian_nontrivial equations seed hseed hjac
  exact squareGeneric_exists_fieldFactor equations hinj

end ArithmeticLift

section AnchoredDominance

variable {R S : Type*} [CommRing R] [CommRing S] [IsDomain S]

omit [IsDomain S] in
/-- Constant terms of an anchored polynomial substitution only see the
constant coefficient of the source polynomial. -/
theorem anchored_constantCoeff
    (f : R →+* Polynomial S) (q : Polynomial S) (hq : q.coeff 0 = 0)
    (p : Polynomial R) :
    Polynomial.constantCoeff (p.eval₂ f q) =
      (Polynomial.constantCoeff.comp f) (p.coeff 0) := by
  have h : Polynomial.constantCoeff.comp (Polynomial.eval₂RingHom f q) =
      (Polynomial.constantCoeff.comp f).comp Polynomial.constantCoeff := by
    apply Polynomial.ringHom_ext
    · intro a
      simp
    · simpa using hq
  exact congrArg (fun h : Polynomial R →+* S => h p) h

/-- Independent endpoint parameters remain independent under a polynomial
deformation when the distinguished curve coordinate has zero constant term
and is nonzero.  No linearity of that coordinate is required. -/
theorem anchored_polynomial_family_injective
    (f : R →+* Polynomial S)
    (hf : Function.Injective (Polynomial.constantCoeff.comp f))
    (q : Polynomial S) (hq0 : q.coeff 0 = 0) (hq : q ≠ 0) :
    Function.Injective (Polynomial.eval₂RingHom f q) := by
  let θ := Polynomial.eval₂RingHom f q
  have hX : θ Polynomial.X ≠ 0 := by
    simpa [θ] using hq
  have hker : ∀ p : Polynomial R, p ≠ 0 → θ p ≠ 0 := by
    intro p
    refine Polynomial.recOnHorner p (by simp) ?_ ?_
    · intro p a hp0 ha _ _ heq
      have hc := congrArg Polynomial.constantCoeff heq
      change Polynomial.constantCoeff ((p + Polynomial.C a).eval₂ f q) = 0 at hc
      rw [anchored_constantCoeff f q hq0] at hc
      simp only [Polynomial.coeff_add, Polynomial.coeff_C_zero, hp0, zero_add] at hc
      exact ha (hf (hc.trans (map_zero (Polynomial.constantCoeff.comp f)).symm))
    · intro p hp ih _ heq
      exact mul_ne_zero (ih hp) hX (by simpa only [map_mul] using heq)
  intro p q hpq
  by_contra h
  exact hker (p - q) (sub_ne_zero.mpr h) (by rw [map_sub, hpq, sub_self])

end AnchoredDominance

end ReflectionCoupledFano

#print axioms ReflectionCoupledFano.square_system_generic_lift
#print axioms ReflectionCoupledFano.anchored_polynomial_family_injective
