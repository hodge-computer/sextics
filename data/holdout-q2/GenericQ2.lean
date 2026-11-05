import Proposal.GenericQuadratic
import Proposal.QuadraticDivergence

/-! The actual generic pole-two cubic certificate, serving U³ V². All
coefficient inverses are justified in the regular localization at (2,2,1,1).
The q=1 contact solver is reused without finding additional cubic lines. -/
noncomputable section
open scoped BigOperators
namespace HoldoutQ2.GenericQ2
open MvPolynomial HodgeTestbed NewLineAlgebra

abbrev K := NewLineAlgebra.Coefficients
abbrev Poly := MvPolynomial (Fin 4) K

def coefficientDenominator : K := QuinticReduction.denominator a b c d

theorem coefficientDenominator_specialize :
    specialize coefficientDenominator = (515198970880 : ℚ) := by
  simp only [coefficientDenominator, QuinticReduction.denominator,
    QuinticReduction.e, QuinticReduction.r, map_mul, map_sub, map_add,
    map_pow, map_ofNat, specialize_a, specialize_b, specialize_c, specialize_d]
  norm_num

theorem coefficientDenominator_isUnit : IsUnit coefficientDenominator := by
  apply (RegularSpecialization.isUnit_iff_specialize_ne_zero point _).mpr
  change specialize coefficientDenominator ≠ 0
  rw [coefficientDenominator_specialize]
  norm_num

def coefficientInverse : K := Ring.inverse coefficientDenominator

theorem coefficientInverse_mul :
    coefficientInverse * QuinticReduction.denominator a b c d = 1 :=
  Ring.inverse_mul_cancel _ coefficientDenominator_isUnit

def polynomialPrimitive : Fin 4 → Poly :=
  QuinticReduction.primitive a b c d coefficientInverse

def divergenceCoefficients : Fin 10 → K :=
  QuadraticDivergence.normalizedCoefficients a b c d coefficientInverse

def F : Poly := GenericQuadratic.F

def B : Poly := X 0^3 * X 1^2

theorem F_eq : F = QuinticReduction.cubic a b c d := by
  exact (QuadraticDivergence.cubic_eq a b c d).symm

theorem F_homogeneous : F.IsHomogeneous 3 := by
  rw [F_eq]
  exact QuinticReduction.cubic_homogeneous a b c d

theorem polynomialPrimitive_homogeneous (i : Fin 4) :
    (polynomialPrimitive i).IsHomogeneous 3 :=
  QuinticReduction.primitive_homogeneous a b c d coefficientInverse i

theorem polynomialPrimitive_source : directional F polynomialPrimitive = B := by
  rw [F_eq]
  exact QuinticReduction.primitive_source a b c d coefficientInverse coefficientInverse_mul

theorem polynomialPrimitive_divergence :
    divergence polynomialPrimitive = QuadraticSolver.quadratic divergenceCoefficients :=
  QuadraticDivergence.primitive_divergence a b c d coefficientInverse

theorem quadratic_certificate :
    Equations F (divergence polynomialPrimitive) GenericQuadratic.D
      (GenericQuadratic.N divergenceCoefficients) 0 := by
  rw [polynomialPrimitive_divergence]
  exact GenericQuadratic.equations divergenceCoefficients

/-- The original norm denominator with its harmless constant factor six. -/
def D : Poly := Q2Reduction.denominator GenericQuadratic.D

def N : Fin 4 → Poly :=
  Q2Reduction.numerators F GenericQuadratic.D polynomialPrimitive
    (GenericQuadratic.N divergenceCoefficients)

theorem D_eq : D = C (6:K) * GenericQuadratic.D := rfl

theorem D_ne_zero : D ≠ 0 := by
  have h6 : (6:K) ≠ 0 := by
    intro h
    have hs := congrArg specialize h
    norm_num [map_ofNat] at hs
  rw [D_eq]
  exact mul_ne_zero (by simpa only [ne_eq, C_eq_zero] using h6)
    GenericQuadratic.D_ne_zero

theorem D_homogeneous : D.IsHomogeneous 27 :=
  Q2Reduction.denominator_homogeneous GenericQuadratic.D_homogeneous

theorem N_homogeneous (i : Fin 4) : (N i).IsHomogeneous 30 := by
  exact Q2Reduction.numerators_homogeneous F GenericQuadratic.D polynomialPrimitive
    (GenericQuadratic.N divergenceCoefficients) 27 F_homogeneous
    GenericQuadratic.D_homogeneous polynomialPrimitive_homogeneous
    (GenericQuadratic.N_homogeneous divergenceCoefficients) i

/-- Both exact strict equations, over all four unspecialized coefficients. -/
theorem equations : 2 * directional F N = B * D ∧ divergenceNumerator D N = 0 :=
  Q2Reduction.q2_equations_of_certificate F B GenericQuadratic.D polynomialPrimitive
    (GenericQuadratic.N divergenceCoefficients) F_homogeneous
    polynomialPrimitive_homogeneous polynomialPrimitive_source quadratic_certificate


/-- Exact norm-denominator profile, including the constant introduced by the
Euler correction. This is the denominator-legality bridge. -/
theorem D_norm_fiber {R : Type*} [CommRing R] (φ : K →+* R) :
    MvPolynomial.eval₂Hom (Polynomial.C.comp φ) ![1, 1, Polynomial.X, 0] D =
      6 * ((Polynomial.X : Polynomial R) •
        (1 : Matrix (Fin 27) (Fin 27) (Polynomial R)) -
        ((GenericQuadratic.representation (lineE+lineF)).map φ).map
          (Polynomial.C : R →+* Polynomial R)).det := by
  rw [D_eq, map_mul, GenericQuadratic.D_norm_fiber]
  simp [map_ofNat]

theorem certificate : D ≠ 0 ∧ D.IsHomogeneous 27 ∧
    (∀ i, (N i).IsHomogeneous 30) ∧
    2 * directional F N = B * D ∧ divergenceNumerator D N = 0 :=
  ⟨D_ne_zero,D_homogeneous,N_homogeneous,equations⟩

end HoldoutQ2.GenericQ2
#print axioms HoldoutQ2.GenericQ2.certificate
