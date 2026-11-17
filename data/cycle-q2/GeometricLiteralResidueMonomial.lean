import Proposal.GeometricCoordinateCechTrace

/-!
# The standard canonical residue monomial

On the triple intersection the numerator x₀²w² is the (2,2) basis vector.
Dividing by x₁x₂x₃ shifts its Laurent exponent to (-1,-1,-1).

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace CycleQ2LiteralResidueMonomial

open MvPolynomial CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations
  CycleQ2SegreTangentLocal CycleQ2SeedQuotientFiniteFree CycleQ2SeedCechThreeOpen
  CycleQ2SeedCechLocalization CycleQ2SeedCechLocalizedBasis
  CycleQ2GeometricSurfaceCoordinates CycleQ2GeometricSeedNormalIdeals
  CycleQ2GeometricCoordinateCharacter CycleQ2GeometricLaurentTop CycleQ2CoordinateCechTrace

/-- The literal fraction in the original Laurent basis over the base coordinates. -/
theorem residueFraction_coordinates (r : ℂ) (ab : ShiftIndex) :
    coordinateLaurent r Finset.univ (polynomialFraction r 1 ((X 0)^2 * (X 4)^2)) ab =
      if ab = (2,2) then T ℂ (fun _ => -1) else 0 := by
  classical
  let p : Poly ℂ := (X 0)^2 * (X 4)^2
  let f := polynomialFraction r 1 p
  have h := congrArg (seedCoordinateEquiv r Finset.univ)
    (polynomialFraction_spec r 1 p)
  simp only [pow_one, map_mul, seedCoordinateEquiv_base, seedRingEquiv_coordinateProduct,
    seedRingEquiv_quotient] at h
  have hcoord := congrArg (fun z => localizedCoordinates ℂ r Complex.I Finset.univ z ab) h
  rw [seed_coordinates_mul_base, localizedCoordinates_algebraMap, baseToLaurent_baseProduct] at hcoord
  have hb := seedBasis_apply ℂ r Complex.I ((2,2) : ShiftIndex)
  change seedBasis ℂ r Complex.I (2,2) =
    Ideal.Quotient.mk _ ((X 0)^2 * (X 4)^2) at hb
  rw [← hb, Module.Basis.repr_self] at hcoord
  change T ℂ (openExponent Finset.univ) * coordinateLaurent r Finset.univ f ab = _ at hcoord
  change coordinateLaurent r Finset.univ f ab = _
  have hexp : openExponent Finset.univ + (fun _ => -1) = 0 := by
    ext i
    simp [openExponent]
  apply (T_isUnit ℂ (openExponent Finset.univ)).mul_right_injective
  dsimp only
  rw [hcoord]
  by_cases hab : ab = (2,2)
  · subst ab
    simp [T_mul, hexp]
  · simp [hab]

theorem residueFraction_trace :
    localCoefficient 57 Finset.univ (2,2) (fun _ => -1)
      (polynomialFraction 57 1 ((X 0)^2 * (X 4)^2)) = 1 := by
  change (coordinateLaurent 57 Finset.univ _ (2,2)).coeff (fun _ => -1) = 1
  rw [residueFraction_coordinates]
  simp [T, AddMonoidAlgebra.coeff_single]

end CycleQ2LiteralResidueMonomial
end

#print axioms CycleQ2LiteralResidueMonomial.residueFraction_coordinates
#print axioms CycleQ2LiteralResidueMonomial.residueFraction_trace
