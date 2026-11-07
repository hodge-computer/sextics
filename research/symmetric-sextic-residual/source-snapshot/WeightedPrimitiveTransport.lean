import WeightedPrimitiveTransportCore
import HodgeComputer.Constructions.HoldoutCover.FiniteResidueClearing
import HodgeComputer.Constructions.HoldoutCover.PolynomialCalculus

/-!
# Canonical finite residue clearing from a relative primitive

The sole geometric input is the three-coefficient relative primitive
identity. All tangent derivations are constructed from the actual quotient,
and the four-coordinate current is the explicit one proved in Core.
-/

noncomputable section
namespace WeightedPrimitiveTransport
open MvPolynomial HoldoutConstruction
open scoped BigOperators

set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

/-- The actual normal coordinate is v, at index four. -/
def normalPartial : Derivation ℤ Poly Poly := integerPartial (4 : Fin 5)

/-- The tangent coordinates are lambda, b, c, d, in that order. -/
def tangentPartial (i : Fin 4) : Derivation ℤ Poly Poly := integerPartial i.castSucc

/-- The unchanged coordinates differentiate through the reflection map. -/
theorem tangent_squareLift (i : Fin 4) (p : Poly) :
    pderiv i.castSucc (squareLift p) = squareLift (pderiv i.castSucc p) := by
  have hi : i.castSucc ≠ (4 : Fin 5) := Fin.castSucc_ne_last i
  induction p using MvPolynomial.induction_on with
  | C r => simp [pderiv_C]
  | add p q hp hq => simp [hp, hq]
  | mul_X p j hp =>
    by_cases hj : j = 4
    · subst j
      simp [pderiv_mul, pderiv_pow, hp, pderiv_X_of_ne hi.symm, hi]
    · by_cases hji : j = i.castSucc
      · subst j
        simp [pderiv_mul, hp, hi]
      · simp [pderiv_mul, hp, hj, hji]

section CanonicalTransport

variable {B K L : Type*} [CommRing B] [IsDomain B]
variable [Field K] [Algebra B K] [IsFractionRing B K] [CharZero K]
variable [Field L] [Algebra K L] [FiniteDimensional K L]

/-- The tangent derivations are the repository's constructed quotient-field
ones, not independent operators supplied by the primitive hypothesis. -/
def chartTangent (π : Poly →+* B) (hsurj : Function.Surjective π)
    (hkernel : ∀ p, π p = 0 ↔ chartEquation ∣ p)
    (hg : algebraMap B K (π (normalPartial chartEquation)) ≠ 0)
    (i : Fin 4) : Derivation ℤ K K :=
  residueTangent π hsurj normalPartial (tangentPartial i) chartEquation hkernel hg

/-- On pulled-back weighted polynomials, the actual physical tangent acts by
exactly the weighted implicit-derivative formula. The factor `2*v` cancels;
compatibility of the reflection cover is proved, not supplied as an input. -/
theorem chartTangent_squareLift (π : Poly →+* B) (hsurj : Function.Surjective π)
    (hkernel : ∀ p, π p = 0 ↔ chartEquation ∣ p)
    (hg : algebraMap B K (π (normalPartial chartEquation)) ≠ 0)
    (i : Fin 4) (p : Poly) :
    chartTangent π hsurj hkernel hg i (algebraMap B K (π (squareLift p))) =
      algebraMap B K (π (squareLift (pderiv i.castSucc p))) -
      algebraMap B K (π (squareLift (pderiv i.castSucc rawWeighted))) /
        algebraMap B K (π (squareLift (pderiv 4 rawWeighted))) *
        algebraMap B K (π (squareLift (pderiv 4 p))) := by
  let σ : Poly →+* K := (algebraMap B K).comp π
  obtain ⟨hv,hu⟩ := normal_nonzero_factors σ rawWeighted hg
  rw [chartTangent, residueTangent_apply]
  change σ (pderiv i.castSucc (squareLift p)) -
    σ (pderiv i.castSucc (squareLift rawWeighted)) /
      σ (pderiv 4 (squareLift rawWeighted)) *
      σ (pderiv 4 (squareLift p)) =
    σ (squareLift (pderiv i.castSucc p)) -
      σ (squareLift (pderiv i.castSucc rawWeighted)) /
        σ (squareLift (pderiv 4 rawWeighted)) *
        σ (squareLift (pderiv 4 p))
  simp only [tangent_squareLift, normal_squareLift, map_mul, map_ofNat]
  field_simp
  <;> ring

/-- The field current computed from the three primitive coefficients. -/
def chartCurrent (π : Poly →+* B) (beta : Fin 3 → L) : Fin 4 → L :=
  relativeCurrent
    (algebraMap K L (algebraMap B K (π (normalPartial chartEquation)))) beta

/-- Exact canonical residue equation from the relative two-form primitive.
The primitive source is the explicit protected numerator residue coefficient. -/
theorem canonical_current_equation (π : Poly →+* B)
    (hsurj : Function.Surjective π)
    (hkernel : ∀ p, π p = 0 ↔ chartEquation ∣ p)
    (hg : algebraMap B K (π (normalPartial chartEquation)) ≠ 0)
    (beta : Fin 3 → L)
    (hprimitive :
      (∑ i : Fin 3, extendFiniteDerivation (L := L)
        (chartTangent π hsurj hkernel hg i.succ) (beta i)) =
      algebraMap K L (residueCoefficient ((algebraMap B K).comp π)
        rawWeighted rawSource)) :
    let E' := fun i => extendFiniteDerivation (L := L)
      (chartTangent π hsurj hkernel hg i)
    let g := algebraMap B K (π (normalPartial chartEquation))
    algebraMap K L
      ((algebraMap B K (π (normalPartial chartSource)) * g -
        algebraMap B K (π chartSource) *
          algebraMap B K (π (normalPartial (normalPartial chartEquation)))) / g^2) +
      ∑ i : Fin 4, (E' i (chartCurrent (K := K) π beta i) -
        chartCurrent (K := K) π beta i * E' i (algebraMap K L g) /
          algebraMap K L g) = 0 := by
  letI : CharZero L := charZero_of_injective_algebraMap (algebraMap K L).injective
  let σ : Poly →+* K := (algebraMap B K).comp π
  let g := algebraMap B K (π (normalPartial chartEquation))
  let rho := residueCoefficient σ rawWeighted rawSource
  let E' := fun i => extendFiniteDerivation (L := L)
    (chartTangent π hsurj hkernel hg i)
  have hg' : algebraMap K L g ≠ 0 := (map_ne_zero (algebraMap K L)).mpr hg
  have heq := relativeCurrent_equation E' (algebraMap K L g)
    (algebraMap K L rho) beta hg' hprimitive
  have hsource :
      (algebraMap B K (π (normalPartial chartSource)) * g -
        algebraMap B K (π chartSource) *
          algebraMap B K (π (normalPartial (normalPartial chartEquation)))) / g^2 =
        g*rho := by
    exact exact_reflected_residue_scalar σ rawWeighted rawSource hg
  change algebraMap K L _ + ∑ i : Fin 4,
    (E' i (relativeCurrent (algebraMap K L g) beta i) -
      relativeCurrent (algebraMap K L g) beta i * E' i (algebraMap K L g) /
        algebraMap K L g) = 0
  rw [hsource, map_mul]
  exact heq

/-- A relative primitive produces legal polynomial data on the exact affine
reflection chart. The finite extension is removed by normalized trace.
Existence of the primitive, not a game identity, is the only differential
input. Irreducibility is a separate algebraic chart fact. -/
theorem exact_chart_clearing_of_relative_primitive (π : Poly →+* B)
    (hsurj : Function.Surjective π)
    (hkernel : ∀ p, π p = 0 ↔ chartEquation ∣ p)
    (hirred : Irreducible chartEquation)
    (hg : algebraMap B K (π (normalPartial chartEquation)) ≠ 0)
    (beta : Fin 3 → L)
    (hprimitive :
      (∑ i : Fin 3, extendFiniteDerivation (L := L)
        (chartTangent π hsurj hkernel hg i.succ) (beta i)) =
      algebraMap K L (residueCoefficient ((algebraMap B K).comp π)
        rawWeighted rawSource)) :
    ∃ D Nv : Poly, ∃ N : Fin 4 → Poly, ∃ Q : Poly,
      D ≠ 0 ∧ IsRelPrime chartEquation D ∧
      (Nv * normalPartial chartEquation +
        ∑ i, N i * tangentPartial i chartEquation = chartSource * D) ∧
      (residueDivNum normalPartial tangentPartial D Nv N = chartEquation * Q) ∧
      chartSource * D^2 - D * (Nv * normalPartial chartEquation +
        ∑ i, N i * tangentPartial i chartEquation) +
        chartEquation * residueDivNum normalPartial tangentPartial D Nv N =
          chartEquation^2 * Q := by
  let E := chartTangent π hsurj hkernel hg
  let E' := fun i => extendFiniteDerivation (L := L) (E i)
  refine finite_residue_solution_clearing π hsurj normalPartial tangentPartial
    E E' chartEquation chartSource (chartCurrent (K := K) π beta)
    hirred hkernel hg ?_ ?_ ?_ ?_
  · intro i
    exact integerPartial_commute i.castSucc (4 : Fin 5) chartEquation
  · intro i p
    exact residueTangent_apply π hsurj normalPartial (tangentPartial i)
      chartEquation hkernel hg p
  · intro i x
    exact extendFiniteDerivation_apply (E i) x
  · exact canonical_current_equation π hsurj hkernel hg beta hprimitive

end CanonicalTransport

#print axioms tangent_squareLift
#print axioms chartTangent_squareLift
#print axioms canonical_current_equation
#print axioms exact_chart_clearing_of_relative_primitive

end WeightedPrimitiveTransport
