import Proposal.CubicTraceDescent
import Proposal.SymmetricPrimitiveEndpoint

/-!
# The exact symmetric primitive from two source trace identities

All base-field objects below belong to the already constructed function
field of the protected reflection chart.  The source is the exact existing
`residueDensity`.  This module supplies a tightly bound endpoint for a
constructed moving-point current and its two coefficient traces.

It does not supply that current or prove the two trace equalities.  In
particular, it makes no primitive-existence assertion and does not replace
the admission in `Submission.relative_primitive_exists`.
-/

noncomputable section

namespace SymmetricTraceEndpoint

open MvPolynomial WeightedPrimitiveTransport SymmetricAffineField
open SymmetricPrimitiveEndpoint CubicTraceDescent
open scoped BigOperators

set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

def weightedMap : Poly →+* FunctionField := residueMap.comp squareLift

def normal : FunctionField := weightedMap (pderiv 4 rawWeighted)
def secondNormal : FunctionField := weightedMap (pderiv 4 (pderiv 4 rawWeighted))
def normalCoordinate : FunctionField := weightedMap (X 4)
def source : FunctionField := weightedMap rawSource
def sourceDerivative : FunctionField := weightedMap (pderiv 4 rawSource)

def leadingPolynomial : Poly :=
  2+2*X 0^6-C (5/7 : ℂ)*X 0^2-C (10/7 : ℂ)*X 0^4

def sourceQuadraticCoefficient : Poly := X 1*X 3*X 0^2

def normalCorrection : FunctionField :=
  weightedMap sourceQuadraticCoefficient / (3*weightedMap leadingPolynomial)

/-- The source after subtracting its quadratic coefficient times `f_u/(3ell)`.
The following formulas avoid any unproved coefficient transport. -/
def targetSource1 : FunctionField := sourceDerivative-normalCorrection*secondNormal

def targetSource0 : FunctionField :=
  source-normalCorrection*normal-targetSource1*normalCoordinate

theorem normal_nonzero : normal ≠ 0 := weighted_normal_nonzero

theorem squareLift_leading : squareLift leadingPolynomial = leadingPolynomial := by
  simp [leadingPolynomial, map_ofNat]

theorem normalPoint_leading : eval normalPoint leadingPolynomial = 2 := by
  norm_num [normalPoint, leadingPolynomial]

/-- The canonical source's new coefficient denominator is nonzero in the
actual chart field; its nonvanishing is witnessed at the existing smooth point. -/
theorem leading_nonzero : weightedMap leadingPolynomial ≠ 0 := by
  change residueMap (squareLift leadingPolynomial) ≠ 0
  rw [squareLift_leading, ne_eq, residueMap_kernel]
  intro hdiv
  have h := map_dvd (eval normalPoint) hdiv
  rw [normalPoint_equation, normalPoint_leading, zero_dvd_iff] at h
  norm_num at h

theorem target_source_sum :
    targetSource0+targetSource1*normalCoordinate = source-normalCorrection*normal := by
  unfold targetSource0
  ring

/-- The two displayed source coefficients reproduce the exact protected
relative density.  This equality is in its actual function field. -/
theorem residueDensity_eq_linearDensity :
    residueDensity = linearDensity normal secondNormal normalCoordinate targetSource0 targetSource1 := by
  change 2*(normal*sourceDerivative-secondNormal*source)/normal^3 = _
  rw [linearDensity, target_source_sum, targetSource1]
  have h := CubicSourceReconstruction.normal_source_gauge
    normal secondNormal source sourceDerivative normalCorrection
  exact congrArg (fun x : FunctionField => 2*x/normal^3) h.symm

variable {L : Type*} [Field L] [Algebra FunctionField L] [FiniteDimensional FunctionField L]

/-- A supplied upstairs current and its two exact trace matches construct
the original `RelativePrimitive`, with no geometric implication assumed. -/
def relativePrimitiveOfTrace
    (E : Fin 3 → Derivation ℤ L L)
    (compatible : ∀ i x, E i (algebraMap FunctionField L x) =
      algebraMap FunctionField L (tangent i.succ x))
    (s0 s1 : L) (w : Fin 3 → L)
    (hequation : (∑ i, E i (w i)) =
      linearDensity (algebraMap FunctionField L normal)
        (algebraMap FunctionField L secondNormal)
        (algebraMap FunctionField L normalCoordinate) s0 s1)
    (hsource0 : Algebra.normalizedTrace FunctionField L s0 = targetSource0)
    (hsource1 : Algebra.normalizedTrace FunctionField L s1 = targetSource1) :
    RelativePrimitive where
  coefficient := fun i => Algebra.normalizedTrace FunctionField L (w i)
  differential_eq := by
    rw [residueDensity_eq_linearDensity]
    exact finiteTrace_primitive_of_source_match (K := FunctionField) (L := L) (ι := Fin 3)
      (fun (i : Fin 3) => tangent i.succ) E compatible
      normal secondNormal normalCoordinate targetSource0 targetSource1
      s0 s1 w hequation hsource0 hsource1

end SymmetricTraceEndpoint

#print axioms SymmetricTraceEndpoint.leading_nonzero
#print axioms SymmetricTraceEndpoint.residueDensity_eq_linearDensity
#print axioms SymmetricTraceEndpoint.relativePrimitiveOfTrace
