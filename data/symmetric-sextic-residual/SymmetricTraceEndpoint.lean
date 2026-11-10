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

/-!
# The two exact trace targets are rational functions of the base coordinates

The canonical coefficients in `SymmetricTraceEndpoint` are defined inside
the full reflection-chart function field.  Here they are identified with
explicit quotients of polynomials in `(lambda,b,c,d)`.  Thus they belong to
the coefficient subfield, independently of the cubic normal coordinate.
These identities specify the two source traces required from a contact
current.  They do not construct that current or a relative primitive.

The chart, source reconstruction, and conditional trace endpoint are the
work of `fqlx`, `benediamond`, and their credited collaborators in the
upstream research drafts #222 and #223.  This coefficient-field binding
was prepared for `kmehltretter82` with OpenAI Codex assistance.  It extends
the existing research draft; the protected primitive-existence obligation
remains open.
-/

noncomputable section

namespace SymmetricTraceCoefficients

open MvPolynomial WeightedPrimitiveTransport SymmetricAffineField
open SymmetricTraceEndpoint

set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

abbrev BasePoly := MvPolynomial (Fin 4) ℂ

def coefficientLift : BasePoly →+* Poly := (rename Fin.castSucc).toRingHom

def coefficientMap : BasePoly →+* FunctionField := weightedMap.comp coefficientLift

def coefficientSubfield : Subfield FunctionField :=
  Subfield.closure (Set.range coefficientMap)

def leading : BasePoly :=
  2+2*X 0^6-C (5/7 : ℂ)*X 0^2-C (10/7 : ℂ)*X 0^4

def leftBase : BasePoly := 1+2*X 1
def rightBase : BasePoly := X 2^2+2*X 2*X 3

def constantCoefficient : BasePoly :=
  2+X 1^6+2*X 2^6+X 3^6+
    C (5/7 : ℂ)*leftBase^2*rightBase+
    C (10/7 : ℂ)*leftBase*rightBase^2

def linearCoefficient : BasePoly :=
  30+30*X 0^2*X 2^4+
    C (5/7 : ℂ)*(-X 0^2*leftBase^2-2*leftBase*rightBase)+
    C (10/7 : ℂ)*(-2*X 0^2*leftBase*rightBase-rightBase^2)

def quadraticCoefficient : BasePoly :=
  30+30*X 0^4*X 2^2+
    C (5/7 : ℂ)*(rightBase+2*X 0^2*leftBase)+
    C (10/7 : ℂ)*(X 0^4*leftBase+2*X 0^2*rightBase)

def sourceConstant : BasePoly := X 1*X 3*X 2^2
def sourceLinear : BasePoly := -X 1*X 3*(X 2^2+X 0^2)
def sourceQuadratic : BasePoly := X 1*X 3*X 0^2

def sourceNumerator0 : BasePoly :=
  3*leading*sourceConstant-sourceQuadratic*linearCoefficient

def sourceNumerator1 : BasePoly :=
  3*leading*sourceLinear-2*sourceQuadratic*quadraticCoefficient

theorem rawWeighted_coefficients :
    rawWeighted = coefficientLift leading*X 4^3+
      coefficientLift quadraticCoefficient*X 4^2+
      coefficientLift linearCoefficient*X 4+coefficientLift constantCoefficient := by
  simp [rawWeighted, leftQuadric, rightQuadric, coefficientLift,
    leading, quadraticCoefficient, linearCoefficient, constantCoefficient,
    leftBase, rightBase, map_ofNat]
  ring

theorem rawSource_coefficients :
    rawSource = coefficientLift sourceConstant+coefficientLift sourceLinear*X 4+
      coefficientLift sourceQuadratic*X 4^2 := by
  simp [rawSource, coefficientLift, sourceConstant, sourceLinear, sourceQuadratic]
  ring

theorem coefficientLift_leading : coefficientLift leading = leadingPolynomial := by
  simp [coefficientLift, leading, leadingPolynomial, map_ofNat]

theorem coefficientLift_sourceQuadratic :
    coefficientLift sourceQuadratic = sourceQuadraticCoefficient := by
  simp [coefficientLift, sourceQuadratic, sourceQuadraticCoefficient]

theorem coefficientLift_vars (p : BasePoly) : (4 : Fin 5) ∉ (coefficientLift p).vars := by
  intro h
  obtain ⟨i, _, hi⟩ := mem_vars_rename Fin.castSucc p h
  exact Fin.castSucc_ne_last i hi

theorem coefficientLift_normal (p : BasePoly) : pderiv 4 (coefficientLift p) = 0 :=
  pderiv_eq_zero_of_notMem_vars (coefficientLift_vars p)

theorem normal_coefficients :
    pderiv 4 rawWeighted = 3*coefficientLift leading*X 4^2+
      2*coefficientLift quadraticCoefficient*X 4+coefficientLift linearCoefficient := by
  simp [rawWeighted_coefficients, coefficientLift_normal]
  ring

theorem secondNormal_coefficients :
    pderiv 4 (pderiv 4 rawWeighted) =
      6*coefficientLift leading*X 4+2*coefficientLift quadraticCoefficient := by
  have htwo : (pderiv 4 : Derivation ℂ Poly Poly) 2 = 0 :=
    (pderiv 4 : Derivation ℂ Poly Poly).map_natCast 2
  have hthree : (pderiv 4 : Derivation ℂ Poly Poly) 3 = 0 :=
    (pderiv 4 : Derivation ℂ Poly Poly).map_natCast 3
  simp [normal_coefficients, coefficientLift_normal, htwo, hthree]
  ring

theorem sourceDerivative_coefficients :
    pderiv 4 rawSource = coefficientLift sourceLinear+2*coefficientLift sourceQuadratic*X 4 := by
  rw [rawSource_coefficients]
  simp only [map_add, pderiv_mul, pderiv_pow, coefficientLift_normal,
    pderiv_X_self, zero_mul, zero_add, mul_one,
    Nat.cast_ofNat]
  ring

theorem coefficient_leading_nonzero : coefficientMap leading ≠ 0 := by
  simpa only [coefficientMap, RingHom.comp_apply, coefficientLift_leading] using leading_nonzero

theorem targetSource1_coefficient_quotient :
    targetSource1 = coefficientMap sourceNumerator1 / coefficientMap (3*leading) := by
  unfold targetSource1 sourceDerivative normalCorrection secondNormal
  simp only [sourceDerivative_coefficients, secondNormal_coefficients,
    ← coefficientLift_sourceQuadratic, ← coefficientLift_leading, sourceNumerator1,
    coefficientMap, RingHom.comp_apply, map_sub, map_add, map_mul, map_ofNat]
  field_simp [show weightedMap (coefficientLift leading) ≠ 0 from coefficient_leading_nonzero]
  ring

theorem targetSource0_coefficient_quotient :
    targetSource0 = coefficientMap sourceNumerator0 / coefficientMap (3*leading) := by
  unfold targetSource0 targetSource1 source sourceDerivative normalCorrection normal secondNormal normalCoordinate
  rw [sourceDerivative_coefficients, secondNormal_coefficients]
  simp only [rawSource_coefficients, normal_coefficients,
    ← coefficientLift_sourceQuadratic, ← coefficientLift_leading, sourceNumerator0,
    coefficientMap, RingHom.comp_apply, map_sub, map_add, map_mul, map_pow, map_ofNat]
  field_simp [show weightedMap (coefficientLift leading) ≠ 0 from coefficient_leading_nonzero]
  ring

theorem coefficientMap_mem (p : BasePoly) : coefficientMap p ∈ coefficientSubfield :=
  Subfield.subset_closure (Set.mem_range_self p)

/-- The first exact source-trace target lies in the four-coordinate coefficient field. -/
theorem targetSource0_mem_coefficientSubfield : targetSource0 ∈ coefficientSubfield :=
  targetSource0_coefficient_quotient.symm ▸
    coefficientSubfield.div_mem (coefficientMap_mem _) (coefficientMap_mem _)

/-- The second exact source-trace target lies in the same coefficient field. -/
theorem targetSource1_mem_coefficientSubfield : targetSource1 ∈ coefficientSubfield :=
  targetSource1_coefficient_quotient.symm ▸
    coefficientSubfield.div_mem (coefficientMap_mem _) (coefficientMap_mem _)


end SymmetricTraceCoefficients

#print axioms SymmetricTraceCoefficients.targetSource0_coefficient_quotient
#print axioms SymmetricTraceCoefficients.targetSource1_coefficient_quotient
#print axioms SymmetricTraceCoefficients.targetSource0_mem_coefficientSubfield
#print axioms SymmetricTraceCoefficients.targetSource1_mem_coefficientSubfield
