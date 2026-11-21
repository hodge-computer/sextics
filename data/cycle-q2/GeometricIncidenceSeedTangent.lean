import Proposal.GeometricIncidenceEtaleParameter
import Proposal.GeometricCanonicalCurveImage

/-!
# The actual seed tangent and its original canonical curve class

The regular time vector field on the constructed parameter algebra is
specialized at its actual complex seed. Differentiating the original
incidence equations and using the retained identity Jacobian shows that
the slice-coordinate velocities vanish there. Consequently the complete
seed velocity is exactly the original chosen trace-one parameterDirection.

This equality transports the existing normal trace and the fixed canonical
curve pairing to the derivative of the actual algebraic family. The
canonical residue connecting map is nonzero on that original paired curve
class. It is not identified here with the derivative of a cycle-class,
Abel--Jacobi, or Gysin map; that geometric comparison is still needed.

The geometric strategy is due to Ben Diamond and the cited work of Claire
Voisin. Prepared for fqlx with OpenAI ChatGPT assistance.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2IncidenceSeedTangent

open MvPolynomial Matrix
open CycleQ2IncidenceNormalForm CycleQ2IncidenceMonomials
  CycleQ2IncidenceUniversalChart CycleQ2IncidenceCoefficientRelations
  CycleQ2IncidencePolynomialRelations CycleQ2IncidencePolynomialJacobianBinding
  CycleQ2PolynomialAffineSlice CycleQ2IncidenceTraceFamily
  CycleQ2IncidenceTraceDirection CycleQ2IncidenceTraceDerivative
  CycleQ2IncidenceTraceGeometry CycleQ2IncidenceCompatibleGenericPoint
  CycleQ2IncidenceEtaleParameter CycleQ2SegreModularDetectorMatrixBinding

@[simp] theorem seedMap_complex (a : ℂ) :
    seedMap (algebraMap ℂ ParameterAlgebra a) = a := by
  rw [IsScalarTower.algebraMap_apply ℂ TraceRing ParameterAlgebra,
    seedMap_algebraMap]
  simp [seedEvaluation]

theorem seedMap_polynomial (p : ParameterPolynomial ℂ) :
    seedMap (aeval incidencePoint p) = eval (seedPoint (57 : ℂ) Complex.I) p := by
  have h : seedMap.comp (aeval incidencePoint).toRingHom =
      eval (seedPoint (57 : ℂ) Complex.I) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      change seedMap (aeval incidencePoint (C a)) =
        eval (seedPoint (57 : ℂ) Complex.I) (C a)
      rw [aeval_C, eval_C]
      exact seedMap_complex a
    · intro j
      change seedMap (aeval incidencePoint (X j)) =
        eval (seedPoint (57 : ℂ) Complex.I) (X j)
      rw [aeval_X, eval_X]
      exact seedMap_incidencePoint j
  exact RingHom.congr_fun h p

def seedVelocity (j : ParameterIndex) : ℂ :=
  seedMap (timeDerivation (incidencePoint j))

def seedSliceVelocity (j : SquareIndex) : ℂ :=
  seedMap (timeDerivation (sliceCoordinate j))

theorem seedVelocity_affine :
    seedVelocity = parameterDirection +
      CycleQ2IncidenceSexticFamily.extendDirections splitting.B *ᵥ seedSliceVelocity := by
  funext j
  have h := derivative_point timeDerivation timeDerivation_traceParameter
    timeDerivation_sexticParameter splitting.B sliceCoordinate j
  have hm := congrArg seedMap h
  simpa only [incidencePoint, seedVelocity, seedSliceVelocity,
    map_add, map_sum, map_mul, seedMap_complex, Matrix.mulVec,
    Matrix.map_apply, dotProduct, Pi.add_apply] using hm

theorem seedVelocity_kernel :
    seedJacobian ℂ (57 : ℂ) Complex.I *ᵥ seedVelocity = 0 := by
  have he (q : ColumnIndex) : aeval incidencePoint ((presentation ℂ 57).equation q) = 0 :=
    tracePoint_original_equations splitting.P splitting.B _ sliceCoordinate
      incidence_isTracePoint q
  have hd := CycleQ2PolynomialDerivationChainRule.differentiated_equations
    timeDerivation incidencePoint (presentation ℂ 57).equation he
  funext q
  have hq := congrArg seedMap (congrFun hd q)
  change (∑ j, eval (seedPoint (57 : ℂ) Complex.I)
    (pderiv j ((presentation ℂ 57).equation q)) * seedVelocity j) = 0
  simpa only [jacobian, Matrix.mulVec, dotProduct, map_sum, map_mul,
    map_zero, Pi.zero_apply, ← aeval_eq_eval₂Hom, seedMap_polynomial, seedVelocity] using hq

/-- The actual chosen finite splitting has identity retained Jacobian at
the literal seed, including the unchanged fixed-sextic embedding. -/
theorem retained_seed_identity :
    splitting.P * seedJacobian ℂ (57 : ℂ) Complex.I *
      CycleQ2IncidenceSexticFamily.extendDirections splitting.B = 1 := by
  rw [Matrix.mul_assoc, CycleQ2IncidenceSexticFamily.jacobian_extendDirections,
    ← Matrix.mul_assoc]
  exact splitting.jacobian

theorem seedSliceVelocity_zero : seedSliceVelocity = 0 := by
  have h := seedVelocity_kernel
  rw [seedVelocity_affine, Matrix.mulVec_add, parameterDirection_kernel, zero_add] at h
  have hp := congrArg (fun v => splitting.P *ᵥ v) h
  simp only [Matrix.mulVec_mulVec, Matrix.mulVec_zero] at hp
  simpa only [← Matrix.mul_assoc, retained_seed_identity, Matrix.one_mulVec] using hp

/-- The actual regular family has precisely the previously chosen
trace-one tangent at the original seed. -/
theorem seedVelocity_eq_parameterDirection : seedVelocity = parameterDirection := by
  rw [seedVelocity_affine, seedSliceVelocity_zero, Matrix.mulVec_zero, add_zero]

theorem seed_trace_one : traceWeights ⬝ᵥ seedVelocity = 1 := by
  rw [seedVelocity_eq_parameterDirection]
  exact traceWeights_parameterDirection

def seedCubicCoordinates (j : Fin 9) : ℂ := seedVelocity (Sum.inl (cubicIndex j))

theorem seedCubic_trace_one :
    CycleQ2SeedCechTheta.derivativeTrace 1 seedCubicCoordinates = 1 := by
  change CycleQ2SeedCechTheta.derivativeTrace 1
    (fun j => seedVelocity (Sum.inl (cubicIndex j))) = 1
  rw [seedVelocity_eq_parameterDirection]
  exact traceWeights_eq_checked_seed_trace.symm.trans traceWeights_parameterDirection

/-- The sign and factor of the existing original normal trace are
retained for the cubic velocity of the actual family. -/
theorem seed_normal_trace :
    CycleQ2NormalConnecting.pairedNormalTrace 57 1 (by norm_num)
      (CycleQ2SeedTrace.substitute
        (fullInvariantPolynomial 3 (fun j => seedVelocity (Sum.inl j)))) = -1 / 171 := by
  rw [seedVelocity_eq_parameterDirection]
  exact parameterCubic_normal_trace

open CycleQ2GeometricLiteralHOne CycleQ2CanonicalCurveImage

/-- The actual original paired canonical curve class for this seed
velocity, with the preexisting normalization of H¹(C, Ω¹_C). -/
def seedPairedCanonicalClass : CurveHOne :=
  literalPairedCanonicalLinear seedCubicCoordinates

theorem seedPairedCanonicalCoordinate :
    literalCanonicalCoordinate seedPairedCanonicalClass = (12 + 24 * Complex.I) / 5 := by
  rw [seedPairedCanonicalClass, literalCanonicalCoordinate_paired, seedCubic_trace_one, mul_one]

theorem seedPairedCanonicalClass_ne_zero : seedPairedCanonicalClass ≠ 0 := by
  intro h
  have ht := (literalPairedCanonicalLinear_eq_zero_iff seedCubicCoordinates).mp h
  rw [seedCubic_trace_one] at ht
  exact one_ne_zero ht

/-- The already constructed canonical residue connecting map detects the
paired curve class belonging to the actual seed tangent. This does not
replace the still-needed geometric cycle-derivative comparison. -/
theorem seed_canonical_connecting_ne_zero :
    canonicalConnectingOnCurve seedPairedCanonicalClass ≠ 0 := by
  intro h
  exact seedPairedCanonicalClass_ne_zero
    (canonicalConnectingOnCurve_injective
      (h.trans canonicalConnectingOnCurve.map_zero.symm))

end CycleQ2IncidenceSeedTangent

#print axioms CycleQ2IncidenceSeedTangent.seedVelocity_eq_parameterDirection
#print axioms CycleQ2IncidenceSeedTangent.seed_normal_trace
#print axioms CycleQ2IncidenceSeedTangent.seed_canonical_connecting_ne_zero

end
