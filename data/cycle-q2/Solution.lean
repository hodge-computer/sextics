import Proposal.SolutionSupport09
import Proposal.GeometricSeedSmooth
import Proposal.GeometricProjector
import Proposal.GeometricExistence
import Proposal.GeometricSerre
import Proposal.GeometricVariation
import Proposal.GeometricConeCech
import Proposal.GeometricPrincipalRestriction
import Proposal.GeometricProjectiveCurve

/-! Source partition of Solution.lean. See solution.md for verification status. -/

set_option Elab.async false

/-!
Nonconstructive geometric route for the unchanged cycle-q2 target.

DRAFT: the algebraic residue-to-certificate bridge is proved and bound to the
actual projective affine chart. The genuine relative exterior forms, their
degree-three derivative, the local formal residue density, and the actual
universal exterior pullback are now proved. Specialization from the actual
generic pencil and descent through finite extensions are also proved.
The concrete incidence equations, their universal polynomial relations,
and the actual sparse and theta-one seed Cech residue calculations are proved.
The actual complex basepoint cover, graded local factor sequences, curve
restriction kernels, and positive graded linkage-ideal Cech vanishing are
also proved. The actual combined Jacobian has rank 1922, its image is the
kernel of the actual relation matrix, and the seven-dimensional obstruction
is identified with the actual scalar Cech class. A characteristic-zero
fixed-sextic tangent with trace one is obtained nonconstructively by an
augmented Gaussian matrix rank argument. Its geometric Abel--Jacobi and
global support comparisons are separate obligations.
Exact characteristic-zero identities now prove the actual cubic gradient
condition and a normal-Jacobian cover of every relevant prime of the r=57
seed curve. Actual local derivations on the minor-localized trace-family
surface extend the coefficient motion. The Segre transition cocycle's
logarithmic variation satisfies the relative Kodaira--Spencer contraction
identity, with the degree twist retained.
The seed normal coordinates are realized by bases of the genuine ideal
cotangent module on every relevant prime chart; the existing normal matrix
is bound to evaluation on the actual defining-equation classes.
The written classical existence argument is recorded in solution.md.
Its final Lean formalization remains open. The source-only continuation
adds a smooth-member gradient witness in the actual fixed-r seed family,
positive-adjoint rational projectors, the affine-curve filtration argument,
and the actual rational cochain complex with its top homology comparison.
The next continuation constructs the genuine smooth affine Jacobian open
and its further principal opens, their regular differential bases, the
actual graded normal Cech pairing, and a paired Fermat Jacobian Higgs model.
The subsequent source constructs genuine restriction maps and a filtered
diagram of regular de Rham complexes on the principal-open basis. Finite
denominators identify its top-cohomology colimit with the original generic
quotient. The normal calculation also reaches actual structure-sheaf
sections on the punctured curve cone and their Cech complex. The genuine
Mayer--Vietoris boundary injects the resulting section quotient into
derived sheaf H^1, preserving the selected nonzero classes, including
the actual trace-one incidence tangent at theta = 1 and literal r = 57.
The curve quotient grading and its genuine projective spectrum with
the two specific affine denominator charts are also constructed. The
degree-one localized modules, their affine frames, and the actual
transition unit now define a genuine additive sheaf on this projective
curve. Its section comparison and Mayer--Vietoris boundary preserve the
nonzero incidence class in actual derived projective H^1. The weighted
incidence surface and generic-section zero locus are also actual Proj
schemes, with maps to their bases and ambient schemes and an exact
binding to the previous polynomial section ideal. Their flatness,
smooth curve fibers, and divisor-class identification remain open.
The projective Serre and moving-curve interpretations, geometric variation,
supported correspondences, and analytic de Rham comparison remain to be
constructed. These new helpers have not been compiled.
The admission below is that precise existence obligation, not a routine
tactic gap. The protected theorem still depends on sorryAx. No completed
solve is claimed.

The previous explicit-current development is archived at commit
2cb80949c1d060bd884bef43cae335ee188d245e and is outside the active proposal.
-/

noncomputable section
namespace CycleQ2Nonconstructive

/-- The actual remaining geometric obligation in the chart X0 = 1.
The field is Frac(C[x0,...,x4]/(F(1,x))). Its four tangent derivations and
normal-source coefficient are concrete definitions, not assumed operators
or identities. A nonconstructive existence proof suffices. -/
def AffineResiduePrimitiveExists : Prop :=
  ∃ w : Fin 4 → CycleQ2AffineHypersurface.AffineFunctionField,
    CycleQ2AffineResidueClosure.affineResidueExpression
      CycleQ2AffineClearing.affineA w = 0

/-- The equivalent remaining assertion in genuine mathlib exterior powers
of the actual relative Kaehler module over the complex numbers. -/
def AffineResidueFormExact : Prop :=
  ∃ η : CycleQ2AffineExterior.Form 3,
    CycleQ2AffineExterior.exteriorD3 η =
      CycleQ2AffineExactness.residueSourceForm CycleQ2AffineClearing.affineA

theorem exact_form_iff_primitive :
    AffineResidueFormExact ↔ AffineResiduePrimitiveExists :=
  CycleQ2AffineExactness.exact_residueSourceForm_iff CycleQ2AffineClearing.affineA

/-- The geometric support argument may be carried out on any sufficiently
small nonempty principal open. This equivalence is supplied by actual
restriction and finite-denominator constructions; it does not assert
vanishing on such an open. The new source has not been compiled. -/
theorem exact_form_iff_regular_zero :
    AffineResidueFormExact ↔
      ∃ s : CycleQ2GeometricRegularDeRham.OpenRing, s ≠ 0 ∧
        CycleQ2GeometricRegularDeRham.residueClass s = 0 :=
  CycleQ2GeometricRationalSpread.protected_exact_iff_exists_regular_zero

end CycleQ2Nonconstructive

namespace Submission

/-- UNPROVED IN LEAN: establish actual exterior-form exactness from geometric support
and global algebraic de Rham comparison, or prove this existential directly.
The checked finite seed/Higgs calculations alone do not supply this theorem.
All subsequent algebraic steps to the protected target are proved. -/
theorem missing_geometric_existence :
    CycleQ2Nonconstructive.AffineResidueFormExact := by
  sorry

theorem certificate :
    HodgeComputer.HasCertificate HodgeSubmission.F HodgeSubmission.q HodgeSubmission.A := by
  exact CycleQ2AffineExactness.protected_certificate_of_exact_residueSourceForm
    missing_geometric_existence

end Submission

#print axioms CycleQ2Nonconstructive.exact_form_iff_primitive
#print axioms CycleQ2AffineExactness.protected_certificate_of_exact_residueSourceForm
#print axioms CycleQ2FormalResidue.residueSourceForm_eq_formalResidue
#print axioms CycleQ2NormalChart.exteriorPullback_ambientCoordinateVolume
#print axioms CycleQ2AffineWeightedTransfer.protected_certificate_of_relative_primitive
#print axioms CycleQ2GenericSpecialization.protected_certificate_of_generic_relative_primitive
#print axioms CycleQ2GenericFiniteSpecialization.protected_certificate_of_finite_generic_primitive
#print axioms CycleQ2IncidencePolynomialRelations.seed_relations_jacobian
#print axioms CycleQ2SeedCech.cechBoundary_iff_trace_zero
#print axioms CycleQ2SeedCechTheta.nonboundary_of_derivativeTrace_ne_zero
#print axioms CycleQ2SegreComplexBasepoint.prime_pivot_cover
#print axioms CycleQ2SeedLinkageRegular.linkage_mul_injective
#print axioms CycleQ2CurveRestriction.left_restriction_surjective
#print axioms CycleQ2CurveRestriction.right_restriction_surjective
#print axioms CycleQ2SeedLinkageRestrictionKernel.homogeneous_mem_linkage_iff_restriction_zero
#print axioms CycleQ2SeedLinkageCechVanishing.left_idealCechExact
#print axioms CycleQ2SeedLinkageCechVanishing.right_idealCechExact
#print axioms CycleQ2SegreGlobalObstruction.relationObstructionInjection_injective
#print axioms CycleQ2SeedGlobalFactorExact.entry_kernel_eq_factor_image
#print axioms CycleQ2SeedGlobalFactorExact.entryJacobianBlock_rank
#print axioms CycleQ2SegreGlobalObstruction.relationObstruction_finrank_le_seven
#print axioms CycleQ2SegreActualRelationRank.literal_coefficient_matrix_rank_lower_bound
#print axioms CycleQ2SegreExactRanks.fixedSexticJacobian_rank
#print axioms CycleQ2SegreExactRanks.fixed_range_eq_relation_kernel
#print axioms CycleQ2SegreExactRanks.literal_coefficient_matrix_rank
#print axioms CycleQ2SegreExactRanks.relationObstructionEquivH2
#print axioms CycleQ2SegreTangentProjection.tangentProjection_surjective
#print axioms CycleQ2SegreNonconstructiveTangent.exists_actual_trace_one_tangent
#print axioms CycleQ2IncidenceTraceDirection.parameterCubic_not_boundary
#print axioms CycleQ2IncidenceTraceDirection.parameterCubic_normal_trace
#print axioms CycleQ2IncidenceBasepointOpen.specialized_prime_pivot_cover
#print axioms CycleQ2GenericSexticGradient.nonzero_gradient_of_injective
#print axioms CycleQ2IncidenceCertifiedGenericPoint.finite_generic_incidence
#print axioms CycleQ2IncidenceCertifiedGenericPoint.finite_pointed_trace_point
#print axioms CycleQ2IncidenceTraceGenericPoint.tracePoint_normalized_derivative_isUnit
#print axioms CycleQ2SeedCubicGradient.nonzero_gradient_over_complex_extension
#print axioms CycleQ2SeedCurveGradient.weighted_prime_normal_cover
#print axioms CycleQ2SeedCurveGradient.weighted_field_normal_cover
#print axioms CycleQ2ConormalJacobian.actualConormalBasis
#print axioms CycleQ2ConormalJacobian.surfaceConormalBasisOnFirstOpen
#print axioms CycleQ2ConormalJacobian.actualEquationNormalMap_eq
#print axioms CycleQ2ConormalCover.exists_actual_conormal_basis
#print axioms CycleQ2LocalizationDerivation.extend_unique
#print axioms CycleQ2PolynomialCoefficientDerivation.coefficientDerivation_monomial
#print axioms CycleQ2SurfaceLocalDerivations.surfaceDerivation_on_constants
#print axioms CycleQ2IncidenceLocalDerivations.time_actualF
#print axioms CycleQ2IncidenceLocalDerivations.actualLocalTime_coefficients
#print axioms CycleQ2SegreKodairaSpencer.twisted_boundary_eq_contraction
#print axioms CycleQ2RelativeKodairaSpencer.boundary_eq_relative_contraction
#print axioms Submission.certificate
