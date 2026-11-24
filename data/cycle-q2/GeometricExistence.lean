import Proposal.GeometricDeRham
import Proposal.GeometricLeray
import Proposal.GeometricRegularDeRham

/-!
# Assembly of the geometric support and affine comparison steps

Source-only continuation of the written proof, Parts III.5 and IV.4--6.
No compilation has been run for this file.

The affine algebraic de Rham comparison must be made on an actual smooth
affine open. Its source is the cohomology of regular forms on that open;
restriction to the function field is a second map. An injective map from
arbitrary rational-form cohomology into the cohomology of one fixed open
is neither assumed nor needed.

The theorem below combines the proved linear Leray argument with this
correct comparison direction and the genuine rational-form complex. Its
geometric inputs remain explicit. In particular, this file does not provide
a geometric comparison, a supported relative correspondence, or a proof of
`Submission.missing_geometric_existence`.

The later regular-open specialization uses the constructed smooth affine
localization, its genuine regular forms, and the actual protected residue.
Its map to generic-point cohomology and its source-binding identity are
proved by `GeometricRegularDeRham`; they are not extra input hypotheses.
-/

set_option autoImplicit false

noncomputable section

namespace CycleQ2GeometricExistence

open CycleQ2AffineExterior

variable {Regular Betti H : Type*}
variable [AddCommGroup Regular] [Module ℂ Regular]
variable [AddCommGroup Betti] [Module ℂ Betti]
variable [AddCommGroup H] [Module ℂ H]

/-- The two distinct maps required in Part IV.6. `Regular` is to be
realized as the algebraic de Rham cohomology of the chosen affine open;
`Betti` as its complex cohomology. This structure records the necessary
data, and does not assert that such geometric data have been constructed. -/
structure AffineComparison (Regular Betti : Type*)
    [AddCommGroup Regular] [Module ℂ Regular]
    [AddCommGroup Betti] [Module ℂ Betti] where
  comparison : Regular →ₗ[ℂ] Betti
  comparison_injective : Function.Injective comparison
  toGeneric : Regular →ₗ[ℂ] CycleQ2GeometricDeRham.complex.homology 4

/-- Vanishing on the chosen affine open gives the exact rational primitive.
The class representing the protected source must be bound to both the
Betti restriction and the actual generic-point residue class. -/
theorem exact_of_affine_comparison
    (C : AffineComparison Regular Betti) (a : Regular)
    (hcomparison : C.comparison a = 0)
    (hsource : C.toGeneric a = CycleQ2GeometricDeRham.residueClass) :
    ∃ η : Form 3, exteriorD3 η =
      CycleQ2AffineExactness.residueSourceForm CycleQ2AffineClearing.affineA := by
  have ha : a = 0 := C.comparison_injective (by
    simpa only [map_zero] using hcomparison)
  apply CycleQ2GeometricDeRham.residueClass_eq_zero_iff.mp
  rw [← hsource, ha, map_zero]

/-- The full source-exactness conclusion of Parts IV.4--6 once the actual
geometric realizations have been supplied. The support conclusion is
derived from the edge splitting and the vanishing next filtration piece;
it is not an assumed zero class of the protected rational form.

There is no closed application of this theorem to the protected variety
yet. Its comparison, invariant submodule, edge map, hyperplane lift,
correspondence and restriction maps must all be constructed geometrically. -/
theorem exact_of_leray_and_affine_comparison
    (edge : H →ₗ[ℂ] ℂ) (hyperplane : H)
    (hedge : edge hyperplane = 1)
    (invariants next : Submodule ℂ H)
    (hhyperplane_invariant : hyperplane ∈ invariants)
    (hnext : next = ⊥)
    (restriction : H →ₗ[ℂ] Betti) (projector : Module.End ℂ H)
    (hgraded : ∀ x ∈ invariants ⊓ LinearMap.ker edge,
      next.mkQ (projector x) = next.mkQ x)
    (hsupport : restriction.comp projector = 0)
    (hhyperplane_support : restriction hyperplane = 0)
    (x : H) (hinvariant : x ∈ invariants)
    (C : AffineComparison Regular Betti) (a : Regular)
    (hcomparison : C.comparison a = restriction x)
    (hsource : C.toGeneric a = CycleQ2GeometricDeRham.residueClass) :
    ∃ η : Form 3, exteriorD3 η =
      CycleQ2AffineExactness.residueSourceForm CycleQ2AffineClearing.affineA := by
  have hzero : restriction x = 0 :=
    CycleQ2GeometricLeray.invariant_class_restriction_eq_zero
      edge hyperplane hedge invariants next hhyperplane_invariant hnext
      restriction projector hgraded hsupport hhyperplane_support hinvariant
  exact exact_of_affine_comparison C a (hcomparison.trans hzero) hsource

/-- The existing algebraic certificate constructor composes with the
geometric assembly, retaining every geometric hypothesis. -/
theorem certificate_of_leray_and_affine_comparison
    (edge : H →ₗ[ℂ] ℂ) (hyperplane : H)
    (hedge : edge hyperplane = 1)
    (invariants next : Submodule ℂ H)
    (hhyperplane_invariant : hyperplane ∈ invariants)
    (hnext : next = ⊥)
    (restriction : H →ₗ[ℂ] Betti) (projector : Module.End ℂ H)
    (hgraded : ∀ x ∈ invariants ⊓ LinearMap.ker edge,
      next.mkQ (projector x) = next.mkQ x)
    (hsupport : restriction.comp projector = 0)
    (hhyperplane_support : restriction hyperplane = 0)
    (x : H) (hinvariant : x ∈ invariants)
    (C : AffineComparison Regular Betti) (a : Regular)
    (hcomparison : C.comparison a = restriction x)
    (hsource : C.toGeneric a = CycleQ2GeometricDeRham.residueClass) :
    HodgeComputer.HasCertificate
      HodgeSubmission.F HodgeSubmission.q HodgeSubmission.A :=
  CycleQ2AffineExactness.protected_certificate_of_exact_residueSourceForm
    (exact_of_leray_and_affine_comparison
      edge hyperplane hedge invariants next hhyperplane_invariant hnext
      restriction projector hgraded hsupport hhyperplane_support x hinvariant
      C a hcomparison hsource)

/-- Specialization to the genuine regular de Rham quotient of a constructed
affine open. The protected regular residue and its map to the original
function-field class are fixed by the preceding construction.

The remaining comparison must be the geometric comparison on this same
open. Its injectivity and the zero comparison class are still hypotheses;
this theorem does not construct them. -/
theorem exact_of_regular_open_comparison
    (s : CycleQ2GeometricRegularDeRham.OpenRing) (hs : s ≠ 0)
    (comparison : CycleQ2GeometricRegularDeRham.TopDeRham s →ₗ[ℂ] Betti)
    (hinjective : Function.Injective comparison)
    (hzero : comparison (CycleQ2GeometricRegularDeRham.residueClass s) = 0) :
    ∃ η : Form 3, exteriorD3 η =
      CycleQ2AffineExactness.residueSourceForm CycleQ2AffineClearing.affineA := by
  have hregular : CycleQ2GeometricRegularDeRham.residueClass s = 0 :=
    hinjective (by simpa only [map_zero] using hzero)
  have hgeneric := congrArg (CycleQ2GeometricRegularDeRham.toGeneric s hs) hregular
  apply (CycleQ2AffineTopCohomology.residueClass_eq_zero_iff
    CycleQ2AffineClearing.affineA).mp
  simpa only [CycleQ2GeometricRegularDeRham.toGeneric_residueClass, map_zero]
    using hgeneric

/-- The Leray/support argument now assembles with a specific regular
residue class on any further nonempty principal open. No arbitrary
regular class, generic-point map, or residue-binding premise is supplied.
The actual geometric comparison, class, correspondence and support
properties still need construction. -/
theorem exact_of_regular_open_leray
    (s : CycleQ2GeometricRegularDeRham.OpenRing) (hs : s ≠ 0)
    (comparison : CycleQ2GeometricRegularDeRham.TopDeRham s →ₗ[ℂ] Betti)
    (hinjective : Function.Injective comparison)
    (edge : H →ₗ[ℂ] ℂ) (hyperplane : H)
    (hedge : edge hyperplane = 1)
    (invariants next : Submodule ℂ H)
    (hhyperplane_invariant : hyperplane ∈ invariants)
    (hnext : next = ⊥)
    (restriction : H →ₗ[ℂ] Betti) (projector : Module.End ℂ H)
    (hgraded : ∀ x ∈ invariants ⊓ LinearMap.ker edge,
      next.mkQ (projector x) = next.mkQ x)
    (hsupport : restriction.comp projector = 0)
    (hhyperplane_support : restriction hyperplane = 0)
    (x : H) (hinvariant : x ∈ invariants)
    (hcomparison : comparison (CycleQ2GeometricRegularDeRham.residueClass s) =
      restriction x) :
    ∃ η : Form 3, exteriorD3 η =
      CycleQ2AffineExactness.residueSourceForm CycleQ2AffineClearing.affineA := by
  apply exact_of_regular_open_comparison s hs comparison hinjective
  rw [hcomparison]
  exact CycleQ2GeometricLeray.invariant_class_restriction_eq_zero
    edge hyperplane hedge invariants next hhyperplane_invariant hnext
    restriction projector hgraded hsupport hhyperplane_support hinvariant

theorem certificate_of_regular_open_comparison
    (s : CycleQ2GeometricRegularDeRham.OpenRing) (hs : s ≠ 0)
    (comparison : CycleQ2GeometricRegularDeRham.TopDeRham s →ₗ[ℂ] Betti)
    (hinjective : Function.Injective comparison)
    (hzero : comparison (CycleQ2GeometricRegularDeRham.residueClass s) = 0) :
    HodgeComputer.HasCertificate
      HodgeSubmission.F HodgeSubmission.q HodgeSubmission.A :=
  CycleQ2AffineExactness.protected_certificate_of_exact_residueSourceForm
    (exact_of_regular_open_comparison s hs comparison hinjective hzero)

end CycleQ2GeometricExistence

end
