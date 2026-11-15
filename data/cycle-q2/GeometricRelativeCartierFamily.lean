import Proposal.GeometricRelativeRegularSection
import Proposal.GeometricRelativeSectionIdeal
import Proposal.GeometricSpecializedProjectiveCurve

/-!
# One actual Cartier section on the incidence family and its original seed

The regular-principal-cover predicate records the original closed
immersion, its actual affine cover, and the actual structure-map kernels.
It is a transparent bundle of those assertions, not an assumed Cartier
or flatness property.

The simultaneous associated-prime choice supplies one nonzero complex
vector for the entire original incidence surface and for the existing
literal specialized seed curve. The original trace-point and seed
identities discharge all equation, leading-unit, and basepoint premises.
In particular the seed curve is the earlier specializedCurve construction,
not a replacement defined using this bundle.

This proves regular principal equations on both total space and seed.
It does not prove flatness of the quotient over the parameter base,
nonempty curve fibers, or the divisor-class comparison.

Source-only draft: no Lean elaboration or kernel replay has been run.
Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md for
attribution of the geometric route and the protected certificate gap.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2RelativeCartierFamily

open CategoryTheory AlgebraicGeometry MvPolynomial
open CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations
  CycleQ2IncidenceUniversalChart CycleQ2IncidencePolynomialJacobianBinding
  CycleQ2IncidenceEtaleParameter CycleQ2IncidenceTraceGeometry
  CycleQ2IncidencePolynomialRelations CycleQ2IncidenceCoefficientRelations
  CycleQ2GeometricIncidenceProj
  CycleQ2RegularSeedSection CycleQ2SpecializedSectionIdeal
  CycleQ2SpecializedProjectiveCurve CycleQ2RelativeConstantSection
  CycleQ2RelativeConstantCurve CycleQ2RelativeRegularSection
  CycleQ2RelativeSectionIdeal

/-- Actual affine regular generators for the kernels of an actual closed
immersion. The zero locus is allowed to be empty. -/
structure HasRegularPrincipalCover {X Y : Scheme} {ι : Type*}
    (f : Y ⟶ X) (U : ι → X.Opens) (s : (i : ι) → Γ(X, U i)) : Prop where
  closedImmersion : IsClosedImmersion f
  cover : (⨆ i, U i) = ⊤
  affine : ∀ i, IsAffineOpen (U i)
  regular : ∀ i, IsSMulRegular Γ(X, U i) (s i)
  kernel : ∀ i, RingHom.ker (f.app (U i)).hom = Ideal.span {s i}

section Relative

variable {S : Type} [CommRing S] [Algebra ℂ S] [Nontrivial S]

theorem relative_hasRegularPrincipalCover (y : ParameterIndex → S)
    (t : Fin 3 → ℂ)
    (he : ∀ q, aeval y ((presentation ℂ 57).equation q) = 0)
    (hu : IsUnit (aeval y (leadingProduct ℂ)))
    (hb : IsUnit (aeval y CycleQ2IncidenceBasepointOpen.basepointPolynomial))
    (hreg : ∀ p : CycleQ2SegreCech.Chart,
      IsSMulRegular (RelativeProjectivePivot y p) (relativeProjectiveEquation y t p)) :
    HasRegularPrincipalCover (relativeCurveToSurface y t)
      (relativePivotOpen y) (relativeEquationSection y t) where
  closedImmersion := inferInstance
  cover := relativePivotOpen_cover y hb
  affine := relativePivotOpen_isAffineOpen y
  regular p := relativeEquationSection_regular y t p (hreg p)
  kernel := relativeSectionKernel_principal y t he hu

end Relative

theorem seed_hasRegularPrincipalCover (t : Fin 3 → ℂ)
    (hreg : ∀ p : CycleQ2SegreCech.Chart,
      IsSMulRegular (ConstantProjectivePivot (seedPoint (57 : ℂ) Complex.I) p)
        (constantProjectiveEquation (seedPoint (57 : ℂ) Complex.I) t p)) :
    HasRegularPrincipalCover
      (specializedCurveToSurface (seedPoint (57 : ℂ) Complex.I) t)
      (constantPivotOpen (seedPoint (57 : ℂ) Complex.I))
      (specializedEquationSection (seedPoint (57 : ℂ) Complex.I) t) where
  closedImmersion := inferInstance
  cover := constantPivotOpen_cover (seedPoint (57 : ℂ) Complex.I) seed_basepoint_unit
  affine := constantPivotOpen_isAffineOpen (seedPoint (57 : ℂ) Complex.I)
  regular p := specializedEquationSection_regular
    (seedPoint (57 : ℂ) Complex.I) t p (hreg p)
  kernel := specializedSectionKernel_principal
    (seedPoint (57 : ℂ) Complex.I) t seed_original_equations seed_leading_unit

/-- One fixed nonzero complex vector cuts out actual regular principal
closed subschemes on the total incidence surface and on its old literal
seed construction. No geometric premise is supplied by a caller. -/
theorem exists_incidence_and_seed_cartier :
    ∃ t : Fin 3 → ℂ, t ≠ 0 ∧
      HasRegularPrincipalCover (relativeCurveToSurface incidencePoint t)
        (relativePivotOpen incidencePoint) (relativeEquationSection incidencePoint t) ∧
      HasRegularPrincipalCover
        (specializedCurveToSurface (seedPoint (57 : ℂ) Complex.I) t)
        (constantPivotOpen (seedPoint (57 : ℂ) Complex.I))
        (specializedEquationSection (seedPoint (57 : ℂ) Complex.I) t) := by
  obtain ⟨t, ht, hrelative, hseed⟩ := exists_incidence_and_seed_regular
  refine ⟨t, ht, ?_, seed_hasRegularPrincipalCover t hseed⟩
  exact relative_hasRegularPrincipalCover incidencePoint t
    (tracePoint_original_equations splitting.P splitting.B _ sliceCoordinate
      incidence_isTracePoint)
    (tracePoint_leading_unit splitting.P splitting.B _ sliceCoordinate incidence_isTracePoint)
    (tracePoint_extra_unit splitting.P splitting.B _ sliceCoordinate incidence_isTracePoint)
    hrelative

#print axioms relative_hasRegularPrincipalCover
#print axioms seed_hasRegularPrincipalCover
#print axioms exists_incidence_and_seed_cartier

end CycleQ2RelativeCartierFamily
end
