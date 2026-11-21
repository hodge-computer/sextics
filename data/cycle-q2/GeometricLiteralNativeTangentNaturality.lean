import Proposal.GeometricLiteralNativeTangentEvaluation
import Proposal.GeometricLiteralNativeRestrictionLocalization

/-!
# The actual native tangent maps commute with restriction

The genuine local universal property detects equality of tangent sections
on the native affine ring. Localization of Kähler modules then proves
that compatible native derivations induce the same restricted tangent
section, on all subopens and all differential-sheaf sections.

Prepared for fqlx with OpenAI ChatGPT assistance; see solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralNativeTangentNaturality

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
  CycleQ2LiteralProjectiveIntersections CycleQ2LiteralProjectiveIntersectionRestrictions
  CycleQ2LiteralProjectiveIntersectionComplex CycleQ2GeometricDifferentialSheaf
  CycleQ2GeometricIntrinsicNormal CycleQ2GeometricDifferentialRestriction
  CycleQ2GeometricDifferentialChartTransport CycleQ2GeometricAffineChartSections
  CycleQ2GeometricAffineOverlap CycleQ2LiteralNativeDifferentialSections
  CycleQ2LiteralNativeTangentEvaluation CycleQ2LiteralNativeRestrictionLocalization

attribute [local instance] CycleQ2LiteralProjectiveIntersectionComplex.closedComplexAlgebra
  CycleQ2LiteralProjectiveIntersectionComplex.closedComplexSMul
  CycleQ2LiteralProjectiveIntersectionComplex.closedComplexModule
  CycleQ2LiteralNativeDifferentialSections.sectionComplexAlgebra
  CycleQ2LiteralNativeDifferentialSections.sectionComplexSMul
  CycleQ2LiteralNativeDifferentialSections.sectionComplexModule

local instance sectionRingSelfModule (U : Surface.Opens) :
    Module (CycleQ2GeometricSectionDifferentials.SectionRing Surface.sheaf U) Γ(Surface,U) :=
  inferInstanceAs (Module (CycleQ2GeometricSectionDifferentials.SectionRing Surface.sheaf U)
    (CycleQ2GeometricSectionDifferentials.SectionRing Surface.sheaf U))

theorem nativeTangent_ext (s : Finset Vertex) (hs : s.Nonempty)
    (x y : tangentSheaf.val.obj (op (closedOpen s)))
    (h : ∀ a : ClosedRing s,
      evaluateTangent (closedOpen s) x (nativeFormToSheaf s hs (KaehlerDifferential.D ℂ (ClosedRing s) a)) =
        evaluateTangent (closedOpen s) y (nativeFormToSheaf s hs (KaehlerDifferential.D ℂ (ClosedRing s) a))) : x = y := by
  apply (localLinearHomEquiv Surface.sheaf DifferentialSheaf structureModule (closedOpen s)).injective
  apply restrictedLift_unique Surface.sheaf globalCoefficient (closedOpen s) (structureModule.over (closedOpen s))
  apply chartDerivation_ext (nativeChart s hs)
    (CycleQ2GeometricSurfaceCoefficients.projectiveToComplex 57 1) (nativeChart_coefficient s hs)
    (structureModule.over (closedOpen s))
  intro a
  change evaluateTangent (closedOpen s) x
      ((universalDifferential Surface.sheaf globalCoefficient).d
        (CycleQ2GeometricAffineChartSections.chartSection (nativeChart s hs) (chartTop (closedOpen s)) a)) =
    evaluateTangent (closedOpen s) y
      ((universalDifferential Surface.sheaf globalCoefficient).d
        (CycleQ2GeometricAffineChartSections.chartSection (nativeChart s hs) (chartTop (closedOpen s)) a))
  have ha := (nativeFormToSheaf_D s hs a).trans
    (congrArg ((universalDifferential Surface.sheaf globalCoefficient).d (X := op (closedOpen s)))
      (nativeChart_section s hs a).symm)
  exact (congrArg (evaluateTangent (closedOpen s) x) ha).symm.trans
    ((h a).trans (congrArg (evaluateTangent (closedOpen s) y) ha))

def nativeContraction (s : Finset Vertex) (hs : s.Nonempty)
    (x : tangentSheaf.val.obj (op (closedOpen s))) :
    KaehlerDifferential ℂ (ClosedRing s) →ₗ[ClosedRing s] ClosedRing s where
  toFun ω := (nativeSectionsAlgEquiv s hs).symm
    (evaluateTangent (closedOpen s) x (nativeFormToSheaf s hs ω))
  map_add' ω η := by rw [map_add, map_add, map_add]
  map_smul' a ω := by
    calc
      _ = (nativeSectionsAlgEquiv s hs).symm
          (evaluateTangent (closedOpen s) x
            (nativeSectionsAlgEquiv s hs a • nativeFormToSheaf s hs ω)) :=
        congrArg (fun z => (nativeSectionsAlgEquiv s hs).symm (evaluateTangent (closedOpen s) x z))
          (nativeFormToSheaf_smul s hs a ω)
      _ = (nativeSectionsAlgEquiv s hs).symm
          ((nativeSectionsAlgEquiv s hs a : Γ(Surface,closedOpen s)) •
            evaluateTangent (closedOpen s) x (nativeFormToSheaf s hs ω)) :=
        congrArg (nativeSectionsAlgEquiv s hs).symm
          ((evaluateTangent (closedOpen s) x).map_smul
            (nativeSectionsAlgEquiv s hs a : Γ(Surface,closedOpen s)) _)
      _ = _ := by
        change (nativeSectionsAlgEquiv s hs).symm
          (nativeSectionsAlgEquiv s hs a * _) = a * _
        rw [map_mul, AlgEquiv.symm_apply_apply]

theorem nativeContraction_injective (s : Finset Vertex) (hs : s.Nonempty) :
    Function.Injective (nativeContraction s hs) := by
  intro x y h
  apply nativeTangent_ext s hs x y
  intro a
  apply (nativeSectionsAlgEquiv s hs).symm.injective
  exact LinearMap.congr_fun h (KaehlerDifferential.D ℂ (ClosedRing s) a)

theorem nativeContraction_nativeTangent (s : Finset Vertex) (hs : s.Nonempty)
    (δ : Derivation ℂ (ClosedRing s) (ClosedRing s)) :
    nativeContraction s hs (nativeTangent s hs δ) = δ.liftKaehlerDifferential := by
  apply LinearMap.ext
  intro ω
  change (nativeSectionsAlgEquiv s hs).symm
    (evaluateTangent (closedOpen s) (nativeTangent s hs δ) (nativeFormToSheaf s hs ω)) = _
  rw [nativeTangent_on_form, AlgEquiv.symm_apply_apply]

theorem nativeContraction_restrict_on_forms {s t : Finset Vertex} (hst : s ⊆ t)
    (hs : s.Nonempty) (ht : t.Nonempty) (δ : Derivation ℂ (ClosedRing s) (ClosedRing s))
    (ω : KaehlerDifferential ℂ (ClosedRing s)) :
    nativeContraction t ht
        (tangentSheaf.val.map (homOfLE (closedOpen_mono hst)).op (nativeTangent s hs δ))
        (differentialMap (closedRestrictionAlgHom hst) ω) =
      closedRestrictionAlgHom hst (δ.liftKaehlerDifferential ω) := by
  apply (nativeSectionsAlgEquiv t ht).injective
  change (nativeSectionsAlgEquiv t ht) ((nativeSectionsAlgEquiv t ht).symm
    (evaluateTangent (closedOpen t)
      (tangentSheaf.val.map (homOfLE (closedOpen_mono hst)).op (nativeTangent s hs δ))
      (nativeFormToSheaf t ht (differentialMap (closedRestrictionAlgHom hst) ω)))) = _
  rw [AlgEquiv.apply_symm_apply]
  calc
    _ = evaluateTangent (closedOpen t)
        (tangentSheaf.val.map (homOfLE (closedOpen_mono hst)).op (nativeTangent s hs δ))
        (DifferentialSheaf.val.map (homOfLE (closedOpen_mono hst)).op (nativeFormToSheaf s hs ω)) :=
      congrArg (evaluateTangent (closedOpen t) _)
        (nativeFormToSheaf_restrict hst hs ht ω).symm
    _ = Surface.presheaf.map (homOfLE (closedOpen_mono hst)).op
        (evaluateTangent (closedOpen s) (nativeTangent s hs δ) (nativeFormToSheaf s hs ω)) :=
      localLinearHomEvaluate_restrict Surface.sheaf DifferentialSheaf structureModule
        (homOfLE (closedOpen_mono hst)) (nativeTangent s hs δ) (nativeFormToSheaf s hs ω)
    _ = Surface.presheaf.map (homOfLE (closedOpen_mono hst)).op
        (nativeSectionsAlgEquiv s hs (δ.liftKaehlerDifferential ω)) :=
      congrArg (Surface.presheaf.map (homOfLE (closedOpen_mono hst)).op)
        (nativeTangent_on_form s hs δ ω)
    _ = _ := nativeSectionsAlgEquiv_restrict hst hs ht _

theorem nativeTangent_restrict {s t : Finset Vertex} (hst : s ⊆ t) (hs : s.Nonempty) (ht : t.Nonempty)
    (δ : Derivation ℂ (ClosedRing s) (ClosedRing s)) (η : Derivation ℂ (ClosedRing t) (ClosedRing t))
    (h : ∀ a : ClosedRing s, closedRestrictionAlgHom hst (δ a) = η (closedRestrictionAlgHom hst a)) :
    tangentSheaf.val.map (homOfLE (closedOpen_mono hst)).op (nativeTangent s hs δ) =
      nativeTangent t ht η := by
  apply nativeContraction_injective t ht
  rw [nativeContraction_nativeTangent]
  apply nativeDifferential_ext hst hs
  intro a
  rw [← differentialMap_D (closedRestrictionAlgHom hst) a,
    nativeContraction_restrict_on_forms hst hs ht δ, differentialMap_D,
    δ.liftKaehlerDifferential_comp_D, η.liftKaehlerDifferential_comp_D]
  exact h a

end CycleQ2LiteralNativeTangentNaturality

end

#print axioms CycleQ2LiteralNativeTangentNaturality.nativeTangent_ext
#print axioms CycleQ2LiteralNativeTangentNaturality.nativeTangent_restrict
