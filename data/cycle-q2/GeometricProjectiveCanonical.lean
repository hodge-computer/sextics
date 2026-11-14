import Proposal.GeometricCanonicalGluing
import Proposal.GeometricModuleOverFrame
import Proposal.GeometricDifferentialChartTransport
import Proposal.GeometricProjectiveChartSections
import Proposal.GeometricProjectiveDifferentialForms
import Proposal.GeometricTwistedModule

/-!
# The actual canonical comparison on the sparse projective curve

For the literal parameter choice theta = 0 and r^3 = 2, the actual sheaf of
complex differentials is isomorphic, as a sheaf of structure-ring modules,
to the existing degree-one twisted sheaf. The local frames come from the
proved full affine Kähler trivializations and the actual affine scheme
charts. Their inverse generators are identified with the explicit forms
already transported into projective sheaf sections.

The first frame is oriented by a minus sign. On the original quartic
denominator overlap, the proved projective differential transition is
exactly the generator identity required by the actual sheaf gluing theorem.
No local freeness, comparison map, or geometric existence premise is added.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2GeometricProjectiveCanonical

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
  CycleQ2GeometricProjectiveCurve CycleQ2GeometricProjectiveAffine
  CycleQ2GeometricProjectiveAffineCoefficients CycleQ2GeometricChartKaehler
  CycleQ2GeometricDifferentialSheaf CycleQ2GeometricAffineChartSections
  CycleQ2GeometricDifferentialChartTransport CycleQ2GeometricSheafKaehlerMap
  CycleQ2GeometricProjectiveChartSections CycleQ2GeometricProjectiveDifferentialForms
  CycleQ2GeometricModuleLocalIso CycleQ2GeometricModuleOverFrame
  CycleQ2GeometricCanonicalGluing

/-- Equal actual section-ring maps give the same universal Kähler lift. -/
private theorem sectionLift_congr {X : TopCat.{0}}
    {R : X.Sheaf CommRingCat.{0}} {c : ℂ →+* R.obj.obj (op ⊤)}
    {M : SheafOfModules.{0} (ringSheaf R)}
    {d : M.val.Derivation' (coefficientMap R c)} {O : Opens X}
    {A : Type} [CommRing A] [Algebra ℂ A]
    {f g : A →+* R.obj.obj (op O)}
    {hf : ∀ z : ℂ, f (algebraMap ℂ A z) = coefficientOn R c O z}
    {hg : ∀ z : ℂ, g (algebraMap ℂ A z) = coefficientOn R c O z}
    (hfg : f = g) (ω : KaehlerDifferential ℂ A) :
    sectionLift R c M d O f hf ω = sectionLift R c M d O g hg ω := by
  subst g
  rfl

/-- The oriented coefficient equivalence has inverse generator equal to
minus the first actual affine cofactor form. -/
def orientedFirstKaehlerEquiv (r : ℂ) (hr : r ^ 3 = 2) :
    KaehlerDifferential ℂ (FirstChartRing r 0) ≃ₗ[FirstChartRing r 0] FirstChartRing r 0 :=
  (firstChartKaehlerEquiv r hr).trans (LinearEquiv.neg (FirstChartRing r 0))

theorem orientedFirstKaehlerEquiv_symm_one (r : ℂ) (hr : r ^ 3 = 2) :
    (orientedFirstKaehlerEquiv r hr).symm 1 = -firstChartForm r hr := by
  apply (orientedFirstKaehlerEquiv r hr).injective
  rw [LinearEquiv.apply_symm_apply]
  change 1 = -firstChartKaehlerEquiv r hr (-firstChartForm r hr)
  rw [map_neg, firstChartKaehlerEquiv_firstChartForm, neg_neg]

theorem secondKaehlerEquiv_symm_one (r : ℂ) (hr : r ^ 3 = 2) :
    (secondChartKaehlerEquiv r hr).symm 1 = secondChartForm r hr := by
  apply (secondChartKaehlerEquiv r hr).injective
  rw [LinearEquiv.apply_symm_apply, secondChartKaehlerEquiv_secondChartForm]

/-- Restriction retains the actual linear maps on every smaller subopen. -/
private def restrictFrame {X : TopCat.{0}} {R : X.Sheaf CommRingCat.{0}}
    {M : SheafOfModules.{0} (TwistedModule.ringSheaf R)} {U V : Opens X}
    (e : LocalFrame R M U) (hVU : V ≤ U) : LocalFrame R M V where
  app O hO := e.app O (hO.trans hVU)
  naturality hPO hO s := e.naturality hPO (hO.trans hVU) s

variable (r : ℂ) (hr : r ^ 3 = 2)

/-- The actual differential sheaf frame on the entire first coordinate chart. -/
def firstCoordinateFrame :
    LocalFrame (projectiveCurve r 0).sheaf (projectiveDifferentialSheaf r 0)
      (coordinateProjectivePatch r 0 1) :=
  patchIsoOfOverFrame
    (chartFrameIso (firstCoordinateChartIso r 0) (projectiveToComplex r 0)
      (firstCoordinateChartIso_overComplex r 0) (orientedFirstKaehlerEquiv r hr))

/-- The actual differential sheaf frame on the entire second coordinate chart. -/
def secondCoordinateFrame :
    LocalFrame (projectiveCurve r 0).sheaf (projectiveDifferentialSheaf r 0)
      (coordinateProjectivePatch r 0 2) :=
  patchIsoOfOverFrame
    (chartFrameIso (secondCoordinateChartIso r 0) (projectiveToComplex r 0)
      (secondCoordinateChartIso_overComplex r 0) (secondChartKaehlerEquiv r hr))

/-- The inverse first coordinate frame is the previously constructed,
projectively oriented section of the actual differential sheaf. -/
theorem firstCoordinateFrame_generator :
    frameGenerator (firstCoordinateFrame r hr) (coordinateProjectivePatch r 0 1) le_rfl =
      firstFormSection r hr (projectiveDifferentialSheaf r 0)
        (projectiveUniversalDifferential r 0) := by
  change (chartFrameIso (firstCoordinateChartIso r 0) (projectiveToComplex r 0)
      (firstCoordinateChartIso_overComplex r 0) (orientedFirstKaehlerEquiv r hr)).inv.val.app
      (op (chartTop (coordinateProjectivePatch r 0 1)))
      (1 : Γ(projectiveCurve r 0, coordinateProjectivePatch r 0 1)) = _
  rw [chartFrameIso_inv_one]
  unfold chartFrameSection firstFormSection
  rw [orientedFirstKaehlerEquiv_symm_one]
  exact sectionLift_congr (first_chartSection_top r 0) (-firstChartForm r hr)

/-- The inverse second coordinate frame is the actual second cofactor form
in projective sheaf sections. -/
theorem secondCoordinateFrame_generator :
    frameGenerator (secondCoordinateFrame r hr) (coordinateProjectivePatch r 0 2) le_rfl =
      secondFormSection r hr (projectiveDifferentialSheaf r 0)
        (projectiveUniversalDifferential r 0) := by
  change (chartFrameIso (secondCoordinateChartIso r 0) (projectiveToComplex r 0)
      (secondCoordinateChartIso_overComplex r 0) (secondChartKaehlerEquiv r hr)).inv.val.app
      (op (chartTop (coordinateProjectivePatch r 0 2)))
      (1 : Γ(projectiveCurve r 0, coordinateProjectivePatch r 0 2)) = _
  rw [chartFrameIso_inv_one]
  unfold chartFrameSection secondFormSection
  rw [secondKaehlerEquiv_symm_one]
  exact sectionLift_congr (second_chartSection_top r 0) (secondChartForm r hr)

/-- The first frame on the original quartic denominator patch. -/
def firstDenominatorFrame :
    LocalFrame (projectiveCurve r 0).sheaf (projectiveDifferentialSheaf r 0)
      (firstProjectivePatch r 0) :=
  restrictFrame (firstCoordinateFrame r hr) (firstProjectivePatch_le_firstCoordinate r 0)

/-- The second frame on the original quartic denominator patch. -/
def secondDenominatorFrame :
    LocalFrame (projectiveCurve r 0).sheaf (projectiveDifferentialSheaf r 0)
      (secondProjectivePatch r 0) :=
  restrictFrame (secondCoordinateFrame r hr) (secondProjectivePatch_le_secondCoordinate r 0)

theorem firstDenominatorFrame_generator :
    frameGenerator (firstDenominatorFrame r hr) (firstProjectivePatch r 0) le_rfl =
      firstDenominatorForm r hr (projectiveDifferentialSheaf r 0)
        (projectiveUniversalDifferential r 0) := by
  change frameGenerator (firstCoordinateFrame r hr) (firstProjectivePatch r 0)
      (firstProjectivePatch_le_firstCoordinate r 0) = _
  rw [← frameGenerator_naturality (firstCoordinateFrame r hr)
    (firstProjectivePatch_le_firstCoordinate r 0) le_rfl,
    firstCoordinateFrame_generator]
  rfl

theorem secondDenominatorFrame_generator :
    frameGenerator (secondDenominatorFrame r hr) (secondProjectivePatch r 0) le_rfl =
      secondDenominatorForm r hr (projectiveDifferentialSheaf r 0)
        (projectiveUniversalDifferential r 0) := by
  change frameGenerator (secondCoordinateFrame r hr) (secondProjectivePatch r 0)
      (secondProjectivePatch_le_secondCoordinate r 0) = _
  rw [← frameGenerator_naturality (secondCoordinateFrame r hr)
    (secondProjectivePatch_le_secondCoordinate r 0) le_rfl,
    secondCoordinateFrame_generator]
  rfl

/-- On the actual denominator overlap, the inverse generators satisfy the
transition unit of the existing degree-one sheaf. -/
theorem denominatorFrame_transition :
    frameGenerator (secondDenominatorFrame r hr) (overlapProjectivePatch r 0)
        ((overlapProjectivePatch_eq r 0).le.trans inf_le_right) =
      (projectiveTransitionUnit r 0 : Γ(projectiveCurve r 0, overlapProjectivePatch r 0)) •
        frameGenerator (firstDenominatorFrame r hr) (overlapProjectivePatch r 0)
          ((overlapProjectivePatch_eq r 0).le.trans inf_le_left) := by
  rw [← frameGenerator_naturality (secondDenominatorFrame r hr)
      ((overlapProjectivePatch_eq r 0).le.trans inf_le_right) le_rfl,
    ← frameGenerator_naturality (firstDenominatorFrame r hr)
      ((overlapProjectivePatch_eq r 0).le.trans inf_le_left) le_rfl,
    secondDenominatorFrame_generator, firstDenominatorFrame_generator]
  exact projective_differential_transition r hr

/-- The actual projective differential sheaf is the actual degree-one
module sheaf at the literal sparse parameter choice. The only inputs are
r and the equation r^3 = 2. -/
def projectiveCanonicalIso : projectiveDifferentialSheaf r 0 ≅ degreeOneModuleSheaf r 0 :=
  canonicalIsoOfOverlap (projectiveCurve r 0).sheaf
    (firstProjectivePatch r 0) (secondProjectivePatch r 0) (overlapProjectivePatch r 0)
    (overlapProjectivePatch_eq r 0) (projectiveTransitionUnit r 0)
    (projectiveDifferentialSheaf r 0) (firstDenominatorFrame r hr) (secondDenominatorFrame r hr)
    (projective_twoOpen_cover r 0 (by
      intro hz
      rw [hz] at hr
      norm_num at hr))
    (denominatorFrame_transition r hr)

#print axioms firstCoordinateFrame_generator
#print axioms secondCoordinateFrame_generator
#print axioms denominatorFrame_transition
#print axioms projectiveCanonicalIso

end CycleQ2GeometricProjectiveCanonical
end
