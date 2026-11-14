import Proposal.GeometricCanonicalGluing
import Proposal.GeometricModuleOverFrame
import Proposal.GeometricDifferentialChartTransport
import Proposal.GeometricProjectiveChartSections
import Proposal.GeometricProjectiveDifferentialForms
import Proposal.GeometricTwistedModule

/-!
# The actual canonical comparison on the projective curve

The actual sheaf of complex differentials is isomorphic, as a sheaf of
structure-ring modules, to the existing degree-one twisted sheaf whenever
both actual affine Jacobian ideals are the unit ideal and r is nonzero.
The common proof uses full affine Kähler frames, the actual affine scheme
charts, and their computed residue transition on the quartic denominator cover.

Two closed specializations are supplied: the sparse seed theta = 0, r^3 = 2,
and the literal complex incidence seed (r, theta) = (57, 1). Each uses its
own proved Jacobian certificates. No smoothness, local freeness, comparison
map, or geometric existence premise is left in either specialization.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2GeometricProjectiveCanonical.At

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
  CycleQ2GeometricProjectiveCurve CycleQ2GeometricProjectiveAffine
  CycleQ2GeometricProjectiveAffineCoefficients CycleQ2GeometricChartKaehler.At
  CycleQ2GeometricDifferentialSheaf CycleQ2GeometricAffineChartSections
  CycleQ2GeometricDifferentialChartTransport CycleQ2GeometricSheafKaehlerMap
  CycleQ2GeometricProjectiveChartSections CycleQ2GeometricProjectiveDifferentialForms.At
  CycleQ2GeometricModuleLocalIso CycleQ2GeometricModuleOverFrame
  CycleQ2GeometricCanonicalGluing
open CycleQ2GeometricChartKaehler (ChartJacobianCover)

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
def orientedFirstKaehlerEquiv (r θ : ℂ) (h : ChartJacobianCover r θ) :
    KaehlerDifferential ℂ (FirstChartRing r θ) ≃ₗ[FirstChartRing r θ] FirstChartRing r θ :=
  (firstChartKaehlerEquiv r θ h).trans (LinearEquiv.neg (FirstChartRing r θ))

theorem orientedFirstKaehlerEquiv_symm_one (r θ : ℂ) (h : ChartJacobianCover r θ) :
    (orientedFirstKaehlerEquiv r θ h).symm 1 = -firstChartForm r θ h := by
  apply (orientedFirstKaehlerEquiv r θ h).injective
  rw [LinearEquiv.apply_symm_apply]
  change 1 = -firstChartKaehlerEquiv r θ h (-firstChartForm r θ h)
  rw [map_neg, firstChartKaehlerEquiv_firstChartForm, neg_neg]

theorem secondKaehlerEquiv_symm_one (r θ : ℂ) (h : ChartJacobianCover r θ) :
    (secondChartKaehlerEquiv r θ h).symm 1 = secondChartForm r θ h := by
  apply (secondChartKaehlerEquiv r θ h).injective
  rw [LinearEquiv.apply_symm_apply, secondChartKaehlerEquiv_secondChartForm]

/-- Restriction retains the actual linear maps on every smaller subopen. -/
private def restrictFrame {X : TopCat.{0}} {R : X.Sheaf CommRingCat.{0}}
    {M : SheafOfModules.{0} (TwistedModule.ringSheaf R)} {U V : Opens X}
    (e : LocalFrame R M U) (hVU : V ≤ U) : LocalFrame R M V where
  app O hO := e.app O (hO.trans hVU)
  naturality hPO hO s := e.naturality hPO (hO.trans hVU) s

variable (r θ : ℂ) (h : ChartJacobianCover r θ)

/-- The actual differential sheaf frame on the entire first coordinate chart. -/
def firstCoordinateFrame :
    LocalFrame (projectiveCurve r θ).sheaf (projectiveDifferentialSheaf r θ)
      (coordinateProjectivePatch r θ 1) :=
  patchIsoOfOverFrame
    (chartFrameIso (firstCoordinateChartIso r θ) (projectiveToComplex r θ)
      (firstCoordinateChartIso_overComplex r θ) (orientedFirstKaehlerEquiv r θ h))

/-- The actual differential sheaf frame on the entire second coordinate chart. -/
def secondCoordinateFrame :
    LocalFrame (projectiveCurve r θ).sheaf (projectiveDifferentialSheaf r θ)
      (coordinateProjectivePatch r θ 2) :=
  patchIsoOfOverFrame
    (chartFrameIso (secondCoordinateChartIso r θ) (projectiveToComplex r θ)
      (secondCoordinateChartIso_overComplex r θ) (secondChartKaehlerEquiv r θ h))

/-- The inverse first coordinate frame is the previously constructed,
projectively oriented section of the actual differential sheaf. -/
theorem firstCoordinateFrame_generator :
    frameGenerator (firstCoordinateFrame r θ h) (coordinateProjectivePatch r θ 1) le_rfl =
      firstFormSection r θ h (projectiveDifferentialSheaf r θ)
        (projectiveUniversalDifferential r θ) := by
  change (chartFrameIso (firstCoordinateChartIso r θ) (projectiveToComplex r θ)
      (firstCoordinateChartIso_overComplex r θ) (orientedFirstKaehlerEquiv r θ h)).inv.val.app
      (op (chartTop (coordinateProjectivePatch r θ 1)))
      (1 : Γ(projectiveCurve r θ, coordinateProjectivePatch r θ 1)) = _
  rw [chartFrameIso_inv_one]
  unfold chartFrameSection firstFormSection
  rw [orientedFirstKaehlerEquiv_symm_one]
  exact sectionLift_congr (first_chartSection_top r θ) (-firstChartForm r θ h)

/-- The inverse second coordinate frame is the actual second cofactor form
in projective sheaf sections. -/
theorem secondCoordinateFrame_generator :
    frameGenerator (secondCoordinateFrame r θ h) (coordinateProjectivePatch r θ 2) le_rfl =
      secondFormSection r θ h (projectiveDifferentialSheaf r θ)
        (projectiveUniversalDifferential r θ) := by
  change (chartFrameIso (secondCoordinateChartIso r θ) (projectiveToComplex r θ)
      (secondCoordinateChartIso_overComplex r θ) (secondChartKaehlerEquiv r θ h)).inv.val.app
      (op (chartTop (coordinateProjectivePatch r θ 2)))
      (1 : Γ(projectiveCurve r θ, coordinateProjectivePatch r θ 2)) = _
  rw [chartFrameIso_inv_one]
  unfold chartFrameSection secondFormSection
  rw [secondKaehlerEquiv_symm_one]
  exact sectionLift_congr (second_chartSection_top r θ) (secondChartForm r θ h)

/-- The first frame on the original quartic denominator patch. -/
def firstDenominatorFrame :
    LocalFrame (projectiveCurve r θ).sheaf (projectiveDifferentialSheaf r θ)
      (firstProjectivePatch r θ) :=
  restrictFrame (firstCoordinateFrame r θ h) (firstProjectivePatch_le_firstCoordinate r θ)

/-- The second frame on the original quartic denominator patch. -/
def secondDenominatorFrame :
    LocalFrame (projectiveCurve r θ).sheaf (projectiveDifferentialSheaf r θ)
      (secondProjectivePatch r θ) :=
  restrictFrame (secondCoordinateFrame r θ h) (secondProjectivePatch_le_secondCoordinate r θ)

theorem firstDenominatorFrame_generator :
    frameGenerator (firstDenominatorFrame r θ h) (firstProjectivePatch r θ) le_rfl =
      firstDenominatorForm r θ h (projectiveDifferentialSheaf r θ)
        (projectiveUniversalDifferential r θ) := by
  change frameGenerator (firstCoordinateFrame r θ h) (firstProjectivePatch r θ)
      (firstProjectivePatch_le_firstCoordinate r θ) = _
  rw [← frameGenerator_naturality (firstCoordinateFrame r θ h)
    (firstProjectivePatch_le_firstCoordinate r θ) le_rfl,
    firstCoordinateFrame_generator]
  rfl

theorem secondDenominatorFrame_generator :
    frameGenerator (secondDenominatorFrame r θ h) (secondProjectivePatch r θ) le_rfl =
      secondDenominatorForm r θ h (projectiveDifferentialSheaf r θ)
        (projectiveUniversalDifferential r θ) := by
  change frameGenerator (secondCoordinateFrame r θ h) (secondProjectivePatch r θ)
      (secondProjectivePatch_le_secondCoordinate r θ) = _
  rw [← frameGenerator_naturality (secondCoordinateFrame r θ h)
    (secondProjectivePatch_le_secondCoordinate r θ) le_rfl,
    secondCoordinateFrame_generator]
  rfl

/-- On the actual denominator overlap, the inverse generators satisfy the
transition unit of the existing degree-one sheaf. -/
theorem denominatorFrame_transition :
    frameGenerator (secondDenominatorFrame r θ h) (overlapProjectivePatch r θ)
        ((overlapProjectivePatch_eq r θ).le.trans inf_le_right) =
      (projectiveTransitionUnit r θ : Γ(projectiveCurve r θ, overlapProjectivePatch r θ)) •
        frameGenerator (firstDenominatorFrame r θ h) (overlapProjectivePatch r θ)
          ((overlapProjectivePatch_eq r θ).le.trans inf_le_left) := by
  rw [← frameGenerator_naturality (secondDenominatorFrame r θ h)
      ((overlapProjectivePatch_eq r θ).le.trans inf_le_right) le_rfl,
    ← frameGenerator_naturality (firstDenominatorFrame r θ h)
      ((overlapProjectivePatch_eq r θ).le.trans inf_le_left) le_rfl,
    secondDenominatorFrame_generator, firstDenominatorFrame_generator]
  exact projective_differential_transition r θ h

/-- The actual differential sheaf and degree-one module sheaf are identified
using the two proved chart Jacobian ideals and the actual quartic open cover. -/
def projectiveCanonicalIso (hr : r ≠ 0) : projectiveDifferentialSheaf r θ ≅ degreeOneModuleSheaf r θ :=
  canonicalIsoOfOverlap (projectiveCurve r θ).sheaf
    (firstProjectivePatch r θ) (secondProjectivePatch r θ) (overlapProjectivePatch r θ)
    (overlapProjectivePatch_eq r θ) (projectiveTransitionUnit r θ)
    (projectiveDifferentialSheaf r θ) (firstDenominatorFrame r θ h) (secondDenominatorFrame r θ h)
    (projective_twoOpen_cover r θ hr)
    (denominatorFrame_transition r θ h)

end CycleQ2GeometricProjectiveCanonical.At

namespace CycleQ2GeometricProjectiveCanonical
open CycleQ2GeometricChartKaehler CycleQ2GeometricProjectiveCurve
  CycleQ2GeometricDifferentialSheaf CategoryTheory

/-! The original sparse comparison and the literal-incidence comparison use
exactly the same constructions, with their separately proved Jacobian covers. -/

abbrev orientedFirstKaehlerEquiv (r : ℂ) (hr : r ^ 3 = 2) :=
  At.orientedFirstKaehlerEquiv r 0 (sparseChartJacobianCover r hr)

abbrev orientedFirstKaehlerEquiv_symm_one (r : ℂ) (hr : r ^ 3 = 2) :=
  At.orientedFirstKaehlerEquiv_symm_one r 0 (sparseChartJacobianCover r hr)

abbrev secondKaehlerEquiv_symm_one (r : ℂ) (hr : r ^ 3 = 2) :=
  At.secondKaehlerEquiv_symm_one r 0 (sparseChartJacobianCover r hr)

abbrev firstCoordinateFrame (r : ℂ) (hr : r ^ 3 = 2) :=
  At.firstCoordinateFrame r 0 (sparseChartJacobianCover r hr)

abbrev secondCoordinateFrame (r : ℂ) (hr : r ^ 3 = 2) :=
  At.secondCoordinateFrame r 0 (sparseChartJacobianCover r hr)

abbrev firstCoordinateFrame_generator (r : ℂ) (hr : r ^ 3 = 2) :=
  At.firstCoordinateFrame_generator r 0 (sparseChartJacobianCover r hr)

abbrev secondCoordinateFrame_generator (r : ℂ) (hr : r ^ 3 = 2) :=
  At.secondCoordinateFrame_generator r 0 (sparseChartJacobianCover r hr)

abbrev firstDenominatorFrame (r : ℂ) (hr : r ^ 3 = 2) :=
  At.firstDenominatorFrame r 0 (sparseChartJacobianCover r hr)

abbrev secondDenominatorFrame (r : ℂ) (hr : r ^ 3 = 2) :=
  At.secondDenominatorFrame r 0 (sparseChartJacobianCover r hr)

abbrev firstDenominatorFrame_generator (r : ℂ) (hr : r ^ 3 = 2) :=
  At.firstDenominatorFrame_generator r 0 (sparseChartJacobianCover r hr)

abbrev secondDenominatorFrame_generator (r : ℂ) (hr : r ^ 3 = 2) :=
  At.secondDenominatorFrame_generator r 0 (sparseChartJacobianCover r hr)

abbrev denominatorFrame_transition (r : ℂ) (hr : r ^ 3 = 2) :=
  At.denominatorFrame_transition r 0 (sparseChartJacobianCover r hr)

/-- The sparse canonical comparison, preserving its original statement. -/
def projectiveCanonicalIso (r : ℂ) (hr : r ^ 3 = 2) :
    projectiveDifferentialSheaf r 0 ≅ degreeOneModuleSheaf r 0 :=
  At.projectiveCanonicalIso r 0 (sparseChartJacobianCover r hr) (by
    intro hz
    simp [hz] at hr)

/-- The actual canonical comparison at the literal complex incidence seed.
Both affine Jacobian covers are supplied by their exact arithmetic certificates. -/
def literalProjectiveCanonicalIso :
    projectiveDifferentialSheaf 57 1 ≅ degreeOneModuleSheaf 57 1 :=
  At.projectiveCanonicalIso 57 1 literalChartJacobianCover (by norm_num)

#print axioms At.denominatorFrame_transition
#print axioms At.projectiveCanonicalIso
#print axioms projectiveCanonicalIso
#print axioms literalProjectiveCanonicalIso

end CycleQ2GeometricProjectiveCanonical
end
