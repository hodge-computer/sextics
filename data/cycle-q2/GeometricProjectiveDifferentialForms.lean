import Proposal.GeometricSheafKaehlerMap
import Proposal.GeometricCanonicalOverlap
import Proposal.GeometricProjectiveTransition

/-!
# The cofactor forms in actual projective sheaf sections

The affine whole-chart forms map into every sheaf-valued derivation on the
actual projective curve. Their restrictions satisfy the proved cofactor
transition in the actual sheaf of modules, first on the coordinate overlap
and then on the original quartic denominator overlap. The latter coefficient
is exactly the transition unit of the existing degree-one twisted sheaf.

Specializing to the universal differential gives actual sections of the
projective differential sheaf, with no extra comparison-map hypothesis.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2GeometricProjectiveDifferentialForms.At

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
  CycleQ2GeometricDifferentialSheaf CycleQ2GeometricSheafKaehlerMap
  CycleQ2GeometricProjectiveCurve CycleQ2GeometricProjectiveAffine
  CycleQ2GeometricProjectiveAffineCoefficients CycleQ2GeometricProjectiveOverlap
  CycleQ2GeometricProjectiveTransition CycleQ2GeometricAffineCurveCharts
  CycleQ2GeometricAffineOverlap CycleQ2GeometricCanonicalOverlap.At
open CycleQ2GeometricChartKaehler (ChartJacobianCover)

local instance additiveSectionsModule {X : TopCat.{0}} (R : X.Sheaf CommRingCat.{0})
    (M : SheafOfModules.{0} (ringSheaf R)) (O : Opens X) :
    Module (R.obj.obj (op O)) (M.val.presheaf.obj (op O)) :=
  (M.val.obj (op O)).isModule

section Naturality

variable {X : TopCat.{0}} (R : X.Sheaf CommRingCat.{0})
  (c : ℂ →+* R.obj.obj (op ⊤)) (M : SheafOfModules.{0} (ringSheaf R))
  (d : M.val.Derivation' (coefficientMap R c))
  {A B : Type} [CommRing A] [Algebra ℂ A] [CommRing B] [Algebra ℂ B]

private theorem restriction_lift (O P : Opens X) (hPO : P ≤ O)
    (f : A →+* R.obj.obj (op O))
    (hf : ∀ z : ℂ, f (algebraMap ℂ A z) = coefficientOn R c O z)
    (g : B →+* R.obj.obj (op P))
    (hg : ∀ z : ℂ, g (algebraMap ℂ B z) = coefficientOn R c P z)
    (φ : A →ₐ[ℂ] B)
    (hfg : ∀ a, R.obj.map (homOfLE hPO).op (f a) = g (φ a))
    (ω : KaehlerDifferential ℂ A) :
    M.val.presheaf.map (homOfLE hPO).op (sectionLift R c M d O f hf ω) =
      sectionLift R c M d P g hg (differentialMap φ ω) := by
  have hcomp : ∀ z : ℂ, (g.comp φ.toRingHom) (algebraMap ℂ A z) =
      coefficientOn R c P z := fun z => (congrArg g (φ.commutes z)).trans (hg z)
  exact (sectionLift_restriction R c M d O f hf P hPO
    (g.comp φ.toRingHom) hcomp hfg ω).trans
      (sectionLift_differentialMap R c M d P (g.comp φ.toRingHom) hcomp
        g hg φ (fun _ => rfl) ω).symm

private theorem restriction_smul {O P : Opens X} (hPO : P ≤ O)
    (a : R.obj.obj (op O)) (s : M.val.obj (op O)) :
    M.val.presheaf.map (homOfLE hPO).op (a • s) =
      R.obj.map (homOfLE hPO).op a • M.val.presheaf.map (homOfLE hPO).op s :=
  M.val.map_smul (homOfLE hPO).op a s

private theorem restriction_path (F : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{0})
    {O P Q W : Opens X} (i : P ⟶ O) (j : W ⟶ P)
    (i' : Q ⟶ O) (j' : W ⟶ Q) (s : F.obj (op O)) :
    F.map j.op (F.map i.op s) = F.map j'.op (F.map i'.op s) := by
  change (F.map i.op ≫ F.map j.op) s = (F.map i'.op ≫ F.map j'.op) s
  rw [← F.map_comp, ← F.map_comp]
  exact congrArg (fun f => F.map f s) (Subsingleton.elim _ _)

end Naturality

def firstSectionMap (r θ : ℂ) :
    FirstChartRing r θ →+* Γ(projectiveCurve r θ, coordinateProjectivePatch r θ 1) :=
  (firstCoordinateSectionsEquiv r θ).symm.toRingHom

def secondSectionMap (r θ : ℂ) :
    SecondChartRing r θ →+* Γ(projectiveCurve r θ, coordinateProjectivePatch r θ 2) :=
  (secondCoordinateSectionsEquiv r θ).symm.toRingHom

def overlapSectionMap (r θ : ℂ) :
    FirstOverlap r θ →+* Γ(projectiveCurve r θ, coordinateOverlapPatch r θ) :=
  (firstOverlapSectionsEquiv r θ).symm.toRingHom

theorem firstSectionMap_coefficient (r θ z : ℂ) :
    firstSectionMap r θ (algebraMap ℂ (FirstChartRing r θ) z) =
      coefficientOn (projectiveCurve r θ).sheaf (projectiveGlobalCoefficient r θ)
        (coordinateProjectivePatch r θ 1) z := by
  apply (firstCoordinateSectionsEquiv r θ).injective
  exact (RingEquiv.apply_symm_apply _ _).trans
    (firstCoordinateSectionsEquiv_coefficient r θ z).symm

theorem secondSectionMap_coefficient (r θ z : ℂ) :
    secondSectionMap r θ (algebraMap ℂ (SecondChartRing r θ) z) =
      coefficientOn (projectiveCurve r θ).sheaf (projectiveGlobalCoefficient r θ)
        (coordinateProjectivePatch r θ 2) z := by
  apply (secondCoordinateSectionsEquiv r θ).injective
  exact (RingEquiv.apply_symm_apply _ _).trans
    (secondCoordinateSectionsEquiv_coefficient r θ z).symm

theorem overlapSectionMap_coefficient (r θ z : ℂ) :
    overlapSectionMap r θ (algebraMap ℂ (FirstOverlap r θ) z) =
      coefficientOn (projectiveCurve r θ).sheaf (projectiveGlobalCoefficient r θ)
        (coordinateOverlapPatch r θ) z := by
  apply (firstOverlapSectionsEquiv r θ).injective
  exact (RingEquiv.apply_symm_apply _ _).trans
    (firstOverlapSectionsEquiv_coefficient r θ z).symm

theorem firstSectionMap_restriction (r θ : ℂ) (a : FirstChartRing r θ) :
    (projectiveCurve r θ).presheaf.map (homOfLE (coordinateOverlap_le_first r θ)).op
        (firstSectionMap r θ a) = overlapSectionMap r θ (CycleQ2GeometricCanonicalOverlap.At.firstChartMap r θ a) := by
  apply (firstOverlapSectionsEquiv r θ).injective
  rw [firstOverlapSectionsEquiv_restriction]
  change algebraMap (FirstChartRing r θ) (FirstOverlap r θ)
      (firstCoordinateSectionsEquiv r θ ((firstCoordinateSectionsEquiv r θ).symm a)) =
    firstOverlapSectionsEquiv r θ ((firstOverlapSectionsEquiv r θ).symm (CycleQ2GeometricCanonicalOverlap.At.firstChartMap r θ a))
  rw [RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
  rfl

theorem secondSectionMap_restriction (r θ : ℂ) (a : SecondChartRing r θ) :
    (projectiveCurve r θ).presheaf.map (homOfLE (coordinateOverlap_le_second r θ)).op
        (secondSectionMap r θ a) = overlapSectionMap r θ (CycleQ2GeometricCanonicalOverlap.At.secondChartMap r θ a) := by
  apply (firstOverlapSectionsEquiv r θ).injective
  rw [overlapSectionsEquiv_compatibility, secondOverlapSectionsEquiv_restriction]
  change overlapEquiv r θ (algebraMap (SecondChartRing r θ) (SecondOverlap r θ)
      (secondCoordinateSectionsEquiv r θ ((secondCoordinateSectionsEquiv r θ).symm a))) =
    firstOverlapSectionsEquiv r θ ((firstOverlapSectionsEquiv r θ).symm (CycleQ2GeometricCanonicalOverlap.At.secondChartMap r θ a))
  rw [RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
  rfl

theorem overlapSectionMap_middle (r θ : ℂ) :
    overlapSectionMap r θ (coordinate (firstEquations r θ) 1) =
      (coordinateMiddleUnit r θ : Γ(projectiveCurve r θ, coordinateOverlapPatch r θ)) := by
  change (firstOverlapSectionsEquiv r θ).symm (coordinate (firstEquations r θ) 1) =
    (firstOverlapSectionsEquiv r θ).symm (middleUnit (firstEquations r θ) : FirstOverlap r θ)
  rw [middleUnit_val]

variable (r θ : ℂ) (h : ChartJacobianCover r θ)
  (M : SheafOfModules.{0} (ringSheaf (projectiveCurve r θ).sheaf))
  (d : M.val.Derivation' (coefficientMap (projectiveCurve r θ).sheaf
    (projectiveGlobalCoefficient r θ)))

local instance projectiveAdditiveSectionsModule (O : (projectiveCurve r θ).Opens) :
    Module Γ(projectiveCurve r θ, O) (M.val.presheaf.obj (op O)) :=
  (M.val.obj (op O)).isModule

/-- The projectively oriented first affine form, in actual sheaf sections. -/
def firstFormSection : M.val.obj (op (coordinateProjectivePatch r θ 1)) :=
  sectionLift (projectiveCurve r θ).sheaf (projectiveGlobalCoefficient r θ)
    M d (coordinateProjectivePatch r θ 1) (firstSectionMap r θ) (firstSectionMap_coefficient r θ)
      (-CycleQ2GeometricChartKaehler.At.firstChartForm r θ h)

/-- The second affine form, in actual sheaf sections. -/
def secondFormSection : M.val.obj (op (coordinateProjectivePatch r θ 2)) :=
  sectionLift (projectiveCurve r θ).sheaf (projectiveGlobalCoefficient r θ)
    M d (coordinateProjectivePatch r θ 2) (secondSectionMap r θ) (secondSectionMap_coefficient r θ)
      (CycleQ2GeometricChartKaehler.At.secondChartForm r θ h)

/-- The entire coordinate-overlap identity now holds in the actual module
sheaf, not only in the affine Kähler module. -/
theorem coordinate_form_transition :
    M.val.presheaf.map (homOfLE (coordinateOverlap_le_second r θ)).op (secondFormSection r θ h M d) =
      (coordinateMiddleUnit r θ : Γ(projectiveCurve r θ, coordinateOverlapPatch r θ)) •
        M.val.presheaf.map (homOfLE (coordinateOverlap_le_first r θ)).op (firstFormSection r θ h M d) := by
  have hfirst := restriction_lift (projectiveCurve r θ).sheaf
    (projectiveGlobalCoefficient r θ) M d _ _ (coordinateOverlap_le_first r θ)
    (firstSectionMap r θ) (firstSectionMap_coefficient r θ)
    (overlapSectionMap r θ) (overlapSectionMap_coefficient r θ) (CycleQ2GeometricCanonicalOverlap.At.firstChartMap r θ)
    (firstSectionMap_restriction r θ) (-CycleQ2GeometricChartKaehler.At.firstChartForm r θ h)
  have hsecond := restriction_lift (projectiveCurve r θ).sheaf
    (projectiveGlobalCoefficient r θ) M d _ _ (coordinateOverlap_le_second r θ)
    (secondSectionMap r θ) (secondSectionMap_coefficient r θ)
    (overlapSectionMap r θ) (overlapSectionMap_coefficient r θ) (CycleQ2GeometricCanonicalOverlap.At.secondChartMap r θ)
    (secondSectionMap_restriction r θ) (CycleQ2GeometricChartKaehler.At.secondChartForm r θ h)
  unfold firstFormSection secondFormSection
  rw [hfirst, hsecond, actual_chart_form_transition, sectionLift_smul]
  exact congrArg (fun a => a •
    sectionLift (projectiveCurve r θ).sheaf (projectiveGlobalCoefficient r θ)
      M d (coordinateOverlapPatch r θ) (overlapSectionMap r θ) (overlapSectionMap_coefficient r θ)
        (differentialMap (CycleQ2GeometricCanonicalOverlap.At.firstChartMap r θ) (-CycleQ2GeometricChartKaehler.At.firstChartForm r θ h)))
    (overlapSectionMap_middle r θ)

def denominatorFirstInclusion : overlapProjectivePatch r θ ⟶ firstProjectivePatch r θ :=
  homOfLE ((overlapProjectivePatch_eq r θ).le.trans inf_le_left)

def denominatorSecondInclusion : overlapProjectivePatch r θ ⟶ secondProjectivePatch r θ :=
  homOfLE ((overlapProjectivePatch_eq r θ).le.trans inf_le_right)

/-- The original transition unit, viewed in the actual acting ring. -/
def denominatorTransitionScalar :
    (ringSheaf (projectiveCurve r θ).sheaf).obj.obj (op (overlapProjectivePatch r θ)) :=
  (projectiveTransitionUnit r θ : Γ(projectiveCurve r θ, overlapProjectivePatch r θ))

/-- The two forms restricted to the original first denominator chart. -/
def firstDenominatorForm : M.val.obj (op (firstProjectivePatch r θ)) :=
  M.val.presheaf.map (homOfLE (firstProjectivePatch_le_firstCoordinate r θ)).op
    (firstFormSection r θ h M d)

/-- The second form on the original second denominator chart. -/
def secondDenominatorForm : M.val.obj (op (secondProjectivePatch r θ)) :=
  M.val.presheaf.map (homOfLE (secondProjectivePatch_le_secondCoordinate r θ)).op
    (secondFormSection r θ h M d)

theorem denominator_form_transition :
    M.val.presheaf.map (denominatorSecondInclusion r θ).op
        (secondDenominatorForm r θ h M d) =
      denominatorTransitionScalar r θ •
        M.val.presheaf.map (denominatorFirstInclusion r θ).op
          (firstDenominatorForm r θ h M d) := by
  have hu := congrArg Units.val (coordinateMiddleUnit_restriction r θ)
  change (projectiveCurve r θ).presheaf.map
      (homOfLE (denominatorOverlap_le_coordinateOverlap r θ)).op
      (coordinateMiddleUnit r θ : Γ(projectiveCurve r θ, coordinateOverlapPatch r θ)) =
    (projectiveTransitionUnit r θ : Γ(projectiveCurve r θ, overlapProjectivePatch r θ)) at hu
  have hsecond := restriction_path M.val.presheaf
    (homOfLE (secondProjectivePatch_le_secondCoordinate r θ)) (denominatorSecondInclusion r θ)
    (homOfLE (coordinateOverlap_le_second r θ))
    (homOfLE (denominatorOverlap_le_coordinateOverlap r θ)) (secondFormSection r θ h M d)
  have hfirst := restriction_path M.val.presheaf
    (homOfLE (firstProjectivePatch_le_firstCoordinate r θ)) (denominatorFirstInclusion r θ)
    (homOfLE (coordinateOverlap_le_first r θ))
    (homOfLE (denominatorOverlap_le_coordinateOverlap r θ)) (firstFormSection r θ h M d)
  apply hsecond.trans
  apply (congrArg
    (M.val.presheaf.map (homOfLE (denominatorOverlap_le_coordinateOverlap r θ)).op)
    (coordinate_form_transition r θ h M d)).trans
  apply (restriction_smul (projectiveCurve r θ).sheaf M
    (denominatorOverlap_le_coordinateOverlap r θ)
    (coordinateMiddleUnit r θ : Γ(projectiveCurve r θ, coordinateOverlapPatch r θ))
    (M.val.presheaf.map (homOfLE (coordinateOverlap_le_first r θ)).op
      (firstFormSection r θ h M d))).trans
  exact (congrArg (fun a => a •
    M.val.presheaf.map (homOfLE (denominatorOverlap_le_coordinateOverlap r θ)).op
      (M.val.presheaf.map (homOfLE (coordinateOverlap_le_first r θ)).op
        (firstFormSection r θ h M d))) hu).trans
    (congrArg (fun s => denominatorTransitionScalar r θ • s) hfirst.symm)

/-- Closed specialization to the actual projective universal differential. -/
theorem projective_differential_transition :
    (projectiveDifferentialSheaf r θ).val.presheaf.map (denominatorSecondInclusion r θ).op
        (secondDenominatorForm r θ h (projectiveDifferentialSheaf r θ)
          (projectiveUniversalDifferential r θ)) =
      denominatorTransitionScalar r θ •
        (projectiveDifferentialSheaf r θ).val.presheaf.map (denominatorFirstInclusion r θ).op
          (firstDenominatorForm r θ h (projectiveDifferentialSheaf r θ)
            (projectiveUniversalDifferential r θ)) :=
  denominator_form_transition r θ h (projectiveDifferentialSheaf r θ)
    (projectiveUniversalDifferential r θ)

end CycleQ2GeometricProjectiveDifferentialForms.At

/-! Sparse specializations retain the original public endpoints. -/
namespace CycleQ2GeometricProjectiveDifferentialForms
open CycleQ2GeometricChartKaehler

abbrev firstSectionMap (r : ℂ) := At.firstSectionMap r 0

abbrev secondSectionMap (r : ℂ) := At.secondSectionMap r 0

abbrev overlapSectionMap (r : ℂ) := At.overlapSectionMap r 0

abbrev firstSectionMap_coefficient (r : ℂ) := At.firstSectionMap_coefficient r 0

abbrev secondSectionMap_coefficient (r : ℂ) := At.secondSectionMap_coefficient r 0

abbrev overlapSectionMap_coefficient (r : ℂ) := At.overlapSectionMap_coefficient r 0

abbrev firstSectionMap_restriction (r : ℂ) := At.firstSectionMap_restriction r 0

abbrev secondSectionMap_restriction (r : ℂ) := At.secondSectionMap_restriction r 0

abbrev overlapSectionMap_middle (r : ℂ) := At.overlapSectionMap_middle r 0

abbrev denominatorFirstInclusion (r : ℂ) := At.denominatorFirstInclusion r 0

abbrev denominatorSecondInclusion (r : ℂ) := At.denominatorSecondInclusion r 0

abbrev denominatorTransitionScalar (r : ℂ) := At.denominatorTransitionScalar r 0

abbrev firstFormSection (r : ℂ) (hr : r ^ 3 = 2) :=
  At.firstFormSection r 0 (sparseChartJacobianCover r hr)

abbrev secondFormSection (r : ℂ) (hr : r ^ 3 = 2) :=
  At.secondFormSection r 0 (sparseChartJacobianCover r hr)

abbrev coordinate_form_transition (r : ℂ) (hr : r ^ 3 = 2) :=
  At.coordinate_form_transition r 0 (sparseChartJacobianCover r hr)

abbrev firstDenominatorForm (r : ℂ) (hr : r ^ 3 = 2) :=
  At.firstDenominatorForm r 0 (sparseChartJacobianCover r hr)

abbrev secondDenominatorForm (r : ℂ) (hr : r ^ 3 = 2) :=
  At.secondDenominatorForm r 0 (sparseChartJacobianCover r hr)

abbrev denominator_form_transition (r : ℂ) (hr : r ^ 3 = 2) :=
  At.denominator_form_transition r 0 (sparseChartJacobianCover r hr)

abbrev projective_differential_transition (r : ℂ) (hr : r ^ 3 = 2) :=
  At.projective_differential_transition r 0 (sparseChartJacobianCover r hr)

#print axioms At.coordinate_form_transition
#print axioms At.denominator_form_transition
#print axioms At.projective_differential_transition

end CycleQ2GeometricProjectiveDifferentialForms
end
