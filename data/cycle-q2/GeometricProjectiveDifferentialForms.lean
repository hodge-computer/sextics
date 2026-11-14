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
namespace CycleQ2GeometricProjectiveDifferentialForms

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
  CycleQ2GeometricDifferentialSheaf CycleQ2GeometricSheafKaehlerMap
  CycleQ2GeometricProjectiveCurve CycleQ2GeometricProjectiveAffine
  CycleQ2GeometricProjectiveAffineCoefficients CycleQ2GeometricProjectiveOverlap
  CycleQ2GeometricProjectiveTransition CycleQ2GeometricAffineCurveCharts
  CycleQ2GeometricAffineOverlap CycleQ2GeometricCanonicalOverlap

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

def firstSectionMap (r : ℂ) :
    FirstChartRing r 0 →+* Γ(projectiveCurve r 0, coordinateProjectivePatch r 0 1) :=
  (firstCoordinateSectionsEquiv r 0).symm.toRingHom

def secondSectionMap (r : ℂ) :
    SecondChartRing r 0 →+* Γ(projectiveCurve r 0, coordinateProjectivePatch r 0 2) :=
  (secondCoordinateSectionsEquiv r 0).symm.toRingHom

def overlapSectionMap (r : ℂ) :
    FirstOverlap r 0 →+* Γ(projectiveCurve r 0, coordinateOverlapPatch r 0) :=
  (firstOverlapSectionsEquiv r 0).symm.toRingHom

theorem firstSectionMap_coefficient (r z : ℂ) :
    firstSectionMap r (algebraMap ℂ (FirstChartRing r 0) z) =
      coefficientOn (projectiveCurve r 0).sheaf (projectiveGlobalCoefficient r 0)
        (coordinateProjectivePatch r 0 1) z := by
  apply (firstCoordinateSectionsEquiv r 0).injective
  exact (RingEquiv.apply_symm_apply _ _).trans
    (firstCoordinateSectionsEquiv_coefficient r 0 z).symm

theorem secondSectionMap_coefficient (r z : ℂ) :
    secondSectionMap r (algebraMap ℂ (SecondChartRing r 0) z) =
      coefficientOn (projectiveCurve r 0).sheaf (projectiveGlobalCoefficient r 0)
        (coordinateProjectivePatch r 0 2) z := by
  apply (secondCoordinateSectionsEquiv r 0).injective
  exact (RingEquiv.apply_symm_apply _ _).trans
    (secondCoordinateSectionsEquiv_coefficient r 0 z).symm

theorem overlapSectionMap_coefficient (r z : ℂ) :
    overlapSectionMap r (algebraMap ℂ (FirstOverlap r 0) z) =
      coefficientOn (projectiveCurve r 0).sheaf (projectiveGlobalCoefficient r 0)
        (coordinateOverlapPatch r 0) z := by
  apply (firstOverlapSectionsEquiv r 0).injective
  exact (RingEquiv.apply_symm_apply _ _).trans
    (firstOverlapSectionsEquiv_coefficient r 0 z).symm

theorem firstSectionMap_restriction (r : ℂ) (a : FirstChartRing r 0) :
    (projectiveCurve r 0).presheaf.map (homOfLE (coordinateOverlap_le_first r 0)).op
        (firstSectionMap r a) = overlapSectionMap r (firstChartMap r a) := by
  apply (firstOverlapSectionsEquiv r 0).injective
  rw [firstOverlapSectionsEquiv_restriction]
  change algebraMap (FirstChartRing r 0) (FirstOverlap r 0)
      (firstCoordinateSectionsEquiv r 0 ((firstCoordinateSectionsEquiv r 0).symm a)) =
    firstOverlapSectionsEquiv r 0 ((firstOverlapSectionsEquiv r 0).symm (firstChartMap r a))
  rw [RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
  rfl

theorem secondSectionMap_restriction (r : ℂ) (a : SecondChartRing r 0) :
    (projectiveCurve r 0).presheaf.map (homOfLE (coordinateOverlap_le_second r 0)).op
        (secondSectionMap r a) = overlapSectionMap r (secondChartMap r a) := by
  apply (firstOverlapSectionsEquiv r 0).injective
  rw [overlapSectionsEquiv_compatibility, secondOverlapSectionsEquiv_restriction]
  change overlapEquiv r 0 (algebraMap (SecondChartRing r 0) (SecondOverlap r 0)
      (secondCoordinateSectionsEquiv r 0 ((secondCoordinateSectionsEquiv r 0).symm a))) =
    firstOverlapSectionsEquiv r 0 ((firstOverlapSectionsEquiv r 0).symm (secondChartMap r a))
  rw [RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
  rfl

theorem overlapSectionMap_middle (r : ℂ) :
    overlapSectionMap r (coordinate (firstEquations r 0) 1) =
      (coordinateMiddleUnit r 0 : Γ(projectiveCurve r 0, coordinateOverlapPatch r 0)) := by
  change (firstOverlapSectionsEquiv r 0).symm (coordinate (firstEquations r 0) 1) =
    (firstOverlapSectionsEquiv r 0).symm (middleUnit (firstEquations r 0) : FirstOverlap r 0)
  rw [middleUnit_val]

variable (r : ℂ) (hr : r ^ 3 = 2)
  (M : SheafOfModules.{0} (ringSheaf (projectiveCurve r 0).sheaf))
  (d : M.val.Derivation' (coefficientMap (projectiveCurve r 0).sheaf
    (projectiveGlobalCoefficient r 0)))

local instance projectiveAdditiveSectionsModule (O : (projectiveCurve r 0).Opens) :
    Module Γ(projectiveCurve r 0, O) (M.val.presheaf.obj (op O)) :=
  (M.val.obj (op O)).isModule

/-- The projectively oriented first affine form, in actual sheaf sections. -/
def firstFormSection : M.val.obj (op (coordinateProjectivePatch r 0 1)) :=
  sectionLift (projectiveCurve r 0).sheaf (projectiveGlobalCoefficient r 0)
    M d (coordinateProjectivePatch r 0 1) (firstSectionMap r) (firstSectionMap_coefficient r)
      (-CycleQ2GeometricChartKaehler.firstChartForm r hr)

/-- The second affine form, in actual sheaf sections. -/
def secondFormSection : M.val.obj (op (coordinateProjectivePatch r 0 2)) :=
  sectionLift (projectiveCurve r 0).sheaf (projectiveGlobalCoefficient r 0)
    M d (coordinateProjectivePatch r 0 2) (secondSectionMap r) (secondSectionMap_coefficient r)
      (CycleQ2GeometricChartKaehler.secondChartForm r hr)

/-- The entire coordinate-overlap identity now holds in the actual module
sheaf, not only in the affine Kähler module. -/
theorem coordinate_form_transition :
    M.val.presheaf.map (homOfLE (coordinateOverlap_le_second r 0)).op (secondFormSection r hr M d) =
      (coordinateMiddleUnit r 0 : Γ(projectiveCurve r 0, coordinateOverlapPatch r 0)) •
        M.val.presheaf.map (homOfLE (coordinateOverlap_le_first r 0)).op (firstFormSection r hr M d) := by
  have hfirst := restriction_lift (projectiveCurve r 0).sheaf
    (projectiveGlobalCoefficient r 0) M d _ _ (coordinateOverlap_le_first r 0)
    (firstSectionMap r) (firstSectionMap_coefficient r)
    (overlapSectionMap r) (overlapSectionMap_coefficient r) (firstChartMap r)
    (firstSectionMap_restriction r) (-CycleQ2GeometricChartKaehler.firstChartForm r hr)
  have hsecond := restriction_lift (projectiveCurve r 0).sheaf
    (projectiveGlobalCoefficient r 0) M d _ _ (coordinateOverlap_le_second r 0)
    (secondSectionMap r) (secondSectionMap_coefficient r)
    (overlapSectionMap r) (overlapSectionMap_coefficient r) (secondChartMap r)
    (secondSectionMap_restriction r) (CycleQ2GeometricChartKaehler.secondChartForm r hr)
  unfold firstFormSection secondFormSection
  rw [hfirst, hsecond, actual_chart_form_transition, sectionLift_smul]
  exact congrArg (fun a => a •
    sectionLift (projectiveCurve r 0).sheaf (projectiveGlobalCoefficient r 0)
      M d (coordinateOverlapPatch r 0) (overlapSectionMap r) (overlapSectionMap_coefficient r)
        (differentialMap (firstChartMap r) (-CycleQ2GeometricChartKaehler.firstChartForm r hr)))
    (overlapSectionMap_middle r)

def denominatorFirstInclusion : overlapProjectivePatch r 0 ⟶ firstProjectivePatch r 0 :=
  homOfLE ((overlapProjectivePatch_eq r 0).le.trans inf_le_left)

def denominatorSecondInclusion : overlapProjectivePatch r 0 ⟶ secondProjectivePatch r 0 :=
  homOfLE ((overlapProjectivePatch_eq r 0).le.trans inf_le_right)

/-- The original transition unit, viewed in the actual acting ring. -/
def denominatorTransitionScalar :
    (ringSheaf (projectiveCurve r 0).sheaf).obj.obj (op (overlapProjectivePatch r 0)) :=
  (projectiveTransitionUnit r 0 : Γ(projectiveCurve r 0, overlapProjectivePatch r 0))

/-- The two forms restricted to the original first denominator chart. -/
def firstDenominatorForm : M.val.obj (op (firstProjectivePatch r 0)) :=
  M.val.presheaf.map (homOfLE (firstProjectivePatch_le_firstCoordinate r 0)).op
    (firstFormSection r hr M d)

/-- The second form on the original second denominator chart. -/
def secondDenominatorForm : M.val.obj (op (secondProjectivePatch r 0)) :=
  M.val.presheaf.map (homOfLE (secondProjectivePatch_le_secondCoordinate r 0)).op
    (secondFormSection r hr M d)

theorem denominator_form_transition :
    M.val.presheaf.map (denominatorSecondInclusion r).op
        (secondDenominatorForm r hr M d) =
      denominatorTransitionScalar r •
        M.val.presheaf.map (denominatorFirstInclusion r).op
          (firstDenominatorForm r hr M d) := by
  have hu := congrArg Units.val (coordinateMiddleUnit_restriction r 0)
  change (projectiveCurve r 0).presheaf.map
      (homOfLE (denominatorOverlap_le_coordinateOverlap r 0)).op
      (coordinateMiddleUnit r 0 : Γ(projectiveCurve r 0, coordinateOverlapPatch r 0)) =
    (projectiveTransitionUnit r 0 : Γ(projectiveCurve r 0, overlapProjectivePatch r 0)) at hu
  have hsecond := restriction_path M.val.presheaf
    (homOfLE (secondProjectivePatch_le_secondCoordinate r 0)) (denominatorSecondInclusion r)
    (homOfLE (coordinateOverlap_le_second r 0))
    (homOfLE (denominatorOverlap_le_coordinateOverlap r 0)) (secondFormSection r hr M d)
  have hfirst := restriction_path M.val.presheaf
    (homOfLE (firstProjectivePatch_le_firstCoordinate r 0)) (denominatorFirstInclusion r)
    (homOfLE (coordinateOverlap_le_first r 0))
    (homOfLE (denominatorOverlap_le_coordinateOverlap r 0)) (firstFormSection r hr M d)
  apply hsecond.trans
  apply (congrArg
    (M.val.presheaf.map (homOfLE (denominatorOverlap_le_coordinateOverlap r 0)).op)
    (coordinate_form_transition r hr M d)).trans
  apply (restriction_smul (projectiveCurve r 0).sheaf M
    (denominatorOverlap_le_coordinateOverlap r 0)
    (coordinateMiddleUnit r 0 : Γ(projectiveCurve r 0, coordinateOverlapPatch r 0))
    (M.val.presheaf.map (homOfLE (coordinateOverlap_le_first r 0)).op
      (firstFormSection r hr M d))).trans
  exact (congrArg (fun a => a •
    M.val.presheaf.map (homOfLE (denominatorOverlap_le_coordinateOverlap r 0)).op
      (M.val.presheaf.map (homOfLE (coordinateOverlap_le_first r 0)).op
        (firstFormSection r hr M d))) hu).trans
    (congrArg (fun s => denominatorTransitionScalar r • s) hfirst.symm)

/-- Closed specialization to the actual projective universal differential. -/
theorem projective_differential_transition :
    (projectiveDifferentialSheaf r 0).val.presheaf.map (denominatorSecondInclusion r).op
        (secondDenominatorForm r hr (projectiveDifferentialSheaf r 0)
          (projectiveUniversalDifferential r 0)) =
      denominatorTransitionScalar r •
        (projectiveDifferentialSheaf r 0).val.presheaf.map (denominatorFirstInclusion r).op
          (firstDenominatorForm r hr (projectiveDifferentialSheaf r 0)
            (projectiveUniversalDifferential r 0)) :=
  denominator_form_transition r hr (projectiveDifferentialSheaf r 0)
    (projectiveUniversalDifferential r 0)

#print axioms coordinate_form_transition
#print axioms denominator_form_transition
#print axioms projective_differential_transition

end CycleQ2GeometricProjectiveDifferentialForms
end
