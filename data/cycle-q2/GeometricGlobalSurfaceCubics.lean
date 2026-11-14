import Proposal.GeometricFullSurfaceResidueCover
import Proposal.GeometricSurfaceFirstThirdTransition
import Proposal.GeometricSurfaceSecondThirdTransition

/-!
# Global cubic two-forms on the actual literal projective surface

Source-only draft: compilation and independent kernel replay were
deferred at the user's request. Cubic residue sections are glued over
the complete three-coordinate augmented-Jacobian cover. Their restrictions
are the original normal-neighborhood sections, with the same orientation.
There is no global-section extension hypothesis in the construction.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2GlobalSurfaceCubics

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry MvPolynomial
open CycleQ2SeedTrace CycleQ2CartierProjectiveCover
  CycleQ2GeometricSurfaceAdjunction CycleQ2GeometricSurfaceDehomogenizedCharts
  CycleQ2GeometricSurfaceCoefficients CycleQ2GeometricAffineChartSections
  CycleQ2GeometricExteriorSheaf CycleQ2ChartExteriorBinding
  CycleQ2SurfaceResidueSheafOverlap CycleQ2SurfaceCommonOpen
  CycleQ2SurfaceSameChartResidueSections CycleQ2ThirdSurfaceChart
  CycleQ2FullSurfaceResidueCover

abbrev WeightedCubic := CycleQ2SurfaceCubicGluing.WeightedCubic
abbrev CanonicalForms := surfaceExteriorSheaf (57 : ℂ) 1
abbrev AdditiveForms := CycleQ2SurfaceCubicGluing.additiveExteriorSheaf (57 : ℂ) 1

local instance sectionModule (O : Surface.Opens) :
    Module Γ(Surface, O) (CanonicalForms.val.obj (op O)) :=
  (CanonicalForms.val.obj (op O)).isModule

private theorem thirdCubicSection_restrict (n t : SurfacePoly) (p : WeightedPoly)
    {V W : Over (thirdPatchOpen (57 : ℂ) 1 n t)} (k : V ⟶ W) :
    CanonicalForms.val.map k.left.op (thirdCubicSection 57 1 n t p W) =
      thirdCubicSection 57 1 n t p V := by
  have hres : CanonicalForms.val.map k.left.op
      (chartResidueSheafSection (projectiveToComplex 57 1) (thirdEquations 57 1) n t
        (thirdPatchChart 57 1 n t) (thirdPatchChart_overComplex 57 1 n t) W) =
    chartResidueSheafSection (projectiveToComplex 57 1) (thirdEquations 57 1) n t
      (thirdPatchChart 57 1 n t) (thirdPatchChart_overComplex 57 1 n t) V :=
    (congrArg (CanonicalForms.val.map k.left.op)
      (chartResidueSheafSection_eq_canonical (projectiveToComplex 57 1)
        (thirdEquations 57 1) n t (thirdPatchChart 57 1 n t)
        (thirdPatchChart_overComplex 57 1 n t) W)).trans
      ((chartExteriorSheafSection_restrict (thirdPatchChart 57 1 n t)
        (projectiveToComplex 57 1) (thirdPatchChart_overComplex 57 1 n t) k 2
        (localSurfaceResidueForm (thirdEquations 57 1) n t)).trans
        (chartResidueSheafSection_eq_canonical (projectiveToComplex 57 1)
          (thirdEquations 57 1) n t (thirdPatchChart 57 1 n t)
          (thirdPatchChart_overComplex 57 1 n t) V).symm)
  unfold thirdCubicSection
  rw [CanonicalForms.val.map_smul, chartSection_naturality, hres]

/-- The original first and second sections, with the positive third-chart
residue added on every augmented Jacobian pair. -/
def localSectionOn (p : WeightedPoly) (a : PatchIndex) (O : Surface.Opens)
    (hO : O ≤ patchOpen a) : CanonicalForms.val.obj (op O) := by
  rcases a with ⟨i,n,t⟩
  fin_cases i
  · exact firstCubicSection 57 1 n t p (Over.mk (homOfLE hO))
  · exact secondCubicSection 57 1 n t p (Over.mk (homOfLE hO))
  · exact thirdCubicSection 57 1 n t p (Over.mk (homOfLE hO))

def localSection (p : WeightedPoly) (a : PatchIndex) :=
  localSectionOn p a (patchOpen a) le_rfl

theorem localSectionOn_restrict (p : WeightedPoly) (a : PatchIndex)
    {O P : Surface.Opens} (hPO : P ≤ O) (hO : O ≤ patchOpen a) :
    CanonicalForms.val.map (homOfLE hPO).op (localSectionOn p a O hO) =
      localSectionOn p a P (hPO.trans hO) := by
  rcases a with ⟨i,n,t⟩
  fin_cases i
  · exact CycleQ2SurfaceCubicGluing.firstCubicSection_restrict 57 1 n t p
      (V := Over.mk (homOfLE (hPO.trans hO))) (W := Over.mk (homOfLE hO))
      (Over.homMk (homOfLE hPO))
  · exact CycleQ2SurfaceCubicGluing.secondCubicSection_restrict 57 1 n t p
      (V := Over.mk (homOfLE (hPO.trans hO))) (W := Over.mk (homOfLE hO))
      (Over.homMk (homOfLE hPO))
  · exact thirdCubicSection_restrict n t p
      (V := Over.mk (homOfLE (hPO.trans hO))) (W := Over.mk (homOfLE hO))
      (Over.homMk (homOfLE hPO))

/-- All nine chart-pair cases are the actual residue comparisons. -/
theorem localSectionOn_pairwise (p : WeightedCubic)
    (a b : PatchIndex) (O : Surface.Opens)
    (ha : O ≤ patchOpen a) (hb : O ≤ patchOpen b) :
    localSectionOn p.val a O ha = localSectionOn p.val b O hb := by
  rcases a with ⟨i,n₁,t₁⟩
  rcases b with ⟨j,n₂,t₂⟩
  fin_cases i <;> fin_cases j
  · exact (first_coefficient_section_independent 57 1 n₁ t₁ n₂ t₂
      (firstSurfaceDehomogenize p.val) (Over.mk (homOfLE (le_inf ha hb)))).symm
  · exact CycleQ2SurfaceResidueSheafOverlap.orientedCubicSections_agree
      57 1 n₁ t₁ n₂ t₂ p.val p.property (Over.mk (homOfLE (le_inf ha hb)))
  · exact CycleQ2SurfaceFirstThirdTransition.orientedCubicSections_agree
      57 1 n₁ t₁ n₂ t₂ p.val p.property (Over.mk (homOfLE (le_inf ha hb)))
  · exact (CycleQ2SurfaceResidueSheafOverlap.orientedCubicSections_agree
      57 1 n₂ t₂ n₁ t₁ p.val p.property (Over.mk (homOfLE (le_inf hb ha)))).symm
  · exact congrArg (fun s : CanonicalForms.val.obj (op O) => -s)
      (second_coefficient_section_independent 57 1 n₁ t₁ n₂ t₂
        (secondSurfaceDehomogenize p.val) (Over.mk (homOfLE (le_inf ha hb)))).symm
  · exact CycleQ2SurfaceSecondThirdTransition.orientedCubicSections_agree
      57 1 n₁ t₁ n₂ t₂ p.val p.property (Over.mk (homOfLE (le_inf ha hb)))
  · exact (CycleQ2SurfaceFirstThirdTransition.orientedCubicSections_agree
      57 1 n₂ t₂ n₁ t₁ p.val p.property (Over.mk (homOfLE (le_inf hb ha)))).symm
  · exact (CycleQ2SurfaceSecondThirdTransition.orientedCubicSections_agree
      57 1 n₂ t₂ n₁ t₁ p.val p.property (Over.mk (homOfLE (le_inf hb ha)))).symm
  · exact (coefficient_section_independent (thirdEquations 57 1) n₁ t₁ n₂ t₂
      (thirdAffineChart 57 1) (projectiveToComplex 57 1) (thirdAffineChart_overComplex 57 1)
      (Over.mk (homOfLE (le_inf ha hb))) (thirdDehomogenize p.val)).symm

theorem localSections_compatible (p : WeightedCubic) :
    TopCat.Presheaf.IsCompatible AdditiveForms.obj patchOpen (localSection p.val) := by
  intro a b
  exact (localSectionOn_restrict p.val a inf_le_left le_rfl).trans
    ((localSectionOn_pairwise p a b _ inf_le_left inf_le_right).trans
      (localSectionOn_restrict p.val b inf_le_right le_rfl).symm)

/-- Existence is actual sheaf gluing over the proved full surface cover. -/
theorem existsUnique_globalCubicSection (p : WeightedCubic) :
    ∃! s : CanonicalForms.val.obj (op (⊤ : Surface.Opens)), ∀ a : PatchIndex,
      CanonicalForms.val.map (homOfLE (show patchOpen a ≤ ⊤ from le_top)).op s =
        localSection p.val a :=
  AdditiveForms.existsUnique_gluing' patchOpen ⊤ (fun _ => homOfLE le_top)
    patchOpen_cover.ge (localSection p.val) (localSections_compatible p)

def globalCubicSection (p : WeightedCubic) : CanonicalForms.val.obj (op (⊤ : Surface.Opens)) :=
  Classical.choose (existsUnique_globalCubicSection p)

theorem globalCubicSection_restrict_patch (p : WeightedCubic) (a : PatchIndex) :
    CanonicalForms.val.map (homOfLE (show patchOpen a ≤ ⊤ from le_top)).op
      (globalCubicSection p) = localSection p.val a :=
  (Classical.choose_spec (existsUnique_globalCubicSection p)).1 a

theorem globalCubicSection_restrict_subopen (p : WeightedCubic) (a : PatchIndex)
    (O : Surface.Opens) (hO : O ≤ patchOpen a) :
    CanonicalForms.val.map (homOfLE (show O ≤ ⊤ from le_top)).op
      (globalCubicSection p) = localSectionOn p.val a O hO := by
  have h := CanonicalForms.val.map_comp_apply
    (homOfLE (show patchOpen a ≤ ⊤ from le_top)).op (homOfLE hO).op (globalCubicSection p)
  exact h.trans ((congrArg (fun s => CanonicalForms.val.map (homOfLE hO).op s)
    (globalCubicSection_restrict_patch p a)).trans
    (localSectionOn_restrict p.val a hO le_rfl))

/-- The full global form restricts to the unchanged original local section. -/
theorem globalCubicSection_restrict_original (p : WeightedCubic)
    (a : CycleQ2SurfaceCubicGluing.PatchIndex) (O : Surface.Opens)
    (hO : O ≤ CycleQ2SurfaceCubicGluing.patchOpen 57 1 a) :
    CanonicalForms.val.map (homOfLE (show O ≤ ⊤ from le_top)).op
      (globalCubicSection p) = CycleQ2SurfaceCubicGluing.localSectionOn 57 1 p.val a O hO := by
  have hO' : O ≤ patchOpen (originalIndex a) := hO.trans (patchOpen_originalIndex a).ge
  have h := globalCubicSection_restrict_subopen p (originalIndex a) O hO'
  cases a <;> exact h

/-- Uniqueness of the original neighborhood gluing fixes the normalization
of the extension, rather than choosing a new cubic section near the curve. -/
theorem globalCubicSection_restrict_neighborhood (p : WeightedCubic) :
    CanonicalForms.val.map
      (homOfLE (show CycleQ2SurfaceCubicGluing.neighborhood 57 1 ≤ ⊤ from le_top)).op
      (globalCubicSection p) = CycleQ2SurfaceCubicGluing.gluedCubicSection 57 1 p := by
  apply CycleQ2SurfaceCubicGluing.gluedCubicSection_unique 57 1 p
  intro a
  rw [← PresheafOfModules.map_comp_apply]
  exact globalCubicSection_restrict_original p a
    (CycleQ2SurfaceCubicGluing.patchOpen 57 1 a) le_rfl

#print axioms localSectionOn_pairwise
#print axioms existsUnique_globalCubicSection
#print axioms globalCubicSection
#print axioms globalCubicSection_restrict_original
#print axioms globalCubicSection_restrict_neighborhood

end CycleQ2GlobalSurfaceCubics

end
