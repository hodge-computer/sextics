import Proposal.GeometricFullSurfaceResidueCover
import Proposal.GeometricExteriorLocalFrames
import Proposal.GeometricSurfaceResidueFunctoriality
import Proposal.GeometricAffineCohomology

/-!
# Canonical-form frames on the three whole surface coordinate charts

Status: source-only proof draft. Compilation and independent kernel replay
are deferred at the user's request. No new axioms or admissions are used.

On a fixed affine coordinate chart, the actual determinant residue is
independent of the augmented Jacobian pair used to compute it. The genuine
local exterior-sheaf frames therefore have equal inverse-one generators.
The previously constructed arbitrary-cover sheaf gluing produces a frame
on the entire coordinate open. The all-minor cover supplies the cover;
the old normal-chart neighborhood is not used as a cover of the surface.

Every frame here uses the positive raw affine residue. The separate
projective cubic sections retain their established (+,-,+) orientation.
The local formulas below identify the glued frame with the unchanged raw
frame on every augmented-Jacobian patch and every subopen of that patch.
The actual affine charts and these frames then give the three canonical
sheaf H′¹ vanishings needed by the degree-two Čech comparison.

The geometric strategy is due to Ben Diamond and the cited work of Claire
Voisin. Prepared for fqlx with OpenAI ChatGPT assistance.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2SurfaceCoordinateFrames

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry MvPolynomial
open CycleQ2CartierProjectiveCover CycleQ2GeometricSurfaceAdjunction
  CycleQ2GeometricSurfaceDehomogenizedCharts CycleQ2GeometricSurfaceJacobianCharts
  CycleQ2GeometricSurfaceCoefficients CycleQ2GeometricAffineChartSections
  CycleQ2GeometricExteriorSheaf CycleQ2GeometricCanonicalGluing
  CycleQ2GeometricExteriorLocalFrames CycleQ2SurfaceResidueSheafOverlap
  CycleQ2SurfaceCommonOpen CycleQ2SurfaceSameChartResidueSections CycleQ2ThirdSurfaceChart
  CycleQ2FullSurfaceResidueCover CycleQ2LocalFrameGluing

abbrev Surface := projectiveSurface (57 : ℂ) 1
abbrev CanonicalForms := surfaceExteriorSheaf (57 : ℂ) 1

section SameChart

variable {X : Scheme.{0}} {U : X.Opens}
  (v : Fin 2 → SurfacePoly) (n₁ t₁ n₂ t₂ : SurfacePoly)
  (e : U.toScheme ≅ Spec (CommRingCat.of (SurfaceChartRing v)))
  (f : X ⟶ Spec (CommRingCat.of ℂ))
  (h : e.inv ≫ U.ι ≫ f =
    Spec.map (CommRingCat.ofHom (algebraMap ℂ (SurfaceChartRing v))))

/-- The same-chart residue identity identifies the actual inverse generators
of the sheafified exterior frames, on an arbitrary common subopen. -/
theorem chartResidueFrame_generator_agreement (O : X.Opens)
    (h₁ : O ≤ principalOpen e (augmentedJacobian v n₁ t₁))
    (h₂ : O ≤ principalOpen e (augmentedJacobian v n₂ t₂)) :
    frameGenerator
        (chartResidueLocalFrame f v n₁ t₁
          (principalChart e (augmentedJacobian v n₁ t₁))
          (principalChart_overComplex e (augmentedJacobian v n₁ t₁) f h)) O h₁ =
      frameGenerator
        (chartResidueLocalFrame f v n₂ t₂
          (principalChart e (augmentedJacobian v n₂ t₂))
          (principalChart_overComplex e (augmentedJacobian v n₂ t₂) f h)) O h₂ := by
  rw [chartResidueLocalFrame_generator, chartResidueLocalFrame_generator]
  exact (section_independent v n₁ t₁ n₂ t₂ e f h
    (Over.mk (homOfLE (le_inf h₁ h₂)))).symm

end SameChart

/-- Raw positive residue frame on every augmented patch of each coordinate
chart, including augmented pairs that are not among the original normal pairs. -/
def rawExteriorFrame : (i : Fin 3) → (n t : SurfacePoly) →
    LocalFrame Surface.sheaf CanonicalForms (patchOpen (i, n, t))
  | 0, n, t =>
      chartResidueLocalFrame (projectiveToComplex 57 1) (firstEquations 57 1) n t
        (firstPatchChart 57 1 n t) (firstPatchChart_overComplex 57 1 n t)
  | 1, n, t =>
      chartResidueLocalFrame (projectiveToComplex 57 1) (secondEquations 57 1) n t
        (secondPatchChart 57 1 n t) (secondPatchChart_overComplex 57 1 n t)
  | 2, n, t =>
      chartResidueLocalFrame (projectiveToComplex 57 1) (thirdEquations 57 1) n t
        (thirdPatchChart 57 1 n t) (thirdPatchChart_overComplex 57 1 n t)

theorem rawExteriorFrame_generator_agreement (i : Fin 3)
    (n₁ t₁ n₂ t₂ : SurfacePoly) (O : Surface.Opens)
    (h₁ : O ≤ patchOpen (i, n₁, t₁)) (h₂ : O ≤ patchOpen (i, n₂, t₂)) :
    frameGenerator (rawExteriorFrame i n₁ t₁) O h₁ =
      frameGenerator (rawExteriorFrame i n₂ t₂) O h₂ := by
  fin_cases i
  · exact chartResidueFrame_generator_agreement (firstEquations 57 1) n₁ t₁ n₂ t₂
      (firstAffineChart 57 1) (projectiveToComplex 57 1)
      (firstAffineChart_overComplex 57 1) O h₁ h₂
  · exact chartResidueFrame_generator_agreement (secondEquations 57 1) n₁ t₁ n₂ t₂
      (secondAffineChart 57 1) (projectiveToComplex 57 1)
      (secondAffineChart_overComplex 57 1) O h₁ h₂
  · exact chartResidueFrame_generator_agreement (thirdEquations 57 1) n₁ t₁ n₂ t₂
      (thirdAffineChart 57 1) (projectiveToComplex 57 1)
      (thirdAffineChart_overComplex 57 1) O h₁ h₂

def coordinateResidueCover (i : Fin 3) (a : SurfacePoly × SurfacePoly) : Surface.Opens :=
  patchOpen (i, a.1, a.2)

theorem coordinateResidueCover_le (i : Fin 3) (a : SurfacePoly × SurfacePoly) :
    coordinateResidueCover i a ≤ coordinateOpen i :=
  patchOpen_le (i, a.1, a.2)

/-- The finite coordinate-minor cover is contained in the family of all
augmented pairs, and all such patches lie in the same coordinate open. -/
theorem coordinateResidueCover_eq (i : Fin 3) :
    (⨆ a, coordinateResidueCover i a) = coordinateOpen i := by
  apply le_antisymm
  · exact iSup_le (coordinateResidueCover_le i)
  · rw [← coordinate_minor_cover i]
    apply iSup_le
    intro a
    apply iSup_le
    intro b
    exact le_iSup (coordinateResidueCover i)
      (X (CycleQ2FullSurfaceJacobianCover.variableIndex a),
        X (CycleQ2FullSurfaceJacobianCover.variableIndex b))

private def frameFamily (i : Fin 3) (a : SurfacePoly × SurfacePoly) :
    LocalFrame Surface.sheaf CanonicalForms (coordinateResidueCover i a) :=
  rawExteriorFrame i a.1 a.2

private theorem frameFamily_generators (i : Fin 3)
    (a b : SurfacePoly × SurfacePoly) :
    frameGenerator (frameFamily i a)
        (coordinateResidueCover i a ⊓ coordinateResidueCover i b) inf_le_left =
      frameGenerator (frameFamily i b)
        (coordinateResidueCover i a ⊓ coordinateResidueCover i b) inf_le_right :=
  rawExteriorFrame_generator_agreement i a.1 a.2 b.1 b.2 _ inf_le_left inf_le_right

/-- A genuine frame of Ω² on the whole coordinate chart X1, X2, or X3.
Both directions and naturality come from the actual sheaf gluing theorem. -/
def coordinateExteriorFrame (i : Fin 3) :
    LocalFrame Surface.sheaf CanonicalForms (coordinateOpen i) :=
  glueLocalFrames Surface.sheaf CanonicalForms (coordinateOpen i)
    (coordinateResidueCover i) (coordinateResidueCover_le i)
    (coordinateResidueCover_eq i).ge (frameFamily i) (frameFamily_generators i)

/-- The glued coordinate map retains the exact raw residue coordinate on
every augmented patch, for arbitrary sections of the actual exterior sheaf. -/
theorem coordinateExteriorFrame_app (i : Fin 3) (n t : SurfacePoly)
    (O : Surface.Opens) (hO : O ≤ patchOpen (i, n, t))
    (s : CanonicalForms.val.obj (op O)) :
    (coordinateExteriorFrame i).app O (hO.trans (patchOpen_le (i, n, t))) s =
      (rawExteriorFrame i n t).app O hO s :=
  glueLocalFrames_app Surface.sheaf CanonicalForms (coordinateOpen i)
    (coordinateResidueCover i) (coordinateResidueCover_le i)
    (coordinateResidueCover_eq i).ge (frameFamily i) (frameFamily_generators i)
    (n, t) O hO s

/-- The inverse coordinate maps also agree on arbitrary scalars. -/
theorem coordinateExteriorFrame_symm_app (i : Fin 3) (n t : SurfacePoly)
    (O : Surface.Opens) (hO : O ≤ patchOpen (i, n, t)) (a : Γ(Surface, O)) :
    ((coordinateExteriorFrame i).app O (hO.trans (patchOpen_le (i, n, t)))).symm a =
      ((rawExteriorFrame i n t).app O hO).symm a :=
  glueLocalFrames_symm_app Surface.sheaf CanonicalForms (coordinateOpen i)
    (coordinateResidueCover i) (coordinateResidueCover_le i)
    (coordinateResidueCover_eq i).ge (frameFamily i) (frameFamily_generators i)
    (n, t) O hO a

theorem coordinateExteriorFrame_generator (i : Fin 3) (n t : SurfacePoly)
    (O : Surface.Opens) (hO : O ≤ patchOpen (i, n, t)) :
    frameGenerator (coordinateExteriorFrame i) O
        (hO.trans (patchOpen_le (i, n, t))) =
      frameGenerator (rawExteriorFrame i n t) O hO :=
  coordinateExteriorFrame_symm_app i n t O hO 1

/-- Restricting a section from the whole coordinate chart gives the original
raw coordinate on any smaller augmented patch. -/
theorem coordinateExteriorFrame_restrict (i : Fin 3) (n t : SurfacePoly)
    {O P : Surface.Opens} (hO : O ≤ coordinateOpen i) (hPO : P ≤ O)
    (hP : P ≤ patchOpen (i, n, t)) (s : CanonicalForms.val.obj (op O)) :
    Surface.presheaf.map (homOfLE hPO).op ((coordinateExteriorFrame i).app O hO s) =
      (rawExteriorFrame i n t).app P hP
        (CanonicalForms.val.map (homOfLE hPO).op s) := by
  calc
    _ = (coordinateExteriorFrame i).app P (hPO.trans hO)
        (CanonicalForms.val.map (homOfLE hPO).op s) :=
      (coordinateExteriorFrame i).naturality hPO hO s
    _ = _ := coordinateExteriorFrame_app i n t P hP _

/-- Literal raw-residue binding on the first coordinate chart. -/
theorem coordinateExteriorFrame_first_generator (n t : SurfacePoly)
    (O : Surface.Opens) (hO : O ≤ firstPatchOpen 57 1 n t) :
    frameGenerator (coordinateExteriorFrame 0) O
        (hO.trans (firstPatchOpen_le 57 1 n t)) =
      chartResidueSheafSection (projectiveToComplex 57 1) (firstEquations 57 1) n t
        (firstPatchChart 57 1 n t) (firstPatchChart_overComplex 57 1 n t)
        (Over.mk (homOfLE hO)) :=
  (coordinateExteriorFrame_generator 0 n t O hO).trans
    (chartResidueLocalFrame_generator (projectiveToComplex 57 1)
      (firstEquations 57 1) n t (firstPatchChart 57 1 n t)
      (firstPatchChart_overComplex 57 1 n t) O hO)

/-- The whole second chart uses the positive raw residue; the negative
orientation of cubic sections is retained in their separate definition. -/
theorem coordinateExteriorFrame_second_generator (n t : SurfacePoly)
    (O : Surface.Opens) (hO : O ≤ secondPatchOpen 57 1 n t) :
    frameGenerator (coordinateExteriorFrame 1) O
        (hO.trans (secondPatchOpen_le 57 1 n t)) =
      chartResidueSheafSection (projectiveToComplex 57 1) (secondEquations 57 1) n t
        (secondPatchChart 57 1 n t) (secondPatchChart_overComplex 57 1 n t)
        (Over.mk (homOfLE hO)) :=
  (coordinateExteriorFrame_generator 1 n t O hO).trans
    (chartResidueLocalFrame_generator (projectiveToComplex 57 1)
      (secondEquations 57 1) n t (secondPatchChart 57 1 n t)
      (secondPatchChart_overComplex 57 1 n t) O hO)

/-- Literal raw-residue binding on the third coordinate chart. -/
theorem coordinateExteriorFrame_third_generator (n t : SurfacePoly)
    (O : Surface.Opens) (hO : O ≤ thirdPatchOpen 57 1 n t) :
    frameGenerator (coordinateExteriorFrame 2) O
        (hO.trans (thirdPatchOpen_le 57 1 n t)) =
      chartResidueSheafSection (projectiveToComplex 57 1) (thirdEquations 57 1) n t
        (thirdPatchChart 57 1 n t) (thirdPatchChart_overComplex 57 1 n t)
        (Over.mk (homOfLE hO)) :=
  (coordinateExteriorFrame_generator 2 n t O hO).trans
    (chartResidueLocalFrame_generator (projectiveToComplex 57 1)
      (thirdEquations 57 1) n t (thirdPatchChart 57 1 n t)
      (thirdPatchChart_overComplex 57 1 n t) O hO)

section Cohomology

open CycleQ2GeometricProjectiveHOne

/-- The same actual canonical sheaf, with its additive structure retained. -/
abbrev canonicalAdditiveSheaf :
    Sheaf (Opens.grothendieckTopology Surface) AddCommGrpCat.{0} :=
  CycleQ2GeometricModuleLocalIso.addSheaf CanonicalForms

/-- Forgetting the genuine coordinate frame gives the required additive
frame against the actual structure sheaf, including all restriction maps. -/
def coordinateCanonicalAdditiveFrame (i : Fin 3) :
    CycleQ2GeometricSheafLocalIso.PatchIso canonicalAdditiveSheaf
      (structureAdditiveSheaf Surface) (coordinateOpen i) where
  app O hO := ((coordinateExteriorFrame i).app O hO).toAddEquiv
  naturality hPO hO s := (coordinateExteriorFrame i).naturality hPO hO s

local instance canonicalSheavesHasExt :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology Surface) AddCommGrpCat.{0}) :=
  HasExt.standard _

/-- The three whole coordinate opens have vanishing actual canonical-sheaf
first cohomology. This supplies the local hypotheses of the degree-two
Čech-to-derived comparison; it is not an assertion about arbitrary sheaf
epimorphisms on sections. -/
theorem coordinateCanonicalHOne_subsingleton (i : Fin 3) :
    Subsingleton (canonicalAdditiveSheaf.H' 1 (coordinateOpen i)) :=
  affineFrameHOne_subsingleton
    (CycleQ2GeometricSurfaceDehomogenizedCharts.coordinateAffineChart 57 1
      (CycleQ2FullSurfaceJacobianCover.projectiveIndex i))
    canonicalAdditiveSheaf (overIsoOfPatchIso (coordinateCanonicalAdditiveFrame i))

end Cohomology

end CycleQ2SurfaceCoordinateFrames

end
