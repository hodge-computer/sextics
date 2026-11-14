import Proposal.GeometricSurfaceCoordinateFrames
import Proposal.GeometricGlobalSurfaceCubics
import Proposal.GeometricSurfaceCoordinateSections

/-!
# Global cubic forms in the whole-coordinate canonical frames

Status: source-only proof draft. Compilation and independent kernel replay
are deferred at the user's request. No new axioms or admissions are used.

The coordinate of a genuine global cubic form is its literal homogeneous
fraction, with the original (+,-,+) orientation. The proof uses the actual
restrictions of the global section on the all-minor cover, the proved raw
residue normalization, and separation of the actual structure sheaf.
It applies to the whole coordinate open and all its subopens.

Specializing to the cubic Xj^3 determines the transition of the entire
coordinate frame, including arbitrary canonical-form sections. This uses
the constructed global cubic and introduces no transition hypothesis.

The geometric strategy is due to Ben Diamond and the cited work of Claire
Voisin. Prepared for fqlx with OpenAI ChatGPT assistance.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2SurfaceCoordinateCubicFrames

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry MvPolynomial
open CycleQ2CartierProjectiveCover CycleQ2GeometricSurfaceAdjunction
  CycleQ2GeometricSurfaceDehomogenizedCharts CycleQ2GeometricSurfaceJacobianCharts
  CycleQ2GeometricSurfaceCoefficients CycleQ2GeometricAffineChartSections
  CycleQ2GeometricExteriorSheaf CycleQ2GeometricCanonicalGluing
  CycleQ2GeometricExteriorLocalFrames CycleQ2SurfaceResidueSheafOverlap
  CycleQ2SurfaceCommonOpen CycleQ2ThirdSurfaceChart CycleQ2FullSurfaceResidueCover
  CycleQ2SurfaceCoordinateFrames CycleQ2SurfaceCoordinateSections

abbrev Surface := CycleQ2SurfaceCoordinateFrames.Surface
abbrev CanonicalForms := CycleQ2SurfaceCoordinateFrames.CanonicalForms
abbrev WeightedCubic := CycleQ2SurfaceCubicGluing.WeightedCubic

/-- The original projective orientation relative to the positive raw frames. -/
def orientation (i : Fin 3) : ℤ := ![1, -1, 1] i

theorem orientation_mul_self (i : Fin 3) (O : Surface.Opens) :
    (orientation i : Γ(Surface, O)) * (orientation i : Γ(Surface, O)) = 1 := by
  fin_cases i <;> norm_num [orientation]

/-- The original chart polynomial sections commute with actual restriction. -/
theorem coordinatePolynomialSection_restrict (r θ : ℂ) (i : Fin 4)
    {O P : (projectiveSurface r θ).Opens}
    (hO : O ≤ coordinatePatch r θ i.castSucc) (hPO : P ≤ O)
    (p : MvPolynomial (Fin 5) ℂ) :
    (projectiveSurface r θ).presheaf.map (homOfLE hPO).op
        (coordinatePolynomialSection r θ i O hO p) =
      coordinatePolynomialSection r θ i P (hPO.trans hO) p :=
  chartSection_naturality (coordinateAffineChart r θ i)
    (show Over.mk (homOfLE (hPO.trans hO)) ⟶ Over.mk (homOfLE hO) from
      Over.homMk (homOfLE hPO))
    (dehomogenizedMap r θ i (dehomogenize i p))

/-- On every augmented patch, the actual cubic has its literal signed
homogeneous coefficient in the actual raw exterior frame. -/
theorem rawExteriorFrame_localSection_coordinate (p : WeightedCubic)
    (i : Fin 3) (n t : SurfacePoly) (O : Surface.Opens)
    (hO : O ≤ patchOpen (i, n, t)) :
    (rawExteriorFrame i n t).app O hO
        (CycleQ2GlobalSurfaceCubics.localSectionOn p.val (i, n, t) O hO) =
      (orientation i : Γ(Surface, O)) *
        coordinatePolynomialSection 57 1
          (CycleQ2FullSurfaceJacobianCover.projectiveIndex i) O
          (hO.trans (patchOpen_le (i, n, t))) p.val := by
  fin_cases i
  · change (chartResidueLocalFrame (projectiveToComplex 57 1)
        (firstEquations 57 1) n t (firstPatchChart 57 1 n t)
        (firstPatchChart_overComplex 57 1 n t)).app O hO
      (chartSection (firstPatchChart 57 1 n t) (Over.mk (homOfLE hO))
        (algebraMap SurfacePoly (AdjunctionPatch (firstEquations 57 1) n t)
          (firstSurfaceDehomogenize p.val)) •
        chartResidueSheafSection (projectiveToComplex 57 1) (firstEquations 57 1) n t
          (firstPatchChart 57 1 n t) (firstPatchChart_overComplex 57 1 n t)
          (Over.mk (homOfLE hO))) =
      (orientation 0 : Γ(Surface, O)) * coordinatePolynomialSection 57 1 1 O
        (hO.trans (firstPatchOpen_le 57 1 n t)) p.val
    rw [← chartResidueLocalFrame_generator]
    change (rawExteriorFrame 0 n t).app O hO
      (_ • ((rawExteriorFrame 0 n t).app O hO).symm 1) = _
    rw [map_smul, LinearEquiv.apply_symm_apply, smul_eq_mul, mul_one]
    simpa [orientation] using
      CycleQ2SurfaceFirstThirdTransition.firstPolynomialSection_homogeneous
        57 1 n t O hO 3 p.val p.property
  · change (chartResidueLocalFrame (projectiveToComplex 57 1)
        (secondEquations 57 1) n t (secondPatchChart 57 1 n t)
        (secondPatchChart_overComplex 57 1 n t)).app O hO
      (-(chartSection (secondPatchChart 57 1 n t) (Over.mk (homOfLE hO))
        (algebraMap SurfacePoly (AdjunctionPatch (secondEquations 57 1) n t)
          (secondSurfaceDehomogenize p.val)) •
        chartResidueSheafSection (projectiveToComplex 57 1) (secondEquations 57 1) n t
          (secondPatchChart 57 1 n t) (secondPatchChart_overComplex 57 1 n t)
          (Over.mk (homOfLE hO)))) =
      (orientation 1 : Γ(Surface, O)) * coordinatePolynomialSection 57 1 2 O
        (hO.trans (secondPatchOpen_le 57 1 n t)) p.val
    rw [map_neg, ← chartResidueLocalFrame_generator]
    change -((rawExteriorFrame 1 n t).app O hO
      (_ • ((rawExteriorFrame 1 n t).app O hO).symm 1)) = _
    rw [map_smul, LinearEquiv.apply_symm_apply, smul_eq_mul, mul_one]
    simpa [orientation] using congrArg Neg.neg
      (CycleQ2SurfaceSecondThirdTransition.secondPolynomialSection_homogeneous
        57 1 n t O hO 3 p.val p.property)
  · change (chartResidueLocalFrame (projectiveToComplex 57 1)
        (thirdEquations 57 1) n t (thirdPatchChart 57 1 n t)
        (thirdPatchChart_overComplex 57 1 n t)).app O hO
      (chartSection (thirdPatchChart 57 1 n t) (Over.mk (homOfLE hO))
        (algebraMap SurfacePoly (AdjunctionPatch (thirdEquations 57 1) n t)
          (thirdDehomogenize p.val)) •
        chartResidueSheafSection (projectiveToComplex 57 1) (thirdEquations 57 1) n t
          (thirdPatchChart 57 1 n t) (thirdPatchChart_overComplex 57 1 n t)
          (Over.mk (homOfLE hO))) =
      (orientation 2 : Γ(Surface, O)) * coordinatePolynomialSection 57 1 3 O
        (hO.trans (thirdPatchOpen_le 57 1 n t)) p.val
    rw [← chartResidueLocalFrame_generator]
    change (rawExteriorFrame 2 n t).app O hO
      (_ • ((rawExteriorFrame 2 n t).app O hO).symm 1) = _
    rw [map_smul, LinearEquiv.apply_symm_apply, smul_eq_mul, mul_one]
    simpa [orientation] using
      CycleQ2SurfaceFirstThirdTransition.thirdPolynomialSection_weighted
        57 1 n t O hO p.val

/-- The genuine global cubic has its literal homogeneous coordinate on an
arbitrary subopen of a whole coordinate chart, with orientation (+,-,+). -/
theorem coordinateExteriorFrame_globalCubic (p : WeightedCubic) (i : Fin 3)
    (O : Surface.Opens) (hO : O ≤ coordinateOpen i) :
    (coordinateExteriorFrame i).app O hO
        (CanonicalForms.val.map (homOfLE (show O ≤ ⊤ from le_top)).op
          (CycleQ2GlobalSurfaceCubics.globalCubicSection p)) =
      (orientation i : Γ(Surface, O)) *
        coordinatePolynomialSection 57 1
          (CycleQ2FullSurfaceJacobianCover.projectiveIndex i) O hO p.val := by
  have hcover : O ≤ ⨆ a, O ⊓ coordinateResidueCover i a := by
    rw [← inf_iSup_eq, coordinateResidueCover_eq]
    exact le_inf le_rfl hO
  apply (CycleQ2GeometricProjectiveHOne.structureAdditiveSheaf Surface).eq_of_locally_eq'
    (fun a => O ⊓ coordinateResidueCover i a) O
    (fun _ => homOfLE inf_le_left) hcover
  intro a
  change Surface.presheaf.map
      (homOfLE (show O ⊓ coordinateResidueCover i a ≤ O from inf_le_left)).op
      ((coordinateExteriorFrame i).app O hO
        (CanonicalForms.val.map (homOfLE (show O ≤ ⊤ from le_top)).op
          (CycleQ2GlobalSurfaceCubics.globalCubicSection p))) =
    Surface.presheaf.map (homOfLE inf_le_left).op
      ((orientation i : Γ(Surface, O)) *
        coordinatePolynomialSection 57 1
          (CycleQ2FullSurfaceJacobianCover.projectiveIndex i) O hO p.val)
  rw [coordinateExteriorFrame_restrict i a.1 a.2 hO inf_le_left inf_le_right,
    map_mul, map_intCast, coordinatePolynomialSection_restrict,
    ← PresheafOfModules.map_comp_apply]
  change (rawExteriorFrame i a.1 a.2).app _ inf_le_right
      (CanonicalForms.val.map
        (homOfLE (show O ⊓ coordinateResidueCover i a ≤ ⊤ from le_top)).op
        (CycleQ2GlobalSurfaceCubics.globalCubicSection p)) = _
  rw [CycleQ2GlobalSurfaceCubics.globalCubicSection_restrict_subopen p (i, a.1, a.2)
    (O ⊓ coordinateResidueCover i a) inf_le_right]
  exact rawExteriorFrame_localSection_coordinate p i a.1 a.2 _ inf_le_right

/-- The original coordinate cube, viewed in the same weighted cubic space. -/
def coordinateCube (i : Fin 3) : WeightedCubic :=
  ⟨X (CycleQ2FullSurfaceJacobianCover.projectiveIndex i).castSucc ^ 3, by
    have hx : (X (CycleQ2FullSurfaceJacobianCover.projectiveIndex i).castSucc :
        MvPolynomial (Fin 5) ℂ).IsWeightedHomogeneous
          CycleQ2CartierSurfaceGrading.weight 1 := by
      fin_cases i <;>
        exact isWeightedHomogeneous_X ℂ CycleQ2CartierSurfaceGrading.weight _
    exact hx.pow 3⟩

/-- Specializing a global cubic to Xj^3 determines the actual coordinate
transition on every canonical-form section on the overlap. -/
theorem coordinateExteriorFrame_transition (i j : Fin 3) (O : Surface.Opens)
    (hi : O ≤ coordinateOpen i) (hj : O ≤ coordinateOpen j)
    (s : CanonicalForms.val.obj (op O)) :
    (coordinateExteriorFrame i).app O hi s =
      ((orientation i : Γ(Surface, O)) * (orientation j : Γ(Surface, O))) *
        (coordinatePolynomialSection 57 1
          (CycleQ2FullSurfaceJacobianCover.projectiveIndex i) O hi
          (X (CycleQ2FullSurfaceJacobianCover.projectiveIndex j).castSucc)) ^ 3 *
        (coordinateExteriorFrame j).app O hj s := by
  let σ : CanonicalForms.val.obj (op O) :=
    CanonicalForms.val.map (homOfLE (show O ≤ ⊤ from le_top)).op
      (CycleQ2GlobalSurfaceCubics.globalCubicSection (coordinateCube j))
  have hσi : (coordinateExteriorFrame i).app O hi σ =
      (orientation i : Γ(Surface, O)) *
        (coordinatePolynomialSection 57 1
          (CycleQ2FullSurfaceJacobianCover.projectiveIndex i) O hi
          (X (CycleQ2FullSurfaceJacobianCover.projectiveIndex j).castSucc)) ^ 3 := by
    simpa only [σ, coordinateCube, map_pow] using
      coordinateExteriorFrame_globalCubic (coordinateCube j) i O hi
  have hσj : (coordinateExteriorFrame j).app O hj σ =
      (orientation j : Γ(Surface, O)) := by
    simpa only [σ, coordinateCube, map_pow, coordinatePolynomialSection_self,
      one_pow, mul_one] using
      coordinateExteriorFrame_globalCubic (coordinateCube j) j O hj
  have hs : s =
      ((orientation j : Γ(Surface, O)) * (coordinateExteriorFrame j).app O hj s) • σ := by
    apply ((coordinateExteriorFrame j).app O hj).injective
    rw [map_smul, hσj, smul_eq_mul]
    calc
      _ = 1 * (coordinateExteriorFrame j).app O hj s := (one_mul _).symm
      _ = ((orientation j : Γ(Surface, O)) * (orientation j : Γ(Surface, O))) *
          (coordinateExteriorFrame j).app O hj s := by rw [orientation_mul_self]
      _ = _ := by ring
  calc
    _ = (coordinateExteriorFrame i).app O hi
        (((orientation j : Γ(Surface, O)) *
          (coordinateExteriorFrame j).app O hj s) • σ) := congrArg _ hs
    _ = _ := by rw [map_smul, hσi, smul_eq_mul]; ring

end CycleQ2SurfaceCoordinateCubicFrames

end
