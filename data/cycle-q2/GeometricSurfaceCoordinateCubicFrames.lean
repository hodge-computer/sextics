import Proposal.GeometricSurfaceCoordinateFrames
import Proposal.GeometricGlobalSurfaceCubics
import Proposal.GeometricSurfaceCoordinateSections

/-!
# Global cubic forms in the whole-coordinate canonical frames

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

private theorem linearEquiv_smul_unit {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] (e : M ≃ₗ[R] R) (u : M)
    (hu : e u = 1) (a : R) : e (a • u) = a := by
  rw [e.map_smul, hu, smul_eq_mul, mul_one]

private theorem linearEquiv_neg_smul_unit {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] (e : M ≃ₗ[R] R) (u : M)
    (hu : e u = 1) (a : R) : e (-(a • u)) = -a := by
  exact (e.map_neg (a • u)).trans
    (congrArg (fun z : R => -z) (linearEquiv_smul_unit e u hu a))

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

private theorem firstRawExteriorFrame_localSection_coordinate (p : WeightedCubic)
    (n t : SurfacePoly) (O : Surface.Opens) (hO : O ≤ patchOpen (0, n, t)) :
    (show Γ(Surface,O) from (rawExteriorFrame (0 : Fin 3) n t).app O hO
        (CycleQ2GlobalSurfaceCubics.localSectionOn p.val ((0 : Fin 3), n, t) O hO)) =
      (orientation (0 : Fin 3) : Γ(Surface, O)) *
        coordinatePolynomialSection 57 1
          (CycleQ2FullSurfaceJacobianCover.projectiveIndex (0 : Fin 3)) O
          (hO.trans (patchOpen_le ((0 : Fin 3), n, t))) p.val := by
  let e : CanonicalForms.val.obj (op O) ≃ₗ[Γ(Surface,O)] Γ(Surface,O) :=
    (chartResidueLocalFrame (projectiveToComplex 57 1) (firstEquations 57 1) n t
      (firstPatchChart 57 1 n t) (firstPatchChart_overComplex 57 1 n t)).app O hO
  let u : CanonicalForms.val.obj (op O) :=
    chartResidueSheafSection (projectiveToComplex 57 1) (firstEquations 57 1) n t
      (firstPatchChart 57 1 n t) (firstPatchChart_overComplex 57 1 n t) (Over.mk (homOfLE hO))
  let a : Γ(Surface,O) := chartSection (firstPatchChart 57 1 n t) (Over.mk (homOfLE hO))
    (algebraMap SurfacePoly (AdjunctionPatch (firstEquations 57 1) n t) (firstSurfaceDehomogenize p.val))
  have hgen := chartResidueLocalFrame_generator (projectiveToComplex 57 1)
    (firstEquations 57 1) n t (firstPatchChart 57 1 n t) (firstPatchChart_overComplex 57 1 n t) O hO
  have hu : e u = (1 : Γ(Surface,O)) := by
    change e.symm (1 : Γ(Surface,O)) = u at hgen
    exact (congrArg e hgen).symm.trans (e.apply_symm_apply _)
  have ha : a = coordinatePolynomialSection 57 1 1 O
      (hO.trans (firstPatchOpen_le 57 1 n t)) p.val :=
    CycleQ2SurfaceFirstThirdTransition.firstPolynomialSection_homogeneous 57 1 n t O hO 3 p.val p.property
  have ho : (orientation 0 : Γ(Surface,O)) = 1 := by
    norm_num [orientation]
  change e (a • u) = (orientation 0 : Γ(Surface,O)) * coordinatePolynomialSection 57 1 1 O
      (hO.trans (firstPatchOpen_le 57 1 n t)) p.val
  exact (linearEquiv_smul_unit e u hu a).trans
    (ha.trans (by rw [ho, one_mul]))

private theorem secondRawExteriorFrame_localSection_coordinate (p : WeightedCubic)
    (n t : SurfacePoly) (O : Surface.Opens) (hO : O ≤ patchOpen (1, n, t)) :
    (show Γ(Surface,O) from (rawExteriorFrame (1 : Fin 3) n t).app O hO
        (CycleQ2GlobalSurfaceCubics.localSectionOn p.val ((1 : Fin 3), n, t) O hO)) =
      (orientation (1 : Fin 3) : Γ(Surface, O)) *
        coordinatePolynomialSection 57 1
          (CycleQ2FullSurfaceJacobianCover.projectiveIndex (1 : Fin 3)) O
          (hO.trans (patchOpen_le ((1 : Fin 3), n, t))) p.val := by
  let e : CanonicalForms.val.obj (op O) ≃ₗ[Γ(Surface,O)] Γ(Surface,O) :=
    (chartResidueLocalFrame (projectiveToComplex 57 1) (secondEquations 57 1) n t
      (secondPatchChart 57 1 n t) (secondPatchChart_overComplex 57 1 n t)).app O hO
  let u : CanonicalForms.val.obj (op O) :=
    chartResidueSheafSection (projectiveToComplex 57 1) (secondEquations 57 1) n t
      (secondPatchChart 57 1 n t) (secondPatchChart_overComplex 57 1 n t) (Over.mk (homOfLE hO))
  let a : Γ(Surface,O) := chartSection (secondPatchChart 57 1 n t) (Over.mk (homOfLE hO))
    (algebraMap SurfacePoly (AdjunctionPatch (secondEquations 57 1) n t) (secondSurfaceDehomogenize p.val))
  have hgen := chartResidueLocalFrame_generator (projectiveToComplex 57 1)
    (secondEquations 57 1) n t (secondPatchChart 57 1 n t) (secondPatchChart_overComplex 57 1 n t) O hO
  have hu : e u = (1 : Γ(Surface,O)) := by
    change e.symm (1 : Γ(Surface,O)) = u at hgen
    exact (congrArg e hgen).symm.trans (e.apply_symm_apply _)
  have ha : a = coordinatePolynomialSection 57 1 2 O
      (hO.trans (secondPatchOpen_le 57 1 n t)) p.val :=
    CycleQ2SurfaceSecondThirdTransition.secondPolynomialSection_homogeneous 57 1 n t O hO 3 p.val p.property
  have ho : (orientation 1 : Γ(Surface,O)) = -1 := by
    norm_num [orientation]
  change e (-(a • u)) = (orientation 1 : Γ(Surface,O)) * coordinatePolynomialSection 57 1 2 O
      (hO.trans (secondPatchOpen_le 57 1 n t)) p.val
  calc
    e (-(a • u)) = -a := linearEquiv_neg_smul_unit e u hu a
    _ = (orientation 1 : Γ(Surface,O)) * coordinatePolynomialSection 57 1 2 O
        (hO.trans (secondPatchOpen_le 57 1 n t)) p.val := by
      rw [ho, neg_one_mul]
      exact congrArg (fun z : Γ(Surface,O) => -z) ha

private theorem thirdRawExteriorFrame_localSection_coordinate (p : WeightedCubic)
    (n t : SurfacePoly) (O : Surface.Opens) (hO : O ≤ patchOpen (2, n, t)) :
    (show Γ(Surface,O) from (rawExteriorFrame (2 : Fin 3) n t).app O hO
        (CycleQ2GlobalSurfaceCubics.localSectionOn p.val ((2 : Fin 3), n, t) O hO)) =
      (orientation (2 : Fin 3) : Γ(Surface, O)) *
        coordinatePolynomialSection 57 1
          (CycleQ2FullSurfaceJacobianCover.projectiveIndex (2 : Fin 3)) O
          (hO.trans (patchOpen_le ((2 : Fin 3), n, t))) p.val := by
  let e : CanonicalForms.val.obj (op O) ≃ₗ[Γ(Surface,O)] Γ(Surface,O) :=
    (chartResidueLocalFrame (projectiveToComplex 57 1) (thirdEquations 57 1) n t
      (thirdPatchChart 57 1 n t) (thirdPatchChart_overComplex 57 1 n t)).app O hO
  let u : CanonicalForms.val.obj (op O) :=
    chartResidueSheafSection (projectiveToComplex 57 1) (thirdEquations 57 1) n t
      (thirdPatchChart 57 1 n t) (thirdPatchChart_overComplex 57 1 n t) (Over.mk (homOfLE hO))
  let a : Γ(Surface,O) := chartSection (thirdPatchChart 57 1 n t) (Over.mk (homOfLE hO))
    (algebraMap SurfacePoly (AdjunctionPatch (thirdEquations 57 1) n t) (thirdDehomogenize p.val))
  have hgen := chartResidueLocalFrame_generator (projectiveToComplex 57 1)
    (thirdEquations 57 1) n t (thirdPatchChart 57 1 n t) (thirdPatchChart_overComplex 57 1 n t) O hO
  have hu : e u = (1 : Γ(Surface,O)) := by
    change e.symm (1 : Γ(Surface,O)) = u at hgen
    exact (congrArg e hgen).symm.trans (e.apply_symm_apply _)
  have ha : a = coordinatePolynomialSection 57 1 3 O
      (hO.trans (thirdPatchOpen_le 57 1 n t)) p.val :=
    CycleQ2SurfaceFirstThirdTransition.thirdPolynomialSection_weighted 57 1 n t O hO p.val
  have ho : (orientation 2 : Γ(Surface,O)) = 1 := by
    change ((1 : ℤ) : Γ(Surface,O)) = 1
    exact Int.cast_one
  change e (a • u) = (orientation 2 : Γ(Surface,O)) * coordinatePolynomialSection 57 1 3 O
      (hO.trans (thirdPatchOpen_le 57 1 n t)) p.val
  exact (linearEquiv_smul_unit e u hu a).trans
    (ha.trans (by rw [ho, one_mul]))

/-- On every augmented patch, the actual cubic has its literal signed
homogeneous coefficient in the actual raw exterior frame. -/
theorem rawExteriorFrame_localSection_coordinate (p : WeightedCubic) :
    ∀ (i : Fin 3) (n t : SurfacePoly) (O : Surface.Opens)
      (hO : O ≤ patchOpen (i, n, t)),
    (show Γ(Surface,O) from (rawExteriorFrame i n t).app O hO
        (CycleQ2GlobalSurfaceCubics.localSectionOn p.val (i, n, t) O hO)) =
      (orientation i : Γ(Surface, O)) *
        coordinatePolynomialSection 57 1
          (CycleQ2FullSurfaceJacobianCover.projectiveIndex i) O
          (hO.trans (patchOpen_le (i, n, t))) p.val
  | 0, n, t, O, hO => firstRawExteriorFrame_localSection_coordinate p n t O hO
  | 1, n, t, O, hO => secondRawExteriorFrame_localSection_coordinate p n t O hO
  | 2, n, t, O, hO => thirdRawExteriorFrame_localSection_coordinate p n t O hO

/-- The genuine global cubic has its literal homogeneous coordinate on an
arbitrary subopen of a whole coordinate chart, with orientation (+,-,+). -/
theorem coordinateExteriorFrame_globalCubic (p : WeightedCubic) (i : Fin 3)
    (O : Surface.Opens) (hO : O ≤ coordinateOpen i) :
    (show Γ(Surface,O) from (coordinateExteriorFrame i).app O hO
        (CanonicalForms.val.map (homOfLE (show O ≤ ⊤ from le_top)).op
          (CycleQ2GlobalSurfaceCubics.globalCubicSection p))) =
      (orientation i : Γ(Surface, O)) *
        coordinatePolynomialSection 57 1
          (CycleQ2FullSurfaceJacobianCover.projectiveIndex i) O hO p.val := by
  have hcover : O ≤ ⨆ a, O ⊓ coordinateResidueCover i a := by
    rw [← inf_iSup_eq, coordinateResidueCover_eq]
    exact le_inf le_rfl hO
  apply TopCat.Sheaf.eq_of_locally_eq'
    (show TopCat.Sheaf AddCommGrpCat (TopCat.of Surface) from
      CycleQ2GeometricProjectiveHOne.structureAdditiveSheaf Surface)
    (fun a => O ⊓ coordinateResidueCover i a) O
    (fun _ => homOfLE inf_le_left) hcover
  intro a
  let P : Surface.Opens := O ⊓ coordinateResidueCover i a
  let hPO : P ≤ O := inf_le_left
  let hP : P ≤ patchOpen (i, a.1, a.2) := inf_le_right
  let σ : CanonicalForms.val.obj (op O) :=
    CanonicalForms.val.map (homOfLE (show O ≤ ⊤ from le_top)).op
      (CycleQ2GlobalSurfaceCubics.globalCubicSection p)
  have hr : Surface.presheaf.map (homOfLE hPO).op
      ((coordinateExteriorFrame i).app O hO σ) =
    (show Γ(Surface,P) from (rawExteriorFrame i a.1 a.2).app P hP
      (CanonicalForms.val.map (homOfLE hPO).op σ)) :=
    coordinateExteriorFrame_restrict i a.1 a.2 hO hPO hP σ
  have hσ : CanonicalForms.val.map (homOfLE hPO).op σ =
      CycleQ2GlobalSurfaceCubics.localSectionOn p.val (i,a.1,a.2) P hP :=
    (CanonicalForms.val.map_comp_apply
      (homOfLE (show O ≤ ⊤ from le_top)).op (homOfLE hPO).op
      (CycleQ2GlobalSurfaceCubics.globalCubicSection p)).symm.trans
      (CycleQ2GlobalSurfaceCubics.globalCubicSection_restrict_subopen p (i,a.1,a.2) P hP)
  have hright : Surface.presheaf.map (homOfLE hPO).op
      ((orientation i : Γ(Surface,O)) * coordinatePolynomialSection 57 1
        (CycleQ2FullSurfaceJacobianCover.projectiveIndex i) O hO p.val) =
    (orientation i : Γ(Surface,P)) * coordinatePolynomialSection 57 1
      (CycleQ2FullSurfaceJacobianCover.projectiveIndex i) P (hPO.trans hO) p.val := by
    rw [map_mul, map_intCast,
      coordinatePolynomialSection_restrict 57 1
        (CycleQ2FullSurfaceJacobianCover.projectiveIndex i) hO hPO p.val]
  exact hr.trans ((congrArg
    (fun z : CanonicalForms.val.obj (op P) =>
      (show Γ(Surface,P) from (rawExteriorFrame i a.1 a.2).app P hP z)) hσ).trans
      ((rawExteriorFrame_localSection_coordinate p i a.1 a.2 P hP).trans hright.symm))

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
    (show Γ(Surface,O) from (coordinateExteriorFrame i).app O hi s) =
      ((orientation i : Γ(Surface, O)) * (orientation j : Γ(Surface, O))) *
        (coordinatePolynomialSection 57 1
          (CycleQ2FullSurfaceJacobianCover.projectiveIndex i) O hi
          (X (CycleQ2FullSurfaceJacobianCover.projectiveIndex j).castSucc)) ^ 3 *
        (show Γ(Surface,O) from (coordinateExteriorFrame j).app O hj s) := by
  let ei : CanonicalForms.val.obj (op O) ≃ₗ[Γ(Surface,O)] Γ(Surface,O) :=
    (coordinateExteriorFrame i).app O hi
  let ej : CanonicalForms.val.obj (op O) ≃ₗ[Γ(Surface,O)] Γ(Surface,O) :=
    (coordinateExteriorFrame j).app O hj
  let σ : CanonicalForms.val.obj (op O) :=
    CanonicalForms.val.map (homOfLE (show O ≤ ⊤ from le_top)).op
      (CycleQ2GlobalSurfaceCubics.globalCubicSection (coordinateCube j))
  have hσi : ei σ =
      (orientation i : Γ(Surface,O)) *
        (coordinatePolynomialSection 57 1
          (CycleQ2FullSurfaceJacobianCover.projectiveIndex i) O hi
          (X (CycleQ2FullSurfaceJacobianCover.projectiveIndex j).castSucc)) ^ 3 := by
    have h := coordinateExteriorFrame_globalCubic (coordinateCube j) i O hi
    change ei σ = (orientation i : Γ(Surface,O)) * coordinatePolynomialSection 57 1
      (CycleQ2FullSurfaceJacobianCover.projectiveIndex i) O hi
      (X (CycleQ2FullSurfaceJacobianCover.projectiveIndex j).castSucc ^ 3) at h
    rw [map_pow] at h
    exact h
  have hσj : ej σ = (orientation j : Γ(Surface,O)) := by
    have h := coordinateExteriorFrame_globalCubic (coordinateCube j) j O hj
    change ej σ = (orientation j : Γ(Surface,O)) * coordinatePolynomialSection 57 1
      (CycleQ2FullSurfaceJacobianCover.projectiveIndex j) O hj
      (X (CycleQ2FullSurfaceJacobianCover.projectiveIndex j).castSucc ^ 3) at h
    rw [map_pow, coordinatePolynomialSection_self 57 1
      (CycleQ2FullSurfaceJacobianCover.projectiveIndex j) O hj, one_pow, mul_one] at h
    exact h
  have hs : s =
      ((orientation j : Γ(Surface, O)) * ej s) • σ := by
    apply (ej).injective
    rw [map_smul, hσj, smul_eq_mul]
    calc
      _ = 1 * ej s := (one_mul _).symm
      _ = ((orientation j : Γ(Surface, O)) * (orientation j : Γ(Surface, O))) *
          ej s := by rw [orientation_mul_self]
      _ = _ := by ring
  change ei s = ((orientation i : Γ(Surface,O)) * (orientation j : Γ(Surface,O))) *
    (coordinatePolynomialSection 57 1 (CycleQ2FullSurfaceJacobianCover.projectiveIndex i)
      O hi (X (CycleQ2FullSurfaceJacobianCover.projectiveIndex j).castSucc)) ^ 3 * ej s
  calc
    _ = ei
        (((orientation j : Γ(Surface, O)) *
          ej s) • σ) := congrArg _ hs
    _ = _ := by rw [map_smul, hσi, smul_eq_mul]; ring

end CycleQ2SurfaceCoordinateCubicFrames

end
