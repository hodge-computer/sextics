import Proposal.GeometricLiteralThreefoldMovingVolume
import Proposal.GeometricLiteralAbelJacobiContractedCocycle

/-!
# The actual cubic in the affine Jacobian frames

On each augmented Jacobian chart the actual global cubic is the
sheafification of its oriented residue two-form. Contracting on a native
pair intersection uses the original Kodaira–Spencer section on the actual surface.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1400000

noncomputable section
namespace CycleQ2LiteralThreefoldCubicPullback

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
  CycleQ2LiteralAbelJacobiContraction CycleQ2LiteralThreefoldSurfaceAdjunction
  CycleQ2LiteralThreefoldSurfaceNormal CycleQ2LiteralThreefoldMovingVolume
  CycleQ2GeometricSurfaceAdjunction CycleQ2GeometricSurfaceCoefficients
  CycleQ2GeometricSurfaceDehomogenizedCharts CycleQ2GeometricSurfaceJacobianCharts
  CycleQ2GeometricAffineChartSections CycleQ2GeometricPrincipalChartSections
  CycleQ2GeometricExteriorLocalFrames CycleQ2GeometricSurfaceExteriorSections
  CycleQ2GeometricExteriorSheaf CycleQ2GeometricDifferentialSheaf
  CycleQ2LiteralAbelJacobiContractedCocycle CycleQ2LiteralAbelJacobiSheafContraction
  CycleQ2LiteralAbelJacobiSurfaceWedge CycleQ2LiteralNativeTangentEvaluation
  CycleQ2LiteralNativeDifferentialSections CycleQ2LiteralNativeKodairaSpencerCocycle
  CycleQ2LiteralNativeChernCocycle CycleQ2LiteralNativeGaugeSections
  CycleQ2LiteralProjectiveIntersections CycleQ2FiniteCechDescent
  CycleQ2GeometricSectionDifferentials CycleQ2GeometricAffineOverlap

abbrev chart (j : Fin 3) := coordinateAffineChart 57 1 j.succ
abbrev jac (n a : SurfacePoly) (j : Fin 3) := augmentedJacobian (E j.succ) n a
abbrev patch (n a : SurfacePoly) (j : Fin 3) := principalOpen (chart j) (jac n a j)
abbrev frameChart (n a : SurfacePoly) (j : Fin 3) := principalChart (chart j) (jac n a j)
abbrev frameComplex (n a : SurfacePoly) (j : Fin 3) :=
  principalChart_overComplex (chart j) (jac n a j) (CycleQ2GeometricSurfaceCoefficients.projectiveToComplex 57 1)
    (coordinateAffineChart_overComplex 57 1 j.succ)

variable (n a : SurfacePoly) (j : Fin 3) (V : Over (patch n a j))

abbrev exteriorOn := chartExteriorSection (frameChart n a j) (CycleQ2GeometricSurfaceCoefficients.projectiveToComplex 57 1)
  (frameComplex n a j) (localSurfaceKaehlerBasis (E j.succ) n a) V

abbrev ordinaryOn := chartKaehlerSection (frameChart n a j) (CycleQ2GeometricSurfaceCoefficients.projectiveToComplex 57 1)
  (frameComplex n a j) V

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

open CycleQ2CartierProjectiveCover CycleQ2CartierSurfaceGrading MvPolynomial

private def changedChart (j : Fin 3) (w : Fin 2 → SurfacePoly) (h : E j.succ = w) :
    (coordinatePatch 57 1 j.succ.castSucc).toScheme ≅ Spec (CommRingCat.of (SurfaceChartRing w)) :=
  Proj.basicOpenIsoSpec (surfaceGrade 57 1) (CycleQ2GeometricCartierNormalLift.surfaceQuotient 57 1 (X j.succ.castSucc))
    (coordinate_mem_grade 57 1 j.succ) (by decide) ≪≫
    Scheme.Spec.mapIso ((coordinateChartEquiv 57 1 j.succ).trans
      (Ideal.quotientEquivAlgOfEq ℂ (congrArg surfaceChartIdeal h)).toRingEquiv).toCommRingCatIso.symm.op

private theorem changedChart_refl : changedChart j (E j.succ) rfl = chart j := by
  have h : (coordinateChartEquiv 57 1 j.succ).trans
      (Ideal.quotientEquivAlgOfEq ℂ (congrArg surfaceChartIdeal (rfl : E j.succ = E j.succ))).toRingEquiv =
        coordinateChartEquiv 57 1 j.succ := by
    apply RingEquiv.ext
    intro z
    change Ideal.quotientEquivAlgOfEq ℂ (rfl : surfaceChartIdeal (E j.succ) = _)
      (coordinateChartEquiv 57 1 j.succ z) = coordinateChartEquiv 57 1 j.succ z
    have he (b : SurfaceChartRing (E j.succ)) :
        Ideal.quotientEquivAlgOfEq ℂ (rfl : surfaceChartIdeal (E j.succ) = _) b = b := by
      obtain ⟨b,rfl⟩ := Ideal.Quotient.mk_surjective b
      rfl
    exact he _
  unfold changedChart chart coordinateAffineChart
  rw [h]

private theorem changed_frame (w : Fin 2 → SurfacePoly) (h : E j.succ = w)
    (e : (coordinatePatch 57 1 j.succ.castSucc).toScheme ≅ Spec (CommRingCat.of (SurfaceChartRing w)))
    (he : changedChart j w h = e) (x : TwoForms.val.obj (op V.left)) :
    ∃ hW : V.left ≤ principalOpen e (augmentedJacobian w n a),
      ∀ hw, (chartResidueLocalFrame (CycleQ2GeometricSurfaceCoefficients.projectiveToComplex 57 1) w n a
        (principalChart e (augmentedJacobian w n a)) hw).app V.left hW x =
      (chartResidueLocalFrame (CycleQ2GeometricSurfaceCoefficients.projectiveToComplex 57 1) (E j.succ) n a
        (frameChart n a j) (frameComplex n a j)).app V.left V.hom.le x := by
  subst e
  subst w
  rw [changedChart_refl]
  exact ⟨V.hom.le, fun _ => rfl⟩

private def ChartAgreement (n a : SurfacePoly) (j : Fin 3) : Prop :=
  ∀ (V : Over (patch n a j)) (x : TwoForms.val.obj (op V.left)),
    (CycleQ2SurfaceCoordinateFrames.coordinateExteriorFrame j).app V.left
      (V.hom.le.trans (principalOpen_le _ _)) x =
    (chartResidueLocalFrame (CycleQ2GeometricSurfaceCoefficients.projectiveToComplex 57 1) (E j.succ) n a
      (frameChart n a j) (frameComplex n a j)).app V.left V.hom.le x

set_option maxHeartbeats 400000 in
private theorem first_agreement : ChartAgreement n a 0 := by
  intro V x
  obtain ⟨hW,h⟩ := changed_frame n a 0 V (firstEquations 57 1) (dehomogenizedEquations_one 57 1)
    (firstAffineChart 57 1) rfl x
  exact (CycleQ2SurfaceCoordinateFrames.coordinateExteriorFrame_app 0 n a V.left hW x).trans
    (h (CycleQ2SurfaceResidueSheafOverlap.firstPatchChart_overComplex 57 1 n a))

set_option maxHeartbeats 400000 in
private theorem second_agreement : ChartAgreement n a 1 := by
  intro V x
  obtain ⟨hW,h⟩ := changed_frame n a 1 V (secondEquations 57 1) (dehomogenizedEquations_two 57 1)
    (secondAffineChart 57 1) rfl x
  exact (CycleQ2SurfaceCoordinateFrames.coordinateExteriorFrame_app 1 n a V.left hW x).trans
    (h (CycleQ2SurfaceResidueSheafOverlap.secondPatchChart_overComplex 57 1 n a))

private theorem third_agreement : ChartAgreement n a 2 := by
  intro V x
  exact CycleQ2SurfaceCoordinateFrames.coordinateExteriorFrame_app 2 n a V.left V.hom.le x

private theorem coordinateFrame_chart : ∀ j, ChartAgreement n a j :=
  Fin.cases (first_agreement n a) (Fin.cases (second_agreement n a)
    (Fin.cases (third_agreement n a) (fun i => Fin.elim0 i)))

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Equality inside the exterior sheaf on every subopen of the Jacobian chart. -/
theorem restricted_global_cubic :
    TwoForms.val.map V.left.leTop.op tangentCubicForm =
      exteriorSection Surface.sheaf DifferentialSheaf.val 2 V.left
        (exteriorOn n a j V (orientedCubic n a j)) := by
  apply ((CycleQ2SurfaceCoordinateFrames.coordinateExteriorFrame j).app V.left
    (V.hom.le.trans (principalOpen_le _ _))).injective
  refine (global_cubic_coordinate n a j V).trans ?_
  symm
  let f := CycleQ2GeometricSurfaceCoefficients.projectiveToComplex 57 1
  let ω := orientedCubic n a j
  have hr := chartResidueLocalFrame_exteriorSection f (E j.succ) n a (frameChart n a j)
    (frameComplex n a j) V.left V.hom.le (exteriorOn n a j V ω)
  have hc := chartResidueCoordinate_exteriorSection f (E j.succ) n a (frameChart n a j)
    (frameComplex n a j) V ω
  exact (coordinateFrame_chart n a j V _).trans (hr.trans hc)

/-- On simultaneous native and Jacobian opens the original contracted cocycle is
the interior product of the genuine native tangent with the chart cubic. -/
theorem contractedValue_jacobian (s : Finset Vertex) (hs : s.Nonempty) (u v : Vertex)
    (hu : u ∈ s) (hv : v ∈ s) (hW : V.left ≤ closedOpen s)
    (hU : V.left ≤ cover u) (hV : V.left ≤ cover v) :
    contractedValue u v V.left hU hV = contract (evaluateTangent V.left
      (CycleQ2GeometricSheafLocalIso.res tangentAddSheaf hW (nativeKodairaSpencerSection s hs u v hu hv)))
      (exteriorOn n a j V (orientedCubic n a j)) := by
  change interior V.left (kodairaSpencerValue u v V.left hU hV)
    (TwoForms.val.map V.left.leTop.op tangentCubicForm) = _
  rw [restricted_global_cubic n a j V, interior_exterior,
    kodairaSpencerValue_common s hs u v hu hv V.left hW hU hV]

end CycleQ2LiteralThreefoldCubicPullback
end

#print axioms CycleQ2LiteralThreefoldCubicPullback.restricted_global_cubic
#print axioms CycleQ2LiteralThreefoldCubicPullback.contractedValue_jacobian
