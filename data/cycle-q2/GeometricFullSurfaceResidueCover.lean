import Proposal.GeometricFullSurfaceJacobianCover
import Proposal.GeometricThirdSurfaceChart

/-!
# A full residue-chart cover of the literal projective surface

Source-only draft: compilation and replay are deferred at the user's
request. The three actual coordinate charts are covered by all augmented
Jacobian pairs. The original twelve normal patches occur literally in
this larger family. In particular, no assertion that those twelve patches
cover the whole surface enters the construction.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2FullSurfaceResidueCover

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry MvPolynomial
open CycleQ2SeedTrace CycleQ2NormalConnecting CycleQ2ConormalJacobian
  CycleQ2GeometricCartierNormalLift CycleQ2CartierProjectiveCover
  CycleQ2GeometricSurfaceAdjunction CycleQ2GeometricSurfaceDehomogenizedCharts
  CycleQ2GeometricSurfaceJacobianCharts CycleQ2GeometricSurfaceNormalCover
  CycleQ2SurfaceCommonOpen CycleQ2ThirdSurfaceChart
  CycleQ2FullSurfaceJacobianCover

abbrev Surface := projectiveSurface (57 : ℂ) 1
abbrev PatchIndex := Fin 3 × SurfacePoly × SurfacePoly

def coordinateOpen (i : Fin 3) : Surface.Opens :=
  coordinatePatch (57 : ℂ) 1 (projectiveIndex i).castSucc

def patchOpen (a : PatchIndex) : Surface.Opens :=
  match a.1 with
  | 0 => firstPatchOpen 57 1 a.2.1 a.2.2
  | 1 => secondPatchOpen 57 1 a.2.1 a.2.2
  | 2 => thirdPatchOpen 57 1 a.2.1 a.2.2

theorem patchOpen_le (a : PatchIndex) : patchOpen a ≤ coordinateOpen a.1 := by
  rcases a with ⟨i,n,t⟩
  fin_cases i
  · exact firstPatchOpen_le 57 1 n t
  · exact secondPatchOpen_le 57 1 n t
  · exact thirdPatchOpen_le 57 1 n t

private theorem firstCoordinateMinorIdeal_top :
    Ideal.span (Set.range (fun ab : Fin 4 × Fin 4 =>
      augmentedJacobian (firstEquations (57 : ℂ) 1)
        (X (variableIndex ab.1)) (X (variableIndex ab.2)))) = ⊤ := by
  have h := augmentedCoordinateIdeal_eq_top 0
  change Ideal.span (Set.range (fun ab : Fin 4 × Fin 4 =>
    augmentedJacobian (dehomogenizedEquations (57 : ℂ) 1 1)
      (X (variableIndex ab.1)) (X (variableIndex ab.2)))) = ⊤ at h
  simpa only [dehomogenizedEquations_one] using h

private theorem secondCoordinateMinorIdeal_top :
    Ideal.span (Set.range (fun ab : Fin 4 × Fin 4 =>
      augmentedJacobian (secondEquations (57 : ℂ) 1)
        (X (variableIndex ab.1)) (X (variableIndex ab.2)))) = ⊤ := by
  have h := augmentedCoordinateIdeal_eq_top 1
  change Ideal.span (Set.range (fun ab : Fin 4 × Fin 4 =>
    augmentedJacobian (dehomogenizedEquations (57 : ℂ) 1 2)
      (X (variableIndex ab.1)) (X (variableIndex ab.2)))) = ⊤ at h
  simpa only [dehomogenizedEquations_two] using h

theorem first_coordinate_minor_cover :
    (⨆ a : Fin 4, ⨆ b : Fin 4,
      firstPatchOpen (57 : ℂ) 1 (X (variableIndex a)) (X (variableIndex b))) =
        coordinateOpen 0 := by
  apply principalOpen_cover_two (firstAffineChart (57 : ℂ) 1)
  have h := PrimeSpectrum.iSup_basicOpen_eq_top_iff.mpr firstCoordinateMinorIdeal_top
  simpa only [iSup_prod] using h

theorem second_coordinate_minor_cover :
    (⨆ a : Fin 4, ⨆ b : Fin 4,
      secondPatchOpen (57 : ℂ) 1 (X (variableIndex a)) (X (variableIndex b))) =
        coordinateOpen 1 := by
  apply principalOpen_cover_two (secondAffineChart (57 : ℂ) 1)
  have h := PrimeSpectrum.iSup_basicOpen_eq_top_iff.mpr secondCoordinateMinorIdeal_top
  simpa only [iSup_prod] using h

theorem third_coordinate_minor_cover :
    (⨆ a : Fin 4, ⨆ b : Fin 4,
      thirdPatchOpen (57 : ℂ) 1 (X (variableIndex a)) (X (variableIndex b))) =
        coordinateOpen 2 := by
  apply principalOpen_cover_two (thirdAffineChart (57 : ℂ) 1)
  have h := PrimeSpectrum.iSup_basicOpen_eq_top_iff.mpr
    (augmentedCoordinateIdeal_eq_top 2)
  simpa only [augmentedCoordinateIdeal, equations, projectiveIndex, iSup_prod] using h

theorem coordinate_minor_cover (i : Fin 3) :
    (⨆ a : Fin 4, ⨆ b : Fin 4,
      patchOpen (i, X (variableIndex a), X (variableIndex b))) = coordinateOpen i := by
  fin_cases i
  · exact first_coordinate_minor_cover
  · exact second_coordinate_minor_cover
  · exact third_coordinate_minor_cover

/-- The three required weight-one coordinates cover every actual projective
point, by the original equations and their existing prime-ideal cover. -/
theorem coordinateOpen_cover : (⨆ i : Fin 3, coordinateOpen i) = ⊤ := by
  apply top_le_iff.mp
  intro q _
  have hq : q ∈ ⨆ j : Fin 5, coordinatePatch (57 : ℂ) 1 j := by
    rw [coordinatePatches_cover]
    trivial
  obtain ⟨j, hj⟩ := Opens.mem_iSup.mp hq
  letI : q.asHomogeneousIdeal.toIdeal.IsPrime := q.isPrime
  let P : Ideal WeightedPoly :=
    Ideal.comap (surfaceQuotient (57 : ℂ) 1) q.asHomogeneousIdeal.toIdeal
  letI : P.IsPrime := inferInstance
  have hF₀ : actualSeedEquation (57 : ℂ) 1 ∈ P := by
    change surfaceQuotient (57 : ℂ) 1 (actualSeedEquation 57 1) ∈
      q.asHomogeneousIdeal.toIdeal
    rw [surfaceQuotient_F]
    exact q.asHomogeneousIdeal.toIdeal.zero_mem
  have hh₀ : thetaH 1 ∈ P := by
    change surfaceQuotient (57 : ℂ) 1 (thetaH 1) ∈ q.asHomogeneousIdeal.toIdeal
    rw [surfaceQuotient_h]
    exact q.asHomogeneousIdeal.toIdeal.zero_mem
  have hF : CycleQ2IncidenceEquations.smoothF (57 : ℂ) Complex.I ∈ P := by
    simpa only [actualSeedEquation_eq_smoothF] using hF₀
  have hh : CycleQ2IncidenceEquations.smoothH Complex.I ∈ P := by
    simpa only [smoothH_eq_thetaH] using hh₀
  have hx : ∃ j : Fin 5, X j ∉ P := ⟨j, hj⟩
  rcases CycleQ2SeedCoordinateCover.seedPrime_coordinate_cover (57 : ℂ) Complex.I
      P hh hF hx with h₁ | h₂ | h₃
  · exact Opens.mem_iSup.mpr ⟨0, h₁⟩
  · exact Opens.mem_iSup.mpr ⟨1, h₂⟩
  · exact Opens.mem_iSup.mpr ⟨2, h₃⟩

/-- A genuine cover of the whole surface by the enlarged residue patches. -/
theorem patchOpen_cover : (⨆ a : PatchIndex, patchOpen a) = ⊤ := by
  apply top_le_iff.mp
  intro q _
  have hq : q ∈ ⨆ i : Fin 3, coordinateOpen i := by
    rw [coordinateOpen_cover]
    trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hq
  rw [← coordinate_minor_cover] at hi
  obtain ⟨a, ha⟩ := Opens.mem_iSup.mp hi
  obtain ⟨b, hb⟩ := Opens.mem_iSup.mp ha
  exact Opens.mem_iSup.mpr ⟨(i, X (variableIndex a), X (variableIndex b)), hb⟩

/-- The former normal patches are literal members of the enlarged family. -/
def originalIndex : CycleQ2SurfaceCubicGluing.PatchIndex → PatchIndex
  | .inl a => (0,
      CycleQ2GeometricSurfaceAdjunction.normalPolynomial
        (CycleQ2GeometricAffineCurveCharts.firstQuadric 57) a.1,
      CycleQ2GeometricSurfaceAdjunction.includeCurve (X a.2))
  | .inr a => (1,
      CycleQ2GeometricSurfaceAdjunction.normalPolynomial
        (CycleQ2GeometricAffineCurveCharts.secondQuadric 57) a.1,
      CycleQ2GeometricSurfaceAdjunction.includeCurve (X a.2))

theorem patchOpen_originalIndex (a : CycleQ2SurfaceCubicGluing.PatchIndex) :
    patchOpen (originalIndex a) = CycleQ2SurfaceCubicGluing.patchOpen 57 1 a := by
  cases a <;> rfl

#print axioms coordinate_minor_cover
#print axioms coordinateOpen_cover
#print axioms patchOpen_cover
#print axioms patchOpen_originalIndex

end CycleQ2FullSurfaceResidueCover

end
