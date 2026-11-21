import Proposal.GeometricLiteralAmbientSingleSurfaceRestriction
import Proposal.GeometricLiteralThreefoldSurfaceChartMap
import Proposal.GeometricLiteralThreefoldSurfaceNormal
import Proposal.GeometricChartSectionPullback

/-! The restriction to the Jacobian chart is the actual map from the
trace surface to the fixed threefold; its sections agree on native subopens.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralThreefoldJacobianChartMap

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial
  CycleQ2GeometricIncidenceProj CycleQ2SeedCubicFamily CycleQ2SeedProjectiveFamily
  CycleQ2SeedFamilyChart CycleQ2SeedFamilyNormalized CycleQ2LiteralAmbientSmooth
  CycleQ2LiteralAmbientCharts CycleQ2LiteralAmbientChartOverlap CycleQ2LiteralAmbientSurface
  CycleQ2LiteralProjectiveIntersections CycleQ2LiteralProjectiveIntersectionComplex
  CycleQ2LiteralNativeTangentEvaluation CycleQ2LiteralThreefoldSurfaceTestLifts
  CycleQ2LiteralAbelJacobiContraction CycleQ2LiteralAbelJacobiMovingNormal
  CycleQ2LiteralThreefoldSurfaceNormal CycleQ2GeometricSurfaceJacobianCharts
  CycleQ2GeometricSurfaceDehomogenizedCharts CycleQ2GeometricSurfaceAdjunction
  CycleQ2CartierProjectiveCover CycleQ2CartierSurfaceGrading CycleQ2GeometricSurfaceCoefficients
  CycleQ2LiteralAmbientSingleSurfaceRestriction CycleQ2GeometricAffineChartSections
  CycleQ2LiteralNativeDifferentialSections CycleQ2ChartSectionPullback
  CycleQ2LiteralThreefoldSurfaceChartMap

attribute [local instance] closedComplexAlgebra closedComplexSMul closedComplexModule

private abbrev nativeMap (i : Fin 4) : CycleQ2SeedFamilyChart.ChartRing 57 i →+* DehomogenizedRing 57 1 i :=
  (coordinateChartEquiv 57 1 i).toRingHom.comp (coordinateSpecialization i)

private abbrev ambientMap (i : Fin 4) : CycleQ2SeedFamilyChart.ChartRing 57 i →+* T i :=
  (chartSpecialization i).comp (chartToNormalized 57 i).toRingHom

private theorem restrict_value (i : Fin 4) (n a : P) (x : CycleQ2SeedFamilyChart.ChartRing 57 i) :
    algebraMap (DehomogenizedRing 57 1 i) (Patch i n a) (nativeMap i x) =
      toSurface i n a (ambientMap i x) := by
  obtain ⟨d, b, hb, rfl⟩ := HomogeneousLocalization.Away.mk_surjective (familyGrade 57)
    (CycleQ2SeedFamilyChart.coordinate_mem_grade 57 i) x
  obtain ⟨p, hp, rfl⟩ := hb
  have hp' : p.IsWeightedHomogeneous geometricWeight d := by simpa using hp
  let u := CycleQ2SeedFamilyChart.homogeneousFraction 57 i d p hp'
  change algebraMap _ (Patch i n a) (coordinateChartEquiv 57 1 i (coordinateSpecialization i u)) =
    toSurface i n a (chartSpecialization i (chartToNormalized 57 i u))
  dsimp only [u]
  rw [coordinate_fraction, coordinateChartEquiv_homogeneousFraction,
    chartToNormalized_homogeneousFraction, chartSpecialization_polynomial]
  rfl

private theorem native_toFamily (i : Fin 4) :
    (coordinateAffineChart 57 1 i).inv ≫ (coordinatePatch 57 1 i.castSucc).ι ≫ surfaceToFamily =
      Spec.map (CommRingCat.ofHom (nativeMap i)) ≫
        Proj.awayι (familyGrade 57) (familyCoordinate 57 i.castSucc)
          (CycleQ2SeedFamilyChart.coordinate_mem_grade 57 i) (by decide) := by
  change (Spec.map (CommRingCat.ofHom (coordinateChartEquiv 57 1 i).toRingHom) ≫
      (Proj.basicOpenIsoSpec (surfaceGrade 57 1) _ (coordinate_mem_grade 57 1 i) (by decide)).inv) ≫
    (Proj.basicOpen (surfaceGrade 57 1) _).ι ≫ surfaceToFamily = _
  rw [Category.assoc, Proj.basicOpenIsoSpec_inv_ι_assoc, coordinate_square, ← Category.assoc,
    ← Spec.map_comp]
  rfl

private theorem ambient_toFamily (i : Fin 4) :
    chartInclusion i ≫ pullback.snd incidenceParameter (familyToParameters 57) =
      Spec.map (CommRingCat.ofHom (ambientMap i)) ≫
        Proj.awayι (familyGrade 57) (familyCoordinate 57 i.castSucc)
          (CycleQ2SeedFamilyChart.coordinate_mem_grade 57 i) (by decide) := by
  rw [chartInclusion_toFamily, normalizedChartToFamily_away, ← Category.assoc, ← Spec.map_comp]
  rfl

abbrev jacobianOpen (i : Fin 4) (n a : P) :=
  principalOpen (coordinateAffineChart 57 1 i) (augmentedJacobian (E i) n a)

abbrev jacobianChart (i : Fin 4) (n a : P) :=
  principalChart (coordinateAffineChart 57 1 i) (augmentedJacobian (E i) n a)

set_option maxHeartbeats 1000000 in
theorem toSurface_over_threefold (i : Fin 4) (n a : P) :
    (jacobianChart i n a).inv ≫ (jacobianOpen i n a).ι ≫ surfaceToFiber =
      Spec.map (CommRingCat.ofHom (toSurface i n a).toRingHom) ≫ chartInclusion i := by
  let l := CommRingCat.ofHom (algebraMap (DehomogenizedRing 57 1 i) (Patch i n a))
  let t := CommRingCat.ofHom (toSurface i n a).toRingHom
  have hc : CommRingCat.ofHom (algebraMap ℂ (T i)) ≫ t =
      CommRingCat.ofHom (algebraMap ℂ (Patch i n a)) :=
    CommRingCat.hom_ext (RingHom.ext (fun c => (toSurface i n a).commutes c))
  have hr : CommRingCat.ofHom (nativeMap i) ≫ l = CommRingCat.ofHom (ambientMap i) ≫ t :=
    CommRingCat.hom_ext (RingHom.ext (restrict_value i n a))
  apply pullback.hom_ext
  · simp only [Category.assoc]
    change _ ≫ _ ≫ surfaceToFiber ≫ incidenceFiberToComplex 57 = Spec.map t ≫ chartInclusion i ≫ incidenceFiberToComplex 57
    rw [surfaceToFiber_overComplex, chartInclusion_overComplex, ← Spec.map_comp, hc]
    exact principalChart_overComplex _ _ _ (coordinateAffineChart_overComplex 57 1 i)
  · simp only [Category.assoc, surfaceToFiber, pullback.lift_snd, ambient_toFamily]
    rw [← Category.assoc, principalChart_inv_ι]
    change (Spec.map l ≫ (coordinateAffineChart 57 1 i).inv ≫ (coordinatePatch 57 1 i.castSucc).ι) ≫
      surfaceToFamily = _
    rw [Category.assoc, Category.assoc, native_toFamily, ← Category.assoc, ← Spec.map_comp,
      ← Category.assoc, ← Spec.map_comp, hr]

private theorem subopen_of_chart_square {X Y S T : Scheme} {U : X.Opens} {V : Y.Opens}
    (e : U.toScheme ≅ S) (g : T ≅ V.toScheme) (f : X ⟶ Y) (h : S ⟶ T)
    (w : e.inv ≫ U.ι ≫ f = h ≫ g.hom ≫ V.ι) : U ≤ f ⁻¹ᵁ V := by
  intro z hz
  let x : U.toScheme := ⟨z,hz⟩
  have q := congrArg (fun m : S ⟶ Y => (e.hom ≫ m) x) w
  simp only [Iso.hom_inv_id_assoc] at q
  change f (U.ι x) = V.ι (g.hom (h (e.hom x))) at q
  change f (U.ι x) ∈ V
  rw [q]
  exact (g.hom (h (e.hom x))).property

theorem jacobianOpen_le_fixedOpen (i : Fin 4) (n a : P) :
    jacobianOpen i n a ≤ surfaceToFiber ⁻¹ᵁ fixedOpen i :=
  subopen_of_chart_square (jacobianChart i n a) (fixedChart i) surfaceToFiber
    (Spec.map (CommRingCat.ofHom (toSurface i n a).toRingHom)) (toSurface_over_threefold i n a)

/-- Native and Jacobian descriptions restrict every threefold function to
the same section on each common surface open. -/
theorem surface_sections_equal (s : Finset Vertex) (hs : s.Nonempty) (v : Vertex) (hv : v ∈ s)
    (n a : P) (W : Surface.Opens) (hJ : W ≤ jacobianOpen (chartIndex v) n a)
    (hW : W ≤ closedOpen s) (z : T (chartIndex v)) :
    chartSection (jacobianChart (chartIndex v) n a) (Over.mk (homOfLE hJ))
        (toSurface (chartIndex v) n a z) =
      Surface.presheaf.map (homOfLE hW).op (nativeSectionsAlgEquiv s hs (fixedPoint s v hv z)) := by
  let i := chartIndex v
  let hP := hW.trans (closedOpen_le_fixedOpen s hs v hv)
  have h₁ := chartSection_pullback surfaceToFiber (fixedChart i).symm (jacobianChart i n a)
    (toSurface i n a).toRingHom (jacobianOpen_le_fixedOpen i n a) (toSurface_over_threefold i n a)
    (fixedOpen i) le_rfl W hJ hP z
  have h₂ := chartSection_pullback surfaceToFiber (fixedChart i).symm (nativeChart s hs)
    (fixedPoint s v hv).toRingHom (closedOpen_le_fixedOpen s hs v hv) (fixedPoint_over_threefold s hs v hv)
    (fixedOpen i) le_rfl W hW hP z
  rw [← nativeChart_section]
  exact h₁.symm.trans (h₂.trans (chartSection_naturality (nativeChart s hs)
    (Over.homMk (homOfLE hW) : Over.mk (homOfLE hW) ⟶ Over.mk (𝟙 (closedOpen s))) _).symm)

end CycleQ2LiteralThreefoldJacobianChartMap

#print axioms CycleQ2LiteralThreefoldJacobianChartMap.toSurface_over_threefold
#print axioms CycleQ2LiteralThreefoldJacobianChartMap.surface_sections_equal
