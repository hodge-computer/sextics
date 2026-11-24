import Proposal.GeometricLiteralAmbientSurfaceRestriction
import Proposal.GeometricLiteralAmbientChartOverlap
import Proposal.GeometricLiteralThreefoldSurfaceTestLifts
import Proposal.GeometricLiteralNativeTangentEvaluation

/-! The reduced point of the threefold surface test is the geometric surface inclusion
on each principal open where the test is evaluated.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralThreefoldSurfaceChartMap

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial
  CycleQ2GeometricIncidenceProj CycleQ2SeedCubicFamily CycleQ2SeedProjectiveFamily
  CycleQ2SeedFamilyChart CycleQ2SeedFamilyNormalized CycleQ2LiteralAmbientSmooth
  CycleQ2LiteralAmbientCharts CycleQ2LiteralAmbientChartOverlap CycleQ2LiteralAmbientSurface
  CycleQ2LiteralProjectiveIntersections CycleQ2LiteralProjectiveIntersectionComplex
  CycleQ2LiteralNativeTangentEvaluation CycleQ2LiteralAffineCotangent
  CycleQ2LiteralThreefoldSurfaceTestLifts CycleQ2IncidenceDehomogenizedChart
  CycleQ2LiteralAbelJacobiContraction

attribute [local instance] closedComplexAlgebra closedComplexSMul closedComplexModule

private def specialize (i : Fin 4) : CycleQ2SeedFamilyChart.ChartRing 57 i →+* T i :=
  (chartSpecialization i).comp (chartToNormalized 57 i).toRingHom

private theorem specialize_toFamily (i : Fin 4) :
    chartInclusion i ≫ pullback.snd incidenceParameter (familyToParameters 57) =
      Spec.map (CommRingCat.ofHom (specialize i)) ≫
        Proj.awayι (familyGrade 57) (familyCoordinate 57 i.castSucc)
          (CycleQ2SeedFamilyChart.coordinate_mem_grade 57 i) (by decide) := by
  rw [chartInclusion_toFamily, normalizedChartToFamily_away, ← Category.assoc, ← Spec.map_comp]
  rfl

private theorem specialize_fixedPoint (s : Finset Vertex) (v : Vertex) (hv : v ∈ s)
    (x : CycleQ2SeedFamilyChart.ChartRing 57 (chartIndex v)) :
    fixedPoint s v hv (specialize (chartIndex v) x) =
      CycleQ2LiteralAmbientSurfaceRestriction.restriction s v hv x := by
  obtain ⟨n, a, ha, rfl⟩ := HomogeneousLocalization.Away.mk_surjective (familyGrade 57)
    (CycleQ2SeedFamilyChart.coordinate_mem_grade 57 (chartIndex v)) x
  obtain ⟨p, hp, rfl⟩ := ha
  have hp' : p.IsWeightedHomogeneous geometricWeight n := by simpa using hp
  let q := MvPolynomial.map (coefficientEvaluation incidenceCoefficients) p
  have hq : q.IsWeightedHomogeneous geometricWeight n := by
    intro m hm
    apply hp'
    intro hz
    exact hm (by rw [MvPolynomial.coeff_map, hz, map_zero])
  change fixedPoint s v hv (chartSpecialization _ (chartToNormalized 57 _
      (CycleQ2SeedFamilyChart.homogeneousFraction 57 (chartIndex v) n p hp'))) =
    CycleQ2LiteralAmbientSurfaceRestriction.restriction s v hv
      (CycleQ2SeedFamilyChart.homogeneousFraction 57 (chartIndex v) n p hp')
  rw [chartToNormalized_homogeneousFraction, chartSpecialization_polynomial]
  exact (fixedPoint_homogeneous s v hv q hq).trans
    (CycleQ2LiteralAmbientSurfaceRestriction.restriction_fraction s v hv n p hp').symm

private theorem fiber_chart_eq {A T C K : CommRingCat} {X F B : Scheme}
    (b : Spec K ⟶ B) (f : F ⟶ B) (m : Spec A ⟶ X) (u : X ⟶ pullback b f)
    (p : Spec T ⟶ pullback b f) (t : T ⟶ A) (ka : K ⟶ A) (kt : K ⟶ T)
    (a : C ⟶ T) (d : C ⟶ A) (x : Spec C ⟶ F)
    (hkm : m ≫ u ≫ pullback.fst b f = Spec.map ka) (hkp : p ≫ pullback.fst b f = Spec.map kt)
    (hxm : m ≫ u ≫ pullback.snd b f = Spec.map d ≫ x) (hxp : p ≫ pullback.snd b f = Spec.map a ≫ x)
    (hk : kt ≫ t = ka) (hd : a ≫ t = d) : m ≫ u = Spec.map t ≫ p := by
  apply pullback.hom_ext
  · simp only [Category.assoc, hkm, hkp, ← Spec.map_comp, hk]
  · rw [Category.assoc, Category.assoc, hxm, hxp, ← hd, Spec.map_comp, Category.assoc]

set_option maxHeartbeats 1200000 in
/-- Evaluating the test chart at the reduced point gives the restriction of
the closed immersion of the trace surface into the fixed threefold. -/
theorem fixedPoint_over_threefold (s : Finset Vertex) (hs : s.Nonempty) (v : Vertex) (hv : v ∈ s) :
    (nativeChart s hs).inv ≫ (closedOpen s).ι ≫ surfaceToFiber =
      Spec.map (CommRingCat.ofHom (fixedPoint s v hv).toRingHom) ≫ chartInclusion (chartIndex v) := by
  rw [← Category.assoc]
  change closedAffineMap s hs ≫ surfaceToFiber = _
  apply fiber_chart_eq incidenceParameter (familyToParameters 57) (closedAffineMap s hs)
    surfaceToFiber (chartInclusion (chartIndex v)) (CommRingCat.ofHom (fixedPoint s v hv).toRingHom)
    (CommRingCat.ofHom (algebraMap ℂ (ClosedRing s))) (CommRingCat.ofHom (algebraMap ℂ (T (chartIndex v))))
    (CommRingCat.ofHom (specialize (chartIndex v)))
    (CommRingCat.ofHom (CycleQ2LiteralAmbientSurfaceRestriction.restriction s v hv)) _
    _ (chartInclusion_overComplex (chartIndex v)) _ (specialize_toFamily (chartIndex v))
    (CommRingCat.hom_ext (RingHom.ext (fun c => (fixedPoint s v hv).commutes c)))
    (CommRingCat.hom_ext (RingHom.ext (specialize_fixedPoint s v hv)))
  · rw [surfaceToFiber, pullback.lift_fst]
    exact closedCoefficient_scheme s hs
  · rw [surfaceToFiber, pullback.lift_snd]
    exact (CycleQ2LiteralAmbientSurfaceRestriction.restriction_toFamily s hs v hv).symm

private theorem open_le_of_factor {X Y S T : Scheme} {U : X.Opens} {V : Y.Opens}
    (e : U.toScheme ≅ S) (g : T ≅ V.toScheme) (f : X ⟶ Y) (h : S ⟶ T)
    (w : e.inv ≫ U.ι ≫ f = h ≫ g.hom ≫ V.ι) : U ≤ f ⁻¹ᵁ V := by
  intro z hz
  let x : U.toScheme := ⟨z,hz⟩
  have he : e.inv (e.hom x) = x := by
    change (e.hom ≫ e.inv) x = x
    rw [e.hom_inv_id]
    rfl
  have hw := congrArg (fun m : S ⟶ Y => m (e.hom x)) w
  change f (U.ι (e.inv (e.hom x))) = V.ι (g.hom (h (e.hom x))) at hw
  rw [he] at hw
  change f (U.ι x) ∈ V
  rw [hw]
  exact (g.hom (h (e.hom x))).property

theorem closedOpen_le_fixedOpen (s : Finset Vertex) (hs : s.Nonempty) (v : Vertex) (hv : v ∈ s) :
    closedOpen s ≤ surfaceToFiber ⁻¹ᵁ fixedOpen (chartIndex v) :=
  open_le_of_factor (nativeChart s hs) (fixedChart (chartIndex v)) surfaceToFiber
    (Spec.map (CommRingCat.ofHom (fixedPoint s v hv).toRingHom)) (fixedPoint_over_threefold s hs v hv)

end CycleQ2LiteralThreefoldSurfaceChartMap

#print axioms CycleQ2LiteralThreefoldSurfaceChartMap.fixedPoint_over_threefold
#print axioms CycleQ2LiteralThreefoldSurfaceChartMap.closedOpen_le_fixedOpen
