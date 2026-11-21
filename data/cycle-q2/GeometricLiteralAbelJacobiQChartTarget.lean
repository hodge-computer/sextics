import Proposal.GeometricLiteralAbelJacobiQCoordinates
import Proposal.GeometricLiteralAmbientCylinder
import Proposal.GeometricLiteralAmbientChartOverlap

/-!
# The native affine target of the first-order moving curve

The dehomogenization of the native sextic on its weight-one charts gives
the affine open immersion used in the smooth model of the incidence fiber.
The comparison preserves the original homogeneous fractions.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralAbelJacobiQChartTarget

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial
  CycleQ2IncidenceFamilyContainment CycleQ2GeometricIncidenceProj
  CycleQ2SeedCubicFamily CycleQ2SeedProjectiveFamily CycleQ2SeedFamilyChart
  CycleQ2SeedFamilyNormalized CycleQ2LiteralAmbientSmooth CycleQ2LiteralAmbientCharts
  CycleQ2LiteralAmbientCylinder CycleQ2LiteralAmbientChartOverlap
  CycleQ2GradedAwaySpecialization CycleQ2LiteralAbelJacobiContraction
  CycleQ2IncidenceDehomogenizedChart CycleQ2LiteralAbelJacobiQCoordinates

private abbrev seed := CycleQ2LiteralAmbientCylinder.point

private abbrev cubicGraded :=
  CycleQ2LiteralAmbientProjFiberPolynomial.graded cubicEval (familyIdeal 57) (sexticIdeal seed)
    cubicIdeal_map

private theorem coordinate_map (i : Fin 4) :
    cubicGraded (familyCoordinate 57 i.castSucc) = sexticX seed i := by
  change Ideal.Quotient.mk _ (MvPolynomial.map cubicEval (X i.castSucc)) = Ideal.Quotient.mk _ (X i.castSucc)
  rw [MvPolynomial.map_X]

private abbrev fiberChartMap (i : Fin 4) :=
  awayMapOfEq cubicGraded (familyCoordinate 57 i.castSucc) (sexticX seed i) (coordinate_map i)

private theorem fiberChartMap_comp (i : Fin 4) :
    (nativeToT i).comp (fiberChartMap i) =
      (chartSpecialization i).comp (chartToNormalized 57 i).toRingHom := by
  apply RingHom.ext
  intro x
  obtain ⟨n, a, ha, rfl⟩ := HomogeneousLocalization.Away.mk_surjective (familyGrade 57)
    (CycleQ2SeedFamilyChart.coordinate_mem_grade 57 i) x
  obtain ⟨p,hp,rfl⟩ := ha
  have hp' : p.IsWeightedHomogeneous geometricWeight n := by simpa using hp
  have hq : (MvPolynomial.map cubicEval p).IsWeightedHomogeneous geometricWeight n := by
    intro m hm
    apply hp'
    intro hz
    exact hm (by rw [MvPolynomial.coeff_map, hz, map_zero])
  rw [RingHom.comp_apply, fiberChartMap, awayMapOfEq_mk _ _ _ _
    (CycleQ2SeedFamilyChart.coordinate_mem_grade 57 i) (sexticX_mem seed i)]
  exact (nativeToT_fraction i n (MvPolynomial.map cubicEval p) hq).trans
    ((congrArg (chartSpecialization i)
      (chartToNormalized_homogeneousFraction 57 i n p hp')).trans
        (chartSpecialization_polynomial i p)).symm

section GradedSpecialization

open CycleQ2LiteralAmbientProjFiber

private theorem projective_away {R S : Type} [CommRing R] [CommRing S]
    (φ : R →+* S) (s : S →+* R) (hs : φ.comp s = RingHom.id S)
    (I : Ideal (MvPolynomial (Fin 5) R)) (J : Ideal (MvPolynomial (Fin 5) S))
    (hIJ : I.map (MvPolynomial.map φ) = J) [GradedRing (Grade I)] [GradedRing (Grade J)]
    (a : MvPolynomial (Fin 5) R ⧸ I) (b : MvPolynomial (Fin 5) S ⧸ J)
    (hab : CycleQ2LiteralAmbientProjFiberPolynomial.graded φ I J hIJ a = b)
    (ha : a ∈ Grade I 1) (hb : b ∈ Grade J 1) :
    Proj.awayι (Grade J) b hb (by decide) ≫ projective φ s hs I J hIJ =
      Spec.map (CommRingCat.ofHom (awayMapOfEq
        (CycleQ2LiteralAmbientProjFiberPolynomial.graded φ I J hIJ) a b hab)) ≫
        Proj.awayι (Grade I) a ha (by decide) :=
  awayι_comp_map_of_eq _ (irrelevant_le φ s hs I J hIJ) a b hab (by decide) ha hb

end GradedSpecialization

private theorem nativeAway_toFamily (i : Fin 4) :
    Proj.awayι (sexticGrade seed) (sexticX seed i) (sexticX_mem seed i) (by decide) ≫
        CycleQ2LiteralAmbientProjFiber.projective cubicEval (algebraMap ℂ ParameterRing)
          cubic_section (familyIdeal 57) (sexticIdeal seed) cubicIdeal_map =
      Spec.map (CommRingCat.ofHom (fiberChartMap i)) ≫
        Proj.awayι (familyGrade 57) (familyCoordinate 57 i.castSucc)
          (CycleQ2SeedFamilyChart.coordinate_mem_grade 57 i) (by decide) :=
  projective_away cubicEval (algebraMap ℂ ParameterRing) cubic_section (familyIdeal 57)
    (sexticIdeal seed) cubicIdeal_map _ _ (coordinate_map i)
    (CycleQ2SeedFamilyChart.coordinate_mem_grade 57 i) (sexticX_mem seed i)

/-- The native projective sextic chart with its explicit dehomogenized coordinates. -/
def nativeChartInclusion (i : Fin 4) : Spec (CommRingCat.of (T i)) ⟶ Native :=
  Spec.map (CommRingCat.ofHom (nativeToT i)) ≫
    Proj.awayι (sexticGrade seed) (sexticX seed i) (sexticX_mem seed i) (by decide)

/-- Both constructions give the very same morphism to the fixed incidence fiber. -/
@[reassoc] theorem nativeChartInclusion_toIncidence (i : Fin 4) :
    nativeChartInclusion i ≫ nativeToIncidence.hom = CycleQ2LiteralAmbientCharts.chartInclusion i := by
  have : IsClosedImmersion incidenceParameter := IsClosedImmersion.spec_of_surjective
    (CommRingCat.ofHom cubicEval) (fun z => ⟨algebraMap ℂ ParameterRing z, RingHom.congr_fun cubic_section z⟩)
  apply (cancel_mono (pullback.snd incidenceParameter (familyToParameters 57))).mp
  rw [Category.assoc, nativeToIncidence_snd, chartInclusion_toFamily, nativeChartInclusion, Category.assoc,
    normalizedChartToFamily_away, nativeAway_toFamily]
  simp only [← Category.assoc, ← Spec.map_comp]
  exact congrArg (fun f : CycleQ2SeedFamilyChart.ChartRing 57 i →+* T i =>
    Spec.map (CommRingCat.ofHom f) ≫ _) (fiberChartMap_comp i)

instance (i : Fin 4) : IsOpenImmersion (nativeChartInclusion i) := by
  have he : nativeChartInclusion i = CycleQ2LiteralAmbientCharts.chartInclusion i ≫ nativeToIncidence.inv := by
    rw [← nativeChartInclusion_toIncidence, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [he]
  infer_instance

end CycleQ2LiteralAbelJacobiQChartTarget
end

#print axioms CycleQ2LiteralAbelJacobiQChartTarget.nativeChartInclusion_toIncidence
