import Proposal.GeometricLiteralAmbientChartOverlap
import Proposal.GeometricLiteralAmbientFamilyOverlap
import Proposal.GeometricLiteralThreefoldResidueChartMaps

/-! Comparison of the weighted transition morphisms on the native fixed threefold.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralAmbientChartTransition

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial
open CycleQ2GeometricIncidenceProj CycleQ2SeedCubicFamily CycleQ2SeedProjectiveFamily
  CycleQ2SeedFamilyChart CycleQ2SeedFamilyNormalized CycleQ2LiteralAmbientSmooth
  CycleQ2LiteralAmbientCharts CycleQ2LiteralAmbientChartOverlap
  CycleQ2IncidenceDehomogenizedChart CycleQ2LiteralAbelJacobiContraction
  CycleQ2LiteralThreefoldResidueCoordinates CycleQ2LiteralThreefoldResidueChartMaps

attribute [local instance] CycleQ2LiteralThreefoldResidueCoordinates.fixedAmbientAlgebra
  CycleQ2LiteralThreefoldResidueChartMaps.fixedAmbientTower
  CycleQ2LiteralThreefoldResidueChartMaps.sourceFixedAlgebra
  CycleQ2LiteralThreefoldResidueChartMaps.sourceFixedTower

private abbrev Chart (i : Fin 4) := CycleQ2SeedFamilyChart.ChartRing 57 i

private def chartValue (i : Fin 4) : Chart i →+* T i :=
  (chartSpecialization i).comp (chartToNormalized 57 i).toRingHom

private theorem chartValue_fraction (i : Fin 4) (n : ℕ) (p : FamilyPolynomial)
    (hp : p.IsWeightedHomogeneous geometricWeight n) :
    chartValue i (CycleQ2SeedFamilyChart.homogeneousFraction 57 i n p hp) =
      Ideal.Quotient.mk (fixedIdeal i)
        (dehomogenize i (MvPolynomial.map (coefficientEvaluation incidenceCoefficients) p)) := by
  rw [chartValue, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
    chartToNormalized_homogeneousFraction, chartSpecialization_polynomial]

private theorem chartValue_ratio (i : Fin 4) (k : Fin 3) :
    chartValue i (CycleQ2SeedFamilyChart.coordinateRatio 57 i (i.succAbove k).castSucc) =
      Ideal.Quotient.mk (fixedIdeal i) (X (some k)) := by
  change chartSpecialization i (chartToNormalized 57 i _) = _
  rw [chartToNormalized_coordinateRatio, chartSpecialization_ratio, linearCoordinate_succAbove]

private def sourceValue (i : Fin 4) (k : Fin 3) : Chart i →+* FixedOverlap i k :=
  (algebraMap (T i) (FixedOverlap i k)).comp (chartValue i)

private def targetValue (i : Fin 4) (k : Fin 3) : Chart (i.succAbove k) →+* FixedOverlap i k :=
  (fixedTargetMap i k).toRingHom.comp (chartValue (i.succAbove k))

private theorem sourceValue_ratio_unit (i : Fin 4) (k : Fin 3) :
    IsUnit (sourceValue i k (CycleQ2SeedFamilyChart.coordinateRatio 57 i (i.succAbove k).castSucc)) := by
  rw [sourceValue, RingHom.comp_apply, chartValue_ratio]
  exact IsLocalization.Away.algebraMap_isUnit (S := Localization.Away
    (Ideal.Quotient.mk (fixedIdeal i) (X (some k)))) _

private theorem source_polynomial (i : Fin 4) (k : Fin 3) (p : ChartPolynomial ℂ) :
    algebraMap (T i) (FixedOverlap i k) (Ideal.Quotient.mk (fixedIdeal i) p) =
      ambientToFixed i k (aeval (overlapCoordinates k) p) :=
  (AlgHom.congr_fun (fixedSourceMap_eq i k) (Ideal.Quotient.mk _ p)).symm

/-- A homogeneous polynomial restricts from either chart with exactly the power
of Xj/Xi dictated by its weight. Both sides are in the fixed-sextic overlap ring. -/
private theorem fraction_change_specialized (i : Fin 4) (k : Fin 3) (n : ℕ)
    (p : FamilyPolynomial) (hp : p.IsWeightedHomogeneous geometricWeight n) :
    targetValue i k (CycleQ2SeedFamilyChart.homogeneousFraction 57 (i.succAbove k) n p hp) *
      sourceValue i k (CycleQ2SeedFamilyChart.coordinateRatio 57 i (i.succAbove k).castSucc)^n =
        sourceValue i k (CycleQ2SeedFamilyChart.homogeneousFraction 57 i n p hp) := by
  let q := MvPolynomial.map (coefficientEvaluation incidenceCoefficients) p
  have hq : q.IsWeightedHomogeneous geometricWeight n := by
    intro m hm
    apply hp
    intro hz
    exact hm (by rw [MvPolynomial.coeff_map, hz, map_zero])
  have ht := homogeneous_change i (i.succAbove k) (overlapCoordinates k) (overlapInverse k)
    (by simpa only [Fin.insertNth_apply_succAbove] using overlapInverse_mul k) q hq
  simp only [sourceValue, targetValue, RingHom.comp_apply, chartValue_fraction, chartValue_ratio,
    source_polynomial, aeval_X]
  change ambientToFixed i k (aeval (changedCoordinate i (i.succAbove k) (overlapCoordinates k)
      (overlapInverse k)) (dehomogenize _ q)) * (ambientToFixed i k (overlapCoordinates k (some k)))^n =
        ambientToFixed i k (aeval (overlapCoordinates k) (dehomogenize i q))
  rw [← map_pow, ← map_mul]
  apply congrArg (ambientToFixed i k)
  rw [ht]
  calc
    _ = (overlapInverse k * overlapCoordinates k (some k))^n *
        aeval (overlapCoordinates k) (dehomogenize i q) := by ring
    _ = _ := by rw [overlapInverse_mul, one_pow, one_mul]

private theorem chartValue_toFamily (i : Fin 4) :
    chartInclusion i ≫ pullback.snd incidenceParameter (familyToParameters 57) =
      Spec.map (CommRingCat.ofHom (chartValue i)) ≫
        Proj.awayι (familyGrade 57) (familyCoordinate 57 i.castSucc)
          (CycleQ2SeedFamilyChart.coordinate_mem_grade 57 i) (by decide) := by
  rw [chartInclusion_toFamily, normalizedChartToFamily_away, ← Category.assoc, ← Spec.map_comp]
  rfl


open CycleQ2LiteralAmbientFamilyOverlap

private def pairValue (i : Fin 4) (k : Fin 3) :
    PairRing 57 i (i.succAbove k) →+* FixedOverlap i k := by
  letI := (leftRestriction 57 i (i.succAbove k)).toAlgebra
  letI := leftRestriction_isLocalization 57 i (i.succAbove k)
  exact IsLocalization.Away.lift (CycleQ2SeedFamilyChart.coordinateRatio 57 i (i.succAbove k).castSucc)
    (g := sourceValue i k) (sourceValue_ratio_unit i k)

private theorem pairValue_left (i : Fin 4) (k : Fin 3) (x : Chart i) :
    pairValue i k (leftRestriction 57 i (i.succAbove k) x) = sourceValue i k x := by
  let := (leftRestriction 57 i (i.succAbove k)).toAlgebra
  let := leftRestriction_isLocalization 57 i (i.succAbove k)
  exact IsLocalization.Away.lift_eq (CycleQ2SeedFamilyChart.coordinateRatio 57 i (i.succAbove k).castSucc)
    (g := sourceValue i k) (sourceValue_ratio_unit i k) x

private theorem pairValue_right (i : Fin 4) (k : Fin 3) (x : Chart (i.succAbove k)) :
    pairValue i k (rightRestriction 57 i (i.succAbove k) x) = targetValue i k x := by
  obtain ⟨n, a, ha, rfl⟩ := HomogeneousLocalization.Away.mk_surjective (familyGrade 57)
    (CycleQ2SeedFamilyChart.coordinate_mem_grade 57 (i.succAbove k)) x
  obtain ⟨p, hp, rfl⟩ := ha
  have hp' : p.IsWeightedHomogeneous geometricWeight n := by simpa using hp
  change pairValue i k (rightRestriction 57 i (i.succAbove k)
      (CycleQ2SeedFamilyChart.homogeneousFraction 57 (i.succAbove k) n p hp')) =
    targetValue i k (CycleQ2SeedFamilyChart.homogeneousFraction 57 (i.succAbove k) n p hp')
  apply ((sourceValue_ratio_unit i k).pow n).mul_left_injective
  have h := congrArg (pairValue i k) (fraction_change 57 i (i.succAbove k) n p hp')
  rw [map_mul, map_pow, pairValue_left, pairValue_left] at h
  exact h.trans (fraction_change_specialized i k n p hp').symm

private theorem common_restrictions {A B C S : CommRingCat} {X : Scheme}
    (a : A ⟶ C) (b : B ⟶ C) (g : C ⟶ S) (u : A ⟶ S) (v : B ⟶ S)
    (hu : a ≫ g = u) (hv : b ≫ g = v)
    (x : Spec A ⟶ X) (y : Spec B ⟶ X) (h : Spec.map a ≫ x = Spec.map b ≫ y) :
    Spec.map u ≫ x = Spec.map v ≫ y := by
  subst u
  subst v
  simp only [Spec.map_comp, Category.assoc, h]

set_option maxHeartbeats 1200000 in
private theorem pairValue_away_square (i : Fin 4) (k : Fin 3) :
    Spec.map (CommRingCat.ofHom (targetValue i k)) ≫
        Proj.awayι (familyGrade 57) (familyCoordinate 57 (i.succAbove k).castSucc)
          (CycleQ2SeedFamilyChart.coordinate_mem_grade 57 (i.succAbove k)) (by decide) =
      Spec.map (CommRingCat.ofHom (sourceValue i k)) ≫
        Proj.awayι (familyGrade 57) (familyCoordinate 57 i.castSucc)
          (CycleQ2SeedFamilyChart.coordinate_mem_grade 57 i) (by decide) := by
  have hl : CommRingCat.ofHom (leftRestriction 57 i (i.succAbove k)) ≫
      CommRingCat.ofHom (pairValue i k) = CommRingCat.ofHom (sourceValue i k) :=
    CommRingCat.hom_ext (RingHom.ext (pairValue_left i k))
  have hr : CommRingCat.ofHom (rightRestriction 57 i (i.succAbove k)) ≫
      CommRingCat.ofHom (pairValue i k) = CommRingCat.ofHom (targetValue i k) :=
    CommRingCat.hom_ext (RingHom.ext (pairValue_right i k))
  exact common_restrictions _ _ _ _ _ hr hl _ _ (normalized_away_square 57 i (i.succAbove k)).symm

private theorem affine_fiber_eq {K S U V C D : CommRingCat} {X P : Scheme}
    (b : Spec K ⟶ P) (f : X ⟶ P) (u : Spec U ⟶ pullback b f) (v : Spec V ⟶ pullback b f)
    (s : U ⟶ S) (t : V ⟶ S) (uk : K ⟶ U) (vk : K ⟶ V) (a : C ⟶ U) (d : D ⟶ V)
    (x : Spec C ⟶ X) (y : Spec D ⟶ X)
    (hu : u ≫ pullback.fst b f = Spec.map uk) (hv : v ≫ pullback.fst b f = Spec.map vk)
    (hx : u ≫ pullback.snd b f = Spec.map a ≫ x) (hy : v ≫ pullback.snd b f = Spec.map d ≫ y)
    (hk : uk ≫ s = vk ≫ t) (hc : Spec.map (a ≫ s) ≫ x = Spec.map (d ≫ t) ≫ y) :
    Spec.map s ≫ u = Spec.map t ≫ v := by
  apply pullback.hom_ext
  · simp only [Category.assoc, hu, hv, ← Spec.map_comp, hk]
  · simpa only [Category.assoc, hx, hy, Spec.map_comp] using hc

set_option maxHeartbeats 1200000 in
/-- The weighted coordinate substitution in the residue calculation gives the
same morphism to the fixed threefold as the canonical localization on the
source chart. -/
theorem fixedTargetMap_over_threefold (i : Fin 4) (k : Fin 3) :
    Spec.map (CommRingCat.ofHom (fixedTargetMap i k).toRingHom) ≫ chartInclusion (i.succAbove k) =
      Spec.map (CommRingCat.ofHom (algebraMap (T i) (FixedOverlap i k))) ≫ chartInclusion i := by
  apply affine_fiber_eq incidenceParameter (familyToParameters 57)
    (chartInclusion (i.succAbove k)) (chartInclusion i)
    (CommRingCat.ofHom (fixedTargetMap i k).toRingHom)
    (CommRingCat.ofHom (algebraMap (T i) (FixedOverlap i k)))
    (CommRingCat.ofHom (algebraMap ℂ (T (i.succAbove k))))
    (CommRingCat.ofHom (algebraMap ℂ (T i))) (CommRingCat.ofHom (chartValue (i.succAbove k)))
    (CommRingCat.ofHom (chartValue i)) _ _
    (chartInclusion_overComplex (i.succAbove k)) (chartInclusion_overComplex i)
    (chartValue_toFamily (i.succAbove k)) (chartValue_toFamily i) _ (pairValue_away_square i k)
  exact CommRingCat.hom_ext (RingHom.ext (fun c => ((fixedTargetMap i k).commutes c).trans
    ((IsScalarTower.toAlgHom ℂ (T i) (FixedOverlap i k)).commutes c).symm))

end CycleQ2LiteralAmbientChartTransition

#print axioms CycleQ2LiteralAmbientChartTransition.fixedTargetMap_over_threefold
