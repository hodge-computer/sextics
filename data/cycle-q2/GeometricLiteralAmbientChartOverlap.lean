import Proposal.GeometricLiteralAmbientCharts

/-! The pairwise intersections of the fixed threefold charts are the principal
opens used in the weighted residue calculation.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralAmbientChartOverlap

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial
open CycleQ2SeedCubicFamily CycleQ2SeedProjectiveFamily CycleQ2SeedFamilyChart
  CycleQ2SeedFamilyNormalized CycleQ2LiteralAmbientSmooth CycleQ2LiteralAmbientCharts
  CycleQ2IncidenceDehomogenizedChart CycleQ2LiteralAbelJacobiContraction

/-- On the i-th chart, the family section cutting out the j-th open is Xj/Xi. -/
private theorem familyLocalizationElement (r : ℂ) (i j : Fin 4) :
    HomogeneousLocalization.Away.isLocalizationElem (𝒜 := familyGrade r)
      (CycleQ2SeedFamilyChart.coordinate_mem_grade r i) (CycleQ2SeedFamilyChart.coordinate_mem_grade r j) = CycleQ2SeedFamilyChart.coordinateRatio r i j.castSucc := by
  apply HomogeneousLocalization.val_injective
  simp only [HomogeneousLocalization.Away.isLocalizationElem, CycleQ2SeedFamilyChart.coordinateRatio,
    CycleQ2SeedFamilyChart.homogeneousFraction,
    CycleQ2SeedFermatProj.geometricWeight_castSucc, HomogeneousLocalization.Away.val_mk, pow_one]
  rfl

theorem normalizedChartToFamily_away (r : ℂ) (i : Fin 4) :
    normalizedChartToFamily r i =
      Spec.map (CommRingCat.ofHom (normalizedChartEquiv r i).symm.toRingHom) ≫
        Proj.awayι (familyGrade r) (familyCoordinate r i.castSucc)
          (CycleQ2SeedFamilyChart.coordinate_mem_grade r i) (by decide) := by
  rw [normalizedChartToFamily, normalizedAffineChart_hom, Category.assoc]
  rfl

private theorem family_preimage (r : ℂ) (i j : Fin 4) :
    normalizedChartToFamily r i ⁻¹ᵁ coordinateOpen r j =
      PrimeSpectrum.basicOpen (normalizedCoordinate r i j.castSucc) := by
  rw [normalizedChartToFamily_away, Scheme.Hom.comp_preimage, coordinateOpen]
  rw [Proj.awayι_preimage_basicOpen (𝒜 := familyGrade r) (CycleQ2SeedFamilyChart.coordinate_mem_grade r i)
    (by decide) (CycleQ2SeedFamilyChart.coordinate_mem_grade r j) (by decide), familyLocalizationElement]
  change PrimeSpectrum.basicOpen (chartToNormalized r i (CycleQ2SeedFamilyChart.coordinateRatio r i j.castSucc)) = _
  rw [chartToNormalized_coordinateRatio]

/-- The ratio Xj/Xi in the same coordinates used for the fixed-sextic contraction. -/
theorem chartSpecialization_ratio (i j : Fin 4) :
    chartSpecialization i (normalizedCoordinate 57 i j.castSucc) =
      Ideal.Quotient.mk (fixedIdeal i) (linearCoordinate i j) := by
  rw [normalizedCoordinate, chartSpecialization_polynomial, MvPolynomial.map_X, dehomogenize_castSucc]

/-- The pullback of the j-th ambient open to the i-th affine chart is the
principal open of Xj/Xi, including the case i = j. -/
theorem chartInclusion_preimage_fixedOpen (i j : Fin 4) :
    chartInclusion i ⁻¹ᵁ fixedOpen j =
      PrimeSpectrum.basicOpen (Ideal.Quotient.mk (fixedIdeal i) (linearCoordinate i j)) := by
  change (chartInclusion i ≫ pullback.snd incidenceParameter (familyToParameters 57)) ⁻¹ᵁ
    coordinateOpen 57 j = _
  rw [chartInclusion_toFamily]
  change Spec.map (CommRingCat.ofHom (chartSpecialization i)) ⁻¹ᵁ
    (normalizedChartToFamily 57 i ⁻¹ᵁ coordinateOpen 57 j) = _
  rw [family_preimage]
  change PrimeSpectrum.basicOpen (chartSpecialization i (normalizedCoordinate 57 i j.castSucc)) = _
  rw [chartSpecialization_ratio]

theorem chartInclusion_preimage_other (i : Fin 4) (k : Fin 3) :
    chartInclusion i ⁻¹ᵁ fixedOpen (i.succAbove k) =
      PrimeSpectrum.basicOpen (Ideal.Quotient.mk (fixedIdeal i) (X (some k))) := by
  rw [chartInclusion_preimage_fixedOpen, linearCoordinate_succAbove]

/-- The conormal and residue calculations on the ordered overlap invert the
affine coordinate indexed by k, which is the ratio Xj/Xi. -/
abbrev OverlapRing (i : Fin 4) (k : Fin 3) :=
  Localization.Away (Ideal.Quotient.mk (fixedIdeal i) (X (some k)))

def fixedOverlapChart (i : Fin 4) (k : Fin 3) :
    (chartInclusion i ⁻¹ᵁ fixedOpen (i.succAbove k)).toScheme ≅
      Spec (CommRingCat.of (OverlapRing i k)) :=
  (Spec (CommRingCat.of (T i))).isoOfEq (chartInclusion_preimage_other i k) ≪≫
    basicOpenIsoSpecAway (R := CommRingCat.of (T i)) (Ideal.Quotient.mk (fixedIdeal i) (X (some k)))

/-- The affine morphism into chart i is induced by the canonical localization. -/
@[reassoc] theorem fixedOverlapChart_hom_toChart (i : Fin 4) (k : Fin 3) :
    (fixedOverlapChart i k).hom ≫
        Spec.map (CommRingCat.ofHom (algebraMap (T i) (OverlapRing i k))) =
      (chartInclusion i ⁻¹ᵁ fixedOpen (i.succAbove k)).ι := by
  simp only [fixedOverlapChart, Iso.trans_hom, Category.assoc]
  rw [basicOpenIsoSpecAway_hom_SpecMap (R := CommRingCat.of (T i))
    (Ideal.Quotient.mk (fixedIdeal i) (X (some k)))]
  exact Scheme.isoOfEq_hom_ι _ _

end CycleQ2LiteralAmbientChartOverlap

#print axioms CycleQ2LiteralAmbientChartOverlap.chartInclusion_preimage_fixedOpen
#print axioms CycleQ2LiteralAmbientChartOverlap.fixedOverlapChart_hom_toChart
