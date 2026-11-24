import Proposal.GeometricGradedAwaySpecialization
import Proposal.GeometricRelativeCurveSeedProj
import Proposal.GeometricSpecializedCurveCoordinateChart
import Proposal.GeometricRelativeCurveChartFiberScheme

/-!
# Restricting the canonical global seed curve map to its actual charts

The canonical graded seed specialization induces a map between the
actual degree-zero coordinate rings. After the established chart
equivalences, this is exactly the same affine quotient specialization
used to compute the scheme-theoretic chart fiber. Consequently the
single global Proj map has the required naturality square on each
weight-one coordinate open. This supplies compatibility of the local
fiber comparisons with the global map, rather than inferring gluing
from independent local isomorphisms.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md for
attribution of the geometric route and the protected certificate gap.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2RelativeCurveSeedChart

open CategoryTheory AlgebraicGeometry MvPolynomial HomogeneousLocalization
open CycleQ2IncidenceNormalForm CycleQ2IncidenceUniversalChart CycleQ2IncidenceImageLine
  CycleQ2IncidenceEtaleParameter CycleQ2IncidencePolynomialJacobianBinding
  CycleQ2GeometricIncidenceProj CycleQ2IncidenceDehomogenizedChart
  CycleQ2IncidenceChartFiberScheme CycleQ2RelativeConstantSection
  CycleQ2RelativeConstantCurve CycleQ2RelativeConstantCurveFiber
  CycleQ2RelativeCurveChart CycleQ2RelativeCurveChartScheme
  CycleQ2RelativeCurveChartFiber CycleQ2RelativeCurveSeedMap
  CycleQ2RelativeCurveSeedProj CycleQ2SpecializedProjectiveCurve
  CycleQ2SpecializedCurveCoordinateChart CycleQ2GradedAwaySpecialization

attribute [local instance] CycleQ2RelativeCurveSeedMap.incidenceSurfaceCommRing
  CycleQ2RelativeCurveSeedMap.seedSurfaceCommRing
  CycleQ2RelativeCurveSeedMap.relativeCurveCommRing
  CycleQ2RelativeCurveSeedMap.specializedCurveCommRing
  CycleQ2RelativeCurveChartScheme.curveCoordinateCommRing
  CycleQ2RelativeCurveChart.coordinateRingCommRing
  CycleQ2RelativeCurveChart.coordinateLocalizationCommRing
  CycleQ2RelativeCurveChart.dehomogenizedCommRing
  CycleQ2SpecializedCurveCoordinateChart.specializedCoordinateCommRing
  CycleQ2RelativeCurveChartFiber.incidenceCurveChartCommRing
  CycleQ2RelativeCurveChartFiber.seedCurveChartCommRing

private theorem seedPolynomial_homogeneous {p : MvPolynomial (Fin 5) ParameterAlgebra}
    {n : ℕ} (hp : p.IsWeightedHomogeneous geometricWeight n) :
    (MvPolynomial.map seedMap p).IsWeightedHomogeneous geometricWeight n := by
  intro d hd
  apply hp
  intro hz
  apply hd
  rw [MvPolynomial.coeff_map, hz, map_zero]

def seedCurveCoordinateSpecialization (t : Fin 3 → ℂ) (i : Fin 4) :
    CurveCoordinateRing incidencePoint t i →+*
      SpecializedCoordinateRing (seedPoint (57 : ℂ) Complex.I) t i :=
  awayMapOfEq (seedCurveGradedMap t)
    (relativeCurveRingMap incidencePoint t (surfaceQuotient incidencePoint (X i.castSucc)))
    (specializedCurveRingMap (seedPoint (57 : ℂ) Complex.I) t
      (surfaceQuotient (seedPoint (57 : ℂ) Complex.I) (X i.castSucc)))
    (seedCurveGradedMap_coordinate t i.castSucc)

theorem seedCurveCoordinateSpecialization_fraction (t : Fin 3 → ℂ) (i : Fin 4)
    (n : ℕ) (p : MvPolynomial (Fin 5) ParameterAlgebra)
    (hp : p.IsWeightedHomogeneous geometricWeight n) :
    seedCurveCoordinateSpecialization t i
        (coordinateCurveMap incidencePoint t i (homogeneousFraction incidencePoint i n p hp)) =
      specializedCoordinateMap (seedPoint (57 : ℂ) Complex.I) t i
        (homogeneousFraction (seedPoint (57 : ℂ) Complex.I) i n
          (MvPolynomial.map seedMap p) (seedPolynomial_homogeneous hp)) := by
  have hpSource : surfaceQuotient incidencePoint p ∈ surfaceGrade incidencePoint (n • (1 : ℕ)) := by
    simpa only [smul_eq_mul, mul_one] using
      (show surfaceQuotient incidencePoint p ∈ surfaceGrade incidencePoint n from ⟨p, hp, rfl⟩)
  have hpTarget : surfaceQuotient (seedPoint (57 : ℂ) Complex.I) (MvPolynomial.map seedMap p) ∈
      surfaceGrade (seedPoint (57 : ℂ) Complex.I) (n • (1 : ℕ)) := by
    simpa only [smul_eq_mul, mul_one] using
      (show surfaceQuotient (seedPoint (57 : ℂ) Complex.I) (MvPolynomial.map seedMap p) ∈
        surfaceGrade (seedPoint (57 : ℂ) Complex.I) n from
          ⟨MvPolynomial.map seedMap p, seedPolynomial_homogeneous hp, rfl⟩)
  change awayMapOfEq (seedCurveGradedMap t) _ _ _
    (Away.map (relativeCurveRingMap incidencePoint t) _
      (Away.mk (surfaceGrade incidencePoint) (coordinate_mem_grade incidencePoint i)
        n (surfaceQuotient incidencePoint p) _)) =
    Away.map (specializedCurveRingMap (seedPoint (57 : ℂ) Complex.I) t) _
      (Away.mk (surfaceGrade (seedPoint (57 : ℂ) Complex.I))
        (coordinate_mem_grade (seedPoint (57 : ℂ) Complex.I) i)
        n (surfaceQuotient (seedPoint (57 : ℂ) Complex.I) (MvPolynomial.map seedMap p)) _)
  have hsource := Away.map_mk (relativeCurveRingMap incidencePoint t)
    (surfaceQuotient incidencePoint (X i.castSucc)) (coordinate_mem_grade incidencePoint i)
      n (surfaceQuotient incidencePoint p) hpSource
  refine (congrArg (awayMapOfEq (seedCurveGradedMap t)
    (relativeCurveRingMap incidencePoint t (surfaceQuotient incidencePoint (X i.castSucc)))
    (specializedCurveRingMap (seedPoint (57 : ℂ) Complex.I) t
      (surfaceQuotient (seedPoint (57 : ℂ) Complex.I) (X i.castSucc)))
    (seedCurveGradedMap_coordinate t i.castSucc)) hsource).trans ?_
  refine (awayMapOfEq_mk (seedCurveGradedMap t)
    (relativeCurveRingMap incidencePoint t (surfaceQuotient incidencePoint (X i.castSucc)))
    (specializedCurveRingMap (seedPoint (57 : ℂ) Complex.I) t
      (surfaceQuotient (seedPoint (57 : ℂ) Complex.I) (X i.castSucc)))
    (seedCurveGradedMap_coordinate t i.castSucc)
    ((relativeCurveRingMap incidencePoint t).2 (coordinate_mem_grade incidencePoint i))
    ((specializedCurveRingMap (seedPoint (57 : ℂ) Complex.I) t).2
      (coordinate_mem_grade (seedPoint (57 : ℂ) Complex.I) i))
    n (relativeCurveRingMap incidencePoint t (surfaceQuotient incidencePoint p))
      ((relativeCurveRingMap incidencePoint t).2 hpSource)).trans ?_
  refine Eq.trans ?_ (Away.map_mk (specializedCurveRingMap (seedPoint (57 : ℂ) Complex.I) t)
    (surfaceQuotient (seedPoint (57 : ℂ) Complex.I) (X i.castSucc))
    (coordinate_mem_grade (seedPoint (57 : ℂ) Complex.I) i)
      n (surfaceQuotient (seedPoint (57 : ℂ) Complex.I) (MvPolynomial.map seedMap p)) hpTarget).symm
  have hnum : seedCurveGradedMap t (relativeCurveRingMap incidencePoint t
        (surfaceQuotient incidencePoint p)) =
      specializedCurveRingMap (seedPoint (57 : ℂ) Complex.I) t
        (surfaceQuotient (seedPoint (57 : ℂ) Complex.I) (MvPolynomial.map seedMap p)) := by
    change seedCurveRingSpecialization t
      (Ideal.Quotient.mk (relativeSectionIdeal incidencePoint t)
        (Ideal.Quotient.mk (pointEquations incidencePoint) p)) = _
    rw [seedCurveRingSpecialization_mk, seedSurfaceSpecialization_mk]
    rfl
  apply HomogeneousLocalization.val_injective
  simp only [Away.val_mk, hnum]

/-- The canonical global graded specialization is the already computed
affine quotient specialization in the exact original chart coordinates. -/
theorem seedCurveCoordinateSpecialization_chart (t : Fin 3 → ℂ) (i : Fin 4)
    (a : CurveCoordinateRing incidencePoint t i) :
    specializedCoordinateChartEquiv (seedPoint (57 : ℂ) Complex.I) t i
        (seedCurveCoordinateSpecialization t i a) =
      curveChartSpecialization t i (curveCoordinateChartEquiv incidencePoint t i a) := by
  obtain ⟨b, rfl⟩ := coordinateCurveMap_surjective incidencePoint t i a
  obtain ⟨n, c, hc, rfl⟩ := Away.mk_surjective (surfaceGrade incidencePoint)
    (coordinate_mem_grade incidencePoint i) b
  obtain ⟨p, hp, rfl⟩ := hc
  have hp' : p.IsWeightedHomogeneous geometricWeight n := by simpa using hp
  change specializedCoordinateChartEquiv (seedPoint (57 : ℂ) Complex.I) t i
      (seedCurveCoordinateSpecialization t i
        (coordinateCurveMap incidencePoint t i
          (homogeneousFraction incidencePoint i n p hp'))) =
    curveChartSpecialization t i (curveCoordinateChartEquiv incidencePoint t i
      (coordinateCurveMap incidencePoint t i (homogeneousFraction incidencePoint i n p hp')))
  simp only [seedCurveCoordinateSpecialization_fraction, specializedCoordinateChartEquiv_map,
    curveCoordinateChartEquiv_map, familyCoordinateChartEquiv_homogeneousFraction,
    curveChartSpecialization_mk, seedChartSpecialization_dehomogenizedPolynomial]

theorem seedCurveToRelative_preimage_coordinatePatch (t : Fin 3 → ℂ) (i : Fin 4) :
    seedCurveToRelative t ⁻¹ᵁ curveCoordinatePatch incidencePoint t i =
      specializedCoordinatePatch (seedPoint (57 : ℂ) Complex.I) t i := by
  rw [curveCoordinatePatch, seedCurveToRelative, Proj.map_preimage_basicOpen]
  erw [seedCurveGradedMap_coordinate]
  rfl

@[reassoc] theorem seedCurveCoordinateSpecialization_awayι (t : Fin 3 → ℂ) (i : Fin 4) :
    Proj.awayι (specializedCurveGrade (seedPoint (57 : ℂ) Complex.I) t)
        (specializedCurveRingMap (seedPoint (57 : ℂ) Complex.I) t
          (surfaceQuotient (seedPoint (57 : ℂ) Complex.I) (X i.castSucc)))
        ((specializedCurveRingMap (seedPoint (57 : ℂ) Complex.I) t).2
          (coordinate_mem_grade (seedPoint (57 : ℂ) Complex.I) i)) (by decide) ≫
      seedCurveToRelative t =
        Spec.map (CommRingCat.ofHom (seedCurveCoordinateSpecialization t i)) ≫
          Proj.awayι (relativeCurveGrade incidencePoint t)
            (relativeCurveRingMap incidencePoint t (surfaceQuotient incidencePoint (X i.castSucc)))
            ((relativeCurveRingMap incidencePoint t).2 (coordinate_mem_grade incidencePoint i))
            (by decide) :=
  awayι_comp_map_of_eq (seedCurveGradedMap t) (irrelevant_le_map_seedCurveGradedMap t)
    _ _ (seedCurveGradedMap_coordinate t i.castSucc) (by decide : 0 < (1 : ℕ))
    ((relativeCurveRingMap incidencePoint t).2 (coordinate_mem_grade incidencePoint i))
    ((specializedCurveRingMap (seedPoint (57 : ℂ) Complex.I) t).2
      (coordinate_mem_grade (seedPoint (57 : ℂ) Complex.I) i))

/-- The one global Proj map restricts to the exact chart specialization
used in projectiveCurveChartSeedFiberIso. -/
@[reassoc] theorem seedCurveToRelative_on_coordinateChart (t : Fin 3 → ℂ) (i : Fin 4) :
    (specializedCoordinateAffineChart (seedPoint (57 : ℂ) Complex.I) t i).inv ≫
        (specializedCoordinatePatch (seedPoint (57 : ℂ) Complex.I) t i).ι ≫
          seedCurveToRelative t =
      Spec.map (CommRingCat.ofHom (curveChartSpecialization t i)) ≫
        (curveCoordinateAffineChart incidencePoint t i).inv ≫
          (curveCoordinatePatch incidencePoint t i).ι := by
  have hspec :
      Spec.map (CommRingCat.ofHom
          (specializedCoordinateChartEquiv (seedPoint (57 : ℂ) Complex.I) t i).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (seedCurveCoordinateSpecialization t i)) =
      Spec.map (CommRingCat.ofHom (curveChartSpecialization t i)) ≫
        Spec.map (CommRingCat.ofHom (curveCoordinateChartEquiv incidencePoint t i).toRingHom) := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    exact seedCurveCoordinateSpecialization_chart t i a
  change (Spec.map (CommRingCat.ofHom
        (specializedCoordinateChartEquiv (seedPoint (57 : ℂ) Complex.I) t i).toRingHom) ≫
      (Proj.basicOpenIsoSpec (specializedCurveGrade (seedPoint (57 : ℂ) Complex.I) t)
        (specializedCurveRingMap (seedPoint (57 : ℂ) Complex.I) t
          (surfaceQuotient (seedPoint (57 : ℂ) Complex.I) (X i.castSucc)))
        ((specializedCurveRingMap (seedPoint (57 : ℂ) Complex.I) t).2
          (coordinate_mem_grade (seedPoint (57 : ℂ) Complex.I) i)) (by decide)).inv) ≫
      (specializedCoordinatePatch (seedPoint (57 : ℂ) Complex.I) t i).ι ≫
        seedCurveToRelative t =
    Spec.map (CommRingCat.ofHom (curveChartSpecialization t i)) ≫
      (Spec.map (CommRingCat.ofHom (curveCoordinateChartEquiv incidencePoint t i).toRingHom) ≫
        (Proj.basicOpenIsoSpec (relativeCurveGrade incidencePoint t)
          (relativeCurveRingMap incidencePoint t (surfaceQuotient incidencePoint (X i.castSucc)))
          ((relativeCurveRingMap incidencePoint t).2 (coordinate_mem_grade incidencePoint i))
          (by decide)).inv) ≫ (curveCoordinatePatch incidencePoint t i).ι
  dsimp only [specializedCoordinatePatch, curveCoordinatePatch]
  simp only [Category.assoc, Proj.basicOpenIsoSpec_inv_ι_assoc,
    Proj.basicOpenIsoSpec_inv_ι]
  rw [seedCurveCoordinateSpecialization_awayι t i]
  have h := congrArg
    (fun f : Spec (CommRingCat.of (AffineCurveChart (seedPoint (57 : ℂ) Complex.I) t i)) ⟶
      Spec (CommRingCat.of (CurveCoordinateRing incidencePoint t i)) =>
        f ≫ Proj.awayι (relativeCurveGrade incidencePoint t)
          (relativeCurveRingMap incidencePoint t (surfaceQuotient incidencePoint (X i.castSucc)))
          ((relativeCurveRingMap incidencePoint t).2 (coordinate_mem_grade incidencePoint i))
          (by decide)) hspec
  simpa only [Category.assoc] using h

#print axioms seedCurveCoordinateSpecialization_fraction
#print axioms seedCurveCoordinateSpecialization_chart
#print axioms seedCurveToRelative_preimage_coordinatePatch
#print axioms seedCurveToRelative_on_coordinateChart

end CycleQ2RelativeCurveSeedChart
end
