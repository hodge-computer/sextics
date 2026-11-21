import Proposal.GeometricRelativeCurveSeedMap
import Proposal.GeometricIncidenceChartFiberScheme

/-!
# The canonical map from the existing seed curve to the actual scheme fiber

The canonical graded coefficient specialization gives a single global
Proj morphism from the existing literal specialized curve to the relative
curve. Its surface square and original coefficient-base square commute.
It therefore factors canonically through the actual scheme pullback at
the retained seed parameter.

This constructs and binds the global morphism. Its being an isomorphism
requires the subsequent comparison on a covering by actual coordinate
opens; it is not inferred from the separate chart isomorphisms here.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md for
attribution of the geometric route and the protected certificate gap.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2RelativeCurveSeedProj

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomogeneousLocalization
open CycleQ2IncidenceNormalForm CycleQ2IncidenceImageLine CycleQ2GeometricIncidenceProj
  CycleQ2IncidenceEtaleParameter CycleQ2IncidencePolynomialJacobianBinding
  CycleQ2IncidenceChartFiberScheme CycleQ2RelativeConstantCurve
  CycleQ2RelativeConstantCurveFiber CycleQ2RelativeCurveSeedMap
  CycleQ2SpecializedProjectiveCurve

local instance incidenceSurfaceCommRing : CommRing (PointSurface incidencePoint) := inferInstance
local instance seedSurfaceCommRing : CommRing (PointSurface (seedPoint (57 : ℂ) Complex.I)) :=
  inferInstance

def seedSurfaceToIncidence :
    surface (seedPoint (57 : ℂ) Complex.I) ⟶ surface incidencePoint :=
  Proj.map seedSurfaceGradedMap irrelevant_le_map_seedSurfaceGradedMap

private theorem seedSurfaceAway_coefficient (s : PointSurface incidencePoint)
    (a : ParameterAlgebra) :
    Away.map seedSurfaceGradedMap s
        (fromZeroRingHom (surfaceGrade incidencePoint) (Submonoid.powers s)
          (surfaceCoefficient incidencePoint a)) =
      fromZeroRingHom (surfaceGrade (seedPoint (57 : ℂ) Complex.I))
        (Submonoid.powers (seedSurfaceGradedMap s))
        (surfaceCoefficient (seedPoint (57 : ℂ) Complex.I) (seedMap a)) := by
  apply HomogeneousLocalization.val_injective
  change (HomogeneousLocalization.map seedSurfaceGradedMap _
    (HomogeneousLocalization.mk ⟨0, surfaceCoefficient incidencePoint a, 1, one_mem _⟩)).val =
      (HomogeneousLocalization.mk ⟨0,
        surfaceCoefficient (seedPoint (57 : ℂ) Complex.I) (seedMap a), 1, one_mem _⟩).val
  rw [HomogeneousLocalization.map_mk]
  have hcoeff : seedSurfaceGradedMap
      (algebraMap ParameterAlgebra (PointSurface incidencePoint) a) =
        algebraMap ℂ (PointSurface (seedPoint (57 : ℂ) Complex.I)) (seedMap a) :=
    seedSurfaceSpecialization_coefficient a
  have hone : seedSurfaceGradedMap
      ((1 : surfaceGrade incidencePoint 0) : PointSurface incidencePoint) =
        ((1 : surfaceGrade (seedPoint (57 : ℂ) Complex.I) 0) :
          PointSurface (seedPoint (57 : ℂ) Complex.I)) := by
    change seedSurfaceGradedMap (1 : PointSurface incidencePoint) = 1
    exact map_one seedSurfaceGradedMap
  simp only [HomogeneousLocalization.val_mk, surfaceCoefficient_val,
    hcoeff, hone]

/-- The Proj specialization is over the original retained seed map. -/
theorem seedSurfaceToIncidence_overBase :
    seedSurfaceToIncidence ≫ surfaceToBase incidencePoint =
      surfaceToBase (seedPoint (57 : ℂ) Complex.I) ≫ seedParameterMorphism := by
  refine (Proj.mapAffineOpenCover seedSurfaceGradedMap
    irrelevant_le_map_seedSurfaceGradedMap).openCover.hom_ext _ _ fun s => ?_
  simp only [Scheme.AffineOpenCover.openCover_f, Proj.mapAffineOpenCover_f,
    seedSurfaceToIncidence, surfaceToBase, Category.assoc, seedParameterMorphism]
  erw [Proj.awayι_comp_map_assoc seedSurfaceGradedMap
    irrelevant_le_map_seedSurfaceGradedMap s.1.2
      (s.2 : PointSurface incidencePoint) s.2.2]
  simp only [Category.assoc, Proj.awayι_toSpecZero_assoc,
    ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  exact seedSurfaceAway_coefficient (s.2 : PointSurface incidencePoint) a

def seedCurveToRelative (t : Fin 3 → ℂ) :
    specializedCurve (seedPoint (57 : ℂ) Complex.I) t ⟶ relativeCurve incidencePoint t :=
  Proj.map (seedCurveGradedMap t) (irrelevant_le_map_seedCurveGradedMap t)

theorem seedCurveToRelative_surface_square (t : Fin 3 → ℂ) :
    seedCurveToRelative t ≫ relativeCurveToSurface incidencePoint t =
      specializedCurveToSurface (seedPoint (57 : ℂ) Complex.I) t ≫ seedSurfaceToIncidence := by
  rw [seedCurveToRelative, relativeCurveToSurface, specializedCurveToSurface,
    seedSurfaceToIncidence, ← Proj.map_comp, ← Proj.map_comp]
  simp only [seedCurveGradedMap_surface_square]

theorem seedCurveToRelative_overBase (t : Fin 3 → ℂ) :
    seedCurveToRelative t ≫ relativeCurveToBase incidencePoint t =
      specializedCurveToBase (seedPoint (57 : ℂ) Complex.I) t ≫ seedParameterMorphism := by
  rw [relativeCurveToBase, ← Category.assoc, seedCurveToRelative_surface_square,
    Category.assoc, seedSurfaceToIncidence_overBase]
  simp only [specializedCurveToBase, Category.assoc]

abbrev RelativeCurveSchemeSeedFiber (t : Fin 3 → ℂ) :=
  pullback seedParameterMorphism (relativeCurveToBase incidencePoint t)

/-- One canonical morphism from the existing specialized seed curve to
the actual scheme-theoretic fiber of the original relative curve. -/
def seedCurveToFiber (t : Fin 3 → ℂ) :
    specializedCurve (seedPoint (57 : ℂ) Complex.I) t ⟶ RelativeCurveSchemeSeedFiber t :=
  pullback.lift (specializedCurveToBase (seedPoint (57 : ℂ) Complex.I) t)
    (seedCurveToRelative t) (seedCurveToRelative_overBase t).symm

@[reassoc, simp] theorem seedCurveToFiber_fst (t : Fin 3 → ℂ) :
    seedCurveToFiber t ≫ pullback.fst seedParameterMorphism (relativeCurveToBase incidencePoint t) =
      specializedCurveToBase (seedPoint (57 : ℂ) Complex.I) t := by
  simp [seedCurveToFiber]

@[reassoc, simp] theorem seedCurveToFiber_snd (t : Fin 3 → ℂ) :
    seedCurveToFiber t ≫ pullback.snd seedParameterMorphism (relativeCurveToBase incidencePoint t) =
      seedCurveToRelative t := by
  simp [seedCurveToFiber]

#print axioms seedSurfaceToIncidence_overBase
#print axioms seedCurveToRelative_surface_square
#print axioms seedCurveToRelative_overBase
#print axioms seedCurveToFiber

end CycleQ2RelativeCurveSeedProj
end
