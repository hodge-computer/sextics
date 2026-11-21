import Proposal.GeometricIncidenceChartMinor
import Mathlib.RingTheory.Localization.Basic

/-!
# Localized split maps for the actual incidence chart minor patches

Status: source-only proof draft. No elaboration or kernel replay was run.

Write A for the actual surface cone ring, x for the chosen weight-one
coordinate, d for the original cone minor, and D for its actual affine
chart ring. The normalized minor in D is denoted dbar.

We construct explicit S-algebra maps
  D[dbar^-1] → A[d^-1][x^-1] → D[dbar^-1]
whose composite is the identity. The section extends because the
normalization identity sends dbar to d times an inverse power of x.

This component establishes the actual maps and retract law only.
Smoothness and finite presentation are supplied separately.

The geometric strategy is due to Ben Diamond and the collaborators cited
in solution.md. Prepared for fqlx with OpenAI ChatGPT assistance.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2IncidenceLocalizedChart

open MvPolynomial
open CycleQ2IncidenceUniversalChart CycleQ2IncidenceImageLine
  CycleQ2IncidenceDehomogenizedChart CycleQ2IncidenceChartMinor

variable {S : Type} [CommRing S] [Algebra ℂ S]
variable (y : ParameterIndex → S) (i : Fin 4) (j k : Fin 5)

abbrev ConeMinorRing :=
  Localization.Away (surfaceQuotient y (surfaceMinor y j k))

def coordinateInConeMinor : ConeMinorRing y j k :=
  algebraMap (PointSurface y) (ConeMinorRing y j k)
    (surfaceQuotient y (X i.castSucc))

abbrev DoubleConeRing :=
  Localization.Away (coordinateInConeMinor y i j k)

abbrev LocalizedChartRing :=
  Localization.Away (normalizedMinor y i j k)

def baseToChartAway :
    PointSurface y →ₐ[S] LocalizedChartRing y i j k :=
  (IsScalarTower.toAlgHom S (DehomogenizedRing y i) (LocalizedChartRing y i j k)).comp
    (surfaceToDehomogenizedAlgHom y i)

@[simp] theorem baseToChartAway_minor :
    baseToChartAway y i j k (surfaceQuotient y (surfaceMinor y j k)) =
      algebraMap (DehomogenizedRing y i) (LocalizedChartRing y i j k)
        (normalizedMinor y i j k) := rfl

@[simp] theorem baseToChartAway_coordinate :
    baseToChartAway y i j k (surfaceQuotient y (X i.castSucc)) = 1 := by
  change algebraMap (DehomogenizedRing y i) (LocalizedChartRing y i j k)
    (surfaceToDehomogenized y i (surfaceQuotient y (X i.castSucc))) = 1
  rw [surfaceToDehomogenized_self, map_one]

def coneMinorToChartAway :
    ConeMinorRing y j k →ₐ[S] LocalizedChartRing y i j k :=
  IsLocalization.Away.liftAlgHom
    (S := ConeMinorRing y j k) (f := baseToChartAway y i j k)
    (surfaceQuotient y (surfaceMinor y j k)) (by
      rw [baseToChartAway_minor]
      exact IsLocalization.Away.algebraMap_isUnit _)

@[simp] theorem coneMinorToChartAway_surface (a : PointSurface y) :
    coneMinorToChartAway y i j k (algebraMap (PointSurface y) (ConeMinorRing y j k) a) =
      baseToChartAway y i j k a := by
  simp [coneMinorToChartAway]

@[simp] theorem coneMinorToChartAway_coordinate :
    coneMinorToChartAway y i j k (coordinateInConeMinor y i j k) = 1 := by
  rw [coordinateInConeMinor, coneMinorToChartAway_surface, baseToChartAway_coordinate]

/-- First invert the original cone minor, then the chosen coordinate. -/
def localizedRetraction :
    DoubleConeRing y i j k →ₐ[S] LocalizedChartRing y i j k :=
  IsLocalization.Away.liftAlgHom
    (S := DoubleConeRing y i j k) (f := coneMinorToChartAway y i j k)
    (coordinateInConeMinor y i j k) (by
      rw [coneMinorToChartAway_coordinate]
      exact isUnit_one)

@[simp] theorem localizedRetraction_cone (a : ConeMinorRing y j k) :
    localizedRetraction y i j k
        (algebraMap (ConeMinorRing y j k) (DoubleConeRing y i j k) a) =
      coneMinorToChartAway y i j k a := by
  simp [localizedRetraction]

@[simp] theorem localizedRetraction_surface (a : PointSurface y) :
    localizedRetraction y i j k
        (algebraMap (PointSurface y) (DoubleConeRing y i j k) a) =
      baseToChartAway y i j k a := by
  rw [IsScalarTower.algebraMap_apply (PointSurface y) (ConeMinorRing y j k)
    (DoubleConeRing y i j k), localizedRetraction_cone, coneMinorToChartAway_surface]

theorem coordinate_isUnit :
    IsUnit (algebraMap (PointSurface y) (DoubleConeRing y i j k)
      (surfaceQuotient y (X i.castSucc))) := by
  rw [IsScalarTower.algebraMap_apply (PointSurface y) (ConeMinorRing y j k)
    (DoubleConeRing y i j k)]
  exact IsLocalization.Away.algebraMap_isUnit (coordinateInConeMinor y i j k)

def coordinateToDouble :
    CoordinateLocalization y i →ₐ[S] DoubleConeRing y i j k :=
  IsLocalization.Away.liftAlgHom
    (S := CoordinateLocalization y i)
    (f := IsScalarTower.toAlgHom S (PointSurface y) (DoubleConeRing y i j k))
    (surfaceQuotient y (X i.castSucc)) (coordinate_isUnit y i j k)

@[simp] theorem coordinateToDouble_surface (a : PointSurface y) :
    coordinateToDouble y i j k
        (algebraMap (PointSurface y) (CoordinateLocalization y i) a) =
      algebraMap (PointSurface y) (DoubleConeRing y i j k) a := by
  simp [coordinateToDouble]

def chartToDouble :
    DehomogenizedRing y i →ₐ[S] DoubleConeRing y i j k :=
  (coordinateToDouble y i j k).comp (dehomogenizedSection y i)

theorem chartToDouble_minor_isUnit :
    IsUnit (chartToDouble y i j k (normalizedMinor y i j k)) := by
  change IsUnit (coordinateToDouble y i j k
    (dehomogenizedSection y i (normalizedMinor y i j k)))
  rw [dehomogenizedSection_normalizedMinor, map_mul, map_pow]
  apply IsUnit.mul
  · rw [coordinateToDouble_surface,
      IsScalarTower.algebraMap_apply (PointSurface y) (ConeMinorRing y j k)
        (DoubleConeRing y i j k)]
    exact IsUnit.map (algebraMap (ConeMinorRing y j k) (DoubleConeRing y i j k))
      (IsLocalization.Away.algebraMap_isUnit (surfaceQuotient y (surfaceMinor y j k)))
  · have hu : IsUnit
        (IsLocalization.Away.invSelf (surfaceQuotient y (X i.castSucc)) :
          CoordinateLocalization y i) := by
      apply isUnit_iff_exists_inv.mpr
      refine ⟨algebraMap (PointSurface y) (CoordinateLocalization y i)
        (surfaceQuotient y (X i.castSucc)), ?_⟩
      rw [mul_comm]
      exact IsLocalization.Away.mul_invSelf _
    exact (IsUnit.map (coordinateToDouble y i j k).toRingHom hu).pow _

/-- The actual chart section extends after its normalized minor is inverted. -/
def localizedSection :
    LocalizedChartRing y i j k →ₐ[S] DoubleConeRing y i j k :=
  IsLocalization.Away.liftAlgHom
    (S := LocalizedChartRing y i j k) (f := chartToDouble y i j k)
    (normalizedMinor y i j k) (chartToDouble_minor_isUnit y i j k)

@[simp] theorem localizedSection_chart (a : DehomogenizedRing y i) :
    localizedSection y i j k
        (algebraMap (DehomogenizedRing y i) (LocalizedChartRing y i j k) a) =
      chartToDouble y i j k a := by
  simp [localizedSection]

@[simp] theorem dehomogenizedRetraction_surface (a : PointSurface y) :
    dehomogenizedRetraction y i
        (algebraMap (PointSurface y) (CoordinateLocalization y i) a) =
      surfaceToDehomogenized y i a := by
  simp [dehomogenizedRetraction, surfaceToDehomogenizedAlgHom]

theorem localizedRetraction_coordinateToDouble :
    (localizedRetraction y i j k).comp (coordinateToDouble y i j k) =
      (IsScalarTower.toAlgHom S (DehomogenizedRing y i)
        (LocalizedChartRing y i j k)).comp (dehomogenizedRetraction y i) := by
  apply IsLocalization.algHom_ext (Submonoid.powers (surfaceQuotient y (X i.castSucc)))
  apply AlgHom.ext
  intro a
  change localizedRetraction y i j k
      (coordinateToDouble y i j k
        (algebraMap (PointSurface y) (CoordinateLocalization y i) a)) =
    algebraMap (DehomogenizedRing y i) (LocalizedChartRing y i j k)
      (dehomogenizedRetraction y i
        (algebraMap (PointSurface y) (CoordinateLocalization y i) a))
  rw [coordinateToDouble_surface, localizedRetraction_surface,
    dehomogenizedRetraction_surface]
  rfl

@[simp] theorem localizedRetraction_chartToDouble (a : DehomogenizedRing y i) :
    localizedRetraction y i j k (chartToDouble y i j k a) =
      algebraMap (DehomogenizedRing y i) (LocalizedChartRing y i j k) a := by
  have h := AlgHom.congr_fun (localizedRetraction_coordinateToDouble y i j k)
    (dehomogenizedSection y i a)
  change localizedRetraction y i j k (chartToDouble y i j k a) =
    algebraMap (DehomogenizedRing y i) (LocalizedChartRing y i j k)
      (dehomogenizedRetraction y i (dehomogenizedSection y i a)) at h
  simpa only [dehomogenizedRetraction_section] using h

theorem localizedRetraction_comp_section :
    (localizedRetraction y i j k).comp (localizedSection y i j k) =
      AlgHom.id S (LocalizedChartRing y i j k) := by
  apply IsLocalization.algHom_ext (Submonoid.powers (normalizedMinor y i j k))
  apply AlgHom.ext
  intro a
  change localizedRetraction y i j k
    (localizedSection y i j k
      (algebraMap (DehomogenizedRing y i) (LocalizedChartRing y i j k) a)) =
    algebraMap (DehomogenizedRing y i) (LocalizedChartRing y i j k) a
  rw [localizedSection_chart, localizedRetraction_chartToDouble]

theorem localizedRetraction_section (a : LocalizedChartRing y i j k) :
    localizedRetraction y i j k (localizedSection y i j k a) = a :=
  AlgHom.congr_fun (localizedRetraction_comp_section y i j k) a

end CycleQ2IncidenceLocalizedChart

end

#print axioms CycleQ2IncidenceLocalizedChart.chartToDouble_minor_isUnit
#print axioms CycleQ2IncidenceLocalizedChart.localizedRetraction_comp_section
#print axioms CycleQ2IncidenceLocalizedChart.localizedRetraction_section

