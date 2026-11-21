import Proposal.GeometricRelativeConstantCurve
import Proposal.GeometricRelativeConstantCurveFiber

/-!
# The canonical graded specialization to the existing seed curve

The original seed coefficient map induces graded maps of the original
surface and of the fixed-vector relative curve. The target is the
existing SpecializedCurveRing, with the exact same complex vector.
Every homogeneous element has a homogeneous lift of the same degree:
lift its complex polynomial coefficients through the original algebra
map into ParameterAlgebra. Consequently the target irrelevant ideal is
contained in the image of the original source irrelevant ideal.

These are the canonical ring maps needed to define one global Proj map;
no gluing or projective base-change result is asserted in this file.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md for
attribution of the geometric route and the protected certificate gap.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2RelativeCurveSeedMap

open MvPolynomial
open CycleQ2IncidenceNormalForm CycleQ2IncidenceUniversalChart
  CycleQ2IncidenceImageLine CycleQ2IncidencePolynomialJacobianBinding
  CycleQ2GeometricIncidenceProj CycleQ2IncidenceEtaleParameter
  CycleQ2RegularSeedSection CycleQ2SpecializedSectionIdeal
  CycleQ2SpecializedProjectiveCurve CycleQ2RelativeConstantSection
  CycleQ2RelativeConstantCurve CycleQ2RelativeConstantCurveFiber

local instance incidenceSurfaceCommRing : CommRing (PointSurface incidencePoint) := inferInstance
local instance seedSurfaceCommRing : CommRing (PointSurface (seedPoint (57 : ℂ) Complex.I)) :=
  inferInstance
local instance relativeCurveCommRing (t : Fin 3 → ℂ) :
    CommRing (RelativeCurveRing incidencePoint t) := inferInstance
local instance specializedCurveCommRing (t : Fin 3 → ℂ) :
    CommRing (SpecializedCurveRing (seedPoint (57 : ℂ) Complex.I) t) := inferInstance

private theorem weightedHomogeneous_map {R T : Type} [CommRing R] [CommRing T]
    (f : R →+* T) {p : MvPolynomial (Fin 5) R} {n : ℕ}
    (hp : p.IsWeightedHomogeneous geometricWeight n) :
    (MvPolynomial.map f p).IsWeightedHomogeneous geometricWeight n := by
  intro d hd
  apply hp
  intro hz
  apply hd
  rw [MvPolynomial.coeff_map, hz, map_zero]

theorem seedSurfaceSpecialization_homogeneous {n : ℕ} {a : PointSurface incidencePoint}
    (ha : a ∈ surfaceGrade incidencePoint n) :
    seedSurfaceSpecialization a ∈ surfaceGrade (seedPoint (57 : ℂ) Complex.I) n := by
  obtain ⟨p, hp, rfl⟩ := ha
  change seedSurfaceSpecialization (Ideal.Quotient.mk (pointEquations incidencePoint) p) ∈ _
  rw [seedSurfaceSpecialization_mk]
  exact ⟨MvPolynomial.map seedMap p, weightedHomogeneous_map seedMap hp, rfl⟩

def seedSurfaceGradedMap :
    surfaceGrade incidencePoint →+*ᵍ surfaceGrade (seedPoint (57 : ℂ) Complex.I) where
  toRingHom := seedSurfaceSpecialization
  map_mem := by
    intro n a ha
    exact seedSurfaceSpecialization_homogeneous ha

theorem seedMap_coefficientLift (p : MvPolynomial (Fin 5) ℂ) :
    MvPolynomial.map seedMap
      (MvPolynomial.map (algebraMap ℂ ParameterAlgebra) p) = p := by
  have h : seedMap.comp (algebraMap ℂ ParameterAlgebra) = RingHom.id ℂ := by
    ext c
    exact CycleQ2IncidenceSeedFiber.seedMap_complex c
  rw [MvPolynomial.map_map, h, MvPolynomial.map_id]

/-- Surjectivity is degree-preserving, not merely ungraded. -/
theorem seedSurfaceGradedMap_homogeneous_surjective (n : ℕ)
    (b : PointSurface (seedPoint (57 : ℂ) Complex.I))
    (hb : b ∈ surfaceGrade (seedPoint (57 : ℂ) Complex.I) n) :
    ∃ a : PointSurface incidencePoint,
      a ∈ surfaceGrade incidencePoint n ∧ seedSurfaceGradedMap a = b := by
  obtain ⟨p, hp, rfl⟩ := hb
  refine ⟨Ideal.Quotient.mk (pointEquations incidencePoint)
    (MvPolynomial.map (algebraMap ℂ ParameterAlgebra) p),
    ⟨_, weightedHomogeneous_map (algebraMap ℂ ParameterAlgebra) hp, rfl⟩, ?_⟩
  change seedSurfaceSpecialization (Ideal.Quotient.mk (pointEquations incidencePoint)
    (MvPolynomial.map (algebraMap ℂ ParameterAlgebra) p)) = _
  rw [seedSurfaceSpecialization_mk, seedMap_coefficientLift]
  rfl

theorem irrelevant_le_map_seedSurfaceGradedMap :
    HomogeneousIdeal.irrelevant (surfaceGrade (seedPoint (57 : ℂ) Complex.I)) ≤
      (HomogeneousIdeal.irrelevant (surfaceGrade incidencePoint)).map seedSurfaceGradedMap := by
  apply toIdeal_le_toIdeal_iff.mp
  apply (HomogeneousIdeal.toIdeal_irrelevant_le _).mpr
  intro n hn b hb
  obtain ⟨a, ha, rfl⟩ := seedSurfaceGradedMap_homogeneous_surjective n b hb
  exact Ideal.mem_map_of_mem seedSurfaceGradedMap
    (HomogeneousIdeal.mem_irrelevant_of_mem (surfaceGrade incidencePoint) hn ha)

def seedCurveRingSpecialization (t : Fin 3 → ℂ) :
    RelativeCurveRing incidencePoint t →+*
      SpecializedCurveRing (seedPoint (57 : ℂ) Complex.I) t :=
  Ideal.Quotient.lift (relativeSectionIdeal incidencePoint t)
    ((Ideal.Quotient.mk (specializedSectionIdeal (seedPoint (57 : ℂ) Complex.I) t)).comp
      seedSurfaceSpecialization) (by
        intro a ha
        apply Ideal.Quotient.eq_zero_iff_mem.mpr
        rw [← relativeSectionIdeal_seed t]
        exact Ideal.mem_map_of_mem seedSurfaceSpecialization ha)

@[simp] theorem seedCurveRingSpecialization_mk (t : Fin 3 → ℂ)
    (a : PointSurface incidencePoint) :
    seedCurveRingSpecialization t
        (Ideal.Quotient.mk (relativeSectionIdeal incidencePoint t) a) =
      Ideal.Quotient.mk (specializedSectionIdeal (seedPoint (57 : ℂ) Complex.I) t)
        (seedSurfaceSpecialization a) := rfl

def seedCurveGradedMap (t : Fin 3 → ℂ) :
    relativeCurveGrade incidencePoint t →+*ᵍ
      specializedCurveGrade (seedPoint (57 : ℂ) Complex.I) t where
  toRingHom := seedCurveRingSpecialization t
  map_mem := by
    intro n a ha
    obtain ⟨b, hb, rfl⟩ := ha
    exact ⟨seedSurfaceSpecialization b, seedSurfaceSpecialization_homogeneous hb, rfl⟩

theorem seedCurveGradedMap_homogeneous_surjective (t : Fin 3 → ℂ) (n : ℕ)
    (b : SpecializedCurveRing (seedPoint (57 : ℂ) Complex.I) t)
    (hb : b ∈ specializedCurveGrade (seedPoint (57 : ℂ) Complex.I) t n) :
    ∃ a : RelativeCurveRing incidencePoint t,
      a ∈ relativeCurveGrade incidencePoint t n ∧ seedCurveGradedMap t a = b := by
  obtain ⟨c, hc, rfl⟩ := hb
  obtain ⟨a, ha, hmap⟩ := seedSurfaceGradedMap_homogeneous_surjective n c hc
  refine ⟨Ideal.Quotient.mk (relativeSectionIdeal incidencePoint t) a,
    ⟨a, ha, rfl⟩, ?_⟩
  change Ideal.Quotient.mk (specializedSectionIdeal (seedPoint (57 : ℂ) Complex.I) t)
    (seedSurfaceSpecialization a) = _
  exact congrArg (Ideal.Quotient.mk
    (specializedSectionIdeal (seedPoint (57 : ℂ) Complex.I) t)) hmap

theorem irrelevant_le_map_seedCurveGradedMap (t : Fin 3 → ℂ) :
    HomogeneousIdeal.irrelevant (specializedCurveGrade (seedPoint (57 : ℂ) Complex.I) t) ≤
      (HomogeneousIdeal.irrelevant (relativeCurveGrade incidencePoint t)).map
        (seedCurveGradedMap t) := by
  apply toIdeal_le_toIdeal_iff.mp
  apply (HomogeneousIdeal.toIdeal_irrelevant_le _).mpr
  intro n hn b hb
  obtain ⟨a, ha, rfl⟩ := seedCurveGradedMap_homogeneous_surjective t n b hb
  exact Ideal.mem_map_of_mem (seedCurveGradedMap t)
    (HomogeneousIdeal.mem_irrelevant_of_mem (relativeCurveGrade incidencePoint t) hn ha)

theorem seedCurveGradedMap_surface_square (t : Fin 3 → ℂ) :
    (seedCurveGradedMap t).comp (relativeCurveRingMap incidencePoint t) =
      (specializedCurveRingMap (seedPoint (57 : ℂ) Complex.I) t).comp seedSurfaceGradedMap := by
  ext a
  rfl

@[simp] theorem seedSurfaceSpecialization_coefficient (a : ParameterAlgebra) :
    seedSurfaceSpecialization (algebraMap ParameterAlgebra (PointSurface incidencePoint) a) =
      algebraMap ℂ (PointSurface (seedPoint (57 : ℂ) Complex.I)) (seedMap a) := by
  change seedSurfaceSpecialization (Ideal.Quotient.mk (pointEquations incidencePoint) (C a)) = _
  rw [seedSurfaceSpecialization_mk, MvPolynomial.map_C]
  rfl

@[simp] theorem seedCurveGradedMap_coefficient (t : Fin 3 → ℂ) (a : ParameterAlgebra) :
    seedCurveGradedMap t (algebraMap ParameterAlgebra (RelativeCurveRing incidencePoint t) a) =
      algebraMap ℂ (SpecializedCurveRing (seedPoint (57 : ℂ) Complex.I) t) (seedMap a) := by
  change seedCurveRingSpecialization t
    (Ideal.Quotient.mk (relativeSectionIdeal incidencePoint t)
      (algebraMap ParameterAlgebra (PointSurface incidencePoint) a)) = _
  rw [seedCurveRingSpecialization_mk, seedSurfaceSpecialization_coefficient]
  rfl

@[simp] theorem seedCurveGradedMap_coordinate (t : Fin 3 → ℂ) (j : Fin 5) :
    seedCurveGradedMap t (relativeCurveRingMap incidencePoint t
      (Ideal.Quotient.mk (pointEquations incidencePoint) (X j))) =
      specializedCurveRingMap (seedPoint (57 : ℂ) Complex.I) t
        (Ideal.Quotient.mk (pointEquations (seedPoint (57 : ℂ) Complex.I)) (X j)) := by
  change seedCurveRingSpecialization t
    (Ideal.Quotient.mk (relativeSectionIdeal incidencePoint t)
      (Ideal.Quotient.mk (pointEquations incidencePoint) (X j))) = _
  rw [seedCurveRingSpecialization_mk, seedSurfaceSpecialization_mk, MvPolynomial.map_X]
  rfl

#print axioms seedSurfaceGradedMap_homogeneous_surjective
#print axioms seedCurveGradedMap_homogeneous_surjective
#print axioms irrelevant_le_map_seedCurveGradedMap
#print axioms seedCurveGradedMap_surface_square
#print axioms seedCurveGradedMap_coefficient

end CycleQ2RelativeCurveSeedMap
end
