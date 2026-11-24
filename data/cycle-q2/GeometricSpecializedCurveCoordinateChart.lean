import Proposal.GeometricRelativeCurveChart
import Proposal.GeometricSpecializedProjectiveCurve

/-!
# Coordinate charts of the existing specialized projective curve

The existing complex specialized curve has the same three-row ideal as
the relative constant-section construction at that complex point. This
file identifies its actual weight-one Away rings and open subschemes
with the explicit affine quotient already used in the relative fiber
calculation. The target remains the existing SpecializedCurveRing and
specializedCurve, rather than a replacement projective scheme.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md for
attribution of the geometric route and the protected certificate gap.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2SpecializedCurveCoordinateChart

open CategoryTheory AlgebraicGeometry MvPolynomial HomogeneousLocalization
open CycleQ2IncidenceUniversalChart CycleQ2IncidenceImageLine
  CycleQ2GeometricIncidenceProj CycleQ2IncidenceDehomogenizedChart
  CycleQ2RelativeConstantSection CycleQ2RelativeCurveChart
  CycleQ2GradedIdealContraction CycleQ2SpecializedSectionIdeal
  CycleQ2SpecializedProjectiveCurve

variable (y : ParameterIndex → ℂ) (t : Fin 3 → ℂ) (i : Fin 4)

local instance pointSurfaceCommRing : CommRing (PointSurface y) := inferInstance
local instance specializedCurveCommRing : CommRing (SpecializedCurveRing y t) := inferInstance
local instance coordinateRingCommRing : CommRing (CoordinateRing y i) := inferInstance
local instance affineCurveChartCommRing : CommRing (AffineCurveChart y t i) := inferInstance

theorem relativeSectionIdeal_eq_specialized :
    relativeSectionIdeal y t = specializedSectionIdeal y t := by
  unfold relativeSectionIdeal specializedSectionIdeal
  apply congrArg (fun g : Fin 3 → PointSurface y => Ideal.span (Set.range g))
  funext j
  exact relativeEquation_complex y t j

abbrev SpecializedCoordinateRing :=
  Away (specializedCurveGrade y t)
    (specializedCurveRingMap y t (surfaceQuotient y (X i.castSucc)))

local instance specializedCoordinateCommRing :
    CommRing (SpecializedCoordinateRing y t i) := inferInstance

instance specializedCoordinateAlgebra : Algebra ℂ (SpecializedCoordinateRing y t i) :=
  ((Away.map (specializedCurveRingMap y t) (surfaceQuotient y (X i.castSucc))).comp
    (algebraMap ℂ (CoordinateRing y i))).toAlgebra

def specializedCoordinateMap : CoordinateRing y i →ₐ[ℂ] SpecializedCoordinateRing y t i where
  toRingHom := Away.map (specializedCurveRingMap y t) (surfaceQuotient y (X i.castSucc))
  commutes' _ := rfl

theorem specializedCoordinateMap_surjective :
    Function.Surjective (specializedCoordinateMap y t i) := by
  intro z
  obtain ⟨n, b, hb, rfl⟩ := Away.mk_surjective (specializedCurveGrade y t)
    ((specializedCurveRingMap y t).2 (coordinate_mem_grade y i)) z
  obtain ⟨a, ha, rfl⟩ := hb
  refine ⟨Away.mk (surfaceGrade y) (coordinate_mem_grade y i) n a ha, ?_⟩
  change Away.map (specializedCurveRingMap y t) (surfaceQuotient y (X i.castSucc))
    (Away.mk (surfaceGrade y) (coordinate_mem_grade y i) n a ha) = _
  simp only [Away.map_mk]
  rfl

theorem specializedCoordinateMap_ker :
    RingHom.ker (specializedCoordinateMap y t i) = normalizedSectionIdeal y t i := by
  change RingHom.ker (Away.map (specializedCurveRingMap y t)
    (surfaceQuotient y (X i.castSucc))) = _
  rw [CycleQ2UniversalCurveCartier.gradedAwayMap_ker (surfaceGrade y)
    (specializedCurveGrade y t) (specializedCurveRingMap y t)
    (surfaceQuotient y (X i.castSucc)) (coordinate_mem_grade y i),
    specializedCurveRingMap_ker, ← relativeSectionIdeal_eq_specialized,
    relativeSectionIdeal_localize_coordinate,
    ideal_map_comap_val (surfaceGrade y) (coordinate_mem_grade y i)]

def specializedCoordinateQuotientEquiv :
    (CoordinateRing y i ⧸ normalizedSectionIdeal y t i) ≃ₐ[ℂ]
      SpecializedCoordinateRing y t i :=
  (Ideal.quotientEquivAlgOfEq ℂ (specializedCoordinateMap_ker y t i).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (f := specializedCoordinateMap y t i)
      (specializedCoordinateMap_surjective y t i))

@[simp] theorem specializedCoordinateQuotientEquiv_mk (a : CoordinateRing y i) :
    specializedCoordinateQuotientEquiv y t i
        (Ideal.Quotient.mk (normalizedSectionIdeal y t i) a) =
      specializedCoordinateMap y t i a := by
  rw [specializedCoordinateQuotientEquiv, AlgEquiv.trans_apply,
    Ideal.quotientEquivAlgOfEq_mk, Ideal.quotientKerAlgEquivOfSurjective_mk]

def specializedCoordinateChartEquiv :
    SpecializedCoordinateRing y t i ≃ₐ[ℂ] AffineCurveChart y t i :=
  (specializedCoordinateQuotientEquiv y t i).symm.trans
    (Ideal.quotientEquivAlg (normalizedSectionIdeal y t i) (affineSectionIdeal y t i)
      (familyCoordinateChartEquiv y i) (normalizedSectionIdeal_map y t i).symm)

@[simp] theorem specializedCoordinateChartEquiv_map (a : CoordinateRing y i) :
    specializedCoordinateChartEquiv y t i (specializedCoordinateMap y t i a) =
      Ideal.Quotient.mk (affineSectionIdeal y t i) (familyCoordinateChartEquiv y i a) := by
  rw [← specializedCoordinateQuotientEquiv_mk y t i a,
    specializedCoordinateChartEquiv, AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply,
    Ideal.quotientEquivAlg_mk]

def specializedCoordinatePatch : (specializedCurve y t).Opens :=
  Proj.basicOpen (specializedCurveGrade y t)
    (specializedCurveRingMap y t (surfaceQuotient y (X i.castSucc)))

theorem specializedCoordinatePatch_eq_preimage :
    specializedCoordinatePatch y t i =
      specializedCurveToSurface y t ⁻¹ᵁ familyCoordinatePatch y i :=
  (specializedCurveToSurface_preimage_basicOpen y t
    (surfaceQuotient y (X i.castSucc))).symm

theorem specializedCoordinatePatch_isAffineOpen :
    IsAffineOpen (specializedCoordinatePatch y t i) :=
  Proj.isAffineOpen_basicOpen (specializedCurveGrade y t)
    (specializedCurveRingMap y t (surfaceQuotient y (X i.castSucc)))
    ((specializedCurveRingMap y t).2 (coordinate_mem_grade y i)) (by decide)

def specializedCoordinateAffineChart :
    (specializedCoordinatePatch y t i).toScheme ≅
      Spec (CommRingCat.of (AffineCurveChart y t i)) :=
  Proj.basicOpenIsoSpec (specializedCurveGrade y t)
      (specializedCurveRingMap y t (surfaceQuotient y (X i.castSucc)))
      ((specializedCurveRingMap y t).2 (coordinate_mem_grade y i)) (by decide) ≪≫
    Scheme.Spec.mapIso
      (specializedCoordinateChartEquiv y t i).toRingEquiv.toCommRingCatIso.symm.op

theorem specializedAwayToBase :
    Proj.awayι (specializedCurveGrade y t)
        (specializedCurveRingMap y t (surfaceQuotient y (X i.castSucc)))
        ((specializedCurveRingMap y t).2 (coordinate_mem_grade y i)) (by decide) ≫
      specializedCurveToBase y t =
        Spec.map (CommRingCat.ofHom (algebraMap ℂ (SpecializedCoordinateRing y t i))) := by
  rw [specializedCurveToBase, specializedCurveToSurface, ← Category.assoc]
  have hcomm := Proj.awayι_comp_map (specializedCurveRingMap y t)
    (irrelevant_le_map_specializedCurveRingMap y t) (by decide : 0 < (1 : ℕ))
    (surfaceQuotient y (X i.castSucc)) (coordinate_mem_grade y i)
  rw [hcomm, Category.assoc, awayι_surfaceToBase, ← Spec.map_comp]
  rfl

theorem specializedCoordinateAffineChart_overBase :
    (specializedCoordinateAffineChart y t i).inv ≫
        (specializedCoordinatePatch y t i).ι ≫ specializedCurveToBase y t =
      Spec.map (CommRingCat.ofHom (algebraMap ℂ (AffineCurveChart y t i))) := by
  change (Spec.map (CommRingCat.ofHom (specializedCoordinateChartEquiv y t i).toRingHom) ≫
      (Proj.basicOpenIsoSpec (specializedCurveGrade y t)
        (specializedCurveRingMap y t (surfaceQuotient y (X i.castSucc)))
        ((specializedCurveRingMap y t).2 (coordinate_mem_grade y i)) (by decide)).inv) ≫
      (specializedCoordinatePatch y t i).ι ≫ specializedCurveToBase y t = _
  dsimp only [specializedCoordinatePatch]
  rw [Category.assoc, Proj.basicOpenIsoSpec_inv_ι_assoc,
    specializedAwayToBase, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro c
  exact (specializedCoordinateChartEquiv y t i).commutes c

#print axioms relativeSectionIdeal_eq_specialized
#print axioms specializedCoordinateMap_ker
#print axioms specializedCoordinateChartEquiv
#print axioms specializedCoordinateAffineChart_overBase

end CycleQ2SpecializedCurveCoordinateChart
end
