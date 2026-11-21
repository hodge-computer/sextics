import Proposal.GeometricRelativeCurveChart

/-!
# Actual projective curve charts over the original coefficient base

The degree-zero quotient chart equivalence is promoted to a scheme
isomorphism for the actual coordinate open of the relative curve. The
structure morphism is the original closed immersion followed by the
original surface structure morphism. Its affine expression is proved
to be the canonical coefficient map of the displayed chart quotient.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md for
attribution of the geometric route and the protected certificate gap.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2RelativeCurveChartScheme

open CategoryTheory AlgebraicGeometry MvPolynomial
open CycleQ2IncidenceUniversalChart CycleQ2IncidenceImageLine CycleQ2GeometricIncidenceProj
  CycleQ2IncidenceDehomogenizedChart CycleQ2RelativeConstantCurve
  CycleQ2RelativeCurveChart

variable {S : Type} [CommRing S] [Algebra ℂ S]
variable (y : ParameterIndex → S) (t : Fin 3 → ℂ) (i : Fin 4)

local instance relativeCurveCommRing :
    CommRing (CycleQ2RelativeConstantSection.RelativeCurveRing y t) := inferInstance
local instance curveCoordinateCommRing : CommRing (CurveCoordinateRing y t i) := inferInstance
local instance affineCurveChartCommRing : CommRing (AffineCurveChart y t i) := inferInstance

def curveCoordinatePatch : (relativeCurve y t).Opens :=
  Proj.basicOpen (relativeCurveGrade y t)
    (relativeCurveRingMap y t (surfaceQuotient y (X i.castSucc)))

theorem curveCoordinatePatch_eq_preimage :
    curveCoordinatePatch y t i =
      relativeCurveToSurface y t ⁻¹ᵁ familyCoordinatePatch y i :=
  (relativeCurveToSurface_preimage_basicOpen y t
    (surfaceQuotient y (X i.castSucc))).symm

theorem curveCoordinatePatch_isAffineOpen : IsAffineOpen (curveCoordinatePatch y t i) :=
  Proj.isAffineOpen_basicOpen (relativeCurveGrade y t)
    (relativeCurveRingMap y t (surfaceQuotient y (X i.castSucc)))
    ((relativeCurveRingMap y t).2 (coordinate_mem_grade y i)) (by decide)

/-- A scheme isomorphism from the actual coordinate open of the relative
projective zero locus to its exact dehomogenized row quotient. -/
def curveCoordinateAffineChart :
    (curveCoordinatePatch y t i).toScheme ≅ Spec (CommRingCat.of (AffineCurveChart y t i)) :=
  Proj.basicOpenIsoSpec (relativeCurveGrade y t)
      (relativeCurveRingMap y t (surfaceQuotient y (X i.castSucc)))
      ((relativeCurveRingMap y t).2 (coordinate_mem_grade y i)) (by decide) ≪≫
    Scheme.Spec.mapIso (curveCoordinateChartEquiv y t i).toRingEquiv.toCommRingCatIso.symm.op

theorem curveAwayToBase :
    Proj.awayι (relativeCurveGrade y t)
        (relativeCurveRingMap y t (surfaceQuotient y (X i.castSucc)))
        ((relativeCurveRingMap y t).2 (coordinate_mem_grade y i)) (by decide) ≫
      relativeCurveToBase y t =
        Spec.map (CommRingCat.ofHom (R := S) (S := CurveCoordinateRing y t i)
          (algebraMap S (CurveCoordinateRing y t i))) := by
  rw [relativeCurveToBase, relativeCurveToSurface, ← Category.assoc]
  have hcomm := Proj.awayι_comp_map (relativeCurveRingMap y t)
    (irrelevant_le_map_relativeCurveRingMap y t) (by decide : 0 < (1 : ℕ))
    (surfaceQuotient y (X i.castSucc)) (coordinate_mem_grade y i)
  rw [hcomm, Category.assoc, awayι_surfaceToBase, ← Spec.map_comp]
  rfl

/-- The chart equivalence respects the actual original base morphism,
including its canonical coefficient map. -/
theorem curveCoordinateAffineChart_overBase :
    (curveCoordinateAffineChart y t i).inv ≫
        (curveCoordinatePatch y t i).ι ≫ relativeCurveToBase y t =
      Spec.map (CommRingCat.ofHom (R := S) (S := AffineCurveChart y t i)
        (algebraMap S (AffineCurveChart y t i))) := by
  change (Spec.map (CommRingCat.ofHom (curveCoordinateChartEquiv y t i).toRingHom) ≫
      (Proj.basicOpenIsoSpec (relativeCurveGrade y t)
        (relativeCurveRingMap y t (surfaceQuotient y (X i.castSucc)))
        ((relativeCurveRingMap y t).2 (coordinate_mem_grade y i)) (by decide)).inv) ≫
      (curveCoordinatePatch y t i).ι ≫ relativeCurveToBase y t = _
  dsimp only [curveCoordinatePatch]
  rw [Category.assoc, Proj.basicOpenIsoSpec_inv_ι_assoc,
    curveAwayToBase, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro c
  exact (curveCoordinateChartEquiv y t i).commutes c

#print axioms curveCoordinateAffineChart
#print axioms curveAwayToBase
#print axioms curveCoordinateAffineChart_overBase

end CycleQ2RelativeCurveChartScheme
end
