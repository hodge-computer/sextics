import Proposal.GeometricProjectiveOverlap
import Proposal.GeometricProjectiveFrames

/-!
# The coordinate ratio and the actual degree-one transition unit

The middle coordinate x2/x1 on the coordinate overlap restricts to exactly
the transition unit of the existing twist on the quartic denominator cover.
This identifies the coefficient appearing in the affine cofactor transition
with the coefficient used to glue the actual sheaf of modules.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

noncomputable section

namespace CycleQ2GeometricProjectiveTransition

open MvPolynomial CategoryTheory AlgebraicGeometry
  CycleQ2NormalConnecting CycleQ2GeometricProjectiveCurve
  CycleQ2GeometricProjectiveAffine CycleQ2GeometricProjectiveOverlap
  CycleQ2GeometricAffineOverlap

theorem awayCoordinateRatio_mul_coordinate (r θ : ℂ) (j k : Fin 4)
    {e : ℕ} (g : CurveRing r θ) (hg : g ∈ curveGrade r θ e)
    (x : CurveRing r θ) (hx : x = coordinateDen r θ j * g) :
    (HomogeneousLocalization.awayMap (curveGrade r θ) hg hx
          (coordinateRatio r θ j k)).val *
        algebraMap (CurveRing r θ) (Localization.Away x) (coordinateDen r θ j) =
      algebraMap (CurveRing r θ) (Localization.Away x) (coordinateDen r θ k) := by
  rw [coordinateRatio_eq_awayMk, HomogeneousLocalization.awayMap_mk,
    HomogeneousLocalization.Away.val_mk]
  simp only [pow_one]
  rw [← Localization.mk_one_eq_algebraMap, ← Localization.mk_one_eq_algebraMap,
    Localization.mk_mul, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [Submonoid.coe_one, Subtype.coe_mk, one_mul, mul_one]
  rw [hx]
  ring

def firstToDenominatorOverlap (r θ : ℂ) :
    ProjectiveCoordinateRing r θ 1 →+* OverlapProjectiveRing r θ :=
  HomogeneousLocalization.awayMap (curveGrade r θ)
    (SetLike.mul_mem_graded (firstFrameComplement_grade r θ) (curveG2_mem_grade r θ))
    (overlapFirstFrame_factorization r θ)

theorem firstToDenominatorOverlap_ratio (r θ : ℂ) :
    firstToDenominatorOverlap r θ (coordinateRatio r θ 1 2) = overlapTransition r θ := by
  apply HomogeneousLocalization.val_injective
  apply (frameCoordinate_isUnit r θ _ _ _
    (overlapFirstFrame_factorization r θ)).mul_right_cancel
  rw [overlapTransition_coordinate]
  exact awayCoordinateRatio_mul_coordinate r θ 1 2 _
    (SetLike.mul_mem_graded (firstFrameComplement_grade r θ) (curveG2_mem_grade r θ)) _
    (overlapFirstFrame_factorization r θ)

theorem denominatorOverlap_le_firstCoordinate (r θ : ℂ) :
    overlapProjectivePatch r θ ≤ coordinateProjectivePatch r θ 1 :=
  Proj.basicOpen_mono (curveGrade r θ) _ _
    ⟨_, overlapFirstFrame_factorization r θ⟩

theorem firstToDenominatorOverlap_is_sheaf_restriction (r θ : ℂ)
    (a : ProjectiveCoordinateRing r θ 1) :
    (projectiveCurve r θ).presheaf.map
        (homOfLE (denominatorOverlap_le_firstCoordinate r θ)).op
        ((Proj.basicOpenIsoAway (curveGrade r θ) (coordinateDen r θ 1)
          (coordinate_mem_grade r θ 1) (by decide)).hom a) =
      (overlapProjectiveSectionsIso r θ).hom (firstToDenominatorOverlap r θ a) := by
  exact congrArg (fun k => k a)
    (Proj.awayMap_awayToSection (curveGrade r θ)
      (SetLike.mul_mem_graded (firstFrameComplement_grade r θ) (curveG2_mem_grade r θ))
      (overlapFirstFrame_factorization r θ)).symm

/-- The middle coordinate is a unit on the actual coordinate overlap,
transported through its proved structure-section ring equivalence. -/
def coordinateMiddleUnit (r θ : ℂ) :
    Γ(projectiveCurve r θ, coordinateOverlapPatch r θ)ˣ :=
  Units.map (firstOverlapSectionsEquiv r θ).symm.toMonoidHom
    (middleUnit (firstEquations r θ))

theorem coordinateMiddleUnit_val (r θ : ℂ) :
    (coordinateMiddleUnit r θ : Γ(projectiveCurve r θ, coordinateOverlapPatch r θ)) =
      (coordinateOverlapSectionsIso r θ).hom
        (firstCoordinateRestriction r θ (coordinateRatio r θ 1 2)) := by
  apply (firstOverlapSectionsEquiv r θ).injective
  change firstOverlapSectionsEquiv r θ
      ((firstOverlapSectionsEquiv r θ).symm (middleUnit (firstEquations r θ) : FirstOverlap r θ)) =
    firstOverlapEquiv r θ ((coordinateOverlapSectionsIso r θ).inv
      ((coordinateOverlapSectionsIso r θ).hom
        (firstCoordinateRestriction r θ (coordinateRatio r θ 1 2))))
  rw [RingEquiv.apply_symm_apply, Iso.hom_inv_id_apply, middleUnit_val, firstOverlapEquiv_ratio]
  simp [CycleQ2GeometricAffineCurveCharts.firstDehomogenize, coordinate]

/-- Restricting the actual affine middle unit gives exactly the existing
degree-one transition unit, with its original sign and orientation. -/
theorem coordinateMiddleUnit_restriction (r θ : ℂ) :
    Units.map
        ((projectiveCurve r θ).presheaf.map
          (homOfLE (denominatorOverlap_le_coordinateOverlap r θ)).op).hom.toMonoidHom
        (coordinateMiddleUnit r θ) =
      projectiveTransitionUnit r θ := by
  apply Units.ext
  change (projectiveCurve r θ).presheaf.map
      (homOfLE (denominatorOverlap_le_coordinateOverlap r θ)).op
        (coordinateMiddleUnit r θ : Γ(projectiveCurve r θ, coordinateOverlapPatch r θ)) =
    (overlapProjectiveSectionsIso r θ).hom (overlapTransition r θ)
  rw [coordinateMiddleUnit_val, ← firstCoordinateRestriction_is_sheaf_restriction]
  have hc (s : Γ(projectiveCurve r θ, coordinateProjectivePatch r θ 1)) :
      (projectiveCurve r θ).presheaf.map
          (homOfLE (denominatorOverlap_le_coordinateOverlap r θ)).op
          ((projectiveCurve r θ).presheaf.map
            (homOfLE (coordinateOverlap_le_first r θ)).op s) =
        (projectiveCurve r θ).presheaf.map
          (homOfLE (denominatorOverlap_le_firstCoordinate r θ)).op s := by
    change ((projectiveCurve r θ).presheaf.map
        (homOfLE (coordinateOverlap_le_first r θ)).op ≫
      (projectiveCurve r θ).presheaf.map
        (homOfLE (denominatorOverlap_le_coordinateOverlap r θ)).op) s = _
    rw [← Functor.map_comp]
    exact congrArg (fun f => (projectiveCurve r θ).presheaf.map f s) (Subsingleton.elim _ _)
  rw [hc, firstToDenominatorOverlap_is_sheaf_restriction, firstToDenominatorOverlap_ratio]

end CycleQ2GeometricProjectiveTransition

end
