import Proposal.GeometricRelativeConstantSection

/-!
# The projective zero locus of the same relative constant section

The three fixed-vector rows define a homogeneous quotient of the original
incidence surface ring over its original coefficient algebra. Its Proj
maps to that original surface by a genuine closed immersion. On every
original matrix-pivot open the structure-map kernel is identified with
the degree-zero contraction of the localized three-row ideal.

These are actual scheme maps and their actual structure-sheaf sections.
Principality, regularity for a chosen vector, parameter flatness, and
nonemptiness are separate statements.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md for
attribution of the geometric route and the protected certificate gap.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2RelativeConstantCurve

open CategoryTheory AlgebraicGeometry MvPolynomial HomogeneousLocalization
open CycleQ2IncidenceUniversalChart CycleQ2IncidenceImageLine
  CycleQ2GeometricIncidenceProj CycleQ2UniversalCurveCartier
  CycleQ2GradedLocalizationProjection CycleQ2RelativeConstantSection

variable {S : Type} [CommRing S] [Algebra ℂ S]
variable (y : ParameterIndex → S) (t : Fin 3 → ℂ)

local instance nativePointSurfaceCommRing : CommRing (PointSurface y) := inferInstance
local instance nativeRelativeCurveCommRing : CommRing (RelativeCurveRing y t) := inferInstance

abbrev relativeCurveGrade (d : ℕ) : Submodule S (RelativeCurveRing y t) :=
  CycleQ2GeometricProjectiveCurve.HomogeneousQuotient.grade
    (surfaceGrade y) (relativeSectionIdeal y t) d

instance relativeCurveGradedRing : GradedRing (relativeCurveGrade y t) :=
  CycleQ2GeometricProjectiveCurve.HomogeneousQuotient.gradedRing
    (surfaceGrade y) (relativeSectionIdeal y t) (relativeSectionIdeal_homogeneous y t)

def relativeCurveRingMap : surfaceGrade y →+*ᵍ relativeCurveGrade y t :=
  CycleQ2GeometricProjectiveCurve.HomogeneousQuotient.quotientMap
    (surfaceGrade y) (relativeSectionIdeal y t)

@[simp] theorem relativeCurveRingMap_apply (a : PointSurface y) :
    relativeCurveRingMap y t a = Ideal.Quotient.mk (relativeSectionIdeal y t) a := rfl

theorem relativeCurveRingMap_ker :
    RingHom.ker (relativeCurveRingMap y t) = relativeSectionIdeal y t := by
  ext a
  change Ideal.Quotient.mk (relativeSectionIdeal y t) a = 0 ↔
    a ∈ relativeSectionIdeal y t
  exact Ideal.Quotient.eq_zero_iff_mem

theorem irrelevant_le_map_relativeCurveRingMap :
    HomogeneousIdeal.irrelevant (relativeCurveGrade y t) ≤
      (HomogeneousIdeal.irrelevant (surfaceGrade y)).map (relativeCurveRingMap y t) :=
  CycleQ2GeometricProjectiveCurve.HomogeneousQuotient.irrelevant_le_map_quotientMap
    (surfaceGrade y) (relativeSectionIdeal y t)

def relativeCurve : Scheme := Proj (relativeCurveGrade y t)

def relativeCurveToSurface : relativeCurve y t ⟶ surface y :=
  Proj.map (relativeCurveRingMap y t) (irrelevant_le_map_relativeCurveRingMap y t)

def relativeCurveToBase : relativeCurve y t ⟶ Spec (CommRingCat.of S) :=
  relativeCurveToSurface y t ≫ surfaceToBase y

@[simp] theorem relativeCurveToSurface_preimage_basicOpen (a : PointSurface y) :
    relativeCurveToSurface y t ⁻¹ᵁ Proj.basicOpen (surfaceGrade y) a =
      Proj.basicOpen (relativeCurveGrade y t) (relativeCurveRingMap y t a) :=
  Proj.map_preimage_basicOpen _ _ a

private theorem relativeAwayMap_surjective (a : PointSurface y)
    {d : ℕ} (ha : a ∈ surfaceGrade y d) :
    Function.Surjective (Away.map (relativeCurveRingMap y t) a) := by
  intro z
  obtain ⟨n, b, hb, rfl⟩ := Away.mk_surjective (relativeCurveGrade y t)
    ((relativeCurveRingMap y t).2 ha) z
  obtain ⟨c, hc, rfl⟩ := hb
  refine ⟨Away.mk (surfaceGrade y) ha n c hc, ?_⟩
  simp only [Away.map_mk]
  rfl

instance relativeCurveToSurface_isClosedImmersion :
    IsClosedImmersion (relativeCurveToSurface y t) := by
  have hc : (⨆ i : Σ n : PNat, surfaceGrade y n,
      Proj.basicOpen (surfaceGrade y) (i.2 : PointSurface y)) = ⊤ := by
    have hh := (Proj.affineOpenCover (surfaceGrade y)).openCover.iSup_opensRange
    change (⨆ i : Σ n : PNat, surfaceGrade y n,
      (Proj.awayι (surfaceGrade y) (i.2 : PointSurface y) i.2.2 i.1.2).opensRange) = ⊤ at hh
    simpa only [Proj.opensRange_awayι] using hh
  refine IsZariskiLocalAtTarget.of_iSup_eq_top
    (P := @IsClosedImmersion) (f := relativeCurveToSurface y t)
    (fun i : Σ n : PNat, surfaceGrade y n =>
      Proj.basicOpen (surfaceGrade y) (i.2 : PointSurface y)) hc ?_
  intro i
  have he : (relativeCurveToSurface y t ∣_
      Proj.basicOpen (surfaceGrade y) (i.2 : PointSurface y)) =
      (Proj.basicOpenIsoSpec (relativeCurveGrade y t)
        (relativeCurveRingMap y t i.2) ((relativeCurveRingMap y t).2 i.2.2) i.1.2).hom ≫
        Spec.map (CommRingCat.ofHom (Away.map (relativeCurveRingMap y t) i.2)) ≫
          (Proj.basicOpenIsoSpec (surfaceGrade y) (i.2 : PointSurface y) i.2.2 i.1.2).inv := by
    have hcomm := Proj.awayι_comp_map (relativeCurveRingMap y t)
      (irrelevant_le_map_relativeCurveRingMap y t) i.1.2 (i.2 : PointSurface y) i.2.2
    apply (cancel_mono (Proj.basicOpen (surfaceGrade y) (i.2 : PointSurface y)).ι).mp
    rw [morphismRestrict_ι]
    change (Proj.basicOpen (relativeCurveGrade y t)
        (relativeCurveRingMap y t i.2)).ι ≫ relativeCurveToSurface y t =
      (Proj.basicOpenIsoSpec (relativeCurveGrade y t)
        (relativeCurveRingMap y t i.2) ((relativeCurveRingMap y t).2 i.2.2) i.1.2).hom ≫
        (Spec.map (CommRingCat.ofHom (Away.map (relativeCurveRingMap y t) i.2)) ≫
          Proj.awayι (surfaceGrade y) (i.2 : PointSurface y) i.2.2 i.1.2)
    rw [← hcomm]
    simp only [Proj.awayι, Category.assoc, Iso.hom_inv_id_assoc]
    rfl
  have : IsClosedImmersion
      (Spec.map (CommRingCat.ofHom (Away.map (relativeCurveRingMap y t) i.2))) :=
    IsClosedImmersion.spec_of_surjective _ (relativeAwayMap_surjective y t i.2 i.2.2)
  rw [he]
  infer_instance

/-- The exact degree-zero chart ideal of the original relative quotient. -/
def projectiveRelativeIdeal (p : CycleQ2SegreCech.Chart) :
    Ideal (RelativeProjectivePivot y p) :=
  ((relativeSectionIdeal y t).map
      (algebraMap (PointSurface y) (CoefficientPivot y p))).comap
    (algebraMap (RelativeProjectivePivot y p) (CoefficientPivot y p))

theorem relativeAwayMap_ker (p : CycleQ2SegreCech.Chart) :
    RingHom.ker (Away.map (relativeCurveRingMap y t) (basePivot y p)) =
      projectiveRelativeIdeal y t p := by
  rw [gradedAwayMap_ker (surfaceGrade y) (relativeCurveGrade y t)
    (relativeCurveRingMap y t) (basePivot y p) (relativePivot_homogeneous y p),
    relativeCurveRingMap_ker]
  rfl

def relativePivotOpen (p : CycleQ2SegreCech.Chart) : (surface y).Opens :=
  Proj.basicOpen (surfaceGrade y) (basePivot y p)

theorem relativePivotOpen_isAffineOpen (p : CycleQ2SegreCech.Chart) :
    IsAffineOpen (relativePivotOpen y p) :=
  Proj.isAffineOpen_basicOpen (surfaceGrade y) (basePivot y p)
    (relativePivot_homogeneous y p) (by decide)

def relativeSurfacePivotSectionsEquiv (p : CycleQ2SegreCech.Chart) :
    RelativeProjectivePivot y p ≃+* Γ(surface y, relativePivotOpen y p) :=
  (Proj.basicOpenIsoAway (surfaceGrade y) (basePivot y p)
    (relativePivot_homogeneous y p) (by decide)).commRingCatIsoToRingEquiv

def relativeCurvePivotSectionsEquiv (p : CycleQ2SegreCech.Chart) :
    Away (relativeCurveGrade y t) (relativeCurveRingMap y t (basePivot y p)) ≃+*
      Γ(relativeCurve y t, relativeCurveToSurface y t ⁻¹ᵁ relativePivotOpen y p) :=
  (Proj.basicOpenIsoAway (relativeCurveGrade y t)
    (relativeCurveRingMap y t (basePivot y p))
    ((relativeCurveRingMap y t).2 (relativePivot_homogeneous y p))
    (by decide)).commRingCatIsoToRingEquiv

theorem relativeCurveToSurface_app_pivot (p : CycleQ2SegreCech.Chart)
    (z : RelativeProjectivePivot y p) :
    (relativeCurveToSurface y t).app (relativePivotOpen y p)
        (relativeSurfacePivotSectionsEquiv y p z) =
      relativeCurvePivotSectionsEquiv y t p
        (Away.map (relativeCurveRingMap y t) (basePivot y p) z) := by
  have h := ConcreteCategory.congr_hom
    (Proj.awayToSection_comp_appLE (relativeCurveRingMap y t)
      (irrelevant_le_map_relativeCurveRingMap y t) (relativePivot_homogeneous y p)) z
  change (relativeCurveToSurface y t).appLE (relativePivotOpen y p)
      (relativeCurveToSurface y t ⁻¹ᵁ relativePivotOpen y p) le_rfl
      (Proj.awayToSection (surfaceGrade y) (basePivot y p) z) =
    Proj.awayToSection (relativeCurveGrade y t)
      (relativeCurveRingMap y t (basePivot y p))
      (Away.map (relativeCurveRingMap y t) (basePivot y p) z) at h
  rw [Scheme.Hom.appLE_eq_app] at h
  exact h

def relativeEquationSection (p : CycleQ2SegreCech.Chart) :
    Γ(surface y, relativePivotOpen y p) :=
  relativeSurfacePivotSectionsEquiv y p (relativeProjectiveEquation y t p)

theorem relativeEquationSection_regular (p : CycleQ2SegreCech.Chart)
    (hreg : IsSMulRegular (RelativeProjectivePivot y p) (relativeProjectiveEquation y t p)) :
    IsSMulRegular Γ(surface y, relativePivotOpen y p) (relativeEquationSection y t p) := by
  intro a b hab
  apply (relativeSurfacePivotSectionsEquiv y p).symm.injective
  apply hreg
  have hm := congrArg (relativeSurfacePivotSectionsEquiv y p).symm hab
  simpa only [smul_eq_mul, map_mul, relativeEquationSection,
    RingEquiv.symm_apply_apply] using hm

/-- The actual structure-map kernel pulls back to the original chart
ideal under the canonical projective section-ring equivalence. -/
theorem relativeSectionKernel_comap (p : CycleQ2SegreCech.Chart) :
    (RingHom.ker ((relativeCurveToSurface y t).app (relativePivotOpen y p)).hom).comap
      (relativeSurfacePivotSectionsEquiv y p).toRingHom =
        projectiveRelativeIdeal y t p := by
  rw [← relativeAwayMap_ker y t p]
  ext a
  change (relativeCurveToSurface y t).app (relativePivotOpen y p)
    (relativeSurfacePivotSectionsEquiv y p a) = 0 ↔ _
  rw [relativeCurveToSurface_app_pivot]
  exact (relativeCurvePivotSectionsEquiv y t p).map_eq_zero_iff

#print axioms relativeCurveToSurface_isClosedImmersion
#print axioms relativeAwayMap_ker
#print axioms relativeCurveToSurface_app_pivot
#print axioms relativeEquationSection_regular
#print axioms relativeSectionKernel_comap

end CycleQ2RelativeConstantCurve
end
