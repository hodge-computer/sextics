import Proposal.GeometricSpecializedSectionIdeal

/-!
# The specialized projective zero locus and its regular chart kernels

The source is the Proj of the actual original surface ring modulo the
three specialized rows. Its grading comes from the proved homogeneity of
that ideal. Its map to the existing surface is a genuine closed immersion.
On the original matrix-pivot opens, the actual structure-sheaf component
has the principal kernel calculated in `GeometricSpecializedSectionIdeal`.

At the literal seed, a single nonzero section vector therefore supplies
a regular principal affine cover of this closed immersion. This does not
identify the construction with a scheme-theoretic base-change fiber, prove
nonemptiness, or establish flatness over any incidence-parameter base.

The geometric strategy is due to Ben Diamond and the collaborators cited
in solution.md. Prepared for fqlx with OpenAI ChatGPT assistance.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2SpecializedProjectiveCurve

open CycleQ2IncidencePolynomialJacobianBinding

open CategoryTheory AlgebraicGeometry MvPolynomial HomogeneousLocalization
open CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations
  CycleQ2IncidenceUniversalChart CycleQ2IncidenceImageLine
  CycleQ2GeometricIncidenceProj CycleQ2IncidenceGenericPointSemantics
  CycleQ2IncidencePolynomialRelations CycleQ2IncidenceCoefficientRelations
  CycleQ2UniversalCurveCartier CycleQ2RegularSeedSection
  CycleQ2SpecializedSectionIdeal

variable (y : ParameterIndex → ℂ) (t : Fin 3 → ℂ)

local instance nativePointSurfaceCommRing : CommRing (PointSurface y) := inferInstance

abbrev SpecializedCurveRing := PointSurface y ⧸ specializedSectionIdeal y t

local instance nativeSpecializedCurveCommRing : CommRing (SpecializedCurveRing y t) :=
  inferInstance

abbrev specializedCurveGrade (d : ℕ) : Submodule ℂ (SpecializedCurveRing y t) :=
  CycleQ2GeometricProjectiveCurve.HomogeneousQuotient.grade
    (surfaceGrade y) (specializedSectionIdeal y t) d

instance specializedCurveGradedRing : GradedRing (specializedCurveGrade y t) :=
  CycleQ2GeometricProjectiveCurve.HomogeneousQuotient.gradedRing
    (surfaceGrade y) (specializedSectionIdeal y t)
    (specializedSectionIdeal_homogeneous y t)

def specializedCurveRingMap : surfaceGrade y →+*ᵍ specializedCurveGrade y t :=
  CycleQ2GeometricProjectiveCurve.HomogeneousQuotient.quotientMap
    (surfaceGrade y) (specializedSectionIdeal y t)

@[simp] theorem specializedCurveRingMap_apply (a : PointSurface y) :
    specializedCurveRingMap y t a = Ideal.Quotient.mk (specializedSectionIdeal y t) a := rfl

theorem specializedCurveRingMap_ker :
    RingHom.ker (specializedCurveRingMap y t) = specializedSectionIdeal y t := by
  ext a
  change Ideal.Quotient.mk (specializedSectionIdeal y t) a = 0 ↔
    a ∈ specializedSectionIdeal y t
  exact Ideal.Quotient.eq_zero_iff_mem

theorem irrelevant_le_map_specializedCurveRingMap :
    HomogeneousIdeal.irrelevant (specializedCurveGrade y t) ≤
      (HomogeneousIdeal.irrelevant (surfaceGrade y)).map (specializedCurveRingMap y t) :=
  CycleQ2GeometricProjectiveCurve.HomogeneousQuotient.irrelevant_le_map_quotientMap
    (surfaceGrade y) (specializedSectionIdeal y t)

/-- The actual projective zero locus in the original surface. -/
def specializedCurve : Scheme := Proj (specializedCurveGrade y t)

def specializedCurveToSurface : specializedCurve y t ⟶ surface y :=
  Proj.map (specializedCurveRingMap y t) (irrelevant_le_map_specializedCurveRingMap y t)

def specializedCurveToBase : specializedCurve y t ⟶ Spec (CommRingCat.of ℂ) :=
  specializedCurveToSurface y t ≫ surfaceToBase y

@[simp] theorem specializedCurveToSurface_preimage_basicOpen (a : PointSurface y) :
    specializedCurveToSurface y t ⁻¹ᵁ Proj.basicOpen (surfaceGrade y) a =
      Proj.basicOpen (specializedCurveGrade y t) (specializedCurveRingMap y t a) :=
  Proj.map_preimage_basicOpen _ _ a

/-! ## The quotient gives an actual closed immersion -/

private theorem specializedAwayMap_surjective (a : PointSurface y)
    {d : ℕ} (ha : a ∈ surfaceGrade y d) :
    Function.Surjective (Away.map (specializedCurveRingMap y t) a) := by
  intro z
  obtain ⟨n, b, hb, rfl⟩ := Away.mk_surjective (specializedCurveGrade y t)
    ((specializedCurveRingMap y t).2 ha) z
  obtain ⟨c, hc, rfl⟩ := hb
  refine ⟨Away.mk (surfaceGrade y) ha n c hc, ?_⟩
  simp only [Away.map_mk]
  rfl

instance specializedCurveToSurface_isClosedImmersion :
    IsClosedImmersion (specializedCurveToSurface y t) := by
  have hc : (⨆ i : Σ n : PNat, surfaceGrade y n,
      Proj.basicOpen (surfaceGrade y) (i.2 : PointSurface y)) = ⊤ := by
    have hh := (Proj.affineOpenCover (surfaceGrade y)).openCover.iSup_opensRange
    change (⨆ i : Σ n : PNat, surfaceGrade y n,
      (Proj.awayι (surfaceGrade y) (i.2 : PointSurface y) i.2.2 i.1.2).opensRange) = ⊤ at hh
    simpa only [Proj.opensRange_awayι] using hh
  refine IsZariskiLocalAtTarget.of_iSup_eq_top
    (P := @IsClosedImmersion) (f := specializedCurveToSurface y t)
    (fun i : Σ n : PNat, surfaceGrade y n =>
      Proj.basicOpen (surfaceGrade y) (i.2 : PointSurface y)) hc ?_
  intro i
  have he : (specializedCurveToSurface y t ∣_
      Proj.basicOpen (surfaceGrade y) (i.2 : PointSurface y)) =
      (Proj.basicOpenIsoSpec (specializedCurveGrade y t)
        (specializedCurveRingMap y t i.2) ((specializedCurveRingMap y t).2 i.2.2) i.1.2).hom ≫
        Spec.map (CommRingCat.ofHom (Away.map (specializedCurveRingMap y t) i.2)) ≫
          (Proj.basicOpenIsoSpec (surfaceGrade y) (i.2 : PointSurface y) i.2.2 i.1.2).inv := by
    have hcomm := Proj.awayι_comp_map (specializedCurveRingMap y t)
      (irrelevant_le_map_specializedCurveRingMap y t) i.1.2 (i.2 : PointSurface y) i.2.2
    apply (cancel_mono (Proj.basicOpen (surfaceGrade y) (i.2 : PointSurface y)).ι).mp
    rw [morphismRestrict_ι]
    change (Proj.basicOpen (specializedCurveGrade y t)
        (specializedCurveRingMap y t i.2)).ι ≫ specializedCurveToSurface y t =
      (Proj.basicOpenIsoSpec (specializedCurveGrade y t)
        (specializedCurveRingMap y t i.2) ((specializedCurveRingMap y t).2 i.2.2) i.1.2).hom ≫
        (Spec.map (CommRingCat.ofHom (Away.map (specializedCurveRingMap y t) i.2)) ≫
          Proj.awayι (surfaceGrade y) (i.2 : PointSurface y) i.2.2 i.1.2)
    rw [← hcomm]
    simp only [Proj.awayι, Category.assoc, Iso.hom_inv_id_assoc]
    rfl
  have : IsClosedImmersion
      (Spec.map (CommRingCat.ofHom (Away.map (specializedCurveRingMap y t) i.2))) :=
    IsClosedImmersion.spec_of_surjective _
      (specializedAwayMap_surjective y t i.2 i.2.2)
  rw [he]
  infer_instance

/-! ## The kernels on the unchanged original pivot charts -/

theorem specializedAwayMap_ker (p : CycleQ2SegreCech.Chart) :
    RingHom.ker (Away.map (specializedCurveRingMap y t) (basePivot y p)) =
      projectiveSpecializedIdeal y t p := by
  rw [gradedAwayMap_ker (surfaceGrade y) (specializedCurveGrade y t)
    (specializedCurveRingMap y t) (basePivot y p) (basePivot_homogeneous y p),
    specializedCurveRingMap_ker]
  rfl

theorem specializedAwayMap_ker_principal
    (he : ∀ q, aeval y ((presentation ℂ 57).equation q) = 0)
    (hu : IsUnit (aeval y (leadingProduct ℂ))) (p : CycleQ2SegreCech.Chart) :
    RingHom.ker (Away.map (specializedCurveRingMap y t) (basePivot y p)) =
      Ideal.span {constantProjectiveEquation y t p} := by
  rw [specializedAwayMap_ker, projectiveSpecializedIdeal_principal y t he hu p]

def surfacePivotSectionsEquiv (p : CycleQ2SegreCech.Chart) :
    ConstantProjectivePivot y p ≃+* Γ(surface y, constantPivotOpen y p) :=
  (Proj.basicOpenIsoAway (surfaceGrade y) (basePivot y p)
    (basePivot_homogeneous y p) (by decide)).commRingCatIsoToRingEquiv

def specializedCurvePivotSectionsEquiv (p : CycleQ2SegreCech.Chart) :
    Away (specializedCurveGrade y t) (specializedCurveRingMap y t (basePivot y p)) ≃+*
      Γ(specializedCurve y t, specializedCurveToSurface y t ⁻¹ᵁ constantPivotOpen y p) :=
  (Proj.basicOpenIsoAway (specializedCurveGrade y t)
    (specializedCurveRingMap y t (basePivot y p))
    ((specializedCurveRingMap y t).2 (basePivot_homogeneous y p))
    (by decide)).commRingCatIsoToRingEquiv

theorem specializedCurveToSurface_app_pivot (p : CycleQ2SegreCech.Chart)
    (z : ConstantProjectivePivot y p) :
    (specializedCurveToSurface y t).app (constantPivotOpen y p)
        (surfacePivotSectionsEquiv y p z) =
      specializedCurvePivotSectionsEquiv y t p
        (Away.map (specializedCurveRingMap y t) (basePivot y p) z) := by
  have h := ConcreteCategory.congr_hom
    (Proj.awayToSection_comp_appLE (specializedCurveRingMap y t)
      (irrelevant_le_map_specializedCurveRingMap y t) (basePivot_homogeneous y p)) z
  change (specializedCurveToSurface y t).appLE (constantPivotOpen y p)
      (specializedCurveToSurface y t ⁻¹ᵁ constantPivotOpen y p) le_rfl
      (Proj.awayToSection (surfaceGrade y) (basePivot y p) z) =
    Proj.awayToSection (specializedCurveGrade y t)
      (specializedCurveRingMap y t (basePivot y p))
      (Away.map (specializedCurveRingMap y t) (basePivot y p) z) at h
  rw [Scheme.Hom.appLE_eq_app] at h
  exact h

def specializedEquationSection (p : CycleQ2SegreCech.Chart) :
    Γ(surface y, constantPivotOpen y p) :=
  surfacePivotSectionsEquiv y p (constantProjectiveEquation y t p)

theorem specializedEquationSection_regular (p : CycleQ2SegreCech.Chart)
    (hreg : IsSMulRegular (ConstantProjectivePivot y p) (constantProjectiveEquation y t p)) :
    IsSMulRegular Γ(surface y, constantPivotOpen y p) (specializedEquationSection y t p) := by
  intro a b hab
  apply (surfacePivotSectionsEquiv y p).symm.injective
  apply hreg
  have hm := congrArg (surfacePivotSectionsEquiv y p).symm hab
  simpa only [smul_eq_mul, map_mul, specializedEquationSection,
    RingEquiv.symm_apply_apply] using hm

/-- The actual structure-map kernel is the ideal of the displayed
specialized equation on the original surface open. -/
theorem specializedSectionKernel_principal
    (he : ∀ q, aeval y ((presentation ℂ 57).equation q) = 0)
    (hu : IsUnit (aeval y (leadingProduct ℂ))) (p : CycleQ2SegreCech.Chart) :
    RingHom.ker ((specializedCurveToSurface y t).app (constantPivotOpen y p)).hom =
      Ideal.span {specializedEquationSection y t p} := by
  have hk :
      (RingHom.ker ((specializedCurveToSurface y t).app (constantPivotOpen y p)).hom).comap
        (surfacePivotSectionsEquiv y p).toRingHom =
      RingHom.ker (Away.map (specializedCurveRingMap y t) (basePivot y p)) := by
    ext a
    change (specializedCurveToSurface y t).app (constantPivotOpen y p)
      (surfacePivotSectionsEquiv y p a) = 0 ↔ _
    rw [specializedCurveToSurface_app_pivot]
    exact (specializedCurvePivotSectionsEquiv y t p).map_eq_zero_iff
  rw [← Ideal.map_comap_of_surjective (surfacePivotSectionsEquiv y p).toRingHom
      (surfacePivotSectionsEquiv y p).surjective
      (RingHom.ker ((specializedCurveToSurface y t).app (constantPivotOpen y p)).hom),
    hk, specializedAwayMap_ker_principal y t he hu p, Ideal.map_span, Set.image_singleton]
  rfl

/-- A genuine projective closed immersion at the literal seed, together
with an affine cover whose actual ideal generators are regular. No
geometric hypothesis is supplied by a caller. -/
theorem exists_seed_cartier_cover :
    ∃ t : Fin 3 → ℂ, t ≠ 0 ∧
      IsClosedImmersion (specializedCurveToSurface (seedPoint (57 : ℂ) Complex.I) t) ∧
      (⨆ p : CycleQ2SegreCech.Chart,
        constantPivotOpen (seedPoint (57 : ℂ) Complex.I) p) = ⊤ ∧
      ∀ p : CycleQ2SegreCech.Chart,
        IsAffineOpen (constantPivotOpen (seedPoint (57 : ℂ) Complex.I) p) ∧
        IsSMulRegular Γ(surface (seedPoint (57 : ℂ) Complex.I),
          constantPivotOpen (seedPoint (57 : ℂ) Complex.I) p)
          (specializedEquationSection (seedPoint (57 : ℂ) Complex.I) t p) ∧
        RingHom.ker ((specializedCurveToSurface (seedPoint (57 : ℂ) Complex.I) t).app
          (constantPivotOpen (seedPoint (57 : ℂ) Complex.I) p)).hom =
            Ideal.span {specializedEquationSection (seedPoint (57 : ℂ) Complex.I) t p} := by
  obtain ⟨t, ht, hcover, hreg⟩ := exists_seed_regular_principal_cover
  refine ⟨t, ht, inferInstance, hcover, fun p => ?_⟩
  exact ⟨constantPivotOpen_isAffineOpen (seedPoint (57 : ℂ) Complex.I) p,
    specializedEquationSection_regular (seedPoint (57 : ℂ) Complex.I) t p (hreg p).1,
    specializedSectionKernel_principal (seedPoint (57 : ℂ) Complex.I) t
      seed_original_equations seed_leading_unit p⟩

#print axioms specializedCurveToSurface_isClosedImmersion
#print axioms specializedAwayMap_ker
#print axioms specializedSectionKernel_principal
#print axioms exists_seed_cartier_cover

end CycleQ2SpecializedProjectiveCurve
end
