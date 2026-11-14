import Proposal.GeometricLiteralSurface
import Proposal.GeometricSurfaceAdjunction
import Proposal.GeometricDehomogenizedCharts
import Proposal.GeometricSurfaceDehomogenizedCharts
import Proposal.GeometricAffineProjectiveCharts

/-!
# The actual projective curve restriction in surface equation charts

The original substitution agrees with dehomogenization, actual section maps,
and their ideal kernels. The scheme maps on both coordinate charts form
actual pullback squares with the local quotient maps used by adjunction.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace CycleQ2GeometricSurfaceCurveCharts
open MvPolynomial CategoryTheory AlgebraicGeometry HomogeneousLocalization
open CycleQ2SeedTrace CycleQ2NormalConnecting CycleQ2SeedCechTheta
open CycleQ2GeometricLiteralSurface CycleQ2GeometricSeedNormalIdeals
open CycleQ2GeometricProjectiveCurve CycleQ2GeometricAffineCurveCharts
open CycleQ2GeometricSurfaceAdjunction

theorem firstSurfaceDehomogenize_curve :
    setNormalZero.comp firstSurfaceDehomogenize = firstDehomogenize.comp substitute := by
  ext j
  fin_cases j <;> simp [setNormalZero,firstSurfaceDehomogenize,firstDehomogenize,substitute]

theorem secondSurfaceDehomogenize_curve :
    setNormalZero.comp secondSurfaceDehomogenize = secondDehomogenize.comp substitute := by
  ext j
  fin_cases j <;> simp [setNormalZero,secondSurfaceDehomogenize,secondDehomogenize,substitute]

@[simp] theorem firstPolynomialToCurve_dehomogenize (r θ : ℂ) (p : WeightedPoly) :
    polynomialToCurve (firstQuadric r) (firstCubic θ) (firstSurfaceDehomogenize p)=
      Ideal.Quotient.mk (chartIdeal ![firstQuadric r,firstCubic θ])
        (firstDehomogenize (substitute p)) := by
  change Ideal.Quotient.mk (chartIdeal ![firstQuadric r,firstCubic θ])
    (setNormalZero (firstSurfaceDehomogenize p))=_
  exact congrArg (Ideal.Quotient.mk (chartIdeal ![firstQuadric r,firstCubic θ]))
    (AlgHom.congr_fun firstSurfaceDehomogenize_curve p)

@[simp] theorem secondPolynomialToCurve_dehomogenize (r θ : ℂ) (p : WeightedPoly) :
    polynomialToCurve (secondQuadric r) (secondCubic θ) (secondSurfaceDehomogenize p)=
      Ideal.Quotient.mk (chartIdeal ![secondQuadric r,secondCubic θ])
        (secondDehomogenize (substitute p)) := by
  change Ideal.Quotient.mk (chartIdeal ![secondQuadric r,secondCubic θ])
    (setNormalZero (secondSurfaceDehomogenize p))=_
  exact congrArg (Ideal.Quotient.mk (chartIdeal ![secondQuadric r,secondCubic θ]))
    (AlgHom.congr_fun secondSurfaceDehomogenize_curve p)

open CycleQ2GeometricDehomogenizedCharts

theorem firstCurveChartEquiv_homogeneousFraction (r θ : ℂ) (n : ℕ)
    (p : Poly) (hp : p.IsHomogeneous n) :
    firstChartEquiv r θ (homogeneousFraction r θ 1 n p hp)=
      Ideal.Quotient.mk (chartIdeal ![firstQuadric r,firstCubic θ]) (firstDehomogenize p) := by
  change Ideal.quotientEquivAlgOfEq ℂ (congrArg chartIdeal (dehomogenizedEquations_one r θ))
    (toDehomogenized r θ 1 (homogeneousFraction r θ 1 n p hp))=_
  rw [toDehomogenized_homogeneousFraction,dehomogenize_one]
  rfl

theorem secondCurveChartEquiv_homogeneousFraction (r θ : ℂ) (n : ℕ)
    (p : Poly) (hp : p.IsHomogeneous n) :
    secondChartEquiv r θ (homogeneousFraction r θ 2 n p hp)=
      Ideal.Quotient.mk (chartIdeal ![secondQuadric r,secondCubic θ]) (secondDehomogenize p) := by
  change Ideal.quotientEquivAlgOfEq ℂ (congrArg chartIdeal (dehomogenizedEquations_two r θ))
    (toDehomogenized r θ 2 (homogeneousFraction r θ 2 n p hp))=_
  rw [toDehomogenized_homogeneousFraction,dehomogenize_two]
  rfl

@[simp] theorem curveGradedMap_coordinate (r θ : ℂ) (i : Fin 4) :
    curveGradedMap r θ (quotient r θ (X i.castSucc))=curveMap r θ (X i) := by
  change ambientCurveMap r θ (X i.castSucc)=_
  fin_cases i <;> simp [ambientCurveMap,substitute]

section RenamedDenominator
variable {A B : Type} [CommRing A] [CommRing B] [Algebra ℂ A] [Algebra ℂ B]
variable (𝒜 : ℕ → Submodule ℂ A) (ℬ : ℕ → Submodule ℂ B)
variable [GradedRing 𝒜] [GradedRing ℬ] (f : 𝒜 →+*ᵍ ℬ)

def gradedAwayMapTo (s : A) (t : B) (hst : f s=t) : Away 𝒜 s →+* Away ℬ t :=
  HomogeneousLocalization.map f (by
    rintro a ⟨n,rfl⟩
    exact ⟨n,by simp only [map_pow,hst]⟩)

theorem gradedAwayMapTo_section
    (hf : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f)
    (s : A) (t : B) (hst : f s=t) {n : ℕ} (hs : s ∈ 𝒜 n) :
    Proj.awayToSection 𝒜 s ≫
      (Proj.map f hf).appLE (Proj.basicOpen 𝒜 s) (Proj.basicOpen ℬ t)
        (by rw [Proj.map_preimage_basicOpen,hst]) =
    CommRingCat.ofHom (gradedAwayMapTo 𝒜 ℬ f s t hst) ≫ Proj.awayToSection ℬ t := by
  subst t
  exact Proj.awayToSection_comp_appLE f hf hs

end RenamedDenominator

def coordinateCurveMap (r θ : ℂ) (i : Fin 4) :
    Away (surfaceGrade r θ) (quotient r θ (X i.castSucc)) →+* CoordinateRing r θ i :=
  gradedAwayMapTo (surfaceGrade r θ) (curveGrade r θ) (curveGradedMap r θ)
    (quotient r θ (X i.castSucc)) (curveMap r θ (X i)) (curveGradedMap_coordinate r θ i)

def firstHomogeneousCurveMap (r θ : ℂ) :
    Away (surfaceGrade r θ) (quotient r θ (X 1)) →+* CoordinateRing r θ 1 :=
  coordinateCurveMap r θ 1

def secondHomogeneousCurveMap (r θ : ℂ) :
    Away (surfaceGrade r θ) (quotient r θ (X 2)) →+* CoordinateRing r θ 2 :=
  coordinateCurveMap r θ 2

@[simp] theorem curveGradedMap_quotient (r θ : ℂ) (p : WeightedPoly) :
    curveGradedMap r θ (quotient r θ p)=curveMap r θ (substitute p) := rfl

theorem coordinateCurveMap_homogeneousFraction (r θ : ℂ) (i : Fin 4) (n : ℕ)
    (p : WeightedPoly) (hp : p.IsWeightedHomogeneous weight n) :
    coordinateCurveMap r θ i
      (CycleQ2GeometricSurfaceDehomogenizedCharts.homogeneousFraction r θ i n p hp)=
      homogeneousFraction r θ i n (substitute p) (substitute_homogeneous hp) := by
  apply HomogeneousLocalization.val_injective
  simp only [coordinateCurveMap,gradedAwayMapTo,
    CycleQ2GeometricSurfaceDehomogenizedCharts.homogeneousFraction,homogeneousFraction,
    Away.mk,HomogeneousLocalization.map_mk,HomogeneousLocalization.val_mk]
  change Localization.mk (curveGradedMap r θ (quotient r θ p))
      ⟨curveGradedMap r θ (quotient r θ (X i.castSucc)^n),_⟩ =
    Localization.mk (curveMap r θ (substitute p)) ⟨curveMap r θ (X i)^n,_⟩
  exact congrArg₂ Localization.mk (curveGradedMap_quotient r θ p)
    (Subtype.ext (by simp only [map_pow,curveGradedMap_coordinate]))

open CycleQ2GeometricSurfaceDehomogenizedCharts (firstEquations secondEquations)

def firstAffineCurveMap (r θ : ℂ) :
    SurfaceChartRing (firstEquations r θ) →ₐ[ℂ] ChartRing ![firstQuadric r,firstCubic θ] :=
  CycleQ2GeometricSurfaceAdjunction.surfaceToCurve (firstQuadric r) (firstCubic θ)
    (firstSurfaceDehomogenize (originalG1 r)) (firstSurfaceDehomogenize originalG2)
    (firstSurfaceDehomogenize (thetaK θ))

def secondAffineCurveMap (r θ : ℂ) :
    SurfaceChartRing (secondEquations r θ) →ₐ[ℂ] ChartRing ![secondQuadric r,secondCubic θ] :=
  CycleQ2GeometricSurfaceAdjunction.surfaceToCurve (secondQuadric r) (secondCubic θ)
    (secondSurfaceDehomogenize (originalG1 r)) (secondSurfaceDehomogenize originalG2)
    (secondSurfaceDehomogenize (thetaK θ))

/-- The local adjunction quotient map is exactly the actual projective
surface-to-curve map under the first coordinate presentations. -/
theorem firstChartEquiv_curveMap (r θ : ℂ)
    (z : CycleQ2GeometricSurfaceDehomogenizedCharts.CoordinateRing r θ 1) :
    firstChartEquiv r θ (coordinateCurveMap r θ 1 z)=
      firstAffineCurveMap r θ (CycleQ2GeometricSurfaceDehomogenizedCharts.firstChartEquiv r θ z) := by
  obtain ⟨n,a,ha,rfl⟩ := Away.mk_surjective (surfaceGrade r θ)
    (CycleQ2GeometricSurfaceDehomogenizedCharts.coordinate_mem_grade r θ 1) z
  obtain ⟨p,hp,rfl⟩ := ha
  have hp' : p.IsWeightedHomogeneous weight n := by simpa using hp
  change firstChartEquiv r θ (coordinateCurveMap r θ 1
      (CycleQ2GeometricSurfaceDehomogenizedCharts.homogeneousFraction r θ 1 n p hp'))=
    firstAffineCurveMap r θ (CycleQ2GeometricSurfaceDehomogenizedCharts.firstChartEquiv r θ
      (CycleQ2GeometricSurfaceDehomogenizedCharts.homogeneousFraction r θ 1 n p hp'))
  rw [coordinateCurveMap_homogeneousFraction,firstCurveChartEquiv_homogeneousFraction,
    CycleQ2GeometricSurfaceDehomogenizedCharts.firstChartEquiv_homogeneousFraction]
  exact (firstPolynomialToCurve_dehomogenize r θ p).symm

/-- The same compatibility holds on the second coordinate presentation. -/
theorem secondChartEquiv_curveMap (r θ : ℂ)
    (z : CycleQ2GeometricSurfaceDehomogenizedCharts.CoordinateRing r θ 2) :
    secondChartEquiv r θ (coordinateCurveMap r θ 2 z)=
      secondAffineCurveMap r θ (CycleQ2GeometricSurfaceDehomogenizedCharts.secondChartEquiv r θ z) := by
  obtain ⟨n,a,ha,rfl⟩ := Away.mk_surjective (surfaceGrade r θ)
    (CycleQ2GeometricSurfaceDehomogenizedCharts.coordinate_mem_grade r θ 2) z
  obtain ⟨p,hp,rfl⟩ := ha
  have hp' : p.IsWeightedHomogeneous weight n := by simpa using hp
  change secondChartEquiv r θ (coordinateCurveMap r θ 2
      (CycleQ2GeometricSurfaceDehomogenizedCharts.homogeneousFraction r θ 2 n p hp'))=
    secondAffineCurveMap r θ (CycleQ2GeometricSurfaceDehomogenizedCharts.secondChartEquiv r θ
      (CycleQ2GeometricSurfaceDehomogenizedCharts.homogeneousFraction r θ 2 n p hp'))
  rw [coordinateCurveMap_homogeneousFraction,secondCurveChartEquiv_homogeneousFraction,
    CycleQ2GeometricSurfaceDehomogenizedCharts.secondChartEquiv_homogeneousFraction]
  exact (secondPolynomialToCurve_dehomogenize r θ p).symm

open CycleQ2CartierProjectiveCover (coordinatePatch)

@[simp] theorem coordinateCurvePreimage (r θ : ℂ) (i : Fin 4) :
    curveToSurface r θ ⁻¹ᵁ coordinatePatch r θ i.castSucc = coordinateProjectivePatch r θ i := by
  change Proj.map (curveGradedMap r θ) (curve_irrelevant_le r θ) ⁻¹ᵁ
    Proj.basicOpen (surfaceGrade r θ) (quotient r θ (X i.castSucc)) =
    Proj.basicOpen (curveGrade r θ) (curveMap r θ (X i))
  rw [Proj.map_preimage_basicOpen,curveGradedMap_coordinate]

/-- Restriction of actual structure-sheaf sections along the closed immersion. -/
def coordinateSectionMap (r θ : ℂ) (i : Fin 4) :
    Γ(surface r θ,coordinatePatch r θ i.castSucc) →+*
      Γ(projectiveCurve r θ,coordinateProjectivePatch r θ i) :=
  ((curveToSurface r θ).appLE (coordinatePatch r θ i.castSucc)
    (coordinateProjectivePatch r θ i) (by rw [coordinateCurvePreimage])).hom

theorem coordinateSectionMap_awayToSection (r θ : ℂ) (i : Fin 4)
    (z : CycleQ2GeometricSurfaceDehomogenizedCharts.CoordinateRing r θ i) :
    coordinateSectionMap r θ i (Proj.awayToSection (surfaceGrade r θ)
      (quotient r θ (X i.castSucc)) z) =
    Proj.awayToSection (curveGrade r θ) (curveMap r θ (X i)) (coordinateCurveMap r θ i z) := by
  exact ConcreteCategory.congr_hom
    (gradedAwayMapTo_section (surfaceGrade r θ) (curveGrade r θ) (curveGradedMap r θ)
      (curve_irrelevant_le r θ) (quotient r θ (X i.castSucc)) (curveMap r θ (X i))
      (curveGradedMap_coordinate r θ i)
      (CycleQ2GeometricSurfaceDehomogenizedCharts.coordinate_mem_grade r θ i)) z

theorem firstSectionsEquiv_curveMap (r θ : ℂ)
    (s : Γ(surface r θ,coordinatePatch r θ 1)) :
    CycleQ2GeometricAffineProjectiveCharts.firstSectionsEquiv r θ
      (coordinateSectionMap r θ 1 s) =
    firstAffineCurveMap r θ (CycleQ2GeometricSurfaceDehomogenizedCharts.firstSectionsEquiv r θ s) := by
  obtain ⟨z,rfl⟩ := (projChartSectionsEquiv (surfaceGrade r θ)
    (quotient r θ (X (1 : Fin 4).castSucc))
    (CycleQ2GeometricSurfaceDehomogenizedCharts.coordinate_mem_grade r θ 1) (by decide)).surjective s
  change CycleQ2GeometricAffineProjectiveCharts.firstSectionsEquiv r θ
      (coordinateSectionMap r θ 1 (Proj.awayToSection (surfaceGrade r θ)
        (quotient r θ (X (1 : Fin 4).castSucc)) z)) = _
  rw [coordinateSectionMap_awayToSection]
  change firstChartEquiv r θ
      ((projChartSectionsEquiv (curveGrade r θ) (curveMap r θ (X 1))
        (coordinate_mem_grade r θ 1) (by decide)).symm
        (projChartSectionsEquiv (curveGrade r θ) (curveMap r θ (X 1))
          (coordinate_mem_grade r θ 1) (by decide) (coordinateCurveMap r θ 1 z))) =
    firstAffineCurveMap r θ (CycleQ2GeometricSurfaceDehomogenizedCharts.firstChartEquiv r θ
      ((projChartSectionsEquiv (surfaceGrade r θ) (quotient r θ (X (1 : Fin 4).castSucc))
        (CycleQ2GeometricSurfaceDehomogenizedCharts.coordinate_mem_grade r θ 1) (by decide)).symm
        (projChartSectionsEquiv (surfaceGrade r θ) (quotient r θ (X (1 : Fin 4).castSucc))
          (CycleQ2GeometricSurfaceDehomogenizedCharts.coordinate_mem_grade r θ 1) (by decide) z)))
  simpa only [RingEquiv.symm_apply_apply] using firstChartEquiv_curveMap r θ z

theorem secondSectionsEquiv_curveMap (r θ : ℂ)
    (s : Γ(surface r θ,coordinatePatch r θ 2)) :
    CycleQ2GeometricAffineProjectiveCharts.secondSectionsEquiv r θ
      (coordinateSectionMap r θ 2 s) =
    secondAffineCurveMap r θ (CycleQ2GeometricSurfaceDehomogenizedCharts.secondSectionsEquiv r θ s) := by
  obtain ⟨z,rfl⟩ := (projChartSectionsEquiv (surfaceGrade r θ)
    (quotient r θ (X (2 : Fin 4).castSucc))
    (CycleQ2GeometricSurfaceDehomogenizedCharts.coordinate_mem_grade r θ 2) (by decide)).surjective s
  change CycleQ2GeometricAffineProjectiveCharts.secondSectionsEquiv r θ
      (coordinateSectionMap r θ 2 (Proj.awayToSection (surfaceGrade r θ)
        (quotient r θ (X (2 : Fin 4).castSucc)) z)) = _
  rw [coordinateSectionMap_awayToSection]
  change secondChartEquiv r θ
      ((projChartSectionsEquiv (curveGrade r θ) (curveMap r θ (X 2))
        (coordinate_mem_grade r θ 2) (by decide)).symm
        (projChartSectionsEquiv (curveGrade r θ) (curveMap r θ (X 2))
          (coordinate_mem_grade r θ 2) (by decide) (coordinateCurveMap r θ 2 z))) =
    secondAffineCurveMap r θ (CycleQ2GeometricSurfaceDehomogenizedCharts.secondChartEquiv r θ
      ((projChartSectionsEquiv (surfaceGrade r θ) (quotient r θ (X (2 : Fin 4).castSucc))
        (CycleQ2GeometricSurfaceDehomogenizedCharts.coordinate_mem_grade r θ 2) (by decide)).symm
        (projChartSectionsEquiv (surfaceGrade r θ) (quotient r θ (X (2 : Fin 4).castSucc))
          (CycleQ2GeometricSurfaceDehomogenizedCharts.coordinate_mem_grade r θ 2) (by decide) z)))
  simpa only [RingEquiv.symm_apply_apply] using secondChartEquiv_curveMap r θ z

theorem kernel_appLE_of_eq {X Y : Scheme} (j : X ⟶ Y) (U : Y.Opens) (V : X.Opens)
    (h : V = j ⁻¹ᵁ U) :
    RingHom.ker (j.appLE U V h.le).hom = RingHom.ker (j.app U).hom := by
  subst V
  rw [Scheme.Hom.appLE_eq_app]

theorem coordinateSectionMap_ker (r θ : ℂ) (i : Fin 4) :
    RingHom.ker (coordinateSectionMap r θ i) =
      RingHom.ker ((curveToSurface r θ).app (coordinatePatch r θ i.castSucc)).hom :=
  kernel_appLE_of_eq (curveToSurface r θ) (coordinatePatch r θ i.castSucc)
    (coordinateProjectivePatch r θ i) (coordinateCurvePreimage r θ i).symm

section KernelTransport
variable {A B C D : Type} [CommRing A] [CommRing B] [CommRing C] [CommRing D]

theorem ker_map_of_equiv (f : A →+* B) (g : C →+* D) (e : A ≃+* C) (e' : B ≃+* D)
    (h : ∀ a, e' (f a) = g (e a)) :
    (RingHom.ker f).map e.toRingHom = RingHom.ker g := by
  have hc : (RingHom.ker g).comap e.toRingHom = RingHom.ker f := by
    ext a
    change g (e a)=0 ↔ f a=0
    rw [← h]
    exact e'.map_eq_zero_iff
  rw [← hc]
  exact Ideal.map_comap_of_surjective e.toRingHom e.surjective _

end KernelTransport

/-- The actual closed-curve ideal on the first projective chart is the
literal affine quotient kernel used in the adjunction calculation. -/
theorem firstSectionsEquiv_curveIdeal (r θ : ℂ) :
    (RingHom.ker ((curveToSurface r θ).app (coordinatePatch r θ 1)).hom).map
      (CycleQ2GeometricSurfaceDehomogenizedCharts.firstSectionsEquiv r θ).toRingHom =
    RingHom.ker (firstAffineCurveMap r θ).toRingHom := by
  have hk := coordinateSectionMap_ker r θ (1 : Fin 4)
  change RingHom.ker (coordinateSectionMap r θ 1) =
    RingHom.ker ((curveToSurface r θ).app (coordinatePatch r θ 1)).hom at hk
  rw [← hk]
  exact ker_map_of_equiv (coordinateSectionMap r θ 1) (firstAffineCurveMap r θ).toRingHom
    (CycleQ2GeometricSurfaceDehomogenizedCharts.firstSectionsEquiv r θ)
    (CycleQ2GeometricAffineProjectiveCharts.firstSectionsEquiv r θ) (firstSectionsEquiv_curveMap r θ)

theorem secondSectionsEquiv_curveIdeal (r θ : ℂ) :
    (RingHom.ker ((curveToSurface r θ).app (coordinatePatch r θ 2)).hom).map
      (CycleQ2GeometricSurfaceDehomogenizedCharts.secondSectionsEquiv r θ).toRingHom =
    RingHom.ker (secondAffineCurveMap r θ).toRingHom := by
  have hk := coordinateSectionMap_ker r θ (2 : Fin 4)
  change RingHom.ker (coordinateSectionMap r θ 2) =
    RingHom.ker ((curveToSurface r θ).app (coordinatePatch r θ 2)).hom at hk
  rw [← hk]
  exact ker_map_of_equiv (coordinateSectionMap r θ 2) (secondAffineCurveMap r θ).toRingHom
    (CycleQ2GeometricSurfaceDehomogenizedCharts.secondSectionsEquiv r θ)
    (CycleQ2GeometricAffineProjectiveCharts.secondSectionsEquiv r θ) (secondSectionsEquiv_curveMap r θ)

#print axioms firstSurfaceDehomogenize_curve
#print axioms firstHomogeneousCurveMap
#print axioms firstChartEquiv_curveMap
#print axioms secondChartEquiv_curveMap
#print axioms firstSectionsEquiv_curveMap
#print axioms secondSectionsEquiv_curveMap
#print axioms firstSectionsEquiv_curveIdeal
#print axioms secondSectionsEquiv_curveIdeal
end CycleQ2GeometricSurfaceCurveCharts
end


set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2GeometricSurfaceCurveCharts
open CategoryTheory AlgebraicGeometry HomogeneousLocalization MvPolynomial
open CycleQ2NormalConnecting CycleQ2GeometricLiteralSurface CycleQ2GeometricProjectiveCurve
open CycleQ2GeometricDehomogenizedCharts CycleQ2GeometricSurfaceAdjunction
open CycleQ2GeometricSeedNormalIdeals
open CycleQ2CartierProjectiveCover (coordinatePatch)

section RenamedCharts
variable {A B : Type} [CommRing A] [CommRing B] [Algebra ℂ A] [Algebra ℂ B]
variable (𝒜 : ℕ → Submodule ℂ A) (ℬ : ℕ → Submodule ℂ B)
variable [GradedRing 𝒜] [GradedRing ℬ] (f : 𝒜 →+*ᵍ ℬ)

theorem gradedAwayMapTo_awayι
    (hf : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f)
    (s : A) (t : B) (hst : f s=t) {n : ℕ} (hs : s ∈ 𝒜 n) (hn : 0<n) :
    Proj.awayι ℬ t (by rw [← hst]; exact f.2 hs) hn ≫ Proj.map f hf =
      Spec.map (CommRingCat.ofHom (gradedAwayMapTo 𝒜 ℬ f s t hst)) ≫
        Proj.awayι 𝒜 s hs hn := by
  subst t
  exact Proj.awayι_comp_map f hf hn s hs

end RenamedCharts

section ChartIso
variable {A C : Type} [CommRing A] [CommRing C] [Algebra ℂ A]
variable (𝒜 : ℕ → Submodule ℂ A) [GradedRing 𝒜]

theorem basicOpenChart_inv_ι (s : A) {n : ℕ} (hs : s ∈ 𝒜 n) (hn : 0<n)
    (e : Away 𝒜 s ≃+* C) :
    ((Proj.basicOpenIsoSpec 𝒜 s hs hn) ≪≫ Scheme.Spec.mapIso e.toCommRingCatIso.symm.op).inv ≫
        (Proj.basicOpen 𝒜 s).ι =
      Spec.map (CommRingCat.ofHom e.toRingHom) ≫ Proj.awayι 𝒜 s hs hn := by
  exact Category.assoc _ _ _

end ChartIso

theorem coordinateCurveMap_awayι (r θ : ℂ) (i : Fin 4) :
    Proj.awayι (curveGrade r θ) (curveMap r θ (X i)) (coordinate_mem_grade r θ i) (by decide) ≫
      curveToSurface r θ =
    Spec.map (CommRingCat.ofHom (coordinateCurveMap r θ i)) ≫
      Proj.awayι (surfaceGrade r θ) (quotient r θ (X i.castSucc))
        (CycleQ2GeometricSurfaceDehomogenizedCharts.coordinate_mem_grade r θ i) (by decide) :=
  gradedAwayMapTo_awayι (surfaceGrade r θ) (curveGrade r θ) (curveGradedMap r θ)
    (curve_irrelevant_le r θ) (quotient r θ (X i.castSucc)) (curveMap r θ (X i))
    (curveGradedMap_coordinate r θ i)
    (CycleQ2GeometricSurfaceDehomogenizedCharts.coordinate_mem_grade r θ i) (by decide)

/-- The literal closed immersion restricted to the actual coordinate opens. -/
def coordinateRestrictedMap (r θ : ℂ) (i : Fin 4) :
    (coordinateProjectivePatch r θ i).toScheme ⟶ (coordinatePatch r θ i.castSucc).toScheme :=
  (curveToSurface r θ).resLE (coordinatePatch r θ i.castSucc)
    (coordinateProjectivePatch r θ i) (by rw [coordinateCurvePreimage])

theorem coordinateRestrictedMap_comp_ι (r θ : ℂ) (i : Fin 4) :
    coordinateRestrictedMap r θ i ≫ (coordinatePatch r θ i.castSucc).ι =
      (coordinateProjectivePatch r θ i).ι ≫ curveToSurface r θ :=
  Scheme.Hom.resLE_comp_ι _ _

theorem firstCurveAffineChart_inv_ι (r θ : ℂ) :
    (CycleQ2GeometricAffineProjectiveCharts.firstAffineChart r θ).inv ≫
      (coordinateProjectivePatch r θ 1).ι =
    Spec.map (CommRingCat.ofHom (firstChartEquiv r θ).toRingHom) ≫
      Proj.awayι (curveGrade r θ) (curveMap r θ (X 1)) (coordinate_mem_grade r θ 1) (by decide) :=
  basicOpenChart_inv_ι (curveGrade r θ) (curveMap r θ (X 1))
    (coordinate_mem_grade r θ 1) (by decide) (firstChartEquiv r θ)

theorem firstSurfaceAffineChart_inv_ι (r θ : ℂ) :
    (CycleQ2GeometricSurfaceDehomogenizedCharts.firstAffineChart r θ).inv ≫
      (coordinatePatch r θ 1).ι =
    Spec.map (CommRingCat.ofHom
      (CycleQ2GeometricSurfaceDehomogenizedCharts.firstChartEquiv r θ).toRingHom) ≫
      Proj.awayι (surfaceGrade r θ) (quotient r θ (X (1 : Fin 4).castSucc))
        (CycleQ2GeometricSurfaceDehomogenizedCharts.coordinate_mem_grade r θ 1) (by decide) :=
  basicOpenChart_inv_ι (surfaceGrade r θ) (quotient r θ (X (1 : Fin 4).castSucc))
    (CycleQ2GeometricSurfaceDehomogenizedCharts.coordinate_mem_grade r θ 1) (by decide)
    (CycleQ2GeometricSurfaceDehomogenizedCharts.firstChartEquiv r θ)

theorem firstAffineChart_curveMap (r θ : ℂ) :
    (CycleQ2GeometricAffineProjectiveCharts.firstAffineChart r θ).inv ≫
      coordinateRestrictedMap r θ 1 =
    Spec.map (CommRingCat.ofHom (firstAffineCurveMap r θ).toRingHom) ≫
      (CycleQ2GeometricSurfaceDehomogenizedCharts.firstAffineChart r θ).inv := by
  apply (cancel_mono (coordinatePatch r θ 1).ι).mp
  have hr := coordinateRestrictedMap_comp_ι r θ (1 : Fin 4)
  change coordinateRestrictedMap r θ 1 ≫ (coordinatePatch r θ 1).ι =
    (coordinateProjectivePatch r θ 1).ι ≫ curveToSurface r θ at hr
  rw [Category.assoc,hr,← Category.assoc,firstCurveAffineChart_inv_ι]
  rw [Category.assoc,coordinateCurveMap_awayι]
  rw [Category.assoc,firstSurfaceAffineChart_inv_ι]
  rw [← Category.assoc,← Category.assoc,← Spec.map_comp,← Spec.map_comp]
  congr 1
  congr 1
  ext z
  exact firstChartEquiv_curveMap r θ z

theorem secondCurveAffineChart_inv_ι (r θ : ℂ) :
    (CycleQ2GeometricAffineProjectiveCharts.secondAffineChart r θ).inv ≫
      (coordinateProjectivePatch r θ 2).ι =
    Spec.map (CommRingCat.ofHom (secondChartEquiv r θ).toRingHom) ≫
      Proj.awayι (curveGrade r θ) (curveMap r θ (X 2)) (coordinate_mem_grade r θ 2) (by decide) :=
  basicOpenChart_inv_ι (curveGrade r θ) (curveMap r θ (X 2))
    (coordinate_mem_grade r θ 2) (by decide) (secondChartEquiv r θ)

theorem secondSurfaceAffineChart_inv_ι (r θ : ℂ) :
    (CycleQ2GeometricSurfaceDehomogenizedCharts.secondAffineChart r θ).inv ≫
      (coordinatePatch r θ 2).ι =
    Spec.map (CommRingCat.ofHom
      (CycleQ2GeometricSurfaceDehomogenizedCharts.secondChartEquiv r θ).toRingHom) ≫
      Proj.awayι (surfaceGrade r θ) (quotient r θ (X (2 : Fin 4).castSucc))
        (CycleQ2GeometricSurfaceDehomogenizedCharts.coordinate_mem_grade r θ 2) (by decide) :=
  basicOpenChart_inv_ι (surfaceGrade r θ) (quotient r θ (X (2 : Fin 4).castSucc))
    (CycleQ2GeometricSurfaceDehomogenizedCharts.coordinate_mem_grade r θ 2) (by decide)
    (CycleQ2GeometricSurfaceDehomogenizedCharts.secondChartEquiv r θ)

theorem secondAffineChart_curveMap (r θ : ℂ) :
    (CycleQ2GeometricAffineProjectiveCharts.secondAffineChart r θ).inv ≫
      coordinateRestrictedMap r θ 2 =
    Spec.map (CommRingCat.ofHom (secondAffineCurveMap r θ).toRingHom) ≫
      (CycleQ2GeometricSurfaceDehomogenizedCharts.secondAffineChart r θ).inv := by
  apply (cancel_mono (coordinatePatch r θ 2).ι).mp
  have hr := coordinateRestrictedMap_comp_ι r θ (2 : Fin 4)
  change coordinateRestrictedMap r θ 2 ≫ (coordinatePatch r θ 2).ι =
    (coordinateProjectivePatch r θ 2).ι ≫ curveToSurface r θ at hr
  rw [Category.assoc,hr,← Category.assoc,secondCurveAffineChart_inv_ι]
  rw [Category.assoc,coordinateCurveMap_awayι]
  rw [Category.assoc,secondSurfaceAffineChart_inv_ι]
  rw [← Category.assoc,← Category.assoc,← Spec.map_comp,← Spec.map_comp]
  congr 1
  congr 1
  ext z
  exact secondChartEquiv_curveMap r θ z

/-- The affine quotient and its two actual projective open immersions form
the original scheme-morphism square. -/
theorem firstAffineChart_open_square (r θ : ℂ) :
    (CycleQ2GeometricAffineProjectiveCharts.firstAffineChart r θ).inv ≫
      (coordinateProjectivePatch r θ 1).ι ≫ curveToSurface r θ =
    Spec.map (CommRingCat.ofHom (firstAffineCurveMap r θ).toRingHom) ≫
      (CycleQ2GeometricSurfaceDehomogenizedCharts.firstAffineChart r θ).inv ≫
        (coordinatePatch r θ 1).ι := by
  have hr := coordinateRestrictedMap_comp_ι r θ (1 : Fin 4)
  change coordinateRestrictedMap r θ 1 ≫ (coordinatePatch r θ 1).ι =
    (coordinateProjectivePatch r θ 1).ι ≫ curveToSurface r θ at hr
  rw [← hr,← Category.assoc,firstAffineChart_curveMap,Category.assoc]

theorem secondAffineChart_open_square (r θ : ℂ) :
    (CycleQ2GeometricAffineProjectiveCharts.secondAffineChart r θ).inv ≫
      (coordinateProjectivePatch r θ 2).ι ≫ curveToSurface r θ =
    Spec.map (CommRingCat.ofHom (secondAffineCurveMap r θ).toRingHom) ≫
      (CycleQ2GeometricSurfaceDehomogenizedCharts.secondAffineChart r θ).inv ≫
        (coordinatePatch r θ 2).ι := by
  have hr := coordinateRestrictedMap_comp_ι r θ (2 : Fin 4)
  change coordinateRestrictedMap r θ 2 ≫ (coordinatePatch r θ 2).ι =
    (coordinateProjectivePatch r θ 2).ι ≫ curveToSurface r θ at hr
  rw [← hr,← Category.assoc,secondAffineChart_curveMap,Category.assoc]

theorem firstAffineChart_isPullback (r θ : ℂ) :
    IsPullback
      (Spec.map (CommRingCat.ofHom (firstAffineCurveMap r θ).toRingHom))
      ((CycleQ2GeometricAffineProjectiveCharts.firstAffineChart r θ).inv ≫
        (coordinateProjectivePatch r θ 1).ι)
      ((CycleQ2GeometricSurfaceDehomogenizedCharts.firstAffineChart r θ).inv ≫
        (coordinatePatch r θ 1).ι)
      (curveToSurface r θ) := by
  apply IsOpenImmersion.isPullback
  · simpa only [Category.assoc] using firstAffineChart_open_square r θ
  · rw [Scheme.Hom.opensRange_comp_of_isIso,Scheme.Hom.opensRange_comp_of_isIso,
      Scheme.Opens.opensRange_ι,Scheme.Opens.opensRange_ι]
    exact coordinateCurvePreimage r θ (1 : Fin 4)

theorem secondAffineChart_isPullback (r θ : ℂ) :
    IsPullback
      (Spec.map (CommRingCat.ofHom (secondAffineCurveMap r θ).toRingHom))
      ((CycleQ2GeometricAffineProjectiveCharts.secondAffineChart r θ).inv ≫
        (coordinateProjectivePatch r θ 2).ι)
      ((CycleQ2GeometricSurfaceDehomogenizedCharts.secondAffineChart r θ).inv ≫
        (coordinatePatch r θ 2).ι)
      (curveToSurface r θ) := by
  apply IsOpenImmersion.isPullback
  · simpa only [Category.assoc] using secondAffineChart_open_square r θ
  · rw [Scheme.Hom.opensRange_comp_of_isIso,Scheme.Hom.opensRange_comp_of_isIso,
      Scheme.Opens.opensRange_ι,Scheme.Opens.opensRange_ι]
    exact coordinateCurvePreimage r θ (2 : Fin 4)

#print axioms gradedAwayMapTo_awayι
#print axioms firstAffineChart_curveMap
#print axioms secondAffineChart_curveMap
#print axioms firstAffineChart_open_square
#print axioms secondAffineChart_open_square
#print axioms firstAffineChart_isPullback
#print axioms secondAffineChart_isPullback

end CycleQ2GeometricSurfaceCurveCharts
end
