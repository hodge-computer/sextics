import Proposal.GeometricSurfaceDehomogenizedCharts
import Proposal.GeometricTwistedDifferential

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2GeometricSurfaceCoefficients

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry MvPolynomial
open CycleQ2GeometricSeedNormalIdeals CycleQ2GeometricCartierNormalLift
open CycleQ2CartierSurfaceGrading CycleQ2CartierProjectiveCover
open CycleQ2GeometricSurfaceDehomogenizedCharts CycleQ2GeometricSurfaceAdjunction
open CycleQ2GeometricDifferentialSheaf CycleQ2GeometricSectionDifferentials

/-- The canonical complex coefficients in the actual degree-zero surface ring. -/
def projectiveCoefficient (r θ : ℂ) : ℂ →+* surfaceGrade r θ 0 :=
  algebraMap ℂ (surfaceGrade r θ 0)

/-- The actual surface structure morphism through the degree-zero ring. -/
def projectiveToComplex (r θ : ℂ) : projectiveSurface r θ ⟶ Spec (CommRingCat.of ℂ) :=
  Proj.toSpecZero (surfaceGrade r θ) ≫
    Spec.map (CommRingCat.ofHom (projectiveCoefficient r θ))

/-- Global complex coefficients induced by the actual structure morphism. -/
def projectiveGlobalCoefficient (r θ : ℂ) : ℂ →+* Γ(projectiveSurface r θ, ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ (projectiveToComplex r θ).appTop).hom

/-- The genuine complex differential sheaf on the actual projective surface. -/
def projectiveDifferentialSheaf (r θ : ℂ) :
    SheafOfModules.{0} (ringSheaf (projectiveSurface r θ).sheaf) :=
  differentialSheaf (projectiveSurface r θ).sheaf (projectiveGlobalCoefficient r θ)

private theorem restriction_from_top (X : Scheme.{0}) (U : X.Opens) :
    U.ι.appTop ≫ U.topIso.hom = X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op := by
  rw [Scheme.Opens.ι_appTop, Scheme.Opens.topIso_hom, ← Functor.map_comp]
  exact congrArg X.presheaf.map (Subsingleton.elim _ _)

def basicOpenCoefficient (r θ : ℂ) (f : SurfaceRing r θ) :
    ℂ →+* HomogeneousLocalization.Away (surfaceGrade r θ) f :=
  (HomogeneousLocalization.fromZeroRingHom (surfaceGrade r θ) (Submonoid.powers f)).comp
    (projectiveCoefficient r θ)

theorem awayι_projectiveToComplex (r θ : ℂ) (f : SurfaceRing r θ) {n : ℕ}
    (hf : f ∈ surfaceGrade r θ n) (hn : 0 < n) :
    Proj.awayι (surfaceGrade r θ) f hf hn ≫ projectiveToComplex r θ =
      Spec.map (CommRingCat.ofHom (basicOpenCoefficient r θ f)) := by
  rw [projectiveToComplex, Proj.awayι_toSpecZero_assoc, ← Spec.map_comp]
  rfl

/-- The actual global scalars restrict to the canonical homogeneous
localization coefficients, under the actual chart-section isomorphism. -/
theorem globalCoefficient_restriction (r θ : ℂ) (f : SurfaceRing r θ) {n : ℕ}
    (hf : f ∈ surfaceGrade r θ n) (hn : 0 < n) :
    CommRingCat.ofHom (projectiveGlobalCoefficient r θ) ≫
        (projectiveSurface r θ).presheaf.map
          (homOfLE (show Proj.basicOpen (surfaceGrade r θ) f ≤ ⊤ from le_top)).op =
      CommRingCat.ofHom (basicOpenCoefficient r θ f) ≫
        (Proj.basicOpenIsoAway (surfaceGrade r θ) f hf hn).hom := by
  have hg := congrArg
    (fun k => (Proj.basicOpenIsoSpec (surfaceGrade r θ) f hf hn).hom ≫ k)
    (awayι_projectiveToComplex r θ f hf hn)
  have hg' : (Proj.basicOpen (surfaceGrade r θ) f).ι ≫ projectiveToComplex r θ =
      (Proj.basicOpenIsoSpec (surfaceGrade r θ) f hf hn).hom ≫
        Spec.map (CommRingCat.ofHom (basicOpenCoefficient r θ f)) := by
    simpa only [Proj.awayι, Category.assoc, Iso.hom_inv_id_assoc] using hg
  have hs := congrArg
    (fun k : (Proj.basicOpen (surfaceGrade r θ) f).toScheme ⟶ Spec (CommRingCat.of ℂ) =>
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ k.appTop ≫
        (Proj.basicOpen (surfaceGrade r θ) f).topIso.hom) hg'
  simp only [Scheme.Hom.comp_appTop, Proj.basicOpenIsoSpec_hom,
    Proj.basicOpenToSpec_app_top, Category.assoc, Scheme.ΓSpecIso_naturality_assoc,
    Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id, restriction_from_top] at hs
  simpa only [projectiveGlobalCoefficient, projectiveSurface, CommRingCat.ofHom_hom, Category.assoc,
    Proj.basicOpenIsoAway_hom] using hs

theorem coefficientOn_basicOpen (r θ : ℂ) (f : SurfaceRing r θ) {n : ℕ}
    (hf : f ∈ surfaceGrade r θ n) (hn : 0 < n) (c : ℂ) :
    (Proj.basicOpenIsoAway (surfaceGrade r θ) f hf hn).inv
      (coefficientOn (projectiveSurface r θ).sheaf (projectiveGlobalCoefficient r θ)
        (Proj.basicOpen (surfaceGrade r θ) f) c) =
      HomogeneousLocalization.fromZeroRingHom (surfaceGrade r θ) (Submonoid.powers f)
        (algebraMap ℂ (surfaceGrade r θ 0) c) := by
  have h := congrArg (fun k : CommRingCat.of ℂ ⟶
      Γ(projectiveSurface r θ, Proj.basicOpen (surfaceGrade r θ) f) => k c)
    (globalCoefficient_restriction r θ f hf hn)
  have h' : coefficientOn (projectiveSurface r θ).sheaf (projectiveGlobalCoefficient r θ)
      (Proj.basicOpen (surfaceGrade r θ) f) c =
        (Proj.basicOpenIsoAway (surfaceGrade r θ) f hf hn).hom
          (basicOpenCoefficient r θ f c) := h
  rw [h', Iso.hom_inv_id_apply]
  rfl

/-- The coefficient map into a weight-one chart is exactly its constant fraction. -/
theorem basicOpenCoefficient_coordinate (r θ : ℂ) (i : Fin 4) (c : ℂ) :
    basicOpenCoefficient r θ (surfaceQuotient r θ (X i.castSucc)) c = constants r θ i c := by
  apply HomogeneousLocalization.val_injective
  rw [constants_val]
  change Localization.mk (algebraMap ℂ (SurfaceRing r θ) c) 1 = _
  rw [Localization.mk_one_eq_algebraMap]
  rfl

/-- This is the canonical degree-zero coefficient algebra, as proved above. -/
instance coordinateAlgebra (r θ : ℂ) (i : Fin 4) : Algebra ℂ (CoordinateRing r θ i) :=
  (basicOpenCoefficient r θ (surfaceQuotient r θ (X i.castSucc))).toAlgebra

@[simp] theorem coordinate_algebraMap (r θ : ℂ) (i : Fin 4) (c : ℂ) :
    algebraMap ℂ (CoordinateRing r θ i) c = constants r θ i c :=
  basicOpenCoefficient_coordinate r θ i c

def coordinateChartAlgEquiv (r θ : ℂ) (i : Fin 4) :
    CoordinateRing r θ i ≃ₐ[ℂ] DehomogenizedRing r θ i where
  __ := coordinateChartEquiv r θ i
  commutes' c := by
    exact (congrArg (coordinateChartEquiv r θ i) (coordinate_algebraMap r θ i c)).trans
      (coordinateChartEquiv_constants r θ i c)

theorem firstChartEquiv_constants (r θ : ℂ) (c : ℂ) :
    firstChartEquiv r θ (constants r θ 1 c) =
      algebraMap ℂ (SurfaceChartRing (firstEquations r θ)) c := by
  change Ideal.quotientEquivAlgOfEq ℂ (congrArg surfaceChartIdeal (dehomogenizedEquations_one r θ))
    (coordinateChartEquiv r θ 1 (constants r θ 1 c)) = _
  rw [coordinateChartEquiv_constants]
  rfl

theorem secondChartEquiv_constants (r θ : ℂ) (c : ℂ) :
    secondChartEquiv r θ (constants r θ 2 c) =
      algebraMap ℂ (SurfaceChartRing (secondEquations r θ)) c := by
  change Ideal.quotientEquivAlgOfEq ℂ (congrArg surfaceChartIdeal (dehomogenizedEquations_two r θ))
    (coordinateChartEquiv r θ 2 (constants r θ 2 c)) = _
  rw [coordinateChartEquiv_constants]
  rfl

def firstChartAlgEquiv (r θ : ℂ) :
    CoordinateRing r θ 1 ≃ₐ[ℂ] SurfaceChartRing (firstEquations r θ) where
  __ := firstChartEquiv r θ
  commutes' c := by rw [coordinate_algebraMap]; exact firstChartEquiv_constants r θ c

def secondChartAlgEquiv (r θ : ℂ) :
    CoordinateRing r θ 2 ≃ₐ[ℂ] SurfaceChartRing (secondEquations r θ) where
  __ := secondChartEquiv r θ
  commutes' c := by rw [coordinate_algebraMap]; exact secondChartEquiv_constants r θ c

theorem coefficientOn_coordinatePatch (r θ : ℂ) (i : Fin 4) (c : ℂ) :
    (Proj.basicOpenIsoAway (surfaceGrade r θ) (surfaceQuotient r θ (X i.castSucc))
      (coordinate_mem_grade r θ i) (by decide)).inv
      (coefficientOn (projectiveSurface r θ).sheaf (projectiveGlobalCoefficient r θ)
        (coordinatePatch r θ i.castSucc) c) = constants r θ i c := by
  exact (coefficientOn_basicOpen r θ (surfaceQuotient r θ (X i.castSucc))
    (coordinate_mem_grade r θ i) (by decide) c).trans
      (basicOpenCoefficient_coordinate r θ i c)

theorem coordinateSectionsEquiv_coefficient (r θ : ℂ) (i : Fin 4) (c : ℂ) :
    coordinateSectionsEquiv r θ i
        (coefficientOn (projectiveSurface r θ).sheaf (projectiveGlobalCoefficient r θ)
          (coordinatePatch r θ i.castSucc) c) =
      algebraMap ℂ (DehomogenizedRing r θ i) c := by
  change coordinateChartEquiv r θ i
    ((Proj.basicOpenIsoAway (surfaceGrade r θ) (surfaceQuotient r θ (X i.castSucc))
      (coordinate_mem_grade r θ i) (by decide)).inv _) = _
  rw [coefficientOn_coordinatePatch, coordinateChartEquiv_constants]
  rfl

theorem firstSectionsEquiv_coefficient (r θ : ℂ) (c : ℂ) :
    firstSectionsEquiv r θ
        (coefficientOn (projectiveSurface r θ).sheaf (projectiveGlobalCoefficient r θ)
          (coordinatePatch r θ 1) c) =
      algebraMap ℂ (SurfaceChartRing (firstEquations r θ)) c := by
  change firstChartEquiv r θ
    ((Proj.basicOpenIsoAway (surfaceGrade r θ) (surfaceQuotient r θ (X (1 : Fin 4).castSucc))
      (coordinate_mem_grade r θ 1) (by decide)).inv _) = _
  exact (congrArg (firstChartEquiv r θ) (coefficientOn_coordinatePatch r θ 1 c)).trans
    (firstChartEquiv_constants r θ c)

theorem secondSectionsEquiv_coefficient (r θ : ℂ) (c : ℂ) :
    secondSectionsEquiv r θ
        (coefficientOn (projectiveSurface r θ).sheaf (projectiveGlobalCoefficient r θ)
          (coordinatePatch r θ 2) c) =
      algebraMap ℂ (SurfaceChartRing (secondEquations r θ)) c := by
  change secondChartEquiv r θ
    ((Proj.basicOpenIsoAway (surfaceGrade r θ) (surfaceQuotient r θ (X (2 : Fin 4).castSucc))
      (coordinate_mem_grade r θ 2) (by decide)).inv _) = _
  exact (congrArg (secondChartEquiv r θ) (coefficientOn_coordinatePatch r θ 2 c)).trans
    (secondChartEquiv_constants r θ c)

/-- The algebra structure is the existing section-differential scalar convention. -/
def coordinateSectionsAlgEquiv (r θ : ℂ) (i : Fin 4) :
    letI : Algebra ℂ Γ(projectiveSurface r θ, coordinatePatch r θ i.castSucc) :=
      sectionAlgebra (projectiveSurface r θ).sheaf (projectiveGlobalCoefficient r θ)
      (coordinatePatch r θ i.castSucc)
    Γ(projectiveSurface r θ, coordinatePatch r θ i.castSucc) ≃ₐ[ℂ] DehomogenizedRing r θ i := by
  letI : Algebra ℂ Γ(projectiveSurface r θ, coordinatePatch r θ i.castSucc) :=
    sectionAlgebra (projectiveSurface r θ).sheaf (projectiveGlobalCoefficient r θ)
    (coordinatePatch r θ i.castSucc)
  exact { coordinateSectionsEquiv r θ i with commutes' := coordinateSectionsEquiv_coefficient r θ i }

def firstSectionsAlgEquiv (r θ : ℂ) :
    letI : Algebra ℂ Γ(projectiveSurface r θ, coordinatePatch r θ 1) :=
      sectionAlgebra (projectiveSurface r θ).sheaf (projectiveGlobalCoefficient r θ)
      (coordinatePatch r θ 1)
    Γ(projectiveSurface r θ, coordinatePatch r θ 1) ≃ₐ[ℂ]
      SurfaceChartRing (firstEquations r θ) := by
  letI : Algebra ℂ Γ(projectiveSurface r θ, coordinatePatch r θ 1) :=
    sectionAlgebra (projectiveSurface r θ).sheaf (projectiveGlobalCoefficient r θ)
    (coordinatePatch r θ 1)
  exact { firstSectionsEquiv r θ with commutes' := firstSectionsEquiv_coefficient r θ }

def secondSectionsAlgEquiv (r θ : ℂ) :
    letI : Algebra ℂ Γ(projectiveSurface r θ, coordinatePatch r θ 2) :=
      sectionAlgebra (projectiveSurface r θ).sheaf (projectiveGlobalCoefficient r θ)
      (coordinatePatch r θ 2)
    Γ(projectiveSurface r θ, coordinatePatch r θ 2) ≃ₐ[ℂ]
      SurfaceChartRing (secondEquations r θ) := by
  letI : Algebra ℂ Γ(projectiveSurface r θ, coordinatePatch r θ 2) :=
    sectionAlgebra (projectiveSurface r θ).sheaf (projectiveGlobalCoefficient r θ)
    (coordinatePatch r θ 2)
  exact { secondSectionsEquiv r θ with commutes' := secondSectionsEquiv_coefficient r θ }

theorem coordinateAffineChart_overComplex (r θ : ℂ) (i : Fin 4) :
    (coordinateAffineChart r θ i).inv ≫ (coordinatePatch r θ i.castSucc).ι ≫
        projectiveToComplex r θ =
      Spec.map (CommRingCat.ofHom (algebraMap ℂ (DehomogenizedRing r θ i))) := by
  change (Spec.map (CommRingCat.ofHom (coordinateChartEquiv r θ i).toRingHom) ≫
      (Proj.basicOpenIsoSpec (surfaceGrade r θ) (surfaceQuotient r θ (X i.castSucc))
        (coordinate_mem_grade r θ i) (by decide)).inv) ≫
      (Proj.basicOpen (surfaceGrade r θ) (surfaceQuotient r θ (X i.castSucc))).ι ≫
        projectiveToComplex r θ = _
  rw [Category.assoc, Proj.basicOpenIsoSpec_inv_ι_assoc,
    awayι_projectiveToComplex, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro c
  exact (coordinateChartAlgEquiv r θ i).commutes c

theorem firstAffineChart_overComplex (r θ : ℂ) :
    (firstAffineChart r θ).inv ≫ (coordinatePatch r θ 1).ι ≫ projectiveToComplex r θ =
      Spec.map (CommRingCat.ofHom (algebraMap ℂ (SurfaceChartRing (firstEquations r θ)))) := by
  change (Spec.map (CommRingCat.ofHom (firstChartEquiv r θ).toRingHom) ≫
      (Proj.basicOpenIsoSpec (surfaceGrade r θ) (surfaceQuotient r θ (X (1 : Fin 4).castSucc))
        (coordinate_mem_grade r θ 1) (by decide)).inv) ≫
      (Proj.basicOpen (surfaceGrade r θ) (surfaceQuotient r θ (X (1 : Fin 4).castSucc))).ι ≫
        projectiveToComplex r θ = _
  rw [Category.assoc, Proj.basicOpenIsoSpec_inv_ι_assoc,
    awayι_projectiveToComplex, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro c
  exact (firstChartAlgEquiv r θ).commutes c

theorem secondAffineChart_overComplex (r θ : ℂ) :
    (secondAffineChart r θ).inv ≫ (coordinatePatch r θ 2).ι ≫ projectiveToComplex r θ =
      Spec.map (CommRingCat.ofHom (algebraMap ℂ (SurfaceChartRing (secondEquations r θ)))) := by
  change (Spec.map (CommRingCat.ofHom (secondChartEquiv r θ).toRingHom) ≫
      (Proj.basicOpenIsoSpec (surfaceGrade r θ) (surfaceQuotient r θ (X (2 : Fin 4).castSucc))
        (coordinate_mem_grade r θ 2) (by decide)).inv) ≫
      (Proj.basicOpen (surfaceGrade r θ) (surfaceQuotient r θ (X (2 : Fin 4).castSucc))).ι ≫
        projectiveToComplex r θ = _
  rw [Category.assoc, Proj.basicOpenIsoSpec_inv_ι_assoc,
    awayι_projectiveToComplex, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro c
  exact (secondChartAlgEquiv r θ).commutes c

#print axioms coefficientOn_coordinatePatch
#print axioms firstSectionsAlgEquiv
#print axioms secondSectionsAlgEquiv
#print axioms firstAffineChart_overComplex
#print axioms secondAffineChart_overComplex

end CycleQ2GeometricSurfaceCoefficients
