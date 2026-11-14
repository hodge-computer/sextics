import Proposal.GeometricSurfaceProjectiveCoefficients
import Proposal.GeometricLiteralSurface
import Proposal.GeometricSurfaceCurveCharts
import Proposal.GeometricProjectiveCoefficients
import Proposal.GeometricAffineChartSections
import Proposal.GeometricDifferentialChartTransport
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Preadditive.Biproducts

/-!
# Actual surface and curve Jacobian charts and differential frames

The canonical complex structures, genuine Jacobian principal charts,
and actual sheaf differential bases are bound to the equation modules
used by local adjunction. The curve Jacobian maps form actual pullback
squares with the projective closed immersion.
-/

section SurfaceComplexRestrictionPart

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2GeometricSurfaceComplexRestriction

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry MvPolynomial
open CycleQ2GeometricSeedNormalIdeals CycleQ2GeometricProjectiveCurve
open CycleQ2NormalConnecting
open CycleQ2GeometricLiteralSurface
open CycleQ2GeometricDifferentialSheaf CycleQ2GeometricAffineChartSections

/-- The actual graded quotient carries the canonical degree-zero complex fractions to each other. -/
theorem gradedAwayMap_coefficient (r θ : ℂ) (s : SurfaceRing r θ) (c : ℂ) :
    HomogeneousLocalization.Away.map (curveGradedMap r θ) s
        (CycleQ2GeometricSurfaceCoefficients.basicOpenCoefficient r θ s c) =
      CycleQ2GeometricProjectiveCoefficients.basicOpenCoefficient r θ (curveGradedMap r θ s) c := by
  apply HomogeneousLocalization.val_injective
  simp only [CycleQ2GeometricSurfaceCoefficients.basicOpenCoefficient,
    CycleQ2GeometricSurfaceCoefficients.projectiveCoefficient,
    CycleQ2GeometricProjectiveCoefficients.basicOpenCoefficient,
    CycleQ2GeometricDifferentialSheaf.projectiveCoefficient,
    RingHom.comp_apply, HomogeneousLocalization.fromZeroRingHom,
    HomogeneousLocalization.Away.map]
  change Localization.mk ((curveRestriction r θ) (algebraMap ℂ (SurfaceRing r θ) c))
    ⟨curveGradedMap r θ 1, _⟩ =
      Localization.mk (algebraMap ℂ (CurveRing r θ) c) 1
  rw [(curveRestriction r θ).commutes]
  congr 1
  apply Subtype.ext
  exact map_one (curveGradedMap r θ)

/-- The actual projective closed immersion respects the canonical complex structure morphisms. -/
theorem curveToSurface_overComplex (r θ : ℂ) :
    curveToSurface r θ ≫ CycleQ2GeometricSurfaceCoefficients.projectiveToComplex r θ =
      CycleQ2GeometricDifferentialSheaf.projectiveToComplex r θ := by
  refine (Proj.mapAffineOpenCover (curveGradedMap r θ) (curve_irrelevant_le r θ)).openCover.hom_ext
    _ _ fun s => ?_
  simp only [Scheme.AffineOpenCover.openCover_f, Proj.mapAffineOpenCover_f]
  change Proj.awayι (curveGrade r θ) (curveGradedMap r θ s.2)
      ((curveGradedMap r θ).2 s.2.2) s.1.2 ≫
      (Proj.map (curveGradedMap r θ) (curve_irrelevant_le r θ) ≫
        CycleQ2GeometricSurfaceCoefficients.projectiveToComplex r θ) = _
  rw [Proj.awayι_comp_map_assoc (curveGradedMap r θ) (curve_irrelevant_le r θ)
      s.1.2 s.2 s.2.2,
    CycleQ2GeometricSurfaceCoefficients.awayι_projectiveToComplex,
    CycleQ2GeometricProjectiveCoefficients.awayι_projectiveToComplex, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro c
  exact gradedAwayMap_coefficient r θ s.2 c

theorem curveToSurface_globalCoefficient (r θ : ℂ) :
    CommRingCat.ofHom (CycleQ2GeometricSurfaceCoefficients.projectiveGlobalCoefficient r θ) ≫
        (curveToSurface r θ).appTop =
      CommRingCat.ofHom (CycleQ2GeometricDifferentialSheaf.projectiveGlobalCoefficient r θ) := by
  have h := congrArg
    (fun f : projectiveCurve r θ ⟶ Spec (CommRingCat.of ℂ) =>
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ f.appTop)
    (curveToSurface_overComplex r θ)
  simpa only [Scheme.Hom.comp_appTop, Category.assoc,
    CycleQ2GeometricSurfaceCoefficients.projectiveGlobalCoefficient,
    CycleQ2GeometricDifferentialSheaf.projectiveGlobalCoefficient,
    CommRingCat.ofHom_hom] using h

/-- Scalar compatibility on every actual open, induced by the same scheme morphism. -/
theorem curveToSurface_coefficient_app (r θ : ℂ) (U : (surface r θ).Opens) (c : ℂ) :
    (curveToSurface r θ).app U
        (coefficientOn (surface r θ).sheaf
          (CycleQ2GeometricSurfaceCoefficients.projectiveGlobalCoefficient r θ) U c) =
      coefficientOn (projectiveCurve r θ).sheaf
        (CycleQ2GeometricDifferentialSheaf.projectiveGlobalCoefficient r θ)
        (curveToSurface r θ ⁻¹ᵁ U) c := by
  have h := coefficientOn_app (curveToSurface r θ)
    (CycleQ2GeometricSurfaceCoefficients.projectiveToComplex r θ) U c
  rw [curveToSurface_overComplex] at h
  exact h

#print axioms curveToSurface_overComplex
#print axioms curveToSurface_coefficient_app

end CycleQ2GeometricSurfaceComplexRestriction

end
end SurfaceComplexRestrictionPart

section SurfaceJacobianChartsPart

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2GeometricSurfaceJacobianCharts

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry MvPolynomial Module
open CycleQ2SeedTrace CycleQ2NormalConnecting CycleQ2GeometricAffineCurveCharts
open CycleQ2GeometricSurfaceAdjunction CycleQ2GeometricSurfaceDehomogenizedCharts
open CycleQ2GeometricSurfaceCoefficients CycleQ2CartierProjectiveCover

section PrincipalChart

variable {X : Scheme.{0}} {U : X.Opens} {A : Type} [CommRing A] [Algebra ℂ A]
  (e : U.toScheme ≅ Spec (CommRingCat.of A)) (a : A)

def principalImmersion : Spec (CommRingCat.of (Localization.Away a)) ⟶ X :=
  Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away a))) ≫ e.inv ≫ U.ι

instance principalImmersion_isOpenImmersion : IsOpenImmersion (principalImmersion e a) := by
  dsimp [principalImmersion]
  infer_instance

def principalOpen : X.Opens := (principalImmersion e a).opensRange

omit [Algebra ℂ A] in
private theorem principalRange : Set.range (principalOpen e a).ι = Set.range (principalImmersion e a) :=
  Subtype.range_coe_subtype

/-- Restrict the actual affine scheme chart to an actual principal localization. -/
def principalChart : (principalOpen e a).toScheme ≅ Spec (CommRingCat.of (Localization.Away a)) :=
  IsOpenImmersion.isoOfRangeEq (principalOpen e a).ι (principalImmersion e a) (principalRange e a)

theorem principalChart_inv_ι :
    (principalChart e a).inv ≫ (principalOpen e a).ι = principalImmersion e a :=
  IsOpenImmersion.isoOfRangeEq_inv_fac _ _ _

variable (f : X ⟶ Spec (CommRingCat.of ℂ))
  (h : e.inv ≫ U.ι ≫ f = Spec.map (CommRingCat.ofHom (algebraMap ℂ A)))

include h in
theorem principalImmersion_overComplex :
    principalImmersion e a ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap ℂ (Localization.Away a))) := by
  dsimp only [principalImmersion]
  rw [Category.assoc, Category.assoc, h, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro c
  exact (IsScalarTower.algebraMap_apply ℂ A (Localization.Away a) c).symm

include h in
theorem principalChart_overComplex :
    (principalChart e a).inv ≫ (principalOpen e a).ι ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap ℂ (Localization.Away a))) := by
  rw [← Category.assoc, principalChart_inv_ι]
  exact principalImmersion_overComplex e a f h

end PrincipalChart

def firstJacobian (r θ : ℂ) (i : Fin 2) (j : Fin 3) : SurfaceChartRing (firstEquations r θ) :=
  augmentedJacobian (firstEquations r θ) (normalPolynomial (firstQuadric r) i) (includeCurve (X j))

def secondJacobian (r θ : ℂ) (i : Fin 2) (j : Fin 3) : SurfaceChartRing (secondEquations r θ) :=
  augmentedJacobian (secondEquations r θ) (normalPolynomial (secondQuadric r) i) (includeCurve (X j))

abbrev FirstNormalRing (r θ : ℂ) (i : Fin 2) (j : Fin 3) :=
  NormalSurfacePatch (firstQuadric r) (firstCubic θ)
    (firstSurfaceDehomogenize (originalG1 r)) (firstSurfaceDehomogenize originalG2)
    (firstSurfaceDehomogenize (thetaK θ)) i j

abbrev SecondNormalRing (r θ : ℂ) (i : Fin 2) (j : Fin 3) :=
  NormalSurfacePatch (secondQuadric r) (secondCubic θ)
    (secondSurfaceDehomogenize (originalG1 r)) (secondSurfaceDehomogenize originalG2)
    (secondSurfaceDehomogenize (thetaK θ)) i j

def firstNormalOpen (r θ : ℂ) (i : Fin 2) (j : Fin 3) : (projectiveSurface r θ).Opens :=
  principalOpen (firstAffineChart r θ) (firstJacobian r θ i j)

def secondNormalOpen (r θ : ℂ) (i : Fin 2) (j : Fin 3) : (projectiveSurface r θ).Opens :=
  principalOpen (secondAffineChart r θ) (secondJacobian r θ i j)

/-- The exact first Jacobian localization from local adjunction is a genuine surface chart. -/
def firstNormalChart (r θ : ℂ) (i : Fin 2) (j : Fin 3) :
    (firstNormalOpen r θ i j).toScheme ≅ Spec (CommRingCat.of (FirstNormalRing r θ i j)) :=
  principalChart (firstAffineChart r θ) (firstJacobian r θ i j)

/-- The exact second Jacobian localization from local adjunction is a genuine surface chart. -/
def secondNormalChart (r θ : ℂ) (i : Fin 2) (j : Fin 3) :
    (secondNormalOpen r θ i j).toScheme ≅ Spec (CommRingCat.of (SecondNormalRing r θ i j)) :=
  principalChart (secondAffineChart r θ) (secondJacobian r θ i j)

theorem firstNormalChart_overComplex (r θ : ℂ) (i : Fin 2) (j : Fin 3) :
    (firstNormalChart r θ i j).inv ≫ (firstNormalOpen r θ i j).ι ≫ projectiveToComplex r θ =
      Spec.map (CommRingCat.ofHom (algebraMap ℂ (FirstNormalRing r θ i j))) :=
  principalChart_overComplex (firstAffineChart r θ) (firstJacobian r θ i j)
    (projectiveToComplex r θ) (firstAffineChart_overComplex r θ)

theorem secondNormalChart_overComplex (r θ : ℂ) (i : Fin 2) (j : Fin 3) :
    (secondNormalChart r θ i j).inv ≫ (secondNormalOpen r θ i j).ι ≫ projectiveToComplex r θ =
      Spec.map (CommRingCat.ofHom (algebraMap ℂ (SecondNormalRing r θ i j))) :=
  principalChart_overComplex (secondAffineChart r θ) (secondJacobian r θ i j)
    (projectiveToComplex r θ) (secondAffineChart_overComplex r θ)

/-- The local adjunction basis now belongs to the actual first affine surface chart. -/
def firstNormalKaehlerBasis (r θ : ℂ) (i : Fin 2) (j : Fin 3) :
    Basis (Fin 2) (FirstNormalRing r θ i j) (KaehlerDifferential ℂ (FirstNormalRing r θ i j)) :=
  localSurfaceKaehlerBasis (firstEquations r θ) (normalPolynomial (firstQuadric r) i) (includeCurve (X j))

def secondNormalKaehlerBasis (r θ : ℂ) (i : Fin 2) (j : Fin 3) :
    Basis (Fin 2) (SecondNormalRing r θ i j) (KaehlerDifferential ℂ (SecondNormalRing r θ i j)) :=
  localSurfaceKaehlerBasis (secondEquations r θ) (normalPolynomial (secondQuadric r) i) (includeCurve (X j))

#print axioms firstNormalChart_overComplex
#print axioms secondNormalChart_overComplex
#print axioms firstNormalKaehlerBasis

end CycleQ2GeometricSurfaceJacobianCharts

end
end SurfaceJacobianChartsPart

section FunctionalDifferentialTransportPart

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

attribute [local instance] CategoryTheory.Limits.HasBinaryBiproducts.of_hasBinaryProducts

namespace CycleQ2GeometricFunctionalDifferentials

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open CycleQ2GeometricDifferentialSheaf CycleQ2GeometricAffineDifferentialSheaf
open scoped TensorProduct

variable {A : Type} [CommRing A] [Algebra ℂ A]

section Localization

variable (M : Submonoid A) (S : Type) [CommRing S]
  [Algebra ℂ S] [Algebra A S] [IsScalarTower ℂ A S] [IsLocalization M S]
  (l : KaehlerDifferential ℂ A →ₗ[A] A)

/-- A linear functional on genuine differentials extends through their genuine localization. -/
def localFunctional : KaehlerDifferential ℂ S →ₗ[S] S := by
  let : Algebra.FormallyEtale A S := Algebra.FormallyEtale.of_isLocalization (Rₘ := S) M
  exact (LinearMap.liftBaseChange S ((Algebra.linearMap A S).comp l)).comp
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale ℂ A S).symm.toLinearMap

@[simp] theorem localFunctional_D_algebraMap (a : A) :
    localFunctional M S l (KaehlerDifferential.D ℂ S (algebraMap A S a)) =
      algebraMap A S (l (KaehlerDifferential.D ℂ A a)) := by
  let : Algebra.FormallyEtale A S := Algebra.FormallyEtale.of_isLocalization (Rₘ := S) M
  simp only [localFunctional, LinearMap.comp_apply, LinearEquiv.coe_coe,
    KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap,
    LinearMap.liftBaseChange_tmul, LinearMap.comp_apply, Algebra.linearMap_apply, one_smul]

def localizedDerivation : Derivation ℂ S S :=
  (localFunctional M S l).compDer (KaehlerDifferential.D ℂ S)

@[simp] theorem localizedDerivation_algebraMap (a : A) :
    localizedDerivation M S l (algebraMap A S a) =
      algebraMap A S (l (KaehlerDifferential.D ℂ A a)) :=
  localFunctional_D_algebraMap M S l a

theorem localizedDerivation_fraction (a : A) (s : M) :
    localizedDerivation M S l (IsLocalization.mk' S a s) =
      (IsLocalization.mk' S 1 s) ^ 2 *
        (algebraMap A S (s : A) * algebraMap A S (l (KaehlerDifferential.D ℂ A a)) -
          algebraMap A S a * algebraMap A S (l (KaehlerDifferential.D ℂ A (s : A)))) := by
  let δ := localizedDerivation M S l
  have ht : IsLocalization.mk' S 1 s * algebraMap A S (s : A) = 1 := by
    rw [IsLocalization.mk'_spec, map_one]
  have hinv := δ.leibniz_of_mul_eq_one ht
  have hpow : (IsLocalization.mk' S 1 s) ^ 2 * algebraMap A S (s : A) =
      IsLocalization.mk' S 1 s := by
    rw [pow_two, mul_assoc, ht, mul_one]
  change δ (IsLocalization.mk' S a s) = _
  rw [IsLocalization.mk'_eq_mul_mk'_one, Derivation.leibniz, hinv]
  simp only [δ, localizedDerivation_algebraMap, smul_eq_mul]
  calc
    _ = (IsLocalization.mk' S 1 s) ^ 2 * algebraMap A S (s : A) *
        algebraMap A S (l (KaehlerDifferential.D ℂ A a)) -
      (IsLocalization.mk' S 1 s) ^ 2 * algebraMap A S a *
        algebraMap A S (l (KaehlerDifferential.D ℂ A (s : A))) := by
      rw [hpow]
      ring
    _ = _ := by ring

end Localization

private theorem localizedDerivation_mk (l : KaehlerDifferential ℂ A →ₗ[A] A)
    (p : PrimeSpectrum.Top A) (a : A) (s : p.asIdeal.primeCompl) :
    localizedDerivation p.asIdeal.primeCompl (StructureSheaf.Localizations A p) l
        (LocalizedModule.mk a s) =
      LocalizedModule.mk ((s : A) * l (KaehlerDifferential.D ℂ A a) -
        a * l (KaehlerDifferential.D ℂ A (s : A))) (s * s) := by
  rw [CycleQ2GeometricStructureDerivation.localizedModule_mk_eq,
    CycleQ2GeometricStructureDerivation.localizedModule_mk_eq]
  rw [localizedDerivation_fraction, ← map_mul, ← map_mul, ← map_sub, pow_two,
    ← IsLocalization.mk'_mul, one_mul, mul_comm, ← IsLocalization.mk'_eq_mul_mk'_one]

/-- Every affine differential functional differentiates actual regular sections. -/
def sectionDerivative (l : KaehlerDifferential ℂ A →ₗ[A] A)
    (U : Opens (PrimeSpectrum.Top A)) : AffineSections A U →+ AffineSections A U where
  toFun s := ⟨fun p => localizedDerivation p.1.asIdeal.primeCompl
      (StructureSheaf.Localizations A p.1) l (s.1 p), by
    intro p
    obtain ⟨V, hpV, i, a, b, h⟩ := s.2 p
    refine ⟨V, hpV, i, b * l (KaehlerDifferential.D ℂ A a) -
      a * l (KaehlerDifferential.D ℂ A b), b * b, fun q => ?_⟩
    obtain ⟨hbq, hq⟩ := h q
    exact ⟨q.1.asIdeal.primeCompl.mul_mem hbq hbq,
      (congrArg (localizedDerivation q.1.asIdeal.primeCompl
        (StructureSheaf.Localizations A q.1) l) hq).trans
          (localizedDerivation_mk l q.1 a ⟨b, hbq⟩)⟩⟩
  map_zero' := by
    apply Subtype.ext
    funext p
    exact map_zero (localizedDerivation p.1.asIdeal.primeCompl
      (StructureSheaf.Localizations A p.1) l)
  map_add' s t := by
    apply Subtype.ext
    funext p
    exact map_add (localizedDerivation p.1.asIdeal.primeCompl
      (StructureSheaf.Localizations A p.1) l) (s.1 p) (t.1 p)

theorem sectionDerivative_algebraMap (l : KaehlerDifferential ℂ A →ₗ[A] A)
    (U : Opens (PrimeSpectrum.Top A)) (a : A) :
    sectionDerivative l U (algebraMap A (AffineSections A U) a) =
      algebraMap A (AffineSections A U) (l (KaehlerDifferential.D ℂ A a)) := by
  apply Subtype.ext
  funext p
  exact localizedDerivation_algebraMap p.1.asIdeal.primeCompl
    (StructureSheaf.Localizations A p.1) l a

/-- The actual regular-section derivation for any linear functional, with no rank-one premise. -/
def regularSectionDerivation (l : KaehlerDifferential ℂ A →ₗ[A] A) :
    AffineDerivation A (affineStructureModule A) where
  d {U} := sectionDerivative l U.unop
  d_mul {U} s t := by
    apply Subtype.ext
    funext p
    exact (localizedDerivation p.1.asIdeal.primeCompl
      (StructureSheaf.Localizations A p.1) l).leibniz (s.1 p) (t.1 p)
  d_map {_ _} _ _ := rfl
  d_app {U} c := by
    change sectionDerivative l U.unop
      (algebraMap A (AffineSections A U.unop) (algebraMap ℂ A c)) = 0
    rw [sectionDerivative_algebraMap, (KaehlerDifferential.D ℂ A).map_algebraMap,
      map_zero, map_zero]

section Chart

open CycleQ2GeometricDifferentialRestriction CycleQ2GeometricAffineChartSections
  CycleQ2GeometricSheafKaehlerMap CycleQ2GeometricDifferentialChartTransport

variable {X : Scheme.{0}} {U : X.Opens}
  (e : U.toScheme ≅ Spec (CommRingCat.of A))
  (f : X ⟶ Spec (CommRingCat.of ℂ))
  (h : e.inv ≫ U.ι ≫ f = Spec.map (CommRingCat.ofHom (algebraMap ℂ A)))
  (l : KaehlerDifferential ℂ A →ₗ[A] A)

/-- The genuine derivation of actual chart sections associated with the
affine Kähler functional. -/
def chartCoefficientDerivation :
    ChartDerivation f (ChartStructureModule (X := X) (U := U)) :=
  CycleQ2GeometricDerivationTransport.structureDerivation
    (chartSourceRingSheaf X U) (Spec.structureSheaf A) (chartOpensEquiv e)
    (chartSectionsIso e) (overCoefficient X.sheaf (schemeCoefficient f) U)
    (coefficientMap (Spec.structureSheaf A) (affineCoefficient A))
    (fun V c => chartSectionsIso_coefficient e f h V.unop c)
    (regularSectionDerivation l)

theorem chartCoefficientDerivation_section (V : Over U) (a : A) :
    (chartCoefficientDerivation e f h l).d (X := op V) (chartSection e V a) =
      chartSection e V (l (KaehlerDifferential.D ℂ A a)) := by
  change (chartSectionIso e V).inv
    (sectionDerivative l ((chartOpensEquiv e).functor.obj V)
      ((chartSectionIso e V).hom ((chartSectionIso e V).inv
        (algebraMap A (AffineSections A ((chartOpensEquiv e).functor.obj V)) a)))) = _
  rw [Iso.inv_hom_id_apply, sectionDerivative_algebraMap]
  rfl

def chartCoefficientMap : ChartDifferentialModule f ⟶ ChartStructureModule (X := X) (U := U) :=
  restrictedLift X.sheaf (schemeCoefficient f) U (ChartStructureModule (X := X) (U := U))
    (chartCoefficientDerivation e f h l)

theorem chartCoefficientMap_D (V : Over U) (s : Γ(X, V.left)) :
    (chartCoefficientMap e f h l).val.app (op V)
        ((universalDifferential X.sheaf (schemeCoefficient f)).d (X := op V.left) s) =
      (chartCoefficientDerivation e f h l).d (X := op V) s :=
  PresheafOfModules.Derivation.congr_d
    (restrictedLift_fac X.sheaf (schemeCoefficient f) U
      (ChartStructureModule (X := X) (U := U)) (chartCoefficientDerivation e f h l)) s

theorem chartCoefficientMap_sectionLift (ω : KaehlerDifferential ℂ A) :
    (chartCoefficientMap e f h l).val.app (op (chartTop U))
        (sectionLift X.sheaf (schemeCoefficient f)
          (differentialSheaf X.sheaf (schemeCoefficient f))
          (universalDifferential X.sheaf (schemeCoefficient f)) U
          (chartSection e (chartTop U)) (chartSection_complex e f h (chartTop U)) ω) =
      chartSection e (chartTop U) (l ω) := by
  have hω : ω ∈ Submodule.span A (Set.range (KaehlerDifferential.D ℂ A)) := by
    rw [KaehlerDifferential.span_range_derivation]
    trivial
  induction hω using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      rw [sectionLift_D]
      exact (chartCoefficientMap_D e f h l (chartTop U)
        (chartSection e (chartTop U) a)).trans
          (chartCoefficientDerivation_section e f h l (chartTop U) a)
  | zero => simp only [map_zero]
  | add x y _ _ hx hy => simp only [map_add, hx, hy]
  | smul a x _ hx =>
      rw [sectionLift_smul, ((chartCoefficientMap e f h l).val.app (op (chartTop U))).hom.map_smul,
        hx]
      change chartSection e (chartTop U) a * chartSection e (chartTop U) (l x) =
        chartSection e (chartTop U) (l (a • x))
      rw [l.map_smul]
      exact (map_mul (chartSection e (chartTop U)) a (l x)).symm


omit l in
def chartBasisSection (b : Module.Basis (Fin 2) A (KaehlerDifferential ℂ A)) (i : Fin 2) :
    (differentialSheaf X.sheaf (schemeCoefficient f)).val.obj (op U) :=
  sectionLift X.sheaf (schemeCoefficient f)
    (differentialSheaf X.sheaf (schemeCoefficient f))
    (universalDifferential X.sheaf (schemeCoefficient f)) U
    (chartSection e (chartTop U)) (chartSection_complex e f h (chartTop U)) (b i)

omit l in
def chartBasisVectorMap (b : Module.Basis (Fin 2) A (KaehlerDifferential ℂ A)) (i : Fin 2) :
    ChartStructureModule (X := X) (U := U) ⟶ ChartDifferentialModule f :=
  unitMapFromChart (ChartDifferentialModule f) (chartBasisSection e f h b i)

omit l in
theorem chartCoefficientMap_basisSection
    (b : Module.Basis (Fin 2) A (KaehlerDifferential ℂ A)) (i j : Fin 2) :
    (chartCoefficientMap e f h (b.coord i)).val.app (op (chartTop U))
      (chartBasisSection e f h b j) = (if i = j then 1 else 0 : Γ(X, U)) := by
  rw [chartBasisSection, chartCoefficientMap_sectionLift]
  by_cases hij : i = j
  · subst j
    simp [Module.Basis.coord_apply]
  · simp [Module.Basis.coord_apply, hij]

omit l in
def chartReconstructionMap (b : Module.Basis (Fin 2) A (KaehlerDifferential ℂ A)) :
    ChartDifferentialModule (U := U) f ⟶ ChartDifferentialModule (U := U) f :=
  chartCoefficientMap e f h (b.coord 0) ≫ chartBasisVectorMap e f h b 0 +
    chartCoefficientMap e f h (b.coord 1) ≫ chartBasisVectorMap e f h b 1

omit l in
/-- The ordinary two-coordinate decomposition reconstructs every actual differential-sheaf section. -/
theorem chartReconstructionMap_eq (b : Module.Basis (Fin 2) A (KaehlerDifferential ℂ A)) :
    chartReconstructionMap e f h b = 𝟙 (ChartDifferentialModule f) := by
  apply restrictedLift_unique X.sheaf (schemeCoefficient f) U
  apply chartDerivation_ext e f h
  intro a
  let L := sectionLift X.sheaf (schemeCoefficient f)
    (differentialSheaf X.sheaf (schemeCoefficient f))
    (universalDifferential X.sheaf (schemeCoefficient f)) U
    (chartSection e (chartTop U)) (chartSection_complex e f h (chartTop U))
  have hv (i : Fin 2) :
      (unitMapFromChart (ChartDifferentialModule f) (chartBasisSection e f h b i)).val.app
        (op (chartTop U)) ((chartCoefficientMap e f h (b.coord i)).val.app (op (chartTop U))
          ((universalDifferential X.sheaf (schemeCoefficient f)).d (chartSection e (chartTop U) a))) =
      L (b.coord i (KaehlerDifferential.D ℂ A a) • b i) := by
    have hc := (chartCoefficientMap_D e f h (b.coord i) (chartTop U)
      (chartSection e (chartTop U) a)).trans
        (chartCoefficientDerivation_section e f h (b.coord i) (chartTop U) a)
    refine (congrArg (fun z : Γ(X, U) =>
      (unitMapFromChart (ChartDifferentialModule f)
        (chartBasisSection e f h b i)).val.app (op (chartTop U)) z) hc).trans ?_
    exact (unitMapFromChart_top (ChartDifferentialModule f) (chartBasisSection e f h b i)
      (chartSection e (chartTop U) (b.coord i (KaehlerDifferential.D ℂ A a)))).trans
        (sectionLift_smul X.sheaf (schemeCoefficient f)
          (differentialSheaf X.sheaf (schemeCoefficient f))
          (universalDifferential X.sheaf (schemeCoefficient f)) U
          (chartSection e (chartTop U)) (chartSection_complex e f h (chartTop U))
          (b.coord i (KaehlerDifferential.D ℂ A a)) (b i)).symm
  change (unitMapFromChart (ChartDifferentialModule f) (chartBasisSection e f h b 0)).val.app
      (op (chartTop U)) ((chartCoefficientMap e f h (b.coord 0)).val.app (op (chartTop U))
        ((universalDifferential X.sheaf (schemeCoefficient f)).d (chartSection e (chartTop U) a))) +
    (unitMapFromChart (ChartDifferentialModule f) (chartBasisSection e f h b 1)).val.app
      (op (chartTop U)) ((chartCoefficientMap e f h (b.coord 1)).val.app (op (chartTop U))
        ((universalDifferential X.sheaf (schemeCoefficient f)).d (chartSection e (chartTop U) a))) =
      (universalDifferential X.sheaf (schemeCoefficient f)).d (chartSection e (chartTop U) a)
  refine (congrArg₂ (fun x y => x + y) (hv 0) (hv 1)).trans ?_
  have hb : b.coord 0 (KaehlerDifferential.D ℂ A a) • b 0 +
      b.coord 1 (KaehlerDifferential.D ℂ A a) • b 1 = KaehlerDifferential.D ℂ A a := by
    simpa only [Module.Basis.coord_apply, Fin.sum_univ_two] using b.sum_repr (KaehlerDifferential.D ℂ A a)
  exact (map_add L _ _).symm.trans ((congrArg L hb).trans
    (sectionLift_D X.sheaf (schemeCoefficient f)
      (differentialSheaf X.sheaf (schemeCoefficient f))
      (universalDifferential X.sheaf (schemeCoefficient f)) U
      (chartSection e (chartTop U)) (chartSection_complex e f h (chartTop U)) a))

omit l in
def chartRestrictedBasisSection (b : Module.Basis (Fin 2) A (KaehlerDifferential ℂ A))
    (V : Over U) (i : Fin 2) : (ChartDifferentialModule f).val.obj (op V) :=
  (ChartDifferentialModule f).val.map (toChartTop V).op (chartBasisSection e f h b i)

omit l in
theorem chartCoefficientMap_restrictedBasisSection
    (b : Module.Basis (Fin 2) A (KaehlerDifferential ℂ A)) (V : Over U) (i j : Fin 2) :
    (chartCoefficientMap e f h (b.coord i)).val.app (op V)
      (chartRestrictedBasisSection e f h b V j) = (if i = j then 1 else 0 : Γ(X, V.left)) := by
  rw [chartRestrictedBasisSection, PresheafOfModules.naturality_apply,
    chartCoefficientMap_basisSection]
  split_ifs
  · change X.presheaf.map V.hom.op (1 : Γ(X, U)) = 1
    exact map_one _
  · exact map_zero _

omit l in
theorem chartSection_reconstruction (b : Module.Basis (Fin 2) A (KaehlerDifferential ℂ A))
    (V : Over U) (ω : (ChartDifferentialModule f).val.obj (op V)) :
    ω = ((chartCoefficientMap e f h (b.coord 0)).val.app (op V) ω : Γ(X, V.left)) •
      chartRestrictedBasisSection e f h b V 0 +
      ((chartCoefficientMap e f h (b.coord 1)).val.app (op V) ω : Γ(X, V.left)) •
      chartRestrictedBasisSection e f h b V 1 := by
  have hh := congrArg (fun k : ChartDifferentialModule f ⟶ ChartDifferentialModule f =>
      k.val.app (op V) ω) (chartReconstructionMap_eq e f h b)
  change (unitMapFromChart (ChartDifferentialModule f) (chartBasisSection e f h b 0)).val.app (op V)
      ((chartCoefficientMap e f h (b.coord 0)).val.app (op V) ω) +
    (unitMapFromChart (ChartDifferentialModule f) (chartBasisSection e f h b 1)).val.app (op V)
      ((chartCoefficientMap e f h (b.coord 1)).val.app (op V) ω) = ω at hh
  rw [unitMapFromChart_apply, unitMapFromChart_apply] at hh
  exact hh.symm

omit l in
/-- On every subopen of the actual chart, the genuine differential-sheaf sections have the
two coefficients supplied by the original algebraic Kähler basis. -/
def chartSectionEquiv (b : Module.Basis (Fin 2) A (KaehlerDifferential ℂ A)) (V : Over U) :
    (ChartDifferentialModule f).val.obj (op V) ≃ₗ[Γ(X, V.left)] (Fin 2 → Γ(X, V.left)) where
  toFun ω i := (chartCoefficientMap e f h (b.coord i)).val.app (op V) ω
  invFun c := c 0 • chartRestrictedBasisSection e f h b V 0 +
    c 1 • chartRestrictedBasisSection e f h b V 1
  left_inv ω := (chartSection_reconstruction e f h b V ω).symm
  right_inv c := by
    funext i
    simp only [map_add, map_smul, chartCoefficientMap_restrictedBasisSection]
    fin_cases i <;> simp
  map_add' ω η := by funext i; exact map_add _ _ _
  map_smul' c ω := by funext i; exact map_smul _ c ω

omit l in
def chartSectionBasis (b : Module.Basis (Fin 2) A (KaehlerDifferential ℂ A)) (V : Over U) :
    Module.Basis (Fin 2) Γ(X, V.left) ((ChartDifferentialModule f).val.obj (op V)) :=
  Module.Basis.ofEquivFun (chartSectionEquiv e f h b V)

omit l in
theorem chartSectionBasis_apply (b : Module.Basis (Fin 2) A (KaehlerDifferential ℂ A))
    (V : Over U) (i : Fin 2) :
    chartSectionBasis e f h b V i = chartRestrictedBasisSection e f h b V i := by
  have hi := congrFun (Module.Basis.coe_ofEquivFun (chartSectionEquiv e f h b V)) i
  rw [show chartSectionBasis e f h b V i =
    (chartSectionEquiv e f h b V).symm (Pi.single i 1) from hi]
  apply (chartSectionEquiv e f h b V).injective
  rw [LinearEquiv.apply_symm_apply]
  funext j
  calc
    (Pi.single i 1 : Fin 2 → Γ(X, V.left)) j = (if j = i then 1 else 0) := by
      simp only [Pi.single_apply, eq_comm]
    _ = _ := (chartCoefficientMap_restrictedBasisSection e f h b V j i).symm

omit l in
theorem chartRestrictedBasisSection_eq_sectionLift
    (b : Module.Basis (Fin 2) A (KaehlerDifferential ℂ A)) (V : Over U) (i : Fin 2) :
    chartRestrictedBasisSection e f h b V i =
      sectionLift X.sheaf (schemeCoefficient f)
        (differentialSheaf X.sheaf (schemeCoefficient f))
        (universalDifferential X.sheaf (schemeCoefficient f)) V.left
        (chartSection e V) (chartSection_complex e f h V) (b i) :=
  sectionLift_restriction X.sheaf (schemeCoefficient f)
    (differentialSheaf X.sheaf (schemeCoefficient f))
    (universalDifferential X.sheaf (schemeCoefficient f)) U
    (chartSection e (chartTop U)) (chartSection_complex e f h (chartTop U))
    V.left V.hom.le (chartSection e V) (chartSection_complex e f h V)
    (chartSection_naturality e (toChartTop V)) (b i)

omit l in
theorem chartSectionBasis_repr_D (b : Module.Basis (Fin 2) A (KaehlerDifferential ℂ A))
    (V : Over U) (a : A) (i : Fin 2) :
    (chartSectionBasis e f h b V).repr
        ((universalDifferential X.sheaf (schemeCoefficient f)).d (chartSection e V a)) i =
      chartSection e V (b.coord i (KaehlerDifferential.D ℂ A a)) := by
  change (chartCoefficientMap e f h (b.coord i)).val.app (op V)
    ((universalDifferential X.sheaf (schemeCoefficient f)).d (chartSection e V a)) = _
  exact (chartCoefficientMap_D e f h (b.coord i) V (chartSection e V a)).trans
    (chartCoefficientDerivation_section e f h (b.coord i) V a)

open CategoryTheory.Limits

omit l in
theorem chartBasisVectorMap_coefficient
    (b : Module.Basis (Fin 2) A (KaehlerDifferential ℂ A)) (i j : Fin 2) :
    chartBasisVectorMap e f h b i ≫ chartCoefficientMap e f h (b.coord j) =
      if j = i then 𝟙 (ChartStructureModule (X := X) (U := U)) else 0 := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  split_ifs with hij
  · change (chartCoefficientMap e f h (b.coord j)).val.app V
        (a • chartRestrictedBasisSection e f h b V.unop i) = a
    rw [map_smul, chartCoefficientMap_restrictedBasisSection, if_pos hij]
    exact mul_one (show Γ(X, V.unop.left) from a)
  · change (chartCoefficientMap e f h (b.coord j)).val.app V
        (a • chartRestrictedBasisSection e f h b V.unop i) = 0
    rw [map_smul, chartCoefficientMap_restrictedBasisSection, if_neg hij]
    exact mul_zero (show Γ(X, V.unop.left) from a)

omit l in
/-- The original algebraic rank-two basis gives an isomorphism of the genuine differential
sheaf with two copies of the actual structure module on the whole affine chart. -/
def chartRankTwoIso (b : Module.Basis (Fin 2) A (KaehlerDifferential ℂ A)) :
    ChartDifferentialModule (U := U) f ≅
      (ChartStructureModule (X := X) (U := U) ⊞ ChartStructureModule (X := X) (U := U)) where
  hom := biprod.lift (chartCoefficientMap e f h (b.coord 0))
    (chartCoefficientMap e f h (b.coord 1))
  inv := biprod.desc (chartBasisVectorMap e f h b 0) (chartBasisVectorMap e f h b 1)
  hom_inv_id := by
    rw [biprod.lift_desc]
    exact chartReconstructionMap_eq e f h b
  inv_hom_id := by
    apply biprod.hom_ext'
    · apply biprod.hom_ext <;> simp [Category.assoc, chartBasisVectorMap_coefficient]
    · apply biprod.hom_ext <;> simp [Category.assoc, chartBasisVectorMap_coefficient]

#print axioms chartRankTwoIso
#print axioms chartSectionBasis_apply
#print axioms chartSectionBasis_repr_D


end Chart

#print axioms regularSectionDerivation

end CycleQ2GeometricFunctionalDifferentials

namespace CycleQ2GeometricSurfaceDifferentialCharts

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry Module
open CycleQ2GeometricDifferentialSheaf CycleQ2GeometricAffineChartSections
open CycleQ2GeometricDifferentialChartTransport CycleQ2GeometricFunctionalDifferentials
open CycleQ2GeometricSurfaceCoefficients CycleQ2GeometricSurfaceJacobianCharts
open CycleQ2CartierProjectiveCover CycleQ2GeometricSurfaceAdjunction

abbrev FirstDifferentialModule (r θ : ℂ) (i : Fin 2) (j : Fin 3) :=
  (CycleQ2GeometricSurfaceCoefficients.projectiveDifferentialSheaf r θ).over (firstNormalOpen r θ i j)

abbrev SecondDifferentialModule (r θ : ℂ) (i : Fin 2) (j : Fin 3) :=
  (CycleQ2GeometricSurfaceCoefficients.projectiveDifferentialSheaf r θ).over (secondNormalOpen r θ i j)

abbrev FirstStructureModule (r θ : ℂ) (i : Fin 2) (j : Fin 3) :=
  ChartStructureModule (X := projectiveSurface r θ) (U := firstNormalOpen r θ i j)

abbrev SecondStructureModule (r θ : ℂ) (i : Fin 2) (j : Fin 3) :=
  ChartStructureModule (X := projectiveSurface r θ) (U := secondNormalOpen r θ i j)

/-- A genuine rank-two frame of the actual surface differential sheaf, induced by
the precise first-chart basis already used in local adjunction. -/
def firstDifferentialIso (r θ : ℂ) (i : Fin 2) (j : Fin 3) :
    FirstDifferentialModule r θ i j ≅
      (FirstStructureModule r θ i j ⊞ FirstStructureModule r θ i j) :=
  chartRankTwoIso (firstNormalChart r θ i j) (projectiveToComplex r θ)
    (firstNormalChart_overComplex r θ i j) (firstNormalKaehlerBasis r θ i j)

def secondDifferentialIso (r θ : ℂ) (i : Fin 2) (j : Fin 3) :
    SecondDifferentialModule r θ i j ≅
      (SecondStructureModule r θ i j ⊞ SecondStructureModule r θ i j) :=
  chartRankTwoIso (secondNormalChart r θ i j) (projectiveToComplex r θ)
    (secondNormalChart_overComplex r θ i j) (secondNormalKaehlerBasis r θ i j)

def firstSectionsBasis (r θ : ℂ) (i : Fin 2) (j : Fin 3) (V : Over (firstNormalOpen r θ i j)) :
    Basis (Fin 2) Γ(projectiveSurface r θ, V.left) ((FirstDifferentialModule r θ i j).val.obj (op V)) :=
  chartSectionBasis (firstNormalChart r θ i j) (projectiveToComplex r θ)
    (firstNormalChart_overComplex r θ i j) (firstNormalKaehlerBasis r θ i j) V

def secondSectionsBasis (r θ : ℂ) (i : Fin 2) (j : Fin 3) (V : Over (secondNormalOpen r θ i j)) :
    Basis (Fin 2) Γ(projectiveSurface r θ, V.left) ((SecondDifferentialModule r θ i j).val.obj (op V)) :=
  chartSectionBasis (secondNormalChart r θ i j) (projectiveToComplex r θ)
    (secondNormalChart_overComplex r θ i j) (secondNormalKaehlerBasis r θ i j) V

theorem firstSectionsBasis_apply (r θ : ℂ) (i : Fin 2) (j : Fin 3)
    (V : Over (firstNormalOpen r θ i j)) (k : Fin 2) :
    firstSectionsBasis r θ i j V k =
      CycleQ2GeometricSheafKaehlerMap.sectionLift (projectiveSurface r θ).sheaf
        (projectiveGlobalCoefficient r θ) (CycleQ2GeometricSurfaceCoefficients.projectiveDifferentialSheaf r θ)
        (universalDifferential (projectiveSurface r θ).sheaf (projectiveGlobalCoefficient r θ)) V.left
        (chartSection (firstNormalChart r θ i j) V)
        (chartSection_complex (firstNormalChart r θ i j) (projectiveToComplex r θ)
          (firstNormalChart_overComplex r θ i j) V) (firstNormalKaehlerBasis r θ i j k) :=
  (chartSectionBasis_apply (firstNormalChart r θ i j) (projectiveToComplex r θ)
    (firstNormalChart_overComplex r θ i j) (firstNormalKaehlerBasis r θ i j) V k).trans
      (chartRestrictedBasisSection_eq_sectionLift (firstNormalChart r θ i j) (projectiveToComplex r θ)
        (firstNormalChart_overComplex r θ i j) (firstNormalKaehlerBasis r θ i j) V k)

theorem secondSectionsBasis_apply (r θ : ℂ) (i : Fin 2) (j : Fin 3)
    (V : Over (secondNormalOpen r θ i j)) (k : Fin 2) :
    secondSectionsBasis r θ i j V k =
      CycleQ2GeometricSheafKaehlerMap.sectionLift (projectiveSurface r θ).sheaf
        (projectiveGlobalCoefficient r θ) (CycleQ2GeometricSurfaceCoefficients.projectiveDifferentialSheaf r θ)
        (universalDifferential (projectiveSurface r θ).sheaf (projectiveGlobalCoefficient r θ)) V.left
        (chartSection (secondNormalChart r θ i j) V)
        (chartSection_complex (secondNormalChart r θ i j) (projectiveToComplex r θ)
          (secondNormalChart_overComplex r θ i j) V) (secondNormalKaehlerBasis r θ i j k) :=
  (chartSectionBasis_apply (secondNormalChart r θ i j) (projectiveToComplex r θ)
    (secondNormalChart_overComplex r θ i j) (secondNormalKaehlerBasis r θ i j) V k).trans
      (chartRestrictedBasisSection_eq_sectionLift (secondNormalChart r θ i j) (projectiveToComplex r θ)
        (secondNormalChart_overComplex r θ i j) (secondNormalKaehlerBasis r θ i j) V k)

/-- The determinant of the actual differential-sheaf sections, on the first Jacobian chart. -/
def firstSectionsDeterminantEquiv (r θ : ℂ) (i : Fin 2) (j : Fin 3)
    (V : Over (firstNormalOpen r θ i j)) :
    (⋀[Γ(projectiveSurface r θ, V.left)]^2 ((FirstDifferentialModule r θ i j).val.obj (op V))) ≃ₗ[
      Γ(projectiveSurface r θ, V.left)] Γ(projectiveSurface r θ, V.left) :=
  determinantEquiv (firstSectionsBasis r θ i j V)

def secondSectionsDeterminantEquiv (r θ : ℂ) (i : Fin 2) (j : Fin 3)
    (V : Over (secondNormalOpen r θ i j)) :
    (⋀[Γ(projectiveSurface r θ, V.left)]^2 ((SecondDifferentialModule r θ i j).val.obj (op V))) ≃ₗ[
      Γ(projectiveSurface r θ, V.left)] Γ(projectiveSurface r θ, V.left) :=
  determinantEquiv (secondSectionsBasis r θ i j V)

#print axioms firstDifferentialIso
#print axioms secondDifferentialIso
#print axioms firstSectionsBasis_apply
#print axioms firstSectionsDeterminantEquiv

end CycleQ2GeometricSurfaceDifferentialCharts

end
end FunctionalDifferentialTransportPart

section SurfacePrincipalCurveChartsPart

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2GeometricSurfacePrincipalCurveCharts
open CategoryTheory AlgebraicGeometry MvPolynomial
open CycleQ2GeometricSurfaceCurveCharts CycleQ2GeometricSurfaceJacobianCharts
open CycleQ2GeometricLiteralSurface CycleQ2GeometricSurfaceAdjunction
open CycleQ2GeometricSurfaceDehomogenizedCharts
open CycleQ2GeometricAffineCurveCharts CycleQ2GeometricProjectiveCurve
open CycleQ2NormalConnecting CycleQ2SeedTrace

section PrincipalSquare
variable {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (a : A)

def affinePrincipalMap : Localization.Away a →+* Localization.Away (φ a) :=
  IsLocalization.Away.map _ _ φ a

theorem affinePrincipalMap_base (b : A) :
    affinePrincipalMap φ a (algebraMap A (Localization.Away a) b) =
      algebraMap B (Localization.Away (φ a)) (φ b) := by
  simp only [affinePrincipalMap,IsLocalization.Away.map,IsLocalization.map_eq]

theorem affinePrincipal_square :
    Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away (φ a)))) ≫
      Spec.map (CommRingCat.ofHom φ) =
    Spec.map (CommRingCat.ofHom (affinePrincipalMap φ a)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away a))) := by
  rw [← Spec.map_comp,← Spec.map_comp]
  apply congrArg Spec.map
  ext b
  exact (affinePrincipalMap_base φ a b).symm

theorem affinePrincipal_isPullback :
    IsPullback
      (Spec.map (CommRingCat.ofHom (affinePrincipalMap φ a)))
      (Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away (φ a)))))
      (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away a))))
      (Spec.map (CommRingCat.ofHom φ)) := by
  apply IsOpenImmersion.isPullback
  · exact affinePrincipal_square φ a
  · rw [Scheme.Hom.opensRange_localizationAway (R := CommRingCat.of A) a,
      Scheme.Hom.opensRange_localizationAway (R := CommRingCat.of B) (φ a)]
    rfl

end PrincipalSquare

abbrev FirstNormalCurveRing (r θ : ℂ) (i : Fin 2) (j : Fin 3) :=
  NormalCurvePatch (firstQuadric r) (firstCubic θ)
    (firstSurfaceDehomogenize (originalG1 r)) (firstSurfaceDehomogenize originalG2)
    (firstSurfaceDehomogenize (thetaK θ)) i j

abbrev SecondNormalCurveRing (r θ : ℂ) (i : Fin 2) (j : Fin 3) :=
  NormalCurvePatch (secondQuadric r) (secondCubic θ)
    (secondSurfaceDehomogenize (originalG1 r)) (secondSurfaceDehomogenize originalG2)
    (secondSurfaceDehomogenize (thetaK θ)) i j

def firstNormalCurveMap (r θ : ℂ) (i : Fin 2) (j : Fin 3) :
    FirstNormalRing r θ i j →ₐ[ℂ] FirstNormalCurveRing r θ i j :=
  normalChartMap (firstQuadric r) (firstCubic θ)
    (firstSurfaceDehomogenize (originalG1 r)) (firstSurfaceDehomogenize originalG2)
    (firstSurfaceDehomogenize (thetaK θ)) i j

def secondNormalCurveMap (r θ : ℂ) (i : Fin 2) (j : Fin 3) :
    SecondNormalRing r θ i j →ₐ[ℂ] SecondNormalCurveRing r θ i j :=
  normalChartMap (secondQuadric r) (secondCubic θ)
    (secondSurfaceDehomogenize (originalG1 r)) (secondSurfaceDehomogenize originalG2)
    (secondSurfaceDehomogenize (thetaK θ)) i j

theorem firstNormalCurveMap_eq (r θ : ℂ) (i : Fin 2) (j : Fin 3) :
    (firstNormalCurveMap r θ i j).toRingHom =
      affinePrincipalMap (firstAffineCurveMap r θ).toRingHom (firstJacobian r θ i j) := by
  rfl

theorem secondNormalCurveMap_eq (r θ : ℂ) (i : Fin 2) (j : Fin 3) :
    (secondNormalCurveMap r θ i j).toRingHom =
      affinePrincipalMap (secondAffineCurveMap r θ).toRingHom (secondJacobian r θ i j) := by
  rfl

def firstNormalCurveImmersion (r θ : ℂ) (i : Fin 2) (j : Fin 3) :
    Spec (CommRingCat.of (FirstNormalCurveRing r θ i j)) ⟶ projectiveCurve r θ :=
  principalImmersion (CycleQ2GeometricAffineProjectiveCharts.firstAffineChart r θ)
    (firstAffineCurveMap r θ (firstJacobian r θ i j))

def secondNormalCurveImmersion (r θ : ℂ) (i : Fin 2) (j : Fin 3) :
    Spec (CommRingCat.of (SecondNormalCurveRing r θ i j)) ⟶ projectiveCurve r θ :=
  principalImmersion (CycleQ2GeometricAffineProjectiveCharts.secondAffineChart r θ)
    (secondAffineCurveMap r θ (secondJacobian r θ i j))

instance firstNormalCurveImmersion_isOpenImmersion (r θ : ℂ) (i : Fin 2) (j : Fin 3) :
    IsOpenImmersion (firstNormalCurveImmersion r θ i j) := by
  dsimp [firstNormalCurveImmersion]
  infer_instance

instance secondNormalCurveImmersion_isOpenImmersion (r θ : ℂ) (i : Fin 2) (j : Fin 3) :
    IsOpenImmersion (secondNormalCurveImmersion r θ i j) := by
  dsimp [secondNormalCurveImmersion]
  infer_instance

theorem firstNormalCurve_isPullback (r θ : ℂ) (i : Fin 2) (j : Fin 3) :
    IsPullback
      (Spec.map (CommRingCat.ofHom (firstNormalCurveMap r θ i j).toRingHom))
      (firstNormalCurveImmersion r θ i j)
      (principalImmersion (firstAffineChart r θ) (firstJacobian r θ i j))
      (curveToSurface r θ) := by
  rw [firstNormalCurveMap_eq]
  have h := (affinePrincipal_isPullback (firstAffineCurveMap r θ).toRingHom
    (firstJacobian r θ i j)).paste_vert (firstAffineChart_isPullback r θ)
  simpa only [principalImmersion,firstNormalCurveImmersion,Category.assoc,
    FirstNormalCurveRing,FirstNormalRing,NormalCurvePatch,NormalSurfacePatch,
    CurveAdjunctionPatch,AdjunctionPatch,firstAffineCurveMap,firstJacobian,firstEquations,
    AlgHom.toRingHom_eq_coe,RingHom.coe_coe] using h

theorem secondNormalCurve_isPullback (r θ : ℂ) (i : Fin 2) (j : Fin 3) :
    IsPullback
      (Spec.map (CommRingCat.ofHom (secondNormalCurveMap r θ i j).toRingHom))
      (secondNormalCurveImmersion r θ i j)
      (principalImmersion (secondAffineChart r θ) (secondJacobian r θ i j))
      (curveToSurface r θ) := by
  rw [secondNormalCurveMap_eq]
  have h := (affinePrincipal_isPullback (secondAffineCurveMap r θ).toRingHom
    (secondJacobian r θ i j)).paste_vert (secondAffineChart_isPullback r θ)
  simpa only [principalImmersion,secondNormalCurveImmersion,Category.assoc,
    SecondNormalCurveRing,SecondNormalRing,NormalCurvePatch,NormalSurfacePatch,
    CurveAdjunctionPatch,AdjunctionPatch,secondAffineCurveMap,secondJacobian,secondEquations,
    AlgHom.toRingHom_eq_coe,RingHom.coe_coe] using h

#print axioms affinePrincipal_isPullback
#print axioms firstNormalCurve_isPullback
#print axioms secondNormalCurve_isPullback

end CycleQ2GeometricSurfacePrincipalCurveCharts
end

end SurfacePrincipalCurveChartsPart

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2GeometricSurfacePrincipalCurveCharts
open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry MvPolynomial
open CycleQ2GeometricSurfaceCurveCharts CycleQ2GeometricSurfaceJacobianCharts
open CycleQ2GeometricLiteralSurface CycleQ2GeometricSurfaceAdjunction
open CycleQ2GeometricSurfaceDehomogenizedCharts CycleQ2GeometricSurfaceComplexRestriction
open CycleQ2GeometricAffineCurveCharts CycleQ2GeometricProjectiveCurve
open CycleQ2NormalConnecting CycleQ2SeedTrace
open CycleQ2GeometricDifferentialSheaf CycleQ2GeometricAffineChartSections
open CycleQ2GeometricDifferentialChartTransport
open CycleQ2GeometricSheafKaehlerMap

section ComplexSquare
variable {A B : Type} [CommRing A] [CommRing B] [Algebra ℂ A] [Algebra ℂ B]
variable {X Y : Scheme.{0}} (φ : A →ₐ[ℂ] B) (j : X ⟶ Y)
  (i : Spec (CommRingCat.of A) ⟶ Y) (k : Spec (CommRingCat.of B) ⟶ X)
  (fX : X ⟶ Spec (CommRingCat.of ℂ)) (fY : Y ⟶ Spec (CommRingCat.of ℂ))

theorem sourceChart_overComplex
    (hc : k ≫ j = Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ i)
    (hj : j ≫ fY = fX)
    (hi : i ≫ fY = Spec.map (CommRingCat.ofHom (algebraMap ℂ A))) :
    k ≫ fX = Spec.map (CommRingCat.ofHom (algebraMap ℂ B)) := by
  rw [← hj,← Category.assoc,hc,Category.assoc,hi,← Spec.map_comp]
  apply congrArg Spec.map
  ext c
  exact φ.commutes c

end ComplexSquare

def firstNormalCurveOpen (r θ : ℂ) (i : Fin 2) (j : Fin 3) : (projectiveCurve r θ).Opens :=
  (firstNormalCurveImmersion r θ i j).opensRange

def secondNormalCurveOpen (r θ : ℂ) (i : Fin 2) (j : Fin 3) : (projectiveCurve r θ).Opens :=
  (secondNormalCurveImmersion r θ i j).opensRange

def firstNormalCurveChart (r θ : ℂ) (i : Fin 2) (j : Fin 3) :
    (firstNormalCurveOpen r θ i j).toScheme ≅ Spec (CommRingCat.of (FirstNormalCurveRing r θ i j)) :=
  principalChart (CycleQ2GeometricAffineProjectiveCharts.firstAffineChart r θ)
    (firstAffineCurveMap r θ (firstJacobian r θ i j))

def secondNormalCurveChart (r θ : ℂ) (i : Fin 2) (j : Fin 3) :
    (secondNormalCurveOpen r θ i j).toScheme ≅ Spec (CommRingCat.of (SecondNormalCurveRing r θ i j)) :=
  principalChart (CycleQ2GeometricAffineProjectiveCharts.secondAffineChart r θ)
    (secondAffineCurveMap r θ (secondJacobian r θ i j))

theorem firstNormalCurveChart_inv_ι (r θ : ℂ) (i : Fin 2) (j : Fin 3) :
    (firstNormalCurveChart r θ i j).inv ≫ (firstNormalCurveOpen r θ i j).ι =
      firstNormalCurveImmersion r θ i j :=
  principalChart_inv_ι _ _

theorem secondNormalCurveChart_inv_ι (r θ : ℂ) (i : Fin 2) (j : Fin 3) :
    (secondNormalCurveChart r θ i j).inv ≫ (secondNormalCurveOpen r θ i j).ι =
      secondNormalCurveImmersion r θ i j :=
  principalChart_inv_ι _ _

theorem firstNormalCurveImmersion_overComplex (r θ : ℂ) (i : Fin 2) (j : Fin 3) :
    firstNormalCurveImmersion r θ i j ≫ projectiveToComplex r θ =
      Spec.map (CommRingCat.ofHom (algebraMap ℂ (FirstNormalCurveRing r θ i j))) := by
  apply sourceChart_overComplex (firstNormalCurveMap r θ i j) (curveToSurface r θ)
    (principalImmersion (firstAffineChart r θ) (firstJacobian r θ i j))
    (firstNormalCurveImmersion r θ i j) (projectiveToComplex r θ)
    (CycleQ2GeometricSurfaceCoefficients.projectiveToComplex r θ)
  · exact (firstNormalCurve_isPullback r θ i j).w.symm
  · exact curveToSurface_overComplex r θ
  · exact principalImmersion_overComplex (firstAffineChart r θ) (firstJacobian r θ i j)
      (CycleQ2GeometricSurfaceCoefficients.projectiveToComplex r θ)
      (CycleQ2GeometricSurfaceCoefficients.firstAffineChart_overComplex r θ)

theorem secondNormalCurveImmersion_overComplex (r θ : ℂ) (i : Fin 2) (j : Fin 3) :
    secondNormalCurveImmersion r θ i j ≫ projectiveToComplex r θ =
      Spec.map (CommRingCat.ofHom (algebraMap ℂ (SecondNormalCurveRing r θ i j))) := by
  apply sourceChart_overComplex (secondNormalCurveMap r θ i j) (curveToSurface r θ)
    (principalImmersion (secondAffineChart r θ) (secondJacobian r θ i j))
    (secondNormalCurveImmersion r θ i j) (projectiveToComplex r θ)
    (CycleQ2GeometricSurfaceCoefficients.projectiveToComplex r θ)
  · exact (secondNormalCurve_isPullback r θ i j).w.symm
  · exact curveToSurface_overComplex r θ
  · exact principalImmersion_overComplex (secondAffineChart r θ) (secondJacobian r θ i j)
      (CycleQ2GeometricSurfaceCoefficients.projectiveToComplex r θ)
      (CycleQ2GeometricSurfaceCoefficients.secondAffineChart_overComplex r θ)

theorem firstNormalCurveChart_overComplex (r θ : ℂ) (i : Fin 2) (j : Fin 3) :
    (firstNormalCurveChart r θ i j).inv ≫ (firstNormalCurveOpen r θ i j).ι ≫
      projectiveToComplex r θ =
      Spec.map (CommRingCat.ofHom (algebraMap ℂ (FirstNormalCurveRing r θ i j))) := by
  rw [← Category.assoc,firstNormalCurveChart_inv_ι]
  exact firstNormalCurveImmersion_overComplex r θ i j

theorem secondNormalCurveChart_overComplex (r θ : ℂ) (i : Fin 2) (j : Fin 3) :
    (secondNormalCurveChart r θ i j).inv ≫ (secondNormalCurveOpen r θ i j).ι ≫
      projectiveToComplex r θ =
      Spec.map (CommRingCat.ofHom (algebraMap ℂ (SecondNormalCurveRing r θ i j))) := by
  rw [← Category.assoc,secondNormalCurveChart_inv_ι]
  exact secondNormalCurveImmersion_overComplex r θ i j

def firstNormalCurveKaehlerFrame (r θ : ℂ) (i : Fin 2) (j : Fin 3) :
    KaehlerDifferential ℂ (FirstNormalCurveRing r θ i j) ≃ₗ[FirstNormalCurveRing r θ i j]
      FirstNormalCurveRing r θ i j :=
  normalCurveKaehlerEquiv (firstQuadric r) (firstCubic θ)
    (firstSurfaceDehomogenize (originalG1 r)) (firstSurfaceDehomogenize originalG2)
    (firstSurfaceDehomogenize (thetaK θ)) i j

def secondNormalCurveKaehlerFrame (r θ : ℂ) (i : Fin 2) (j : Fin 3) :
    KaehlerDifferential ℂ (SecondNormalCurveRing r θ i j) ≃ₗ[SecondNormalCurveRing r θ i j]
      SecondNormalCurveRing r θ i j :=
  normalCurveKaehlerEquiv (secondQuadric r) (secondCubic θ)
    (secondSurfaceDehomogenize (originalG1 r)) (secondSurfaceDehomogenize originalG2)
    (secondSurfaceDehomogenize (thetaK θ)) i j

def firstNormalCurveDifferentialIso (r θ : ℂ) (i : Fin 2) (j : Fin 3) :
    (projectiveDifferentialSheaf r θ).over (firstNormalCurveOpen r θ i j) ≅
      ChartStructureModule (X := projectiveCurve r θ) (U := firstNormalCurveOpen r θ i j) :=
  chartFrameIso (firstNormalCurveChart r θ i j) (projectiveToComplex r θ)
    (firstNormalCurveChart_overComplex r θ i j) (firstNormalCurveKaehlerFrame r θ i j)

def secondNormalCurveDifferentialIso (r θ : ℂ) (i : Fin 2) (j : Fin 3) :
    (projectiveDifferentialSheaf r θ).over (secondNormalCurveOpen r θ i j) ≅
      ChartStructureModule (X := projectiveCurve r θ) (U := secondNormalCurveOpen r θ i j) :=
  chartFrameIso (secondNormalCurveChart r θ i j) (projectiveToComplex r θ)
    (secondNormalCurveChart_overComplex r θ i j) (secondNormalCurveKaehlerFrame r θ i j)

section FrameCoordinate
variable {X : Scheme.{0}} {U : X.Opens} {A : Type} [CommRing A] [Algebra ℂ A]
  (e : U.toScheme ≅ Spec (CommRingCat.of A))
  (f : X ⟶ Spec (CommRingCat.of ℂ))
  (h : e.inv ≫ U.ι ≫ f = Spec.map (CommRingCat.ofHom (algebraMap ℂ A)))
  (frame : KaehlerDifferential ℂ A ≃ₗ[A] A)

theorem chartFrameIso_inv_one_of_coordinate (a : A)
    (ha : frame (KaehlerDifferential.D ℂ A a)=1) (V : Over U) :
    (chartFrameIso e f h frame).inv.val.app (op V) (1 : Γ(X,V.left)) =
      (universalDifferential X.sheaf (schemeCoefficient f)).d (chartSection e V a) := by
  have hf : frame.symm 1 = KaehlerDifferential.D ℂ A a := by
    apply frame.injective
    rw [LinearEquiv.apply_symm_apply,ha]
  rw [chartFrameIso_inv_one_subopen,hf]
  exact sectionLift_D X.sheaf (schemeCoefficient f)
    (differentialSheaf X.sheaf (schemeCoefficient f))
    (universalDifferential X.sheaf (schemeCoefficient f)) V.left
    (chartSection e V) (chartSection_complex e f h V) a

end FrameCoordinate

def firstNormalCurveCoordinate (r θ : ℂ) (i : Fin 2) (j : Fin 3) :
    FirstNormalCurveRing r θ i j :=
  normalCoefficientMap (firstQuadric r) (firstCubic θ)
    (firstSurfaceDehomogenize (originalG1 r)) (firstSurfaceDehomogenize originalG2)
    (firstSurfaceDehomogenize (thetaK θ)) i j (includeCurve (X j))

def secondNormalCurveCoordinate (r θ : ℂ) (i : Fin 2) (j : Fin 3) :
    SecondNormalCurveRing r θ i j :=
  normalCoefficientMap (secondQuadric r) (secondCubic θ)
    (secondSurfaceDehomogenize (originalG1 r)) (secondSurfaceDehomogenize originalG2)
    (secondSurfaceDehomogenize (thetaK θ)) i j (includeCurve (X j))

/-- The actual sheaf frame has precisely the coordinate differential used
in local adjunction, on every subopen of the actual first Jacobian chart. -/
theorem firstNormalCurveDifferentialIso_inv_one (r θ : ℂ) (i : Fin 2) (j : Fin 3)
    (V : Over (firstNormalCurveOpen r θ i j)) :
    (firstNormalCurveDifferentialIso r θ i j).inv.val.app (op V)
      (1 : Γ(projectiveCurve r θ,V.left)) =
      (universalDifferential (projectiveCurve r θ).sheaf
        (schemeCoefficient (projectiveToComplex r θ))).d
          (chartSection (firstNormalCurveChart r θ i j) V
            (firstNormalCurveCoordinate r θ i j)) := by
  apply chartFrameIso_inv_one_of_coordinate
  exact normalCurveKaehlerEquiv_coordinate _ _ _ _ _ i j

/-- The second chart preserves the same literal coordinate generator. -/
theorem secondNormalCurveDifferentialIso_inv_one (r θ : ℂ) (i : Fin 2) (j : Fin 3)
    (V : Over (secondNormalCurveOpen r θ i j)) :
    (secondNormalCurveDifferentialIso r θ i j).inv.val.app (op V)
      (1 : Γ(projectiveCurve r θ,V.left)) =
      (universalDifferential (projectiveCurve r θ).sheaf
        (schemeCoefficient (projectiveToComplex r θ))).d
          (chartSection (secondNormalCurveChart r θ i j) V
            (secondNormalCurveCoordinate r θ i j)) := by
  apply chartFrameIso_inv_one_of_coordinate
  exact normalCurveKaehlerEquiv_coordinate _ _ _ _ _ i j

#print axioms firstNormalCurveChart_overComplex
#print axioms secondNormalCurveChart_overComplex
#print axioms firstNormalCurveDifferentialIso
#print axioms secondNormalCurveDifferentialIso
#print axioms chartFrameIso_inv_one_of_coordinate
#print axioms firstNormalCurveDifferentialIso_inv_one
#print axioms secondNormalCurveDifferentialIso_inv_one

end CycleQ2GeometricSurfacePrincipalCurveCharts
end

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2GeometricSurfaceExteriorSections

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry Module
open CycleQ2GeometricDifferentialSheaf CycleQ2GeometricAffineChartSections
open CycleQ2GeometricDifferentialChartTransport CycleQ2GeometricSheafKaehlerMap
open CycleQ2GeometricFunctionalDifferentials CycleQ2GeometricSurfaceAdjunction

variable {X : Scheme.{0}} {U : X.Opens} {A : Type} [CommRing A] [Algebra ℂ A]
  (e : U.toScheme ≅ Spec (CommRingCat.of A))
  (f : X ⟶ Spec (CommRingCat.of ℂ))
  (h : e.inv ≫ U.ι ≫ f = Spec.map (CommRingCat.ofHom (algebraMap ℂ A)))

/-- The actual map from affine Kähler forms to sheaf sections on a subopen. -/
def chartKaehlerSection (V : Over U) :
    KaehlerDifferential ℂ A →+ (ChartDifferentialModule f).val.obj (op V) :=
  sectionLift X.sheaf (schemeCoefficient f)
    (differentialSheaf X.sheaf (schemeCoefficient f))
    (universalDifferential X.sheaf (schemeCoefficient f)) V.left
    (chartSection e V) (chartSection_complex e f h V)

theorem chartCoefficientMap_sectionLift_subopen
    (l : KaehlerDifferential ℂ A →ₗ[A] A) (V : Over U) (ω : KaehlerDifferential ℂ A) :
    (CycleQ2GeometricFunctionalDifferentials.chartCoefficientMap e f h l).val.app (op V)
        (chartKaehlerSection e f h V ω) = chartSection e V (l ω) := by
  have hr : (ChartDifferentialModule f).val.map (toChartTop V).op
      (chartKaehlerSection e f h (chartTop U) ω) = chartKaehlerSection e f h V ω :=
    sectionLift_restriction X.sheaf (schemeCoefficient f)
      (differentialSheaf X.sheaf (schemeCoefficient f))
      (universalDifferential X.sheaf (schemeCoefficient f)) U
      (chartSection e (chartTop U)) (chartSection_complex e f h (chartTop U))
      V.left V.hom.le (chartSection e V) (chartSection_complex e f h V)
      (chartSection_naturality e (toChartTop V)) ω
  calc
    _ = (CycleQ2GeometricFunctionalDifferentials.chartCoefficientMap e f h l).val.app (op V)
        ((ChartDifferentialModule f).val.map (toChartTop V).op
          (chartKaehlerSection e f h (chartTop U) ω)) := congrArg _ hr.symm
    _ = (ChartStructureModule (X := X) (U := U)).val.map (toChartTop V).op
        ((CycleQ2GeometricFunctionalDifferentials.chartCoefficientMap e f h l).val.app
          (op (chartTop U)) (chartKaehlerSection e f h (chartTop U) ω)) :=
      PresheafOfModules.naturality_apply
        (CycleQ2GeometricFunctionalDifferentials.chartCoefficientMap e f h l).val
        (toChartTop V).op (chartKaehlerSection e f h (chartTop U) ω)
    _ = (ChartStructureModule (X := X) (U := U)).val.map (toChartTop V).op
        (chartSection e (chartTop U) (l ω)) :=
      congrArg ((ChartStructureModule (X := X) (U := U)).val.map (toChartTop V).op)
        (CycleQ2GeometricFunctionalDifferentials.chartCoefficientMap_sectionLift e f h l ω)
    _ = chartSection e V (l ω) := chartSection_naturality e (toChartTop V) (l ω)

theorem chartSectionBasis_repr_sectionLift
    (b : Basis (Fin 2) A (KaehlerDifferential ℂ A)) (V : Over U)
    (ω : KaehlerDifferential ℂ A) (i : Fin 2) :
    (chartSectionBasis e f h b V).repr (chartKaehlerSection e f h V ω) i =
      chartSection e V (b.repr ω i) :=
  chartCoefficientMap_sectionLift_subopen e f h (b.coord i) V ω

/-- The exterior-square map obtained from the actual section lift. Its
formula on every wedge below proves its independence from basis choices. -/
def chartExteriorSection (b : Basis (Fin 2) A (KaehlerDifferential ℂ A)) (V : Over U) :
    (⋀[A]^2 (KaehlerDifferential ℂ A)) →ₛₗ[chartSection e V]
      (⋀[Γ(X,V.left)]^2 ((ChartDifferentialModule f).val.obj (op V))) where
  toFun ω := chartSection e V (determinantEquiv b ω) •
    exteriorPower.ιMulti Γ(X,V.left) 2 (chartSectionBasis e f h b V)
  map_add' x y := by simp only [map_add,add_smul]
  map_smul' a x := by simp only [map_smul,smul_eq_mul,map_mul,mul_smul]

theorem chartExteriorSection_coordinate
    (b : Basis (Fin 2) A (KaehlerDifferential ℂ A)) (V : Over U)
    (ω : ⋀[A]^2 (KaehlerDifferential ℂ A)) :
    determinantEquiv (chartSectionBasis e f h b V) (chartExteriorSection e f h b V ω) =
      chartSection e V (determinantEquiv b ω) := by
  change determinantEquiv (chartSectionBasis e f h b V)
    (chartSection e V (determinantEquiv b ω) •
      exteriorPower.ιMulti Γ(X,V.left) 2 (chartSectionBasis e f h b V)) = _
  rw [map_smul,determinantEquiv_wedge,smul_eq_mul,mul_one]

/-- The transported exterior map is the actual wedge of the actual
transported one-forms, on every subopen of the chart. -/
theorem chartExteriorSection_wedge
    (b : Basis (Fin 2) A (KaehlerDifferential ℂ A)) (V : Over U)
    (ω η : KaehlerDifferential ℂ A) :
    chartExteriorSection e f h b V (exteriorPower.ιMulti A 2 ![ω,η]) =
      exteriorPower.ιMulti Γ(X,V.left) 2
        ![chartKaehlerSection e f h V ω,chartKaehlerSection e f h V η] := by
  apply (determinantEquiv (chartSectionBasis e f h b V)).injective
  rw [chartExteriorSection_coordinate,determinantEquiv_pair,determinantEquiv_pair]
  simp only [chartSectionBasis_repr_sectionLift,map_sub,map_mul]

end CycleQ2GeometricSurfaceExteriorSections

namespace CycleQ2GeometricSurfaceExteriorSections

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry Module
open CycleQ2GeometricDifferentialSheaf CycleQ2GeometricAffineChartSections
open CycleQ2GeometricDifferentialChartTransport CycleQ2GeometricSheafKaehlerMap
open CycleQ2GeometricFunctionalDifferentials CycleQ2GeometricSurfaceAdjunction

variable {X : Scheme.{0}} {U : X.Opens} {A : Type} [CommRing A] [Algebra ℂ A]
  (e : U.toScheme ≅ Spec (CommRingCat.of A))
  (f : X ⟶ Spec (CommRingCat.of ℂ))
  (h : e.inv ≫ U.ι ≫ f = Spec.map (CommRingCat.ofHom (algebraMap ℂ A)))

theorem chartExteriorSection_basisIndependent
    (b₁ b₂ : Basis (Fin 2) A (KaehlerDifferential ℂ A)) (V : Over U)
    (ω : ⋀[A]^2 (KaehlerDifferential ℂ A)) :
    chartExteriorSection e f h b₁ V ω = chartExteriorSection e f h b₂ V ω := by
  have hω : ω ∈ Submodule.span A (Set.range (exteriorPower.ιMulti A 2)) := by
    rw [exteriorPower.ιMulti_span]
    trivial
  induction hω using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨a,rfl⟩ := hx
      have ha : a = ![a 0,a 1] := by funext j; fin_cases j <;> rfl
      rw [ha,chartExteriorSection_wedge,chartExteriorSection_wedge]
  | zero => simp only [map_zero]
  | add x y _ _ hx hy => simp only [map_add,hx,hy]
  | smul a x _ hx => simp only [map_smulₛₗ,hx]

section Residue

variable (v : Fin 2 → CycleQ2GeometricSurfaceAdjunction.SurfacePoly)
  (n t : CycleQ2GeometricSurfaceAdjunction.SurfacePoly)
  (eR : U.toScheme ≅ Spec (CommRingCat.of (AdjunctionPatch v n t)))
  (hR : eR.inv ≫ U.ι ≫ f =
    Spec.map (CommRingCat.ofHom (algebraMap ℂ (AdjunctionPatch v n t))))

/-- The residue determinant coordinate on the actual differential-sheaf
sections, normalized by the actual localized augmented Jacobian. -/
def chartResidueCoordinate (V : Over U) :
    (⋀[Γ(X,V.left)]^2 ((ChartDifferentialModule f).val.obj (op V))) ≃ₗ[
      Γ(X,V.left)] Γ(X,V.left) :=
  (determinantEquiv (chartSectionBasis eR f hR (localSurfaceKaehlerBasis v n t) V)).trans
    (LinearEquiv.smulOfUnit (Units.map (chartSection eR V).toMonoidHom
      (IsLocalization.Away.algebraMap_isUnit (S := AdjunctionPatch v n t)
        (augmentedJacobian v n t)).unit))

theorem chartResidueCoordinate_apply (V : Over U)
    (ω : ⋀[Γ(X,V.left)]^2 ((ChartDifferentialModule f).val.obj (op V))) :
    chartResidueCoordinate f v n t eR hR V ω =
      chartSection eR V (algebraMap (SurfaceChartRing v) (AdjunctionPatch v n t)
        (augmentedJacobian v n t)) *
      determinantEquiv (chartSectionBasis eR f hR (localSurfaceKaehlerBasis v n t) V) ω := by
  change chartSection eR V
    (↑(IsLocalization.Away.algebraMap_isUnit (S := AdjunctionPatch v n t)
      (augmentedJacobian v n t)).unit) * _ = _
  rw [IsUnit.unit_spec]
  rfl

/-- Every affine top form is carried with exactly its original residue
coordinate; this includes the coefficient of the canonical generator. -/
theorem chartResidueCoordinate_exteriorSection (V : Over U)
    (ω : ⋀[AdjunctionPatch v n t]^2 (KaehlerDifferential ℂ (AdjunctionPatch v n t))) :
    chartResidueCoordinate f v n t eR hR V
      (chartExteriorSection eR f hR (localSurfaceKaehlerBasis v n t) V ω) =
      chartSection eR V (localSurfaceDeterminantEquiv v n t ω) := by
  rw [chartResidueCoordinate_apply,chartExteriorSection_coordinate,← map_mul]
  congr 1

/-- The actual wedge of two transported one-forms satisfies the same
augmented determinant formula as the original affine forms. -/
theorem chartResidueCoordinate_wedge (V : Over U)
    (ω η : KaehlerDifferential ℂ (AdjunctionPatch v n t)) :
    chartResidueCoordinate f v n t eR hR V
      (exteriorPower.ιMulti Γ(X,V.left) 2
        ![chartKaehlerSection eR f hR V ω,chartKaehlerSection eR f hR V η]) =
      chartSection eR V (localSurfaceDeterminantEquiv v n t
        (exteriorPower.ιMulti (AdjunctionPatch v n t) 2 ![ω,η])) := by
  rw [← chartExteriorSection_wedge eR f hR (localSurfaceKaehlerBasis v n t)]
  exact chartResidueCoordinate_exteriorSection f v n t eR hR V _

/-- The local residue is an actual exterior form in the sheaf section
module, with the normalization inherited from the equation determinant. -/
def chartResidueSection (V : Over U) :
    ⋀[Γ(X,V.left)]^2 ((ChartDifferentialModule f).val.obj (op V)) :=
  chartExteriorSection eR f hR (localSurfaceKaehlerBasis v n t) V
    (localSurfaceResidueForm v n t)

@[simp] theorem chartResidueSection_normalization (V : Over U) :
    chartResidueCoordinate f v n t eR hR V (chartResidueSection f v n t eR hR V) = 1 := by
  rw [chartResidueSection,chartResidueCoordinate_exteriorSection,
    localSurfaceResidueForm_normalization,map_one]

end Residue

#print axioms chartExteriorSection_wedge
#print axioms chartExteriorSection_basisIndependent
#print axioms chartResidueCoordinate_wedge
#print axioms chartResidueSection_normalization

end CycleQ2GeometricSurfaceExteriorSections

end
