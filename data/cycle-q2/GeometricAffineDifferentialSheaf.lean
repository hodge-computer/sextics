import Proposal.GeometricDifferentialSheaf
import Proposal.GeometricLocalizedDifferentials

/-!
# A differential frame induces a derivation on the actual structure sheaf

On every stalk the coefficient of a differential is defined by the genuine
localization theorem for Kähler modules. The fraction rule shows that these
pointwise coefficients remain regular sections; restriction compatibility
then follows from the actual definition of structure-sheaf restriction.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2GeometricStructureDerivation

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
  CycleQ2GeometricDifferentialSheaf CycleQ2GeometricLocalizedDifferentials

variable {A : Type} [CommRing A] [Algebra ℂ A]

instance localizationComplexTower (M : Submonoid A) :
    IsScalarTower ℂ A (LocalizedModule M A) where
  smul_assoc c a := by
    rintro ⟨b, s⟩
    simp only [LocalizedModule.smul'_mk, smul_assoc]

theorem localizedModule_mk_eq (M : Submonoid A) (a : A) (s : M) :
    LocalizedModule.mk a s = IsLocalization.mk' (LocalizedModule M A) a s := by
  rw [IsLocalization.mk'_eq_mk', IsLocalizedModule.mk_eq_mk']
  rfl

/-- The actual local coefficient of the differential of a fraction is again
a fraction, with its original denominator squared. -/
theorem coefficientDerivation_fraction (M : Submonoid A)
    (e : KaehlerDifferential ℂ A ≃ₗ[A] A) (a : A) (s : M) :
    coefficientDerivation M (LocalizedModule M A) e (LocalizedModule.mk a s) =
      LocalizedModule.mk
        ((s : A) * e (KaehlerDifferential.D ℂ A a) -
          a * e (KaehlerDifferential.D ℂ A (s : A))) (s * s) := by
  rw [localizedModule_mk_eq, localizedModule_mk_eq]
  change localEquiv M (LocalizedModule M A) e
    (KaehlerDifferential.D ℂ (LocalizedModule M A) (IsLocalization.mk' _ a s)) = _
  rw [localEquiv_D_fraction, ← map_mul, ← map_mul, ← map_sub, pow_two,
    ← IsLocalization.mk'_mul, one_mul, mul_comm, ← IsLocalization.mk'_eq_mul_mk'_one]

abbrev AffineSections (U : Opens (PrimeSpectrum.Top A)) :=
  (Spec.structureSheaf A).obj.obj (op U)

/-- Local differentiation of a regular section remains a regular section. -/
theorem coefficient_isLocallyFraction (e : KaehlerDifferential ℂ A ≃ₗ[A] A)
    (U : Opens (PrimeSpectrum.Top A)) (s : AffineSections U) :
    (StructureSheaf.isLocallyFraction A A).pred
      (fun x : U => coefficientDerivation x.1.asIdeal.primeCompl
        (StructureSheaf.Localizations A x.1) e (s.1 x)) := by
  intro x
  obtain ⟨V, hxV, i, a, b, hab⟩ := s.2 x
  refine ⟨V, hxV, i,
    b * e (KaehlerDifferential.D ℂ A a) - a * e (KaehlerDifferential.D ℂ A b),
    b * b, ?_⟩
  intro y
  obtain ⟨hb, hy⟩ := hab y
  refine ⟨y.1.asIdeal.primeCompl.mul_mem hb hb, ?_⟩
  change coefficientDerivation y.1.asIdeal.primeCompl
    (StructureSheaf.Localizations A y.1) e (s.1 (i y)) = _
  exact (congrArg (coefficientDerivation y.1.asIdeal.primeCompl
    (StructureSheaf.Localizations A y.1) e) hy).trans
      (coefficientDerivation_fraction y.1.asIdeal.primeCompl e a ⟨b, hb⟩)

/-- The derivative is defined in the literal structure-sheaf section ring. -/
def sectionDerivative (e : KaehlerDifferential ℂ A ≃ₗ[A] A)
    (U : Opens (PrimeSpectrum.Top A)) (s : AffineSections U) : AffineSections U :=
  ⟨fun x => coefficientDerivation x.1.asIdeal.primeCompl
    (StructureSheaf.Localizations A x.1) e (s.1 x), coefficient_isLocallyFraction e U s⟩

theorem sectionDerivative_add (e : KaehlerDifferential ℂ A ≃ₗ[A] A)
    (U : Opens (PrimeSpectrum.Top A)) (s t : AffineSections U) :
    sectionDerivative e U (s + t) = sectionDerivative e U s + sectionDerivative e U t := by
  apply Subtype.ext
  funext x
  exact map_add (coefficientDerivation x.1.asIdeal.primeCompl
    (StructureSheaf.Localizations A x.1) e) (s.1 x) (t.1 x)

theorem sectionDerivative_mul (e : KaehlerDifferential ℂ A ≃ₗ[A] A)
    (U : Opens (PrimeSpectrum.Top A)) (s t : AffineSections U) :
    sectionDerivative e U (s * t) = s * sectionDerivative e U t + t * sectionDerivative e U s := by
  apply Subtype.ext
  funext x
  exact (coefficientDerivation x.1.asIdeal.primeCompl
    (StructureSheaf.Localizations A x.1) e).leibniz (s.1 x) (t.1 x)

theorem sectionDerivative_algebraMap (e : KaehlerDifferential ℂ A ≃ₗ[A] A)
    (U : Opens (PrimeSpectrum.Top A)) (a : A) :
    sectionDerivative e U (algebraMap A (AffineSections U) a) =
      algebraMap A (AffineSections U) (e (KaehlerDifferential.D ℂ A a)) := by
  apply Subtype.ext
  funext x
  exact coefficientDerivation_algebraMap x.1.asIdeal.primeCompl
    (StructureSheaf.Localizations A x.1) e a

theorem sectionDerivative_restrict (e : KaehlerDifferential ℂ A ≃ₗ[A] A)
    {U V : Opens (PrimeSpectrum.Top A)} (i : V ⟶ U) (s : AffineSections U) :
    sectionDerivative e V ((Spec.structureSheaf A).obj.map i.op s) =
      (Spec.structureSheaf A).obj.map i.op (sectionDerivative e U s) := rfl

def sectionDerivativeAddHom (e : KaehlerDifferential ℂ A ≃ₗ[A] A)
    (U : Opens (PrimeSpectrum.Top A)) : AffineSections U →+ AffineSections U :=
  AddMonoidHom.mk' (sectionDerivative e U) (sectionDerivative_add e U)

/-- The resulting derivation on the actual structure sheaf uses every open,
not just the selected coordinate or denominator charts. -/
def structureSheafDerivation (e : KaehlerDifferential ℂ A ≃ₗ[A] A) :
    (SheafOfModules.unit (ringSheaf (Spec.structureSheaf A))).val.Derivation'
      (coefficientMap (Spec.structureSheaf A)
        ((algebraMap A (AffineSections (⊤ : Opens (PrimeSpectrum.Top A)))).comp
          (algebraMap ℂ A))) where
  d {U} := sectionDerivativeAddHom e U.unop
  d_mul {U} a b := sectionDerivative_mul e U.unop a b
  d_map {_ _} i s := rfl
  d_app {U} c := by
    change sectionDerivative e U.unop
      (algebraMap A (AffineSections U.unop) (algebraMap ℂ A c)) = 0
    rw [sectionDerivative_algebraMap, Derivation.map_algebraMap, map_zero, map_zero]

@[simp] theorem structureSheafDerivation_algebraMap
    (e : KaehlerDifferential ℂ A ≃ₗ[A] A)
    (U : (Opens (PrimeSpectrum.Top A))ᵒᵖ) (a : A) :
    (structureSheafDerivation e).d (X := U) (algebraMap A (AffineSections U.unop) a) =
      algebraMap A (AffineSections U.unop) (e (KaehlerDifferential.D ℂ A a)) :=
  sectionDerivative_algebraMap e U.unop a

#print axioms coefficient_isLocallyFraction
#print axioms structureSheafDerivation
#print axioms structureSheafDerivation_algebraMap

end CycleQ2GeometricStructureDerivation

end

/-!
# Differentials of the actual affine structure sheaf

The scalar map on an affine scheme is the canonical complex algebra map
followed by its actual global-section map. Derivations into any sheaf of
structure modules are determined by their values on the global affine ring.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2GeometricAffineDifferentialSheaf

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
  CycleQ2GeometricDifferentialSheaf

variable (A : Type) [CommRing A] [Algebra ℂ A]

def affineCoefficient : ℂ →+* (Spec.structureSheaf A).obj.obj (op ⊤) :=
  (algebraMap A ((Spec.structureSheaf A).obj.obj (op ⊤))).comp (algebraMap ℂ A)

theorem affineCoefficientOn (U : Opens (PrimeSpectrum.Top A)) (c : ℂ) :
    coefficientOn (Spec.structureSheaf A) (affineCoefficient A) U c =
      algebraMap A ((Spec.structureSheaf A).obj.obj (op U)) (algebraMap ℂ A c) := rfl

theorem affineCoefficient_structureMorphism :
    CommRingCat.ofHom (affineCoefficient A) =
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫
        (Spec.map (CommRingCat.ofHom (algebraMap ℂ A))).appTop := by
  exact Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap ℂ A))

abbrev AffineModule := SheafOfModules.{0} (ringSheaf (Spec.structureSheaf A))

abbrev AffineDerivation (M : AffineModule A) :=
  M.val.Derivation' (coefficientMap (Spec.structureSheaf A) (affineCoefficient A))

abbrev AffineSections (U : Opens (PrimeSpectrum.Top A)) :=
  (Spec.structureSheaf A).obj.obj (op U)

variable {A}

private theorem derivation_basic_ext (M : AffineModule A) (d e : AffineDerivation A M)
    (h : ∀ a : A, d.d (X := op ⊤) (algebraMap A (AffineSections A ⊤) a) =
      e.d (X := op ⊤) (algebraMap A (AffineSections A ⊤) a))
    (f : A) (s : (Spec.structureSheaf A).obj.obj (op (PrimeSpectrum.basicOpen f))) :
    d.d s = e.d s := by
  have ha (a : A) :
      d.d (X := op (PrimeSpectrum.basicOpen f))
          (algebraMap A (AffineSections A (PrimeSpectrum.basicOpen f)) a) =
        e.d (X := op (PrimeSpectrum.basicOpen f))
          (algebraMap A (AffineSections A (PrimeSpectrum.basicOpen f)) a) := by
    have hx := congrArg (M.val.map (homOfLE
      (show PrimeSpectrum.basicOpen f ≤ ⊤ from le_top)).op) (h a)
    exact (d.d_map (homOfLE (show PrimeSpectrum.basicOpen f ≤ ⊤ from le_top)).op
      (algebraMap A (AffineSections A ⊤) a)).trans (hx.trans
        (e.d_map (homOfLE (show PrimeSpectrum.basicOpen f ≤ ⊤ from le_top)).op
          (algebraMap A (AffineSections A ⊤) a)).symm)
  obtain ⟨⟨a, b⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers f) s
  apply (IsLocalization.map_units
    ((Spec.structureSheaf A).obj.obj (op (PrimeSpectrum.basicOpen f))) b).isSMulRegular
      (M.val.obj (op (PrimeSpectrum.basicOpen f)))
  have hd := d.d_mul (IsLocalization.mk'
    ((Spec.structureSheaf A).obj.obj (op (PrimeSpectrum.basicOpen f))) a b)
      (algebraMap A (AffineSections A (PrimeSpectrum.basicOpen f)) b)
  have he := e.d_mul (IsLocalization.mk'
    ((Spec.structureSheaf A).obj.obj (op (PrimeSpectrum.basicOpen f))) a b)
      (algebraMap A (AffineSections A (PrimeSpectrum.basicOpen f)) b)
  have hd' := (congrArg (d.d (X := op (PrimeSpectrum.basicOpen f)))
    (IsLocalization.mk'_spec (AffineSections A (PrimeSpectrum.basicOpen f)) a b)).symm.trans hd
  have he' := (congrArg (e.d (X := op (PrimeSpectrum.basicOpen f)))
    (IsLocalization.mk'_spec (AffineSections A (PrimeSpectrum.basicOpen f)) a b)).symm.trans he
  rw [ha a, ha b] at hd'
  exact add_left_cancel (hd'.symm.trans he')

/-- A derivation into an arbitrary genuine sheaf of modules on an affine
scheme is determined by its values on the global affine ring. -/
theorem affineDerivation_ext (M : AffineModule A) (d e : AffineDerivation A M)
    (h : ∀ a : A, d.d (X := op ⊤) (algebraMap A (AffineSections A ⊤) a) =
      e.d (X := op ⊤) (algebraMap A (AffineSections A ⊤) a)) : d = e := by
  ext U s
  apply TopCat.Presheaf.IsSheaf.section_ext M.isSheaf
  intro x hx
  obtain ⟨f, hxf, hfU, a, ha⟩ := StructureSheaf.exists_const U.unop s x hx
  refine ⟨PrimeSpectrum.basicOpen f, hfU, hxf, ?_⟩
  change M.val.map (homOfLE hfU).op (d.d s) = M.val.map (homOfLE hfU).op (e.d s)
  exact (d.d_map (homOfLE hfU).op s).symm.trans
    ((derivation_basic_ext M d e h f _).trans (e.d_map (homOfLE hfU).op s))

instance globalAffineModule (M : AffineModule A) : Module A (M.val.obj (op ⊤)) :=
  Module.compHom _ (algebraMap A (AffineSections A ⊤))

instance globalComplexModule (M : AffineModule A) : Module ℂ (M.val.obj (op ⊤)) :=
  Module.compHom _ (algebraMap ℂ A)

instance globalComplexTower (M : AffineModule A) :
    IsScalarTower ℂ A (M.val.obj (op ⊤)) :=
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

instance globalAffineTower (M : AffineModule A) :
    IsScalarTower A (AffineSections A ⊤) (M.val.obj (op ⊤)) :=
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

/-- Restriction of a sheaf-valued derivation to the actual affine ring. -/
def globalDerivation (M : AffineModule A) (d : AffineDerivation A M) :
    Derivation ℂ A (M.val.obj (op ⊤)) where
  toFun a := d.d (algebraMap A (AffineSections A ⊤) a)
  map_add' a b := by rw [map_add, map_add]
  map_smul' c a := by
    change d.d (algebraMap A (AffineSections A ⊤) (c • a)) =
      algebraMap A (AffineSections A ⊤) (algebraMap ℂ A c) •
        d.d (algebraMap A (AffineSections A ⊤) a)
    rw [Algebra.smul_def, map_mul, d.d_mul]
    have hc := d.d_app (X := op ⊤) c
    change d.d (algebraMap A (AffineSections A ⊤) (algebraMap ℂ A c)) = 0 at hc
    rw [hc, smul_zero, add_zero]
  map_one_eq_zero' := by
    change d.d (algebraMap A (AffineSections A ⊤) 1) = 0
    rw [map_one, d.d_one]
  leibniz' a b := by
    change d.d (algebraMap A (AffineSections A ⊤) (a * b)) =
      algebraMap A (AffineSections A ⊤) a • d.d (algebraMap A (AffineSections A ⊤) b) +
        algebraMap A (AffineSections A ⊤) b • d.d (algebraMap A (AffineSections A ⊤) a)
    rw [map_mul, d.d_mul]

def globalKaehlerMap (M : AffineModule A) (d : AffineDerivation A M) :
    KaehlerDifferential ℂ A →ₗ[A] M.val.obj (op ⊤) :=
  (globalDerivation M d).liftKaehlerDifferential

theorem globalKaehlerMap_D (M : AffineModule A) (d : AffineDerivation A M) (a : A) :
    globalKaehlerMap M d (KaehlerDifferential.D ℂ A a) =
      d.d (algebraMap A (AffineSections A ⊤) a) :=
  (globalDerivation M d).liftKaehlerDifferential_comp_D a

def globalModuleMap {M N : AffineModule A} (f : M ⟶ N) :
    M.val.obj (op ⊤) →ₗ[A] N.val.obj (op ⊤) where
  toFun := f.val.app (op ⊤)
  map_add' := map_add _
  map_smul' a m := (f.val.app (op ⊤)).hom.map_smul
    (algebraMap A (AffineSections A ⊤) a) m

theorem globalKaehlerMap_naturality {M N : AffineModule A} (f : M ⟶ N)
    (d : AffineDerivation A M) :
    globalKaehlerMap N (d.postcomp f.val) =
      (globalModuleMap f).comp (globalKaehlerMap M d) := by
  apply Derivation.liftKaehlerDifferential_unique
  ext a
  change globalKaehlerMap N (d.postcomp f.val) (KaehlerDifferential.D ℂ A a) =
    globalModuleMap f (globalKaehlerMap M d (KaehlerDifferential.D ℂ A a))
  rw [globalKaehlerMap_D, globalKaehlerMap_D]
  rfl

def sectionsFromGlobal (M : AffineModule A) (m : M.val.obj (op ⊤)) : M.sections :=
  M.val.sectionsMk (fun U => M.val.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op m)
    (fun U V f => by rw [← M.val.map_comp_apply]; congr 2)

def unitMapFromGlobal (M : AffineModule A) (m : M.val.obj (op ⊤)) :
    SheafOfModules.unit (ringSheaf (Spec.structureSheaf A)) ⟶ M :=
  M.unitHomEquiv.symm (sectionsFromGlobal M m)

omit [Algebra ℂ A] in
theorem unitMapFromGlobal_apply (M : AffineModule A) (m : M.val.obj (op ⊤))
    (U : (Opens (PrimeSpectrum.Top A))ᵒᵖ) (a : AffineSections A U.unop) :
    (unitMapFromGlobal M m).val.app U a =
      a • M.val.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op m := rfl

omit [Algebra ℂ A] in
theorem unitMapFromGlobal_top (M : AffineModule A) (m : M.val.obj (op ⊤))
    (a : AffineSections A ⊤) :
    (unitMapFromGlobal M m).val.app (op ⊤) a = a • m := by
  rw [unitMapFromGlobal_apply]
  have hm : M.val.map (homOfLE (show (⊤ : Opens (PrimeSpectrum.Top A)) ≤ ⊤
      from le_top)).op m = m := by
    change M.val.presheaf.map (𝟙 (op ⊤)) m = m
    exact congrArg (fun f : M.val.presheaf.obj (op ⊤) ⟶ M.val.presheaf.obj (op ⊤) => f m)
      (M.val.presheaf.map_id (op ⊤))
  exact congrArg (fun z : M.val.obj (op ⊤) => a • z) hm

variable (A)

abbrev affineDifferentialSheaf : AffineModule A :=
  differentialSheaf (Spec.structureSheaf A) (affineCoefficient A)

abbrev affineUniversalDifferential : AffineDerivation A (affineDifferentialSheaf A) :=
  universalDifferential (Spec.structureSheaf A) (affineCoefficient A)

abbrev affineStructureModule : AffineModule A :=
  SheafOfModules.unit (ringSheaf (Spec.structureSheaf A))

variable {A}

def globalFrame (e : KaehlerDifferential ℂ A ≃ₗ[A] A) :
    (affineDifferentialSheaf A).val.obj (op ⊤) :=
  globalKaehlerMap (affineDifferentialSheaf A) (affineUniversalDifferential A) (e.symm 1)

def frameSheafMap (e : KaehlerDifferential ℂ A ≃ₗ[A] A) :
    affineStructureModule A ⟶ affineDifferentialSheaf A :=
  unitMapFromGlobal (affineDifferentialSheaf A) (globalFrame e)

def coefficientSheafMap (d : AffineDerivation A (affineStructureModule A)) :
    affineDifferentialSheaf A ⟶ affineStructureModule A :=
  differentialLift (Spec.structureSheaf A) (affineCoefficient A) (affineStructureModule A) d

theorem coefficientSheafMap_D (d : AffineDerivation A (affineStructureModule A))
    (U : (Opens (PrimeSpectrum.Top A))ᵒᵖ) (a : AffineSections A U.unop) :
    (coefficientSheafMap d).val.app U ((affineUniversalDifferential A).d a) = d.d a :=
  PresheafOfModules.Derivation.congr_d
    (differentialLift_fac (Spec.structureSheaf A) (affineCoefficient A)
      (affineStructureModule A) d) a

section Inverse

variable (e : KaehlerDifferential ℂ A ≃ₗ[A] A)
  (d : AffineDerivation A (affineStructureModule A))
  (hd : ∀ a : A, d.d (X := op ⊤) (algebraMap A (AffineSections A ⊤) a) =
    algebraMap A (AffineSections A ⊤) (e (KaehlerDifferential.D ℂ A a)))

private def globalCoefficientLinear :
    KaehlerDifferential ℂ A →ₗ[A] (affineStructureModule A).val.obj (op ⊤) where
  toFun ω := algebraMap A (AffineSections A ⊤) (e ω)
  map_add' ω η := by
    change algebraMap A (AffineSections A ⊤) (e (ω + η)) = _
    rw [map_add, map_add]
  map_smul' a ω := by
    change algebraMap A (AffineSections A ⊤) (e (a • ω)) =
      algebraMap A (AffineSections A ⊤) a * algebraMap A (AffineSections A ⊤) (e ω)
    rw [map_smul, smul_eq_mul, map_mul]

include hd

private theorem coefficientSheafMap_globalKaehler :
    (globalModuleMap (coefficientSheafMap d)).comp
        (globalKaehlerMap (affineDifferentialSheaf A) (affineUniversalDifferential A)) =
      globalCoefficientLinear e := by
  apply Derivation.liftKaehlerDifferential_unique
  ext a
  change (coefficientSheafMap d).val.app (op ⊤)
      (globalKaehlerMap (affineDifferentialSheaf A) (affineUniversalDifferential A)
        (KaehlerDifferential.D ℂ A a)) =
    algebraMap A (AffineSections A ⊤) (e (KaehlerDifferential.D ℂ A a))
  rw [globalKaehlerMap_D, coefficientSheafMap_D]
  exact hd a

theorem coefficientSheafMap_globalFrame :
    (coefficientSheafMap d).val.app (op ⊤) (globalFrame e) = (1 : AffineSections A ⊤) := by
  have h := LinearMap.congr_fun (coefficientSheafMap_globalKaehler e d hd) (e.symm 1)
  change (coefficientSheafMap d).val.app (op ⊤) (globalFrame e) =
    algebraMap A (AffineSections A ⊤) (e (e.symm 1)) at h
  simpa only [LinearEquiv.apply_symm_apply, map_one] using h

theorem frameSheafMap_coefficientSheafMap :
    frameSheafMap e ≫ coefficientSheafMap d = 𝟙 (affineStructureModule A) := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  change (coefficientSheafMap d).val.app U
      ((unitMapFromGlobal (affineDifferentialSheaf A) (globalFrame e)).val.app U a) = a
  rw [unitMapFromGlobal_apply, map_smul]
  rw [PresheafOfModules.naturality_apply, coefficientSheafMap_globalFrame e d hd]
  let b : AffineSections A U.unop := a
  change b * (Spec.structureSheaf A).obj.map
    (homOfLE (show U.unop ≤ ⊤ from le_top)).op (1 : AffineSections A ⊤) = b
  rw [map_one, mul_one]

theorem coefficientSheafMap_frameSheafMap :
    coefficientSheafMap d ≫ frameSheafMap e = 𝟙 (affineDifferentialSheaf A) := by
  apply differentialLift_unique (Spec.structureSheaf A) (affineCoefficient A)
  apply affineDerivation_ext
  intro a
  change (unitMapFromGlobal (affineDifferentialSheaf A) (globalFrame e)).val.app (op ⊤)
      ((coefficientSheafMap d).val.app (op ⊤)
        ((affineUniversalDifferential A).d (algebraMap A (AffineSections A ⊤) a))) =
    (affineUniversalDifferential A).d (algebraMap A (AffineSections A ⊤) a)
  rw [coefficientSheafMap_D, hd a, unitMapFromGlobal_top]
  change e (KaehlerDifferential.D ℂ A a) •
      globalKaehlerMap (affineDifferentialSheaf A) (affineUniversalDifferential A) (e.symm 1) = _
  rw [← map_smul]
  have he : e (KaehlerDifferential.D ℂ A a) • e.symm 1 = KaehlerDifferential.D ℂ A a := by
    apply e.injective
    rw [map_smul, LinearEquiv.apply_symm_apply, smul_eq_mul, mul_one]
  rw [he, globalKaehlerMap_D]

def affineDifferentialIsoOfDerivation :
    affineDifferentialSheaf A ≅ affineStructureModule A where
  hom := coefficientSheafMap d
  inv := frameSheafMap e
  hom_inv_id := coefficientSheafMap_frameSheafMap e d hd
  inv_hom_id := frameSheafMap_coefficientSheafMap e d hd

end Inverse

/-! ## The derivation on actual regular sections -/

open CycleQ2GeometricLocalizedDifferentials

private def fiberDerivative (e : KaehlerDifferential ℂ A ≃ₗ[A] A)
    (p : PrimeSpectrum.Top A) : StructureSheaf.Localizations A p → StructureSheaf.Localizations A p :=
  coefficientDerivation p.asIdeal.primeCompl (StructureSheaf.Localizations A p) e

omit [Algebra ℂ A] in
private theorem localizedModule_mk_eq (M : Submonoid A) (a : A) (s : M) :
    LocalizedModule.mk a s = IsLocalization.mk' (LocalizedModule M A) a s := by
  rw [IsLocalization.mk'_eq_mk', IsLocalizedModule.mk_eq_mk']
  rfl

private theorem fiberDerivative_mk (e : KaehlerDifferential ℂ A ≃ₗ[A] A)
    (p : PrimeSpectrum.Top A) (a : A) (s : p.asIdeal.primeCompl) :
    fiberDerivative e p (LocalizedModule.mk a s) =
      LocalizedModule.mk ((s : A) * e (KaehlerDifferential.D ℂ A a) -
        a * e (KaehlerDifferential.D ℂ A (s : A))) (s * s) := by
  rw [localizedModule_mk_eq, localizedModule_mk_eq]
  change localEquiv p.asIdeal.primeCompl (StructureSheaf.Localizations A p) e
    (KaehlerDifferential.D ℂ (StructureSheaf.Localizations A p)
      (IsLocalization.mk' _ a s)) = _
  rw [localEquiv_D_fraction, ← map_mul, ← map_mul, ← map_sub, pow_two,
    ← IsLocalization.mk'_mul, one_mul, mul_comm, ← IsLocalization.mk'_eq_mul_mk'_one]

/-- Differentiation of a regular section, performed in its actual prime
localizations. The fraction rule proves the result remains a regular section. -/
def sectionDerivative (e : KaehlerDifferential ℂ A ≃ₗ[A] A)
    (U : Opens (PrimeSpectrum.Top A)) : AffineSections A U →+ AffineSections A U where
  toFun s := ⟨fun p => fiberDerivative e p.1 (s.1 p), by
    intro p
    obtain ⟨V, hpV, i, a, b, h⟩ := s.2 p
    refine ⟨V, hpV, i, b * e (KaehlerDifferential.D ℂ A a) -
      a * e (KaehlerDifferential.D ℂ A b), b * b, fun q => ?_⟩
    obtain ⟨hbq, hq⟩ := h q
    exact ⟨q.1.asIdeal.primeCompl.mul_mem hbq hbq,
      (congrArg (fiberDerivative e q.1) hq).trans (fiberDerivative_mk e q.1 a ⟨b, hbq⟩)⟩⟩
  map_zero' := by
    apply Subtype.ext
    funext p
    exact map_zero (coefficientDerivation p.1.asIdeal.primeCompl
      (StructureSheaf.Localizations A p.1) e)
  map_add' s t := by
    apply Subtype.ext
    funext p
    exact map_add (coefficientDerivation p.1.asIdeal.primeCompl
      (StructureSheaf.Localizations A p.1) e) (s.1 p) (t.1 p)

theorem sectionDerivative_algebraMap (e : KaehlerDifferential ℂ A ≃ₗ[A] A)
    (U : Opens (PrimeSpectrum.Top A)) (a : A) :
    sectionDerivative e U (algebraMap A (AffineSections A U) a) =
      algebraMap A (AffineSections A U) (e (KaehlerDifferential.D ℂ A a)) := by
  apply Subtype.ext
  funext p
  exact coefficientDerivation_algebraMap p.1.asIdeal.primeCompl
    (StructureSheaf.Localizations A p.1) e a

/-- The localized coefficient derivations form one genuine derivation of
the structure sheaf, natural on all opens and vanishing on complex scalars. -/
def regularSectionDerivation (e : KaehlerDifferential ℂ A ≃ₗ[A] A) :
    AffineDerivation A (affineStructureModule A) where
  d {U} := sectionDerivative e U.unop
  d_mul {U} s t := by
    apply Subtype.ext
    funext p
    exact (coefficientDerivation p.1.asIdeal.primeCompl
      (StructureSheaf.Localizations A p.1) e).leibniz (s.1 p) (t.1 p)
  d_map {_ _} _ _ := rfl
  d_app {U} c := by
    change sectionDerivative e U.unop
      (algebraMap A (AffineSections A U.unop) (algebraMap ℂ A c)) = 0
    rw [sectionDerivative_algebraMap, (KaehlerDifferential.D ℂ A).map_algebraMap,
      map_zero, map_zero]


/-- The actual structure-sheaf derivation obtained from the affine Kähler
frame. Its existence is proved by differentiation of locally regular fractions. -/
def affineFrameDerivation (e : KaehlerDifferential ℂ A ≃ₗ[A] A) :
    AffineDerivation A (affineStructureModule A) :=
  CycleQ2GeometricStructureDerivation.structureSheafDerivation e

@[simp] theorem affineFrameDerivation_algebraMap
    (e : KaehlerDifferential ℂ A ≃ₗ[A] A)
    (U : (Opens (PrimeSpectrum.Top A))ᵒᵖ) (a : A) :
    (affineFrameDerivation e).d (X := U) (algebraMap A (AffineSections A U.unop) a) =
      algebraMap A (AffineSections A U.unop) (e (KaehlerDifferential.D ℂ A a)) :=
  CycleQ2GeometricStructureDerivation.structureSheafDerivation_algebraMap e U a

/-- The two constructions of the regular-section derivative have the same
actual stalk values. This retains both public interfaces after reconciliation. -/
theorem sectionDerivative_eq_structureSectionDerivative
    (e : KaehlerDifferential ℂ A ≃ₗ[A] A)
    (U : Opens (PrimeSpectrum.Top A)) (a : AffineSections A U) :
    sectionDerivative e U a =
      CycleQ2GeometricStructureDerivation.sectionDerivative e U a := by
  apply Subtype.ext
  funext p
  rfl

/-- The incoming and local sheaf-valued coefficient derivations agree. -/
theorem regularSectionDerivation_eq_affineFrameDerivation
    (e : KaehlerDifferential ℂ A ≃ₗ[A] A) :
    regularSectionDerivation e = affineFrameDerivation e := by
  apply affineDerivation_ext
  intro a
  change sectionDerivative e ⊤ (algebraMap A (AffineSections A ⊤) a) =
    (affineFrameDerivation e).d (algebraMap A (AffineSections A ⊤) a)
  rw [sectionDerivative_algebraMap, affineFrameDerivation_algebraMap]

/-- Every derivation into an arbitrary sheaf of structure modules factors
through the actual coefficient derivation of an affine Kähler frame.
The image of the frame is obtained from the given derivation itself. -/
theorem derivation_factorization (e : KaehlerDifferential ℂ A ≃ₗ[A] A)
    (M : AffineModule A) (d : AffineDerivation A M) :
    d = (affineFrameDerivation e).postcomp
      (unitMapFromGlobal M (globalKaehlerMap M d (e.symm 1))).val := by
  apply affineDerivation_ext
  intro a
  change d.d (algebraMap A (AffineSections A ⊤) a) =
    (unitMapFromGlobal M (globalKaehlerMap M d (e.symm 1))).val.app (op ⊤)
      ((affineFrameDerivation e).d (algebraMap A (AffineSections A ⊤) a))
  rw [affineFrameDerivation_algebraMap, unitMapFromGlobal_top]
  change d.d (algebraMap A (AffineSections A ⊤) a) =
    e (KaehlerDifferential.D ℂ A a) • globalKaehlerMap M d (e.symm 1)
  rw [← map_smul]
  have he : e (KaehlerDifferential.D ℂ A a) • e.symm 1 = KaehlerDifferential.D ℂ A a := by
    apply e.injective
    rw [map_smul, LinearEquiv.apply_symm_apply, smul_eq_mul, mul_one]
  rw [he, globalKaehlerMap_D]

/-- An actual affine Kähler trivialization extends to an isomorphism of the
genuine differential sheaf with the structure module. No sheaf derivation,
local-freeness comparison, or extension premise is supplied as an assumption. -/
def affineDifferentialIso (e : KaehlerDifferential ℂ A ≃ₗ[A] A) :
    affineDifferentialSheaf A ≅ affineStructureModule A :=
  affineDifferentialIsoOfDerivation e (affineFrameDerivation e)
    (affineFrameDerivation_algebraMap e (op ⊤))

@[simp] theorem affineDifferentialIso_inv (e : KaehlerDifferential ℂ A ≃ₗ[A] A) :
    (affineDifferentialIso e).inv = frameSheafMap e := rfl

@[simp] theorem affineDifferentialIso_hom_D (e : KaehlerDifferential ℂ A ≃ₗ[A] A)
    (U : (Opens (PrimeSpectrum.Top A))ᵒᵖ) (a : A) :
    (affineDifferentialIso e).hom.val.app U
      ((affineUniversalDifferential A).d (algebraMap A (AffineSections A U.unop) a)) =
        algebraMap A (AffineSections A U.unop) (e (KaehlerDifferential.D ℂ A a)) := by
  rw [show (affineDifferentialIso e).hom = coefficientSheafMap (affineFrameDerivation e) from rfl,
    coefficientSheafMap_D, affineFrameDerivation_algebraMap]

/-- The coefficient formula on an arbitrary regular section is the local
fraction derivative constructed in the actual structure sheaf. -/
theorem affineDifferentialIso_hom_D_section (e : KaehlerDifferential ℂ A ≃ₗ[A] A)
    (U : (Opens (PrimeSpectrum.Top A))ᵒᵖ) (a : AffineSections A U.unop) :
    (affineDifferentialIso e).hom.val.app U ((affineUniversalDifferential A).d a) =
      CycleQ2GeometricStructureDerivation.sectionDerivative e U.unop a :=
  coefficientSheafMap_D (affineFrameDerivation e) U a

theorem affineDifferentialIso_inv_apply (e : KaehlerDifferential ℂ A ≃ₗ[A] A)
    (U : (Opens (PrimeSpectrum.Top A))ᵒᵖ) (a : AffineSections A U.unop) :
    (affineDifferentialIso e).inv.val.app U a =
      a • (affineDifferentialSheaf A).val.map
        (homOfLE (show U.unop ≤ ⊤ from le_top)).op (globalFrame e) :=
  unitMapFromGlobal_apply (affineDifferentialSheaf A) (globalFrame e) U a

/-- Every actual sheaf section has a unique coefficient in the restriction
of the affine frame. This is a consequence of the constructed sheaf isomorphism. -/
theorem section_reconstruction (e : KaehlerDifferential ℂ A ≃ₗ[A] A)
    (U : (Opens (PrimeSpectrum.Top A))ᵒᵖ)
    (ω : (affineDifferentialSheaf A).val.obj U) :
    ω = ((affineDifferentialIso e).hom.val.app U ω : AffineSections A U.unop) •
      (affineDifferentialSheaf A).val.map
        (homOfLE (show U.unop ≤ ⊤ from le_top)).op (globalFrame e) := by
  have h := congrArg (fun f : affineDifferentialSheaf A ⟶ affineDifferentialSheaf A =>
    f.val.app U ω) (affineDifferentialIso e).hom_inv_id
  change (affineDifferentialIso e).inv.val.app U
    ((affineDifferentialIso e).hom.val.app U ω) = ω at h
  rw [affineDifferentialIso_inv_apply] at h
  exact h.symm

/-- Compatibility name retained for the incoming affine chart interface. -/
theorem affineDifferentialIso_hom_D_algebraMap
    (e : KaehlerDifferential ℂ A ≃ₗ[A] A)
    (U : (Opens (PrimeSpectrum.Top A))ᵒᵖ) (a : A) :
    (affineDifferentialIso e).hom.val.app U
      ((affineUniversalDifferential A).d (algebraMap A (AffineSections A U.unop) a)) =
      algebraMap A (AffineSections A U.unop) (e (KaehlerDifferential.D ℂ A a)) :=
  affineDifferentialIso_hom_D e U a

theorem affineDifferentialIso_inv_one (e : KaehlerDifferential ℂ A ≃ₗ[A] A) :
    (affineDifferentialIso e).inv.val.app (op ⊤) (1 : AffineSections A ⊤) = globalFrame e := by
  change (unitMapFromGlobal (affineDifferentialSheaf A) (globalFrame e)).val.app (op ⊤)
    (1 : AffineSections A ⊤) = _
  rw [unitMapFromGlobal_top, one_smul]


#print axioms regularSectionDerivation_eq_affineFrameDerivation
#print axioms affineDerivation_ext
#print axioms affineDifferentialIso
#print axioms affineDifferentialIso_hom_D
#print axioms section_reconstruction
#print axioms derivation_factorization

end CycleQ2GeometricAffineDifferentialSheaf

end
