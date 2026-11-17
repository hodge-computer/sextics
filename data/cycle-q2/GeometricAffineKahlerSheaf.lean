import Proposal.GeometricAffineDifferentialSheaf
import Mathlib.AlgebraicGeometry.Modules.Tilde

/-!
# The actual affine differential sheaf is the tilde Kähler module

The universal differential of the affine ring is localized at each prime.
Its fraction rule gives genuine regular sections in the tilde Kähler
module, with the original restrictions on every open. The two universal
properties then identify this tilde module with the actual differential
sheaf without any rank or smoothness premise.

Prepared for fqlx with OpenAI ChatGPT assistance; see solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2GeometricAffineKahlerSheaf

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
  CycleQ2GeometricDifferentialSheaf CycleQ2GeometricAffineDifferentialSheaf

variable {A : Type} [CommRing A] [Algebra ℂ A]

attribute [local instance] LocalizedModule.smulOfIsLocalization LocalizedModule.moduleOfIsLocalization

abbrev KahlerModule := KaehlerDifferential ℂ A

abbrev kahlerTilde : (Spec (CommRingCat.of A)).Modules :=
  tilde (ModuleCat.of A (KahlerModule (A := A)))

instance localizedComplexTower (S : Submonoid A) :
    IsScalarTower ℂ A (LocalizedModule S (KahlerModule (A := A))) where
  smul_assoc c a := by
    rintro ⟨m, s⟩
    simp only [smul_assoc]

instance localizedComplexRingTower (S : Submonoid A) :
    IsScalarTower ℂ (LocalizedModule S A)
      (LocalizedModule S (KahlerModule (A := A))) :=
  IsScalarTower.to₁₃₄ ℂ A (LocalizedModule S A) _

def localKahlerEquiv (S : Submonoid A) :
    KaehlerDifferential ℂ (LocalizedModule S A) ≃ₗ[LocalizedModule S A]
      LocalizedModule S (KahlerModule (A := A)) :=
  (IsLocalizedModule.linearEquiv S
    (KaehlerDifferential.map ℂ ℂ A (LocalizedModule S A))
    (LocalizedModule.mkLinearMap S (KahlerModule (A := A)))).extendScalarsOfIsLocalization
      S (LocalizedModule S A)

theorem localKahlerEquiv_map (S : Submonoid A) (ω : KahlerModule (A := A)) :
    localKahlerEquiv S (KaehlerDifferential.map ℂ ℂ A (LocalizedModule S A) ω) =
      LocalizedModule.mk ω 1 :=
  IsLocalizedModule.linearEquiv_apply S _ _ ω

def localDerivative (S : Submonoid A) :
    Derivation ℂ (LocalizedModule S A) (LocalizedModule S (KahlerModule (A := A))) :=
  (localKahlerEquiv S).toLinearMap.compDer (KaehlerDifferential.D ℂ (LocalizedModule S A))

theorem localDerivative_algebraMap (S : Submonoid A) (a : A) :
    localDerivative S (algebraMap A (LocalizedModule S A) a) =
      LocalizedModule.mk (KaehlerDifferential.D ℂ A a) 1 := by
  change localKahlerEquiv S
    (KaehlerDifferential.D ℂ (LocalizedModule S A) (algebraMap A _ a)) = _
  rw [← KaehlerDifferential.map_D ℂ ℂ A (LocalizedModule S A), localKahlerEquiv_map]

theorem localDerivative_mk (S : Submonoid A) (a : A) (s : S) :
    localDerivative S (LocalizedModule.mk a s) =
      LocalizedModule.mk
        ((s : A) • KaehlerDifferential.D ℂ A a -
          a • KaehlerDifferential.D ℂ A (s : A)) (s * s) := by
  let d := localDerivative S
  let t : LocalizedModule S A := IsLocalization.mk' _ 1 s
  have ht : t * algebraMap A (LocalizedModule S A) (s : A) = 1 := by
    exact (IsLocalization.mk'_spec _ 1 s).trans (map_one _)
  have hpow : t ^ 2 * algebraMap A (LocalizedModule S A) (s : A) = t := by
    rw [pow_two, mul_assoc, ht, mul_one]
  change d (LocalizedModule.mk a s) = _
  rw [CycleQ2GeometricStructureDerivation.localizedModule_mk_eq,
    IsLocalization.mk'_eq_mul_mk'_one, Derivation.leibniz,
    d.leibniz_of_mul_eq_one ht]
  simp only [d, localDerivative_algebraMap, neg_smul, smul_neg]
  have hs (m : KahlerModule (A := A)) :
      t ^ 2 • LocalizedModule.mk ((s : A) • m) (1 : S) =
        t • LocalizedModule.mk m (1 : S) := by
    rw [← LocalizedModule.smul'_mk (s : A) m (1 : S),
      ← IsScalarTower.algebraMap_smul (R := A) (LocalizedModule S A), smul_smul, hpow]
  calc
    _ = t ^ 2 • (LocalizedModule.mk ((s : A) • KaehlerDifferential.D ℂ A a) 1 -
        LocalizedModule.mk (a • KaehlerDifferential.D ℂ A (s : A)) 1) := by
      rw [smul_sub, hs, ← LocalizedModule.smul'_mk a
          (KaehlerDifferential.D ℂ A (s : A)) (1 : S),
        ← IsScalarTower.algebraMap_smul (R := A) (LocalizedModule S A), smul_comm]
      exact neg_add_eq_sub _ _
    _ = t ^ 2 • LocalizedModule.mk
        ((s : A) • KaehlerDifferential.D ℂ A a -
          a • KaehlerDifferential.D ℂ A (s : A)) 1 := by
      congr 1
      exact (map_sub (LocalizedModule.mkLinearMap S (KahlerModule (A := A))) _ _).symm
    _ = _ := by
      dsimp only [t]
      rw [pow_two, ← IsLocalization.mk'_mul, one_mul,
        ← CycleQ2GeometricStructureDerivation.localizedModule_mk_eq]
      simpa only [one_smul, one_mul, mul_one] using OreLocalization.oreDiv_smul_char (1 : A)
        ((s : A) • KaehlerDifferential.D ℂ A a - a • KaehlerDifferential.D ℂ A (s : A))
        (s * s) (1 : S) (1 : A) (1 : S) (by simp)

theorem derivative_isLocallyFraction
    (U : Opens (PrimeSpectrum.Top A)) (s : AffineSections A U) :
    (StructureSheaf.isLocallyFraction A (KahlerModule (A := A))).pred
      (fun x : U => localDerivative x.1.asIdeal.primeCompl (s.1 x)) := by
  intro x
  obtain ⟨V, hxV, i, a, b, hab⟩ := s.2 x
  refine ⟨V, hxV, i,
    b • KaehlerDifferential.D ℂ A a - a • KaehlerDifferential.D ℂ A b, b * b, ?_⟩
  intro y
  obtain ⟨hb, hy⟩ := hab y
  refine ⟨y.1.asIdeal.primeCompl.mul_mem hb hb, ?_⟩
  exact (congrArg (localDerivative y.1.asIdeal.primeCompl) hy).trans
    (localDerivative_mk y.1.asIdeal.primeCompl a ⟨b, hb⟩)

def sectionDerivative (U : Opens (PrimeSpectrum.Top A)) (s : AffineSections A U) :
    Γ(kahlerTilde (A := A), U) :=
  ⟨fun x => localDerivative x.1.asIdeal.primeCompl (s.1 x),
    derivative_isLocallyFraction U s⟩

instance sectionRingModule (U : Opens (PrimeSpectrum.Top A)) :
    Module (AffineSections A U) Γ(kahlerTilde (A := A), U) :=
  inferInstanceAs (Module ((ringSheaf (Spec.structureSheaf A)).obj.obj (op U))
    ((kahlerTilde (A := A)).val.obj (op U)))

theorem sectionDerivative_add (U : Opens (PrimeSpectrum.Top A)) (s t : AffineSections A U) :
    sectionDerivative U (s + t) = sectionDerivative U s + sectionDerivative U t := by
  apply Subtype.ext
  funext x
  exact map_add (localDerivative x.1.asIdeal.primeCompl) (s.1 x) (t.1 x)

theorem sectionDerivative_mul (U : Opens (PrimeSpectrum.Top A)) (s t : AffineSections A U) :
    sectionDerivative U (s * t) = s • sectionDerivative U t + t • sectionDerivative U s := by
  apply Subtype.ext
  funext x
  exact (localDerivative x.1.asIdeal.primeCompl).leibniz (s.1 x) (t.1 x)

theorem sectionDerivative_algebraMap (U : Opens (PrimeSpectrum.Top A)) (a : A) :
    sectionDerivative U (algebraMap A (AffineSections A U) a) =
      (tilde.toOpen (R := CommRingCat.of A) (ModuleCat.of A (KahlerModule (A := A))) U)
        (KaehlerDifferential.D ℂ A a) := by
  apply Subtype.ext
  funext x
  exact localDerivative_algebraMap x.1.asIdeal.primeCompl a

def tildeDerivation : AffineDerivation A (kahlerTilde (A := A)) where
  d {U} := AddMonoidHom.mk' (sectionDerivative U.unop) (sectionDerivative_add U.unop)
  d_mul {U} := sectionDerivative_mul U.unop
  d_map {_ _} _ _ := rfl
  d_app {U} c := by
    change sectionDerivative U.unop
      (algebraMap A (AffineSections A U.unop) (algebraMap ℂ A c)) = 0
    rw [sectionDerivative_algebraMap, Derivation.map_algebraMap, map_zero]

theorem tildeDerivation_algebraMap
    (U : (Opens (PrimeSpectrum.Top A))ᵒᵖ) (a : A) :
    (tildeDerivation (A := A)).d (X := U) (algebraMap A (AffineSections A U.unop) a) =
      tilde.toOpen (R := CommRingCat.of A) (ModuleCat.of A (KahlerModule (A := A))) U.unop
        (KaehlerDifferential.D ℂ A a) := sectionDerivative_algebraMap U.unop a

def differentialToTilde : affineDifferentialSheaf A ⟶ kahlerTilde (A := A) :=
  differentialLift (Spec.structureSheaf A) (affineCoefficient A) _ tildeDerivation

theorem differentialToTilde_D (U : (Opens (PrimeSpectrum.Top A))ᵒᵖ)
    (s : AffineSections A U.unop) :
    (differentialToTilde (A := A)).val.app U ((affineUniversalDifferential A).d s) =
      (tildeDerivation (A := A)).d s :=
  PresheafOfModules.Derivation.congr_d
    (differentialLift_fac (Spec.structureSheaf A) (affineCoefficient A) _ tildeDerivation) s

def globalDifferentialMap : ModuleCat.of A (KahlerModule (A := A)) ⟶
    (moduleSpecΓFunctor (R := CommRingCat.of A)).obj (affineDifferentialSheaf A) := by
  let N := (moduleSpecΓFunctor (R := CommRingCat.of A)).obj (affineDifferentialSheaf A)
  letI : Module A N := N.isModule
  exact ModuleCat.ofHom (Y := N)
    { toFun := fun ω => globalKaehlerMap (affineDifferentialSheaf A) (affineUniversalDifferential A) ω
      map_add' ω η := (globalKaehlerMap (affineDifferentialSheaf A)
        (affineUniversalDifferential A)).map_add ω η
      map_smul' a ω := by
        exact (globalKaehlerMap (affineDifferentialSheaf A)
          (affineUniversalDifferential A)).map_smul a ω }

def tildeToDifferential : kahlerTilde (A := A) ⟶ affineDifferentialSheaf A :=
  ((tilde.adjunction (R := CommRingCat.of A)).homEquiv
    (ModuleCat.of A (KahlerModule (A := A))) (affineDifferentialSheaf A)).symm
      globalDifferentialMap

theorem tildeToDifferential_top (ω : KahlerModule (A := A)) :
    (tildeToDifferential (A := A)).val.app (op ⊤)
        (tilde.toOpen (R := CommRingCat.of A) (ModuleCat.of A (KahlerModule (A := A))) ⊤ ω) =
      globalKaehlerMap (affineDifferentialSheaf A) (affineUniversalDifferential A) ω := by
  have h := ((tilde.adjunction (R := CommRingCat.of A)).homEquiv
    (ModuleCat.of A (KahlerModule (A := A))) (affineDifferentialSheaf A)).apply_symm_apply
      globalDifferentialMap
  exact congrArg (fun f => f ω) h

theorem differentialToTilde_tildeToDifferential :
    differentialToTilde (A := A) ≫ tildeToDifferential = 𝟙 (affineDifferentialSheaf A) := by
  apply differentialLift_unique (Spec.structureSheaf A) (affineCoefficient A)
  apply affineDerivation_ext
  intro a
  change (tildeToDifferential (A := A)).val.app (op ⊤)
    ((differentialToTilde (A := A)).val.app (op ⊤)
      ((affineUniversalDifferential A).d (algebraMap A (AffineSections A ⊤) a))) =
    (affineUniversalDifferential A).d (algebraMap A (AffineSections A ⊤) a)
  rw [differentialToTilde_D, tildeDerivation_algebraMap, tildeToDifferential_top,
    globalKaehlerMap_D]

theorem tildeToDifferential_differentialToTilde :
    tildeToDifferential (A := A) ≫ differentialToTilde = 𝟙 (kahlerTilde (A := A)) := by
  apply ((tilde.adjunction (R := CommRingCat.of A)).homEquiv
    (ModuleCat.of A (KahlerModule (A := A))) (kahlerTilde (A := A))).injective
  apply ModuleCat.hom_ext
  apply LinearMap.ext_on_range (KaehlerDifferential.span_range_derivation ℂ A)
  intro a
  change (differentialToTilde (A := A)).val.app (op ⊤)
    ((tildeToDifferential (A := A)).val.app (op ⊤)
      (tilde.toOpen (R := CommRingCat.of A) (ModuleCat.of A (KahlerModule (A := A))) ⊤
        (KaehlerDifferential.D ℂ A a))) =
    tilde.toOpen (R := CommRingCat.of A) (ModuleCat.of A (KahlerModule (A := A))) ⊤
      (KaehlerDifferential.D ℂ A a)
  rw [tildeToDifferential_top, globalKaehlerMap_D, differentialToTilde_D,
    tildeDerivation_algebraMap]

def affineKahlerIso : affineDifferentialSheaf A ≅ kahlerTilde (A := A) where
  hom := differentialToTilde
  inv := tildeToDifferential
  hom_inv_id := differentialToTilde_tildeToDifferential
  inv_hom_id := tildeToDifferential_differentialToTilde

instance affineDifferential_isQuasicoherent : (affineDifferentialSheaf A).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent (Spec (CommRingCat.of A)).ringCatSheaf).prop_of_iso
    (affineKahlerIso (A := A)).symm inferInstance

end CycleQ2GeometricAffineKahlerSheaf

end

#print axioms CycleQ2GeometricAffineKahlerSheaf.localDerivative_mk
#print axioms CycleQ2GeometricAffineKahlerSheaf.tildeDerivation
#print axioms CycleQ2GeometricAffineKahlerSheaf.affineKahlerIso
