import Proposal.GeometricSchemeCotangentMaps
import Proposal.GeometricLiteralAffineCotangent

/-!
# The canonical affine cotangent map is the original tensor reduction

Both sheaf comparisons are normalized by the original universal
differentials and the actual pullback unit. The canonical scheme
cotangent map is therefore the tilde of the actual base-changed Kähler
map, with no additional comparison hypothesis.

Prepared for fqlx with OpenAI ChatGPT assistance; see solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2GeometricAffineCotangentReduction

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
  CycleQ2GeometricDifferentialSheaf CycleQ2GeometricAffineDifferentialSheaf
  CycleQ2GeometricAffineKahlerSheaf CycleQ2GeometricAffineModulePullback
  CycleQ2GeometricSchemeCotangentMaps CycleQ2GeometricSchemeDifferentialMap

open scoped TensorProduct

variable {B C : Type} [CommRing B] [CommRing C] [Algebra ℂ B] [Algebra ℂ C]
  (ρ : B →ₐ[ℂ] C)

abbrev affineMap := Spec.map (CommRingCat.ofHom ρ.toRingHom)

theorem affineMap_coefficient (U : (Spec (CommRingCat.of B)).Opens) (c : ℂ) :
    (affineMap ρ).app U (coefficientOn (Spec.structureSheaf B) (affineCoefficient B) U c) =
      coefficientOn (Spec.structureSheaf C) (affineCoefficient C) (affineMap ρ ⁻¹ᵁ U) c := by
  have hs : affineMap ρ ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ B)) =
      Spec.map (CommRingCat.ofHom (algebraMap ℂ C)) := by
    rw [← Spec.map_comp]
    congr 1
    ext c
    exact ρ.commutes c
  have he : CycleQ2GeometricAffineChartSections.schemeCoefficient
      (Spec.map (CommRingCat.ofHom (algebraMap ℂ B))) = affineCoefficient B :=
    congrArg CommRingCat.Hom.hom (affineCoefficient_structureMorphism B).symm
  exact he ▸ CycleQ2LiteralAffineCotangent.affineCoefficient_square (affineMap ρ)
    (Spec.map (CommRingCat.ofHom (algebraMap ℂ B))) hs U c

abbrev tensorModule : ModuleCat C :=
  (ModuleCat.extendScalars ρ.toRingHom).obj (ModuleCat.of B (KaehlerDifferential ℂ B))

def tensorReduction : tensorModule ρ ⟶ ModuleCat.of C (KaehlerDifferential ℂ C) := by
  let : Algebra B C := ρ.toRingHom.toAlgebra
  let : IsScalarTower ℂ B C :=
    IsScalarTower.of_algebraMap_eq fun c => (ρ.commutes c).symm
  exact ModuleCat.ofHom ((KaehlerDifferential.map ℂ ℂ B C).liftBaseChange C)

theorem tensorReduction_D (b : B) :
    tensorReduction ρ
        ((ModuleCat.extendRestrictScalarsAdj ρ.toRingHom).unit.app
          (ModuleCat.of B (KaehlerDifferential ℂ B)) (KaehlerDifferential.D ℂ B b)) =
      KaehlerDifferential.D ℂ C (ρ b) := by
  let : Algebra B C := ρ.toRingHom.toAlgebra
  let : IsScalarTower ℂ B C :=
    IsScalarTower.of_algebraMap_eq fun c => (ρ.commutes c).symm
  change (KaehlerDifferential.map ℂ ℂ B C).liftBaseChange C
    ((1 : C) ⊗ₜ[B] KaehlerDifferential.D ℂ B b) = _
  rw [LinearMap.liftBaseChange_tmul, one_smul, KaehlerDifferential.map_D]
  rfl

abbrev tensorTilde := tilde (R := CommRingCat.of C) (tensorModule ρ)

def tensorReductionTilde : tensorTilde ρ ⟶ kahlerTilde (A := C) :=
  tilde.map (tensorReduction ρ)

def canonicalAffineCotangentMap :
    (Scheme.Modules.pullback (affineMap ρ)).obj (affineDifferentialSheaf B) ⟶
      affineDifferentialSheaf C :=
  cotangentMap (affineMap ρ) (affineCoefficient C) (affineCoefficient B) (affineMap_coefficient ρ)

theorem affineMap_original (b : B) :
    (affineMap ρ).appTop (algebraMap B (AffineSections B ⊤) b) =
      algebraMap C (AffineSections C ⊤) (ρ b) :=
  congrArg (fun f => f b)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom ρ.toRingHom)).symm

theorem tensorComparisonReduction :
    (pullbackTildeIso (CommRingCat.ofHom ρ.toRingHom)).hom.app
          (ModuleCat.of B (KaehlerDifferential ℂ B)) ≫ tensorReductionTilde ρ =
      (Scheme.Modules.pullback (affineMap ρ)).map (affineKahlerIso (A := B)).inv ≫
        canonicalAffineCotangentMap ρ ≫ (affineKahlerIso (A := C)).hom := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction (affineMap ρ)).homEquiv
    (kahlerTilde (A := B)) (kahlerTilde (A := C))).injective
  unfold canonicalAffineCotangentMap
  rw [Adjunction.homEquiv_naturality_left]
  erw [
    (Scheme.Modules.pullbackPushforwardAdjunction (affineMap ρ)).homEquiv_naturality_right
      (cotangentMap (affineMap ρ) (affineCoefficient C) (affineCoefficient B)
        (affineMap_coefficient ρ)) (affineKahlerIso (A := C)).hom]
  rw [cotangentMap_adjunct (affineMap ρ) (affineCoefficient C) (affineCoefficient B)
    (affineMap_coefficient ρ)]
  apply ((tilde.adjunction (R := CommRingCat.of B)).homEquiv
    (ModuleCat.of B (KaehlerDifferential ℂ B))
    ((Scheme.Modules.pushforward (affineMap ρ)).obj (kahlerTilde (A := C)))).injective
  apply ModuleCat.hom_ext
  apply LinearMap.ext_on_range (KaehlerDifferential.span_range_derivation ℂ B)
  intro b
  simp only [Adjunction.homEquiv_apply]
  change (tensorReductionTilde ρ).val.app (op ⊤)
      (((pullbackTildeIso (CommRingCat.ofHom ρ.toRingHom)).hom.app
        (ModuleCat.of B (KaehlerDifferential ℂ B))).val.app (op ⊤)
        (((Scheme.Modules.pullbackPushforwardAdjunction (affineMap ρ)).unit.app
          (kahlerTilde (A := B))).val.app (op ⊤)
            (tilde.toOpen (R := CommRingCat.of B) (ModuleCat.of B (KaehlerDifferential ℂ B)) ⊤
              (KaehlerDifferential.D ℂ B b)))) =
    (differentialToTilde (A := C)).val.app (op ⊤)
      ((schemeDifferentialMap (affineMap ρ) (affineCoefficient C) (affineCoefficient B)
        (affineMap_coefficient ρ)).val.app (op ⊤)
          ((tildeToDifferential (A := B)).val.app (op ⊤)
            (tilde.toOpen (R := CommRingCat.of B) (ModuleCat.of B (KaehlerDifferential ℂ B)) ⊤
              (KaehlerDifferential.D ℂ B b))))
  rw [pullbackTilde_unit_apply, tildeToDifferential_top, globalKaehlerMap_D]
  have hd := schemeDifferentialMap_D (affineMap ρ) (affineCoefficient C) (affineCoefficient B)
    (affineMap_coefficient ρ) ⊤ (algebraMap B (AffineSections B ⊤) b)
  have hright := (congrArg ((differentialToTilde (A := C)).val.app (op ⊤)) hd).trans
    ((congrArg (fun a : AffineSections C ⊤ => (differentialToTilde (A := C)).val.app (op ⊤)
      ((affineUniversalDifferential C).d a)) (affineMap_original ρ b)).trans
        ((differentialToTilde_D (A := C) (op ⊤)
          (algebraMap C (AffineSections C ⊤) (ρ b))).trans
            (tildeDerivation_algebraMap (A := C) (op ⊤) (ρ b))))
  have h := ConcreteCategory.congr_hom (C := ModuleCat C) (X := tensorModule ρ)
    (tilde.toOpen_map_app (R := CommRingCat.of C) (tensorReduction ρ) ⊤)
    (show tensorModule ρ from ((ModuleCat.extendRestrictScalarsAdj ρ.toRingHom).unit.app
      (ModuleCat.of B (KaehlerDifferential ℂ B)) (KaehlerDifferential.D ℂ B b)))
  change (tensorReductionTilde ρ).val.app (op ⊤)
      (tilde.toOpen (R := CommRingCat.of C) (tensorModule ρ) ⊤
        ((ModuleCat.extendRestrictScalarsAdj ρ.toRingHom).unit.app
          (ModuleCat.of B (KaehlerDifferential ℂ B)) (KaehlerDifferential.D ℂ B b))) =
    tilde.toOpen (R := CommRingCat.of C) (ModuleCat.of C (KaehlerDifferential ℂ C)) ⊤
      (tensorReduction ρ ((ModuleCat.extendRestrictScalarsAdj ρ.toRingHom).unit.app
        (ModuleCat.of B (KaehlerDifferential ℂ B)) (KaehlerDifferential.D ℂ B b))) at h
  exact (h.trans (congrArg (tilde.toOpen (R := CommRingCat.of C)
    (ModuleCat.of C (KaehlerDifferential ℂ C)) ⊤) (tensorReduction_D ρ b))).trans hright.symm

theorem affineCotangentReduction_comm :
    (Scheme.Modules.pullback (affineMap ρ)).map (affineKahlerIso (A := B)).hom ≫
        (pullbackTildeIso (CommRingCat.ofHom ρ.toRingHom)).hom.app
          (ModuleCat.of B (KaehlerDifferential ℂ B)) ≫ tensorReductionTilde ρ =
      canonicalAffineCotangentMap ρ ≫ (affineKahlerIso (A := C)).hom := by
  rw [tensorComparisonReduction, ← Category.assoc, ← Functor.map_comp,
    Iso.hom_inv_id, (Scheme.Modules.pullback (affineMap ρ)).map_id (affineDifferentialSheaf B),
    Category.id_comp]

end CycleQ2GeometricAffineCotangentReduction

end

#print axioms CycleQ2GeometricAffineCotangentReduction.tensorReduction_D
#print axioms CycleQ2GeometricAffineCotangentReduction.tensorComparisonReduction
#print axioms CycleQ2GeometricAffineCotangentReduction.affineCotangentReduction_comm
