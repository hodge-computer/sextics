import Proposal.GeometricHodgeTwistConstantSections
import Proposal.GeometricAffineChartSections
import Proposal.GeometricHodgeThreefoldLiteral

/-!
# Canonical constants on the original monic weighted threefold

The degree-zero Laurent coefficient gives the actual constant coming from
the structure morphism, rather than an unspecified additive coordinate.
Thus the canonical scalar map onto global functions is surjective.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 3000
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2HodgeGlobalConstants

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open CycleQ2GeometricHodgeThreefold
open CycleQ2GenericSexticGradient (CoeffRing)
open CycleQ2HodgeTwistAnchor (torus torus_le commonCoefficient)
open CycleQ2HodgeTwistMonomials (evaluate monomial)
open CycleQ2HodgeTwistTorusChart (structureChart structureLaurentSections)
open CycleQ2HodgeTwistGlobal (globalMap globalMap_injective)
open CycleQ2HodgeTwistConstantSections (constant coefficient constant_coefficient structureSections)
open CycleQ2GeometricAffineChartSections (schemeCoefficient)
open CycleQ2GeometricDifferentialSheaf (coefficientOn)
open CycleQ2GeometricProjectiveCurve.Twisted (res res_comp)

private theorem restrict_top (X : Scheme.{0}) (U : X.Opens) :
    U.ι.appTop ≫ U.topIso.hom = X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op := by
  rw [Scheme.Opens.ι_appTop, Scheme.Opens.topIso_hom, ← Functor.map_comp]
  exact congrArg X.presheaf.map (Subsingleton.elim _ _)

private theorem chartScalar_map (φ : CoeffRing →+* ℂ) (i : Fin 4) :
    CommRingCat.ofHom (schemeCoefficient (toBase φ)) ≫ (threefold φ).presheaf.map
        (homOfLE (show coordinateOpen φ i ≤ ⊤ from le_top)).op =
      CommRingCat.ofHom (chartCoefficient φ i) ≫ Proj.awayToSection (grade φ) (coord φ i.castSucc) := by
  let U := coordinateOpen φ i
  let e := coordinateChart φ i
  have hb : e.inv ≫ U.ι ≫ toBase φ = Spec.map (CommRingCat.ofHom (chartCoefficient φ i)) :=
    coordinateChart_overBase φ i
  have h : U.ι ≫ toBase φ = e.hom ≫ Spec.map (CommRingCat.ofHom (chartCoefficient φ i)) :=
    (Iso.hom_inv_id_assoc e _).symm.trans (congrArg (fun k => e.hom ≫ k) hb)
  have he := congrArg (fun k : U.toScheme ⟶ Spec (CommRingCat.of ℂ) =>
    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ k.appTop ≫ U.topIso.hom) h
  simp only [Scheme.Hom.comp_appTop, U, e, coordinateChart, Proj.basicOpenIsoSpec_hom,
    Proj.basicOpenToSpec_app_top, Category.assoc, Scheme.ΓSpecIso_naturality_assoc,
    Iso.inv_hom_id_assoc, restrict_top] at he
  simpa only [schemeCoefficient, CommRingCat.ofHom_hom, Category.assoc,
    Proj.basicOpenIsoAway_hom, Iso.inv_hom_id, Category.comp_id, threefold, coordinateOpen] using he

theorem chartScalar (φ : CoeffRing →+* ℂ) (i : Fin 4) (c : ℂ) :
    coefficientOn (threefold φ).sheaf (schemeCoefficient (toBase φ)) (coordinateOpen φ i) c =
      (Proj.awayToSection (grade φ) (coord φ i.castSucc)) (chartCoefficient φ i c) :=
  congrArg (fun k : CommRingCat.of ℂ ⟶ Γ(threefold φ, coordinateOpen φ i) => k.hom c)
    (chartScalar_map φ i)

theorem torusScalar (φ : CoeffRing →+* ℂ) (c : ℂ) :
    coefficientOn (threefold φ).sheaf (schemeCoefficient (toBase φ)) (torus φ) c =
      commonCoefficient φ c := by
  have e := congrArg (res (threefold φ).sheaf (torus_le φ 0)) (chartScalar φ 0 c)
  change res _ _ (res _ _ (schemeCoefficient (toBase φ) c)) = commonCoefficient φ c at e
  rw [res_comp] at e
  exact e

variable (φ : CoeffRing →+* ℂ) (h : IsUnit (φ vertexCoefficient))

private theorem torus_evaluate (s : Γ(threefold φ, torus φ)) :
    evaluate φ (torus φ) (torus_le φ) (commonCoefficient φ) 0
      ((structureChart φ h).coordinates s) = s := by
  let W := torus φ
  let e := CycleQ2HodgeThreefoldTwist.chartFrame φ 0 0 W (torus_le φ 0)
  let p := e.symm s
  have hn := CycleQ2HodgeTwistAnchor.face_frame_evaluation φ 0 h Finset.univ (Finset.mem_univ _) 0 p
  change e (CycleQ2GeometricSheafLocalIso.res
    (CycleQ2GeometricModuleLocalIso.addSheaf (CycleQ2HodgeThreefoldTwist.twist φ 0))
      (show W ≤ W from le_rfl) p) = _ at hn
  rw [CycleQ2GeometricSheafLocalIso.res_self] at hn
  exact hn.symm.trans (e.apply_symm_apply s)

private theorem evaluate_constant (c : ℂ) :
    evaluate φ (torus φ) (torus_le φ) (commonCoefficient φ) 0 (constant c).val =
      commonCoefficient φ c := by
  classical
  simp [evaluate, constant, Fin.sum_univ_three, monomial, CycleQ2HodgeTwistMonomials.units]

include h in
theorem restrict_torus_injective : Function.Injective
    (res (threefold φ).sheaf (show torus φ ≤ ⊤ from le_top)) := by
  intro a b hab
  apply globalMap_injective (structureLaurentSections φ h) (coordinateOpens_cover φ h)
  apply Subtype.ext
  change (structureChart φ h).coordinates (res (threefold φ).sheaf le_top a) =
    (structureChart φ h).coordinates (res (threefold φ).sheaf le_top b)
  exact congrArg (structureChart φ h).coordinates hab

/-- The previously computed Laurent coefficient is the canonical scalar itself. -/
theorem section_eq_scalar (s : Γ(threefold φ, ⊤)) :
    s = schemeCoefficient (toBase φ) (structureSections φ h s) := by
  apply restrict_torus_injective φ h
  let p := globalMap (structureLaurentSections φ h) s
  have hp : (constant (structureSections φ h s)).val = p.val :=
    congrArg Subtype.val (constant_coefficient p)
  calc
    res (threefold φ).sheaf le_top s =
        evaluate φ (torus φ) (torus_le φ) (commonCoefficient φ) 0 p.val :=
      (torus_evaluate φ h _).symm
    _ = commonCoefficient φ (structureSections φ h s) := by rw [← hp, evaluate_constant]
    _ = _ := (torusScalar φ _).symm

include h in
/-- Every actual global function comes from the original structure morphism. -/
theorem scalar_surjective : Function.Surjective (schemeCoefficient (toBase φ)) :=
  fun s => ⟨structureSections φ h s, (section_eq_scalar φ h s).symm⟩

/-- The isomorphism is the canonical ring map, with its multiplication intact. -/
def scalarEquiv : ℂ ≃+* Γ(threefold φ, ⊤) := by
  letI : Nontrivial Γ(threefold φ, ⊤) := (structureSections φ h).symm.injective.nontrivial
  exact RingEquiv.ofBijective (schemeCoefficient (toBase φ))
    ⟨RingHom.injective _, scalar_surjective φ h⟩

open CycleQ2GeometricHodgeThreefoldIncidence
open CycleQ2LiteralAmbientSmooth (incidenceFiberToComplex)

/-- Transport uses the actual isomorphism over the original complex point. -/
theorem original_scalar_surjective : Function.Surjective (schemeCoefficient (incidenceFiberToComplex 57)) := by
  intro s
  obtain ⟨c,hc⟩ := scalar_surjective literalEval literal_vertex_unit (literalIso.hom.appTop s)
  refine ⟨c, ?_⟩
  apply (ConcreteCategory.bijective_of_isIso literalIso.hom.appTop).injective
  have hf := CycleQ2GeometricAffineChartSections.schemeCoefficient_comp
    literalIso.hom (incidenceFiberToComplex 57) c
  rw [literalIso_overComplex] at hf
  exact hf.symm.trans hc

end CycleQ2HodgeGlobalConstants
end

#print axioms CycleQ2HodgeGlobalConstants.chartScalar
#print axioms CycleQ2HodgeGlobalConstants.section_eq_scalar
#print axioms CycleQ2HodgeGlobalConstants.scalar_surjective
#print axioms CycleQ2HodgeGlobalConstants.scalarEquiv
#print axioms CycleQ2HodgeGlobalConstants.original_scalar_surjective
