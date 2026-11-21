import Proposal.GeometricAffineKahlerSheaf
import Proposal.GeometricOpenDifferentialSheaf
import Proposal.GeometricTwistedDifferential

/-!
# Ordinary Kähler differentials on an affine open

The sheafification map to differentials on a complex scheme is an isomorphism
on every affine open. We compare on universal differentials with an affine
chart, where the global sections of the tilde module recover the ordinary
Kähler module.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2AffineOpenOrdinaryDifferentials

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
  CycleQ2GeometricDifferentialSheaf CycleQ2GeometricOpenDifferentialSheaf
  CycleQ2GeometricAffineDifferentialSheaf CycleQ2GeometricAffineKahlerSheaf
  CycleQ2GeometricSectionDifferentials CycleQ2GeometricAffineOverlap
  CycleQ2GeometricAffineChartSections

section Chart
variable {A : Type} [CommRing A] [Algebra ℂ A] {Y : Scheme.{0}}
  (j : Spec (CommRingCat.of A) ⟶ Y) [IsOpenImmersion j] (cY : ℂ →+* Γ(Y,⊤))
  (hc : ∀ (U : Y.Opens) (c : ℂ), j.app U (coefficientOn Y.sheaf cY U c) =
    coefficientOn (Spec.structureSheaf A) (affineCoefficient A) (j ⁻¹ᵁ U) c)


def chartRingEquiv : letI : Algebra ℂ Γ(Y,j ''ᵁ ⊤) := sectionAlgebra Y.sheaf cY (j ''ᵁ ⊤)
    A ≃ₐ[ℂ] Γ(Y,(j ''ᵁ ⊤)) := by
  letI : Algebra ℂ Γ(Y,j ''ᵁ ⊤) := sectionAlgebra Y.sheaf cY (j ''ᵁ ⊤)
  let e := ((Scheme.ΓSpecIso (CommRingCat.of A)).symm ≪≫ (j.appIso ⊤).symm).commRingCatIsoToRingEquiv
  apply AlgEquiv.ofRingEquiv (f := e)
  intro a
  exact appIso_coefficient j (affineCoefficient A) cY hc ⊤ a

theorem chartRingEquiv_apply (a : A) : letI : Algebra ℂ Γ(Y,j ''ᵁ ⊤) := sectionAlgebra Y.sheaf cY (j ''ᵁ ⊤)
    chartRingEquiv j cY hc a = (j.appIso ⊤).inv (algebraMap A (AffineSections A ⊤) a) := rfl

private abbrev affineGlobal := globalKaehlerMap (affineDifferentialSheaf A) (affineUniversalDifferential A)

theorem affineGlobal_bijective : Function.Bijective (affineGlobal (A := A)) := by
  let e := affineKahlerIso (A := A)
  have h := (ConcreteCategory.bijective_of_isIso
    ((SheafOfModules.evaluation _ (op ⊤)).map e.inv)).comp
      ((tilde.isoTop (R := CommRingCat.of A) (ModuleCat.of A (KahlerModule (A := A)))).toLinearEquiv.bijective)
  have he : affineGlobal (A := A) =
      (fun x => e.inv.val.app (op ⊤) (tilde.toOpen (R := CommRingCat.of A)
        (ModuleCat.of A (KahlerModule (A := A))) ⊤ x)) := by
    funext x
    exact (tildeToDifferential_top x).symm
  rw [he]
  exact h

theorem chart_comparison (ω : KaehlerDifferential ℂ A) : letI : Algebra ℂ Γ(Y,j ''ᵁ ⊤) := sectionAlgebra Y.sheaf cY (j ''ᵁ ⊤)
    toSheaf Y.sheaf cY (j ''ᵁ ⊤) (differentialEquiv (chartRingEquiv j cY hc) ω) =
      (openDifferentialIso j (affineCoefficient A) cY hc).inv.val.app (op ⊤)
        (affineGlobal ω) := by
  let : Algebra ℂ Γ(Y,j ''ᵁ ⊤) := sectionAlgebra Y.sheaf cY (j ''ᵁ ⊤)
  have hm : ω ∈ Submodule.span A (Set.range (KaehlerDifferential.D ℂ A)) := by
    rw [KaehlerDifferential.span_range_derivation]
    trivial
  induction hm using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨x,rfl⟩ := ha
    rw [differentialEquiv_D]
    change (universalDifferential Y.sheaf cY).d ((chartRingEquiv j cY hc) x) = _
    refine (openDifferentialIso_inv_D j (affineCoefficient A) cY hc ⊤
      (algebraMap A (AffineSections A ⊤) x)).symm.trans ?_
    exact congrArg (fun z => (openDifferentialIso j (affineCoefficient A) cY hc).inv.val.app (op ⊤) z)
      (globalKaehlerMap_D (affineDifferentialSheaf A) (affineUniversalDifferential A) x).symm
  | zero => simp only [map_zero]
  | add a b _ _ ha hb => simp only [map_add, ha, hb]
  | smul r a _ ha =>
    let k := chartRingEquiv j cY hc
    let B := toSheaf Y.sheaf cY (j ''ᵁ ⊤)
    let : Module Γ(Y,j ''ᵁ ⊤) ((differentialSheaf Y.sheaf cY).val.obj (op (j ''ᵁ ⊤))) :=
      ((differentialSheaf Y.sheaf cY).val.obj (op (j ''ᵁ ⊤))).isModule
    let m := (openDifferentialIso j (affineCoefficient A) cY hc).inv.val.app (op ⊤)
    refine (congrArg B (differentialEquiv_smul k r a)).trans ?_
    refine (B.map_smul (k r) (differentialEquiv k a)).trans ?_
    refine (congrArg (fun z : (differentialSheaf Y.sheaf cY).val.obj (op (j ''ᵁ ⊤)) =>
      (show Γ(Y,j ''ᵁ ⊤) from k r) • z) ha).trans ?_
    refine (m.hom.map_smul (algebraMap A (AffineSections A ⊤) r) (affineGlobal a)).symm.trans ?_
    exact congrArg (fun z => m z) ((affineGlobal (A := A)).map_smul r a).symm

include hc in
theorem toSheaf_bijective_on_chart :
    Function.Bijective (toSheaf Y.sheaf cY (j ''ᵁ ⊤)) := by
  let : Algebra ℂ Γ(Y,j ''ᵁ ⊤) := sectionAlgebra Y.sheaf cY (j ''ᵁ ⊤)
  let e := openDifferentialIso j (affineCoefficient A) cY hc
  have h := (ConcreteCategory.bijective_of_isIso
    ((SheafOfModules.evaluation _ (op ⊤)).map e.inv)).comp (affineGlobal_bijective (A := A))
  let a := differentialEquiv (A := A) (B := Γ(Y,j ''ᵁ ⊤)) (chartRingEquiv j cY hc)
  have hh : Function.Bijective ((toSheaf Y.sheaf cY (j ''ᵁ ⊤)) ∘ a) := by
    change Function.Bijective (fun x => toSheaf Y.sheaf cY (j ''ᵁ ⊤) (a x))
    change Function.Bijective (fun x : KaehlerDifferential ℂ A =>
      (openDifferentialIso j (affineCoefficient A) cY hc).inv.val.app (op ⊤)
        (affineGlobal x)) at h
    have eqf : (fun x => toSheaf Y.sheaf cY (j ''ᵁ ⊤) (a x)) =
        (fun x : KaehlerDifferential ℂ A =>
        (openDifferentialIso j (affineCoefficient A) cY hc).inv.val.app (op ⊤) (affineGlobal x)) :=
      funext (chart_comparison j cY hc)
    rw [eqf]
    exact h
  exact (Function.Bijective.of_comp_iff _ a.bijective).mp hh

end Chart
theorem toSheaf_bijective_of_isAffineOpen {Y : Scheme.{0}} (cY : ℂ →+* Γ(Y,⊤))
    (W : Y.Opens) (hW : IsAffineOpen W) : Function.Bijective (toSheaf Y.sheaf cY W) := by
  let j := hW.fromSpec
  let cX := j.appTop.hom.comp cY
  let e := Scheme.ΓSpecIso Γ(Y,W)
  let : Algebra ℂ Γ(Y,W) := (e.hom.hom.comp cX).toAlgebra
  have he : affineCoefficient Γ(Y,W) = cX := by
    ext a
    change e.inv (e.hom (cX a)) = cX a
    exact Iso.hom_inv_id_apply e _
  have hc (U : Y.Opens) (a : ℂ) :
      j.app U (coefficientOn Y.sheaf cY U a) =
        coefficientOn (Spec.structureSheaf Γ(Y,W)) (affineCoefficient Γ(Y,W)) (j ⁻¹ᵁ U) a := by
    rw [he]
    exact congrArg (fun k => k (cY a)) (j.naturality (homOfLE (show U ≤ ⊤ from le_top)).op)
  have H := toSheaf_bijective_on_chart j cY hc
  have hU : (j ''ᵁ ⊤) = W := j.image_top_eq_opensRange.trans hW.opensRange_fromSpec
  exact hU ▸ H

end CycleQ2AffineOpenOrdinaryDifferentials
end
#print axioms CycleQ2AffineOpenOrdinaryDifferentials.toSheaf_bijective_of_isAffineOpen
