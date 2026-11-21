import Proposal.GeometricOpenDifferentialSheaf
import Proposal.GeometricExteriorPullComposition

/-!
# Actual differential sections under a scheme isomorphism

The canonical scheme differential map is bijective on every actual open
when the scheme map is an isomorphism. Its section maps commute with
restriction and carry the genuine universal differential of a function
to that of its actual pullback.

Prepared for fqlx with OpenAI ChatGPT assistance; see solution.md.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2IsoDifferentialSections
open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open CycleQ2GeometricDifferentialSheaf CycleQ2GeometricSchemeDifferentialMap
open CycleQ2GeometricOpenDifferentialSheaf

variable {X Y : Scheme.{0}} (e : X ≅ Y)
  (cX : ℂ →+* Γ(X,⊤)) (cY : ℂ →+* Γ(Y,⊤))

/-- Keeping compatibility as a proposition with an explicit field prevents
concrete projective section rings from unfolding while its type is matched. -/
structure Compatible : Prop where
  app : CycleQ2ExteriorPullComposition.compatible e.hom cX cY

theorem compatible_over (s : X ⟶ Spec (CommRingCat.of ℂ))
    (t : Y ⟶ Spec (CommRingCat.of ℂ)) (h : e.hom ≫ t = s) :
    Compatible e (CycleQ2GeometricAffineChartSections.schemeCoefficient s)
      (CycleQ2GeometricAffineChartSections.schemeCoefficient t) :=
  ⟨CycleQ2ExteriorPullComposition.compatible_over e.hom s t h⟩

variable (hc : Compatible e cX cY)

abbrev source : Y.Modules := differentialSheaf Y.sheaf cY
abbrev target : X.Modules := differentialSheaf X.sheaf cX

def pull (U : Y.Opens) :
    (source (Y := Y) cY).val.obj (op U) →+ (target (X := X) cX).val.obj (op (e.hom ⁻¹ᵁ U)) :=
  ((schemeDifferentialMap e.hom cX cY hc.app).val.app (op U)).hom.toAddMonoidHom

theorem pull_bijective (U : Y.Opens) : Function.Bijective (pull e cX cY hc U) := by
  have hU : e.hom ''ᵁ (e.hom ⁻¹ᵁ U) = U := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Hom.opensRange_of_isIso, top_inf_eq]
  have hr : Function.Bijective ((source (Y := Y) cY).val.map
      (homOfLE (e.hom.image_preimage_le U)).op) := by
    have hh : homOfLE (e.hom.image_preimage_le U) = eqToHom hU := Subsingleton.elim _ _
    rw [hh]
    change Function.Bijective ((source (Y := Y) cY).presheaf.map (eqToHom hU).op)
    exact ConcreteCategory.bijective_of_isIso _
  have hi := ConcreteCategory.bijective_of_isIso
    ((SheafOfModules.evaluation _ (op (e.hom ⁻¹ᵁ U))).map
      (openDifferentialIso e.hom cX cY hc.app).hom)
  have hp : pull e cX cY hc U =
      fun x => (openDifferentialIso e.hom cX cY hc.app).hom.val.app (op (e.hom ⁻¹ᵁ U))
        ((source (Y := Y) cY).val.map (homOfLE (e.hom.image_preimage_le U)).op x) := by
    funext x
    have ha := openDifferentialIso_adjunct e.hom cX cY hc.app
    rw [Adjunction.homEquiv_apply] at ha
    exact congrArg (fun f => f.val.app (op U) x) ha.symm
  rw [hp]
  exact hi.comp hr

def sectionEquiv (U : Y.Opens) :
    (source (Y := Y) cY).val.obj (op U) ≃+ (target (X := X) cX).val.obj (op (e.hom ⁻¹ᵁ U)) :=
  AddEquiv.ofBijective (pull e cX cY hc U) (pull_bijective e cX cY hc U)

theorem pull_restrict {U V : Y.Opens} (h : V ≤ U) (s : (source (Y := Y) cY).val.obj (op U)) :
    pull e cX cY hc V ((source (Y := Y) cY).val.map (homOfLE h).op s) =
      (target (X := X) cX).val.map ((Opens.map e.hom.base).map (homOfLE h)).op
        (pull e cX cY hc U s) :=
  ConcreteCategory.congr_hom ((schemeDifferentialMap e.hom cX cY hc.app).val.naturality (homOfLE h).op) s

def pullMap : CycleQ2GeometricModuleLocalIso.addSheaf (source (Y := Y) cY) ⟶
    CycleQ2FiniteCechOrbitPullback.push e.hom.base
      (CycleQ2GeometricModuleLocalIso.addSheaf (target (X := X) cX)) where
  hom.app U := AddCommGrpCat.ofHom (pull e cX cY hc U.unop)
  hom.naturality {U V} h := by
    apply ConcreteCategory.hom_ext
    intro s
    exact pull_restrict e cX cY hc h.unop.le s

theorem pullMap_app (U : Y.Opens) (s : (source (Y := Y) cY).val.obj (op U)) :
    CycleQ2CechTwoToDerived.app (pullMap e cX cY hc) U s = pull e cX cY hc U s := rfl

theorem pull_edge {ι : Type} (U : ι → Y.Opens)
    (b : CycleQ2FiniteInjectiveCech.One (CycleQ2GeometricModuleLocalIso.addSheaf (source (Y := Y) cY)) U)
    (i j : ι) (P : Y.Opens) (hi : P ≤ U i) (hj : P ≤ U j) :
    CycleQ2FiniteInjectiveCech.edgeValue (CycleQ2GeometricModuleLocalIso.addSheaf (target (X := X) cX))
      (CycleQ2FiniteCechOrbitPullback.cover e.hom.base U)
      (CycleQ2FiniteCechOrbitPullback.pullOne e.hom.base (pullMap e cX cY hc) U b)
      i j (e.hom ⁻¹ᵁ P) (fun _ hx => hi hx) (fun _ hx => hj hx) =
        pull e cX cY hc P
          (CycleQ2FiniteInjectiveCech.edgeValue (CycleQ2GeometricModuleLocalIso.addSheaf (source (Y := Y) cY))
            U b i j P hi hj) := by
  have h := CycleQ2FiniteCechOrbitPullback.edgeValue_pullOne e.hom.base (pullMap e cX cY hc)
    U b i j (show e.hom ⁻¹ᵁ P ≤ e.hom ⁻¹ᵁ P from le_rfl) hi hj
  change _ = CycleQ2GeometricSheafLocalIso.res
    (CycleQ2GeometricModuleLocalIso.addSheaf (target (X := X) cX)) le_rfl
      (pull e cX cY hc P
        (CycleQ2FiniteInjectiveCech.edgeValue (CycleQ2GeometricModuleLocalIso.addSheaf (source (Y := Y) cY))
          U b i j P hi hj)) at h
  rw [CycleQ2GeometricSheafLocalIso.res_self] at h
  exact h


def ringEquiv (U : Y.Opens) : Γ(Y,U) ≃+* Γ(X,e.hom ⁻¹ᵁ U) :=
  (asIso (e.hom.app U)).commRingCatIsoToRingEquiv

def inverseUnit (U : Y.Opens) (v : Γ(X,e.hom ⁻¹ᵁ U)ˣ) : Γ(Y,U)ˣ :=
  Units.map (ringEquiv e U).symm.toMonoidHom v

theorem map_inverseUnit (U : Y.Opens) (v : Γ(X,e.hom ⁻¹ᵁ U)ˣ) :
    Units.map (e.hom.app U).hom.toMonoidHom (inverseUnit e U v) = v := by
  apply Units.ext
  exact (ringEquiv e U).apply_symm_apply _

theorem pull_D (U : Y.Opens) (a : Γ(Y,U)) :
    pull e cX cY hc U ((universalDifferential Y.sheaf cY).d a) =
      (universalDifferential X.sheaf cX).d (e.hom.app U a) :=
  schemeDifferentialMap_D e.hom cX cY hc.app U a

theorem pull_smul (U : Y.Opens) (a : Γ(Y,U)) (s : (source (Y := Y) cY).val.obj (op U)) :
    pull e cX cY hc U (a • s) = e.hom.app U a • pull e cX cY hc U s :=
  ((schemeDifferentialMap e.hom cX cY hc.app).val.app (op U)).hom.map_smul a s

def scaledLog (U : X.Opens) (a : Γ(X,U)) (v : Γ(X,U)ˣ) :
    (CycleQ2GeometricModuleLocalIso.addSheaf (target (X := X) cX)).obj.obj (op U) :=
  a • ((v⁻¹ : Γ(X,U)ˣ).val • (universalDifferential X.sheaf cX).d (X := op U) (v : Γ(X,U)))

def scalarLog (U : X.Opens) (c : ℂ) (v : Γ(X,U)ˣ) :
    (CycleQ2GeometricModuleLocalIso.addSheaf (target (X := X) cX)).obj.obj (op U) :=
  scaledLog (X := X) cX U (coefficientOn X.sheaf cX U c) v

theorem pull_scalarLog (U : Y.Opens) (c : ℂ) (v : Γ(Y,U)ˣ) :
    pull e cX cY hc U (scalarLog (X := Y) cY U c v) =
      scalarLog (X := X) cX (e.hom ⁻¹ᵁ U) c (Units.map (e.hom.app U).hom.toMonoidHom v) := by
  unfold scalarLog scaledLog
  rw [pull_smul,pull_smul,pull_D,hc.app]
  rfl

theorem pull_scalarLog_inverseUnit (U : Y.Opens) (c : ℂ) (v : Γ(X,e.hom ⁻¹ᵁ U)ˣ) :
    pull e cX cY hc U (scalarLog (X := Y) cY U c (inverseUnit e U v)) =
      scalarLog (X := X) cX (e.hom ⁻¹ᵁ U) c v := by
  rw [pull_scalarLog,map_inverseUnit]

end CycleQ2IsoDifferentialSections
end
#print axioms CycleQ2IsoDifferentialSections.pull_bijective
#print axioms CycleQ2IsoDifferentialSections.pull_restrict
#print axioms CycleQ2IsoDifferentialSections.pull_D
