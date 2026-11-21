import Proposal.GeometricSurfaceNormalCharts

/-!
# Universal differentials under an actual open immersion

The genuine restriction of the original differential sheaf remains
universal. Its derivation uses the inverse of the actual open-immersion
section isomorphism. The restriction/pushforward adjunction constructs
the lift, and its formulas prove universality on all actual opens.

Prepared for fqlx with OpenAI ChatGPT assistance; see solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2GeometricOpenDifferentialSheaf

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
  CycleQ2GeometricDifferentialSheaf CycleQ2GeometricSchemeDifferentialMap

variable {X Y : Scheme.{0}} (j : X ⟶ Y) [IsOpenImmersion j]
  (cX : ℂ →+* Γ(X, ⊤)) (cY : ℂ →+* Γ(Y, ⊤))
  (hc : ∀ (U : Y.Opens) (c : ℂ),
    j.app U (coefficientOn Y.sheaf cY U c) =
      coefficientOn X.sheaf cX (j ⁻¹ᵁ U) c)

abbrev RestrictedDifferential : X.Modules :=
  (Scheme.Modules.restrictFunctor j).obj (differentialSheaf Y.sheaf cY)

include hc in
theorem appIso_coefficient (U : X.Opens) (c : ℂ) :
    (j.appIso U).inv (coefficientOn X.sheaf cX U c) =
      coefficientOn Y.sheaf cY (j ''ᵁ U) c := by
  apply (j.appIso U).commRingCatIsoToRingEquiv.injective
  change (j.appIso U).hom ((j.appIso U).inv (coefficientOn X.sheaf cX U c)) =
    (j.appIso U).hom (coefficientOn Y.sheaf cY (j ''ᵁ U) c)
  rw [Iso.inv_hom_id_apply, Scheme.Hom.appIso_hom]
  change coefficientOn X.sheaf cX U c =
    X.presheaf.map (eqToHom (j.preimage_image_eq U).symm).op
      (j.app (j ''ᵁ U) (coefficientOn Y.sheaf cY (j ''ᵁ U) c))
  rw [hc]
  unfold coefficientOn
  change X.presheaf.map _ (cX c) = (X.presheaf.map _ ≫ X.presheaf.map _) (cX c)
  rw [← X.presheaf.map_comp]
  congr 2

def restrictedUniversal :
    (RestrictedDifferential j cY).val.Derivation' (coefficientMap X.sheaf cX) where
  d {U} := ((universalDifferential Y.sheaf cY).d (X := op (j ''ᵁ U.unop))).comp
    (j.appIso U.unop).inv.hom.toAddMonoidHom
  d_mul {U} a b := by
    change (universalDifferential Y.sheaf cY).d ((j.appIso U.unop).inv (a * b)) = _
    rw [map_mul, (universalDifferential Y.sheaf cY).d_mul]
    rfl
  d_map {U V} f a := by
    change (universalDifferential Y.sheaf cY).d
        ((j.appIso V.unop).inv (X.presheaf.map f a)) =
      (differentialSheaf Y.sheaf cY).val.map (j.opensFunctor.map f.unop).op
        ((universalDifferential Y.sheaf cY).d ((j.appIso U.unop).inv a))
    have hn := congrArg (fun k => k a) (j.appIso_inv_naturality f)
    exact (congrArg ((universalDifferential Y.sheaf cY).d
      (X := op (j ''ᵁ V.unop))) hn).trans
        ((universalDifferential Y.sheaf cY).d_map _ _)
  d_app {U} c := by
    change (universalDifferential Y.sheaf cY).d
      ((j.appIso U.unop).inv (coefficientOn X.sheaf cX U.unop c)) = 0
    rw [appIso_coefficient j cX cY hc]
    exact (universalDifferential Y.sheaf cY).d_app c

def pushDerivation (M : X.Modules)
    (d : M.val.Derivation' (coefficientMap X.sheaf cX)) :
    ((Scheme.Modules.pushforward j).obj M).val.Derivation' (coefficientMap Y.sheaf cY) where
  d {U} := (d.d (X := op (j ⁻¹ᵁ U.unop))).comp (j.app U.unop).hom.toAddMonoidHom
  d_mul {U} a b := by
    change d.d (j.app U.unop (a * b)) = _
    rw [map_mul, d.d_mul]
    rfl
  d_map {U V} f a := by
    change d.d (j.app V.unop (Y.presheaf.map f a)) =
      M.val.map ((Opens.map j.base).map f.unop).op (d.d (j.app U.unop a))
    have hn := ConcreteCategory.congr_hom (j.naturality f) a
    change j.app V.unop (Y.presheaf.map f a) =
      X.presheaf.map ((Opens.map j.base).map f.unop).op (j.app U.unop a) at hn
    rw [hn]
    exact d.d_map _ _
  d_app {U} c := by
    change d.d (j.app U.unop (coefficientOn Y.sheaf cY U.unop c)) = 0
    rw [hc]
    exact d.d_app c

def restrictedLift (M : X.Modules)
    (d : M.val.Derivation' (coefficientMap X.sheaf cX)) :
    RestrictedDifferential j cY ⟶ M :=
  ((Scheme.Modules.restrictAdjunction j).homEquiv
    (differentialSheaf Y.sheaf cY) M).symm
      (differentialLift Y.sheaf cY _ (pushDerivation j cX cY hc M d))

theorem restrictedLift_fac (M : X.Modules)
    (d : M.val.Derivation' (coefficientMap X.sheaf cX)) :
    (restrictedUniversal j cX cY hc).postcomp (restrictedLift j cX cY hc M d).val = d := by
  ext U a
  rw [restrictedLift, Adjunction.homEquiv_symm_apply]
  change M.presheaf.map (eqToHom (j.preimage_image_eq U.unop).symm).op
    ((differentialLift Y.sheaf cY _ (pushDerivation j cX cY hc M d)).val.app
      (op (j ''ᵁ U.unop)) ((universalDifferential Y.sheaf cY).d ((j.appIso U.unop).inv a))) =
    d.d a
  have hfac := PresheafOfModules.Derivation.congr_d
    (differentialLift_fac Y.sheaf cY _ (pushDerivation j cX cY hc M d))
      ((j.appIso U.unop).inv a)
  change (differentialLift Y.sheaf cY _ (pushDerivation j cX cY hc M d)).val.app
      (op (j ''ᵁ U.unop)) ((universalDifferential Y.sheaf cY).d ((j.appIso U.unop).inv a)) =
    d.d (j.app (j ''ᵁ U.unop) ((j.appIso U.unop).inv a)) at hfac
  refine (congrArg
    (M.presheaf.map (eqToHom (j.preimage_image_eq U.unop).symm).op) hfac).trans ?_
  exact (d.d_map (eqToHom (j.preimage_image_eq U.unop).symm).op
    (j.app (j ''ᵁ U.unop) ((j.appIso U.unop).inv a))).symm.trans
      (congrArg (d.d (X := U))
        (congrArg (fun f => f a) (j.appIso_inv_app_presheafMap U.unop)))

theorem restrictedLift_unique (M : X.Modules) (f g : RestrictedDifferential j cY ⟶ M)
    (h : (restrictedUniversal j cX cY hc).postcomp f.val =
      (restrictedUniversal j cX cY hc).postcomp g.val) : f = g := by
  apply ((Scheme.Modules.restrictAdjunction j).homEquiv
    (differentialSheaf Y.sheaf cY) M).injective
  apply differentialLift_unique Y.sheaf cY
  ext U a
  rw [Adjunction.homEquiv_apply, Adjunction.homEquiv_apply]
  change f.val.app (op (j ⁻¹ᵁ U.unop))
      ((differentialSheaf Y.sheaf cY).val.map (homOfLE (j.image_preimage_le U.unop)).op
        ((universalDifferential Y.sheaf cY).d a)) =
    g.val.app (op (j ⁻¹ᵁ U.unop))
      ((differentialSheaf Y.sheaf cY).val.map (homOfLE (j.image_preimage_le U.unop)).op
        ((universalDifferential Y.sheaf cY).d a))
  have hh := PresheafOfModules.Derivation.congr_d
    (X := op (j ⁻¹ᵁ U.unop)) h (j.app U.unop a)
  change f.val.app (op (j ⁻¹ᵁ U.unop))
      ((universalDifferential Y.sheaf cY).d ((j.appIso (j ⁻¹ᵁ U.unop)).inv (j.app U.unop a))) =
    g.val.app (op (j ⁻¹ᵁ U.unop))
      ((universalDifferential Y.sheaf cY).d ((j.appIso (j ⁻¹ᵁ U.unop)).inv (j.app U.unop a))) at hh
  have ha := congrArg (fun k => k a) (j.app_appIso_inv U.unop)
  change (j.appIso (j ⁻¹ᵁ U.unop)).inv (j.app U.unop a) =
    Y.presheaf.map (homOfLE (j.image_preimage_le U.unop)).op a at ha
  rw [ha] at hh
  exact (congrArg (f.val.app (op (j ⁻¹ᵁ U.unop)))
    ((universalDifferential Y.sheaf cY).d_map _ a)).symm.trans
      (hh.trans (congrArg (g.val.app (op (j ⁻¹ᵁ U.unop)))
        ((universalDifferential Y.sheaf cY).d_map _ a)))

def openDifferentialIso : RestrictedDifferential j cY ≅ differentialSheaf X.sheaf cX where
  hom := restrictedLift j cX cY hc _ (universalDifferential X.sheaf cX)
  inv := differentialLift X.sheaf cX _ (restrictedUniversal j cX cY hc)
  hom_inv_id := by
    apply restrictedLift_unique j cX cY hc
    ext U a
    change (differentialLift X.sheaf cX _ (restrictedUniversal j cX cY hc)).val.app U
      ((restrictedLift j cX cY hc _ (universalDifferential X.sheaf cX)).val.app U
        ((restrictedUniversal j cX cY hc).d a)) = (restrictedUniversal j cX cY hc).d a
    have h₁ := PresheafOfModules.Derivation.congr_d
      (restrictedLift_fac j cX cY hc _ (universalDifferential X.sheaf cX)) a
    change (restrictedLift j cX cY hc _ (universalDifferential X.sheaf cX)).val.app U
      ((restrictedUniversal j cX cY hc).d a) = (universalDifferential X.sheaf cX).d a at h₁
    exact (congrArg
      ((differentialLift X.sheaf cX _ (restrictedUniversal j cX cY hc)).val.app U) h₁).trans
        (PresheafOfModules.Derivation.congr_d
          (differentialLift_fac X.sheaf cX _ (restrictedUniversal j cX cY hc)) a)
  inv_hom_id := by
    apply differentialLift_unique X.sheaf cX
    ext U a
    change (restrictedLift j cX cY hc _ (universalDifferential X.sheaf cX)).val.app U
      ((differentialLift X.sheaf cX _ (restrictedUniversal j cX cY hc)).val.app U
        ((universalDifferential X.sheaf cX).d a)) = (universalDifferential X.sheaf cX).d a
    have h₁ := PresheafOfModules.Derivation.congr_d
      (differentialLift_fac X.sheaf cX _ (restrictedUniversal j cX cY hc)) a
    change (differentialLift X.sheaf cX _ (restrictedUniversal j cX cY hc)).val.app U
      ((universalDifferential X.sheaf cX).d a) = (restrictedUniversal j cX cY hc).d a at h₁
    exact (congrArg
      ((restrictedLift j cX cY hc _ (universalDifferential X.sheaf cX)).val.app U) h₁).trans
        (PresheafOfModules.Derivation.congr_d
          (restrictedLift_fac j cX cY hc _ (universalDifferential X.sheaf cX)) a)

theorem openDifferentialIso_hom_D (U : X.Opens) (a : Γ(X, U)) :
    (openDifferentialIso j cX cY hc).hom.val.app (op U)
      ((universalDifferential Y.sheaf cY).d ((j.appIso U).inv a)) =
        (universalDifferential X.sheaf cX).d a :=
  PresheafOfModules.Derivation.congr_d
    (restrictedLift_fac j cX cY hc _ (universalDifferential X.sheaf cX)) a

theorem openDifferentialIso_inv_D (U : X.Opens) (a : Γ(X, U)) :
    (openDifferentialIso j cX cY hc).inv.val.app (op U)
      ((universalDifferential X.sheaf cX).d a) =
        (universalDifferential Y.sheaf cY).d ((j.appIso U).inv a) :=
  PresheafOfModules.Derivation.congr_d
    (differentialLift_fac X.sheaf cX _ (restrictedUniversal j cX cY hc)) a

def pullbackOpenDifferentialIso :
    (Scheme.Modules.pullback j).obj (differentialSheaf Y.sheaf cY) ≅
      differentialSheaf X.sheaf cX :=
  ((Scheme.Modules.restrictFunctorIsoPullback j).app (differentialSheaf Y.sheaf cY)).symm ≪≫
    openDifferentialIso j cX cY hc

/-- The open comparison is the original scheme differential map under
the actual restriction/pushforward adjunction. -/
theorem openDifferentialIso_adjunct :
    (Scheme.Modules.restrictAdjunction j).homEquiv
        (differentialSheaf Y.sheaf cY) (differentialSheaf X.sheaf cX)
        (openDifferentialIso j cX cY hc).hom =
      schemeDifferentialMap j cX cY hc :=
  ((Scheme.Modules.restrictAdjunction j).homEquiv
    (differentialSheaf Y.sheaf cY) (differentialSheaf X.sheaf cX)).apply_symm_apply _

/-- The genuine pullback comparison has precisely the canonical
scheme-differential adjunct, rather than a newly chosen sheaf isomorphism. -/
theorem pullbackOpenDifferentialIso_adjunct :
    (Scheme.Modules.pullbackPushforwardAdjunction j).homEquiv
        (differentialSheaf Y.sheaf cY) (differentialSheaf X.sheaf cX)
        (pullbackOpenDifferentialIso j cX cY hc).hom =
      schemeDifferentialMap j cX cY hc := by
  calc
    _ = (Scheme.Modules.restrictAdjunction j).homEquiv
        (differentialSheaf Y.sheaf cY) (differentialSheaf X.sheaf cX)
        (openDifferentialIso j cX cY hc).hom := by
      rw [Adjunction.homEquiv_apply, Adjunction.homEquiv_apply]
      change (Scheme.Modules.pullbackPushforwardAdjunction j).unit.app
          (differentialSheaf Y.sheaf cY) ≫
          (Scheme.Modules.pushforward j).map
            (((Scheme.Modules.restrictFunctorIsoPullback j).app
              (differentialSheaf Y.sheaf cY)).inv ≫ (openDifferentialIso j cX cY hc).hom) = _
      have hu := Adjunction.unit_leftAdjointUniq_hom_app
        (Scheme.Modules.restrictAdjunction j) (Scheme.Modules.pullbackPushforwardAdjunction j)
        (differentialSheaf Y.sheaf cY)
      change (Scheme.Modules.restrictAdjunction j).unit.app (differentialSheaf Y.sheaf cY) ≫
          (Scheme.Modules.pushforward j).map
            (((Scheme.Modules.restrictFunctorIsoPullback j).app
              (differentialSheaf Y.sheaf cY)).hom) =
        (Scheme.Modules.pullbackPushforwardAdjunction j).unit.app
          (differentialSheaf Y.sheaf cY) at hu
      rw [← hu, Category.assoc, ← Functor.map_comp]
      simp only [Iso.hom_inv_id_assoc]
    _ = _ := openDifferentialIso_adjunct j cX cY hc

end CycleQ2GeometricOpenDifferentialSheaf

end

#print axioms CycleQ2GeometricOpenDifferentialSheaf.restrictedLift_fac
#print axioms CycleQ2GeometricOpenDifferentialSheaf.restrictedLift_unique
#print axioms CycleQ2GeometricOpenDifferentialSheaf.openDifferentialIso
#print axioms CycleQ2GeometricOpenDifferentialSheaf.pullbackOpenDifferentialIso_adjunct
