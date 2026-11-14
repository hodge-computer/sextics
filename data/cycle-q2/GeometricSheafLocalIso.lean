import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
import Mathlib.Algebra.Category.Grp.Limits

/-!
# Gluing actual local isomorphisms of additive sheaves

Compatible natural isomorphisms on all subopens of two covering opens give
an isomorphism of the actual sheaves. Each component is constructed by the
sheaf's unique gluing property, and its restrictions are the specified local
maps. Global bijectivity is proved from the local inverse maps.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
universe u

namespace CycleQ2GeometricSheafLocalIso

open CategoryTheory Opposite TopologicalSpace

variable {X : TopCat.{u}}

abbrev AddSheaf (X : TopCat.{u}) := TopCat.Sheaf AddCommGrpCat.{u} X

/-- The actual restriction homomorphism of the given sheaf. -/
def res (F : AddSheaf X) {O P : Opens X} (h : P ≤ O) :
    F.obj.obj (op O) →+ F.obj.obj (op P) :=
  (F.obj.map (homOfLE h).op).hom

@[simp] theorem res_self (F : AddSheaf X) (O : Opens X) (s : F.obj.obj (op O)) :
    res F (le_refl O) s = s := by
  change F.obj.map (𝟙 (op O)) s = s
  simp

theorem res_comp (F : AddSheaf X) {O P Q : Opens X} (hPO : P ≤ O) (hQP : Q ≤ P)
    (s : F.obj.obj (op O)) : res F hQP (res F hPO s) = res F (hQP.trans hPO) s := by
  change (F.obj.map (homOfLE hPO).op ≫ F.obj.map (homOfLE hQP).op) s = _
  rw [← F.obj.map_comp]
  rfl

/-- A natural family of actual additive equivalences on every subopen. -/
structure PatchIso (F G : AddSheaf X) (U : Opens X) where
  app (O : Opens X) (hO : O ≤ U) : F.obj.obj (op O) ≃+ G.obj.obj (op O)
  naturality {O P : Opens X} (hPO : P ≤ O) (hO : O ≤ U) (s : F.obj.obj (op O)) :
    res G hPO (app O hO s) = app P (hPO.trans hO) (res F hPO s)

namespace PatchIso
variable {F G : AddSheaf X} {U V : Opens X}

def symm (e : PatchIso F G U) : PatchIso G F U where
  app O hO := (e.app O hO).symm
  naturality hPO hO s := by
    apply (e.app _ (hPO.trans hO)).injective
    rw [AddEquiv.apply_symm_apply]
    have h := e.naturality hPO hO ((e.app _ hO).symm s)
    rw [AddEquiv.apply_symm_apply] at h
    exact h.symm

/-- The two local maps agree on every common subopen. -/
def Compatible (eU : PatchIso F G U) (eV : PatchIso F G V) : Prop :=
  ∀ (O : Opens X) (hU : O ≤ U) (hV : O ≤ V) (s : F.obj.obj (op O)),
    eU.app O hU s = eV.app O hV s

theorem Compatible.symm {eU : PatchIso F G U} {eV : PatchIso F G V}
    (h : Compatible eU eV) : Compatible eU.symm eV.symm := by
  intro O hU hV s
  apply (eU.app O hU).injective
  change eU.app O hU ((eU.app O hU).symm s) =
    eU.app O hU ((eV.app O hV).symm s)
  rw [AddEquiv.apply_symm_apply, h O hU hV ((eV.app O hV).symm s),
    AddEquiv.apply_symm_apply]

end PatchIso

/-- The two-open gluing principle, derived directly from sheaf unique gluing. -/
theorem existsUnique_pair (F : AddSheaf X) (O P Q : Opens X)
    (hP : P ≤ O) (hQ : Q ≤ O) (hcover : O ≤ P ⊔ Q)
    (p : F.obj.obj (op P)) (q : F.obj.obj (op Q))
    (hc : ∀ (W : Opens X) (hWP : W ≤ P) (hWQ : W ≤ Q),
      res F hWP p = res F hWQ q) :
    ∃! s : F.obj.obj (op O), res F hP s = p ∧ res F hQ s = q := by
  let W : Bool → Opens X := fun b => if b then P else Q
  let iWO : ∀ b, W b ⟶ O := fun b => by
    cases b
    · exact homOfLE hQ
    · exact homOfLE hP
  let sf : ∀ b, F.obj.obj (op (W b)) := fun b => by
    cases b
    · exact q
    · exact p
  have hW : O ≤ ⨆ b, W b := hcover.trans (sup_le (le_iSup W true) (le_iSup W false))
  have hsf : TopCat.Presheaf.IsCompatible F.obj W sf := by
    intro i j
    cases i <;> cases j
    · rfl
    · exact (hc (Q ⊓ P) inf_le_right inf_le_left).symm
    · exact hc (P ⊓ Q) inf_le_left inf_le_right
    · rfl
  obtain ⟨s, hs, hu⟩ := F.existsUnique_gluing' W O iWO hW sf hsf
  refine ⟨s, ⟨hs true, hs false⟩, ?_⟩
  intro t ht
  apply hu t
  intro b
  cases b
  · exact ht.2
  · exact ht.1

section Gluing

variable (F G : AddSheaf X) (U V : Opens X) (hcover : U ⊔ V = ⊤)
  (eU : PatchIso F G U) (eV : PatchIso F G V) (hc : eU.Compatible eV)

include hcover in
private theorem cover_on (O : Opens X) : O ≤ (O ⊓ U) ⊔ (O ⊓ V) := by
  rw [← inf_sup_left, hcover, inf_top_eq]

include hc in
private theorem image_compatible (O : Opens X) (s : F.obj.obj (op O))
    (W : Opens X) (hWU : W ≤ O ⊓ U) (hWV : W ≤ O ⊓ V) :
    res G hWU (eU.app (O ⊓ U) inf_le_right (res F inf_le_left s)) =
      res G hWV (eV.app (O ⊓ V) inf_le_right (res F inf_le_left s)) := by
  rw [eU.naturality, eV.naturality, res_comp, res_comp]
  exact hc W _ _ _

include hcover hc in
private theorem image_exists (O : Opens X) (s : F.obj.obj (op O)) :
    ∃! t : G.obj.obj (op O),
      res G (show O ⊓ U ≤ O from inf_le_left) t =
          eU.app (O ⊓ U) inf_le_right (res F inf_le_left s) ∧
      res G (show O ⊓ V ≤ O from inf_le_left) t =
          eV.app (O ⊓ V) inf_le_right (res F inf_le_left s) :=
  existsUnique_pair G O (O ⊓ U) (O ⊓ V) inf_le_left inf_le_left (cover_on U V hcover O)
    _ _ (image_compatible F G U V eU eV hc O s)

/-- The actual global section is chosen from the proved unique gluing. -/
def mapSection (O : Opens X) (s : F.obj.obj (op O)) : G.obj.obj (op O) :=
  Classical.choose (image_exists F G U V hcover eU eV hc O s)

@[simp] theorem mapSection_restrictU (O : Opens X) (s : F.obj.obj (op O)) :
    res G (show O ⊓ U ≤ O from inf_le_left) (mapSection F G U V hcover eU eV hc O s) =
      eU.app (O ⊓ U) inf_le_right (res F inf_le_left s) :=
  (Classical.choose_spec (image_exists F G U V hcover eU eV hc O s)).1.1

@[simp] theorem mapSection_restrictV (O : Opens X) (s : F.obj.obj (op O)) :
    res G (show O ⊓ V ≤ O from inf_le_left) (mapSection F G U V hcover eU eV hc O s) =
      eV.app (O ⊓ V) inf_le_right (res F inf_le_left s) :=
  (Classical.choose_spec (image_exists F G U V hcover eU eV hc O s)).1.2

include hcover in
private theorem local_ext (H : AddSheaf X) (O : Opens X) (s t : H.obj.obj (op O))
    (hU : res H (show O ⊓ U ≤ O from inf_le_left) s = res H inf_le_left t)
    (hV : res H (show O ⊓ V ≤ O from inf_le_left) s = res H inf_le_left t) : s = t :=
  H.eq_of_locally_eq₂ (homOfLE (show O ⊓ U ≤ O from inf_le_left))
    (homOfLE (show O ⊓ V ≤ O from inf_le_left)) (cover_on U V hcover O) s t hU hV

theorem mapSection_add (O : Opens X) (s t : F.obj.obj (op O)) :
    mapSection F G U V hcover eU eV hc O (s + t) =
      mapSection F G U V hcover eU eV hc O s + mapSection F G U V hcover eU eV hc O t := by
  apply local_ext U V hcover G O
  · simp only [mapSection_restrictU, map_add]
  · simp only [mapSection_restrictV, map_add]

/-- A component on an arbitrary subopen of U is exactly the prescribed map. -/
theorem mapSection_of_leU (O : Opens X) (hO : O ≤ U) (s : F.obj.obj (op O)) :
    mapSection F G U V hcover eU eV hc O s = eU.app O hO s := by
  apply local_ext U V hcover G O
  · rw [mapSection_restrictU, eU.naturality]
  · rw [mapSection_restrictV, eU.naturality]
    exact (hc (O ⊓ V) _ _ _).symm

theorem mapSection_of_leV (O : Opens X) (hO : O ≤ V) (s : F.obj.obj (op O)) :
    mapSection F G U V hcover eU eV hc O s = eV.app O hO s := by
  apply local_ext U V hcover G O
  · rw [mapSection_restrictU, eV.naturality]
    exact hc (O ⊓ U) _ _ _
  · rw [mapSection_restrictV, eV.naturality]

/-- Restriction of the glued section to any open lying in the first patch. -/
theorem mapSection_restrict_toU {O P : Opens X} (hPO : P ≤ O) (hPU : P ≤ U)
    (s : F.obj.obj (op O)) :
    res G hPO (mapSection F G U V hcover eU eV hc O s) =
      eU.app P hPU (res F hPO s) := by
  calc
    _ = res G (le_inf hPO hPU)
        (res G (show O ⊓ U ≤ O from inf_le_left)
          (mapSection F G U V hcover eU eV hc O s)) := by rw [res_comp]
    _ = _ := by rw [mapSection_restrictU, eU.naturality, res_comp]

theorem mapSection_restrict_toV {O P : Opens X} (hPO : P ≤ O) (hPV : P ≤ V)
    (s : F.obj.obj (op O)) :
    res G hPO (mapSection F G U V hcover eU eV hc O s) =
      eV.app P hPV (res F hPO s) := by
  calc
    _ = res G (le_inf hPO hPV)
        (res G (show O ⊓ V ≤ O from inf_le_left)
          (mapSection F G U V hcover eU eV hc O s)) := by rw [res_comp]
    _ = _ := by rw [mapSection_restrictV, eV.naturality, res_comp]

/-- Naturality is proved by the sheaf's local equality principle. -/
theorem mapSection_naturality {O P : Opens X} (hPO : P ≤ O) (s : F.obj.obj (op O)) :
    res G hPO (mapSection F G U V hcover eU eV hc O s) =
      mapSection F G U V hcover eU eV hc P (res F hPO s) := by
  apply local_ext U V hcover G P
  · rw [res_comp,
      mapSection_restrict_toU F G U V hcover eU eV hc (inf_le_left.trans hPO) inf_le_right,
      mapSection_restrictU, res_comp]
  · rw [res_comp,
      mapSection_restrict_toV F G U V hcover eU eV hc (inf_le_left.trans hPO) inf_le_right,
      mapSection_restrictV, res_comp]

def sectionHom (O : Opens X) : F.obj.obj (op O) →+ G.obj.obj (op O) where
  toFun := mapSection F G U V hcover eU eV hc O
  map_zero' := by
    apply local_ext U V hcover G O
    · simp only [mapSection_restrictU, map_zero]
    · simp only [mapSection_restrictV, map_zero]
  map_add' := mapSection_add F G U V hcover eU eV hc O

/-- The glued maps are a genuine morphism in the sheaf category. -/
def glueHom : F ⟶ G where
  hom :=
    { app := fun O => AddCommGrpCat.ofHom (sectionHom F G U V hcover eU eV hc O.unop)
      naturality := by
        intro O P f
        apply AddCommGrpCat.ext
        intro s
        change mapSection F G U V hcover eU eV hc P.unop
          (res F (leOfHom f.unop) s) =
            res G (leOfHom f.unop) (mapSection F G U V hcover eU eV hc O.unop s)
        exact (mapSection_naturality F G U V hcover eU eV hc (leOfHom f.unop) s).symm }

/-- The glued inverse is a left inverse, because this holds on both patches. -/
theorem mapSection_symm_apply (O : Opens X) (s : F.obj.obj (op O)) :
    mapSection G F U V hcover eU.symm eV.symm hc.symm O
      (mapSection F G U V hcover eU eV hc O s) = s := by
  apply local_ext U V hcover F O
  · rw [mapSection_restrictU, mapSection_restrictU]
    exact (eU.app (O ⊓ U) inf_le_right).symm_apply_apply _
  · rw [mapSection_restrictV, mapSection_restrictV]
    exact (eV.app (O ⊓ V) inf_le_right).symm_apply_apply _

/-- The glued inverse is a right inverse by the same sheaf equality principle. -/
theorem mapSection_apply_symm (O : Opens X) (s : G.obj.obj (op O)) :
    mapSection F G U V hcover eU eV hc O
      (mapSection G F U V hcover eU.symm eV.symm hc.symm O s) = s := by
  apply local_ext U V hcover G O
  · rw [mapSection_restrictU, mapSection_restrictU]
    exact (eU.app (O ⊓ U) inf_le_right).apply_symm_apply _
  · rw [mapSection_restrictV, mapSection_restrictV]
    exact (eV.app (O ⊓ V) inf_le_right).apply_symm_apply _

/-- The actual sheaf isomorphism constructed from the compatible local data. -/
def glueIso : F ≅ G where
  hom := glueHom F G U V hcover eU eV hc
  inv := glueHom G F U V hcover eU.symm eV.symm hc.symm
  hom_inv_id := by
    apply CategoryTheory.Sheaf.hom_ext
    apply NatTrans.ext
    funext O
    apply AddCommGrpCat.ext
    intro s
    exact mapSection_symm_apply F G U V hcover eU eV hc O.unop s
  inv_hom_id := by
    apply CategoryTheory.Sheaf.hom_ext
    apply NatTrans.ext
    funext O
    apply AddCommGrpCat.ext
    intro s
    exact mapSection_apply_symm F G U V hcover eU eV hc O.unop s

@[simp] theorem glueIso_hom_app (O : Opens X) (s : F.obj.obj (op O)) :
    (glueIso F G U V hcover eU eV hc).hom.hom.app (op O) s =
      mapSection F G U V hcover eU eV hc O s := rfl

@[simp] theorem glueIso_hom_app_of_leU (O : Opens X) (hO : O ≤ U)
    (s : F.obj.obj (op O)) :
    (glueIso F G U V hcover eU eV hc).hom.hom.app (op O) s = eU.app O hO s :=
  mapSection_of_leU F G U V hcover eU eV hc O hO s

@[simp] theorem glueIso_hom_app_of_leV (O : Opens X) (hO : O ≤ V)
    (s : F.obj.obj (op O)) :
    (glueIso F G U V hcover eU eV hc).hom.hom.app (op O) s = eV.app O hO s :=
  mapSection_of_leV F G U V hcover eU eV hc O hO s

@[simp] theorem glueIso_inv_app_of_leU (O : Opens X) (hO : O ≤ U)
    (s : G.obj.obj (op O)) :
    (glueIso F G U V hcover eU eV hc).inv.hom.app (op O) s = (eU.app O hO).symm s :=
  mapSection_of_leU G F U V hcover eU.symm eV.symm hc.symm O hO s

@[simp] theorem glueIso_inv_app_of_leV (O : Opens X) (hO : O ≤ V)
    (s : G.obj.obj (op O)) :
    (glueIso F G U V hcover eU eV hc).inv.hom.app (op O) s = (eV.app O hO).symm s :=
  mapSection_of_leV G F U V hcover eU.symm eV.symm hc.symm O hO s

#print axioms glueIso
#print axioms glueIso_hom_app_of_leU
#print axioms glueIso_hom_app_of_leV
#print axioms glueIso_inv_app_of_leU
#print axioms glueIso_inv_app_of_leV

end Gluing

end CycleQ2GeometricSheafLocalIso
end
