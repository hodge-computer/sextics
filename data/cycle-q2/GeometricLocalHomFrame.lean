import Proposal.GeometricIntrinsicNormal
import Proposal.GeometricCanonicalGluing

/-!
# Local target frames act on actual internal-Hom sheaves

The maps below postcompose every local component of an actual linear
sheaf morphism with the prescribed local target frame. They define a
natural linear isomorphism on every subopen and retain literal evaluation
of the original morphism. No freeness assumption on the source is used.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LocalHomFrame

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open CycleQ2GeometricDifferentialSheaf CycleQ2GeometricIntrinsicNormal
  CycleQ2GeometricIntrinsicCartierSequence
open CycleQ2GeometricModuleLocalIso CycleQ2GeometricCanonicalGluing

attribute [local instance] CycleQ2GeometricIntrinsicNormal.overHomCommModuleMk
  CycleQ2GeometricIntrinsicNormal.localLinearRingModule
  CycleQ2GeometricIntrinsicNormal.moduleHomObjModule

variable {T : TopCat.{0}} (R : T.Sheaf CommRingCat.{0})
  (L : SheafOfModules.{0} (ringSheaf R))
  {K N : SheafOfModules.{0} (ringSheaf R)} {U : Opens T}
  (e : PatchIso K N U)

/-- Postcompose all restricted components with the actual local target isomorphism. -/
def postcompose (O : Opens T) (hO : O ≤ U)
    (H : LocalLinearHom R L K O) : LocalLinearHom R L N O :=
  ⟨{
    app V := H.val.app V ≫ AddCommGrpCat.ofHom
      ((e.app V.unop.left (V.unop.hom.le.trans hO)).toLinearMap.toAddMonoidHom)
    naturality {V W} a := by
      apply ConcreteCategory.hom_ext
      intro x
      change e.app W.unop.left (W.unop.hom.le.trans hO)
        (H.val.app W (L.val.map a.unop.left.op x)) =
        N.val.map a.unop.left.op
          (e.app V.unop.left (V.unop.hom.le.trans hO) (H.val.app V x))
      have hH := ConcreteCategory.congr_hom (H.val.naturality a) x
      have he := e.naturality a.unop.left.le (V.unop.hom.le.trans hO)
        (H.val.app V x)
      exact (congrArg (e.app W.unop.left (W.unop.hom.le.trans hO)) hH).trans he.symm
  }, by
    intro V r x
    change e.app V.left (V.hom.le.trans hO) (H.val.app (op V) (r • x)) =
      r • e.app V.left (V.hom.le.trans hO) (H.val.app (op V) x)
    rw [H.property V r x]
    exact (e.app V.left (V.hom.le.trans hO)).map_smul r _⟩

theorem postcompose_app (O : Opens T) (hO : O ≤ U)
    (H : LocalLinearHom R L K O) (V : Over O) (x : L.val.obj (op V.left)) :
    (postcompose R L e O hO H).val.app (op V) x =
      e.app V.left (V.hom.le.trans hO) (H.val.app (op V) x) := rfl

theorem postcompose_evaluate (O : Opens T) (hO : O ≤ U)
    (H : LocalLinearHom R L K O) (x : L.val.obj (op O)) :
    localLinearHomEvaluate R L N O (postcompose R L e O hO H) x =
      e.app O hO (localLinearHomEvaluate R L K O H x) := rfl

theorem postcompose_restrict {O P : Opens T} (hPO : P ≤ O) (hO : O ≤ U)
    (H : LocalLinearHom R L K O) :
    restrictLocalLinearHom R L N (homOfLE hPO).op (postcompose R L e O hO H) =
      postcompose R L e P (hPO.trans hO)
        (restrictLocalLinearHom R L K (homOfLE hPO).op H) := by
  apply localLinearHom_ext
  intro V x
  rfl

/-- The local target frame supplies a linear equivalence on every actual
internal-Hom section module. -/
def sectionEquiv (O : Opens T) (hO : O ≤ U) :
    LocalLinearHom R L K O ≃ₗ[R.obj.obj (op O)] LocalLinearHom R L N O where
  toFun := postcompose R L e O hO
  invFun := postcompose R L e.symm O hO
  left_inv H := by
    apply localLinearHom_ext
    intro V x
    exact (e.app V.left (V.hom.le.trans hO)).symm_apply_apply _
  right_inv H := by
    apply localLinearHom_ext
    intro V x
    exact (e.app V.left (V.hom.le.trans hO)).apply_symm_apply _
  map_add' H G := by
    apply localLinearHom_ext
    intro V x
    exact (e.app V.left (V.hom.le.trans hO)).map_add _ _
  map_smul' r H := by
    apply localLinearHom_ext
    intro V x
    exact (e.app V.left (V.hom.le.trans hO)).map_smul
      (R.obj.map V.hom.op r) (H.val.app (op V) x)

/-- A genuine local isomorphism of the actual internal-Hom module sheaves. -/
def internalHomPatchIso : PatchIso (moduleHomSheaf R L K) (moduleHomSheaf R L N) U where
  app O hO := sectionEquiv R L e O hO
  naturality hPO hO H := postcompose_restrict R L e hPO hO H

theorem internalHomPatchIso_evaluate (O : Opens T) (hO : O ≤ U)
    (H : LocalLinearHom R L K O) (x : L.val.obj (op O)) :
    localLinearHomEvaluate R L N O ((internalHomPatchIso R L e).app O hO H) x =
      e.app O hO (localLinearHomEvaluate R L K O H x) := rfl

/-- In particular, a local line frame trivializes the target of an internal Hom. -/
def internalHomFrame (eK : LocalFrame R K U) :
    PatchIso (moduleHomSheaf R L K)
      (moduleHomSheaf R L (SheafOfModules.unit (ringSheaf R))) U :=
  internalHomPatchIso R L eK

section CanonicalInclusion

variable (K) (ι : L ⟶ SheafOfModules.unit (ringSheaf R))

/-- Keep the inclusion coefficient in the actual commutative section ring. -/
def inclusionCoefficient (O : Opens T) :
    L.val.obj (op O) →ₗ[R.obj.obj (op O)] R.obj.obj (op O) where
  toFun x := ι.val.app (op O) x
  map_add' x y := (ι.val.app (op O)).hom.map_add x y
  map_smul' r x := (ι.val.app (op O)).hom.map_smul r x

theorem inclusionCoefficient_restrict {O P : Opens T} (a : P ⟶ O)
    (x : L.val.obj (op O)) :
    inclusionCoefficient R L ι P (L.val.map a.op x) =
      R.obj.map a.op (inclusionCoefficient R L ι O x) :=
  PresheafOfModules.naturality_apply ι.val a.op x

/-- A regular section acts on the original ideal by literal multiplication
with the original ideal-inclusion morphism. -/
def regularSection (O : Opens T) (s : K.val.obj (op O)) : LocalLinearHom R L K O :=
  ⟨{
    app V := AddCommGrpCat.ofHom
      { toFun := fun x => inclusionCoefficient R L ι V.unop.left x •
          K.val.map V.unop.hom.op s
        map_zero' := by rw [map_zero, zero_smul]
        map_add' x y := by rw [map_add, add_smul] }
    naturality {V W} a := by
      apply ConcreteCategory.hom_ext
      intro x
      change inclusionCoefficient R L ι W.unop.left (L.val.map a.unop.left.op x) •
          K.val.map W.unop.hom.op s =
        K.val.map a.unop.left.op
          (inclusionCoefficient R L ι V.unop.left x •
            K.val.map V.unop.hom.op s)
      rw [K.val.map_smul, inclusionCoefficient_restrict,
        ← PresheafOfModules.map_comp_apply]
      congr 1
  }, by
    intro V r x
    change inclusionCoefficient R L ι V.left (r • x) •
      K.val.map V.hom.op s = r •
        (inclusionCoefficient R L ι V.left x • K.val.map V.hom.op s)
    rw [(inclusionCoefficient R L ι V.left).map_smul
      (show R.obj.obj (op V.left) from r) x]
    exact mul_smul (show R.obj.obj (op V.left) from r)
      (inclusionCoefficient R L ι V.left x) (K.val.map V.hom.op s)⟩

theorem regularSection_app (O : Opens T) (s : K.val.obj (op O))
    (V : Over O) (x : L.val.obj (op V.left)) :
    (regularSection R L K ι O s).val.app (op V) x =
      (ι.val.app (op V.left) x : R.obj.obj (op V.left)) • K.val.map V.hom.op s := rfl

def regularSectionLinearMap (O : Opens T) :
    K.val.obj (op O) →ₗ[R.obj.obj (op O)] LocalLinearHom R L K O where
  toFun := regularSection R L K ι O
  map_add' s t := by
    apply localLinearHom_ext
    intro V x
    change inclusionCoefficient R L ι V.left x •
      K.val.map V.hom.op (s + t) =
      inclusionCoefficient R L ι V.left x • K.val.map V.hom.op s +
        inclusionCoefficient R L ι V.left x • K.val.map V.hom.op t
    rw [map_add, smul_add]
  map_smul' r s := by
    apply localLinearHom_ext
    intro V x
    change inclusionCoefficient R L ι V.left x •
      K.val.map V.hom.op (r • s) = R.obj.map V.hom.op r •
        (inclusionCoefficient R L ι V.left x • K.val.map V.hom.op s)
    rw [K.val.map_smul]
    exact @smul_comm (R.obj.obj (op V.left)) (R.obj.obj (op V.left))
      (K.val.obj (op V.left)) _ _ _ _ _ _

theorem regularSection_restrict {O P : Opens T} (h : P ⟶ O)
    (s : K.val.obj (op O)) :
    restrictLocalLinearHom R L K h.op (regularSection R L K ι O s) =
      regularSection R L K ι P (K.val.map h.op s) := by
  apply localLinearHom_ext
  intro V x
  change (ι.val.app (op V.left) x : R.obj.obj (op V.left)) •
    K.val.map (V.hom ≫ h).op s =
    (ι.val.app (op V.left) x : R.obj.obj (op V.left)) •
      K.val.map V.hom.op (K.val.map h.op s)
  rw [op_comp, PresheafOfModules.map_comp_apply]

/-- The canonical regular-to-pole inclusion into the actual internal Hom. -/
def regularInclusion : K ⟶ moduleHomSheaf R L K where
  val.app O := ModuleCat.ofHom (regularSectionLinearMap R L K ι O.unop)
  val.naturality {O P} h := by
    apply ConcreteCategory.hom_ext
    intro s
    exact (regularSection_restrict R L K ι h.unop s).symm

theorem regularInclusion_evaluate (O : Opens T) (s : K.val.obj (op O))
    (x : L.val.obj (op O)) :
    localLinearHomEvaluate R L K O ((regularInclusion R L K ι).val.app (op O) s) x =
      (ι.val.app (op O) x : R.obj.obj (op O)) • s := by
  have h := regularSection_app R L K ι O s (Over.mk (𝟙 O)) x
  exact h.trans (congrArg
    (fun z : K.val.obj (op O) => (ι.val.app (op O) x : R.obj.obj (op O)) • z)
    (ConcreteCategory.congr_hom (K.val.presheaf.map_id (op O)) s))

/-- Under an actual target line frame, the canonical regular inclusion is
exactly the scalar inclusion into the original inverse-ideal Hom sheaf. -/
theorem internalHomFrame_regularInclusion (eK : LocalFrame R K U)
    (O : Opens T) (hO : O ≤ U) (s : K.val.obj (op O)) :
    (internalHomFrame R L eK).app O hO
        ((regularInclusion R L K ι).val.app (op O) s) =
      (CycleQ2GeometricIntrinsicHomMaps.scalarHom R L
        (SheafOfModules.unit (ringSheaf R)) ι).val.app (op O) (eK.app O hO s) := by
  apply localLinearHom_ext
  intro V x
  change eK.app V.left (V.hom.le.trans hO)
      ((ι.val.app (op V.left) x : R.obj.obj (op V.left)) • K.val.map V.hom.op s) =
    R.obj.map V.hom.op (eK.app O hO s) •
      (ι.val.app (op V.left) x : R.obj.obj (op V.left))
  rw [map_smul]
  have he := eK.naturality V.hom.le hO s
  change R.obj.map V.hom.op (eK.app O hO s) =
    eK.app V.left (V.hom.le.trans hO) (K.val.map V.hom.op s) at he
  rw [← he]
  change (inclusionCoefficient R L ι V.left x) *
      (R.obj.map V.hom.op (frameCoordinate eK O hO s)) =
    (R.obj.map V.hom.op (frameCoordinate eK O hO s)) *
      (inclusionCoefficient R L ι V.left x)
  exact mul_comm _ _

end CanonicalInclusion

section IdealInclusion

variable {X Y : Scheme.{0}} (j : X ⟶ Y) (K : Y.Modules)

/-- Specialization to the actual kernel ideal of the original scheme map. -/
def idealRegularInclusion :
    K ⟶ moduleHomSheaf Y.sheaf (kernelIdealSheaf j) K :=
  regularInclusion Y.sheaf (kernelIdealSheaf j) K (kernel.ι (schemeStructureMap j))

/-- The square uses the unchanged inverseIdealScalar and the unchanged
kernel inclusion, rather than a separately chosen ideal model. -/
theorem internalHomFrame_idealRegularInclusion {U : Y.Opens}
    (eK : LocalFrame Y.sheaf K U) (O : Y.Opens) (hO : O ≤ U)
    (s : K.val.obj (op O)) :
    (internalHomFrame Y.sheaf (kernelIdealSheaf j) eK).app O hO
        ((idealRegularInclusion j K).val.app (op O) s) =
      (inverseIdealScalar j).val.app (op O) (eK.app O hO s) :=
  internalHomFrame_regularInclusion Y.sheaf (kernelIdealSheaf j) K
    (kernel.ι (schemeStructureMap j)) eK O hO s

end IdealInclusion

#print axioms postcompose_evaluate
#print axioms internalHomPatchIso
#print axioms internalHomFrame
#print axioms regularInclusion
#print axioms internalHomFrame_regularInclusion
#print axioms internalHomFrame_idealRegularInclusion

end CycleQ2LocalHomFrame

end
