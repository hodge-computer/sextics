import Proposal.GeometricIntrinsicNormal
import Proposal.GeometricCartierDerivedClass
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.CategoryTheory.Limits.Lattice
import Proposal.GeometricSurfaceBindings
import Proposal.GeometricCartierCohomologyScalar
import Proposal.GeometricSurfaceCurveCharts
import Proposal.GeometricSurfaceProjectiveCoefficients
import Proposal.GeometricProjectiveCoefficients

section

/-! The source-side conormal and normal sheaves of the original closed
immersion. The ideal is the actual categorical kernel already constructed
from its structure-sheaf morphism. The conormal is its genuine pullback;
the normal is its genuine internal linear dual. The global comparison to
the existing direct-image normal sheaf uses the original module-sheaf
pullback/pushforward adjunction. -/
set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace CycleQ2SourceNormalSheaf
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
  CycleQ2GeometricDifferentialSheaf CycleQ2GeometricIntrinsicNormal

section AdditiveHom
variable (Z : Scheme.{0}) (M N : Z.Modules)

/-- The canonical global local-Hom correspondence preserves addition. -/
def localLinearHomTopAddEquiv : LocalLinearHom Z.sheaf M N ⊤ ≃+ (M ⟶ N) where
  __ := localLinearHomTopEquiv Z.sheaf M N
  map_add' f g := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    rfl

end AdditiveHom

variable {X Y : Scheme.{0}} (j : X ⟶ Y)

/-- The canonical unit module over the actual structure sheaf. -/
def structureModule (Z : Scheme.{0}) : Z.Modules := SheafOfModules.unit Z.ringCatSheaf

/-- The original categorical kernel, regarded in the scheme-module category. -/
def idealModule : Y.Modules := kernelIdealSheaf j

/-- The original direct image of the source structure module. -/
def imageModule : Y.Modules := imageStructureModule j

/-- The incoming direct-image structure module is the original scheme
module pushforward, for every scheme morphism. -/
theorem imageStructureModule_eq_schemePushforward :
    imageStructureModule j = (Scheme.Modules.pushforward j).obj (structureModule X) := rfl

/-- The intrinsic conormal on the source is the actual pullback of the
categorical kernel ideal. -/
def sourceConormal : X.Modules :=
  (Scheme.Modules.pullback j).obj (idealModule j)

/-- The intrinsic normal sheaf on the source is the internal linear dual
of the actual pullback conormal. -/
def sourceNormal : X.Modules :=
  moduleHomSheaf X.sheaf (sourceConormal j) (structureModule X)

/-- All-open sections of the intrinsic normal are actual local morphisms
from the conormal to the original structure module. -/
def sourceNormalSectionsEquiv (U : X.Opens) :
    Γ(sourceNormal j,U) ≃
      (SheafOfModules.over (sourceConormal j) U ⟶
        SheafOfModules.over (structureModule X) U) :=
  localLinearHomEquiv X.sheaf (sourceConormal j) (structureModule X) U

/-- Global normal sections are genuine global linear maps from the conormal. -/
def sourceNormalGlobalHomEquiv :
    Γ(sourceNormal j,⊤) ≃+ (sourceConormal j ⟶ structureModule X) :=
  localLinearHomTopAddEquiv X (sourceConormal j) (structureModule X)

/-- The genuine module-sheaf adjunction identifies source normal sections
with maps from the original ideal into the pushed-forward structure sheaf. -/
def sourceNormalGlobalAdjunction :
    Γ(sourceNormal j,⊤) ≃+
      (idealModule j ⟶
        (Scheme.Modules.pushforward j).obj (structureModule X)) :=
  (sourceNormalGlobalHomEquiv j).trans
    ((Scheme.Modules.pullbackPushforwardAdjunction j).homAddEquiv
      (idealModule j) (structureModule X))

/-- This is the canonical comparison with the existing direct-image normal
sheaf at the whole surface, with both original sheaf actions retained. -/
def normalGlobalComparison :
    Γ(sourceNormal j,⊤) ≃+ (normalDirectImageSheaf j).val.obj (op ⊤) :=
  (sourceNormalGlobalAdjunction j).trans
    (localLinearHomTopAddEquiv Y (idealModule j) (imageModule j)).symm

/-- The comparison is exactly the existing adjunction on its underlying map. -/
theorem normalGlobalComparison_hom (x : Γ(sourceNormal j,⊤)) :
    localLinearHomTopEquiv Y.sheaf (kernelIdealSheaf j) (imageStructureModule j)
      (normalGlobalComparison j x) =
    (Scheme.Modules.pullbackPushforwardAdjunction j).homEquiv
      (idealModule j) (structureModule X)
      (sourceNormalGlobalHomEquiv j x) :=
  (localLinearHomTopAddEquiv Y (idealModule j) (imageModule j)).apply_symm_apply _

section ActualCurve

/-- The incoming literal quotient is the original surface-to-curve quotient. -/
theorem literal_curveRestriction_eq (r θ : ℂ) :
    (CycleQ2GeometricLiteralSurface.curveRestriction r θ).toRingHom =
      CycleQ2ProjectiveCurveSurface.surfaceToCurve r θ := rfl

/-- Both named projective curve immersions are the same original morphism. -/
theorem literal_curveToSurface_eq (r θ : ℂ) :
    CycleQ2GeometricLiteralSurface.curveToSurface r θ =
      CycleQ2ProjectiveCurveSurface.curveToSurface r θ := rfl

/-- The intrinsic conormal of the original projective curve immersion. -/
def actualConormal (r θ : ℂ) : (CycleQ2GeometricProjectiveCurve.projectiveCurve r θ).Modules :=
  sourceConormal (CycleQ2ProjectiveCurveSurface.curveToSurface r θ)

/-- The intrinsic normal of the original projective curve immersion. -/
def actualNormal (r θ : ℂ) : (CycleQ2GeometricProjectiveCurve.projectiveCurve r θ).Modules :=
  sourceNormal (CycleQ2ProjectiveCurveSurface.curveToSurface r θ)

/-- Canonical global sections comparison to the incoming intrinsic normal,
proved for the same original immersion rather than an identified model. -/
def actualNormalGlobalComparison (r θ : ℂ) :
    Γ(actualNormal r θ,⊤) ≃+
      (literalNormalDirectImageSheaf r θ).val.obj (op ⊤) :=
  normalGlobalComparison (CycleQ2ProjectiveCurveSurface.curveToSurface r θ)

end ActualCurve

#print axioms localLinearHomTopAddEquiv
#print axioms imageStructureModule_eq_schemePushforward
#print axioms sourceConormal
#print axioms sourceNormal
#print axioms sourceNormalSectionsEquiv
#print axioms sourceNormalGlobalHomEquiv
#print axioms sourceNormalGlobalAdjunction
#print axioms normalGlobalComparison
#print axioms normalGlobalComparison_hom
#print axioms literal_curveRestriction_eq
#print axioms literal_curveToSurface_eq
#print axioms actualConormal
#print axioms actualNormal
#print axioms actualNormalGlobalComparison

end CycleQ2SourceNormalSheaf
end

end


section

/-! The canonical pushforward comparison from the source-side internal Hom
to the internal Hom into a pushforward. It is induced by the genuine unit
of the scheme-module adjunction, and retains the original actions. -/
set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace CycleQ2NormalPushforward
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
  CycleQ2GeometricDifferentialSheaf CycleQ2GeometricIntrinsicNormal
  CycleQ2SourceNormalSheaf

variable {X Y : Scheme.{0}} (j : X ⟶ Y) (M : Y.Modules) (N : X.Modules)

private abbrev pulled : X.Modules := (Scheme.Modules.pullback j).obj M
private abbrev pushed : Y.Modules := (Scheme.Modules.pushforward j).obj N

local instance schemeLocalHomModule (Z : Scheme.{0}) (P Q : Z.Modules) (U : Z.Opens) :
    Module Γ(Z,U) (LocalLinearHom Z.sheaf P Q U) :=
  localLinearHomModule Z.sheaf P Q U

/-- On every open, apply a local source morphism after the actual adjunction unit. -/
def localForward (U : Y.Opens)
    (f : LocalLinearHom X.sheaf (pulled j M) N (j ⁻¹ᵁ U)) :
    LocalLinearHom Y.sheaf M (pushed j N) U := by
  let u := (Scheme.Modules.pullbackPushforwardAdjunction j).unit.app M
  refine ⟨Functor.whiskerLeft (Over.forget U).op u.mapPresheaf ≫
    Functor.whiskerLeft (Over.post (X := U) (Opens.map j.base)).op f.val, ?_⟩
  intro V r m
  let W : Over (j ⁻¹ᵁ U) := (Over.post (X := U) (Opens.map j.base)).obj V
  have hu := (u.val.app (op V.left)).hom.map_smul r m
  exact (congrArg (f.val.app (op W)) hu).trans
    (f.property W (j.app V.left r) (u.val.app (op V.left) m))

/-- The comparison on an open is additive. -/
def localForwardAddHom (U : Y.Opens) :
    LocalLinearHom X.sheaf (pulled j M) N (j ⁻¹ᵁ U) →+
      LocalLinearHom Y.sheaf M (pushed j N) U where
  toFun := localForward j M N U
  map_zero' := by
    apply localLinearHom_ext
    intro V m
    rfl
  map_add' f g := by
    apply localLinearHom_ext
    intro V m
    rfl

/-- Naturality uses the actual restrictions on both schemes. -/
theorem localForward_restrict {U V : Y.Opens} (h : V ⟶ U)
    (f : LocalLinearHom X.sheaf (pulled j M) N (j ⁻¹ᵁ U)) :
    localForward j M N V
      (restrictLocalLinearHom X.sheaf (pulled j M) N
        ((Opens.map j.base).map h).op f) =
    restrictLocalLinearHom Y.sheaf M (pushed j N) h.op (localForward j M N U f) := by
  apply localLinearHom_ext
  intro W m
  rfl

/-- Multiplication is carried through the original scheme coefficient maps. -/
theorem localForward_smul (U : Y.Opens) (r : Γ(Y,U))
    (f : LocalLinearHom X.sheaf (pulled j M) N (j ⁻¹ᵁ U)) :
    localForward j M N U (j.app U r • f) = r • localForward j M N U f := by
  apply localLinearHom_ext
  intro V m
  let u := (Scheme.Modules.pullbackPushforwardAdjunction j).unit.app M
  let W : Over (j ⁻¹ᵁ U) := (Over.post (X := U) (Opens.map j.base)).obj V
  let O : X.Opens := j ⁻¹ᵁ V.left
  let n : Γ(N,O) := f.val.app (op W) (u.val.app (op V.left) m)
  let a : Γ(X,O) := X.presheaf.map ((Opens.map j.base).map V.hom).op (j.app U r)
  let b : Γ(X,O) := j.app V.left (Y.presheaf.map V.hom.op r)
  change a • n = b • n
  exact congrArg (fun s : Γ(X,O) => s • n)
    (ConcreteCategory.congr_hom (j.naturality V.hom.op) r).symm

/-- The actual module-sheaf morphism induced by the unit of pullback and pushforward. -/
def internalHomPushforward :
    (Scheme.Modules.pushforward j).obj
      (show X.Modules from moduleHomSheaf X.sheaf (pulled j M) N) ⟶
    (show Y.Modules from moduleHomSheaf Y.sheaf M (pushed j N)) where
  val := PresheafOfModules.homMk
    { app U := AddCommGrpCat.ofHom (localForwardAddHom j M N U.unop)
      naturality {U V} h := by
        apply ConcreteCategory.hom_ext
        intro f
        exact localForward_restrict j M N h.unop f }
    (fun U r f => localForward_smul j M N U.unop r f)

/-- The canonical comparison for the actual intrinsic normal sheaves. -/
def normalPushforward :
    (Scheme.Modules.pushforward j).obj (sourceNormal j) ⟶
      (show Y.Modules from normalDirectImageSheaf j) :=
  internalHomPushforward j (show Y.Modules from kernelIdealSheaf j) (structureModule X)

/-- At the top open, the sheaf morphism is the same canonical global adjunction. -/
theorem normalPushforward_app_top (x : Γ(sourceNormal j,⊤)) :
    (normalPushforward j).app ⊤ x = normalGlobalComparison j x := by
  let e := localLinearHomTopAddEquiv Y (idealModule j) (imageModule j)
  apply e.injective
  have h₁ : e ((normalPushforward j).app ⊤ x) =
        (Scheme.Modules.pullbackPushforwardAdjunction j).homEquiv
          (idealModule j) (structureModule X) (sourceNormalGlobalHomEquiv j x) := by
    apply Scheme.Modules.hom_ext
    intro U
    apply ConcreteCategory.hom_ext
    intro m
    rfl
  have h₂ : e (normalGlobalComparison j x) =
      (Scheme.Modules.pullbackPushforwardAdjunction j).homEquiv
        (idealModule j) (structureModule X) (sourceNormalGlobalHomEquiv j x) :=
    normalGlobalComparison_hom j x
  exact h₁.trans h₂.symm

/-- The canonical pushforward comparison is bijective on global sections. -/
theorem normalPushforward_top_bijective :
    Function.Bijective (fun x : Γ(sourceNormal j,⊤) => (normalPushforward j).app ⊤ x) := by
  constructor
  · intro x y h
    apply (normalGlobalComparison j).injective
    exact (normalPushforward_app_top j x).symm.trans
      (h.trans (normalPushforward_app_top j y))
  · intro y
    obtain ⟨x, hx⟩ := (normalGlobalComparison j).surjective y
    exact ⟨x, (normalPushforward_app_top j x).trans hx⟩

#print axioms localForward
#print axioms localForward_restrict
#print axioms localForward_smul
#print axioms internalHomPushforward
#print axioms normalPushforward
#print axioms normalPushforward_app_top
#print axioms normalPushforward_top_bijective

end CycleQ2NormalPushforward
end

end


section

/-! Restriction followed by its genuine right adjoint commutes with scheme
pushforward. The comparison uses the equality between the two actual
inverse-image intersections and retains the original section-ring actions. -/
set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace CycleQ2ModuleOverPushforward
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
  TopologicalSpace Opposite

variable {X Y : Scheme.{0}} (j : X ⟶ Y)

/-- The actual right adjoint to restriction, applied to a restricted module. -/
def extension (Z : Scheme.{0}) (U : Z.Opens) (N : Z.Modules) : Z.Modules :=
  (SheafOfModules.pushforward (SheafOfModules.pushforwardOver (R := Z.ringCatSheaf) U)).obj
    (N.over U)

def leftExtension (U : Y.Opens) (N : X.Modules) : Y.Modules :=
  (Scheme.Modules.pushforward j).obj (extension X (j ⁻¹ᵁ U) N)

def rightExtension (U : Y.Opens) (N : X.Modules) : Y.Modules :=
  extension Y U ((Scheme.Modules.pushforward j).obj N)

/-- Inverse images preserve the actual binary intersections used by `Over.star`. -/
def preimageProductIso (U V : Y.Opens) :
    Limits.prod (j ⁻¹ᵁ U) (j ⁻¹ᵁ V) ≅ j ⁻¹ᵁ (Limits.prod U V) :=
  eqToIso (by
    rw [CategoryTheory.Limits.CompleteLattice.prod_eq_inf,
      CategoryTheory.Limits.CompleteLattice.prod_eq_inf]
    rfl)

/-- The additive section comparison is the original restriction along the
canonical equality of the inverse-image intersections. -/
def sectionAddIso (U : Y.Opens) (N : X.Modules) (V : Y.Opens) :
    Γ(leftExtension j U N,V) ≅ Γ(rightExtension j U N,V) :=
  N.presheaf.mapIso (preimageProductIso j U V).symm.op

/-- The intersection comparison preserves the genuine action of `Γ(Y,V)`. -/
theorem sectionAddIso_smul (U : Y.Opens) (N : X.Modules) (V : Y.Opens)
    (r : Γ(Y,V)) (x : Γ(leftExtension j U N,V)) :
    (sectionAddIso j U N V).hom (r • x) =
      r • (sectionAddIso j U N V).hom x := by
  let e := preimageProductIso j U V
  let L : X.Opens := Limits.prod (j ⁻¹ᵁ U) (j ⁻¹ᵁ V)
  let Q : X.Opens := j ⁻¹ᵁ (Limits.prod U V)
  let ep : Q ⟶ L := e.inv
  let p : L ⟶ j ⁻¹ᵁ V := Limits.prod.snd
  let q : Limits.prod U V ⟶ V := Limits.prod.snd
  let x' : Γ(N,L) := x
  let y : Γ(N,Q) := N.presheaf.map ep.op x'
  let a : Γ(X,L) := X.presheaf.map p.op (j.app V r)
  let b : Γ(X,Q) := j.app (Limits.prod U V) (Y.presheaf.map q.op r)
  change N.presheaf.map ep.op (a • x') = b • y
  refine (N.map_smul ep a x').trans ?_
  apply congrArg (fun z : Γ(X,Q) => z • y)
  have hp : p.op ≫ ep.op = ((Opens.map j.base).map q).op := Subsingleton.elim _ _
  have he : X.presheaf.map p.op ≫ X.presheaf.map ep.op =
      X.presheaf.map ((Opens.map j.base).map q).op :=
    (X.presheaf.map_comp p.op ep.op).symm.trans
      (congrArg (fun g : op (j ⁻¹ᵁ V) ⟶ op Q => X.presheaf.map g) hp)
  exact (ConcreteCategory.congr_hom he (j.app V r)).trans
    (ConcreteCategory.congr_hom (j.naturality q.op) r).symm

/-- The genuine linear comparison of the two modules of sections. -/
def sectionIso (U : Y.Opens) (N : X.Modules) (V : Y.Opens) :
    (leftExtension j U N).val.obj (op V) ≅ (rightExtension j U N).val.obj (op V) :=
  ModuleCat.isoMk (sectionAddIso j U N V) (fun r => by
    apply ConcreteCategory.hom_ext
    intro x
    exact (sectionAddIso_smul j U N V r x).symm)

/-- The two genuine right-adjoint extensions commute with scheme pushforward. -/
def extensionPushforwardIso (U : Y.Opens) (N : X.Modules) :
    leftExtension j U N ≅ rightExtension j U N := by
  let e : (leftExtension j U N).val ≅ (rightExtension j U N).val :=
    PresheafOfModules.isoMk (fun V => sectionIso j U N V.unop) (by
      intro V W h
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      let L : X.Opens := Limits.prod (j ⁻¹ᵁ U) (j ⁻¹ᵁ V.unop)
      let Q : X.Opens := j ⁻¹ᵁ (Limits.prod U W.unop)
      let a : Limits.prod (j ⁻¹ᵁ U) (j ⁻¹ᵁ W.unop) ⟶ L :=
        ((Over.star (j ⁻¹ᵁ U)).map ((Opens.map j.base).map h.unop)).left
      let b : Q ⟶ Limits.prod (j ⁻¹ᵁ U) (j ⁻¹ᵁ W.unop) :=
        (preimageProductIso j U W.unop).inv
      let c : j ⁻¹ᵁ (Limits.prod U V.unop) ⟶ L :=
        (preimageProductIso j U V.unop).inv
      let d : Q ⟶ j ⁻¹ᵁ (Limits.prod U V.unop) :=
        (Opens.map j.base).map (((Over.star U).map h.unop).left)
      change (N.presheaf.map a.op ≫ N.presheaf.map b.op) x =
        (N.presheaf.map c.op ≫ N.presheaf.map d.op) x
      have hp : a.op ≫ b.op = c.op ≫ d.op := Subsingleton.elim _ _
      have he : N.presheaf.map a.op ≫ N.presheaf.map b.op =
          N.presheaf.map c.op ≫ N.presheaf.map d.op :=
        (N.presheaf.map_comp a.op b.op).symm.trans
          ((congrArg (fun f : op L ⟶ op Q => N.presheaf.map f) hp).trans
            (N.presheaf.map_comp c.op d.op))
      exact ConcreteCategory.congr_hom he x)
  exact
    { hom := ⟨e.hom⟩
      inv := ⟨e.inv⟩
      hom_inv_id := SheafOfModules.hom_ext e.hom_inv_id
      inv_hom_id := SheafOfModules.hom_ext e.inv_hom_id }

#print axioms preimageProductIso
#print axioms sectionAddIso_smul
#print axioms extensionPushforwardIso

end CycleQ2ModuleOverPushforward
end

end


section

/-! The internal-Hom pushforward comparison is an actual isomorphism of
module sheaves. Its pointwise bijection is the composite of the genuine
restriction and scheme pullback adjunctions. -/
set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace CycleQ2NormalPushforwardIso
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
  CycleQ2GeometricDifferentialSheaf CycleQ2GeometricIntrinsicNormal
  CycleQ2SourceNormalSheaf CycleQ2NormalPushforward CycleQ2ModuleOverPushforward

variable {X Y : Scheme.{0}} (j : X ⟶ Y) (M : Y.Modules) (N : X.Modules)

/-- The original adjunction between restriction and its right adjoint. -/
def overHomEquiv (Z : Scheme.{0}) (P Q : Z.Modules) (U : Z.Opens) :
    (P.over U ⟶ Q.over U) ≃ (P ⟶ extension Z U Q) :=
  (SheafOfModules.overPushforwardOverAdj (R := Z.ringCatSheaf) U).homEquiv P (Q.over U)

/-- The genuine local Hom adjunction on every open, retaining both original
module sheaves and their original section-ring actions. -/
def localAdjunctionEquiv (U : Y.Opens) :
    LocalLinearHom X.sheaf ((Scheme.Modules.pullback j).obj M) N (j ⁻¹ᵁ U) ≃
      LocalLinearHom Y.sheaf M ((Scheme.Modules.pushforward j).obj N) U :=
  let e₁ := localLinearHomEquiv X.sheaf ((Scheme.Modules.pullback j).obj M) N (j ⁻¹ᵁ U)
  let e₂ := overHomEquiv X ((Scheme.Modules.pullback j).obj M) N (j ⁻¹ᵁ U)
  let e₃ := (Scheme.Modules.pullbackPushforwardAdjunction j).homEquiv M
    (extension X (j ⁻¹ᵁ U) N)
  let e₄ := Iso.homCongr (Iso.refl M) (extensionPushforwardIso j U N)
  let e₅ := (overHomEquiv Y M ((Scheme.Modules.pushforward j).obj N) U).symm
  let e₆ := (localLinearHomEquiv Y.sheaf M ((Scheme.Modules.pushforward j).obj N) U).symm
  e₁.trans (e₂.trans (e₃.trans (e₄.trans (e₅.trans e₆))))

/-- The pointwise bijection is exactly the canonical unit-induced map,
not a newly chosen identification of the two local Hom spaces. -/
theorem localAdjunctionEquiv_apply (U : Y.Opens)
    (f : LocalLinearHom X.sheaf ((Scheme.Modules.pullback j).obj M) N (j ⁻¹ᵁ U)) :
    localAdjunctionEquiv j M N U f = localForward j M N U f := by
  apply localLinearHom_ext
  intro V m
  let Pm : X.Modules := (Scheme.Modules.pullback j).obj M
  let O : X.Opens := j ⁻¹ᵁ V.left
  let LP : X.Opens := Limits.prod (j ⁻¹ᵁ U) O
  let RP : X.Opens := j ⁻¹ᵁ (Limits.prod U V.left)
  let W : Over (j ⁻¹ᵁ U) := (Over.post (X := U) (Opens.map j.base)).obj V
  let P : Over (j ⁻¹ᵁ U) := (Over.star (j ⁻¹ᵁ U)).obj O
  let e := preimageProductIso j U V.left
  let u := (Scheme.Modules.pullbackPushforwardAdjunction j).unit.app M
  let v : V.left ⟶ Limits.prod U V.left := ((Over.forgetAdjStar U).unit.app V).left
  let fv : O ⟶ RP := (Opens.map j.base).map v
  let ep : RP ⟶ LP := e.inv
  let a : W ⟶ P := Over.homMk (fv ≫ ep)
  let aa : O ⟶ LP := a.left
  let p : LP ⟶ O := Limits.prod.snd
  let t : Γ(Pm,O) := u.app V.left m
  let z : Γ(Pm,LP) := Pm.presheaf.map p.op t
  let fW : Γ(Pm,O) → Γ(N,O) := f.val.app (op W)
  let fP : Γ(Pm,LP) → Γ(N,LP) := f.val.app (op P)
  let k : Γ(N,LP) := fP z
  change N.presheaf.map fv.op (N.presheaf.map ep.op k) = fW t
  have hn : fW (Pm.presheaf.map aa.op z) = N.presheaf.map aa.op k :=
    ConcreteCategory.congr_hom (f.val.naturality a.op) z
  have hp : ep.op ≫ fv.op = aa.op := Subsingleton.elim _ _
  have hc : N.presheaf.map ep.op ≫ N.presheaf.map fv.op = N.presheaf.map aa.op :=
    (N.presheaf.map_comp ep.op fv.op).symm.trans
      (congrArg (fun g : op LP ⟶ op O => N.presheaf.map g) hp)
  have hpi : p.op ≫ aa.op = 𝟙 (op O) := Subsingleton.elim _ _
  have hi : Pm.presheaf.map p.op ≫ Pm.presheaf.map aa.op = 𝟙 _ :=
    (Pm.presheaf.map_comp p.op aa.op).symm.trans
      ((congrArg (fun g : op O ⟶ op O => Pm.presheaf.map g) hpi).trans
        (Pm.presheaf.map_id (op O)))
  exact (ConcreteCategory.congr_hom hc k).trans
    (hn.symm.trans (congrArg fW (ConcreteCategory.congr_hom hi t)))

/-- Every component of the canonical internal-Hom comparison is bijective. -/
theorem localForward_bijective (U : Y.Opens) :
    Function.Bijective (localForward j M N U) := by
  let e := localAdjunctionEquiv j M N U
  constructor
  · intro f g h
    apply e.injective
    exact (localAdjunctionEquiv_apply j M N U f).trans
      (h.trans (localAdjunctionEquiv_apply j M N U g).symm)
  · intro g
    obtain ⟨f, hf⟩ := e.surjective g
    exact ⟨f, (localAdjunctionEquiv_apply j M N U f).symm.trans hf⟩

/-- The canonical map is an isomorphism on the original module sheaves. -/
instance internalHomPushforward_isIso : IsIso (internalHomPushforward j M N) := by
  apply Scheme.Modules.Hom.isIso_iff_isIso_app.mpr
  intro U
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  exact localForward_bijective j M N U

/-- The full canonical sheaf-level pullback/internal-Hom adjunction. -/
def internalHomPushforwardIso :
    (Scheme.Modules.pushforward j).obj
      (show X.Modules from moduleHomSheaf X.sheaf ((Scheme.Modules.pullback j).obj M) N) ≅
    (show Y.Modules from moduleHomSheaf Y.sheaf M ((Scheme.Modules.pushforward j).obj N)) :=
  asIso (internalHomPushforward j M N)

/-- The source intrinsic normal pushes forward to the original intrinsic
surface-side normal sheaf, on every open. -/
def normalPushforwardIso :
    (Scheme.Modules.pushforward j).obj (sourceNormal j) ≅
      (show Y.Modules from normalDirectImageSheaf j) :=
  internalHomPushforwardIso j (idealModule j) (structureModule X)

/-- The actual source and target belong to the original projective immersion. -/
def actualNormalPushforwardIso (r θ : ℂ) :
    (Scheme.Modules.pushforward (CycleQ2ProjectiveCurveSurface.curveToSurface r θ)).obj
        (actualNormal r θ) ≅
      (show (CycleQ2CartierProjectiveCover.projectiveSurface r θ).Modules from
        literalNormalDirectImageSheaf r θ) :=
  normalPushforwardIso (CycleQ2ProjectiveCurveSurface.curveToSurface r θ)

#print axioms localAdjunctionEquiv
#print axioms localAdjunctionEquiv_apply
#print axioms localForward_bijective
#print axioms internalHomPushforwardIso
#print axioms normalPushforwardIso
#print axioms actualNormalPushforwardIso

end CycleQ2NormalPushforwardIso
end

end


section

/-! The original incidence seed and the Cartier surface are the same
quotient Proj construction, transported along their proved ideal equality. -/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace CycleQ2OriginalSurfaceIdentification

open CategoryTheory AlgebraicGeometry MvPolynomial
  CycleQ2GeometricSurfaceAdjunction CycleQ2GeometricSeedNormalIdeals
  CycleQ2GeometricProjectiveCurve CycleQ2ConormalJacobian
  CycleQ2IncidencePolynomialJacobianBinding CycleQ2GeometricProjectiveHOne

attribute [local instance] MvPolynomial.weightedGradedAlgebra

def quotientProj (I : Ideal (MvPolynomial (Fin 5) ℂ))
    (hI : I.IsHomogeneous CycleQ2CartierSurfaceGrading.PolynomialGrade) : Scheme := by
  letI := HomogeneousQuotient.gradedRing
    CycleQ2CartierSurfaceGrading.PolynomialGrade I hI
  exact Proj (HomogeneousQuotient.grade CycleQ2CartierSurfaceGrading.PolynomialGrade I)

theorem quotientProj_congr (I J : Ideal (MvPolynomial (Fin 5) ℂ))
    (hI : I.IsHomogeneous CycleQ2CartierSurfaceGrading.PolynomialGrade)
    (hJ : J.IsHomogeneous CycleQ2CartierSurfaceGrading.PolynomialGrade)
    (e : I = J) : quotientProj I hI = quotientProj J hJ := by
  subst J
  rfl

/-- This is equality of the actual projective schemes, using the original
seed ideal equality and the identical quotient grading construction. -/
theorem literalIncidenceSurface_eq :
    literalIncidenceSurface = CycleQ2CartierProjectiveCover.projectiveSurface 57 1 := by
  exact quotientProj_congr
    (CycleQ2GeometricIncidenceProj.pointEquations (seedPoint (57 : ℂ) Complex.I))
    (surfaceIdeal 57 1)
    (CycleQ2GeometricIncidenceProj.pointEquations_homogeneous
      (seedPoint (57 : ℂ) Complex.I))
    (CycleQ2CartierSurfaceGrading.surfaceIdeal_homogeneous 57 1)
    literalPointSurface_ideal

def literalIncidenceSurfaceIso :
    literalIncidenceSurface ≅ CycleQ2CartierProjectiveCover.projectiveSurface 57 1 :=
  eqToIso literalIncidenceSurface_eq

local instance schemeSheavesHasExt (X : Scheme.{0}) :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}) :=
  HasExt.standard _

/-- The checked nonzero ordinary cohomology class belongs to the actual
original incidence surface, via the equality of the quotient Proj schemes. -/
theorem original_H_two_nontrivial :
    Nontrivial ((structureAdditiveSheaf literalIncidenceSurface).H 2) := by
  rw [literalIncidenceSurface_eq]
  exact CycleQ2ProjectiveCartierDerived.literal_H_two_nontrivial

end CycleQ2OriginalSurfaceIdentification
end

end


section

/-! The actual quotient-Proj identification preserves the original
coordinate opens and the canonical complex structure morphism. -/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace CycleQ2OriginalSurfaceChartBinding

open CategoryTheory AlgebraicGeometry MvPolynomial
  CycleQ2GeometricSurfaceAdjunction CycleQ2GeometricSeedNormalIdeals
  CycleQ2GeometricProjectiveCurve CycleQ2ConormalJacobian
  CycleQ2IncidencePolynomialJacobianBinding CycleQ2OriginalSurfaceIdentification

attribute [local instance] MvPolynomial.weightedGradedAlgebra

def quotientBasicOpen (I : Ideal (MvPolynomial (Fin 5) ℂ))
    (hI : I.IsHomogeneous CycleQ2CartierSurfaceGrading.PolynomialGrade)
    (p : MvPolynomial (Fin 5) ℂ) : (quotientProj I hI).Opens := by
  letI := HomogeneousQuotient.gradedRing
    CycleQ2CartierSurfaceGrading.PolynomialGrade I hI
  exact Proj.basicOpen (HomogeneousQuotient.grade
    CycleQ2CartierSurfaceGrading.PolynomialGrade I) (Ideal.Quotient.mk I p)

theorem quotientBasicOpen_preimage (I J : Ideal (MvPolynomial (Fin 5) ℂ))
    (hI : I.IsHomogeneous CycleQ2CartierSurfaceGrading.PolynomialGrade)
    (hJ : J.IsHomogeneous CycleQ2CartierSurfaceGrading.PolynomialGrade)
    (e : I = J) (p : MvPolynomial (Fin 5) ℂ) :
    (eqToHom (quotientProj_congr I J hI hJ e)) ⁻¹ᵁ quotientBasicOpen J hJ p =
      quotientBasicOpen I hI p := by
  subst J
  rfl

/-- The global scheme identification respects every original weight-one
coordinate chart, not only the abstract projective surface. -/
theorem literalCoordinatePatch_preimage (i : Fin 4) :
    literalIncidenceSurfaceIso.hom ⁻¹ᵁ
        CycleQ2CartierProjectiveCover.coordinatePatch 57 1 i.castSucc =
      literalSurfaceCoordinatePatch i :=
  quotientBasicOpen_preimage
    (CycleQ2GeometricIncidenceProj.pointEquations (seedPoint (57 : ℂ) Complex.I))
    (surfaceIdeal 57 1)
    (CycleQ2GeometricIncidenceProj.pointEquations_homogeneous
      (seedPoint (57 : ℂ) Complex.I))
    (CycleQ2CartierSurfaceGrading.surfaceIdeal_homogeneous 57 1)
    literalPointSurface_ideal (X i.castSucc)

def quotientToComplex (I : Ideal (MvPolynomial (Fin 5) ℂ))
    (hI : I.IsHomogeneous CycleQ2CartierSurfaceGrading.PolynomialGrade) :
    quotientProj I hI ⟶ Spec (CommRingCat.of ℂ) := by
  letI := HomogeneousQuotient.gradedRing
    CycleQ2CartierSurfaceGrading.PolynomialGrade I hI
  exact Proj.toSpecZero (HomogeneousQuotient.grade
      CycleQ2CartierSurfaceGrading.PolynomialGrade I) ≫
    Spec.map (CommRingCat.ofHom (algebraMap ℂ
      (HomogeneousQuotient.grade CycleQ2CartierSurfaceGrading.PolynomialGrade I 0)))

theorem quotientToComplex_congr (I J : Ideal (MvPolynomial (Fin 5) ℂ))
    (hI : I.IsHomogeneous CycleQ2CartierSurfaceGrading.PolynomialGrade)
    (hJ : J.IsHomogeneous CycleQ2CartierSurfaceGrading.PolynomialGrade)
    (e : I = J) :
    eqToHom (quotientProj_congr I J hI hJ e) ≫ quotientToComplex J hJ =
      quotientToComplex I hI := by
  subst J
  simp

/-- The original incidence surface carries its canonical Proj structure
morphism to the complex base. -/
def literalSurfaceToComplex : literalIncidenceSurface ⟶ Spec (CommRingCat.of ℂ) :=
  quotientToComplex
    (CycleQ2GeometricIncidenceProj.pointEquations (seedPoint (57 : ℂ) Complex.I))
    (CycleQ2GeometricIncidenceProj.pointEquations_homogeneous
      (seedPoint (57 : ℂ) Complex.I))

theorem literalSurfaceToComplex_compatibility :
    literalIncidenceSurfaceIso.hom ≫ CycleQ2SurfaceCechTwoScalar.surfaceToComplex 57 1 =
      literalSurfaceToComplex :=
  quotientToComplex_congr
    (CycleQ2GeometricIncidenceProj.pointEquations (seedPoint (57 : ℂ) Complex.I))
    (surfaceIdeal 57 1)
    (CycleQ2GeometricIncidenceProj.pointEquations_homogeneous
      (seedPoint (57 : ℂ) Complex.I))
    (CycleQ2CartierSurfaceGrading.surfaceIdeal_homogeneous 57 1)
    literalPointSurface_ideal

end CycleQ2OriginalSurfaceChartBinding
end

end


section

/-!
Actual augmented-Jacobian charts of the projective curve immersion.
The local rings and local quotient maps are exactly those used by the
proved affine normal-adjunction calculation. No affine presentation or
pullback identification is supplied as an assumption.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace CycleQ2SurfaceNormalCharts
open CategoryTheory AlgebraicGeometry MvPolynomial
open CycleQ2GeometricAffineCurveCharts CycleQ2GeometricSurfaceAdjunction
open CycleQ2GeometricSurfaceDehomogenizedCharts (firstEquations secondEquations)
open CycleQ2GeometricSurfaceCurveCharts (firstAffineCurveMap secondAffineCurveMap)
open CycleQ2GeometricProjectiveCurve CycleQ2GeometricLiteralSurface
open CycleQ2CartierProjectiveCover CycleQ2SeedTrace CycleQ2SeedCechTheta
open CycleQ2NormalConnecting

section Localization
variable {A B : Type} [CommRing A] [CommRing B]

/-- The image of the actual localization morphism is its principal open. -/
theorem localization_opensRange (d : A) :
    (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away d)))).opensRange =
      PrimeSpectrum.basicOpen d := by
  apply TopologicalSpace.Opens.ext
  exact PrimeSpectrum.localization_away_comap_range (Localization.Away d) d

/-- Localization of a ring map gives the actual pullback of affine schemes. -/
theorem localization_isPullback (f : A →+* B) (d : A) :
    IsPullback
      (Spec.map (CommRingCat.ofHom
        (IsLocalization.Away.map (Localization.Away d) (Localization.Away (f d)) f d)))
      (Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away (f d)))))
      (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away d))))
      (Spec.map (CommRingCat.ofHom f)) := by
  apply IsOpenImmersion.isPullback
  · rw [← Spec.map_comp, ← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    ext a
    change algebraMap B (Localization.Away (f d)) (f a) =
      IsLocalization.Away.map (Localization.Away d) (Localization.Away (f d)) f d
        (algebraMap A (Localization.Away d) a)
    rw [IsLocalization.Away.map, IsLocalization.map_eq]
  · rw [localization_opensRange, localization_opensRange]
    exact SpecMap_preimage_basicOpen (CommRingCat.ofHom f) d

/-- A localization of an actual complex chart remains over the same
complex structure morphism. -/
theorem localization_overComplex [Algebra ℂ A] {X : Scheme}
    (u : Spec (CommRingCat.of A) ⟶ X) (c : X ⟶ Spec (CommRingCat.of ℂ))
    (hu : u ≫ c = Spec.map (CommRingCat.ofHom (algebraMap ℂ A))) (d : A) :
    (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away d))) ≫ u) ≫ c =
      Spec.map (CommRingCat.ofHom (algebraMap ℂ (Localization.Away d))) := by
  rw [Category.assoc, hu, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  ext z
  exact (IsScalarTower.algebraMap_apply ℂ A (Localization.Away d) z).symm

end Localization


/-- The parallel dehomogenized curve presentation has the original
projective complex coefficient map. -/
theorem curve_basicOpenCoefficient_coordinate (r θ : ℂ) (i : Fin 4) (c : ℂ) :
    CycleQ2GeometricProjectiveCoefficients.basicOpenCoefficient r θ (curveMap r θ (X i)) c =
      CycleQ2GeometricDehomogenizedCharts.constants r θ i c := by
  apply HomogeneousLocalization.val_injective
  rw [CycleQ2GeometricDehomogenizedCharts.constants_val]
  change Localization.mk (algebraMap ℂ (CurveRing r θ) c) 1 = _
  rw [Localization.mk_one_eq_algebraMap]
  rfl

theorem firstCurveChart_overComplex (r θ : ℂ) :
    ((CycleQ2GeometricAffineProjectiveCharts.firstAffineChart r θ).inv ≫
        (coordinateProjectivePatch r θ 1).ι) ≫
      CycleQ2GeometricDifferentialSheaf.projectiveToComplex r θ =
        Spec.map (CommRingCat.ofHom
          (algebraMap ℂ (ChartRing ![firstQuadric r, firstCubic θ]))) := by
  have h := congrArg
    (fun f : Spec (CommRingCat.of (ChartRing ![firstQuadric r, firstCubic θ])) ⟶
        projectiveCurve r θ => f ≫ CycleQ2GeometricDifferentialSheaf.projectiveToComplex r θ)
    (CycleQ2GeometricSurfaceCurveCharts.firstCurveAffineChart_inv_ι r θ)
  have hc := CycleQ2GeometricProjectiveCoefficients.awayι_projectiveToComplex
    r θ (curveMap r θ (X 1)) (coordinate_mem_grade r θ 1) (by decide)
  have he : CommRingCat.ofHom
      (CycleQ2GeometricProjectiveCoefficients.basicOpenCoefficient r θ (curveMap r θ (X 1))) ≫
      CommRingCat.ofHom (CycleQ2GeometricDehomogenizedCharts.firstChartEquiv r θ).toRingHom =
      CommRingCat.ofHom (algebraMap ℂ (ChartRing ![firstQuadric r, firstCubic θ])) := by
    apply CommRingCat.hom_ext
    ext c
    change CycleQ2GeometricDehomogenizedCharts.firstChartEquiv r θ
      (CycleQ2GeometricProjectiveCoefficients.basicOpenCoefficient r θ
        (curveMap r θ (X 1)) c) = _
    rw [curve_basicOpenCoefficient_coordinate]
    exact CycleQ2GeometricDehomogenizedCharts.firstChartEquiv_constants r θ c
  exact h.trans ((Category.assoc _ _ _).trans
    ((congrArg (fun k : Spec (CommRingCat.of
        (CycleQ2GeometricDehomogenizedCharts.CoordinateRing r θ 1)) ⟶
        Spec (CommRingCat.of ℂ) =>
      Spec.map (CommRingCat.ofHom
        (CycleQ2GeometricDehomogenizedCharts.firstChartEquiv r θ).toRingHom) ≫ k) hc).trans
      ((Spec.map_comp _ _).symm.trans (congrArg Spec.map he))))

theorem secondCurveChart_overComplex (r θ : ℂ) :
    ((CycleQ2GeometricAffineProjectiveCharts.secondAffineChart r θ).inv ≫
        (coordinateProjectivePatch r θ 2).ι) ≫
      CycleQ2GeometricDifferentialSheaf.projectiveToComplex r θ =
        Spec.map (CommRingCat.ofHom
          (algebraMap ℂ (ChartRing ![secondQuadric r, secondCubic θ]))) := by
  have h := congrArg
    (fun f : Spec (CommRingCat.of (ChartRing ![secondQuadric r, secondCubic θ])) ⟶
        projectiveCurve r θ => f ≫ CycleQ2GeometricDifferentialSheaf.projectiveToComplex r θ)
    (CycleQ2GeometricSurfaceCurveCharts.secondCurveAffineChart_inv_ι r θ)
  have hc := CycleQ2GeometricProjectiveCoefficients.awayι_projectiveToComplex
    r θ (curveMap r θ (X 2)) (coordinate_mem_grade r θ 2) (by decide)
  have he : CommRingCat.ofHom
      (CycleQ2GeometricProjectiveCoefficients.basicOpenCoefficient r θ (curveMap r θ (X 2))) ≫
      CommRingCat.ofHom (CycleQ2GeometricDehomogenizedCharts.secondChartEquiv r θ).toRingHom =
      CommRingCat.ofHom (algebraMap ℂ (ChartRing ![secondQuadric r, secondCubic θ])) := by
    apply CommRingCat.hom_ext
    ext c
    change CycleQ2GeometricDehomogenizedCharts.secondChartEquiv r θ
      (CycleQ2GeometricProjectiveCoefficients.basicOpenCoefficient r θ
        (curveMap r θ (X 2)) c) = _
    rw [curve_basicOpenCoefficient_coordinate]
    exact CycleQ2GeometricDehomogenizedCharts.secondChartEquiv_constants r θ c
  exact h.trans ((Category.assoc _ _ _).trans
    ((congrArg (fun k : Spec (CommRingCat.of
        (CycleQ2GeometricDehomogenizedCharts.CoordinateRing r θ 2)) ⟶
        Spec (CommRingCat.of ℂ) =>
      Spec.map (CommRingCat.ofHom
        (CycleQ2GeometricDehomogenizedCharts.secondChartEquiv r θ).toRingHom) ≫ k) hc).trans
      ((Spec.map_comp _ _).symm.trans (congrArg Spec.map he))))

abbrev FirstNormalSurface (r θ : ℂ) (i : Fin 2) (j : Fin 3) :=
  NormalSurfacePatch (firstQuadric r) (firstCubic θ)
    (firstSurfaceDehomogenize (originalG1 r)) (firstSurfaceDehomogenize originalG2)
    (firstSurfaceDehomogenize (thetaK θ)) i j

abbrev FirstNormalCurve (r θ : ℂ) (i : Fin 2) (j : Fin 3) :=
  NormalCurvePatch (firstQuadric r) (firstCubic θ)
    (firstSurfaceDehomogenize (originalG1 r)) (firstSurfaceDehomogenize originalG2)
    (firstSurfaceDehomogenize (thetaK θ)) i j

abbrev SecondNormalSurface (r θ : ℂ) (i : Fin 2) (j : Fin 3) :=
  NormalSurfacePatch (secondQuadric r) (secondCubic θ)
    (secondSurfaceDehomogenize (originalG1 r)) (secondSurfaceDehomogenize originalG2)
    (secondSurfaceDehomogenize (thetaK θ)) i j

abbrev SecondNormalCurve (r θ : ℂ) (i : Fin 2) (j : Fin 3) :=
  NormalCurvePatch (secondQuadric r) (secondCubic θ)
    (secondSurfaceDehomogenize (originalG1 r)) (secondSurfaceDehomogenize originalG2)
    (secondSurfaceDehomogenize (thetaK θ)) i j

abbrev firstNormalMap (r θ : ℂ) (i : Fin 2) (j : Fin 3) :
    FirstNormalSurface r θ i j →ₐ[ℂ] FirstNormalCurve r θ i j :=
  normalChartMap (firstQuadric r) (firstCubic θ)
    (firstSurfaceDehomogenize (originalG1 r)) (firstSurfaceDehomogenize originalG2)
    (firstSurfaceDehomogenize (thetaK θ)) i j

abbrev secondNormalMap (r θ : ℂ) (i : Fin 2) (j : Fin 3) :
    SecondNormalSurface r θ i j →ₐ[ℂ] SecondNormalCurve r θ i j :=
  normalChartMap (secondQuadric r) (secondCubic θ)
    (secondSurfaceDehomogenize (originalG1 r)) (secondSurfaceDehomogenize originalG2)
    (secondSurfaceDehomogenize (thetaK θ)) i j

abbrev firstNormalDen (r θ : ℂ) (i : Fin 2) (j : Fin 3) :=
  augmentedJacobian (firstEquations r θ) (normalPolynomial (firstQuadric r) i)
    (includeCurve (X j))

abbrev secondNormalDen (r θ : ℂ) (i : Fin 2) (j : Fin 3) :=
  augmentedJacobian (secondEquations r θ) (normalPolynomial (secondQuadric r) i)
    (includeCurve (X j))


/-- The canonical localization algebra, with its concrete chart base made explicit. -/
instance firstNormalSurfaceAlgebra (r θ : ℂ) (i : Fin 2) (j : Fin 3) :
    Algebra (SurfaceChartRing (firstEquations r θ)) (FirstNormalSurface r θ i j) :=
  inferInstanceAs (Algebra (SurfaceChartRing (firstEquations r θ))
    (Localization.Away (firstNormalDen r θ i j)))

instance firstNormalSurface_isLocalization (r θ : ℂ) (i : Fin 2) (j : Fin 3) :
    IsLocalization.Away (firstNormalDen r θ i j) (FirstNormalSurface r θ i j) :=
  inferInstanceAs (IsLocalization.Away (firstNormalDen r θ i j)
    (Localization.Away (firstNormalDen r θ i j)))

/-- The canonical localization algebra, with its concrete chart base made explicit. -/
instance secondNormalSurfaceAlgebra (r θ : ℂ) (i : Fin 2) (j : Fin 3) :
    Algebra (SurfaceChartRing (secondEquations r θ)) (SecondNormalSurface r θ i j) :=
  inferInstanceAs (Algebra (SurfaceChartRing (secondEquations r θ))
    (Localization.Away (secondNormalDen r θ i j)))

instance secondNormalSurface_isLocalization (r θ : ℂ) (i : Fin 2) (j : Fin 3) :
    IsLocalization.Away (secondNormalDen r θ i j) (SecondNormalSurface r θ i j) :=
  inferInstanceAs (IsLocalization.Away (secondNormalDen r θ i j)
    (Localization.Away (secondNormalDen r θ i j)))

def firstNormalSurfaceEmbedding (r θ : ℂ) (i : Fin 2) (j : Fin 3) :
    Spec (CommRingCat.of (FirstNormalSurface r θ i j)) ⟶ surface r θ :=
  Spec.map (CommRingCat.ofHom
      (algebraMap (SurfaceChartRing (firstEquations r θ)) (FirstNormalSurface r θ i j))) ≫
    (CycleQ2GeometricSurfaceDehomogenizedCharts.firstAffineChart r θ).inv ≫
      (coordinatePatch r θ 1).ι

def firstNormalCurveEmbedding (r θ : ℂ) (i : Fin 2) (j : Fin 3) :
    Spec (CommRingCat.of (FirstNormalCurve r θ i j)) ⟶ projectiveCurve r θ :=
  Spec.map (CommRingCat.ofHom
      (algebraMap (ChartRing ![firstQuadric r, firstCubic θ]) (FirstNormalCurve r θ i j))) ≫
    (CycleQ2GeometricAffineProjectiveCharts.firstAffineChart r θ).inv ≫
      (coordinateProjectivePatch r θ 1).ι

def secondNormalSurfaceEmbedding (r θ : ℂ) (i : Fin 2) (j : Fin 3) :
    Spec (CommRingCat.of (SecondNormalSurface r θ i j)) ⟶ surface r θ :=
  Spec.map (CommRingCat.ofHom
      (algebraMap (SurfaceChartRing (secondEquations r θ)) (SecondNormalSurface r θ i j))) ≫
    (CycleQ2GeometricSurfaceDehomogenizedCharts.secondAffineChart r θ).inv ≫
      (coordinatePatch r θ 2).ι

def secondNormalCurveEmbedding (r θ : ℂ) (i : Fin 2) (j : Fin 3) :
    Spec (CommRingCat.of (SecondNormalCurve r θ i j)) ⟶ projectiveCurve r θ :=
  Spec.map (CommRingCat.ofHom
      (algebraMap (ChartRing ![secondQuadric r, secondCubic θ]) (SecondNormalCurve r θ i j))) ≫
    (CycleQ2GeometricAffineProjectiveCharts.secondAffineChart r θ).inv ≫
      (coordinateProjectivePatch r θ 2).ι

instance firstNormalSurfaceEmbedding_isOpenImmersion (r θ : ℂ) (i : Fin 2) (j : Fin 3) :
    IsOpenImmersion (firstNormalSurfaceEmbedding r θ i j) := by
  change IsOpenImmersion
    (Spec.map (CommRingCat.ofHom (algebraMap (SurfaceChartRing (firstEquations r θ))
      (Localization.Away (firstNormalDen r θ i j)))) ≫
      (CycleQ2GeometricSurfaceDehomogenizedCharts.firstAffineChart r θ).inv ≫
        (coordinatePatch r θ 1).ι)
  infer_instance

instance firstNormalCurveEmbedding_isOpenImmersion (r θ : ℂ) (i : Fin 2) (j : Fin 3) :
    IsOpenImmersion (firstNormalCurveEmbedding r θ i j) := by
  unfold firstNormalCurveEmbedding
  infer_instance

instance secondNormalSurfaceEmbedding_isOpenImmersion (r θ : ℂ) (i : Fin 2) (j : Fin 3) :
    IsOpenImmersion (secondNormalSurfaceEmbedding r θ i j) := by
  change IsOpenImmersion
    (Spec.map (CommRingCat.ofHom (algebraMap (SurfaceChartRing (secondEquations r θ))
      (Localization.Away (secondNormalDen r θ i j)))) ≫
      (CycleQ2GeometricSurfaceDehomogenizedCharts.secondAffineChart r θ).inv ≫
        (coordinatePatch r θ 2).ι)
  infer_instance

instance secondNormalCurveEmbedding_isOpenImmersion (r θ : ℂ) (i : Fin 2) (j : Fin 3) :
    IsOpenImmersion (secondNormalCurveEmbedding r θ i j) := by
  unfold secondNormalCurveEmbedding
  infer_instance

/-- The first-chart normal-adjunction map is the actual restricted projective immersion. -/
theorem firstNormal_isPullback (r θ : ℂ) (i : Fin 2) (j : Fin 3) :
    IsPullback (Spec.map (CommRingCat.ofHom (firstNormalMap r θ i j).toRingHom))
      (firstNormalCurveEmbedding r θ i j) (firstNormalSurfaceEmbedding r θ i j)
      (curveToSurface r θ) := by
  exact (localization_isPullback (firstAffineCurveMap r θ).toRingHom
      (firstNormalDen r θ i j)).paste_vert
    (CycleQ2GeometricSurfaceCurveCharts.firstAffineChart_isPullback r θ)

/-- The second-chart normal-adjunction map is the actual restricted projective immersion. -/
theorem secondNormal_isPullback (r θ : ℂ) (i : Fin 2) (j : Fin 3) :
    IsPullback (Spec.map (CommRingCat.ofHom (secondNormalMap r θ i j).toRingHom))
      (secondNormalCurveEmbedding r θ i j) (secondNormalSurfaceEmbedding r θ i j)
      (curveToSurface r θ) := by
  exact (localization_isPullback (secondAffineCurveMap r θ).toRingHom
      (secondNormalDen r θ i j)).paste_vert
    (CycleQ2GeometricSurfaceCurveCharts.secondAffineChart_isPullback r θ)

theorem firstNormalSurfaceEmbedding_overComplex (r θ : ℂ) (i : Fin 2) (j : Fin 3) :
    firstNormalSurfaceEmbedding r θ i j ≫
        CycleQ2GeometricSurfaceCoefficients.projectiveToComplex r θ =
      Spec.map (CommRingCat.ofHom (algebraMap ℂ (FirstNormalSurface r θ i j))) := by
  change (Spec.map (CommRingCat.ofHom
      (algebraMap (SurfaceChartRing (firstEquations r θ))
        (Localization.Away (firstNormalDen r θ i j)))) ≫
      (CycleQ2GeometricSurfaceDehomogenizedCharts.firstAffineChart r θ).inv ≫
        (coordinatePatch r θ 1).ι) ≫
      CycleQ2GeometricSurfaceCoefficients.projectiveToComplex r θ =
        Spec.map (CommRingCat.ofHom
          (algebraMap ℂ (Localization.Away (firstNormalDen r θ i j))))
  exact localization_overComplex
    ((CycleQ2GeometricSurfaceDehomogenizedCharts.firstAffineChart r θ).inv ≫
      (coordinatePatch r θ 1).ι)
    (CycleQ2GeometricSurfaceCoefficients.projectiveToComplex r θ)
    (by simpa only [Category.assoc] using
      CycleQ2GeometricSurfaceCoefficients.firstAffineChart_overComplex r θ)
    (firstNormalDen r θ i j)

theorem secondNormalSurfaceEmbedding_overComplex (r θ : ℂ) (i : Fin 2) (j : Fin 3) :
    secondNormalSurfaceEmbedding r θ i j ≫
        CycleQ2GeometricSurfaceCoefficients.projectiveToComplex r θ =
      Spec.map (CommRingCat.ofHom (algebraMap ℂ (SecondNormalSurface r θ i j))) := by
  change (Spec.map (CommRingCat.ofHom
      (algebraMap (SurfaceChartRing (secondEquations r θ))
        (Localization.Away (secondNormalDen r θ i j)))) ≫
      (CycleQ2GeometricSurfaceDehomogenizedCharts.secondAffineChart r θ).inv ≫
        (coordinatePatch r θ 2).ι) ≫
      CycleQ2GeometricSurfaceCoefficients.projectiveToComplex r θ =
        Spec.map (CommRingCat.ofHom
          (algebraMap ℂ (Localization.Away (secondNormalDen r θ i j))))
  exact localization_overComplex
    ((CycleQ2GeometricSurfaceDehomogenizedCharts.secondAffineChart r θ).inv ≫
      (coordinatePatch r θ 2).ι)
    (CycleQ2GeometricSurfaceCoefficients.projectiveToComplex r θ)
    (by simpa only [Category.assoc] using
      CycleQ2GeometricSurfaceCoefficients.secondAffineChart_overComplex r θ)
    (secondNormalDen r θ i j)


/-- The actual image open of the specified augmented-Jacobian chart. -/
def firstNormalSurfaceOpen (r θ : ℂ) (i : Fin 2) (j : Fin 3) :
    (surface r θ).Opens := (firstNormalSurfaceEmbedding r θ i j).opensRange

theorem firstNormalSurfaceOpen_isAffine (r θ : ℂ) (i : Fin 2) (j : Fin 3) :
    IsAffineOpen (firstNormalSurfaceOpen r θ i j) :=
  isAffineOpen_opensRange (firstNormalSurfaceEmbedding r θ i j)

/-- The original local adjunction ring presents this actual projective open. -/
def firstNormalSurfaceChart (r θ : ℂ) (i : Fin 2) (j : Fin 3) :
    (firstNormalSurfaceOpen r θ i j).toScheme ≅
      Spec (CommRingCat.of (FirstNormalSurface r θ i j)) :=
  IsOpenImmersion.isoOfRangeEq (firstNormalSurfaceOpen r θ i j).ι
    (firstNormalSurfaceEmbedding r θ i j) (by rw [Scheme.Opens.range_ι]; rfl)

theorem firstNormalSurfaceChart_inv_ι (r θ : ℂ) (i : Fin 2) (j : Fin 3) :
    (firstNormalSurfaceChart r θ i j).inv ≫ (firstNormalSurfaceOpen r θ i j).ι =
      firstNormalSurfaceEmbedding r θ i j :=
  IsOpenImmersion.isoOfRangeEq_inv_fac _ _ _

/-- The actual image open of the specified augmented-Jacobian chart. -/
def firstNormalCurveOpen (r θ : ℂ) (i : Fin 2) (j : Fin 3) :
    (projectiveCurve r θ).Opens := (firstNormalCurveEmbedding r θ i j).opensRange

theorem firstNormalCurveOpen_isAffine (r θ : ℂ) (i : Fin 2) (j : Fin 3) :
    IsAffineOpen (firstNormalCurveOpen r θ i j) :=
  isAffineOpen_opensRange (firstNormalCurveEmbedding r θ i j)

/-- The original local adjunction ring presents this actual projective open. -/
def firstNormalCurveChart (r θ : ℂ) (i : Fin 2) (j : Fin 3) :
    (firstNormalCurveOpen r θ i j).toScheme ≅
      Spec (CommRingCat.of (FirstNormalCurve r θ i j)) :=
  IsOpenImmersion.isoOfRangeEq (firstNormalCurveOpen r θ i j).ι
    (firstNormalCurveEmbedding r θ i j) (by rw [Scheme.Opens.range_ι]; rfl)

theorem firstNormalCurveChart_inv_ι (r θ : ℂ) (i : Fin 2) (j : Fin 3) :
    (firstNormalCurveChart r θ i j).inv ≫ (firstNormalCurveOpen r θ i j).ι =
      firstNormalCurveEmbedding r θ i j :=
  IsOpenImmersion.isoOfRangeEq_inv_fac _ _ _

/-- The curve chart is exactly the preimage of the surface chart. -/
theorem firstNormal_preimage (r θ : ℂ) (i : Fin 2) (j : Fin 3) :
    curveToSurface r θ ⁻¹ᵁ firstNormalSurfaceOpen r θ i j =
      firstNormalCurveOpen r θ i j := by
  have h := IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback
    (firstNormal_isPullback r θ i j) (⊤ : (Spec (CommRingCat.of
      (FirstNormalSurface r θ i j))).Opens)
  change curveToSurface r θ ⁻¹ᵁ (firstNormalSurfaceEmbedding r θ i j).opensRange =
    (firstNormalCurveEmbedding r θ i j).opensRange
  simpa only [Scheme.Hom.preimage_top, Scheme.Hom.image_top_eq_opensRange] using h.symm

/-- The actual image open of the specified augmented-Jacobian chart. -/
def secondNormalSurfaceOpen (r θ : ℂ) (i : Fin 2) (j : Fin 3) :
    (surface r θ).Opens := (secondNormalSurfaceEmbedding r θ i j).opensRange

theorem secondNormalSurfaceOpen_isAffine (r θ : ℂ) (i : Fin 2) (j : Fin 3) :
    IsAffineOpen (secondNormalSurfaceOpen r θ i j) :=
  isAffineOpen_opensRange (secondNormalSurfaceEmbedding r θ i j)

/-- The original local adjunction ring presents this actual projective open. -/
def secondNormalSurfaceChart (r θ : ℂ) (i : Fin 2) (j : Fin 3) :
    (secondNormalSurfaceOpen r θ i j).toScheme ≅
      Spec (CommRingCat.of (SecondNormalSurface r θ i j)) :=
  IsOpenImmersion.isoOfRangeEq (secondNormalSurfaceOpen r θ i j).ι
    (secondNormalSurfaceEmbedding r θ i j) (by rw [Scheme.Opens.range_ι]; rfl)

theorem secondNormalSurfaceChart_inv_ι (r θ : ℂ) (i : Fin 2) (j : Fin 3) :
    (secondNormalSurfaceChart r θ i j).inv ≫ (secondNormalSurfaceOpen r θ i j).ι =
      secondNormalSurfaceEmbedding r θ i j :=
  IsOpenImmersion.isoOfRangeEq_inv_fac _ _ _

/-- The actual image open of the specified augmented-Jacobian chart. -/
def secondNormalCurveOpen (r θ : ℂ) (i : Fin 2) (j : Fin 3) :
    (projectiveCurve r θ).Opens := (secondNormalCurveEmbedding r θ i j).opensRange

theorem secondNormalCurveOpen_isAffine (r θ : ℂ) (i : Fin 2) (j : Fin 3) :
    IsAffineOpen (secondNormalCurveOpen r θ i j) :=
  isAffineOpen_opensRange (secondNormalCurveEmbedding r θ i j)

/-- The original local adjunction ring presents this actual projective open. -/
def secondNormalCurveChart (r θ : ℂ) (i : Fin 2) (j : Fin 3) :
    (secondNormalCurveOpen r θ i j).toScheme ≅
      Spec (CommRingCat.of (SecondNormalCurve r θ i j)) :=
  IsOpenImmersion.isoOfRangeEq (secondNormalCurveOpen r θ i j).ι
    (secondNormalCurveEmbedding r θ i j) (by rw [Scheme.Opens.range_ι]; rfl)

theorem secondNormalCurveChart_inv_ι (r θ : ℂ) (i : Fin 2) (j : Fin 3) :
    (secondNormalCurveChart r θ i j).inv ≫ (secondNormalCurveOpen r θ i j).ι =
      secondNormalCurveEmbedding r θ i j :=
  IsOpenImmersion.isoOfRangeEq_inv_fac _ _ _

/-- The curve chart is exactly the preimage of the surface chart. -/
theorem secondNormal_preimage (r θ : ℂ) (i : Fin 2) (j : Fin 3) :
    curveToSurface r θ ⁻¹ᵁ secondNormalSurfaceOpen r θ i j =
      secondNormalCurveOpen r θ i j := by
  have h := IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback
    (secondNormal_isPullback r θ i j) (⊤ : (Spec (CommRingCat.of
      (SecondNormalSurface r θ i j))).Opens)
  change curveToSurface r θ ⁻¹ᵁ (secondNormalSurfaceEmbedding r θ i j).opensRange =
    (secondNormalCurveEmbedding r θ i j).opensRange
  simpa only [Scheme.Hom.preimage_top, Scheme.Hom.image_top_eq_opensRange] using h.symm


/-- The actual intrinsic immersion ideal restricts to the ideal of the
literal localized quotient used by normal adjunction. -/
theorem firstNormal_intrinsicIdeal (r θ : ℂ) (i : Fin 2) (j : Fin 3)
    (W : (Spec (CommRingCat.of (FirstNormalSurface r θ i j))).affineOpens) :
    (Spec.map (CommRingCat.ofHom (firstNormalMap r θ i j).toRingHom)).ker.ideal W =
      ((curveToSurface r θ).ker.ideal
        ⟨firstNormalSurfaceEmbedding r θ i j ''ᵁ W,
          W.2.image_of_isOpenImmersion _⟩).comap
        ((firstNormalSurfaceEmbedding r θ i j).appIso W).inv.hom :=
  Scheme.ker_ideal_of_isPullback_of_isOpenImmersion
    (curveToSurface r θ)
    (Spec.map (CommRingCat.ofHom (firstNormalMap r θ i j).toRingHom))
    (firstNormalCurveEmbedding r θ i j) (firstNormalSurfaceEmbedding r θ i j)
    (firstNormal_isPullback r θ i j) W

/-- The actual intrinsic immersion ideal restricts to the ideal of the
literal localized quotient used by normal adjunction. -/
theorem secondNormal_intrinsicIdeal (r θ : ℂ) (i : Fin 2) (j : Fin 3)
    (W : (Spec (CommRingCat.of (SecondNormalSurface r θ i j))).affineOpens) :
    (Spec.map (CommRingCat.ofHom (secondNormalMap r θ i j).toRingHom)).ker.ideal W =
      ((curveToSurface r θ).ker.ideal
        ⟨secondNormalSurfaceEmbedding r θ i j ''ᵁ W,
          W.2.image_of_isOpenImmersion _⟩).comap
        ((secondNormalSurfaceEmbedding r θ i j).appIso W).inv.hom :=
  Scheme.ker_ideal_of_isPullback_of_isOpenImmersion
    (curveToSurface r θ)
    (Spec.map (CommRingCat.ofHom (secondNormalMap r θ i j).toRingHom))
    (secondNormalCurveEmbedding r θ i j) (secondNormalSurfaceEmbedding r θ i j)
    (secondNormal_isPullback r θ i j) W


theorem firstNormalCurveEmbedding_overComplex (r θ : ℂ) (i : Fin 2) (j : Fin 3) :
    firstNormalCurveEmbedding r θ i j ≫
        CycleQ2GeometricDifferentialSheaf.projectiveToComplex r θ =
      Spec.map (CommRingCat.ofHom (algebraMap ℂ (FirstNormalCurve r θ i j))) := by
  change (Spec.map (CommRingCat.ofHom
      (algebraMap (ChartRing ![firstQuadric r, firstCubic θ])
        (Localization.Away (firstAffineCurveMap r θ (firstNormalDen r θ i j))))) ≫
      (CycleQ2GeometricAffineProjectiveCharts.firstAffineChart r θ).inv ≫
        (coordinateProjectivePatch r θ 1).ι) ≫
      CycleQ2GeometricDifferentialSheaf.projectiveToComplex r θ =
        Spec.map (CommRingCat.ofHom (algebraMap ℂ (Localization.Away (firstAffineCurveMap r θ (firstNormalDen r θ i j)))))
  exact localization_overComplex
    ((CycleQ2GeometricAffineProjectiveCharts.firstAffineChart r θ).inv ≫
      (coordinateProjectivePatch r θ 1).ι)
    (CycleQ2GeometricDifferentialSheaf.projectiveToComplex r θ)
    (firstCurveChart_overComplex r θ)
    (firstAffineCurveMap r θ (firstNormalDen r θ i j))

theorem secondNormalCurveEmbedding_overComplex (r θ : ℂ) (i : Fin 2) (j : Fin 3) :
    secondNormalCurveEmbedding r θ i j ≫
        CycleQ2GeometricDifferentialSheaf.projectiveToComplex r θ =
      Spec.map (CommRingCat.ofHom (algebraMap ℂ (SecondNormalCurve r θ i j))) := by
  change (Spec.map (CommRingCat.ofHom
      (algebraMap (ChartRing ![secondQuadric r, secondCubic θ])
        (Localization.Away (secondAffineCurveMap r θ (secondNormalDen r θ i j))))) ≫
      (CycleQ2GeometricAffineProjectiveCharts.secondAffineChart r θ).inv ≫
        (coordinateProjectivePatch r θ 2).ι) ≫
      CycleQ2GeometricDifferentialSheaf.projectiveToComplex r θ =
        Spec.map (CommRingCat.ofHom (algebraMap ℂ (Localization.Away (secondAffineCurveMap r θ (secondNormalDen r θ i j)))))
  exact localization_overComplex
    ((CycleQ2GeometricAffineProjectiveCharts.secondAffineChart r θ).inv ≫
      (coordinateProjectivePatch r θ 2).ι)
    (CycleQ2GeometricDifferentialSheaf.projectiveToComplex r θ)
    (secondCurveChart_overComplex r θ)
    (secondAffineCurveMap r θ (secondNormalDen r θ i j))

end CycleQ2SurfaceNormalCharts
end

end
