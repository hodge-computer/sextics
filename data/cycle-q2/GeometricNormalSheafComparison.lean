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
import Proposal.GeometricSurfaceAdjunction
import Proposal.GeometricSurfaceNormalCharts
import Proposal.GeometricSurfaceResidueFunctoriality
import Proposal.GeometricAffineChartSections
import Proposal.GeometricSurfaceResidueOverlap
import Proposal.GeometricProjectiveNormalClass
import Proposal.GeometricProjectiveTransition
import Proposal.GeometricSurfaceOverlap
import Proposal.GeometricProjectiveAffineCoefficients

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


section

/-! Internal linear Hom commutes with actual restriction along an open
immersion. The comparison uses the original image functor on opens and
the original inverse section-ring isomorphism in module restriction. -/
set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace CycleQ2InternalHomRestriction
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
  CycleQ2GeometricDifferentialSheaf CycleQ2GeometricIntrinsicNormal
  CycleQ2SourceNormalSheaf

variable {X Y : Scheme.{0}} (j : X ⟶ Y) [IsOpenImmersion j]

private theorem over_eq_of_left_eq {Z : Type*} [PartialOrder Z] {U : Z}
    {V W : Over U} (h : V.left = W.left) : V = W := by
  cases V
  cases W
  subst h
  congr <;> exact Subsingleton.elim _ _

/-- Every subopen of an image open is itself the image of its preimage. -/
theorem overImage_surjective (U : X.Opens) :
    Function.Surjective (Over.post (X := U) j.opensFunctor).obj := by
  intro V
  let W : Over U := Over.mk (homOfLE (show j ⁻¹ᵁ V.left ≤ U from by
    exact (j.preimage_mono (leOfHom V.hom)).trans (j.preimage_image_eq U).le))
  refine ⟨W, over_eq_of_left_eq ?_⟩
  change j ''ᵁ (j ⁻¹ᵁ V.left) = V.left
  rw [j.image_preimage_eq_opensRange_inf]
  exact inf_eq_right.mpr ((leOfHom V.hom).trans (j.image_le_opensRange U))

instance overImage_essSurj (U : X.Opens) :
    (Over.post (X := U) j.opensFunctor).EssSurj where
  mem_essImage V := by
    obtain ⟨W, hW⟩ := overImage_surjective j U V
    exact ⟨W, ⟨eqToIso hW⟩⟩

instance overImage_isEquivalence (U : X.Opens) :
    (Over.post (X := U) j.opensFunctor).IsEquivalence where

variable (M N : Y.Modules)

private abbrev restricted (M : Y.Modules) : X.Modules := M.restrict j

local instance schemeLocalHomModule (Z : Scheme.{0}) (P Q : Z.Modules) (U : Z.Opens) :
    Module Γ(Z,U) (LocalLinearHom Z.sheaf P Q U) :=
  localLinearHomModule Z.sheaf P Q U

/-- The canonical restriction of a locally linear natural transformation. -/
def localRestriction (U : X.Opens)
    (f : LocalLinearHom Y.sheaf M N (j ''ᵁ U)) :
    LocalLinearHom X.sheaf (restricted j M) (restricted j N) U :=
  ⟨Functor.whiskerLeft (Over.post (X := U) j.opensFunctor).op f.val, by
    intro V r m
    exact f.property ((Over.post (X := U) j.opensFunctor).obj V)
      ((j.appIso V.left).inv r) m⟩

/-- The underlying local restriction is additive. -/
def localRestrictionAddHom (U : X.Opens) :
    LocalLinearHom Y.sheaf M N (j ''ᵁ U) →+
      LocalLinearHom X.sheaf (restricted j M) (restricted j N) U where
  toFun := localRestriction j M N U
  map_zero' := by apply localLinearHom_ext; intro V m; rfl
  map_add' f g := by apply localLinearHom_ext; intro V m; rfl

/-- Restricting local Hom loses no information on an open immersion. -/
theorem localRestriction_bijective (U : X.Opens) :
    Function.Bijective (localRestriction j M N U) := by
  let E := Over.post (X := U) j.opensFunctor
  let F := (Functor.whiskeringLeft (Over U)ᵒᵖ (Over (j ''ᵁ U))ᵒᵖ AddCommGrpCat).obj E.op
  constructor
  · intro f g h
    apply Subtype.ext
    apply F.map_injective
    exact congrArg Subtype.val h
  · intro g
    let A : (Over (j ''ᵁ U))ᵒᵖ ⥤ AddCommGrpCat := (Over.forget (j ''ᵁ U)).op ⋙ M.presheaf
    let B : (Over (j ''ᵁ U))ᵒᵖ ⥤ AddCommGrpCat := (Over.forget (j ''ᵁ U)).op ⋙ N.presheaf
    let gg : F.obj A ⟶ F.obj B := g.val
    obtain ⟨f, hf⟩ := F.map_surjective gg
    have hlin : ∀ (V : Over (j ''ᵁ U)) (r : Γ(Y,V.left)) (m : Γ(M,V.left)),
        (show Γ(N,V.left) from f.app (op V) (r • m)) =
          r • (show Γ(N,V.left) from f.app (op V) m) := by
      intro V r m
      obtain ⟨W, hW⟩ := overImage_surjective j U V
      subst V
      have hfW := NatTrans.congr_app hf (op W)
      change f.app (op (E.obj W)) = g.val.app (op W) at hfW
      rw [hfW]
      let r' : Γ(Y,j ''ᵁ W.left) := r
      let m' : Γ(M,j ''ᵁ W.left) := m
      let gW : Γ(M,j ''ᵁ W.left) → Γ(N,j ''ᵁ W.left) := g.val.app (op W)
      change gW (r' • m') = r' • gW m'
      have hg : gW ((j.appIso W.left).inv ((j.appIso W.left).hom r') • m') =
          (j.appIso W.left).inv ((j.appIso W.left).hom r') • gW m' :=
        g.property W ((j.appIso W.left).hom r') m'
      simpa only [Iso.hom_inv_id_apply] using hg
    refine ⟨⟨f, hlin⟩, ?_⟩
    apply Subtype.ext
    exact hf

/-- The comparison commutes with the actual restrictions of sections. -/
theorem localRestriction_restrict {U V : X.Opens} (h : V ⟶ U)
    (f : LocalLinearHom Y.sheaf M N (j ''ᵁ U)) :
    localRestriction j M N V
      (restrictLocalLinearHom Y.sheaf M N (j.opensFunctor.map h).op f) =
    restrictLocalLinearHom X.sheaf (restricted j M) (restricted j N) h.op
      (localRestriction j M N U f) := by
  apply localLinearHom_ext
  intro W m
  rfl

/-- The comparison preserves the genuine scalar action of module restriction. -/
theorem localRestriction_smul (U : X.Opens) (r : Γ(X,U))
    (f : LocalLinearHom Y.sheaf M N (j ''ᵁ U)) :
    localRestriction j M N U ((j.appIso U).inv r • f) =
      r • localRestriction j M N U f := by
  apply localLinearHom_ext
  intro V m
  let W : Over (j ''ᵁ U) := (Over.post (X := U) j.opensFunctor).obj V
  let O : Y.Opens := j ''ᵁ V.left
  let n : Γ(N,O) := f.val.app (op W) m
  let a : Γ(Y,O) := Y.presheaf.map W.hom.op ((j.appIso U).inv r)
  let b : Γ(Y,O) := (j.appIso V.left).inv (X.presheaf.map V.hom.op r)
  change a • n = b • n
  exact congrArg (fun s : Γ(Y,O) => s • n)
    (ConcreteCategory.congr_hom (j.appIso_inv_naturality V.hom.op) r).symm

/-- Canonical restriction of the actual internal linear-Hom sheaf. -/
def internalHomRestriction :
    (show Y.Modules from moduleHomSheaf Y.sheaf M N).restrict j ⟶
      (show X.Modules from
        moduleHomSheaf X.sheaf (restricted j M) (restricted j N)) where
  val := PresheafOfModules.homMk
    { app U := AddCommGrpCat.ofHom (localRestrictionAddHom j M N U.unop)
      naturality {U V} h := by
        apply ConcreteCategory.hom_ext
        intro f
        exact localRestriction_restrict j M N h.unop f }
    (fun U r f => localRestriction_smul j M N U.unop r f)

instance internalHomRestriction_isIso : IsIso (internalHomRestriction j M N) := by
  apply Scheme.Modules.Hom.isIso_iff_isIso_app.mpr
  intro U
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  exact localRestriction_bijective j M N U

/-- Restriction along an open immersion commutes with intrinsic internal Hom,
with the original scalar actions on both sides. -/
def internalHomRestrictionIso :
    (show Y.Modules from moduleHomSheaf Y.sheaf M N).restrict j ≅
      (show X.Modules from
        moduleHomSheaf X.sheaf (restricted j M) (restricted j N)) :=
  asIso (internalHomRestriction j M N)

#print axioms overImage_surjective
#print axioms localRestriction
#print axioms localRestriction_bijective
#print axioms localRestriction_restrict
#print axioms localRestriction_smul
#print axioms internalHomRestrictionIso

end CycleQ2InternalHomRestriction
end

end


section

/-! Canonical internal-Hom functoriality and congruence for genuine
module-sheaf maps. This retains the original module structures. -/
set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace CycleQ2InternalHomCongr
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
  CycleQ2GeometricDifferentialSheaf CycleQ2GeometricIntrinsicNormal

variable {X : Scheme.{0}} {M₁ M₂ N₁ N₂ : X.Modules}

local instance schemeLocalHomModule (P Q : X.Modules) (U : X.Opens) :
    Module Γ(X,U) (LocalLinearHom X.sheaf P Q U) :=
  localLinearHomModule X.sheaf P Q U

/-- Precompose and postcompose a local linear map with genuine module maps. -/
def localHomMap (a : M₂ ⟶ M₁) (b : N₁ ⟶ N₂) (U : X.Opens)
    (f : LocalLinearHom X.sheaf M₁ N₁ U) : LocalLinearHom X.sheaf M₂ N₂ U := by
  refine ⟨Functor.whiskerLeft (Over.forget U).op a.mapPresheaf ≫ f.val ≫
    Functor.whiskerLeft (Over.forget U).op b.mapPresheaf, ?_⟩
  intro V r m
  exact (congrArg (fun n => b.app V.left (f.val.app (op V) n))
      (a.app_smul r m)).trans
    ((congrArg (b.app V.left) (f.property V r (a.app V.left m))).trans
      (b.app_smul r (f.val.app (op V) (a.app V.left m))))

def localHomMapAddHom (a : M₂ ⟶ M₁) (b : N₁ ⟶ N₂) (U : X.Opens) :
    LocalLinearHom X.sheaf M₁ N₁ U →+ LocalLinearHom X.sheaf M₂ N₂ U where
  toFun := localHomMap a b U
  map_zero' := by
    apply localLinearHom_ext
    intro V m
    exact (b.app V.left).hom.map_zero
  map_add' f g := by
    apply localLinearHom_ext
    intro V m
    exact (b.app V.left).hom.map_add _ _

theorem localHomMap_restrict (a : M₂ ⟶ M₁) (b : N₁ ⟶ N₂)
    {U V : X.Opens} (h : V ⟶ U) (f : LocalLinearHom X.sheaf M₁ N₁ U) :
    localHomMap a b V (restrictLocalLinearHom X.sheaf M₁ N₁ h.op f) =
      restrictLocalLinearHom X.sheaf M₂ N₂ h.op (localHomMap a b U f) := by
  apply localLinearHom_ext
  intro W m
  rfl

theorem localHomMap_smul (a : M₂ ⟶ M₁) (b : N₁ ⟶ N₂)
    (U : X.Opens) (r : Γ(X,U)) (f : LocalLinearHom X.sheaf M₁ N₁ U) :
    localHomMap a b U (r • f) = r • localHomMap a b U f := by
  apply localLinearHom_ext
  intro V m
  exact b.app_smul (X.presheaf.map V.hom.op r) (f.val.app (op V) (a.app V.left m))

/-- Functoriality of the actual internal linear-Hom sheaf. -/
def internalHomMap (a : M₂ ⟶ M₁) (b : N₁ ⟶ N₂) :
    (show X.Modules from moduleHomSheaf X.sheaf M₁ N₁) ⟶
      (show X.Modules from moduleHomSheaf X.sheaf M₂ N₂) where
  val := PresheafOfModules.homMk
    { app U := AddCommGrpCat.ofHom (localHomMapAddHom a b U.unop)
      naturality {U V} h := by
        apply ConcreteCategory.hom_ext
        intro f
        exact localHomMap_restrict a b h.unop f }
    (fun U r f => localHomMap_smul a b U.unop r f)

/-- The local map for two isomorphisms is the original Hom congruence
between the restricted module sheaves. -/
def localHomEquiv (a : M₁ ≅ M₂) (b : N₁ ≅ N₂) (U : X.Opens) :
    LocalLinearHom X.sheaf M₁ N₁ U ≃ LocalLinearHom X.sheaf M₂ N₂ U :=
  let F := SheafOfModules.overFunctor X.ringCatSheaf U
  (localLinearHomEquiv X.sheaf M₁ N₁ U).trans
    ((Iso.homCongr (F.mapIso a) (F.mapIso b)).trans
      (localLinearHomEquiv X.sheaf M₂ N₂ U).symm)

theorem localHomEquiv_apply (a : M₁ ≅ M₂) (b : N₁ ≅ N₂) (U : X.Opens)
    (f : LocalLinearHom X.sheaf M₁ N₁ U) :
    localHomEquiv a b U f = localHomMap a.inv b.hom U f := by
  apply localLinearHom_ext
  intro V m
  rfl

theorem localHomMap_bijective (a : M₁ ≅ M₂) (b : N₁ ≅ N₂) (U : X.Opens) :
    Function.Bijective (localHomMap a.inv b.hom U) := by
  let e := localHomEquiv a b U
  constructor
  · intro f g h
    apply e.injective
    exact (localHomEquiv_apply a b U f).trans (h.trans (localHomEquiv_apply a b U g).symm)
  · intro g
    obtain ⟨f, hf⟩ := e.surjective g
    exact ⟨f, (localHomEquiv_apply a b U f).symm.trans hf⟩

instance internalHomMap_isIso (a : M₁ ≅ M₂) (b : N₁ ≅ N₂) :
    IsIso (internalHomMap a.inv b.hom) := by
  apply Scheme.Modules.Hom.isIso_iff_isIso_app.mpr
  intro U
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  exact localHomMap_bijective a b U

/-- Canonical congruence of internal Hom under isomorphisms of its genuine
source and target module sheaves. -/
def internalHomCongr (a : M₁ ≅ M₂) (b : N₁ ≅ N₂) :
    (show X.Modules from moduleHomSheaf X.sheaf M₁ N₁) ≅
      (show X.Modules from moduleHomSheaf X.sheaf M₂ N₂) :=
  asIso (internalHomMap a.inv b.hom)

#print axioms localHomMap
#print axioms localHomMap_restrict
#print axioms localHomMap_smul
#print axioms internalHomMap
#print axioms localHomEquiv_apply
#print axioms internalHomCongr

end CycleQ2InternalHomCongr
end

end


section

/-! Source-side conormal and normal under actual Cartesian open restriction.
The original categorical kernel comparison is supplied by the public
intrinsic-normal construction; the remaining maps use the genuine scheme
module pullback and internal-Hom restriction isomorphisms. -/
set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace CycleQ2SourceNormalRestriction
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
  CycleQ2GeometricIntrinsicNormal CycleQ2SourceNormalSheaf
  CycleQ2InternalHomRestriction CycleQ2InternalHomCongr

variable {X X' Y Y' : Scheme.{0}} (j : X ⟶ Y) (j' : X' ⟶ Y')
  (u : X' ⟶ X) (v : Y' ⟶ Y) [IsOpenImmersion u] [IsOpenImmersion v]
  (h : IsPullback j' u v j)

/-- The actual conormal pullback commutes with the actual Cartesian open
restriction, by the original pullback composition isomorphisms. -/
def sourceConormalRestrictionIso : (sourceConormal j).restrict u ≅ sourceConormal j' :=
  (Scheme.Modules.restrictFunctorIsoPullback u).app (sourceConormal j) ≪≫
    (Scheme.Modules.pullbackComp u j).app (idealModule j) ≪≫
    (Scheme.Modules.pullbackCongr h.w.symm).app (idealModule j) ≪≫
    ((Scheme.Modules.pullbackComp j' v).app (idealModule j)).symm ≪≫
    (Scheme.Modules.pullback j').mapIso
      ((Scheme.Modules.restrictFunctorIsoPullback v).app (idealModule j)).symm ≪≫
    (Scheme.Modules.pullback j').mapIso (kernelIdealOpenBaseChangeIso j v u j' h)

/-- The intrinsic normal on the source restricts to the intrinsic normal
of the actual chart immersion, with its original module action. -/
def sourceNormalRestrictionIso : (sourceNormal j).restrict u ≅ sourceNormal j' :=
  internalHomRestrictionIso u (sourceConormal j) (structureModule X) ≪≫
    internalHomCongr (sourceConormalRestrictionIso j j' u v h)
      (Scheme.Modules.restrictUnitIso u)

/-- The same restriction comparison is an isomorphism of the complete
surface-side normal module sheaves. -/
def normalDirectImageRestrictionIso :
    (show Y.Modules from normalDirectImageSheaf j).restrict v ≅
      (show Y'.Modules from normalDirectImageSheaf j') :=
  internalHomRestrictionIso v (idealModule j) (imageModule j) ≪≫
    internalHomCongr (kernelIdealOpenBaseChangeIso j v u j' h)
      (imageStructureOpenBaseChangeIso j v u j' h)

/-- The genuine source normal sections on every image open. -/
def sourceNormalSectionsIso (U : X'.Opens) :
    Γ(sourceNormal j, u ''ᵁ U) ≅ Γ(sourceNormal j', U) :=
  ((sourceNormal j).restrictAppIso u U).symm ≪≫
    asIso ((sourceNormalRestrictionIso j j' u v h).hom.app U)

/-- The section comparison uses the original open-immersion coefficient
isomorphism, rather than a transported scalar action. -/
theorem sourceNormalSectionsIso_smul (U : X'.Opens) (r : Γ(X,u ''ᵁ U))
    (m : Γ(sourceNormal j,u ''ᵁ U)) :
    (sourceNormalSectionsIso j j' u v h U).hom (r • m) =
      (u.appIso U).hom r • (sourceNormalSectionsIso j j' u v h U).hom m := by
  let e := sourceNormalRestrictionIso j j' u v h
  have hs := ConcreteCategory.congr_hom
    (Scheme.Modules.smul_restrictAppIso_inv u (sourceNormal j) U r) m
  exact (congrArg (e.hom.app U) hs).trans
    (e.hom.app_smul ((u.appIso U).hom r) (((sourceNormal j).restrictAppIso u U).inv m))

/-- The full normal sheaf isomorphism induces the incoming range-open
comparison on its exact underlying local functional. -/
theorem normalDirectImageRestrictionIso_app_top
    (f : (normalDirectImageSheaf j).val.obj (op v.opensRange)) :
    (normalDirectImageRestrictionIso j j' u v h).hom.app ⊤
        ((normalDirectImageSheaf j).val.map
          (homOfLE (v.image_le_opensRange ⊤)).op f) =
      normalSectionOpenBaseChangeEquiv j v u j' h f := by
  apply localLinearHom_ext
  intro W m
  let K := kernelIdealOpenBaseChangeIso j v u j' h
  let I := imageStructureOpenBaseChangeIso j v u j' h
  let a := K.inv.val.app (op W.left) m
  exact congrArg (I.hom.val.app (op W.left))
    (localLinearHomOpenImmersionEquiv_app v (idealModule j) (imageModule j) f W.left a).symm

#print axioms sourceConormalRestrictionIso
#print axioms sourceNormalRestrictionIso
#print axioms normalDirectImageRestrictionIso
#print axioms sourceNormalSectionsIso
#print axioms sourceNormalSectionsIso_smul
#print axioms normalDirectImageRestrictionIso_app_top

end CycleQ2SourceNormalRestriction
end

end


section

/-! The intrinsic normal and conormal of the original projective immersion
restrict to the genuine normal and conormal of its actual augmented
Jacobian affine charts. The chart morphisms are the proved Cartesian
open restrictions of that same immersion. -/
set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace CycleQ2NormalAffineRestriction
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
  CycleQ2GeometricIntrinsicNormal CycleQ2SourceNormalSheaf
  CycleQ2SourceNormalRestriction CycleQ2SurfaceNormalCharts

variable (r θ : ℂ) (i : Fin 2) (k : Fin 3)

private abbrev firstMap :=
  Spec.map (CommRingCat.ofHom (firstNormalMap r θ i k).toRingHom)
private abbrev secondMap :=
  Spec.map (CommRingCat.ofHom (secondNormalMap r θ i k).toRingHom)

/-- First actual normal chart: the original categorical kernel restricts
to the kernel of the literal localized ring map. -/
def firstIdealRestrictionIso :
    (idealModule (CycleQ2ProjectiveCurveSurface.curveToSurface r θ)).restrict
        (firstNormalSurfaceEmbedding r θ i k) ≅ idealModule (firstMap r θ i k) :=
  kernelIdealOpenBaseChangeIso _ _ _ _ (firstNormal_isPullback r θ i k)

/-- Second actual normal chart: the original categorical kernel restricts
to the kernel of the literal localized ring map. -/
def secondIdealRestrictionIso :
    (idealModule (CycleQ2ProjectiveCurveSurface.curveToSurface r θ)).restrict
        (secondNormalSurfaceEmbedding r θ i k) ≅ idealModule (secondMap r θ i k) :=
  kernelIdealOpenBaseChangeIso _ _ _ _ (secondNormal_isPullback r θ i k)

def firstConormalRestrictionIso :
    (actualConormal r θ).restrict (firstNormalCurveEmbedding r θ i k) ≅
      sourceConormal (firstMap r θ i k) :=
  sourceConormalRestrictionIso _ _ _ _ (firstNormal_isPullback r θ i k)

def secondConormalRestrictionIso :
    (actualConormal r θ).restrict (secondNormalCurveEmbedding r θ i k) ≅
      sourceConormal (secondMap r θ i k) :=
  sourceConormalRestrictionIso _ _ _ _ (secondNormal_isPullback r θ i k)

/-- The actual source intrinsic normal on the first affine normal chart. -/
def firstNormalRestrictionIso :
    (actualNormal r θ).restrict (firstNormalCurveEmbedding r θ i k) ≅
      sourceNormal (firstMap r θ i k) :=
  sourceNormalRestrictionIso _ _ _ _ (firstNormal_isPullback r θ i k)

/-- The actual source intrinsic normal on the second affine normal chart. -/
def secondNormalRestrictionIso :
    (actualNormal r θ).restrict (secondNormalCurveEmbedding r θ i k) ≅
      sourceNormal (secondMap r θ i k) :=
  sourceNormalRestrictionIso _ _ _ _ (secondNormal_isPullback r θ i k)

def firstSurfaceNormalRestrictionIso :
    (show (CycleQ2CartierProjectiveCover.projectiveSurface r θ).Modules from
      literalNormalDirectImageSheaf r θ).restrict (firstNormalSurfaceEmbedding r θ i k) ≅
      (show (Spec (CommRingCat.of (FirstNormalSurface r θ i k))).Modules from
        normalDirectImageSheaf (firstMap r θ i k)) :=
  normalDirectImageRestrictionIso _ _ _ _ (firstNormal_isPullback r θ i k)

def secondSurfaceNormalRestrictionIso :
    (show (CycleQ2CartierProjectiveCover.projectiveSurface r θ).Modules from
      literalNormalDirectImageSheaf r θ).restrict (secondNormalSurfaceEmbedding r θ i k) ≅
      (show (Spec (CommRingCat.of (SecondNormalSurface r θ i k))).Modules from
        normalDirectImageSheaf (secondMap r θ i k)) :=
  normalDirectImageRestrictionIso _ _ _ _ (secondNormal_isPullback r θ i k)

/-- Actual normal sections on the first projective image open, identified
with the normal sections on the literal affine chart. -/
def firstNormalSectionsIso :
    Γ(actualNormal r θ, firstNormalCurveOpen r θ i k) ≅
      Γ(sourceNormal (firstMap r θ i k), ⊤) :=
  (actualNormal r θ).presheaf.mapIso
      (eqToIso (Scheme.Hom.image_top_eq_opensRange (firstNormalCurveEmbedding r θ i k))).op ≪≫
    ((actualNormal r θ).restrictAppIso (firstNormalCurveEmbedding r θ i k) ⊤).symm ≪≫
    asIso ((firstNormalRestrictionIso r θ i k).hom.app ⊤)

/-- Actual normal sections on the second projective image open, identified
with the normal sections on the literal affine chart. -/
def secondNormalSectionsIso :
    Γ(actualNormal r θ, secondNormalCurveOpen r θ i k) ≅
      Γ(sourceNormal (secondMap r θ i k), ⊤) :=
  (actualNormal r θ).presheaf.mapIso
      (eqToIso (Scheme.Hom.image_top_eq_opensRange (secondNormalCurveEmbedding r θ i k))).op ≪≫
    ((actualNormal r θ).restrictAppIso (secondNormalCurveEmbedding r θ i k) ⊤).symm ≪≫
    asIso ((secondNormalRestrictionIso r θ i k).hom.app ⊤)

#print axioms firstIdealRestrictionIso
#print axioms secondIdealRestrictionIso
#print axioms firstConormalRestrictionIso
#print axioms secondConormalRestrictionIso
#print axioms firstNormalRestrictionIso
#print axioms secondNormalRestrictionIso
#print axioms firstSurfaceNormalRestrictionIso
#print axioms secondSurfaceNormalRestrictionIso
#print axioms firstNormalSectionsIso
#print axioms secondNormalSectionsIso

end CycleQ2NormalAffineRestriction
end

end


section

/-! Coherence of the original pullback adjunction units under actual
scheme composition and open restriction. -/
set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace CycleQ2NormalRestrictionNaturality
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
  CycleQ2GeometricIntrinsicNormal CycleQ2SourceNormalSheaf
  CycleQ2SourceNormalRestriction CycleQ2NormalPushforward

variable {X Y Z : Scheme.{0}}

/-- Pullback composition uses the original adjunction units. -/
theorem pullbackUnit_comp (f : X ⟶ Y) (g : Y ⟶ Z) (M : Z.Modules) :
    (Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M ≫
      (Scheme.Modules.pushforward g).map
        ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
          ((Scheme.Modules.pullback g).obj M)) ≫
      (Scheme.Modules.pushforward f ⋙ Scheme.Modules.pushforward g).map
        ((Scheme.Modules.pullbackComp f g).hom.app M) ≫
      (Scheme.Modules.pushforwardComp f g).hom.app
        ((Scheme.Modules.pullback (f ≫ g)).obj M) =
    (Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g)).unit.app M := by
  have h := unit_conjugateEquiv
    ((Scheme.Modules.pullbackPushforwardAdjunction g).comp
      (Scheme.Modules.pullbackPushforwardAdjunction f))
    (Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g))
    (Scheme.Modules.pullbackComp f g).inv M
  rw [Scheme.Modules.conjugateEquiv_pullbackComp_inv] at h
  rw [← Category.assoc]
  change ((Scheme.Modules.pullbackPushforwardAdjunction g).comp
      (Scheme.Modules.pullbackPushforwardAdjunction f)).unit.app M ≫ _ ≫ _ = _
  rw [(Scheme.Modules.pushforwardComp f g).hom.naturality
    ((Scheme.Modules.pullbackComp f g).hom.app M)]
  rw [← Category.assoc, h, Category.assoc, ← Functor.map_comp]
  simp only [Iso.inv_hom_id_app]
  exact (congrArg
    (fun z => (Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g)).unit.app M ≫ z)
    ((Scheme.Modules.pushforward (f ≫ g)).map_id
      ((Scheme.Modules.pullback (f ≫ g)).obj M))).trans (Category.comp_id _)

/-- The open restriction/pullback isomorphism preserves the genuine unit. -/
theorem restrict_pullbackUnit (f : X ⟶ Y) [IsOpenImmersion f] (M : Y.Modules) :
    (Scheme.Modules.restrictAdjunction f).unit.app M ≫
      (Scheme.Modules.pushforward f).map
        ((Scheme.Modules.restrictFunctorIsoPullback f).hom.app M) =
    (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M :=
  Adjunction.unit_leftAdjointUniq_hom_app _ _ _

/-- Equality of scheme maps carries the original pullback unit to itself. -/
theorem pullbackUnit_congr {f g : X ⟶ Y} (h : f = g) (M : Y.Modules) :
    (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M ≫
      (Scheme.Modules.pushforward f).map
        ((Scheme.Modules.pullbackCongr h).hom.app M) ≫
      (Scheme.Modules.pushforwardCongr h).hom.app
        ((Scheme.Modules.pullback g).obj M) =
    (Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M := by
  subst g
  apply Scheme.Modules.hom_ext
  intro U
  simp [Scheme.Modules.pullbackCongr]
  exact Category.comp_id _

section Conjugate
variable {C D : Type*} [Category* C] [Category* D]
  {L₁ L₂ L₃ : C ⥤ D} {R₁ R₂ R₃ : D ⥤ C}

private theorem conjugate_trans_inv (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (a₃ : L₃ ⊣ R₃)
    (e : L₁ ≅ L₂) (f : L₂ ≅ L₃) :
    conjugateEquiv a₁ a₃ (e ≪≫ f).inv =
      conjugateEquiv a₁ a₂ e.inv ≫ conjugateEquiv a₂ a₃ f.inv :=
  (conjugateEquiv_comp a₁ a₂ a₃ e.inv f.inv).symm

private theorem conjugate_homEquiv (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂)
    (e : L₂ ⟶ L₁) (M : C) (N : D) (f : L₁.obj M ⟶ N) :
    a₂.homEquiv M N (e.app M ≫ f) =
      a₁.homEquiv M N f ≫ (conjugateEquiv a₁ a₂ e).app N := by
  calc
    _ = a₂.unit.app M ≫ R₂.map (e.app M) ≫ R₂.map f := by
      rw [Adjunction.homEquiv_unit, Functor.map_comp]
    _ = (a₁.unit.app M ≫ (conjugateEquiv a₁ a₂ e).app (L₁.obj M)) ≫ R₂.map f := by
      rw [unit_conjugateEquiv, Category.assoc]
    _ = a₁.unit.app M ≫ R₁.map f ≫ (conjugateEquiv a₁ a₂ e).app N := by
      rw [Category.assoc, ← (conjugateEquiv a₁ a₂ e).naturality f]
    _ = _ := by rw [Adjunction.homEquiv_unit, Category.assoc]

end Conjugate

private theorem restrict_conjugate_inv (f : X ⟶ Y) [IsOpenImmersion f] :
    conjugateEquiv (Scheme.Modules.restrictAdjunction f)
      (Scheme.Modules.pullbackPushforwardAdjunction f)
      (Scheme.Modules.restrictFunctorIsoPullback f).inv =
    𝟙 (Scheme.Modules.pushforward f) := by
  simp only [Scheme.Modules.restrictFunctorIsoPullback, Adjunction.leftAdjointUniq,
    Iso.symm_inv, conjugateIsoEquiv_symm_apply_hom, Iso.refl_hom, Equiv.apply_symm_apply]

private theorem restrict_conjugate_hom (f : X ⟶ Y) [IsOpenImmersion f] :
    conjugateEquiv (Scheme.Modules.pullbackPushforwardAdjunction f)
      (Scheme.Modules.restrictAdjunction f)
      (Scheme.Modules.restrictFunctorIsoPullback f).hom =
    𝟙 (Scheme.Modules.pushforward f) := by
  simp only [Scheme.Modules.restrictFunctorIsoPullback, Adjunction.leftAdjointUniq,
    Iso.symm_hom, conjugateIsoEquiv_symm_apply_inv, Iso.refl_inv, Equiv.apply_symm_apply]

private theorem pullbackComp_conjugate_hom (f : X ⟶ Y) (g : Y ⟶ Z) :
    conjugateEquiv (Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g))
      ((Scheme.Modules.pullbackPushforwardAdjunction g).comp
        (Scheme.Modules.pullbackPushforwardAdjunction f))
      (Scheme.Modules.pullbackComp f g).hom = (Scheme.Modules.pushforwardComp f g).inv := by
  have he : conjugateIsoEquiv
      ((Scheme.Modules.pullbackPushforwardAdjunction g).comp
        (Scheme.Modules.pullbackPushforwardAdjunction f))
      (Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g))
      (Scheme.Modules.pullbackComp f g).symm = Scheme.Modules.pushforwardComp f g :=
    Iso.ext (Scheme.Modules.conjugateEquiv_pullbackComp_inv f g)
  exact congrArg Iso.inv he

private theorem pullbackCongr_conjugate_inv {f g : X ⟶ Y} (h : f = g) :
    conjugateEquiv (Scheme.Modules.pullbackPushforwardAdjunction f)
      (Scheme.Modules.pullbackPushforwardAdjunction g)
      (Scheme.Modules.pullbackCongr h).inv = (Scheme.Modules.pushforwardCongr h).hom := by
  subst g
  change conjugateEquiv (Scheme.Modules.pullbackPushforwardAdjunction f)
    (Scheme.Modules.pullbackPushforwardAdjunction f) (𝟙 _) = _
  rw [conjugateEquiv_id]
  apply NatTrans.ext
  funext M
  apply Scheme.Modules.hom_ext
  intro U
  simp

section OpenSquare
variable {X' Y' : Scheme.{0}} (j : X ⟶ Y) (j' : X' ⟶ Y')
  (u : X' ⟶ X) (v : Y' ⟶ Y) [IsOpenImmersion u] [IsOpenImmersion v]
  (w : j' ≫ v = u ≫ j)

/-- The actual left-adjoint comparison before applying the kernel isomorphism. -/
def pullbackOpenComparison :
    Scheme.Modules.pullback j ⋙ Scheme.Modules.restrictFunctor u ≅
      Scheme.Modules.restrictFunctor v ⋙ Scheme.Modules.pullback j' :=
  Functor.isoWhiskerLeft (Scheme.Modules.pullback j)
      (Scheme.Modules.restrictFunctorIsoPullback u) ≪≫
    Scheme.Modules.pullbackComp u j ≪≫
    Scheme.Modules.pullbackCongr w.symm ≪≫
    (Scheme.Modules.pullbackComp j' v).symm ≪≫
    Functor.isoWhiskerRight (Scheme.Modules.restrictFunctorIsoPullback v).symm
      (Scheme.Modules.pullback j')

/-- The corresponding right-adjoint comparison is the original pushforward
composition and equality comparison of scheme morphisms. -/
def pushforwardOpenComparison :
    Scheme.Modules.pushforward u ⋙ Scheme.Modules.pushforward j ≅
      Scheme.Modules.pushforward j' ⋙ Scheme.Modules.pushforward v :=
  Scheme.Modules.pushforwardComp u j ≪≫
    Scheme.Modules.pushforwardCongr w.symm ≪≫ (Scheme.Modules.pushforwardComp j' v).symm

/-- The two original functorial comparisons are conjugate under the genuine
scheme-module adjunctions. -/
theorem pullbackOpenComparison_conjugate :
    conjugateEquiv
      ((Scheme.Modules.pullbackPushforwardAdjunction j).comp
        (Scheme.Modules.restrictAdjunction u))
      ((Scheme.Modules.restrictAdjunction v).comp
        (Scheme.Modules.pullbackPushforwardAdjunction j'))
      (pullbackOpenComparison j j' u v w).inv =
    (pushforwardOpenComparison j j' u v w).hom := by
  let a₀ := (Scheme.Modules.pullbackPushforwardAdjunction j).comp
    (Scheme.Modules.restrictAdjunction u)
  let a₁ := (Scheme.Modules.pullbackPushforwardAdjunction j).comp
    (Scheme.Modules.pullbackPushforwardAdjunction u)
  let a₂ := Scheme.Modules.pullbackPushforwardAdjunction (u ≫ j)
  let a₃ := Scheme.Modules.pullbackPushforwardAdjunction (j' ≫ v)
  let a₄ := (Scheme.Modules.pullbackPushforwardAdjunction v).comp
    (Scheme.Modules.pullbackPushforwardAdjunction j')
  let a₅ := (Scheme.Modules.restrictAdjunction v).comp
    (Scheme.Modules.pullbackPushforwardAdjunction j')
  change conjugateEquiv a₀ a₅ _ = _
  unfold pullbackOpenComparison
  rw [conjugate_trans_inv a₀ a₁ a₅,
    conjugate_trans_inv a₁ a₂ a₅,
    conjugate_trans_inv a₂ a₃ a₅,
    conjugate_trans_inv a₃ a₄ a₅]
  change conjugateEquiv a₀ a₁
      (Functor.whiskerLeft (Scheme.Modules.pullback j)
        (Scheme.Modules.restrictFunctorIsoPullback u).inv) ≫
    conjugateEquiv a₁ a₂ (Scheme.Modules.pullbackComp u j).inv ≫
    conjugateEquiv a₂ a₃ (Scheme.Modules.pullbackCongr w.symm).inv ≫
    conjugateEquiv a₃ a₄ (Scheme.Modules.pullbackComp j' v).hom ≫
    conjugateEquiv a₄ a₅
      (Functor.whiskerRight (Scheme.Modules.restrictFunctorIsoPullback v).hom
        (Scheme.Modules.pullback j')) = _
  rw [conjugateEquiv_whiskerLeft, conjugateEquiv_whiskerRight,
    restrict_conjugate_inv, restrict_conjugate_hom,
    Scheme.Modules.conjugateEquiv_pullbackComp_inv,
    pullbackCongr_conjugate_inv, pullbackComp_conjugate_hom]
  rfl

/-- The normal-section adjunction is compatible with the same actual
open pullback comparison, with its exact underlying Hom map. -/
theorem pullbackOpenComparison_homEquiv (M : Y.Modules) (N : X'.Modules)
    (f : (Scheme.Modules.pullback j ⋙ Scheme.Modules.restrictFunctor u).obj M ⟶ N) :
    ((Scheme.Modules.restrictAdjunction v).comp
        (Scheme.Modules.pullbackPushforwardAdjunction j')).homEquiv M N
      ((pullbackOpenComparison j j' u v w).inv.app M ≫ f) =
    ((Scheme.Modules.pullbackPushforwardAdjunction j).comp
        (Scheme.Modules.restrictAdjunction u)).homEquiv M N f ≫
      (pushforwardOpenComparison j j' u v w).hom.app N := by
  have h := conjugate_homEquiv
    ((Scheme.Modules.pullbackPushforwardAdjunction j).comp
      (Scheme.Modules.restrictAdjunction u))
    ((Scheme.Modules.restrictAdjunction v).comp
      (Scheme.Modules.pullbackPushforwardAdjunction j'))
    (pullbackOpenComparison j j' u v w).inv M N f
  rw [pullbackOpenComparison_conjugate] at h
  exact h

end OpenSquare

section IntrinsicKernel
variable {X' Y' : Scheme.{0}} (j : X ⟶ Y) (j' : X' ⟶ Y')
  (u : X' ⟶ X) (v : Y' ⟶ Y) [IsOpenImmersion u] [IsOpenImmersion v]
  (h : IsPullback j' u v j)

/-- The intrinsic conormal restriction is the original functorial comparison,
followed by the genuine restricted ideal-kernel isomorphism. -/
theorem sourceConormalRestrictionIso_eq :
    sourceConormalRestrictionIso j j' u v h =
      (pullbackOpenComparison j j' u v h.w).app (idealModule j) ≪≫
        (Scheme.Modules.pullback j').mapIso (kernelIdealOpenBaseChangeIso j v u j' h) := rfl

/-- The exact conormal restriction isomorphism commutes with the original
normal-section adjunction after the canonical kernel identification. -/
theorem sourceConormalRestriction_adjunction (N : X'.Modules)
    (f : (sourceConormal j).restrict u ⟶ N) :
    (Scheme.Modules.restrictAdjunction v).homEquiv (idealModule j)
        ((Scheme.Modules.pushforward j').obj N)
      ((kernelIdealOpenBaseChangeIso j v u j' h).hom ≫
        (Scheme.Modules.pullbackPushforwardAdjunction j').homEquiv (idealModule j') N
          ((sourceConormalRestrictionIso j j' u v h).inv ≫ f)) =
    ((Scheme.Modules.pullbackPushforwardAdjunction j).comp
        (Scheme.Modules.restrictAdjunction u)).homEquiv (idealModule j) N f ≫
      (pushforwardOpenComparison j j' u v h.w).hom.app N := by
  let E := pullbackOpenComparison j j' u v h.w
  let K : (idealModule j).restrict v ≅ idealModule j' :=
    kernelIdealOpenBaseChangeIso j v u j' h
  have hl : K.hom ≫
      (Scheme.Modules.pullbackPushforwardAdjunction j').homEquiv (idealModule j') N
        ((sourceConormalRestrictionIso j j' u v h).inv ≫ f) =
      (Scheme.Modules.pullbackPushforwardAdjunction j').homEquiv
        ((Scheme.Modules.restrictFunctor v).obj (idealModule j)) N
        (E.inv.app (idealModule j) ≫ f) := by
    change K.hom ≫
      (Scheme.Modules.pullbackPushforwardAdjunction j').homEquiv (idealModule j') N
        ((Scheme.Modules.pullback j').map K.inv ≫ (E.inv.app (idealModule j) ≫ f)) = _
    rw [Adjunction.homEquiv_naturality_left, ← Category.assoc,
      Iso.hom_inv_id, Category.id_comp]
  change (Scheme.Modules.restrictAdjunction v).homEquiv (idealModule j)
    ((Scheme.Modules.pushforward j').obj N) (K.hom ≫ _) = _
  rw [hl]
  simpa only [Adjunction.comp_homEquiv, Equiv.trans_apply] using
    (pullbackOpenComparison_homEquiv j j' u v h.w (idealModule j) N f)

/-- At the top of an open chart, the source restriction isomorphism is
exactly the local Hom restriction with the original conormal comparison. -/
theorem sourceNormalRestriction_hom_top
    (x : Γ(sourceNormal j,u.opensRange)) :
    sourceNormalGlobalHomEquiv j'
      ((sourceNormalRestrictionIso j j' u v h).hom.app ⊤
        ((sourceNormal j).presheaf.map
          (homOfLE (u.image_le_opensRange ⊤)).op x)) =
    (sourceConormalRestrictionIso j j' u v h).inv ≫
      localLinearHomOpenImmersionEquiv u (sourceConormal j) (structureModule X) x ≫
      (Scheme.Modules.restrictUnitIso u).hom := by
  apply Scheme.Modules.hom_ext
  intro U
  apply ConcreteCategory.hom_ext
  intro m
  let E : (sourceConormal j).restrict u ≅ sourceConormal j' :=
    sourceConormalRestrictionIso j j' u v h
  let L : (structureModule X).restrict u ≅ structureModule X' :=
    Scheme.Modules.restrictUnitIso u
  let a := E.inv.val.app (op U) m
  exact congrArg (L.hom.val.app (op U))
    (localLinearHomOpenImmersionEquiv_app u (sourceConormal j) (structureModule X) x U a).symm

/-- The actual source-normal section map and its canonical global normal
adjunction satisfy the original Cartesian open square at the level of Hom.
Every coefficient and functor in this equality is the genuine scheme one. -/
theorem sourceNormalRestriction_globalAdjunction
    (x : Γ(sourceNormal j,u.opensRange)) :
    (Scheme.Modules.restrictAdjunction v).homEquiv (idealModule j)
        ((Scheme.Modules.pushforward j').obj (structureModule X'))
      ((kernelIdealOpenBaseChangeIso j v u j' h).hom ≫
        localLinearHomTopEquiv Y'.sheaf (idealModule j') (imageModule j')
          (normalGlobalComparison j'
            ((sourceNormalRestrictionIso j j' u v h).hom.app ⊤
              ((sourceNormal j).presheaf.map
                (homOfLE (u.image_le_opensRange ⊤)).op x)))) =
    ((Scheme.Modules.pullbackPushforwardAdjunction j).comp
        (Scheme.Modules.restrictAdjunction u)).homEquiv
      (idealModule j) (structureModule X')
      (localLinearHomOpenImmersionEquiv u (sourceConormal j) (structureModule X) x ≫
        (Scheme.Modules.restrictUnitIso u).hom) ≫
      (pushforwardOpenComparison j j' u v h.w).hom.app (structureModule X') := by
  let K : (idealModule j).restrict v ≅ idealModule j' :=
    kernelIdealOpenBaseChangeIso j v u j' h
  let y : Γ(sourceNormal j',⊤) :=
    (sourceNormalRestrictionIso j j' u v h).hom.app ⊤
      ((sourceNormal j).presheaf.map (homOfLE (u.image_le_opensRange ⊤)).op x)
  let g : (sourceConormal j).restrict u ⟶ structureModule X' :=
    localLinearHomOpenImmersionEquiv u (sourceConormal j) (structureModule X) x ≫
      (Scheme.Modules.restrictUnitIso u).hom
  have hs : sourceNormalGlobalHomEquiv j' y =
      (sourceConormalRestrictionIso j j' u v h).inv ≫ g :=
    sourceNormalRestriction_hom_top j j' u v h x
  have he : localLinearHomTopEquiv Y'.sheaf (idealModule j') (imageModule j')
      (normalGlobalComparison j' y) =
      (Scheme.Modules.pullbackPushforwardAdjunction j').homEquiv
        (idealModule j') (structureModule X')
        ((sourceConormalRestrictionIso j j' u v h).inv ≫ g) :=
    (normalGlobalComparison_hom j' y).trans
      (congrArg
        (fun k : sourceConormal j' ⟶ structureModule X' =>
          (Scheme.Modules.pullbackPushforwardAdjunction j').homEquiv
            (idealModule j') (structureModule X') k) hs)
  exact (congrArg
      (fun b : idealModule j' ⟶ imageModule j' =>
        (Scheme.Modules.restrictAdjunction v).homEquiv (idealModule j)
          ((Scheme.Modules.pushforward j').obj (structureModule X')) (K.hom ≫ b)) he).trans
    (sourceConormalRestriction_adjunction j j' u v h (structureModule X') g)

end IntrinsicKernel

#print axioms pullbackUnit_comp
#print axioms restrict_pullbackUnit
#print axioms pullbackUnit_congr
#print axioms pullbackOpenComparison_conjugate
#print axioms pullbackOpenComparison_homEquiv
#print axioms sourceConormalRestrictionIso_eq
#print axioms sourceConormalRestriction_adjunction
#print axioms sourceNormalRestriction_hom_top
#print axioms sourceNormalRestriction_globalAdjunction

end CycleQ2NormalRestrictionNaturality
end

end


section

/-! Exact equation evaluation for the actual normal restriction isomorphism
on every open of a Cartesian chart. -/
set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace CycleQ2NormalSectionEvaluation
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
  CycleQ2GeometricIntrinsicNormal CycleQ2SourceNormalSheaf
  CycleQ2SourceNormalRestriction

variable {X X' Y Y' : Scheme.{0}} (j : X ⟶ Y) (j' : X' ⟶ Y')
  (u : X' ⟶ X) (v : Y' ⟶ Y) [IsOpenImmersion u] [IsOpenImmersion v]
  (h : IsPullback j' u v j)

/-- On every actual subopen the normal restriction evaluates the same
original equation through the original ring base-change isomorphism. -/
theorem normalDirectImageRestrictionIso_evaluate (U : Y'.Opens)
    (f : (normalDirectImageSheaf j).val.obj (op (v ''ᵁ U)))
    (a : RingHom.ker (j'.app U).hom) :
    (normalSectionEvaluate j' U
      ((normalDirectImageRestrictionIso j j' u v h).hom.app U f)).toFun a =
    (baseChangeStructureSectionIso j v u j' h U).hom
      ((normalSectionEvaluate j (v ''ᵁ U) f).toFun
        (normalOpenIdealPullback j v u j' h U a)) := by
  let K : (idealModule j).restrict v ≅ idealModule j' :=
    kernelIdealOpenBaseChangeIso j v u j' h
  let m := K.inv.val.app (op U) ((kernelIdealSectionEquiv j' U).toEquiv.symm a)
  let e := baseChangeStructureSectionIso j v u j' h U
  change e.hom (f.val.app (op (Over.mk (𝟙 (v ''ᵁ U)))) m) =
    e.hom (f.val.app (op (Over.mk (𝟙 (v ''ᵁ U))))
      ((kernelIdealSectionEquiv j (v ''ᵁ U)).toEquiv.symm ((kernelIdealSectionEquiv j (v ''ᵁ U)).toEquiv m)))
  exact congrArg (fun z => e.hom (f.val.app (op (Over.mk (𝟙 (v ''ᵁ U)))) z))
    ((kernelIdealSectionEquiv j (v ''ᵁ U)).toEquiv.symm_apply_apply m).symm

#print axioms normalDirectImageRestrictionIso_evaluate

end CycleQ2NormalSectionEvaluation
end

end


section

/-! Actual section formulas for canonical normal restriction. This continues
the frozen Hom-level adjunction square without changing its proof bodies. -/
set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace CycleQ2NormalSectionRestriction
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
  CycleQ2GeometricIntrinsicNormal CycleQ2SourceNormalSheaf
  CycleQ2SourceNormalRestriction CycleQ2NormalPushforward
  CycleQ2NormalRestrictionNaturality

variable {X Y : Scheme.{0}}

/-- The open-restriction adjunct evaluates through the actual presheaf restriction. -/
theorem restrictAdjunction_homEquiv_app (u : X ⟶ Y) [IsOpenImmersion u]
    (M : Y.Modules) (N : X.Modules) (f : M.restrict u ⟶ N)
    (U : Y.Opens) (m : Γ(M,U)) :
    ((Scheme.Modules.restrictAdjunction u).homEquiv M N f).app U m =
      f.app (u ⁻¹ᵁ U) (M.presheaf.map (homOfLE (u.image_preimage_le U)).op m) := by
  rw [Adjunction.homEquiv_unit]
  rfl

/-- The inverse adjunct uses the actual preimage-image counit restriction. -/
theorem restrictAdjunction_homEquiv_symm_app (u : X ⟶ Y) [IsOpenImmersion u]
    (M : Y.Modules) (N : X.Modules) (f : M ⟶ (Scheme.Modules.pushforward u).obj N)
    (U : X.Opens) (m : Γ(M,u ''ᵁ U)) :
    (((Scheme.Modules.restrictAdjunction u).homEquiv M N).symm f).app U m =
      N.presheaf.map (eqToHom (u.preimage_image_eq U).symm).op (f.app (u ''ᵁ U) m) := by
  rw [Adjunction.homEquiv_counit]
  rfl

/-- The section-ring comparison of an image equality is the literal open
immersion map, so no scalar transport is chosen. -/
theorem appIso_imageEq (u : X ⟶ Y) [IsOpenImmersion u]
    (U : X.Opens) (V : Y.Opens) (h : u ''ᵁ U = V) :
    Y.presheaf.map (eqToHom h).op ≫ (u.appIso U).hom =
      u.appLE V U (by rw [← h, u.preimage_image_eq]) := by
  subst V
  simp only [eqToHom_refl, op_id]
  exact (congrArg (fun z => z ≫ (u.appIso U).hom)
    (Y.presheaf.map_id (op (u ''ᵁ U)))).trans
      ((Category.id_comp _).trans (u.appIso_hom' U))

variable {X' Y' : Scheme.{0}} (j : X ⟶ Y) (j' : X' ⟶ Y')
  (u : X' ⟶ X) (v : Y' ⟶ Y) [IsOpenImmersion u] [IsOpenImmersion v]
  (h : IsPullback j' u v j)

include h in
/-- The source image is the actual inverse image of the surface image. -/
theorem sourceRange_eq : u.opensRange = j ⁻¹ᵁ v.opensRange := by
  simpa only [Scheme.Hom.preimage_top, Scheme.Hom.image_top_eq_opensRange] using
    IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback h ⊤

/-- The actual section isomorphism used to evaluate the pushforward on its
precise inverse-image open. -/
def sourceRangeSectionsIso :
    Γ(sourceNormal j,u.opensRange) ≅ Γ(sourceNormal j,j ⁻¹ᵁ v.opensRange) :=
  (sourceNormal j).presheaf.mapIso (eqToIso (sourceRange_eq j j' u v h).symm).op

/-- The source normal section on the actual affine chart, using the frozen
module-sheaf restriction isomorphism. -/
def sourceChartNormalSection (x : Γ(sourceNormal j,u.opensRange)) : Γ(sourceNormal j',⊤) :=
  (sourceNormalRestrictionIso j j' u v h).hom.app ⊤
    ((sourceNormal j).presheaf.map (homOfLE (u.image_le_opensRange ⊤)).op x)

include h in
omit [IsOpenImmersion u] [IsOpenImmersion v] in
/-- Equality of the literal inverse-image opens in the Cartesian square. -/
theorem preimage_comp_eq (U : Y.Opens) :
    j' ⁻¹ᵁ (v ⁻¹ᵁ U) = u ⁻¹ᵁ (j ⁻¹ᵁ U) := by
  change (j' ≫ v) ⁻¹ᵁ U = (u ≫ j) ⁻¹ᵁ U
  rw [h.w]

include h in
/-- The two source restriction domains are the same actual open. -/
theorem sectionDomain_eq (U : Y.Opens) :
    j ⁻¹ᵁ (v ''ᵁ (v ⁻¹ᵁ U)) = u ''ᵁ (u ⁻¹ᵁ (j ⁻¹ᵁ U)) :=
  (IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback h (v ⁻¹ᵁ U)).symm.trans
    (congrArg (fun W => u ''ᵁ W) (preimage_comp_eq j j' u v h U))

/-- The original ring base-change isomorphism is compatible with the two
literal source restrictions. -/
theorem baseChange_ring_formula (U : Y.Opens) :
    X.presheaf.map (eqToHom (sectionDomain_eq j j' u v h U)).op ≫
        (baseChangeStructureSectionIso j v u j' h (v ⁻¹ᵁ U)).hom =
      (u.appIso (u ⁻¹ᵁ (j ⁻¹ᵁ U))).hom ≫
        X'.presheaf.map (eqToHom (preimage_comp_eq j j' u v h U)).op := by
  let A : X.Opens := u ''ᵁ (u ⁻¹ᵁ (j ⁻¹ᵁ U))
  let B : X.Opens := j ⁻¹ᵁ (v ''ᵁ (v ⁻¹ᵁ U))
  let W : X'.Opens := j' ⁻¹ᵁ (v ⁻¹ᵁ U)
  let W' : X'.Opens := u ⁻¹ᵁ (j ⁻¹ᵁ U)
  have hb : W ≤ u ⁻¹ᵁ B :=
    (IsOpenImmersion.app_eq_invApp_app_of_comp_eq_aux j' v (u ≫ j) h.w.symm
      (v ⁻¹ᵁ U)).le
  have ha : W' ≤ u ⁻¹ᵁ A := (u.preimage_image_eq W').ge
  change X.presheaf.map (eqToHom (sectionDomain_eq j j' u v h U)).op ≫
      u.appLE B W hb = (u.appIso W').hom ≫
        X'.presheaf.map (eqToHom (preimage_comp_eq j j' u v h U)).op
  exact (u.map_appLE hb (eqToHom (sectionDomain_eq j j' u v h U)).op).trans
    ((u.appLE_map ha (eqToHom (preimage_comp_eq j j' u v h U)).op).symm.trans
      (congrArg (fun z => z ≫ X'.presheaf.map
        (eqToHom (preimage_comp_eq j j' u v h U)).op) (u.appIso_hom' W').symm))

omit [IsOpenImmersion u] [IsOpenImmersion v] in
/-- The pushforward comparison is exactly the original restriction along
the equality of inverse-image opens. -/
theorem pushforwardOpenComparison_app (N : X'.Modules) (U : Y.Opens) :
    ((pushforwardOpenComparison j j' u v h.w).hom.app N).app U =
      N.presheaf.map (eqToHom (preimage_comp_eq j j' u v h U)).op := by
  rfl

private def conormalUnit : idealModule j ⟶
    (Scheme.Modules.pushforward j).obj (sourceConormal j) :=
  (Scheme.Modules.pullbackPushforwardAdjunction j).unit.app (idealModule j)

private def upperArgument (U : Y.Opens) (a : Γ(idealModule j,U)) :
    Γ(sourceConormal j,u ''ᵁ (u ⁻¹ᵁ (j ⁻¹ᵁ U))) :=
  (sourceConormal j).presheaf.map (homOfLE (u.image_preimage_le (j ⁻¹ᵁ U))).op
    ((conormalUnit j).app U a)

private def lowerArgument (U : Y.Opens) (a : Γ(idealModule j,U)) :
    Γ(sourceConormal j,j ⁻¹ᵁ (v ''ᵁ (v ⁻¹ᵁ U))) :=
  (conormalUnit j).app (v ''ᵁ (v ⁻¹ᵁ U))
    ((idealModule j).presheaf.map (homOfLE (v.image_preimage_le U)).op a)

/-- Naturality of the original conormal adjunction unit identifies the two
actual equation arguments before applying a local normal functional. -/
theorem argument_restriction (U : Y.Opens) (a : Γ(idealModule j,U)) :
    (sourceConormal j).presheaf.map (eqToHom (sectionDomain_eq j j' u v h U)).op
      (upperArgument j u U a) = lowerArgument j v U a := by
  let η : idealModule j ⟶ (Scheme.Modules.pushforward j).obj (sourceConormal j) :=
    conormalUnit j
  let D : Y.Opens := v ''ᵁ (v ⁻¹ᵁ U)
  let aD : D ⟶ U := homOfLE (v.image_preimage_le U)
  have hn := ConcreteCategory.congr_hom (η.mapPresheaf.naturality aD.op) a
  have hm :
      (sourceConormal j).presheaf.map (homOfLE (u.image_preimage_le (j ⁻¹ᵁ U))).op ≫
        (sourceConormal j).presheaf.map (eqToHom (sectionDomain_eq j j' u v h U)).op =
      (sourceConormal j).presheaf.map ((Opens.map j.base).map aD).op := by
    rw [← Functor.map_comp]
    rfl
  exact (ConcreteCategory.congr_hom hm (η.app U a)).trans hn.symm

private def rangeValue (x : Γ(sourceNormal j,u.opensRange)) (U : X.Opens)
    (hU : U ≤ u.opensRange) (m : Γ(sourceConormal j,U)) : Γ(X,U) :=
  x.val.app (op (Over.mk (homOfLE hU))) m

/-- A local normal functional commutes with the literal equality of the
source domains, including the original unit argument. -/
theorem localValue_restriction (x : Γ(sourceNormal j,u.opensRange))
    (U : Y.Opens) (a : Γ(idealModule j,U)) :
    rangeValue j u x (j ⁻¹ᵁ (v ''ᵁ (v ⁻¹ᵁ U)))
      ((sectionDomain_eq j j' u v h U).le.trans
        (u.image_le_opensRange (u ⁻¹ᵁ (j ⁻¹ᵁ U))))
      (lowerArgument j v U a) =
    X.presheaf.map (eqToHom (sectionDomain_eq j j' u v h U)).op
      (rangeValue j u x (u ''ᵁ (u ⁻¹ᵁ (j ⁻¹ᵁ U)))
        (u.image_le_opensRange _) (upperArgument j u U a)) := by
  let A : Over u.opensRange :=
    Over.mk (homOfLE (u.image_le_opensRange (u ⁻¹ᵁ (j ⁻¹ᵁ U))))
  let B : Over u.opensRange := Over.mk (homOfLE
    ((sectionDomain_eq j j' u v h U).le.trans
      (u.image_le_opensRange (u ⁻¹ᵁ (j ⁻¹ᵁ U)))))
  let e : B ⟶ A := Over.homMk (eqToHom (sectionDomain_eq j j' u v h U))
  have hx := ConcreteCategory.congr_hom (x.val.naturality e.op) (upperArgument j u U a)
  exact (congrArg (x.val.app (op B)) (argument_restriction j j' u v h U a).symm).trans hx

/-- The actual normal value transforms through the original ring base-change
isomorphism after applying the same local functional. -/
theorem cartesian_normal_value (x : Γ(sourceNormal j,u.opensRange))
    (U : Y.Opens) (a : Γ(idealModule j,U)) :
    (baseChangeStructureSectionIso j v u j' h (v ⁻¹ᵁ U)).hom
      (rangeValue j u x (j ⁻¹ᵁ (v ''ᵁ (v ⁻¹ᵁ U)))
        ((sectionDomain_eq j j' u v h U).le.trans
          (u.image_le_opensRange (u ⁻¹ᵁ (j ⁻¹ᵁ U))))
        (lowerArgument j v U a)) =
    X'.presheaf.map (eqToHom (preimage_comp_eq j j' u v h U)).op
      ((u.appIso (u ⁻¹ᵁ (j ⁻¹ᵁ U))).hom
        (rangeValue j u x (u ''ᵁ (u ⁻¹ᵁ (j ⁻¹ᵁ U)))
          (u.image_le_opensRange _) (upperArgument j u U a))) :=
  (congrArg (baseChangeStructureSectionIso j v u j' h (v ⁻¹ᵁ U)).hom
      (localValue_restriction j j' u v h x U a)).trans
    (ConcreteCategory.congr_hom (baseChange_ring_formula j j' u v h U)
      (rangeValue j u x (u ''ᵁ (u ⁻¹ᵁ (j ⁻¹ᵁ U)))
        (u.image_le_opensRange _) (upperArgument j u U a)))

private def restrictedNormalMorphism (x : Γ(sourceNormal j,u.opensRange)) :
    (sourceConormal j).restrict u ⟶ structureModule X' :=
  localLinearHomOpenImmersionEquiv u (sourceConormal j) (structureModule X) x ≫
    (Scheme.Modules.restrictUnitIso u).hom

private def sourceAdjunctionMap (x : Γ(sourceNormal j,u.opensRange)) :
    idealModule j ⟶ (Scheme.Modules.pushforward v).obj (imageModule j') :=
  ((Scheme.Modules.pullbackPushforwardAdjunction j).comp
      (Scheme.Modules.restrictAdjunction u)).homEquiv
    (idealModule j) (structureModule X') (restrictedNormalMorphism j u x) ≫
      (pushforwardOpenComparison j j' u v h.w).hom.app (structureModule X')

private def chartAdjunctionMap (x : Γ(sourceNormal j,u.opensRange)) :
    idealModule j ⟶ (Scheme.Modules.pushforward v).obj (imageModule j') :=
  (Scheme.Modules.restrictAdjunction v).homEquiv (idealModule j) (imageModule j')
    (localLinearHomOpenImmersionEquiv v (idealModule j) (imageModule j)
      ((normalPushforward j).app v.opensRange ((sourceRangeSectionsIso j j' u v h).hom x)) ≫
      (imageStructureOpenBaseChangeIso j v u j' h).hom)

omit [IsOpenImmersion v] in
private theorem sourceAdjunctionMap_app (x : Γ(sourceNormal j,u.opensRange))
    (U : Y.Opens) (a : Γ(idealModule j,U)) :
    (sourceAdjunctionMap j j' u v h x).app U a =
    X'.presheaf.map (eqToHom (preimage_comp_eq j j' u v h U)).op
      ((u.appIso (u ⁻¹ᵁ (j ⁻¹ᵁ U))).hom
        (rangeValue j u x (u ''ᵁ (u ⁻¹ᵁ (j ⁻¹ᵁ U)))
          (u.image_le_opensRange _) (upperArgument j u U a))) := by
  unfold sourceAdjunctionMap
  rw [Adjunction.comp_homEquiv]
  change ((pushforwardOpenComparison j j' u v h.w).hom.app (structureModule X')).app U
    (((Scheme.Modules.pullbackPushforwardAdjunction j).homEquiv
      (idealModule j) ((Scheme.Modules.pushforward u).obj (structureModule X'))
      ((Scheme.Modules.restrictAdjunction u).homEquiv
        (sourceConormal j) (structureModule X') (restrictedNormalMorphism j u x))).app U a) = _
  rw [Adjunction.homEquiv_unit]
  change ((pushforwardOpenComparison j j' u v h.w).hom.app (structureModule X')).app U
    (((Scheme.Modules.restrictAdjunction u).homEquiv
      (sourceConormal j) (structureModule X') (restrictedNormalMorphism j u x)).app
      (j ⁻¹ᵁ U) ((conormalUnit j).app U a)) = _
  let W : X'.Opens := u ⁻¹ᵁ (j ⁻¹ᵁ U)
  let m : Γ(sourceConormal j,j ⁻¹ᵁ U) := (conormalUnit j).app U a
  let P := ((pushforwardOpenComparison j j' u v h.w).hom.app
    (structureModule X')).app U
  have hres := restrictAdjunction_homEquiv_app u (sourceConormal j)
    (structureModule X') (restrictedNormalMorphism j u x) (j ⁻¹ᵁ U) m
  have hlocal : (restrictedNormalMorphism j u x).app W (upperArgument j u U a) =
      (u.appIso W).hom (rangeValue j u x (u ''ᵁ W)
        (u.image_le_opensRange W) (upperArgument j u U a)) :=
    congrArg (u.appIso W).hom
      (localLinearHomOpenImmersionEquiv_app u (sourceConormal j)
        (structureModule X) x W (upperArgument j u U a))
  exact (congrArg P hres).trans ((congrArg P hlocal).trans
    (ConcreteCategory.congr_hom
      (pushforwardOpenComparison_app j j' u v h (structureModule X') U)
      ((u.appIso W).hom (rangeValue j u x (u ''ᵁ W)
        (u.image_le_opensRange W) (upperArgument j u U a)))))

private theorem chartAdjunctionMap_app (x : Γ(sourceNormal j,u.opensRange))
    (U : Y.Opens) (a : Γ(idealModule j,U)) :
    (chartAdjunctionMap j j' u v h x).app U a =
    (baseChangeStructureSectionIso j v u j' h (v ⁻¹ᵁ U)).hom
      (rangeValue j u x (j ⁻¹ᵁ (v ''ᵁ (v ⁻¹ᵁ U)))
        ((sectionDomain_eq j j' u v h U).le.trans
          (u.image_le_opensRange (u ⁻¹ᵁ (j ⁻¹ᵁ U))))
        (lowerArgument j v U a)) := by
  let I : (imageModule j).restrict v ≅ imageModule j' :=
    imageStructureOpenBaseChangeIso j v u j' h
  change ((Scheme.Modules.restrictAdjunction v).homEquiv (idealModule j) (imageModule j')
    (localLinearHomOpenImmersionEquiv v (idealModule j) (imageModule j)
      ((normalPushforward j).app v.opensRange ((sourceRangeSectionsIso j j' u v h).hom x)) ≫
      I.hom)).app U a = _
  rw [restrictAdjunction_homEquiv_app]
  change I.hom.app (v ⁻¹ᵁ U)
    ((localLinearHomOpenImmersionEquiv v (idealModule j) (imageModule j)
      ((normalPushforward j).app v.opensRange ((sourceRangeSectionsIso j j' u v h).hom x))).val.app
        (op (v ⁻¹ᵁ U))
        ((idealModule j).presheaf.map (homOfLE (v.image_preimage_le U)).op a)) = _
  let y := (normalPushforward j).app v.opensRange
    ((sourceRangeSectionsIso j j' u v h).hom x)
  let a' : Γ(idealModule j,v ''ᵁ (v ⁻¹ᵁ U)) :=
    (idealModule j).presheaf.map (homOfLE (v.image_preimage_le U)).op a
  exact congrArg (I.hom.app (v ⁻¹ᵁ U))
    (localLinearHomOpenImmersionEquiv_app v (idealModule j)
      (imageModule j) y (v ⁻¹ᵁ U) a')

/-- The original source-normal functional and the incoming surface chart
comparison induce the same genuine global adjoint morphism. -/
theorem normalPushforward_restriction_adjunction (x : Γ(sourceNormal j,u.opensRange)) :
    chartAdjunctionMap j j' u v h x = sourceAdjunctionMap j j' u v h x := by
  apply Scheme.Modules.hom_ext
  intro U
  apply ConcreteCategory.hom_ext
  intro a
  exact (chartAdjunctionMap_app j j' u v h x U a).trans
    ((cartesian_normal_value j j' u v h x U a).trans
      (sourceAdjunctionMap_app j j' u v h x U a).symm)

/-- The source-normal restriction map is exactly the incoming chart normal
map under the canonical global normal adjunction. -/
theorem sourceChartNormalSection_globalComparison (x : Γ(sourceNormal j,u.opensRange)) :
    normalGlobalComparison j' (sourceChartNormalSection j j' u v h x) =
      normalSectionOpenBaseChangeEquiv j v u j' h
        ((normalPushforward j).app v.opensRange ((sourceRangeSectionsIso j j' u v h).hom x)) := by
  let K : (idealModule j).restrict v ≅ idealModule j' :=
    kernelIdealOpenBaseChangeIso j v u j' h
  let I : (imageModule j).restrict v ≅ imageModule j' :=
    imageStructureOpenBaseChangeIso j v u j' h
  let e : LocalLinearHom Y'.sheaf (idealModule j') (imageModule j') ⊤ ≃+
      (idealModule j' ⟶ imageModule j') :=
    localLinearHomTopAddEquiv Y' (idealModule j') (imageModule j')
  let y := (normalPushforward j).app v.opensRange ((sourceRangeSectionsIso j j' u v h).hom x)
  let F : (idealModule j).restrict v ⟶ (imageModule j).restrict v :=
    localLinearHomOpenImmersionEquiv v (idealModule j) (imageModule j) y
  have he : e (normalSectionOpenBaseChangeEquiv j v u j' h y) = K.inv ≫ F ≫ I.hom := by
    change e (e.symm (K.inv ≫ F ≫ I.hom)) = _
    exact e.apply_symm_apply _
  have hr : (Scheme.Modules.restrictAdjunction v).homEquiv
      (idealModule j) (imageModule j')
      (K.hom ≫ e (normalSectionOpenBaseChangeEquiv j v u j' h y)) =
      chartAdjunctionMap j j' u v h x := by
    have hc : K.hom ≫ (K.inv ≫ F ≫ I.hom) = F ≫ I.hom := by
      rw [← Category.assoc, K.hom_inv_id, Category.id_comp]
    exact congrArg ((Scheme.Modules.restrictAdjunction v).homEquiv
      (idealModule j) (imageModule j'))
      ((congrArg (fun b : idealModule j' ⟶ imageModule j' => K.hom ≫ b) he).trans hc)
  apply e.injective
  apply (cancel_epi K.hom).mp
  apply ((Scheme.Modules.restrictAdjunction v).homEquiv
    (idealModule j) (imageModule j')).injective
  exact (sourceNormalRestriction_globalAdjunction j j' u v h x).trans
    ((normalPushforward_restriction_adjunction j j' u v h x).symm.trans hr.symm)

#print axioms sourceRange_eq
#print axioms sourceRangeSectionsIso
#print axioms sourceChartNormalSection
#print axioms argument_restriction
#print axioms localValue_restriction
#print axioms cartesian_normal_value
#print axioms normalPushforward_restriction_adjunction
#print axioms sourceChartNormalSection_globalComparison

end CycleQ2NormalSectionRestriction
end

end


section

/-!
# Source-normal sections in the original affine coordinate rings

The incoming intrinsic-normal comparison already identifies the actual
direct-image normal sheaf with the dual of the original affine conormal.
Here the genuine pullback/pushforward adjunction supplies the source-side
comparison. For an actual quotient map, lifting coefficients proves its
semilinearity over the original source ring. The final specialization uses
the proved surjectivity of the literal normal-chart map and fixes both
defining-equation values of the actual normal section.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2SourceNormalRaw

open CategoryTheory AlgebraicGeometry Opposite
open CycleQ2GeometricIntrinsicNormal CycleQ2SourceNormalSheaf
open scoped TensorProduct

local instance schemeSectionModule (Z : Scheme.{0}) (M : Z.Modules) (U : Z.Opens) :
    Module Γ(Z, U) Γ(M, U) := (M.val.obj (op U)).isModule

local instance normalSectionModule {X Y : Scheme.{0}} (j : X ⟶ Y) (U : Y.Opens) :
    Module Γ(Y, U) ((normalDirectImageSheaf j).val.obj (op U)) :=
  ((normalDirectImageSheaf j).val.obj (op U)).isModule

local instance imageSectionModule {X Y : Scheme.{0}} (j : X ⟶ Y) (U : Y.Opens) :
    Module Γ(Y, U) ((imageStructureModule j).val.obj (op U)) :=
  ((imageStructureModule j).val.obj (op U)).isModule

/-- The source-normal comparison carries ambient coefficients through
the original morphism of structure sheaves. -/
theorem normalGlobalComparison_smul {X Y : Scheme.{0}} (j : X ⟶ Y)
    (a : Γ(Y, ⊤)) (f : Γ(sourceNormal j, ⊤)) :
    normalGlobalComparison j (j.appTop a • f) =
      a • normalGlobalComparison j f := by
  have he := CycleQ2NormalPushforward.localForward_smul j
    (idealModule j) (structureModule X) ⊤ a f
  change (CycleQ2NormalPushforward.normalPushforward j).app ⊤ (j.appTop a • f) =
    a • (CycleQ2NormalPushforward.normalPushforward j).app ⊤ f at he
  simpa only [CycleQ2NormalPushforward.normalPushforward_app_top] using he

variable {A B : CommRingCat.{0}} (φ : A ⟶ B)

/-- The canonical source-normal comparison with the original affine
conormal dual. It is defined by the actual module-sheaf adjunction. -/
def sourceNormalRawAddEquiv :
    letI : Algebra A B := φ.hom.toAlgebra
    Γ(sourceNormal (Spec.map φ), ⊤) ≃+
      (B ⊗[A] (RingHom.ker φ.hom).Cotangent →ₗ[B] B) := by
  letI : Algebra A B := φ.hom.toAlgebra
  exact (normalGlobalComparison (Spec.map φ)).trans
    (affineNormalAlgebraConormalEquiv φ).toAddEquiv

/-- Its value on each original ideal element is the actual intrinsic
normal functional, read through the canonical Spec section isomorphism. -/
theorem sourceNormalRaw_tmul
    (f : Γ(sourceNormal (Spec.map φ), ⊤)) (b : B) (a : RingHom.ker φ.hom) :
    letI : Algebra A B := φ.hom.toAlgebra
    sourceNormalRawAddEquiv φ f
      (b ⊗ₜ[A] (RingHom.ker φ.hom).toCotangent a) =
      b * specTopRingEquiv B
        (normalSectionEvaluate (Spec.map φ) ⊤ (normalGlobalComparison (Spec.map φ) f)
          ((affineKernelSectionSemilinearEquiv φ).symm a)) := by
  let : Algebra A B := φ.hom.toAlgebra
  exact affineNormalAlgebraConormalEquiv_tmul φ
    (normalGlobalComparison (Spec.map φ) f) b a

/-- Every source coefficient lifts through the actual affine quotient,
so the canonical comparison respects the full source scalar action. -/
theorem sourceNormalRaw_smul (hsurj : Function.Surjective φ.hom)
    (b : Γ(Spec B, ⊤)) (f : Γ(sourceNormal (Spec.map φ), ⊤)) :
    letI : Algebra A B := φ.hom.toAlgebra
    sourceNormalRawAddEquiv φ (b • f) =
      specTopRingEquiv B b • sourceNormalRawAddEquiv φ f := by
  let : Algebra A B := φ.hom.toAlgebra
  obtain ⟨a, ha⟩ := hsurj (specTopRingEquiv B b)
  have hb : (Spec.map φ).appTop ((specTopRingEquiv A).symm a) = b := by
    apply (specTopRingEquiv B).injective
    change specTopRingEquiv B ((Spec.map φ).app ⊤ ((specTopRingEquiv A).symm a)) = _
    rw [affineSectionMap_normalization, RingEquiv.apply_symm_apply]
    exact ha
  calc
    sourceNormalRawAddEquiv φ (b • f) =
        sourceNormalRawAddEquiv φ
          ((Spec.map φ).appTop ((specTopRingEquiv A).symm a) • f) :=
      congrArg (fun c => sourceNormalRawAddEquiv φ (c • f)) hb.symm
    _ = a • sourceNormalRawAddEquiv φ f := by
      change affineNormalAlgebraConormalEquiv φ
        (normalGlobalComparison (Spec.map φ)
          ((Spec.map φ).appTop ((specTopRingEquiv A).symm a) • f)) = _
      rw [normalGlobalComparison_smul, map_smulₛₗ]
      exact congrArg (fun c : A => c • sourceNormalRawAddEquiv φ f)
        ((specTopRingEquiv A).apply_symm_apply a)
    _ = specTopRingEquiv B b • sourceNormalRawAddEquiv φ f := by
      rw [← IsScalarTower.algebraMap_smul B a _]
      exact congrArg (fun c : B => c • sourceNormalRawAddEquiv φ f) ha

/-- The actual intrinsic source normal has the original algebraic
conormal dual, with its genuine source-ring action. -/
def sourceNormalRawEquiv (hsurj : Function.Surjective φ.hom) :
    letI : Algebra A B := φ.hom.toAlgebra
    Γ(sourceNormal (Spec.map φ), ⊤) ≃ₛₗ[(specTopRingEquiv B).toRingHom]
      (B ⊗[A] (RingHom.ker φ.hom).Cotangent →ₗ[B] B) := by
  letI : Algebra A B := φ.hom.toAlgebra
  exact
    { __ := sourceNormalRawAddEquiv φ
      map_smul' := sourceNormalRaw_smul φ hsurj }

/-- The inverse comparison also preserves the original ideal values. -/
theorem sourceNormalRaw_symm_evaluate (a : RingHom.ker φ.hom) :
    letI : Algebra A B := φ.hom.toAlgebra
    ∀ g : B ⊗[A] (RingHom.ker φ.hom).Cotangent →ₗ[B] B,
      specTopRingEquiv B
        (normalSectionEvaluate (Spec.map φ) ⊤
          (normalGlobalComparison (Spec.map φ) ((sourceNormalRawAddEquiv φ).symm g))
          ((affineKernelSectionSemilinearEquiv φ).symm a)) =
      g ((1 : B) ⊗ₜ[A] (RingHom.ker φ.hom).toCotangent a) := by
  let : Algebra A B := φ.hom.toAlgebra
  intro g
  have h := sourceNormalRaw_tmul φ ((sourceNormalRawAddEquiv φ).symm g) 1 a
  rw [AddEquiv.apply_symm_apply, one_mul] at h
  exact h.symm

end CycleQ2SourceNormalRaw

namespace CycleQ2SourceNormalPatch

open CategoryTheory AlgebraicGeometry Opposite
open CycleQ2GeometricSurfaceAdjunction CycleQ2GeometricAffineCurveCharts
open CycleQ2GeometricIntrinsicNormal CycleQ2SourceNormalSheaf CycleQ2SourceNormalRaw
open scoped TensorProduct

attribute [local instance] CycleQ2SourceNormalRaw.schemeSectionModule
  CycleQ2SourceNormalRaw.normalSectionModule CycleQ2SourceNormalRaw.imageSectionModule

variable (q h : AffinePoly) (g₁ g₂ k : SurfacePoly) (i : Fin 2) (j : Fin 3)

abbrev patchRingMap := CommRingCat.ofHom (normalChartMap q h g₁ g₂ k i j).toRingHom
abbrev patchImmersion := Spec.map (patchRingMap q h g₁ g₂ k i j)

local instance patchCoefficientPair :
    RingHomInvPair
      (specTopRingEquiv (CommRingCat.of (NormalCurvePatch q h g₁ g₂ k i j))).toRingHom
      (specTopRingEquiv (CommRingCat.of (NormalCurvePatch q h g₁ g₂ k i j))).symm.toRingHom :=
  RingHomInvPair.of_ringEquiv
    (specTopRingEquiv (CommRingCat.of (NormalCurvePatch q h g₁ g₂ k i j)))

local instance patchCoefficientPairSymm :
    RingHomInvPair
      (specTopRingEquiv (CommRingCat.of (NormalCurvePatch q h g₁ g₂ k i j))).symm.toRingHom
      (specTopRingEquiv (CommRingCat.of (NormalCurvePatch q h g₁ g₂ k i j))).toRingHom :=
  RingHomInvPair.of_ringEquiv
    (specTopRingEquiv (CommRingCat.of (NormalCurvePatch q h g₁ g₂ k i j))).symm

/-- On every literal augmented-Jacobian patch, the source intrinsic
normal sections have the exact raw conormal dual used by adjunction. -/
def rawEquiv :
    Γ(sourceNormal (patchImmersion q h g₁ g₂ k i j), ⊤) ≃ₛₗ[
      (specTopRingEquiv (CommRingCat.of (NormalCurvePatch q h g₁ g₂ k i j))).toRingHom]
      (NormalConormal q h g₁ g₂ k i j →ₗ[NormalCurvePatch q h g₁ g₂ k i j]
        NormalCurvePatch q h g₁ g₂ k i j) :=
  sourceNormalRawEquiv (patchRingMap q h g₁ g₂ k i j)
    (normalChartAlgebra_surjective q h g₁ g₂ k i j)

/-- The actual ideal section obtained from either literal defining equation. -/
def equationSection (a : Fin 2) :
    RingHom.ker ((patchImmersion q h g₁ g₂ k i j).app ⊤).hom :=
  (affineKernelSectionSemilinearEquiv (patchRingMap q h g₁ g₂ k i j)).symm
    ⟨algebraMap SurfacePoly (NormalSurfacePatch q h g₁ g₂ k i j) (normalPolynomial q a),
      normalEquation_mem q h g₁ g₂ k i j a⟩

@[simp] theorem equationSection_coe (a : Fin 2) :
    (equationSection q h g₁ g₂ k i j a :
      Γ(Spec (CommRingCat.of (NormalSurfacePatch q h g₁ g₂ k i j)), ⊤)) =
      (Scheme.ΓSpecIso (CommRingCat.of (NormalSurfacePatch q h g₁ g₂ k i j))).inv
        (algebraMap SurfacePoly (NormalSurfacePatch q h g₁ g₂ k i j)
          (normalPolynomial q a)) := rfl

/-- Read the actual intrinsic normal's value on an original equation in
the original curve ring, using only the canonical section isomorphism. -/
def equationValue (f : Γ(sourceNormal (patchImmersion q h g₁ g₂ k i j), ⊤))
    (a : Fin 2) : NormalCurvePatch q h g₁ g₂ k i j :=
  specTopRingEquiv (CommRingCat.of (NormalCurvePatch q h g₁ g₂ k i j))
    (normalSectionEvaluate (patchImmersion q h g₁ g₂ k i j) ⊤
      (normalGlobalComparison (patchImmersion q h g₁ g₂ k i j) f)
      (equationSection q h g₁ g₂ k i j a))

@[simp] theorem rawEquiv_equation
    (f : Γ(sourceNormal (patchImmersion q h g₁ g₂ k i j), ⊤)) (a : Fin 2) :
    rawEquiv q h g₁ g₂ k i j f (normalEquationClass q h g₁ g₂ k i j a) =
      equationValue q h g₁ g₂ k i j f a := by
  have he := sourceNormalRaw_tmul
    (patchRingMap q h g₁ g₂ k i j) f 1
      ⟨algebraMap SurfacePoly (NormalSurfacePatch q h g₁ g₂ k i j) (normalPolynomial q a),
        normalEquation_mem q h g₁ g₂ k i j a⟩
  change rawEquiv q h g₁ g₂ k i j f (normalEquationClass q h g₁ g₂ k i j a) =
    1 * equationValue q h g₁ g₂ k i j f a at he
  exact he.trans (one_mul _)

/-- The fixed raw normal vector defines an actual intrinsic source-normal section. -/
def normalVectorSection : Γ(sourceNormal (patchImmersion q h g₁ g₂ k i j), ⊤) :=
  (rawEquiv q h g₁ g₂ k i j).symm (normalVector q h g₁ g₂ k i j)

@[simp] theorem rawEquiv_normalVectorSection :
    rawEquiv q h g₁ g₂ k i j (normalVectorSection q h g₁ g₂ k i j) =
      normalVector q h g₁ g₂ k i j :=
  (rawEquiv q h g₁ g₂ k i j).apply_symm_apply _

/-- The true source-normal section retains the original (G₂,−G₁) signs. -/
@[simp] theorem normalVectorSection_equation (a : Fin 2) :
    equationValue q h g₁ g₂ k i j (normalVectorSection q h g₁ g₂ k i j) a =
      ![normalCoefficientMap q h g₁ g₂ k i j g₂,
        -normalCoefficientMap q h g₁ g₂ k i j g₁] a := by
  rw [← rawEquiv_equation, rawEquiv_normalVectorSection]
  exact normalVector_equation q h g₁ g₂ k i j a

theorem normalVectorSection_unique
    (f : Γ(sourceNormal (patchImmersion q h g₁ g₂ k i j), ⊤))
    (hf : ∀ a, equationValue q h g₁ g₂ k i j f a =
      ![normalCoefficientMap q h g₁ g₂ k i j g₂,
        -normalCoefficientMap q h g₁ g₂ k i j g₁] a) :
    f = normalVectorSection q h g₁ g₂ k i j := by
  apply (rawEquiv q h g₁ g₂ k i j).injective
  rw [rawEquiv_normalVectorSection]
  apply normalVector_unique q h g₁ g₂ k i j
  intro a
  exact (rawEquiv_equation q h g₁ g₂ k i j f a).trans (hf a)

end CycleQ2SourceNormalPatch
end

end


section

/-!
# Actual source normal vectors on the projective Jacobian opens

The canonical normal pushforward isomorphism transfers the incoming
intrinsic equation functionals to the original source normal sheaf.
Restriction and coefficient multiplication use its actual sheaf maps.
The fixed equation values and uniqueness remain those of the original
normal vector, with no normalization choice or gluing premise.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2SourceNormalVectors

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open CycleQ2GeometricIntrinsicNormal CycleQ2SourceNormalSheaf
open CycleQ2NormalPushforwardIso

variable {X Y : Scheme.{0}} (j : X ⟶ Y)

local instance directSectionModule (U : Y.Opens) :
    Module Γ(Y, U) ((normalDirectImageSheaf j).val.obj (op U)) :=
  ((normalDirectImageSheaf j).val.obj (op U)).isModule

/-- The actual component isomorphism retains its original categorical inverse. -/
def sectionIso (U : Y.Opens) :
    Γ((Scheme.Modules.pushforward j).obj (sourceNormal j), U) ≅
      Γ((show Y.Modules from normalDirectImageSheaf j), U) where
  hom := (normalPushforwardIso j).hom.app U
  inv := (normalPushforwardIso j).inv.app U
  hom_inv_id := congrArg (fun g => g.app U) (normalPushforwardIso j).hom_inv_id
  inv_hom_id := congrArg (fun g => g.app U) (normalPushforwardIso j).inv_hom_id

/-- The genuine normal pushforward isomorphism on each actual open. -/
def sectionEquiv (U : Y.Opens) :
    Γ(sourceNormal j, j ⁻¹ᵁ U) ≃+
      Γ((show Y.Modules from normalDirectImageSheaf j), U) :=
  (sectionIso j U).addCommGroupIsoToAddEquiv

/-- The comparison carries the actual pulled-back surface coefficient. -/
theorem sectionEquiv_smul (U : Y.Opens) (a : Γ(Y, U))
    (f : Γ(sourceNormal j, j ⁻¹ᵁ U)) :
    sectionEquiv j U (j.app U a • f) = a • sectionEquiv j U f :=
  (normalPushforwardIso j).hom.app_smul a f

/-- The inverse uses the same actual coefficient morphism. -/
theorem sectionEquiv_symm_smul (U : Y.Opens) (a : Γ(Y, U))
    (f : Γ((show Y.Modules from normalDirectImageSheaf j), U)) :
    (sectionEquiv j U).symm (a • f) = j.app U a • (sectionEquiv j U).symm f :=
  (normalPushforwardIso j).inv.app_smul a f

/-- This comparison commutes with the genuine restrictions on both schemes. -/
theorem sectionEquiv_restrict {U V : Y.Opens} (h : V ⟶ U)
    (f : Γ(sourceNormal j, j ⁻¹ᵁ U)) :
    sectionEquiv j V
        ((sourceNormal j).presheaf.map ((Opens.map j.base).map h).op f) =
      (normalDirectImageSheaf j).val.map h.op (sectionEquiv j U f) :=
  ConcreteCategory.congr_hom ((normalPushforwardIso j).hom.mapPresheaf.naturality h.op) f

/-- The canonical inverse preserves the same restrictions. -/
theorem sectionEquiv_symm_restrict {U V : Y.Opens} (h : V ⟶ U)
    (f : Γ((show Y.Modules from normalDirectImageSheaf j), U)) :
    (sectionEquiv j V).symm ((normalDirectImageSheaf j).val.map h.op f) =
      (sourceNormal j).presheaf.map ((Opens.map j.base).map h).op
        ((sectionEquiv j U).symm f) :=
  ConcreteCategory.congr_hom ((normalPushforwardIso j).inv.mapPresheaf.naturality h.op) f

section Actual

open CycleQ2GeometricLiteralSurface CycleQ2GeometricNormalCharts
open CycleQ2GeometricSurfaceJacobianCharts CycleQ2GeometricSurfacePrincipalCurveCharts
open CycleQ2GeometricSurfaceAdjunction CycleQ2GeometricSurfaceDehomogenizedCharts
open CycleQ2GeometricAffineCurveCharts CycleQ2SeedTrace CycleQ2NormalConnecting

/-- The fixed first-chart vector as a section of the original source normal sheaf. -/
def firstSourceNormalVector (r θ : ℂ) (i : Fin 2) (a : Fin 3) :
    Γ(actualNormal r θ, curveToSurface r θ ⁻¹ᵁ firstNormalOpen r θ i a) :=
  (sectionEquiv (curveToSurface r θ) (firstNormalOpen r θ i a)).symm
    (firstNormalVectorSection r θ i a)

/-- The fixed second-chart vector as a section of the original source normal sheaf. -/
def secondSourceNormalVector (r θ : ℂ) (i : Fin 2) (a : Fin 3) :
    Γ(actualNormal r θ, curveToSurface r θ ⁻¹ᵁ secondNormalOpen r θ i a) :=
  (sectionEquiv (curveToSurface r θ) (secondNormalOpen r θ i a)).symm
    (secondNormalVectorSection r θ i a)

def firstSourceEquationValue (r θ : ℂ) (i : Fin 2) (a : Fin 3)
    (f : Γ(actualNormal r θ, curveToSurface r θ ⁻¹ᵁ firstNormalOpen r θ i a))
    (b : Fin 2) : FirstNormalCurveRing r θ i a :=
  firstNormalEquationValue r θ i a
    (sectionEquiv (curveToSurface r θ) (firstNormalOpen r θ i a) f) b

def secondSourceEquationValue (r θ : ℂ) (i : Fin 2) (a : Fin 3)
    (f : Γ(actualNormal r θ, curveToSurface r θ ⁻¹ᵁ secondNormalOpen r θ i a))
    (b : Fin 2) : SecondNormalCurveRing r θ i a :=
  secondNormalEquationValue r θ i a
    (sectionEquiv (curveToSurface r θ) (secondNormalOpen r θ i a) f) b

theorem firstSourceEquation_ext (r θ : ℂ) (i : Fin 2) (a : Fin 3)
    (f g : Γ(actualNormal r θ, curveToSurface r θ ⁻¹ᵁ firstNormalOpen r θ i a))
    (hfg : ∀ b, firstSourceEquationValue r θ i a f b =
      firstSourceEquationValue r θ i a g b) : f = g := by
  apply (sectionEquiv (curveToSurface r θ) (firstNormalOpen r θ i a)).injective
  exact firstNormalSection_ext r θ i a _ _ hfg

theorem secondSourceEquation_ext (r θ : ℂ) (i : Fin 2) (a : Fin 3)
    (f g : Γ(actualNormal r θ, curveToSurface r θ ⁻¹ᵁ secondNormalOpen r θ i a))
    (hfg : ∀ b, secondSourceEquationValue r θ i a f b =
      secondSourceEquationValue r θ i a g b) : f = g := by
  apply (sectionEquiv (curveToSurface r θ) (secondNormalOpen r θ i a)).injective
  exact secondNormalSection_ext r θ i a _ _ hfg

/-- The first source vector has the fixed original defining-equation values. -/
theorem firstSourceNormalVector_equation (r θ : ℂ) (i : Fin 2) (a : Fin 3) (b : Fin 2) :
    firstSourceEquationValue r θ i a (firstSourceNormalVector r θ i a) b =
      ![normalCoefficientMap (firstQuadric r) (firstCubic θ)
          (firstSurfaceDehomogenize (originalG1 r)) (firstSurfaceDehomogenize originalG2)
          (firstSurfaceDehomogenize (thetaK θ)) i a (firstSurfaceDehomogenize originalG2),
        -normalCoefficientMap (firstQuadric r) (firstCubic θ)
          (firstSurfaceDehomogenize (originalG1 r)) (firstSurfaceDehomogenize originalG2)
          (firstSurfaceDehomogenize (thetaK θ)) i a (firstSurfaceDehomogenize (originalG1 r))] b := by
  exact (congrArg (fun f => firstNormalEquationValue r θ i a f b)
    ((sectionEquiv (curveToSurface r θ) (firstNormalOpen r θ i a)).apply_symm_apply
      (firstNormalVectorSection r θ i a))).trans
        (firstNormalVectorSection_equation r θ i a b)

/-- The second source vector has the same fixed (G₂,−G₁) convention. -/
theorem secondSourceNormalVector_equation (r θ : ℂ) (i : Fin 2) (a : Fin 3) (b : Fin 2) :
    secondSourceEquationValue r θ i a (secondSourceNormalVector r θ i a) b =
      ![normalCoefficientMap (secondQuadric r) (secondCubic θ)
          (secondSurfaceDehomogenize (originalG1 r)) (secondSurfaceDehomogenize originalG2)
          (secondSurfaceDehomogenize (thetaK θ)) i a (secondSurfaceDehomogenize originalG2),
        -normalCoefficientMap (secondQuadric r) (secondCubic θ)
          (secondSurfaceDehomogenize (originalG1 r)) (secondSurfaceDehomogenize originalG2)
          (secondSurfaceDehomogenize (thetaK θ)) i a (secondSurfaceDehomogenize (originalG1 r))] b := by
  exact (congrArg (fun f => secondNormalEquationValue r θ i a f b)
    ((sectionEquiv (curveToSurface r θ) (secondNormalOpen r θ i a)).apply_symm_apply
      (secondNormalVectorSection r θ i a))).trans
        (secondNormalVectorSection_equation r θ i a b)

end Actual
end CycleQ2SourceNormalVectors
end

end


section

/-!
# Original ideal generators determine projective normal sections

The affine all-subopen uniqueness theorem is transported through the
actual Cartesian chart and the original normal restriction isomorphism.
Every equation remains the original section under the canonical ring maps.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2NormalChartGeneratorExt

open CategoryTheory AlgebraicGeometry Opposite
open CycleQ2GeometricIntrinsicNormal CycleQ2AffineNormalGeneratorExt
open CycleQ2SourceNormalRestriction CycleQ2NormalSectionEvaluation

variable {A B : CommRingCat.{0}} (φ : A ⟶ B)
  {X Y : Scheme.{0}} (j : X ⟶ Y) (v : Spec A ⟶ Y) (u : Spec B ⟶ X)
  [IsOpenImmersion v] [IsOpenImmersion u]
  (H : IsPullback (Spec.map φ) u v j)

/-- An original affine ideal element, restricted and read in the actual
surface image open by the original Cartesian ideal comparison. -/
def chartIdealOn (U : (Spec A).Opens) (a : RingHom.ker φ.hom) :
    RingHom.ker (j.app (v ''ᵁ U)).hom :=
  normalOpenIdealPullback j v u (Spec.map φ) H U
    (restrictedOriginalIdeal φ U a)

/-- The ideal comparison has the literal canonical section formula. -/
theorem chartIdealOn_coe (U : (Spec A).Opens) (a : RingHom.ker φ.hom) :
    (chartIdealOn φ j v u H U a : Γ(Y, v ''ᵁ U)) =
      (v.appIso U).inv ((Spec A).presheaf.map
        (homOfLE (show U ≤ ⊤ from le_top)).op ((Scheme.ΓSpecIso A).inv a)) := by
  have h := kernelSectionRestrict_coe (Spec.map φ)
    (homOfLE (show U ≤ ⊤ from le_top))
    ((affineKernelSectionSemilinearEquiv φ).symm a)
  exact (normalOpenIdealPullback_coe j v u (Spec.map φ) H U
    (restrictedOriginalIdeal φ U a)).trans (congrArg (v.appIso U).inv h)

/-- The actual normal restriction evaluates each original ideal element
through the genuine structure-ring base-change isomorphism. -/
theorem chartNormal_evaluate (U : (Spec A).Opens)
    (f : (normalDirectImageSheaf j).val.obj (op (v ''ᵁ U)))
    (a : RingHom.ker φ.hom) :
    normalSectionEvaluate (Spec.map φ) U
      ((normalDirectImageRestrictionIso j (Spec.map φ) u v H).hom.app U f)
      (restrictedOriginalIdeal φ U a) =
    (baseChangeStructureSectionIso j v u (Spec.map φ) H U).hom
      (normalSectionEvaluate j (v ''ᵁ U) f (chartIdealOn φ j v u H U a)) :=
  normalDirectImageRestrictionIso_evaluate j (Spec.map φ) u v H U f
    (restrictedOriginalIdeal φ U a)

/-- On every image subopen of a genuine affine Cartesian chart, the
original ideal generators determine the actual normal sheaf section. -/
theorem chartNormal_ext_on_generators {ι : Type*}
    (w : ι → RingHom.ker φ.hom) (hw : Submodule.span A (Set.range w) = ⊤)
    (U : (Spec A).Opens)
    (f g : (normalDirectImageSheaf j).val.obj (op (v ''ᵁ U)))
    (hfg : ∀ a,
      normalSectionEvaluate j (v ''ᵁ U) f (chartIdealOn φ j v u H U (w a)) =
        normalSectionEvaluate j (v ''ᵁ U) g (chartIdealOn φ j v u H U (w a))) :
    f = g := by
  apply (ConcreteCategory.bijective_of_isIso
    ((normalDirectImageRestrictionIso j (Spec.map φ) u v H).hom.app U)).injective
  apply affineNormal_ext_on_generators φ w hw U
  intro a
  exact (chartNormal_evaluate φ j v u H U f (w a)).trans
    ((congrArg (baseChangeStructureSectionIso j v u (Spec.map φ) H U).hom (hfg a)).trans
      (chartNormal_evaluate φ j v u H U g (w a)).symm)

/-- The canonical ideal pullback uses the actual restrictions on every
subopen, including all scheme-section equality transports. -/
theorem idealPullback_restrict {U V : (Spec A).Opens} (k : U ⟶ V)
    (a : RingHom.ker ((Spec.map φ).app V).hom) :
    kernelSectionRestrict j (v.opensFunctor.map k)
        (normalOpenIdealPullback j v u (Spec.map φ) H V a) =
      normalOpenIdealPullback j v u (Spec.map φ) H U
        (kernelSectionRestrict (Spec.map φ) k a) := by
  apply Subtype.ext
  have hn := ConcreteCategory.congr_hom (v.appIso_inv_naturality k.op) (a : Γ(Spec A, V))
  have hl := kernelSectionRestrict_coe j (v.opensFunctor.map k)
    (normalOpenIdealPullback j v u (Spec.map φ) H V a)
  have hr := normalOpenIdealPullback_coe j v u (Spec.map φ) H U
    (kernelSectionRestrict (Spec.map φ) k a)
  exact hl.trans
    ((congrArg (Y.presheaf.map (v.opensFunctor.map k).op)
      (normalOpenIdealPullback_coe j v u (Spec.map φ) H V a)).trans
      (hn.symm.trans ((congrArg (v.appIso U).inv
        (kernelSectionRestrict_coe (Spec.map φ) k a)).symm.trans hr.symm)))

section NormalPatch

open CycleQ2GeometricSurfaceAdjunction CycleQ2GeometricAffineCurveCharts

variable (q h : AffinePoly) (g₁ g₂ k : SurfacePoly) (n : Fin 2) (t : Fin 3)
  (iS : Spec (CommRingCat.of (NormalSurfacePatch q h g₁ g₂ k n t)) ⟶ Y)
  (iC : Spec (CommRingCat.of (NormalCurvePatch q h g₁ g₂ k n t)) ⟶ X)
  [IsOpenImmersion iS] [IsOpenImmersion iC]
  (HC : IsPullback (Spec.map (CycleQ2AffineNormalPatchExt.patchMap q h g₁ g₂ k n t))
    iC iS j)

/-- The original q or z equation on every image subopen of an actual
augmented-Jacobian chart. -/
def normalChartEquationOn
    (U : (Spec (CommRingCat.of (NormalSurfacePatch q h g₁ g₂ k n t))).Opens)
    (a : Fin 2) : RingHom.ker (j.app (iS ''ᵁ U)).hom :=
  chartIdealOn (CycleQ2AffineNormalPatchExt.patchMap q h g₁ g₂ k n t) j iS iC HC U
    ⟨algebraMap SurfacePoly (NormalSurfacePatch q h g₁ g₂ k n t)
      (normalPolynomial q a), normalEquation_mem q h g₁ g₂ k n t a⟩

/-- The two original equations determine actual projective normal
sections on every smaller chart open, with no additional generation
or local-freeness hypothesis. -/
theorem normalChartSection_ext
    (U : (Spec (CommRingCat.of (NormalSurfacePatch q h g₁ g₂ k n t))).Opens)
    (f g : (normalDirectImageSheaf j).val.obj (op (iS ''ᵁ U)))
    (hfg : ∀ a : Fin 2,
      normalSectionEvaluate j (iS ''ᵁ U) f
        (normalChartEquationOn j q h g₁ g₂ k n t iS iC HC U a) =
      normalSectionEvaluate j (iS ''ᵁ U) g
        (normalChartEquationOn j q h g₁ g₂ k n t iS iC HC U a)) : f = g :=
  chartNormal_ext_on_generators (CycleQ2AffineNormalPatchExt.patchMap q h g₁ g₂ k n t)
    j iS iC HC
    (fun a : Fin 2 => ⟨algebraMap SurfacePoly (NormalSurfacePatch q h g₁ g₂ k n t)
      (normalPolynomial q a), normalEquation_mem q h g₁ g₂ k n t a⟩)
    (CycleQ2AffineNormalPatchExt.equationGenerators_span q h g₁ g₂ k n t) U f g hfg

end NormalPatch

end CycleQ2NormalChartGeneratorExt
end

end


section

/-! Original chart ideal elements as the actual coordinate sections. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2NormalChartSections

open CategoryTheory AlgebraicGeometry Opposite
open CycleQ2GeometricIntrinsicNormal CycleQ2GeometricAffineChartSections
open CycleQ2GeometricAffineDifferentialSheaf CycleQ2NormalChartGeneratorExt

variable {A : CommRingCat.{0}} {Y : Scheme.{0}} {W : Y.Opens}
  (e : W.toScheme ≅ Spec A)

/-- The original chart section on an image open is precisely the inverse
open-immersion ring map applied to the original affine constant section. -/
theorem chartSection_image (U : (Spec A).Opens)
    (hU : (e.inv ≫ W.ι) ''ᵁ U ≤ W) (a : A) :
    chartSection e (Over.mk (homOfLE hU)) a =
      ((e.inv ≫ W.ι).appIso U).inv
        ((Spec A).presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op
          ((Scheme.ΓSpecIso A).inv a)) := by
  let v : Spec A ⟶ Y := e.inv ≫ W.ι
  let V : Over W := Over.mk (homOfLE hU)
  have hs := ConcreteCategory.congr_hom (chartSectionIso e V).inv_hom_id
    (algebraMap A (AffineSections A (v ⁻¹ᵁ (v ''ᵁ U))) a)
  change v.app (v ''ᵁ U) (chartSection e V a) =
    algebraMap A (AffineSections A (v ⁻¹ᵁ (v ''ᵁ U))) a at hs
  have ht := congrArg ((Spec A).presheaf.map
    (eqToHom (v.preimage_image_eq U).symm).op) hs
  change (Spec A).presheaf.map (eqToHom (v.preimage_image_eq U).symm).op
      (v.app (v ''ᵁ U) (chartSection e V a)) =
    (Spec A).presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op
      ((Scheme.ΓSpecIso A).inv a) at ht
  have hh := ConcreteCategory.congr_hom (v.appIso_hom U) (chartSection e V a)
  apply (v.appIso U).commRingCatIsoToRingEquiv.injective
  exact (hh.trans ht).trans
    (ConcreteCategory.congr_hom (v.appIso U).inv_hom_id
      ((Spec A).presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op
        ((Scheme.ΓSpecIso A).inv a))).symm

section IdealSections

variable {B : CommRingCat.{0}} (φ : A ⟶ B)
  {X : Scheme.{0}} (j : X ⟶ Y) (v : Spec A ⟶ Y) (u : Spec B ⟶ X)
  [IsOpenImmersion v] [IsOpenImmersion u]
  (H : IsPullback (Spec.map φ) u v j)

theorem kernelSectionRestrict_comp {U V Z : Y.Opens} (h : V ⟶ U) (k : Z ⟶ V)
    (a : RingHom.ker (j.app U).hom) :
    kernelSectionRestrict j k (kernelSectionRestrict j h a) =
      kernelSectionRestrict j (k ≫ h) a := by
  apply Subtype.ext
  simp only [kernelSectionRestrict_coe]
  exact (ConcreteCategory.congr_hom (Y.presheaf.map_comp h.op k.op) (a : Γ(Y, U))).symm

theorem originalIdeal_restrict {U V : (Spec A).Opens} (k : U ⟶ V)
    (a : RingHom.ker φ.hom) :
    kernelSectionRestrict (Spec.map φ) k
        (CycleQ2AffineNormalGeneratorExt.restrictedOriginalIdeal φ V a) =
      CycleQ2AffineNormalGeneratorExt.restrictedOriginalIdeal φ U a :=
  kernelSectionRestrict_comp (Spec.map φ)
    (homOfLE (show V ≤ ⊤ from le_top)) k
      ((affineKernelSectionSemilinearEquiv φ).symm a)

theorem chartIdealOn_restrict {U V : (Spec A).Opens} (k : U ⟶ V)
    (a : RingHom.ker φ.hom) :
    kernelSectionRestrict j (v.opensFunctor.map k) (chartIdealOn φ j v u H V a) =
      chartIdealOn φ j v u H U a :=
  (idealPullback_restrict φ j v u H k
    (CycleQ2AffineNormalGeneratorExt.restrictedOriginalIdeal φ V a)).trans
      (congrArg (normalOpenIdealPullback j v u (Spec.map φ) H U)
        (originalIdeal_restrict φ k a))

/-- An original equation on any actual subopen of the chart range. -/
def idealOnSubopen (V : Y.Opens) (hV : V ≤ v.opensRange) (a : RingHom.ker φ.hom) :
    RingHom.ker (j.app V).hom :=
  kernelSectionRestrict j
    (homOfLE (hV.trans_eq v.image_top_eq_opensRange.symm))
      (chartIdealOn φ j v u H ⊤ a)

theorem idealOnSubopen_restrict {U V : Y.Opens} (k : U ⟶ V)
    (hV : V ≤ v.opensRange) (a : RingHom.ker φ.hom) :
    kernelSectionRestrict j k (idealOnSubopen φ j v u H V hV a) =
      idealOnSubopen φ j v u H U (k.le.trans hV) a :=
  kernelSectionRestrict_comp j
    (homOfLE (hV.trans_eq v.image_top_eq_opensRange.symm)) k
      (chartIdealOn φ j v u H ⊤ a)

theorem idealOnSubopen_image (V : Y.Opens) (hV : V ≤ v.opensRange)
    (a : RingHom.ker φ.hom) :
    kernelSectionRestrict j (homOfLE (v.image_preimage_le V))
      (idealOnSubopen φ j v u H V hV a) =
        chartIdealOn φ j v u H (v ⁻¹ᵁ V) a := by
  exact (kernelSectionRestrict_comp j
    (homOfLE (hV.trans_eq v.image_top_eq_opensRange.symm))
    (homOfLE (v.image_preimage_le V)) (chartIdealOn φ j v u H ⊤ a)).trans
      (chartIdealOn_restrict φ j v u H
        (homOfLE (show v ⁻¹ᵁ V ≤ ⊤ from le_top)) a)

/-- The original generators detect actual normal sections on every
open contained in the chart, without choosing an affine subcover. -/
theorem normal_ext_on_subopen {ι : Type*}
    (w : ι → RingHom.ker φ.hom) (hw : Submodule.span A (Set.range w) = ⊤)
    (V : Y.Opens) (hV : V ≤ v.opensRange)
    (f g : (normalDirectImageSheaf j).val.obj (op V))
    (hfg : ∀ a,
      normalSectionEvaluate j V f (idealOnSubopen φ j v u H V hV (w a)) =
        normalSectionEvaluate j V g (idealOnSubopen φ j v u H V hV (w a))) :
    f = g := by
  let k : v ''ᵁ (v ⁻¹ᵁ V) ⟶ V := homOfLE (v.image_preimage_le V)
  have hi : V ≤ v ''ᵁ (v ⁻¹ᵁ V) := by
    rw [v.image_preimage_eq_opensRange_inf]
    exact le_inf hV le_rfl
  have : IsIso k :=
    ⟨homOfLE hi, Subsingleton.elim _ _, Subsingleton.elim _ _⟩
  apply (ConcreteCategory.bijective_of_isIso
    ((normalDirectImageSheaf j).val.presheaf.map k.op)).injective
  apply chartNormal_ext_on_generators φ j v u H w hw (v ⁻¹ᵁ V)
  intro a
  have ha := idealOnSubopen_image φ j v u H V hV (w a)
  have hf := normalSectionEvaluate_restrict j k f
    (idealOnSubopen φ j v u H V hV (w a))
  have hg := normalSectionEvaluate_restrict j k g
    (idealOnSubopen φ j v u H V hV (w a))
  exact ((congrArg (normalSectionEvaluate j (v ''ᵁ (v ⁻¹ᵁ V))
    ((normalDirectImageSheaf j).val.map k.op f)) ha).symm.trans hf).trans
      ((congrArg ((imageStructureModule j).val.map k.op) (hfg a)).trans
        ((congrArg (normalSectionEvaluate j (v ''ᵁ (v ⁻¹ᵁ V))
          ((normalDirectImageSheaf j).val.map k.op g)) ha).symm.trans hg).symm)

/-- Original coefficients on an actual chart subopen, using only the
canonical affine section and open-immersion maps. -/
def coefficientOnSubopen (V : Y.Opens) (hV : V ≤ v.opensRange) : A →+* Γ(Y, V) :=
  (Y.presheaf.map (homOfLE (hV.trans_eq v.image_top_eq_opensRange.symm)).op).hom.comp
    ((v.appIso ⊤).inv.hom.comp (Scheme.ΓSpecIso A).inv.hom)

theorem originalIdeal_top (a : RingHom.ker φ.hom) :
    CycleQ2AffineNormalGeneratorExt.restrictedOriginalIdeal φ ⊤ a =
      (affineKernelSectionSemilinearEquiv φ).symm a := by
  apply Subtype.ext
  rw [CycleQ2AffineNormalGeneratorExt.restrictedOriginalIdeal, kernelSectionRestrict_coe]
  change ((Spec A).presheaf.map (𝟙 (op ⊤))) _ = _
  exact ConcreteCategory.congr_hom ((Spec A).presheaf.map_id (op ⊤)) _

theorem chartIdealOn_top (a : RingHom.ker φ.hom) :
    chartIdealOn φ j v u H ⊤ a =
      normalOpenIdealPullback j v u (Spec.map φ) H ⊤
        ((affineKernelSectionSemilinearEquiv φ).symm a) :=
  congrArg (normalOpenIdealPullback j v u (Spec.map φ) H ⊤) (originalIdeal_top φ a)

theorem idealOnSubopen_coe (V : Y.Opens) (hV : V ≤ v.opensRange)
    (a : RingHom.ker φ.hom) :
    (idealOnSubopen φ j v u H V hV a : Γ(Y, V)) = coefficientOnSubopen v V hV a := by
  have ht := congrArg (fun x : RingHom.ker (j.app (v ''ᵁ ⊤)).hom => (x : Γ(Y, v ''ᵁ ⊤)))
    (chartIdealOn_top φ j v u H a)
  exact (kernelSectionRestrict_coe j
    (homOfLE (hV.trans_eq v.image_top_eq_opensRange.symm))
      (chartIdealOn φ j v u H ⊤ a)).trans
    (congrArg (Y.presheaf.map
      (homOfLE (hV.trans_eq v.image_top_eq_opensRange.symm)).op)
        (ht.trans (normalOpenAlgebraIdeal_coe φ j v u H a)))

/-- The original coefficient maps are exactly the actual chart-section
maps on every smaller open, with no choice of trivialization. -/
theorem coefficientOnSubopen_chartSection
    (hv : e.inv ≫ W.ι = v) (V : Y.Opens) (hV : V ≤ v.opensRange)
    (hVW : V ≤ W) (a : A) :
    coefficientOnSubopen v V hV a = chartSection e (Over.mk (homOfLE hVW)) a := by
  subst v
  have htop : (e.inv ≫ W.ι) ''ᵁ (⊤ : (Spec A).Opens) ≤ W := by
    rw [Scheme.Hom.image_top_eq_opensRange,
      Scheme.Hom.opensRange_comp_of_isIso, Scheme.Opens.opensRange_ι]
  let k : V ⟶ (e.inv ≫ W.ι) ''ᵁ (⊤ : (Spec A).Opens) :=
    homOfLE (hV.trans_eq (e.inv ≫ W.ι).image_top_eq_opensRange.symm)
  have h := chartSection_image e ⊤ htop a
  have ht : chartSection e (Over.mk (homOfLE htop)) a =
      ((e.inv ≫ W.ι).appIso ⊤).inv ((Scheme.ΓSpecIso A).inv a) := by
    change chartSection e (Over.mk (homOfLE htop)) a = _ at h
    simpa only [show (homOfLE (show (⊤ : (Spec A).Opens) ≤ ⊤ from le_top)).op =
      𝟙 (op ⊤) from rfl, CategoryTheory.Functor.map_id, CommRingCat.id_apply] using h
  have hn := chartSection_naturality e
    (Over.homMk k (Subsingleton.elim _ _) :
      Over.mk (homOfLE hVW) ⟶ Over.mk (homOfLE htop)) a
  exact (congrArg (Y.presheaf.map k.op) ht).symm.trans hn

theorem idealOnSubopen_chartSection
    (hv : e.inv ≫ W.ι = v) (V : Y.Opens) (hV : V ≤ v.opensRange)
    (hVW : V ≤ W) (a : RingHom.ker φ.hom) :
    (idealOnSubopen φ j v u H V hV a : Γ(Y, V)) =
      chartSection e (Over.mk (homOfLE hVW)) a :=
  (idealOnSubopen_coe φ j v u H V hV a).trans
    (coefficientOnSubopen_chartSection e v hv V hV hVW a)

end IdealSections

end CycleQ2NormalChartSections
end

end


section

/-! The fixed normal vectors retain their original equation values on
every projective chart subopen. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2NormalVectorEvaluation

open CategoryTheory AlgebraicGeometry Opposite
open CycleQ2GeometricIntrinsicNormal CycleQ2GeometricNormalCharts
open CycleQ2NormalChartGeneratorExt CycleQ2NormalChartSections

private theorem normalIndexCases (a : Fin 2) : a = 0 ∨ a = 1 := by
  fin_cases a <;> simp

variable {A B : CommRingCat.{0}} (φ : A ⟶ B)
  {X Y : Scheme.{0}} (j : X ⟶ Y) (v : Spec A ⟶ Y) (u : Spec B ⟶ X)
  [IsOpenImmersion v] [IsOpenImmersion u]
  (H : IsPullback (Spec.map φ) u v j)

/-- Undoing the canonical normal-value normalization gives the
original structure-sheaf coefficient, with its original sign. -/
theorem normalizedValue_top
    (f : (normalDirectImageSheaf j).val.obj (op v.opensRange))
    (a : RingHom.ker φ.hom) (b : A)
    (hf : normalOpenIdealValue φ j v u H f a = φ b) :
    normalSectionEvaluate j (v ''ᵁ ⊤)
        ((normalDirectImageSheaf j).val.map
          (homOfLE (v.image_le_opensRange ⊤)).op f)
        (chartIdealOn φ j v u H ⊤ a) =
      j.app (v ''ᵁ ⊤) ((v.appIso ⊤).inv ((Scheme.ΓSpecIso A).inv b)) := by
  have hraw :
      normalSectionEvaluate j (v ''ᵁ ⊤)
          ((normalDirectImageSheaf j).val.map
            (homOfLE (v.image_le_opensRange ⊤)).op f)
          (normalOpenIdealPullback j v u (Spec.map φ) H ⊤
            ((affineKernelSectionSemilinearEquiv φ).symm a)) =
        j.app (v ''ᵁ ⊤) ((v.appIso ⊤).inv ((Scheme.ΓSpecIso A).inv b)) := by
    apply (baseChangeStructureSectionIso j v u (Spec.map φ) H ⊤).commRingCatIsoToRingEquiv.injective
    apply (specTopRingEquiv B).injective
    have hc := congrArg (specTopRingEquiv B)
      (ConcreteCategory.congr_hom
        (baseChangeStructureSectionIso_app j v u (Spec.map φ) H ⊤)
        ((Scheme.ΓSpecIso A).inv b))
    have hb : specTopRingEquiv B
        ((baseChangeStructureSectionIso j v u (Spec.map φ) H ⊤).hom
          (j.app (v ''ᵁ ⊤) ((v.appIso ⊤).inv ((Scheme.ΓSpecIso A).inv b)))) = φ b :=
      hc.trans ((affineSectionMap_normalization φ ((Scheme.ΓSpecIso A).inv b)).trans
        (congrArg φ ((specTopRingEquiv A).apply_symm_apply b)))
    exact hf.trans hb.symm
  exact (congrArg (normalSectionEvaluate j (v ''ᵁ ⊤)
    ((normalDirectImageSheaf j).val.map
      (homOfLE (v.image_le_opensRange ⊤)).op f))
    (chartIdealOn_top φ j v u H a)).trans hraw

/-- The same fixed equation value holds on every actual contained open. -/
theorem normalizedValue_subopen
    (f : (normalDirectImageSheaf j).val.obj (op v.opensRange))
    (a : RingHom.ker φ.hom) (b : A)
    (hf : normalOpenIdealValue φ j v u H f a = φ b)
    (V : Y.Opens) (hV : V ≤ v.opensRange) :
    normalSectionEvaluate j V
        ((normalDirectImageSheaf j).val.map (homOfLE hV).op f)
        (idealOnSubopen φ j v u H V hV a) =
      j.app V (coefficientOnSubopen v V hV b) := by
  let k : V ⟶ v ''ᵁ (⊤ : (Spec A).Opens) :=
    homOfLE (hV.trans_eq v.image_top_eq_opensRange.symm)
  let t : v ''ᵁ (⊤ : (Spec A).Opens) ⟶ v.opensRange :=
    homOfLE (v.image_le_opensRange ⊤)
  have hr : (normalDirectImageSheaf j).val.map k.op
      ((normalDirectImageSheaf j).val.map t.op f) =
        (normalDirectImageSheaf j).val.map (homOfLE hV).op f :=
    (ConcreteCategory.congr_hom
      ((normalDirectImageSheaf j).val.presheaf.map_comp t.op k.op) f).symm
  have he := normalSectionEvaluate_restrict j k
    ((normalDirectImageSheaf j).val.map t.op f) (chartIdealOn φ j v u H ⊤ a)
  have hv := normalizedValue_top φ j v u H f a b hf
  have hn := ConcreteCategory.congr_hom (j.naturality k.op)
    ((v.appIso ⊤).inv ((Scheme.ΓSpecIso A).inv b))
  exact ((congrArg (fun z => normalSectionEvaluate j V z
    (idealOnSubopen φ j v u H V hV a)) hr).symm.trans he).trans
    ((congrArg ((imageStructureModule j).val.map k.op) hv).trans hn.symm)

section NormalPatch

open CycleQ2GeometricSurfaceAdjunction CycleQ2GeometricAffineCurveCharts

variable (q h : AffinePoly) (g₁ g₂ k : SurfacePoly) (n : Fin 2) (t : Fin 3)
  (iS : Spec (CommRingCat.of (NormalSurfacePatch q h g₁ g₂ k n t)) ⟶ Y)
  (iC : Spec (CommRingCat.of (NormalCurvePatch q h g₁ g₂ k n t)) ⟶ X)
  [IsOpenImmersion iS] [IsOpenImmersion iC]
  (HC : IsPullback (Spec.map (CycleQ2AffineNormalPatchExt.patchMap q h g₁ g₂ k n t))
    iC iS j)

/-- The actual fixed normal vector has its original (G₂,−G₁) equation
values on every projective chart subopen, before any normalization by a
chosen basis or passage to cohomology. -/
theorem normalVector_value_subopen (V : Y.Opens) (hV : V ≤ iS.opensRange) (a : Fin 2) :
    normalSectionEvaluate j V
        ((normalDirectImageSheaf j).val.map (homOfLE hV).op
          (normalChartVectorSection q h g₁ g₂ k n t j iS iC HC))
        (idealOnSubopen (CycleQ2AffineNormalPatchExt.patchMap q h g₁ g₂ k n t)
          j iS iC HC V hV (normalChartIdealEquation q h g₁ g₂ k n t a)) =
      j.app V (coefficientOnSubopen iS V hV
        (algebraMap SurfacePoly (NormalSurfacePatch q h g₁ g₂ k n t) (![g₂, -g₁] a))) := by
  apply normalizedValue_subopen
  have hv := normalChartVectorSection_equation q h g₁ g₂ k n t j iS iC HC a
  have hb : (CycleQ2AffineNormalPatchExt.patchMap q h g₁ g₂ k n t)
      (algebraMap SurfacePoly (NormalSurfacePatch q h g₁ g₂ k n t) (![g₂, -g₁] a)) =
        ![normalCoefficientMap q h g₁ g₂ k n t g₂,
          -normalCoefficientMap q h g₁ g₂ k n t g₁] a := by
    exact (normalAlgebraMap_polynomial q h g₁ g₂ k n t (![g₂, -g₁] a)).trans (by
      rcases normalIndexCases a with rfl | rfl
      · rfl
      · exact map_neg _ _)
  exact hv.trans hb.symm

end NormalPatch

end CycleQ2NormalVectorEvaluation
end

end


section

/-!
# Intrinsic normal coefficients on the original quartic overlap

The inverse coordinate section on the actual surface overlap pulls back,
after restriction to the original curve overlap, to the inverse of the
existing projective transition unit. Its square is exactly the transition
of the existing normal module sheaf. The two overlaps are kept distinct.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace CycleQ2NormalTransitionBinding

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry MvPolynomial
open CycleQ2CartierProjectiveCover CycleQ2GeometricSurfaceAdjunction
open CycleQ2GeometricSurfaceDehomogenizedCharts CycleQ2GeometricSurfaceOverlap
open CycleQ2GeometricSurfaceCurveCharts CycleQ2SurfaceOverlapSections
open CycleQ2GeometricProjectiveCurve CycleQ2GeometricProjectiveTransition
open CycleQ2GeometricProjectiveNormalClass

private theorem pullback_restriction_square {X Y : Scheme.{0}} (j : X ⟶ Y)
    {U V : Y.Opens} {P Q : X.Opens} (hVU : V ≤ U) (hP : P ≤ j ⁻¹ᵁ U)
    (hQP : Q ≤ P) (hQV : Q ≤ j ⁻¹ᵁ V) (s : Γ(Y, U)) :
    j.appLE V Q hQV (Y.presheaf.map (homOfLE hVU).op s) =
      X.presheaf.map (homOfLE hQP).op (j.appLE U P hP s) :=
  (ConcreteCategory.congr_hom (j.map_appLE hQV (homOfLE hVU).op) s).trans
    (ConcreteCategory.congr_hom (j.appLE_map hP (homOfLE hQP).op) s).symm

private theorem restriction_comp {X : Scheme.{0}} {U V W : X.Opens}
    (hVU : V ≤ U) (hWV : W ≤ V) (s : Γ(X, U)) :
    X.presheaf.map (homOfLE hWV).op (X.presheaf.map (homOfLE hVU).op s) =
      X.presheaf.map (homOfLE (hWV.trans hVU)).op s :=
  (ConcreteCategory.congr_hom
    (X.presheaf.map_comp (homOfLE hVU).op (homOfLE hWV).op) s).symm

def firstSurfaceCoordinateSection (r θ : ℂ) :
    Γ(projectiveSurface r θ, coordinatePatch r θ 1) :=
  (CycleQ2GeometricSurfaceDehomogenizedCharts.firstSectionsEquiv r θ).symm
    (surfaceMap (firstEquations r θ) (X (some 1)))

def firstCurveRatioSection (r θ : ℂ) :
    Γ(projectiveCurve r θ, coordinateProjectivePatch r θ 1) :=
  (Proj.basicOpenIsoAway (CycleQ2GeometricProjectiveCurve.curveGrade r θ)
    (CycleQ2GeometricProjectiveAffine.coordinateDen r θ 1)
    (CycleQ2GeometricProjectiveCurve.coordinate_mem_grade r θ 1) (by decide)).hom
    (CycleQ2GeometricProjectiveAffine.coordinateRatio r θ 1 2)

private theorem old_ratio_eq_dehomogenized_ratio (r θ : ℂ) :
    CycleQ2GeometricProjectiveAffine.coordinateRatio r θ 1 2 =
      CycleQ2GeometricDehomogenizedCharts.coordinateRatio r θ 1 2 := by
  rw [CycleQ2GeometricProjectiveOverlap.coordinateRatio_eq_awayMk]
  rfl

private theorem curve_ratio_coordinate (r θ : ℂ) :
    CycleQ2GeometricAffineProjectiveCharts.firstSectionsEquiv r θ (firstCurveRatioSection r θ) =
      Ideal.Quotient.mk (CycleQ2GeometricAffineCurveCharts.chartIdeal
        ![CycleQ2GeometricAffineCurveCharts.firstQuadric r,
          CycleQ2GeometricAffineCurveCharts.firstCubic θ]) (X (1 : Fin 3)) := by
  change CycleQ2GeometricDehomogenizedCharts.firstChartEquiv r θ
    ((Proj.basicOpenIsoAway (CycleQ2GeometricProjectiveCurve.curveGrade r θ)
      (CycleQ2GeometricProjectiveAffine.coordinateDen r θ 1)
      (CycleQ2GeometricProjectiveCurve.coordinate_mem_grade r θ 1) (by decide)).inv
      ((Proj.basicOpenIsoAway (CycleQ2GeometricProjectiveCurve.curveGrade r θ)
        (CycleQ2GeometricProjectiveAffine.coordinateDen r θ 1)
        (CycleQ2GeometricProjectiveCurve.coordinate_mem_grade r θ 1) (by decide)).hom
        (CycleQ2GeometricProjectiveAffine.coordinateRatio r θ 1 2))) = _
  rw [Iso.hom_inv_id_apply, old_ratio_eq_dehomogenized_ratio]
  exact CycleQ2GeometricDehomogenizedCharts.firstChartEquiv_coordinateRatio r θ (1 : Fin 3)

private theorem firstAffineCurveMap_coordinate (r θ : ℂ) :
    firstAffineCurveMap r θ (surfaceMap (firstEquations r θ) (X (some 1))) =
      Ideal.Quotient.mk (CycleQ2GeometricAffineCurveCharts.chartIdeal
        ![CycleQ2GeometricAffineCurveCharts.firstQuadric r,
          CycleQ2GeometricAffineCurveCharts.firstCubic θ]) (X (1 : Fin 3)) := by
  change Ideal.Quotient.mk _ (setNormalZero (X (some 1))) = _
  simp only [setNormalZero, aeval_X]

/-- Actual restriction of the surface coordinate section along the closed immersion. -/
theorem firstCoordinate_pullback (r θ : ℂ) :
    coordinateSectionMap r θ 1 (firstSurfaceCoordinateSection r θ) =
      firstCurveRatioSection r θ := by
  apply (CycleQ2GeometricAffineProjectiveCharts.firstSectionsEquiv r θ).injective
  have h := firstSectionsEquiv_curveMap r θ (firstSurfaceCoordinateSection r θ)
  have he := (CycleQ2GeometricSurfaceDehomogenizedCharts.firstSectionsEquiv r θ).apply_symm_apply
    (surfaceMap (firstEquations r θ) (X (some 1)))
  exact h.trans ((congrArg (firstAffineCurveMap r θ) he).trans
    ((firstAffineCurveMap_coordinate r θ).trans (curve_ratio_coordinate r θ).symm))

theorem coordinateSection_restrict_first (r θ : ℂ)
    (V : (projectiveSurface r θ).Opens) (hV : V ≤ overlapPatch r θ) :
    coordinateSection r θ V hV =
      (projectiveSurface r θ).presheaf.map
        (homOfLE (hV.trans (overlap_le_first r θ))).op (firstSurfaceCoordinateSection r θ) := by
  have h := overlapSectionMap_first r θ V hV
    (surfaceMap (firstEquations r θ) (X (some 1)))
  exact h.trans (CycleQ2GeometricSurfaceOverlap.first_chartSection_subopen r θ
    (Over.mk (homOfLE (hV.trans (overlap_le_first r θ))))
    (surfaceMap (firstEquations r θ) (X (some 1))))

/-- The same first-coordinate ratio on the original quartic denominator overlap. -/
theorem firstCurveRatio_restrict_quartic (r θ : ℂ) :
    (projectiveCurve r θ).presheaf.map
        (homOfLE (denominatorOverlap_le_firstCoordinate r θ)).op
        (firstCurveRatioSection r θ) =
      (projectiveTransitionUnit r θ : Γ(projectiveCurve r θ, overlapProjectivePatch r θ)) :=
  (firstToDenominatorOverlap_is_sheaf_restriction r θ
    (CycleQ2GeometricProjectiveAffine.coordinateRatio r θ 1 2)).trans
    (congrArg ((overlapProjectiveSectionsIso r θ).hom)
      (firstToDenominatorOverlap_ratio r θ))

def curveRestriction (r θ : ℂ) (W : (projectiveCurve r θ).Opens)
    (hW : W ≤ overlapProjectivePatch r θ) :
    Γ(projectiveCurve r θ, overlapProjectivePatch r θ) →+* Γ(projectiveCurve r θ, W) :=
  ((projectiveCurve r θ).presheaf.map (homOfLE hW).op).hom

def curvePullback (r θ : ℂ) (V : (projectiveSurface r θ).Opens)
    (W : (projectiveCurve r θ).Opens)
    (hWV : W ≤ CycleQ2GeometricLiteralSurface.curveToSurface r θ ⁻¹ᵁ V) :
    Γ(projectiveSurface r θ, V) →+* Γ(projectiveCurve r θ, W) :=
  ((CycleQ2GeometricLiteralSurface.curveToSurface r θ).appLE V W hWV).hom

/-- Both restrictions meet on the actual curve subopen W; no equality of
surface-coordinate and curve-quartic overlaps is assumed. -/
theorem coordinateSection_pullback (r θ : ℂ)
    (V : (projectiveSurface r θ).Opens) (hV : V ≤ overlapPatch r θ)
    (W : (projectiveCurve r θ).Opens) (hW : W ≤ overlapProjectivePatch r θ)
    (hWV : W ≤ CycleQ2GeometricLiteralSurface.curveToSurface r θ ⁻¹ᵁ V) :
    curvePullback r θ V W hWV (coordinateSection r θ V hV) =
      curveRestriction r θ W hW
        (projectiveTransitionUnit r θ : Γ(projectiveCurve r θ, overlapProjectivePatch r θ)) := by
  let hW₁ := hW.trans (denominatorOverlap_le_firstCoordinate r θ)
  have hs := pullback_restriction_square (CycleQ2GeometricLiteralSurface.curveToSurface r θ)
    (hV.trans (overlap_le_first r θ))
    (show coordinateProjectivePatch r θ 1 ≤
      CycleQ2GeometricLiteralSurface.curveToSurface r θ ⁻¹ᵁ coordinatePatch r θ 1 from
        (coordinateCurvePreimage r θ (1 : Fin 4)).symm.le) hW₁ hWV (firstSurfaceCoordinateSection r θ)
  calc
    _ = (CycleQ2GeometricLiteralSurface.curveToSurface r θ).appLE V W hWV
        ((projectiveSurface r θ).presheaf.map
          (homOfLE (hV.trans (overlap_le_first r θ))).op (firstSurfaceCoordinateSection r θ)) :=
      congrArg (curvePullback r θ V W hWV) (coordinateSection_restrict_first r θ V hV)
    _ = (projectiveCurve r θ).presheaf.map (homOfLE hW₁).op
        (coordinateSectionMap r θ 1 (firstSurfaceCoordinateSection r θ)) := hs
    _ = (projectiveCurve r θ).presheaf.map (homOfLE hW₁).op (firstCurveRatioSection r θ) :=
      congrArg ((projectiveCurve r θ).presheaf.map (homOfLE hW₁).op)
        (firstCoordinate_pullback r θ)
    _ = curveRestriction r θ W hW
        ((projectiveCurve r θ).presheaf.map
          (homOfLE (denominatorOverlap_le_firstCoordinate r θ)).op (firstCurveRatioSection r θ)) :=
      (restriction_comp (denominatorOverlap_le_firstCoordinate r θ) hW
        (firstCurveRatioSection r θ)).symm
    _ = _ := congrArg (curveRestriction r θ W hW) (firstCurveRatio_restrict_quartic r θ)

private theorem inverse_unique {R : Type} [CommRing R] (u : Rˣ) (x : R)
    (h : (u : R) * x = 1) : x = (↑(u⁻¹) : R) :=
  u.isUnit.mul_left_cancel (h.trans u.val_inv.symm)

theorem inverseSection_pullback (r θ : ℂ)
    (V : (projectiveSurface r θ).Opens) (hV : V ≤ overlapPatch r θ)
    (W : (projectiveCurve r θ).Opens) (hW : W ≤ overlapProjectivePatch r θ)
    (hWV : W ≤ CycleQ2GeometricLiteralSurface.curveToSurface r θ ⁻¹ᵁ V) :
    curvePullback r θ V W hWV (inverseSection r θ V hV) =
      curveRestriction r θ W hW
        (↑((projectiveTransitionUnit r θ)⁻¹) : Γ(projectiveCurve r θ, overlapProjectivePatch r θ)) := by
  let u : Γ(projectiveCurve r θ, W)ˣ := Units.map (curveRestriction r θ W hW).toMonoidHom
    (projectiveTransitionUnit r θ)
  have hc := coordinateSection_pullback r θ V hV W hW hWV
  have hm : curvePullback r θ V W hWV (coordinateSection r θ V hV) *
      curvePullback r θ V W hWV (inverseSection r θ V hV) = 1 :=
    (map_mul (curvePullback r θ V W hWV) _ _).symm.trans
      ((congrArg (curvePullback r θ V W hWV)
        (coordinateSection_mul_inverseSection r θ V hV)).trans (map_one _))
  exact inverse_unique u _
    ((congrArg (fun z : Γ(projectiveCurve r θ, W) =>
      z * curvePullback r θ V W hWV (inverseSection r θ V hV)) hc).symm.trans hm)

/-- The genuine normal-frame coefficient is exactly the old normal
transition, restricted to the same actual curve subopen. -/
theorem normalTransition_pullback (r θ : ℂ)
    (V : (projectiveSurface r θ).Opens) (hV : V ≤ overlapPatch r θ)
    (W : (projectiveCurve r θ).Opens) (hW : W ≤ overlapProjectivePatch r θ)
    (hWV : W ≤ CycleQ2GeometricLiteralSurface.curveToSurface r θ ⁻¹ᵁ V) :
    curvePullback r θ V W hWV (inverseSection r θ V hV ^ 2) =
      curveRestriction r θ W hW
        (normalTransitionUnit r θ : Γ(projectiveCurve r θ, overlapProjectivePatch r θ)) := by
  exact (map_pow (curvePullback r θ V W hWV) _ 2).trans
    ((congrArg (fun z : Γ(projectiveCurve r θ, W) => z ^ 2)
      (inverseSection_pullback r θ V hV W hW hWV)).trans
      (map_pow (curveRestriction r θ W hW) _ 2).symm)

def inverseSectionUnit (r θ : ℂ) (V : (projectiveSurface r θ).Opens)
    (hV : V ≤ overlapPatch r θ) : Γ(projectiveSurface r θ, V)ˣ :=
  (inverseSection_isUnit r θ V hV).unit

theorem inverseSectionUnit_value (r θ : ℂ) (V : (projectiveSurface r θ).Opens)
    (hV : V ≤ overlapPatch r θ) :
    (inverseSectionUnit r θ V hV : Γ(projectiveSurface r θ, V)) = inverseSection r θ V hV :=
  (inverseSection_isUnit r θ V hV).unit_spec

theorem normalTransitionUnit_pullback (r θ : ℂ)
    (V : (projectiveSurface r θ).Opens) (hV : V ≤ overlapPatch r θ)
    (W : (projectiveCurve r θ).Opens) (hW : W ≤ overlapProjectivePatch r θ)
    (hWV : W ≤ CycleQ2GeometricLiteralSurface.curveToSurface r θ ⁻¹ᵁ V) :
    Units.map (curvePullback r θ V W hWV).toMonoidHom (inverseSectionUnit r θ V hV ^ 2) =
      Units.map (curveRestriction r θ W hW).toMonoidHom (normalTransitionUnit r θ) := by
  apply Units.ext
  change curvePullback r θ V W hWV ((inverseSectionUnit r θ V hV).val ^ 2) = _
  rw [inverseSectionUnit_value]
  exact normalTransition_pullback r θ V hV W hW hWV

end CycleQ2NormalTransitionBinding
end

end


section

/-! The original normal vectors on actual projective chart overlaps. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2ProjectiveNormalTransition

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite MvPolynomial
open CycleQ2GeometricLiteralSurface CycleQ2GeometricNormalCharts
open CycleQ2GeometricIntrinsicNormal CycleQ2GeometricSurfaceAdjunction
open CycleQ2GeometricSurfaceJacobianCharts CycleQ2GeometricSurfacePrincipalCurveCharts
open CycleQ2GeometricSurfaceDehomogenizedCharts CycleQ2GeometricSurfaceOverlap
open CycleQ2GeometricAffineChartSections CycleQ2GeometricAffineCurveCharts
open CycleQ2NormalChartSections CycleQ2NormalVectorEvaluation
open CycleQ2SourceNormalVectors CycleQ2SourceNormalSheaf
open CycleQ2SeedTrace CycleQ2NormalConnecting CycleQ2CartierProjectiveCover
open CycleQ2SurfaceOverlapSections

local instance actualNormalSectionModule (r θ : ℂ) (V : (surface r θ).Opens) :
    Module Γ(surface r θ, V) ((normalDirectImageSheaf (curveToSurface r θ)).val.obj (op V)) :=
  ((normalDirectImageSheaf (curveToSurface r θ)).val.obj (op V)).isModule

section EvaluationScalar

variable {X Y : Scheme.{0}} (j : X ⟶ Y) (V : Y.Opens)

local instance normalSectionModule :
    Module Γ(Y, V) ((normalDirectImageSheaf j).val.obj (op V)) :=
  ((normalDirectImageSheaf j).val.obj (op V)).isModule

local instance imageSectionModule :
    Module Γ(Y, V) ((imageStructureModule j).val.obj (op V)) :=
  ((imageStructureModule j).val.obj (op V)).isModule

/-- Scaling both the actual normal functional and its original ideal
argument uses the square of the same genuine section coefficient. -/
theorem scaledEquationEvaluation (c : Γ(Y, V))
    (f : (normalDirectImageSheaf j).val.obj (op V))
    (a : RingHom.ker (j.app V).hom) :
    normalSectionEvaluate j V (c • f) (c • a) =
      c ^ 2 • normalSectionEvaluate j V f a := by
  have h := LinearMap.congr_fun ((normalSectionEvaluationLinearMap j V).map_smul c f) (c • a)
  change normalSectionEvaluate j V (c • f) (c • a) =
    c • normalSectionEvaluate j V f (c • a) at h
  exact h.trans ((congrArg (fun z : (imageStructureModule j).val.obj (op V) => c • z)
    ((normalSectionEvaluate j V f).map_smul c a)).trans (by
      rw [smul_smul, pow_two]))

theorem scaledEquationEvaluation_coefficient (c d : Γ(Y, V))
    (f : (normalDirectImageSheaf j).val.obj (op V))
    (a : RingHom.ker (j.app V).hom)
    (hf : normalSectionEvaluate j V f a = j.app V d) :
    normalSectionEvaluate j V (c • f) (c • a) = j.app V (c ^ 2 * d) := by
  have h := scaledEquationEvaluation j V c f a
  have hs₁ := congrArg (fun z : (imageStructureModule j).val.obj (op V) => c ^ 2 • z) hf
  have hs₂ : c ^ 2 • (show (imageStructureModule j).val.obj (op V) from j.app V d) =
      j.app V (c ^ 2 * d) := by
    change j.app V (c ^ 2) * j.app V d = _
    exact (map_mul (j.app V).hom (c ^ 2) d).symm
  exact h.trans (hs₁.trans hs₂)

end EvaluationScalar

/-- Generic typed transport keeps the actual section and original ideal
argument explicit while passing from normalized affine values to the
chosen structure-sheaf coefficient. -/
private theorem normalizedValue_with_coordinates
    {A B : CommRingCat.{0}} (φ : A ⟶ B)
    {X Y : Scheme.{0}} (j : X ⟶ Y) (v : Spec A ⟶ Y) (u : Spec B ⟶ X)
    [IsOpenImmersion v] [IsOpenImmersion u]
    (H : IsPullback (Spec.map φ) u v j)
    (f : (normalDirectImageSheaf j).val.obj (op v.opensRange))
    (a : RingHom.ker φ.hom) (b : A)
    (hf : normalOpenIdealValue φ j v u H f a = φ b)
    (V : Y.Opens) (hV : V ≤ v.opensRange)
    (fV : (normalDirectImageSheaf j).val.obj (op V))
    (aV : RingHom.ker (j.app V).hom)
    (hfV : fV = (normalDirectImageSheaf j).val.map (homOfLE hV).op f)
    (haV : aV = idealOnSubopen φ j v u H V hV a)
    (c : Γ(Y, V)) (hc : coefficientOnSubopen v V hV b = c) :
    (normalSectionEvaluate j V fV).toFun aV = j.app V c := by
  subst fV
  subst aV
  exact (normalizedValue_subopen φ j v u H f a b hf V hV).trans
    (congrArg (fun z : Γ(Y, V) =>
      (show (imageStructureModule j).val.obj (op V) from j.app V z)) hc)

private theorem normalIndexCases (a : Fin 2) : a = 0 ∨ a = 1 := by
  fin_cases a <;> simp

def weightedEquation (r : ℂ) (a : Fin 2) : WeightedPoly := ![originalF1 r, originalF2] a
def weightedValue (r : ℂ) (a : Fin 2) : WeightedPoly := ![originalG2, -originalG1 r] a

theorem weightedEquation_homogeneous (r : ℂ) (a : Fin 2) :
    (weightedEquation r a).IsWeightedHomogeneous CycleQ2CartierSurfaceGrading.weight 2 := by
  rcases normalIndexCases a with rfl | rfl
  · exact CycleQ2CartierSurfaceGrading.originalF1_homogeneous r
  · exact CycleQ2CartierSurfaceGrading.originalF2_homogeneous

theorem weightedValue_homogeneous (r : ℂ) (a : Fin 2) :
    (weightedValue r a).IsWeightedHomogeneous CycleQ2CartierSurfaceGrading.weight 4 := by
  rcases normalIndexCases a with rfl | rfl
  · exact CycleQ2CartierSurfaceGrading.originalG2_homogeneous
  · exact (CycleQ2CartierSurfaceGrading.originalG1_homogeneous r).neg

theorem firstDehom_equation (r : ℂ) (a : Fin 2) :
    firstSurfaceDehomogenize (weightedEquation r a) = normalPolynomial (firstQuadric r) a := by
  rcases normalIndexCases a with rfl | rfl <;> simp only [weightedEquation, normalPolynomial, Matrix.cons_val_zero,
    Matrix.cons_val_one, firstSurfaceDehomogenize_f1, firstSurfaceDehomogenize_f2]

theorem secondDehom_equation (r : ℂ) (a : Fin 2) :
    secondSurfaceDehomogenize (weightedEquation r a) = normalPolynomial (secondQuadric r) a := by
  rcases normalIndexCases a with rfl | rfl <;> simp only [weightedEquation, normalPolynomial, Matrix.cons_val_zero,
    Matrix.cons_val_one, secondSurfaceDehomogenize_f1, secondSurfaceDehomogenize_f2]

theorem firstDehom_value (r : ℂ) (a : Fin 2) :
    firstSurfaceDehomogenize (weightedValue r a) =
      ![firstSurfaceDehomogenize originalG2, -firstSurfaceDehomogenize (originalG1 r)] a := by
  rcases normalIndexCases a with rfl | rfl <;> simp only [weightedValue, Matrix.cons_val_zero, Matrix.cons_val_one, map_neg]

theorem secondDehom_value (r : ℂ) (a : Fin 2) :
    secondSurfaceDehomogenize (weightedValue r a) =
      ![secondSurfaceDehomogenize originalG2, -secondSurfaceDehomogenize (originalG1 r)] a := by
  rcases normalIndexCases a with rfl | rfl <;> simp only [weightedValue, Matrix.cons_val_zero, Matrix.cons_val_one, map_neg]

def firstPolynomialSection (r θ : ℂ) (V : (surface r θ).Opens)
    (hV : V ≤ coordinatePatch r θ 1) : WeightedPoly →+* Γ(surface r θ, V) :=
  (chartSection (firstAffineChart r θ) (Over.mk (homOfLE hV))).comp
    ((surfaceMap (firstEquations r θ)).toRingHom.comp firstSurfaceDehomogenize.toRingHom)

def secondPolynomialSection (r θ : ℂ) (V : (surface r θ).Opens)
    (hV : V ≤ coordinatePatch r θ 2) : WeightedPoly →+* Γ(surface r θ, V) :=
  (chartSection (secondAffineChart r θ) (Over.mk (homOfLE hV))).comp
    ((surfaceMap (secondEquations r θ)).toRingHom.comp secondSurfaceDehomogenize.toRingHom)

theorem firstCoefficient_polynomial (r θ : ℂ) (i : Fin 2) (a : Fin 3)
    (V : (surface r θ).Opens) (hV : V ≤ firstNormalOpen r θ i a) (p : SurfacePoly) :
    coefficientOnSubopen (firstNormalSurfaceImmersion r θ i a) V hV
        (algebraMap SurfacePoly (FirstNormalRing r θ i a) p) =
      chartSection (firstAffineChart r θ)
        (Over.mk (homOfLE (hV.trans (firstNormalOpen_le r θ i a))))
        (surfaceMap (firstEquations r θ) p) :=
  (coefficientOnSubopen_chartSection (firstNormalChart r θ i a)
    (firstNormalSurfaceImmersion r θ i a)
    (principalChart_inv_ι (firstAffineChart r θ) (firstJacobian r θ i a)) V hV hV _).trans
      (firstNormal_chartSection r θ i a (Over.mk (homOfLE hV))
        (surfaceMap (firstEquations r θ) p))

abbrev firstVectorOn (r θ : ℂ) (i : Fin 2) (a : Fin 3)
    (V : (surface r θ).Opens) (hV : V ≤ firstNormalOpen r θ i a) :
    (normalDirectImageSheaf (curveToSurface r θ)).val.obj (op V) :=
  (normalDirectImageSheaf (curveToSurface r θ)).val.map (homOfLE hV).op
    (firstNormalVectorSection r θ i a)

abbrev firstIdealOn (r θ : ℂ) (i : Fin 2) (a : Fin 3)
    (V : (surface r θ).Opens) (hV : V ≤ firstNormalOpen r θ i a) (b : Fin 2) :
    RingHom.ker ((curveToSurface r θ).app V).hom :=
  idealOnSubopen (CommRingCat.ofHom (firstNormalCurveMap r θ i a).toRingHom)
    (curveToSurface r θ) (firstNormalSurfaceImmersion r θ i a)
    (firstNormalCurveImmersion r θ i a) (firstNormalCurve_isPullback r θ i a)
    V hV (firstNormalIdealEquation r θ i a b)

theorem firstIdealOn_coe (r θ : ℂ) (i : Fin 2) (a : Fin 3)
    (V : (surface r θ).Opens) (hV : V ≤ firstNormalOpen r θ i a) (b : Fin 2) :
    (firstIdealOn r θ i a V hV b : Γ(surface r θ, V)) =
      firstPolynomialSection r θ V (hV.trans (firstNormalOpen_le r θ i a))
        (weightedEquation r b) := by
  have h₁ := idealOnSubopen_coe
    (CommRingCat.ofHom (firstNormalCurveMap r θ i a).toRingHom)
    (curveToSurface r θ) (firstNormalSurfaceImmersion r θ i a)
    (firstNormalCurveImmersion r θ i a) (firstNormalCurve_isPullback r θ i a)
    V hV (firstNormalIdealEquation r θ i a b)
  have h₂ := firstCoefficient_polynomial r θ i a V hV (normalPolynomial (firstQuadric r) b)
  exact h₁.trans (h₂.trans
    (congrArg (fun p : SurfacePoly => chartSection (firstAffineChart r θ)
      (Over.mk (homOfLE (hV.trans (firstNormalOpen_le r θ i a))))
      (surfaceMap (firstEquations r θ) p)) (firstDehom_equation r b).symm))

theorem firstVectorOn_value (r θ : ℂ) (i : Fin 2) (a : Fin 3)
    (V : (surface r θ).Opens) (hV : V ≤ firstNormalOpen r θ i a) (b : Fin 2) :
    normalSectionEvaluate (curveToSurface r θ) V (firstVectorOn r θ i a V hV)
        (firstIdealOn r θ i a V hV b) =
      (curveToSurface r θ).app V
        (firstPolynomialSection r θ V (hV.trans (firstNormalOpen_le r θ i a))
          (weightedValue r b)) := by
  have hb : firstNormalCurveMap r θ i a
      (algebraMap SurfacePoly (FirstNormalRing r θ i a)
        (![firstSurfaceDehomogenize originalG2, -firstSurfaceDehomogenize (originalG1 r)] b)) =
      ![normalCoefficientMap (firstQuadric r) (firstCubic θ)
          (firstSurfaceDehomogenize (originalG1 r)) (firstSurfaceDehomogenize originalG2)
          (firstSurfaceDehomogenize (thetaK θ)) i a (firstSurfaceDehomogenize originalG2),
        -normalCoefficientMap (firstQuadric r) (firstCubic θ)
          (firstSurfaceDehomogenize (originalG1 r)) (firstSurfaceDehomogenize originalG2)
          (firstSurfaceDehomogenize (thetaK θ)) i a (firstSurfaceDehomogenize (originalG1 r))] b := by
    exact (normalAlgebraMap_polynomial (firstQuadric r) (firstCubic θ)
      (firstSurfaceDehomogenize (originalG1 r)) (firstSurfaceDehomogenize originalG2)
      (firstSurfaceDehomogenize (thetaK θ)) i a _).trans (by
        rcases normalIndexCases b with rfl | rfl
        · rfl
        · exact map_neg _ _)
  have hn := (firstNormalVectorSection_equation r θ i a b).trans hb.symm
  dsimp only [firstNormalEquationValue, normalChartEquationValue] at hn
  have h₂ := firstCoefficient_polynomial r θ i a V hV
    (![firstSurfaceDehomogenize originalG2, -firstSurfaceDehomogenize (originalG1 r)] b)
  have h₃ := congrArg (fun p : SurfacePoly => chartSection (firstAffineChart r θ)
      (Over.mk (homOfLE (hV.trans (firstNormalOpen_le r θ i a))))
      (surfaceMap (firstEquations r θ) p)) (firstDehom_value r b).symm
  have hc : coefficientOnSubopen (firstNormalSurfaceImmersion r θ i a) V hV
      (algebraMap SurfacePoly (FirstNormalRing r θ i a)
        (![firstSurfaceDehomogenize originalG2, -firstSurfaceDehomogenize (originalG1 r)] b)) =
      firstPolynomialSection r θ V (hV.trans (firstNormalOpen_le r θ i a))
        (weightedValue r b) := h₂.trans h₃
  exact normalizedValue_with_coordinates
    (CommRingCat.ofHom (firstNormalCurveMap r θ i a).toRingHom)
    (curveToSurface r θ) (firstNormalSurfaceImmersion r θ i a)
    (firstNormalCurveImmersion r θ i a) (firstNormalCurve_isPullback r θ i a)
    (firstNormalVectorSection r θ i a) (firstNormalIdealEquation r θ i a b)
    (algebraMap SurfacePoly (FirstNormalRing r θ i a)
      (![firstSurfaceDehomogenize originalG2, -firstSurfaceDehomogenize (originalG1 r)] b))
    hn V hV (firstVectorOn r θ i a V hV) (firstIdealOn r θ i a V hV b) rfl rfl
    (firstPolynomialSection r θ V (hV.trans (firstNormalOpen_le r θ i a)) (weightedValue r b)) hc

theorem firstVectorOn_ext (r θ : ℂ) (i : Fin 2) (a : Fin 3)
    (V : (surface r θ).Opens) (hV : V ≤ firstNormalOpen r θ i a)
    (f g : (normalDirectImageSheaf (curveToSurface r θ)).val.obj (op V))
    (hfg : ∀ b, normalSectionEvaluate (curveToSurface r θ) V f (firstIdealOn r θ i a V hV b) =
      normalSectionEvaluate (curveToSurface r θ) V g (firstIdealOn r θ i a V hV b)) : f = g :=
  normal_ext_on_subopen (CommRingCat.ofHom (firstNormalCurveMap r θ i a).toRingHom)
    (curveToSurface r θ) (firstNormalSurfaceImmersion r θ i a)
    (firstNormalCurveImmersion r θ i a) (firstNormalCurve_isPullback r θ i a)
    (firstNormalIdealEquation r θ i a)
    (CycleQ2AffineNormalPatchExt.equationGenerators_span (firstQuadric r) (firstCubic θ)
      (firstSurfaceDehomogenize (originalG1 r)) (firstSurfaceDehomogenize originalG2)
      (firstSurfaceDehomogenize (thetaK θ)) i a) V hV f g hfg

theorem secondCoefficient_polynomial (r θ : ℂ) (i : Fin 2) (a : Fin 3)
    (V : (surface r θ).Opens) (hV : V ≤ secondNormalOpen r θ i a) (p : SurfacePoly) :
    coefficientOnSubopen (secondNormalSurfaceImmersion r θ i a) V hV
        (algebraMap SurfacePoly (SecondNormalRing r θ i a) p) =
      chartSection (secondAffineChart r θ)
        (Over.mk (homOfLE (hV.trans (secondNormalOpen_le r θ i a))))
        (surfaceMap (secondEquations r θ) p) :=
  (coefficientOnSubopen_chartSection (secondNormalChart r θ i a)
    (secondNormalSurfaceImmersion r θ i a)
    (principalChart_inv_ι (secondAffineChart r θ) (secondJacobian r θ i a)) V hV hV _).trans
      (secondNormal_chartSection r θ i a (Over.mk (homOfLE hV))
        (surfaceMap (secondEquations r θ) p))

abbrev secondVectorOn (r θ : ℂ) (i : Fin 2) (a : Fin 3)
    (V : (surface r θ).Opens) (hV : V ≤ secondNormalOpen r θ i a) :
    (normalDirectImageSheaf (curveToSurface r θ)).val.obj (op V) :=
  (normalDirectImageSheaf (curveToSurface r θ)).val.map (homOfLE hV).op
    (secondNormalVectorSection r θ i a)

abbrev secondIdealOn (r θ : ℂ) (i : Fin 2) (a : Fin 3)
    (V : (surface r θ).Opens) (hV : V ≤ secondNormalOpen r θ i a) (b : Fin 2) :
    RingHom.ker ((curveToSurface r θ).app V).hom :=
  idealOnSubopen (CommRingCat.ofHom (secondNormalCurveMap r θ i a).toRingHom)
    (curveToSurface r θ) (secondNormalSurfaceImmersion r θ i a)
    (secondNormalCurveImmersion r θ i a) (secondNormalCurve_isPullback r θ i a)
    V hV (secondNormalIdealEquation r θ i a b)

theorem secondIdealOn_coe (r θ : ℂ) (i : Fin 2) (a : Fin 3)
    (V : (surface r θ).Opens) (hV : V ≤ secondNormalOpen r θ i a) (b : Fin 2) :
    (secondIdealOn r θ i a V hV b : Γ(surface r θ, V)) =
      secondPolynomialSection r θ V (hV.trans (secondNormalOpen_le r θ i a))
        (weightedEquation r b) := by
  have h₁ := idealOnSubopen_coe
    (CommRingCat.ofHom (secondNormalCurveMap r θ i a).toRingHom)
    (curveToSurface r θ) (secondNormalSurfaceImmersion r θ i a)
    (secondNormalCurveImmersion r θ i a) (secondNormalCurve_isPullback r θ i a)
    V hV (secondNormalIdealEquation r θ i a b)
  have h₂ := secondCoefficient_polynomial r θ i a V hV (normalPolynomial (secondQuadric r) b)
  exact h₁.trans (h₂.trans
    (congrArg (fun p : SurfacePoly => chartSection (secondAffineChart r θ)
      (Over.mk (homOfLE (hV.trans (secondNormalOpen_le r θ i a))))
      (surfaceMap (secondEquations r θ) p)) (secondDehom_equation r b).symm))

theorem secondVectorOn_value (r θ : ℂ) (i : Fin 2) (a : Fin 3)
    (V : (surface r θ).Opens) (hV : V ≤ secondNormalOpen r θ i a) (b : Fin 2) :
    normalSectionEvaluate (curveToSurface r θ) V (secondVectorOn r θ i a V hV)
        (secondIdealOn r θ i a V hV b) =
      (curveToSurface r θ).app V
        (secondPolynomialSection r θ V (hV.trans (secondNormalOpen_le r θ i a))
          (weightedValue r b)) := by
  have hb : secondNormalCurveMap r θ i a
      (algebraMap SurfacePoly (SecondNormalRing r θ i a)
        (![secondSurfaceDehomogenize originalG2, -secondSurfaceDehomogenize (originalG1 r)] b)) =
      ![normalCoefficientMap (secondQuadric r) (secondCubic θ)
          (secondSurfaceDehomogenize (originalG1 r)) (secondSurfaceDehomogenize originalG2)
          (secondSurfaceDehomogenize (thetaK θ)) i a (secondSurfaceDehomogenize originalG2),
        -normalCoefficientMap (secondQuadric r) (secondCubic θ)
          (secondSurfaceDehomogenize (originalG1 r)) (secondSurfaceDehomogenize originalG2)
          (secondSurfaceDehomogenize (thetaK θ)) i a (secondSurfaceDehomogenize (originalG1 r))] b := by
    exact (normalAlgebraMap_polynomial (secondQuadric r) (secondCubic θ)
      (secondSurfaceDehomogenize (originalG1 r)) (secondSurfaceDehomogenize originalG2)
      (secondSurfaceDehomogenize (thetaK θ)) i a _).trans (by
        rcases normalIndexCases b with rfl | rfl
        · rfl
        · exact map_neg _ _)
  have hn := (secondNormalVectorSection_equation r θ i a b).trans hb.symm
  dsimp only [secondNormalEquationValue, normalChartEquationValue] at hn
  have h₂ := secondCoefficient_polynomial r θ i a V hV
    (![secondSurfaceDehomogenize originalG2, -secondSurfaceDehomogenize (originalG1 r)] b)
  have h₃ := congrArg (fun p : SurfacePoly => chartSection (secondAffineChart r θ)
      (Over.mk (homOfLE (hV.trans (secondNormalOpen_le r θ i a))))
      (surfaceMap (secondEquations r θ) p)) (secondDehom_value r b).symm
  have hc : coefficientOnSubopen (secondNormalSurfaceImmersion r θ i a) V hV
      (algebraMap SurfacePoly (SecondNormalRing r θ i a)
        (![secondSurfaceDehomogenize originalG2, -secondSurfaceDehomogenize (originalG1 r)] b)) =
      secondPolynomialSection r θ V (hV.trans (secondNormalOpen_le r θ i a))
        (weightedValue r b) := h₂.trans h₃
  exact normalizedValue_with_coordinates
    (CommRingCat.ofHom (secondNormalCurveMap r θ i a).toRingHom)
    (curveToSurface r θ) (secondNormalSurfaceImmersion r θ i a)
    (secondNormalCurveImmersion r θ i a) (secondNormalCurve_isPullback r θ i a)
    (secondNormalVectorSection r θ i a) (secondNormalIdealEquation r θ i a b)
    (algebraMap SurfacePoly (SecondNormalRing r θ i a)
      (![secondSurfaceDehomogenize originalG2, -secondSurfaceDehomogenize (originalG1 r)] b))
    hn V hV (secondVectorOn r θ i a V hV) (secondIdealOn r θ i a V hV b) rfl rfl
    (secondPolynomialSection r θ V (hV.trans (secondNormalOpen_le r θ i a)) (weightedValue r b)) hc

theorem secondVectorOn_ext (r θ : ℂ) (i : Fin 2) (a : Fin 3)
    (V : (surface r θ).Opens) (hV : V ≤ secondNormalOpen r θ i a)
    (f g : (normalDirectImageSheaf (curveToSurface r θ)).val.obj (op V))
    (hfg : ∀ b, normalSectionEvaluate (curveToSurface r θ) V f (secondIdealOn r θ i a V hV b) =
      normalSectionEvaluate (curveToSurface r θ) V g (secondIdealOn r θ i a V hV b)) : f = g :=
  normal_ext_on_subopen (CommRingCat.ofHom (secondNormalCurveMap r θ i a).toRingHom)
    (curveToSurface r θ) (secondNormalSurfaceImmersion r θ i a)
    (secondNormalCurveImmersion r θ i a) (secondNormalCurve_isPullback r θ i a)
    (secondNormalIdealEquation r θ i a)
    (CycleQ2AffineNormalPatchExt.equationGenerators_span (secondQuadric r) (secondCubic θ)
      (secondSurfaceDehomogenize (originalG1 r)) (secondSurfaceDehomogenize originalG2)
      (secondSurfaceDehomogenize (thetaK θ)) i a) V hV f g hfg

/-- On two first-coordinate Jacobian patches, the fixed normal vectors
agree as actual normal-sheaf sections on every common subopen. -/
theorem firstVectors_agree (r θ : ℂ) (i₁ i₂ : Fin 2) (a₁ a₂ : Fin 3)
    (V : (surface r θ).Opens) (h₁ : V ≤ firstNormalOpen r θ i₁ a₁)
    (h₂ : V ≤ firstNormalOpen r θ i₂ a₂) :
    firstVectorOn r θ i₁ a₁ V h₁ = firstVectorOn r θ i₂ a₂ V h₂ := by
  apply firstVectorOn_ext r θ i₁ a₁ V h₁
  intro b
  have he : firstIdealOn r θ i₁ a₁ V h₁ b = firstIdealOn r θ i₂ a₂ V h₂ b :=
    Subtype.ext ((firstIdealOn_coe r θ i₁ a₁ V h₁ b).trans
      (firstIdealOn_coe r θ i₂ a₂ V h₂ b).symm)
  exact (firstVectorOn_value r θ i₁ a₁ V h₁ b).trans
    ((firstVectorOn_value r θ i₂ a₂ V h₂ b).symm.trans
      (congrArg (normalSectionEvaluate (curveToSurface r θ) V
        (firstVectorOn r θ i₂ a₂ V h₂)) he.symm))

/-- The same compatibility holds throughout the second-coordinate family. -/
theorem secondVectors_agree (r θ : ℂ) (i₁ i₂ : Fin 2) (a₁ a₂ : Fin 3)
    (V : (surface r θ).Opens) (h₁ : V ≤ secondNormalOpen r θ i₁ a₁)
    (h₂ : V ≤ secondNormalOpen r θ i₂ a₂) :
    secondVectorOn r θ i₁ a₁ V h₁ = secondVectorOn r θ i₂ a₂ V h₂ := by
  apply secondVectorOn_ext r θ i₁ a₁ V h₁
  intro b
  have he : secondIdealOn r θ i₁ a₁ V h₁ b = secondIdealOn r θ i₂ a₂ V h₂ b :=
    Subtype.ext ((secondIdealOn_coe r θ i₁ a₁ V h₁ b).trans
      (secondIdealOn_coe r θ i₂ a₂ V h₂ b).symm)
  exact (secondVectorOn_value r θ i₁ a₁ V h₁ b).trans
    ((secondVectorOn_value r θ i₂ a₂ V h₂ b).symm.trans
      (congrArg (normalSectionEvaluate (curveToSurface r θ) V
        (secondVectorOn r θ i₂ a₂ V h₂)) he.symm))

def firstSourceOn (r θ : ℂ) (i : Fin 2) (a : Fin 3)
    (V : (surface r θ).Opens) (hV : V ≤ firstNormalOpen r θ i a) :
    Γ(actualNormal r θ, curveToSurface r θ ⁻¹ᵁ V) :=
  (actualNormal r θ).presheaf.map
    ((Opens.map (curveToSurface r θ).base).map (homOfLE hV)).op
      (firstSourceNormalVector r θ i a)

def secondSourceOn (r θ : ℂ) (i : Fin 2) (a : Fin 3)
    (V : (surface r θ).Opens) (hV : V ≤ secondNormalOpen r θ i a) :
    Γ(actualNormal r θ, curveToSurface r θ ⁻¹ᵁ V) :=
  (actualNormal r θ).presheaf.map
    ((Opens.map (curveToSurface r θ).base).map (homOfLE hV)).op
      (secondSourceNormalVector r θ i a)

theorem firstSourceOn_comparison (r θ : ℂ) (i : Fin 2) (a : Fin 3)
    (V : (surface r θ).Opens) (hV : V ≤ firstNormalOpen r θ i a) :
    sectionEquiv (curveToSurface r θ) V (firstSourceOn r θ i a V hV) =
      firstVectorOn r θ i a V hV :=
  (sectionEquiv_restrict (curveToSurface r θ) (homOfLE hV)
    (firstSourceNormalVector r θ i a)).trans
    (congrArg ((normalDirectImageSheaf (curveToSurface r θ)).val.map (homOfLE hV).op)
      ((sectionEquiv (curveToSurface r θ) (firstNormalOpen r θ i a)).apply_symm_apply
        (firstNormalVectorSection r θ i a)))

theorem secondSourceOn_comparison (r θ : ℂ) (i : Fin 2) (a : Fin 3)
    (V : (surface r θ).Opens) (hV : V ≤ secondNormalOpen r θ i a) :
    sectionEquiv (curveToSurface r θ) V (secondSourceOn r θ i a V hV) =
      secondVectorOn r θ i a V hV :=
  (sectionEquiv_restrict (curveToSurface r θ) (homOfLE hV)
    (secondSourceNormalVector r θ i a)).trans
    (congrArg ((normalDirectImageSheaf (curveToSurface r θ)).val.map (homOfLE hV).op)
      ((sectionEquiv (curveToSurface r θ) (secondNormalOpen r θ i a)).apply_symm_apply
        (secondNormalVectorSection r θ i a)))

/-- These are equalities in the intrinsic source normal sheaf itself. -/
theorem firstSourceVectors_agree (r θ : ℂ) (i₁ i₂ : Fin 2) (a₁ a₂ : Fin 3)
    (V : (surface r θ).Opens) (h₁ : V ≤ firstNormalOpen r θ i₁ a₁)
    (h₂ : V ≤ firstNormalOpen r θ i₂ a₂) :
    firstSourceOn r θ i₁ a₁ V h₁ = firstSourceOn r θ i₂ a₂ V h₂ := by
  apply (sectionEquiv (curveToSurface r θ) V).injective
  exact (firstSourceOn_comparison r θ i₁ a₁ V h₁).trans
    ((firstVectors_agree r θ i₁ i₂ a₁ a₂ V h₁ h₂).trans
      (firstSourceOn_comparison r θ i₂ a₂ V h₂).symm)

theorem secondSourceVectors_agree (r θ : ℂ) (i₁ i₂ : Fin 2) (a₁ a₂ : Fin 3)
    (V : (surface r θ).Opens) (h₁ : V ≤ secondNormalOpen r θ i₁ a₁)
    (h₂ : V ≤ secondNormalOpen r θ i₂ a₂) :
    secondSourceOn r θ i₁ a₁ V h₁ = secondSourceOn r θ i₂ a₂ V h₂ := by
  apply (sectionEquiv (curveToSurface r θ) V).injective
  exact (secondSourceOn_comparison r θ i₁ a₁ V h₁).trans
    ((secondVectors_agree r θ i₁ i₂ a₁ a₂ V h₁ h₂).trans
      (secondSourceOn_comparison r θ i₂ a₂ V h₂).symm)

theorem normalCommon_le_overlap (r θ : ℂ) (i₁ i₂ : Fin 2) (a₁ a₂ : Fin 3)
    (V : (surface r θ).Opens) (h₁ : V ≤ firstNormalOpen r θ i₁ a₁)
    (h₂ : V ≤ secondNormalOpen r θ i₂ a₂) : V ≤ overlapPatch r θ := by
  rw [overlapPatch_eq]
  exact le_inf (h₁.trans (firstNormalOpen_le r θ i₁ a₁))
    (h₂.trans (secondNormalOpen_le r θ i₂ a₂))

/-- The literal inverse-square coordinate coefficient in the actual
surface structure sheaf. -/
def transitionCoefficient (r θ : ℂ) (i₁ i₂ : Fin 2) (a₁ a₂ : Fin 3)
    (V : (surface r θ).Opens) (h₁ : V ≤ firstNormalOpen r θ i₁ a₁)
    (h₂ : V ≤ secondNormalOpen r θ i₂ a₂) : Γ(surface r θ, V) :=
  inverseSection r θ V (normalCommon_le_overlap r θ i₁ i₂ a₁ a₂ V h₁ h₂) ^ 2

theorem transitionCoefficient_isUnit (r θ : ℂ) (i₁ i₂ : Fin 2) (a₁ a₂ : Fin 3)
    (V : (surface r θ).Opens) (h₁ : V ≤ firstNormalOpen r θ i₁ a₁)
    (h₂ : V ≤ secondNormalOpen r θ i₂ a₂) :
    IsUnit (transitionCoefficient r θ i₁ i₂ a₁ a₂ V h₁ h₂) :=
  (inverseSection_isUnit r θ V (normalCommon_le_overlap r θ i₁ i₂ a₁ a₂ V h₁ h₂)).pow 2

/-- The genuine normal vectors have the inverse-square transition on
every actual cross-chart subopen. Both the degree-two ideal equations
and degree-four equation values participate in this calculation. -/
theorem crossVectors_transition (r θ : ℂ) (i₁ i₂ : Fin 2) (a₁ a₂ : Fin 3)
    (V : (surface r θ).Opens) (h₁ : V ≤ firstNormalOpen r θ i₁ a₁)
    (h₂ : V ≤ secondNormalOpen r θ i₂ a₂) :
    secondVectorOn r θ i₂ a₂ V h₂ =
      transitionCoefficient r θ i₁ i₂ a₁ a₂ V h₁ h₂ • firstVectorOn r θ i₁ a₁ V h₁ := by
  apply secondVectorOn_ext r θ i₂ a₂ V h₂
  intro b
  let hV := normalCommon_le_overlap r θ i₁ i₂ a₁ a₂ V h₁ h₂
  let t := inverseSection r θ V hV
  have hePoly :
      secondPolynomialSection r θ V (h₂.trans (secondNormalOpen_le r θ i₂ a₂))
          (weightedEquation r b) =
        t ^ 2 * firstPolynomialSection r θ V (h₁.trans (firstNormalOpen_le r θ i₁ a₁))
          (weightedEquation r b) :=
    weighted_polynomial_sections r θ V hV 2 (weightedEquation r b) (weightedEquation_homogeneous r b)
  have he : secondIdealOn r θ i₂ a₂ V h₂ b = t ^ 2 • firstIdealOn r θ i₁ a₁ V h₁ b := by
    apply Subtype.ext
    change (secondIdealOn r θ i₂ a₂ V h₂ b : Γ(surface r θ, V)) =
      t ^ 2 * (firstIdealOn r θ i₁ a₁ V h₁ b : Γ(surface r θ, V))
    exact (secondIdealOn_coe r θ i₂ a₂ V h₂ b).trans
      (hePoly.trans (congrArg (fun z : Γ(surface r θ, V) => t ^ 2 * z)
        (firstIdealOn_coe r θ i₁ a₁ V h₁ b).symm))
  have hvPoly :
      secondPolynomialSection r θ V (h₂.trans (secondNormalOpen_le r θ i₂ a₂))
          (weightedValue r b) =
        t ^ 4 * firstPolynomialSection r θ V (h₁.trans (firstNormalOpen_le r θ i₁ a₁))
          (weightedValue r b) :=
    weighted_polynomial_sections r θ V hV 4 (weightedValue r b) (weightedValue_homogeneous r b)
  have hs := scaledEquationEvaluation_coefficient (curveToSurface r θ) V (t ^ 2)
    (firstPolynomialSection r θ V (h₁.trans (firstNormalOpen_le r θ i₁ a₁)) (weightedValue r b))
    (firstVectorOn r θ i₁ a₁ V h₁) (firstIdealOn r θ i₁ a₁ V h₁ b)
    (firstVectorOn_value r θ i₁ a₁ V h₁ b)
  have hp : t ^ 4 = (t ^ 2) ^ 2 := by ring
  exact (secondVectorOn_value r θ i₂ a₂ V h₂ b).trans
    ((congrArg ((curveToSurface r θ).app V) hvPoly).trans
      ((congrArg (fun z : Γ(surface r θ, V) => (curveToSurface r θ).app V
        (z * firstPolynomialSection r θ V (h₁.trans (firstNormalOpen_le r θ i₁ a₁))
          (weightedValue r b))) hp).trans
        (hs.symm.trans (congrArg (normalSectionEvaluate (curveToSurface r θ) V
          (t ^ 2 • firstVectorOn r θ i₁ a₁ V h₁)) he.symm))))

/-- The same fixed transition holds in the actual intrinsic normal
module sheaf on the curve, with the original pulled-back coefficient. -/
theorem sourceCrossVectors_transition (r θ : ℂ) (i₁ i₂ : Fin 2) (a₁ a₂ : Fin 3)
    (V : (surface r θ).Opens) (h₁ : V ≤ firstNormalOpen r θ i₁ a₁)
    (h₂ : V ≤ secondNormalOpen r θ i₂ a₂) :
    secondSourceOn r θ i₂ a₂ V h₂ =
      (curveToSurface r θ).app V (transitionCoefficient r θ i₁ i₂ a₁ a₂ V h₁ h₂) •
        firstSourceOn r θ i₁ a₁ V h₁ := by
  apply (sectionEquiv (curveToSurface r θ) V).injective
  have hr := (sectionEquiv_smul (curveToSurface r θ) V
    (transitionCoefficient r θ i₁ i₂ a₁ a₂ V h₁ h₂) (firstSourceOn r θ i₁ a₁ V h₁)).trans
    (congrArg (fun z => transitionCoefficient r θ i₁ i₂ a₁ a₂ V h₁ h₂ • z)
      (firstSourceOn_comparison r θ i₁ a₁ V h₁))
  exact (secondSourceOn_comparison r θ i₂ a₂ V h₂).trans
    ((crossVectors_transition r θ i₁ i₂ a₁ a₂ V h₁ h₂).trans hr.symm)

end CycleQ2ProjectiveNormalTransition
end

end


section

/-! Actual source-normal sections on arbitrary affine subopens, with the
original coefficient action and values on the original kernel ideal. -/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace CycleQ2AffineNormalSections

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open CycleQ2GeometricIntrinsicNormal CycleQ2AffineNormalGeneratorExt
  CycleQ2AffineLocalHom CycleQ2SourceNormalSheaf CycleQ2NormalPushforward
  CycleQ2NormalPushforwardIso
open scoped TensorProduct

variable {A B : CommRingCat.{0}} (φ : A ⟶ B)

@[instance_reducible] def originalAlgebra : Algebra A B := φ.hom.toAlgebra

local instance rawSectionModule (Z : Scheme.{0}) (M : Z.Modules) (V : Z.Opens) :
    Module Γ(Z, V) (M.val.obj (op V)) := (M.val.obj (op V)).isModule

local instance kernelSectionModule {X Y : Scheme.{0}} (j : X ⟶ Y) (V : Y.Opens) :
    Module Γ(Y, V) ((kernelIdealSheaf j).val.obj (op V)) :=
  ((kernelIdealSheaf j).val.obj (op V)).isModule

local instance imageSectionModule {X Y : Scheme.{0}} (j : X ⟶ Y) (V : Y.Opens) :
    Module Γ(Y, V) ((imageStructureModule j).val.obj (op V)) :=
  ((imageStructureModule j).val.obj (op V)).isModule

abbrev sourceOpen (U : (Spec A).Opens) : (Spec B).Opens := (Spec.map φ) ⁻¹ᵁ U
abbrev sourceSections (U : (Spec A).Opens) := Γ(Spec B, sourceOpen φ U)

/-- The coefficient map is the original quotient followed by actual
restriction of the source structure sheaf. -/
@[instance_reducible] def sourceSectionsAlgebra (U : (Spec A).Opens) :
    Algebra A (sourceSections φ U) :=
  ((algebraMap B (sourceSections φ U)).comp φ.hom).toAlgebra

attribute [local instance] sourceSectionsAlgebra

theorem sourceSectionsTower (U : (Spec A).Opens) :
    letI : Algebra A B := originalAlgebra φ
    IsScalarTower A B (sourceSections φ U) := by
  let : Algebra A B := originalAlgebra φ
  exact
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

/-- The original ideal/global-section comparison is linear over the
original affine ring, using its canonical section coefficient map. -/
def originalIdealLinearEquiv :
    RingHom.ker φ.hom ≃ₗ[A]
      Γ((show (Spec A).Modules from kernelIdealSheaf (Spec.map φ)), ⊤) where
  __ := (originalIdealSectionEquiv φ).toAddEquiv
  map_smul' a x := by
    let M : (Spec A).Modules := kernelIdealSheaf (Spec.map φ)
    let y : Γ(M, ⊤) := (originalIdealSectionEquiv φ).toEquiv.toFun x
    have he := (originalIdealSectionEquiv φ).map_smulₛₗ a x
    change (originalIdealSectionEquiv φ).toEquiv.toFun (a • x) =
      (Spec A).presheaf.map (𝟙 (op (⊤ : (Spec A).Opens)))
        ((Scheme.ΓSpecIso A).inv a) • y
    exact he.trans (congrArg (fun c : Γ(Spec A, ⊤) => c • y)
      (ConcreteCategory.congr_hom ((Spec A).presheaf.map_id (op ⊤))
        ((Scheme.ΓSpecIso A).inv a)).symm)

/-- The actual structure morphism respects the original affine
coefficient on every open, not only at the top. -/
theorem sourceCoefficient_original (U : (Spec A).Opens) (a : A) :
    (Spec.map φ).app U
      ((Spec A).presheaf.map U.leTop.op ((Scheme.ΓSpecIso A).inv a)) =
      algebraMap B (sourceSections φ U) (φ a) := by
  have hn := ConcreteCategory.congr_hom ((Spec.map φ).naturality U.leTop.op)
    ((Scheme.ΓSpecIso A).inv a)
  have ht : (Spec.map φ).app ⊤ ((Scheme.ΓSpecIso A).inv a) =
      (Scheme.ΓSpecIso B).inv (φ a) :=
    (ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality φ) a).symm
  exact hn.trans (congrArg
    ((Spec B).presheaf.map (sourceOpen φ U).leTop.op) ht)

/-- The pushforward target sections carry the actual quotient action. -/
def imageSectionLinearEquiv (U : (Spec A).Opens) :
    Γ((show (Spec A).Modules from imageStructureModule (Spec.map φ)), U) ≃ₗ[A]
      sourceSections φ U where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' a x := by
    let x' : sourceSections φ U := x
    change (Spec.map φ).app U
      ((Spec A).presheaf.map U.leTop.op ((Scheme.ΓSpecIso A).inv a)) * x' =
      algebraMap B (sourceSections φ U) (φ a) * x'
    exact congrArg (fun c : sourceSections φ U => c * x')
      (sourceCoefficient_original φ U a)

/-- Actual local normal maps are exactly the original ideal functionals
with values in the original curve sections on the inverse-image open. -/
def originalFunctionalEquiv (U : (Spec A).Opens) :
    (normalDirectImageSheaf (Spec.map φ)).val.obj (op U) ≃
      (RingHom.ker φ.hom →ₗ[A] sourceSections φ U) :=
  (localHomOriginalEquiv
    (show (Spec A).Modules from kernelIdealSheaf (Spec.map φ))
    (show (Spec A).Modules from imageStructureModule (Spec.map φ)) U).trans
      (((originalIdealLinearEquiv φ).symm.arrowCongr
        (imageSectionLinearEquiv φ U)).toEquiv)

/-- This equivalence is fixed by evaluation on the original ideal. -/
theorem originalFunctionalEquiv_apply (U : (Spec A).Opens)
    (f : (normalDirectImageSheaf (Spec.map φ)).val.obj (op U))
    (a : RingHom.ker φ.hom) :
    originalFunctionalEquiv φ U f a =
      (normalSectionEvaluate (Spec.map φ) U f).toFun (restrictedOriginalIdeal φ U a) := by
  exact (localHomOriginalEquiv_apply
    (show (Spec A).Modules from kernelIdealSheaf (Spec.map φ))
    (show (Spec A).Modules from imageStructureModule (Spec.map φ)) U f
      ((originalIdealSectionEquiv φ).toEquiv.toFun a)).trans
    (normalSectionEvaluate_original φ U f a).symm

end CycleQ2AffineNormalSections

namespace CycleQ2SourceNormalEvaluation

open CategoryTheory AlgebraicGeometry Opposite
open CycleQ2GeometricIntrinsicNormal CycleQ2SourceNormalSheaf CycleQ2NormalPushforward

attribute [local instance] CycleQ2AffineNormalSections.imageSectionModule

variable {X Y : Scheme.{0}} (j : X ⟶ Y) (U : Y.Opens)

/-- The canonical source-to-direct-image comparison evaluates with the
genuine source-ring scalar action on every inverse-image open. -/
theorem normalPushforward_evaluate_smul
    (c : Γ(X, j ⁻¹ᵁ U)) (x : Γ(sourceNormal j, j ⁻¹ᵁ U))
    (a : RingHom.ker (j.app U).hom) :
    (show Γ(X, j ⁻¹ᵁ U) from
      (normalSectionEvaluate j U ((normalPushforward j).app U (c • x))).toFun a) =
      c * (show Γ(X, j ⁻¹ᵁ U) from
        (normalSectionEvaluate j U ((normalPushforward j).app U x)).toFun a) := by
  let z : Γ(X, j ⁻¹ᵁ U) :=
    (normalSectionEvaluate j U ((normalPushforward j).app U x)).toFun a
  change X.presheaf.map (𝟙 (op (j ⁻¹ᵁ U))) c * z = c * z
  exact congrArg (fun r : Γ(X, j ⁻¹ᵁ U) => r * z)
    (ConcreteCategory.congr_hom (X.presheaf.map_id (op (j ⁻¹ᵁ U))) c)

theorem normalPushforward_evaluate_add
    (x y : Γ(sourceNormal j, j ⁻¹ᵁ U)) (a : RingHom.ker (j.app U).hom) :
    (normalSectionEvaluate j U ((normalPushforward j).app U (x + y))).toFun a =
      (normalSectionEvaluate j U ((normalPushforward j).app U x)).toFun a +
        (normalSectionEvaluate j U ((normalPushforward j).app U y)).toFun a := rfl

end CycleQ2SourceNormalEvaluation

#print axioms CycleQ2AffineNormalSections.originalFunctionalEquiv
#print axioms CycleQ2AffineNormalSections.originalFunctionalEquiv_apply
#print axioms CycleQ2SourceNormalEvaluation.normalPushforward_evaluate_smul

namespace CycleQ2AffineNormalSections

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open CycleQ2GeometricIntrinsicNormal CycleQ2AffineNormalGeneratorExt
  CycleQ2SourceNormalSheaf CycleQ2NormalPushforward CycleQ2NormalPushforwardIso
  CycleQ2SourceNormalEvaluation
open scoped TensorProduct

variable {A B : CommRingCat.{0}} (φ : A ⟶ B) (U : (Spec A).Opens)

attribute [local instance] sourceSectionsAlgebra imageSectionModule

/-- The actual source normal section determines the original ideal
functional, linearly for the full curve section ring. -/
def sourceOriginalLinearMap :
    Γ(sourceNormal (Spec.map φ), sourceOpen φ U) →ₗ[sourceSections φ U]
      (RingHom.ker φ.hom →ₗ[A] sourceSections φ U) where
  toFun x := originalFunctionalEquiv φ U ((normalPushforward (Spec.map φ)).app U x)
  map_add' x y := by
    apply LinearMap.ext
    intro a
    exact (originalFunctionalEquiv_apply φ U _ a).trans
      ((normalPushforward_evaluate_add (Spec.map φ) U x y
        (restrictedOriginalIdeal φ U a)).trans
        (congrArg₂ (fun s t : sourceSections φ U => s + t)
          (originalFunctionalEquiv_apply φ U _ a).symm
          (originalFunctionalEquiv_apply φ U _ a).symm))
  map_smul' c x := by
    apply LinearMap.ext
    intro a
    exact (originalFunctionalEquiv_apply φ U _ a).trans
      ((normalPushforward_evaluate_smul (Spec.map φ) U c x
        (restrictedOriginalIdeal φ U a)).trans
        (congrArg (fun t : sourceSections φ U => c * t)
          (originalFunctionalEquiv_apply φ U _ a).symm))

theorem sourceOriginalLinearMap_bijective :
    Function.Bijective (sourceOriginalLinearMap φ U) := by
  have hp : Function.Bijective (fun x : Γ(sourceNormal (Spec.map φ), sourceOpen φ U) =>
      (normalPushforward (Spec.map φ)).app U x) :=
    localForward_bijective (Spec.map φ) (idealModule (Spec.map φ))
      (structureModule (Spec B)) U
  exact (originalFunctionalEquiv φ U).bijective.comp hp

/-- This is the intrinsic source-normal module with its genuine scalar
action, characterized on every affine surface subopen. -/
def sourceOriginalEquiv :
    Γ(sourceNormal (Spec.map φ), sourceOpen φ U) ≃ₗ[sourceSections φ U]
      (RingHom.ker φ.hom →ₗ[A] sourceSections φ U) :=
  LinearEquiv.ofBijective (sourceOriginalLinearMap φ U)
    (sourceOriginalLinearMap_bijective φ U)

theorem sourceOriginalEquiv_apply
    (x : Γ(sourceNormal (Spec.map φ), sourceOpen φ U)) (a : RingHom.ker φ.hom) :
    sourceOriginalEquiv φ U x a =
      (normalSectionEvaluate (Spec.map φ) U
        ((normalPushforward (Spec.map φ)).app U x)).toFun (restrictedOriginalIdeal φ U a) :=
  originalFunctionalEquiv_apply φ U _ a

theorem originalIdeal_killed (a : A) (ha : a ∈ RingHom.ker φ.hom) :
    algebraMap A (sourceSections φ U) a = 0 := by
  change algebraMap B (sourceSections φ U) (φ a) = 0
  exact (congrArg (algebraMap B (sourceSections φ U)) ha).trans (map_zero _)

/-- Associativity identifies the original conormal extended to actual
curve sections with the same cotangent quotient over those sections. -/
def conormalSectionTensorEquiv :
    letI : Algebra A B := originalAlgebra φ
    (sourceSections φ U ⊗[B] (B ⊗[A] (RingHom.ker φ.hom).Cotangent)) ≃ₗ[sourceSections φ U]
      sourceSections φ U ⊗[A] (RingHom.ker φ.hom).Cotangent := by
  letI : Algebra A B := originalAlgebra φ
  letI : IsScalarTower A B (sourceSections φ U) := sourceSectionsTower φ U
  exact TensorProduct.AlgebraTensorModule.cancelBaseChange A B
    (sourceSections φ U) (sourceSections φ U) (RingHom.ker φ.hom).Cotangent

/-- The source intrinsic normal on the inverse-image open is exactly the
dual of the scalar-extended original conormal. No local-freeness premise
or affine-open assumption is inserted into this comparison. -/
def sourceConormalDualEquiv :
    letI : Algebra A B := originalAlgebra φ
    Γ(sourceNormal (Spec.map φ), sourceOpen φ U) ≃ₗ[sourceSections φ U]
      ((sourceSections φ U ⊗[B] (B ⊗[A] (RingHom.ker φ.hom).Cotangent))
        →ₗ[sourceSections φ U] sourceSections φ U) := by
  letI : Algebra A B := originalAlgebra φ
  exact (sourceOriginalEquiv φ U).trans
    ((normalFunctionalEquiv (RingHom.ker φ.hom) (originalIdeal_killed φ U)).trans
      ((conormalSectionTensorEquiv φ U).symm.arrowCongr
        (LinearEquiv.refl (sourceSections φ U) (sourceSections φ U))))

/-- The comparison is normalized on every original ideal element. -/
theorem sourceConormalDualEquiv_tmul
    (x : Γ(sourceNormal (Spec.map φ), sourceOpen φ U))
    (s : sourceSections φ U) (a : RingHom.ker φ.hom) :
    letI : Algebra A B := originalAlgebra φ
    sourceConormalDualEquiv φ U x
      (s ⊗ₜ[B] ((1 : B) ⊗ₜ[A] (RingHom.ker φ.hom).toCotangent a)) =
      s * (show sourceSections φ U from (normalSectionEvaluate (Spec.map φ) U
        ((normalPushforward (Spec.map φ)).app U x)).toFun (restrictedOriginalIdeal φ U a)) := by
  let : Algebra A B := originalAlgebra φ
  change normalFunctionalEquiv (RingHom.ker φ.hom) (originalIdeal_killed φ U)
    (sourceOriginalEquiv φ U x)
    (conormalSectionTensorEquiv φ U
      (s ⊗ₜ[B] ((1 : B) ⊗ₜ[A] (RingHom.ker φ.hom).toCotangent a))) = _
  rw [conormalSectionTensorEquiv, TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul,
    one_smul, normalFunctionalEquiv_tmul, sourceOriginalEquiv_apply]

end CycleQ2AffineNormalSections

#print axioms CycleQ2AffineNormalSections.sourceOriginalEquiv
#print axioms CycleQ2AffineNormalSections.sourceConormalDualEquiv
#print axioms CycleQ2AffineNormalSections.sourceConormalDualEquiv_tmul

end

end


section

/-! Restriction of the genuine intrinsic normal functional on every
affine subopen, normalized on the original ideal elements. -/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace CycleQ2AffineNormalSectionNaturality

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open CycleQ2GeometricIntrinsicNormal CycleQ2AffineNormalGeneratorExt
  CycleQ2SourceNormalSheaf CycleQ2NormalPushforward CycleQ2AffineNormalSections
open scoped TensorProduct

attribute [local instance] CycleQ2AffineNormalSections.sourceSectionsAlgebra
  CycleQ2AffineNormalSections.imageSectionModule

variable {A B : CommRingCat.{0}} (φ : A ⟶ B)

/-- The coefficient restriction is the original structure-sheaf map. -/
def sourceRestriction {U V : (Spec A).Opens} (h : V ⟶ U) :
    sourceSections φ U →+* sourceSections φ V :=
  ((Spec B).presheaf.map ((Opens.map (Spec.map φ).base).map h).op).hom

theorem sourceRestriction_algebraMap {U V : (Spec A).Opens} (h : V ⟶ U) (b : B) :
    sourceRestriction φ h (algebraMap B (sourceSections φ U) b) =
      algebraMap B (sourceSections φ V) b := by
  let h' : sourceOpen φ V ⟶ sourceOpen φ U := (Opens.map (Spec.map φ).base).map h
  have he : (Spec B).presheaf.map (sourceOpen φ U).leTop.op ≫
      (Spec B).presheaf.map h'.op =
        (Spec B).presheaf.map (sourceOpen φ V).leTop.op :=
    ((Spec B).presheaf.map_comp (sourceOpen φ U).leTop.op h'.op).symm.trans
      (congrArg (fun z : op (⊤ : (Spec B).Opens) ⟶ op (sourceOpen φ V) =>
        (Spec B).presheaf.map z) (Subsingleton.elim _ _))
  exact ConcreteCategory.congr_hom he ((Scheme.ΓSpecIso B).inv b)

/-- The original ideal section restricts to the same original element. -/
theorem restrictedOriginalIdeal_restrict {U V : (Spec A).Opens} (h : V ⟶ U)
    (a : RingHom.ker φ.hom) :
    kernelSectionRestrict (Spec.map φ) h (restrictedOriginalIdeal φ U a) =
      restrictedOriginalIdeal φ V a := by
  apply Subtype.ext
  simp only [restrictedOriginalIdeal, kernelSectionRestrict_coe]
  have he : (Spec A).presheaf.map U.leTop.op ≫ (Spec A).presheaf.map h.op =
      (Spec A).presheaf.map V.leTop.op :=
    ((Spec A).presheaf.map_comp U.leTop.op h.op).symm.trans
      (congrArg (fun z : op (⊤ : (Spec A).Opens) ⟶ op V =>
        (Spec A).presheaf.map z) (Subsingleton.elim _ _))
  exact ConcreteCategory.congr_hom he
    ((affineKernelSectionSemilinearEquiv φ).symm.toEquiv.toFun a)

/-- The source-normal comparison commutes with actual restriction,
evaluated on every original ideal element. -/
theorem sourceOriginalEquiv_restrict {U V : (Spec A).Opens} (h : V ⟶ U)
    (x : Γ(sourceNormal (Spec.map φ), sourceOpen φ U)) (a : RingHom.ker φ.hom) :
    sourceOriginalEquiv φ V
      ((sourceNormal (Spec.map φ)).presheaf.map
        ((Opens.map (Spec.map φ).base).map h).op x) a =
      sourceRestriction φ h (sourceOriginalEquiv φ U x a) := by
  let j := Spec.map φ
  let xV : Γ(sourceNormal j, sourceOpen φ V) :=
    (sourceNormal j).presheaf.map ((Opens.map j.base).map h).op x
  let fU : (normalDirectImageSheaf j).val.obj (op U) := (normalPushforward j).app U x
  let fV : (normalDirectImageSheaf j).val.obj (op V) :=
    (normalDirectImageSheaf j).val.map h.op fU
  let valueV : (normalDirectImageSheaf j).val.obj (op V) →
      RingHom.ker (j.app V).hom → sourceSections φ V :=
    fun f a => (normalSectionEvaluate j V f).toFun a
  have hp : (normalPushforward j).app V xV = fV :=
    ConcreteCategory.congr_hom ((normalPushforward j).mapPresheaf.naturality h.op) x
  have ha := restrictedOriginalIdeal_restrict φ h a
  have hr := normalSectionEvaluate_restrict j h fU (restrictedOriginalIdeal φ U a)
  calc
    sourceOriginalEquiv φ V xV a = valueV ((normalPushforward j).app V xV)
        (restrictedOriginalIdeal φ V a) := sourceOriginalEquiv_apply φ V xV a
    _ = valueV fV (restrictedOriginalIdeal φ V a) :=
      congrArg (fun f => valueV f (restrictedOriginalIdeal φ V a)) hp
    _ = valueV fV (kernelSectionRestrict j h (restrictedOriginalIdeal φ U a)) :=
      congrArg (valueV fV) ha.symm
    _ = sourceRestriction φ h
        ((normalSectionEvaluate j U fU).toFun (restrictedOriginalIdeal φ U a)) := hr
    _ = sourceRestriction φ h (sourceOriginalEquiv φ U x a) :=
      congrArg (sourceRestriction φ h) (sourceOriginalEquiv_apply φ U x a).symm

#print axioms sourceRestriction_algebraMap
#print axioms restrictedOriginalIdeal_restrict
#print axioms sourceOriginalEquiv_restrict

end CycleQ2AffineNormalSectionNaturality
end

end


section

/-! The original normal vector is a genuine frame on every literal
augmented-Jacobian patch. Its scale is the proved unit normalMultiplier. -/
set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace CycleQ2NormalVectorFrame

open CategoryTheory AlgebraicGeometry Opposite
open CycleQ2GeometricSurfaceAdjunction CycleQ2GeometricAffineCurveCharts
open CycleQ2GeometricIntrinsicNormal CycleQ2SourceNormalSheaf
open CycleQ2SourceNormalRaw CycleQ2SourceNormalPatch

section Semilinear

variable {R S M N : Type} [CommRing R] [CommRing S]
  [AddCommGroup M] [AddCommGroup N] [Module R M] [Module S N]
  (σ : R ≃+* S)

local instance forwardScalarPair : RingHomInvPair σ.toRingHom σ.symm.toRingHom :=
  RingHomInvPair.of_ringEquiv σ
local instance backwardScalarPair : RingHomInvPair σ.symm.toRingHom σ.toRingHom :=
  RingHomInvPair.of_ringEquiv σ.symm

/-- A semilinear isomorphism preserves the assertion that the original
coefficient-times-vector map is bijective. -/
theorem coefficient_bijective_of_semilinear
    (e : M ≃ₛₗ[σ.toRingHom] N) (v : M)
    (h : Function.Bijective (fun s : S => s • e v)) :
    Function.Bijective (fun r : R => r • v) := by
  constructor
  · intro a b hab
    apply σ.injective
    apply h.1
    exact (map_smulₛₗ e a v).symm.trans ((congrArg e hab).trans (map_smulₛₗ e b v))
  · intro m
    obtain ⟨s, hs⟩ := h.2 (e m)
    refine ⟨σ.symm s, e.injective ?_⟩
    exact (map_smulₛₗ e (σ.symm s) v).trans
      ((congrArg (fun z : S => z • e v) (σ.apply_symm_apply s)).trans hs)

end Semilinear

section Actual

variable (q h : AffinePoly) (g₁ g₂ k : SurfacePoly) (i : Fin 2) (j : Fin 3)

/-- The prescribed original normal value is a unit because the actual
augmented Jacobian was inverted. -/
def normalVectorUnit : (NormalCurvePatch q h g₁ g₂ k i j)ˣ :=
  (normalMultiplier_isUnit q h g₁ g₂ k i j).neg.unit

@[simp] theorem normalVectorUnit_value :
    (normalVectorUnit q h g₁ g₂ k i j : NormalCurvePatch q h g₁ g₂ k i j) =
      -normalCoefficientMap q h g₁ g₂ k i j (normalMultiplier g₁ g₂ i) :=
  IsUnit.unit_spec _

/-- A genuine linear frame of the original conormal dual. -/
def rawFrame :
    NormalCurvePatch q h g₁ g₂ k i j ≃ₗ[NormalCurvePatch q h g₁ g₂ k i j]
      (NormalConormal q h g₁ g₂ k i j →ₗ[NormalCurvePatch q h g₁ g₂ k i j]
        NormalCurvePatch q h g₁ g₂ k i j) :=
  (normalDualEquiv q h g₁ g₂ k i j).symm.trans
    (LinearEquiv.smulOfUnit (normalVectorUnit q h g₁ g₂ k i j))

/-- The frame is exactly multiplication by the fixed original vector;
its construction does not introduce a new normalization. -/
theorem rawFrame_apply (b : NormalCurvePatch q h g₁ g₂ k i j) :
    rawFrame q h g₁ g₂ k i j b = b • normalVector q h g₁ g₂ k i j := by
  change (normalVectorUnit q h g₁ g₂ k i j : NormalCurvePatch q h g₁ g₂ k i j) •
      (b • (normalConormalEquiv q h g₁ g₂ k i j).toLinearMap) =
    b • ((-normalCoefficientMap q h g₁ g₂ k i j (normalMultiplier g₁ g₂ i)) •
      (normalConormalEquiv q h g₁ g₂ k i j).toLinearMap)
  rw [normalVectorUnit_value, smul_comm]

theorem rawCoefficient_bijective :
    Function.Bijective (fun b : NormalCurvePatch q h g₁ g₂ k i j =>
      b • normalVector q h g₁ g₂ k i j) := by
  have he : (fun b : NormalCurvePatch q h g₁ g₂ k i j =>
      b • normalVector q h g₁ g₂ k i j) =
      (fun b => rawFrame q h g₁ g₂ k i j b) :=
    funext (fun b => (rawFrame_apply q h g₁ g₂ k i j b).symm)
  rw [he]
  exact (rawFrame q h g₁ g₂ k i j).bijective

local instance sourceSectionModule :
    Module Γ(Spec (CommRingCat.of (NormalCurvePatch q h g₁ g₂ k i j)), ⊤)
      Γ(sourceNormal (patchImmersion q h g₁ g₂ k i j), ⊤) :=
  ((sourceNormal (patchImmersion q h g₁ g₂ k i j)).val.obj (op ⊤)).isModule

/-- The actual source-normal section is a frame over the actual ring of
global sections of its affine curve patch. -/
theorem sourceTopCoefficient_bijective :
    Function.Bijective
      (fun b : Γ(Spec (CommRingCat.of (NormalCurvePatch q h g₁ g₂ k i j)), ⊤) =>
        b • normalVectorSection q h g₁ g₂ k i j) := by
  apply coefficient_bijective_of_semilinear
    (specTopRingEquiv (CommRingCat.of (NormalCurvePatch q h g₁ g₂ k i j)))
    (rawEquiv q h g₁ g₂ k i j) (normalVectorSection q h g₁ g₂ k i j)
  have he := rawEquiv_normalVectorSection q h g₁ g₂ k i j
  exact (congrArg (fun v : NormalConormal q h g₁ g₂ k i j →ₗ[
      NormalCurvePatch q h g₁ g₂ k i j] NormalCurvePatch q h g₁ g₂ k i j =>
      Function.Bijective (fun b : NormalCurvePatch q h g₁ g₂ k i j => b • v)) he).mpr
    (rawCoefficient_bijective q h g₁ g₂ k i j)

/-- The coefficient map itself, now as an actual linear isomorphism. -/
def sourceTopFrame :
    Γ(Spec (CommRingCat.of (NormalCurvePatch q h g₁ g₂ k i j)), ⊤) ≃ₗ[
      Γ(Spec (CommRingCat.of (NormalCurvePatch q h g₁ g₂ k i j)), ⊤)]
      Γ(sourceNormal (patchImmersion q h g₁ g₂ k i j), ⊤) :=
  LinearEquiv.ofBijective
    (LinearMap.toSpanSingleton _ _ (normalVectorSection q h g₁ g₂ k i j))
    (sourceTopCoefficient_bijective q h g₁ g₂ k i j)

@[simp] theorem sourceTopFrame_apply
    (b : Γ(Spec (CommRingCat.of (NormalCurvePatch q h g₁ g₂ k i j)), ⊤)) :
    sourceTopFrame q h g₁ g₂ k i j b = b • normalVectorSection q h g₁ g₂ k i j := rfl

@[simp] theorem sourceTopFrame_one :
    sourceTopFrame q h g₁ g₂ k i j 1 = normalVectorSection q h g₁ g₂ k i j :=
  (sourceTopFrame_apply q h g₁ g₂ k i j 1).trans (one_smul _ _)

end Actual
end CycleQ2NormalVectorFrame
end

end


section

/-! The fixed conormal-dual frame after any actual scalar extension.
The only freeness used is the already proved normalConormalEquiv. -/
set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace CycleQ2NormalVectorBaseChange

open CycleQ2GeometricSurfaceAdjunction CycleQ2GeometricAffineCurveCharts
open CycleQ2NormalVectorFrame
open scoped TensorProduct

section Linear

variable {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]

/-- The dual frame of an actual rank-one linear equivalence. -/
def dualLineFrame (e : M ≃ₗ[R] R) : R ≃ₗ[R] (M →ₗ[R] R) :=
  (LinearMap.ringLmapEquivSelf R R R).symm.trans
    (e.symm.arrowCongr (LinearEquiv.refl R R))

theorem dualLineFrame_apply (e : M ≃ₗ[R] R) (r : R) :
    dualLineFrame e r = r • e.toLinearMap := by
  apply LinearMap.ext
  intro x
  change e x * r = r * e x
  exact mul_comm _ _

/-- A normalized generator detects linear functionals on an actual line. -/
theorem dual_ext_of_generator (e : M ≃ₗ[R] R) (u : M) (hu : e u = 1)
    (f g : M →ₗ[R] R) (hfg : f u = g u) : f = g := by
  apply LinearMap.ext
  intro x
  have hx : x = e x • u := by
    apply e.injective
    rw [map_smul, hu, smul_eq_mul, mul_one]
  exact (congrArg f hx).trans ((f.map_smul (e x) u).trans
    ((congrArg (fun z : R => e x • z) hfg).trans
      ((g.map_smul (e x) u).symm.trans (congrArg g hx).symm)))

end Linear

section Actual

variable (q h : AffinePoly) (g₁ g₂ k : SurfacePoly) (i : Fin 2) (j : Fin 3)
variable (S : Type) [CommRing S] [Algebra (NormalCurvePatch q h g₁ g₂ k i j) S]

/-- The original conormal line, extended to the actual coefficient ring. -/
def baseConormalEquiv :
    (S ⊗[NormalCurvePatch q h g₁ g₂ k i j] NormalConormal q h g₁ g₂ k i j) ≃ₗ[S] S :=
  ((normalConormalEquiv q h g₁ g₂ k i j).baseChange
    (NormalCurvePatch q h g₁ g₂ k i j) S
    (NormalConormal q h g₁ g₂ k i j) (NormalCurvePatch q h g₁ g₂ k i j)).trans
      (TensorProduct.AlgebraTensorModule.rid (NormalCurvePatch q h g₁ g₂ k i j) S S)

theorem baseConormalEquiv_tmul (s : S) (x : NormalConormal q h g₁ g₂ k i j) :
    baseConormalEquiv q h g₁ g₂ k i j S (s ⊗ₜ x) =
      algebraMap (NormalCurvePatch q h g₁ g₂ k i j) S
        (normalConormalEquiv q h g₁ g₂ k i j x) * s := by
  change normalConormalEquiv q h g₁ g₂ k i j x • s = _
  exact Algebra.smul_def _ _

theorem baseConormalEquiv_selected :
    baseConormalEquiv q h g₁ g₂ k i j S
      ((1 : S) ⊗ₜ normalEquationClass q h g₁ g₂ k i j i) = 1 := by
  rw [baseConormalEquiv_tmul, normalConormalEquiv_selected, map_one, mul_one]

/-- Scalar extension preserves the prescribed original normal vector. -/
def baseNormalVector :
    (S ⊗[NormalCurvePatch q h g₁ g₂ k i j] NormalConormal q h g₁ g₂ k i j) →ₗ[S] S :=
  (algebraMap (NormalCurvePatch q h g₁ g₂ k i j) S
    (-normalCoefficientMap q h g₁ g₂ k i j (normalMultiplier g₁ g₂ i))) •
      (baseConormalEquiv q h g₁ g₂ k i j S).toLinearMap

theorem baseNormalVector_tmul (s : S) (x : NormalConormal q h g₁ g₂ k i j) :
    baseNormalVector q h g₁ g₂ k i j S (s ⊗ₜ x) =
      s * algebraMap (NormalCurvePatch q h g₁ g₂ k i j) S
        (normalVector q h g₁ g₂ k i j x) := by
  change algebraMap (NormalCurvePatch q h g₁ g₂ k i j) S
      (-normalCoefficientMap q h g₁ g₂ k i j (normalMultiplier g₁ g₂ i)) *
      baseConormalEquiv q h g₁ g₂ k i j S (s ⊗ₜ x) =
    s * algebraMap (NormalCurvePatch q h g₁ g₂ k i j) S
      ((-normalCoefficientMap q h g₁ g₂ k i j (normalMultiplier g₁ g₂ i)) *
        normalConormalEquiv q h g₁ g₂ k i j x)
  rw [baseConormalEquiv_tmul, map_mul]
  ring

/-- The full coefficient map is an isomorphism over any actual target
ring, since the original normal value is still a unit there. -/
def baseNormalFrame : S ≃ₗ[S]
    ((S ⊗[NormalCurvePatch q h g₁ g₂ k i j] NormalConormal q h g₁ g₂ k i j) →ₗ[S] S) :=
  (dualLineFrame (baseConormalEquiv q h g₁ g₂ k i j S)).trans
    (LinearEquiv.smulOfUnit
      (Units.map (algebraMap (NormalCurvePatch q h g₁ g₂ k i j) S).toMonoidHom
        (normalVectorUnit q h g₁ g₂ k i j)))

theorem baseNormalFrame_apply (s : S) :
    baseNormalFrame q h g₁ g₂ k i j S s =
      s • baseNormalVector q h g₁ g₂ k i j S := by
  change (algebraMap (NormalCurvePatch q h g₁ g₂ k i j) S
      (normalVectorUnit q h g₁ g₂ k i j : NormalCurvePatch q h g₁ g₂ k i j)) •
      dualLineFrame (baseConormalEquiv q h g₁ g₂ k i j S) s = _
  rw [dualLineFrame_apply, normalVectorUnit_value, smul_comm]
  rfl

theorem baseNormalFrame_one :
    baseNormalFrame q h g₁ g₂ k i j S 1 = baseNormalVector q h g₁ g₂ k i j S :=
  (baseNormalFrame_apply q h g₁ g₂ k i j S 1).trans (one_smul _ _)

/-- Evaluation on the original selected equation detects every linear
functional on the actual extended conormal. -/
theorem baseDual_ext
    (f g : (S ⊗[NormalCurvePatch q h g₁ g₂ k i j] NormalConormal q h g₁ g₂ k i j) →ₗ[S] S)
    (hfg : f ((1 : S) ⊗ₜ normalEquationClass q h g₁ g₂ k i j i) =
      g ((1 : S) ⊗ₜ normalEquationClass q h g₁ g₂ k i j i)) : f = g := by
  exact dual_ext_of_generator (baseConormalEquiv q h g₁ g₂ k i j S)
    ((1 : S) ⊗ₜ normalEquationClass q h g₁ g₂ k i j i)
    (baseConormalEquiv_selected q h g₁ g₂ k i j S) f g hfg

end Actual
end CycleQ2NormalVectorBaseChange
end

end


section

/-! Genuine normal frames on every open of the actual affine normal
curve patch, normalized by the original vector (G2,-G1). -/
set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace CycleQ2NormalVectorLocalFrame

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open CycleQ2GeometricSurfaceAdjunction CycleQ2GeometricAffineCurveCharts
open CycleQ2GeometricIntrinsicNormal CycleQ2SourceNormalSheaf CycleQ2NormalPushforward
open CycleQ2SourceNormalRaw CycleQ2SourceNormalPatch CycleQ2AffineNormalGeneratorExt
open CycleQ2AffineNormalSections CycleQ2AffineNormalSectionNaturality
open CycleQ2NormalVectorFrame CycleQ2NormalVectorBaseChange
open scoped TensorProduct

attribute [local instance] CycleQ2AffineNormalSections.sourceSectionsAlgebra

section Generic
variable {A B : CommRingCat.{0}} (φ : A ⟶ B)

/-- The all-open original-ideal functional agrees at the top with the
previous actual Spec/conormal comparison. -/
theorem sourceOriginal_top_raw
    (x : Γ(sourceNormal (Spec.map φ), ⊤)) (a : RingHom.ker φ.hom) :
    letI : Algebra A B := originalAlgebra φ
    sourceOriginalEquiv φ ⊤ x a =
      algebraMap B (sourceSections φ ⊤)
        (sourceNormalRawAddEquiv φ x ((1 : B) ⊗ₜ[A] (RingHom.ker φ.hom).toCotangent a)) := by
  let : Algebra A B := originalAlgebra φ
  let ev : (normalDirectImageSheaf (Spec.map φ)).val.obj (op (⊤ : (Spec A).Opens)) →
      RingHom.ker ((Spec.map φ).app ⊤).hom → Γ(Spec B, ⊤) :=
    fun f a => (normalSectionEvaluate (Spec.map φ) ⊤ f).toFun a
  have hp := normalPushforward_app_top (Spec.map φ) x
  have ha := CycleQ2NormalChartSections.originalIdeal_top φ a
  have he : ev ((normalPushforward (Spec.map φ)).app ⊤ x) (restrictedOriginalIdeal φ ⊤ a) =
      ev (normalGlobalComparison (Spec.map φ) x) ((affineKernelSectionSemilinearEquiv φ).symm a) :=
    (congrArg (fun f => ev f (restrictedOriginalIdeal φ ⊤ a)) hp).trans
      (congrArg (ev (normalGlobalComparison (Spec.map φ) x)) ha)
  have hraw := (sourceNormalRaw_tmul φ x 1 a).trans (one_mul _)
  apply (specTopRingEquiv B).injective
  exact (congrArg (specTopRingEquiv B)
    ((sourceOriginalEquiv_apply φ ⊤ x a).trans he)).trans
      (hraw.symm.trans ((specTopRingEquiv B).apply_symm_apply _).symm)

/-- Evaluation of the extended conormal on an original ideal generator
is exactly the genuine source-normal functional. -/
theorem sourceDual_generator (U : (Spec A).Opens)
    (x : Γ(sourceNormal (Spec.map φ), sourceOpen φ U)) (a : RingHom.ker φ.hom) :
    letI : Algebra A B := originalAlgebra φ
    sourceConormalDualEquiv φ U x
      ((1 : sourceSections φ U) ⊗ₜ[B] ((1 : B) ⊗ₜ[A] (RingHom.ker φ.hom).toCotangent a)) =
      sourceOriginalEquiv φ U x a := by
  let : Algebra A B := originalAlgebra φ
  exact ((sourceConormalDualEquiv_tmul φ U x 1 a).trans (one_mul _)).trans
    (sourceOriginalEquiv_apply φ U x a).symm

/-- Every curve open is an actual inverse-image open under the affine
closed immersion; no assertion about surjectivity on nonaffine sections
is needed. -/
theorem sourceOpen_exists (hφ : Function.Surjective φ.hom) (W : (Spec B).Opens) :
    ∃ U : (Spec A).Opens, sourceOpen φ U = W := by
  let : IsClosedImmersion (Spec.map φ) := IsClosedImmersion.spec_of_surjective φ hφ
  obtain ⟨T, hT, hpre⟩ :=
    (Spec.map φ).isClosedEmbedding.isEmbedding.isInducing.isOpen_iff.mp W.isOpen
  exact ⟨⟨T, hT⟩, SetLike.coe_injective hpre⟩

end Generic

section Actual
variable (q h : AffinePoly) (g₁ g₂ k : SurfacePoly) (i : Fin 2) (j : Fin 3)

abbrev sectionRing (U : (Spec (CommRingCat.of (NormalSurfacePatch q h g₁ g₂ k i j))).Opens) :=
  sourceSections (patchRingMap q h g₁ g₂ k i j) U

local instance sectionRingAlgebra
    (U : (Spec (CommRingCat.of (NormalSurfacePatch q h g₁ g₂ k i j))).Opens) :
    Algebra (NormalCurvePatch q h g₁ g₂ k i j) (sectionRing q h g₁ g₂ k i j U) :=
  @IsAffineOpen.instAlgebraCarrierObjOppositeOpensCarrierCarrierCommRingCatSpecPresheafOpOpens
    (CommRingCat.of (NormalCurvePatch q h g₁ g₂ k i j))
    (sourceOpen (patchRingMap q h g₁ g₂ k i j) U)

abbrev originalEquation (a : Fin 2) : RingHom.ker (patchRingMap q h g₁ g₂ k i j).hom :=
  ⟨algebraMap SurfacePoly (NormalSurfacePatch q h g₁ g₂ k i j) (normalPolynomial q a),
    normalEquation_mem q h g₁ g₂ k i j a⟩

/-- The actual restriction of the fixed source-normal vector. -/
def vectorOn (U : (Spec (CommRingCat.of (NormalSurfacePatch q h g₁ g₂ k i j))).Opens) :
    Γ(sourceNormal (patchImmersion q h g₁ g₂ k i j),
      sourceOpen (patchRingMap q h g₁ g₂ k i j) U) :=
  (sourceNormal (patchImmersion q h g₁ g₂ k i j)).presheaf.map
    ((Opens.map (patchImmersion q h g₁ g₂ k i j).base).map U.leTop).op
      (normalVectorSection q h g₁ g₂ k i j)

/-- Its values on the two original equations are their original raw
values, followed by the actual curve coefficient map. -/
theorem vectorOn_original_value
    (U : (Spec (CommRingCat.of (NormalSurfacePatch q h g₁ g₂ k i j))).Opens) (a : Fin 2) :
    sourceOriginalEquiv (patchRingMap q h g₁ g₂ k i j) U
        (vectorOn q h g₁ g₂ k i j U) (originalEquation q h g₁ g₂ k i j a) =
      algebraMap (NormalCurvePatch q h g₁ g₂ k i j) (sectionRing q h g₁ g₂ k i j U)
        (normalVector q h g₁ g₂ k i j (normalEquationClass q h g₁ g₂ k i j a)) := by
  have hr := sourceOriginalEquiv_restrict (patchRingMap q h g₁ g₂ k i j) U.leTop
    (normalVectorSection q h g₁ g₂ k i j) (originalEquation q h g₁ g₂ k i j a)
  have ht := sourceOriginal_top_raw (patchRingMap q h g₁ g₂ k i j)
    (normalVectorSection q h g₁ g₂ k i j) (originalEquation q h g₁ g₂ k i j a)
  have hraw : sourceNormalRawAddEquiv (patchRingMap q h g₁ g₂ k i j)
      (normalVectorSection q h g₁ g₂ k i j)
      ((1 : NormalCurvePatch q h g₁ g₂ k i j) ⊗ₜ[NormalSurfacePatch q h g₁ g₂ k i j]
        (RingHom.ker (patchRingMap q h g₁ g₂ k i j).hom).toCotangent
          (originalEquation q h g₁ g₂ k i j a)) =
      normalVector q h g₁ g₂ k i j (normalEquationClass q h g₁ g₂ k i j a) :=
    congrArg (fun f : NormalConormal q h g₁ g₂ k i j →ₗ[NormalCurvePatch q h g₁ g₂ k i j]
      NormalCurvePatch q h g₁ g₂ k i j => f (normalEquationClass q h g₁ g₂ k i j a))
      (rawEquiv_normalVectorSection q h g₁ g₂ k i j)
  have ht' := ht.trans (congrArg
    (algebraMap (NormalCurvePatch q h g₁ g₂ k i j)
      (sectionRing q h g₁ g₂ k i j ⊤)) hraw)
  exact hr.trans ((congrArg (sourceRestriction (patchRingMap q h g₁ g₂ k i j) U.leTop) ht').trans
    (sourceRestriction_algebraMap (patchRingMap q h g₁ g₂ k i j) U.leTop _))

/-- The canonical all-open sheaf comparison with the actual extended
conormal dual. -/
def localDualEquiv
    (U : (Spec (CommRingCat.of (NormalSurfacePatch q h g₁ g₂ k i j))).Opens) :
    Γ(sourceNormal (patchImmersion q h g₁ g₂ k i j),
      sourceOpen (patchRingMap q h g₁ g₂ k i j) U) ≃ₗ[sectionRing q h g₁ g₂ k i j U]
      ((sectionRing q h g₁ g₂ k i j U ⊗[NormalCurvePatch q h g₁ g₂ k i j]
          NormalConormal q h g₁ g₂ k i j) →ₗ[sectionRing q h g₁ g₂ k i j U]
        sectionRing q h g₁ g₂ k i j U) :=
  sourceConormalDualEquiv (patchRingMap q h g₁ g₂ k i j) U

/-- The genuine source section is sent to the scalar extension of the
fixed raw vector, not to an arbitrarily chosen generator. -/
theorem localDualEquiv_vectorOn
    (U : (Spec (CommRingCat.of (NormalSurfacePatch q h g₁ g₂ k i j))).Opens) :
    localDualEquiv q h g₁ g₂ k i j U (vectorOn q h g₁ g₂ k i j U) =
      baseNormalVector q h g₁ g₂ k i j (sectionRing q h g₁ g₂ k i j U) := by
  apply baseDual_ext q h g₁ g₂ k i j (sectionRing q h g₁ g₂ k i j U)
  have hl := sourceDual_generator (patchRingMap q h g₁ g₂ k i j) U
    (vectorOn q h g₁ g₂ k i j U) (originalEquation q h g₁ g₂ k i j i)
  have hr := (baseNormalVector_tmul q h g₁ g₂ k i j
    (sectionRing q h g₁ g₂ k i j U) 1 (normalEquationClass q h g₁ g₂ k i j i)).trans (one_mul _)
  exact hl.trans ((vectorOn_original_value q h g₁ g₂ k i j U i).trans hr.symm)

/-- The actual source-normal module is free with the fixed vector on
every inverse-image open of the affine chart. -/
def preimageFrame
    (U : (Spec (CommRingCat.of (NormalSurfacePatch q h g₁ g₂ k i j))).Opens) :
    sectionRing q h g₁ g₂ k i j U ≃ₗ[sectionRing q h g₁ g₂ k i j U]
      Γ(sourceNormal (patchImmersion q h g₁ g₂ k i j),
        sourceOpen (patchRingMap q h g₁ g₂ k i j) U) :=
  (baseNormalFrame q h g₁ g₂ k i j (sectionRing q h g₁ g₂ k i j U)).trans
    (localDualEquiv q h g₁ g₂ k i j U).symm

theorem preimageFrame_apply
    (U : (Spec (CommRingCat.of (NormalSurfacePatch q h g₁ g₂ k i j))).Opens)
    (c : sectionRing q h g₁ g₂ k i j U) :
    preimageFrame q h g₁ g₂ k i j U c = c • vectorOn q h g₁ g₂ k i j U := by
  apply (localDualEquiv q h g₁ g₂ k i j U).injective
  have hl := (localDualEquiv q h g₁ g₂ k i j U).apply_symm_apply
    (baseNormalFrame q h g₁ g₂ k i j (sectionRing q h g₁ g₂ k i j U) c)
  have hr := (map_smul (localDualEquiv q h g₁ g₂ k i j U) c
    (vectorOn q h g₁ g₂ k i j U)).trans
    (congrArg (fun x => c • x) (localDualEquiv_vectorOn q h g₁ g₂ k i j U))
  exact hl.trans ((baseNormalFrame_apply q h g₁ g₂ k i j
    (sectionRing q h g₁ g₂ k i j U) c).trans hr.symm)

/-- Restriction of the fixed vector to an arbitrary curve open. -/
def curveVector (W : (Spec (CommRingCat.of (NormalCurvePatch q h g₁ g₂ k i j))).Opens) :
    Γ(sourceNormal (patchImmersion q h g₁ g₂ k i j), W) :=
  (sourceNormal (patchImmersion q h g₁ g₂ k i j)).presheaf.map W.leTop.op
    (normalVectorSection q h g₁ g₂ k i j)

theorem curveCoefficient_bijective
    (W : (Spec (CommRingCat.of (NormalCurvePatch q h g₁ g₂ k i j))).Opens) :
    Function.Bijective (fun c : Γ(Spec (CommRingCat.of (NormalCurvePatch q h g₁ g₂ k i j)), W) =>
      c • curveVector q h g₁ g₂ k i j W) := by
  obtain ⟨U, rfl⟩ := sourceOpen_exists (patchRingMap q h g₁ g₂ k i j)
    (normalChartAlgebra_surjective q h g₁ g₂ k i j) W
  have he : (fun c : sectionRing q h g₁ g₂ k i j U =>
      c • vectorOn q h g₁ g₂ k i j U) =
      (fun c => preimageFrame q h g₁ g₂ k i j U c) :=
    funext (fun c => (preimageFrame_apply q h g₁ g₂ k i j U c).symm)
  change Function.Bijective (fun c : sectionRing q h g₁ g₂ k i j U =>
    c • vectorOn q h g₁ g₂ k i j U)
  rw [he]
  exact (preimageFrame q h g₁ g₂ k i j U).bijective

/-- The literal coefficient-times-vector isomorphism on every curve open. -/
def curveFrame
    (W : (Spec (CommRingCat.of (NormalCurvePatch q h g₁ g₂ k i j))).Opens) :
    Γ(Spec (CommRingCat.of (NormalCurvePatch q h g₁ g₂ k i j)), W) ≃ₗ[
      Γ(Spec (CommRingCat.of (NormalCurvePatch q h g₁ g₂ k i j)), W)]
      Γ(sourceNormal (patchImmersion q h g₁ g₂ k i j), W) :=
  LinearEquiv.ofBijective (LinearMap.toSpanSingleton _ _ (curveVector q h g₁ g₂ k i j W))
    (curveCoefficient_bijective q h g₁ g₂ k i j W)

theorem curveFrame_apply
    (W : (Spec (CommRingCat.of (NormalCurvePatch q h g₁ g₂ k i j))).Opens)
    (c : Γ(Spec (CommRingCat.of (NormalCurvePatch q h g₁ g₂ k i j)), W)) :
    curveFrame q h g₁ g₂ k i j W c = c • curveVector q h g₁ g₂ k i j W := rfl

theorem curveVector_restrict
    {U V : (Spec (CommRingCat.of (NormalCurvePatch q h g₁ g₂ k i j))).Opens} (f : V ⟶ U) :
    (sourceNormal (patchImmersion q h g₁ g₂ k i j)).presheaf.map f.op
        (curveVector q h g₁ g₂ k i j U) = curveVector q h g₁ g₂ k i j V :=
  (ConcreteCategory.congr_hom
    ((sourceNormal (patchImmersion q h g₁ g₂ k i j)).presheaf.map_comp U.leTop.op f.op)
      (normalVectorSection q h g₁ g₂ k i j)).symm

theorem curveFrame_naturality
    {U V : (Spec (CommRingCat.of (NormalCurvePatch q h g₁ g₂ k i j))).Opens} (f : V ⟶ U)
    (c : Γ(Spec (CommRingCat.of (NormalCurvePatch q h g₁ g₂ k i j)), U)) :
    (sourceNormal (patchImmersion q h g₁ g₂ k i j)).presheaf.map f.op
        (curveFrame q h g₁ g₂ k i j U c) =
      curveFrame q h g₁ g₂ k i j V
        ((Spec (CommRingCat.of (NormalCurvePatch q h g₁ g₂ k i j))).presheaf.map f.op c) := by
  have hs := (sourceNormal (patchImmersion q h g₁ g₂ k i j)).val.map_smul f.op c
    (curveVector q h g₁ g₂ k i j U)
  exact (congrArg ((sourceNormal (patchImmersion q h g₁ g₂ k i j)).presheaf.map f.op)
    (curveFrame_apply q h g₁ g₂ k i j U c)).trans
      (hs.trans ((congrArg (fun x =>
        ((Spec (CommRingCat.of (NormalCurvePatch q h g₁ g₂ k i j))).presheaf.map f.op c) • x)
          (curveVector_restrict q h g₁ g₂ k i j f)).trans
            (curveFrame_apply q h g₁ g₂ k i j V _).symm))

/-- A genuine isomorphism of module sheaves on the actual affine curve
patch, with the original vector as the image of one. -/
def affineSourceFrameIso :
    structureModule (Spec (CommRingCat.of (NormalCurvePatch q h g₁ g₂ k i j))) ≅
      sourceNormal (patchImmersion q h g₁ g₂ k i j) :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (fun U => (curveFrame q h g₁ g₂ k i j U.unop).toModuleIso)
      (by
        intro U V f
        apply ConcreteCategory.hom_ext
        intro c
        exact (curveFrame_naturality q h g₁ g₂ k i j f.unop c).symm))

theorem affineSourceFrameIso_hom_apply
    (W : (Spec (CommRingCat.of (NormalCurvePatch q h g₁ g₂ k i j))).Opens)
    (c : Γ(Spec (CommRingCat.of (NormalCurvePatch q h g₁ g₂ k i j)), W)) :
    (affineSourceFrameIso q h g₁ g₂ k i j).hom.app W c =
      c • curveVector q h g₁ g₂ k i j W := rfl

theorem affineSourceFrameIso_inv_vector
    (W : (Spec (CommRingCat.of (NormalCurvePatch q h g₁ g₂ k i j))).Opens) :
    (affineSourceFrameIso q h g₁ g₂ k i j).inv.app W (curveVector q h g₁ g₂ k i j W) =
      (1 : Γ(Spec (CommRingCat.of (NormalCurvePatch q h g₁ g₂ k i j)), W)) := by
  change (curveFrame q h g₁ g₂ k i j W).symm (curveVector q h g₁ g₂ k i j W) = 1
  apply (curveFrame q h g₁ g₂ k i j W).injective
  rw [LinearEquiv.apply_symm_apply, curveFrame_apply, one_smul]

end Actual
end CycleQ2NormalVectorLocalFrame
end

end


section

/-! The fixed normal vectors on arbitrary curve subopens. These identities
use the actual source module restrictions and the original quartic
transition unit, preserving the distinction between the two covers. -/
set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace CycleQ2NormalVectorOnCurve

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
open CycleQ2GeometricLiteralSurface CycleQ2SourceNormalSheaf
open CycleQ2SourceNormalVectors CycleQ2ProjectiveNormalTransition
open CycleQ2GeometricSurfaceJacobianCharts CycleQ2GeometricNormalCharts
open CycleQ2GeometricProjectiveCurve CycleQ2GeometricProjectiveNormalClass
open CycleQ2NormalTransitionBinding

section Restriction
variable {X : Scheme.{0}} (M : X.Modules)

def sectionRes {U V : X.Opens} (h : V ≤ U) (x : Γ(M,U)) : Γ(M,V) :=
  M.presheaf.map (homOfLE h).op x

theorem sectionRes_comp {U V W : X.Opens} (hVU : V ≤ U) (hWV : W ≤ V) (x : Γ(M,U)) :
    sectionRes M hWV (sectionRes M hVU x) = sectionRes M (hWV.trans hVU) x :=
  (ConcreteCategory.congr_hom
    (M.presheaf.map_comp (homOfLE hVU).op (homOfLE hWV).op) x).symm

theorem sectionRes_smul {U V : X.Opens} (hVU : V ≤ U) (a : Γ(X,U)) (x : Γ(M,U)) :
    sectionRes M hVU (a • x) =
      X.presheaf.map (homOfLE hVU).op a • sectionRes M hVU x :=
  M.map_smul (homOfLE hVU) a x

end Restriction

variable (r θ : ℂ)

def firstVectorAt (i : Fin 2) (a : Fin 3) (W : (projectiveCurve r θ).Opens)
    (hW : W ≤ curveToSurface r θ ⁻¹ᵁ firstNormalOpen r θ i a) : Γ(actualNormal r θ,W) :=
  sectionRes (actualNormal r θ) hW (firstSourceNormalVector r θ i a)

def secondVectorAt (i : Fin 2) (a : Fin 3) (W : (projectiveCurve r θ).Opens)
    (hW : W ≤ curveToSurface r θ ⁻¹ᵁ secondNormalOpen r θ i a) : Γ(actualNormal r θ,W) :=
  sectionRes (actualNormal r θ) hW (secondSourceNormalVector r θ i a)

theorem firstVectorAt_restrict (i : Fin 2) (a : Fin 3) {W Z : (projectiveCurve r θ).Opens}
    (hW : W ≤ curveToSurface r θ ⁻¹ᵁ firstNormalOpen r θ i a) (hZW : Z ≤ W) :
    sectionRes (actualNormal r θ) hZW (firstVectorAt r θ i a W hW) =
      firstVectorAt r θ i a Z (hZW.trans hW) :=
  sectionRes_comp (actualNormal r θ) hW hZW _

theorem secondVectorAt_restrict (i : Fin 2) (a : Fin 3) {W Z : (projectiveCurve r θ).Opens}
    (hW : W ≤ curveToSurface r θ ⁻¹ᵁ secondNormalOpen r θ i a) (hZW : Z ≤ W) :
    sectionRes (actualNormal r θ) hZW (secondVectorAt r θ i a W hW) =
      secondVectorAt r θ i a Z (hZW.trans hW) :=
  sectionRes_comp (actualNormal r θ) hW hZW _

/-- Same-coordinate vectors agree on every genuine common curve open. -/
theorem firstVectorAt_agree (i₁ i₂ : Fin 2) (a₁ a₂ : Fin 3)
    (W : (projectiveCurve r θ).Opens)
    (h₁ : W ≤ curveToSurface r θ ⁻¹ᵁ firstNormalOpen r θ i₁ a₁)
    (h₂ : W ≤ curveToSurface r θ ⁻¹ᵁ firstNormalOpen r θ i₂ a₂) :
    firstVectorAt r θ i₁ a₁ W h₁ = firstVectorAt r θ i₂ a₂ W h₂ := by
  let V := firstNormalOpen r θ i₁ a₁ ⊓ firstNormalOpen r θ i₂ a₂
  have hWV : W ≤ curveToSurface r θ ⁻¹ᵁ V := fun _ hx => ⟨h₁ hx,h₂ hx⟩
  have he := congrArg (sectionRes (actualNormal r θ) hWV)
    (firstSourceVectors_agree r θ i₁ i₂ a₁ a₂ V inf_le_left inf_le_right)
  have hl : sectionRes (actualNormal r θ) hWV (firstSourceOn r θ i₁ a₁ V inf_le_left) =
      firstVectorAt r θ i₁ a₁ W h₁ := sectionRes_comp (actualNormal r θ) _ hWV _
  have hr : sectionRes (actualNormal r θ) hWV (firstSourceOn r θ i₂ a₂ V inf_le_right) =
      firstVectorAt r θ i₂ a₂ W h₂ := sectionRes_comp (actualNormal r θ) _ hWV _
  exact hl.symm.trans (he.trans hr)

theorem secondVectorAt_agree (i₁ i₂ : Fin 2) (a₁ a₂ : Fin 3)
    (W : (projectiveCurve r θ).Opens)
    (h₁ : W ≤ curveToSurface r θ ⁻¹ᵁ secondNormalOpen r θ i₁ a₁)
    (h₂ : W ≤ curveToSurface r θ ⁻¹ᵁ secondNormalOpen r θ i₂ a₂) :
    secondVectorAt r θ i₁ a₁ W h₁ = secondVectorAt r θ i₂ a₂ W h₂ := by
  let V := secondNormalOpen r θ i₁ a₁ ⊓ secondNormalOpen r θ i₂ a₂
  have hWV : W ≤ curveToSurface r θ ⁻¹ᵁ V := fun _ hx => ⟨h₁ hx,h₂ hx⟩
  have he := congrArg (sectionRes (actualNormal r θ) hWV)
    (secondSourceVectors_agree r θ i₁ i₂ a₁ a₂ V inf_le_left inf_le_right)
  have hl : sectionRes (actualNormal r θ) hWV (secondSourceOn r θ i₁ a₁ V inf_le_left) =
      secondVectorAt r θ i₁ a₁ W h₁ := sectionRes_comp (actualNormal r θ) _ hWV _
  have hr : sectionRes (actualNormal r θ) hWV (secondSourceOn r θ i₂ a₂ V inf_le_right) =
      secondVectorAt r θ i₂ a₂ W h₂ := sectionRes_comp (actualNormal r θ) _ hWV _
  exact hl.symm.trans (he.trans hr)

/-- The original inverse-square transition on an arbitrary subopen of
the old quartic overlap. -/
def normalCoefficientAt (W : (projectiveCurve r θ).Opens) (hW : W ≤ overlapProjectivePatch r θ) :
    Γ(projectiveCurve r θ,W) :=
  (projectiveCurve r θ).presheaf.map (homOfLE hW).op
    (normalTransitionUnit r θ : Γ(projectiveCurve r θ,overlapProjectivePatch r θ))

/-- The actual intrinsic vectors have exactly the transition of the
existing normal module sheaf, on every simultaneous chart refinement. -/
theorem vectorAt_transition (i₁ i₂ : Fin 2) (a₁ a₂ : Fin 3)
    (W : (projectiveCurve r θ).Opens) (hW : W ≤ overlapProjectivePatch r θ)
    (h₁ : W ≤ curveToSurface r θ ⁻¹ᵁ firstNormalOpen r θ i₁ a₁)
    (h₂ : W ≤ curveToSurface r θ ⁻¹ᵁ secondNormalOpen r θ i₂ a₂) :
    secondVectorAt r θ i₂ a₂ W h₂ =
      normalCoefficientAt r θ W hW • firstVectorAt r θ i₁ a₁ W h₁ := by
  let V := firstNormalOpen r θ i₁ a₁ ⊓ secondNormalOpen r θ i₂ a₂
  have hWV : W ≤ curveToSurface r θ ⁻¹ᵁ V := fun _ hx => ⟨h₁ hx,h₂ hx⟩
  let c := transitionCoefficient r θ i₁ i₂ a₁ a₂ V inf_le_left inf_le_right
  have he := congrArg (sectionRes (actualNormal r θ) hWV)
    (sourceCrossVectors_transition r θ i₁ i₂ a₁ a₂ V inf_le_left inf_le_right)
  have hl : sectionRes (actualNormal r θ) hWV (secondSourceOn r θ i₂ a₂ V inf_le_right) =
      secondVectorAt r θ i₂ a₂ W h₂ := sectionRes_comp (actualNormal r θ) _ hWV _
  have hr : sectionRes (actualNormal r θ) hWV (firstSourceOn r θ i₁ a₁ V inf_le_left) =
      firstVectorAt r θ i₁ a₁ W h₁ := sectionRes_comp (actualNormal r θ) _ hWV _
  have hc : (projectiveCurve r θ).presheaf.map (homOfLE hWV).op ((curveToSurface r θ).app V c) =
      normalCoefficientAt r θ W hW :=
    normalTransition_pullback r θ V
      (normalCommon_le_overlap r θ i₁ i₂ a₁ a₂ V inf_le_left inf_le_right) W hW hWV
  have hs := sectionRes_smul (actualNormal r θ) hWV ((curveToSurface r θ).app V c)
    (firstSourceOn r θ i₁ a₁ V inf_le_left)
  exact hl.symm.trans (he.trans (hs.trans (congrArg₂ (fun a x => a • x) hc hr)))

end CycleQ2NormalVectorOnCurve
end


end


section

/-! Functorial transport from a proved source-normal model isomorphism
through the actual module-sheaf pushforward and the canonical internal-Hom
adjunction. This construction retains the intrinsic surface-side normal
sheaf and uses genuine cohomology functors on its sheaf morphisms. -/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2SurfaceNormalTransport

open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite
  CycleQ2SurfaceNormalCohomology CycleQ2CartierProjectiveCover
  CycleQ2ProjectiveCurveSurface CycleQ2GeometricProjectiveNormalClass
  CycleQ2SourceNormalSheaf CycleQ2NormalPushforwardIso
  CycleQ2GeometricIntrinsicNormal CycleQ2GeometricDifferentialSheaf
  CycleQ2GeometricSheafCohomologyScalar CycleQ2SeedTrace

variable (r θ : ℂ)

local instance surfaceHasExt :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology (projectiveSurface r θ)) AddCommGrpCat.{0}) :=
  HasExt.standard _

abbrev intrinsicSurfaceNormalModule : (projectiveSurface r θ).Modules :=
  literalNormalDirectImageSheaf r θ

abbrev intrinsicSurfaceNormalSheaf :=
  additiveSheaf (projectiveSurface r θ).sheaf (intrinsicSurfaceNormalModule r θ)

abbrev IntrinsicNormalH1 := (intrinsicSurfaceNormalSheaf r θ).H' 1 ⊤

variable (e : actualNormal r θ ≅ normalModuleSheaf r θ)

def surfaceNormalModelIso :
    intrinsicSurfaceNormalModule r θ ≅
      (Scheme.Modules.pushforward (curveToSurface r θ)).obj (normalModuleSheaf r θ) :=
  (actualNormalPushforwardIso r θ).symm ≪≫
    (Scheme.Modules.pushforward (curveToSurface r θ)).mapIso e

def surfaceNormalAdditiveIso : intrinsicSurfaceNormalSheaf r θ ≅ pushedNormalSheaf r θ :=
  (SheafOfModules.toSheaf (ringSheaf (projectiveSurface r θ).sheaf)).mapIso
    (surfaceNormalModelIso r θ e)

def normalH1Equiv : IntrinsicNormalH1 r θ ≃+ NormalH1OnSurface r θ :=
  (((Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology (projectiveSurface r θ)) 1).mapIso
    (surfaceNormalAdditiveIso r θ e)).app (op ⊤)).addCommGroupIsoToAddEquiv

def intrinsicNormalClass (hr : r ≠ 0) (p : Poly) (hp : p.IsHomogeneous 6) :
    IntrinsicNormalH1 r θ :=
  (normalH1Equiv r θ e).symm (normalClassOnSurface r θ hr p hp)

theorem normalH1Equiv_class (hr : r ≠ 0) (p : Poly) (hp : p.IsHomogeneous 6) :
    normalH1Equiv r θ e (intrinsicNormalClass r θ e hr p hp) =
      normalClassOnSurface r θ hr p hp :=
  (normalH1Equiv r θ e).apply_symm_apply _

theorem intrinsicNormalClass_zero_iff (hr : r ≠ 0) (p : Poly) (hp : p.IsHomogeneous 6) :
    intrinsicNormalClass r θ e hr p hp = 0 ↔ normalClass r θ hr p hp = 0 := by
  change (normalH1Equiv r θ e).symm (normalClassOnSurface r θ hr p hp) = 0 ↔ _
  rw [map_eq_zero_iff _ (normalH1Equiv r θ e).symm.injective]
  exact normalClassOnSurface_zero_iff r θ hr p hp

/-- The actual composite sheaf morphism, before applying cohomology. -/
def intrinsicCubicMorphism (hr : r ≠ 0) (σ : Poly) (hσ : σ.IsHomogeneous 3) :
    intrinsicSurfaceNormalSheaf r θ ⟶ pushedDegreeOneSheaf r θ :=
  (surfaceNormalAdditiveIso r θ e).hom ≫
    (TopCat.Sheaf.pushforward AddCommGrpCat.{0} (curveToSurface r θ).base).map
      (cubicAdditiveMorphism r θ hr σ hσ)

def intrinsicCubicH1Map (hr : r ≠ 0) (σ : Poly) (hσ : σ.IsHomogeneous 3) :
    IntrinsicNormalH1 r θ →+ (pushedDegreeOneSheaf r θ).H' 1 ⊤ :=
  (((Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology (projectiveSurface r θ)) 1).map
    (intrinsicCubicMorphism r θ e hr σ hσ)).app (op ⊤)).hom

theorem intrinsicCubicH1Map_apply (hr : r ≠ 0) (σ : Poly) (hσ : σ.IsHomogeneous 3)
    (x : IntrinsicNormalH1 r θ) :
    intrinsicCubicH1Map r θ e hr σ hσ x =
      cubicH1OnSurface r θ hr σ hσ (normalH1Equiv r θ e x) := by
  let H := Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology (projectiveSurface r θ)) 1
  exact ConcreteCategory.congr_hom
    (congrArg (fun f => f.app (op ⊤)) (H.map_comp
      (surfaceNormalAdditiveIso r θ e).hom
      ((TopCat.Sheaf.pushforward AddCommGrpCat.{0} (curveToSurface r θ).base).map
        (cubicAdditiveMorphism r θ hr σ hσ)))) x

theorem intrinsicCubicH1Map_class (hr : r ≠ 0) (p : Poly) (hp : p.IsHomogeneous 6)
    (σ : Poly) (hσ : σ.IsHomogeneous 3) :
    intrinsicCubicH1Map r θ e hr σ hσ (intrinsicNormalClass r θ e hr p hp) =
      cubicH1OnSurface r θ hr σ hσ (normalClassOnSurface r θ hr p hp) := by
  rw [intrinsicCubicH1Map_apply, normalH1Equiv_class]

theorem intrinsicCubicH1Map_class_zero_iff (hr : r ≠ 0) (p : Poly) (hp : p.IsHomogeneous 6)
    (σ : Poly) (hσ : σ.IsHomogeneous 3) :
    intrinsicCubicH1Map r θ e hr σ hσ (intrinsicNormalClass r θ e hr p hp) = 0 ↔
      cubicH1Map r θ hr σ hσ (normalClass r θ hr p hp) = 0 := by
  rw [intrinsicCubicH1Map_class]
  exact cubicH1OnSurface_normalClass_zero_iff r θ hr p hp σ hσ

end CycleQ2SurfaceNormalTransport
end

end


section

/-!
# The actual local coefficient of cubic multiplication

The cubic morphism on the inverse-square normal model uses a degree-one
fraction. In the original coordinate frame its coefficient is the ordinary
dehomogenized cubic, restricted from the actual coordinate chart. These
identities fix the coefficient before composing with the canonical
differential-sheaf isomorphism.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace CycleQ2CubicSheafCoefficients

open CategoryTheory Opposite AlgebraicGeometry MvPolynomial
open CycleQ2SeedTrace CycleQ2NormalConnecting CycleQ2GeometricProjectiveCurve
  CycleQ2GeometricProjectiveNormalClass CycleQ2GeometricProjectiveAffine
  CycleQ2GeometricProjectiveAffineCoefficients CycleQ2GeometricAffineCurveCharts

/-- The homogeneous degree-zero fraction of a cubic on a coordinate chart. -/
def coordinateCubicFraction (r θ : ℂ) (j : Fin 4) (σ : Poly)
    (hσ : σ.IsHomogeneous 3) : ProjectiveCoordinateRing r θ j :=
  HomogeneousLocalization.Away.mk (curveGrade r θ) (coordinate_mem_grade r θ j)
    3 (curveMap r θ σ) (by simpa using curveMap_mem_grade r θ hσ)

theorem cubicLocalImage_coordinate (r θ : ℂ) (f x g : CurveRing r θ)
    (hf : f ∈ curveGrade r θ 4) (hx : x ∈ curveGrade r θ 1)
    (hg : g ∈ curveGrade r θ 3) (hfg : f = x * g)
    (σ : Poly) (hσ : σ.IsHomogeneous 3) :
    (degreeOneFrameEquiv r θ f 3 hf x g hx hg hfg).symm
        (cubicLocalImage r θ f hf g hg σ hσ) =
      HomogeneousLocalization.awayMap (curveGrade r θ) hg hfg
        (HomogeneousLocalization.Away.mk (curveGrade r θ) hx 3 (curveMap r θ σ)
          (by simpa using curveMap_mem_grade r θ hσ)) := by
  apply (degreeOneFrameEquiv r θ f 3 hf x g hx hg hfg).injective
  rw [LinearEquiv.apply_symm_apply]
  apply Subtype.ext
  rw [degreeOneFrameEquiv_coe, HomogeneousLocalization.awayMap_mk,
    HomogeneousLocalization.Away.val_mk]
  change awayFraction r θ f 2 (curveMap r θ σ * g ^ 2) = _
  rw [← Localization.mk_one_eq_algebraMap, Localization.mk_mul, awayFraction,
    Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [Submonoid.coe_one, Subtype.coe_mk, one_mul, mul_one]
  rw [hfg]
  ring

theorem firstCubicImage_coordinate (r θ : ℂ) (σ : Poly)
    (hσ : σ.IsHomogeneous 3) :
    (firstDegreeOneEquiv r θ).symm (firstCubicImage r θ σ hσ) =
      HomogeneousLocalization.awayMap (curveGrade r θ)
        (firstFrameComplement_grade r θ) (firstFrame_factorization r θ)
        (coordinateCubicFraction r θ 1 σ hσ) :=
  cubicLocalImage_coordinate r θ _ _ _ (curveG1_mem_grade r θ)
    (coordinate_mem_grade r θ 1) (firstFrameComplement_grade r θ)
    (firstFrame_factorization r θ) σ hσ

theorem secondCubicImage_coordinate (r θ : ℂ) (σ : Poly)
    (hσ : σ.IsHomogeneous 3) :
    (secondDegreeOneEquiv r θ).symm (secondCubicImage r θ σ hσ) =
      HomogeneousLocalization.awayMap (curveGrade r θ)
        (secondFrameComplement_grade r θ) (secondFrame_factorization r θ)
        (coordinateCubicFraction r θ 2 σ hσ) :=
  cubicLocalImage_coordinate r θ _ _ _ (curveG2_mem_grade r θ)
    (coordinate_mem_grade r θ 2) (secondFrameComplement_grade r θ)
    (secondFrame_factorization r θ) σ hσ

/-- The first coefficient is obtained from the actual affine presentation. -/
def firstCoefficient (r θ : ℂ) (σ : Poly) :
    Γ(projectiveCurve r θ, coordinateProjectivePatch r θ 1) :=
  (firstCoordinateSectionsEquiv r θ).symm (firstChartMap r θ (firstDehomogenize σ))

/-- The second coefficient uses the second actual affine presentation. -/
def secondCoefficient (r θ : ℂ) (σ : Poly) :
    Γ(projectiveCurve r θ, coordinateProjectivePatch r θ 2) :=
  (secondCoordinateSectionsEquiv r θ).symm (secondChartMap r θ (secondDehomogenize σ))

theorem firstCoefficient_fraction (r θ : ℂ) (σ : Poly)
    (hσ : σ.IsHomogeneous 3) :
    firstCoefficient r θ σ =
      (Proj.basicOpenIsoAway (curveGrade r θ) (coordinateDen r θ 1)
        (coordinate_mem_grade r θ 1) (by decide)).hom
          (coordinateCubicFraction r θ 1 σ hσ) := by
  apply (firstCoordinateSectionsEquiv r θ).injective
  rw [firstCoefficient, RingEquiv.apply_symm_apply]
  change _ = firstCoordinateEquiv r θ
    ((Proj.basicOpenIsoAway (curveGrade r θ) (coordinateDen r θ 1)
      (coordinate_mem_grade r θ 1) (by decide)).inv
        ((Proj.basicOpenIsoAway (curveGrade r θ) (coordinateDen r θ 1)
          (coordinate_mem_grade r θ 1) (by decide)).hom _))
  rw [Iso.hom_inv_id_apply]
  exact (firstCoordinateEquiv_fraction r θ 3 σ hσ).symm

theorem secondCoefficient_fraction (r θ : ℂ) (σ : Poly)
    (hσ : σ.IsHomogeneous 3) :
    secondCoefficient r θ σ =
      (Proj.basicOpenIsoAway (curveGrade r θ) (coordinateDen r θ 2)
        (coordinate_mem_grade r θ 2) (by decide)).hom
          (coordinateCubicFraction r θ 2 σ hσ) := by
  apply (secondCoordinateSectionsEquiv r θ).injective
  rw [secondCoefficient, RingEquiv.apply_symm_apply]
  change _ = secondCoordinateEquiv r θ
    ((Proj.basicOpenIsoAway (curveGrade r θ) (coordinateDen r θ 2)
      (coordinate_mem_grade r θ 2) (by decide)).inv
        ((Proj.basicOpenIsoAway (curveGrade r θ) (coordinateDen r θ 2)
          (coordinate_mem_grade r θ 2) (by decide)).hom _))
  rw [Iso.hom_inv_id_apply]
  exact (secondCoordinateEquiv_fraction r θ 3 σ hσ).symm

theorem firstCubicSection_coordinate (r θ : ℂ) (σ : Poly)
    (hσ : σ.IsHomogeneous 3) :
    firstSheafFrame r θ (firstCubicSection r θ σ hσ) =
      (projectiveCurve r θ).presheaf.map
        (homOfLE (firstProjectivePatch_le_firstCoordinate r θ)).op
          (firstCoefficient r θ σ) := by
  rw [firstCubicSection, firstDegreeOneSectionsEquiv_coordinate,
    firstCubicImage_coordinate, firstCoefficient_fraction r θ σ hσ]
  exact congrArg (fun k => k (coordinateCubicFraction r θ 1 σ hσ))
    (Proj.awayMap_awayToSection (curveGrade r θ)
      (firstFrameComplement_grade r θ) (firstFrame_factorization r θ))

theorem secondCubicSection_coordinate (r θ : ℂ) (σ : Poly)
    (hσ : σ.IsHomogeneous 3) :
    secondSheafFrame r θ (secondCubicSection r θ σ hσ) =
      (projectiveCurve r θ).presheaf.map
        (homOfLE (secondProjectivePatch_eq_secondCoordinate r θ).le).op
          (secondCoefficient r θ σ) := by
  rw [secondCubicSection, secondDegreeOneSectionsEquiv_coordinate,
    secondCubicImage_coordinate, secondCoefficient_fraction r θ σ hσ]
  exact congrArg (fun k => k (coordinateCubicFraction r θ 2 σ hσ))
    (Proj.awayMap_awayToSection (curveGrade r θ)
      (secondFrameComplement_grade r θ) (secondFrame_factorization r θ))

theorem firstCubicSection_coordinate_on (r θ : ℂ) (σ : Poly)
    (hσ : σ.IsHomogeneous 3) (O : (projectiveCurve r θ).Opens)
    (hO : O ≤ firstProjectivePatch r θ) :
    Twisted.firstLocalSectionsEquiv (projectiveCurve r θ).sheaf
        (firstProjectivePatch r θ) (secondProjectivePatch r θ) (overlapProjectivePatch r θ)
        (overlapProjectivePatch_eq r θ) (projectiveTransitionUnit r θ) O hO
        ((degreeOneSheaf r θ).obj.map (homOfLE hO).op (firstCubicSection r θ σ hσ)) =
      (projectiveCurve r θ).presheaf.map
        (homOfLE (hO.trans (firstProjectivePatch_le_firstCoordinate r θ))).op
          (firstCoefficient r θ σ) := by
  have hn := Twisted.firstLocalSectionsEquiv_naturality (projectiveCurve r θ).sheaf
    (firstProjectivePatch r θ) (secondProjectivePatch r θ) (overlapProjectivePatch r θ)
    (overlapProjectivePatch_eq r θ) (projectiveTransitionUnit r θ)
    hO le_rfl (firstCubicSection r θ σ hσ)
  change _ = Twisted.res (projectiveCurve r θ).sheaf hO
    (firstSheafFrame r θ (firstCubicSection r θ σ hσ)) at hn
  exact hn.trans ((congrArg (Twisted.res (projectiveCurve r θ).sheaf hO)
    (firstCubicSection_coordinate r θ σ hσ)).trans
      (Twisted.res_comp (projectiveCurve r θ).sheaf
        (firstProjectivePatch_le_firstCoordinate r θ) hO (firstCoefficient r θ σ)))

theorem secondCubicSection_coordinate_on (r θ : ℂ) (σ : Poly)
    (hσ : σ.IsHomogeneous 3) (O : (projectiveCurve r θ).Opens)
    (hO : O ≤ secondProjectivePatch r θ) :
    Twisted.secondLocalSectionsEquiv (projectiveCurve r θ).sheaf
        (firstProjectivePatch r θ) (secondProjectivePatch r θ) (overlapProjectivePatch r θ)
        (overlapProjectivePatch_eq r θ) (projectiveTransitionUnit r θ) O hO
        ((degreeOneSheaf r θ).obj.map (homOfLE hO).op (secondCubicSection r θ σ hσ)) =
      (projectiveCurve r θ).presheaf.map
        (homOfLE (hO.trans (secondProjectivePatch_le_secondCoordinate r θ))).op
          (secondCoefficient r θ σ) := by
  have hn := Twisted.secondLocalSectionsEquiv_naturality (projectiveCurve r θ).sheaf
    (firstProjectivePatch r θ) (secondProjectivePatch r θ) (overlapProjectivePatch r θ)
    (overlapProjectivePatch_eq r θ) (projectiveTransitionUnit r θ)
    hO le_rfl (secondCubicSection r θ σ hσ)
  change _ = Twisted.res (projectiveCurve r θ).sheaf hO
    (secondSheafFrame r θ (secondCubicSection r θ σ hσ)) at hn
  exact hn.trans ((congrArg (Twisted.res (projectiveCurve r θ).sheaf hO)
    (secondCubicSection_coordinate r θ σ hσ)).trans
      (Twisted.res_comp (projectiveCurve r θ).sheaf
        (secondProjectivePatch_le_secondCoordinate r θ) hO (secondCoefficient r θ σ)))

end CycleQ2CubicSheafCoefficients
end

end


section

/-!
# Cubic multiplication as an actual differential-sheaf morphism

The existing inverse-square normal model maps to the genuine complex
differential sheaf through the original cubic morphism and canonical
isomorphism. On every subopen of each original patch, its coefficient is
the actual dehomogenized cubic and its differential generator is the
original oriented canonical frame.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace CycleQ2CubicDifferentialMap

open CategoryTheory Opposite AlgebraicGeometry MvPolynomial
open CycleQ2SeedTrace CycleQ2GeometricProjectiveCurve
  CycleQ2GeometricProjectiveNormalClass CycleQ2GeometricDifferentialSheaf
  CycleQ2GeometricCanonicalSheaf CycleQ2GeometricProjectiveAffine
  CycleQ2GeometricSparseJacobianCover CycleQ2GeometricAffineOverlap
  CycleQ2GeometricTwistedFrameMap CycleQ2CubicSheafCoefficients

local instance (r θ : ℂ) (O : (projectiveCurve r θ).Opens) :
    Module Γ(projectiveCurve r θ, O)
      ((projectiveDifferentialSheaf r θ).val.obj (op O)) :=
  inferInstanceAs (Module ((ringSheaf (projectiveCurve r θ).sheaf).obj.obj (op O))
    ((projectiveDifferentialSheaf r θ).val.obj (op O)))

abbrev normalModel (r θ : ℂ) : (projectiveCurve r θ).Modules :=
  normalModuleSheaf r θ

abbrev degreeOneModel (r θ : ℂ) : (projectiveCurve r θ).Modules :=
  degreeOneModuleSheaf r θ

abbrev curveDifferentials (r θ : ℂ) : (projectiveCurve r θ).Modules :=
  projectiveDifferentialSheaf r θ

def firstNormalCoordinate (r θ : ℂ) (O : (projectiveCurve r θ).Opens)
    (hO : O ≤ firstProjectivePatch r θ) :
    (normalModuleSheaf r θ).val.obj (op O) ≃+ Γ(projectiveCurve r θ, O) :=
  Twisted.firstLocalSectionsEquiv (projectiveCurve r θ).sheaf
    (firstProjectivePatch r θ) (secondProjectivePatch r θ) (overlapProjectivePatch r θ)
    (overlapProjectivePatch_eq r θ) (normalTransitionUnit r θ) O hO

def secondNormalCoordinate (r θ : ℂ) (O : (projectiveCurve r θ).Opens)
    (hO : O ≤ secondProjectivePatch r θ) :
    (normalModuleSheaf r θ).val.obj (op O) ≃+ Γ(projectiveCurve r θ, O) :=
  Twisted.secondLocalSectionsEquiv (projectiveCurve r θ).sheaf
    (firstProjectivePatch r θ) (secondProjectivePatch r θ) (overlapProjectivePatch r θ)
    (overlapProjectivePatch_eq r θ) (normalTransitionUnit r θ) O hO

variable (r θ : ℂ) (hr : r ≠ 0)
  (h1 : jacobianIdeal (firstEquations r θ) = ⊤)
  (h2 : jacobianIdeal (secondEquations r θ) = ⊤)

/-- The actual cubic morphism followed by the actual canonical sheaf iso. -/
def modelCubicDifferential (σ : Poly) (hσ : σ.IsHomogeneous 3) :
    normalModel r θ ⟶ curveDifferentials r θ :=
  let f : normalModel r θ ⟶ degreeOneModel r θ := cubicMorphism r θ hr σ hσ
  let e : degreeOneModel r θ ≅ curveDifferentials r θ := canonicalSheafIso r θ h1 h2 hr
  f ≫ e.hom

theorem modelCubicDifferential_first_local (σ : Poly) (hσ : σ.IsHomogeneous 3)
    (O : (projectiveCurve r θ).Opens) (hO : O ≤ firstProjectivePatch r θ)
    (s : (normalModuleSheaf r θ).val.obj (op O)) :
    (modelCubicDifferential r θ hr h1 h2 σ hσ).val.app (op O) s =
      (firstNormalCoordinate r θ O hO s *
        (projectiveCurve r θ).presheaf.map
          (homOfLE (hO.trans (firstProjectivePatch_le_firstCoordinate r θ))).op
            (firstCoefficient r θ σ)) •
      (show (projectiveDifferentialSheaf r θ).val.obj (op O) from
        (projectiveDifferentialSheaf r θ).val.map (homOfLE hO).op
          (CycleQ2GeometricProjectiveFrameRestriction.firstDenominatorFrame r θ h1 h2)) := by
  have hc := frameMorphism_first_local (projectiveCurve r θ).sheaf
    (degreeOneModuleSheaf r θ) (firstProjectivePatch r θ) (secondProjectivePatch r θ)
    (overlapProjectivePatch r θ) (overlapProjectivePatch_eq r θ)
    (normalTransitionUnit r θ) (projective_twoOpen_cover r θ hr)
    (firstCubicSection r θ σ hσ) (secondCubicSection r θ σ hσ)
    (cubicSection_transition r θ σ hσ) O hO s
  change (cubicMorphism r θ hr σ hσ).val.app (op O) s =
    firstNormalCoordinate r θ O hO s •
      (degreeOneSheaf r θ).obj.map (homOfLE hO).op (firstCubicSection r θ σ hσ) at hc
  let F : (degreeOneSheaf r θ).obj.obj (op O) ≃+ Γ(projectiveCurve r θ, O) :=
    Twisted.firstLocalSectionsEquiv (projectiveCurve r θ).sheaf
      (firstProjectivePatch r θ) (secondProjectivePatch r θ) (overlapProjectivePatch r θ)
      (overlapProjectivePatch_eq r θ) (projectiveTransitionUnit r θ) O hO
  let ω : (projectiveDifferentialSheaf r θ).val.obj (op O) :=
    (projectiveDifferentialSheaf r θ).val.map (homOfLE hO).op
      (CycleQ2GeometricProjectiveFrameRestriction.firstDenominatorFrame r θ h1 h2)
  have hs := TwistedModule.firstLocalSections_smul (projectiveCurve r θ).sheaf
    (firstProjectivePatch r θ) (secondProjectivePatch r θ) (overlapProjectivePatch r θ)
    (overlapProjectivePatch_eq r θ) (projectiveTransitionUnit r θ) O hO
    (firstNormalCoordinate r θ O hO s)
    ((degreeOneSheaf r θ).obj.map (homOfLE hO).op (firstCubicSection r θ σ hσ))
  have hz := firstCubicSection_coordinate_on r θ σ hσ O hO
  have hcoef : F ((cubicMorphism r θ hr σ hσ).val.app (op O) s) =
      firstNormalCoordinate r θ O hO s *
        (projectiveCurve r θ).presheaf.map
          (homOfLE (hO.trans (firstProjectivePatch_le_firstCoordinate r θ))).op
            (firstCoefficient r θ σ) :=
    (congrArg F hc).trans (hs.trans
      (congrArg (fun b : Γ(projectiveCurve r θ, O) =>
        firstNormalCoordinate r θ O hO s * b) hz))
  have hk : (modelCubicDifferential r θ hr h1 h2 σ hσ).val.app (op O) s =
      F ((cubicMorphism r θ hr σ hσ).val.app (op O) s) • ω :=
    canonicalSheafMap_first_local r θ hr h1 h2 O hO
      ((cubicMorphism r θ hr σ hσ).val.app (op O) s)
  exact hk.trans (congrArg (fun b : Γ(projectiveCurve r θ, O) => b • ω) hcoef)

theorem modelCubicDifferential_second_local (σ : Poly) (hσ : σ.IsHomogeneous 3)
    (O : (projectiveCurve r θ).Opens) (hO : O ≤ secondProjectivePatch r θ)
    (s : (normalModuleSheaf r θ).val.obj (op O)) :
    (modelCubicDifferential r θ hr h1 h2 σ hσ).val.app (op O) s =
      (secondNormalCoordinate r θ O hO s *
        (projectiveCurve r θ).presheaf.map
          (homOfLE (hO.trans (secondProjectivePatch_le_secondCoordinate r θ))).op
            (secondCoefficient r θ σ)) •
      (show (projectiveDifferentialSheaf r θ).val.obj (op O) from
        (projectiveDifferentialSheaf r θ).val.map (homOfLE hO).op
          (CycleQ2GeometricProjectiveFrameRestriction.secondDenominatorFrame r θ h1 h2)) := by
  have hc := frameMorphism_second_local (projectiveCurve r θ).sheaf
    (degreeOneModuleSheaf r θ) (firstProjectivePatch r θ) (secondProjectivePatch r θ)
    (overlapProjectivePatch r θ) (overlapProjectivePatch_eq r θ)
    (normalTransitionUnit r θ) (projective_twoOpen_cover r θ hr)
    (firstCubicSection r θ σ hσ) (secondCubicSection r θ σ hσ)
    (cubicSection_transition r θ σ hσ) O hO s
  change (cubicMorphism r θ hr σ hσ).val.app (op O) s =
    secondNormalCoordinate r θ O hO s •
      (degreeOneSheaf r θ).obj.map (homOfLE hO).op (secondCubicSection r θ σ hσ) at hc
  let F : (degreeOneSheaf r θ).obj.obj (op O) ≃+ Γ(projectiveCurve r θ, O) :=
    Twisted.secondLocalSectionsEquiv (projectiveCurve r θ).sheaf
      (firstProjectivePatch r θ) (secondProjectivePatch r θ) (overlapProjectivePatch r θ)
      (overlapProjectivePatch_eq r θ) (projectiveTransitionUnit r θ) O hO
  let ω : (projectiveDifferentialSheaf r θ).val.obj (op O) :=
    (projectiveDifferentialSheaf r θ).val.map (homOfLE hO).op
      (CycleQ2GeometricProjectiveFrameRestriction.secondDenominatorFrame r θ h1 h2)
  have hs := TwistedModule.secondLocalSections_smul (projectiveCurve r θ).sheaf
    (firstProjectivePatch r θ) (secondProjectivePatch r θ) (overlapProjectivePatch r θ)
    (overlapProjectivePatch_eq r θ) (projectiveTransitionUnit r θ) O hO
    (secondNormalCoordinate r θ O hO s)
    ((degreeOneSheaf r θ).obj.map (homOfLE hO).op (secondCubicSection r θ σ hσ))
  have hz := secondCubicSection_coordinate_on r θ σ hσ O hO
  have hcoef : F ((cubicMorphism r θ hr σ hσ).val.app (op O) s) =
      secondNormalCoordinate r θ O hO s *
        (projectiveCurve r θ).presheaf.map
          (homOfLE (hO.trans (secondProjectivePatch_le_secondCoordinate r θ))).op
            (secondCoefficient r θ σ) :=
    (congrArg F hc).trans (hs.trans
      (congrArg (fun b : Γ(projectiveCurve r θ, O) =>
        secondNormalCoordinate r θ O hO s * b) hz))
  have hk : (modelCubicDifferential r θ hr h1 h2 σ hσ).val.app (op O) s =
      F ((cubicMorphism r θ hr σ hσ).val.app (op O) s) • ω :=
    canonicalSheafMap_second_local r θ hr h1 h2 O hO
      ((cubicMorphism r θ hr σ hσ).val.app (op O) s)
  exact hk.trans (congrArg (fun b : Γ(projectiveCurve r θ, O) => b • ω) hcoef)

/-- At the literal seed both Jacobian-cover hypotheses are already proved. -/
def literalModelCubicDifferential (σ : Poly) (hσ : σ.IsHomogeneous 3) :
    normalModel 57 1 ⟶ curveDifferentials 57 1 :=
  modelCubicDifferential 57 1 (by norm_num)
    CycleQ2GeometricIncidenceJacobianCover.first_chart_jacobianIdeal_eq_top
    CycleQ2GeometricIncidenceJacobianCover.second_chart_jacobianIdeal_eq_top σ hσ

end CycleQ2CubicDifferentialMap
end

end


section

/-! The genuine affine normal frame, transported through the original
Cartesian open chart, has exactly the fixed projective normal vector.
The normalization is derived from the actual normal adjunction square. -/
set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace CycleQ2NormalChartFrameNormalization

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
open CycleQ2GeometricIntrinsicNormal CycleQ2SourceNormalSheaf CycleQ2NormalPushforward
open CycleQ2SourceNormalRaw CycleQ2SourceNormalVectors CycleQ2SourceNormalPatch
open CycleQ2SourceNormalRestriction CycleQ2NormalSectionRestriction
open CycleQ2GeometricSurfaceAdjunction CycleQ2GeometricAffineCurveCharts
open CycleQ2GeometricNormalCharts CycleQ2NormalVectorLocalFrame
open scoped TensorProduct

section Generic
variable {X Y : Scheme.{0}} {A B : CommRingCat.{0}} (φ : A ⟶ B)
  (j : X ⟶ Y) (iS : Spec A ⟶ Y) (iC : Spec B ⟶ X)
  [IsOpenImmersion iS] [IsOpenImmersion iC]
  (H : IsPullback (Spec.map φ) iC iS j)

/-- The canonical source restriction and the original affine functional
comparison are the same map, including their original equation values. -/
theorem raw_chartSection (x : Γ(sourceNormal j, iC.opensRange)) :
    letI : Algebra A B := φ.hom.toAlgebra
    sourceNormalRawAddEquiv φ (sourceChartNormalSection j (Spec.map φ) iC iS H x) =
      normalOpenAlgebraConormalEquiv φ j iS iC H
        ((normalPushforward j).app iS.opensRange
          ((sourceRangeSectionsIso j (Spec.map φ) iC iS H).hom x)) := by
  let : Algebra A B := φ.hom.toAlgebra
  exact congrArg (fun f : (normalDirectImageSheaf (Spec.map φ)).val.obj (op ⊤) =>
    (affineNormalAlgebraConormalEquiv φ).toEquiv.toFun f)
    (sourceChartNormalSection_globalComparison j (Spec.map φ) iC iS H x)

/-- The inverse normalization is proved before specializing the affine
algebras, so its equality uses the actual comparison maps directly. -/
theorem raw_chartSection_inverse :
    letI : Algebra A B := φ.hom.toAlgebra
    ∀ v : (B ⊗[A] (RingHom.ker φ.hom).Cotangent →ₗ[B] B),
    sourceChartNormalSection j (Spec.map φ) iC iS H
      ((sourceRangeSectionsIso j (Spec.map φ) iC iS H).inv
        ((sectionEquiv j iS.opensRange).symm
          ((normalOpenAlgebraConormalEquiv φ j iS iC H).symm v))) =
      (sourceNormalRawAddEquiv φ).symm v := by
  let : Algebra A B := φ.hom.toAlgebra
  intro v
  let E := normalOpenAlgebraConormalEquiv φ j iS iC H
  let P := sectionEquiv j iS.opensRange
  let Q := (sourceRangeSectionsIso j (Spec.map φ) iC iS H).addCommGroupIsoToAddEquiv
  let x := Q.symm (P.symm (E.symm v))
  have hp : (normalPushforward j).app iS.opensRange
      ((sourceRangeSectionsIso j (Spec.map φ) iC iS H).hom x) = E.symm v :=
    (congrArg P (Q.apply_symm_apply (P.symm (E.symm v)))).trans
      (P.apply_symm_apply (E.symm v))
  apply (sourceNormalRawAddEquiv φ).injective
  exact (raw_chartSection φ j iS iC H x).trans
    ((congrArg E hp).trans ((E.apply_symm_apply v).trans
      ((sourceNormalRawAddEquiv φ).apply_symm_apply v).symm))

end Generic

section Actual
variable (q h : AffinePoly) (g₁ g₂ k : SurfacePoly) (n : Fin 2) (t : Fin 3)
variable {X Y : Scheme.{0}} (j : X ⟶ Y)
  (iS : Spec (CommRingCat.of (NormalSurfacePatch q h g₁ g₂ k n t)) ⟶ Y)
  (iC : Spec (CommRingCat.of (NormalCurvePatch q h g₁ g₂ k n t)) ⟶ X)
  [IsOpenImmersion iS] [IsOpenImmersion iC]
  (H : IsPullback (patchImmersion q h g₁ g₂ k n t) iC iS j)

/-- The original source normal vector on the actual curve chart image.
Its surface-side functional is the already fixed (G₂,-G₁) vector. -/
def chartSourceVector : Γ(sourceNormal j, iC.opensRange) :=
  (sourceRangeSectionsIso j (patchImmersion q h g₁ g₂ k n t) iC iS H).inv
    ((sectionEquiv j iS.opensRange).symm
      (normalChartVectorSection q h g₁ g₂ k n t j iS iC H))

/-- The actual pushforward comparison returns the original fixed
surface-side vector, with no rescaling. -/
theorem chartSourceVector_pushforward :
    (normalPushforward j).app iS.opensRange
        ((sourceRangeSectionsIso j (patchImmersion q h g₁ g₂ k n t) iC iS H).hom
          (chartSourceVector q h g₁ g₂ k n t j iS iC H)) =
      normalChartVectorSection q h g₁ g₂ k n t j iS iC H := by
  let f := normalChartVectorSection q h g₁ g₂ k n t j iS iC H
  let e :=
    (sourceRangeSectionsIso j (patchImmersion q h g₁ g₂ k n t) iC iS H).addCommGroupIsoToAddEquiv
  have he := e.apply_symm_apply ((sectionEquiv j iS.opensRange).symm f)
  exact (congrArg ((normalPushforward j).app iS.opensRange) he).trans
    ((sectionEquiv j iS.opensRange).apply_symm_apply f)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Restriction through the genuine normal sheaf isomorphism gives the
same affine source vector used in the all-open local frame. -/
theorem chartSourceVector_chart :
    sourceChartNormalSection j (patchImmersion q h g₁ g₂ k n t) iC iS H
        (chartSourceVector q h g₁ g₂ k n t j iS iC H) =
      normalVectorSection q h g₁ g₂ k n t := by
  have he :
      (normalOpenAlgebraConormalEquiv (patchRingMap q h g₁ g₂ k n t) j iS iC H).symm
        (normalVector q h g₁ g₂ k n t) =
      normalChartVectorSection q h g₁ g₂ k n t j iS iC H := by
    unfold normalChartVectorSection normalChartIntrinsicEquiv patchRingMap
    rfl
  have hs : (sourceNormalRawAddEquiv (patchRingMap q h g₁ g₂ k n t)).symm
      (normalVector q h g₁ g₂ k n t) = normalVectorSection q h g₁ g₂ k n t := by
    unfold normalVectorSection rawEquiv sourceNormalRawEquiv
    rfl
  have hh := raw_chartSection_inverse (patchRingMap q h g₁ g₂ k n t) j iS iC H
    (normalVector q h g₁ g₂ k n t)
  let T : (normalDirectImageSheaf j).val.obj (op iS.opensRange) →
      Γ(sourceNormal (patchImmersion q h g₁ g₂ k n t), ⊤) := fun f =>
    sourceChartNormalSection j (patchImmersion q h g₁ g₂ k n t) iC iS H
      ((sourceRangeSectionsIso j (patchImmersion q h g₁ g₂ k n t) iC iS H).inv
        ((sectionEquiv j iS.opensRange).symm f))
  exact (congrArg T he).symm.trans (hh.trans hs)

/-- The source-normal coordinate isomorphism on the genuine affine chart. -/
def chartCoordinateIso :
    (sourceNormal j).restrict iC ≅
      structureModule (Spec (CommRingCat.of (NormalCurvePatch q h g₁ g₂ k n t))) :=
  sourceNormalRestrictionIso j (patchImmersion q h g₁ g₂ k n t) iC iS H ≪≫
    (affineSourceFrameIso q h g₁ g₂ k n t).symm

theorem curveVector_top :
    curveVector q h g₁ g₂ k n t ⊤ = normalVectorSection q h g₁ g₂ k n t :=
  ConcreteCategory.congr_hom
    ((sourceNormal (patchImmersion q h g₁ g₂ k n t)).presheaf.map_id (op ⊤))
      (normalVectorSection q h g₁ g₂ k n t)

/-- The genuine chart coordinate sends the fixed projective normal
vector to one. This fixes the normalization before descent. -/
theorem chartCoordinateIso_vector :
    (chartCoordinateIso q h g₁ g₂ k n t j iS iC H).hom.app ⊤
      ((sourceNormal j).presheaf.map (homOfLE (iC.image_le_opensRange ⊤)).op
        (chartSourceVector q h g₁ g₂ k n t j iS iC H)) =
      (1 : Γ(Spec (CommRingCat.of (NormalCurvePatch q h g₁ g₂ k n t)), ⊤)) := by
  let f := (affineSourceFrameIso q h g₁ g₂ k n t).inv.app ⊤
  exact (congrArg f (chartSourceVector_chart q h g₁ g₂ k n t j iS iC H)).trans
    ((congrArg f (curveVector_top q h g₁ g₂ k n t).symm).trans
      (affineSourceFrameIso_inv_vector q h g₁ g₂ k n t ⊤))

end Actual
end CycleQ2NormalChartFrameNormalization
end

end


section

/-! Actual intrinsic normal frames on the projective augmented-Jacobian
opens. Their generator is the prescribed source normal vector, on every
curve subopen, as fixed by the canonical affine restriction comparison. -/
set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace CycleQ2ProjectiveNormalFrames

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open CycleQ2GeometricProjectiveCurve CycleQ2GeometricCanonicalGluing
open CycleQ2SourceNormalSheaf CycleQ2SourceNormalVectors
open CycleQ2SourceNormalPatch CycleQ2NormalSectionRestriction
open CycleQ2GeometricSurfaceAdjunction CycleQ2GeometricAffineCurveCharts
open CycleQ2GeometricNormalCharts CycleQ2NormalChartFrameNormalization
open CycleQ2NormalVectorOnCurve

/-- Restrict a proved natural frame to an actual smaller open. -/
def restrictFrame {X : TopCat.{0}} {R : X.Sheaf CommRingCat.{0}}
    {M : SheafOfModules.{0} (TwistedModule.ringSheaf R)} {U V : Opens X}
    (e : LocalFrame R M U) (hVU : V ≤ U) : LocalFrame R M V where
  app O hO := e.app O (hO.trans hVU)
  naturality hPO hO x := e.naturality hPO (hO.trans hVU) x

section Chart
variable (q h : AffinePoly) (g₁ g₂ k : SurfacePoly) (n : Fin 2) (t : Fin 3)
variable {X Y : Scheme.{0}} (j : X ⟶ Y)
  (iS : Spec (CommRingCat.of (NormalSurfacePatch q h g₁ g₂ k n t)) ⟶ Y)
  (iC : Spec (CommRingCat.of (NormalCurvePatch q h g₁ g₂ k n t)) ⟶ X)
  [IsOpenImmersion iS] [IsOpenImmersion iC]
  (H : IsPullback (patchImmersion q h g₁ g₂ k n t) iC iS j)

/-- The original intrinsic normal is a line on the genuine curve
preimage of every actual normal surface chart. -/
def chartFrame : LocalFrame X.sheaf (sourceNormal j) (j ⁻¹ᵁ iS.opensRange) :=
  restrictFrame
    (CycleQ2OpenImmersionFrame.localFrame iC (sourceNormal j)
      (chartCoordinateIso q h g₁ g₂ k n t j iS iC H))
    (sourceRange_eq j (patchImmersion q h g₁ g₂ k n t) iC iS H).ge

/-- This local frame's inverse-one section is exactly the restriction
of the original fixed normal functional on every curve subopen. -/
theorem chartFrame_generator (W : X.Opens) (hW : W ≤ j ⁻¹ᵁ iS.opensRange) :
    frameGenerator (chartFrame q h g₁ g₂ k n t j iS iC H) W hW =
      sectionRes (sourceNormal j) hW
        ((sectionEquiv j iS.opensRange).symm
          (normalChartVectorSection q h g₁ g₂ k n t j iS iC H)) := by
  let E := CycleQ2OpenImmersionFrame.localFrame iC (sourceNormal j)
    (chartCoordinateIso q h g₁ g₂ k n t j iS iC H)
  let P := j ⁻¹ᵁ iS.opensRange
  let hP : P ≤ iC.opensRange :=
    (sourceRange_eq j (patchImmersion q h g₁ g₂ k n t) iC iS H).ge
  have hg : frameGenerator E iC.opensRange le_rfl =
      chartSourceVector q h g₁ g₂ k n t j iS iC H :=
    CycleQ2OpenImmersionFrame.frameGenerator_eq_normalized iC (sourceNormal j)
      (chartCoordinateIso q h g₁ g₂ k n t j iS iC H)
      (chartSourceVector q h g₁ g₂ k n t j iS iC H)
      (chartCoordinateIso_vector q h g₁ g₂ k n t j iS iC H)
  have hp : sectionRes (sourceNormal j) hP
      (chartSourceVector q h g₁ g₂ k n t j iS iC H) =
      (sectionEquiv j iS.opensRange).symm
        (normalChartVectorSection q h g₁ g₂ k n t j iS iC H) :=
    (sourceRangeSectionsIso j (patchImmersion q h g₁ g₂ k n t) iC iS H).addCommGroupIsoToAddEquiv.apply_symm_apply _
  have htop : frameGenerator (chartFrame q h g₁ g₂ k n t j iS iC H) P le_rfl =
      (sectionEquiv j iS.opensRange).symm
        (normalChartVectorSection q h g₁ g₂ k n t j iS iC H) :=
    (frameGenerator_naturality E hP le_rfl).symm.trans
      ((congrArg (sectionRes (sourceNormal j) hP) hg).trans hp)
  exact (frameGenerator_naturality (chartFrame q h g₁ g₂ k n t j iS iC H) hW le_rfl).symm.trans
    (congrArg (sectionRes (sourceNormal j) hW) htop)

end Chart

section Actual
open CycleQ2GeometricLiteralSurface CycleQ2GeometricSurfaceJacobianCharts
open CycleQ2GeometricSurfacePrincipalCurveCharts CycleQ2GeometricSurfaceDehomogenizedCharts
open CycleQ2SeedTrace CycleQ2SeedCechTheta CycleQ2NormalConnecting

def firstNormalFrame (r θ : ℂ) (i : Fin 2) (a : Fin 3) :
    LocalFrame (projectiveCurve r θ).sheaf (actualNormal r θ)
      (curveToSurface r θ ⁻¹ᵁ firstNormalOpen r θ i a) :=
  chartFrame (firstQuadric r) (firstCubic θ)
    (firstSurfaceDehomogenize (originalG1 r)) (firstSurfaceDehomogenize originalG2)
    (firstSurfaceDehomogenize (thetaK θ)) i a
    (curveToSurface r θ) (firstNormalSurfaceImmersion r θ i a)
    (firstNormalCurveImmersion r θ i a) (firstNormalCurve_isPullback r θ i a)

def secondNormalFrame (r θ : ℂ) (i : Fin 2) (a : Fin 3) :
    LocalFrame (projectiveCurve r θ).sheaf (actualNormal r θ)
      (curveToSurface r θ ⁻¹ᵁ secondNormalOpen r θ i a) :=
  chartFrame (secondQuadric r) (secondCubic θ)
    (secondSurfaceDehomogenize (originalG1 r)) (secondSurfaceDehomogenize originalG2)
    (secondSurfaceDehomogenize (thetaK θ)) i a
    (curveToSurface r θ) (secondNormalSurfaceImmersion r θ i a)
    (secondNormalCurveImmersion r θ i a) (secondNormalCurve_isPullback r θ i a)

theorem firstNormalFrame_generator (r θ : ℂ) (i : Fin 2) (a : Fin 3)
    (W : (projectiveCurve r θ).Opens)
    (hW : W ≤ curveToSurface r θ ⁻¹ᵁ firstNormalOpen r θ i a) :
    frameGenerator (firstNormalFrame r θ i a) W hW = firstVectorAt r θ i a W hW :=
  chartFrame_generator (firstQuadric r) (firstCubic θ)
    (firstSurfaceDehomogenize (originalG1 r)) (firstSurfaceDehomogenize originalG2)
    (firstSurfaceDehomogenize (thetaK θ)) i a
    (curveToSurface r θ) (firstNormalSurfaceImmersion r θ i a)
    (firstNormalCurveImmersion r θ i a) (firstNormalCurve_isPullback r θ i a) W hW

theorem secondNormalFrame_generator (r θ : ℂ) (i : Fin 2) (a : Fin 3)
    (W : (projectiveCurve r θ).Opens)
    (hW : W ≤ curveToSurface r θ ⁻¹ᵁ secondNormalOpen r θ i a) :
    frameGenerator (secondNormalFrame r θ i a) W hW = secondVectorAt r θ i a W hW :=
  chartFrame_generator (secondQuadric r) (secondCubic θ)
    (secondSurfaceDehomogenize (originalG1 r)) (secondSurfaceDehomogenize originalG2)
    (secondSurfaceDehomogenize (thetaK θ)) i a
    (curveToSurface r θ) (secondNormalSurfaceImmersion r θ i a)
    (secondNormalCurveImmersion r θ i a) (secondNormalCurve_isPullback r θ i a) W hW

end Actual
end CycleQ2ProjectiveNormalFrames
end


end


section

/-! The actual intrinsic normal of the literal projective curve is the
original inverse-square normal module. Every local generator is the
fixed (G₂,-G₁) vector, and descent uses the proved Jacobian covers and the
actual quartic transition computation. -/
set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace CycleQ2IntrinsicNormalModel

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open CycleQ2GeometricProjectiveCurve CycleQ2GeometricProjectiveNormalClass
open CycleQ2GeometricLiteralSurface CycleQ2SourceNormalSheaf
open CycleQ2GeometricSurfaceJacobianCharts CycleQ2GeometricSurfaceNormalCover
open CycleQ2GeometricCanonicalGluing CycleQ2GeometricModuleLocalIso
open CycleQ2ProjectiveNormalFrames CycleQ2NormalVectorOnCurve CycleQ2LocalFrameGluing
open CycleQ2GeometricProjectiveAffine

private abbrev C := projectiveCurve (57 : ℂ) 1
private abbrev N := actualNormal (57 : ℂ) 1

local instance normalSectionModule (W : C.Opens) :
    Module Γ(C,W) (N.val.obj (op W)) := (N.val.obj (op W)).isModule

abbrev NormalIndex := Fin 2 × Fin 3

def firstFamily (p : NormalIndex) : C.Opens :=
  curveToSurface 57 1 ⁻¹ᵁ firstNormalOpen 57 1 p.1 p.2

def secondFamily (p : NormalIndex) : C.Opens :=
  curveToSurface 57 1 ⁻¹ᵁ secondNormalOpen 57 1 p.1 p.2

theorem firstFamily_cover : (⨆ p, firstFamily p) = coordinateProjectivePatch 57 1 1 := by
  simpa only [firstFamily, firstNormalOpen_preimage, iSup_prod] using first_normalOpen_cover

theorem secondFamily_cover : (⨆ p, secondFamily p) = coordinateProjectivePatch 57 1 2 := by
  simpa only [secondFamily, secondNormalOpen_preimage, iSup_prod] using second_normalOpen_cover

theorem firstFamily_le (p : NormalIndex) : firstFamily p ≤ coordinateProjectivePatch 57 1 1 :=
  (le_iSup firstFamily p).trans firstFamily_cover.le

theorem secondFamily_le (p : NormalIndex) : secondFamily p ≤ coordinateProjectivePatch 57 1 2 :=
  (le_iSup secondFamily p).trans secondFamily_cover.le

private theorem firstFrames_compatible (p q : NormalIndex) :
    frameGenerator (firstNormalFrame 57 1 p.1 p.2) (firstFamily p ⊓ firstFamily q) inf_le_left =
      frameGenerator (firstNormalFrame 57 1 q.1 q.2) (firstFamily p ⊓ firstFamily q) inf_le_right :=
  (firstNormalFrame_generator 57 1 p.1 p.2 _ inf_le_left).trans
    ((firstVectorAt_agree 57 1 p.1 q.1 p.2 q.2 _ inf_le_left inf_le_right).trans
      (firstNormalFrame_generator 57 1 q.1 q.2 _ inf_le_right).symm)

private theorem secondFrames_compatible (p q : NormalIndex) :
    frameGenerator (secondNormalFrame 57 1 p.1 p.2) (secondFamily p ⊓ secondFamily q) inf_le_left =
      frameGenerator (secondNormalFrame 57 1 q.1 q.2) (secondFamily p ⊓ secondFamily q) inf_le_right :=
  (secondNormalFrame_generator 57 1 p.1 p.2 _ inf_le_left).trans
    ((secondVectorAt_agree 57 1 p.1 q.1 p.2 q.2 _ inf_le_left inf_le_right).trans
      (secondNormalFrame_generator 57 1 q.1 q.2 _ inf_le_right).symm)

/-- The six actual first-coordinate normal charts supply a genuine frame. -/
def firstCoordinateFrame : LocalFrame C.sheaf N (coordinateProjectivePatch 57 1 1) :=
  glueLocalFrames C.sheaf N (coordinateProjectivePatch 57 1 1) firstFamily
    firstFamily_le firstFamily_cover.ge (fun p => firstNormalFrame 57 1 p.1 p.2)
    firstFrames_compatible

/-- The same descent constructs the second-coordinate intrinsic frame. -/
def secondCoordinateFrame : LocalFrame C.sheaf N (coordinateProjectivePatch 57 1 2) :=
  glueLocalFrames C.sheaf N (coordinateProjectivePatch 57 1 2) secondFamily
    secondFamily_le secondFamily_cover.ge (fun p => secondNormalFrame 57 1 p.1 p.2)
    secondFrames_compatible

theorem firstCoordinateFrame_generator (p : NormalIndex) (W : C.Opens) (hW : W ≤ firstFamily p) :
    frameGenerator firstCoordinateFrame W (hW.trans (firstFamily_le p)) =
      firstVectorAt 57 1 p.1 p.2 W hW :=
  (glueLocalFrames_generator C.sheaf N (coordinateProjectivePatch 57 1 1) firstFamily
    firstFamily_le firstFamily_cover.ge (fun p => firstNormalFrame 57 1 p.1 p.2)
    firstFrames_compatible p W hW).trans (firstNormalFrame_generator 57 1 p.1 p.2 W hW)

theorem secondCoordinateFrame_generator (p : NormalIndex) (W : C.Opens) (hW : W ≤ secondFamily p) :
    frameGenerator secondCoordinateFrame W (hW.trans (secondFamily_le p)) =
      secondVectorAt 57 1 p.1 p.2 W hW :=
  (glueLocalFrames_generator C.sheaf N (coordinateProjectivePatch 57 1 2) secondFamily
    secondFamily_le secondFamily_cover.ge (fun p => secondNormalFrame 57 1 p.1 p.2)
    secondFrames_compatible p W hW).trans (secondNormalFrame_generator 57 1 p.1 p.2 W hW)

def firstQuarticFrame : LocalFrame C.sheaf N (firstProjectivePatch 57 1) :=
  restrictFrame firstCoordinateFrame (firstProjectivePatch_le_firstCoordinate 57 1)

def secondQuarticFrame : LocalFrame C.sheaf N (secondProjectivePatch 57 1) :=
  restrictFrame secondCoordinateFrame (secondProjectivePatch_le_secondCoordinate 57 1)

theorem firstQuarticFrame_generator (p : NormalIndex) (W : C.Opens)
    (hW : W ≤ firstProjectivePatch 57 1) (hp : W ≤ firstFamily p) :
    frameGenerator firstQuarticFrame W hW = firstVectorAt 57 1 p.1 p.2 W hp :=
  firstCoordinateFrame_generator p W hp

theorem secondQuarticFrame_generator (p : NormalIndex) (W : C.Opens)
    (hW : W ≤ secondProjectivePatch 57 1) (hp : W ≤ secondFamily p) :
    frameGenerator secondQuarticFrame W hW = secondVectorAt 57 1 p.1 p.2 W hp :=
  secondCoordinateFrame_generator p W hp

private abbrev overlap := overlapProjectivePatch (57 : ℂ) 1
private theorem overlap_first : overlap ≤ firstProjectivePatch 57 1 :=
  (overlapProjectivePatch_eq 57 1).le.trans inf_le_left
private theorem overlap_second : overlap ≤ secondProjectivePatch 57 1 :=
  (overlapProjectivePatch_eq 57 1).le.trans inf_le_right

def overlapFamily (p : NormalIndex × NormalIndex) : C.Opens :=
  (overlap ⊓ firstFamily p.1) ⊓ secondFamily p.2

theorem overlapFamily_cover : overlap ≤ ⨆ p, overlapFamily p := by
  intro x hx
  have hx₁ : x ∈ coordinateProjectivePatch 57 1 1 :=
    ((firstProjectivePatch_le_firstCoordinate 57 1) (overlap_first hx))
  have hx₂ : x ∈ coordinateProjectivePatch 57 1 2 :=
    ((secondProjectivePatch_le_secondCoordinate 57 1) (overlap_second hx))
  have h₁ : x ∈ ⨆ p, firstFamily p := firstFamily_cover.ge hx₁
  have h₂ : x ∈ ⨆ p, secondFamily p := secondFamily_cover.ge hx₂
  obtain ⟨p,hp⟩ := Opens.mem_iSup.mp h₁
  obtain ⟨q,hq⟩ := Opens.mem_iSup.mp h₂
  exact (le_iSup overlapFamily (p,q)) ⟨⟨hx,hp⟩,hq⟩

/-- The two descended intrinsic frames have exactly the transition of
the original normal module sheaf. -/
theorem quarticFrame_transition :
    frameGenerator secondQuarticFrame overlap overlap_second =
      (normalTransitionUnit 57 1 : Γ(C,overlap)) •
        frameGenerator firstQuarticFrame overlap overlap_first := by
  let F := addSheaf N
  apply F.eq_of_locally_eq' overlapFamily overlap
    (fun _ => homOfLE (show overlapFamily _ ≤ overlap from inf_le_left.trans inf_le_left))
    overlapFamily_cover
  intro p
  let W := overlapFamily p
  have hW : W ≤ overlap := inf_le_left.trans inf_le_left
  have h₁ : W ≤ firstFamily p.1 := inf_le_left.trans inf_le_right
  have h₂ : W ≤ secondFamily p.2 := inf_le_right
  have hs : sectionRes N hW (frameGenerator secondQuarticFrame overlap overlap_second) =
      secondVectorAt 57 1 p.2.1 p.2.2 W h₂ :=
    (frameGenerator_naturality secondQuarticFrame hW overlap_second).trans
      (secondQuarticFrame_generator p.2 W (hW.trans overlap_second) h₂)
  have hf : sectionRes N hW (frameGenerator firstQuarticFrame overlap overlap_first) =
      firstVectorAt 57 1 p.1.1 p.1.2 W h₁ :=
    (frameGenerator_naturality firstQuarticFrame hW overlap_first).trans
      (firstQuarticFrame_generator p.1 W (hW.trans overlap_first) h₁)
  have hr := sectionRes_smul N hW (normalTransitionUnit 57 1 : Γ(C,overlap))
    (frameGenerator firstQuarticFrame overlap overlap_first)
  have ht := vectorAt_transition 57 1 p.1.1 p.2.1 p.1.2 p.2.2 W hW h₁ h₂
  exact hs.trans (ht.trans ((congrArg
    (fun x : Γ(N,W) => normalCoefficientAt 57 1 W hW • x) hf.symm).trans hr.symm))

/-- The actual intrinsic normal sheaf of the literal curve is the
original inverse-square normal module, with the original fixed vectors. -/
def intrinsicNormalIso : actualNormal 57 1 ≅ normalModuleSheaf 57 1 :=
  canonicalIsoOfOverlap C.sheaf (firstProjectivePatch 57 1) (secondProjectivePatch 57 1)
    overlap (overlapProjectivePatch_eq 57 1) (normalTransitionUnit 57 1)
    N firstQuarticFrame secondQuarticFrame (projective_twoOpen_cover 57 1 (by norm_num))
    quarticFrame_transition

def firstModelCoordinate (W : C.Opens) (hW : W ≤ firstProjectivePatch 57 1) :=
  TwistedModule.firstLocalSectionsLinearEquiv C.sheaf
    (firstProjectivePatch 57 1) (secondProjectivePatch 57 1)
    overlap (overlapProjectivePatch_eq 57 1) (normalTransitionUnit 57 1) W hW

def secondModelCoordinate (W : C.Opens) (hW : W ≤ secondProjectivePatch 57 1) :=
  TwistedModule.secondLocalSectionsLinearEquiv C.sheaf
    (firstProjectivePatch 57 1) (secondProjectivePatch 57 1)
    overlap (overlapProjectivePatch_eq 57 1) (normalTransitionUnit 57 1) W hW

theorem intrinsicNormalIso_first (W : C.Opens) (hW : W ≤ firstProjectivePatch 57 1)
    (x : Γ(N,W)) :
    firstModelCoordinate W hW (intrinsicNormalIso.hom.val.app (op W) x) =
      firstQuarticFrame.app W hW x :=
  canonicalIso_hom_first C.sheaf (firstProjectivePatch 57 1) (secondProjectivePatch 57 1)
    overlap (overlapProjectivePatch_eq 57 1) (normalTransitionUnit 57 1)
    N firstQuarticFrame secondQuarticFrame (projective_twoOpen_cover 57 1 (by norm_num))
    (generatorTransition_of_overlap C.sheaf (firstProjectivePatch 57 1) (secondProjectivePatch 57 1)
      overlap (overlapProjectivePatch_eq 57 1) (normalTransitionUnit 57 1)
      N firstQuarticFrame secondQuarticFrame quarticFrame_transition) W hW x

theorem intrinsicNormalIso_second (W : C.Opens) (hW : W ≤ secondProjectivePatch 57 1)
    (x : Γ(N,W)) :
    secondModelCoordinate W hW (intrinsicNormalIso.hom.val.app (op W) x) =
      secondQuarticFrame.app W hW x :=
  canonicalIso_hom_second C.sheaf (firstProjectivePatch 57 1) (secondProjectivePatch 57 1)
    overlap (overlapProjectivePatch_eq 57 1) (normalTransitionUnit 57 1)
    N firstQuarticFrame secondQuarticFrame (projective_twoOpen_cover 57 1 (by norm_num))
    (generatorTransition_of_overlap C.sheaf (firstProjectivePatch 57 1) (secondProjectivePatch 57 1)
      overlap (overlapProjectivePatch_eq 57 1) (normalTransitionUnit 57 1)
      N firstQuarticFrame secondQuarticFrame quarticFrame_transition) W hW x

/-- The first original normal vector has model coordinate exactly one on
every matching normal-chart/quartic refinement. -/
theorem intrinsicNormalIso_first_vector (p : NormalIndex) (W : C.Opens)
    (hW : W ≤ firstProjectivePatch 57 1) (hp : W ≤ firstFamily p) :
    firstModelCoordinate W hW
      (intrinsicNormalIso.hom.val.app (op W) (firstVectorAt 57 1 p.1 p.2 W hp)) = 1 :=
  (intrinsicNormalIso_first W hW _).trans
    ((congrArg (firstQuarticFrame.app W hW) (firstQuarticFrame_generator p W hW hp).symm).trans
      ((firstQuarticFrame.app W hW).apply_symm_apply (1 : Γ(C,W))))

/-- The second original vector has the same fixed unit coordinate. -/
theorem intrinsicNormalIso_second_vector (p : NormalIndex) (W : C.Opens)
    (hW : W ≤ secondProjectivePatch 57 1) (hp : W ≤ secondFamily p) :
    secondModelCoordinate W hW
      (intrinsicNormalIso.hom.val.app (op W) (secondVectorAt 57 1 p.1 p.2 W hp)) = 1 :=
  (intrinsicNormalIso_second W hW _).trans
    ((congrArg (secondQuarticFrame.app W hW) (secondQuarticFrame_generator p W hW hp).symm).trans
      ((secondQuarticFrame.app W hW).apply_symm_apply (1 : Γ(C,W))))

end CycleQ2IntrinsicNormalModel
end


end
