import Proposal.GeometricLiteralAbelJacobiTimeProjection
import Proposal.GeometricLiteralAmbientCylinder
import Proposal.GeometricLiteralThreefoldHodgeCech
import Proposal.GeometricFiniteCechOrbitPullback
import Proposal.GeometricSchemeCotangentMaps

/-!
# Pullback of two-forms by the second cylinder projection

The scheme differential of the moving family's projection to the smooth
fixed threefold induces a morphism of the exterior-square Kähler sheaves.
Pulling the native overlap cocycle through this morphism gives a derived
degree-one class on the actual time family.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2LiteralAbelJacobiQPullback

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
  CycleQ2GeometricExteriorSheaf CycleQ2GeometricDifferentialSheaf
  CycleQ2GeometricSchemeDifferentialMap CycleQ2GeometricAffineChartSections

attribute [local instance] CycleQ2GeometricExteriorSheaf.exteriorObjectModule

section Exterior

variable {X Y : Scheme.{0}} (j : X ⟶ Y) {M : Y.Modules} {N : X.Modules}
  (φ : M ⟶ (Scheme.Modules.pushforward j).obj N) (n : ℕ)

/-- The section map from the pushforward morphism, with its scalar ring map exposed. -/
def onSections (U : Y.Opens) : M.val.obj (op U) →ₛₗ[(j.app U).hom] N.val.obj (op (j ⁻¹ᵁ U)) where
  toFun := φ.val.app (op U)
  map_add' := (φ.val.app (op U)).hom.map_add
  map_smul' := (φ.val.app (op U)).hom.map_smul

private theorem restriction_square {U V : Y.Opens} (h : V ⟶ U)
    (x : ⋀[Γ(Y,U)]^n (M.val.obj (op U))) :
    exteriorMap (j.app V).hom (onSections j φ V) n
      (exteriorMap (Y.presheaf.map h.op).hom (M.val.restrictₛₗ h.op) n x) =
    exteriorMap (X.presheaf.map ((Opens.map j.base).map h).op).hom
      (N.val.restrictₛₗ ((Opens.map j.base).map h).op) n
        (exteriorMap (j.app U).hom (onSections j φ U) n x) := by
  have hx : x ∈ Submodule.span Γ(Y,U) (Set.range (exteriorPower.ιMulti Γ(Y,U) n)) := by
    rw [exteriorPower.ιMulti_span]; trivial
  induction hx using Submodule.span_induction with
  | mem _ hx =>
    obtain ⟨a, rfl⟩ := hx
    simp only [exteriorMap_wedge]
    apply congrArg (exteriorPower.ιMulti _ n)
    funext k
    exact PresheafOfModules.naturality_apply φ.val h.op (a k)
  | zero => simp only [map_zero]
  | add _ _ _ _ hx hy => simp only [map_add,hx,hy]
  | smul r x _ hx =>
    simp only [map_smulₛₗ, hx]
    exact congrArg (fun a : Γ(X,j ⁻¹ᵁ V) => a • _) (ConcreteCategory.congr_hom (j.naturality h.op) r)

private abbrev extM := exteriorSheaf Y.sheaf M.val n
private abbrev extN := exteriorSheaf X.sheaf N.val n

private def rawComponent (U : Y.Opens) :
    (⋀[Γ(Y,U)]^n (M.val.obj (op U))) →ₗ[Γ(Y,U)]
      ((Scheme.Modules.pushforward j).obj (extN (N := N) n)).val.obj (op U) where
  toFun x := exteriorSection X.sheaf N.val n (j ⁻¹ᵁ U) (exteriorMap (j.app U).hom (onSections j φ U) n x)
  map_add' _ _ := by simp only [map_add]
  map_smul' r x := by
    change exteriorSection X.sheaf N.val n (j ⁻¹ᵁ U)
      (exteriorMap (j.app U).hom (onSections j φ U) n (r • x)) = j.app U r • _
    rw [map_smulₛₗ, map_smul]

set_option maxHeartbeats 850000 in
private def rawPull : exteriorPresheaf Y.sheaf.obj M.val n ⟶
    ((Scheme.Modules.pushforward j).obj (extN (N := N) n)).val where
  app U := ConcreteCategory.ofHom (C := ModuleCat Γ(Y,U.unop))
    (X := (exteriorPresheaf Y.sheaf.obj M.val n).obj U)
    (Y := ((Scheme.Modules.pushforward j).obj (extN (N := N) n)).val.obj U)
    (rawComponent j φ n U.unop)
  naturality {U V} h := by
    apply ConcreteCategory.hom_ext
    intro x
    change exteriorSection X.sheaf N.val n _
      (exteriorMap (j.app V.unop).hom (onSections j φ V.unop) n
        (exteriorMap (Y.presheaf.map h).hom (M.val.restrictₛₗ h) n x)) =
      (extN (N := N) n).val.map ((Opens.map j.base).map h.unop).op
        (exteriorSection X.sheaf N.val n _ _)
    rw [exteriorSection_restrict]
    exact congrArg (exteriorSection X.sheaf N.val n _) (restriction_square j φ n h.unop x)

/-- Exterior powers of a semilinear morphism into the actual direct image. -/
def exteriorPull : extM (M := M) n ⟶ (Scheme.Modules.pushforward j).obj (extN (N := N) n) :=
  (exteriorSheafHomEquiv Y.sheaf M.val n _).symm (rawPull j φ n)

theorem exteriorPull_section (U : Y.Opens) (x : ⋀[Γ(Y,U)]^n (M.val.obj (op U))) :
    (exteriorPull j φ n).val.app (op U) (exteriorSection Y.sheaf M.val n U x) =
      exteriorSection X.sheaf N.val n (j ⁻¹ᵁ U) (exteriorMap (j.app U).hom (onSections j φ U) n x) := by
  exact congrArg (fun a => PresheafOfModules.Hom.app a (op U) x)
    ((exteriorSheafHomEquiv Y.sheaf M.val n _).apply_symm_apply (rawPull j φ n))

end Exterior

open CycleQ2LiteralThreefoldHodgeCech CycleQ2LiteralAbelJacobiTimeFamily
  CycleQ2LiteralAmbientSmooth CycleQ2IncidenceEtaleParameter CycleQ2LiteralAmbientCylinder
  CycleQ2LiteralIncidenceTimeCurve CycleQ2FiniteCechHOne CycleQ2LiteralThreefoldOverlapAtlas
  CycleQ2LiteralAmbientCharts CycleQ2FiniteCechOrbitPullback

variable (V : parameterScheme.Opens) (t : Fin 3 → ℂ)

/-- The second projection, landing in the actual smooth fibre that carries the Hodge class. -/
def toThreefold : family V t ⟶ Threefold := CycleQ2LiteralAbelJacobiTimeProjection.q V t ≫ fixedIso.hom

@[reassoc, simp] theorem toThreefold_overComplex :
    toThreefold V t ≫ structureMap = projection V t ≫ (timeOpen V).ι ≫ toComplex := by
  simp [toThreefold,structureMap]

abbrev familyCoefficient := schemeCoefficient (projection V t ≫ (timeOpen V).ι ≫ toComplex)
abbrev familyDifferentials := differentialSheaf (family V t).sheaf (familyCoefficient V t)
abbrev familyTwoForms := exteriorSheaf (family V t).sheaf (familyDifferentials V t).val 2
abbrev familyHodgeSheaf := CycleQ2GeometricModuleLocalIso.addSheaf (familyTwoForms V t)

private theorem compatible (U : Threefold.Opens) (c : ℂ) :
    (toThreefold V t).app U (coefficientOn Threefold.sheaf coefficients U c) =
      coefficientOn (family V t).sheaf (familyCoefficient V t) ((toThreefold V t) ⁻¹ᵁ U) c := by
  rw [coefficientOn_app, toThreefold_overComplex]

/-- The actual pushforward-adjoint pullback of Kähler two-forms under the second projection. -/
def qForms : TwoForms ⟶ (Scheme.Modules.pushforward (toThreefold V t)).obj (familyTwoForms V t) :=
  exteriorPull (toThreefold V t) (schemeDifferentialMap (toThreefold V t) _ _ (compatible V t)) 2

/-- Additive sheaf morphism used on every Čech overlap. -/
def qAdd : HodgeSheaf ⟶ push (toThreefold V t).base (familyHodgeSheaf V t) :=
  (SheafOfModules.toSheaf Threefold.ringCatSheaf).map (qForms V t)

local instance (X : Scheme.{0}) : HasExt.{1} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}) :=
  HasExt.standard _

/-- The pullback of the native two-form cocycle as a derived H¹ class on the time family. -/
def pulledHodgeClass (ω : NativeEdges)
    (faces : ∀ (i j k : Fin 4) (hij : i < j) (hjk : j < k), Face ω i j k hij hjk) :
    (familyHodgeSheaf V t).H' 1 ⊤ :=
  cechOneClass (cover (toThreefold V t).base fixedOpen)
    (cover_top _ _ fixedOpen_cover) (pullOne _ (qAdd V t) _ (hodgeCocycle ω faces).val)
    (pullOne_closed _ (qAdd V t) _ _ (fun i j k W hi hj hk =>
      ((hodgeCocycle ω faces).condition i j k W hi hj hk).symm))

end CycleQ2LiteralAbelJacobiQPullback
end

#print axioms CycleQ2LiteralAbelJacobiQPullback.qForms
#print axioms CycleQ2LiteralAbelJacobiQPullback.pulledHodgeClass
