import Proposal.GeometricLiteralAbelJacobiQPullback
import Proposal.GeometricExteriorLocalFrames
import Proposal.GeometricAffineCotangentReduction
import Proposal.GeometricLiteralCylinderEvaluation
import Proposal.GeometricLiteralAbelJacobiTimeContraction

/-!
# Evaluating a vector along an affine morphism on the sheaf of two-forms

The component of the resulting morphism on each open is interior multiplication
in the first slot followed by pullback of the surviving one-form.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralAbelJacobiEvaluationAffine

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
  CycleQ2GeometricExteriorSheaf CycleQ2GeometricDifferentialSheaf
  CycleQ2GeometricAffineDifferentialSheaf CycleQ2GeometricAffineKahlerSheaf
  CycleQ2GeometricSchemeDifferentialMap CycleQ2GeometricAffineCotangentReduction
  CycleQ2LiteralAbelJacobiQPullback

attribute [local instance] CycleQ2GeometricExteriorSheaf.exteriorObjectModule

section Exterior
variable {X Y : Scheme.{0}} (j : X ⟶ Y) {M : Y.Modules} {N : X.Modules}

abbrev functions (X : Scheme.{0}) := SheafOfModules.unit.{0} X.ringCatSheaf
variable (u : M ⟶ (Scheme.Modules.pushforward j).obj (functions X))
  (p : M ⟶ (Scheme.Modules.pushforward j).obj N)

private def detPair {S : Type} [CommRing S] (E : Type) [AddCommGroup E] [Module S E] :
    (⋀[S]^2 (S × E)) →ₗ[S] E :=
  exteriorPower.alternatingMapLinearEquiv
    { toFun := fun m => (m 0).1 • (m 1).2 - (m 1).1 • (m 0).2
      map_update_add' := by
        intro _ m i a b
        fin_cases i <;> simp [Function.update, add_smul, smul_add] <;> abel
      map_update_smul' := by
        intro _ m i r a
        fin_cases i <;> simp [Function.update, smul_sub, smul_smul, mul_comm]
      map_eq_zero_of_eq' := by
        intro m i k h hne
        fin_cases i <;> fin_cases k <;> simp_all }

private def pair (U : Y.Opens) : M.val.obj (op U) →ₛₗ[(j.app U).hom]
    Γ(X,j ⁻¹ᵁ U) × N.val.obj (op (j ⁻¹ᵁ U)) :=
  { toFun := fun x => (onSections j u U x, onSections j p U x)
    map_add' := fun x y => Prod.ext ((onSections j u U).map_add x y) ((onSections j p U).map_add x y)
    map_smul' := fun c x => Prod.ext ((onSections j u U).map_smulₛₗ c x) ((onSections j p U).map_smulₛₗ c x) }

private def onExterior (U : Y.Opens) :
    (⋀[Γ(Y,U)]^2 (M.val.obj (op U))) →ₗ[Γ(Y,U)] ((Scheme.Modules.pushforward j).obj N).val.obj (op U) where
  toFun w := detPair (S := Γ(X,j ⁻¹ᵁ U)) (N.val.obj (op (j ⁻¹ᵁ U))) (exteriorMap (j.app U).hom (pair j u p U) 2 w)
  map_add' a b := by simp
  map_smul' r w := by
    change detPair (S := Γ(X,j ⁻¹ᵁ U)) (N.val.obj (op (j ⁻¹ᵁ U))) (exteriorMap _ _ _ (r • w)) = (j.app U r) • _
    rw [map_smulₛₗ, map_smul]

private theorem onExterior_wedge (U : Y.Opens) (v : Fin 2 → M.val.obj (op U)) :
    onExterior j u p U (exteriorPower.ιMulti Γ(Y,U) 2 v) =
      (onSections j u U (v 0) : Γ(X,j ⁻¹ᵁ U)) • onSections j p U (v 1) -
      (onSections j u U (v 1) : Γ(X,j ⁻¹ᵁ U)) • onSections j p U (v 0) := by
  change detPair (S := Γ(X,j ⁻¹ᵁ U)) (N.val.obj (op (j ⁻¹ᵁ U))) (exteriorMap _ _ _ _) = _
  rw [exteriorMap_wedge, detPair, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  rfl

set_option maxHeartbeats 1300000 in
private def raw : exteriorPresheaf Y.sheaf.obj M.val 2 ⟶ ((Scheme.Modules.pushforward j).obj N).val where
  app U := ConcreteCategory.ofHom (C := ModuleCat Γ(Y,U.unop))
    (X := (exteriorPresheaf Y.sheaf.obj M.val 2).obj U)
    (Y := ((Scheme.Modules.pushforward j).obj N).val.obj U) (onExterior j u p U.unop)
  naturality {U V} h := by
    apply ConcreteCategory.hom_ext
    intro w
    change onExterior j u p V.unop (exteriorMap (Y.presheaf.map h).hom (M.val.restrictₛₗ h) 2 w) =
      ((Scheme.Modules.pushforward j).obj N).val.restrictₛₗ h (onExterior j u p U.unop w)
    have hw : w ∈ Submodule.span Γ(Y,U.unop) (Set.range (exteriorPower.ιMulti Γ(Y,U.unop) 2)) := by
      rw [exteriorPower.ιMulti_span]; trivial
    induction hw using Submodule.span_induction with
    | mem _ hm =>
      obtain ⟨a, rfl⟩ := hm
      rw [exteriorMap_wedge, onExterior_wedge, onExterior_wedge]
      let k := ((Opens.map j.base).map h.unop).op
      change _ = N.val.restrictₛₗ k (_ - _)
      rw [map_sub, map_smulₛₗ, map_smulₛₗ]
      have hu (x) := PresheafOfModules.naturality_apply u.val h x
      have hp (x) := PresheafOfModules.naturality_apply p.val h x
      exact congrArg₂ (· - ·) (congrArg₂ (· • ·) (hu _) (hp _)) (congrArg₂ (· • ·) (hu _) (hp _))
    | zero => simp only [map_zero]
    | add _ _ _ _ h₁ h₂ => simp only [map_add, h₁, h₂]
    | smul r x _ hx =>
      simp only [map_smulₛₗ, hx]
      rfl

/-- Pair a vector and the one-form pullback on the actual exterior sheaf. -/
def alongSheaf : exteriorSheaf Y.sheaf M.val 2 ⟶ (Scheme.Modules.pushforward j).obj N where
  val := (PresheafOfModules.homEquivOfIsLocallyBijective (toExteriorSheaf Y.sheaf M.val 2)
    ((Scheme.Modules.pushforward j).obj N).isSheaf).symm (raw j u p)

set_option maxHeartbeats 500000 in
private theorem alongSheaf_section (U : Y.Opens) (w : ⋀[Γ(Y,U)]^2 (M.val.obj (op U))) :
    (alongSheaf j u p).val.app (op U) (exteriorSection Y.sheaf M.val 2 U w) =
      onExterior j u p U w := by
  have h := (PresheafOfModules.homEquivOfIsLocallyBijective (toExteriorSheaf Y.sheaf M.val 2)
    ((Scheme.Modules.pushforward j).obj N).isSheaf).apply_symm_apply (raw j u p)
  exact congrArg (fun f : exteriorPresheaf Y.sheaf.obj M.val 2 ⟶ ((Scheme.Modules.pushforward j).obj N).val =>
    f.app (op U) w) h

theorem alongSheaf_wedge (U : Y.Opens) (a : Fin 2 → M.val.obj (op U)) :
    (alongSheaf j u p).val.app (op U) (wedgeSection Y.sheaf M.val 2 U a) =
      (onSections j u U (a 0) : Γ(X,j ⁻¹ᵁ U)) • onSections j p U (a 1) -
      (onSections j u U (a 1) : Γ(X,j ⁻¹ᵁ U)) • onSections j p U (a 0) :=
  (alongSheaf_section j u p U (exteriorPower.ιMulti Γ(Y,U) 2 a)).trans (onExterior_wedge j u p U a)

end Exterior

section Affine
variable {B A : Type} [CommRing B] [CommRing A] [Algebra ℂ B] [Algebra ℂ A] [Algebra B A] [IsScalarTower ℂ B A]

abbrev reduction (B A : Type) [CommRing B] [CommRing A] [Algebra B A] :=
  Spec.map (CommRingCat.ofHom (algebraMap B A))

abbrev pushedFunctions := (Scheme.Modules.pushforward (reduction B A)).obj (functions (Spec (CommRingCat.of A)))

private def globalTangent (v : Derivation ℂ B A) : ModuleCat.of B (KaehlerDifferential ℂ B) ⟶
    (moduleSpecΓFunctor (R := CommRingCat.of B)).obj (pushedFunctions (B := B) (A := A)) := by
  let N := (moduleSpecΓFunctor (R := CommRingCat.of B)).obj (pushedFunctions (B := B) (A := A))
  letI : Module B N := N.isModule
  refine ModuleCat.ofHom (Y := N) { toFun := fun ω => algebraMap A (AffineSections A ⊤) (v.liftKaehlerDifferential ω),
                                     map_add' := by simp,
                                     map_smul' := ?_ }
  intro b ω
  change algebraMap A (AffineSections A ⊤) (v.liftKaehlerDifferential (b • ω)) =
    (show AffineSections A ⊤ from (reduction B A).appTop (algebraMap B (AffineSections B ⊤) b)) * _
  rw [map_smul, Algebra.smul_def, map_mul]
  exact congrArg (· * _) (affineMap_original (IsScalarTower.toAlgHom ℂ B A) b).symm

/-- The affine derivation gives an honest sheaf morphism into the functions on the closed curve. -/
def tangentMap (v : Derivation ℂ B A) : affineDifferentialSheaf B ⟶ pushedFunctions (B := B) (A := A) :=
  (affineKahlerIso (A := B)).hom ≫ ((tilde.adjunction (R := CommRingCat.of B)).homEquiv
    (ModuleCat.of B (KaehlerDifferential ℂ B)) _).symm (globalTangent v)

abbrev pulledOne := schemeDifferentialMap (reduction B A) (affineCoefficient A) (affineCoefficient B)
  (affineMap_coefficient (IsScalarTower.toAlgHom ℂ B A))

def evaluation (v : Derivation ℂ B A) :
    exteriorSheaf (Spec.structureSheaf B) (affineDifferentialSheaf B).val 2 ⟶
      (Scheme.Modules.pushforward (reduction B A)).obj (affineDifferentialSheaf A) :=
  alongSheaf (reduction B A) (tangentMap v) (pulledOne (B := B) (A := A))


/-- An algebraic one-form as a global section of the intrinsic affine differential sheaf. -/
abbrev globalForm (R : Type) [CommRing R] [Algebra ℂ R] :=
  globalKaehlerMap (affineDifferentialSheaf R) (affineUniversalDifferential R)

theorem tangentMap_top (v : Derivation ℂ B A) (ω : KaehlerDifferential ℂ B) :
    (tangentMap v).val.app (op ⊤) (globalForm B ω) =
      algebraMap A (AffineSections A ⊤) (v.liftKaehlerDifferential ω) := by
  let e := affineKahlerIso (A := B)
  let z := tilde.toOpen (R := CommRingCat.of B) (ModuleCat.of B (KaehlerDifferential ℂ B)) ⊤ ω
  let q := ((tilde.adjunction (R := CommRingCat.of B)).homEquiv
    (ModuleCat.of B (KaehlerDifferential ℂ B)) _).symm (globalTangent v)
  have hi : e.hom.val.app (op ⊤) (e.inv.val.app (op ⊤) z) = z :=
    congrArg (fun k => SheafOfModules.Hom.val k |>.app (op ⊤) z) e.inv_hom_id
  have hq : q.val.app (op ⊤) z = algebraMap A (AffineSections A ⊤) (v.liftKaehlerDifferential ω) :=
    congrArg (fun f => f ω) (((tilde.adjunction (R := CommRingCat.of B)).homEquiv
      (ModuleCat.of B (KaehlerDifferential ℂ B)) _).apply_symm_apply (globalTangent v))
  change q.val.app (op ⊤) (e.hom.val.app (op ⊤) (globalForm B ω)) = _
  rw [← tildeToDifferential_top (A := B) ω]
  exact (congrArg (q.val.app (op ⊤)) hi).trans hq

/-- The velocity on the original structure sheaf of the thick curve. -/
def velocity (v : Derivation ℂ B A) : AffineDerivation B (pushedFunctions (B := B) (A := A)) :=
  (affineUniversalDifferential B).postcomp (tangentMap v).val

abbrev velocityOn (v : Derivation ℂ B A) (U : (Spec (CommRingCat.of B)).Opens)
    (x : Γ(Spec (CommRingCat.of B), U)) : Γ(Spec (CommRingCat.of A), reduction B A ⁻¹ᵁ U) :=
  (velocity v).d (X := op U) x

theorem velocityOn_top (v : Derivation ℂ B A) (x : B) :
    velocityOn v ⊤ (algebraMap B (AffineSections B ⊤) x) =
      algebraMap A (AffineSections A ⊤) (v x) := by
  have h := tangentMap_top v (KaehlerDifferential.D ℂ B x)
  rw [globalForm, globalKaehlerMap_D, Derivation.liftKaehlerDifferential_comp_D] at h
  exact h

theorem velocityOn_restrict (v : Derivation ℂ B A) {U V : (Spec (CommRingCat.of B)).Opens}
    (k : V ⟶ U) (x : Γ(Spec (CommRingCat.of B), U)) :
    velocityOn v V ((Spec (CommRingCat.of B)).presheaf.map k.op x) =
      (Spec (CommRingCat.of A)).presheaf.map ((Opens.map (reduction B A).base).map k).op
        (velocityOn v U x) := (velocity v).d_map k.op x

private theorem globalForm_smul (R : Type) [CommRing R] [Algebra ℂ R] (a : R)
    (ω : KaehlerDifferential ℂ R) :
    globalForm R (a • ω) = algebraMap R (AffineSections R ⊤) a • globalForm R ω :=
  (globalForm R).map_smul a ω

private theorem globalMap_smul {M : (Spec (CommRingCat.of B)).Modules} {N : (Spec (CommRingCat.of A)).Modules}
    (f : M ⟶ (Scheme.Modules.pushforward (reduction B A)).obj N) (r : B) (x : M.val.obj (op ⊤)) :
    f.val.app (op ⊤) (algebraMap B (AffineSections B ⊤) r • x) =
      algebraMap A (AffineSections A ⊤) (algebraMap B A r) •
        (show N.val.obj (op ⊤) from f.val.app (op ⊤) x) :=
  ((onSections (reduction B A) f ⊤).map_smulₛₗ _ _).trans
    (congrArg (fun a : AffineSections A ⊤ => a • (show N.val.obj (op ⊤) from f.val.app (op ⊤) x))
      (affineMap_original (IsScalarTower.toAlgHom ℂ B A) r))

theorem pulledOne_top (ω : KaehlerDifferential ℂ B) :
    (pulledOne (B := B) (A := A)).val.app (op ⊤) (globalForm B ω) =
      globalForm A (KaehlerDifferential.map ℂ ℂ B A ω) := by
  have hω : ω ∈ Submodule.span B (Set.range (KaehlerDifferential.D ℂ B)) := by
    rw [KaehlerDifferential.span_range_derivation]; trivial
  induction hω using Submodule.span_induction with
  | mem _ h =>
    obtain ⟨b, rfl⟩ := h
    rw [globalForm, globalKaehlerMap_D, KaehlerDifferential.map_D, globalForm, globalKaehlerMap_D]
    refine (schemeDifferentialMap_D (reduction B A) (affineCoefficient A) (affineCoefficient B)
      (affineMap_coefficient (IsScalarTower.toAlgHom ℂ B A)) ⊤ (algebraMap B (AffineSections B ⊤) b)).trans ?_
    exact congrArg (fun s : AffineSections A ⊤ => (affineUniversalDifferential A).d s)
      (affineMap_original (IsScalarTower.toAlgHom ℂ B A) b)
  | zero => simp only [map_zero]
  | add _ _ _ _ h₁ h₂ => simp only [map_add, h₁, h₂]
  | smul r x _ hx =>
    rw [globalForm_smul]
    refine (globalMap_smul (B := B) (A := A) (N := affineDifferentialSheaf A)
      (pulledOne (B := B) (A := A)) r (globalForm B x)).trans ?_
    rw [(KaehlerDifferential.map ℂ ℂ B A).map_smul,
      ← IsScalarTower.algebraMap_smul A r ((KaehlerDifferential.map ℂ ℂ B A) x), globalForm_smul]
    exact congrArg (fun q : (affineDifferentialSheaf A).val.obj (op ⊤) =>
      algebraMap A (AffineSections A ⊤) (algebraMap B A r) • q) hx

theorem evaluation_wedge (v : Derivation ℂ B A) (U : (Spec (CommRingCat.of B)).Opens)
    (a : Fin 2 → (affineDifferentialSheaf B).val.obj (op U)) :
    (evaluation v).val.app (op U) (wedgeSection (Spec.structureSheaf B) (affineDifferentialSheaf B).val 2 U a) =
      (onSections (reduction B A) (tangentMap v) U (a 0) : Γ(Spec (CommRingCat.of A), reduction B A ⁻¹ᵁ U)) •
        onSections (reduction B A) (pulledOne (B := B) (A := A)) U (a 1) -
      (onSections (reduction B A) (tangentMap v) U (a 1) : Γ(Spec (CommRingCat.of A), reduction B A ⁻¹ᵁ U)) •
        onSections (reduction B A) (pulledOne (B := B) (A := A)) U (a 0) :=
  alongSheaf_wedge _ _ _ _ _

theorem evaluation_restrict (v : Derivation ℂ B A) {U V : (Spec (CommRingCat.of B)).Opens} (k : V ⟶ U)
    (w : (exteriorSheaf (Spec.structureSheaf B) (affineDifferentialSheaf B).val 2).val.obj (op U)) :
    (evaluation v).val.app (op V) ((exteriorSheaf (Spec.structureSheaf B)
      (affineDifferentialSheaf B).val 2).val.map k.op w) =
      (affineDifferentialSheaf A).val.map ((Opens.map (reduction B A).base).map k).op
        ((evaluation v).val.app (op U) w) :=
  PresheafOfModules.naturality_apply (evaluation v).val k.op w

/-- Exterior algebra on the original affine ring maps to sections of the exterior sheaf. -/
def globalTwo (R : Type) [CommRing R] [Algebra ℂ R] :
    (⋀[R]^2 (KaehlerDifferential ℂ R)) →ₛₗ[algebraMap R (AffineSections R ⊤)]
      (exteriorSheaf (Spec.structureSheaf R) (affineDifferentialSheaf R).val 2).val.obj (op ⊤) :=
  (exteriorSection (Spec.structureSheaf R) (affineDifferentialSheaf R).val 2 ⊤).comp
    (exteriorMap (algebraMap R (AffineSections R ⊤))
      (show KaehlerDifferential ℂ R →ₛₗ[algebraMap R (AffineSections R ⊤)]
        (affineDifferentialSheaf R).val.obj (op ⊤) from
        { toFun := globalForm R, map_add' := (globalForm R).map_add, map_smul' := (globalForm R).map_smul }) 2)

theorem evaluation_top (v : Derivation ℂ B A) (w : ⋀[B]^2 (KaehlerDifferential ℂ B)) :
    (evaluation v).val.app (op ⊤) (globalTwo B w) =
      globalForm A (CycleQ2LiteralAbelJacobiContraction.contractRestrict v w) := by
  have hw : w ∈ Submodule.span B (Set.range (exteriorPower.ιMulti B 2)) := by
    rw [exteriorPower.ιMulti_span]; trivial
  induction hw using Submodule.span_induction with
  | mem _ hm =>
    obtain ⟨m, rfl⟩ := hm
    have hm : m = ![m 0, m 1] := by ext i; fin_cases i <;> rfl
    simp only [globalTwo, LinearMap.comp_apply, exteriorMap_wedge]
    rw [← wedgeSection, evaluation_wedge, hm, CycleQ2LiteralAbelJacobiContraction.contractRestrict_wedge]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, map_sub, globalForm_smul]
    let act := fun (c : AffineSections A ⊤) (w : (affineDifferentialSheaf A).val.obj (op ⊤)) => c • w
    exact congrArg₂ (· - ·)
      (congrArg₂ act (tangentMap_top v _) (pulledOne_top (B := B) (A := A) _))
      (congrArg₂ act (tangentMap_top v _) (pulledOne_top (B := B) (A := A) _))
  | zero => simp only [map_zero]
  | add _ _ _ _ h₁ h₂ => simp only [map_add, h₁, h₂]
  | smul r x _ hx =>
    rw [map_smulₛₗ]
    refine (globalMap_smul (B := B) (A := A) (N := affineDifferentialSheaf A)
      (evaluation v) r (globalTwo B x)).trans ?_
    rw [(CycleQ2LiteralAbelJacobiContraction.contractRestrict v).map_smul,
      ← IsScalarTower.algebraMap_smul A r (CycleQ2LiteralAbelJacobiContraction.contractRestrict v x),
      globalForm_smul]
    exact congrArg (fun q : (affineDifferentialSheaf A).val.obj (op ⊤) =>
      algebraMap A (AffineSections A ⊤) (algebraMap B A r) • q) hx

end Affine

section Literal

open scoped DualNumber
open CycleQ2LiteralAbelJacobiMovingNormal CycleQ2LiteralAbelJacobiContraction
  CycleQ2LiteralAbelJacobiEquations CycleQ2CurveCylinderPullback CycleQ2LiteralCylinderEvaluation

attribute [local instance] CycleQ2IncidenceSeedFiber.seedAlgebra
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderAlgebra
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderModule
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderSMul
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderTower
  CycleQ2LiteralAbelJacobiContraction.fixedAlgebra
  CycleQ2LiteralAbelJacobiContraction.fixedTower
  CycleQ2LiteralCylinderEvaluation.familyRing
  CycleQ2LiteralCylinderEvaluation.closedRing
  CycleQ2LiteralCylinderEvaluation.threefoldRing
  CycleQ2CurveParameterTangent.chartComplexAlgebra
  CycleQ2LiteralCylinderEvaluation.familyComplexSMul
  CycleQ2LiteralCylinderEvaluation.familyComplexModule
  CycleQ2LiteralCylinderEvaluation.familyAlgebra
  CycleQ2LiteralCylinderEvaluation.familyComplexTower
  CycleQ2LiteralCylinderEvaluation.reductionAlgebra
  CycleQ2LiteralCylinderEvaluation.fixedCurveTower
  CycleQ2LiteralCylinderEvaluation.familyReductionTower

/-- Every original first-order chart has a sheaf evaluation with parameter speed one.
On the pullback of the cubic conormal wedge its value on the seed fibre is the
negative retained cubic times the restricted one-form. -/
theorem exists_chart_evaluation (t : Fin 3 → ℂ) (ht : AlgebraicIndependent ℚ t) (i : Fin 4) :
    ∃ v : Derivation ℂ (B t i) (A t i), v (algebraMap ℂ[ε] (B t i) ε) = 1 ∧
      ∀ β : KaehlerDifferential ℂ (T i),
        (evaluation v).val.app (op ⊤)
          (globalTwo (B t i) (pullTwo (T i) (B t i) (exteriorPower.ιMulti (T i) 2
            ![KaehlerDifferential.D ℂ (T i) (cubicOnT i), β]))) =
          globalForm (A t i) (-(seedChartMap t i (tangentL i)) •
            KaehlerDifferential.map ℂ ℂ (T i) (A t i) β) := by
  have h := CycleQ2LiteralAbelJacobiBertiniMinor.prime_minor_of_independent t ht
  have hs := CycleQ2LiteralAbelJacobiSeedLiftDimension.smooth_seed_of_seedMinorCover t h
  have := CycleQ2LiteralAbelJacobiSeedLiftRegular.firstOrderCurveChart_flat_of_smooth_seed t hs i
  have := CycleQ2LiteralAbelJacobiSmoothNormal.seedChart_smooth_of_minors t h i
  obtain ⟨v, hv, he⟩ := exists_evaluation t i
  exact ⟨v, hv, fun β => (evaluation_top v _).trans (congrArg (globalForm (A t i)) (he β))⟩

end Literal

end CycleQ2LiteralAbelJacobiEvaluationAffine

end

#print axioms CycleQ2LiteralAbelJacobiEvaluationAffine.evaluation_top
#print axioms CycleQ2LiteralAbelJacobiEvaluationAffine.exists_chart_evaluation
