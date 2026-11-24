import Proposal.GeometricLiteralAbelJacobiQPullbackDerived

/-!
# Composition of pullbacks of sheafified exterior forms

The pushforward-adjoint exterior morphism composes on all sections. Wedges
generate the exterior presheaf and sheafification determines the morphism
on the entire exterior sheaf.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2ExteriorPullComposition

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
  CycleQ2GeometricExteriorSheaf CycleQ2GeometricDifferentialSheaf
  CycleQ2GeometricSchemeDifferentialMap CycleQ2GeometricSchemeCotangentMaps
  CycleQ2GeometricAffineChartSections CycleQ2LiteralAbelJacobiQPullback

attribute [local instance] CycleQ2GeometricExteriorSheaf.exteriorObjectModule

variable {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z)

abbrev composeIntoPush {A : X.Modules} {B : Y.Modules} {C : Z.Modules}
    (φ : B ⟶ (Scheme.Modules.pushforward f).obj A)
    (ψ : C ⟶ (Scheme.Modules.pushforward g).obj B) :
    C ⟶ (Scheme.Modules.pushforward (f ≫ g)).obj A :=
  ψ ≫ (Scheme.Modules.pushforward g).map φ ≫ (Scheme.Modules.pushforwardComp f g).hom.app A

set_option maxHeartbeats 1500000 in
/-- Functoriality for arbitrary modules and semilinear maps into direct images. -/
theorem exteriorPull_comp {A : X.Modules} {B : Y.Modules} {C : Z.Modules}
    (φ : B ⟶ (Scheme.Modules.pushforward f).obj A)
    (ψ : C ⟶ (Scheme.Modules.pushforward g).obj B) (n : ℕ) :
    exteriorPull (f ≫ g) (composeIntoPush f g φ ψ) n =
      composeIntoPush f g (A := exteriorSheaf X.sheaf A.val n)
        (B := exteriorSheaf Y.sheaf B.val n) (C := exteriorSheaf Z.sheaf C.val n)
        (exteriorPull f φ n) (exteriorPull g ψ n) := by
  apply (exteriorSheafHomEquiv Z.sheaf C.val n _).injective
  apply PresheafOfModules.hom_ext
  intro U
  apply ConcreteCategory.hom_ext
  intro x
  change (exteriorPull (f ≫ g) (composeIntoPush f g φ ψ) n).val.app U
      (exteriorSection Z.sheaf C.val n U.unop x) =
    (exteriorPull f φ n).val.app (op (g ⁻¹ᵁ U.unop))
      ((exteriorPull g ψ n).val.app U (exteriorSection Z.sheaf C.val n U.unop x))
  rw [exteriorPull_section, exteriorPull_section, exteriorPull_section]
  apply congrArg (exteriorSection X.sheaf A.val n _)
  exact exteriorMap_composition _ _ _ _ _ _ (fun _ => rfl) (fun _ => rfl) n x

abbrev compatible {S T : Scheme.{0}} (j : S ⟶ T)
    (cS : ℂ →+* Γ(S, ⊤)) (cT : ℂ →+* Γ(T, ⊤)) :=
  ∀ (U : T.Opens) (z : ℂ), j.app U (coefficientOn T.sheaf cT U z) =
    coefficientOn S.sheaf cS (j ⁻¹ᵁ U) z

abbrev forms (S : Scheme.{0}) (c : ℂ →+* Γ(S, ⊤)) (n : ℕ) :=
  exteriorSheaf S.sheaf (differentialSheaf S.sheaf c).val n

abbrev schemeExteriorPull {S T : Scheme.{0}} (j : S ⟶ T)
    (cS : ℂ →+* Γ(S, ⊤)) (cT : ℂ →+* Γ(T, ⊤))
    (hj : compatible j cS cT) (n : ℕ) :
    forms T cT n ⟶ (Scheme.Modules.pushforward j).obj (forms S cS n) :=
  exteriorPull j (schemeDifferentialMap j cS cT hj) n

variable (cX : ℂ →+* Γ(X, ⊤)) (cY : ℂ →+* Γ(Y, ⊤)) (cZ : ℂ →+* Γ(Z, ⊤))
  (hf : compatible f cX cY) (hg : compatible g cY cZ)

theorem schemeExteriorPull_comp (n : ℕ) :
    schemeExteriorPull (f ≫ g) cX cZ (compositionCoefficient g cY cZ hg f cX hf) n =
      composeIntoPush f g (schemeExteriorPull f cX cY hf n) (schemeExteriorPull g cY cZ hg n) := by
  unfold schemeExteriorPull
  rw [schemeDifferentialMap_comp g cY cZ hg f cX hf]
  exact exteriorPull_comp f g _ _ n

theorem schemeExteriorPull_comp_apply (n : ℕ) (U : Z.Opens) (ω : (forms Z cZ n).val.obj (op U)) :
    (schemeExteriorPull (f ≫ g) cX cZ (compositionCoefficient g cY cZ hg f cX hf) n).val.app
        (op U) ω =
      (schemeExteriorPull f cX cY hf n).val.app (op (g ⁻¹ᵁ U))
        ((schemeExteriorPull g cY cZ hg n).val.app (op U) ω) := by
  exact congrArg (fun φ => φ.val.app (op U) ω) (schemeExteriorPull_comp f g cX cY cZ hf hg n)

theorem compatible_over {S T : Scheme.{0}} (j : S ⟶ T)
    (s : S ⟶ Spec (CommRingCat.of ℂ)) (t : T ⟶ Spec (CommRingCat.of ℂ)) (h : j ≫ t = s) :
    compatible j (schemeCoefficient s) (schemeCoefficient t) := by
  intro U z
  rw [coefficientOn_app, h]

section Cech

open CycleQ2InjectiveCech CycleQ2FiniteInjectiveCech CycleQ2FiniteCechHOne
  CycleQ2FiniteCechOrbitPullback CycleQ2GeometricModuleLocalIso

abbrev additiveForms (S : Scheme.{0}) (c : ℂ →+* Γ(S, ⊤)) (n : ℕ) :=
  addSheaf (forms S c n)

abbrev additivePull {S T : Scheme.{0}} (j : S ⟶ T)
    (cS : ℂ →+* Γ(S, ⊤)) (cT : ℂ →+* Γ(T, ⊤))
    (hj : compatible j cS cT) (n : ℕ) :
    additiveForms T cT n ⟶ push j.base (additiveForms S cS n) :=
  (SheafOfModules.toSheaf T.ringCatSheaf).map (schemeExteriorPull j cS cT hj n)

variable {ι : Type} (n : ℕ) (U : ι → Z.Opens) (a : One (additiveForms Z cZ n) U)

/-- Direct and iterated pullback agree on every edge in the finite cover. -/
theorem pullOne_comp :
    pullOne (f ≫ g).base (additivePull (f ≫ g) cX cZ (compositionCoefficient g cY cZ hg f cX hf) n) U a =
      pullOne f.base (additivePull f cX cY hf n) (cover g.base U)
        (pullOne g.base (additivePull g cY cZ hg n) U a) := by
  funext i j
  exact schemeExteriorPull_comp_apply f g cX cY cZ hf hg n (U i ⊓ U j) (a i j)

local instance (S : Scheme.{0}) : HasExt.{1} (AbSheaf (show TopCat from S)) := HasExt.standard _

/-- The two cocycle pullbacks give the same actual derived degree-one class. -/
theorem cechOneClass_comp [Fintype ι] (hU : (⨆ i, U i) = ⊤) (ha : IsOneCocycle _ U a) :
    cechOneClass (cover (f ≫ g).base U) (cover_top _ _ hU)
        (pullOne (f ≫ g).base (additivePull (f ≫ g) cX cZ
          (compositionCoefficient g cY cZ hg f cX hf) n) U a)
        (pullOne_closed _ _ _ _ ha) =
      cechOneClass (cover f.base (cover g.base U)) (cover_top _ _ (cover_top _ _ hU))
        (pullOne f.base (additivePull f cX cY hf n) (cover g.base U)
          (pullOne g.base (additivePull g cY cZ hg n) U a))
        (pullOne_closed _ _ _ _ (pullOne_closed _ _ _ _ ha)) := by
  congr 1
  exact pullOne_comp f g cX cY cZ hf hg n U a

open CycleQ2LiteralAbelJacobiQPullbackDerived (pullH pullH_cech)

/-- Functoriality of the genuine degree-one cohomology pullback on the class of
a finite two-form cocycle. -/
theorem pullH_comp_cech [Fintype ι] (hU : (⨆ i, U i) = ⊤) (ha : IsOneCocycle _ U a) :
    pullH (f ≫ g).base (additivePull (f ≫ g) cX cZ
        (compositionCoefficient g cY cZ hg f cX hf) n) 1 (cechOneClass U hU a ha) =
      pullH f.base (additivePull f cX cY hf n) 1
        (pullH g.base (additivePull g cY cZ hg n) 1 (cechOneClass U hU a ha)) := by
  rw [pullH_cech, pullH_cech, pullH_cech]
  exact cechOneClass_comp f g cX cY cZ hf hg n U a hU ha

end Cech

end CycleQ2ExteriorPullComposition

#print axioms CycleQ2ExteriorPullComposition.schemeExteriorPull_comp_apply
#print axioms CycleQ2ExteriorPullComposition.cechOneClass_comp
#print axioms CycleQ2ExteriorPullComposition.pullH_comp_cech
