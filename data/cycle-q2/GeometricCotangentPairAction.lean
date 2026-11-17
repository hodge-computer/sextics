import Proposal.GeometricLiteralCotangentEpsilonMap

/-!
# Equivariance of the restricted cotangent sequence

The middle map is induced by the differential on the thick surface and the
closed-fibre square. On the canonical normal generator its adjoint multiplies
by the character of epsilon.

Prepared for fqlx with OpenAI ChatGPT assistance; see solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2LiteralOrbitBoundary

open CategoryTheory Opposite AlgebraicGeometry
  CycleQ2GeometricDifferentialSheaf CycleQ2GeometricSchemeCotangentMaps
  CycleQ2LiteralCotangentEpsilonComparison CycleQ2LiteralCotangentEpsilonMap
  CycleQ2SurfacePullbackFrame

section Pair

variable {S T : Scheme.{0}} (i : S ⟶ T) (g : S ⟶ S) (G : T ⟶ T)
    (h : g ≫ i = i ≫ G)
    (cs : ℂ →+* Γ(S, ⊤)) (ct : ℂ →+* Γ(T, ⊤))
    (hi : ∀ U a, i.app U (coefficientOn T.sheaf ct U a) =
      coefficientOn S.sheaf cs (i ⁻¹ᵁ U) a)
    (hg : ∀ U a, g.app U (coefficientOn S.sheaf cs U a) =
      coefficientOn S.sheaf cs (g ⁻¹ᵁ U) a)
    (hG : ∀ U a, G.app U (coefficientOn T.sheaf ct U a) =
      coefficientOn T.sheaf ct (G ⁻¹ᵁ U) a)

def restrictedMap :
    (Scheme.Modules.pullback g).obj ((Scheme.Modules.pullback i).obj
      (differentialSheaf T.sheaf ct)) ⟶
      (Scheme.Modules.pullback i).obj (differentialSheaf T.sheaf ct) :=
  (Scheme.Modules.pullbackComp g i).hom.app _ ≫
    (Scheme.Modules.pullbackCongr h).hom.app _ ≫
    (Scheme.Modules.pullbackComp i G).inv.app _ ≫
    (Scheme.Modules.pullback i).map (cotangentMap G ct ct hG)

theorem reduction_square :
    restrictedMap i g G h ct hG ≫ cotangentMap i cs ct hi =
      (Scheme.Modules.pullback g).map (cotangentMap i cs ct hi) ≫ cotangentMap g cs cs hg := by
  simpa only [restrictedMap, Category.assoc] using
    cotangentMap_square i cs ct hi g cs hg G i ct hG hi h

theorem restrictedMap_differential (e : Γ(T, ⊤)) :
    onTop (restrictedMap i g G h ct hG)
      (pullTop g _ (pullTop i (differentialSheaf T.sheaf ct) ((universalDifferential T.sheaf ct).d e))) =
      pullTop i (differentialSheaf T.sheaf ct) ((universalDifferential T.sheaf ct).d (G.appTop e)) := by
  unfold restrictedMap
  simp only [onTop_comp]
  rw [pullTop_square, pullTop_map]
  exact congrArg (pullTop i (differentialSheaf T.sheaf ct)) (cotangentMap_unit_D G ct ct hG ⊤ e)

private theorem coefficient_top (a : ℂ) : coefficientOn T.sheaf ct ⊤ a = ct a := by
  change T.presheaf.map (𝟙 (op ⊤)) (ct a) = ct a
  exact ConcreteCategory.congr_hom (T.presheaf.map_id (op ⊤)) (ct a)

private theorem differential_coefficient_mul (a : ℂ) (e : Γ(T, ⊤)) :
    (universalDifferential T.sheaf ct).d (ct a * e) =
      ct a • (universalDifferential T.sheaf ct).d e := by
  have hz : (universalDifferential T.sheaf ct).d (ct a) = 0 := by
    rw [← coefficient_top ct a]
    exact (universalDifferential T.sheaf ct).d_app (X := op ⊤) a
  rw [(universalDifferential T.sheaf ct).d_mul, hz, smul_zero, add_zero]

theorem pullTop_smul (M : T.Modules) (a : Γ(T, ⊤)) (x : Γ(M, ⊤)) :
    pullTop i M (a • x) = i.appTop a • pullTop i M x :=
  (((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app M).val.app (op ⊤)).hom.map_smul a x

include hi in
theorem normal_generator (e : Γ(T, ⊤)) (a : ℂ) (he : G.appTop e = ct a * e) :
    onTop (restrictedMap i g G h ct hG)
      (pullTop g _ (pullTop i (differentialSheaf T.sheaf ct) ((universalDifferential T.sheaf ct).d e))) =
      cs a • pullTop i (differentialSheaf T.sheaf ct) ((universalDifferential T.sheaf ct).d e) := by
  rw [restrictedMap_differential, he, differential_coefficient_mul, pullTop_smul]
  have H := hi ⊤ a
  change i.appTop (coefficientOn T.sheaf ct ⊤ a) = coefficientOn S.sheaf cs ⊤ a at H
  rw [coefficient_top, coefficient_top] at H
  rw [H]

def coefficientEnd (cs : ℂ →+* Γ(S, ⊤)) (a : ℂ) : structureModule S ⟶ structureModule S :=
  (structureModule S).unitHomEquiv.symm <|
    (structureModule S).val.sectionsMk
      (fun U => coefficientOn S.sheaf cs U.unop a)
      (fun _ _ k => ConcreteCategory.congr_hom ((coefficientMap S.sheaf cs).naturality k).symm a)

theorem coefficientEnd_apply (a : ℂ) (U : S.Opens) (x : Γ(S,U)) :
    (coefficientEnd cs a).val.app (op U) x = x * (show Γ(S, U) from coefficientOn S.sheaf cs U a) := rfl

private theorem coefficientEnd_one (a : ℂ) :
    onTop (coefficientEnd cs a) (1 : Γ(S, ⊤)) = cs a := by
  change (1 : Γ(S, ⊤)) * (show Γ(S, ⊤) from coefficientOn S.sheaf cs ⊤ a) = cs a
  rw [one_mul, coefficient_top]

include hi in
theorem inclusion_square (e : Γ(T, ⊤)) (a : ℂ) (he : G.appTop e = ct a * e)
    (incl : structureModule S ⟶ (Scheme.Modules.pullback i).obj (differentialSheaf T.sheaf ct))
    (h₁ : onTop incl (1 : Γ(S, ⊤)) =
      pullTop i (differentialSheaf T.sheaf ct) ((universalDifferential T.sheaf ct).d e)) :
    (pullbackUnitIso g).hom ≫ coefficientEnd cs a ≫ incl =
      (Scheme.Modules.pullback g).map incl ≫ restrictedMap i g G h ct hG := by
  apply pulledUnit_hom_ext
  simp only [onTop_comp, pulledUnitIso_one, coefficientEnd_one, pullTop_map, h₁]
  rw [normal_generator i g G h cs ct hi hG e a he, ← h₁]
  have hl := (incl.val.app (op ⊤)).hom.map_smul (cs a) (1 : Γ(S, ⊤))
  change onTop incl ((cs a * 1 : Γ(S, ⊤))) = cs a • onTop incl (1 : Γ(S, ⊤)) at hl
  simpa only [mul_one] using hl

end Pair

open CycleQ2GeometricAffineChartSections

theorem coefficient_of_overComplex {S : Scheme.{0}} (g : S ⟶ S)
    (q : S ⟶ Spec (CommRingCat.of ℂ)) (hq : g ≫ q = q) (U : S.Opens) (a : ℂ) :
    g.app U (coefficientOn S.sheaf (schemeCoefficient q) U a) =
      coefficientOn S.sheaf (schemeCoefficient q) (g ⁻¹ᵁ U) a := by
  rw [coefficientOn_app, hq]

section Adjoints

variable {C D : Type*} [Category C] [Category D]
  {L : C ⥤ D} {R : D ⥤ C} (A : L ⊣ R)

theorem adjunct_square {P Q : C} {P' Q' : D} (u : P ⟶ Q) (v : P' ⟶ Q')
    (l : L.obj P ⟶ P') (m : L.obj Q ⟶ Q') (h : l ≫ v = L.map u ≫ m) :
    A.homEquiv P P' l ≫ R.map v = u ≫ A.homEquiv Q Q' m := by
  rw [← A.homEquiv_naturality_right, h, A.homEquiv_naturality_left]

end Adjoints

section ScalarAdjoint

variable {S : Scheme.{0}} (g : S ⟶ S) (cs : ℂ →+* Γ(S, ⊤)) (a : ℂ)

def scalarAdjoint : structureModule S ⟶ (Scheme.Modules.pushforward g).obj (structureModule S) :=
  (Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _
    ((pullbackUnitIso g).hom ≫ coefficientEnd cs a)

theorem scalarAdjoint_apply (U : S.Opens) (x : Γ(S, U)) :
    (scalarAdjoint g cs a).val.app (op U) x =
      g.app U x * (show Γ(S, g ⁻¹ᵁ U) from coefficientOn S.sheaf cs (g ⁻¹ᵁ U) a) := by
  unfold scalarAdjoint
  rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_apply, pullbackUnitIso_unit]
  rfl

end ScalarAdjoint

section AdjointSquares
variable {S T : Scheme.{0}} (i : S ⟶ T) (g : S ⟶ S) (G : T ⟶ T)
    (h : g ≫ i = i ≫ G) (cs : ℂ →+* Γ(S, ⊤)) (ct : ℂ →+* Γ(T, ⊤))
    (hi : ∀ U a, i.app U (coefficientOn T.sheaf ct U a) = coefficientOn S.sheaf cs (i ⁻¹ᵁ U) a)
    (hg : ∀ U a, g.app U (coefficientOn S.sheaf cs U a) = coefficientOn S.sheaf cs (g ⁻¹ᵁ U) a)
    (hG : ∀ U a, G.app U (coefficientOn T.sheaf ct U a) = coefficientOn T.sheaf ct (G ⁻¹ᵁ U) a)

def middleAdjoint :
    (Scheme.Modules.pullback i).obj (differentialSheaf T.sheaf ct) ⟶
      (Scheme.Modules.pushforward g).obj ((Scheme.Modules.pullback i).obj (differentialSheaf T.sheaf ct)) :=
  (Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _
    (restrictedMap i g G h ct hG)

theorem adjoint_reduction :
    middleAdjoint i g G h ct hG ≫ (Scheme.Modules.pushforward g).map (cotangentMap i cs ct hi) =
      cotangentMap i cs ct hi ≫ CycleQ2GeometricSchemeDifferentialMap.schemeDifferentialMap g cs cs hg := by
  rw [← cotangentMap_adjunct g cs cs hg]
  exact adjunct_square (Scheme.Modules.pullbackPushforwardAdjunction g) _ _ _ _
    (reduction_square i g G h cs ct hi hg hG)

include hi in
theorem adjoint_inclusion (e : Γ(T, ⊤)) (a : ℂ) (he : G.appTop e = ct a * e)
    (incl : structureModule S ⟶ (Scheme.Modules.pullback i).obj (differentialSheaf T.sheaf ct))
    (h₁ : onTop incl (1 : Γ(S, ⊤)) =
      pullTop i (differentialSheaf T.sheaf ct) ((universalDifferential T.sheaf ct).d e)) :
    scalarAdjoint g cs a ≫ (Scheme.Modules.pushforward g).map incl =
      incl ≫ middleAdjoint i g G h ct hG := by
  exact adjunct_square (Scheme.Modules.pullbackPushforwardAdjunction g) incl incl _ _
    (inclusion_square i g G h cs ct hi hG e a he incl h₁)
end AdjointSquares

end CycleQ2LiteralOrbitBoundary
end

#print axioms CycleQ2LiteralOrbitBoundary.inclusion_square
#print axioms CycleQ2LiteralOrbitBoundary.adjoint_inclusion
#print axioms CycleQ2LiteralOrbitBoundary.adjoint_reduction
