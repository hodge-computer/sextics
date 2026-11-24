import Proposal.GeometricLiteralCotangentEpsilon
import Proposal.GeometricSchemeCotangentMaps

/-!
# The original global epsilon differential on the native affine charts

The pullback unit sends a global section to its pullback along a scheme
morphism. The composition and equality isomorphisms used in the native
cotangent comparison carry this element to the corresponding pullback along
the other side of the original closed-fibre square.

Prepared for fqlx with OpenAI ChatGPT assistance; see solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralCotangentEpsilonComparison

open CategoryTheory Opposite AlgebraicGeometry CycleQ2LiteralCotangentEpsilon
  CycleQ2GeometricSchemeCotangentMaps CycleQ2LiteralProjectiveCotangent
  CycleQ2LiteralProjectiveDeformation CycleQ2LiteralProjectiveIntersections
  CycleQ2LiteralProjectiveIntersectionKernel CycleQ2LiteralAffineCotangent
  CycleQ2LiteralNativeCotangent CycleQ2GeometricAffineModulePullback
  CycleQ2GeometricDifferentialSheaf CycleQ2GeometricAffineKahlerSheaf
  CycleQ2GeometricAffineDifferentialSheaf

section Units

variable {X Y Z W : Scheme.{0}}

def onTop {M N : X.Modules} (u : M ⟶ N) (x : Γ(M, ⊤)) : Γ(N, ⊤) := u.app ⊤ x

def pullTop (f : X ⟶ Y) (M : Y.Modules) (x : Γ(M, ⊤)) :
    Γ((Scheme.Modules.pullback f).obj M, ⊤) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).app ⊤ x

theorem onTop_comp {A B C : X.Modules} (u : A ⟶ B) (v : B ⟶ C) (x : Γ(A, ⊤)) :
    onTop (u ≫ v) x = onTop v (onTop u x) := rfl

theorem pullTop_map (f : X ⟶ Y) {M N : Y.Modules} (u : M ⟶ N) (x : Γ(M, ⊤)) :
    onTop ((Scheme.Modules.pullback f).map u) (pullTop f M x) = pullTop f N (onTop u x) := by
  have h := (Scheme.Modules.pullbackPushforwardAdjunction f).unit.naturality u
  exact (congrArg (fun v => v.app ⊤ x) h).symm

theorem pullTop_comp_inv (f : X ⟶ Y) (g : Y ⟶ Z) (M : Z.Modules) (x : Γ(M, ⊤)) :
    onTop ((Scheme.Modules.pullbackComp f g).inv.app M) (pullTop (f ≫ g) M x) =
      pullTop f _ (pullTop g M x) := by
  have h := unit_conjugateEquiv
    ((Scheme.Modules.pullbackPushforwardAdjunction g).comp
      (Scheme.Modules.pullbackPushforwardAdjunction f))
    (Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g))
    (Scheme.Modules.pullbackComp f g).inv M
  rw [Scheme.Modules.conjugateEquiv_pullbackComp_inv] at h
  exact (congrArg (fun v => v.app ⊤ x) h).symm

theorem pullTop_comp_hom (f : X ⟶ Y) (g : Y ⟶ Z) (M : Z.Modules) (x : Γ(M, ⊤)) :
    onTop ((Scheme.Modules.pullbackComp f g).hom.app M) (pullTop f _ (pullTop g M x)) =
      pullTop (f ≫ g) M x := by
  rw [← pullTop_comp_inv, ← onTop_comp, Iso.inv_hom_id_app]
  rfl

theorem pullTop_congr {f g : X ⟶ Y} (h : f = g) (M : Y.Modules) (x : Γ(M, ⊤)) :
    onTop ((Scheme.Modules.pullbackCongr h).hom.app M) (pullTop f M x) =
      pullTop g M x := by
  subst g
  rfl

theorem pullTop_square (f : X ⟶ Y) (g : Y ⟶ Z) (r : X ⟶ W) (k : W ⟶ Z)
    (h : f ≫ g = r ≫ k) (M : Z.Modules) (x : Γ(M, ⊤)) :
    onTop ((Scheme.Modules.pullbackComp r k).inv.app M)
      (onTop ((Scheme.Modules.pullbackCongr h).hom.app M)
        (onTop ((Scheme.Modules.pullbackComp f g).hom.app M)
          (pullTop f _ (pullTop g M x)))) = pullTop r _ (pullTop k M x) := by
  rw [pullTop_comp_hom, pullTop_congr, pullTop_comp_inv]

end Units

section AffineChart

variable {B : Type} [CommRing B] [Algebra ℂ B] {Y : Scheme.{0}}
    (f : Spec (CommRingCat.of B) ⟶ Y) [IsOpenImmersion f]
    (cY : ℂ →+* Γ(Y, ⊤))
    (hc : ∀ (U : Y.Opens) (c : ℂ),
      f.app U (coefficientOn Y.sheaf cY U c) =
        coefficientOn (Spec.structureSheaf B) (affineCoefficient B) (f ⁻¹ᵁ U) c)

theorem affineChart_differential (a : Γ(Y, ⊤)) (b : B)
    (hab : f.appTop a = (Scheme.ΓSpecIso (CommRingCat.of B)).inv b) :
    onTop ((CycleQ2GeometricOpenDifferentialSheaf.pullbackOpenDifferentialIso
        f (affineCoefficient B) cY hc ≪≫ affineKahlerIso (A := B)).hom)
      (pullTop f _ ((universalDifferential Y.sheaf cY).d a)) =
        tilde.toOpen (R := CommRingCat.of B) (ModuleCat.of B (KaehlerDifferential ℂ B)) ⊤
          (KaehlerDifferential.D ℂ B b) := by
  rw [Iso.trans_hom, onTop_comp, ← cotangentMap_eq_open]
  have hd : onTop (cotangentMap f (affineCoefficient B) cY hc)
      (pullTop f _ ((universalDifferential Y.sheaf cY).d a)) =
      (affineUniversalDifferential B).d (f.appTop a) :=
    cotangentMap_unit_D f (affineCoefficient B) cY hc ⊤ a
  rw [hd]
  have he : f.appTop a = algebraMap B (AffineSections B ⊤) b := hab
  rw [he]
  exact (differentialToTilde_D (A := B) (op ⊤)
    (algebraMap B (AffineSections B ⊤) b)).trans
    (tildeDerivation_algebraMap (A := B) (op ⊤) b)

end AffineChart

theorem affineSquare_element {B C : CommRingCat.{0}} (ρ : B ⟶ C) {X Y : Scheme.{0}}
    (f : Spec C ⟶ X) (g : X ⟶ Y) (k : Spec B ⟶ Y) (h : f ≫ g = Spec.map ρ ≫ k)
    (M : Y.Modules) (P : ModuleCat B) (Q : ModuleCat C)
    (e : (Scheme.Modules.pullback k).obj M ≅ tilde (R := B) P)
    (t : (ModuleCat.extendScalars ρ.hom).obj P ≅ Q) (x : Γ(M, ⊤)) (b : P)
    (he : onTop e.hom (pullTop k M x) = tilde.toOpen (R := B) P ⊤ b) :
    onTop (((Scheme.Modules.pullbackComp f g).app M ≪≫
      (Scheme.Modules.pullbackCongr h).app M ≪≫
      ((Scheme.Modules.pullbackComp (Spec.map ρ) k).app M).symm ≪≫
      (Scheme.Modules.pullback (Spec.map ρ)).mapIso e ≪≫
      (pullbackTildeIso ρ).app P ≪≫ (tilde.functor C).mapIso t).hom)
      (pullTop f _ (pullTop g M x)) =
      tilde.toOpen (R := C) Q ⊤ (t.hom ((ModuleCat.extendRestrictScalarsAdj ρ.hom).unit.app P b)) := by
  simp only [Iso.trans_hom, onTop_comp]
  have hs := pullTop_square f g (Spec.map ρ) k h M x
  change onTop ((tilde.functor C).map t.hom)
    (onTop ((pullbackTildeIso ρ).hom.app P)
      (onTop ((Scheme.Modules.pullback (Spec.map ρ)).map e.hom)
        (onTop ((Scheme.Modules.pullbackComp (Spec.map ρ) k).inv.app M)
          (onTop ((Scheme.Modules.pullbackCongr h).hom.app M)
            (onTop ((Scheme.Modules.pullbackComp f g).hom.app M)
              (pullTop f _ (pullTop g M x))))))) = _
  rw [hs, pullTop_map, he]
  have hu : onTop ((pullbackTildeIso ρ).hom.app P)
      (pullTop (Spec.map ρ) _ (tilde.toOpen (R := B) P ⊤ b)) =
      tilde.toOpen (R := C) _ ⊤ ((ModuleCat.extendRestrictScalarsAdj ρ.hom).unit.app P b) :=
    pullbackTilde_unit_apply ρ P b
  rw [hu]
  exact (ConcreteCategory.congr_hom (C := ModuleCat C)
    (X := (ModuleCat.extendScalars ρ.hom).obj P)
    (tilde.toOpen_map_app (R := C) t.hom ⊤)
    (show (ModuleCat.extendScalars ρ.hom).obj P from
      (ModuleCat.extendRestrictScalarsAdj ρ.hom).unit.app P b))

attribute [local instance] CycleQ2LiteralProjectiveIntersectionKernel.nativeReductionAlgebra
  CycleQ2LiteralProjectiveIntersectionComplex.thickComplexAlgebra
  CycleQ2LiteralProjectiveIntersectionComplex.closedComplexAlgebra
  CycleQ2LiteralProjectiveIntersectionComplex.thickComplexSMul
  CycleQ2LiteralProjectiveIntersectionComplex.closedComplexSMul
  CycleQ2LiteralProjectiveIntersectionComplex.thickComplexModule
  CycleQ2LiteralProjectiveIntersectionComplex.closedComplexModule
  CycleQ2LiteralProjectiveIntersectionComplex.complexReductionTower

/-- Pulling the original differential of epsilon to the thick affine chart
gives the ordinary Kähler differential of the original degree-zero epsilon. -/
theorem thickDifferential_epsilon (s : Finset Vertex) (hs : s.Nonempty) :
    onTop (thickDifferentialIso s hs).hom (pullTop (thickAffineMap s hs) totalDifferentialSheaf
      ((universalDifferential projectiveDeformation.sheaf totalGlobalCoefficient).d totalEpsilon)) =
    tilde.toOpen (R := CommRingCat.of (ThickRing s))
      (ModuleCat.of (ThickRing s) (KaehlerDifferential ℂ (ThickRing s))) ⊤
      (KaehlerDifferential.D ℂ (ThickRing s) (nativeEpsilon s)) :=
  affineChart_differential (B := ThickRing s) (Y := projectiveDeformation) (thickAffineMap s hs) totalGlobalCoefficient
    (thickAffine_coefficient s hs) totalEpsilon (nativeEpsilon s) (totalEpsilon_native s hs)


/-- The native comparison carries the pulled-back global section to the
original tensor-module inclusion evaluated at one. -/
theorem nativeCotangentIso_epsilon (s : Finset Vertex) (hs : s.Nonempty) :
    onTop (nativeCotangentIso s hs).hom
      (pullTop (closedAffineMap s hs) restrictedCotangentSheaf restrictedEpsilonDifferential) =
    tilde.toOpen (R := CommRingCat.of (ClosedRing s))
      (ModuleCat.of (ClosedRing s) (NativeCotangent s)) ⊤ (nativeEpsilonInclusion s 1) := by
  rw [nativeEpsilonInclusion_tmul]
  exact affineSquare_element (CommRingCat.ofHom (nativeReduction s))
    (closedAffineMap s hs) closedFiber (thickAffineMap s hs) (nativeReduction_scheme_square s hs)
    totalDifferentialSheaf (ModuleCat.of (ThickRing s) (KaehlerDifferential ℂ (ThickRing s)))
    (ModuleCat.of (ClosedRing s) (NativeCotangent s)) (thickDifferentialIso s hs)
    (nativeTensorModuleIso s)
    ((universalDifferential projectiveDeformation.sheaf totalGlobalCoefficient).d totalEpsilon)
    (KaehlerDifferential.D ℂ (ThickRing s) (nativeEpsilon s)) (thickDifferential_epsilon s hs)

end CycleQ2LiteralCotangentEpsilonComparison

end

#print axioms CycleQ2LiteralCotangentEpsilonComparison.nativeCotangentIso_epsilon
