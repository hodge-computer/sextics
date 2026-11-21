import Proposal.GeometricAffineCotangentReduction

/-!
# The original canonical cotangent reduction on every native chart

The original global cotangent reduction, restricted through the actual
closed affine Proj chart, is identified with the tilde of the original
native tensor reduction. The proof uses the actual commuting scheme
square, canonical differential-map composition, and the fixed affine
pullback normalization.

Prepared for fqlx with OpenAI ChatGPT assistance; see solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralCotangentReduction

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
  CycleQ2LiteralProjectiveIntersections CycleQ2LiteralProjectiveIntersectionComplex
  CycleQ2LiteralProjectiveDeformation CycleQ2LiteralProjectiveCotangent
  CycleQ2LiteralNativeCotangent CycleQ2LiteralAffineCotangent
  CycleQ2GeometricDifferentialSheaf CycleQ2GeometricAffineDifferentialSheaf
  CycleQ2GeometricAffineKahlerSheaf CycleQ2GeometricAffineModulePullback
  CycleQ2GeometricSchemeCotangentMaps CycleQ2GeometricAffineCotangentReduction

attribute [local instance] CycleQ2LiteralProjectiveIntersectionKernel.nativeReductionAlgebra
  CycleQ2LiteralProjectiveIntersectionComplex.thickComplexAlgebra
  CycleQ2LiteralProjectiveIntersectionComplex.closedComplexAlgebra
  CycleQ2LiteralProjectiveIntersectionComplex.thickComplexSMul
  CycleQ2LiteralProjectiveIntersectionComplex.closedComplexSMul
  CycleQ2LiteralProjectiveIntersectionComplex.thickComplexModule
  CycleQ2LiteralProjectiveIntersectionComplex.closedComplexModule
  CycleQ2LiteralProjectiveIntersectionComplex.complexReductionTower

def nativeTensorReductionTilde (s : Finset Vertex) :
    nativeCotangentTilde s ⟶ kahlerTilde (A := ClosedRing s) :=
  tilde.map (ModuleCat.ofHom (nativeCotangentReduction s))

theorem tensorReductionTilde_eq_native (s : Finset Vertex) :
    ((tilde.functor (CommRingCat.of (ClosedRing s))).mapIso (nativeTensorModuleIso s)).hom ≫
        nativeTensorReductionTilde s = tensorReductionTilde (nativeReductionAlgHom s) := by
  simp only [nativeTensorModuleIso, Functor.mapIso_refl, Iso.refl_hom, Category.id_comp]
  rfl

private theorem compareChartMaps {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) {B B' B'' : C} {X U V T N P Q Y : D}
    (e₁ : X ≅ U) (e₂ : U ≅ V) (e₃ : F.obj B ≅ V)
    (e : B ≅ B'') (j : B ⟶ B') (d : B' ≅ B'') (he : e.hom = j ≫ d.hom)
    (t : F.obj B'' ≅ T) (v : T ≅ N) (n : N ⟶ Q) (u : T ⟶ Q) (hv : v.hom ≫ n = u)
    (r : F.obj B' ⟶ P) (δ : P ≅ Q) (hr : F.map d.hom ≫ t.hom ≫ u = r ≫ δ.hom)
    (q : X ⟶ Y) (g : Y ⟶ P) (e' : Y ≅ Q) (hg : e'.hom = g ≫ δ.hom)
    (h : e₁.hom ≫ e₂.hom ≫ e₃.inv ≫ F.map j ≫ r = q ≫ g) :
    (e₁ ≪≫ e₂ ≪≫ e₃.symm ≪≫ F.mapIso e ≪≫ t ≪≫ v).hom ≫ n = q ≫ e'.hom := by
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, he, Functor.map_comp,
    Category.assoc, hv, hr, hg]
  simpa only [Category.assoc] using congrArg (fun f => f ≫ δ.hom) h

section AffineSquare

variable {X Y : Scheme.{0}} {B A : Type} [CommRing B] [CommRing A] [Algebra ℂ B] [Algebra ℂ A]
    (ρ : B →ₐ[ℂ] A) (j : X ⟶ Y) (g : Spec (CommRingCat.of A) ⟶ X)
    (k : Spec (CommRingCat.of B) ⟶ Y) [IsOpenImmersion g] [IsOpenImmersion k]
    (cx : ℂ →+* Γ(X, ⊤)) (cy : ℂ →+* Γ(Y, ⊤))
    (hj : ∀ U c, j.app U (coefficientOn Y.sheaf cy U c) = coefficientOn X.sheaf cx (j ⁻¹ᵁ U) c)
    (hg : ∀ U c, g.app U (coefficientOn X.sheaf cx U c) =
      coefficientOn (Spec.structureSheaf A) (affineCoefficient A) (g ⁻¹ᵁ U) c)
    (hk : ∀ U c, k.app U (coefficientOn Y.sheaf cy U c) =
      coefficientOn (Spec.structureSheaf B) (affineCoefficient B) (k ⁻¹ᵁ U) c)
    (h : g ≫ j = affineMap ρ ≫ k)

open CycleQ2GeometricOpenDifferentialSheaf

private theorem affineChartComparison {N : (Spec (CommRingCat.of A)).Modules}
    (v : tensorTilde ρ ≅ N) (n : N ⟶ kahlerTilde (A := A))
    (hv : v.hom ≫ n = tensorReductionTilde ρ) :
    (((Scheme.Modules.pullbackComp g j).app (differentialSheaf Y.sheaf cy) ≪≫
      (Scheme.Modules.pullbackCongr h).app (differentialSheaf Y.sheaf cy) ≪≫
      ((Scheme.Modules.pullbackComp (affineMap ρ) k).app (differentialSheaf Y.sheaf cy)).symm ≪≫
      (Scheme.Modules.pullback (affineMap ρ)).mapIso
        (pullbackOpenDifferentialIso k (affineCoefficient B) cy hk ≪≫ affineKahlerIso) ≪≫
      (pullbackTildeIso (CommRingCat.ofHom ρ.toRingHom)).app
        (ModuleCat.of B (KaehlerDifferential ℂ B)) ≪≫ v).hom ≫ n) =
      (Scheme.Modules.pullback g).map (cotangentMap j cx cy hj) ≫
        (pullbackOpenDifferentialIso g (affineCoefficient A) cx hg ≪≫ affineKahlerIso).hom := by
  let d := differentialSheaf Y.sheaf cy
  let eB := pullbackOpenDifferentialIso k (affineCoefficient B) cy hk
  let eA := pullbackOpenDifferentialIso g (affineCoefficient A) cx hg
  let aB := affineKahlerIso (A := B)
  let aA := affineKahlerIso (A := A)
  let jB := cotangentMap k (affineCoefficient B) cy hk
  let jA := cotangentMap g (affineCoefficient A) cx hg
  have heB : (eB ≪≫ aB).hom = jB ≫ aB.hom :=
    congrArg (fun m => m ≫ aB.hom) (cotangentMap_eq_open k (affineCoefficient B) cy hk).symm
  have heA : (eA ≪≫ aA).hom = jA ≫ aA.hom :=
    congrArg (fun m => m ≫ aA.hom) (cotangentMap_eq_open g (affineCoefficient A) cx hg).symm
  exact compareChartMaps
    (C := (Spec (CommRingCat.of B)).Modules) (D := (Spec (CommRingCat.of A)).Modules)
    (B := (Scheme.Modules.pullback k).obj d) (B' := affineDifferentialSheaf B)
    (B'' := kahlerTilde (A := B)) (P := affineDifferentialSheaf A) (Q := kahlerTilde (A := A))
    (N := N) (T := tensorTilde ρ) (Scheme.Modules.pullback (affineMap ρ))
    ((Scheme.Modules.pullbackComp g j).app d) ((Scheme.Modules.pullbackCongr h).app d)
    ((Scheme.Modules.pullbackComp (affineMap ρ) k).app d)
    (eB ≪≫ aB) jB aB heB
    ((pullbackTildeIso (CommRingCat.ofHom ρ.toRingHom)).app (ModuleCat.of B (KaehlerDifferential ℂ B)))
    v n (tensorReductionTilde ρ) hv (canonicalAffineCotangentMap ρ) aA
    (affineCotangentReduction_comm ρ) ((Scheme.Modules.pullback g).map (cotangentMap j cx cy hj))
    jA (eA ≪≫ aA) heA
    (cotangentMap_square j cx cy hj g (affineCoefficient A) hg k (affineMap ρ)
      (affineCoefficient B) hk (affineMap_coefficient ρ) h)

/-- Keep the chart isomorphisms bundled while transporting their comparison. -/
private theorem bundledChartComparison {N : (Spec (CommRingCat.of A)).Modules}
    (n : N ⟶ kahlerTilde (A := A)) (v : tensorTilde ρ ≅ N)
    (hv : v.hom ≫ n = tensorReductionTilde ρ)
    (q : (Scheme.Modules.pullback j).obj (differentialSheaf Y.sheaf cy) ⟶ differentialSheaf X.sheaf cx)
    (hq : q = cotangentMap j cx cy hj)
    (e : (Scheme.Modules.pullback k).obj (differentialSheaf Y.sheaf cy) ≅ kahlerTilde (A := B))
    (he : e = pullbackOpenDifferentialIso k (affineCoefficient B) cy hk ≪≫ affineKahlerIso)
    (d : (Scheme.Modules.pullback g).obj (differentialSheaf X.sheaf cx) ≅ kahlerTilde (A := A))
    (hd : d = pullbackOpenDifferentialIso g (affineCoefficient A) cx hg ≪≫ affineKahlerIso)
    (t : (Scheme.Modules.pullback g).obj ((Scheme.Modules.pullback j).obj (differentialSheaf Y.sheaf cy)) ≅ N)
    (ht : t = (Scheme.Modules.pullbackComp g j).app (differentialSheaf Y.sheaf cy) ≪≫
      (Scheme.Modules.pullbackCongr h).app (differentialSheaf Y.sheaf cy) ≪≫
      ((Scheme.Modules.pullbackComp (affineMap ρ) k).app (differentialSheaf Y.sheaf cy)).symm ≪≫
      (Scheme.Modules.pullback (affineMap ρ)).mapIso e ≪≫
      (pullbackTildeIso (CommRingCat.ofHom ρ.toRingHom)).app
        (ModuleCat.of B (KaehlerDifferential ℂ B)) ≪≫ v) :
    t.hom ≫ n = (Scheme.Modules.pullback g).map q ≫ d.hom := by
  subst q e d t
  exact affineChartComparison ρ j g k cx cy hj hg hk h v n hv

end AffineSquare

/-- The canonical global reduction is the original native tensor map
under the already fixed canonical affine sheaf identifications. -/
theorem nativeCotangentReduction_comm (s : Finset Vertex) (hs : s.Nonempty) :
    (nativeCotangentIso s hs).hom ≫ nativeTensorReductionTilde s =
      (Scheme.Modules.pullback (closedAffineMap s hs)).map cotangentReduction ≫
        (closedDifferentialIso s hs).hom :=
  bundledChartComparison (X := ClosedSurface) (Y := projectiveDeformation)
    (B := ThickRing s) (A := ClosedRing s) (N := nativeCotangentTilde s) (nativeReductionAlgHom s)
    closedFiber (closedAffineMap s hs) (thickAffineMap s hs)
    (CycleQ2GeometricSurfaceCoefficients.projectiveGlobalCoefficient 57 1) totalGlobalCoefficient
    closedFiber_coefficient (closedAffine_coefficient s hs) (thickAffine_coefficient s hs)
    (nativeReduction_scheme_square s hs) (nativeTensorReductionTilde s)
    ((tilde.functor (CommRingCat.of (ClosedRing s))).mapIso (nativeTensorModuleIso s))
    (tensorReductionTilde_eq_native s) cotangentReduction rfl
    (thickDifferentialIso s hs) rfl (closedDifferentialIso s hs) rfl (nativeCotangentIso s hs) rfl

end CycleQ2LiteralCotangentReduction

end

#print axioms CycleQ2LiteralCotangentReduction.nativeCotangentReduction_comm
