import Proposal.GeometricLiteralCotangentReduction

/-!
# Local sections of the original cotangent reduction

Each admissible projective chart splitting gives a section of the pullback
of the original cotangent reduction. The section is the sheafification
of the native Kähler splitting transported along the two affine comparisons.

Prepared for fqlx with OpenAI ChatGPT assistance; see solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralCotangentLocalSplitting

open CategoryTheory AlgebraicGeometry CycleQ2LiteralProjectiveIntersections
  CycleQ2LiteralProjectiveIntersectionSplittings CycleQ2LiteralProjectiveCotangent
  CycleQ2LiteralNativeCotangent CycleQ2LiteralAffineCotangent
  CycleQ2LiteralCotangentReduction CycleQ2GeometricAffineKahlerSheaf

attribute [local instance] CycleQ2LiteralProjectiveIntersectionKernel.nativeReductionAlgebra
  CycleQ2LiteralProjectiveIntersectionComplex.thickComplexAlgebra
  CycleQ2LiteralProjectiveIntersectionComplex.closedComplexAlgebra
  CycleQ2LiteralProjectiveIntersectionComplex.thickComplexSMul
  CycleQ2LiteralProjectiveIntersectionComplex.closedComplexSMul
  CycleQ2LiteralProjectiveIntersectionComplex.thickComplexModule
  CycleQ2LiteralProjectiveIntersectionComplex.closedComplexModule
  CycleQ2LiteralProjectiveIntersectionComplex.complexReductionTower

def nativeTensorSplittingTilde (s : Finset Vertex) (a : Fin 4) (ha : Admissible s a) :
    kahlerTilde (A := ClosedRing s) ⟶ nativeCotangentTilde s :=
  tilde.map (ModuleCat.ofHom (nativeCotangentSplitting s a ha))

private theorem tildeSection_fac {R : CommRingCat} {D N : ModuleCat R}
    (t : D ⟶ N) (q : N ⟶ D) (h : t ≫ q = 𝟙 D) :
    tilde.map (R := R) t ≫ tilde.map q = 𝟙 _ := by
  rw [← tilde.map_comp, h, tilde.map_id]

theorem nativeTensorSplittingTilde_fac (s : Finset Vertex) (a : Fin 4) (ha : Admissible s a) :
    nativeTensorSplittingTilde s a ha ≫ nativeTensorReductionTilde s = 𝟙 _ := by
  let N := ModuleCat.of (ClosedRing s) (NativeCotangent s)
  let D := ModuleCat.of (ClosedRing s) (KaehlerDifferential ℂ (ClosedRing s))
  let t : D ⟶ N := ModuleCat.ofHom (nativeCotangentSplitting s a ha)
  let q : N ⟶ D := ModuleCat.ofHom (nativeCotangentReduction s)
  have h : t ≫ q = 𝟙 D :=
    ModuleCat.hom_ext (nativeCotangentReduction_splitting s a ha)
  exact tildeSection_fac (R := CommRingCat.of (ClosedRing s)) (D := D) (N := N) t q h

private theorem transportedSection_fac {C : Type*} [Category* C] {X Y X' Y' : C}
    (q : X ⟶ Y) (q' : X' ⟶ Y') (e : X ≅ X') (d : Y ≅ Y') (t : Y' ⟶ X')
    (hq : e.hom ≫ q' = q ≫ d.hom) (ht : t ≫ q' = 𝟙 _) :
    (d.hom ≫ t ≫ e.inv) ≫ q = 𝟙 Y := by
  apply (cancel_mono d.hom).mp
  simp only [Category.assoc, Category.id_comp, ← hq, e.inv_hom_id_assoc, ht, Category.comp_id]

/-- The section in the actual scheme-module category on the intersection chart. -/
def chartCotangentSection (s : Finset Vertex) (hs : s.Nonempty) (a : Fin 4)
    (ha : Admissible s a) :
    (Scheme.Modules.pullback (closedAffineMap s hs)).obj originalDifferentialSheaf ⟶
      (Scheme.Modules.pullback (closedAffineMap s hs)).obj restrictedCotangentSheaf :=
  (closedDifferentialIso s hs).hom ≫ nativeTensorSplittingTilde s a ha ≫
    (nativeCotangentIso s hs).inv

theorem chartCotangentSection_fac (s : Finset Vertex) (hs : s.Nonempty) (a : Fin 4)
    (ha : Admissible s a) :
    chartCotangentSection s hs a ha ≫
      (Scheme.Modules.pullback (closedAffineMap s hs)).map cotangentReduction = 𝟙 _ :=
  transportedSection_fac _ _ (nativeCotangentIso s hs) (closedDifferentialIso s hs)
    (nativeTensorSplittingTilde s a ha) (nativeCotangentReduction_comm s hs)
    (nativeTensorSplittingTilde_fac s a ha)

/-- Every nonempty native intersection has a split-epimorphic reduction. -/
theorem chartCotangentReduction_isSplitEpi (s : Finset Vertex) (hs : s.Nonempty) :
    IsSplitEpi ((Scheme.Modules.pullback (closedAffineMap s hs)).map cotangentReduction) := by
  obtain ⟨⟨a, l⟩, hv⟩ := hs
  exact ⟨⟨⟨chartCotangentSection s _ a ⟨l, hv⟩, chartCotangentSection_fac s _ a ⟨l, hv⟩⟩⟩⟩

end CycleQ2LiteralCotangentLocalSplitting

end

#print axioms CycleQ2LiteralCotangentLocalSplitting.chartCotangentSection_fac
#print axioms CycleQ2LiteralCotangentLocalSplitting.chartCotangentReduction_isSplitEpi
