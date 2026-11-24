import Proposal.GeometricFiniteCechHOneRefinement

/-!
# Checking a signed difference of Čech edges on affine opens

Sections of an additive sheaf on a scheme are determined on its affine
basis. A signed edge identity with given vertex corrections can therefore
be verified in the actual affine coordinate rings.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2AffineCechGauge

open CycleQ2GeometricSheafLocalIso CategoryTheory Opposite TopologicalSpace AlgebraicGeometry CycleQ2InjectiveCech
  CycleQ2FiniteInjectiveCech CycleQ2FiniteCechDescent

variable {X : Scheme.{0}} {ι : Type} (F : AbSheaf X) (U : ι → X.Opens)

theorem signed_edges_on_affines (c b : One F U) (x : Zero F U) (i j : ι)
    (h : ∀ (W : X.Opens) (hi : W ≤ U i) (hj : W ≤ U j), IsAffineOpen W →
      edgeValue F U c i j W hi hj + res F hj (x j) = res F hi (x i) - edgeValue F U b i j W hi hj)
    (W : X.Opens) (hi : W ≤ U i) (hj : W ≤ U j) :
    edgeValue F U c i j W hi hj + res F hj (x j) = res F hi (x i) - edgeValue F U b i j W hi hj := by
  apply TopCat.Presheaf.IsSheaf.section_ext F.property
  intro p hp
  obtain ⟨V,hV,hpV,hVW⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens hp
  refine ⟨V,hVW,hpV,?_⟩
  change res F hVW (_ + _) = res F hVW (_ - _)
  rw [map_add, map_sub]
  unfold edgeValue
  simp only [res_comp]
  exact h V (hVW.trans hi) (hVW.trans hj) hV

end CycleQ2AffineCechGauge
end

#print axioms CycleQ2AffineCechGauge.signed_edges_on_affines
