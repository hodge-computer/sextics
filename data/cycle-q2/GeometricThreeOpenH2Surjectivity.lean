import Proposal.GeometricThreeOpenH2Naturality

/-!
# Surjectivity of the three-open degree-two comparison

The inner and outer Mayer–Vietoris sequences give representatives on the
triple intersection when the three opens have vanishing H² and their pair
intersections have vanishing H¹.

Prepared for fqlx with OpenAI ChatGPT assistance; see solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2ThreeOpenH2Surjectivity

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
  TopologicalSpace Opposite CycleQ2ThreeOpenCechH2
  CycleQ2GeometricConeCech.HZero CycleQ2ThreeOpenH2Naturality

variable {X : TopCat.{0}}
  [HasExt.{1} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0})]
  (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0})

private theorem deltaOne_surjective (S : (Opens.grothendieckTopology X).MayerVietorisSquare)
    (h₂ : Subsingleton (F.H' 2 S.X₂)) (h₃ : Subsingleton (F.H' 2 S.X₃)) :
    Function.Surjective (S.δ F 1 2 rfl) := by
  intro y
  have hy : S.toBiprod F 2 y = 0 := by
    rw [S.toBiprod_apply]
    have hz : ((F.cohomologyPresheaf 2).map S.f₂₄.op y,
        (F.cohomologyPresheaf 2).map S.f₃₄.op y) = (0,0) :=
      Prod.ext (h₂.elim _ _) (h₃.elim _ _)
    rw [hz]
    exact map_zero _
  exact (ShortComplex.ab_exact_iff _).mp ((S.sequence_exact F 1 2 rfl).exact 2) y hy

/-- Every class on the union is represented by an actual triple section. -/
theorem connecting_surjective (U V W : Opens X)
    [hU : Subsingleton (F.H' 2 U)] [hV : Subsingleton (F.H' 2 V)]
    [hW : Subsingleton (F.H' 2 W)] [hUV : Subsingleton (F.H' 1 (U ⊓ V))]
    [hUW : Subsingleton (F.H' 1 (U ⊓ W))] [hVW : Subsingleton (F.H' 1 (V ⊓ W))] :
    Function.Surjective (CycleQ2ThreeOpenSectionH2.connecting F U V W) := by
  let S := Opens.mayerVietorisSquare U V
  have hpair : Subsingleton (F.H' 2 (U ⊔ V)) := by
    apply subsingleton_of_forall_eq 0
    intro y
    obtain ⟨x, rfl⟩ := deltaOne_surjective F S hU hV y
    have hx : x = 0 := hUV.elim _ _
    rw [hx, map_zero]
  let R := Opens.mayerVietorisSquare (U ⊓ W) (V ⊓ W)
  let : Subsingleton (F.H' 1 R.X₂) := hUW
  let : Subsingleton (F.H' 1 R.X₃) := hVW
  intro y
  obtain ⟨z,hz⟩ := deltaOne_surjective F (outerSquare U V W) hpair hW y
  obtain ⟨x,hx⟩ := delta_surjective F R z
  refine ⟨sectionsEquiv F (TripleOpen U V W) x, ?_⟩
  change (outerSquare U V W).δ F 1 2 rfl (R.δ F 0 1 rfl
    ((sectionsEquiv F (TripleOpen U V W)).symm ((sectionsEquiv F (TripleOpen U V W)) x))) = y
  rw [AddEquiv.symm_apply_apply,hx,hz]

theorem connectingAtTop_surjective (U V W : Opens X) (hcover : (U ⊔ V) ⊔ W = ⊤)
    [Subsingleton (F.H' 2 U)] [Subsingleton (F.H' 2 V)] [Subsingleton (F.H' 2 W)]
    [Subsingleton (F.H' 1 (U ⊓ V))] [Subsingleton (F.H' 1 (U ⊓ W))]
    [Subsingleton (F.H' 1 (V ⊓ W))] :
    Function.Surjective (connectingAtTop F U V W hcover) :=
  (((F.cohomologyPresheaf 2).mapIso (eqToIso hcover.symm).op).addCommGroupIsoToAddEquiv.surjective).comp
    (connecting_surjective F U V W)

#print axioms connectingAtTop_surjective

end CycleQ2ThreeOpenH2Surjectivity

end
