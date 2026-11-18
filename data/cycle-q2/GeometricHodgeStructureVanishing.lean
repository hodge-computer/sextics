import Proposal.GeometricHodgeTwistTorusChart

/-!
# Actual structure-sheaf primitives on the monic weighted sextic

The common Laurent coordinates give primitives for actual structure-sheaf
one- and two-cocycles on the four weight-one opens. Affine local vanishing
then identifies both intermediate ordinary cohomology groups as zero.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2HodgeStructureVanishing

open CategoryTheory AlgebraicGeometry TopologicalSpace
open CycleQ2GenericSexticGradient (CoeffRing)
open CycleQ2GeometricHodgeThreefold (threefold coordinateOpen vertexCoefficient)
open CycleQ2GeometricProjectiveHOne (structureAdditiveSheaf)
open CycleQ2InjectiveCech CycleQ2FiniteInjectiveCech CycleQ2GeometricSheafLocalIso
open CycleQ2HodgeTwistTorusChart (structureLaurentSections)

local instance (X : TopCat.{0}) : HasExt.{1} (AbSheaf X) := HasExt.standard _

variable {R : Type} [CommRing R] [Nontrivial R] (φ : CoeffRing →+* R)
  (h : IsUnit (φ vertexCoefficient))

abbrev O := structureAdditiveSheaf (threefold φ)
abbrev U := coordinateOpen φ

include h in
/-- An actual one-cocycle on the original four opens has vertex primitives. -/
theorem one_primitive (c : One (O φ) (U φ)) (hc : IsOneCocycle (O φ) (U φ) c) :
    ∃ p : CycleQ2FiniteCechDescent.Zero (O φ) (U φ),
      ∀ i j W hi hj, res (O φ) hj (p j) - res (O φ) hi (p i) =
        edgeValue (O φ) (U φ) c i j W hi hj :=
  CycleQ2HodgeTwistCoordinates.one_primitive (structureLaurentSections φ h) c hc

include h in
/-- An actual two-cocycle has an edge primitive on these same opens. -/
theorem two_primitive (c : Two (O φ) (U φ)) (hc : IsTwoCocycle (O φ) (U φ) c) :
    ∃ b : One (O φ) (U φ), ∀ i j k W hi hj hk,
      boundaryValue (O φ) (U φ) b i j k W hi hj hk =
        faceValue (O φ) (U φ) c i j k W hi hj hk :=
  CycleQ2HodgeTwistCoordinates.two_primitive (structureLaurentSections φ h) c hc

include h in
/-- Both intermediate cohomology groups of the genuine structure sheaf vanish. -/
theorem ordinary_vanishing : Subsingleton ((O φ).H 1) ∧ Subsingleton ((O φ).H 2) := by
  have ha (S : Finset (Fin 4)) (i : Fin 4) (hi : i ∈ S) :
      IsAffineOpen (S.inf (coordinateOpen φ)) := by
    rw [← CycleQ2HodgeTwistFaces.face_inf φ i S hi]
    exact CycleQ2HodgeTwistFaces.face_affine φ i _
  apply CycleQ2HodgeTwistCoordinates.ordinary_vanishing (structureLaurentSections φ h)
    (CycleQ2GeometricHodgeThreefold.coordinateOpens_cover φ h)
  · intro i
    simpa using ha {i} i (by simp)
  · intro i j
    simpa using ha {i,j} i (by simp)
  · intro i
    exact { app := fun V hV => AddEquiv.refl _, naturality := fun _ _ _ => rfl }

end CycleQ2HodgeStructureVanishing
end

#print axioms CycleQ2HodgeStructureVanishing.one_primitive
#print axioms CycleQ2HodgeStructureVanishing.two_primitive
#print axioms CycleQ2HodgeStructureVanishing.ordinary_vanishing
