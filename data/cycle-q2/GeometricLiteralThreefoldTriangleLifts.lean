import Proposal.GeometricLiteralThreefoldLiftTransition

/-!
# Comparing normalizations of a lifted point on three charts

Given two normalizations of the same first-order point, rescale the first
by the original source coordinate times the second inverse coordinate.
This gives the second normalization, including its square-zero part.
Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2LiteralThreefoldTriangleLifts

open CycleQ2LiteralAbelJacobiContraction CycleQ2LiteralThreefoldKodairaSpencer
  CycleQ2LiteralThreefoldChartLift CycleQ2LiteralThreefoldResidueCoordinates
  CycleQ2LiteralThreefoldLiftTransition

variable {S : Type*} [CommRing S] [Algebra ℂ S]

/-- The source point, written with target homogeneous coordinate equal to one,
is the given target point. The witness inverts the full first-order coordinate. -/
def Normalizes {i j : Fin 4} (x : Lift i S) (y : Lift j S) : Prop :=
  ∃ (u : Jet S) (hu : u * linearValues i x.x j = 1), change x j u hu = y

theorem normalizedLift_normalizes (i : Fin 4) (k : Fin 3) (g : FixedOverlap i k →ₐ[ℂ] S) :
    Normalizes (canonical i (g.comp (sourceMap i k))) (normalizedLift i k g) :=
  ⟨↑(sourceUnit i k g)⁻¹, sourceUnit_normalizes i k g, rfl⟩

theorem normalizedLift_normalizes_of_source (i : Fin 4) (k : Fin 3)
    (g : FixedOverlap i k →ₐ[ℂ] S) (f : T i →ₐ[ℂ] S) (hf : g.comp (sourceMap i k) = f) :
    Normalizes (canonical i f) (normalizedLift i k g) := by
  subst f
  exact normalizedLift_normalizes i k g

/-- Two changes from the same lifted point determine a change from the
first target chart to the second. This also applies when chart indices coincide. -/
theorem normalizes_common_source {i j l : Fin 4} {x : Lift i S} {y : Lift j S} {z : Lift l S}
    (hxy : Normalizes x y) (hxz : Normalizes x z) : Normalizes y z := by
  obtain ⟨u, hu, rfl⟩ := hxy
  obtain ⟨v, hv, rfl⟩ := hxz
  let d := linearValues i x.x j
  let w := v * d
  have hwu : w * u = v := by
    calc
      w * u = v * (u * d) := by dsimp [w]; ring
      _ = v := by rw [show u * d = 1 from hu, mul_one]
  have he : linearValues j (changedCoordinate i j x.x u) l = u * linearValues i x.x l := by
    simpa only [eval_linearCoordinate, linearValues] using changed_linear i j x.x u hu l
  have hw : w * linearValues j (change x j u hu).x l = 1 := by
    change w * linearValues j (changedCoordinate i j x.x u) l = 1
    rw [he, ← mul_assoc, hwu, hv]
  obtain ⟨hw', hchange⟩ := change_comp i j l x u w hu hw
  refine ⟨w, hw, lift_ext (hchange.trans ?_)⟩
  exact congrArg (changedCoordinate i l x.x) hwu

end CycleQ2LiteralThreefoldTriangleLifts
end

#print axioms CycleQ2LiteralThreefoldTriangleLifts.normalizedLift_normalizes_of_source
#print axioms CycleQ2LiteralThreefoldTriangleLifts.normalizes_common_source
