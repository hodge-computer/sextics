import Proposal.GeometricLiteralMovingDivisorOrbitPullback
import Proposal.GeometricLiteralMovingDivisorCoordinate
import Proposal.GeometricLiteralMovingDivisorOrbitPrincipal
import Proposal.GeometricLiteralOrbitChern
import Proposal.GeometricLiteralMovingDivisorOrbitFrames

/-!
# Geometric translates of the original curve ideal on a common chart

The pullback of the native Cartier equation generates the two acted-on
homogeneous equations on every coordinate patch meeting a translated
Cartier open. Both numerators have degree two, so changing the coordinate
denominator multiplies both sections by the same unit.

Prepared for fqlx with OpenAI ChatGPT assistance; see solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralMovingDivisorOrbitPullback

open CategoryTheory AlgebraicGeometry MvPolynomial
  CycleQ2SeedTrace CycleQ2NormalConnecting CycleQ2GeometricSeedNormalIdeals
  CycleQ2GeometricCartierNormalLift CycleQ2CartierSurfaceGrading
  CycleQ2SeedCyclicAction CycleQ2SeedProjectiveImageCocycle CycleQ2LiteralOrbitAction
  CycleQ2LiteralProjectiveDeformation CycleQ2LiteralProjectiveIntersections
  CycleQ2LiteralProjectiveIntersectionRestrictions CycleQ2LiteralNativeCartierFrames CycleQ2LiteralNativeGaugeSections CycleQ2LiteralOrbitChern
  CycleQ2LiteralMovingDivisorCoordinate CycleQ2LiteralMovingDivisorOrbitPrincipal

private theorem span_pair_unit_mul {R : Type*} [CommRing R] {u : R} (hu : IsUnit u) (a b : R) :
    Ideal.span {u * a, u * b} = Ideal.span {a,b} := by
  rw [Ideal.span_insert, Ideal.span_insert a,
    ← Ideal.span_singleton_mul_span_singleton, ← Ideal.span_singleton_mul_span_singleton,
    Ideal.span_singleton_eq_top.mpr hu, Ideal.top_mul, Ideal.top_mul]

private theorem nativeSection₁ (s : Finset Vertex) (hs : s.Nonempty) (v : Vertex) (hv : v ∈ s) :
    closedSectionsEquiv s hs (normalizedEquation s v hv 2) =
      polynomialSection v.2 (closedOpen s) (closedOpen_le_patch s v hv) (originalF1 57) :=
  normalized_polynomialSection s hs v hv 2 (cartierElement 2) (cartierElement_homogeneous 2)
    (originalF1 57) (originalF1_homogeneous 57) (reduction_cartierElement 2)

private theorem nativeSection₂ (s : Finset Vertex) (hs : s.Nonempty) (v : Vertex) (hv : v ∈ s) :
    closedSectionsEquiv s hs (normalizedEquation s v hv 3) =
      polynomialSection v.2 (closedOpen s) (closedOpen_le_patch s v hv) originalF2 :=
  normalized_polynomialSection s hs v hv 2 (cartierElement 3) (cartierElement_homogeneous 3)
    originalF2 originalF2_homogeneous (reduction_cartierElement 3)

private theorem pullback_span_pair (z : ℂ) (hz : z^3 = 1) (a i : Fin 3)
    (V W : Surface.Opens) (hV : V ≤ Patch a) (hi : W ≤ Patch i)
    (hW : W ≤ (closedProjectiveAction z hz).hom ⁻¹ᵁ V) (n : ℕ) (p q : WeightedPoly)
    (hp : p.IsWeightedHomogeneous weight n) (hq : q.IsWeightedHomogeneous weight n) :
    Ideal.span {((closedProjectiveAction z hz).hom.appLE V W hW) (polynomialSection a V hV p),
      ((closedProjectiveAction z hz).hom.appLE V W hW) (polynomialSection a V hV q)} =
      Ideal.span {polynomialSection i W hi (polynomialAction z p),
        polynomialSection i W hi (polynomialAction z q)} := by
  let ha := (hW.trans ((closedProjectiveAction z hz).hom.preimage_mono hV)).trans
    (preimage_patch_le z hz a)
  let c := (coordinateScale z a)⁻¹ ^ n
  let t := transitionUnit i a W hi ha ^ n
  have hc : IsUnit (polynomialSection a W ha (C c)) :=
    (isUnit_iff_ne_zero.mpr (pow_ne_zero n (inv_ne_zero (coordinateScale_ne_zero z hz a)))).map
      ((polynomialSection a W ha).comp C)
  rw [polynomialSection_pullback z hz a V W hV hW n p hp,
    polynomialSection_pullback z hz a V W hV hW n q hq, map_mul, map_mul,
    polynomialSection_change i a W hi ha n _ (polynomialAction_weighted z hp), polynomialSection_change i a W hi ha n _ (polynomialAction_weighted z hq)]
  change Ideal.span {polynomialSection a W ha (C c) * ((t : Γ(Surface,W)) * _),
    polynomialSection a W ha (C c) * ((t : Γ(Surface,W)) * _)} = _
  rw [span_pair_unit_mul hc, span_pair_unit_mul t.isUnit]

/-- The chosen native Cartier generator pulls back to a generator of the
ideal of the two acted-on equations, in any common affine chart. -/
theorem edgeGenerator_span_pair (z : ℂ) (hz : z^3 = 1) (i : Fin 3)
    (W : Surface.Opens) (hi : W ≤ Patch i) (v : Vertex)
    (hv : W ≤ (closedProjectiveAction z hz).hom ⁻¹ᵁ cover v) :
    Ideal.span {edgeGenerator (closedProjectiveAction z hz).hom v W hv} =
      Ideal.span {polynomialSection i W hi (polynomialAction z (originalF1 57)),
        polynomialSection i W hi (polynomialAction z originalF2)} := by
  let j := (closedProjectiveAction z hz).hom
  let s : Finset Vertex := {v}
  have hsv : v ∈ s := Finset.mem_singleton_self v
  have hvc : cover v ≤ closedOpen s := by
    rw [closedOpen_eq]
    refine le_iInf (fun w => le_iInf (fun hw => ?_))
    have he : w = v := Finset.mem_singleton.mp hw
    subst w
    exact le_rfl
  let hw := hv.trans (j.preimage_mono hvc)
  let hs : s.Nonempty := ⟨v,hsv⟩
  change Ideal.span {chartMap j s hs W hw (generator s v hsv)} = _
  rw [← nativeGenerator_map_span s v hsv (chartMap j s hs W hw)]
  change Ideal.span {j.appLE (closedOpen s) W hw (closedSectionsEquiv s hs (normalizedEquation s v hsv 2)),
    j.appLE (closedOpen s) W hw (closedSectionsEquiv s hs (normalizedEquation s v hsv 3))} = _
  rw [nativeSection₁, nativeSection₂]
  exact pullback_span_pair z hz v.2 i (closedOpen s) W (closedOpen_le_patch s v hsv) hi hw
    2 (originalF1 57) originalF2 (originalF1_homogeneous 57) originalF2_homogeneous

/-- The scheme-theoretic pullback of the chosen original Cartier generator
generates the translated seed ideal on the simultaneous open. -/
theorem edgeGenerator_span (z : ℂ) (hz : z^3 = 1) (i : Fin 3)
    (W : Surface.Opens) (hi : W ≤ Patch i) (v : Vertex)
    (hv : W ≤ (closedProjectiveAction z hz).hom ⁻¹ᵁ cover v) :
    Ideal.span {edgeGenerator (closedProjectiveAction z hz).hom v W hv} =
      CycleQ2LiteralMovingDivisorOrbitFrames.translateIdeal i W hi z :=
  (edgeGenerator_span_pair z hz i W hi v hv).trans
    (CycleQ2LiteralMovingDivisorOrbitFrames.translateIdeal_eq_pair i W hi z hz).symm

end CycleQ2LiteralMovingDivisorOrbitPullback

end

#print axioms CycleQ2LiteralMovingDivisorOrbitPullback.edgeGenerator_span
