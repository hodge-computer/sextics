import Proposal.GeometricLiteralThreefoldMixedVertexBinding
import Proposal.GeometricLiteralThreefoldMixedEdgeGauge
import Proposal.GeometricThreefoldMixedTimeVelocity

/-!
# A fixed-overlap test edge with two independently normalized chart velocities

An ambient overlap function is evaluated on the first-order section ring.
The velocity in each chart may be chosen separately, provided both take the
same value on the generator of the closed fibre. This gives the actual two
vertex corrections and the adapted edge in their respective coordinates.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2LiteralThreefoldNormalizedEdge

open MvPolynomial CycleQ2LiteralAbelJacobiContraction CycleQ2LiteralThreefoldChartLift
  CycleQ2LiteralThreefoldLiftDifference CycleQ2LiteralThreefoldResidueCoordinates CycleQ2LiteralThreefoldResidueChartMaps
  CycleQ2LiteralThreefoldLiftTransition CycleQ2LiteralThreefoldTriangleLifts
  CycleQ2LiteralThreefoldTestEdges CycleQ2LiteralThreefoldMixedLiftChange CycleQ2LiteralThreefoldMixedEdgeGauge
  CycleQ2LiteralThreefoldMixedRestriction CycleQ2LiteralThreefoldMixedVertexBinding CycleQ2ThreefoldMixedCurveForm
  CycleQ2LiteralThreefoldSurfaceNormal CycleQ2LiteralThreefoldTangentOverlap
  CycleQ2ThreefoldContractionAlongMap CycleQ2ThreefoldMixedTimeVelocity

variable {B C : Type} [CommRing B] [CommRing C] [Algebra ℂ B] [Algebra ℂ C] [Algebra B C]
  [IsScalarTower ℂ B C] [Module.Projective C (KaehlerDifferential ℂ C)] [Subsingleton (Forms C 2)]

section Velocity
variable {U : Type} [CommRing U] [Algebra ℂ U] [Algebra U B] [IsScalarTower ℂ U B]
  [Algebra U C] [IsScalarTower ℂ U C] [IsScalarTower U B C]
  {i : Fin 4} (a : T i →ₐ[ℂ] U) (x y : Lift i C)
  (hx : LiesOver x ((IsScalarTower.toAlgHom ℂ U C).comp a))
  (hy : LiesOver y ((IsScalarTower.toAlgHom ℂ U C).comp a))

theorem vertex_same_speed (e : B) (surj : Function.Surjective (algebraMap B C))
    (ker : RingHom.ker (algebraMap B C) = Ideal.span {e})
    (v w : Derivation ℂ B C) (h : v e = w e) :
    vertexMixed a x y hx hy (v.compAlgebraMap U) = vertexMixed a x y hx hy (w.compAlgebraMap U) := by
  let f := (IsScalarTower.toAlgHom ℂ U C).comp a
  let g := (IsScalarTower.toAlgHom ℂ U B).comp a
  let := a.toRingHom.toAlgebra
  let := IsScalarTower.of_algHom a
  let := f.toRingHom.toAlgebra
  let := IsScalarTower.of_algHom f
  let := g.toRingHom.toAlgebra
  let := IsScalarTower.of_algHom g
  let : IsScalarTower (T i) B C := IsScalarTower.of_algebraMap_eq fun r => by
    exact IsScalarTower.algebraMap_apply U B C (a r)
  exact mixed_eq_of_speed e surj ker (tangent x y hx hy) v w h (orientedVolume i)
end Velocity

variable (i j : Fin 4) (k : Fin 3) (d : FixedOverlap i k →ₐ[ℂ] B)
  (f : T i →ₐ[ℂ] C) (g : T j →ₐ[ℂ] C)

private abbrev reduced := (IsScalarTower.toAlgHom ℂ B C).comp d

/-- The three correction terms are computed in their native chart. The
source and target velocities can come from different first-order charts. -/
theorem corrected (hij : i.succAbove k = j)
    (hf : (reduced (C := C) i k d).comp (sourceMap i k) = f)
    (hg : ∀ p : MvPolynomial (Option (Fin 3)) ℂ,
      reduced (C := C) i k d (fixedTargetMap i k (q (i.succAbove k) p)) = g (q j p))
    (x : Lift i C) (x' y : Lift j C) (hn : Normalizes x x')
    (hx : LiesOver x f) (hx' : LiesOver x' g) (hy : LiesOver y g)
    (e : B) (surj : Function.Surjective (algebraMap B C)) (ker : RingHom.ker (algebraMap B C) = Ideal.span {e})
    (v w : Derivation ℂ B C) (speed : v e = w e) :
    letI := d.toRingHom.toAlgebra
    letI := IsScalarTower.of_algHom d
    letI := (reduced (C := C) i k d).toRingHom.toAlgebra
    letI := IsScalarTower.of_algHom (reduced (C := C) i k d)
    letI : IsScalarTower (FixedOverlap i k) B C := IsScalarTower.of_algebraMap_eq' rfl
    letI := f.toRingHom.toAlgebra
    letI := IsScalarTower.of_algHom f
    letI := g.toRingHom.toAlgebra
    letI := IsScalarTower.of_algHom g
    ∀ (ν : Derivation ℂ (T i) C) (μ : Derivation ℂ (T j) C),
      (∀ r, v (d (sourceMap i k r)) = ν r) →
      (∀ p : MvPolynomial (Option (Fin 3)) ℂ,
        w (d (fixedTargetMap i k (q (i.succAbove k) p))) = μ (q j p)) →
      contractRestrict (v.compAlgebraMap (FixedOverlap i k)) (nativeEdge i k) +
        vertexForm g (canonical j g) y (canonical_liesOver j g) hy μ =
      vertexForm f (canonical i f) x (canonical_liesOver i f) hx ν +
        vertexForm g x' y hx' hy μ := by
  subst j
  have htarget : (reduced (C := C) i k d).comp (fixedTargetMap i k) = g := by
    apply AlgHom.ext
    intro r
    obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective r
    exact hg p
  subst g
  subst f
  let := d.toRingHom.toAlgebra
  let := IsScalarTower.of_algHom d
  let := (reduced (C := C) i k d).toRingHom.toAlgebra
  let := IsScalarTower.of_algHom (reduced (C := C) i k d)
  let : IsScalarTower (FixedOverlap i k) B C := IsScalarTower.of_algebraMap_eq' rfl
  intro ν μ hν hμ
  have hw (r : T (i.succAbove k)) : w (d (fixedTargetMap i k r)) = μ r := by
    obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective r
    exact hμ p
  let a := sourceMap i k
  let b := fixedTargetMap i k
  have target (z : Lift (i.succAbove k) C) (hz : LiesOver z ((reduced (C := C) i k d).comp b)) :
      vertexMixed b z y hz hy (v.compAlgebraMap (FixedOverlap i k)) =
        vertexForm ((reduced (C := C) i k d).comp b) z y hz hy μ :=
    (vertex_same_speed b z y hz hy e surj ker v w speed).trans
      (vertexMixed_eq_vertexForm b _ rfl z y hz hy hz hy (w.compAlgebraMap (FixedOverlap i k)) μ hw)
  have src := vertexMixed_eq_vertexForm a _ rfl (canonical i ((reduced (C := C) i k d).comp a)) x
    (canonical_liesOver _ _) hx (canonical_liesOver _ _) hx (v.compAlgebraMap (FixedOverlap i k)) ν hν
  exact ((congrArg (contractRestrict (v.compAlgebraMap (FixedOverlap i k)) (nativeEdge i k) + ·)
    (target _ (canonical_liesOver _ _))).symm.trans
    (nativeEdge_mixed_change_of_lifts i k x x' y hn hx hx' hy (v.compAlgebraMap (FixedOverlap i k)))).trans
      (congrArg₂ (· + ·) src (target x' hx'))

end CycleQ2LiteralThreefoldNormalizedEdge
end

#print axioms CycleQ2LiteralThreefoldNormalizedEdge.corrected
