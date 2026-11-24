import Proposal.GeometricLiteralThreefoldTestClass

/-!
# Comparison of ambient and surface-adapted test lifts

On each original threefold overlap, replacing the two ambient lifts by
lifts of the same deformation changes the evaluated two-form by the
difference of the two vertex corrections. Each correction is evaluated in
its own chart.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2LiteralThreefoldTestGauge

open MvPolynomial CycleQ2LiteralAbelJacobiContraction CycleQ2LiteralThreefoldKodairaSpencer
  CycleQ2LiteralThreefoldChartLift CycleQ2LiteralThreefoldResidueCoordinates
  CycleQ2LiteralThreefoldResidueChartMaps CycleQ2LiteralThreefoldLiftTransition
  CycleQ2LiteralThreefoldLiftDifference CycleQ2LiteralThreefoldTriangleLifts
  CycleQ2LiteralThreefoldTestEdges CycleQ2LiteralThreefoldTestClass

variable {S : Type} [CommRing S] [Algebra ℂ S]

/-- The literal ambient edge plus the target-vertex correction equals the
source-vertex correction plus the edge from the alternative two lifts. -/
theorem nativeEdge_change_of_lifts (i : Fin 4) (k : Fin 3) (g : FixedOverlap i k →ₐ[ℂ] S)
    (z : Lift i S) (z' w : Lift (i.succAbove k) S) (hn : Normalizes z z')
    (hz : LiesOver z (g.comp (sourceMap i k))) (hz' : LiesOver z' (g.comp (fixedTargetMap i k)))
    (hw : LiesOver w (g.comp (fixedTargetMap i k))) :
    edgeAt i k g + value (canonical _ (g.comp (fixedTargetMap i k))) w (fun a => (hw a).symm) =
      value (canonical i (g.comp (sourceMap i k))) z (fun a => (hz a).symm) +
        value z' w (fun a => (hz' a).trans (hw a).symm) := by
  let j := i.succAbove k
  let t := normalizedLift i k g
  let u := canonical j (g.comp (fixedTargetMap i k))
  have htu (a : Index) : (t.x a).fst = (u.x a).fst := normalizedLift_fst i k g a
  have htz (a : Index) : (t.x a).fst = (z'.x a).fst := (htu a).trans (hz' a).symm
  have hzw (a : Index) : (z'.x a).fst = (w.x a).fst := (hz' a).trans (hw a).symm
  have hvertex := value_normalizes (Fin.succAbove_ne i k).symm
    (normalizedLift_normalizes i k g) hn (fun a => (hz a).symm) htz
  calc
    _ = value t w (fun a => (htu a).trans (hw a).symm) :=
      (value_cocycle t u w htu (fun a => (hw a).symm)).symm
    _ = value t z' htz + value z' w hzw := value_cocycle t z' w htz hzw
    _ = _ := congrArg (fun a => a + value z' w hzw) hvertex

/-- Evaluate a difference as a vector along the ambient chart, retaining the
transverse differential before passage to ordinary differentials on the base. -/
def liftCovector {i : Fin 4} (f : T i →ₐ[ℂ] S) (x y : Lift i S)
    (hx : LiesOver x f) (hy : LiesOver y f) :
    KaehlerDifferential ℂ (T i) →ₛₗ[f.toRingHom] S :=
  CycleQ2TangentPointDifferential.covector f
    (CycleQ2LiteralThreefoldTangentCoordinates.tangentPoint x y (fun a => (hx a).trans (hy a).symm))
    (by
      intro a
      obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective a
      rw [show Ideal.Quotient.mk _ p = q i p from rfl,
        CycleQ2LiteralThreefoldTangentCoordinates.tangentPoint_mk]
      exact eval_fst x f hx p)

theorem liftCovector_D {i : Fin 4} (f : T i →ₐ[ℂ] S) (x y : Lift i S)
    (hx : LiesOver x f) (hy : LiesOver y f) (p : P) :
    liftCovector f x y hx hy (KaehlerDifferential.D ℂ (T i) (q i p)) =
      (aeval x.x p).snd - (aeval y.x p).snd := by
  rw [liftCovector, CycleQ2TangentPointDifferential.covector_D,
    CycleQ2LiteralThreefoldTangentCoordinates.tangentPoint_mk]
  rfl

/-- The gauge comparison in the full ambient tangent space along the point.
It can consequently be evaluated against a vector transverse to the surface. -/
theorem native_covector_correction (i : Fin 4) (k : Fin 3) (g : FixedOverlap i k →ₐ[ℂ] S)
    (z w : Lift (i.succAbove k) S) (hz : LiesOver z (g.comp (fixedTargetMap i k)))
    (hw : LiesOver w (g.comp (fixedTargetMap i k))) :
    let f := g.comp (fixedTargetMap i k)
    let x := normalizedLift i k g
    let y := canonical (i.succAbove k) f
    let hx : LiesOver x f := normalizedLift_fst i k g
    let hy : LiesOver y f := canonical_liesOver _ _
    liftCovector f x y hx hy + liftCovector f y w hy hw =
      liftCovector f x z hx hz + liftCovector f z w hz hw := by
  dsimp only
  apply LinearMap.ext_on_range (KaehlerDifferential.span_range_derivation ℂ _)
  intro a
  obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective a
  simp only [LinearMap.add_apply, show Ideal.Quotient.mk _ p = q (i.succAbove k) p from rfl,
    liftCovector_D]
  abel

end CycleQ2LiteralThreefoldTestGauge
end

#print axioms CycleQ2LiteralThreefoldTestGauge.nativeEdge_change_of_lifts
#print axioms CycleQ2LiteralThreefoldTestGauge.native_covector_correction
