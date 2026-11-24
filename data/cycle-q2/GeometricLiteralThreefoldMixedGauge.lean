import Proposal.GeometricLiteralThreefoldTestGauge
import Proposal.GeometricThreefoldMixedCurveForm

/-!
# The comparison with the surface-adapted lifts before restricting the normal slot

On chart overlaps, the two vertex corrections compare the actual ambient
test derivative with alternate lifts in the full ambient cotangent space.
Inserting the motion vector into the second slot gives this same correction
identity in ordinary curve one-forms, including motions transverse to the
cubic surface.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2LiteralThreefoldMixedGauge

open CycleQ2LiteralAbelJacobiContraction CycleQ2LiteralThreefoldChartLift
  CycleQ2LiteralThreefoldResidueCoordinates CycleQ2LiteralThreefoldResidueChartMaps
  CycleQ2LiteralThreefoldLiftTransition CycleQ2LiteralThreefoldLiftDifference
  CycleQ2ThreefoldMixedCurveForm CycleQ2ThreefoldContractionAlongMap

variable {S : Type} [CommRing S] [Algebra ℂ S]
  [Module.Projective S (KaehlerDifferential ℂ S)]

/-- Four first-order lifts give the same mixed curve one-form around the
quadrilateral, for any transverse motion vector. -/
theorem mixed_lift_correction {i : Fin 4} [Algebra (T i) S] [IsScalarTower ℂ (T i) S]
    (x y z w : Lift i S) (hx : LiesOver x point) (hy : LiesOver y point)
    (hz : LiesOver z point) (hw : LiesOver w point)
    (ν : Derivation ℂ (T i) S) (ω : Forms (T i) 3) :
    mixed (tangent x y hx hy) ν ω + mixed (tangent y w hy hw) ν ω =
      mixed (tangent x z hx hz) ν ω + mixed (tangent z w hz hw) ν ω := by
  exact ((mixed_add_left _ ν _ ω).symm.trans
    (congrArg (fun κ : Derivation ℂ (T i) S => mixed κ ν ω)
      ((tangent_cocycle x y w hx hy hw).symm.trans (tangent_cocycle x z w hx hz hw)))).trans
        (mixed_add_left _ ν _ ω)

/-- On a native pair, the first term is the genuine ambient test edge and
the last the edge of the alternative chart lifts. -/
theorem native_mixed_correction (i : Fin 4) (k : Fin 3)
    [Algebra (T (i.succAbove k)) S] [IsScalarTower ℂ (T (i.succAbove k)) S]
    (ρ : FixedOverlap i k →ₐ[ℂ] S) (hρ : ρ.comp (fixedTargetMap i k) = point)
    (z w : Lift (i.succAbove k) S) (hz : LiesOver z point) (hw : LiesOver w point)
    (ν : Derivation ℂ (T (i.succAbove k)) S) (ω : Forms (T (i.succAbove k)) 3) :
    let x := normalizedLift i k ρ
    let y := canonical (i.succAbove k) point
    let hx : LiesOver x point := hρ ▸ normalizedLift_fst i k ρ
    let hy : LiesOver y point := canonical_liesOver _ _
    mixed (tangent x y hx hy) ν ω + mixed (tangent y w hy hw) ν ω =
      mixed (tangent x z hx hz) ν ω + mixed (tangent z w hz hw) ν ω := by
  exact mixed_lift_correction _ _ _ _ _ _ _ _ ν ω

end CycleQ2LiteralThreefoldMixedGauge
end

#print axioms CycleQ2LiteralThreefoldMixedGauge.native_mixed_correction
