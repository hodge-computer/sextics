import Proposal.GeometricLiteralThreefoldOrbitLift
import Proposal.GeometricLiteralThreefoldTriangleLifts

/-!
# Equivariance of chart normalization for the translated lifts

Normalizing the acted coordinates multiplies the old inverse coordinate
by the ratio of the chart characters. The identity on all dehomogenized
homogeneous polynomials includes the shifted weight-two coordinate.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2LiteralThreefoldOrbitLift

open MvPolynomial CycleQ2IncidenceDehomogenizedChart CycleQ2GeometricIncidenceProj
  CycleQ2LiteralAbelJacobiEquations CycleQ2LiteralAbelJacobiContraction
  CycleQ2LiteralThreefoldKodairaSpencer CycleQ2LiteralThreefoldChartLift
  CycleQ2LiteralThreefoldResidueCoordinates CycleQ2LiteralThreefoldTriangleLifts
  CycleQ2LiteralThreefoldOrbitAction CycleQ2GeometricLiteralDirection CycleQ2SeedCyclicAction

variable {S : Type*} [CommRing S] [Algebra ℂ S]

private theorem ratio_base (z : ℂ) (hz : z ^ 3 = 1) (i j : Fin 4) :
    linearScale z j i * baseScale z i = baseScale z j := by
  unfold linearScale baseScale
  field_simp [char_ne_zero z hz]

private theorem ratio_inverse (z : ℂ) (hz : z ^ 3 = 1) (i j : Fin 4) :
    linearScale z j i * linearScale z i j = 1 := by
  unfold linearScale baseScale
  field_simp [char_ne_zero z hz]

private theorem transform_linear (z : ℂ) (hz : z^3 = 1) {i : Fin 4} (x : Lift i S) (k : Fin 4) :
    linearValues i (transform z hz x).x k =
      algebraMap ℂ (Jet S) (linearScale z i k) * scaleJet z (linearValues i x.x k) := by
  rw [show linearValues i (transform z hz x).x k = aeval (transform z hz x).x (linearCoordinate (S := ℂ) i k) from
    (eval_linearCoordinate i (transform z hz x).x k).symm, transform_eval, chartPolynomialAction_linear z hz, map_mul, aeval_C, map_mul,
    AlgHom.commutes, eval_linearCoordinate]
  rfl

private theorem transform_homogeneous (z : ℂ) (hz : z^3 = 1) {i : Fin 4} (x : Lift i S)
    (p : MvPolynomial (Fin 5) ℂ) {n : ℕ} (hp : p.IsWeightedHomogeneous geometricWeight n) :
    aeval (transform z hz x).x (dehomogenize i p) =
      algebraMap ℂ (Jet S) (baseScale z i) ^ n *
        scaleJet z (aeval x.x (dehomogenize i (polynomialAction z p))) := by
  rw [transform_eval, chartPolynomialAction_homogeneous z hz i hp, map_mul, aeval_C,
    map_mul, AlgHom.commutes, map_pow]

private theorem chart_normalization_ext {j : Fin 4} {x y : Lift j S}
    (h : ∀ (k : Fin 5), aeval x.x (dehomogenize (S := ℂ) j (X (R := ℂ) k)) = aeval y.x (dehomogenize (S := ℂ) j (X (R := ℂ) k))) :
    x = y := by
  apply CycleQ2LiteralThreefoldLiftTransition.lift_ext
  funext a
  cases a with
  | some k =>
    simpa only [dehomogenize_castSucc, linearCoordinate_succAbove, aeval_X] using h (j.succAbove k).castSucc
  | none =>
    have h2 := h (2 : Fin 4).castSucc
    simp only [dehomogenize_castSucc] at h2
    have hn := h (Fin.last 4)
    simp only [dehomogenize_last, map_sub, map_pow, aeval_X] at hn
    rw [h2] at hn
    linear_combination hn

private theorem evaluatedChange (i j : Fin 4) (x : Lift i S) (t : Jet S)
    (ht : t * linearValues i x.x j = 1) (p : MvPolynomial (Fin 5) ℂ) {n : ℕ}
    (hp : p.IsWeightedHomogeneous geometricWeight n) :
    aeval (change x j t ht).x (dehomogenize j p) = t ^ n * aeval x.x (dehomogenize i p) :=
  homogeneous_change i j x.x t ht _ hp

theorem transform_normalizes (z : ℂ) (hz : z^3 = 1) {i j : Fin 4} {x : Lift i S} {y : Lift j S}
    (hxy : Normalizes x y) : Normalizes (transform z hz x) (transform z hz y) := by
  obtain ⟨u, hu, rfl⟩ := hxy
  let d := algebraMap ℂ (Jet S) (linearScale z j i)
  let v := d * scaleJet z u
  have hv : v * linearValues i (transform z hz x).x j = 1 := by
    rw [transform_linear]
    have hd : d * algebraMap ℂ (Jet S) (linearScale z i j) = 1 := by
      dsimp [d]
      rw [← map_mul, ratio_inverse z hz, map_one]
    calc
      _ = (d * algebraMap ℂ (Jet S) (linearScale z i j)) * scaleJet z (u * linearValues i x.x j) := by
        dsimp [v]
        rw [map_mul]
        ring
      _ = 1 := by rw [hu, hd, map_one, mul_one]
  refine ⟨v, hv, chart_normalization_ext (fun k => ?_)⟩
  let p := X (R := ℂ) k
  let n := geometricWeight k
  have hp : p.IsWeightedHomogeneous geometricWeight n := isWeightedHomogeneous_X ℂ geometricWeight k
  have hscale : d * algebraMap ℂ (Jet S) (baseScale z i) = algebraMap ℂ (Jet S) (baseScale z j) := by
    dsimp [d]
    rw [← map_mul, ratio_base z hz]
  rw [evaluatedChange i j (transform z hz x) v hv p hp, transform_homogeneous z hz x p hp,
    transform_homogeneous z hz (change x j u hu) p hp,
    evaluatedChange i j x u hu _ (CycleQ2LiteralOrbitAction.polynomialAction_weighted z hp),
    map_mul, map_pow, ← hscale]
  dsimp only [v]
  rw [mul_pow, mul_pow]
  ring

end CycleQ2LiteralThreefoldOrbitLift
end

#print axioms CycleQ2LiteralThreefoldOrbitLift.transform_normalizes
