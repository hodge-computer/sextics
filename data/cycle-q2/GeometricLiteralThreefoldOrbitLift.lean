import Proposal.GeometricLiteralThreefoldOrbitLiftJet
import Proposal.GeometricLiteralThreefoldOrbitActionCharts

/-!
# Cyclic translates of the native threefold deformation lifts

The affine action uses the full polynomial substitution in the shifted
weight-two coordinate. Pulling a chart lift back and then applying the
inverse substitution produces a lift over the original point.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2LiteralThreefoldOrbitLift

open MvPolynomial CycleQ2IncidenceDehomogenizedChart CycleQ2LiteralAbelJacobiEquations
  CycleQ2LiteralAbelJacobiContraction CycleQ2LiteralThreefoldKodairaSpencer
  CycleQ2LiteralThreefoldChartLift CycleQ2LiteralThreefoldLiftDifference
  CycleQ2LiteralThreefoldLiftTransition CycleQ2LiteralThreefoldTangentCoordinates
  CycleQ2LiteralThreefoldOrbitAction CycleQ2GeometricLiteralDirection

theorem square_cube (z : ℂ) (hz : z ^ 3 = 1) : (z ^ 2) ^ 3 = 1 := by
  rw [← pow_mul, Nat.mul_comm, pow_mul, hz, one_pow]

theorem action_test (z : ℂ) (hz : z^3 = 1) (i : Fin 4) :
    chartPolynomialAction z i (test i) = C z * test i := by
  rw [test, chartPolynomialAction_homogeneous z hz i test_homogeneous,
    baseScale_six z hz, map_one, one_mul]
  have he : CycleQ2SeedCyclicAction.polynomialAction z ambientTest = C z * ambientTest :=
    CycleQ2LiteralCyclicDeformation.polynomialAction_perturbation z
  rw [he, map_mul, show (dehomogenize i) (C z) = C z from aeval_C _ _]

private theorem char_square (z : ℂ) (j : Fin 5) : char (z^2) j = char z j ^ 2 := by
  fin_cases j <;> simp [char]

private theorem base_square (z : ℂ) (i : Fin 4) : baseScale (z^2) i = baseScale z i ^ 2 := by
  simp [baseScale, char_square]

private theorem linear_square (z : ℂ) (i k : Fin 4) :
    linearScale (z^2) i k = linearScale z i k ^ 2 := by
  simp [linearScale, base_square, char_square, mul_pow]

private theorem linear_cube (z : ℂ) (hz : z^3 = 1) (i k : Fin 4) :
    linearScale z i k ^ 3 = 1 := by
  rw [linearScale, mul_pow, char_cube z hz, baseScale_cube z hz, one_mul]

private theorem compose_eigen (A B : P →ₐ[ℂ] P) (p : P) (c d : ℂ)
    (hA : A p = C c * p) (hB : B p = C d * p) (h : d*c = 1) :
    A (B p) = p := by
  rw [hB, map_mul, show A (C d) = C d from A.commutes d, hA, ← mul_assoc, ← map_mul, h,
    map_one, one_mul]

private theorem raw_eigen (z : ℂ) (hz : z^3 = 1) (i : Fin 4) :
    chartPolynomialAction z i (X none - linearCoordinate i 2 ^ 2) =
      C (baseScale z i ^ 2) * (X none - linearCoordinate i 2 ^ 2) := by
  simp only [map_sub, map_pow, chartPolynomialAction_normal, chartPolynomialAction_linear z hz]
  ring

theorem chart_inverse (z : ℂ) (hz : z ^ 3 = 1) (i : Fin 4) :
    (chartAction z hz i).comp (chartAction (z^2) (square_cube z hz) i) = AlgHom.id ℂ _ := by
  let A := chartPolynomialAction z i
  let B := chartPolynomialAction (z^2) i
  have hL (j : Fin 4) : A (B (linearCoordinate i j)) = linearCoordinate i j := by
    apply compose_eigen A B _ _ _ (chartPolynomialAction_linear z hz i j)
      (chartPolynomialAction_linear (z^2) (square_cube z hz) i j)
    rw [linear_square, ← pow_succ, linear_cube z hz]
  have hN := compose_eigen A B _ _ _ (raw_eigen z hz i) (raw_eigen (z^2) (square_cube z hz) i)
    (show (baseScale (z^2) i)^2 * baseScale z i ^ 2 = 1 by
      rw [base_square, ← pow_mul, ← pow_add]
      exact baseScale_six z hz i)
  have hab : A.comp B = AlgHom.id ℂ _ := by
    apply MvPolynomial.algHom_ext
    intro j
    cases j with
    | some k =>
      simpa only [linearCoordinate_succAbove, AlgHom.comp_apply, AlgHom.id_apply] using hL (i.succAbove k)
    | none =>
      simp only [map_sub, map_pow, hL] at hN
      change A (B (X none)) = X none
      linear_combination hN
  apply AlgHom.ext
  intro t
  obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective t
  exact congrArg (q i) (AlgHom.congr_fun hab p)

variable {S U : Type*} [CommRing S] [Algebra ℂ S] [CommRing U] [Algebra ℂ U]

def transform (z : ℂ) (hz : z^3 = 1) {i : Fin 4} (x : Lift i S) : Lift i S :=
  transformBy (chartPolynomialAction z i) z (chartPolynomialAction_seedF z hz i) (action_test z hz i) x

theorem transform_eval (z : ℂ) (hz : z^3 = 1) {i : Fin 4} (x : Lift i S) (p : P) :
    aeval (transform z hz x).x p = scaleJet z (aeval x.x (chartPolynomialAction z i p)) :=
  transformBy_eval _ _ _ _ _ _

theorem transform_liesOver (z : ℂ) (hz : z^3 = 1) {i : Fin 4} {x : Lift i S} {f : T i →ₐ[ℂ] S}
    (hx : LiesOver x f) : LiesOver (transform z hz x) (f.comp (chartAction z hz i)) :=
  transformBy_liesOver _ _ _ _ _ (chartAction_mk z hz i) hx

theorem transform_fst (z : ℂ) (hz : z^3 = 1) {i : Fin 4} (x y : Lift i S)
    (h : ∀ k, (x.x k).fst = (y.x k).fst) (k : Index) :
    ((transform z hz x).x k).fst = ((transform z hz y).x k).fst :=
  transformBy_fst_eq _ _ _ _ _ _ h k

theorem tangentPoint_transform (z : ℂ) (hz : z^3 = 1) {i : Fin 4} (x y : Lift i S)
    (h : ∀ k, (x.x k).fst = (y.x k).fst) :
    tangentPoint (transform z hz x) (transform z hz y) (transform_fst z hz x y h) =
      (scaleJet z).comp ((tangentPoint x y h).comp (chartAction z hz i)) :=
  tangentPoint_transformBy _ _ _ _ _ (chartAction_mk z hz i) _ _ h

theorem mapLift_transform (z : ℂ) (hz : z^3 = 1) (b : S →ₐ[ℂ] U) {i : Fin 4} (x : Lift i S) :
    mapLift b (transform z hz x) = transform z hz (mapLift b x) :=
  mapLift_transformBy _ _ _ _ b x

def actedCanonical (z : ℂ) (hz : z^3 = 1) (i : Fin 4) : Lift i (T i) :=
  transform (z^2) (square_cube z hz) (canonical i (chartAction z hz i))

theorem actedCanonical_liesOver (z : ℂ) (hz : z^3 = 1) (i : Fin 4) :
    LiesOver (actedCanonical z hz i) (AlgHom.id ℂ _) :=
  chart_inverse z hz i ▸ transform_liesOver (z^2) (square_cube z hz) (canonical_liesOver i _)

theorem mapLift_actedCanonical (z : ℂ) (hz : z^3 = 1) (i : Fin 4) (f : T i →ₐ[ℂ] S) :
    mapLift f (actedCanonical z hz i) =
      transform (z^2) (square_cube z hz) (canonical i (f.comp (chartAction z hz i))) := by
  unfold actedCanonical
  rw [mapLift_transform, mapLift_canonical]

end CycleQ2LiteralThreefoldOrbitLift
end

#print axioms CycleQ2LiteralThreefoldOrbitLift.actedCanonical_liesOver
#print axioms CycleQ2LiteralThreefoldOrbitLift.tangentPoint_transform
