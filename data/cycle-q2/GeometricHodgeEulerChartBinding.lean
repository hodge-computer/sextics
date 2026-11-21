import Proposal.GeometricHodgeThreefold
import Proposal.GeometricHodgeEuler
import Proposal.GeometricIncidenceDehomogenizedChart

/-!
# Weight-one affine charts of the invariant sextic threefold

On each of the four opens where a weight-one coordinate is invertible,
a homogeneous fraction of degree zero evaluates by setting that coordinate
to one. The inverse sends an affine coordinate of weight `w` to its
homogeneous ratio with denominator the `w`-th power of the chart coordinate.
Both maps use the single hypersurface equation and preserve coefficients.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2HodgeEulerChartBinding

open AlgebraicGeometry CategoryTheory MvPolynomial
open CycleQ2GeometricHodgeThreefold CycleQ2HodgeEuler
open CycleQ2GeometricIncidenceProj CycleQ2GenericSexticGradient

variable {R : Type} [CommRing R] (φ : CoeffRing →+* R) (i : Fin 4)

private abbrev ConeLoc := Localization.Away (coord φ i.castSucc)

private def invCoord : ConeLoc φ i := IsLocalization.Away.invSelf (coord φ i.castSucc)

def fraction (n : ℕ) (p : MvPolynomial (Fin 5) R) (hp : p.IsWeightedHomogeneous geometricWeight n) :
    ChartRing φ i :=
  HomogeneousLocalization.Away.mk (grade φ) (weightOne_mem_grade φ i)
    n (quotient φ p) (by simpa using quotient_mem_grade φ p hp)

private theorem fraction_val (n : ℕ) (p : MvPolynomial (Fin 5) R)
    (hp : p.IsWeightedHomogeneous geometricWeight n) :
    (fraction φ i n p hp).val =
      algebraMap (cone φ) (ConeLoc φ i) (quotient φ p) * invCoord φ i ^ n := by
  rw [fraction, HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk',
    IsLocalization.mk'_eq_iff_eq_mul]
  simp only [map_pow]
  rw [mul_assoc, mul_comm (invCoord φ i ^ n), ← mul_pow,
    show algebraMap (cone φ) (ConeLoc φ i) (coord φ i.castSucc) * invCoord φ i = 1 from
      IsLocalization.Away.mul_invSelf _, one_pow, mul_one]

def ratio (j : Fin 5) : ChartRing φ i :=
  fraction φ i (geometricWeight j) (X j) (isWeightedHomogeneous_X R geometricWeight j)

private theorem ratio_self : ratio φ i i.castSucc = 1 := by
  apply HomogeneousLocalization.val_injective
  have h : geometricWeight i.castSucc = 1 := by fin_cases i <;> rfl
  rw [ratio, fraction_val, h, pow_one]
  exact (IsLocalization.Away.mul_invSelf (coord φ i.castSucc)).trans
    HomogeneousLocalization.val_one.symm

private def normalize : MvPolynomial (Fin 5) R →+* ChartRing φ i :=
  eval₂Hom (chartCoefficient φ i) (ratio φ i)

private theorem normalize_homogeneous (n : ℕ) (p : MvPolynomial (Fin 5) R)
    (hp : p.IsWeightedHomogeneous geometricWeight n) : normalize φ i p = fraction φ i n p hp := by
  let _ : Algebra ℂ R := (φ.comp (C : ℂ →+* CoeffRing)).toAlgebra
  let f := (algebraMap (cone φ) (ConeLoc φ i)).comp (quotient φ)
  have heval : eval₂Hom (f.comp C) (fun j => f (X j)) = f := by
    apply MvPolynomial.ringHom_ext <;> intro x <;> simp
  have hcomp : (algebraMap (ChartRing φ i) (ConeLoc φ i)).comp (normalize φ i) =
      eval₂Hom (f.comp C) (fun j => invCoord φ i ^ geometricWeight j * f (X j)) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp only [RingHom.comp_apply, normalize, eval₂Hom_C,
        HomogeneousLocalization.algebraMap_apply, chartCoefficient_val]
      rfl
    · intro j
      simp only [RingHom.comp_apply, normalize, eval₂Hom_X',
        HomogeneousLocalization.algebraMap_apply, ratio, fraction_val]
      exact mul_comm _ _
  apply HomogeneousLocalization.val_injective
  change ((algebraMap (ChartRing φ i) (ConeLoc φ i)).comp (normalize φ i)) p = _
  rw [hcomp, CycleQ2IncidenceDehomogenizedChart.weighted_homogeneous_eval_scale
    (f.comp C) (fun j => f (X j)) (invCoord φ i) p n hp, heval, fraction_val]
  exact mul_comm _ _

private def affineEval : MvPolynomial (Fin 4) R →+* ChartRing φ i :=
  eval₂Hom (chartCoefficient φ i) (fun j => ratio φ i (i.castSucc.succAbove j))

private theorem affineEval_dehom (p : MvPolynomial (Fin 5) R) :
    affineEval φ i (dehom i p) = normalize φ i p := by
  have he : (affineEval φ i).comp (dehom (R := R) i).toRingHom = normalize φ i := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [affineEval, normalize, dehom]
    · intro j
      rcases Fin.eq_self_or_eq_succAbove i.castSucc j with rfl | ⟨a, rfl⟩
      · simp [normalize, ratio_self]
      · simp [affineEval, normalize]
  exact RingHom.congr_fun he p

private theorem normalize_equation : normalize φ i (equation φ) = 0 := by
  rw [normalize_homogeneous φ i 6 _ (equation_homogeneous φ)]
  apply HomogeneousLocalization.val_injective
  simp only [fraction_val, equation_zero, map_zero, zero_mul, HomogeneousLocalization.val_zero]

private def fromChart : chart φ i →+* ChartRing φ i :=
  Ideal.Quotient.lift _ (affineEval φ i) (fun _ h => by
    apply (show Ideal.span {F φ i} ≤ RingHom.ker (affineEval φ i) from
      Ideal.span_le.mpr (by
        rintro _ ⟨rfl⟩
        exact (affineEval_dehom φ i (equation φ)).trans (normalize_equation φ i))) h)

private def coneToChart : cone φ →+* chart φ i :=
  Ideal.Quotient.lift _ ((chartMap φ i).comp (dehom i)).toRingHom (fun _ h => by
    apply (show Ideal.span {equation φ} ≤ RingHom.ker ((chartMap φ i).comp (dehom i)).toRingHom from
      Ideal.span_le.mpr (by
        rintro _ ⟨rfl⟩
        exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _)))) h)

private theorem coneToChart_self : coneToChart φ i (coord φ i.castSucc) = 1 := by
  change chartMap φ i (dehom i (X i.castSucc)) = 1
  rw [dehom_X_self, map_one]

private def localToChart : ConeLoc φ i →+* chart φ i :=
  IsLocalization.Away.lift (coord φ i.castSucc) (show IsUnit (coneToChart φ i (coord φ i.castSucc)) by
    rw [coneToChart_self]; exact isUnit_one)

private theorem localToChart_map (a : cone φ) :
    localToChart φ i (algebraMap (cone φ) (ConeLoc φ i) a) = coneToChart φ i a :=
  IsLocalization.Away.lift_eq _ _ _

private theorem localToChart_inverse : localToChart φ i (invCoord φ i) = 1 := by
  have h := congrArg (localToChart φ i)
    (IsLocalization.Away.mul_invSelf (S := ConeLoc φ i) (coord φ i.castSucc))
  change localToChart φ i (IsLocalization.Away.invSelf (coord φ i.castSucc)) = 1
  simpa only [map_mul, localToChart_map, coneToChart_self, one_mul, map_one] using h

private def toChart : ChartRing φ i →+* chart φ i :=
  (localToChart φ i).comp (algebraMap (ChartRing φ i) (ConeLoc φ i))

private theorem toChart_fraction (n : ℕ) (p : MvPolynomial (Fin 5) R)
    (hp : p.IsWeightedHomogeneous geometricWeight n) :
    toChart φ i (fraction φ i n p hp) = chartMap φ i (dehom i p) := by
  change localToChart φ i (fraction φ i n p hp).val = _
  rw [fraction_val, map_mul, map_pow, localToChart_map, localToChart_inverse, one_pow, mul_one]
  rfl

private theorem toChart_coefficient (c : R) :
    toChart φ i (chartCoefficient φ i c) = algebraMap R (chart φ i) c := by
  change localToChart φ i (chartCoefficient φ i c).val = _
  rw [chartCoefficient_val, localToChart_map]
  change (chartMap φ i) (dehom i (C c)) = _
  simp [dehom]

def chartEquiv : ChartRing φ i ≃ₐ[R] chart φ i where
  __ := toChart φ i
  invFun := fromChart φ i
  left_inv z := by
    obtain ⟨n, a, ha, rfl⟩ := HomogeneousLocalization.Away.mk_surjective
      (grade φ) (weightOne_mem_grade φ i) z
    obtain ⟨p, hp, rfl⟩ := ha
    have hp' : p.IsWeightedHomogeneous geometricWeight n := by simpa using hp
    change fromChart φ i (toChart φ i (fraction φ i n p hp')) = fraction φ i n p hp'
    rw [toChart_fraction]
    exact (affineEval_dehom φ i p).trans (normalize_homogeneous φ i n p hp')
  right_inv z := by
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
    have he : (toChart φ i).comp (affineEval φ i) = (chartMap φ i).toRingHom := by
      apply MvPolynomial.ringHom_ext
      · intro c
        change toChart φ i (affineEval φ i (C c)) = chartMap φ i (C c)
        rw [affineEval, eval₂Hom_C, toChart_coefficient]
        exact ((chartMap φ i).commutes c).symm
      · intro a
        change toChart φ i (affineEval φ i (X a)) = chartMap φ i (X a)
        rw [affineEval, eval₂Hom_X', ratio, toChart_fraction, dehom_X_succAbove]
    exact RingHom.congr_fun he p
  commutes' := toChart_coefficient φ i

theorem chartEquiv_fraction (n : ℕ) (p : MvPolynomial (Fin 5) R)
    (hp : p.IsWeightedHomogeneous geometricWeight n) :
    chartEquiv φ i (fraction φ i n p hp) = chartMap φ i (dehom i p) :=
  toChart_fraction φ i n p hp

@[simp] theorem chartEquiv_ratio (j : Fin 5) :
    chartEquiv φ i (ratio φ i j) = chartMap φ i (dehom i (X j)) :=
  chartEquiv_fraction φ i _ _ _

@[simp] theorem chartEquiv_ratio_succAbove (j : Fin 4) :
    chartEquiv φ i (ratio φ i (i.castSucc.succAbove j)) = chartMap φ i (X j) := by
  rw [chartEquiv_ratio, dehom_X_succAbove]

/-- The homogeneous Jacobian coordinate divided by the chart coordinate to its weight. -/
def gradientRatio (j : Fin 5) : ChartRing φ i :=
  fraction φ i (6 - geometricWeight j) (pderiv j (equation φ)) <|
    (equation_homogeneous φ).pderiv (Nat.sub_add_cancel (by fin_cases j <;> decide))

theorem chartEquiv_gradientRatio (j : Fin 5) :
    chartEquiv φ i (gradientRatio φ i j) = conePartial φ i j :=
  chartEquiv_fraction φ i _ _ _

theorem chartEquiv_gradientRatio_succAbove (j : Fin 4) :
    chartEquiv φ i (gradientRatio φ i (i.castSucc.succAbove j)) =
      chartMap φ i (pderiv j (F φ i)) :=
  (chartEquiv_gradientRatio φ i _).trans (partial_succAbove φ i j)

def affineChart : (coordinateOpen φ i).toScheme ≅ Spec (CommRingCat.of (chart φ i)) :=
  coordinateChart φ i ≪≫ Scheme.Spec.mapIso (chartEquiv φ i).toRingEquiv.toCommRingCatIso.symm.op

theorem affineChart_overBase :
    (affineChart φ i).inv ≫ (coordinateOpen φ i).ι ≫ toBase φ =
      Spec.map (CommRingCat.ofHom (algebraMap R (chart φ i))) := by
  change (Spec.map (CommRingCat.ofHom (chartEquiv φ i).toRingEquiv.toRingHom) ≫
    (coordinateChart φ i).inv) ≫ (coordinateOpen φ i).ι ≫ toBase φ = _
  rw [Category.assoc, coordinateChart_overBase, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  exact RingHom.ext (fun c => (chartEquiv φ i).commutes c)

end CycleQ2HodgeEulerChartBinding
end

#print axioms CycleQ2HodgeEulerChartBinding.chartEquiv_fraction
#print axioms CycleQ2HodgeEulerChartBinding.affineChart
