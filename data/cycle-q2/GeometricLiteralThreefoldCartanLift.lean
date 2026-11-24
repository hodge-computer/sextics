import Proposal.GeometricLiteralThreefoldCartan
import Proposal.GeometricLiteralThreefoldDeformedVolume

/-!
# Cartan's identity for two lifts of the actual incidence threefold

On a localization of a fixed chart, the subtraction of two lifts descends to
a tangent point of the fixed hypersurface. Extending it to the localization
gives a derivation. Its action on the inverse gradient gives the variation
of the normalized adjunction coefficient. This identifies the difference of
the two relative volumes with the derivative of the contracted fixed volume.

Prepared for `fqlx` with OpenAI ChatGPT assistance.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2LiteralThreefoldCartanLift

open MvPolynomial CycleQ2LiteralAbelJacobiContraction CycleQ2LiteralAbelJacobiEquations
  CycleQ2LiteralThreefoldChartLift CycleQ2LiteralThreefoldLiftDifference CycleQ2LiteralThreefoldKodairaSpencer
  CycleQ2LiteralThreefoldTangentCoordinates CycleQ2LiteralThreefoldResidueFrame
  CycleQ2LiteralThreefoldResidueMinors CycleQ2LiteralThreefoldChartVolume
  CycleQ2LiteralThreefoldCartan CycleQ2LiteralThreefoldResidueContraction

open scoped DualNumber

variable {i : Fin 4} {S : Type} [CommRing S] [Algebra ℂ S] [Algebra (T i) S]
  [IsScalarTower ℂ (T i) S]

abbrev chartPoint := IsScalarTower.toAlgHom ℂ (T i) S

variable (M : Submonoid (T i)) [IsLocalization M S] (x y : Lift i S)
  (hx : LiesOver x chartPoint) (hy : LiesOver y chartPoint)

private def baseDifference : T i →ₐ[ℂ] S[ε] :=
  tangentPoint x y (fun a => (hx a).trans (hy a).symm)

private theorem baseDifference_fst (a : T i) :
    (baseDifference x y hx hy a).fst = algebraMap (T i) S a := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  change (tangentPoint x y _ (q i p)).fst = _
  rw [tangentPoint_mk]
  exact eval_fst x chartPoint hx p

private def localDifference : S →ₐ[ℂ] S[ε] :=
  IsLocalization.liftAlgHom (M := M) (f := baseDifference x y hx hy)
    (fun a => TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr <| by
      rw [baseDifference_fst]
      exact IsLocalization.map_units S a)

private theorem localDifference_map (a : T i) :
    localDifference M x y hx hy (algebraMap (T i) S a) = baseDifference x y hx hy a :=
  IsLocalization.lift_eq _ _

private theorem localDifference_fst (a : S) :
    (localDifference M x y hx hy a).fst = a := by
  have h : (TrivSqZeroExt.fstHom ℂ S S).comp (localDifference M x y hx hy) = AlgHom.id ℂ S := by
    apply IsLocalization.algHom_ext M
    apply AlgHom.ext
    intro z
    change (localDifference M x y hx hy (algebraMap (T i) S z)).fst = algebraMap (T i) S z
    rw [localDifference_map, baseDifference_fst]
  exact AlgHom.congr_fun h a

/-- Source-minus-target tangent of two genuine lifts on the localization. -/
def localizedTangent : Derivation ℂ S S :=
  jetDerivation (localDifference M x y hx hy) (fun a => by
    rw [localDifference_fst, Algebra.algebraMap_self, RingHom.id_apply])

theorem localizedTangent_polynomial (p : P) :
    localizedTangent M x y hx hy (chartPoint (q i p)) =
      (aeval x.x p).snd - (aeval y.x p).snd := by
  change (localDifference M x y hx hy (algebraMap (T i) S (q i p))).snd = _
  rw [localDifference_map]
  change (tangentPoint x y _ (q i p)).snd = _
  rw [tangentPoint_mk]
  rfl

abbrev liftedGradient (z : Lift i S) (j : Fin 4) := CycleQ2LiteralThreefoldDeformedVolume.gradient z j
abbrev fixedGradient (j : Fin 4) : S := chartPoint (gradient i j)
abbrev ordinaryCoefficient (j : Fin 4) (h : IsUnit (fixedGradient (i := i) (S := S) j)) : S :=
  (↑h.unit⁻¹ : S) * (-1 : S)^j.val

private theorem gradient_difference (j : Fin 4) :
    (liftedGradient x j).snd - (liftedGradient y j).snd = localizedTangent M x y hx hy (fixedGradient (i := i) (S := S) j) := by
  rw [show fixedGradient (i := i) (S := S) j = chartPoint (q i (pderiv (coordIndex j) (seedF i))) from rfl,
    localizedTangent_polynomial]
  change ((aeval x.x _).snd - (0 * _ + 1 * (aeval x.x _).fst)) -
    ((aeval y.x _).snd - (0 * _ + 1 * (aeval y.x _).fst)) = _
  rw [eval_fst x chartPoint hx, eval_fst y chartPoint hy]
  simp only [zero_mul, one_mul, zero_add]
  abel

/-- The dual inverse has constant part the ordinary inverse and infinitesimal
part minus the square of that inverse times the gradient velocity. -/
def dualCoefficient (j : Fin 4) (h : IsUnit (fixedGradient (i := i) (S := S) j)) (z : Lift i S) : S[ε] :=
  ⟨ordinaryCoefficient j h, -(↑h.unit⁻¹ : S)^2 * (-1 : S)^j.val * (liftedGradient z j).snd⟩

private theorem dualCoefficient_gradient (j : Fin 4) (h : IsUnit (fixedGradient (i := i) (S := S) j))
    (z : Lift i S) (hz : LiesOver z chartPoint) :
    dualCoefficient j h z * liftedGradient z j = (-1 : S[ε])^j.val := by
  have hsign : (-1 : S[ε])^j.val = TrivSqZeroExt.inl ((-1 : S)^j.val) := by
    have he : (-1 : S[ε]) = (TrivSqZeroExt.inlHom S S) (-1) := by simp
    rw [he, ← map_pow]
    rfl
  have hinv : (↑h.unit⁻¹ : S) * fixedGradient (i := i) j = 1 := by
    simpa only [h.unit_spec] using h.unit.inv_mul
  rw [hsign]
  apply TrivSqZeroExt.ext
  · change ordinaryCoefficient j h * (liftedGradient z j).fst = (-1 : S)^j.val
    rw [CycleQ2LiteralThreefoldDeformedVolume.gradient_fst z chartPoint hz]
    change (↑h.unit⁻¹ : S) * _ * fixedGradient (i := i) (S := S) j = _
    rw [mul_right_comm, hinv, one_mul]
  · rw [DualNumber.snd_mul, CycleQ2LiteralThreefoldDeformedVolume.gradient_fst z chartPoint hz]
    change (↑h.unit⁻¹ : S) * (-1:S)^j.val * (liftedGradient z j).snd +
      (-(↑h.unit⁻¹ : S)^2 * (-1:S)^j.val * (liftedGradient z j).snd) * fixedGradient (i := i) (S := S) j = 0
    linear_combination -(↑h.unit⁻¹ : S) * (-1:S)^j.val * (liftedGradient z j).snd * hinv

private theorem dualCoefficient_difference (j : Fin 4) (h : IsUnit (fixedGradient (i := i) (S := S) j)) :
    (dualCoefficient j h x).snd - (dualCoefficient j h y).snd =
      localizedTangent M x y hx hy (ordinaryCoefficient j h) := by
  let δ := localizedTangent M x y hx hy
  have hsgn : δ ((-1:S)^j.val) = 0 := by
    have hh : (-1:S)^j.val = algebraMap ℂ S ((-1:ℂ)^j.val) := by simp
    rw [hh, Derivation.map_algebraMap]
  have hinv : δ (↑h.unit⁻¹ : S) = -(↑h.unit⁻¹ : S)^2 * δ (fixedGradient (i := i) (S := S) j) := by
    exact δ.leibniz_of_mul_eq_one (by simpa only [h.unit_spec] using h.unit.inv_mul)
  change _ = δ ((↑h.unit⁻¹ : S) * (-1:S)^j.val)
  rw [Derivation.leibniz, hsgn, smul_zero, zero_add, hinv, smul_eq_mul]
  change -(↑h.unit⁻¹ : S)^2 * (-1:S)^j.val * (liftedGradient x j).snd -
    -(↑h.unit⁻¹ : S)^2 * (-1:S)^j.val * (liftedGradient y j).snd = _
  rw [← gradient_difference M x y hx hy]
  ring

/-- The relative deformed volume is the ordinary omitted-coordinate wedge
with its genuine first-order inverse-gradient coefficient. -/
theorem volume_eq_liftedVolume (j : Fin 4) (h : IsUnit (fixedGradient (i := i) (S := S) j))
    (z : Lift i S) (hz : LiesOver z chartPoint) :
    CycleQ2LiteralThreefoldDeformedVolume.volume z chartPoint hz =
      liftedVolume (dualCoefficient j h z) (fun k => z.x (coordIndex (j.succAbove k))) := by
  have hg : IsUnit (liftedGradient z j) := TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr <| by
    rw [CycleQ2LiteralThreefoldDeformedVolume.gradient_fst z chartPoint hz]
    exact h
  apply (IsUnit.smul_left_cancel hg).mp
  rw [CycleQ2LiteralThreefoldDeformedVolume.gradient_smul_volume, liftedVolume, smul_smul,
    mul_comm (liftedGradient z j), dualCoefficient_gradient j h z hz]
  rfl

variable (j : Fin 4) (h : IsUnit (fixedGradient (i := i) (S := S) j)) (b : Module.Basis (Fin 3) S (OneForms S))
  (hb : ∀ k, b k = KaehlerDifferential.D ℂ S (chartPoint (coord i (j.succAbove k))))

include h hb

/-- First-order coefficient of the actual relative adjunction volume at one
lift. The common defining equation for the moving chart enters through
its actual deformed partial derivative. -/
theorem evaluate_deformed_volume_snd (z : Lift i S) (hz : LiesOver z chartPoint) :
    (evaluateJetVolume b (CycleQ2LiteralThreefoldDeformedVolume.volume z chartPoint hz)).snd =
      ordinaryCoefficient j h * ∑ k, coordinateDerivation b k (z.x (coordIndex (j.succAbove k))).snd +
      (-(↑h.unit⁻¹ : S)^2 * (-1:S)^j.val * (liftedGradient z j).snd) := by
  rw [volume_eq_liftedVolume j h z hz]
  exact evaluate_liftedVolume_snd _ _ hb _ _ (fun k => hz _)

theorem fixedVolume_eq :
    CycleQ2ExteriorSectionNaturality.exteriorDifferentialMap chartPoint 3 (chartVolume i) =
      ordinaryCoefficient j h • orderedVolume b := by
  rw [chartVolume_eq_residue i chartPoint j h, CycleQ2LiteralThreefoldResidueMinors.residue,
    signedOmitted, ordinaryCoefficient, mul_smul]
  congr 2
  apply congrArg (exteriorPower.ιMulti S 3)
  funext k
  exact (hb k).symm

/-- The variation of the actual lifted relative top form is the exterior
derivative of the intrinsic tangent contraction on this localization. -/
theorem actual_volume_difference :
    ((evaluateJetVolume b (CycleQ2LiteralThreefoldDeformedVolume.volume x chartPoint hx)).snd -
      (evaluateJetVolume b (CycleQ2LiteralThreefoldDeformedVolume.volume y chartPoint hy)).snd) •
        orderedVolume b =
      exteriorD2 b (interior 2 (localizedTangent M x y hx hy).liftKaehlerDifferential
        (CycleQ2ExteriorSectionNaturality.exteriorDifferentialMap chartPoint 3 (chartVolume i))) := by
  rw [volume_eq_liftedVolume j h x hx, volume_eq_liftedVolume j h y hy,
    fixedVolume_eq j h b hb]
  refine (sub_smul _ _ (orderedVolume b)).trans ?_
  apply variation_difference b _ hb (localizedTangent M x y hx hy)
      (dualCoefficient j h x) (dualCoefficient j h y)
      (fun k => x.x (coordIndex (j.succAbove k))) (fun k => y.x (coordIndex (j.succAbove k)))
      rfl (fun k => hx _) (fun k => hy _) (dualCoefficient_difference M x y hx hy j h)
  intro k
  have hk := (localizedTangent_polynomial M x y hx hy (X (coordIndex (j.succAbove k)))).symm
  change (x.x (coordIndex (j.succAbove k))).snd - (y.x (coordIndex (j.succAbove k))).snd =
    localizedTangent M x y hx hy (chartPoint (q i (X (coordIndex (j.succAbove k)))))
  simpa only [aeval_X] using hk

omit h hb

/-- On each gradient chart the regularity of the presentation supplies all
localization and basis hypotheses. The two lifted points only have to reduce
to the original structural map. -/
theorem patch_actual_volume_difference (i j : Fin 4)
    (x y : Lift i (Patch i j)) (hx : LiesOver x chartPoint) (hy : LiesOver y chartPoint) :
    ((evaluateJetVolume (basis i j) (CycleQ2LiteralThreefoldDeformedVolume.volume x chartPoint hx)).snd -
      (evaluateJetVolume (basis i j) (CycleQ2LiteralThreefoldDeformedVolume.volume y chartPoint hy)).snd) •
        orderedVolume (basis i j) =
      exteriorD2 (basis i j) (interior 2
        (localizedTangent (Submonoid.powers (gradient i j)) x y hx hy).liftKaehlerDifferential
        (CycleQ2ExteriorSectionNaturality.exteriorDifferentialMap chartPoint 3 (chartVolume i))) :=
  actual_volume_difference _ x y hx hy j (IsLocalization.Away.algebraMap_isUnit (S := Patch i j) _)
    (basis i j) (basis_apply i j)

end CycleQ2LiteralThreefoldCartanLift
end

#print axioms CycleQ2LiteralThreefoldCartanLift.evaluate_deformed_volume_snd
#print axioms CycleQ2LiteralThreefoldCartanLift.actual_volume_difference

#print axioms CycleQ2LiteralThreefoldCartanLift.patch_actual_volume_difference
