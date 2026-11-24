import Proposal.GeometricLiteralThreefoldOrbitVolume
import Proposal.GeometricLiteralThreefoldOrbitActionCharts
import Proposal.GeometricLiteralThreefoldOrbitLiftJet

/-!
# The cyclic character of the ambient hypersurface residue

The chart denominators contribute six copies of their inverse character.
The homogeneous sextic and this sixth power are fixed. The product of
the diagonal coordinate characters is therefore the character of the
residue on every chart. Scaling the tangent parameter by the generator
cancels this character after contraction.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2LiteralThreefoldOrbitVolume

open MvPolynomial CycleQ2IncidenceDehomogenizedChart CycleQ2LiteralAbelJacobiMovingNormal
  CycleQ2LiteralAbelJacobiContraction CycleQ2LiteralAbelJacobiEquations
  CycleQ2LiteralThreefoldChartVolume CycleQ2LiteralThreefoldOrbitAction
  CycleQ2LiteralThreefoldChartEvaluation CycleQ2LiteralThreefoldTestEdges
  CycleQ2LiteralThreefoldLiftTransition CycleQ2LiteralThreefoldChartLift CycleQ2ThreefoldContractionAlongMap
  CycleQ2TangentPointDifferential CycleQ2ExteriorSectionNaturality
  CycleQ2LiteralThreefoldOrbitLift

theorem chart_determinant (z : ℂ) (hz : z ^ 3 = 1) (i : Fin 4) :
    baseScale z i ^ 2 * ∏ k : Fin 3, linearScale z i (i.succAbove k) = z ^ 2 := by
  have h := Fin.prod_univ_succAbove (fun j : Fin 4 => char z j.castSucc) i
  have full : ∏ j : Fin 4, char z j.castSucc = z^2 := by
    simp only [Fin.prod_univ_four, char]
    change z^2 * z^2 * z * 1 = z^2
    linear_combination z^2 * hz
  have h' : ∏ k : Fin 3, char z (i.succAbove k).castSucc =
      (∏ j : Fin 4, char z j.castSucc) * baseScale z i := by
    rw [h, baseScale, mul_right_comm, mul_inv_cancel₀ (char_ne_zero z hz _), one_mul]
  simp only [linearScale, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, h', full]
  have hs := baseScale_six z hz i
  linear_combination z^2 * hs

private theorem pderiv_none_linear (i j : Fin 4) :
    pderiv none (linearCoordinate (S := ℂ) i j) = 0 := by
  rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨k,rfl⟩
  · simp
  · simp [pderiv_X, Pi.single_apply]

theorem chartVolume_action (z : ℂ) (hz : z ^ 3 = 1) (i : Fin 4) :
    exteriorDifferentialMap (chartAction z hz i) 3 (chartVolume i) =
      algebraMap ℂ (T i) (z ^ 2) • chartVolume i := by
  rw [← chart_determinant z hz i]
  apply chartVolume_triangular i (chartPolynomialAction z i) (chartAction z hz i)
    (chartAction_mk z hz i) (chartPolynomialAction_seedF z hz i)
  · rw [chartPolynomialAction_normal, map_add, pderiv_C_mul, pderiv_C_mul, pderiv_X_self]
    simp [Derivation.leibniz_pow, pderiv_none_linear]
  · intro k
    exact (by simpa only [linearCoordinate_succAbove] using chartPolynomialAction_linear z hz i (i.succAbove k))

theorem orientedVolume_action (z : ℂ) (hz : z ^ 3 = 1) (i : Fin 4) :
    exteriorDifferentialMap (chartAction z hz i) 3 ((-1 : T i)^i.val • chartVolume i) =
      algebraMap ℂ (T i) (z ^ 2) • ((-1 : T i)^i.val • chartVolume i) := by
  rw [map_smulₛₗ, chartVolume_action]
  simp only [map_pow, map_neg, map_one]
  exact smul_comm _ _ _

variable {S : Type} [CommRing S] [Algebra ℂ S]

theorem jetValue_action (z : ℂ) (hz : z ^ 3 = 1) (i : Fin 4) (v : T i →ₐ[ℂ] Jet S) :
    jetValue i (v.comp (chartAction z hz i)) =
      algebraMap ℂ S (z ^ 2) • jetValue i v := by
  let f := (TrivSqZeroExt.fstHom ℂ S S).comp v
  change evaluate i (f.comp (chartAction z hz i)) (v.comp (chartAction z hz i)) _ =
    algebraMap ℂ S (z^2) • evaluate i f v (fun _ => rfl)
  rw [evaluate_precomp, orientedVolume_action, map_smulₛₗ]
  exact congrArg (fun c : S => c • evaluate i f v (fun _ => rfl)) (f.commutes (z^2))

private theorem along_smul {R : Type} [CommRing R] [Algebra ℂ R] (n : ℕ)
    (f : R →ₐ[ℂ] S) (u : KaehlerDifferential ℂ R →ₛₗ[f.toRingHom] S) (c : S) :
    along n f (c • u) = c • along n f u := by
  apply LinearMap.ext_on (exteriorPower.ιMulti_span R (n+1) (KaehlerDifferential ℂ R))
  rintro _ ⟨m,rfl⟩
  simp only [LinearMap.smul_apply, along_wedge, Finset.smul_sum, smul_eq_mul, mul_smul]
  exact Finset.sum_congr rfl (fun j _ => smul_comm _ _ _)

theorem jetValue_scaled (z : ℂ) (i : Fin 4) (v : T i →ₐ[ℂ] Jet S) :
    jetValue i ((scaleJet z).comp v) = algebraMap ℂ S z • jetValue i v := by
  let f := (TrivSqZeroExt.fstHom ℂ S S).comp v
  have e : covector f ((scaleJet z).comp v) (fun _ => rfl) =
      algebraMap ℂ S z • covector f v (fun _ => rfl) := by
    apply LinearMap.ext_on_range (KaehlerDifferential.span_range_derivation ℂ (T i))
    intro r
    rw [LinearMap.smul_apply, covector_D, covector_D]
    rfl
  change along 2 f (covector f _ _) _ = _
  rw [e, along_smul]
  rfl

theorem jetValue_scaled_action (z : ℂ) (hz : z ^ 3 = 1) (i : Fin 4) (v : T i →ₐ[ℂ] Jet S) :
    jetValue i ((scaleJet z).comp (v.comp (chartAction z hz i))) = jetValue i v := by
  rw [jetValue_scaled, jetValue_action, ← mul_smul, ← map_mul]
  rw [show z * z^2 = 1 from (by linear_combination hz), map_one, one_smul]

end CycleQ2LiteralThreefoldOrbitVolume
end

#print axioms CycleQ2LiteralThreefoldOrbitVolume.orientedVolume_action
#print axioms CycleQ2LiteralThreefoldOrbitVolume.jetValue_scaled_action
