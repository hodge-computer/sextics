import Proposal.CurrentCorrection
import Proposal.Normalization

/-! The saved normal-gauge construction, now attached to concrete current data.
The comparison error is retained. No archived source identity is assumed. -/
noncomputable section
namespace CycleQ2Concrete
open MvPolynomial HodgeTestbed HodgeComputer HodgeComputer.RadialNormalization

 def baseB : Poly := divergenceNumerator baseD baseN
 def normalK : Poly := baseB + F * baseR - F ^ 2 * baseQ
 def normalD : Poly := baseD ^ 2
 def normalN (i : Fin 6) : Poly := baseD * baseN i + radial 6 2 (-normalK) i
 def normalR : Poly := baseD ^ 2 * baseR
 def normalQ : Poly := baseD ^ 2 * baseQ

lemma h_base_divergence : (divergence baseN).IsHomogeneous 3732 := by
  unfold divergence
  apply IsHomogeneous.sum
  intro i _
  exact (h_baseN i).pderiv

lemma h_base_directional_D : (directional baseD baseN).IsHomogeneous 7458 := by
  unfold directional
  apply IsHomogeneous.sum
  intro i _
  exact h_baseD.pderiv.mul (h_baseN i)

lemma h_baseB : baseB.IsHomogeneous 7458 := by
  exact (h_baseD.mul h_base_divergence).sub h_base_directional_D

lemma h_normalK : normalK.IsHomogeneous 7458 := by
  exact (h_baseB.add (CycleQ2Workspace.originalF_homogeneous.mul h_baseR)).sub
    ((CycleQ2Workspace.originalF_homogeneous.pow 2).mul h_baseQ)

lemma h_normalD : normalD.IsHomogeneous 7452 := h_baseD.pow 2

lemma h_normalN (i : Fin 6) : (normalN i).IsHomogeneous 7459 := by
  have hr : (radial 6 2 (-normalK) i).IsHomogeneous 7459 := by
    exact (h_normalK.neg.C_mul (1 / 12 : ℂ)).mul (isHomogeneous_X ℂ i)
  exact (h_baseD.mul (h_baseN i)).add hr

lemma h_normalR : normalR.IsHomogeneous 14904 := (h_baseD.pow 2).mul h_baseR
lemma h_normalQ : normalQ.IsHomogeneous 14898 := (h_baseD.pow 2).mul h_baseQ

private lemma twelve_inverse : (12 : Poly) * C (1 / 12 : ℂ) = 1 := by
  calc
    _ = C (12 : ℂ) * C (1 / 12 : ℂ) := by rw [_root_.map_ofNat]
    _ = C ((12 : ℂ) * (1 / 12)) := by rw [map_mul]
    _ = 1 := by norm_num

/-- Its first-normal error is EXACTLY minus the retained transport error. -/
theorem normal_first_error :
    2 * directional F normalN - A * normalD = -transportError := by
  have he : transportError =
      A * baseD ^ 2 - 2 * baseD * directional F baseN + F * normalK := by
    unfold transportError literalDefect HodgeComputer.defect normalK baseB
    ring
  rw [he]
  unfold normalN normalD
  rw [HodgeComputer.directional_add, HodgeTestbed.directional_mul,
    directional_radial, euler_of_homogeneous CycleQ2Workspace.originalF_homogeneous]
  norm_num only [map_natCast, map_ofNat, Nat.cast_ofNat, Nat.reduceMul]
  linear_combination -(F * normalK) * twelve_inverse

/-- The divergence calculation retains every derivative of the old denominator
and of K. The homogeneity proofs above supply the two Euler identities. -/
theorem normal_divergence_identity :
    divergenceNumerator normalD normalN = -F * normalR + F ^ 2 * normalQ := by
  have hs : divergenceNumerator normalD (fun i => baseD * baseN i) =
      baseD ^ 2 * baseB := by
    simpa only [normalD, pow_two, baseB] using
      HodgeTestbed.divergenceNumerator_mul baseD baseD baseN
  have hr : divergenceNumerator normalD (radial 6 2 (-normalK)) = -normalD * normalK := by
    rw [divergenceNumerator_radial,
      euler_of_homogeneous h_normalK.neg, euler_of_homogeneous h_normalD]
    norm_num only [map_natCast, map_ofNat, Nat.cast_ofNat, Nat.reduceMul]
    linear_combination -(normalD * normalK) * twelve_inverse
  unfold normalN
  rw [HodgeComputer.divergenceNumerator_add, hs, hr]
  unfold normalK normalD normalR normalQ
  ring

/-- This identity is valid before proving transportError=0; the error is not dropped. -/
theorem normal_defect_with_transport_error :
    defect F A normalD 2 normalN =
      normalD * transportError - F ^ 2 * normalR + F ^ 3 * normalQ := by
  unfold defect
  rw [normal_divergence_identity]
  linear_combination -normalD * normal_first_error

/-- The usual normalized partial current follows only from the explicit source proof. -/
theorem normal_first_of_transport_verified (h : ArchivedPartialIdentityGoal) :
    2 * directional F normalN = A * normalD := by
  change transportError = 0 at h
  have hn := normal_first_error
  rw [h, neg_zero] at hn
  exact sub_eq_zero.mp hn

#print axioms normal_first_error
#print axioms normal_divergence_identity
#print axioms normal_defect_with_transport_error
end CycleQ2Concrete
