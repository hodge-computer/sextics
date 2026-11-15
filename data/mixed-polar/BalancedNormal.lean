import HodgeComputer.Constructions.ResidueTransport.MovingMap
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! Balanced xyz-source normal correction for the mixed-polar target.
The passive factor is X1*X2*Y1*Y2.  This changes the accepted central
x³-source's paired-normal factor 7 to 3.  Prepared independently from the
fixed mixed-polar target; no certificate is asserted by this file alone. -/
noncomputable section
namespace MixedPolarBalanced
open HoldoutConstruction
open scoped BigOperators

section Normal
variable {K : Type*} [Field K] [CharZero K]

/-- Exact X0-normal to paired-sign normal correction for A=k*p*q.
The formal physical application uses p=X0, q=Y0, k=X1*X2*Y1*Y2. -/
theorem paired_normal_change_balanced (D : Derivation ℤ K K)
    (k p q f g fpp fpq fqq : K)
    (hf : f ≠ 0) (hh : p*f+q*g ≠ 0)
    (Dk : D k = 0) (Dp : D p = -g/f) (Dq : D q = 1)
    (Df : D f = fpq-g/f*fpp) (Dg : D g = fqq-g/f*fpq) :
    k*q/f-k*p*q*fpp/f^2 =
      k*p*q*(3*(p*f+q*g)-(p^2*fpp+2*p*q*fpq+q^2*fqq))/(p*f+q*g)^2+
      (D (-k*p*q^2/(p*f+q*g))-
        (-k*p*q^2/(p*f+q*g))*D f/f) := by
  simp only [Derivation.leibniz_div, Derivation.leibniz, Derivation.leibniz_pow,
    map_neg, map_add, smul_eq_mul, nsmul_eq_mul, Dk, Dp, Dq, Df, Dg]
  norm_num
  have hsq : q*f*p*g*2+q^2*g^2+f^2*p^2 ≠ 0 := by
    convert pow_ne_zero 2 hh using 1 <;> ring
  field_simp [hf, hh]
  ring_nf
  have hinv : (q*f*p*g*2+q^2*g^2+f^2*p^2)*
      (q*f*p*g*2+q^2*g^2+f^2*p^2)⁻¹ = 1 := mul_inv_cancel₀ hsq
  linear_combination -(k*q*f-k*q*p*fpp)*hinv

/-- The paired-normal scalar after the exact physical gradient/Hessian
identities and A=L*R³*x*y.  Here g=Ux and h=Uxx. -/
theorem paired_source_is_xyz_jet (L R x y g h : K)
    (hR : R ≠ 0) (hx : x ≠ 0) (hg : g ≠ 0) :
    (L*R^3*x*y)*
        (3*(2*R^3*x*g)-(2*R^3*x*g+4*R^3*x^2*h))/(2*R^3*x*g)^2 =
      L*(y-x*y*h/g)/g := by
  field_simp
  ring

end Normal

section Volume
variable {K ι : Type*} [Field K] [Fintype ι]

/-- Scaling a residue vector by a passive scalar creates no extra term
provided that scalar is constant along the vector's actual direction. -/
theorem residueDivergence_scale_passive
    (Ds : ι → Derivation ℤ K K) (g c : K) (w : ι → K)
    (hc : ∑ i, w i * Ds i c = 0) :
    residueDivergence Ds g (fun i => c*w i) =
      c*residueDivergence Ds g w := by
  simp only [residueDivergence, fieldDivergence, Derivation.leibniz,
    smul_eq_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
  rw [hc]
  ring

/-- A source-specific moving-map vector can be obtained from the accepted
volume direction by the passive scalar c1*c2. -/
theorem balanced_volume_direction
    (Ds : ι → Derivation ℤ K K) (D : Derivation ℤ K K)
    (density g L c : K) (w : ι → K)
    (hdiv : residueDivergence Ds density w = 0)
    (hdir : ∀ z, ∑ i, w i * Ds i z = L*g*D z)
    (hc : D c = 0) :
    residueDivergence Ds density (fun i => c*w i) = 0 ∧
      ∀ z, ∑ i, (c*w i) * Ds i z = (c*L)*g*D z := by
  constructor
  · rw [residueDivergence_scale_passive Ds density c w]
    · rw [hdiv, mul_zero]
    · rw [hdir, hc, mul_zero]
  · intro z
    simp only [mul_assoc, ← Finset.mul_sum]
    rw [hdir]
    ring

end Volume

section Assembly
variable {K ι : Type*} [Field K] [Fintype ι]

lemma residueDivergence_sub (Ds : ι → Derivation ℤ K K)
    (g : K) (v w : ι → K) :
    residueDivergence Ds g (v-w) =
      residueDivergence Ds g v-residueDivergence Ds g w := by
  simp only [residueDivergence, fieldDivergence, Pi.sub_apply, map_sub,
    sub_mul, Finset.sum_sub_distrib]
  ring

/-- Formal closure of the balanced physical source once the Jacobian
primitive, moving-map jet, and actual normal-chart identities are supplied.
No parameter derivative on the specialized field is postulated. -/
theorem residue_solution_of_balanced_transport
    (Ds : ι → Derivation ℤ K K) (D : Derivation ℤ K K)
    (density normal L g η ξ adot bdot gdot ξdot : K)
    (jacobian moving correction : ι → K)
    (hnormal : normal = L*(gdot/g) + residueDivergence Ds density correction)
    (hjacobian : residueDivergence Ds density jacobian =
      -L*(adot*ξ+bdot)/(2*η^2))
    (hmoving : residueDivergence Ds density moving =
      L*g/3*D (ξdot/(2*η)))
    (hjet : gdot/g = (adot*ξ+bdot)/(2*η^2)-
      (g/3)*D (ξdot/(2*η))) :
    ∃ w : ι → K, residueDivergence Ds density w = -normal := by
  refine ⟨jacobian+moving-correction, ?_⟩
  rw [residueDivergence_sub, residueDivergence_add,
    hjacobian, hmoving, hnormal, hjet]
  ring

end Assembly
end MixedPolarBalanced
#print axioms MixedPolarBalanced.paired_normal_change_balanced
#print axioms MixedPolarBalanced.paired_source_is_xyz_jet
#print axioms MixedPolarBalanced.balanced_volume_direction
#print axioms MixedPolarBalanced.residue_solution_of_balanced_transport
