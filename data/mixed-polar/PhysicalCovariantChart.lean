import Proposal.PhysicalChart
import Proposal.ResultantSpecialization
import HodgeComputer.Constructions.TransitiveCubic.Functorial
import HodgeComputer.Constructions.TransitiveCubic.Diagonal
import Mathlib.Tactic.ComputeDegree

/-! Nonvanishing of the sheared covariants. A resultant transfers the
diagonal specialization through either quadratic shear root, using only the
explicit localization chart. The quadratic polynomial need not be
irreducible over the physical function field. Prepared with Codex assistance. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace MixedPolarPhysicalCovariantChart
open Polynomial MixedPolarPhysical MixedPolarPhysicalChart TransitiveCovariants

def shearEquation : Polynomial Chart := 3*C a*X^2+2*C d*X+C f
def shearedB : Polynomial Chart := C b+C a*X^3+C d*X^2+C f*X
def shearedD : Polynomial Chart := C d+3*C a*X
def shearedX : Polynomial Chart := C x-X*C y
def hPolynomial : Polynomial Chart :=
  H (C a) shearedB (C c) shearedD (C e) 0 shearedX (C y) 1
def jPolynomial : Polynomial Chart :=
  J (C a) shearedB (C c) shearedD (C e) 0 shearedX (C y) 1

lemma shearEquation_degree : shearEquation.natDegree≤2 := by
  unfold shearEquation
  compute_degree

lemma shearEquation_point :
    shearEquation.map toPoint=C (3*(1-Complex.I/8))*X^2 := by
  obtain ⟨ha,hb,hc,hd,he,hf,hx,hy⟩ := point_values
  simp [shearEquation,ha,hd,hf,Polynomial.C_ofNat]

lemma leading_point_ne_zero : (3*(1-Complex.I/8):ℂ)≠0 := by
  intro h
  have := congrArg Complex.re h
  norm_num at this

lemma hPolynomial_point_ne_zero : hPolynomial.eval₂ toPoint 0≠0 := by
  obtain ⟨ha,hb,hc,hd,he,hf,hx,hy⟩ := point_values
  change (eval₂RingHom toPoint 0) hPolynomial≠0
  simp only [hPolynomial,map_H,shearedB,shearedD,shearedX,map_add,map_mul,
    map_pow,map_sub,map_zero,map_one,map_ofNat,coe_eval₂RingHom,eval₂_C,eval₂_X,eval₂_natCast,eval₂_ofNat,
    zero_pow (by decide : (2:ℕ)≠0),zero_pow (by decide : (3:ℕ)≠0),
    mul_zero,zero_mul,add_zero,sub_zero,ha,hb,hc,hd,he,hf,hx,hy]
  rw [H_diagonal]
  intro h
  have := congrArg Complex.re h
  norm_num [Complex.mul_re,Complex.mul_im] at this

lemma jPolynomial_point_ne_zero : jPolynomial.eval₂ toPoint 0≠0 := by
  obtain ⟨ha,hb,hc,hd,he,hf,hx,hy⟩ := point_values
  change (eval₂RingHom toPoint 0) jPolynomial≠0
  simp only [jPolynomial,map_J,shearedB,shearedD,shearedX,map_add,map_mul,
    map_pow,map_sub,map_zero,map_one,map_ofNat,coe_eval₂RingHom,eval₂_C,eval₂_X,eval₂_natCast,eval₂_ofNat,
    zero_pow (by decide : (2:ℕ)≠0),zero_pow (by decide : (3:ℕ)≠0),
    mul_zero,zero_mul,add_zero,sub_zero,ha,hb,hc,hd,he,hf,hx,hy]
  rw [J_diagonal]
  intro h
  have := congrArg Complex.re h
  norm_num [pow_succ,Complex.mul_re,Complex.mul_im] at this

section Extension
variable {L : Type*} [Field L] [Algebra FunctionField L]
local notation "ι" => algebraMap FunctionField L
def chartToExtension : Chart →+* L := (algebraMap FunctionField L).comp toField

lemma specialization_kernel (z : Chart) (hz : chartToExtension (L:=L) z=0) :
    toPoint z=0 := by
  by_contra hp
  apply nonzero_of_point z hp
  apply (algebraMap FunctionField L).injective
  simpa only [chartToExtension,RingHom.comp_apply,map_zero] using hz

lemma shearEquation_root (k : L)
    (hk : 3*ι MixedPolarPhysicalCoordinates.coeffA*k^2+
      2*ι MixedPolarPhysicalCoordinates.coeffD*k+ι MixedPolarPhysicalCoordinates.coeffF=0) :
    shearEquation.eval₂ chartToExtension k=0 := by
  obtain ⟨ha,hb,hc,hd,he,hf,hx,hy⟩ := field_values
  simpa only [shearEquation,chartToExtension,eval₂_add,eval₂_mul,eval₂_pow,
    coe_eval₂RingHom,eval₂_C,eval₂_X,eval₂_natCast,eval₂_ofNat,RingHom.comp_apply,map_ofNat,ha,hd,hf] using hk

theorem hPolynomial_nonzero (k : L)
    (hk : 3*ι MixedPolarPhysicalCoordinates.coeffA*k^2+
      2*ι MixedPolarPhysicalCoordinates.coeffD*k+ι MixedPolarPhysicalCoordinates.coeffF=0) :
    hPolynomial.eval₂ chartToExtension k≠0 :=
  MixedPolarResultant.eval_ne_zero_of_double_root_specialization
    chartToExtension toPoint specialization_kernel shearEquation hPolynomial k
    (3*(1-Complex.I/8)) shearEquation_degree (shearEquation_root k hk)
    shearEquation_point leading_point_ne_zero hPolynomial_point_ne_zero

theorem jPolynomial_nonzero (k : L)
    (hk : 3*ι MixedPolarPhysicalCoordinates.coeffA*k^2+
      2*ι MixedPolarPhysicalCoordinates.coeffD*k+ι MixedPolarPhysicalCoordinates.coeffF=0) :
    jPolynomial.eval₂ chartToExtension k≠0 :=
  MixedPolarResultant.eval_ne_zero_of_double_root_specialization
    chartToExtension toPoint specialization_kernel shearEquation jPolynomial k
    (3*(1-Complex.I/8)) shearEquation_degree (shearEquation_root k hk)
    shearEquation_point leading_point_ne_zero jPolynomial_point_ne_zero

theorem physical_H_nonzero (k : L)
    (hk : 3*ι MixedPolarPhysicalCoordinates.coeffA*k^2+
      2*ι MixedPolarPhysicalCoordinates.coeffD*k+ι MixedPolarPhysicalCoordinates.coeffF=0) :
    H (ι MixedPolarPhysicalCoordinates.coeffA)
      (ι MixedPolarPhysicalCoordinates.coeffB+ι MixedPolarPhysicalCoordinates.coeffA*k^3+
        ι MixedPolarPhysicalCoordinates.coeffD*k^2+ι MixedPolarPhysicalCoordinates.coeffF*k)
      (ι MixedPolarPhysicalCoordinates.coeffC)
      (ι MixedPolarPhysicalCoordinates.coeffD+3*ι MixedPolarPhysicalCoordinates.coeffA*k)
      (ι MixedPolarPhysicalCoordinates.coeffE) 0
      (ι MixedPolarPhysicalCoordinates.x-k*ι MixedPolarPhysicalCoordinates.y)
      (ι MixedPolarPhysicalCoordinates.y) 1≠0 := by
  obtain ⟨ha,hb,hc,hd,he,hf,hx,hy⟩ := field_values
  have h := hPolynomial_nonzero k hk
  change (eval₂RingHom chartToExtension k) hPolynomial≠0 at h
  simpa only [hPolynomial,map_H,shearedB,shearedD,shearedX,map_add,map_mul,
    map_pow,map_sub,map_zero,map_one,map_ofNat,coe_eval₂RingHom,eval₂_C,eval₂_X,eval₂_natCast,eval₂_ofNat,
    chartToExtension,RingHom.comp_apply,ha,hb,hc,hd,he,hf,hx,hy] using h

theorem physical_J_nonzero (k : L)
    (hk : 3*ι MixedPolarPhysicalCoordinates.coeffA*k^2+
      2*ι MixedPolarPhysicalCoordinates.coeffD*k+ι MixedPolarPhysicalCoordinates.coeffF=0) :
    J (ι MixedPolarPhysicalCoordinates.coeffA)
      (ι MixedPolarPhysicalCoordinates.coeffB+ι MixedPolarPhysicalCoordinates.coeffA*k^3+
        ι MixedPolarPhysicalCoordinates.coeffD*k^2+ι MixedPolarPhysicalCoordinates.coeffF*k)
      (ι MixedPolarPhysicalCoordinates.coeffC)
      (ι MixedPolarPhysicalCoordinates.coeffD+3*ι MixedPolarPhysicalCoordinates.coeffA*k)
      (ι MixedPolarPhysicalCoordinates.coeffE) 0
      (ι MixedPolarPhysicalCoordinates.x-k*ι MixedPolarPhysicalCoordinates.y)
      (ι MixedPolarPhysicalCoordinates.y) 1≠0 := by
  obtain ⟨ha,hb,hc,hd,he,hf,hx,hy⟩ := field_values
  have h := jPolynomial_nonzero k hk
  change (eval₂RingHom chartToExtension k) jPolynomial≠0 at h
  simpa only [jPolynomial,map_J,shearedB,shearedD,shearedX,map_add,map_mul,
    map_pow,map_sub,map_zero,map_one,map_ofNat,coe_eval₂RingHom,eval₂_C,eval₂_X,eval₂_natCast,eval₂_ofNat,
    chartToExtension,RingHom.comp_apply,ha,hb,hc,hd,he,hf,hx,hy] using h

end Extension
end MixedPolarPhysicalCovariantChart
#print axioms MixedPolarPhysicalCovariantChart.hPolynomial_nonzero
#print axioms MixedPolarPhysicalCovariantChart.jPolynomial_nonzero
#print axioms MixedPolarPhysicalCovariantChart.physical_H_nonzero
#print axioms MixedPolarPhysicalCovariantChart.physical_J_nonzero
