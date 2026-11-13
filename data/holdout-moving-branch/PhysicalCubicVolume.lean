import Proposal.PhysicalCubicTangent

/-! The divergence-free relative cubic direction in the physical residue
volume. This supplies the exact moving-map correction for an arbitrary
rational function, without expanding that function's covariants.
Original cycle-three construction prepared with OpenAI Codex assistance.
The transitive-cubic adaptation is due to fqlx. Adapted here to holdout-moving-branch for benediamond with OpenAI Codex assistance. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
namespace CyclePhysicalCubicVolume
open HoldoutConstruction CyclePhysical CyclePhysicalCoordinates
open CyclePhysicalNormalTransport CyclePhysicalCubicTangent
open scoped BigOperators
local instance : Algebra ℤ FunctionField := Ring.toIntAlgebra _
local notation "p" => coordinate

@[simp] lemma derivation_numeral {K : Type*} [CommRing K]
    (D : Derivation ℤ K K) (n : ℕ) [n.AtLeastTwo] :
    D (ofNat(n) : K)=0 := D.map_natCast n

lemma tangent_gradient_all (i : Fin 5) (j : Fin 6) :
    tangent i (gradient j)=hessian i.succ j-gradient i.succ/gradient 0*hessian 0 j :=
  tangent_apply i _

def weight : FunctionField := p 3^3/(4*p 0^5*p 1^2*p 2^2)
def volumeVector : Fin 5 → FunctionField :=
  ![weight*pairedGradient*p 1,0,-weight*secondPairedGradient*p 3,
    weight*pairedGradient*p 4,0]

theorem volume_divergence : residueDivergence tangent (gradient 0) volumeVector=0 := by
  have h0 := coordinate_ne_zero 0
  have h1 := coordinate_ne_zero 1
  have h2 := coordinate_ne_zero 2
  have hn : gradient 0≠0 := normal_ne_zero
  simp only [residueDivergence,fieldDivergence,volumeVector,
    Fin.sum_univ_succ,Matrix.cons_val_zero,Matrix.cons_val_succ,Fin.reduceSucc,
    Finset.univ_eq_empty,Finset.sum_empty,map_zero,zero_mul,zero_div,add_zero,
    weight,pairedGradient,secondPairedGradient,Derivation.leibniz_div,
    Derivation.leibniz_pow,Derivation.leibniz,map_add,map_neg,
    smul_eq_mul,nsmul_eq_mul,derivation_numeral,tangent_coordinate,tangent_gradient_all]
  norm_num [Fin.ext_iff]
  simp only [hessian_commute 1 0,hessian_commute 3 0,hessian_commute 4 0,
    hessian_commute 3 1,hessian_commute 4 1,hessian_commute 4 3]
  field_simp
  ring

theorem volume_vector_identity (i : Fin 5) :
    volumeVector i=ratio^3*cubicNormal*velocity i.succ := by
  have h0 := coordinate_ne_zero 0
  have h1 := coordinate_ne_zero 1
  have h2 := coordinate_ne_zero 2
  have hr := radial_ne_zero
  have hx : x≠0 := div_ne_zero (pow_ne_zero _ h0) hr
  have hy := y_ne_zero
  have hh := paired_gradient_ne_zero
  have hg : cubicNormal=pairedGradient/(2*radial^3*x) := by
    apply (eq_div_iff (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hr)) hx)).2
    linear_combination -paired_gradient_identity
  rw [hg]
  fin_cases i <;>
    norm_num [volumeVector,velocity,Matrix.cons_val_two,Matrix.cons_val_three,
      Matrix.cons_val_four,Matrix.head_cons,Matrix.tail_cons,weight,ratio,radial,x,y] <;>
    field_simp <;> ring

lemma volume_direction (z : FunctionField) :
    (∑ i, volumeVector i*tangent i z)=ratio^3*cubicNormal*derivative z := by
  simp only [volume_vector_identity,Fin.sum_univ_succ,velocity,
    Matrix.cons_val_zero,Matrix.cons_val_succ,Fin.reduceSucc,
    Finset.univ_eq_empty,Finset.sum_empty,zero_mul,mul_zero,add_zero,
    derivative,Derivation.add_apply,Derivation.smul_apply,smul_eq_mul]
  norm_num [velocity,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
    Matrix.head_cons,Matrix.tail_cons]
  ring

theorem correction_divergence (z : FunctionField) :
    residueDivergence tangent (gradient 0) (fun i => (z/3)*volumeVector i)=
      ratio^3*cubicNormal/3*derivative z := by
  rw [residueDivergence_smul,volume_divergence,mul_zero,zero_add]
  have hd (i : Fin 5) : tangent i (z/3)=tangent i z/3 := by
    rw [Derivation.leibniz_div]
    simp [smul_eq_mul]
    ring
  simp only [hd,← mul_div_assoc,← Finset.sum_div]
  rw [volume_direction]
  ring
end CyclePhysicalCubicVolume
#print axioms CyclePhysicalCubicVolume.volume_divergence
#print axioms CyclePhysicalCubicVolume.correction_divergence
