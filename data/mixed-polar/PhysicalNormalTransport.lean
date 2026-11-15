import Proposal.PhysicalCoordinates
import Proposal.BalancedNormal

/-! The balanced source on the exact mixed-polar sextic, transported from
the X0 normal to the paired radial normal. The correction uses the shared
residue-divergence construction of fqlx and collaborators. Prepared with
OpenAI Codex assistance. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace MixedPolarPhysicalNormalTransport
open HoldoutConstruction MixedPolarPhysical MixedPolarPhysicalCoordinates
open scoped BigOperators
local instance : Algebra ℤ FunctionField := Ring.toIntAlgebra _
local notation "p" => coordinate

def sourcePassive : FunctionField := p 1*p 2*p 4*p 5
def sourceFactor : FunctionField := cOne*cTwo*ratio^3
def cubicNormalJet : FunctionField := y-x*y*cubicSecondNormal/cubicNormal
def correction : FunctionField := -sourcePassive*p 0*p 3^2/pairedGradient
def correctionVector : Fin 5 → FunctionField := Pi.single 2 correction

lemma tangent_coordinate (i : Fin 5) (j : Fin 6) :
    tangent i (p j) = (if i.succ=j then 1 else 0)-
      gradient i.succ/gradient 0*(if (0:Fin 6)=j then 1 else 0) := by
  rw [coordinate,tangent_apply]
  simp [gradient,MvPolynomial.pderiv_X,Pi.single_apply,eq_comm]

lemma tangent_p0 : tangent 2 (p 0)= -gradient 3/gradient 0 := by
  simp [tangent_coordinate,neg_div]
lemma tangent_p3 : tangent 2 (p 3)=1 := by
  simp [tangent_coordinate]
lemma tangent_sourcePassive : tangent 2 sourcePassive=0 := by
  simp [sourcePassive,Derivation.leibniz,tangent_coordinate,smul_eq_mul]
lemma tangent_gradient (j : Fin 6) :
    tangent 2 (gradient j)=hessian 3 j-gradient 3/gradient 0*hessian 0 j :=
  tangent_apply 2 _
lemma hessian_commute (i j : Fin 6) : hessian i j=hessian j i := by
  unfold hessian
  rw [HoldoutConstruction.pderiv_commute]

lemma correction_divergence :
    residueDivergence tangent (gradient 0) correctionVector =
      tangent 2 correction-correction*tangent 2 (gradient 0)/gradient 0 := by
  classical
  simp [correctionVector,residueDivergence,fieldDivergence,Pi.single_apply,
    Finset.sum_ite_eq',apply_ite]

lemma source_value : residueMap source=sourcePassive*p 0*p 3 := by
  simp [source,sourcePassive,coordinate]
  ring
lemma source_derivative : residueMap (MvPolynomial.pderiv 0 source)=sourcePassive*p 3 := by
  norm_num [source,sourcePassive,MvPolynomial.pderiv_mul,MvPolynomial.pderiv_X,
    Pi.single_apply,coordinate_X,Fin.ext_iff]
  ring
lemma source_scaling : sourcePassive*p 0*p 3=sourceFactor*radial^3*x*y := by
  have h0 := coordinate_ne_zero 0
  have h1 := coordinate_ne_zero 1
  have h2 := coordinate_ne_zero 2
  have h3 := coordinate_ne_zero 3
  simp only [sourcePassive,sourceFactor,cOne,cTwo,ratio,radial,x,y]
  field_simp

/-- The exact target source, with its normal-chart correction retained. -/
theorem physical_source_transport (hg : cubicNormal≠0) :
    residueMap (MvPolynomial.pderiv 0 source)/gradient 0-
      residueMap source*hessian 0 0/(gradient 0)^2 =
      sourceFactor*cubicNormalJet/cubicNormal+
        residueDivergence tangent (gradient 0) correctionVector := by
  have hn : gradient 0≠0 := normal_ne_zero
  have hr := radial_ne_zero
  have hx : x≠0 := div_ne_zero (pow_ne_zero _ (coordinate_ne_zero 0)) hr
  have hh : pairedGradient≠0 := by
    rw [paired_gradient_identity]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num)
      (pow_ne_zero _ hr)) hx) hg
  have hp := MixedPolarBalanced.paired_normal_change_balanced (tangent 2)
    sourcePassive (p 0) (p 3) (gradient 0) (gradient 3)
    (hessian 0 0) (hessian 0 3) (hessian 3 3) hn hh
    tangent_sourcePassive tangent_p0 tangent_p3
    (by rw [tangent_gradient,hessian_commute 3 0]) (tangent_gradient 3)
  rw [source_value,source_derivative,correction_divergence]
  change _ = _+(tangent 2 (-sourcePassive*p 0*p 3^2/pairedGradient)-
    (-sourcePassive*p 0*p 3^2/pairedGradient)*tangent 2 (gradient 0)/gradient 0)
  change _ = sourcePassive*p 0*p 3*(3*pairedGradient-pairedHessian)/pairedGradient^2+_ at hp
  rw [hp]
  congr 1
  have hs := paired_hessian_identity
  rw [paired_gradient_identity] at hs ⊢
  rw [source_scaling,sub_eq_iff_eq_add.mp hs]
  simpa only [cubicNormalJet,add_comm] using
    MixedPolarBalanced.paired_source_is_xyz_jet sourceFactor radial x y
      cubicNormal cubicSecondNormal hr hx hg

end MixedPolarPhysicalNormalTransport
#print axioms MixedPolarPhysicalNormalTransport.physical_source_transport
