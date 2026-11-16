import Proposal.PhysicalCoordinates

/-! Concrete coefficient and normal nonvanishing on the fixed mixed-polar
function field. The exact Gaussian point is used only for polynomial
evaluation followed by the proved kernel (F), never for arbitrary fractions.
The point adapts the accepted cyclic/mixed-biweight chart of
hodgepodgeconjecture and fqlx. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace MixedPolarPhysicalCoordinates
open MixedPolarPhysical
local notation "p" => coordinate
local notation "X" => (MvPolynomial.X : Fin 6 → Ambient)

def testPoint (i : Fin 6) : ℂ :=
  if i=0 then 2 else if i=1 then 2*Complex.I else
    if i=2 then 1-Complex.I else if i=3 then 1+Complex.I else 0
def pointValue : Ambient →+* ℂ := MvPolynomial.eval₂Hom (RingHom.id ℂ) testPoint

lemma testPoint_denominators_nonzero : ∀ i : Fin 4,testPoint i.castSucc.castSucc ≠ 0 := by
  intro i
  fin_cases i <;> simp [testPoint]
  all_goals intro h; have hh := congrArg Complex.re h; norm_num at hh

lemma point_on_sextic : pointValue sextic=0 := by
  simp [pointValue,sextic,testPoint]
  apply Complex.ext <;> norm_num [pow_succ,Complex.mul_re,Complex.mul_im]

lemma residue_ne_zero_of_point (P : Ambient) (hP : pointValue P≠0) : residueMap P≠0 := by
  intro hz
  obtain ⟨Q,hQ⟩ := (residueMap_kernel P).mp hz
  apply hP
  rw [hQ,map_mul,point_on_sextic,zero_mul]

lemma cOne_ne_zero : cOne≠0 :=
  div_ne_zero (div_ne_zero (coordinate_ne_zero 4) (coordinate_ne_zero 1)) ratio_ne_zero
lemma cTwo_ne_zero : cTwo≠0 :=
  div_ne_zero (div_ne_zero (coordinate_ne_zero 5) (coordinate_ne_zero 2)) ratio_ne_zero

def aNumerator : Ambient := X 0^6+X 3^6
lemma aNumerator_ne_zero : residueMap aNumerator≠0 := by
  apply residue_ne_zero_of_point
  intro hz
  have h:=congrArg Complex.re hz
  norm_num [pointValue,aNumerator,testPoint,pow_succ,Complex.mul_re,Complex.mul_im,Fin.ext_iff] at h

lemma coeffA_ne_zero : coeffA≠0 := by
  have he : coeffA=residueMap aNumerator/(p 0)^6 := by
    have h0 := coordinate_ne_zero 0
    simp only [coeffA,t,ratio,aNumerator,map_add,map_pow,coordinate_X]
    field_simp
  rw [he]
  exact div_ne_zero aNumerator_ne_zero (pow_ne_zero _ (coordinate_ne_zero 0))

def discriminantFactorNumerator : Ambient :=
  X 1*X 3*X 0^5-4*X 4*X 0^6-4*X 4*X 3^6
lemma discriminantFactorNumerator_ne_zero : residueMap discriminantFactorNumerator≠0 := by
  apply residue_ne_zero_of_point
  intro hz
  have h:=congrArg Complex.re hz
  norm_num [pointValue,discriminantFactorNumerator,testPoint,pow_succ,
    Complex.mul_re,Complex.mul_im,Fin.ext_iff] at h

lemma discriminant_factor_identity :
    (1/4:FunctionField)-cOne*coeffA=
      residueMap discriminantFactorNumerator/(4*p 1*p 3*p 0^5) := by
  have h0 := coordinate_ne_zero 0
  have h1 := coordinate_ne_zero 1
  have h3 := coordinate_ne_zero 3
  simp only [discriminantFactorNumerator,map_sub,map_mul,map_pow,map_ofNat,
    coordinate_X,cOne,coeffA,t,ratio]
  field_simp
  ring

lemma discriminant_factor_ne_zero : (1/4:FunctionField)-cOne*coeffA≠0 := by
  rw [discriminant_factor_identity]
  exact div_ne_zero discriminantFactorNumerator_ne_zero
    (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (coordinate_ne_zero 1))
      (coordinate_ne_zero 3)) (pow_ne_zero _ (coordinate_ne_zero 0)))

lemma discriminant_identity :
    coeffD^2-3*coeffA*coeffF=ratio^4*cOne^2*((1/4:FunctionField)-cOne*coeffA) := by
  unfold coeffD coeffF
  field_simp
  ring

lemma discriminant_ne_zero : coeffD^2-3*coeffA*coeffF≠0 := by
  rw [discriminant_identity]
  exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ ratio_ne_zero)
    (pow_ne_zero _ cOne_ne_zero)) discriminant_factor_ne_zero

lemma paired_gradient_ne_zero : pairedGradient≠0 := by
  have hp : residueMap (X 0*MvPolynomial.pderiv 0 sextic+
      X 3*MvPolynomial.pderiv 3 sextic)≠0 := by
    apply residue_ne_zero_of_point
    intro hz
    have h:=congrArg Complex.re hz
    norm_num [pointValue,sextic,testPoint,MvPolynomial.pderiv_mul,
      MvPolynomial.pderiv_pow,MvPolynomial.pderiv_X,MvPolynomial.pderiv_C,
      Pi.single_apply,pow_succ,Complex.mul_re,Complex.mul_im,Fin.ext_iff] at h
  simpa only [map_add,map_mul,coordinate_X,pairedGradient,gradient] using hp

lemma cubic_normal_ne_zero : cubicNormal≠0 := by
  intro hz
  have h:=paired_gradient_identity
  rw [hz,mul_zero] at h
  exact paired_gradient_ne_zero h

end MixedPolarPhysicalCoordinates
#print axioms MixedPolarPhysicalCoordinates.coeffA_ne_zero
#print axioms MixedPolarPhysicalCoordinates.discriminant_ne_zero
#print axioms MixedPolarPhysicalCoordinates.cubic_normal_ne_zero
