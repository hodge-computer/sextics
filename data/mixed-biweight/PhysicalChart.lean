import Proposal.JacobianModel
import Proposal.CubicPoint
import HodgeComputer.Constructions.TransitiveCubic.Functorial
import Mathlib.RingTheory.Localization.Away.Basic

/-! A localization lets an exact point certify nonvanishing of the covariants
in the physical function field. Only X0,X1,X2,Y0 are inverted. The argument
does not evaluate arbitrary rational functions at a point: it first works in
this explicitly specified open chart and uses the kernel (F).
Original cycle-three work prepared with OpenAI Codex assistance for hodgepodgeconjecture.
Adapted to mixed-biweight for fqlx with OpenAI Codex assistance. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace CyclePhysicalChart
open CyclePhysical CyclePhysicalCoordinates TransitiveCovariants
local notation "X" => (MvPolynomial.X : Fin 6 → Ambient)
def denominator : Ambient := X 0*X 1*X 2*X 3
abbrev Chart := Localization.Away denominator
def ofPolynomial : Ambient →+* Chart := algebraMap Ambient Chart
def coord (i : Fin 6) : Chart := ofPolynomial (X i)
def invDenominator : Chart := IsLocalization.Away.invSelf denominator
def inverse (i : Fin 4) : Chart :=
  if i=0 then coord 1*coord 2*coord 3*invDenominator else
  if i=1 then coord 0*coord 2*coord 3*invDenominator else
  if i=2 then coord 0*coord 1*coord 3*invDenominator else
    coord 0*coord 1*coord 2*invDenominator

lemma inverse_spec (i : Fin 4) : coord i.castSucc.castSucc*inverse i=1 := by
  have h := IsLocalization.Away.mul_invSelf (S := Chart) denominator
  change ofPolynomial denominator*invDenominator=1 at h
  simp only [denominator,map_mul] at h
  change coord 0*coord 1*coord 2*coord 3*invDenominator=1 at h
  fin_cases i
  · change coord 0*(coord 1*coord 2*coord 3*invDenominator)=1
    linear_combination h
  · change coord 1*(coord 0*coord 2*coord 3*invDenominator)=1
    linear_combination h
  · change coord 2*(coord 0*coord 1*coord 3*invDenominator)=1
    linear_combination h
  · change coord 3*(coord 0*coord 1*coord 2*invDenominator)=1
    linear_combination h

lemma denominator_residue_ne_zero : residueMap denominator ≠ 0 := by
  simpa only [denominator,map_mul,coordinate] using
    mul_ne_zero (mul_ne_zero (mul_ne_zero (coordinate_ne_zero 0)
      (coordinate_ne_zero 1)) (coordinate_ne_zero 2)) (coordinate_ne_zero 3)
lemma denominator_point_ne_zero : CycleCubicPoint.value denominator ≠ 0 := by
  have h := CycleCubicPoint.denominators_nonzero
  simpa [denominator,CycleCubicPoint.value,Matrix.cons_val,Fin.castSucc_mk] using
    mul_ne_zero (mul_ne_zero (mul_ne_zero (h 0) (h 1)) (h 2)) (h 3)

def toField : Chart →+* FunctionField := IsLocalization.Away.lift denominator
  (isUnit_iff_ne_zero.mpr denominator_residue_ne_zero)
def toPoint : Chart →+* ℂ := IsLocalization.Away.lift denominator
  (isUnit_iff_ne_zero.mpr denominator_point_ne_zero)

lemma field_polynomial (p : Ambient) : toField (ofPolynomial p)=residueMap p :=
  IsLocalization.Away.lift_eq _ _ _
lemma point_polynomial (p : Ambient) : toPoint (ofPolynomial p)=CycleCubicPoint.value p :=
  IsLocalization.Away.lift_eq _ _ _

lemma nonzero_of_point (z : Chart) (hz : toPoint z ≠ 0) : toField z ≠ 0 := by
  intro hf
  obtain ⟨n,p,hp⟩ := IsLocalization.Away.surj denominator z
  have hr := congrArg toField hp
  simp only [map_mul,map_pow,show algebraMap Ambient Chart=ofPolynomial from rfl,
    field_polynomial,hf,zero_mul] at hr
  obtain ⟨q,hq⟩ := (residueMap_kernel p).mp hr.symm
  have he : CycleCubicPoint.value p=0 := by
    rw [hq,map_mul,CycleCubicPoint.on_sextic,zero_mul]
  have ht := congrArg toPoint hp
  simp only [map_mul,map_pow,show algebraMap Ambient Chart=ofPolynomial from rfl,
    point_polynomial,he] at ht
  exact hz ((mul_eq_zero.mp ht).resolve_right (pow_ne_zero _ denominator_point_ne_zero))

lemma field_coordinate (i : Fin 6) : toField (coord i)=coordinate i := field_polynomial _
lemma point_coordinate (i : Fin 6) : toPoint (coord i)=CycleCubicPoint.point i := by
  rw [coord,point_polynomial]
  simp [CycleCubicPoint.value]
lemma field_inverse (i : Fin 4) : toField (inverse i)=(coordinate i.castSucc.castSucc)⁻¹ := by
  have h := congrArg toField (inverse_spec i)
  rw [map_mul,map_one,field_coordinate] at h
  exact eq_inv_of_mul_eq_one_right h
lemma point_inverse (i : Fin 4) : toPoint (inverse i)=(CycleCubicPoint.point i.castSucc.castSucc)⁻¹ := by
  have h := congrArg toPoint (inverse_spec i)
  rw [map_mul,map_one,point_coordinate] at h
  exact eq_inv_of_mul_eq_one_right h

def half : Chart := ofPolynomial (MvPolynomial.C (1/2:ℂ))
def ratio : Chart := coord 3*inverse 0
def cOne : Chart := coord 4*inverse 1*coord 0*inverse 3
def cTwo : Chart := coord 5*inverse 2*coord 0*inverse 3
def x : Chart := coord 0^2*inverse 2^2
def y : Chart := coord 1^2*inverse 2^2
def a : Chart := 1+ratio^6
def b : Chart := 1+cOne^6*ratio^6
def c : Chart := 1+cTwo^6*ratio^6
def d : Chart := ratio^2*cOne*half
def e : Chart := ratio^2*cOne*cTwo*half
def third : Chart := ofPolynomial (MvPolynomial.C (1/3:ℂ))
def f : Chart := ratio^4*cTwo*third
def hessian : Chart := H a b c d e f x y 1
def jacobian : Chart := J a b c d e f x y 1

lemma point_half : toPoint half=(1/2:ℂ) := by
  rw [half,point_polynomial]
  simp [CycleCubicPoint.value]
lemma field_half : toField half=(1/2:FunctionField) := by
  rw [half,field_polynomial]
  change (residueMap.comp MvPolynomial.C) (1/2:ℂ)=_
  rw [map_div₀,map_one,map_ofNat]

lemma point_third : toPoint third=(1/3:ℂ) := by
  rw [third,point_polynomial]
  simp [CycleCubicPoint.value]
lemma field_third : toField third=(1/3:FunctionField) := by
  rw [third,field_polynomial]
  change (residueMap.comp MvPolynomial.C) (1/3:ℂ)=_
  rw [map_div₀,map_one,map_ofNat]

lemma cast_0 : (Fin.castSucc (Fin.castSucc (0:Fin 4)) : Fin 6)=0 := rfl
lemma cast_1 : (Fin.castSucc (Fin.castSucc (1:Fin 4)) : Fin 6)=1 := rfl
lemma cast_2 : (Fin.castSucc (Fin.castSucc (2:Fin 4)) : Fin 6)=2 := rfl
lemma cast_3 : (Fin.castSucc (Fin.castSucc (3:Fin 4)) : Fin 6)=3 := rfl
lemma point_0 : CycleCubicPoint.point 0=2 := rfl
lemma point_1 : CycleCubicPoint.point 1=2*Complex.I := rfl
lemma point_2 : CycleCubicPoint.point 2=1-Complex.I := rfl
lemma point_3 : CycleCubicPoint.point 3=1+Complex.I := rfl
lemma point_4 : CycleCubicPoint.point 4=0 := rfl
lemma point_5 : CycleCubicPoint.point 5=0 := rfl

lemma point_values :
    toPoint a=1-Complex.I/8 ∧ toPoint b=1 ∧ toPoint c=1 ∧
    toPoint d=0 ∧ toPoint e=0 ∧ toPoint f=0 ∧
    toPoint x=2*Complex.I ∧ toPoint y= -2*Complex.I := by
  simp only [a,b,c,d,e,f,ratio,cOne,cTwo,x,y,map_add,map_mul,map_pow,map_one,
    point_half,point_third,point_coordinate,point_inverse,cast_0,cast_1,cast_2,cast_3,point_0,point_1,point_2,point_3,point_4,point_5]
  norm_num
  refine ⟨?_,?_,?_⟩
  all_goals apply Complex.ext <;>
    norm_num [pow_succ,Complex.mul_re,Complex.mul_im,Complex.inv_re,Complex.inv_im,Complex.normSq]

lemma hessian_at_point : toPoint hessian≠0 := by
  obtain ⟨ha,hb,hc,hd,he,hf,hx,hy⟩ := point_values
  unfold hessian
  rw [map_H,map_one,ha,hb,hc,hd,he,hf,hx,hy]
  exact CycleCubicPoint.H_nonzero
lemma jacobian_at_point : toPoint jacobian≠0 := by
  obtain ⟨ha,hb,hc,hd,he,hf,hx,hy⟩ := point_values
  unfold jacobian
  rw [map_J,map_one,ha,hb,hc,hd,he,hf,hx,hy]
  exact CycleCubicPoint.J_nonzero

lemma hessian_in_field : toField hessian≠0 := nonzero_of_point hessian hessian_at_point
lemma jacobian_in_field : toField jacobian≠0 := nonzero_of_point jacobian jacobian_at_point

lemma field_values :
    toField a=coeffA ∧ toField b=coeffB ∧ toField c=coeffC ∧
    toField d=coeffD ∧ toField e=coeffE ∧ toField f=coeffF ∧
    toField x=CyclePhysicalCoordinates.x ∧ toField y=CyclePhysicalCoordinates.y := by
  simp only [a,b,c,d,e,f,ratio,cOne,cTwo,x,y,map_add,map_mul,map_pow,map_one,
    field_half,field_third,field_coordinate,field_inverse,coeffA,coeffB,coeffC,coeffD,coeffE,coeffF,
    CyclePhysicalCoordinates.x,CyclePhysicalCoordinates.y,CyclePhysicalCoordinates.radial,
    CyclePhysicalCoordinates.t,CyclePhysicalCoordinates.ratio,
    CyclePhysicalCoordinates.cOne,CyclePhysicalCoordinates.cTwo,
    div_eq_mul_inv,mul_inv_rev,inv_inv,inv_pow,cast_0,cast_1,cast_2,cast_3]
  repeat' apply And.intro
  all_goals first | trivial | ring

lemma physical_hessian_ne_zero :
    H coeffA coeffB coeffC coeffD coeffE coeffF
      CyclePhysicalCoordinates.x CyclePhysicalCoordinates.y 1 ≠ 0 := by
  have h := hessian_in_field
  obtain ⟨ha,hb,hc,hd,he,hf,hx,hy⟩ := field_values
  unfold hessian at h
  rw [map_H,map_one,ha,hb,hc,hd,he,hf,hx,hy] at h
  exact h
lemma physical_jacobian_ne_zero :
    J coeffA coeffB coeffC coeffD coeffE coeffF
      CyclePhysicalCoordinates.x CyclePhysicalCoordinates.y 1 ≠ 0 := by
  have h := jacobian_in_field
  obtain ⟨ha,hb,hc,hd,he,hf,hx,hy⟩ := field_values
  unfold jacobian at h
  rw [map_J,map_one,ha,hb,hc,hd,he,hf,hx,hy] at h
  exact h

def normal : Chart := 3*a*x^2+2*d*x*y+2*f*x
lemma normal_at_point : toPoint normal ≠ 0 := by
  obtain ⟨ha,hb,hc,hd,he,hf,hx,hy⟩ := point_values
  simpa only [normal,map_add,map_mul,map_pow,map_ofNat,ha,hd,hf,hx,hy,
    mul_zero,zero_mul,add_zero] using CycleCubicPoint.normal_nonzero
lemma physical_normal_ne_zero :
    3*coeffA*CyclePhysicalCoordinates.x^2+
      2*coeffD*CyclePhysicalCoordinates.x*CyclePhysicalCoordinates.y+2*coeffF*CyclePhysicalCoordinates.x ≠ 0 := by
  have h := nonzero_of_point normal normal_at_point
  obtain ⟨ha,hb,hc,hd,he,hf,hx,hy⟩ := field_values
  simpa only [normal,map_add,map_mul,map_pow,map_ofNat,ha,hd,hf,hx,hy] using h

end CyclePhysicalChart
#print axioms CyclePhysicalChart.hessian_in_field
#print axioms CyclePhysicalChart.jacobian_in_field

#print axioms CyclePhysicalChart.physical_jacobian_ne_zero
#print axioms CyclePhysicalChart.physical_normal_ne_zero
