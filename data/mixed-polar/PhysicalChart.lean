import Proposal.PhysicalNonzero
import Mathlib.RingTheory.Localization.Away.Basic

/-! Explicit coordinate localization and its honest point map. Adapted from
fqlx's accepted mixed-biweight chart and the cyclic chart of
hodgepodgeconjecture. No covariant formula or root-point evaluation is assumed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace MixedPolarPhysicalChart
open MixedPolarPhysical MixedPolarPhysicalCoordinates
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
lemma denominator_point_ne_zero : MixedPolarPhysicalCoordinates.pointValue denominator ≠ 0 := by
  have h := MixedPolarPhysicalCoordinates.testPoint_denominators_nonzero
  simpa [denominator,MixedPolarPhysicalCoordinates.pointValue,Matrix.cons_val,Fin.castSucc_mk] using
    mul_ne_zero (mul_ne_zero (mul_ne_zero (h 0) (h 1)) (h 2)) (h 3)

def toField : Chart →+* FunctionField := IsLocalization.Away.lift denominator
  (isUnit_iff_ne_zero.mpr denominator_residue_ne_zero)
def toPoint : Chart →+* ℂ := IsLocalization.Away.lift denominator
  (isUnit_iff_ne_zero.mpr denominator_point_ne_zero)

lemma field_polynomial (p : Ambient) : toField (ofPolynomial p)=residueMap p :=
  IsLocalization.Away.lift_eq _ _ _
lemma point_polynomial (p : Ambient) : toPoint (ofPolynomial p)=MixedPolarPhysicalCoordinates.pointValue p :=
  IsLocalization.Away.lift_eq _ _ _

lemma nonzero_of_point (z : Chart) (hz : toPoint z ≠ 0) : toField z ≠ 0 := by
  intro hf
  obtain ⟨n,p,hp⟩ := IsLocalization.Away.surj denominator z
  have hr := congrArg toField hp
  simp only [map_mul,map_pow,show algebraMap Ambient Chart=ofPolynomial from rfl,
    field_polynomial,hf,zero_mul] at hr
  obtain ⟨q,hq⟩ := (residueMap_kernel p).mp hr.symm
  have he : MixedPolarPhysicalCoordinates.pointValue p=0 := by
    rw [hq,map_mul,MixedPolarPhysicalCoordinates.point_on_sextic,zero_mul]
  have ht := congrArg toPoint hp
  simp only [map_mul,map_pow,show algebraMap Ambient Chart=ofPolynomial from rfl,
    point_polynomial,he] at ht
  exact hz ((mul_eq_zero.mp ht).resolve_right (pow_ne_zero _ denominator_point_ne_zero))

lemma field_coordinate (i : Fin 6) : toField (coord i)=coordinate i := field_polynomial _
lemma point_coordinate (i : Fin 6) : toPoint (coord i)=MixedPolarPhysicalCoordinates.testPoint i := by
  rw [coord,point_polynomial]
  simp [MixedPolarPhysicalCoordinates.pointValue]
lemma field_inverse (i : Fin 4) : toField (inverse i)=(coordinate i.castSucc.castSucc)⁻¹ := by
  have h := congrArg toField (inverse_spec i)
  rw [map_mul,map_one,field_coordinate] at h
  exact eq_inv_of_mul_eq_one_right h
lemma point_inverse (i : Fin 4) : toPoint (inverse i)=(MixedPolarPhysicalCoordinates.testPoint i.castSucc.castSucc)⁻¹ := by
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
def f : Chart := ratio^4*cOne^3*third
lemma point_half : toPoint half=(1/2:ℂ) := by
  rw [half,point_polynomial]
  simp [MixedPolarPhysicalCoordinates.pointValue]
lemma field_half : toField half=(1/2:FunctionField) := by
  rw [half,field_polynomial]
  change (residueMap.comp MvPolynomial.C) (1/2:ℂ)=_
  rw [map_div₀,map_one,map_ofNat]

lemma point_third : toPoint third=(1/3:ℂ) := by
  rw [third,point_polynomial]
  simp [MixedPolarPhysicalCoordinates.pointValue]
lemma field_third : toField third=(1/3:FunctionField) := by
  rw [third,field_polynomial]
  change (residueMap.comp MvPolynomial.C) (1/3:ℂ)=_
  rw [map_div₀,map_one,map_ofNat]

lemma cast_0 : (Fin.castSucc (Fin.castSucc (0:Fin 4)) : Fin 6)=0 := rfl
lemma cast_1 : (Fin.castSucc (Fin.castSucc (1:Fin 4)) : Fin 6)=1 := rfl
lemma cast_2 : (Fin.castSucc (Fin.castSucc (2:Fin 4)) : Fin 6)=2 := rfl
lemma cast_3 : (Fin.castSucc (Fin.castSucc (3:Fin 4)) : Fin 6)=3 := rfl
lemma point_0 : MixedPolarPhysicalCoordinates.testPoint 0=2 := rfl
lemma point_1 : MixedPolarPhysicalCoordinates.testPoint 1=2*Complex.I := rfl
lemma point_2 : MixedPolarPhysicalCoordinates.testPoint 2=1-Complex.I := rfl
lemma point_3 : MixedPolarPhysicalCoordinates.testPoint 3=1+Complex.I := rfl
lemma point_4 : MixedPolarPhysicalCoordinates.testPoint 4=0 := rfl
lemma point_5 : MixedPolarPhysicalCoordinates.testPoint 5=0 := rfl

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

lemma field_values :
    toField a=coeffA ∧ toField b=coeffB ∧ toField c=coeffC ∧
    toField d=coeffD ∧ toField e=coeffE ∧ toField f=coeffF ∧
    toField x=MixedPolarPhysicalCoordinates.x ∧ toField y=MixedPolarPhysicalCoordinates.y := by
  simp only [a,b,c,d,e,f,ratio,cOne,cTwo,x,y,map_add,map_mul,map_pow,map_one,
    field_half,field_third,field_coordinate,field_inverse,coeffA,coeffB,coeffC,coeffD,coeffE,coeffF,
    MixedPolarPhysicalCoordinates.x,MixedPolarPhysicalCoordinates.y,MixedPolarPhysicalCoordinates.radial,
    MixedPolarPhysicalCoordinates.t,MixedPolarPhysicalCoordinates.ratio,
    MixedPolarPhysicalCoordinates.cOne,MixedPolarPhysicalCoordinates.cTwo,
    div_eq_mul_inv,mul_inv_rev,inv_inv,inv_pow,cast_0,cast_1,cast_2,cast_3]
  repeat' apply And.intro
  all_goals first | trivial | ring


end MixedPolarPhysicalChart

#print axioms MixedPolarPhysicalChart.nonzero_of_point
#print axioms MixedPolarPhysicalChart.field_values
#print axioms MixedPolarPhysicalChart.point_values
