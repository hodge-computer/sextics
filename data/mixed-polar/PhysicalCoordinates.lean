import Proposal.PhysicalField
import Mathlib.Tactic.LinearCombination
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

/-! The exact mixed-polar paired-sign coordinates. Adapted from the accepted
mixed-biweight coordinates with attribution to fqlx and hodgepodgeconjecture.
The reverse edge is xy^2, and the physical source is balanced. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace MixedPolarPhysicalCoordinates
open MixedPolarPhysical
def coordinate (i : Fin 6) : FunctionField := residueMap (MvPolynomial.X i)
local notation "p" => coordinate

instance physical_charZero : CharZero FunctionField :=
  charZero_of_injective_ringHom (f := residueMap.comp MvPolynomial.C)
    (residueMap.comp MvPolynomial.C).injective

def cubic {K : Type*} [CommRing K] (a b c d e f x y z : K) : K :=
  a*x^3+b*y^3+c*z^3+d*x^2*y+e*y^2*z+f*x*y^2

lemma coordinate_ne_zero (i : Fin 6) : p i ≠ 0 := by
  intro hz
  have hd := (residueMap_kernel _).mp hz
  have hb := MvPolynomial.totalDegree_le_of_dvd_of_isDomain hd (MvPolynomial.X_ne_zero i)
  rw [sextic_homogeneous.totalDegree sextic_irreducible.ne_zero,
    MvPolynomial.totalDegree_X] at hb
  norm_num at hb

lemma equation_zero :
    p 0^6+p 1^6+p 2^6+p 3^6+p 4^6+p 5^6+
      (1/2)*(p 0^3*p 1*p 3*p 4+p 1^3*p 2*p 4*p 5)+(1/3)*(p 0*p 1*p 3*p 4^3)=0 := by
  have hh : residueMap (MvPolynomial.C (1/2:ℂ))=(1/2:FunctionField) := by
    change (residueMap.comp MvPolynomial.C) (1/2:ℂ)=_
    rw [map_div₀,map_one,map_ofNat]
  have ht : residueMap (MvPolynomial.C (1/3:ℂ))=(1/3:FunctionField) := by
    change (residueMap.comp MvPolynomial.C) (1/3:ℂ)=_
    rw [map_div₀,map_one,map_ofNat]
  have he := (residueMap_kernel sextic).mpr (dvd_refl sextic)
  simpa only [sextic,map_add,map_mul,map_pow,hh,ht,coordinate] using he

def radial : FunctionField := p 2^2
def ratio : FunctionField := p 3/p 0
def cOne : FunctionField := (p 4/p 1)/ratio
def cTwo : FunctionField := (p 5/p 2)/ratio
def x : FunctionField := p 0^2/radial
def y : FunctionField := p 1^2/radial
def t : FunctionField := ratio^6
def parameterT : FunctionField := radial*t
def coeffA : FunctionField := 1+t
def coeffB : FunctionField := 1+cOne^6*t
def coeffC : FunctionField := 1+cTwo^6*t
def coeffD : FunctionField := ratio^2*cOne/2
def coeffE : FunctionField := ratio^2*cOne*cTwo/2
def coeffF : FunctionField := ratio^4*cOne^3/3

lemma radial_ne_zero : radial ≠ 0 := pow_ne_zero _ (coordinate_ne_zero 2)
lemma ratio_ne_zero : ratio ≠ 0 := div_ne_zero (coordinate_ne_zero 3) (coordinate_ne_zero 0)
lemma t_ne_zero : t ≠ 0 := pow_ne_zero _ ratio_ne_zero

lemma cubic_equation :
    cubic coeffA coeffB coeffC coeffD coeffE coeffF x y 1=0 := by
  have h0 := coordinate_ne_zero 0
  have h1 := coordinate_ne_zero 1
  have h2 := coordinate_ne_zero 2
  have h3 := coordinate_ne_zero 3
  have he := equation_zero
  simp only [cubic,coeffA,coeffB,coeffC,coeffD,coeffE,coeffF,
    x,y,radial,t,cOne,cTwo,ratio]
  field_simp
  linear_combination 6*he

lemma coordinate_X (i : Fin 6) : residueMap (MvPolynomial.X i)=p i := rfl
lemma field_half : residueMap (MvPolynomial.C (1/2:ℂ))=(1/2:FunctionField) := by
  change (residueMap.comp MvPolynomial.C) (1/2:ℂ)=_
  rw [map_div₀,map_one,map_ofNat]
lemma field_third : residueMap (MvPolynomial.C (1/3:ℂ))=(1/3:FunctionField) := by
  change (residueMap.comp MvPolynomial.C) (1/3:ℂ)=_
  rw [map_div₀,map_one,map_ofNat]
def gradient (i : Fin 6) : FunctionField := residueMap (MvPolynomial.pderiv i sextic)
def hessian (i j : Fin 6) : FunctionField :=
  residueMap (MvPolynomial.pderiv i (MvPolynomial.pderiv j sextic))
def pairedGradient : FunctionField := p 0*gradient 0+p 3*gradient 3
def pairedHessian : FunctionField :=
  p 0^2*hessian 0 0+2*p 0*p 3*hessian 0 3+p 3^2*hessian 3 3
def cubicNormal : FunctionField := 3*coeffA*x^2+2*coeffD*x*y+coeffF*y^2
def cubicSecondNormal : FunctionField := 6*coeffA*x+2*coeffD*y

lemma paired_gradient_identity : pairedGradient=2*radial^3*x*cubicNormal := by
  have h0 := coordinate_ne_zero 0
  have h1 := coordinate_ne_zero 1
  have h2 := coordinate_ne_zero 2
  have h3 := coordinate_ne_zero 3
  simp only [pairedGradient,gradient,sextic,MvPolynomial.pderiv_mul,
    MvPolynomial.pderiv_pow,map_add,map_mul,map_pow,MvPolynomial.pderiv_C,
    MvPolynomial.pderiv_X,Pi.single_apply]
  norm_num [Fin.ext_iff,coordinate_X,map_ofNat,field_half,field_third]
  simp only [cubicNormal,coeffA,coeffD,coeffF,radial,x,y,t,cOne,cTwo,ratio]
  field_simp
  ring

lemma paired_hessian_identity :
    pairedHessian-pairedGradient=4*radial^3*x^2*cubicSecondNormal := by
  have h0 := coordinate_ne_zero 0
  have h1 := coordinate_ne_zero 1
  have h2 := coordinate_ne_zero 2
  have h3 := coordinate_ne_zero 3
  simp only [pairedHessian,pairedGradient,hessian,gradient,sextic,
    MvPolynomial.pderiv_mul,MvPolynomial.pderiv_pow,map_add,map_mul,map_pow,
    MvPolynomial.pderiv_C,MvPolynomial.pderiv_X,Pi.single_apply,
    Derivation.map_natCast]
  norm_num [Fin.ext_iff,coordinate_X,map_ofNat,field_half,field_third]
  simp only [cubicSecondNormal,coeffA,coeffD,coeffF,radial,x,y,t,cOne,cTwo,ratio]
  field_simp
  ring


end MixedPolarPhysicalCoordinates
#print axioms MixedPolarPhysicalCoordinates.cubic_equation
