import Proposal.PhysicalChart
import HodgeComputer.Constructions.HoldoutCover.ResiduePiolaPullback
import HodgeComputer.Constructions.ResidueTransport.NormalChange

/-! Exact correction from the physical X0-normal to the paired-sign normal.
This closes the normal-chart source obligation independently of the cubic
covariants. It retains the fixed sextic and target. The residue-divergence
interface is the shared construction credited to fqlx and collaborators.
Original cycle-three work prepared with OpenAI Codex assistance for hodgepodgeconjecture.
Adapted to mixed-biweight for fqlx with OpenAI Codex assistance. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace CyclePhysicalNormalTransport
open HoldoutConstruction CyclePhysical CyclePhysicalCoordinates
open scoped BigOperators

instance physical_charZero : CharZero FunctionField :=
  charZero_of_injective_ringHom (f := residueMap.comp MvPolynomial.C)
    (residueMap.comp MvPolynomial.C).injective

local notation "p" => coordinate
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
def cubicNormal : FunctionField := 3*coeffA*x^2+2*coeffD*x*y+2*coeffF*x
def cubicSecondNormal : FunctionField := 6*coeffA*x+2*coeffD*y+2*coeffF
def cubicNormalJet : FunctionField := 3*x^2-x^3*cubicSecondNormal/cubicNormal
def correction : FunctionField := -p 0^3*p 3^4/pairedGradient
def correctionVector : Fin 5 → FunctionField := Pi.single 2 correction

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

lemma cubic_normal_ne_zero : cubicNormal≠0 := CyclePhysicalChart.physical_normal_ne_zero
lemma paired_gradient_ne_zero : pairedGradient≠0 := by
  rw [paired_gradient_identity]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num)
    (pow_ne_zero _ radial_ne_zero)) (div_ne_zero (pow_ne_zero _ (coordinate_ne_zero 0))
      radial_ne_zero)) cubic_normal_ne_zero

lemma tangent_p0 : tangent 2 (p 0)= -gradient 3/gradient 0 := by
  rw [coordinate,tangent_apply]
  norm_num [gradient,MvPolynomial.pderiv_X,Pi.single_apply,
    show (2:Fin 5).succ=(3:Fin 6) from rfl,Fin.ext_iff,neg_div]
lemma tangent_p3 : tangent 2 (p 3)=1 := by
  rw [coordinate,tangent_apply]
  norm_num [MvPolynomial.pderiv_X,Pi.single_apply,
    show (2:Fin 5).succ=(3:Fin 6) from rfl,Fin.ext_iff]
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

lemma source_value : residueMap source=p 0^3*p 3^3 := by simp [source,coordinate]
lemma source_derivative : residueMap (MvPolynomial.pderiv 0 source)=3*p 0^2*p 3^3 := by
  norm_num [source,MvPolynomial.pderiv_mul,MvPolynomial.pderiv_pow,
    MvPolynomial.pderiv_X,Pi.single_apply,coordinate_X,map_ofNat,Fin.ext_iff]
  ring

theorem physical_source_transport :
    residueMap (MvPolynomial.pderiv 0 source)/gradient 0-
      residueMap source*hessian 0 0/(gradient 0)^2 =
      ratio^3*cubicNormalJet/cubicNormal+
        residueDivergence tangent (gradient 0) correctionVector := by
  have hn : gradient 0≠0 := normal_ne_zero
  have hp := ResidueNormalChange.cubed_paired_normal_change (tangent 2) (p 0) (p 3) (gradient 0) (gradient 3)
    (hessian 0 0) (hessian 0 3) (hessian 3 3) hn paired_gradient_ne_zero
    tangent_p0 tangent_p3 (by rw [tangent_gradient,hessian_commute 3 0])
    (tangent_gradient 3)
  rw [source_value,source_derivative,correction_divergence]
  change _ = _+(tangent 2 (-p 0^3*p 3^4/pairedGradient)-
    (-p 0^3*p 3^4/pairedGradient)*tangent 2 (gradient 0)/gradient 0)
  change _ = p 0^3*p 3^3*(7*pairedGradient-pairedHessian)/pairedGradient^2+_ at hp
  rw [hp]
  congr 1
  have hs := paired_hessian_identity
  rw [paired_gradient_identity] at hs ⊢
  have hg := cubic_normal_ne_zero
  have h0 := coordinate_ne_zero 0
  have hr := radial_ne_zero
  have hx : x≠0 := div_ne_zero (pow_ne_zero _ h0) hr
  have he : p 0^3*p 3^3=ratio^3*radial^3*x^3 := by
    simp only [ratio,x]
    field_simp
  rw [he]
  unfold cubicNormalJet
  rw [sub_eq_iff_eq_add.mp hs]
  field_simp
  ring

end CyclePhysicalNormalTransport
#print axioms CyclePhysicalNormalTransport.physical_source_transport
