import Proposal.CubicJetCalculus
import Proposal.CubicSyzygy
import HodgeComputer.Constructions.ResidueTransport.MovingMap

open ResidueFirstJets

/-! First variation of the actual physical cubic-to-Jacobian map, represented
by dual numbers at the immutable parameter value. No parameter derivation on
the specialized function field is postulated.
Original cycle-three construction prepared with OpenAI Codex assistance.
Adapted to mixed-polar for benediamond with OpenAI Codex assistance. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace CyclePhysicalCubicJets
open CyclePhysical CyclePhysicalCoordinates CyclePhysicalNormalTransport
open CyclePhysicalCubicTangent CycleCubicFieldDifferential.Physical
open CycleCubicJetCalculus PolarCovariants TrivSqZeroExt
local instance cachedPhysicalField : Field FunctionField := inferInstance
local instance cachedPhysicalCharZero : CharZero FunctionField := inferInstance
local instance : Algebra ℤ FunctionField := Ring.toIntAlgebra _
abbrev JField := Jet (K:=FunctionField)
local instance cachedJetRing : CommRing JField := inferInstance
def aJet : JField := (coeffA,0)
def bJet : JField := (coeffB,0)
def cJet : JField := (coeffC,0)
def dJet : JField := (coeffD,0)
def eJet : JField := (coeffE,0)
def fJet : JField := (coeffF,0)
def kJet : JField := (0,1/2)
def xJet : JField := (x,-x*y/cubicNormal)
def yJet : JField := (y,0)
def hJet : JField := HJet aJet bJet cJet dJet eJet fJet kJet xJet yJet 1
def qJet : JField := ThetaJet aJet bJet cJet dJet eJet fJet kJet xJet yJet 1
def jJet : JField := JJet aJet bJet cJet dJet eJet fJet kJet xJet yJet 1
def sJet : JField := inl (1/3 : FunctionField)*PolarCubic.s4NumeratorJet aJet bJet cJet dJet eJet fJet kJet
def tJet : JField := inl (1/27 : FunctionField)*PolarCubic.s6NumeratorJet aJet bJet cJet dJet eJet fJet kJet
def gJet : JField := 3*aJet*xJet^2+2*dJet*xJet*yJet+fJet*yJet^2+2*kJet*yJet
def half : JField := inl (1/2 : FunctionField)
def xiJet : JField := qJet*hJet⁻¹^2
def etaJet : JField := -half*jJet*hJet⁻¹^3
def bWeierstrassJet : JField := -half^2*tJet
def aWeierstrass : FunctionField := PolarCubic.s4 coeffA coeffB coeffC coeffD coeffE coeffF
def bWeierstrass : FunctionField := -PolarCubic.s6 coeffA coeffB coeffC coeffD coeffE coeffF/4
def xiDot : FunctionField := xiJet.snd
def etaDot : FunctionField := etaJet.snd
def aDot : FunctionField := sJet.snd
def bDot : FunctionField := bWeierstrassJet.snd
def D : Derivation ℤ JField JField := jetDerivation derivative

@[simp] lemma derivative_numeral (n : ℕ) [n.AtLeastTwo] :
    derivative (ofNat(n) : FunctionField)=0 := derivative.map_natCast n

lemma hJet_value : hJet.fst=H coeffA coeffB coeffC coeffD coeffE coeffF x y 1 := by
  simpa [hJet,HJet,kJet,aJet,bJet,cJet,dJet,eJet,fJet,xJet,yJet] using
    map_HJet (fstHom FunctionField FunctionField FunctionField).toRingHom
      aJet bJet cJet dJet eJet fJet kJet xJet yJet 1
lemma qJet_value : qJet.fst=Theta coeffA coeffB coeffC coeffD coeffE coeffF x y 1 := by
  simpa [qJet,ThetaJet,kJet,aJet,bJet,cJet,dJet,eJet,fJet,xJet,yJet] using
    map_ThetaJet (fstHom FunctionField FunctionField FunctionField).toRingHom
      aJet bJet cJet dJet eJet fJet kJet xJet yJet 1
lemma jJet_value : jJet.fst=J coeffA coeffB coeffC coeffD coeffE coeffF x y 1 := by
  simpa [jJet,JJet,kJet,aJet,bJet,cJet,dJet,eJet,fJet,xJet,yJet] using
    map_JJet (fstHom FunctionField FunctionField FunctionField).toRingHom
      aJet bJet cJet dJet eJet fJet kJet xJet yJet 1
lemma hJet_nonzero : hJet.fst≠0 := by
  rw [hJet_value]
  exact CyclePhysicalChart.physical_hessian_ne_zero
lemma half_identity : (2*half : JField)=1 := by
  ext <;> norm_num [half,smul_eq_mul,op_smul_eq_smul]
lemma kJet_square : (kJet^2 : JField)=0 := by
  ext <;> simp [kJet,smul_eq_mul,op_smul_eq_smul]
lemma jet_equation : PolarCubic.cubicJet aJet bJet cJet dJet eJet fJet kJet xJet yJet 1=0 :=
  jet_cubic coeffA coeffB coeffC coeffD coeffE coeffF x y cubic_equation cubic_normal_ne_zero

lemma coefficient_derivatives :
    D aJet=0 ∧ D bJet=0 ∧ D cJet=0 ∧ D dJet=0 ∧ D eJet=0 ∧ D fJet=0 := by
  obtain ⟨ha,hb,hc,hd,he,hf⟩ := coefficient_constants
  repeat' apply And.intro
  all_goals apply TrivSqZeroExt.ext <;>
    simp [D,jetDerivation,aJet,bJet,cJet,dJet,eJet,fJet,ha,hb,hc,hd,he,hf]
lemma kJet_derivative : D kJet=0 := by
  apply TrivSqZeroExt.ext <;>
    simp [D,jetDerivation,kJet,Derivation.leibniz_inv,smul_eq_mul]
lemma yJet_derivative : D yJet=1 := by
  apply TrivSqZeroExt.ext <;>
    simp [D,jetDerivation,yJet,passive_parameters.2.2.2.2.1]
lemma jet_differential : (gJet*D xiJet : JField)=6*etaJet := by
  obtain ⟨ha,hb,hc,hd,he,hf⟩ := coefficient_derivatives
  have hc := cleared_differential D aJet bJet cJet dJet eJet fJet kJet xJet yJet
    ha hb hc hd he hf kJet_square kJet_derivative jet_equation yJet_derivative
  exact invariant_from_cleared D hJet qJet jJet gJet hJet⁻¹ half
    (TrivSqZeroExt.inv_mul_cancel hJet_nonzero) half_identity hc
lemma jet_curve : (etaJet^2 : JField)=xiJet^3+sJet*xiJet+bWeierstrassJet := by
  have hc := PolarCovariants.IdentityData.full_syzygyJet (K:=JField)
    aJet bJet cJet dJet eJet fJet kJet xJet yJet kJet_square
  dsimp only at hc
  rw [jet_equation,zero_mul,add_zero] at hc
  have hthird : (3:JField)*inl (1/3:FunctionField)=1 := by
    ext <;> norm_num [smul_eq_mul,op_smul_eq_smul]
  have hinv27 : (27:JField)*inl (1/27:FunctionField)=1 := by
    ext <;> norm_num [smul_eq_mul,op_smul_eq_smul]
  simpa only [etaJet,xiJet,bWeierstrassJet,sJet,tJet,sub_eq_add_neg,neg_mul] using
    curve_from_syzygy27 hJet qJet jJet
      (PolarCubic.s4NumeratorJet aJet bJet cJet dJet eJet fJet kJet)
      (PolarCubic.s6NumeratorJet aJet bJet cJet dJet eJet fJet kJet)
      hJet⁻¹ half (inl (1/3:FunctionField)) (inl (1/27:FunctionField))
      (TrivSqZeroExt.inv_mul_cancel hJet_nonzero) half_identity hthird hinv27 hc

lemma xiJet_value : xiJet.fst=xi := by
  simp only [xiJet,fst_mul,fst_pow,fst_inv,qJet_value,hJet_value,xi,div_eq_mul_inv,inv_pow]
lemma etaJet_value : etaJet.fst=eta := by
  simp only [etaJet,fst_mul,fst_neg,fst_pow,fst_inv,jJet_value,hJet_value,half,fst_inl,eta]
  ring
lemma sJet_value : sJet.fst=aWeierstrass := by
  simp [sJet,PolarCubic.s4,PolarCubic.s4NumeratorJet,PolarCubic.s4Numerator,
    aJet,bJet,cJet,dJet,eJet,fJet,kJet,aWeierstrass] <;> ring
lemma bWeierstrassJet_value : bWeierstrassJet.fst=bWeierstrass := by
  simp [bWeierstrassJet,half,tJet,PolarCubic.s6,PolarCubic.s6NumeratorJet,PolarCubic.s6Numerator,
    aJet,bJet,cJet,dJet,eJet,fJet,kJet,bWeierstrass]
  ring
lemma gJet_value : gJet.fst=cubicNormal := by
  simp [gJet,aJet,dJet,fJet,kJet,xJet,yJet,cubicNormal]
lemma gJet_dot : gJet.snd=cubicNormalJet := by
  simp [gJet,aJet,dJet,fJet,kJet,xJet,yJet,cubicNormalJet,cubicSecondNormal,
    smul_eq_mul,op_smul_eq_smul]
  ring

lemma curve : eta^2=xi^3+aWeierstrass*xi+bWeierstrass := by
  have h := congrArg TrivSqZeroExt.fst jet_curve
  simpa only [fst_pow,fst_add,fst_mul,xiJet_value,etaJet_value,sJet_value,bWeierstrassJet_value] using h
lemma curve_jet : 2*eta*etaDot=(3*xi^2+aWeierstrass)*xiDot+aDot*xi+bDot := by
  have h := curve_first_variation xiJet etaJet sJet bWeierstrassJet jet_curve
  simpa only [xiJet_value,etaJet_value,sJet_value,xiDot,etaDot,aDot,bDot] using h
lemma differential_value : cubicNormal*derivative xi=6*eta := by
  have h := congrArg TrivSqZeroExt.fst jet_differential
  simpa only [fst_mul,fst_numeral,D,jetDerivation_fst,xiJet_value,etaJet_value,gJet_value] using h
lemma differential_jet :
    cubicNormal^2*(2*eta*derivative xiDot-2*derivative xi*etaDot)=
      -4*eta^2*3*cubicNormalJet := by
  have h := differential_first_variation derivative xiJet etaJet gJet jet_differential
  simp only [xiJet_value,gJet_value,gJet_dot] at h
  exact differential_jet_from_cleared cubicNormal eta (derivative xi)
    (derivative xiDot) etaDot cubicNormalJet differential_value h

lemma aDot_formula : aDot=(9*coeffA*coeffB*coeffC-coeffC*coeffD*coeffF)/2 := by
  simp [aDot,sJet,PolarCubic.s4NumeratorJet,PolarCubic.s4Numerator,PolarCubic.s4NumeratorK,
    aJet,bJet,cJet,dJet,eJet,fJet,kJet,
    smul_eq_mul,op_smul_eq_smul]
  ring
lemma bDot_formula : bDot=
    coeffA*coeffC*coeffD*coeffE^2 := by
  simp [bDot,bWeierstrassJet,tJet,half,PolarCubic.s6NumeratorJet,
    PolarCubic.s6Numerator,PolarCubic.s6NumeratorK,
    aJet,bJet,cJet,dJet,eJet,fJet,kJet,smul_eq_mul,op_smul_eq_smul]
  ring
lemma weierstrass_constants : derivative aWeierstrass=0 ∧ derivative bWeierstrass=0 := by
  obtain ⟨ha,hb,hc,hd,he,hf⟩ := coefficient_constants
  have h27 : derivative (27:FunctionField)=0 := derivative.map_natCast 27
  have h4 : derivative (4:FunctionField)=0 := derivative.map_natCast 4
  have h6 : derivative (6:FunctionField)=0 := derivative.map_natCast 6
  simp [aWeierstrass,bWeierstrass,PolarCubic.s4,PolarCubic.s6,PolarCubic.s4Numerator,PolarCubic.s6Numerator,
    Derivation.leibniz,Derivation.leibniz_pow,Derivation.leibniz_div,
    smul_eq_mul,nsmul_eq_mul,ha,hb,hc,hd,he,hf,h27,h4,h6]
lemma eta_nonzero : eta≠0 :=
  div_ne_zero (neg_ne_zero.mpr CyclePhysicalChart.physical_jacobian_ne_zero)
    (mul_ne_zero (by norm_num) (pow_ne_zero _ CyclePhysicalChart.physical_hessian_ne_zero))
theorem source_transport :
    cubicNormalJet/cubicNormal=(aDot*xi+bDot)/(2*eta^2)-
      (cubicNormal/3)*derivative (xiDot/(2*eta)) :=
  CycleMovingMap.residue_source_from_jet derivative xi eta aWeierstrass bWeierstrass
    cubicNormal 3 xiDot etaDot aDot bDot cubicNormalJet cubic_normal_ne_zero
    eta_nonzero (by norm_num) curve weierstrass_constants.1 weierstrass_constants.2
    invariant_differential curve_jet differential_jet

end CyclePhysicalCubicJets
#print axioms CyclePhysicalCubicJets.curve_jet
#print axioms CyclePhysicalCubicJets.differential_jet
#print axioms CyclePhysicalCubicJets.source_transport
