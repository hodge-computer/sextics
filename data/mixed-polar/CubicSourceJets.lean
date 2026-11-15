import Proposal.CubicJetCalculus
import Proposal.BalancedShear
import HodgeComputer.Constructions.ResidueTransport.MovingMap

/-! The actual balanced xyz first variation after the two determinant-one
shears.  The six coefficient jets are explicitly (0,0,0,0,k,-3a/(2d));
no parameter derivation on the specialized physical field is assumed.
The maintained TransitiveCubic supplies every covariant identity. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
namespace MixedPolarCubicSourceJets
open TransitiveCovariants MixedPolarCubicJetCalculus TrivSqZeroExt
variable {K : Type*} [Field K] [CharZero K]

@[simp] lemma derivation_numeral (D : Derivation ℤ K K) (n : ℕ) [n.AtLeastTwo] :
    D (ofNat(n) : K)=0 := D.map_natCast n

structure Data (K : Type*) where
  a : K
  b : K
  c : K
  d : K
  e : K
  k : K
  x : K
  y : K

def normal (p : Data K) : K := 3*p.a*p.x^2+2*p.d*p.x*p.y
def secondNormal (p : Data K) : K := 6*p.a*p.x+2*p.d*p.y
def modifiedSource (p : Data K) : K := p.k*p.y^2-3*p.a*p.x^2/(2*p.d)
def normalDot (p : Data K) : K := p.y-(p.x+p.k*p.y)*p.y*secondNormal p/normal p
def aJet (p : Data K) : (Jet (K:=K)) := (p.a,0)
def bJet (p : Data K) : (Jet (K:=K)) := (p.b,0)
def cJet (p : Data K) : (Jet (K:=K)) := (p.c,0)
def dJet (p : Data K) : (Jet (K:=K)) := (p.d,0)
def eJet (p : Data K) : (Jet (K:=K)) := (p.e,p.k)
def fJet (p : Data K) : (Jet (K:=K)) := (0,-3*p.a/(2*p.d))
def xJet (p : Data K) : (Jet (K:=K)) := (p.x,-modifiedSource p/normal p)
def yJet (p : Data K) : (Jet (K:=K)) := (p.y,0)
def hJet (p : Data K) : (Jet (K:=K)) := H (aJet p) (bJet p) (cJet p) (dJet p) (eJet p) (fJet p) (xJet p) (yJet p) 1
def qJet (p : Data K) : (Jet (K:=K)) := Theta (aJet p) (bJet p) (cJet p) (dJet p) (eJet p) (fJet p) (xJet p) (yJet p) 1
def jJet (p : Data K) : (Jet (K:=K)) := J (aJet p) (bJet p) (cJet p) (dJet p) (eJet p) (fJet p) (xJet p) (yJet p) 1
def sJet (p : Data K) : (Jet (K:=K)) := inl (1/3:K)*TransitiveCubic.s4Numerator (aJet p) (bJet p) (cJet p) (dJet p) (eJet p) (fJet p)
def tJet (p : Data K) : (Jet (K:=K)) := inl (1/27:K)*TransitiveCubic.s6Numerator (aJet p) (bJet p) (cJet p) (dJet p) (eJet p) (fJet p)
def half : (Jet (K:=K)) := inl (1/2:K)
def xiJet (p : Data K) : (Jet (K:=K)) := qJet p*(hJet p)⁻¹^2
def etaJet (p : Data K) : (Jet (K:=K)) := -half*jJet p*(hJet p)⁻¹^3
def bWeierstrassJet (p : Data K) : (Jet (K:=K)) := -half^2*tJet p
def gJet (p : Data K) : (Jet (K:=K)) := 3*aJet p*xJet p^2+2*dJet p*xJet p*yJet p+2*fJet p*xJet p

def xi (p : Data K) : K := Theta p.a p.b p.c p.d p.e 0 p.x p.y 1/(H p.a p.b p.c p.d p.e 0 p.x p.y 1)^2
def eta (p : Data K) : K := -J p.a p.b p.c p.d p.e 0 p.x p.y 1/(2*(H p.a p.b p.c p.d p.e 0 p.x p.y 1)^3)
def aWeierstrass (p : Data K) : K := TransitiveCubic.s4 p.a p.b p.c p.d p.e 0
def bWeierstrass (p : Data K) : K := -TransitiveCubic.s6 p.a p.b p.c p.d p.e 0/4
def xiDot (p : Data K) : K := (xiJet p).snd
def etaDot (p : Data K) : K := (etaJet p).snd
def aDot (p : Data K) : K := (sJet p).snd
def bDot (p : Data K) : K := (bWeierstrassJet p).snd

lemma hJet_value (p : Data K) : (hJet p).fst=H p.a p.b p.c p.d p.e 0 p.x p.y 1 := by
  exact map_H (fstHom K K K).toRingHom (aJet p) (bJet p) (cJet p) (dJet p) (eJet p) (fJet p) (xJet p) (yJet p) 1
lemma qJet_value (p : Data K) : (qJet p).fst=Theta p.a p.b p.c p.d p.e 0 p.x p.y 1 := by
  exact map_Theta (fstHom K K K).toRingHom (aJet p) (bJet p) (cJet p) (dJet p) (eJet p) (fJet p) (xJet p) (yJet p) 1
lemma jJet_value (p : Data K) : (jJet p).fst=J p.a p.b p.c p.d p.e 0 p.x p.y 1 := by
  exact map_J (fstHom K K K).toRingHom (aJet p) (bJet p) (cJet p) (dJet p) (eJet p) (fJet p) (xJet p) (yJet p) 1
lemma xiJet_value (p : Data K) : (xiJet p).fst=xi p := by
  simp only [xiJet,fst_mul,fst_pow,fst_inv,qJet_value,hJet_value,xi,div_eq_mul_inv,inv_pow]
lemma etaJet_value (p : Data K) : (etaJet p).fst=eta p := by
  simp only [etaJet,fst_mul,fst_neg,fst_pow,fst_inv,jJet_value,hJet_value,half,fst_inl,eta]
  ring
lemma sJet_value (p : Data K) : (sJet p).fst=aWeierstrass p := by
  simp [sJet,TransitiveCubic.s4,TransitiveCubic.s4Numerator,aJet,bJet,cJet,dJet,eJet,fJet,aWeierstrass] <;> ring
lemma bJet_value (p : Data K) : (bWeierstrassJet p).fst=bWeierstrass p := by
  simp [bWeierstrassJet,half,tJet,TransitiveCubic.s6,TransitiveCubic.s6Numerator,aJet,bJet,cJet,dJet,eJet,fJet,bWeierstrass]
  ring
lemma gJet_value (p : Data K) : (gJet p).fst=normal p := by
  simp [gJet,aJet,dJet,fJet,xJet,yJet,normal]

lemma jet_equation (p : Data K)
    (hu : TransitiveCubic.cubic p.a p.b p.c p.d p.e 0 p.x p.y 1=0)
    (hg : normal p ≠ 0) :
    TransitiveCubic.cubic (aJet p) (bJet p) (cJet p) (dJet p) (eJet p) (fJet p) (xJet p) (yJet p) (1:(Jet (K:=K)))=0 := by
  apply TrivSqZeroExt.ext
  · simpa [TransitiveCubic.cubic,aJet,bJet,cJet,dJet,eJet,fJet,xJet,yJet] using hu
  · simp [TransitiveCubic.cubic,aJet,bJet,cJet,dJet,eJet,fJet,xJet,yJet,smul_eq_mul,op_smul_eq_smul]
    have ht : (-modifiedSource p/normal p)*normal p = -modifiedSource p := div_mul_cancel₀ _ hg
    dsimp only [normal,modifiedSource] at ht ⊢
    linear_combination ht

lemma gJet_dot (p : Data K) (hd : p.d ≠ 0) (hg : normal p ≠ 0) :
    (gJet p).snd=normalDot p := by
  have hh := MixedPolarBalancedShear.second_normal_source_unchanged p.a p.d p.k p.x p.y (normal p) hd hg rfl
  have hh' : (-3*p.a*p.x/p.d-modifiedSource p*secondNormal p/normal p)=normalDot p := by
    apply (div_left_inj' hg).mp
    exact hh
  simp [gJet,aJet,dJet,fJet,xJet,yJet,smul_eq_mul,op_smul_eq_smul]
  rw [← hh']
  dsimp only [modifiedSource,secondNormal]
  ring

lemma aDot_formula (p : Data K) (hd : p.d ≠ 0) :
    aDot p=p.c*p.d^2*p.k+(9/2:K)*p.a*p.b*p.c := by
  simp [aDot,sJet,TransitiveCubic.s4Numerator,aJet,bJet,cJet,dJet,eJet,fJet,smul_eq_mul,op_smul_eq_smul]
  field_simp
  ring
lemma bDot_formula (p : Data K) (hd : p.d ≠ 0) :
    bDot p=-(12*p.a^2*p.c*p.e^2*p.k-4*p.a*p.c*p.d*p.e^2)/4 := by
  simp [bDot,bWeierstrassJet,tJet,half,TransitiveCubic.s6Numerator,aJet,bJet,cJet,dJet,eJet,fJet,smul_eq_mul,op_smul_eq_smul]
  field_simp
  ring

lemma half_identity : (2:(Jet (K:=K)))*half=1 := by
  ext <;> norm_num [half,smul_eq_mul,op_smul_eq_smul]

lemma jet_curve (p : Data K)
    (hu : TransitiveCubic.cubic p.a p.b p.c p.d p.e 0 p.x p.y 1=0)
    (hg : normal p ≠ 0) (hH : H p.a p.b p.c p.d p.e 0 p.x p.y 1 ≠ 0) :
    etaJet p^2=xiJet p^3+sJet p*xiJet p+bWeierstrassJet p := by
  have hhn : (hJet p).fst ≠ 0 := hJet_value p ▸ hH
  have hc := TransitiveCovariants.IdentityData.full_syzygy
    (aJet p) (bJet p) (cJet p) (dJet p) (eJet p) (fJet p) (xJet p) (yJet p)
  dsimp only at hc
  rw [jet_equation p hu hg,zero_mul,add_zero] at hc
  have hthird : (3:(Jet (K:=K)))*inl (1/3:K)=1 := by
    ext <;> norm_num [smul_eq_mul,op_smul_eq_smul]
  have hinv27 : (27:(Jet (K:=K)))*inl (1/27:K)=1 := by
    ext <;> norm_num [smul_eq_mul,op_smul_eq_smul]
  simpa only [etaJet,xiJet,bWeierstrassJet,sJet,tJet,sub_eq_add_neg,neg_mul] using
    curve_from_syzygy27 (hJet p) (qJet p) (jJet p)
      (TransitiveCubic.s4Numerator (aJet p) (bJet p) (cJet p) (dJet p) (eJet p) (fJet p))
      (TransitiveCubic.s6Numerator (aJet p) (bJet p) (cJet p) (dJet p) (eJet p) (fJet p))
      (hJet p)⁻¹ half (inl (1/3:K)) (inl (1/27:K))
      (TrivSqZeroExt.inv_mul_cancel hhn) half_identity hthird hinv27 hc

lemma coefficient_derivatives (p : Data K) (D : Derivation ℤ K K)
    (ha : D p.a=0) (hb : D p.b=0) (hc : D p.c=0)
    (hd : D p.d=0) (he : D p.e=0) (hk : D p.k=0) :
    jetDerivation D (aJet p)=0 ∧ jetDerivation D (bJet p)=0 ∧
    jetDerivation D (cJet p)=0 ∧ jetDerivation D (dJet p)=0 ∧
    jetDerivation D (eJet p)=0 ∧ jetDerivation D (fJet p)=0 := by
  repeat' apply And.intro
  all_goals apply TrivSqZeroExt.ext <;>
    simp [jetDerivation,aJet,bJet,cJet,dJet,eJet,fJet,ha,hb,hc,hd,he,hk,
      Derivation.leibniz_div,Derivation.leibniz,smul_eq_mul,D.map_natCast]

lemma jet_differential (p : Data K) (D : Derivation ℤ K K)
    (ha : D p.a=0) (hb : D p.b=0) (hc : D p.c=0)
    (hd : D p.d=0) (he : D p.e=0) (hk : D p.k=0)
    (hy : D p.y=1)
    (hu : TransitiveCubic.cubic p.a p.b p.c p.d p.e 0 p.x p.y 1=0)
    (hg : normal p ≠ 0) (hH : H p.a p.b p.c p.d p.e 0 p.x p.y 1 ≠ 0) :
    gJet p*jetDerivation D (xiJet p)=6*etaJet p := by
  obtain ⟨ha',hb',hc',hd',he',hf'⟩ := coefficient_derivatives p D ha hb hc hd he hk
  have hy' : jetDerivation D (yJet p)=1 := by
    apply TrivSqZeroExt.ext <;> simp [jetDerivation,yJet,hy]
  have hc' := cleared_differential (jetDerivation D) (aJet p) (bJet p) (cJet p)
    (dJet p) (eJet p) (fJet p) (xJet p) (yJet p)
    ha' hb' hc' hd' he' hf' (jet_equation p hu hg) hy'
  exact invariant_from_cleared (jetDerivation D) (hJet p) (qJet p) (jJet p) (gJet p)
    (hJet p)⁻¹ half (TrivSqZeroExt.inv_mul_cancel (hJet_value p ▸ hH))
    half_identity hc'

lemma curve (p : Data K)
    (hu : TransitiveCubic.cubic p.a p.b p.c p.d p.e 0 p.x p.y 1=0)
    (hg : normal p ≠ 0) (hH : H p.a p.b p.c p.d p.e 0 p.x p.y 1 ≠ 0) :
    eta p^2=xi p^3+aWeierstrass p*xi p+bWeierstrass p := by
  have hh := congrArg TrivSqZeroExt.fst (jet_curve p hu hg hH)
  simpa only [fst_pow,fst_add,fst_mul,xiJet_value,etaJet_value,sJet_value,bJet_value] using hh

lemma differential_value (p : Data K) (D : Derivation ℤ K K)
    (ha : D p.a=0) (hb : D p.b=0) (hc : D p.c=0)
    (hd : D p.d=0) (he : D p.e=0) (hk : D p.k=0)
    (hy : D p.y=1)
    (hu : TransitiveCubic.cubic p.a p.b p.c p.d p.e 0 p.x p.y 1=0)
    (hg : normal p ≠ 0) (hH : H p.a p.b p.c p.d p.e 0 p.x p.y 1 ≠ 0) :
    normal p*D (xi p)=6*eta p := by
  have hh := congrArg TrivSqZeroExt.fst (jet_differential p D ha hb hc hd he hk hy hu hg hH)
  simpa only [fst_mul,fst_numeral,jetDerivation_fst,xiJet_value,etaJet_value,gJet_value] using hh

lemma eta_nonzero (p : Data K)
    (hH : H p.a p.b p.c p.d p.e 0 p.x p.y 1 ≠ 0)
    (hJ : J p.a p.b p.c p.d p.e 0 p.x p.y 1 ≠ 0) : eta p ≠ 0 :=
  div_ne_zero (neg_ne_zero.mpr hJ) (mul_ne_zero (by norm_num) (pow_ne_zero _ hH))

lemma weierstrass_constants (p : Data K) (D : Derivation ℤ K K)
    (ha : D p.a=0) (hb : D p.b=0) (hc : D p.c=0)
    (hd : D p.d=0) (he : D p.e=0) :
    D (aWeierstrass p)=0 ∧ D (bWeierstrass p)=0 := by
  simp [aWeierstrass,bWeierstrass,TransitiveCubic.s4,TransitiveCubic.s6,
    TransitiveCubic.s4Numerator,TransitiveCubic.s6Numerator,
    Derivation.leibniz,Derivation.leibniz_pow,Derivation.leibniz_div,
    smul_eq_mul,nsmul_eq_mul,ha,hb,hc,hd,he,D.map_natCast]

/-- The complete source transport for the actual sheared xyz jet.  The
normal source includes both source and denominator derivatives. -/
theorem source_transport (p : Data K) (D : Derivation ℤ K K)
    (ha : D p.a=0) (hb : D p.b=0) (hc : D p.c=0)
    (hd : D p.d=0) (he : D p.e=0) (hk : D p.k=0)
    (hy : D p.y=1)
    (hu : TransitiveCubic.cubic p.a p.b p.c p.d p.e 0 p.x p.y 1=0)
    (hdn : p.d ≠ 0) (hg : normal p ≠ 0)
    (hH : H p.a p.b p.c p.d p.e 0 p.x p.y 1 ≠ 0)
    (hJ : J p.a p.b p.c p.d p.e 0 p.x p.y 1 ≠ 0) :
    normalDot p/normal p=(aDot p*xi p+bDot p)/(2*eta p^2)-
      (normal p/3)*D (xiDot p/(2*eta p)) := by
  have hjc := jet_curve p hu hg hH
  have hjd := jet_differential p D ha hb hc hd he hk hy hu hg hH
  have hcurve : eta p^2=xi p^3+aWeierstrass p*xi p+bWeierstrass p := by
    have hh := congrArg TrivSqZeroExt.fst hjc
    simpa only [fst_pow,fst_add,fst_mul,xiJet_value,etaJet_value,sJet_value,bJet_value] using hh
  have hcurvejet : 2*eta p*etaDot p=(3*xi p^2+aWeierstrass p)*xiDot p+
      aDot p*xi p+bDot p := by
    have hh := curve_first_variation (xiJet p) (etaJet p) (sJet p) (bWeierstrassJet p) hjc
    simpa only [xiJet_value,etaJet_value,sJet_value,xiDot,etaDot,aDot,bDot] using hh
  have hdiff : normal p*D (xi p)=6*eta p := by
    have hh := congrArg TrivSqZeroExt.fst hjd
    simpa only [fst_mul,fst_numeral,jetDerivation_fst,xiJet_value,etaJet_value,gJet_value] using hh
  have hdiffjet : normal p^2*(2*eta p*D (xiDot p)-2*D (xi p)*etaDot p)=
      -4*eta p^2*3*normalDot p := by
    have hh := differential_first_variation D (xiJet p) (etaJet p) (gJet p) hjd
    simp only [xiJet_value,gJet_value,gJet_dot p hdn hg] at hh
    exact differential_jet_from_cleared (normal p) (eta p) (D (xi p))
      (D (xiDot p)) (etaDot p) (normalDot p) hdiff hh
  have hinvariant : D (xi p)/(2*eta p)=3/normal p := by
    have hn := eta_nonzero p hH hJ
    field_simp
    linear_combination hdiff
  obtain ⟨hDa,hDb⟩ := weierstrass_constants p D ha hb hc hd he
  exact CycleMovingMap.residue_source_from_jet D (xi p) (eta p) (aWeierstrass p)
    (bWeierstrass p) (normal p) 3 (xiDot p) (etaDot p) (aDot p) (bDot p)
    (normalDot p) hg (eta_nonzero p hH hJ) (by norm_num)
    hcurve hDa hDb hinvariant hcurvejet hdiffjet

end MixedPolarCubicSourceJets
#print axioms MixedPolarCubicSourceJets.jet_equation
#print axioms MixedPolarCubicSourceJets.gJet_dot
#print axioms MixedPolarCubicSourceJets.aDot_formula
#print axioms MixedPolarCubicSourceJets.bDot_formula
#print axioms MixedPolarCubicSourceJets.source_transport
