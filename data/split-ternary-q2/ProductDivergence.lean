import Proposal.CertificateClearing
import HodgeComputer.Constructions.EllipticCompanions.Contraction

/-!
Target-specific product and weighted descent for split-ternary-q2, conditional
on two supplied companion scalar primitives. The algebraic assembly adapts the
accepted crossed-ternary construction of 1337isnot1337 (PR #149), whose generic
elliptic contraction is imported from the maintained library.
Prepared with OpenAI Codex assistance for contributor fqlx.
No primitive existence is asserted by this conditional assembly.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
namespace SplitTernaryProduct
open Polynomial HoldoutConstruction CrossedElliptic
open scoped BigOperators

abbrev Base := SplitTernaryPhysical.Base
abbrev F := SplitTernaryPhysical.BaseField
abbrev P2 := MvPolynomial (Fin 2) ℂ
local instance : Algebra ℤ F := Ring.toIntAlgebra _
abbrev p := SplitTernaryPhysical.p
abbrev q := SplitTernaryPhysical.q
abbrev baseD := SplitTernaryPhysical.baseD
abbrev baseD_polynomial := SplitTernaryPhysical.baseD_polynomial

def firstIndex : Fin 2 → Fin 4 := ![0,1]
def secondIndex : Fin 2 → Fin 4 := ![2,3]
def firstMap : P2 →+* F := (algebraMap Base F).comp (MvPolynomial.rename firstIndex).toRingHom
def secondMap : P2 →+* F := (algebraMap Base F).comp (MvPolynomial.rename secondIndex).toRingHom

def rootsPolynomial : F[X] := (X^3-C p)*(X^3-C q)
abbrev K := rootsPolynomial.SplittingField
local instance : Algebra ℤ K := Ring.toIntAlgebra _
def inclusion : F →+* K := algebraMap F K
def coordinates (i : Fin 4) : K := inclusion (algebraMap Base F (MvPolynomial.X i))
def phi : P2 →+* K := inclusion.comp firstMap
def psi : P2 →+* K := inclusion.comp secondMap

def D (i : Fin 4) : Derivation ℤ K K := extendFiniteDerivation (baseD i)
lemma D_base (i : Fin 4) (c : F) : D i (inclusion c)=inclusion (baseD i c) := extendFiniteDerivation_apply _ _
lemma D_polynomial (i : Fin 4) (P : Base) :
    D i (inclusion (algebraMap Base F P))=inclusion (algebraMap Base F (integerPartial i P)) := by
  rw [D_base,baseD_polynomial]
lemma D_C (i : Fin 4) (c : ℂ) : D i (inclusion (algebraMap Base F (MvPolynomial.C c)))=0 := by
  rw [D_polynomial,integerPartial_C,map_zero,map_zero]
lemma D_coordinate (i j : Fin 4) : D i (coordinates j)=if j=i then 1 else 0 := by
  rw [coordinates,D_polynomial]
  by_cases he : j=i
  · subst j; rw [integerPartial_X_self,map_one,map_one,if_pos rfl]
  · rw [integerPartial_X_of_ne _ _ he,map_zero,map_zero,if_neg he]

lemma firstIndex_injective : Function.Injective firstIndex := by intro i j h; fin_cases i <;> fin_cases j <;> simp_all [firstIndex]
lemma secondIndex_injective : Function.Injective secondIndex := by intro i j h; fin_cases i <;> fin_cases j <;> simp_all [secondIndex]
lemma phi_injective : Function.Injective phi := inclusion.injective.comp
  ((IsFractionRing.injective Base F).comp (MvPolynomial.rename_injective firstIndex firstIndex_injective))
lemma psi_injective : Function.Injective psi := inclusion.injective.comp
  ((IsFractionRing.injective Base F).comp (MvPolynomial.rename_injective secondIndex secondIndex_injective))
lemma phi_C (c : ℂ) : phi (MvPolynomial.C c)=inclusion (algebraMap Base F (MvPolynomial.C c)) := by
  simp [phi,firstMap]
lemma psi_C (c : ℂ) : psi (MvPolynomial.C c)=inclusion (algebraMap Base F (MvPolynomial.C c)) := by
  simp [psi,secondMap]
lemma phi_X (i : Fin 2) : phi (MvPolynomial.X i)=coordinates (firstIndex i) := by
  simp [phi,firstMap,coordinates]
lemma psi_X (i : Fin 2) : psi (MvPolynomial.X i)=coordinates (secondIndex i) := by
  simp [psi,secondMap,coordinates]

lemma p_ne_zero : p≠0 := SplitTernaryPhysical.p_ne_zero
lemma q_ne_zero : q≠0 := SplitTernaryPhysical.q_ne_zero

lemma first_cubic_splits : ((X^3-C p).map inclusion).Splits := by
  have hs := IsSplittingField.splits K rootsPolynomial
  change (((X^3-C p)*(X^3-C q)).map (algebraMap F K)).Splits at hs
  rw [Polynomial.map_mul] at hs
  exact hs.of_dvd (mul_ne_zero
    (Polynomial.map_ne_zero (monic_X_pow_sub_C p (by decide : (3 : ℕ)≠0)).ne_zero)
    (Polynomial.map_ne_zero (monic_X_pow_sub_C q (by decide : (3 : ℕ)≠0)).ne_zero)) (dvd_mul_right _ _)
lemma second_cubic_splits : ((X^3-C q).map inclusion).Splits := by
  have hs := IsSplittingField.splits K rootsPolynomial
  change (((X^3-C p)*(X^3-C q)).map (algebraMap F K)).Splits at hs
  rw [Polynomial.map_mul] at hs
  exact hs.of_dvd (mul_ne_zero
    (Polynomial.map_ne_zero (monic_X_pow_sub_C p (by decide : (3 : ℕ)≠0)).ne_zero)
    (Polynomial.map_ne_zero (monic_X_pow_sub_C q (by decide : (3 : ℕ)≠0)).ne_zero)) (dvd_mul_left _ _)
lemma cubic_degree (c : F) : ((X^3-C c).map inclusion).degree≠0 := by
  simp only [Polynomial.map_sub,Polynomial.map_pow,Polynomial.map_X,Polynomial.map_C]
  rw [degree_X_pow_sub_C (by decide : 0<3)]
  norm_num

def u : K := Polynomial.rootOfSplits first_cubic_splits (cubic_degree p)
def v : K := Polynomial.rootOfSplits second_cubic_splits (cubic_degree q)
lemma u_cube : u^3=inclusion p := by
  have h := Polynomial.eval_rootOfSplits first_cubic_splits (cubic_degree p)
  change ((X^3-C p).map inclusion).eval u=0 at h
  simpa [sub_eq_zero,Polynomial.eval_map_apply] using h
lemma v_cube : v^3=inclusion q := by
  have h := Polynomial.eval_rootOfSplits second_cubic_splits (cubic_degree q)
  change ((X^3-C q).map inclusion).eval v=0 at h
  simpa [sub_eq_zero,Polynomial.eval_map_apply] using h
lemma u_ne_zero : u≠0 := by
  intro hu
  have h := u_cube
  rw [hu,zero_pow (by decide : (3 : ℕ)≠0)] at h
  exact (_root_.map_ne_zero inclusion).mpr p_ne_zero h.symm
lemma v_ne_zero : v≠0 := by
  intro hv
  have h := v_cube
  rw [hv,zero_pow (by decide : (3 : ℕ)≠0)] at h
  exact (_root_.map_ne_zero inclusion).mpr q_ne_zero h.symm

end SplitTernaryProduct
end

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace SplitTernaryProduct
open Polynomial HoldoutConstruction CrossedElliptic
open scoped BigOperators
local instance : Algebra ℤ K := Ring.toIntAlgebra _

def DX : Fin 2 → Derivation ℤ K K := ![D 0,D 1]
def DY : Fin 2 → Derivation ℤ K K := ![D 2,D 3]
lemma DX_phi_C (i : Fin 2) (c : ℂ) : DX i (phi (MvPolynomial.C c))=0 := by
  rw [phi_C]
  fin_cases i <;> exact D_C _ c
lemma DY_psi_C (i : Fin 2) (c : ℂ) : DY i (psi (MvPolynomial.C c))=0 := by
  rw [psi_C]
  fin_cases i <;> exact D_C _ c
lemma DX_phi_X (i j : Fin 2) : DX i (phi (MvPolynomial.X j))=if j=i then 1 else 0 := by
  rw [phi_X]
  fin_cases i <;> fin_cases j <;> simp [DX,firstIndex,D_coordinate]
lemma DY_psi_X (i j : Fin 2) : DY i (psi (MvPolynomial.X j))=if j=i then 1 else 0 := by
  rw [psi_X]
  fin_cases i <;> fin_cases j <;> simp [DY,secondIndex,D_coordinate]

lemma polynomialMap_eval₂ (φ : P2 →+* K) :
    φ=MvPolynomial.eval₂Hom (φ.comp MvPolynomial.C) (fun i => φ (MvPolynomial.X i)) := by
  apply MvPolynomial.ringHom_ext
  · intro c; rw [MvPolynomial.eval₂Hom_C]; rfl
  · intro i; rw [MvPolynomial.eval₂Hom_X']
lemma DX_psi (i : Fin 2) (P : P2) : DX i (psi P)=0 := by
  have hc (c : ℂ) : DX i (psi (MvPolynomial.C c))=0 := by
    rw [psi_C]; fin_cases i <;> exact D_C _ c
  have hx (j : Fin 2) : DX i (psi (MvPolynomial.X j))=0 := by
    rw [psi_X]; fin_cases i <;> fin_cases j <;> simp [DX,secondIndex,D_coordinate]
  have h := derivation_eval₂_chain (DX i) (psi.comp MvPolynomial.C) (fun j => psi (MvPolynomial.X j)) hc P
  rw [← polynomialMap_eval₂ psi] at h
  simpa only [hx,mul_zero,Finset.sum_const_zero] using h
lemma DY_phi (i : Fin 2) (P : P2) : DY i (phi P)=0 := by
  have hc (c : ℂ) : DY i (phi (MvPolynomial.C c))=0 := by
    rw [phi_C]; fin_cases i <;> exact D_C _ c
  have hx (j : Fin 2) : DY i (phi (MvPolynomial.X j))=0 := by
    rw [phi_X]; fin_cases i <;> fin_cases j <;> simp [DY,firstIndex,D_coordinate]
  have h := derivation_eval₂_chain (DY i) (phi.comp MvPolynomial.C) (fun j => phi (MvPolynomial.X j)) hc P
  rw [← polynomialMap_eval₂ phi] at h
  simpa only [hx,mul_zero,Finset.sum_const_zero] using h

lemma D_u (i : Fin 4) : D i u=inclusion (baseD i p)/(3*u^2) := by
  have he := congrArg (D i) u_cube
  simp only [Derivation.leibniz_pow,smul_eq_mul,nsmul_eq_mul,D_base] at he
  field_simp [u_ne_zero]
  linear_combination he
lemma D_v (i : Fin 4) : D i v=inclusion (baseD i q)/(3*v^2) := by
  have he := congrArg (D i) v_cube
  simp only [Derivation.leibniz_pow,smul_eq_mul,nsmul_eq_mul,D_base] at he
  field_simp [v_ne_zero]
  linear_combination he

def firstPolynomial : P2 := SplitTernaryPhysical.leftTernary (MvPolynomial.C (5/7 : ℂ))
  (MvPolynomial.X 0) (MvPolynomial.X 1) 1
def secondPolynomial : P2 := SplitTernaryPhysical.rightTernary (MvPolynomial.C (5/7 : ℂ))
  (MvPolynomial.X 0) (MvPolynomial.X 1) 1
lemma phi_p : phi firstPolynomial=inclusion p := by
  simp [phi,firstMap,firstPolynomial,SplitTernaryPhysical.p,SplitTernaryPhysical.pPolynomial,
    SplitTernaryPhysical.leftTernary,firstIndex,map_ofNat]
lemma psi_q : psi secondPolynomial=inclusion q := by
  simp [psi,secondMap,secondPolynomial,SplitTernaryPhysical.q,SplitTernaryPhysical.qPolynomial,
    SplitTernaryPhysical.rightTernary,secondIndex,map_ofNat]
lemma DX_v (i : Fin 2) : DX i v=0 := by
  have he := congrArg (DX i) v_cube
  rw [← psi_q,DX_psi] at he
  simp only [Derivation.leibniz_pow,smul_eq_mul,nsmul_eq_mul] at he
  have h3 : (3 : K)≠0 := by norm_num
  have he' : (3*v^2)*DX i v=0 := by simpa only [Nat.reduceSub,Nat.cast_ofNat,← mul_assoc] using he
  exact (mul_eq_zero.mp he').resolve_left (mul_ne_zero h3 (pow_ne_zero 2 v_ne_zero))
lemma DY_u (i : Fin 2) : DY i u=0 := by
  have he := congrArg (DY i) u_cube
  rw [← phi_p,DY_phi] at he
  simp only [Derivation.leibniz_pow,smul_eq_mul,nsmul_eq_mul] at he
  have h3 : (3 : K)≠0 := by norm_num
  have he' : (3*u^2)*DY i u=0 := by simpa only [Nat.reduceSub,Nat.cast_ofNat,← mul_assoc] using he
  exact (mul_eq_zero.mp he').resolve_left (mul_ne_zero h3 (pow_ne_zero 2 u_ne_zero))

def alpha : K := coordinates 0^4*coordinates 1^3/u^5
def beta : K := coordinates 2^3*coordinates 3^2/v^4
lemma DY_alpha (i : Fin 2) : DY i alpha=0 := by
  have hx : DY i (coordinates 0)=0 := by fin_cases i <;> simp [DY,D_coordinate]
  have ha : DY i (coordinates 1)=0 := by fin_cases i <;> simp [DY,D_coordinate]
  simp [alpha,Derivation.leibniz_div,Derivation.leibniz,Derivation.leibniz_pow,hx,ha,DY_u]

/-- The ordinary primitive supplied by the second companion. Its preservation
clause is stated for arbitrary derivations killing that block and its root. -/
def OrdinaryPrimitive : Prop :=
  ∃ bf cr cz : E K,
    (delta bf+coefficient (DY 0) cr+coefficient (DY 1) cz=algebraMap K (E K) beta) ∧
    ∀ Z : Derivation ℤ K K,(∀ P : P2,Z (psi P)=0) → Z v=0 →
      coefficient Z bf=0 ∧ coefficient Z cr=0 ∧ coefficient Z cz=0

/-- The theta primitive supplied by the first, higher-pole companion. -/
def ThetaPrimitive : Prop :=
  ∃ bg cx ca : E K,
    (delta bg+coefficient (DX 0) cx+coefficient (DX 1) ca=algebraMap K (E K) alpha*thetaRatio) ∧
    ∀ Z : Derivation ℤ K K,(∀ P : P2,Z (phi P)=0) → Z u=0 →
      coefficient Z bg=0 ∧ coefficient Z cx=0 ∧ coefficient Z ca=0

theorem ordinary_product_divergence (hOrdinary : OrdinaryPrimitive) (hTheta : ThetaPrimitive) :
    ∃ U : Fin 4 → K,(∑ i,D i (U i))=alpha*beta := by
  obtain ⟨bf,cr,cz,hf,hfk⟩ := hOrdinary
  obtain ⟨bg,cx,ca,hg,hgk⟩ := hTheta
  have hF : delta bf+∑ i,coefficient (DY i) (![cr,cz] i)=algebraMap K (E K) beta := by
    simpa only [Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,add_assoc] using hf
  have hB : delta bg+∑ i,coefficient (DX i) (![cx,ca] i)=algebraMap K (E K) alpha*thetaRatio := by
    simpa only [Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,add_assoc] using hg
  obtain ⟨uy,ux,he⟩ := product_divergence DY DX beta alpha bf bg ![cr,cz] ![cx,ca] hF hB
    (fun i => (hgk (DY i) (DY_phi i) (DY_u i)).1)
    (fun i => (hfk (DX i) (DX_psi i) (DX_v i)).1) DY_alpha
  refine ⟨![ux 0,ux 1,uy 0,uy 1],?_⟩
  simpa [Fin.sum_univ_four,Fin.sum_univ_two,DX,DY,add_assoc,add_comm,add_left_comm,mul_comm] using he

end SplitTernaryProduct
end

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace SplitTernaryProduct
open Polynomial HoldoutConstruction CrossedElliptic
open scoped BigOperators
local instance : Algebra ℤ F := Ring.toIntAlgebra _
local instance : Algebra ℤ K := Ring.toIntAlgebra _

abbrev source := SplitTernaryPhysical.source
def weight : K := u^5*v^4
def connection (i : Fin 4) : F := -(5/(3*p))*baseD i p-(4/(3*q))*baseD i q

lemma weight_connection (i : Fin 4) : D i weight+weight*inclusion (connection i)=0 := by
  have hu : u^3=inclusion p := u_cube
  have hv : v^3=inclusion q := v_cube
  simp only [weight,connection,Derivation.leibniz,Derivation.leibniz_pow,D_u,D_v,
    smul_eq_mul,nsmul_eq_mul,map_sub,map_neg,map_mul,map_div₀,map_ofNat,← hu,← hv]
  norm_num only
  field_simp [u_ne_zero,v_ne_zero]
  ring

lemma weighted_source : weight*(alpha*beta)=inclusion source := by
  simp only [weight,alpha,beta,SplitTernaryPhysical.source,SplitTernaryPhysical.sourcePolynomial,
    map_mul,map_pow,coordinates]
  field_simp [u_ne_zero,v_ne_zero]

theorem weighted_divergence_with_connection (hOrdinary : OrdinaryPrimitive) (hTheta : ThetaPrimitive) :
    ∃ W : Fin 4 → F,(∑ i,(baseD i (W i)+W i*connection i))=source := by
  obtain ⟨U,hU⟩ := ordinary_product_divergence hOrdinary hTheta
  let V : Fin 4 → K := fun i => weight*U i
  have hV (i : Fin 4) : D i (V i)+V i*inclusion (connection i)=weight*D i (U i) := by
    dsimp [V]
    rw [Derivation.leibniz]
    simp only [smul_eq_mul]
    linear_combination U i*weight_connection i
  have he : (∑ i,(D i (V i)+V i*algebraMap F K (connection i)))=algebraMap F K source := by
    change (∑ i,(D i (V i)+V i*inclusion (connection i)))=inclusion source
    rw [Finset.sum_congr rfl (fun i _ => hV i)]
    rw [← Finset.mul_sum,hU,weighted_source]
  refine ⟨fun i => Algebra.normalizedTrace F K (V i),?_⟩
  exact finiteNormalizedTrace_firstOrder baseD D D_base connection source V he

/-- The precise weighted identity consumed by physical transport and clearing. -/
theorem weighted_divergence (hOrdinary : OrdinaryPrimitive) (hTheta : ThetaPrimitive) :
    ∃ W : Fin 4 → F,
      (∑ i,baseD i (W i))-5*SplitTernaryPhysical.directionalP W/(3*p)-
        4*SplitTernaryPhysical.directionalQ W/(3*q)=source := by
  obtain ⟨W,hW⟩ := weighted_divergence_with_connection hOrdinary hTheta
  refine ⟨W,?_⟩
  have hsum : (∑ i,W i*connection i)=
      -5*SplitTernaryPhysical.directionalP W/(3*p)-4*SplitTernaryPhysical.directionalQ W/(3*q) := by
    calc
      _=(∑ i,((-(5/(3*p)))*(W i*baseD i p)+(-(4/(3*q)))*(W i*baseD i q))) := by
        apply Finset.sum_congr rfl
        intro i _
        unfold connection
        ring
      _=(-(5/(3*p)))*(∑ i,W i*baseD i p)+(-(4/(3*q)))*(∑ i,W i*baseD i q) := by
        rw [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum]
      _=_ := by unfold SplitTernaryPhysical.directionalP SplitTernaryPhysical.directionalQ; ring
  rw [Finset.sum_add_distrib,hsum] at hW
  linear_combination hW

/-- Conditional assembly: the two actual companion primitives are the only
remaining existence inputs; no such primitives are asserted here. -/
theorem certificate_of_companion_primitives (hOrdinary : OrdinaryPrimitive) (hTheta : ThetaPrimitive) :
    HodgeComputer.HasCertificate SplitTernaryPhysical.physicalF SplitTernaryPhysical.physicalA 2 := by
  obtain ⟨W,hW⟩ := weighted_divergence hOrdinary hTheta
  exact SplitTernaryPhysical.physical_certificate_of_weighted_divergence W hW

end SplitTernaryProduct
end

#print axioms SplitTernaryProduct.weighted_divergence
#print axioms SplitTernaryProduct.certificate_of_companion_primitives
