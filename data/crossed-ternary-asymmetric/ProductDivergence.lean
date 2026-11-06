import Proposal.EllipticKernels
import HodgeComputer.Constructions.EllipticCompanions.Contraction

/- Prepared with OpenAI Codex assistance for contributor 1337isnot1337.
See solution.md for the construction, provenance, and prior-work credit. -/

/- Source component: CrossedProductField. -/
section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
namespace CrossedProductField
open Polynomial HoldoutConstruction CrossedFanoElliptic CrossedElliptic
open scoped BigOperators

abbrev Base := MvPolynomial (Fin 4) ℂ
abbrev F := FractionRing Base
local instance : Algebra ℤ F := Ring.toIntAlgebra _

def firstIndex : Fin 2 → Fin 4 := ![0,1]
def secondIndex : Fin 2 → Fin 4 := ![2,3]
def firstMap : P2 →+* F := (algebraMap Base F).comp (MvPolynomial.rename firstIndex).toRingHom
def secondMap : P2 →+* F := (algebraMap Base F).comp (MvPolynomial.rename secondIndex).toRingHom
def p : F := firstMap basePolynomial
def q : F := secondMap basePolynomial

def baseD (i : Fin 4) : Derivation ℤ F F := extendRingDerivation (integerPartial (R:=ℂ) i)
lemma baseD_polynomial (i : Fin 4) (P : Base) :
    baseD i (algebraMap Base F P)=algebraMap Base F (integerPartial i P) := extendRingDerivation_apply _ _

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

lemma basePolynomial_ne_zero : (basePolynomial : P2)≠0 := by
  intro h
  have hh := congrArg (MvPolynomial.eval (fun _ : Fin 2 => (0 : ℂ))) h
  norm_num [basePolynomial] at hh
lemma p_ne_zero : p≠0 := by
  have hi : Function.Injective firstMap := (IsFractionRing.injective Base F).comp
    (MvPolynomial.rename_injective firstIndex firstIndex_injective)
  simpa only [p,map_zero] using hi.ne basePolynomial_ne_zero
lemma q_ne_zero : q≠0 := by
  have hi : Function.Injective secondMap := (IsFractionRing.injective Base F).comp
    (MvPolynomial.rename_injective secondIndex secondIndex_injective)
  simpa only [q,map_zero] using hi.ne basePolynomial_ne_zero

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
lemma u_cube : u^3=phi basePolynomial := by
  have h := Polynomial.eval_rootOfSplits first_cubic_splits (cubic_degree p)
  change ((X^3-C p).map inclusion).eval u=0 at h
  simpa [sub_eq_zero,phi,p,Polynomial.eval_map_apply] using h
lemma v_cube : v^3=psi basePolynomial := by
  have h := Polynomial.eval_rootOfSplits second_cubic_splits (cubic_degree q)
  change ((X^3-C q).map inclusion).eval v=0 at h
  simpa [sub_eq_zero,psi,q,Polynomial.eval_map_apply] using h
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

end CrossedProductField
end
end

/- Source component: CrossedProductPrimitives. -/
section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
namespace CrossedProductField
open Polynomial HoldoutConstruction CrossedFanoElliptic CrossedElliptic
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
lemma DX_v (i : Fin 2) : DX i v=0 := by
  rw [cubic_derivative (DX i) psi v v_cube v_ne_zero,DX_psi,zero_div]
lemma DY_u (i : Fin 2) : DY i u=0 := by
  rw [cubic_derivative (DY i) phi u u_cube u_ne_zero,DY_phi,zero_div]

def alpha : K := coordinates 0^4*coordinates 1/u^4
def beta : K := coordinates 2/v^2
lemma DX_beta (i : Fin 2) : DX i beta=0 := by
  have hr : DX i (coordinates 2)=0 := by fin_cases i <;> simp [DX,D_coordinate]
  simp only [beta,Derivation.leibniz_div,Derivation.leibniz_pow,hr,DX_v,
    smul_eq_mul,smul_zero,mul_zero,zero_mul,sub_self,zero_div]

theorem ordinary_product_divergence : ∃ U : Fin 4 → K,(∑ i,D i (U i))=alpha*beta := by
  obtain ⟨bf,cx,cy,hf,hfk⟩ := first_scalar_primitive phi phi_injective u u_ne_zero u_cube
    (DX 0) (DX 1) (DX_phi_C 0) (DX_phi_C 1) (DX_phi_X 0) (DX_phi_X 1)
  obtain ⟨bg,cr,cz,hg,hgk⟩ := second_scalar_primitive psi psi_injective v v_ne_zero v_cube
    (DY 0) (DY 1) (DY_psi_C 0) (DY_psi_C 1) (DY_psi_X 0) (DY_psi_X 1)
  have hφsrc : (phi (MvPolynomial.X 0))^4*phi (MvPolynomial.X 1)/u^4=alpha := by
    rw [phi_X,phi_X]; rfl
  have hψsrc : psi (MvPolynomial.X 0)/v^2=beta := by rw [psi_X]; rfl
  rw [hφsrc] at hf
  rw [hψsrc] at hg
  have hF : delta bf+∑ i,coefficient (DX i) (![cx,cy] i)=algebraMap K (E K) alpha := by
    simpa only [Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,add_assoc] using hf
  have hB : delta bg+∑ i,coefficient (DY i) (![cr,cz] i)=algebraMap K (E K) beta*thetaRatio := by
    simpa only [Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,add_assoc] using hg
  obtain ⟨ux,uy,he⟩ := product_divergence DX DY alpha beta bf bg ![cx,cy] ![cr,cz] hF hB
    (fun i => (hgk (DX i) (DX_psi i) (DX_v i)).1)
    (fun i => (hfk (DY i) (DY_phi i) (DY_u i)).1) DX_beta
  refine ⟨![ux 0,ux 1,uy 0,uy 1],?_⟩
  simpa [Fin.sum_univ_four,Fin.sum_univ_two,DX,DY,add_assoc] using he

end CrossedProductField
end
end

/- Source component: CrossedWeightedDivergence. -/
section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000
namespace CrossedProductField
open Polynomial HoldoutConstruction CrossedFanoElliptic CrossedElliptic
open scoped BigOperators
local instance : Algebra ℤ F := Ring.toIntAlgebra _
local instance : Algebra ℤ K := Ring.toIntAlgebra _

def weight : K := u^4*v^2
def connection (i : Fin 4) : F := -(4/(3*p))*baseD i p-(2/(3*q))*baseD i q
def source : F := algebraMap Base F (MvPolynomial.X 0^4*MvPolynomial.X 1*MvPolynomial.X 2)

lemma D_u (i : Fin 4) : D i u=inclusion (baseD i p)/(3*u^2) := by
  rw [cubic_derivative (D i) phi u u_cube u_ne_zero]
  change D i (inclusion p)/(3*u^2)=_
  rw [D_base]
lemma D_v (i : Fin 4) : D i v=inclusion (baseD i q)/(3*v^2) := by
  rw [cubic_derivative (D i) psi v v_cube v_ne_zero]
  change D i (inclusion q)/(3*v^2)=_
  rw [D_base]

lemma weight_connection (i : Fin 4) : D i weight+weight*inclusion (connection i)=0 := by
  have hu : u^3=inclusion p := u_cube
  have hv : v^3=inclusion q := v_cube
  simp only [weight,connection,Derivation.leibniz,Derivation.leibniz_pow,D_u,D_v,
    smul_eq_mul,nsmul_eq_mul,map_sub,map_neg,map_mul,map_div₀,map_ofNat,← hu,← hv]
  norm_num only
  field_simp [u_ne_zero,v_ne_zero]
  ring

lemma weighted_source : weight*(alpha*beta)=inclusion source := by
  simp only [weight,alpha,beta,source,map_mul,map_pow,coordinates]
  field_simp [u_ne_zero,v_ne_zero]

theorem weighted_divergence : ∃ W : Fin 4 → F,
    (∑ i,(baseD i (W i)+W i*connection i))=source := by
  obtain ⟨U,hU⟩ := ordinary_product_divergence
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

end CrossedProductField
end
end
