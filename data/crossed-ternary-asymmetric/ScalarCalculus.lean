import HodgeComputer.Constructions.EllipticCompanions.Calculus
import Proposal.CompanionPrimitives
import HodgeComputer.Constructions.HoldoutCover.PolynomialCalculus
import HodgeComputer.Constructions.HoldoutCover.ResidueClearing
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Tactic

/- Prepared with OpenAI Codex assistance for contributor 1337isnot1337.
See solution.md for the construction, provenance, and prior-work credit. -/

/- Source component: FanoEllipticCalculus. -/
section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
namespace CrossedFanoElliptic
open HoldoutConstruction CrossedElliptic CrossedConicIncidence
open scoped BigOperators
variable {K : Type*} [Field K] [CharZero K]
local instance : Algebra ℤ (E K) := Ring.toIntAlgebra _

abbrev P2 := MvPolynomial (Fin 2) ℂ
abbrev P4 := MvPolynomial (Fin 4) ℂ

def swap : Fin 4 → Fin 4 := ![1,0,2,3]
def ambientD (i : Fin 4) : Derivation ℤ P4 P4 := integerPartial (swap i)
def baseGradient (φ : P2 →+* K) (i : Fin 2) : K := φ (integerPartial i basePolynomial)

lemma evaluation_eq_eval₂ (φ : P2 →+* K) (u : K) (hu : u^3=φ basePolynomial) :
    evaluation φ u hu=MvPolynomial.eval₂Hom ((algebraMap K (E K)).comp (φ.comp MvPolynomial.C))
      ![algebraMap K (E K) (φ (MvPolynomial.X 1)),algebraMap K (E K) (φ (MvPolynomial.X 0)),
        algebraMap K (E K) u*a (K:=K),algebraMap K (E K) u*b (K:=K)] := by
  apply MvPolynomial.ringHom_ext
  · intro c; rw [MvPolynomial.eval₂Hom_C]; exact evaluation_C φ u hu c
  · intro i; rw [evaluation_X,MvPolynomial.eval₂Hom_X']

lemma evaluation_chain (φ : P2 →+* K) (u : K) (hu : u^3=φ basePolynomial)
    (D : Derivation ℤ (E K) (E K))
    (hc : ∀ c,D (algebraMap K (E K) (φ (MvPolynomial.C c)))=0) (p : P4) :
    D (evaluation φ u hu p)=∑ i,evaluation φ u hu (ambientD i p)*
      D (![algebraMap K (E K) (φ (MvPolynomial.X 0)),algebraMap K (E K) (φ (MvPolynomial.X 1)),
        algebraMap K (E K) u*a (K:=K),algebraMap K (E K) u*b (K:=K)] i) := by
  rw [evaluation_eq_eval₂]
  have hh := derivation_eval₂_chain D ((algebraMap K (E K)).comp (φ.comp MvPolynomial.C))
    ![algebraMap K (E K) (φ (MvPolynomial.X 1)),algebraMap K (E K) (φ (MvPolynomial.X 0)),
      algebraMap K (E K) u*a (K:=K),algebraMap K (E K) u*b (K:=K)] hc p
  rw [hh]
  simp [Fin.sum_univ_four,ambientD,swap,integerPartial_apply]
  ring

lemma evaluated_gradient (φ : P2 →+* K) (u : K) (hu : u^3=φ basePolynomial) (i : Fin 4) :
    evaluation φ u hu (ambientD i CrossedFanoAffineData.equation)=7*
      ![algebraMap K (E K) (baseGradient φ 0),algebraMap K (E K) (baseGradient φ 1),
        3*(algebraMap K (E K) u)^2*a (K:=K)^2,
        3*(algebraMap K (E K) u)^2*b (K:=K)^2] i := by
  have hc (n : ℕ) : evaluation φ u hu (n : P4)=(n : E K) := map_natCast _ n
  have hcφ (n : ℕ) : φ (n : P2)=(n : K) := map_natCast _ n
  have hcK (n : ℕ) : algebraMap K (E K) (n : K)=(n : E K) := map_natCast _ n
  have hq : algebraMap K (E K) (φ (MvPolynomial.C (5/7 : ℂ)))=(5/7 : E K) := by
    have h := map_ratCast ((algebraMap K (E K)).comp (φ.comp MvPolynomial.C)) (5/7 : ℚ)
    norm_num only [Rat.cast_div,Rat.cast_ofNat] at h
    exact h
  have hz2 (j : Fin 4) : MvPolynomial.pderiv (R:=ℂ) j (2 : P4)=0 := (MvPolynomial.pderiv j).map_natCast 2
  have hb2 (j : Fin 2) : MvPolynomial.pderiv (R:=ℂ) j (2 : P2)=0 := (MvPolynomial.pderiv j).map_natCast 2
  have hz3 (j : Fin 4) : MvPolynomial.pderiv (R:=ℂ) j (3 : P4)=0 := (MvPolynomial.pderiv j).map_natCast 3
  have hb3 (j : Fin 2) : MvPolynomial.pderiv (R:=ℂ) j (3 : P2)=0 := (MvPolynomial.pderiv j).map_natCast 3
  have hz5 (j : Fin 4) : MvPolynomial.pderiv (R:=ℂ) j (5 : P4)=0 := (MvPolynomial.pderiv j).map_natCast 5
  have hb5 (j : Fin 2) : MvPolynomial.pderiv (R:=ℂ) j (5 : P2)=0 := (MvPolynomial.pderiv j).map_natCast 5
  have hz6 (j : Fin 4) : MvPolynomial.pderiv (R:=ℂ) j (6 : P4)=0 := (MvPolynomial.pderiv j).map_natCast 6
  have hb6 (j : Fin 2) : MvPolynomial.pderiv (R:=ℂ) j (6 : P2)=0 := (MvPolynomial.pderiv j).map_natCast 6
  have hz7 (j : Fin 4) : MvPolynomial.pderiv (R:=ℂ) j (7 : P4)=0 := (MvPolynomial.pderiv j).map_natCast 7
  have hb7 (j : Fin 2) : MvPolynomial.pderiv (R:=ℂ) j (7 : P2)=0 := (MvPolynomial.pderiv j).map_natCast 7
  fin_cases i <;>
    simp [ambientD,swap,CrossedFanoAffineData.equation,H,baseGradient,basePolynomial,
      integerPartial_apply,MvPolynomial.pderiv_mul,Derivation.leibniz_pow,smul_eq_mul,
      evaluation_X,evaluation_C,hc,hcφ,hcK,hq,map_ofNat,hz2,hz3,hz5,hz6,hz7,hb2,hb3,hb5,hb6,hb7] <;> ring

lemma evaluated_hessian_S (φ : P2 →+* K) (u : K) (hu : u^3=φ basePolynomial) (i : Fin 4) :
    evaluation φ u hu (ambientD 2 (ambientD i CrossedFanoAffineData.equation))=
      ![0,0,42*algebraMap K (E K) u*a (K:=K),0] i := by
  have hc (n : ℕ) : evaluation φ u hu (n : P4)=(n : E K) := map_natCast _ n
  have hz2 (j : Fin 4) : MvPolynomial.pderiv (R:=ℂ) j (2 : P4)=0 := (MvPolynomial.pderiv j).map_natCast 2
  have hb2 (j : Fin 2) : MvPolynomial.pderiv (R:=ℂ) j (2 : P2)=0 := (MvPolynomial.pderiv j).map_natCast 2
  have hz3 (j : Fin 4) : MvPolynomial.pderiv (R:=ℂ) j (3 : P4)=0 := (MvPolynomial.pderiv j).map_natCast 3
  have hb3 (j : Fin 2) : MvPolynomial.pderiv (R:=ℂ) j (3 : P2)=0 := (MvPolynomial.pderiv j).map_natCast 3
  have hz5 (j : Fin 4) : MvPolynomial.pderiv (R:=ℂ) j (5 : P4)=0 := (MvPolynomial.pderiv j).map_natCast 5
  have hb5 (j : Fin 2) : MvPolynomial.pderiv (R:=ℂ) j (5 : P2)=0 := (MvPolynomial.pderiv j).map_natCast 5
  have hz6 (j : Fin 4) : MvPolynomial.pderiv (R:=ℂ) j (6 : P4)=0 := (MvPolynomial.pderiv j).map_natCast 6
  have hb6 (j : Fin 2) : MvPolynomial.pderiv (R:=ℂ) j (6 : P2)=0 := (MvPolynomial.pderiv j).map_natCast 6
  have hz7 (j : Fin 4) : MvPolynomial.pderiv (R:=ℂ) j (7 : P4)=0 := (MvPolynomial.pderiv j).map_natCast 7
  have hb7 (j : Fin 2) : MvPolynomial.pderiv (R:=ℂ) j (7 : P2)=0 := (MvPolynomial.pderiv j).map_natCast 7
  fin_cases i <;>
    simp [ambientD,swap,CrossedFanoAffineData.equation,H,integerPartial_apply,
      MvPolynomial.pderiv_mul,Derivation.leibniz_pow,smul_eq_mul,evaluation_X,hc,map_ofNat,hz2,hz3,hz5,hz6,hz7,hb2,hb3,hb5,hb6,hb7] <;> ring

lemma evaluated_hessian_T (φ : P2 →+* K) (u : K) (hu : u^3=φ basePolynomial) (i : Fin 4) :
    evaluation φ u hu (ambientD 3 (ambientD i CrossedFanoAffineData.equation))=
      ![0,0,0,42*algebraMap K (E K) u*b (K:=K)] i := by
  have hc (n : ℕ) : evaluation φ u hu (n : P4)=(n : E K) := map_natCast _ n
  have hz2 (j : Fin 4) : MvPolynomial.pderiv (R:=ℂ) j (2 : P4)=0 := (MvPolynomial.pderiv j).map_natCast 2
  have hb2 (j : Fin 2) : MvPolynomial.pderiv (R:=ℂ) j (2 : P2)=0 := (MvPolynomial.pderiv j).map_natCast 2
  have hz3 (j : Fin 4) : MvPolynomial.pderiv (R:=ℂ) j (3 : P4)=0 := (MvPolynomial.pderiv j).map_natCast 3
  have hb3 (j : Fin 2) : MvPolynomial.pderiv (R:=ℂ) j (3 : P2)=0 := (MvPolynomial.pderiv j).map_natCast 3
  have hz5 (j : Fin 4) : MvPolynomial.pderiv (R:=ℂ) j (5 : P4)=0 := (MvPolynomial.pderiv j).map_natCast 5
  have hb5 (j : Fin 2) : MvPolynomial.pderiv (R:=ℂ) j (5 : P2)=0 := (MvPolynomial.pderiv j).map_natCast 5
  have hz6 (j : Fin 4) : MvPolynomial.pderiv (R:=ℂ) j (6 : P4)=0 := (MvPolynomial.pderiv j).map_natCast 6
  have hb6 (j : Fin 2) : MvPolynomial.pderiv (R:=ℂ) j (6 : P2)=0 := (MvPolynomial.pderiv j).map_natCast 6
  have hz7 (j : Fin 4) : MvPolynomial.pderiv (R:=ℂ) j (7 : P4)=0 := (MvPolynomial.pderiv j).map_natCast 7
  have hb7 (j : Fin 2) : MvPolynomial.pderiv (R:=ℂ) j (7 : P2)=0 := (MvPolynomial.pderiv j).map_natCast 7
  fin_cases i <;>
    simp [ambientD,swap,CrossedFanoAffineData.equation,H,integerPartial_apply,
      MvPolynomial.pderiv_mul,Derivation.leibniz_pow,smul_eq_mul,evaluation_X,hc,map_ofNat,hz2,hz3,hz5,hz6,hz7,hb2,hb3,hb5,hb6,hb7] <;> ring

lemma base_chain (φ : P2 →+* K) (D : Derivation ℤ K K)
    (hc : ∀ c,D (φ (MvPolynomial.C c))=0)
    (hx : ∀ i : Fin 2,D (φ (MvPolynomial.X i))=if i=0 then 1 else 0) :
    D (φ basePolynomial)=baseGradient φ 0 := by
  have he : φ=MvPolynomial.eval₂Hom (φ.comp MvPolynomial.C) (fun i => φ (MvPolynomial.X i)) := by
    apply MvPolynomial.ringHom_ext
    · intro c; rw [MvPolynomial.eval₂Hom_C]; rfl
    · intro i; rw [MvPolynomial.eval₂Hom_X']
  have h := derivation_eval₂_chain D (φ.comp MvPolynomial.C) (fun i => φ (MvPolynomial.X i)) hc basePolynomial
  rw [← he] at h
  simpa [Fin.sum_univ_succ,hx,baseGradient,integerPartial_apply] using h

lemma base_chain_at (φ : P2 →+* K) (D : Derivation ℤ K K) (j : Fin 2)
    (hc : ∀ c,D (φ (MvPolynomial.C c))=0)
    (hx : ∀ i : Fin 2,D (φ (MvPolynomial.X i))=if i=j then 1 else 0) :
    D (φ basePolynomial)=baseGradient φ j := by
  have he : φ=MvPolynomial.eval₂Hom (φ.comp MvPolynomial.C) (fun i => φ (MvPolynomial.X i)) := by
    apply MvPolynomial.ringHom_ext
    · intro c; rw [MvPolynomial.eval₂Hom_C]; rfl
    · intro i; rw [MvPolynomial.eval₂Hom_X']
  have h := derivation_eval₂_chain D (φ.comp MvPolynomial.C) (fun i => φ (MvPolynomial.X i)) hc basePolynomial
  rw [← he] at h
  simpa [hx,baseGradient,integerPartial_apply] using h

lemma cubic_derivative (D : Derivation ℤ K K) (φ : P2 →+* K) (u : K)
    (hu : u^3=φ basePolynomial) (hu0 : u≠0) :
    D u=D (φ basePolynomial)/(3*u^2) := by
  have h := congrArg D hu
  simp only [Derivation.leibniz_pow,smul_eq_mul,nsmul_eq_mul] at h
  norm_num only at h
  apply (eq_div_iff (mul_ne_zero (by norm_num) (pow_ne_zero _ hu0))).mpr
  linear_combination h

end CrossedFanoElliptic
end
end

/- Source component: FanoScalarPrimitive. -/
section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
namespace CrossedFanoElliptic
open HoldoutConstruction CrossedElliptic CrossedEvaluatedJets CrossedScalarCompanionJet
open scoped BigOperators
variable {K : Type*} [Field K] [CharZero K]
local instance : Algebra ℤ (E K) := Ring.toIntAlgebra _

lemma data_reindex (A D N₀ : P4) (N : Fin 3 → P4)
    (hn : N₀*integerPartial 0 CrossedFanoAffineData.equation+
      ∑ i,N i*integerPartial i.succ CrossedFanoAffineData.equation=A*D) :
    (∑ i,![N 0,N₀,N 1,N 2] i*ambientD i CrossedFanoAffineData.equation)=A*D := by
  simp [Fin.sum_univ_four,Fin.sum_univ_succ,ambientD,swap] at hn ⊢
  linear_combination hn

lemma divergence_reindex (D N₀ : P4) (N : Fin 3 → P4) :
    D*(∑ i,ambientD i (![N 0,N₀,N 1,N 2] i))-
      (∑ i,![N 0,N₀,N 1,N 2] i*ambientD i D)=
    residueDivNum (integerPartial 0) (fun i : Fin 3 => integerPartial i.succ) D N₀ N := by
  simp [Fin.sum_univ_four,Fin.sum_univ_succ,ambientD,swap,residueDivNum]
  ring

lemma delta_evaluation_chain (φ : P2 →+* K) (u : K) (hu : u^3=φ basePolynomial) (p : P4) :
    delta (evaluation φ u hu p)=∑ j,evaluation φ u hu (ambientD j p)*
      ![0,0,algebraMap K (E K) u*b (K:=K)^2,-(algebraMap K (E K) u)*a (K:=K)^2] j := by
  rw [evaluation_chain φ u hu delta (fun _ => delta_base _) p]
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  fin_cases i <;> simp [delta_base,Derivation.leibniz,delta_a,delta_b,smul_eq_mul]

lemma coefficient_evaluation_chain (φ : P2 →+* K) (u : K) (hu : u^3=φ basePolynomial)
    (hu0 : u≠0) (D : Derivation ℤ K K) (j : Fin 2)
    (hc : ∀ c,D (φ (MvPolynomial.C c))=0)
    (hx : ∀ i : Fin 2,D (φ (MvPolynomial.X i))=if i=j then 1 else 0) (p : P4) :
    coefficient D (evaluation φ u hu p)=∑ i,evaluation φ u hu (ambientD i p)*
      ![if j=0 then 1 else 0,if j=1 then 1 else 0,
        algebraMap K (E K) (baseGradient φ j)/(3*(algebraMap K (E K) u)^2)*a (K:=K),
        algebraMap K (E K) (baseGradient φ j)/(3*(algebraMap K (E K) u)^2)*b (K:=K)] i := by
  have du := cubic_derivative D φ u hu hu0
  rw [base_chain_at φ D j hc hx] at du
  rw [evaluation_chain φ u hu (coefficient D) (by intro c; rw [coefficient_scalar,hc,map_zero]) p]
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  fin_cases i <;>
    simp [coefficient_scalar,hx,Derivation.leibniz,coefficient_a,coefficient_b,smul_eq_mul,
      du,map_div₀,map_mul,map_pow,map_ofNat,eq_comm] <;> ring

lemma evaluation_killed (φ : P2 →+* K) (u : K) (hu : u^3=φ basePolynomial)
    (D : Derivation ℤ K K) (hφ : ∀ p,D (φ p)=0) (huD : D u=0) (p : P4) :
    coefficient D (evaluation φ u hu p)=0 := by
  rw [evaluation_chain φ u hu (coefficient D) (by intro c; rw [coefficient_scalar,hφ,map_zero]) p]
  apply Finset.sum_eq_zero
  intro i hi
  have hz : coefficient D
      (![algebraMap K (E K) (φ (MvPolynomial.X 0)),algebraMap K (E K) (φ (MvPolynomial.X 1)),
        algebraMap K (E K) u*a (K:=K),algebraMap K (E K) u*b (K:=K)] i)=0 := by
    fin_cases i <;> simp [coefficient_scalar,hφ,huD,Derivation.leibniz,coefficient_a,coefficient_b,smul_eq_mul]
  rw [hz,mul_zero]

/-- The actual affine polynomial data yield a scalar primitive on the cubic cover. -/
theorem scalar_primitive_of_data (φ : P2 →+* K) (hφ : Function.Injective φ)
    (u : K) (hu0 : u≠0) (hu : u^3=φ basePolynomial)
    (Dx Dy : Derivation ℤ K K)
    (hcx : ∀ c,Dx (φ (MvPolynomial.C c))=0)
    (hcy : ∀ c,Dy (φ (MvPolynomial.C c))=0)
    (hxx : ∀ i : Fin 2,Dx (φ (MvPolynomial.X i))=if i=0 then 1 else 0)
    (hyy : ∀ i : Fin 2,Dy (φ (MvPolynomial.X i))=if i=1 then 1 else 0)
    (A D N₀ : P4) (N : Fin 3 → P4) (hd : CrossedFanoAffineData.evaluation D≠0)
    (hn : N₀*integerPartial 0 CrossedFanoAffineData.equation+
      ∑ i,N i*integerPartial i.succ CrossedFanoAffineData.equation=A*D)
    (hdiv : CrossedFanoAffineData.evaluation
      (residueDivNum (integerPartial 0) (fun i : Fin 3 => integerPartial i.succ) D N₀ N)=0) :
    ∃ bf cx cy : E K,(delta bf+coefficient Dx cx+coefficient Dy cy=
      evaluation φ u hu A/(7*(algebraMap K (E K) u)^4)-
      (a (K:=K)*evaluation φ u hu (ambientD 2 A)+b (K:=K)*evaluation φ u hu (ambientD 3 A))/
        (7*(algebraMap K (E K) u)^3)) ∧
      ∀ D : Derivation ℤ K K,(∀ p,D (φ p)=0) → D u=0 →
        coefficient D bf=0 ∧ coefficient D cx=0 ∧ coefficient D cy=0 := by
  let ρ := evaluation φ u hu
  let nn : Fin 4 → P4 := ![N 0,N₀,N 1,N 2]
  let vv := values ρ D nn
  let jj := jet ρ ambientD D nn
  let uu := algebraMap K (E K) u
  let px := algebraMap K (E K) (baseGradient φ 0)
  let py := algebraMap K (E K) (baseGradient φ 1)
  have hd' : ρ D≠0 := evaluation_denominator_nonzero φ hφ u hu0 hu D hd
  have hu' : uu≠0 := by simpa only [map_zero] using (algebraMap K (E K)).injective.ne hu0
  have hn' := data_reindex A D N₀ N hn
  have hv := normal_values ρ D A nn (fun i => ambientD i CrossedFanoAffineData.equation) hd' hn'
  have hs := normal_jets ρ ambientD D A nn (fun i => ambientD i CrossedFanoAffineData.equation) hd' hn' 2
  have ht := normal_jets ρ ambientD D A nn (fun i => ambientD i CrossedFanoAffineData.equation) hd' hn' 3
  have hdv := divergence_jets ρ ambientD D nn hd' (by
    rw [show D*(∑ i,ambientD i (nn i))-(∑ i,nn i*ambientD i D)=
      residueDivNum (integerPartial 0) (fun i : Fin 3 => integerPartial i.succ) D N₀ N
      from divergence_reindex D N₀ N]
    exact evaluation_zero_of_old φ u hu _ hdiv)
  change (∑ i,jj i i)=0 at hdv
  have hg (i : Fin 4) : ρ (ambientD i CrossedFanoAffineData.equation)=
      7*![px,py,3*uu^2*a (K:=K)^2,3*uu^2*b (K:=K)^2] i := evaluated_gradient φ u hu i
  have hgs (i : Fin 4) : ρ (ambientD 2 (ambientD i CrossedFanoAffineData.equation))=
      ![0,0,42*uu*a (K:=K),0] i := evaluated_hessian_S φ u hu i
  have hgt (i : Fin 4) : ρ (ambientD 3 (ambientD i CrossedFanoAffineData.equation))=
      ![0,0,0,42*uu*b (K:=K)] i := evaluated_hessian_T φ u hu i
  change (∑ i,vv i*ρ (ambientD i CrossedFanoAffineData.equation))=ρ A at hv
  change (∑ i,jj i 2*ρ (ambientD i CrossedFanoAffineData.equation))+
    (∑ i,vv i*ρ (ambientD 2 (ambientD i CrossedFanoAffineData.equation)))=ρ (ambientD 2 A) at hs
  change (∑ i,jj i 3*ρ (ambientD i CrossedFanoAffineData.equation))+
    (∑ i,vv i*ρ (ambientD 3 (ambientD i CrossedFanoAffineData.equation)))=ρ (ambientD 3 A) at ht
  simp only [hg,hgs,hgt,Fin.sum_univ_four] at hv hs ht
  simp at hv hs ht
  have hδ (i : Fin 4) := derivative_values ρ ambientD delta
    ![0,0,uu*b (K:=K)^2,-uu*a (K:=K)^2] (delta_evaluation_chain φ u hu) D nn hd' i
  have hx (i : Fin 4) := derivative_values ρ ambientD (coefficient Dx)
    ![1,0,px/(3*uu^2)*a (K:=K),px/(3*uu^2)*b (K:=K)]
    (by simpa using coefficient_evaluation_chain φ u hu hu0 Dx 0 hcx hxx) D nn hd' i
  have hy (i : Fin 4) := derivative_values ρ ambientD (coefficient Dy)
    ![0,1,py/(3*uu^2)*a (K:=K),py/(3*uu^2)*b (K:=K)]
    (by simpa using coefficient_evaluation_chain φ u hu hu0 Dy 1 hcy hyy) D nn hd' i
  change ∀ i,delta (vv i)=∑ j,jj i j*![0,0,uu*b (K:=K)^2,-uu*a (K:=K)^2] j at hδ
  change ∀ i,coefficient Dx (vv i)=∑ j,jj i j*![1,0,px/(3*uu^2)*a (K:=K),px/(3*uu^2)*b (K:=K)] j at hx
  change ∀ i,coefficient Dy (vv i)=∑ j,jj i j*![0,1,py/(3*uu^2)*a (K:=K),py/(3*uu^2)*b (K:=K)] j at hy
  refine ⟨scalarB uu a b vv,scalarX uu vv,scalarY uu vv,?_,?_⟩
  ·
    have dux : coefficient Dx uu=px/(3*uu^2) := by
      dsimp [uu,px]
      rw [coefficient_scalar,cubic_derivative Dx φ u hu hu0,base_chain_at φ Dx 0 hcx hxx]
      simp [map_div₀,map_mul,map_pow,map_ofNat]
    have duy : coefficient Dy uu=py/(3*uu^2) := by
      dsimp [uu,py]
      rw [coefficient_scalar,cubic_derivative Dy φ u hu hu0,base_chain_at φ Dy 1 hcy hyy]
      simp [map_div₀,map_mul,map_pow,map_ofNat]
    have result := scalar_equation delta (coefficient Dx) (coefficient Dy)
      uu a b px py (ρ A/7) (ρ (ambientD 2 A)/7) (ρ (ambientD 3 A)/7) vv jj hu'
      (delta_base u) delta_a delta_b dux duy
      (by rw [hδ]; simp [Fin.sum_univ_four]; ring)
      (by rw [hδ]; simp [Fin.sum_univ_four]; ring)
      (by rw [hx]; simp [Fin.sum_univ_four]; ring)
      (by rw [hy]; simp [Fin.sum_univ_four]; ring)
      fermat_relation
      (by simpa [Fin.sum_univ_four,add_assoc] using hdv)
      (by linear_combination (1/7 : E K)*hv)
      (by linear_combination (1/7 : E K)*hs)
      (by linear_combination (1/7 : E K)*ht)
    convert result using 1 <;> dsimp [uu,ρ] <;> field_simp <;> ring
  · intro Dz hzφ hzu
    have hzρ (p : P4) : coefficient Dz (ρ p)=0 := evaluation_killed φ u hu Dz hzφ hzu p
    have hzuu : coefficient Dz uu=0 := by
      change coefficient Dz (algebraMap K (E K) u)=0
      rw [coefficient_scalar,hzu,map_zero]
    have hzv (i : Fin 4) : coefficient Dz (vv i)=0 := by
      change coefficient Dz (ρ (nn i)/ρ D)=0
      simp only [Derivation.leibniz_div,hzρ,
        smul_eq_mul,zero_mul,mul_zero,sub_self,zero_div]
    have hz3 : coefficient Dz (3 : E K)=0 := (coefficient Dz).map_natCast 3
    simp only [scalarB,scalarX,scalarY,Derivation.leibniz_div,Derivation.leibniz,
      Derivation.leibniz_pow,map_sub,map_neg,hzv,coefficient_scalar,coefficient_a,coefficient_b,
      hzuu,hz3,smul_eq_mul,smul_zero,mul_zero,zero_mul,sub_self,add_zero,zero_add,zero_div,
      nsmul_eq_mul,and_self,neg_zero,true_and]


end CrossedFanoElliptic
end
end
