import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Tactic

/- Exact normal/tangent Taylor identities for split-ternary-q2.
Prepared with OpenAI Codex assistance for fqlx. The hypotheses are the
explicit chain-rule identities of an actual hypersurface evaluation. -/

noncomputable section
set_option maxHeartbeats 4000000
namespace SplitNormalTaylor
open scoped BigOperators
variable {K : Type*} [Field K] [CharZero K]

def advect (E : Fin 4 → Derivation ℤ K K) (w : Fin 4 → K) (B : K) : K :=
  ∑ i,w i*E i B

def restrictedHessian (E : Fin 4 → Derivation ℤ K K) (w : Fin 4 → K) (B : K) : K :=
  ∑ i,∑ j,w i*w j*E i (E j B)

def firstJet (ψ b : Fin 5 → K) : K := ∑ i,ψ i*b i
def secondJet (ψ : Fin 5 → K) (BB : Matrix (Fin 5) (Fin 5) K) : K :=
  (∑ i,∑ j,ψ i*ψ j*BB i j)/2

omit [CharZero K] in
lemma normal_zero_coordinate (g ψ : Fin 5 → K) (hg : g 0≠0)
    (hnormal : (∑ i,g i*ψ i)=1) :
    ψ 0=(1-∑ i : Fin 4,g i.succ*ψ i.succ)/g 0 := by
  rw [Fin.sum_univ_succ] at hnormal
  field_simp [hg]
  linear_combination hnormal

theorem first_jet_formula (E : Fin 4 → Derivation ℤ K K)
    (g ψ b : Fin 5 → K) (B : K) (hg : g 0≠0)
    (hnormal : (∑ i,g i*ψ i)=1)
    (hE : ∀ i,E i B=b i.succ-g i.succ/g 0*b 0) :
    firstJet ψ b=b 0/g 0+advect E (fun i => ψ i.succ) B := by
  rw [firstJet,Fin.sum_univ_succ,normal_zero_coordinate g ψ hg hnormal]
  simp only [advect,hE,Fin.sum_univ_four]
  field_simp [hg]
  ring

/-- The second normal Taylor coefficient is determined by the actual
restricted Hessian and the second jet of the defining equation. -/
theorem second_jet_formula (E : Fin 4 → Derivation ℤ K K)
    (g ψ b : Fin 5 → K) (B : K)
    (BB FF : Matrix (Fin 5) (Fin 5) K)
    (hg : g 0≠0) (hnormal : (∑ i,g i*ψ i)=1)
    (hBB : BB.IsSymm) (hFF : FF.IsSymm)
    (hE : ∀ i,E i B=b i.succ-g i.succ/g 0*b 0)
    (hEb : ∀ i j,E i (b j)=BB j i.succ-g i.succ/g 0*BB j 0)
    (hEg : ∀ i j,E i (g j)=FF j i.succ-g i.succ/g 0*FF j 0) :
    secondJet ψ BB =
      (BB 0 0/(g 0)^2-b 0*FF 0 0/(g 0)^3)/2 +
      advect E (fun i => ψ i.succ) (b 0/g 0) +
      restrictedHessian E (fun i => ψ i.succ) B/2 +
      secondJet ψ FF*b 0/g 0 := by
  have hB (i j : Fin 5) : BB i j=BB j i := (hBB.apply i j).symm
  have hF (i j : Fin 5) : FF i j=FF j i := (hFF.apply i j).symm
  have hb10 := hB 1 0; have hb20 := hB 2 0; have hb30 := hB 3 0; have hb40 := hB 4 0
  have hb21 := hB 2 1; have hb31 := hB 3 1; have hb41 := hB 4 1
  have hb32 := hB 3 2; have hb42 := hB 4 2; have hb43 := hB 4 3
  have hf10 := hF 1 0; have hf20 := hF 2 0; have hf30 := hF 3 0; have hf40 := hF 4 0
  have hf21 := hF 2 1; have hf31 := hF 3 1; have hf41 := hF 4 1
  have hf32 := hF 3 2; have hf42 := hF 4 2; have hf43 := hF 4 3
  simp only [secondJet,advect,restrictedHessian,Fin.sum_univ_succ,Fin.sum_univ_zero,
    hE,map_sub,Derivation.leibniz,Derivation.leibniz_div,
    hEb,hEg,smul_eq_mul]
  rw [normal_zero_coordinate g ψ hg hnormal]
  have hs2 {n : ℕ} : (2 : Fin (n+3)).succ=(3 : Fin (n+4)) := rfl
  have hs3 {n : ℕ} : (3 : Fin (n+4)).succ=(4 : Fin (n+5)) := rfl
  simp only [Fin.succ_zero_eq_one,Fin.succ_one_eq_two,hs2,hs3]
  simp only [Fin.sum_univ_four,Fin.succ_zero_eq_one,Fin.succ_one_eq_two,hs2,hs3,
    hb10,hb20,hb30,hb40,hb21,hb31,hb41,hb32,hb42,hb43,
    hf10,hf20,hf30,hf40,hf21,hf31,hf41,hf32,hf42,hf43]
  field_simp [hg]
  ring

#print axioms first_jet_formula
#print axioms second_jet_formula
end SplitNormalTaylor
