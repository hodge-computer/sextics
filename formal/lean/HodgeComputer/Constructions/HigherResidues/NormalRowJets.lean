import HodgeComputer.Constructions.HigherResidues.JacobianJets
import HodgeComputer.Constructions.HigherResidues.NormalJetBinding

/- Actual normal-row Taylor jets of a polynomial hypersurface.
Prepared with OpenAI Codex assistance for fqlx. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
namespace SplitHigherResidue
open Polynomial HoldoutConstruction SplitNormalJetBinding
open scoped BigOperators
variable {K : Type*} [Field K] [CharZero K]

def firstGradientJet (π : P →+* K) (F : P) (ψ : Fin 5 → K) (j : Fin 5) : K :=
  ∑ k,hessian π F j k*ψ k

def secondGradientJet (π : P →+* K) (F : P) (ψ : Fin 5 → K) (j : Fin 5) : K :=
  (1/2)*(∑ k,∑ l,third π F j k l*ψ k*ψ l)

def normalQuadraticJet (π : P →+* K) (F : P) (ψ : Fin 5 → K) : K :=
  (1/2)*(∑ j,∑ k,hessian π F j k*ψ j*ψ k)

def normalCubicJet (π : P →+* K) (F : P) (ψ : Fin 5 → K) : K :=
  (1/3)*(∑ j,secondGradientJet π F ψ j*ψ j)

def normalVariation (D : Fin 4 → Derivation ℤ K K) (ψ : Fin 5 → K) :
    Matrix (Fin 5) (Fin 5) K := fun j => Fin.cases 0 (fun i => D i (ψ j))

lemma normalQuadraticJet_eq (π : P →+* K) (F : P) (ψ : Fin 5 → K) :
    normalQuadraticJet π F ψ=SplitNormalTaylor.secondJet ψ (hessian π F) := by
  unfold normalQuadraticJet SplitNormalTaylor.secondJet
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero]
  ring

lemma firstGradientJet_pairing (π : P →+* K) (F : P) (ψ : Fin 5 → K) :
    (∑ j,firstGradientJet π F ψ j*ψ j)=2*normalQuadraticJet π F ψ := by
  unfold firstGradientJet normalQuadraticJet
  have h : (∑ j,(∑ k,hessian π F j k*ψ k)*ψ j)=
      ∑ j,∑ k,hessian π F j k*ψ j*ψ k := by
    simp only [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [h]
  ring

lemma secondGradientJet_pairing (π : P →+* K) (F : P) (ψ : Fin 5 → K) :
    (∑ j,secondGradientJet π F ψ j*ψ j)=3*normalCubicJet π F ψ := by
  unfold normalCubicJet
  ring

/-- Differentiating the quadratic normal coefficient gives the second row jet. -/
lemma normalQuadraticJet_derivative (π : P →+* K) (F : P) (ψ : Fin 5 → K)
    (D : Derivation ℤ K K) (v : Fin 5 → K)
    (hD : ∀ B,D (π B)=∑ j,π (integerPartial j B)*v j) :
    D (normalQuadraticJet π F ψ) =
      (∑ j,secondGradientJet π F ψ j*v j)+
      ∑ j,firstGradientJet π F ψ j*D (ψ j) := by
  apply quadratic_derivative_normal_jet D (hessian π F) (third π F) ψ v
  · intro j k
    exact (hessian_symm π F).apply k j
  · exact third_cycle π F
  · intro j k
    exact hD (integerPartial k (integerPartial j F))

theorem actual_polynomial_normal_row_jet
    (π : P →+* K) (F : P) (D : Fin 4 → Derivation ℤ K K)
    (M : Matrix (Fin 5) (Fin 5) K) (ψ : Fin 5 → K)
    (hF : π F=0) (hM : ∀ j,M j 0=ψ j)
    (hnormal : ∑ j,gradient π F j*ψ j=1)
    (hD : ∀ i B,D i (π B)=∑ j,π (integerPartial j B)*M j i.succ) :
    Matrix.vecMul (quadraticRow (gradient π F) (firstGradientJet π F ψ)
      (secondGradientJet π F ψ)) (linearMatrix M (normalVariation D ψ)) =
      (1+C (2*normalQuadraticJet π F ψ)*(X : K[X])+
        C (3*normalCubicJet π F ψ)*(X : K[X])^2) •
        (Pi.single (0 : Fin 5) (1 : K[X]))+
      (X : K[X])^2 • (C ∘ Fin.cases 0 (fun i : Fin 4 => D i (normalQuadraticJet π F ψ)))+
      (X : K[X])^3 • (C ∘ Matrix.vecMul (secondGradientJet π F ψ) (normalVariation D ψ)) := by
  apply polynomial_normal_row_jet M (normalVariation D ψ) (gradient π F)
    (firstGradientJet π F ψ) (secondGradientJet π F ψ)
    (normalQuadraticJet π F ψ) (normalCubicJet π F ψ)
    (Fin.cases 0 (fun i : Fin 4 => D i (normalQuadraticJet π F ψ)))
  · funext j
    induction j using Fin.cases with
    | zero => simpa [Matrix.vecMul,dotProduct,hM] using hnormal
    | succ i =>
      have h := hD i F
      rw [hF,map_zero] at h
      simpa [Matrix.vecMul,dotProduct,gradient,Pi.single_apply,Fin.succ_ne_zero] using h.symm
  · funext j
    induction j using Fin.cases with
    | zero =>
      simpa [Matrix.vecMul,dotProduct,normalVariation,hM,Fin.cases_zero,Pi.single_apply] using
        firstGradientJet_pairing π F ψ
    | succ i =>
      have hgrad (k : Fin 5) : D i (gradient π F k)=∑ l,hessian π F k l*M l i.succ := hD i (integerPartial k F)
      have hn := normal_vector_derivative D M (hessian π F) (gradient π F) ψ hnormal (fun i k => hD i (integerPartial k F)) i
      have hh : (∑ k,firstGradientJet π F ψ k*M k i.succ)=
          ∑ j,∑ k,hessian π F j k*M k i.succ*ψ j := by
        simp only [firstGradientJet,Finset.sum_mul]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro j hj
        apply Finset.sum_congr rfl
        intro k hk
        rw [(hessian_symm π F).apply j k]
        ring
      simp only [Pi.add_apply,Pi.smul_apply,Matrix.vecMul,dotProduct,
        normalVariation,Fin.cases_succ,Pi.single_apply,Fin.succ_ne_zero,if_false,smul_eq_mul,mul_zero]
      rw [hh,hn]
      ring
  · funext j
    induction j using Fin.cases with
    | zero =>
      simpa [Matrix.vecMul,dotProduct,normalVariation,hM,Fin.cases_zero,Pi.single_apply] using
        secondGradientJet_pairing π F ψ
    | succ i =>
      have ha := normalQuadraticJet_derivative π F ψ (D i) (fun j => M j i.succ) (hD i)
      simp only [Pi.add_apply,Pi.smul_apply,Matrix.vecMul,dotProduct,
        normalVariation,Fin.cases_succ,Pi.single_apply,Fin.succ_ne_zero,if_false,smul_eq_mul,mul_zero,zero_add]
      exact ha.symm

end SplitHigherResidue
