import HodgeComputer.Constructions.HigherResidues.HigherResidue

/- Second normal Jacobian jets for the exact polynomial-curve construction.
Prepared with OpenAI Codex assistance for fqlx. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
namespace SplitHigherResidue
open Polynomial HoldoutConstruction
open scoped BigOperators
variable {K : Type*} [Field K] [CharZero K]

def linearMatrix {n : ℕ} (M₀ M₁ : Matrix (Fin n) (Fin n) K) : Matrix (Fin n) (Fin n) K[X] :=
  M₀.map C+(X : K[X]) • M₁.map C

def quadraticRow {n : ℕ} (G₀ G₁ G₂ : Fin n → K) : Fin n → K[X] :=
  ((C ∘ G₀)+(X : K[X]) • (C ∘ G₁))+(X : K[X])^2 • (C ∘ G₂)

lemma linearMatrix_det_zero {n : ℕ} (M₀ M₁ : Matrix (Fin n) (Fin n) K) :
    (linearMatrix M₀ M₁).det.coeff 0 = M₀.det := by
  simpa [linearMatrix,add_comm] using Polynomial.coeff_det_X_add_C_zero M₁ M₀

lemma linearMatrix_tail (M₀ M₁ : Matrix (Fin 5) (Fin 5) K) :
    (linearMatrix M₀ M₁).submatrix Fin.succ Fin.succ =
      linearMatrix (M₀.submatrix Fin.succ Fin.succ) (M₁.submatrix Fin.succ Fin.succ) := by
  rfl

lemma linearMatrix_updatedRow_zero (M₀ M₁ : Matrix (Fin 5) (Fin 5) K) (d : Fin 5 → K) :
    ((linearMatrix M₀ M₁).updateRow 0 (C ∘ d)).det.coeff 0 = (M₀.updateRow 0 d).det := by
  change (Polynomial.constantCoeff : K[X] →+* K)
    (((linearMatrix M₀ M₁).updateRow 0 (C ∘ d)).det) = _
  rw [RingHom.map_det]
  congr 1
  ext i j
  by_cases hi : i=0
  · subst i
    simp [linearMatrix,Matrix.updateRow]
  · simp [linearMatrix,Matrix.updateRow,hi]

lemma quadratic_times_coeff_one (g l m : K) (P : K[X]) :
    ((C g+(X : K[X])*C l+(X : K[X])^2*C m)*P).coeff 1 =
      g*P.coeff 1+l*P.coeff 0 := by
  simp [Polynomial.coeff_mul,Finset.Nat.sum_antidiagonal_succ]

lemma quadratic_times_coeff_two (g l m : K) (P : K[X]) :
    ((C g+(X : K[X])*C l+(X : K[X])^2*C m)*P).coeff 2 =
      g*P.coeff 2+l*P.coeff 1+m*P.coeff 0 := by
  simp [Polynomial.coeff_mul,Finset.Nat.sum_antidiagonal_succ]
  norm_num [Polynomial.coeff_one,Polynomial.coeff_X]
  ring

/-- Matrix coefficient identities for the linear thickening. The row-jet
hypothesis is supplied by the differentiated normal pairing and Hessian. -/
theorem jacobian_jet_equations
    (D E : Fin 4 → Derivation ℤ K K)
    (M N M₁ : Matrix (Fin 5) (Fin 5) K) (g ψ G₁ G₂ : Fin 5 → K)
    (a b : K) (q : Fin 5 → K[X])
    (hNM : N*M=1) (hN : ∀ j,N 0 j=g j) (hM : ∀ j,M j 0=ψ j)
    (hg : g 0≠0) (hψ : ∑ j,g j*ψ j=1)
    (chain : ∀ j x,E j x=∑ i,tangentInverse N g i j*D i x)
    (hrow : Matrix.vecMul (quadraticRow g G₁ G₂) (linearMatrix M M₁) =
      (1+C (2*a)*(X : K[X])+C (3*b)*(X : K[X])^2) •
        (Pi.single (0 : Fin 5) (1 : K[X]))+
      (X : K[X])^2 • (C ∘ Fin.cases 0 (fun i : Fin 4 => D i a))+(X : K[X])^3 • q)
    (hfactor : ∀ i j : Fin 4, M₁ i.succ j.succ =
      ∑ k : Fin 4, E k (ψ i.succ)*M k.succ j.succ) :
    g 0*(linearMatrix M M₁).det.coeff 1+G₁ 0*M.det =
      g 0*M.det*(fieldDivergence E (fun i => ψ i.succ)+2*a) ∧
    g 0*(linearMatrix M M₁).det.coeff 2+G₁ 0*(linearMatrix M M₁).det.coeff 1+G₂ 0*M.det =
      g 0*M.det*((1/2)*((fieldDivergence E (fun i => ψ i.succ))^2-
        traceSquare E (fun i => ψ i.succ))+2*a*fieldDivergence E (fun i => ψ i.succ)+
        3*b-advect E (fun i => ψ i.succ) a) := by
  let W : Matrix (Fin 4) (Fin 4) K := fun i j => E j (ψ i.succ)
  let A : Matrix (Fin 4) (Fin 4) K := M.submatrix Fin.succ Fin.succ
  let L := linearMatrix M M₁
  let d : Fin 5 → K := Fin.cases 0 (fun i : Fin 4 => D i a)
  have hgrad (j : Fin 5) : (∑ k,g k*M k j)=if j=0 then 1 else 0 := by
    have h := congrArg (fun P : Matrix (Fin 5) (Fin 5) K => P 0 j) hNM
    simpa [Matrix.mul_apply,hN,Matrix.one_apply,eq_comm] using h
  have hA : A.det=g 0*M.det := normal_matrix_determinant M g hgrad
  have htail : L.submatrix Fin.succ Fin.succ = (1+(X : K[X]) • W.map C)*A.map C := by
    change (linearMatrix M M₁).submatrix Fin.succ Fin.succ = _
    rw [linearMatrix_tail]
    apply tangent_linear_factorization A _ W
    ext i j
    exact hfactor i j
  have ht := tangent_determinant_coefficients_zero_one W A
  have ht2 := tangent_determinant_coefficient_two W A
  have h0 : L.det.coeff 0=M.det := linearMatrix_det_zero M M₁
  have hd : (M.updateRow 0 d).det = -g 0*M.det*advect E (fun i => ψ i.succ) a := by
    rw [determinant_updateRow_inverse M N hNM d]
    rw [Fin.sum_univ_succ]
    simp only [d,Fin.cases_zero,Fin.cases_succ,zero_mul,zero_add]
    rw [normal_cofactor_contraction D E M N g ψ hNM hN hM hg hψ chain a]
    unfold advect
    ring
  have hr1 := determinant_normal_row_coeff_one L (quadraticRow g G₁ G₂) q a b d hrow
  have hr2 := determinant_normal_row_coeff_two L (quadraticRow g G₁ G₂) q a b d hrow
  change ((C (g 0)+(X : K[X])*C (G₁ 0)+(X : K[X])^2*C (G₂ 0))*L.det).coeff 1 = _ at hr1
  change ((C (g 0)+(X : K[X])*C (G₁ 0)+(X : K[X])^2*C (G₂ 0))*L.det).coeff 2 = _ at hr2
  rw [quadratic_times_coeff_one,h0,htail,ht.1,ht.2,hA] at hr1
  have hd0 : (L.updateRow 0 (fun j => C (d j))).det.coeff 0 = (M.updateRow 0 d).det :=
    linearMatrix_updatedRow_zero M M₁ d
  rw [quadratic_times_coeff_two,h0,htail,ht.1,ht.2,hd0,hd,hA] at hr2
  change _ at ht2
  have hu : (∑ i,W i i)=fieldDivergence E (fun i => ψ i.succ) := rfl
  have hs : (∑ i,∑ j,W i j*W j i)=traceSquare E (fun i => ψ i.succ) := by
    unfold W traceSquare
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hu,hs,hA] at ht2
  constructor
  · dsimp only [L] at hr1
    rw [hu] at hr1
    linear_combination hr1
  · change _ at hr2
    dsimp only [L] at hr2 ⊢
    rw [hu] at hr2
    linear_combination hr2+(1/2)*ht2

end SplitHigherResidue
