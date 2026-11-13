import HodgeComputer.Constructions.HoldoutCover.PolynomialFamily
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Tactic

/-!
Finite second-order density transport for a third-order pole. This module
records an exact Lie-derivative identity and polynomial-density integration.
The application must separately identify its normal-coordinate Taylor jets.
Prepared with OpenAI Codex assistance for contributor fqlx.
-/

noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
namespace SplitHigherResidue
open HoldoutConstruction Polynomial
open scoped BigOperators
variable {K : Type*} [Field K] [CharZero K]
variable {ι : Type*} [Fintype ι]

def advect (D : ι → Derivation ℤ K K) (w : ι → K) (r : K) : K :=
  ∑ i, w i*D i r

def advectVector (D : ι → Derivation ℤ K K) (w v : ι → K) : ι → K :=
  fun i => advect D w (v i)

omit [CharZero K] in
lemma advect_mul (D : ι → Derivation ℤ K K) (w : ι → K) (r s : K) :
    advect D w (r*s) = advect D w r*s+r*advect D w s := by
  simp only [advect, Derivation.leibniz, smul_eq_mul, mul_add,
    Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
  conv_lhs => rw [add_comm]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i hi <;> ring

omit [CharZero K] in
lemma advect_add (D : ι → Derivation ℤ K K) (w : ι → K) (r s : K) :
    advect D w (r+s) = advect D w r+advect D w s := by
  simp only [advect, map_add, mul_add, Finset.sum_add_distrib]

omit [CharZero K] in
lemma divergence_smul (D : ι → Derivation ℤ K K) (r : K) (w : ι → K) :
    fieldDivergence D (fun i => r*w i) = advect D w r+r*fieldDivergence D w := by
  exact fieldDivergence_smul D r w

omit [CharZero K] in
lemma divergence_advect (D : ι → Derivation ℤ K K) (w v : ι → K)
    (hc : ∀ i j, Function.Commute (D i) (D j)) :
    fieldDivergence D (advectVector D w v) =
      (∑ i, ∑ j, D i (w j)*D j (v i))+advect D w (fieldDivergence D v) := by
  simp only [fieldDivergence, advectVector, advect, map_sum,
    Derivation.leibniz, smul_eq_mul, Finset.sum_add_distrib]
  conv_lhs => rw [add_comm]
  congr 1
  · apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hc i j]

omit [CharZero K] in
lemma advect_advect (D : ι → Derivation ℤ K K) (w : ι → K) (r : K) :
    advect D w (advect D w r) =
      advect D (advectVector D w w) r+
      ∑ i, ∑ j, w i*w j*D i (D j r) := by
  simp only [advectVector, advect, map_sum, Derivation.leibniz, smul_eq_mul,
    Finset.mul_sum, mul_add, Finset.sum_add_distrib]
  conv_lhs => rw [add_comm]
  congr 1
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  · apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring

def traceSquare (D : ι → Derivation ℤ K K) (w : ι → K) : K :=
  ∑ i, ∑ j, D i (w j)*D j (w i)

def hessianDensity (D : ι → Derivation ℤ K K) (w : ι → K) (r : K) : K :=
  ∑ i, ∑ j, w i*w j*D i (D j r)

lemma second_lie_divergence (D : ι → Derivation ℤ K K) (w : ι → K) (r : K)
    (hc : ∀ i j, Function.Commute (D i) (D j)) :
    fieldDivergence D (fun i => w i*fieldDivergence D (fun j => r*w j)-
      r*advectVector D w w i) =
      hessianDensity D w r+2*advect D w r*fieldDivergence D w+
        r*((fieldDivergence D w)^2-traceSquare D w) := by
  have hsub (u v : ι → K) :
      fieldDivergence D (fun i => u i-v i)=fieldDivergence D u-fieldDivergence D v := by
    simp only [fieldDivergence, map_sub, Finset.sum_sub_distrib]
  rw [hsub]
  have hmul := divergence_smul D (fieldDivergence D (fun j => r*w j)) w
  have hswap : (fun i => w i*fieldDivergence D (fun j => r*w j)) =
      (fun i => fieldDivergence D (fun j => r*w j)*w i) := by funext i; ring
  rw [hswap, hmul, divergence_smul, divergence_smul,
    divergence_advect D w w hc]
  rw [advect_add, advect_advect, advect_mul]
  change _ = hessianDensity D w r+2*advect D w r*fieldDivergence D w+
    r*((fieldDivergence D w)^2-traceSquare D w)
  dsimp only [hessianDensity, traceSquare]
  ring

/-- The universal second density coefficient for a moving tangent chart. -/
def secondDensity (D : ι → Derivation ℤ K K) (r₀ r₁ r₂ : K) (w v : ι → K) : K :=
  r₂+advect D w r₁+advect D v r₀+(1/2)*hessianDensity D w r₀+
    (r₁+advect D w r₀)*fieldDivergence D w+
    r₀*(fieldDivergence D v+(1/2)*((fieldDivergence D w)^2-traceSquare D w))

def secondCorrection (D : ι → Derivation ℤ K K) (r₀ r₁ : K) (w v : ι → K) : ι → K :=
  fun i => r₁*w i+r₀*v i+(1/2)*(w i*fieldDivergence D (fun j => r₀*w j)-
    r₀*advectVector D w w i)

theorem second_density_transgression (D : ι → Derivation ℤ K K)
    (hc : ∀ i j, Function.Commute (D i) (D j))
    (r₀ r₁ r₂ : K) (w v : ι → K) :
    secondDensity D r₀ r₁ r₂ w v =
      r₂+fieldDivergence D (secondCorrection D r₀ r₁ w v) := by
  have hhalf (i : ι) : D i (1/2 : K) = 0 := by
    have htwo : D i (2 : K) = 0 := (D i).map_natCast 2
    rw [Derivation.leibniz_div]
    simp [htwo]
  have hlin : fieldDivergence D (secondCorrection D r₀ r₁ w v) =
      fieldDivergence D (fun i => r₁*w i)+fieldDivergence D (fun i => r₀*v i)+
        (1/2)*fieldDivergence D (fun i => w i*fieldDivergence D (fun j => r₀*w j)-
          r₀*advectVector D w w i) := by
    simp only [fieldDivergence, secondCorrection, map_add, Derivation.leibniz,
      hhalf, mul_zero, add_zero, smul_eq_mul,
      Finset.sum_add_distrib, Finset.mul_sum]
  rw [hlin, divergence_smul, divergence_smul, second_lie_divergence D w r₀ hc]
  unfold secondDensity
  ring

/-- Normal-chart coefficients of the residue of A/F² and A/F³. -/
def normalSourceOne (A A₀ g g₀ : K) : K := A₀/g-A*g₀/g^2

def normalSourceTwo (A A₀ A₀₀ g g₀ g₀₀ : K) : K :=
  (1/2)*(A₀₀/g^2-(3*A₀*g₀+A*g₀₀)/g^3+3*A*g₀^2/g^4)

/-- The tangent correction for the inverse normal parameter
s=z-a*z²+O(z³), including its divergence term. -/
def normalCorrection (D : ι → Derivation ℤ K K) (g A A₀ g₀ a : K)
    (w : ι → K) : ι → K :=
  fun i => g*secondCorrection D (A/g) (normalSourceOne A A₀ g g₀/g)
    w (fun j => -a*w j) i

theorem weighted_second_transgression (D : ι → Derivation ℤ K K)
    (hc : ∀ i j, Function.Commute (D i) (D j))
    (A A₀ A₀₀ g g₀ g₀₀ a : K) (w : ι → K) (hg : g ≠ 0) :
    g*secondDensity D (A/g) (normalSourceOne A A₀ g g₀/g)
      (normalSourceTwo A A₀ A₀₀ g g₀ g₀₀/g) w (fun j => -a*w j) =
    normalSourceTwo A A₀ A₀₀ g g₀ g₀₀+
      residueDivergence D g (normalCorrection D g A A₀ g₀ a w) := by
  rw [second_density_transgression D hc]
  unfold normalCorrection
  rw [residueDivergence_cancel_density D g hg]
  field_simp [hg]

/-- Pure second-order Taylor algebra. The five hypotheses are the two
Jacobian coefficients and the three source coefficients of a linear normal
thickening; none asserts the final transgression identity. -/
theorem linear_thickening_density_identity (D : ι → Derivation ℤ K K)
    (r₀ r₁ r₂ A₀ A₁ A₂ J J₁ J₂ g l m a b : K) (w : ι → K)
    (hA₀ : A₀ = g*r₀)
    (hA₁ : A₁ = l*r₀+g*(r₁+advect D w r₀))
    (hA₂ : A₂ = m*r₀+l*(r₁+advect D w r₀)+
      g*(r₂+a*r₁+advect D w r₁+(1/2)*hessianDensity D w r₀))
    (hJ₁ : g*J₁+l*J = g*J*(fieldDivergence D w+2*a))
    (hJ₂ : g*J₂+l*J₁+m*J = g*J*((1/2)*
      ((fieldDivergence D w)^2-traceSquare D w)+
      2*a*fieldDivergence D w+3*b-advect D w a)) :
    A₂*J+A₁*J₁+A₀*J₂-3*a*(A₁*J+A₀*J₁)+(6*a^2-3*b)*A₀*J =
      g*J*secondDensity D r₀ r₁ r₂ w (fun j => -a*w j) := by
  have hneg (v : ι → K) : advect D (fun j => -a*v j) r₀ = -a*advect D v r₀ := by
    simp only [advect, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hdiv : fieldDivergence D (fun j => -a*w j) =
      -advect D w a-a*fieldDivergence D w := by
    rw [divergence_smul]
    simp only [advect, map_neg, mul_neg, Finset.sum_neg_distrib]
    ring
  rw [hA₀,hA₁,hA₂]
  unfold secondDensity
  rw [hneg,hdiv]
  linear_combination r₀*hJ₂+(r₁+advect D w r₀-3*a*r₀)*hJ₁

theorem determinant_linear_coeff_two_four {K : Type*} [Field K] [CharZero K] (W : Matrix (Fin 4) (Fin 4) K) :
    2*(Matrix.det (fun (i j : Fin 4) => (Polynomial.C (if i=j then (1:K) else 0)+
      Polynomial.C (W i j)*Polynomial.X))).coeff 2 =
      (∑ i, W i i)^2-(∑ i, ∑ j, W i j*W j i) := by
  rw [Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.submatrix_apply, Matrix.det_fin_three,
    Fin.succAbove, Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_succ]
  norm_num [Polynomial.coeff_one, Polynomial.coeff_X, Polynomial.coeff_neg]
  ring

theorem determinant_normal_row_coeff_two {K : Type*} [Field K] [CharZero K] {n : ℕ}
    (M : Matrix (Fin (n+1)) (Fin (n+1)) K[X]) (G q : Fin (n+1) → K[X])
    (a b : K) (d : Fin (n+1) → K)
    (hrow : Matrix.vecMul G M =
      (1+C (2*a)*(X : K[X])+C (3*b)*(X : K[X])^2) • (Pi.single (0 : Fin (n+1)) (1 : K[X]))+
      (X : K[X])^2 • (fun j => C (d j))+(X : K[X])^3 • q) :
    (G 0*M.det).coeff 2 =
      (M.submatrix Fin.succ Fin.succ).det.coeff 2+
      2*a*(M.submatrix Fin.succ Fin.succ).det.coeff 1+
      3*b*(M.submatrix Fin.succ Fin.succ).det.coeff 0+
      (M.updateRow 0 (fun j => C (d j))).det.coeff 0 := by
  have hdet : G 0*M.det=(M.updateRow 0 (Matrix.vecMul G M)).det := by
    have h := Matrix.det_updateRow_sum M 0 G
    have hs : (∑ k, G k • M k) = Matrix.vecMul G M := by
      ext j
      simp [Matrix.vecMul, dotProduct]
    rw [hs] at h
    simpa only [smul_eq_mul] using h.symm
  have ht : (M.updateRow 0 (Pi.single 0 1)).det=(M.submatrix Fin.succ Fin.succ).det := by
    rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
    simp [Matrix.updateRow, Function.update, Matrix.submatrix, Fin.succ_ne_zero]
  rw [hdet,hrow,Matrix.det_updateRow_add,Matrix.det_updateRow_add,
    Matrix.det_updateRow_smul,Matrix.det_updateRow_smul,Matrix.det_updateRow_smul,ht]
  simp [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_succ]
  norm_num [Polynomial.coeff_one, Polynomial.coeff_X]
  ring

theorem polynomial_normal_row_jet {K : Type*} [Field K] [CharZero K] {n : ℕ}
    (M₀ M₁ : Matrix (Fin (n+1)) (Fin (n+1)) K)
    (G₀ G₁ G₂ : Fin (n+1) → K) (a b : K) (d : Fin (n+1) → K)
    (h₀ : Matrix.vecMul G₀ M₀ = Pi.single 0 1)
    (h₁ : Matrix.vecMul G₁ M₀+Matrix.vecMul G₀ M₁ = (2*a) • Pi.single 0 1)
    (h₂ : Matrix.vecMul G₂ M₀+Matrix.vecMul G₁ M₁ = (3*b) • Pi.single 0 1+d) :
    Matrix.vecMul (((C ∘ G₀)+(X : K[X]) • (C ∘ G₁))+(X : K[X])^2 • (C ∘ G₂))
      (M₀.map C+(X : K[X]) • M₁.map C) =
      (1+C (2*a)*(X : K[X])+C (3*b)*(X : K[X])^2) •
        (Pi.single (0 : Fin (n+1)) (1 : K[X]))+
      (X : K[X])^2 • (C ∘ d)+(X : K[X])^3 • (C ∘ Matrix.vecMul G₂ M₁) := by
  have hm (G : Fin (n+1) → K) (M : Matrix (Fin (n+1)) (Fin (n+1)) K) :
      Matrix.vecMul (C ∘ G) (M.map C) = C ∘ Matrix.vecMul G M := by
    funext j
    exact (RingHom.map_vecMul Polynomial.C M G j).symm
  simp_rw [Matrix.add_vecMul, Matrix.vecMul_add, Matrix.smul_vecMul, Matrix.vecMul_smul, hm]
  funext j
  have hc₀ := congrArg (fun v => (C (v j) : K[X])) h₀
  have hc₁ := congrArg (fun v => (C (v j) : K[X])) h₁
  have hc₂ := congrArg (fun v => (C (v j) : K[X])) h₂
  simp only [Pi.add_apply, Pi.smul_apply, Function.comp_apply, smul_eq_mul,
    map_add, map_mul, Pi.single_apply, apply_ite, map_one, map_zero] at hc₀ hc₁ hc₂ ⊢
  by_cases hj : j=0
  · subst j
    simp only [if_true] at hc₀ hc₁ hc₂ ⊢
    linear_combination hc₀+(X : K[X])*hc₁+(X : K[X])^2*hc₂
  · simp only [hj, if_false] at hc₀ hc₁ hc₂ ⊢
    linear_combination hc₀+(X : K[X])*hc₁+(X : K[X])^2*hc₂

theorem determinant_updateRow_inverse {K : Type*} [Field K] {n : ℕ}
    (M N : Matrix (Fin (n+1)) (Fin (n+1)) K) (hNM : N*M=1)
    (d : Fin (n+1) → K) :
    (M.updateRow 0 d).det = M.det*∑ j, d j*N j 0 := by
  have ht : M.transpose*N.transpose=1 := by rw [← Matrix.transpose_mul,hNM,Matrix.transpose_one]
  have h := det_updateCol_inverse M.transpose N.transpose ht 0 d
  have heq : (M.transpose.updateCol 0 d).det = (M.updateRow 0 d).det := by
    rw [← Matrix.det_transpose, Matrix.updateCol_transpose, Matrix.transpose_transpose]
  rw [heq,Matrix.det_transpose] at h
  simp only [Matrix.transpose_apply] at h
  rw [h]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem normal_cofactor_contraction {K : Type*} [Field K] {n : ℕ}
    (D E : Fin n → Derivation ℤ K K)
    (M N : Matrix (Fin (n+1)) (Fin (n+1)) K) (g ψ : Fin (n+1) → K)
    (hNM : N*M=1) (hM : ∀ j,M j 0=ψ j)
    (hg : g 0≠0) (hψ : ∑ j,g j*ψ j=1)
    (chain : ∀ j x,E j x=∑ i,tangentInverse N g i j*D i x) (a : K) :
    ∑ i,D i a*N i.succ 0 = -g 0*∑ j,ψ j.succ*E j a := by
  have hn (i : Fin n) : ∑ j,N i.succ j*ψ j=0 := by
    have h := congrArg (fun A : Matrix (Fin (n+1)) (Fin (n+1)) K => A i.succ 0) hNM
    simpa [Matrix.mul_apply,hM,Matrix.one_apply,Fin.succ_ne_zero] using h
  have hi (i : Fin n) : ∑ j,ψ j.succ*tangentInverse N g i j = -N i.succ 0/g 0 := by
    have hp : g 0*ψ 0+∑ j : Fin n,g j.succ*ψ j.succ=1 := by simpa [Fin.sum_univ_succ] using hψ
    have hh := hn i
    simp only [Fin.sum_univ_succ] at hh
    simp only [tangentInverse,mul_sub,Finset.sum_sub_distrib]
    have hs : (∑ j : Fin n,ψ j.succ*(N i.succ 0/g 0*g j.succ)) =
        (N i.succ 0/g 0)*(∑ j : Fin n,g j.succ*ψ j.succ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    rw [hs]
    have hc : (∑ j : Fin n,ψ j.succ*N i.succ j.succ) =
        ∑ j : Fin n,N i.succ j.succ*ψ j.succ := by
      apply Finset.sum_congr rfl
      intro j hj
      ring
    rw [hc]
    field_simp [hg]
    linear_combination (g 0)*hh-N i.succ 0*hp
  have ht : (∑ j,ψ j.succ*E j a) = ∑ i,(-N i.succ 0/g 0)*D i a := by
    simp_rw [chain,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hmem
    calc
      (∑ j,ψ j.succ*(tangentInverse N g i j*D i a)) =
          (∑ j,ψ j.succ*tangentInverse N g i j)*D i a := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = _ := by rw [hi i]
  rw [ht,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hmem
  field_simp [hg]

theorem quadratic_derivative {K ι : Type*} [Field K] [CharZero K] [Fintype ι]
    (D : Derivation ℤ K K) (H : Matrix ι ι K) (ψ : ι → K)
    (hH : ∀ j k,H j k=H k j) :
    D ((1/2)*(∑ j,∑ k,H j k*ψ j*ψ k)) =
      (∑ j,∑ k,H j k*ψ k*D (ψ j))+
      (1/2)*(∑ j,∑ k,D (H j k)*ψ j*ψ k) := by
  have htwo : D (2 : K)=0 := D.map_natCast 2
  have hhalf : D (1/2 : K)=0 := by rw [Derivation.leibniz_div]; simp [htwo]
  have hs : (∑ j,∑ k,H j k*ψ j*D (ψ k)) = ∑ j,∑ k,H j k*ψ k*D (ψ j) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro k hk
    rw [hH k j]
  have he : (∑ j,∑ k,ψ k*ψ j*D (H j k)) = ∑ j,∑ k,D (H j k)*ψ j*ψ k := by
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro k hk
    ring
  simp only [Derivation.leibniz,smul_eq_mul,hhalf,mul_zero,add_zero,map_sum,
    mul_add,Finset.sum_add_distrib]
  have hf : (∑ j,∑ k,ψ k*H j k*D (ψ j)) = ∑ j,∑ k,H j k*ψ k*D (ψ j) := by
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro k hk
    ring
  simp only [mul_assoc] at he hf
  rw [hs,he,hf]
  ring

theorem quadratic_derivative_normal_jet {K ι : Type*} [Field K] [CharZero K] [Fintype ι]
    (D : Derivation ℤ K K) (H : Matrix ι ι K) (T : ι → ι → ι → K)
    (ψ v : ι → K) (hH : ∀ j k,H j k=H k j)
    (hT : ∀ j k l,T j k l=T l j k)
    (hDH : ∀ j k,D (H j k)=∑ l,T j k l*v l) :
    D ((1/2)*(∑ j,∑ k,H j k*ψ j*ψ k)) =
      (∑ j,((1/2)*(∑ k,∑ l,T j k l*ψ k*ψ l))*v j)+
      ∑ j,(∑ k,H j k*ψ k)*D (ψ j) := by
  rw [quadratic_derivative D H ψ hH]
  have ht : (∑ j,∑ k,D (H j k)*ψ j*ψ k) =
      ∑ l,∑ j,∑ k,T l j k*ψ j*ψ k*v l := by
    simp_rw [hDH,Finset.sum_mul]
    calc
      (∑ j,∑ k,∑ l,T j k l*v l*ψ j*ψ k) =
          ∑ j,∑ l,∑ k,T j k l*v l*ψ j*ψ k := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [Finset.sum_comm]
      _ = ∑ l,∑ j,∑ k,T j k l*v l*ψ j*ψ k := by rw [Finset.sum_comm]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro l hl
        apply Finset.sum_congr rfl
        intro j hj
        apply Finset.sum_congr rfl
        intro k hk
        rw [hT j k l]
        ring
  rw [ht]
  simp only [Finset.sum_mul,Finset.mul_sum]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro l hl
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  ring

theorem determinant_normal_row_coeff_one {K : Type*} [Field K] [CharZero K] {n : ℕ}
    (M : Matrix (Fin (n+1)) (Fin (n+1)) K[X]) (G q : Fin (n+1) → K[X])
    (a b : K) (d : Fin (n+1) → K)
    (hrow : Matrix.vecMul G M =
      (1+C (2*a)*(X : K[X])+C (3*b)*(X : K[X])^2) • (Pi.single (0 : Fin (n+1)) (1 : K[X]))+
      (X : K[X])^2 • (fun j => C (d j))+(X : K[X])^3 • q) :
    (G 0*M.det).coeff 1 =
      (M.submatrix Fin.succ Fin.succ).det.coeff 1+
      2*a*(M.submatrix Fin.succ Fin.succ).det.coeff 0 := by
  have hdet : G 0*M.det=(M.updateRow 0 (Matrix.vecMul G M)).det := by
    have h := Matrix.det_updateRow_sum M 0 G
    have hs : (∑ k, G k • M k) = Matrix.vecMul G M := by
      ext j
      simp [Matrix.vecMul, dotProduct]
    rw [hs] at h
    simpa only [smul_eq_mul] using h.symm
  have ht : (M.updateRow 0 (Pi.single 0 1)).det=(M.submatrix Fin.succ Fin.succ).det := by
    rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
    simp [Matrix.updateRow, Function.update, Matrix.submatrix, Fin.succ_ne_zero]
  rw [hdet,hrow,Matrix.det_updateRow_add,Matrix.det_updateRow_add,
    Matrix.det_updateRow_smul,Matrix.det_updateRow_smul,Matrix.det_updateRow_smul,ht]
  simp [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_succ]
  norm_num [Polynomial.coeff_one, Polynomial.coeff_X]

theorem tangent_determinant_coefficients_zero_one {K : Type*} [Field K] [CharZero K]
    (W A : Matrix (Fin 4) (Fin 4) K) :
    ((1+(X : K[X]) • W.map C)*A.map C).det.coeff 0 = A.det ∧
    ((1+(X : K[X]) • W.map C)*A.map C).det.coeff 1 = A.det*∑ i,W i i := by
  have hmap : (A.map (Polynomial.C : K →+* K[X])).det=C A.det := by
    exact (RingHom.map_det Polynomial.C A).symm
  rw [Matrix.det_mul,hmap]
  have hzero : (1+(X : K[X]) • W.map C).det.coeff 0 = 1 := by
    have h := Polynomial.coeff_det_X_add_C_zero W (1 : Matrix (Fin 4) (Fin 4) K)
    simpa [Matrix.map_one,add_comm] using h
  have hone : (1+(X : K[X]) • W.map C).det.coeff 1 = ∑ i,W i i := by
    simpa [Matrix.trace] using Matrix.coeff_det_one_add_X_smul_one W
  simp only [Polynomial.coeff_mul_C,hzero,hone]
  constructor <;> ring


 omit [CharZero K] in
 theorem tangent_linear_factorization
    (A B W : Matrix (Fin 4) (Fin 4) K) (hB : B=W*A) :
    A.map C+(X : K[X]) • B.map C =
      (1+(X : K[X]) • W.map C)*A.map C := by
  rw [hB,Matrix.map_mul,Matrix.add_mul,Matrix.one_mul,Matrix.smul_mul]

theorem tangent_determinant_coefficient_two
    (W A : Matrix (Fin 4) (Fin 4) K) :
    2*((1+(X : K[X]) • W.map C)*A.map C).det.coeff 2 =
      A.det*((∑ i,W i i)^2-(∑ i,∑ j,W i j*W j i)) := by
  have hmap : (A.map (Polynomial.C : K →+* K[X])).det=C A.det := by
    exact (RingHom.map_det Polynomial.C A).symm
  have heq : ((fun (i j : Fin 4) => C (if i=j then (1:K) else 0)+
      C (W i j)*(X : K[X])) : Matrix (Fin 4) (Fin 4) K[X]) =
      ((1 : Matrix (Fin 4) (Fin 4) K[X])+(X : K[X]) • W.map C) := by
    ext i j
    simp only [Matrix.add_apply,Matrix.one_apply,Matrix.smul_apply,Matrix.map_apply,smul_eq_mul]
    simp only [apply_ite,map_one,map_zero]
    ring
  have h := determinant_linear_coeff_two_four W
  rw [heq] at h
  rw [Matrix.det_mul,hmap,Polynomial.coeff_mul_C]
  linear_combination A.det*h

section Integration
variable [DecidableEq ι]
variable {R : Type*} [CommRing R]

/-- Once the normal-coordinate Taylor calculation is bound to the actual
curve, the remaining primitive construction uses the maintained Piola and
finite polynomial integration theorem. -/
theorem higher_residue_solution_of_density
    (D E : ι → Derivation ℤ K K) (M N : Matrix ι ι K)
    (g J r P : K) (v : ι → K)
    (φ : R →+* K) (t : K) (timeIndex : ι)
    (hconst : ∀ a, D timeIndex (φ a) = 0) (ht : D timeIndex t = 1)
    (hg : g ≠ 0) (hJ : J ≠ 0)
    (hdet : M.det = g*J) (hMN : M*N = 1) (hNM : N*M = 1)
    (chain : ∀ j x, E j x = ∑ k, N k j*D k x)
    (mixed : ∀ i j k, D k (M j i) = D i (M j k))
    (hpoly : P ∈ (Polynomial.eval₂RingHom φ t).range)
    (hjet : P = J*(r+residueDivergence E g v)) :
    ∃ w : ι → K, residueDivergence E g w = -r := by
  obtain ⟨q,hq⟩ := hpoly
  obtain ⟨h,hh⟩ := exists_polynomial_antiderivative (D timeIndex) φ hconst t ht q
  change q.eval₂ φ t = P at hq
  rw [hq] at hh
  exact residue_solution_of_antiderivative D E M N g J hg hJ hdet hMN hNM
    chain mixed v r P h timeIndex hjet hh

end Integration
end SplitHigherResidue
