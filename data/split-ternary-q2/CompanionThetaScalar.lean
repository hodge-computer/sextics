import Proposal.CompanionThetaBridge

/-! The actual first-companion scalar primitive. The evaluated-jet conversion
uses the maintained generic construction from the accepted proof by
1337isnot1337. Prepared with OpenAI Codex assistance for fqlx. -/
noncomputable section
open scoped BigOperators
namespace SplitFElliptic
open Polynomial HoldoutConstruction CrossedElliptic SplitFCompanion
variable {K : Type*} [Field K] [CharZero K]
local instance : Algebra ℤ (E K) := Ring.toIntAlgebra _
abbrev P4 := SplitFCompanion.Poly
abbrev coefficientMap (φ : P2 →+* K) (u : K) : Coeff →+* E K := EllipticCompanion.coefficientMap φ u
abbrev ringMap (φ : P2 →+* K) (u : K) (hu : u^3=φ p) := EllipticCompanion.ringMap p φ u hu

def evaluation (φ : P2 →+* K) (u : K) (hu : u^3=φ p) : P4 →+* E K :=
  (ringMap φ u hu).comp projection
lemma evaluation_univariate (φ : P2 →+* K) (u : K) (hu : u^3=φ p) (q : P4) :
    evaluation φ u hu q=(MvPolynomial.finSuccEquiv ℂ 3 q).eval₂
      (coefficientMap φ u) (algebraMap K (E K) u*b (K:=K)) := rfl
lemma evaluation_C (φ : P2 →+* K) (u : K) (hu : u^3=φ p) (c : ℂ) :
    evaluation φ u hu (MvPolynomial.C c)=algebraMap K (E K) (φ (MvPolynomial.C c)) := by
  rw [evaluation_univariate]
  rw [show MvPolynomial.finSuccEquiv ℂ 3 (MvPolynomial.C c)=C (MvPolynomial.C c)
    from (MvPolynomial.finSuccEquiv ℂ 3).commutes c,Polynomial.eval₂_C,EllipticCompanion.coefficientMap_C]
lemma evaluation_X (φ : P2 →+* K) (u : K) (hu : u^3=φ p) (i : Fin 4) :
    evaluation φ u hu (MvPolynomial.X i)=
      ![algebraMap K (E K) u*b (K:=K),algebraMap K (E K) u*a (K:=K),
        algebraMap K (E K) (φ (MvPolynomial.X 0)),algebraMap K (E K) (φ (MvPolynomial.X 1))] i := by
  have hv : (Fin.cases (Polynomial.X : Polynomial Coeff) (fun j => C (MvPolynomial.X j)))=
      ![X,C (MvPolynomial.X 0),C (MvPolynomial.X 1),C (MvPolynomial.X 2)] := by
    funext j; fin_cases j <;> rfl
  have hx1 := EllipticCompanion.coefficientMap_X_succ φ u 0
  have hx2 := EllipticCompanion.coefficientMap_X_succ φ u 1
  change coefficientMap φ u (MvPolynomial.X 1)=_ at hx1
  change coefficientMap φ u (MvPolynomial.X 2)=_ at hx2
  rw [evaluation_univariate]
  fin_cases i <;>
    simp [MvPolynomial.finSuccEquiv_apply,hv,EllipticCompanion.coefficientMap_S,hx1,hx2]
lemma evaluation_nonzero (φ : P2 →+* K) (hφ : Function.Injective φ)
    (u : K) (hu0 : u≠0) (hu : u^3=φ p) (D : P4)
    (hD : SplitFCompanion.evaluation D≠0) : evaluation φ u hu D≠0 := by
  have hπ : projection D≠0 := by
    intro he
    apply hD
    change algebraMap CoordinateRing AffineField (projection D)=0
    rw [he,map_zero]
  have hh := (EllipticCompanion.ringMap_injective p equation_irreducible φ hφ u hu0 hu).ne hπ
  simpa only [evaluation,RingHom.comp_apply,map_zero] using hh
lemma evaluation_zero (φ : P2 →+* K) (u : K) (hu : u^3=φ p) (P : P4)
    (hP : SplitFCompanion.evaluation P=0) : evaluation φ u hu P=0 := by
  change algebraMap CoordinateRing AffineField (projection P)=0 at hP
  have hπ : projection P=0 := by
    apply IsFractionRing.injective CoordinateRing AffineField
    simpa only [map_zero] using hP
  change ringMap φ u hu (projection P)=0
  rw [hπ,map_zero]

def order : Fin 4 → Fin 4 := ![2,3,1,0]
def ambientD (i : Fin 4) : Derivation ℤ P4 P4 := integerPartial (order i)
def baseGradient (φ : P2 →+* K) (i : Fin 2) : K := φ (integerPartial i p)

lemma evaluation_eq_eval₂ (φ : P2 →+* K) (u : K) (hu : u^3=φ p) :
    evaluation φ u hu=MvPolynomial.eval₂Hom ((algebraMap K (E K)).comp (φ.comp MvPolynomial.C))
      ![algebraMap K (E K) u*b (K:=K),algebraMap K (E K) u*a (K:=K),
        algebraMap K (E K) (φ (MvPolynomial.X 0)),algebraMap K (E K) (φ (MvPolynomial.X 1))] := by
  apply MvPolynomial.ringHom_ext
  · intro c; rw [MvPolynomial.eval₂Hom_C]; exact evaluation_C φ u hu c
  · intro i; rw [evaluation_X,MvPolynomial.eval₂Hom_X']
lemma evaluation_chain (φ : P2 →+* K) (u : K) (hu : u^3=φ p)
    (D : Derivation ℤ (E K) (E K))
    (hc : ∀ c,D (algebraMap K (E K) (φ (MvPolynomial.C c)))=0) (P : P4) :
    D (evaluation φ u hu P)=∑ i,evaluation φ u hu (ambientD i P)*
      D (![algebraMap K (E K) (φ (MvPolynomial.X 0)),algebraMap K (E K) (φ (MvPolynomial.X 1)),
        algebraMap K (E K) u*a (K:=K),algebraMap K (E K) u*b (K:=K)] i) := by
  rw [evaluation_eq_eval₂]
  have hh := derivation_eval₂_chain D ((algebraMap K (E K)).comp (φ.comp MvPolynomial.C))
    ![algebraMap K (E K) u*b (K:=K),algebraMap K (E K) u*a (K:=K),
      algebraMap K (E K) (φ (MvPolynomial.X 0)),algebraMap K (E K) (φ (MvPolynomial.X 1))] hc P
  rw [hh]
  simp [Fin.sum_univ_four,ambientD,order,integerPartial_apply]
  ring

lemma base_expanded : base=MvPolynomial.X 2^6+MvPolynomial.X 3^6+1+
    MvPolynomial.C (5/7 : ℂ)*(MvPolynomial.X 2^5*MvPolynomial.X 3+
      MvPolynomial.X 2^2*MvPolynomial.X 3^3+3*MvPolynomial.X 2+2*MvPolynomial.X 3^5) := by
  apply (MvPolynomial.finSuccEquiv ℂ 3).injective
  rw [base_univariate,coefficient_base_expanded]
  have hv : (Fin.cases (Polynomial.X : Polynomial Coeff) (fun j => C (MvPolynomial.X j)))=
      ![X,C (MvPolynomial.X 0),C (MvPolynomial.X 1),C (MvPolynomial.X 2)] := by
    funext j; fin_cases j <;> rfl
  simp [MvPolynomial.finSuccEquiv_apply,hv,Polynomial.C_ofNat]

lemma evaluated_gradient (φ : P2 →+* K) (u : K) (hu : u^3=φ SplitFCompanion.p) (i : Fin 4) :
    evaluation φ u hu (ambientD i clearedAffineEquation)=7*
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
    simp [ambientD,order,clearedAffineEquation,base_expanded,baseGradient,SplitFCompanion.p,
      integerPartial_apply,MvPolynomial.pderiv_mul,Derivation.leibniz_pow,smul_eq_mul,
      evaluation_X,evaluation_C,hc,hcφ,hcK,hq,map_ofNat,hz2,hz3,hz5,hz6,hz7,hb2,hb3,hb5,hb6,hb7] <;> ring

lemma evaluated_hessian_S (φ : P2 →+* K) (u : K) (hu : u^3=φ SplitFCompanion.p) (i : Fin 4) :
    evaluation φ u hu (ambientD 2 (ambientD i clearedAffineEquation))=
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
    simp [ambientD,order,clearedAffineEquation,base_expanded,integerPartial_apply,
      MvPolynomial.pderiv_mul,Derivation.leibniz_pow,smul_eq_mul,evaluation_X,hc,map_ofNat,hz2,hz3,hz5,hz6,hz7,hb2,hb3,hb5,hb6,hb7] <;> ring

lemma evaluated_hessian_T (φ : P2 →+* K) (u : K) (hu : u^3=φ SplitFCompanion.p) (i : Fin 4) :
    evaluation φ u hu (ambientD 3 (ambientD i clearedAffineEquation))=
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
    simp [ambientD,order,clearedAffineEquation,base_expanded,integerPartial_apply,
      MvPolynomial.pderiv_mul,Derivation.leibniz_pow,smul_eq_mul,evaluation_X,hc,map_ofNat,hz2,hz3,hz5,hz6,hz7,hb2,hb3,hb5,hb6,hb7] <;> ring


lemma base_chain_at (φ : P2 →+* K) (D : Derivation ℤ K K) (j : Fin 2)
    (hc : ∀ c,D (φ (MvPolynomial.C c))=0)
    (hx : ∀ i : Fin 2,D (φ (MvPolynomial.X i))=if i=j then 1 else 0) :
    D (φ SplitFCompanion.p)=baseGradient φ j := by
  have he : φ=MvPolynomial.eval₂Hom (φ.comp MvPolynomial.C) (fun i => φ (MvPolynomial.X i)) := by
    apply MvPolynomial.ringHom_ext
    · intro c; rw [MvPolynomial.eval₂Hom_C]; rfl
    · intro i; rw [MvPolynomial.eval₂Hom_X']
  have h := derivation_eval₂_chain D (φ.comp MvPolynomial.C) (fun i => φ (MvPolynomial.X i)) hc SplitFCompanion.p
  rw [← he] at h
  simpa [hx,baseGradient,integerPartial_apply] using h

lemma cubic_derivative (D : Derivation ℤ K K) (φ : P2 →+* K) (u : K)
    (hu : u^3=φ SplitFCompanion.p) (hu0 : u≠0) :
    D u=D (φ SplitFCompanion.p)/(3*u^2) := by
  have h := congrArg D hu
  simp only [Derivation.leibniz_pow,smul_eq_mul,nsmul_eq_mul] at h
  norm_num only at h
  apply (eq_div_iff (mul_ne_zero (by norm_num) (pow_ne_zero _ hu0))).mpr
  linear_combination h


lemma delta_evaluation_chain (φ : P2 →+* K) (u : K) (hu : u^3=φ SplitFCompanion.p) (p : P4) :
    delta (evaluation φ u hu p)=∑ j,evaluation φ u hu (ambientD j p)*
      ![0,0,algebraMap K (E K) u*b (K:=K)^2,-(algebraMap K (E K) u)*a (K:=K)^2] j := by
  rw [evaluation_chain φ u hu delta (fun _ => delta_base _) p]
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  fin_cases i <;> simp [delta_base,Derivation.leibniz,delta_a,delta_b,smul_eq_mul]

lemma coefficient_evaluation_chain (φ : P2 →+* K) (u : K) (hu : u^3=φ SplitFCompanion.p)
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

lemma evaluation_killed (φ : P2 →+* K) (u : K) (hu : u^3=φ SplitFCompanion.p)
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



lemma source_values (φ : P2 →+* K) (u : K) (hu : u^3=φ p) (hu0 : u≠0) :
    evaluation φ u hu denominator≠0 ∧
    evaluation φ u hu numerator/evaluation φ u hu denominator=
      -7*SplitCompanionScalar.polynomialValue φ h*a/(6*SplitCompanionScalar.rootValue u*b^2) ∧
    (evaluation φ u hu (ambientD 2 numerator)*evaluation φ u hu denominator-
      evaluation φ u hu numerator*evaluation φ u hu (ambientD 2 denominator))/
      (evaluation φ u hu denominator)^2=
      -7*SplitCompanionScalar.polynomialValue φ h/(6*(SplitCompanionScalar.rootValue u)^2*b^2) ∧
    (evaluation φ u hu (ambientD 3 numerator)*evaluation φ u hu denominator-
      evaluation φ u hu numerator*evaluation φ u hu (ambientD 3 denominator))/
      (evaluation φ u hu denominator)^2=
      7*SplitCompanionScalar.polynomialValue φ h*a/(3*(SplitCompanionScalar.rootValue u)^2*b^3) := by
  have hu' : (algebraMap K (E K) u)≠0 := by
    simpa only [map_zero] using (algebraMap K (E K)).injective.ne hu0
  have hb := SplitCompanionScalar.b_ne_zero (K:=K)
  have hc (n : ℕ) : evaluation φ u hu (n : P4)=(n : E K) := map_natCast _ n
  have hz7 (j : Fin 4) : MvPolynomial.pderiv (R:=ℂ) j (7 : P4)=0 := (MvPolynomial.pderiv j).map_natCast 7
  have hz6 (j : Fin 4) : MvPolynomial.pderiv (R:=ℂ) j (6 : P4)=0 := (MvPolynomial.pderiv j).map_natCast 6
  refine ⟨?_,?_,?_,?_⟩ <;>
    simp [numerator,denominator,ambientD,order,integerPartial_apply,
      MvPolynomial.pderiv_mul,Derivation.leibniz_pow,map_neg,smul_eq_mul,hz7,hz6,
      evaluation_X,map_ofNat,SplitCompanionScalar.polynomialValue,SplitCompanionScalar.rootValue,h,
      map_mul,map_pow,hu',hb] <;>
    field_simp [hu',hb] <;> ring

/-- Scalar conversion of the actual first companion, with its source
A_num/Q=-7*x4*a3*S/(6*T²) and every denominator checked by injection. -/
theorem theta_primitive_of_polynomial_data (φ : P2 →+* K) (hφ : Function.Injective φ)
    (u : K) (hu0 : u≠0) (hu : u^3=φ p)
    (Dx Dy : Derivation ℤ K K)
    (hcx : ∀ c,Dx (φ (MvPolynomial.C c))=0)
    (hcy : ∀ c,Dy (φ (MvPolynomial.C c))=0)
    (hxx : ∀ i : Fin 2,Dx (φ (MvPolynomial.X i))=if i=0 then 1 else 0)
    (hyy : ∀ i : Fin 2,Dy (φ (MvPolynomial.X i))=if i=1 then 1 else 0)
    (D : P4) (N : Fin 4 → P4) (hd : SplitFCompanion.evaluation D≠0)
    (hn : denominator*(∑ i,N i*integerPartial i clearedAffineEquation)=numerator*D)
    (hdiv : SplitFCompanion.evaluation
      (D*(∑ i,integerPartial i (N i))-(∑ i,N i*integerPartial i D))=0) :
    ∃ bf cx cy : E K,
      (delta bf+coefficient Dx cx+coefficient Dy cy=
        algebraMap K (E K) (φ h/u^5)*thetaRatio) ∧
      ∀ Z : Derivation ℤ K K,(∀ P : P2,Z (φ P)=0) → Z u=0 →
        coefficient Z bf=0 ∧ coefficient Z cx=0 ∧ coefficient Z cy=0 := by
  let ρ := evaluation φ u hu
  let nn : Fin 4 → P4 := fun i => N (order i)
  have hd' : ρ D≠0 := evaluation_nonzero φ hφ u hu0 hu D hd
  have hn' : denominator*(∑ i,nn i*ambientD i clearedAffineEquation)=numerator*D := by
    simp [nn,order,ambientD,Fin.sum_univ_four] at hn ⊢
    linear_combination hn
  have hdiv' : ρ (D*(∑ i,ambientD i (nn i))-(∑ i,nn i*ambientD i D))=0 := by
    have he : D*(∑ i,ambientD i (nn i))-(∑ i,nn i*ambientD i D)=
        D*(∑ i,integerPartial i (N i))-(∑ i,N i*integerPartial i D) := by
      simp [nn,order,ambientD,Fin.sum_univ_four]
      ring
    rw [he]
    exact evaluation_zero φ u hu _ hdiv
  obtain ⟨hq,hs,hss,hst⟩ := source_values φ u hu hu0
  have hgrad (i : Fin 4) : ρ (ambientD i clearedAffineEquation)=
      ![7*SplitCompanionScalar.gradientValue φ p 0,7*SplitCompanionScalar.gradientValue φ p 1,
        21*(SplitCompanionScalar.rootValue u)^2*a^2,21*(SplitCompanionScalar.rootValue u)^2*b^2] i := by
    have he := evaluated_gradient φ u hu i
    fin_cases i <;> simp [ρ,SplitCompanionScalar.gradientValue,SplitCompanionScalar.polynomialValue,
      SplitCompanionScalar.rootValue,baseGradient,integerPartial_apply] at he ⊢ <;> linear_combination he
  have hessS (i : Fin 4) : ρ (ambientD 2 (ambientD i clearedAffineEquation))=
      ![0,0,42*SplitCompanionScalar.rootValue u*a,0] i := evaluated_hessian_S φ u hu i
  have hessT (i : Fin 4) : ρ (ambientD 3 (ambientD i clearedAffineEquation))=
      ![0,0,0,42*SplitCompanionScalar.rootValue u*b] i := evaluated_hessian_T φ u hu i
  have hdx (P : P4) : coefficient Dx (ρ P)=∑ j,ρ (ambientD j P)*
      ![1,0,a*SplitCompanionScalar.gradientValue φ p 0/(3*(SplitCompanionScalar.rootValue u)^2),
        b*SplitCompanionScalar.gradientValue φ p 0/(3*(SplitCompanionScalar.rootValue u)^2)] j := by
    rw [coefficient_evaluation_chain φ u hu hu0 Dx 0 hcx hxx]
    simp [ρ,Fin.sum_univ_four,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val]
    simp only [baseGradient,SplitCompanionScalar.gradientValue,SplitCompanionScalar.polynomialValue,
      SplitCompanionScalar.rootValue,integerPartial_apply]
    ring
  have hdy (P : P4) : coefficient Dy (ρ P)=∑ j,ρ (ambientD j P)*
      ![0,1,a*SplitCompanionScalar.gradientValue φ p 1/(3*(SplitCompanionScalar.rootValue u)^2),
        b*SplitCompanionScalar.gradientValue φ p 1/(3*(SplitCompanionScalar.rootValue u)^2)] j := by
    rw [coefficient_evaluation_chain φ u hu hu0 Dy 1 hcy hyy]
    simp [ρ,Fin.sum_univ_four,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val]
    simp only [baseGradient,SplitCompanionScalar.gradientValue,SplitCompanionScalar.polynomialValue,
      SplitCompanionScalar.rootValue,integerPartial_apply]
    ring
  let v := SplitCompanionScalar.jetData_of_polynomial_rational_source p h φ u Dx Dy
    ρ ambientD D numerator denominator nn (fun i => ambientD i clearedAffineEquation)
    hd' hq hn' hdiv' hgrad hessS hessT hs hss hst (delta_evaluation_chain φ u hu) hdx hdy
    (fun Z hZ hZu P => evaluation_killed φ u hu Z hZ hZu P)
  apply SplitCompanionScalar.theta_primitive_of_jets p h φ u Dx Dy hu0
  · rw [cubic_derivative Dx φ u hu hu0,base_chain_at φ Dx 0 hcx hxx]
    rfl
  · rw [cubic_derivative Dy φ u hu hu0,base_chain_at φ Dy 1 hcy hyy]
    rfl
  · exact v

/-- This final scalar interface has only the geometric cone-density existence
left to supply through its affine residue extraction. -/
theorem theta_scalar_primitive_of_affine_residue (φ : P2 →+* K) (hφ : Function.Injective φ)
    (u : K) (hu0 : u≠0) (hu : u^3=φ p)
    (Dx Dy : Derivation ℤ K K)
    (hcx : ∀ c,Dx (φ (MvPolynomial.C c))=0)
    (hcy : ∀ c,Dy (φ (MvPolynomial.C c))=0)
    (hxx : ∀ i : Fin 2,Dx (φ (MvPolynomial.X i))=if i=0 then 1 else 0)
    (hyy : ∀ i : Fin 2,Dy (φ (MvPolynomial.X i))=if i=1 then 1 else 0)
    (hex : ∃ w : Fin 3 → AffineField,
      residueDivergence tangent (21*normal^2) w=affineDensity) :
    ∃ bf cx cy : E K,
      (delta bf+coefficient Dx cx+coefficient Dy cy=
        algebraMap K (E K) (φ h/u^5)*thetaRatio) ∧
      ∀ Z : Derivation ℤ K K,(∀ P : P2,Z (φ P)=0) → Z u=0 →
        coefficient Z bf=0 ∧ coefficient Z cx=0 ∧ coefficient Z cy=0 := by
  obtain ⟨D,N,hD,hn,hdiv⟩ := source_data_of_affine_residue hex
  exact theta_primitive_of_polynomial_data φ hφ u hu0 hu Dx Dy hcx hcy hxx hyy D N hD hn hdiv

/-- Final scalar interface: the only geometric input is the exact T-normal
cone density primitive provided by the higher-pole family construction. -/
theorem theta_scalar_primitive (φ : P2 →+* K) (hφ : Function.Injective φ)
    (u : K) (hu0 : u≠0) (hu : u^3=φ p)
    (Dx Dy : Derivation ℤ K K)
    (hcx : ∀ c,Dx (φ (MvPolynomial.C c))=0)
    (hcy : ∀ c,Dy (φ (MvPolynomial.C c))=0)
    (hxx : ∀ i : Fin 2,Dx (φ (MvPolynomial.X i))=if i=0 then 1 else 0)
    (hyy : ∀ i : Fin 2,Dy (φ (MvPolynomial.X i))=if i=1 then 1 else 0)
    (hex : ConeDensityPrimitive) :
    ∃ bf cx cy : E K,
      (delta bf+coefficient Dx cx+coefficient Dy cy=
        algebraMap K (E K) (φ h/u^5)*thetaRatio) ∧
      ∀ Z : Derivation ℤ K K,(∀ P : P2,Z (φ P)=0) → Z u=0 →
        coefficient Z bf=0 ∧ coefficient Z cx=0 ∧ coefficient Z cy=0 := by
  apply theta_scalar_primitive_of_affine_residue φ hφ u hu0 hu Dx Dy hcx hcy hxx hyy
  exact affine_residue_of_cone hex
end SplitFElliptic

#print axioms SplitFElliptic.theta_scalar_primitive
