import Proposal.CompanionPrimitives

/-!
Elliptic specialization of the exact second companion. The target-specific
polynomial derivatives and degree-five source adapt the accepted scalar-jet
argument of 1337isnot1337. Prepared with OpenAI Codex assistance for fqlx.
-/
noncomputable section
open scoped BigOperators

namespace SplitGCompanion

def cubicProjection : Poly →+* EllipticCompanion.CoordinateRing p :=
  (AdjoinRoot.mk (EllipticCompanion.equation p)).comp
    ((MvPolynomial.finSuccEquiv ℂ 3).toRingHom.comp (MvPolynomial.rename reverse).toRingHom)
lemma old_projection_kernel (q : Poly) : projection q=0 ↔ affineEquation ∣ q := by
  change AdjoinRoot.mk equation (MvPolynomial.finSuccEquiv ℂ 3 q)=0 ↔ _
  rw [AdjoinRoot.mk_eq_zero,← old_univariate]
  exact map_dvd_iff (MvPolynomial.finSuccEquiv ℂ 3)
lemma cubic_projection_kernel (q : Poly) : cubicProjection q=0 ↔ affineEquation ∣ q := by
  change AdjoinRoot.mk (EllipticCompanion.equation p) (MvPolynomial.finSuccEquiv ℂ 3
    (MvPolynomial.rename reverse q))=0 ↔ _
  rw [AdjoinRoot.mk_eq_zero,← new_univariate,map_dvd_iff (MvPolynomial.finSuccEquiv ℂ 3)]
  exact map_dvd_iff (MvPolynomial.renameEquiv (R:=ℂ) reverse)
lemma cubic_nonzero_of_evaluation (q : Poly) (hq : evaluation q≠0) : cubicProjection q≠0 := by
  intro h
  apply hq
  change algebraMap CoordinateRing AffineField (projection q)=0
  rw [(old_projection_kernel q).mpr ((cubic_projection_kernel q).mp h),map_zero]
lemma cubic_zero_of_evaluation (q : Poly) (hq : evaluation q=0) : cubicProjection q=0 := by
  change algebraMap CoordinateRing AffineField (projection q)=0 at hq
  have hπ : projection q=0 := by
    apply IsFractionRing.injective CoordinateRing AffineField
    simpa only [map_zero] using hq
  exact (cubic_projection_kernel q).mpr ((old_projection_kernel q).mp hπ)
end SplitGCompanion

namespace SplitGElliptic
open Polynomial HoldoutConstruction CrossedElliptic SplitGCompanion
variable {K : Type*} [Field K] [CharZero K]
local instance : Algebra ℤ (E K) := Ring.toIntAlgebra _
abbrev P4 := SplitGCompanion.Poly
abbrev coefficientMap (φ : P2 →+* K) (u : K) : Coeff →+* E K := EllipticCompanion.coefficientMap φ u
abbrev ringMap (φ : P2 →+* K) (u : K) (hu : u^3=φ p) := EllipticCompanion.ringMap p φ u hu

def ellipticEvaluation (φ : P2 →+* K) (u : K) (hu : u^3=φ p) : P4 →+* E K :=
  (ringMap φ u hu).comp cubicProjection
lemma ellipticEvaluation_univariate (φ : P2 →+* K) (u : K) (hu : u^3=φ p) (q : P4) :
    ellipticEvaluation φ u hu q=(MvPolynomial.finSuccEquiv ℂ 3 (MvPolynomial.rename reverse q)).eval₂
      (coefficientMap φ u) (algebraMap K (E K) u*b (K:=K)) := rfl
lemma ellipticEvaluation_C (φ : MvPolynomial (Fin 2) ℂ →+* K) (u : K) (hu : u^3=φ p) (c : ℂ) :
    ellipticEvaluation φ u hu (MvPolynomial.C c)=algebraMap K (E K) (φ (MvPolynomial.C c)) := by
  rw [ellipticEvaluation_univariate,MvPolynomial.rename_C]
  rw [show MvPolynomial.finSuccEquiv ℂ 3 (MvPolynomial.C c)=C (MvPolynomial.C c)
    from (MvPolynomial.finSuccEquiv ℂ 3).commutes c,Polynomial.eval₂_C,EllipticCompanion.coefficientMap_C]

lemma ellipticEvaluation_X (φ : MvPolynomial (Fin 2) ℂ →+* K) (u : K) (hu : u^3=φ p) (i : Fin 4) :
    ellipticEvaluation φ u hu (MvPolynomial.X i)=
      ![algebraMap K (E K) (φ (MvPolynomial.X 1)),algebraMap K (E K) (φ (MvPolynomial.X 0)),
        algebraMap K (E K) u*a (K:=K),algebraMap K (E K) u*b (K:=K)] i := by
  have hv : (Fin.cases (Polynomial.X : Polynomial Coeff)
      (fun j => C (MvPolynomial.X j)))=![X,C (MvPolynomial.X 0),C (MvPolynomial.X 1),C (MvPolynomial.X 2)] := by
    funext j; fin_cases j <;> rfl
  have hx1 := EllipticCompanion.coefficientMap_X_succ φ u 0
  have hx2 := EllipticCompanion.coefficientMap_X_succ φ u 1
  change coefficientMap φ u (MvPolynomial.X 1)=_ at hx1
  change coefficientMap φ u (MvPolynomial.X 2)=_ at hx2
  rw [ellipticEvaluation_univariate,MvPolynomial.rename_X]
  fin_cases i <;>
    simp [SplitGCompanion.reverse,MvPolynomial.finSuccEquiv_apply,hv,EllipticCompanion.coefficientMap_S,hx1,hx2]

lemma ellipticEvaluation_denominator_nonzero (φ : MvPolynomial (Fin 2) ℂ →+* K) (hφ : Function.Injective φ)
    (u : K) (hu0 : u≠0) (hu : u^3=φ p) (D : MvPolynomial (Fin 4) ℂ)
    (hD : SplitGCompanion.evaluation D≠0) : ellipticEvaluation φ u hu D≠0 := by
  have h := (EllipticCompanion.ringMap_injective p cubic_irreducible φ hφ u hu0 hu).ne (cubic_nonzero_of_evaluation D hD)
  change ringMap φ u hu (cubicProjection D)≠0
  simpa only [map_zero] using h

lemma ellipticEvaluation_zero_of_old (φ : MvPolynomial (Fin 2) ℂ →+* K) (u : K) (hu : u^3=φ p)
    (p : MvPolynomial (Fin 4) ℂ) (hp : SplitGCompanion.evaluation p=0) : ellipticEvaluation φ u hu p=0 := by
  change ringMap φ u hu (cubicProjection p)=0
  rw [cubic_zero_of_evaluation p hp,map_zero]

def swap : Fin 4 → Fin 4 := ![1,0,2,3]
def ambientD (i : Fin 4) : Derivation ℤ P4 P4 := integerPartial (swap i)
def baseGradient (φ : P2 →+* K) (i : Fin 2) : K := φ (integerPartial i SplitGCompanion.p)

lemma ellipticEvaluation_eq_eval₂ (φ : P2 →+* K) (u : K) (hu : u^3=φ SplitGCompanion.p) :
    ellipticEvaluation φ u hu=MvPolynomial.eval₂Hom ((algebraMap K (E K)).comp (φ.comp MvPolynomial.C))
      ![algebraMap K (E K) (φ (MvPolynomial.X 1)),algebraMap K (E K) (φ (MvPolynomial.X 0)),
        algebraMap K (E K) u*a (K:=K),algebraMap K (E K) u*b (K:=K)] := by
  apply MvPolynomial.ringHom_ext
  · intro c; rw [MvPolynomial.eval₂Hom_C]; exact ellipticEvaluation_C φ u hu c
  · intro i; rw [ellipticEvaluation_X,MvPolynomial.eval₂Hom_X']

lemma ellipticEvaluation_chain (φ : P2 →+* K) (u : K) (hu : u^3=φ SplitGCompanion.p)
    (D : Derivation ℤ (E K) (E K))
    (hc : ∀ c,D (algebraMap K (E K) (φ (MvPolynomial.C c)))=0) (p : P4) :
    D (ellipticEvaluation φ u hu p)=∑ i,ellipticEvaluation φ u hu (ambientD i p)*
      D (![algebraMap K (E K) (φ (MvPolynomial.X 0)),algebraMap K (E K) (φ (MvPolynomial.X 1)),
        algebraMap K (E K) u*a (K:=K),algebraMap K (E K) u*b (K:=K)] i) := by
  rw [ellipticEvaluation_eq_eval₂]
  have hh := derivation_eval₂_chain D ((algebraMap K (E K)).comp (φ.comp MvPolynomial.C))
    ![algebraMap K (E K) (φ (MvPolynomial.X 1)),algebraMap K (E K) (φ (MvPolynomial.X 0)),
      algebraMap K (E K) u*a (K:=K),algebraMap K (E K) u*b (K:=K)] hc p
  rw [hh]
  simp [Fin.sum_univ_four,ambientD,swap,integerPartial_apply]
  ring

lemma evaluated_gradient (φ : P2 →+* K) (u : K) (hu : u^3=φ SplitGCompanion.p) (i : Fin 4) :
    ellipticEvaluation φ u hu (ambientD i clearedAffineEquation)=7*
      ![algebraMap K (E K) (baseGradient φ 0),algebraMap K (E K) (baseGradient φ 1),
        3*(algebraMap K (E K) u)^2*a (K:=K)^2,
        3*(algebraMap K (E K) u)^2*b (K:=K)^2] i := by
  have hc (n : ℕ) : ellipticEvaluation φ u hu (n : P4)=(n : E K) := map_natCast _ n
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
    simp [ambientD,swap,clearedAffineEquation,SplitCompanion.H,SplitCompanion.second,baseGradient,SplitGCompanion.p,
      integerPartial_apply,MvPolynomial.pderiv_mul,Derivation.leibniz_pow,smul_eq_mul,
      ellipticEvaluation_X,ellipticEvaluation_C,hc,hcφ,hcK,hq,map_ofNat,hz2,hz3,hz5,hz6,hz7,hb2,hb3,hb5,hb6,hb7] <;> ring

lemma evaluated_hessian_S (φ : P2 →+* K) (u : K) (hu : u^3=φ SplitGCompanion.p) (i : Fin 4) :
    ellipticEvaluation φ u hu (ambientD 2 (ambientD i clearedAffineEquation))=
      ![0,0,42*algebraMap K (E K) u*a (K:=K),0] i := by
  have hc (n : ℕ) : ellipticEvaluation φ u hu (n : P4)=(n : E K) := map_natCast _ n
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
    simp [ambientD,swap,clearedAffineEquation,SplitCompanion.H,SplitCompanion.second,integerPartial_apply,
      MvPolynomial.pderiv_mul,Derivation.leibniz_pow,smul_eq_mul,ellipticEvaluation_X,hc,map_ofNat,hz2,hz3,hz5,hz6,hz7,hb2,hb3,hb5,hb6,hb7] <;> ring

lemma evaluated_hessian_T (φ : P2 →+* K) (u : K) (hu : u^3=φ SplitGCompanion.p) (i : Fin 4) :
    ellipticEvaluation φ u hu (ambientD 3 (ambientD i clearedAffineEquation))=
      ![0,0,0,42*algebraMap K (E K) u*b (K:=K)] i := by
  have hc (n : ℕ) : ellipticEvaluation φ u hu (n : P4)=(n : E K) := map_natCast _ n
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
    simp [ambientD,swap,clearedAffineEquation,SplitCompanion.H,SplitCompanion.second,integerPartial_apply,
      MvPolynomial.pderiv_mul,Derivation.leibniz_pow,smul_eq_mul,ellipticEvaluation_X,hc,map_ofNat,hz2,hz3,hz5,hz6,hz7,hb2,hb3,hb5,hb6,hb7] <;> ring

lemma base_chain (φ : P2 →+* K) (D : Derivation ℤ K K)
    (hc : ∀ c,D (φ (MvPolynomial.C c))=0)
    (hx : ∀ i : Fin 2,D (φ (MvPolynomial.X i))=if i=0 then 1 else 0) :
    D (φ SplitGCompanion.p)=baseGradient φ 0 := by
  have he : φ=MvPolynomial.eval₂Hom (φ.comp MvPolynomial.C) (fun i => φ (MvPolynomial.X i)) := by
    apply MvPolynomial.ringHom_ext
    · intro c; rw [MvPolynomial.eval₂Hom_C]; rfl
    · intro i; rw [MvPolynomial.eval₂Hom_X']
  have h := derivation_eval₂_chain D (φ.comp MvPolynomial.C) (fun i => φ (MvPolynomial.X i)) hc SplitGCompanion.p
  rw [← he] at h
  simpa [Fin.sum_univ_succ,hx,baseGradient,integerPartial_apply] using h

lemma base_chain_at (φ : P2 →+* K) (D : Derivation ℤ K K) (j : Fin 2)
    (hc : ∀ c,D (φ (MvPolynomial.C c))=0)
    (hx : ∀ i : Fin 2,D (φ (MvPolynomial.X i))=if i=j then 1 else 0) :
    D (φ SplitGCompanion.p)=baseGradient φ j := by
  have he : φ=MvPolynomial.eval₂Hom (φ.comp MvPolynomial.C) (fun i => φ (MvPolynomial.X i)) := by
    apply MvPolynomial.ringHom_ext
    · intro c; rw [MvPolynomial.eval₂Hom_C]; rfl
    · intro i; rw [MvPolynomial.eval₂Hom_X']
  have h := derivation_eval₂_chain D (φ.comp MvPolynomial.C) (fun i => φ (MvPolynomial.X i)) hc SplitGCompanion.p
  rw [← he] at h
  simpa [hx,baseGradient,integerPartial_apply] using h

lemma cubic_derivative (D : Derivation ℤ K K) (φ : P2 →+* K) (u : K)
    (hu : u^3=φ SplitGCompanion.p) (hu0 : u≠0) :
    D u=D (φ SplitGCompanion.p)/(3*u^2) := by
  have h := congrArg D hu
  simp only [Derivation.leibniz_pow,smul_eq_mul,nsmul_eq_mul] at h
  norm_num only at h
  apply (eq_div_iff (mul_ne_zero (by norm_num) (pow_ne_zero _ hu0))).mpr
  linear_combination h

open CrossedEvaluatedJets CrossedScalarCompanionJet
lemma data_reindex (A D N₀ : P4) (N : Fin 3 → P4)
    (hn : N₀*integerPartial 0 clearedAffineEquation+
      ∑ i,N i*integerPartial i.succ clearedAffineEquation=A*D) :
    (∑ i,![N 0,N₀,N 1,N 2] i*ambientD i clearedAffineEquation)=A*D := by
  simp [Fin.sum_univ_four,Fin.sum_univ_succ,ambientD,swap] at hn ⊢
  linear_combination hn

lemma divergence_reindex (D N₀ : P4) (N : Fin 3 → P4) :
    D*(∑ i,ambientD i (![N 0,N₀,N 1,N 2] i))-
      (∑ i,![N 0,N₀,N 1,N 2] i*ambientD i D)=
    residueDivNum (integerPartial 0) (fun i : Fin 3 => integerPartial i.succ) D N₀ N := by
  change _=D*(integerPartial 0 N₀+∑ i : Fin 3,integerPartial i.succ (N i))-
    (N₀*integerPartial 0 D+∑ i : Fin 3,N i*integerPartial i.succ D)
  simp [Fin.sum_univ_four,Fin.sum_univ_succ,ambientD,swap]
  ring

lemma delta_evaluation_chain (φ : P2 →+* K) (u : K) (hu : u^3=φ SplitGCompanion.p) (p : P4) :
    delta (ellipticEvaluation φ u hu p)=∑ j,ellipticEvaluation φ u hu (ambientD j p)*
      ![0,0,algebraMap K (E K) u*b (K:=K)^2,-(algebraMap K (E K) u)*a (K:=K)^2] j := by
  rw [ellipticEvaluation_chain φ u hu delta (fun _ => delta_base _) p]
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  fin_cases i <;> simp [delta_base,Derivation.leibniz,delta_a,delta_b,smul_eq_mul]

lemma coefficient_evaluation_chain (φ : P2 →+* K) (u : K) (hu : u^3=φ SplitGCompanion.p)
    (hu0 : u≠0) (D : Derivation ℤ K K) (j : Fin 2)
    (hc : ∀ c,D (φ (MvPolynomial.C c))=0)
    (hx : ∀ i : Fin 2,D (φ (MvPolynomial.X i))=if i=j then 1 else 0) (p : P4) :
    coefficient D (ellipticEvaluation φ u hu p)=∑ i,ellipticEvaluation φ u hu (ambientD i p)*
      ![if j=0 then 1 else 0,if j=1 then 1 else 0,
        algebraMap K (E K) (baseGradient φ j)/(3*(algebraMap K (E K) u)^2)*a (K:=K),
        algebraMap K (E K) (baseGradient φ j)/(3*(algebraMap K (E K) u)^2)*b (K:=K)] i := by
  have du := cubic_derivative D φ u hu hu0
  rw [base_chain_at φ D j hc hx] at du
  rw [ellipticEvaluation_chain φ u hu (coefficient D) (by intro c; rw [coefficient_scalar,hc,map_zero]) p]
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  fin_cases i <;>
    simp [coefficient_scalar,hx,Derivation.leibniz,coefficient_a,coefficient_b,smul_eq_mul,
      du,map_div₀,map_mul,map_pow,map_ofNat,eq_comm] <;> ring

lemma ellipticEvaluation_killed (φ : P2 →+* K) (u : K) (hu : u^3=φ SplitGCompanion.p)
    (D : Derivation ℤ K K) (hφ : ∀ p,D (φ p)=0) (huD : D u=0) (p : P4) :
    coefficient D (ellipticEvaluation φ u hu p)=0 := by
  rw [ellipticEvaluation_chain φ u hu (coefficient D) (by intro c; rw [coefficient_scalar,hφ,map_zero]) p]
  apply Finset.sum_eq_zero
  intro i hi
  have hz : coefficient D
      (![algebraMap K (E K) (φ (MvPolynomial.X 0)),algebraMap K (E K) (φ (MvPolynomial.X 1)),
        algebraMap K (E K) u*a (K:=K),algebraMap K (E K) u*b (K:=K)] i)=0 := by
    fin_cases i <;> simp [coefficient_scalar,hφ,huD,Derivation.leibniz,coefficient_a,coefficient_b,smul_eq_mul]
  rw [hz,mul_zero]

/-- The actual affine polynomial data yield a scalar primitive on the cubic cover. -/
theorem scalar_primitive_of_data (φ : P2 →+* K) (hφ : Function.Injective φ)
    (u : K) (hu0 : u≠0) (hu : u^3=φ SplitGCompanion.p)
    (Dx Dy : Derivation ℤ K K)
    (hcx : ∀ c,Dx (φ (MvPolynomial.C c))=0)
    (hcy : ∀ c,Dy (φ (MvPolynomial.C c))=0)
    (hxx : ∀ i : Fin 2,Dx (φ (MvPolynomial.X i))=if i=0 then 1 else 0)
    (hyy : ∀ i : Fin 2,Dy (φ (MvPolynomial.X i))=if i=1 then 1 else 0)
    (A D N₀ : P4) (N : Fin 3 → P4) (hd : SplitGCompanion.evaluation D≠0)
    (hn : N₀*integerPartial 0 clearedAffineEquation+
      ∑ i,N i*integerPartial i.succ clearedAffineEquation=A*D)
    (hdiv : SplitGCompanion.evaluation
      (residueDivNum (integerPartial 0) (fun i : Fin 3 => integerPartial i.succ) D N₀ N)=0) :
    ∃ bf cx cy : E K,(delta bf+coefficient Dx cx+coefficient Dy cy=
      ellipticEvaluation φ u hu A/(7*(algebraMap K (E K) u)^4)-
      (a (K:=K)*ellipticEvaluation φ u hu (ambientD 2 A)+b (K:=K)*ellipticEvaluation φ u hu (ambientD 3 A))/
        (7*(algebraMap K (E K) u)^3)) ∧
      ∀ D : Derivation ℤ K K,(∀ p,D (φ p)=0) → D u=0 →
        coefficient D bf=0 ∧ coefficient D cx=0 ∧ coefficient D cy=0 := by
  let ρ := ellipticEvaluation φ u hu
  let nn : Fin 4 → P4 := ![N 0,N₀,N 1,N 2]
  let vv := values ρ D nn
  let jj := jet ρ ambientD D nn
  let uu := algebraMap K (E K) u
  let px := algebraMap K (E K) (baseGradient φ 0)
  let py := algebraMap K (E K) (baseGradient φ 1)
  have hd' : ρ D≠0 := ellipticEvaluation_denominator_nonzero φ hφ u hu0 hu D hd
  have hu' : uu≠0 := by simpa only [map_zero] using (algebraMap K (E K)).injective.ne hu0
  have hn' := data_reindex A D N₀ N hn
  have hv := normal_values ρ D A nn (fun i => ambientD i clearedAffineEquation) hd' hn'
  have hs := normal_jets ρ ambientD D A nn (fun i => ambientD i clearedAffineEquation) hd' hn' 2
  have ht := normal_jets ρ ambientD D A nn (fun i => ambientD i clearedAffineEquation) hd' hn' 3
  have hdv := divergence_jets ρ ambientD D nn hd'
    ((congrArg ρ (divergence_reindex D N₀ N)).trans (ellipticEvaluation_zero_of_old φ u hu _ hdiv))
  change (∑ i,jj i i)=0 at hdv
  have hg (i : Fin 4) : ρ (ambientD i clearedAffineEquation)=
      7*![px,py,3*uu^2*a (K:=K)^2,3*uu^2*b (K:=K)^2] i := evaluated_gradient φ u hu i
  have hgs (i : Fin 4) : ρ (ambientD 2 (ambientD i clearedAffineEquation))=
      ![0,0,42*uu*a (K:=K),0] i := evaluated_hessian_S φ u hu i
  have hgt (i : Fin 4) : ρ (ambientD 3 (ambientD i clearedAffineEquation))=
      ![0,0,0,42*uu*b (K:=K)] i := evaluated_hessian_T φ u hu i
  change (∑ i,vv i*ρ (ambientD i clearedAffineEquation))=ρ A at hv
  change (∑ i,jj i 2*ρ (ambientD i clearedAffineEquation))+
    (∑ i,vv i*ρ (ambientD 2 (ambientD i clearedAffineEquation)))=ρ (ambientD 2 A) at hs
  change (∑ i,jj i 3*ρ (ambientD i clearedAffineEquation))+
    (∑ i,vv i*ρ (ambientD 3 (ambientD i clearedAffineEquation)))=ρ (ambientD 3 A) at ht
  simp only [hg,hgs,hgt,Fin.sum_univ_four] at hv hs ht
  simp at hv hs ht
  have hδ (i : Fin 4) := derivative_values ρ ambientD delta
    ![0,0,uu*b (K:=K)^2,-uu*a (K:=K)^2] (delta_evaluation_chain φ u hu) D nn hd' i
  have hx (i : Fin 4) := derivative_values ρ ambientD (coefficient Dx)
    ![1,0,px/(3*uu^2)*a (K:=K),px/(3*uu^2)*b (K:=K)]
    (coefficient_evaluation_chain φ u hu hu0 Dx 0 hcx hxx) D nn hd' i
  have hy (i : Fin 4) := derivative_values ρ ambientD (coefficient Dy)
    ![0,1,py/(3*uu^2)*a (K:=K),py/(3*uu^2)*b (K:=K)]
    (coefficient_evaluation_chain φ u hu hu0 Dy 1 hcy hyy) D nn hd' i
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
    have hzρ (p : P4) : coefficient Dz (ρ p)=0 := ellipticEvaluation_killed φ u hu Dz hzφ hzu p
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


lemma source_scalar (φ : P2 →+* K) (u : K) (hu : u^3=φ p) :
    ellipticEvaluation φ u hu source/(7*(algebraMap K (E K) u)^4)-
      (a (K:=K)*ellipticEvaluation φ u hu (ambientD 2 source)+
       b (K:=K)*ellipticEvaluation φ u hu (ambientD 3 source))/(7*(algebraMap K (E K) u)^3)=
    algebraMap K (E K) (φ (MvPolynomial.X 0)^3*φ (MvPolynomial.X 1)^2/u^4) := by
  have h7 (i : Fin 4) : MvPolynomial.pderiv (R:=ℂ) i (7 : P4)=0 := (MvPolynomial.pderiv i).map_natCast 7
  simp [source,ambientD,swap,integerPartial_apply,ellipticEvaluation_X,map_div₀,map_ofNat,h7]
  <;> ring

/-- The actual ordinary scalar primitive for the protected second ternary. -/
theorem ordinary_scalar_primitive (φ : P2 →+* K) (hφ : Function.Injective φ)
    (u : K) (hu0 : u≠0) (hu : u^3=φ p)
    (Dx Dy : Derivation ℤ K K)
    (hcx : ∀ c,Dx (φ (MvPolynomial.C c))=0)
    (hcy : ∀ c,Dy (φ (MvPolynomial.C c))=0)
    (hxx : ∀ i : Fin 2,Dx (φ (MvPolynomial.X i))=if i=0 then 1 else 0)
    (hyy : ∀ i : Fin 2,Dy (φ (MvPolynomial.X i))=if i=1 then 1 else 0) :
    ∃ bf cr cz : E K,
      (delta bf+coefficient Dx cr+coefficient Dy cz=
        algebraMap K (E K) (φ (MvPolynomial.X 0)^3*φ (MvPolynomial.X 1)^2/u^4)) ∧
      ∀ D : Derivation ℤ K K,(∀ q,D (φ q)=0) → D u=0 →
        coefficient D bf=0 ∧ coefficient D cr=0 ∧ coefficient D cz=0 := by
  obtain ⟨D,N₀,N,hd,hn,hdiv⟩ := source_data
  obtain ⟨bf,cr,cz,he,hkill⟩ := scalar_primitive_of_data φ hφ u hu0 hu Dx Dy hcx hcy hxx hyy
    source D N₀ N hd hn hdiv
  exact ⟨bf,cr,cz,(source_scalar φ u hu ▸ he),hkill⟩

#print axioms ordinary_scalar_primitive
end SplitGElliptic
