import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.Tactic

/-! # Polynomial coordinates and the implicit trace of a tangent direction -/

set_option Elab.async false

/- Component: continuation_3/cylinder_bridge/ImplicitTraceNumerator.lean -/
section
/-! A denominator-free polynomial numerator for the trace of an implicit
affine derivative.  The adjugate identity records the actual differentiated
equations and makes the nonvanishing condition an ordinary principal open. -/

noncomputable section
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2ImplicitTraceNumerator
open Matrix

variable {R S ι σ : Type*} [CommRing R] [CommRing S]
  [Fintype ι] [DecidableEq ι] [Fintype σ]

def correctionNumerator (J : Matrix ι ι R) (g : ι → R) : ι → R :=
  -(J.adjugate *ᵥ g)

def traceNumerator (J : Matrix ι ι R) (g : ι → R)
    (weights direction : σ → R) (B : Matrix σ ι R) : R :=
  J.det * (weights ⬝ᵥ direction) + weights ⬝ᵥ (B *ᵥ correctionNumerator J g)

theorem jacobian_correction (J : Matrix ι ι R) (g : ι → R) :
    J *ᵥ correctionNumerator J g = -(J.det • g) := by
  rw [correctionNumerator,mulVec_neg,mulVec_mulVec,mul_adjugate,smul_mulVec,one_mulVec]

/-- Every genuine implicit derivative has this exact adjugate numerator. -/
theorem scaled_implicit_correction (J : Matrix ι ι R) (g u : ι → R)
    (hu : J *ᵥ u + g=0) : J.det • u=correctionNumerator J g := by
  have he : J *ᵥ u = -g := eq_neg_of_add_eq_zero_left hu
  have h := congrArg (fun v => J.adjugate *ᵥ v) he
  rw [mulVec_mulVec,adjugate_mul,smul_mulVec,one_mulVec,mulVec_neg] at h
  exact h

theorem traceNumerator_eq_scaled_trace (J : Matrix ι ι R) (g u : ι → R)
    (weights direction : σ → R) (B : Matrix σ ι R)
    (hu : J *ᵥ u + g=0) :
    traceNumerator J g weights direction B =
      J.det * (weights ⬝ᵥ (direction + B *ᵥ u)) := by
  rw [traceNumerator,← scaled_implicit_correction J g u hu,
    mulVec_smul,dotProduct_smul,dotProduct_add,smul_eq_mul,mul_add]

theorem trace_isUnit_of_numerator_isUnit (J : Matrix ι ι R) (g u : ι → R)
    (weights direction : σ → R) (B : Matrix σ ι R)
    (hu : J *ᵥ u + g=0) (hN : IsUnit (traceNumerator J g weights direction B)) :
    IsUnit (weights ⬝ᵥ (direction + B *ᵥ u)) := by
  rw [traceNumerator_eq_scaled_trace J g u weights direction B hu] at hN
  exact isUnit_of_mul_isUnit_right hN

theorem traceNumerator_seed (weights direction : σ → R) (B : Matrix σ ι R)
    (htrace : weights ⬝ᵥ direction=1) :
    traceNumerator (1 : Matrix ι ι R) (0 : ι → R) weights direction B=1 := by
  simp only [traceNumerator,correctionNumerator,det_one,mulVec_zero,neg_zero,
    dotProduct_zero,htrace,one_mul,add_zero]

theorem correctionNumerator_map (φ : R →+* S) (J : Matrix ι ι R) (g : ι → R) :
    φ ∘ correctionNumerator J g = correctionNumerator (J.map φ) (φ ∘ g) := by
  funext i
  have ha : J.adjugate.map φ=(J.map φ).adjugate := φ.map_adjugate J
  simp only [correctionNumerator,Function.comp_apply,Pi.neg_apply,map_neg,
    RingHom.map_mulVec,ha]

theorem traceNumerator_map (φ : R →+* S) (J : Matrix ι ι R) (g : ι → R)
    (weights direction : σ → R) (B : Matrix σ ι R) :
    φ (traceNumerator J g weights direction B) =
      traceNumerator (J.map φ) (φ ∘ g) (φ ∘ weights) (φ ∘ direction) (B.map φ) := by
  have hdet : φ J.det=(J.map φ).det := φ.map_det J
  have hc := correctionNumerator_map φ J g
  have hB : φ ∘ (B *ᵥ correctionNumerator J g) =
      B.map φ *ᵥ correctionNumerator (J.map φ) (φ ∘ g) := by
    funext i
    rw [Function.comp_apply,RingHom.map_mulVec,hc]
  simp only [traceNumerator,map_add,map_mul,hdet,RingHom.map_dotProduct,hB]

section Field
variable {K : Type*} [Field K]

def implicitCorrection (J : Matrix ι ι K) (g : ι → K) : ι → K :=
  J.det⁻¹ • correctionNumerator J g

theorem implicitCorrection_equation (J : Matrix ι ι K) (g : ι → K)
    (hJ : J.det≠0) : J *ᵥ implicitCorrection J g + g=0 := by
  rw [implicitCorrection,mulVec_smul,jacobian_correction,smul_neg,smul_smul,
    inv_mul_cancel₀ hJ,one_smul,neg_add_cancel]

theorem implicit_trace_eq_div (J : Matrix ι ι K) (g : ι → K)
    (weights direction : σ → K) (B : Matrix σ ι K) (hJ : J.det≠0) :
    weights ⬝ᵥ (direction + B *ᵥ implicitCorrection J g) =
      traceNumerator J g weights direction B / J.det := by
  apply (eq_div_iff hJ).mpr
  rw [mul_comm]
  exact (traceNumerator_eq_scaled_trace J g (implicitCorrection J g)
    weights direction B (implicitCorrection_equation J g hJ)).symm

end Field
end CycleQ2ImplicitTraceNumerator

#print axioms CycleQ2ImplicitTraceNumerator.scaled_implicit_correction
#print axioms CycleQ2ImplicitTraceNumerator.trace_isUnit_of_numerator_isUnit
#print axioms CycleQ2ImplicitTraceNumerator.implicit_trace_eq_div
end
end

/- Component: continuation_3/cylinder_bridge/PolynomialAffineSlice.lean -/
section
/-! Affine polynomial substitution and its literal Jacobian.  The centre may
belong to a parameter coefficient ring; it need not be a constant complex
point.  Thus the same construction fixes the external family parameters. -/

noncomputable section
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2PolynomialAffineSlice
open MvPolynomial Matrix

variable {R S σ ι m : Type*} [CommRing R] [CommRing S]
  [Fintype ι]

def affinePoint (a : σ → R) (B : Matrix σ ι R) : σ → MvPolynomial ι R :=
  fun k => C (a k) + ∑ j, C (B k j) * X j

def substitute (a : σ → R) (B : Matrix σ ι R) :
    MvPolynomial σ R →ₐ[R] MvPolynomial ι R :=
  aeval (affinePoint a B)

def pointValue (φ : R →+* S) (a : σ → R) (B : Matrix σ ι R)
    (x : ι → S) : σ → S :=
  fun k => φ (a k) + ∑ j, φ (B k j) * x j

theorem eval_affinePoint (φ : R →+* S) (a : σ → R) (B : Matrix σ ι R)
    (x : ι → S) (k : σ) :
    eval₂Hom φ x (affinePoint a B k) = pointValue φ a B x k := by
  simp [affinePoint,pointValue]

theorem eval_substitute (φ : R →+* S) (a : σ → R) (B : Matrix σ ι R)
    (x : ι → S) (p : MvPolynomial σ R) :
    eval₂Hom φ x (substitute a B p) = eval₂Hom φ (pointValue φ a B x) p := by
  have h : (eval₂Hom φ x).comp (substitute a B).toRingHom =
      eval₂Hom φ (pointValue φ a B x) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [substitute]
    · intro k
      change eval₂Hom φ x (aeval (affinePoint a B) (X k)) =
        eval₂Hom φ (pointValue φ a B x) (X k)
      rw [aeval_X,eval₂Hom_X']
      exact eval_affinePoint φ a B x k
  exact RingHom.congr_fun h p

theorem eval_zero_substitute (φ : R →+* S) (a : σ → R) (B : Matrix σ ι R)
    (p : MvPolynomial σ R) :
    eval₂Hom φ (0 : ι → S) (substitute a B p) = eval₂Hom φ (φ ∘ a) p := by
  have hp : pointValue φ a B (0 : ι → S) = φ ∘ a := by
    funext k
    simp [pointValue]
  rw [eval_substitute,hp]

theorem pderiv_affinePoint (a : σ → R) (B : Matrix σ ι R) (j : ι) (k : σ) :
    pderiv j (affinePoint a B k) = C (B k j) := by
  classical
  simp [affinePoint,Pi.single_apply]

theorem substitute_C (a : σ → R) (B : Matrix σ ι R) (r : R) :
    substitute a B (C r) = C r := by
  exact aeval_C (affinePoint a B) r

theorem substitute_X (a : σ → R) (B : Matrix σ ι R) (k : σ) :
    substitute a B (X k) = affinePoint a B k := aeval_X _ k

variable [Fintype σ]

/-- The exact chain rule for the chosen affine parameter directions. -/
theorem pderiv_substitute (a : σ → R) (B : Matrix σ ι R) (j : ι)
    (p : MvPolynomial σ R) :
    pderiv j (substitute a B p) =
      ∑ k, C (B k j) * substitute a B (pderiv k p) := by
  classical
  refine MvPolynomial.induction_on (motive := fun f =>
    pderiv j (substitute a B f) = ∑ k, C (B k j) * substitute a B (pderiv k f))
    p ?_ ?_ ?_
  · intro r
    simp only [substitute_C,pderiv_C,map_zero,mul_zero,Finset.sum_const_zero]
  · intro p q hp hq
    simp only [map_add,hp,hq,mul_add,Finset.sum_add_distrib]
  · intro p k hp
    have hx : substitute a B (X k) = affinePoint a B k := substitute_X a B k
    have hs : (∑ l, C (B l j) * substitute a B p *
        substitute a B (pderiv l (X k))) = C (B k j) * substitute a B p := by
      rw [Finset.sum_eq_single k]
      · rw [pderiv_X_self,map_one,mul_one]
      · intro l _ hl
        rw [pderiv_X_of_ne (Ne.symm hl),map_zero,mul_zero]
      · intro hk
        exact (hk (Finset.mem_univ k)).elim
    calc
      _ = (∑ l, C (B l j) * substitute a B (pderiv l p)) * affinePoint a B k +
          substitute a B p * C (B k j) := by
        rw [map_mul,pderiv_mul,hp,hx,pderiv_affinePoint]
      _ = (∑ l, C (B l j) * substitute a B (pderiv l p) * affinePoint a B k) +
          ∑ l, C (B l j) * substitute a B p * substitute a B (pderiv l (X k)) := by
        rw [← Finset.sum_mul,hs,mul_comm (substitute a B p)]
      _ = ∑ l, C (B l j) * substitute a B (pderiv l (p * X k)) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro l _
        rw [pderiv_mul,map_add,map_mul,map_mul,hx]
        simp only [mul_add,mul_assoc]
theorem eval_pderiv_substitute (φ : R →+* S) (a : σ → R) (B : Matrix σ ι R)
    (x : ι → S) (j : ι) (p : MvPolynomial σ R) :
    eval₂Hom φ x (pderiv j (substitute a B p)) =
      ∑ k, φ (B k j) * eval₂Hom φ (pointValue φ a B x) (pderiv k p) := by
  rw [pderiv_substitute]
  simp only [map_sum,map_mul,eval₂Hom_C,eval_substitute]

theorem eval_zero_pderiv_substitute (φ : R →+* S) (a : σ → R) (B : Matrix σ ι R)
    (j : ι) (p : MvPolynomial σ R) :
    eval₂Hom φ (0 : ι → S) (pderiv j (substitute a B p)) =
      ∑ k, φ (B k j) * eval₂Hom φ (φ ∘ a) (pderiv k p) := by
  have hp : pointValue φ a B (0 : ι → S) = φ ∘ a := by
    funext k
    simp [pointValue]
  rw [eval_pderiv_substitute,hp]

def jacobian (φ : R →+* S) (x : σ → S) (e : m → MvPolynomial σ R) :
    Matrix m σ S := fun q k => eval₂Hom φ x (pderiv k (e q))

theorem jacobian_substitute (φ : R →+* S) (a : σ → R) (B : Matrix σ ι R)
    (x : ι → S) (e : m → MvPolynomial σ R) :
    jacobian φ x (fun q => substitute a B (e q)) =
      jacobian φ (pointValue φ a B x) e * B.map φ := by
  funext q j
  simp only [jacobian,eval_pderiv_substitute,Matrix.mul_apply,Matrix.map_apply,mul_comm]

theorem jacobian_zero_substitute (φ : R →+* S) (a : σ → R) (B : Matrix σ ι R)
    (e : m → MvPolynomial σ R) :
    jacobian φ (0 : ι → S) (fun q => substitute a B (e q)) =
      jacobian φ (φ ∘ a) e * B.map φ := by
  have hp : pointValue φ a B (0 : ι → S) = φ ∘ a := by
    funext k
    simp [pointValue]
  rw [jacobian_substitute,hp]

end CycleQ2PolynomialAffineSlice

#print axioms CycleQ2PolynomialAffineSlice.pderiv_substitute
#print axioms CycleQ2PolynomialAffineSlice.jacobian_zero_substitute
end
end

/- Component: continuation_3/cylinder_bridge/PolynomialDualEvaluation.lean -/
section
/-! A literal single-coordinate dual-number evaluation of a polynomial has
first coefficient equal to its formal partial derivative at the base point. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000

namespace CycleQ2PolynomialDualEvaluation
open MvPolynomial

variable {R σ : Type*} [CommRing R]

abbrev Dual (R : Type*) := TrivSqZeroExt R R

def point (x : σ → R) (j : σ) : σ → Dual R := by
  classical
  exact fun i => ⟨x i,if j=i then 1 else 0⟩

theorem eval_point (x : σ → R) (j : σ) (p : MvPolynomial σ R) :
    aeval (point x j) p = (⟨eval x p,eval x (pderiv j p)⟩ : Dual R) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C c =>
      apply TrivSqZeroExt.ext <;> simp [point, TrivSqZeroExt.algebraMap_eq_inl]
  | add p q hp hq =>
      rw [map_add,hp,hq]
      apply TrivSqZeroExt.ext <;> simp
  | mul_X p i hp =>
      rw [map_mul,hp,aeval_X]
      apply TrivSqZeroExt.ext
      · simp [point]
      · by_cases hij : j=i
        · subst i
          simp [point,pderiv_mul,pderiv_X,smul_eq_mul,op_smul_eq_smul]
          ring
        · simp [point,pderiv_mul,pderiv_X,Pi.single_apply,hij,Ne.symm hij,
            smul_eq_mul,op_smul_eq_smul]
          ring

theorem eval_point_fst (x : σ → R) (j : σ) (p : MvPolynomial σ R) :
    (aeval (point x j) p).fst=eval x p := by rw [eval_point]; rfl

theorem eval_point_snd (x : σ → R) (j : σ) (p : MvPolynomial σ R) :
    (aeval (point x j) p).snd=eval x (pderiv j p) := by rw [eval_point]; rfl

end CycleQ2PolynomialDualEvaluation

#print axioms CycleQ2PolynomialDualEvaluation.eval_point_snd
end
end

/- Component: continuation_3/cylinder_bridge/PolynomialAffineBaseChange.lean -/
section
/-! Coefficient base change of the literal affine-slice Jacobian, and the
fact that a zero direction row fixes the corresponding external parameter. -/

noncomputable section
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2PolynomialAffineSlice
open MvPolynomial Matrix

variable {R S T σ ι m : Type*} [CommRing R] [CommRing S] [CommRing T]

theorem jacobian_map (ψ : R →+* S) (φ : S →+* T) (x : σ → T)
    (e : m → MvPolynomial σ R) :
    jacobian φ x (fun q => MvPolynomial.map ψ (e q)) = jacobian (φ.comp ψ) x e := by
  funext q j
  simp only [jacobian,pderiv_map,eval₂Hom_map_hom]

theorem pointValue_of_zero_row [Fintype ι] (φ : R →+* S)
    (a : σ → R) (B : Matrix σ ι R) (x : ι → S) (k : σ)
    (hB : ∀ j, B k j=0) : pointValue φ a B x k=φ (a k) := by
  simp only [pointValue,hB,map_zero,zero_mul,Finset.sum_const_zero,add_zero]

theorem affinePoint_of_zero_row [Fintype ι] (a : σ → R) (B : Matrix σ ι R)
    (k : σ) (hB : ∀ j, B k j=0) : affinePoint a B k=C (a k) := by
  simp only [affinePoint,hB,map_zero,zero_mul,Finset.sum_const_zero,add_zero]

end CycleQ2PolynomialAffineSlice

#print axioms CycleQ2PolynomialAffineSlice.jacobian_map
#print axioms CycleQ2PolynomialAffineSlice.pointValue_of_zero_row
end
end

/- Component: continuation_3/cylinder_bridge/PolynomialDerivationChainRule.lean -/
section
/-! Differentiating an actual polynomial solution gives the literal
Jacobian equation.  In affine coordinates this is exactly the relation
used by the adjugate trace numerator. -/

noncomputable section
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2PolynomialDerivationChainRule
open MvPolynomial Matrix CycleQ2PolynomialAffineSlice

variable {R S σ m ι : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [Fintype σ]

theorem derivation_aeval (D : Derivation R S S) (x : σ → S)
    (p : MvPolynomial σ R) :
    D (aeval x p) = ∑ k, aeval x (pderiv k p) * D (x k) := by
  classical
  refine MvPolynomial.induction_on (motive := fun f =>
    D (aeval x f) = ∑ k, aeval x (pderiv k f) * D (x k)) p ?_ ?_ ?_
  · intro r
    simp only [aeval_C,Derivation.map_algebraMap,pderiv_C,map_zero,zero_mul,
      Finset.sum_const_zero]
  · intro p q hp hq
    simp only [map_add,hp,hq,add_mul,Finset.sum_add_distrib]
  · intro p j hp
    have hs : (∑ k, aeval x p * aeval x (pderiv k (X j : MvPolynomial σ R)) * D (x k)) =
        aeval x p * D (x j) := by
      rw [Finset.sum_eq_single j]
      · rw [pderiv_X_self,map_one,mul_one]
      · intro k _ hk
        rw [pderiv_X_of_ne (Ne.symm hk),map_zero,mul_zero,zero_mul]
      · intro hj
        exact (hj (Finset.mem_univ j)).elim
    calc
      _ = aeval x p * D (x j) + x j * (∑ k, aeval x (pderiv k p) * D (x k)) := by
        rw [map_mul,aeval_X,Derivation.leibniz,hp]
        rfl
      _ = (∑ k, aeval x (pderiv k p) * x j * D (x k)) +
          ∑ k, aeval x p * aeval x (pderiv k (X j : MvPolynomial σ R)) * D (x k) := by
        rw [hs,Finset.mul_sum,add_comm]
        congr 1
        apply Finset.sum_congr rfl
        intro k _
        ring
      _ = ∑ k, aeval x (pderiv k (p*X j)) * D (x k) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro k _
        rw [pderiv_mul,map_add,map_mul,map_mul,aeval_X]
        ring

theorem differentiated_equations (D : Derivation R S S) (x : σ → S)
    (e : m → MvPolynomial σ R) (he : ∀ q, aeval x (e q)=0) :
    jacobian (algebraMap R S) x e *ᵥ (fun k => D (x k))=0 := by
  funext q
  have h := derivation_aeval D x (e q)
  rw [he q,map_zero] at h
  exact h.symm

theorem derivation_affine_value [Fintype ι] (D : Derivation R S S)
    (a : σ → S) (B : Matrix σ ι R) (z : ι → S) (k : σ) :
    D (a k + ∑ j, algebraMap R S (B k j) * z j) =
      D (a k) + ∑ j, algebraMap R S (B k j) * D (z j) := by
  simp only [map_add,map_sum,Derivation.leibniz,Derivation.map_algebraMap,
    smul_eq_mul,mul_zero,add_zero]

theorem implicit_derivative_relation [Fintype m] [Fintype ι]
    (D : Derivation R S S) (x : σ → S) (z : ι → S)
    (P : Matrix ι m R) (B : Matrix σ ι R) (direction : σ → S)
    (e : m → MvPolynomial σ R) (he : ∀ q, aeval x (e q)=0)
    (hder : ∀ k, D (x k)=direction k+
      (B.map (algebraMap R S) *ᵥ (fun j => D (z j))) k) :
    (P.map (algebraMap R S) * jacobian (algebraMap R S) x e * B.map (algebraMap R S)) *ᵥ
        (fun j => D (z j)) +
      (P.map (algebraMap R S) * jacobian (algebraMap R S) x e) *ᵥ direction=0 := by
  have hy : (fun k => D (x k))=direction+B.map (algebraMap R S) *ᵥ (fun j => D (z j)) :=
    funext hder
  have h := differentiated_equations D x e he
  rw [hy,mulVec_add] at h
  have hp := congrArg (fun v => P.map (algebraMap R S) *ᵥ v) h
  simp only [mulVec_add,mulVec_mulVec,mulVec_zero,← Matrix.mul_assoc] at hp
  exact (add_comm _ _).trans hp

end CycleQ2PolynomialDerivationChainRule

#print axioms CycleQ2PolynomialDerivationChainRule.derivation_aeval
#print axioms CycleQ2PolynomialDerivationChainRule.implicit_derivative_relation
end
end

/- Component: continuation_3/cylinder_bridge/PolynomialImplicitTrace.lean -/
section
/-! The implicit trace numerator is a literal polynomial in the original
parameters.  At a compatible seed and a trace-one kernel direction it has
value one.  On a genuine differentiated solution, its being a unit forces
the fixed linear trace of that derivative to be a unit. -/

noncomputable section
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2PolynomialImplicitTrace
open Matrix MvPolynomial CycleQ2PolynomialAffineSlice
  CycleQ2PolynomialDerivationChainRule CycleQ2ImplicitTraceNumerator

variable {R S σ m ι : Type*} [CommRing R] [CommRing S]
  [Fintype σ] [Fintype m] [Fintype ι] [DecidableEq ι]

def polynomialJacobian (e : m → MvPolynomial σ R) : Matrix m σ (MvPolynomial σ R) :=
  fun q k => pderiv k (e q)

def retainedJacobian (P : Matrix ι m R) (B : Matrix σ ι R)
    (e : m → MvPolynomial σ R) : Matrix ι ι (MvPolynomial σ R) :=
  P.map C * polynomialJacobian e * B.map C

def directionDerivative (P : Matrix ι m R) (direction : σ → R)
    (e : m → MvPolynomial σ R) : ι → MvPolynomial σ R :=
  (P.map C * polynomialJacobian e) *ᵥ (C ∘ direction)

def tracePolynomial (P : Matrix ι m R) (B : Matrix σ ι R)
    (e : m → MvPolynomial σ R) (weights direction : σ → R) : MvPolynomial σ R :=
  traceNumerator (retainedJacobian P B e) (directionDerivative P direction e)
    (C ∘ weights) (C ∘ direction) (B.map C)

theorem eval_polynomialJacobian (φ : R →+* S) (x : σ → S)
    (e : m → MvPolynomial σ R) :
    (polynomialJacobian e).map (eval₂Hom φ x)=jacobian φ x e := rfl

theorem eval_retainedJacobian (φ : R →+* S) (x : σ → S)
    (P : Matrix ι m R) (B : Matrix σ ι R) (e : m → MvPolynomial σ R) :
    (retainedJacobian P B e).map (eval₂Hom φ x)=
      P.map φ * jacobian φ x e * B.map φ := by
  simp only [retainedJacobian,Matrix.map_mul,eval_polynomialJacobian,Matrix.map_map,
    Function.comp_def,eval₂Hom_C]

theorem eval_directionDerivative (φ : R →+* S) (x : σ → S)
    (P : Matrix ι m R) (direction : σ → R) (e : m → MvPolynomial σ R) :
    (eval₂Hom φ x) ∘ directionDerivative P direction e =
      (P.map φ * jacobian φ x e) *ᵥ (φ ∘ direction) := by
  funext i
  simp only [directionDerivative,Function.comp_apply,RingHom.map_mulVec,
    Matrix.map_mul,eval_polynomialJacobian,Matrix.map_map,Function.comp_def,eval₂Hom_C]

theorem eval_tracePolynomial (φ : R →+* S) (x : σ → S)
    (P : Matrix ι m R) (B : Matrix σ ι R) (e : m → MvPolynomial σ R)
    (weights direction : σ → R) :
    eval₂Hom φ x (tracePolynomial P B e weights direction) =
      traceNumerator (P.map φ * jacobian φ x e * B.map φ)
        ((P.map φ * jacobian φ x e) *ᵥ (φ ∘ direction))
        (φ ∘ weights) (φ ∘ direction) (B.map φ) := by
  rw [tracePolynomial,traceNumerator_map,eval_retainedJacobian,eval_directionDerivative]
  simp only [Function.comp_def,eval₂Hom_C,Matrix.map_map]

theorem seed_tracePolynomial_one (φ : R →+* S) (x : σ → S)
    (P : Matrix ι m R) (B : Matrix σ ι R) (e : m → MvPolynomial σ R)
    (weights direction : σ → R)
    (hJ : P.map φ * jacobian φ x e * B.map φ=1)
    (hkernel : jacobian φ x e *ᵥ (φ ∘ direction)=0)
    (htrace : (φ ∘ weights) ⬝ᵥ (φ ∘ direction)=1) :
    eval₂Hom φ x (tracePolynomial P B e weights direction)=1 := by
  rw [eval_tracePolynomial,hJ,← mulVec_mulVec,hkernel,mulVec_zero]
  exact traceNumerator_seed _ _ _ htrace

theorem derivative_trace_isUnit [Algebra R S]
    (D : Derivation R S S) (x : σ → S) (z : ι → S)
    (P : Matrix ι m R) (B : Matrix σ ι R) (e : m → MvPolynomial σ R)
    (weights direction : σ → R)
    (he : ∀ q, aeval x (e q)=0)
    (hder : ∀ k, D (x k)=algebraMap R S (direction k)+
      (B.map (algebraMap R S) *ᵥ (fun j => D (z j))) k)
    (hN : IsUnit (aeval x (tracePolynomial P B e weights direction))) :
    IsUnit ((algebraMap R S ∘ weights) ⬝ᵥ (fun k => D (x k))) := by
  have hu := implicit_derivative_relation D x z P B ((algebraMap R S) ∘ direction) e he hder
  change IsUnit (eval₂Hom (algebraMap R S) x (tracePolynomial P B e weights direction)) at hN
  rw [eval_tracePolynomial] at hN
  have ht := trace_isUnit_of_numerator_isUnit
    (P.map (algebraMap R S) * jacobian (algebraMap R S) x e * B.map (algebraMap R S))
    ((P.map (algebraMap R S) * jacobian (algebraMap R S) x e) *ᵥ ((algebraMap R S) ∘ direction))
    (fun j => D (z j)) ((algebraMap R S) ∘ weights) ((algebraMap R S) ∘ direction)
    (B.map (algebraMap R S)) hu hN
  have hx : (fun k => D (x k))=((algebraMap R S) ∘ direction)+
      B.map (algebraMap R S) *ᵥ (fun j => D (z j)) := funext hder
  rw [hx]
  exact ht

end CycleQ2PolynomialImplicitTrace

#print axioms CycleQ2PolynomialImplicitTrace.seed_tracePolynomial_one
#print axioms CycleQ2PolynomialImplicitTrace.derivative_trace_isUnit
end
end

/- Component: continuation_3/cylinder_bridge/PolynomialProjectiveTrace.lean -/
section
/-! A literal polynomial open detects motion of a projective coefficient
vector.  It retains the numerator of the derivative of a ratio of two
linear coefficient functionals, so scalar rescaling cannot account for
the nonvanishing. -/

noncomputable section
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2PolynomialProjectiveTrace
open Matrix MvPolynomial CycleQ2PolynomialAffineSlice
  CycleQ2PolynomialDerivationChainRule CycleQ2PolynomialImplicitTrace
  CycleQ2ImplicitTraceNumerator
open scoped BigOperators

variable {R S σ m ι : Type*} [CommRing R] [CommRing S]
  [Fintype σ] [Fintype m] [Fintype ι] [DecidableEq ι]

def linearValue (weights : σ → R) : MvPolynomial σ R :=
  ∑ k, C (weights k)*X k

theorem eval_linearValue (φ : R →+* S) (x : σ → S) (weights : σ → R) :
    eval₂Hom φ x (linearValue weights)=(φ ∘ weights) ⬝ᵥ x := by
  simp only [linearValue,map_sum,map_mul,eval₂Hom_C,eval₂Hom_X',dotProduct,
    Function.comp_apply]

def projectiveTracePolynomial (P : Matrix ι m R) (B : Matrix σ ι R)
    (e : m → MvPolynomial σ R) (weights leading direction : σ → R) :
    MvPolynomial σ R :=
  linearValue leading*tracePolynomial P B e weights direction-
    linearValue weights*tracePolynomial P B e leading direction

theorem seed_projectiveTracePolynomial_one (φ : R →+* S) (x : σ → S)
    (P : Matrix ι m R) (B : Matrix σ ι R) (e : m → MvPolynomial σ R)
    (weights leading direction : σ → R)
    (hJ : P.map φ*jacobian φ x e*B.map φ=1)
    (hkernel : jacobian φ x e*ᵥ(φ ∘ direction)=0)
    (htrace : (φ ∘ weights) ⬝ᵥ (φ ∘ direction)=1)
    (hleading : (φ ∘ leading) ⬝ᵥ x=1)
    (hvalue : (φ ∘ weights) ⬝ᵥ x=0) :
    eval₂Hom φ x (projectiveTracePolynomial P B e weights leading direction)=1 := by
  rw [projectiveTracePolynomial,map_sub,map_mul,map_mul,eval_linearValue,
    eval_linearValue,hleading,hvalue,zero_mul,sub_zero,one_mul]
  exact seed_tracePolynomial_one φ x P B e weights direction hJ hkernel htrace

theorem derivative_tracePolynomial [Algebra R S]
    (D : Derivation R S S) (x : σ → S) (z : ι → S)
    (P : Matrix ι m R) (B : Matrix σ ι R) (e : m → MvPolynomial σ R)
    (weights direction : σ → R)
    (he : ∀ q, aeval x (e q)=0)
    (hder : ∀ k, D (x k)=algebraMap R S (direction k)+
      (B.map (algebraMap R S)*ᵥ(fun j => D (z j))) k) :
    aeval x (tracePolynomial P B e weights direction)=
      aeval x (retainedJacobian P B e).det*
        ((algebraMap R S ∘ weights) ⬝ᵥ (fun k => D (x k))) := by
  have hu := implicit_derivative_relation D x z P B ((algebraMap R S) ∘ direction) e he hder
  have hx : (fun k => D (x k))=((algebraMap R S) ∘ direction)+
      B.map (algebraMap R S)*ᵥ(fun j => D (z j)) := funext hder
  change eval₂Hom (algebraMap R S) x (tracePolynomial P B e weights direction)=_
  rw [eval_tracePolynomial,traceNumerator_eq_scaled_trace _ _ _ _ _ _ hu,←hx]
  congr 1
  change _=eval₂Hom (algebraMap R S) x (retainedJacobian P B e).det
  rw [RingHom.map_det]
  exact congrArg Matrix.det (eval_retainedJacobian (algebraMap R S) x P B e).symm

theorem derivation_linear_value [Algebra R S]
    (D : Derivation R S S) (x : σ → S) (weights : σ → R) :
    D ((algebraMap R S ∘ weights) ⬝ᵥ x)=
      (algebraMap R S ∘ weights) ⬝ᵥ (fun k => D (x k)) := by
  simp only [dotProduct,map_sum,Function.comp_apply,Derivation.leibniz,
    Derivation.map_algebraMap,smul_eq_mul,mul_zero,add_zero]

theorem derivative_projectiveTracePolynomial [Algebra R S]
    (D : Derivation R S S) (x : σ → S) (z : ι → S)
    (P : Matrix ι m R) (B : Matrix σ ι R) (e : m → MvPolynomial σ R)
    (weights leading direction : σ → R)
    (he : ∀ q, aeval x (e q)=0)
    (hder : ∀ k, D (x k)=algebraMap R S (direction k)+
      (B.map (algebraMap R S)*ᵥ(fun j => D (z j))) k) :
    aeval x (projectiveTracePolynomial P B e weights leading direction)=
      aeval x (retainedJacobian P B e).det*
        (((algebraMap R S ∘ leading) ⬝ᵥ x)*
          D ((algebraMap R S ∘ weights) ⬝ᵥ x)-
        ((algebraMap R S ∘ weights) ⬝ᵥ x)*
          D ((algebraMap R S ∘ leading) ⬝ᵥ x)) := by
  rw [projectiveTracePolynomial,map_sub,map_mul,map_mul]
  change eval₂Hom (algebraMap R S) x (linearValue leading)*_-
      eval₂Hom (algebraMap R S) x (linearValue weights)*_=_
  rw [eval_linearValue,eval_linearValue,
    derivative_tracePolynomial D x z P B e weights direction he hder,
    derivative_tracePolynomial D x z P B e leading direction he hder,
    derivation_linear_value,derivation_linear_value]
  ring

theorem derivative_projective_trace_isUnit [Algebra R S]
    (D : Derivation R S S) (x : σ → S) (z : ι → S)
    (P : Matrix ι m R) (B : Matrix σ ι R) (e : m → MvPolynomial σ R)
    (weights leading direction : σ → R)
    (he : ∀ q, aeval x (e q)=0)
    (hder : ∀ k, D (x k)=algebraMap R S (direction k)+
      (B.map (algebraMap R S)*ᵥ(fun j => D (z j))) k)
    (hN : IsUnit (aeval x (projectiveTracePolynomial P B e weights leading direction))) :
    IsUnit (((algebraMap R S ∘ leading) ⬝ᵥ x)*
      D ((algebraMap R S ∘ weights) ⬝ᵥ x)-
      ((algebraMap R S ∘ weights) ⬝ᵥ x)*
        D ((algebraMap R S ∘ leading) ⬝ᵥ x)) := by
  rw [derivative_projectiveTracePolynomial D x z P B e weights leading direction he hder] at hN
  exact isUnit_of_mul_isUnit_right hN

end CycleQ2PolynomialProjectiveTrace

#print axioms CycleQ2PolynomialProjectiveTrace.seed_projectiveTracePolynomial_one
#print axioms CycleQ2PolynomialProjectiveTrace.derivative_projective_trace_isUnit
end
end
