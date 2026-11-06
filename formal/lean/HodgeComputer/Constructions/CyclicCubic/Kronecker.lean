import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Tactic

/-! A small exact encoding for covariant coefficient identities.
At fixed cubic diagonal weight, the exponents of a,b,c are determined by
those of d,e,f. When all three weights are below 38, the latter
exponents are below 19. Substitution a=b=c=1, d=X, e=X^19, f=X^361 is then
injective on that homogeneous component. Prepared with OpenAI Codex assistance.
-/
noncomputable section
set_option maxRecDepth 4096
namespace CycleCubicKronecker
open MvPolynomial
open scoped BigOperators
abbrev Grade := ℕ × ℕ × ℕ
abbrev Exponent := Fin 6 →₀ ℕ
def weights : Fin 6 → Grade := ![(3,0,0),(0,3,0),(0,0,3),(2,1,0),(0,2,1),(1,0,2)]
def code (m : Exponent) : ℕ := m 3+19*m 4+361*m 5

lemma weight_formula (m : Exponent) :
    Finsupp.weight weights m=
      (3*m 0+2*m 3+m 5,3*m 1+m 3+2*m 4,3*m 2+m 4+2*m 5) := by
  rw [Finsupp.weight_apply,Finsupp.sum_fintype]
  · simp only [weights,Fin.sum_univ_succ,Matrix.cons_val_zero,Matrix.cons_val_succ,
      Fin.reduceSucc,Matrix.cons_val_one,Matrix.cons_val,Finset.univ_eq_empty,Finset.sum_empty,
      Prod.smul_mk,Prod.mk_add_mk,nsmul_eq_mul]
    ext <;> simp <;> ring
  · intro; simp

lemma digit_bound (a b c d e f u v w : ℕ)
    (h0 : 3*a+2*d+f=u) (h1 : 3*b+d+2*e=v) (h2 : 3*c+e+2*f=w)
    (hw : u<38 ∧ v<38 ∧ w<38) : d<19 ∧ e<19 ∧ f<19 := by omega

lemma digits_unique (a b c d e f : ℕ)
    (ha : a<19) (hb : b<19) (hd : d<19) (he : e<19)
    (h : a+19*b+361*c=d+19*e+361*f) : a=d ∧ b=e ∧ c=f := by
  have had : a=d := by
    have hm := congrArg (fun k : ℕ => k%19) h
    simpa only [Nat.add_mod,Nat.mul_mod,Nat.mod_self,Nat.zero_mul,Nat.add_zero,
      show 361%19=0 from rfl,Nat.mod_eq_of_lt ha,Nat.mod_eq_of_lt hd,
      Nat.mod_mod] using hm
  have hbc : b+19*c=e+19*f := by
    rw [had,add_assoc,add_assoc] at h
    have hh := Nat.add_left_cancel h
    have hfac : 19*(b+19*c)=19*(e+19*f) := by nlinarith only [hh]
    exact Nat.eq_of_mul_eq_mul_left (by decide : 0<19) hfac
  have hbe : b=e := by
    have hm := congrArg (fun k : ℕ => k%19) hbc
    simpa only [Nat.add_mod,Nat.mul_mod,Nat.mod_self,Nat.zero_mul,Nat.add_zero,
      Nat.mod_eq_of_lt hb,Nat.mod_eq_of_lt he,Nat.mod_mod,Nat.zero_mod] using hm
  have hcf : c=f := by
    rw [hbe] at hbc
    exact Nat.eq_of_mul_eq_mul_left (by decide : 0<19) (Nat.add_left_cancel hbc)
  exact ⟨had,hbe,hcf⟩

lemma recover_coefficient (a b s t u : ℕ)
    (h : 3*a+s+t=u) (h' : 3*b+s+t=u) : a=b := by omega

lemma code_injective_on_grade (w : Grade) (hw : w.1<38 ∧ w.2.1<38 ∧ w.2.2<38) :
    Set.InjOn code {m : Exponent | Finsupp.weight weights m=w} := by
  intro m hm n hn he
  rw [Set.mem_setOf_eq,weight_formula] at hm hn
  have hm0 := congrArg Prod.fst hm
  have hm1 := congrArg (fun z : Grade => z.2.1) hm
  have hm2 := congrArg (fun z : Grade => z.2.2) hm
  have hn0 := congrArg Prod.fst hn
  have hn1 := congrArg (fun z : Grade => z.2.1) hn
  have hn2 := congrArg (fun z : Grade => z.2.2) hn
  dsimp only at hm0 hm1 hm2 hn0 hn1 hn2
  have hmb := digit_bound _ _ _ _ _ _ _ _ _ hm0 hm1 hm2 hw
  have hnb := digit_bound _ _ _ _ _ _ _ _ _ hn0 hn1 hn2 hw
  obtain ⟨he3,he4,he5⟩ := digits_unique _ _ _ _ _ _ hmb.1 hmb.2.1 hnb.1 hnb.2.1 he
  rw [he3,he5] at hm0
  rw [he3,he4] at hm1
  rw [he4,he5] at hm2
  have he0 := recover_coefficient _ _ _ _ _ hm0 hn0
  have he1 := recover_coefficient _ _ _ _ _ hm1 hn1
  have he2 := recover_coefficient _ _ _ _ _ hm2 hn2
  ext i
  fin_cases i <;> assumption

variable {R : Type*} [CommSemiring R]
def encode : MvPolynomial (Fin 6) R →+* Polynomial R :=
  MvPolynomial.eval₂Hom Polynomial.C
    ![1,1,1,Polynomial.X,Polynomial.X^19,Polynomial.X^361]

lemma encode_monomial (m : Exponent) (r : R) :
    encode (MvPolynomial.monomial m r)=Polynomial.monomial (code m) r := by
  rw [← Polynomial.C_mul_X_pow_eq_monomial]
  simp [encode,MvPolynomial.eval₂Hom_monomial,Finsupp.prod_fintype,
    Fin.prod_univ_succ,code,pow_add,pow_mul,mul_assoc,mul_comm,mul_left_comm]

lemma encode_finsupp (p : MvPolynomial (Fin 6) R) :
    (encode p).toFinsupp.coeff=Finsupp.mapDomain code (AddMonoidAlgebra.coeff p) := by
  induction p using MvPolynomial.induction_on' with
  | monomial m r =>
    rw [encode_monomial]
    simp [Polynomial.toFinsupp_monomial,MvPolynomial.monomial,Finsupp.mapDomain_single]
  | add p q hp hq =>
    simp only [map_add,Polynomial.toFinsupp_add,AddMonoidAlgebra.coeff_add,
      Finsupp.mapDomain_add,hp,hq]

theorem encode_injective_on_grade (w : Grade) (hw : w.1<38 ∧ w.2.1<38 ∧ w.2.2<38)
    (p q : MvPolynomial (Fin 6) R)
    (hp : p.IsWeightedHomogeneous weights w) (hq : q.IsWeightedHomogeneous weights w)
    (he : encode p=encode q) : p=q := by
  classical
  let S : Set Exponent := {m | Finsupp.weight weights m=w}
  have hsP : (p.support : Set Exponent)⊆S := fun m hm => hp (mem_support_iff.mp hm)
  have hsQ : (q.support : Set Exponent)⊆S := fun m hm => hq (mem_support_iff.mp hm)
  have heF := congrArg (fun r : Polynomial R => r.toFinsupp.coeff) he
  rw [encode_finsupp,encode_finsupp] at heF
  ext m
  by_cases hm : m∈S
  · have h := congrArg (fun f : ℕ →₀ R => f (code m)) heF
    rw [Finsupp.mapDomain_apply' S (AddMonoidAlgebra.coeff p) hsP (code_injective_on_grade w hw) hm,
      Finsupp.mapDomain_apply' S (AddMonoidAlgebra.coeff q) hsQ (code_injective_on_grade w hw) hm] at h
    exact h
  · have hp0 : coeff m p=0 := by
      by_contra h; exact hm (hp h)
    have hq0 : coeff m q=0 := by
      by_contra h; exact hm (hq h)
    rw [hp0,hq0]

end CycleCubicKronecker
#print axioms CycleCubicKronecker.encode_injective_on_grade
