import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Tactic

/-!
# First variations of polynomial and elliptic identities

Generic commutative-ring chain rules, normalization of cleared covariant
identities, and square-zero jets. The first-variation lemmas provide the
curve and differential inputs to `ResidueTransport.MovingMap` at a fixed
parameter value; they require no parameter derivation on the specialized
function field.

Extracted from `hodgepodgeconjecture`'s accepted cyclic cubic construction,
`data/cycle-three/CubicJetCalculus.lean` (PR #165). Its polynomial chain rule
extends the construction of `fqlx` and the Hodge Computer collaborators.
The original construction and this extraction acknowledge OpenAI Codex
assistance. Cubic-family equations and their nonvanishing proofs remain
application-specific.

The integral-normalization variant `curve_from_syzygy27` and evaluation
at a square-zero element were prepared for `benediamond` with OpenAI
ChatGPT and Codex assistance in the mixed-polar construction. The
normalization uses explicit inverses in the coefficient ring.
-/

noncomputable section

namespace ResidueFirstJets

open MvPolynomial
open scoped BigOperators

/-- The shared polynomial chain rule, extended from fields to commutative rings.
The proof follows HoldoutConstruction.derivation_eval₂_chain (fqlx/project).
The extension is needed because dual numbers have zero divisors. -/
lemma ring_chain {R L σ : Type*} [CommRing R] [CommRing L] [Fintype σ] [DecidableEq σ]
    (D : Derivation ℤ L L) (φ : R →+* L) (x : σ → L)
    (hC : ∀ r, D (φ r)=0) (p : MvPolynomial σ R) :
    D (MvPolynomial.eval₂Hom φ x p)=
      ∑ i, MvPolynomial.eval₂Hom φ x (MvPolynomial.pderiv i p)*D (x i) := by
  let θ := MvPolynomial.eval₂Hom φ x
  change D (θ p)=∑ i, θ (MvPolynomial.pderiv i p)*D (x i)
  induction p using MvPolynomial.induction_on with
  | C r => simp [θ,hC]
  | add p q hp hq => simp only [map_add,hp,hq,add_mul,Finset.sum_add_distrib]
  | mul_X p j hp =>
    rw [map_mul,Derivation.leibniz]
    simp only [θ,MvPolynomial.eval₂Hom_X',smul_eq_mul] at hp ⊢
    rw [hp]
    simp only [MvPolynomial.pderiv_mul,map_add,map_mul,MvPolynomial.eval₂Hom_X',
      add_mul,Finset.sum_add_distrib]
    have hsum : (∑ i, MvPolynomial.eval₂Hom φ x (MvPolynomial.pderiv i p)*x j*D (x i))=
        x j*(∑ i, MvPolynomial.eval₂Hom φ x (MvPolynomial.pderiv i p)*D (x i)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hsum]
    have hdelta : (∑ i, MvPolynomial.eval₂Hom φ x p*
        MvPolynomial.eval₂Hom φ x (MvPolynomial.pderiv i (MvPolynomial.X j))*D (x i))=
        MvPolynomial.eval₂Hom φ x p*D (x j) := by
      simp [MvPolynomial.pderiv_X,Pi.single_apply,apply_ite,ite_mul]
    rw [hdelta]
    ring

section InvertibleAlgebra
variable {R : Type*} [CommRing R]
lemma invariant_from_cleared (D : Derivation ℤ R R) (h q j g hi half : R)
    (hinv : hi*h=1) (hhalf : 2*half=1)
    (hc : g*(h*D q-2*q*D h)+3*j=0) :
    g*D (q*hi^2)=6*(-half*j*hi^3) := by
  have hd : D hi= -hi^2*D h := by
    simpa only [smul_eq_mul] using D.leibniz_of_mul_eq_one hinv
  rw [Derivation.leibniz,Derivation.leibniz_pow,hd]
  simp only [smul_eq_mul,nsmul_eq_mul]
  linear_combination hi^3*hc-g*D q*hi^2*hinv+3*j*hi^3*hhalf

lemma curve_from_syzygy (h q j s t hi half : R)
    (hinv : hi*h=1) (hhalf : 2*half=1)
    (hs : j^2=4*q^3+4*s*q*h^4-t*h^6) :
    (-half*j*hi^3)^2=(q*hi^2)^3+s*(q*hi^2)-half^2*t := by
  have h4 : (hi*h)^4=1 := by rw [hinv,one_pow]
  have h6 : (hi*h)^6=1 := by rw [hinv,one_pow]
  have hh : 4*half^2=1 := by
    calc
      _=(2*half)^2 := by ring
      _=1 := by rw [hhalf,one_pow]
  linear_combination half^2*hi^6*hs+q^3*hi^6*hh+
    s*q*hi^2*(hi*h)^4*hh+s*q*hi^2*h4-half^2*t*h6

/-- Normalize an integral covariant syzygy with leading coefficient `27`.
Explicit inverses of `3` and `27` keep the result valid over commutative
rings, including square-zero extensions used for first variations. -/
lemma curve_from_syzygy27 (h q j SN TN hi half third inv27 : R)
    (hinv : hi*h=1) (hhalf : 2*half=1)
    (hthird : 3*third=1) (hinv27 : 27*inv27=1)
    (hs : 27*j^2=108*q^3+36*SN*q*h^4-TN*h^6) :
    (-half*j*hi^3)^2=(q*hi^2)^3+(third*SN)*(q*hi^2)-half^2*(inv27*TN) := by
  have h36 : 36*inv27=4*third := by
    linear_combination 4*third*hinv27-36*inv27*hthird
  have hs' : j^2=4*q^3+4*(third*SN)*q*h^4-(inv27*TN)*h^6 := by
    linear_combination inv27*hs-(j^2-4*q^3)*hinv27+SN*q*h^4*h36
  exact curve_from_syzygy h q j (third*SN) (inv27*TN) hi half hinv hhalf hs'
end InvertibleAlgebra

section SquareZeroEvaluation
variable {R : Type*} [CommRing R]
open TrivSqZeroExt

/-- Evaluate a first-order identity at an arbitrary square-zero element. -/
def squareZeroEval (k : R) (hk : k^2=0) : TrivSqZeroExt R R →+* R where
  toFun a := a.fst+k*a.snd
  map_zero' := by simp
  map_one' := by simp
  map_add' := by intro a b; simp only [fst_add,snd_add]; ring
  map_mul' := by
    intro a b
    simp only [fst_mul,snd_mul,smul_eq_mul,op_smul_eq_smul]
    linear_combination -a.snd*b.snd*hk

@[simp] theorem squareZeroEval_mk (k : R) (hk : k^2=0) (a b : R) :
    squareZeroEval k hk (a,b)=a+k*b := rfl
end SquareZeroEvaluation

section Jets
variable {K : Type*} [Field K]
abbrev Jet := TrivSqZeroExt K K
open TrivSqZeroExt

@[simp] lemma fst_numeral (n : ℕ) [n.AtLeastTwo] :
    (ofNat(n) : Jet (K:=K)).fst=(ofNat(n) : K) := rfl
@[simp] lemma snd_numeral (n : ℕ) [n.AtLeastTwo] :
    (ofNat(n) : Jet (K:=K)).snd=0 := rfl

def jetDerivation (D : Derivation ℤ K K) : Derivation ℤ (Jet (K:=K)) (Jet (K:=K)) where
  toFun z := (D z.fst,D z.snd)
  map_add' a b := TrivSqZeroExt.ext (map_add D a.fst b.fst) (map_add D a.snd b.snd)
  map_smul' n a := TrivSqZeroExt.ext (D.map_smul n a.fst) (D.map_smul n a.snd)
  map_one_eq_zero' := TrivSqZeroExt.ext D.map_one_eq_zero (map_zero D)
  leibniz' a b := TrivSqZeroExt.ext (D.leibniz a.fst b.fst)
    (show D (a.fst*b.snd+a.snd*b.fst) =
        (a.fst*D b.snd+a.snd*D b.fst)+(b.fst*D a.snd+b.snd*D a.fst) by
      rw [map_add,D.leibniz,D.leibniz]
      simp only [smul_eq_mul]
      ring)

lemma jetDerivation_fst (D : Derivation ℤ K K) (a : Jet (K:=K)) :
    (jetDerivation D a).fst=D a.fst := rfl
lemma jetDerivation_snd (D : Derivation ℤ K K) (a : Jet (K:=K)) :
    (jetDerivation D a).snd=D a.snd := rfl

lemma jetDerivation_inv (D : Derivation ℤ K K) (a : Jet (K:=K)) (ha : a.fst≠0) :
    jetDerivation D a⁻¹= -a⁻¹^2*jetDerivation D a := by
  simpa only [smul_eq_mul] using
    (jetDerivation D).leibniz_of_mul_eq_one (TrivSqZeroExt.inv_mul_cancel ha)

lemma curve_first_variation (ξ η a b : Jet (K:=K))
    (h : η^2=ξ^3+a*ξ+b) :
    2*η.fst*η.snd=(3*ξ.fst^2+a.fst)*ξ.snd+a.snd*ξ.fst+b.snd := by
  have hs := congrArg TrivSqZeroExt.snd h
  simp only [snd_pow,snd_add,snd_mul,smul_eq_mul,op_smul_eq_smul,nsmul_eq_mul] at hs
  norm_num at hs
  linear_combination hs

lemma differential_first_variation (D : Derivation ℤ K K) (ξ η g : Jet (K:=K))
    (h : g*jetDerivation D ξ=6*η) :
    g.fst*D ξ.snd+g.snd*D ξ.fst=6*η.snd := by
  have hs := congrArg TrivSqZeroExt.snd h
  simp only [snd_mul,jetDerivation_fst,jetDerivation_snd,fst_numeral,snd_numeral,
    smul_eq_mul,op_smul_eq_smul,mul_zero,add_zero] at hs
  linear_combination hs

lemma differential_jet_from_cleared (g η Dξ ξdotDerivative ηdot gdot : K)
    (hvalue : g*Dξ=6*η)
    (hjet : g*ξdotDerivative+gdot*Dξ=6*ηdot) :
    g^2*(2*η*ξdotDerivative-2*Dξ*ηdot)= -4*η^2*3*gdot := by
  linear_combination 2*η*g*hjet-(2*g*ηdot+2*η*gdot)*hvalue

end Jets
end ResidueFirstJets

#print axioms ResidueFirstJets.ring_chain
#print axioms ResidueFirstJets.invariant_from_cleared
#print axioms ResidueFirstJets.curve_from_syzygy
#print axioms ResidueFirstJets.curve_from_syzygy27
#print axioms ResidueFirstJets.squareZeroEval
#print axioms ResidueFirstJets.curve_first_variation
#print axioms ResidueFirstJets.differential_first_variation
#print axioms ResidueFirstJets.differential_jet_from_cleared
