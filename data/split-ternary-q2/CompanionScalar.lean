import Proposal.EllipticSource
import HodgeComputer.Constructions.EllipticCompanions.Calculus
import HodgeComputer.Constructions.EllipticCompanions.Kernels
import HodgeComputer.Constructions.EllipticCompanions.ScalarEmbedding

/-!
Scalar conversion for an arbitrary affine ternary p and the rational source
-7*h*S/(6*T^2). Only supplied ambient primitive/jet data are consumed; existence
of such data is not assumed from an arbitrary affine source replacement.
The first-jet identity is imported from the accepted crossed-ternary proof of
1337isnot1337, through its maintained generic library.
Prepared with OpenAI Codex assistance for contributor fqlx.
-/

noncomputable section
namespace SplitCompanionScalar
open CrossedElliptic CrossedScalarCompanionJet
open scoped BigOperators
abbrev P2 := MvPolynomial (Fin 2) ℂ
variable {K : Type*} [Field K] [CharZero K]
local instance : Algebra ℤ (E K) := Ring.toIntAlgebra _

def rootValue (u : K) : E K := algebraMap K (E K) u
def polynomialValue (φ : P2 →+* K) (h : P2) : E K := algebraMap K (E K) (φ h)
def gradientValue (φ : P2 →+* K) (p : P2) (i : Fin 2) : E K :=
  polynomialValue φ (MvPolynomial.pderiv i p)

/-- Evaluated ambient values and first jets for the rational pole-two source.
The normal equation and its S,T derivatives use the UNscaled companion p+S³+T³.
A cleared-equation adapter below divides all three source equations by seven. -/
structure JetData (p h : P2) (φ : P2 →+* K) (u : K)
    (Dx Dy : Derivation ℤ K K) where
  value : Fin 4 → E K
  jet : Matrix (Fin 4) (Fin 4) (E K)
  deltaS : delta (value 2)=rootValue u*b^2*jet 2 2-rootValue u*a^2*jet 2 3
  deltaT : delta (value 3)=rootValue u*b^2*jet 3 2-rootValue u*a^2*jet 3 3
  derivativeX : coefficient Dx (value 0)=jet 0 0+
    gradientValue φ p 0/(3*(rootValue u)^2)*(a*jet 0 2+b*jet 0 3)
  derivativeY : coefficient Dy (value 1)=jet 1 1+
    gradientValue φ p 1/(3*(rootValue u)^2)*(a*jet 1 2+b*jet 1 3)
  divergence : jet 0 0+jet 1 1+jet 2 2+jet 3 3=0
  normal : gradientValue φ p 0*value 0+gradientValue φ p 1*value 1+
    3*(rootValue u)^2*a^2*value 2+3*(rootValue u)^2*b^2*value 3=
      -polynomialValue φ h*a/(6*rootValue u*b^2)
  normalS : gradientValue φ p 0*jet 0 2+gradientValue φ p 1*jet 1 2+
    6*rootValue u*a*value 2+3*(rootValue u)^2*a^2*jet 2 2+3*(rootValue u)^2*b^2*jet 3 2=
      -polynomialValue φ h/(6*(rootValue u)^2*b^2)
  normalT : gradientValue φ p 0*jet 0 3+gradientValue φ p 1*jet 1 3+
    6*rootValue u*b*value 3+3*(rootValue u)^2*a^2*jet 2 3+3*(rootValue u)^2*b^2*jet 3 3=
      polynomialValue φ h*a/(3*(rootValue u)^2*b^3)
  killed : ∀ Z : Derivation ℤ K K,(∀ P : P2,Z (φ P)=0) → Z u=0 →
    ∀ i,coefficient Z (value i)=0

lemma a_ne_zero : a (K:=K)≠0 := by
  intro ha
  apply fermat_a_transcendental (K:=K)
  rw [ha]
  exact isAlgebraic_zero
lemma b_ne_zero : b (K:=K)≠0 := by
  intro hb
  have he := fermat_relation (K:=K)
  rw [hb,zero_pow (by decide : (3 : ℕ)≠0),add_zero] at he
  apply fermat_a_transcendental (K:=K)
  apply IsAlgebraic.of_pow (n:=3) (by decide : 0<3)
  rw [show a (K:=K)^3= -1 by linear_combination he]
  exact isAlgebraic_one.neg

theorem scalar_equation_of_jets (p h : P2) (φ : P2 →+* K) (u : K)
    (Dx Dy : Derivation ℤ K K) (hu : u≠0)
    (hDx : Dx u=φ (MvPolynomial.pderiv 0 p)/(3*u^2))
    (hDy : Dy u=φ (MvPolynomial.pderiv 1 p)/(3*u^2))
    (v : JetData p h φ u Dx Dy) :
    delta (scalarB (rootValue u) a b v.value)+
      coefficient Dx (scalarX (rootValue u) v.value)+
      coefficient Dy (scalarY (rootValue u) v.value)=
        -(polynomialValue φ h)*a/(3*(rootValue u)^5*b^2) := by
  have hu0 : rootValue u≠0 := (map_ne_zero _).mpr hu
  have hdX : coefficient Dx (rootValue u)=gradientValue φ p 0/(3*(rootValue u)^2) := by
    simp only [rootValue,gradientValue,polynomialValue,coefficient_scalar,hDx,map_div₀,map_mul,map_pow,map_ofNat]
  have hdY : coefficient Dy (rootValue u)=gradientValue φ p 1/(3*(rootValue u)^2) := by
    simp only [rootValue,gradientValue,polynomialValue,coefficient_scalar,hDy,map_div₀,map_mul,map_pow,map_ofNat]
  have he := CrossedScalarCompanionJet.scalar_equation delta (coefficient Dx) (coefficient Dy)
    (rootValue u) a b (gradientValue φ p 0) (gradientValue φ p 1)
    (-polynomialValue φ h*a/(6*rootValue u*b^2))
    (-polynomialValue φ h/(6*(rootValue u)^2*b^2))
    (polynomialValue φ h*a/(3*(rootValue u)^2*b^3)) v.value v.jet
    hu0 (delta_base u) delta_a delta_b hdX hdY v.deltaS v.deltaT v.derivativeX v.derivativeY
    fermat_relation v.divergence v.normal v.normalS v.normalT
  rw [he]
  field_simp [hu0,b_ne_zero (K:=K)]
  ring

/-- The rational companion source produces the actual theta primitive,
including preservation under arbitrary derivations killing the block. -/
theorem theta_primitive_of_jets (p h : P2) (φ : P2 →+* K) (u : K)
    (Dx Dy : Derivation ℤ K K) (hu : u≠0)
    (hDx : Dx u=φ (MvPolynomial.pderiv 0 p)/(3*u^2))
    (hDy : Dy u=φ (MvPolynomial.pderiv 1 p)/(3*u^2))
    (v : JetData p h φ u Dx Dy) :
    ∃ bf cx cy : E K,
      (delta bf+coefficient Dx cx+coefficient Dy cy=
        algebraMap K (E K) (φ h/u^5)*thetaRatio) ∧
      ∀ Z : Derivation ℤ K K,(∀ P : P2,Z (φ P)=0) → Z u=0 →
        coefficient Z bf=0 ∧ coefficient Z cx=0 ∧ coefficient Z cy=0 := by
  let f := scalarB (rootValue u) a b v.value
  let cx := scalarX (rootValue u) v.value
  let cy := scalarY (rootValue u) v.value
  let α : E K := algebraMap K (E K) (φ h/u^5)
  have hf : delta f+(coefficient Dx cx+coefficient Dy cy)= -α*a/(3*b^2) := by
    have he := scalar_equation_of_jets p h φ u Dx Dy hu hDx hDy v
    change delta (scalarB (rootValue u) a b v.value)+
      (coefficient Dx (scalarX (rootValue u) v.value)+
        coefficient Dy (scalarY (rootValue u) v.value))=_
    rw [← add_assoc,he]
    simp only [α,polynomialValue,rootValue,map_div₀,map_pow]
    ring
  have hc := SplitEllipticSource.corrected_primitive delta a b α f
    (coefficient Dx cx+coefficient Dy cy) a_ne_zero b_ne_zero delta_a delta_b
    (delta_base _) fermat_relation hf
  refine ⟨-3*f+α*(a^2/b+b^2/a),-3*cx,-3*cy,?_,?_⟩
  · have h3x : coefficient Dx (-3 : E K)=0 := by
      rw [map_neg]; exact neg_eq_zero.mpr ((coefficient Dx).map_natCast 3)
    have h3y : coefficient Dy (-3 : E K)=0 := by
      rw [map_neg]; exact neg_eq_zero.mpr ((coefficient Dy).map_natCast 3)
    simp only [Derivation.leibniz,h3x,h3y,smul_eq_mul,smul_zero,zero_mul,zero_add,thetaRatio]
    linear_combination hc
  · intro Z hZ hZu
    have hα : coefficient Z α=0 := by
      simp only [α,coefficient_scalar,Derivation.leibniz_div,Derivation.leibniz_pow,hZ,hZu,
        smul_eq_mul,smul_zero,zero_mul,mul_zero,sub_self,zero_div,map_zero]
    have h3 : coefficient Z (3 : E K)=0 := (coefficient Z).map_natCast 3
    have hf0 : coefficient Z f=0 := by
      simp only [f,scalarB,Derivation.leibniz_div,Derivation.leibniz,Derivation.leibniz_pow,
        map_sub,rootValue,coefficient_scalar,coefficient_a,coefficient_b,v.killed Z hZ hZu,
        hZu,h3,smul_eq_mul,smul_zero,mul_zero,zero_mul,sub_self,zero_add,add_zero,zero_div,map_zero]
    have hx0 : coefficient Z cx=0 := by
      simp only [cx,scalarX,Derivation.leibniz_div,Derivation.leibniz,map_neg,rootValue,
        coefficient_scalar,v.killed Z hZ hZu,hZu,h3,smul_eq_mul,smul_zero,mul_zero,zero_mul,
        sub_self,zero_add,add_zero,zero_div,map_zero,neg_zero]
    have hy0 : coefficient Z cy=0 := by
      simp only [cy,scalarY,Derivation.leibniz_div,Derivation.leibniz,map_neg,rootValue,
        coefficient_scalar,v.killed Z hZ hZu,hZu,h3,smul_eq_mul,smul_zero,mul_zero,zero_mul,
        sub_self,zero_add,add_zero,zero_div,map_zero,neg_zero]
    simp only [map_add,map_neg,Derivation.leibniz,Derivation.leibniz_div,Derivation.leibniz_pow,
      coefficient_a,coefficient_b,hα,hf0,hx0,hy0,h3,smul_eq_mul,smul_zero,mul_zero,zero_mul,
      sub_self,zero_add,add_zero,zero_div,neg_zero]
    trivial

end SplitCompanionScalar

#print axioms SplitCompanionScalar.theta_primitive_of_jets

namespace SplitCompanionScalar
open CrossedElliptic CrossedEvaluatedJets HoldoutConstruction
open scoped BigOperators
variable {K R : Type*} [Field K] [CharZero K] [CommRing R]
local instance : Algebra ℤ (E K) := Ring.toIntAlgebra _

/-- An ambient cleared primitive gives evaluated first jets. R may be the
polynomial ring localized at T, so the rational source is an actual element
of R. The only denominator inversion here is the explicitly nonzero rho D.
No map on an unrestricted ambient rational function field is assumed. -/
def jetData_of_ambient
    (p h : P2) (φ : P2 →+* K) (u : K) (Dx Dy : Derivation ℤ K K)
    (ρ : R →+* E K) (Δ : Fin 4 → Derivation ℤ R R)
    (D A : R) (N g : Fin 4 → R)
    (hd : ρ D≠0) (hn : (∑ i,N i*g i)=A*D)
    (hdiv : ρ (D*(∑ i,Δ i (N i))-(∑ i,N i*Δ i D))=0)
    (hgradient : ∀ i,ρ (g i)=
      ![7*gradientValue φ p 0,7*gradientValue φ p 1,
        21*(rootValue u)^2*a^2,21*(rootValue u)^2*b^2] i)
    (hhessianS : ∀ i,ρ (Δ 2 (g i))=![0,0,42*rootValue u*a,0] i)
    (hhessianT : ∀ i,ρ (Δ 3 (g i))=![0,0,0,42*rootValue u*b] i)
    (hsource : ρ A= -7*polynomialValue φ h*a/(6*rootValue u*b^2))
    (hsourceS : ρ (Δ 2 A)= -7*polynomialValue φ h/(6*(rootValue u)^2*b^2))
    (hsourceT : ρ (Δ 3 A)= 7*polynomialValue φ h*a/(3*(rootValue u)^2*b^3))
    (hdelta : ∀ P,delta (ρ P)=∑ j,ρ (Δ j P)*![0,0,rootValue u*b^2,-rootValue u*a^2] j)
    (hDx : ∀ P,coefficient Dx (ρ P)=∑ j,ρ (Δ j P)*
      ![1,0,a*gradientValue φ p 0/(3*(rootValue u)^2),b*gradientValue φ p 0/(3*(rootValue u)^2)] j)
    (hDy : ∀ P,coefficient Dy (ρ P)=∑ j,ρ (Δ j P)*
      ![0,1,a*gradientValue φ p 1/(3*(rootValue u)^2),b*gradientValue φ p 1/(3*(rootValue u)^2)] j)
    (hkilled : ∀ Z : Derivation ℤ K K,(∀ P : P2,Z (φ P)=0) → Z u=0 →
      ∀ P,coefficient Z (ρ P)=0) : JetData p h φ u Dx Dy := by
  let V := values ρ D N
  let J := jet ρ Δ D N
  refine {
    value := V
    jet := J
    deltaS := ?_
    deltaT := ?_
    derivativeX := ?_
    derivativeY := ?_
    divergence := ?_
    normal := ?_
    normalS := ?_
    normalT := ?_
    killed := ?_ }
  · have he := derivative_values ρ Δ delta
      ![0,0,rootValue u*b^2,-rootValue u*a^2] hdelta D N hd 2
    change delta (V 2)=_ at he
    change delta (V 2)=_
    simp only [Fin.sum_univ_four,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val] at he
    linear_combination he
  · have he := derivative_values ρ Δ delta
      ![0,0,rootValue u*b^2,-rootValue u*a^2] hdelta D N hd 3
    change delta (V 3)=_ at he
    change delta (V 3)=_
    simp only [Fin.sum_univ_four,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val] at he
    linear_combination he
  · have he := derivative_values ρ Δ (coefficient Dx)
      ![1,0,a*gradientValue φ p 0/(3*(rootValue u)^2),b*gradientValue φ p 0/(3*(rootValue u)^2)]
      hDx D N hd 0
    change coefficient Dx (V 0)=_ at he
    change coefficient Dx (V 0)=_
    simp only [Fin.sum_univ_four,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val] at he
    linear_combination he
  · have he := derivative_values ρ Δ (coefficient Dy)
      ![0,1,a*gradientValue φ p 1/(3*(rootValue u)^2),b*gradientValue φ p 1/(3*(rootValue u)^2)]
      hDy D N hd 1
    change coefficient Dy (V 1)=_ at he
    change coefficient Dy (V 1)=_
    simp only [Fin.sum_univ_four,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val] at he
    linear_combination he
  · have he := divergence_jets ρ Δ D N hd hdiv
    simpa only [Fin.sum_univ_four,add_assoc] using he
  · have he := normal_values ρ D A N g hd hn
    simp only [hgradient,hsource,Fin.sum_univ_four,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val] at he
    linear_combination (1/7 : E K)*he
  · have he := normal_jets ρ Δ D A N g hd hn 2
    simp only [hgradient,hhessianS,hsourceS,Fin.sum_univ_four,Matrix.cons_val_zero,
      Matrix.cons_val_one,Matrix.cons_val] at he
    linear_combination (1/7 : E K)*he
  · have he := normal_jets ρ Δ D A N g hd hn 3
    simp only [hgradient,hhessianT,hsourceT,Fin.sum_univ_four,Matrix.cons_val_zero,
      Matrix.cons_val_one,Matrix.cons_val] at he
    linear_combination (1/7 : E K)*he
  · intro Z hZ hZu i
    simp only [V,values,Derivation.leibniz_div,hkilled Z hZ hZu,smul_eq_mul,
      zero_mul,mul_zero,sub_self,zero_div]

end SplitCompanionScalar

#print axioms SplitCompanionScalar.jetData_of_ambient

namespace SplitCompanionScalar
open CrossedEvaluatedJets HoldoutConstruction
open scoped BigOperators
variable {R L : Type*} [CommRing R] [Field L]

lemma rational_normal_values (ρ : R →+* L) (D A Q : R) (N g : Fin 4 → R)
    (hd : ρ D≠0) (hq : ρ Q≠0) (hn : Q*(∑ i,N i*g i)=A*D) :
    (∑ i,values ρ D N i*ρ (g i))=ρ A/ρ Q := by
  have he := congrArg ρ hn
  simp only [map_sum,map_mul,map_add,map_zero,Fin.sum_univ_four] at he
  simp only [values,Fin.sum_univ_four]
  field_simp
  linear_combination he

lemma rational_normal_jets (ρ : R →+* L) (Δ : Fin 4 → Derivation ℤ R R)
    (D A Q : R) (N g : Fin 4 → R) (hd : ρ D≠0) (hq : ρ Q≠0)
    (hn : Q*(∑ i,N i*g i)=A*D) (j : Fin 4) :
    (∑ i,jet ρ Δ D N i j*ρ (g i))+
      (∑ i,values ρ D N i*ρ (Δ j (g i)))=
        (ρ (Δ j A)*ρ Q-ρ A*ρ (Δ j Q))/(ρ Q)^2 := by
  have he := congrArg ρ hn
  have he' := congrArg (fun P => ρ (Δ j P)) hn
  simp only [map_sum,map_mul,map_add,map_zero,Derivation.leibniz,smul_eq_mul,Fin.sum_univ_four] at he he'
  simp only [jet,values,Fin.sum_univ_four]
  field_simp
  linear_combination ρ D*ρ Q*he'-(ρ D*ρ (Δ j Q)+ρ Q*ρ (Δ j D))*he

end SplitCompanionScalar

namespace SplitCompanionScalar
open CrossedElliptic CrossedEvaluatedJets HoldoutConstruction
open scoped BigOperators
variable {K R : Type*} [Field K] [CharZero K] [CommRing R]
local instance : Algebra ℤ (E K) := Ring.toIntAlgebra _

/-- Polynomial-only version: the source A/Q is supplied through its cleared
normal identity and quotient-rule source jets. Q=6*T² is the intended use.
No localization of R or extension of its ambient derivations is needed. -/
def jetData_of_polynomial_rational_source
    (p h : P2) (φ : P2 →+* K) (u : K) (Dx Dy : Derivation ℤ K K)
    (ρ : R →+* E K) (Δ : Fin 4 → Derivation ℤ R R)
    (D A Q : R) (N g : Fin 4 → R)
    (hd : ρ D≠0) (hq : ρ Q≠0) (hn : Q*(∑ i,N i*g i)=A*D)
    (hdiv : ρ (D*(∑ i,Δ i (N i))-(∑ i,N i*Δ i D))=0)
    (hgradient : ∀ i,ρ (g i)=
      ![7*gradientValue φ p 0,7*gradientValue φ p 1,
        21*(rootValue u)^2*a^2,21*(rootValue u)^2*b^2] i)
    (hhessianS : ∀ i,ρ (Δ 2 (g i))=![0,0,42*rootValue u*a,0] i)
    (hhessianT : ∀ i,ρ (Δ 3 (g i))=![0,0,0,42*rootValue u*b] i)
    (hsource : ρ A/ρ Q= -7*polynomialValue φ h*a/(6*rootValue u*b^2))
    (hsourceS : (ρ (Δ 2 A)*ρ Q-ρ A*ρ (Δ 2 Q))/(ρ Q)^2= -7*polynomialValue φ h/(6*(rootValue u)^2*b^2))
    (hsourceT : (ρ (Δ 3 A)*ρ Q-ρ A*ρ (Δ 3 Q))/(ρ Q)^2= 7*polynomialValue φ h*a/(3*(rootValue u)^2*b^3))
    (hdelta : ∀ P,delta (ρ P)=∑ j,ρ (Δ j P)*![0,0,rootValue u*b^2,-rootValue u*a^2] j)
    (hDx : ∀ P,coefficient Dx (ρ P)=∑ j,ρ (Δ j P)*
      ![1,0,a*gradientValue φ p 0/(3*(rootValue u)^2),b*gradientValue φ p 0/(3*(rootValue u)^2)] j)
    (hDy : ∀ P,coefficient Dy (ρ P)=∑ j,ρ (Δ j P)*
      ![0,1,a*gradientValue φ p 1/(3*(rootValue u)^2),b*gradientValue φ p 1/(3*(rootValue u)^2)] j)
    (hkilled : ∀ Z : Derivation ℤ K K,(∀ P : P2,Z (φ P)=0) → Z u=0 →
      ∀ P,coefficient Z (ρ P)=0) : JetData p h φ u Dx Dy := by
  let V := values ρ D N
  let J := jet ρ Δ D N
  refine {
    value := V
    jet := J
    deltaS := ?_
    deltaT := ?_
    derivativeX := ?_
    derivativeY := ?_
    divergence := ?_
    normal := ?_
    normalS := ?_
    normalT := ?_
    killed := ?_ }
  · have he := derivative_values ρ Δ delta
      ![0,0,rootValue u*b^2,-rootValue u*a^2] hdelta D N hd 2
    change delta (V 2)=_ at he
    change delta (V 2)=_
    simp only [Fin.sum_univ_four,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val] at he
    linear_combination he
  · have he := derivative_values ρ Δ delta
      ![0,0,rootValue u*b^2,-rootValue u*a^2] hdelta D N hd 3
    change delta (V 3)=_ at he
    change delta (V 3)=_
    simp only [Fin.sum_univ_four,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val] at he
    linear_combination he
  · have he := derivative_values ρ Δ (coefficient Dx)
      ![1,0,a*gradientValue φ p 0/(3*(rootValue u)^2),b*gradientValue φ p 0/(3*(rootValue u)^2)]
      hDx D N hd 0
    change coefficient Dx (V 0)=_ at he
    change coefficient Dx (V 0)=_
    simp only [Fin.sum_univ_four,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val] at he
    linear_combination he
  · have he := derivative_values ρ Δ (coefficient Dy)
      ![0,1,a*gradientValue φ p 1/(3*(rootValue u)^2),b*gradientValue φ p 1/(3*(rootValue u)^2)]
      hDy D N hd 1
    change coefficient Dy (V 1)=_ at he
    change coefficient Dy (V 1)=_
    simp only [Fin.sum_univ_four,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val] at he
    linear_combination he
  · have he := divergence_jets ρ Δ D N hd hdiv
    simpa only [Fin.sum_univ_four,add_assoc] using he
  · have he := rational_normal_values ρ D A Q N g hd hq hn
    simp only [hgradient,hsource,Fin.sum_univ_four,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val] at he
    linear_combination (1/7 : E K)*he
  · have he := rational_normal_jets ρ Δ D A Q N g hd hq hn 2
    simp only [hgradient,hhessianS,hsourceS,Fin.sum_univ_four,Matrix.cons_val_zero,
      Matrix.cons_val_one,Matrix.cons_val] at he
    linear_combination (1/7 : E K)*he
  · have he := rational_normal_jets ρ Δ D A Q N g hd hq hn 3
    simp only [hgradient,hhessianT,hsourceT,Fin.sum_univ_four,Matrix.cons_val_zero,
      Matrix.cons_val_one,Matrix.cons_val] at he
    linear_combination (1/7 : E K)*he
  · intro Z hZ hZu i
    simp only [V,values,Derivation.leibniz_div,hkilled Z hZ hZu,smul_eq_mul,
      zero_mul,mul_zero,sub_self,zero_div]

end SplitCompanionScalar

#print axioms SplitCompanionScalar.jetData_of_polynomial_rational_source
