import Proposal.HigherPoleTransport
import HodgeComputer.Constructions.HoldoutCover.HomogeneousField
import HodgeComputer.Constructions.HoldoutCover.HypersurfaceDomain
import HodgeComputer.Constructions.HoldoutCover.FiniteDifferentials
import HodgeComputer.Constructions.HoldoutCover.PolynomialFamilyBridge
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

/-!
Physical chart for the exact split-ternary-q2 target.
The coordinate, derivation, and Jacobian arguments adapt the accepted
crossed-ternary-asymmetric construction of 1337isnot1337, which builds
on the fqlx and HeadOfNaps finite-field/derivation constructions credited there.
The chart, exact target, and pole-two field here are target-specific.
Prepared with OpenAI Codex assistance for contributor fqlx.
No certificate existence is asserted without the weighted-divergence input.
-/

noncomputable section
namespace SplitTernaryPhysical
open MvPolynomial HoldoutConstruction

abbrev Poly := MvPolynomial (Fin 6) ℂ
abbrev M := FractionRing Poly
abbrev Base := MvPolynomial (Fin 4) ℂ
abbrev BaseField := FractionRing Base
local instance : Algebra ℤ BaseField := Ring.toIntAlgebra _
def baseD (i : Fin 4) : Derivation ℤ BaseField BaseField := extendRingDerivation (integerPartial (R:=ℂ) i)
lemma baseD_polynomial (i : Fin 4) (P : Base) :
    baseD i (algebraMap Base BaseField P)=algebraMap Base BaseField (integerPartial i P) := extendRingDerivation_apply _ _
local instance : Algebra ℤ M := Ring.toIntAlgebra _

/-- Physical coordinates in the order x,a,r,z,lambda,t. -/
def exponentMap : (Fin 6 →₀ ℕ) →+ (Fin 6 →₀ ℕ) where
  toFun s := Finsupp.single 0 (s 0)+Finsupp.single 1 (s 1)+
    Finsupp.single 2 (s 3)+Finsupp.single 3 (s 4)+Finsupp.single 4 (s 3+s 4+s 5)+
    Finsupp.single 5 (s 0+s 1+s 2+s 3+s 4+s 5)
  map_zero' := by ext j; fin_cases j <;> simp
  map_add' s u := by ext j; fin_cases j <;> simp <;> omega
lemma exponentMap_injective : Function.Injective exponentMap := by
  intro s u h
  have h0 := congrArg (fun v : Fin 6 →₀ ℕ => v 0) h
  have h1 := congrArg (fun v : Fin 6 →₀ ℕ => v 1) h
  have h2 := congrArg (fun v : Fin 6 →₀ ℕ => v 2) h
  have h3 := congrArg (fun v : Fin 6 →₀ ℕ => v 3) h
  have h4 := congrArg (fun v : Fin 6 →₀ ℕ => v 4) h
  have h5 := congrArg (fun v : Fin 6 →₀ ℕ => v 5) h
  simp [exponentMap] at h0 h1 h2 h3 h4 h5
  have hs2 : s 2=u 2 := by omega
  have hs5 : s 5=u 5 := by omega
  ext j
  fin_cases j
  · exact h0
  · exact h1
  · exact hs2
  · exact h2
  · exact h3
  · exact hs5

def monomialMap : Poly →+* Poly := AddMonoidAlgebra.mapDomainRingHom ℂ exponentMap
lemma monomialMap_injective : Function.Injective monomialMap := AddMonoidAlgebra.mapDomain_injective exponentMap_injective
lemma monomialMap_C (c : ℂ) : monomialMap (C c)=C c := by
  simp [monomialMap,MvPolynomial.C,MvPolynomial.monomial,exponentMap]
lemma monomialMap_X (i : Fin 6) : monomialMap (X i)=
    ![X 5*X 0,X 5*X 1,X 5,X 5*X 4*X 2,X 5*X 4*X 3,X 5*X 4] i := by
  change AddMonoidAlgebra.mapDomain exponentMap
    (AddMonoidAlgebra.single (Finsupp.single i 1) (1 : ℂ))=_
  rw [AddMonoidAlgebra.mapDomain_single]
  fin_cases i <;>
    simp only [Matrix.cons_val_zero',Matrix.cons_val_succ',MvPolynomial.X,
      MvPolynomial.monomial,AddMonoidAlgebra.lsingle_apply,AddMonoidAlgebra.single_mul_single,
      AddMonoidAlgebra.single_pow,one_mul,one_pow]
  all_goals congr 1
  all_goals ext j
  all_goals fin_cases j <;> simp [exponentMap]

def θ : Poly →+* M := (algebraMap Poly M).comp monomialMap
lemma θ_injective : Function.Injective θ := (IsFractionRing.injective Poly M).comp monomialMap_injective

def coordinate (i : Fin 6) : M := algebraMap Poly M (X i)
def chartD (i : Fin 6) : Derivation ℤ M M := extendRingDerivation (integerPartial (R:=ℂ) i)
lemma chartD_polynomial (i : Fin 6) (P : Poly) :
    chartD i (algebraMap Poly M P)=algebraMap Poly M (integerPartial i P) := extendRingDerivation_apply _ _
lemma chartD_C (i : Fin 6) (c : ℂ) : chartD i (algebraMap Poly M (C c))=0 := by
  rw [chartD_polynomial,integerPartial_C,map_zero]
lemma chartD_coordinate (i j : Fin 6) : chartD i (coordinate j)=if j=i then 1 else 0 := by
  rw [coordinate,chartD_polynomial]
  by_cases h : j=i
  · subst j; simp
  · rw [integerPartial_X_of_ne _ _ h,map_zero,ite_eq_right h]
lemma coordinate_ne_zero (i : Fin 6) : coordinate i≠0 := by
  simpa only [coordinate,map_zero] using (IsFractionRing.injective Poly M).ne (MvPolynomial.X_ne_zero (R:=ℂ) i)
lemma θ_C (c : ℂ) : θ (C c)=algebraMap Poly M (C c) := by rw [θ,RingHom.comp_apply,monomialMap_C]
lemma θ_X (i : Fin 6) : θ (X i)=
    ![coordinate 5*coordinate 0,coordinate 5*coordinate 1,coordinate 5,
      coordinate 5*coordinate 4*coordinate 2,coordinate 5*coordinate 4*coordinate 3,coordinate 5*coordinate 4] i := by
  rw [θ,RingHom.comp_apply,monomialMap_X]
  fin_cases i <;> simp [coordinate]

def baseIndex : Fin 4 → Fin 6 := ![0,1,2,3]
lemma baseIndex_injective : Function.Injective baseIndex := by
  intro i j h; fin_cases i <;> fin_cases j <;> simp_all [baseIndex]
def baseRingMap : Base →+* M :=
  (algebraMap Poly M).comp (MvPolynomial.rename baseIndex).toRingHom
lemma baseRingMap_injective : Function.Injective baseRingMap :=
  (IsFractionRing.injective Poly M).comp (MvPolynomial.rename_injective baseIndex baseIndex_injective)
def baseValue : BaseField →+* M := IsFractionRing.lift baseRingMap_injective
lemma baseValue_polynomial (P : Base) :
    baseValue (algebraMap Base BaseField P)=baseRingMap P :=
  IsFractionRing.lift_algebraMap baseRingMap_injective P
lemma baseRingMap_C (c : ℂ) : baseRingMap (C c)=algebraMap Poly M (C c) := by simp [baseRingMap]
lemma baseRingMap_X (i : Fin 4) : baseRingMap (X i)=coordinate (baseIndex i) := by simp [baseRingMap,coordinate]

end SplitTernaryPhysical
end

/- Source component: PhysicalChartDerivations. -/
section

noncomputable section
namespace SplitTernaryPhysical
open MvPolynomial HoldoutConstruction
open scoped BigOperators
local instance : Algebra ℤ M := Ring.toIntAlgebra _
local instance : Algebra ℤ BaseField := Ring.toIntAlgebra _

lemma chartD_baseValue (i : Fin 4) (f : BaseField) :
    chartD (baseIndex i) (baseValue f)=baseValue (baseD i f) := by
  apply derivation_intertwines_quotient_fraction (RingHom.id Base)
    Function.surjective_id baseValue (baseD i) (chartD (baseIndex i))
  · intro c
    simp only [RingHom.id_apply,baseValue_polynomial,baseD_polynomial,
      integerPartial_C,map_zero,baseRingMap_C,chartD_C]
  · intro j
    simp only [RingHom.id_apply,baseValue_polynomial,baseD_polynomial,
      integerPartial_apply,baseRingMap_X,chartD_coordinate]
    by_cases h : j=i
    · subst j; simp
    · have hne : baseIndex j≠baseIndex i := fun he => h (baseIndex_injective he)
      simp [h,hne]

lemma chartD_baseValue_zero (k : Fin 6) (hk : ∀ i : Fin 4,baseIndex i≠k) (f : BaseField) :
    chartD k (baseValue f)=0 := by
  have he := derivation_intertwines_quotient_fraction (RingHom.id Base)
    Function.surjective_id baseValue (0 : Derivation ℤ BaseField BaseField) (chartD k)
    (by intro c; simp only [RingHom.id_apply,baseValue_polynomial,baseRingMap_C,chartD_C,
          FunLike.coe_zero,Pi.zero_apply,map_zero])
    (by intro i; simp only [RingHom.id_apply,baseValue_polynomial,baseRingMap_X,chartD_coordinate,
          ite_eq_right (hk i),FunLike.coe_zero,Pi.zero_apply,map_zero]) f
  simpa only [FunLike.coe_zero,Pi.zero_apply,map_zero] using he
lemma chartD_lambda_base (f : BaseField) : chartD 4 (baseValue f)=0 := by
  apply chartD_baseValue_zero
  intro i; fin_cases i <;> simp [baseIndex]
lemma chartD_radial_base (f : BaseField) : chartD 5 (baseValue f)=0 := by
  apply chartD_baseValue_zero
  intro i; fin_cases i <;> simp [baseIndex]

def physicalCoefficients (i : Fin 6) : Fin 6 → M :=
  ![![1/coordinate 5,0,0,0,0,0],![0,1/coordinate 5,0,0,0,0],
    ![-coordinate 0/coordinate 5,-coordinate 1/coordinate 5,0,0,-coordinate 4/coordinate 5,1],
    ![0,0,1/(coordinate 5*coordinate 4),0,0,0],![0,0,0,1/(coordinate 5*coordinate 4),0,0],
    ![0,0,-coordinate 2/(coordinate 5*coordinate 4),-coordinate 3/(coordinate 5*coordinate 4),1/coordinate 5,0]] i

def physicalD (i : Fin 6) : Derivation ℤ M M := derivationLinearCombination chartD (physicalCoefficients i)
lemma physicalD_apply (i : Fin 6) (f : M) :
    physicalD i f=∑ k,physicalCoefficients i k*chartD k f := derivationLinearCombination_apply _ _ _
lemma physicalD_C (i : Fin 6) (c : ℂ) : physicalD i (algebraMap Poly M (C c))=0 := by
  simp only [physicalD_apply,chartD_C,mul_zero,Finset.sum_const_zero]
lemma physicalD_coordinate (i k : Fin 6) : physicalD i (coordinate k)=physicalCoefficients i k := by
  simp [physicalD_apply,chartD_coordinate,mul_ite,eq_comm]

lemma physicalD_θ_X (i j : Fin 6) : physicalD i (θ (X j))=if j=i then 1 else 0 := by
  rw [θ_X]
  fin_cases i <;> fin_cases j <;>
    simp [Derivation.leibniz,smul_eq_mul,physicalD_coordinate,physicalCoefficients,
      coordinate_ne_zero,div_eq_mul_inv] <;>
    field_simp [coordinate_ne_zero 4,coordinate_ne_zero 5] <;> ring

lemma physicalD_θ (i : Fin 6) (P : Poly) : physicalD i (θ P)=θ (pderiv i P) := by
  rw [derivation_polynomial_ringHom_chain (physicalD i) θ
    (fun c => by rw [θ_C]; exact physicalD_C i c) P]
  simp [physicalD_θ_X,mul_ite]

end SplitTernaryPhysical
end
end


noncomputable section
namespace SplitTernaryPhysical
open MvPolynomial HoldoutConstruction
open scoped BigOperators
local instance : Algebra ℤ M := Ring.toIntAlgebra _

/-- The exact left ternary, with c=5/7. -/
def leftTernary {R : Type*} [CommRing R] (c x a y : R) : R :=
  x^6+c*x^5*a+c*x^2*a^3*y+3*c*x*y^5+a^6+2*c*a^5*y+y^6
/-- The exact right ternary; its asymmetric coefficients differ from the left. -/
def rightTernary {R : Type*} [CommRing R] (c x a y : R) : R :=
  x^6+2*c*x^5*a+2*c*x^3*a*y^2+c*x*y^5+a^6+3*c*a^5*y+y^6

def physicalF : Poly :=
  leftTernary (C (5/7 : ℂ)) (X 0) (X 1) (X 2)+
    rightTernary (C (5/7 : ℂ)) (X 3) (X 4) (X 5)
def physicalA : Poly := X 0^4*X 1^3*X 3^3*X 4^2

def pPolynomial : Base := leftTernary (C (5/7 : ℂ)) (X 0) (X 1) 1
def qPolynomial : Base := rightTernary (C (5/7 : ℂ)) (X 2) (X 3) 1
def sourcePolynomial : Base := X 0^4*X 1^3*X 2^3*X 3^2

def p : BaseField := algebraMap Base BaseField pPolynomial
def q : BaseField := algebraMap Base BaseField qPolynomial
def source : BaseField := algebraMap Base BaseField sourcePolynomial

def coefficient : M := algebraMap Poly M (C (5/7 : ℂ))

lemma baseValue_p : baseValue p=leftTernary coefficient (coordinate 0) (coordinate 1) 1 := by
  simp [p,pPolynomial,leftTernary,baseValue_polynomial,baseRingMap,baseIndex,coefficient,coordinate,map_ofNat]
lemma baseValue_q : baseValue q=rightTernary coefficient (coordinate 2) (coordinate 3) 1 := by
  simp [q,qPolynomial,rightTernary,baseValue_polynomial,baseRingMap,baseIndex,coefficient,coordinate,map_ofNat]
lemma baseValue_source : baseValue source=coordinate 0^4*coordinate 1^3*coordinate 2^3*coordinate 3^2 := by
  simp [source,sourcePolynomial,baseValue_polynomial,baseRingMap,baseIndex,coordinate]

lemma θ_F : θ physicalF=coordinate 5^6*(baseValue p+coordinate 4^6*baseValue q) := by
  rw [baseValue_p,baseValue_q]
  simp only [physicalF,leftTernary,rightTernary,map_add,map_mul,map_pow,map_ofNat,θ_X,θ_C,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val]
  change _=coordinate 5^6*(leftTernary coefficient (coordinate 0) (coordinate 1) 1+
    coordinate 4^6*rightTernary coefficient (coordinate 2) (coordinate 3) 1)
  unfold leftTernary rightTernary coefficient
  ring

lemma θ_A : θ physicalA=coordinate 5^12*coordinate 4^5*baseValue source := by
  rw [baseValue_source]
  simp only [physicalA,map_mul,map_pow,θ_X,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val]
  ring

/-- Push forward chart velocities; the radial coordinate t=X2 is fixed. -/
def physicalVector (w : Fin 4 → M) (wl : M) : Fin 6 → M :=
  ![coordinate 5*w 0,coordinate 5*w 1,0,
    coordinate 5*(coordinate 4*w 2+coordinate 2*wl),
    coordinate 5*(coordinate 4*w 3+coordinate 3*wl),coordinate 5*wl]

lemma physicalVector_directional (w : Fin 4 → M) (wl f : M) :
    (∑ i,physicalVector w wl i*physicalD i f)=
      (∑ i,w i*chartD (baseIndex i) f)+wl*chartD 4 f := by
  simp [physicalVector,physicalD_apply,physicalCoefficients,Fin.sum_univ_succ,baseIndex]
  field_simp [coordinate_ne_zero 4,coordinate_ne_zero 5]
  ring
lemma physicalVector_divergence (w : Fin 4 → M) (wl : M) :
    (∑ i,physicalD i (physicalVector w wl i))=
      (∑ i,chartD (baseIndex i) (w i))+chartD 4 wl+2*wl/coordinate 4 := by
  simp [physicalVector,physicalD_apply,physicalCoefficients,Fin.sum_univ_succ,baseIndex,
    Derivation.leibniz,smul_eq_mul,chartD_coordinate]
  field_simp [coordinate_ne_zero 4,coordinate_ne_zero 5]
  ring

lemma baseIndex_ne_lambda (i : Fin 4) : baseIndex i≠(4 : Fin 6) := by fin_cases i <;> simp [baseIndex]
lemma baseIndex_ne_radial (i : Fin 4) : baseIndex i≠(5 : Fin 6) := by fin_cases i <;> simp [baseIndex]

end SplitTernaryPhysical

namespace SplitTernaryPhysical
open MvPolynomial HoldoutConstruction
open scoped BigOperators
local instance : Algebra ℤ M := Ring.toIntAlgebra _

lemma pPolynomial_ne_zero : pPolynomial ≠ 0 := by
  intro h
  have he := congrArg (MvPolynomial.eval (fun _ : Fin 4 => (0 : ℂ))) h
  norm_num [pPolynomial,leftTernary] at he
lemma qPolynomial_ne_zero : qPolynomial ≠ 0 := by
  intro h
  have he := congrArg (MvPolynomial.eval (fun _ : Fin 4 => (0 : ℂ))) h
  norm_num [qPolynomial,rightTernary] at he
lemma p_ne_zero : p ≠ 0 := by
  simpa only [p,map_zero] using (IsFractionRing.injective Base BaseField).ne pPolynomial_ne_zero
lemma q_ne_zero : q ≠ 0 := by
  simpa only [q,map_zero] using (IsFractionRing.injective Base BaseField).ne qPolynomial_ne_zero

def directionalP (W : Fin 4 → BaseField) : BaseField := ∑ i,W i*baseD i p
def directionalQ (W : Fin 4 → BaseField) : BaseField := ∑ i,W i*baseD i q

def baseVelocity (W : Fin 4 → BaseField) (i : Fin 4) : M :=
  SplitTernaryHigherPole.baseCoefficient (baseValue p) (baseValue q) (coordinate 4)*baseValue (W i)
def lambdaVelocity (W : Fin 4 → BaseField) : M :=
  SplitTernaryHigherPole.vertical (baseValue p) (baseValue q) (coordinate 4)
    (baseValue source) (baseValue (directionalP W)) (baseValue (directionalQ W))
def transportedVector (W : Fin 4 → BaseField) : Fin 6 → M :=
  physicalVector (fun i => coordinate 5^6*baseVelocity W i) (coordinate 5^6*lambdaVelocity W)

lemma chart_strict_identity (W : Fin 4 → BaseField)
    (hw : (∑ i,baseD i (W i))-5*directionalP W/(3*p)-4*directionalQ W/(3*q)=source) :
    coordinate 4^5*baseValue source-
        2*((∑ i,baseVelocity W i*chartD (baseIndex i)
          (SplitTernaryHigherPole.chartEquation (baseValue p) (baseValue q) (coordinate 4)))+
          lambdaVelocity W*chartD 4
            (SplitTernaryHigherPole.chartEquation (baseValue p) (baseValue q) (coordinate 4)))+
        SplitTernaryHigherPole.chartEquation (baseValue p) (baseValue q) (coordinate 4)*
          ((∑ i,chartD (baseIndex i) (baseVelocity W i))+chartD 4 (lambdaVelocity W)+
            2*lambdaVelocity W/coordinate 4)=0 := by
  apply SplitTernaryHigherPole.strict_chart_from_weighted_divergence
    (fun i => chartD (baseIndex i)) (chartD 4) (fun i => baseValue (W i))
    (baseValue p) (baseValue q) (coordinate 4) (baseValue source)
    (baseValue (directionalP W)) (baseValue (directionalQ W))
    ((map_ne_zero _).mpr p_ne_zero) ((map_ne_zero _).mpr q_ne_zero) (coordinate_ne_zero 4)
  · intro i
    simp [chartD_coordinate,Ne.symm (baseIndex_ne_lambda i)]
  · simp only [chartD_baseValue,directionalP,map_sum,map_mul]
  · simp only [chartD_baseValue,directionalQ,map_sum,map_mul]
  · have he := congrArg baseValue hw
    simpa only [map_sub,map_sum,map_mul,map_div₀,map_ofNat,chartD_baseValue] using he
  · exact chartD_lambda_base p
  · exact chartD_lambda_base q
  · simp [chartD_coordinate]
  · exact chartD_lambda_base source
  · exact chartD_lambda_base (directionalP W)
  · exact chartD_lambda_base (directionalQ W)

/-- The exact strict physical identity conditional on a weighted-divergence
primitive for the prescribed source. It does not assert existence of W. -/
theorem transported_strict_identity (W : Fin 4 → BaseField)
    (hw : (∑ i,baseD i (W i))-5*directionalP W/(3*p)-4*directionalQ W/(3*q)=source) :
    θ physicalA-2*(∑ i,transportedVector W i*physicalD i (θ physicalF))+
      θ physicalF*(∑ i,physicalD i (transportedVector W i))=0 := by
  have ht (i : Fin 4) : chartD (baseIndex i) (coordinate 5)=0 := by
    simp [chartD_coordinate,Ne.symm (baseIndex_ne_radial i)]
  have ht4 : chartD 4 (coordinate 5)=0 := by simp [chartD_coordinate]
  have hscaled (i : Fin 4) :
      (coordinate 5^6*baseVelocity W i)*chartD (baseIndex i) (θ physicalF)=
        coordinate 5^12*(baseVelocity W i*chartD (baseIndex i)
          (SplitTernaryHigherPole.chartEquation (baseValue p) (baseValue q) (coordinate 4))) := by
    rw [θ_F]
    change _=coordinate 5^12*(baseVelocity W i*chartD (baseIndex i)
      (baseValue p+coordinate 4^6*baseValue q))
    simp only [Derivation.leibniz,Derivation.leibniz_pow,smul_eq_mul,ht,mul_zero,zero_add]
    ring
  have hscaled4 :
      (coordinate 5^6*lambdaVelocity W)*chartD 4 (θ physicalF)=
        coordinate 5^12*(lambdaVelocity W*chartD 4
          (SplitTernaryHigherPole.chartEquation (baseValue p) (baseValue q) (coordinate 4))) := by
    rw [θ_F]
    change _=coordinate 5^12*(lambdaVelocity W*chartD 4
      (baseValue p+coordinate 4^6*baseValue q))
    simp only [Derivation.leibniz,Derivation.leibniz_pow,smul_eq_mul,ht4,mul_zero,zero_add]
    ring
  have hdiv (i : Fin 4) : chartD (baseIndex i) (coordinate 5^6*baseVelocity W i)=
      coordinate 5^6*chartD (baseIndex i) (baseVelocity W i) := by
    simp [Derivation.leibniz,Derivation.leibniz_pow,smul_eq_mul,ht]
  have hdiv4 : chartD 4 (coordinate 5^6*lambdaVelocity W)=
      coordinate 5^6*chartD 4 (lambdaVelocity W) := by
    simp [Derivation.leibniz,Derivation.leibniz_pow,smul_eq_mul,ht4]
  change θ physicalA-2*(∑ i,physicalVector _ _ i*physicalD i (θ physicalF))+
    θ physicalF*(∑ i,physicalD i (physicalVector _ _ i))=0
  rw [physicalVector_directional,physicalVector_divergence]
  simp_rw [hscaled,hdiv]
  rw [hscaled4,hdiv4,θ_A,θ_F]
  simp only [← Finset.mul_sum]
  have he := chart_strict_identity W hw
  unfold SplitTernaryHigherPole.chartEquation at he ⊢
  linear_combination coordinate 5^12*he

end SplitTernaryPhysical
end

#print axioms SplitTernaryPhysical.θ_injective
#print axioms SplitTernaryPhysical.physicalVector_divergence
#print axioms SplitTernaryPhysical.transported_strict_identity
