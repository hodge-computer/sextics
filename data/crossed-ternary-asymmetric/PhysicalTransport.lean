import Proposal.ProductDivergence
import HodgeComputer.Constructions.HoldoutCover.HomogeneousField
import HodgeComputer.Constructions.HoldoutCover.HypersurfaceDomain
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Basic.Complex.Basic

/- Prepared with OpenAI Codex assistance for contributor 1337isnot1337.
See solution.md for the construction, provenance, and prior-work credit. -/

/- Source component: PhysicalChartEmbedding. -/
section

noncomputable section
namespace CrossedPhysicalChart
open MvPolynomial HoldoutConstruction

abbrev Poly := MvPolynomial (Fin 6) ℂ
abbrev M := FractionRing Poly
local instance : Algebra ℤ M := Ring.toIntAlgebra _

/-- Physical coordinates in the order x,a,r,z,lambda,t. -/
def exponentMap : (Fin 6 →₀ ℕ) →+ (Fin 6 →₀ ℕ) where
  toFun s := Finsupp.single 0 (s 0)+Finsupp.single 1 (s 1)+
    Finsupp.single 2 (s 4)+Finsupp.single 3 (s 5)+Finsupp.single 4 (s 2+s 4+s 5)+
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
  have hs3 : s 3=u 3 := by omega
  ext j
  fin_cases j
  · exact h0
  · exact h1
  · exact hs2
  · exact hs3
  · exact h2
  · exact h3

def monomialMap : Poly →+* Poly := AddMonoidAlgebra.mapDomainRingHom ℂ exponentMap
lemma monomialMap_injective : Function.Injective monomialMap := AddMonoidAlgebra.mapDomain_injective exponentMap_injective
lemma monomialMap_C (c : ℂ) : monomialMap (C c)=C c := by
  simp [monomialMap,MvPolynomial.C,MvPolynomial.monomial,exponentMap]
lemma monomialMap_X (i : Fin 6) : monomialMap (X i)=
    ![X 5*X 0,X 5*X 1,X 5*X 4,X 5,X 5*X 4*X 2,X 5*X 4*X 3] i := by
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
    ![coordinate 5*coordinate 0,coordinate 5*coordinate 1,coordinate 5*coordinate 4,
      coordinate 5,coordinate 5*coordinate 4*coordinate 2,coordinate 5*coordinate 4*coordinate 3] i := by
  rw [θ,RingHom.comp_apply,monomialMap_X]
  fin_cases i <;> simp [coordinate]

def baseIndex : Fin 4 → Fin 6 := ![0,1,2,3]
lemma baseIndex_injective : Function.Injective baseIndex := by
  intro i j h; fin_cases i <;> fin_cases j <;> simp_all [baseIndex]
def baseRingMap : CrossedProductField.Base →+* M :=
  (algebraMap Poly M).comp (MvPolynomial.rename baseIndex).toRingHom
lemma baseRingMap_injective : Function.Injective baseRingMap :=
  (IsFractionRing.injective Poly M).comp (MvPolynomial.rename_injective baseIndex baseIndex_injective)
def baseValue : CrossedProductField.F →+* M := IsFractionRing.lift baseRingMap_injective
lemma baseValue_polynomial (P : CrossedProductField.Base) :
    baseValue (algebraMap CrossedProductField.Base CrossedProductField.F P)=baseRingMap P :=
  IsFractionRing.lift_algebraMap baseRingMap_injective P
lemma baseRingMap_C (c : ℂ) : baseRingMap (C c)=algebraMap Poly M (C c) := by simp [baseRingMap]
lemma baseRingMap_X (i : Fin 4) : baseRingMap (X i)=coordinate (baseIndex i) := by simp [baseRingMap,coordinate]

end CrossedPhysicalChart
end
end

/- Source component: PhysicalChartDerivations. -/
section

noncomputable section
namespace CrossedPhysicalChart
open MvPolynomial HoldoutConstruction
open scoped BigOperators
local instance : Algebra ℤ M := Ring.toIntAlgebra _
local instance : Algebra ℤ CrossedProductField.F := Ring.toIntAlgebra _

lemma chartD_baseValue (i : Fin 4) (f : CrossedProductField.F) :
    chartD (baseIndex i) (baseValue f)=baseValue (CrossedProductField.baseD i f) := by
  apply derivation_intertwines_quotient_fraction (RingHom.id CrossedProductField.Base)
    Function.surjective_id baseValue (CrossedProductField.baseD i) (chartD (baseIndex i))
  · intro c
    simp only [RingHom.id_apply,baseValue_polynomial,CrossedProductField.baseD_polynomial,
      integerPartial_C,map_zero,baseRingMap_C,chartD_C]
  · intro j
    simp only [RingHom.id_apply,baseValue_polynomial,CrossedProductField.baseD_polynomial,
      integerPartial_apply,baseRingMap_X,chartD_coordinate]
    by_cases h : j=i
    · subst j; simp
    · have hne : baseIndex j≠baseIndex i := fun he => h (baseIndex_injective he)
      simp [h,hne]

lemma chartD_baseValue_zero (k : Fin 6) (hk : ∀ i : Fin 4,baseIndex i≠k) (f : CrossedProductField.F) :
    chartD k (baseValue f)=0 := by
  have he := derivation_intertwines_quotient_fraction (RingHom.id CrossedProductField.Base)
    Function.surjective_id baseValue (0 : Derivation ℤ CrossedProductField.F CrossedProductField.F) (chartD k)
    (by intro c; simp only [RingHom.id_apply,baseValue_polynomial,baseRingMap_C,chartD_C,
          FunLike.coe_zero,Pi.zero_apply,map_zero])
    (by intro i; simp only [RingHom.id_apply,baseValue_polynomial,baseRingMap_X,chartD_coordinate,
          ite_eq_right (hk i),FunLike.coe_zero,Pi.zero_apply,map_zero]) f
  simpa only [FunLike.coe_zero,Pi.zero_apply,map_zero] using he
lemma chartD_lambda_base (f : CrossedProductField.F) : chartD 4 (baseValue f)=0 := by
  apply chartD_baseValue_zero
  intro i; fin_cases i <;> simp [baseIndex]
lemma chartD_radial_base (f : CrossedProductField.F) : chartD 5 (baseValue f)=0 := by
  apply chartD_baseValue_zero
  intro i; fin_cases i <;> simp [baseIndex]

def physicalCoefficients (i : Fin 6) : Fin 6 → M :=
  ![![1/coordinate 5,0,0,0,0,0],![0,1/coordinate 5,0,0,0,0],
    ![0,0,-coordinate 2/(coordinate 5*coordinate 4),-coordinate 3/(coordinate 5*coordinate 4),1/coordinate 5,0],
    ![-coordinate 0/coordinate 5,-coordinate 1/coordinate 5,0,0,-coordinate 4/coordinate 5,1],
    ![0,0,1/(coordinate 5*coordinate 4),0,0,0],![0,0,0,1/(coordinate 5*coordinate 4),0,0]] i

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

end CrossedPhysicalChart
end
end

/- Source component: CrossedGlobalDomain. -/
section

/- Exact complex irreducibility of the selected sextic, viewed as a monic
   polynomial in Y0. This concerns the fixed equation, not a deformation. -/
noncomputable section
namespace CrossedGlobalDomain
open Polynomial
abbrev Coeff := MvPolynomial (Fin 5) ℂ

def lower : Polynomial Coeff :=
  C (MvPolynomial.C (5/7 : ℂ)*MvPolynomial.X 0*MvPolynomial.X 1)*X^4+
  C (MvPolynomial.C (5/7 : ℂ)*(MvPolynomial.X 0)^3*MvPolynomial.X 1)*X^2+
  C ((MvPolynomial.X 0)^6+(MvPolynomial.X 1)^6+
    MvPolynomial.C (5/7 : ℂ)*((MvPolynomial.X 0)^5*MvPolynomial.X 1+
      2*MvPolynomial.X 0*(MvPolynomial.X 1)^5)+
    ((MvPolynomial.X 3)^6+(MvPolynomial.X 4)^6+(MvPolynomial.X 2)^6+
      MvPolynomial.C (5/7 : ℂ)*((MvPolynomial.X 3)^5*MvPolynomial.X 4+
        (MvPolynomial.X 3)^3*MvPolynomial.X 4*(MvPolynomial.X 2)^2+
        MvPolynomial.X 3*MvPolynomial.X 4*(MvPolynomial.X 2)^4+
        2*MvPolynomial.X 3*(MvPolynomial.X 4)^5)))
def equation : Polynomial Coeff := X^6+lower
lemma lower_degree : lower.degree < 6 := by
  unfold lower
  compute_degree <;> norm_num
lemma equation_monic : equation.Monic := monic_X_pow_add lower_degree

def specialization : Coeff →+* ℂ[X] :=
  MvPolynomial.eval₂Hom C ![0,0,X-1,0,C Complex.I]

lemma equation_specialization : equation.map specialization =
    (X : (ℂ[X])[X])^6+C ((X-1)^6-1) := by
  have hi : (Complex.I : ℂ)^6 = -1 := by
    calc Complex.I^6 = (Complex.I^2)^3 := by ring
         _ = -1 := by rw [Complex.I_sq]; norm_num
  have hip : (C Complex.I : ℂ[X])^6 = -1 := by
    rw [← map_pow,hi]
    simp
  have hipp : (C (C Complex.I) : (ℂ[X])[X])^6 = -1 := by
    rw [← map_pow,hip]
    simp
  simp [equation,lower,specialization,hipp]
  ring

lemma equation_irreducible : Irreducible equation := by
  apply equation_monic.irreducible_of_irreducible_map specialization
  rw [equation_specialization]
  have he : (X-1)^6-1 = (X^6-6*X^5+15*X^4-20*X^3+15*X^2-6*X : ℂ[X]) := by ring
  rw [he]
  exact HoldoutConstruction.irreducible_power_add_constant
    (X^6-6*X^5+15*X^4-20*X^3+15*X^2-6*X : ℂ[X])
    (by simp) (by norm_num) 6 (by decide)

end CrossedGlobalDomain
end
end

/- Source component: CrossedPhysicalPolynomial. -/
section

noncomputable section
namespace CrossedPhysicalChart
open MvPolynomial Polynomial HoldoutConstruction

def ternary {R : Type*} [CommRing R] (k x a y : R) : R :=
  x^6+a^6+y^6+k*(x^5*a+x^3*a*y^2+x*a*y^4+2*x*a^5)
def physicalF : Poly := ternary (MvPolynomial.C (5/7 : ℂ)) (MvPolynomial.X 0) (MvPolynomial.X 1) (MvPolynomial.X 3)+
  ternary (MvPolynomial.C (5/7 : ℂ)) (MvPolynomial.X 4) (MvPolynomial.X 5) (MvPolynomial.X 2)
def physicalA : Poly := MvPolynomial.X 0^4*MvPolynomial.X 1*MvPolynomial.X 4

def coefficient : M := algebraMap Poly M (MvPolynomial.C (5/7 : ℂ))
lemma baseValue_p : baseValue CrossedProductField.p=ternary coefficient (coordinate 0) (coordinate 1) 1 := by
  change baseValue (algebraMap CrossedProductField.Base CrossedProductField.F
    (MvPolynomial.rename CrossedProductField.firstIndex CrossedFanoElliptic.basePolynomial))=_
  rw [baseValue_polynomial]
  simp [CrossedFanoElliptic.basePolynomial,CrossedProductField.firstIndex,baseRingMap_C,baseRingMap_X,
    baseIndex,ternary,coefficient,map_ofNat]
lemma baseValue_q : baseValue CrossedProductField.q=ternary coefficient (coordinate 2) (coordinate 3) 1 := by
  change baseValue (algebraMap CrossedProductField.Base CrossedProductField.F
    (MvPolynomial.rename CrossedProductField.secondIndex CrossedFanoElliptic.basePolynomial))=_
  rw [baseValue_polynomial]
  simp [CrossedFanoElliptic.basePolynomial,CrossedProductField.secondIndex,baseRingMap_C,baseRingMap_X,
    baseIndex,ternary,coefficient,map_ofNat]
lemma baseValue_source : baseValue CrossedProductField.source=coordinate 0^4*coordinate 1*coordinate 2 := by
  rw [CrossedProductField.source,baseValue_polynomial]
  simp [baseRingMap_X,baseIndex]
lemma θ_F : θ physicalF=coordinate 5^6*(baseValue CrossedProductField.p+
    coordinate 4^6*baseValue CrossedProductField.q) := by
  simp only [physicalF,ternary,map_add,map_mul,map_pow,map_ofNat,θ_X,θ_C,baseValue_p,baseValue_q]
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,
    Matrix.cons_val_four]
  simp [ternary,coefficient]
  ring
lemma θ_A : θ physicalA=coordinate 5^6*coordinate 4*baseValue CrossedProductField.source := by
  simp [physicalA,baseValue_source,θ_X,map_ofNat]
  ring

lemma ternary_homogeneous (k : ℂ) (i j l : Fin 6) :
    (ternary (MvPolynomial.C k) (MvPolynomial.X i) (MvPolynomial.X j) (MvPolynomial.X l)).IsHomogeneous 6 := by
  have h2 : MvPolynomial.C (2 : ℂ)=(2 : Poly) := map_ofNat _ 2
  have hinner : (MvPolynomial.X i^5*MvPolynomial.X j+
      MvPolynomial.X i^3*MvPolynomial.X j*MvPolynomial.X l^2+
      MvPolynomial.X i*MvPolynomial.X j*MvPolynomial.X l^4+
      2*MvPolynomial.X i*MvPolynomial.X j^5 : Poly).IsHomogeneous 6 := by
    refine (((isHomogeneous_X_pow i 5).mul (isHomogeneous_X ℂ j)).add
      (((isHomogeneous_X_pow i 3).mul (isHomogeneous_X ℂ j)).mul (isHomogeneous_X_pow l 2))).add ?_ |>.add ?_
    · exact ((isHomogeneous_X ℂ i).mul (isHomogeneous_X ℂ j)).mul (isHomogeneous_X_pow l 4)
    · rw [← h2]
      exact ((isHomogeneous_C (Fin 6) (2 : ℂ)).mul (isHomogeneous_X ℂ i)).mul (isHomogeneous_X_pow j 5)
  exact (((isHomogeneous_X_pow i 6).add (isHomogeneous_X_pow j 6)).add
    (isHomogeneous_X_pow l 6)).add ((isHomogeneous_C (Fin 6) k).mul hinner)
lemma physicalF_homogeneous : physicalF.IsHomogeneous 6 :=
  (ternary_homogeneous (5/7) 0 1 3).add (ternary_homogeneous (5/7) 4 5 2)
lemma physicalA_homogeneous : physicalA.IsHomogeneous 6 :=
  ((isHomogeneous_X_pow (0 : Fin 6) 4).mul (isHomogeneous_X ℂ 1)).mul (isHomogeneous_X ℂ 4)

/-- Move Y0 to the monic normal position. -/
def normalPermutation : Equiv (Fin 6) (Fin 6) where
  toFun := ![1,2,3,0,4,5]
  invFun := ![3,0,1,2,4,5]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def normalEquiv := (MvPolynomial.renameEquiv ℂ normalPermutation).trans (MvPolynomial.finSuccEquiv ℂ 5)
lemma normal_equation : normalEquiv physicalF=CrossedGlobalDomain.equation := by
  have hv : (Fin.cases (Polynomial.X : Polynomial CrossedGlobalDomain.Coeff)
      (fun j => Polynomial.C (MvPolynomial.X j)))=
      ![Polynomial.X,Polynomial.C (MvPolynomial.X 0),Polynomial.C (MvPolynomial.X 1),
        Polynomial.C (MvPolynomial.X 2),Polynomial.C (MvPolynomial.X 3),Polynomial.C (MvPolynomial.X 4)] := by
    funext i; fin_cases i <;> rfl
  have hr2 : MvPolynomial.rename normalPermutation (2 : Poly)=(2 : Poly) := map_ofNat _ 2
  have h2 : Polynomial.C (2 : CrossedGlobalDomain.Coeff)=(2 : Polynomial CrossedGlobalDomain.Coeff) := map_ofNat _ 2
  simp [normalEquiv,MvPolynomial.renameEquiv_apply,physicalF,ternary,normalPermutation,
    MvPolynomial.finSuccEquiv_apply,hv,CrossedGlobalDomain.equation,CrossedGlobalDomain.lower,h2,hr2,map_ofNat]
  ring
lemma physicalF_irreducible : Irreducible physicalF := by
  apply (MulEquiv.irreducible_iff normalEquiv).mp
  rw [normal_equation]
  exact CrossedGlobalDomain.equation_irreducible

lemma physical_normal_ne_zero : MvPolynomial.pderiv 3 physicalF≠0 := by
  have h2 : MvPolynomial.pderiv (R:=ℂ) (3 : Fin 6) (2 : Poly)=0 := (MvPolynomial.pderiv 3).map_natCast 2
  have he : MvPolynomial.eval ![0,0,0,1,0,0] (MvPolynomial.pderiv 3 physicalF)=(6 : ℂ) := by
    simp [physicalF,ternary,MvPolynomial.pderiv_mul,Derivation.leibniz_pow,smul_eq_mul,h2]
  intro hz
  rw [hz,map_zero] at he
  norm_num at he
lemma physical_normal_legal : ¬physicalF∣MvPolynomial.pderiv 3 physicalF := by
  intro hd
  have hdeg := MvPolynomial.totalDegree_le_of_dvd_of_isDomain hd physical_normal_ne_zero
  have hFdeg := physicalF_homogeneous.totalDegree physicalF_irreducible.ne_zero
  have hgdeg := (pderiv_isHomogeneous physicalF_homogeneous 3).totalDegree_le
  omega

end CrossedPhysicalChart
end
end

/- Source component: PhysicalVectorCalculus. -/
section

noncomputable section
namespace CrossedPhysicalChart
open MvPolynomial HoldoutConstruction
open scoped BigOperators
local instance : Algebra ℤ M := Ring.toIntAlgebra _

def physicalVector (w : Fin 4 → M) (wl : M) : Fin 6 → M :=
  ![coordinate 5*w 0,coordinate 5*w 1,coordinate 5*wl,0,
    coordinate 5*(coordinate 4*w 2+coordinate 2*wl),
    coordinate 5*(coordinate 4*w 3+coordinate 3*wl)]

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

lemma chartD_base_F (i : Fin 4) : chartD (baseIndex i) (θ physicalF)=coordinate 5^6*
    (baseValue (CrossedProductField.baseD i CrossedProductField.p)+
      coordinate 4^6*baseValue (CrossedProductField.baseD i CrossedProductField.q)) := by
  rw [θ_F]
  simp [Derivation.leibniz,Derivation.leibniz_pow,smul_eq_mul,nsmul_eq_mul,
    chartD_coordinate,Ne.symm (baseIndex_ne_lambda i),Ne.symm (baseIndex_ne_radial i),chartD_baseValue]
lemma chartD_lambda_F : chartD 4 (θ physicalF)=6*coordinate 5^6*coordinate 4^5*baseValue CrossedProductField.q := by
  rw [θ_F]
  simp [Derivation.leibniz,Derivation.leibniz_pow,smul_eq_mul,nsmul_eq_mul,
    chartD_coordinate,chartD_lambda_base]
  ring

end CrossedPhysicalChart
end
end

/- Source component: PhysicalWeightedTransport. -/
section

noncomputable section
namespace CrossedPhysicalChart
open MvPolynomial HoldoutConstruction
open scoped BigOperators
local instance : Algebra ℤ M := Ring.toIntAlgebra _
abbrev Field4 := CrossedProductField.F

def directionalP (W : Fin 4 → Field4) : Field4 := ∑ i,W i*CrossedProductField.baseD i CrossedProductField.p
def directionalQ (W : Fin 4 → Field4) : Field4 := ∑ i,W i*CrossedProductField.baseD i CrossedProductField.q

def baseVector {R : Type*} [Field R] (h : Field4 →+* R) (l : R) (W : Fin 4 → Field4) (i : Fin 4) : R :=
  -l/(3*h CrossedProductField.p)*h (W i)
def lambdaVector {R : Type*} [Field R] (h : Field4 →+* R) (l : R) (W : Fin 4 → Field4) : R :=
  (3*h CrossedProductField.p*h CrossedProductField.source+h (directionalP W)+l^6*h (directionalQ W))/
    (18*h CrossedProductField.p*l^4*h CrossedProductField.q)
def divergenceQuotient {R : Type*} [Field R] (h : Field4 →+* R) (l t : R) (W : Fin 4 → Field4) : R :=
  -(3*h CrossedProductField.p*h CrossedProductField.source+h (directionalP W))/
    (9*(h CrossedProductField.p)^2*h CrossedProductField.q*l^5*t^6)

def transportedVector (W : Fin 4 → Field4) : Fin 6 → M :=
  physicalVector (baseVector baseValue (coordinate 4) W) (lambdaVector baseValue (coordinate 4) W)

lemma baseValue_p_ne_zero : baseValue CrossedProductField.p≠0 := (_root_.map_ne_zero _).mpr CrossedProductField.p_ne_zero
lemma baseValue_q_ne_zero : baseValue CrossedProductField.q≠0 := (_root_.map_ne_zero _).mpr CrossedProductField.q_ne_zero

lemma transported_normal (W : Fin 4 → Field4) :
    (∑ i,transportedVector W i*θ (pderiv i physicalF))=θ physicalA := by
  simp only [← physicalD_θ]
  rw [transportedVector,physicalVector_directional]
  simp only [chartD_base_F,chartD_lambda_F,baseVector]
  have hs : (∑ i,(-coordinate 4/(3*baseValue CrossedProductField.p)*baseValue (W i))*
      (coordinate 5^6*(baseValue (CrossedProductField.baseD i CrossedProductField.p)+
        coordinate 4^6*baseValue (CrossedProductField.baseD i CrossedProductField.q))))=
      coordinate 5^6*(-coordinate 4/(3*baseValue CrossedProductField.p))*
        (baseValue (directionalP W)+coordinate 4^6*baseValue (directionalQ W)) := by
    simp only [directionalP,directionalQ,map_sum,map_mul,map_add,Fin.sum_univ_four]
    ring
  rw [hs,θ_A]
  have he := CrossedEllipticJet.affine_first_equation (baseValue CrossedProductField.p)
    (baseValue CrossedProductField.q) (coordinate 4) (baseValue CrossedProductField.source)
    (baseValue (directionalP W)) (baseValue (directionalQ W)) baseValue_p_ne_zero baseValue_q_ne_zero (coordinate_ne_zero 4)
  dsimp [lambdaVector] at *
  linear_combination coordinate 5^6*he

lemma baseVector_derivative (W : Fin 4 → Field4) (i : Fin 4) :
    chartD (baseIndex i) (baseVector baseValue (coordinate 4) W i)=
      -coordinate 4/(3*baseValue CrossedProductField.p)*baseValue (CrossedProductField.baseD i (W i))+
      coordinate 4/(3*(baseValue CrossedProductField.p)^2)*
        baseValue (W i)*baseValue (CrossedProductField.baseD i CrossedProductField.p) := by
  have h3 : chartD (baseIndex i) (3 : M)=0 := (chartD (baseIndex i)).map_natCast 3
  simp only [baseVector,Derivation.leibniz,Derivation.leibniz_div,map_neg,h3,
    chartD_baseValue,chartD_coordinate,ite_eq_right (Ne.symm (baseIndex_ne_lambda i)),smul_eq_mul]
  field_simp [baseValue_p_ne_zero]
  ring

lemma lambdaVector_divergence (W : Fin 4 → Field4) :
    chartD 4 (lambdaVector baseValue (coordinate 4) W)+2*lambdaVector baseValue (coordinate 4) W/coordinate 4=
      -(3*baseValue CrossedProductField.p*baseValue CrossedProductField.source+baseValue (directionalP W))/
        (9*baseValue CrossedProductField.p*baseValue CrossedProductField.q*coordinate 4^5)+
      2*coordinate 4*baseValue (directionalQ W)/(9*baseValue CrossedProductField.p*baseValue CrossedProductField.q) := by
  have h3 : chartD 4 (3 : M)=0 := (chartD 4).map_natCast 3
  have h18 : chartD 4 (18 : M)=0 := (chartD 4).map_natCast 18
  simp only [lambdaVector,Derivation.leibniz,Derivation.leibniz_div,Derivation.leibniz_pow,
    map_add,h3,h18,chartD_lambda_base,chartD_coordinate,ite_eq_left rfl,smul_eq_mul,nsmul_eq_mul]
  norm_num only
  simp only [ite_true,zero_mul,mul_zero,add_zero,zero_add,sub_zero,zero_sub]
  field_simp [baseValue_p_ne_zero,baseValue_q_ne_zero,coordinate_ne_zero 4]
  ring

lemma weighted_divergence_value (W : Fin 4 → Field4)
    (hW : (∑ i,(CrossedProductField.baseD i (W i)+W i*CrossedProductField.connection i))=CrossedProductField.source) :
    (∑ i,baseValue (CrossedProductField.baseD i (W i)))=baseValue CrossedProductField.source+
      4*baseValue (directionalP W)/(3*baseValue CrossedProductField.p)+
      2*baseValue (directionalQ W)/(3*baseValue CrossedProductField.q) := by
  have he := congrArg baseValue hW
  simp only [map_sum,map_add,map_mul,CrossedProductField.connection,map_sub,map_neg,map_div₀,map_ofNat] at he
  simp only [directionalP,directionalQ,map_sum,map_mul,map_add,Fin.sum_univ_four] at he ⊢
  linear_combination he

lemma transported_divergence (W : Fin 4 → Field4)
    (hW : (∑ i,(CrossedProductField.baseD i (W i)+W i*CrossedProductField.connection i))=CrossedProductField.source) :
    (∑ i,physicalD i (transportedVector W i))=θ physicalF*divergenceQuotient baseValue (coordinate 4) (coordinate 5) W := by
  rw [transportedVector,physicalVector_divergence]
  have hsum : (∑ i,chartD (baseIndex i) (baseVector baseValue (coordinate 4) W i))=
      -coordinate 4/(3*baseValue CrossedProductField.p)*(∑ i,baseValue (CrossedProductField.baseD i (W i)))+
      coordinate 4*baseValue (directionalP W)/(3*(baseValue CrossedProductField.p)^2) := by
    simp_rw [baseVector_derivative]
    simp only [directionalP,map_sum,map_mul,map_add,Fin.sum_univ_four]
    ring
  rw [hsum,add_assoc,lambdaVector_divergence,weighted_divergence_value W hW,θ_F]
  have he := CrossedEllipticJet.affine_divergence_quotient (baseValue CrossedProductField.p)
    (baseValue CrossedProductField.q) (coordinate 4) (baseValue CrossedProductField.source)
    (baseValue (directionalP W)) (baseValue (directionalQ W)) baseValue_p_ne_zero baseValue_q_ne_zero (coordinate_ne_zero 4)
  dsimp [divergenceQuotient]
  field_simp [baseValue_p_ne_zero,baseValue_q_ne_zero,coordinate_ne_zero 4,coordinate_ne_zero 5] at he ⊢
  linear_combination he

end CrossedPhysicalChart
end
end
