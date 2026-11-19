import Proposal.CompanionScalar
import Proposal.CompanionResidue
import Proposal.RationalAmbient
import HodgeComputer.Constructions.EllipticCompanions.AffineCompanion
import HodgeComputer.Constructions.EllipticCompanions.Residues

/-!
The first protected ternary, using T as normal coordinate.  The cone has
independent weights (1,1,1,2), and its affine chart has independent weights
(1,1,2).  The normal 21*T² has weight four, which makes radial residue
extraction compatible with the affine residue divergence.
Prepared with OpenAI Codex assistance for contributor fqlx.
-/
noncomputable section
open scoped BigOperators

namespace SplitThetaRadial
open CrossedElliptic HoldoutConstruction CrossedRationalResidue
variable {K : Type*} [Field K] [CharZero K]
local instance : Algebra ℤ (RatFunc K) := Ring.toIntAlgebra _

def coneDerivations (D : Fin 3 → Derivation ℤ K K) (c : Fin 3 → K) :
    Fin 4 → Derivation ℤ (RatFunc K) (RatFunc K) :=
  ![(RatFunc.X : RatFunc K)⁻¹ • baseCoefficient (D 0),
    (RatFunc.X : RatFunc K)⁻¹ • baseCoefficient (D 1),
    (baseTime (K:=K))-(RatFunc.C (c 0)/RatFunc.X) • baseCoefficient (D 0)-
      (RatFunc.C (c 1)/RatFunc.X) • baseCoefficient (D 1)-
      (2*RatFunc.C (c 2)/RatFunc.X) • baseCoefficient (D 2),
    ((RatFunc.X : RatFunc K)^2)⁻¹ • baseCoefficient (D 2)]

def projectedField (c : Fin 3 → K) (w : Fin 4 → RatFunc K) : Fin 3 → RatFunc K :=
  ![w 0/RatFunc.X-RatFunc.C (c 0)*w 2/RatFunc.X,
    w 1/RatFunc.X-RatFunc.C (c 1)*w 2/RatFunc.X,
    w 3/RatFunc.X^2-2*RatFunc.C (c 2)*w 2/RatFunc.X]

def independentCoordinates (c : Fin 3 → K) : Fin 4 → RatFunc K :=
  ![RatFunc.X*RatFunc.C (c 0),RatFunc.X*RatFunc.C (c 1),RatFunc.X,
    RatFunc.X^2*RatFunc.C (c 2)]

lemma coneDerivations_coordinate (D : Fin 3 → Derivation ℤ K K) (c : Fin 3 → K)
    (hc : ∀ i j,D i (c j)=if j=i then 1 else 0) (i j : Fin 4) :
    coneDerivations D c i (independentCoordinates c j)=if j=i then 1 else 0 := by
  have hX : (RatFunc.X : RatFunc K)≠0 := CrossedRationalResidue.X_ne_zero
  have h2 (i : Fin 3) : baseCoefficient (D i) (2 : RatFunc K)=0 :=
    (baseCoefficient (D i)).map_natCast 2
  fin_cases i <;> fin_cases j <;>
    simp [coneDerivations,independentCoordinates,sub_apply,smul_apply,
      Derivation.leibniz,Derivation.leibniz_pow,smul_eq_mul,
      baseTime_X,baseTime_C,baseCoefficient_X,baseCoefficient_C,hc,h2] <;>
    field_simp <;> ring

lemma coneDerivations_constant (D : Fin 3 → Derivation ℤ K K) (c : Fin 3 → K)
    (a : K) (ha : ∀ i,D i a=0) (i : Fin 4) :
    coneDerivations D c i (RatFunc.C a)=0 := by
  fin_cases i <;> simp [coneDerivations,sub_apply,smul_apply,
    baseTime_C,baseCoefficient_C,ha]

lemma radial_divergence_identity (D : Fin 3 → Derivation ℤ K K) (c : Fin 3 → K)
    (hc : ∀ i,D i (c i)=1) (g : K) (hg : g≠0) (w : Fin 4 → RatFunc K) :
    residueDivergence (coneDerivations D c) (RatFunc.X^4*RatFunc.C g) w=
      baseTime (w 2)+residueDivergence (fun i => baseCoefficient (D i))
        (RatFunc.C g) (projectedField c w) := by
  have hX : (RatFunc.X : RatFunc K)≠0 := CrossedRationalResidue.X_ne_zero
  have hg' : (RatFunc.C g : RatFunc K)≠0 := (RatFunc.C_injective.ne hg).trans_eq (map_zero RatFunc.C)
  have h2 (i : Fin 3) : baseCoefficient (D i) (2 : RatFunc K)=0 :=
    (baseCoefficient (D i)).map_natCast 2
  simp [residueDivergence,fieldDivergence,coneDerivations,projectedField,
    Fin.sum_univ_succ,sub_apply,smul_apply,Derivation.leibniz,
    Derivation.leibniz_div,Derivation.leibniz_pow,Derivation.leibniz_inv,
    smul_eq_mul,Algebra.smul_def,Algebra.algebraMap_self,RingHom.id_apply,
    baseTime_X,baseTime_C,baseCoefficient_X,baseCoefficient_C,hc,h2]
  field_simp
  ring

theorem residue_solution_descends_radial (D : Fin 3 → Derivation ℤ K K)
    (c : Fin 3 → K) (hc : ∀ i,D i (c i)=1) (g : K) (hg : g≠0)
    (s : K) (w : Fin 4 → RatFunc K)
    (hw : residueDivergence (coneDerivations D c) (RatFunc.X^4*RatFunc.C g) w=
      RatFunc.C s/RatFunc.X) :
    ∃ v : Fin 3 → K,residueDivergence D g v=s := by
  refine ⟨fun i => residue (K:=K) 0 (projectedField c w i),?_⟩
  rw [radial_divergence_identity D c hc g hg w] at hw
  have hr := congrArg (residue (K:=K) 0) hw
  rw [map_add,residue_time,CrossedRadialResidue.residue_weighted_divergence D g hg,zero_add] at hr
  have hs : residue (K:=K) 0 (RatFunc.C s/RatFunc.X)=s := by
    simpa only [rationalConstantTerm_apply] using rationalConstantTerm_C s
  exact hr.trans hs
end SplitThetaRadial

namespace SplitFCompanion
open Polynomial HoldoutConstruction
abbrev P2 := MvPolynomial (Fin 2) ℂ
abbrev Poly := MvPolynomial (Fin 4) ℂ
abbrev Coeff := MvPolynomial (Fin 3) ℂ

def p : P2 := MvPolynomial.X 0^6+MvPolynomial.X 1^6+1+
  MvPolynomial.C (5/7 : ℂ)*(MvPolynomial.X 0^5*MvPolynomial.X 1+
    MvPolynomial.X 0^2*MvPolynomial.X 1^3+3*MvPolynomial.X 0+2*MvPolynomial.X 1^5)
def h : P2 := MvPolynomial.X 0^4*MvPolynomial.X 1^3
lemma p_zero : EllipticCompanion.zeroEvaluation p=1 := by
  simp [p,EllipticCompanion.zeroEvaluation]
lemma equation_irreducible : Irreducible (EllipticCompanion.equation p) :=
  EllipticCompanion.equation_irreducible p p_zero
abbrev equation := EllipticCompanion.equation p
abbrev CoordinateRing := EllipticCompanion.CoordinateRing p
instance : IsDomain CoordinateRing := AdjoinRoot.isDomain_of_prime equation_irreducible.prime
abbrev AffineField := FractionRing CoordinateRing
instance : CharZero AffineField :=
  charZero_of_injective_ringHom (f:=algebraMap ℂ AffineField) (algebraMap ℂ AffineField).injective
local instance : Algebra ℤ AffineField := Ring.toIntAlgebra _

def coefficientEmbedding : Coeff →+* AffineField :=
  (algebraMap CoordinateRing AffineField).comp (AdjoinRoot.of equation)
lemma coefficientEmbedding_injective : Function.Injective coefficientEmbedding :=
  (IsFractionRing.injective CoordinateRing AffineField).comp
    (AdjoinRoot.of.injective_of_degree_ne_zero
      (ne_of_gt ((EllipticCompanion.equation_monic p).degree_pos_of_not_isUnit equation_irreducible.not_isUnit)))
@[simp] lemma coefficientEmbedding_C (c : ℂ) : coefficientEmbedding (MvPolynomial.C c)=algebraMap ℂ AffineField c := rfl

/-- Order x,a,S on the affine base; the coefficient ring order is S,x,a. -/
def coordinate (i : Fin 3) : AffineField :=
  coefficientEmbedding (MvPolynomial.X (![1,2,0] i))
def normal : AffineField := algebraMap CoordinateRing AffineField (AdjoinRoot.root equation)
abbrev projection := CrossedMonicHypersurface.projection equation
abbrev evaluation := CrossedMonicHypersurface.residueMap equation
abbrev originalTangent := CrossedMonicHypersurface.tangent equation
  (EllipticCompanion.equation_monic p) equation_irreducible
/-- Affine tangent order x,a,S, matching the radial chart. -/
def tangent (i : Fin 3) : Derivation ℤ AffineField AffineField := originalTangent (![1,2,0] i)
lemma tangent_coordinate (i j : Fin 3) : tangent i (coordinate j)=if j=i then 1 else 0 := by
  have hp (i : Fin 3) : evaluation (MvPolynomial.X ((![1,2,0] i : Fin 3).succ))=coordinate i := by
    rw [CrossedMonicHypersurface.residueMap_X_succ]; rfl
  rw [← hp j]
  rw [tangent,CrossedMonicHypersurface.tangent_parameter]
  fin_cases i <;> fin_cases j <;> rfl
@[simp] lemma tangent_base (i : Fin 3) (c : ℂ) : tangent i (algebraMap ℂ AffineField c)=0 :=
  CrossedMonicHypersurface.tangent_constant equation
    (EllipticCompanion.equation_monic p) equation_irreducible _ c

def base : Poly := (MvPolynomial.finSuccEquiv ℂ 3).symm (C (EllipticCompanion.base p))
def clearedAffineEquation : Poly := 7*(MvPolynomial.X 0^3+MvPolynomial.X 1^3+base)
def numerator : Poly := -7*(MvPolynomial.X 2^4*MvPolynomial.X 3^3)*MvPolynomial.X 1
def denominator : Poly := 6*MvPolynomial.X 0^2
lemma base_univariate : MvPolynomial.finSuccEquiv ℂ 3 base=C (EllipticCompanion.base p) :=
  (MvPolynomial.finSuccEquiv ℂ 3).apply_symm_apply _
lemma base_partial_zero : integerPartial 0 base=0 := by
  apply (MvPolynomial.finSuccEquiv ℂ 3).injective
  rw [← CrossedMonicHypersurface.derivative_finSuccEquiv,base_univariate,Polynomial.derivative_C,map_zero]

lemma equation_univariate : MvPolynomial.finSuccEquiv ℂ 3 clearedAffineEquation=7*equation := by
  have hv : (Fin.cases (Polynomial.X : Polynomial Coeff) (fun j => C (MvPolynomial.X j)))=
      ![X,C (MvPolynomial.X 0),C (MvPolynomial.X 1),C (MvPolynomial.X 2)] := by
    funext j; fin_cases j <;> rfl
  unfold clearedAffineEquation
  rw [map_mul,map_ofNat,map_add,map_add,map_pow,MvPolynomial.finSuccEquiv_X_zero,
    map_pow,show (MvPolynomial.finSuccEquiv ℂ 3) (MvPolynomial.X 1)=C (MvPolynomial.X 0) from MvPolynomial.finSuccEquiv_X_succ (j:=0),base_univariate]
  simp only [EllipticCompanion.equation,Polynomial.C_add,Polynomial.C_pow]
  ring
lemma normal_polynomial : integerPartial 0 clearedAffineEquation=21*MvPolynomial.X 0^2 := by
  have h7 : integerPartial 0 (7 : Poly)=0 := (integerPartial 0).map_natCast 7
  unfold clearedAffineEquation
  simp only [Derivation.leibniz,Derivation.leibniz_pow,h7,map_add,
    integerPartial_X_self,integerPartial_X_of_ne 0 1 (by decide),base_partial_zero,
    smul_eq_mul,nsmul_eq_mul]
  norm_num
  ring
lemma normal_evaluation : evaluation (integerPartial 0 clearedAffineEquation)=21*normal^2 := by
  rw [normal_polynomial,map_mul,map_ofNat,map_pow,CrossedMonicHypersurface.residueMap_X_zero]
  rfl
lemma clearNormal_ne_zero : 21*normal^2≠0 := by
  have hn := CrossedMonicHypersurface.normal_ne_zero equation
    (EllipticCompanion.equation_monic p) equation_irreducible
  have he : integerPartial 0 (CrossedMonicHypersurface.equation equation)=3*MvPolynomial.X 0^2 := by
    apply (MvPolynomial.finSuccEquiv ℂ 3).injective
    rw [← CrossedMonicHypersurface.derivative_finSuccEquiv]
    rw [CrossedMonicHypersurface.equation,AlgEquiv.apply_symm_apply]
    simp only [EllipticCompanion.equation,Polynomial.derivative_add,
      Polynomial.derivative_X_pow,Polynomial.derivative_C]
    norm_num
    simp [MvPolynomial.finSuccEquiv_apply,Polynomial.C_ofNat]
  rw [he,map_mul,map_ofNat,map_pow,CrossedMonicHypersurface.residueMap_X_zero] at hn
  intro hz
  apply hn
  change 3*normal^2=0
  linear_combination hz/7
end SplitFCompanion

#print axioms SplitThetaRadial.residue_solution_descends_radial
#print axioms SplitFCompanion.clearNormal_ne_zero

namespace SplitFCompanion
open Polynomial HoldoutConstruction
abbrev ConeCoeff := MvPolynomial (Fin 4) ℂ
abbrev ConePoly := MvPolynomial (Fin 5) ℂ

def homogeneousBase : ConeCoeff :=
  MvPolynomial.X 0^6+MvPolynomial.X 1^6+MvPolynomial.X 2^6+
    MvPolynomial.C (5/7 : ℂ)*(MvPolynomial.X 0^5*MvPolynomial.X 1+
      MvPolynomial.X 0^2*MvPolynomial.X 1^3*MvPolynomial.X 2+
      3*MvPolynomial.X 0*MvPolynomial.X 2^5+2*MvPolynomial.X 1^5*MvPolynomial.X 2)
def coneEquation : Polynomial ConeCoeff := X^3+C (MvPolynomial.X 3^3+homogeneousBase)
lemma coneEquation_monic : coneEquation.Monic := monic_X_pow_add_C _ (by decide)

def coefficientSpecialization : ConeCoeff →+* Coeff :=
  MvPolynomial.eval₂Hom MvPolynomial.C ![MvPolynomial.X 1,MvPolynomial.X 2,1,MvPolynomial.X 0]
lemma coefficient_base_expanded : EllipticCompanion.base p=
    MvPolynomial.X 1^6+MvPolynomial.X 2^6+1+
      MvPolynomial.C (5/7 : ℂ)*(MvPolynomial.X 1^5*MvPolynomial.X 2+
        MvPolynomial.X 1^2*MvPolynomial.X 2^3+3*MvPolynomial.X 1+2*MvPolynomial.X 2^5) := by
  apply (MvPolynomial.finSuccEquiv ℂ 2).injective
  rw [EllipticCompanion.base_univariate]
  have hv : (Fin.cases (Polynomial.X : Polynomial P2) (fun j => C (MvPolynomial.X j)))=
      ![X,C (MvPolynomial.X 0),C (MvPolynomial.X 1)] := by
    funext i; fin_cases i <;> rfl
  simp [p,MvPolynomial.finSuccEquiv_apply,hv,Polynomial.C_ofNat]
lemma coefficientSpecialization_equation : coneEquation.map coefficientSpecialization=equation := by
  simp only [coneEquation,Polynomial.map_add,Polynomial.map_pow,Polynomial.map_X,Polynomial.map_C,
    EllipticCompanion.equation,coefficient_base_expanded]
  have h2 : coefficientSpecialization (2 : ConeCoeff)=2 := map_natCast _ 2
  have h3 : coefficientSpecialization (3 : ConeCoeff)=3 := map_natCast _ 3
  simp only [homogeneousBase,map_add,map_mul,map_pow,map_one,h2,h3]
  simp [coefficientSpecialization]
lemma coneEquation_irreducible : Irreducible coneEquation := by
  apply coneEquation_monic.irreducible_of_irreducible_map coefficientSpecialization
  rw [coefficientSpecialization_equation]
  exact equation_irreducible

abbrev RadialField := RatFunc AffineField
local instance : Algebra ℤ RadialField := Ring.toIntAlgebra _

def radialExponent : (Fin 4 →₀ ℕ) →+ (Fin 4 →₀ ℕ) where
  toFun s := s+Finsupp.single 2 (s 0+s 1+2*s 3)
  map_zero' := by ext j; simp
  map_add' s t := by
    ext j
    simp only [Finsupp.add_apply,Finsupp.single_apply]
    split_ifs <;> omega
lemma radialExponent_injective : Function.Injective radialExponent := by
  intro s t h
  have h0 := congrArg (fun v : Fin 4 →₀ ℕ => v 0) h
  have h1 := congrArg (fun v : Fin 4 →₀ ℕ => v 1) h
  have h2 := congrArg (fun v : Fin 4 →₀ ℕ => v 2) h
  have h3 := congrArg (fun v : Fin 4 →₀ ℕ => v 3) h
  simp [radialExponent] at h0 h1 h2 h3
  have hs2 : s 2=t 2 := by omega
  ext j
  fin_cases j
  · exact h0
  · exact h1
  · exact hs2
  · exact h3

def radialMonomialMap : ConeCoeff →+* ConeCoeff :=
  AddMonoidAlgebra.mapDomainRingHom ℂ radialExponent
lemma radialMonomialMap_injective : Function.Injective radialMonomialMap :=
  AddMonoidAlgebra.mapDomain_injective radialExponent_injective
lemma radialMonomialMap_C (c : ℂ) : radialMonomialMap (MvPolynomial.C c)=MvPolynomial.C c := by
  simp [radialMonomialMap,MvPolynomial.C,MvPolynomial.monomial,radialExponent]
lemma radialMonomialMap_X (i : Fin 4) : radialMonomialMap (MvPolynomial.X i)=
    ![MvPolynomial.X 0*MvPolynomial.X 2,MvPolynomial.X 1*MvPolynomial.X 2,
      MvPolynomial.X 2,MvPolynomial.X 3*MvPolynomial.X 2^2] i := by
  change AddMonoidAlgebra.mapDomain radialExponent
    (AddMonoidAlgebra.single (Finsupp.single i 1) (1 : ℂ))=_
  rw [AddMonoidAlgebra.mapDomain_single]
  fin_cases i <;>
    simp only [Matrix.cons_val_zero',Matrix.cons_val_succ',MvPolynomial.X,
      MvPolynomial.monomial,AddMonoidAlgebra.lsingle_apply,AddMonoidAlgebra.single_mul_single,
      AddMonoidAlgebra.single_pow,one_mul,one_pow]
  all_goals congr 1
  all_goals ext j
  all_goals fin_cases j <;> simp [radialExponent]

/-- Reorder the coefficient variables x,a,y,S to y,S,x,a. -/
def radialPermutation : Fin 4 ≃ Fin 4 where
  toFun i := ![2,3,0,1] i
  invFun i := ![2,3,0,1] i
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def rawPolynomialMap : ConeCoeff →+* Polynomial AffineField :=
  (Polynomial.mapRingHom coefficientEmbedding).comp
    ((MvPolynomial.finSuccEquiv ℂ 3).toRingHom.comp (MvPolynomial.rename radialPermutation).toRingHom)
lemma rawPolynomialMap_injective : Function.Injective rawPolynomialMap :=
  (Polynomial.map_injective coefficientEmbedding coefficientEmbedding_injective).comp
    ((MvPolynomial.finSuccEquiv ℂ 3).injective.comp
      (MvPolynomial.rename_injective (R:=ℂ) radialPermutation radialPermutation.injective))
lemma rawPolynomialMap_C (c : ℂ) : rawPolynomialMap (MvPolynomial.C c)=C (algebraMap ℂ AffineField c) := by
  simp [rawPolynomialMap,MvPolynomial.rename_C,MvPolynomial.finSuccEquiv_apply]
lemma rawPolynomialMap_X (i : Fin 4) : rawPolynomialMap (MvPolynomial.X i)=
    ![C (coordinate 0),C (coordinate 1),X,C (coordinate 2)] i := by
  have hv : (Fin.cases (Polynomial.X : Polynomial Coeff) (fun j => C (MvPolynomial.X j)))=
      ![X,C (MvPolynomial.X 0),C (MvPolynomial.X 1),C (MvPolynomial.X 2)] := by
    funext j; fin_cases j <;> rfl
  fin_cases i <;> simp [rawPolynomialMap,coordinate,MvPolynomial.finSuccEquiv_apply,hv,radialPermutation]

def coneCoefficientMap : ConeCoeff →+* RadialField :=
  (algebraMap (Polynomial AffineField) RadialField).comp (rawPolynomialMap.comp radialMonomialMap)
lemma coneCoefficientMap_injective : Function.Injective coneCoefficientMap := by
  rw [coneCoefficientMap,RingHom.coe_comp,RingHom.coe_comp]
  exact (IsFractionRing.injective (Polynomial AffineField) RadialField).comp
    (rawPolynomialMap_injective.comp radialMonomialMap_injective)
lemma coneCoefficientMap_C (c : ℂ) : coneCoefficientMap (MvPolynomial.C c)=algebraMap ℂ RadialField c := by
  rw [coneCoefficientMap,RingHom.comp_apply,RingHom.comp_apply,radialMonomialMap_C,rawPolynomialMap_C]
  rfl
lemma coneCoefficientMap_X (i : Fin 4) : coneCoefficientMap (MvPolynomial.X i)=
    SplitThetaRadial.independentCoordinates coordinate i := by
  rw [coneCoefficientMap,RingHom.comp_apply,RingHom.comp_apply,radialMonomialMap_X]
  fin_cases i <;> simp [rawPolynomialMap_X,SplitThetaRadial.independentCoordinates,
    RatFunc.algebraMap_X,RatFunc.algebraMap_C]
  all_goals ring

lemma affine_root : normal^3+(coordinate 2)^3+
    (coordinate 0)^6+(coordinate 1)^6+1+(5/7 : AffineField)*
      ((coordinate 0)^5*coordinate 1+(coordinate 0)^2*(coordinate 1)^3+
        3*coordinate 0+2*(coordinate 1)^5)=0 := by
  have hh := congrArg (algebraMap CoordinateRing AffineField) (AdjoinRoot.eval₂_root equation)
  rw [map_zero,Polynomial.hom_eval₂] at hh
  change equation.eval₂ coefficientEmbedding normal=0 at hh
  simp only [EllipticCompanion.equation,Polynomial.eval₂_add,Polynomial.eval₂_pow,
    Polynomial.eval₂_X,Polynomial.eval₂_C,Polynomial.eval₂_mul,Polynomial.eval₂_one,Polynomial.eval₂_ofNat,coefficient_base_expanded,map_add,map_mul,map_pow,
    map_one,map_ofNat,coefficientEmbedding_C] at hh
  change normal^3+((coordinate 2)^3+_)=0 at hh
  have h5 : algebraMap ℂ AffineField (5/7 : ℂ)=(5/7 : AffineField) := by
    rw [map_div₀]; congr 1 <;> exact map_natCast _ _
  rw [h5] at hh
  change normal^3+((coordinate 2)^3+((coordinate 0)^6+(coordinate 1)^6+1+
    (5/7 : AffineField)*((coordinate 0)^5*coordinate 1+(coordinate 0)^2*(coordinate 1)^3+
      3*coordinate 0+2*(coordinate 1)^5)))=0 at hh
  linear_combination hh

lemma cone_root : coneEquation.eval₂ coneCoefficientMap (RatFunc.X^2*RatFunc.C normal)=0 := by
  have hh := congrArg (RatFunc.C : AffineField →+* RadialField) affine_root
  simp only [map_zero,map_add,map_mul,map_pow,map_one,map_div₀,map_ofNat] at hh
  simp only [coneEquation,homogeneousBase,Polynomial.eval₂_add,Polynomial.eval₂_pow,
    Polynomial.eval₂_X,Polynomial.eval₂_C,Polynomial.eval₂_mul,Polynomial.eval₂_one,Polynomial.eval₂_ofNat,map_add,map_mul,map_pow,map_ofNat,
    coneCoefficientMap_C,coneCoefficientMap_X]
  have h5 : algebraMap ℂ RadialField (5/7 : ℂ)=(5/7 : RadialField) := by
    rw [map_div₀]; congr 1 <;> exact map_natCast _ _
  rw [h5]
  change (RatFunc.X^2*RatFunc.C normal)^3+((RatFunc.X^2*RatFunc.C (coordinate 2))^3+
    ((RatFunc.X*RatFunc.C (coordinate 0))^6+(RatFunc.X*RatFunc.C (coordinate 1))^6+RatFunc.X^6+
    (5/7 : RadialField)*((RatFunc.X*RatFunc.C (coordinate 0))^5*(RatFunc.X*RatFunc.C (coordinate 1))+
      (RatFunc.X*RatFunc.C (coordinate 0))^2*(RatFunc.X*RatFunc.C (coordinate 1))^3*RatFunc.X+
      3*(RatFunc.X*RatFunc.C (coordinate 0))*RatFunc.X^5+
      2*(RatFunc.X*RatFunc.C (coordinate 1))^5*RatFunc.X)))=0
  linear_combination (RatFunc.X : RadialField)^6*hh

abbrev ConeCoordinateRing := AdjoinRoot coneEquation
instance : IsDomain ConeCoordinateRing := AdjoinRoot.isDomain_of_prime coneEquation_irreducible.prime

def newConeRingMap : ConeCoordinateRing →+* RadialField :=
  AdjoinRoot.lift (f:=coneEquation) coneCoefficientMap (RatFunc.X^2*RatFunc.C normal) cone_root
lemma newConeRingMap_injective : Function.Injective newConeRingMap :=
  monic_root_embedding_injective coneEquation coneEquation_monic coneEquation_irreducible
    coneCoefficientMap coneCoefficientMap_injective (RatFunc.X^2*RatFunc.C normal) cone_root
end SplitFCompanion

#print axioms SplitFCompanion.newConeRingMap_injective

namespace SplitThetaFactor
variable {R S L : Type*} [CommRing R] [CommRing S] [CommRing L]

def descend (f : R →+* S) (g : R →+* L) (hf : Function.Surjective f)
    (hker : ∀ r,f r=0 → g r=0) : S →+* L :=
  (Ideal.Quotient.lift (RingHom.ker f) g (fun r hr => hker r hr)).comp
    (RingHom.quotientKerEquivOfSurjective hf).symm.toRingHom
@[simp] lemma descend_apply (f : R →+* S) (g : R →+* L) (hf : Function.Surjective f)
    (hker : ∀ r,f r=0 → g r=0) (r : R) : descend f g hf hker (f r)=g r := by
  change (Ideal.Quotient.lift (RingHom.ker f) g (fun r hr => hker r hr))
    ((RingHom.quotientKerEquivOfSurjective hf).symm (f r))=g r
  rw [RingHom.quotientKerEquivOfSurjective_symm_apply]
  rfl
lemma descend_injective (f : R →+* S) (g : R →+* L) (hf : Function.Surjective f)
    (hker : ∀ r,f r=0 → g r=0) (hker' : ∀ r,g r=0 → f r=0) :
    Function.Injective (descend f g hf hker) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro s hs
  obtain ⟨r,rfl⟩ := hf s
  rw [descend_apply] at hs
  exact hker' r hs
end SplitThetaFactor

namespace SplitFCompanion
open Polynomial HoldoutConstruction
local instance : Algebra ℤ AffineField := Ring.toIntAlgebra _

lemma cleared_eq : clearedAffineEquation=7*CrossedMonicHypersurface.equation equation := by
  apply (MvPolynomial.finSuccEquiv ℂ 3).injective
  rw [equation_univariate,map_mul,map_ofNat,CrossedMonicHypersurface.equation,AlgEquiv.apply_symm_apply]
lemma cleared_partial (i : Fin 4) : integerPartial i clearedAffineEquation=
    7*integerPartial i (CrossedMonicHypersurface.equation equation) := by
  have h7 : integerPartial i (7 : Poly)=0 := (integerPartial i).map_natCast 7
  rw [cleared_eq,Derivation.leibniz,h7]
  simp only [smul_eq_mul,mul_zero,add_zero]
lemma tangent_formula (i : Fin 3) (P : Poly) :
    originalTangent i (evaluation P)=evaluation (integerPartial i.succ P)-
      evaluation (integerPartial i.succ clearedAffineEquation)/
        evaluation (integerPartial 0 clearedAffineEquation)*evaluation (integerPartial 0 P) := by
  have h0 : evaluation (integerPartial 0 clearedAffineEquation)=
      7*evaluation (integerPartial 0 (CrossedMonicHypersurface.equation equation)) := by
    rw [cleared_partial,map_mul,map_ofNat]
  have hi : evaluation (integerPartial i.succ clearedAffineEquation)=
      7*evaluation (integerPartial i.succ (CrossedMonicHypersurface.equation equation)) := by
    rw [cleared_partial,map_mul,map_ofNat]
  rw [h0,hi,mul_div_mul_left _ _ (by norm_num : (7 : AffineField)≠0)]
  exact CrossedMonicHypersurface.tangent_apply equation
    (EllipticCompanion.equation_monic p) equation_irreducible i P

lemma normal_ne_zero : normal≠0 := by
  intro hn
  apply clearNormal_ne_zero
  simp [hn]
lemma denominator_evaluation : evaluation denominator=6*normal^2 := by
  simp only [denominator,map_mul,map_ofNat,map_pow,CrossedMonicHypersurface.residueMap_X_zero]
  rfl
lemma denominator_ne_zero : evaluation denominator≠0 := by
  rw [denominator_evaluation]
  exact mul_ne_zero (by norm_num) (pow_ne_zero 2 normal_ne_zero)
lemma numerator_evaluation : evaluation numerator= -7*(coordinate 0)^4*(coordinate 1)^3*coordinate 2 := by
  simp only [numerator,map_mul,map_neg,map_ofNat,map_pow]
  rw [show evaluation (MvPolynomial.X 1)=coordinate 2 from CrossedMonicHypersurface.residueMap_X_succ equation 0,
    show evaluation (MvPolynomial.X 2)=coordinate 0 from CrossedMonicHypersurface.residueMap_X_succ equation 1,
    show evaluation (MvPolynomial.X 3)=coordinate 1 from CrossedMonicHypersurface.residueMap_X_succ equation 2]
  ring
lemma numerator_partial : integerPartial 0 numerator=0 := by
  have h7 : integerPartial 0 (7 : Poly)=0 := (integerPartial 0).map_natCast 7
  have hp7 : MvPolynomial.pderiv 0 (7 : Poly)=0 := (MvPolynomial.pderiv 0).map_natCast 7
  simp [numerator,Derivation.leibniz,Derivation.leibniz_pow,smul_eq_mul,h7,hp7]
lemma denominator_partial : integerPartial 0 denominator=12*MvPolynomial.X 0 := by
  have h6 : integerPartial 0 (6 : Poly)=0 := (integerPartial 0).map_natCast 6
  simp [denominator,Derivation.leibniz,Derivation.leibniz_pow,smul_eq_mul,h6]
  ring
lemma hessian_polynomial : integerPartial 0 (integerPartial 0 clearedAffineEquation)=42*MvPolynomial.X 0 := by
  rw [normal_polynomial]
  have h21 : integerPartial 0 (21 : Poly)=0 := (integerPartial 0).map_natCast 21
  simp [Derivation.leibniz,Derivation.leibniz_pow,smul_eq_mul,h21]
  ring

def affineDensity : AffineField := -2*(coordinate 0)^4*(coordinate 1)^3*coordinate 2/(9*normal^5)

/-- Only the geometric affine residue primitive is an input here. All rational
source denominators, normal equations and divergence clearing are explicit. -/
theorem source_data_of_affine_residue
    (hex : ∃ w : Fin 3 → AffineField,
      residueDivergence tangent (21*normal^2) w=affineDensity) :
    ∃ D : Poly,∃ N : Fin 4 → Poly,
      evaluation D≠0 ∧ denominator*(∑ i,N i*integerPartial i clearedAffineEquation)=numerator*D ∧
        evaluation (D*(∑ i,integerPartial i (N i))-(∑ i,N i*integerPartial i D))=0 := by
  obtain ⟨w,hw⟩ := hex
  let w' : Fin 3 → AffineField := fun i => w (![2,0,1] i)
  have hwp : residueDivergence originalTangent (21*normal^2) w'=affineDensity := by
    rw [← hw]
    simp [residueDivergence,fieldDivergence,Fin.sum_univ_three,w',tangent]
    ring
  obtain ⟨D,N₀,N,hD,hn,hdiv⟩ := SplitRationalAmbient.ambient_data evaluation (integerPartial 0)
    (fun i : Fin 3 => integerPartial i.succ) originalTangent clearedAffineEquation numerator denominator w'
    (normal_evaluation.trans_ne clearNormal_ne_zero) denominator_ne_zero
    (fun i => integerPartial_commute i.succ 0 clearedAffineEquation) tangent_formula
    (residue_common_representatives projection (CrossedMonicHypersurface.projection_surjective equation) w') (by
      change residueDivergence originalTangent (evaluation (integerPartial 0 clearedAffineEquation)) w'=
        -(evaluation (integerPartial 0 numerator)/(evaluation denominator*evaluation (integerPartial 0 clearedAffineEquation))-
          evaluation numerator*evaluation (integerPartial 0 denominator)/
            (evaluation denominator^2*evaluation (integerPartial 0 clearedAffineEquation))-
          evaluation numerator*evaluation (integerPartial 0 (integerPartial 0 clearedAffineEquation))/
            (evaluation denominator*evaluation (integerPartial 0 clearedAffineEquation)^2))
      rw [normal_evaluation,hessian_polynomial,numerator_partial,map_zero,denominator_partial,
        map_mul,map_ofNat,CrossedMonicHypersurface.residueMap_X_zero,
        numerator_evaluation,denominator_evaluation,hwp]
      simp only [map_mul,map_ofNat,show evaluation (MvPolynomial.X 0)=normal from
        CrossedMonicHypersurface.residueMap_X_zero equation]
      change affineDensity= -(_-_-_)
      unfold affineDensity
      field_simp [normal_ne_zero]
      dsimp only [normal]
      ring)
  refine ⟨D,Fin.cases N₀ N,hD,?_,?_⟩
  · rw [Fin.sum_univ_succ]
    simp only [Fin.cases_zero,Fin.cases_succ]
    exact hn
  · convert hdiv using 1 <;> congr 1 <;>
      simp only [residueDivNum,Fin.sum_univ_four,Fin.sum_univ_three,Fin.cases_zero,Fin.cases_succ] <;> ring
end SplitFCompanion

#print axioms SplitFCompanion.source_data_of_affine_residue
