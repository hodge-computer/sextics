import Proposal.CompanionResidue
import HodgeComputer.Constructions.EllipticCompanions.AffineCompanion
import HodgeComputer.Constructions.EllipticCompanions.Calculus
import HodgeComputer.Constructions.EllipticCompanions.Residues

/-!
Actual ordinary elliptic primitive for the second protected ternary.
The construction adapts the accepted crossed-ternary radial and scalar-jet
argument of 1337isnot1337 to the exact present polynomial and degree-five
source. The maintained generic algebra retains its original attribution.
Prepared with OpenAI Codex assistance for fqlx.
-/
noncomputable section
open scoped BigOperators

namespace SplitGCompanion
open Polynomial HoldoutConstruction
abbrev P2 := MvPolynomial (Fin 2) ℂ
abbrev Poly := MvPolynomial (Fin 4) ℂ
abbrev Coeff := MvPolynomial (Fin 3) ℂ

def p : P2 := MvPolynomial.X 0^6+MvPolynomial.X 1^6+1+
  MvPolynomial.C (5/7 : ℂ)*(2*MvPolynomial.X 0^5*MvPolynomial.X 1+
    2*MvPolynomial.X 0^3*MvPolynomial.X 1+MvPolynomial.X 0+3*MvPolynomial.X 1^5)
lemma p_zero : EllipticCompanion.zeroEvaluation p=1 := by
  simp [p,EllipticCompanion.zeroEvaluation]
lemma cubic_irreducible : Irreducible (EllipticCompanion.equation p) :=
  EllipticCompanion.equation_irreducible p p_zero

def lower : Polynomial Coeff :=
  C (MvPolynomial.X 0^6+1+MvPolynomial.X 1^3+MvPolynomial.X 2^3)+
    C (MvPolynomial.C (5/7 : ℂ))*(C (3 : Coeff)*X^5+
      C (2*MvPolynomial.X 0^5+2*MvPolynomial.X 0^3)*X+C (MvPolynomial.X 0))
def equation : Polynomial Coeff := X^6+lower
lemma lower_degree : lower.degree<6 := by unfold lower; compute_degree <;> norm_num
lemma equation_monic : equation.Monic := monic_X_pow_add (by simpa using lower_degree)

def affineEquation : Poly := MvPolynomial.X 0^6+MvPolynomial.X 1^6+1+
  MvPolynomial.C (5/7 : ℂ)*(2*MvPolynomial.X 1^5*MvPolynomial.X 0+
    2*MvPolynomial.X 1^3*MvPolynomial.X 0+MvPolynomial.X 1+3*MvPolynomial.X 0^5)+
  MvPolynomial.X 2^3+MvPolynomial.X 3^3

def reverse : Fin 4 ≃ Fin 4 where
  toFun i := ![3,2,1,0] i
  invFun i := ![3,2,1,0] i
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

lemma old_univariate : MvPolynomial.finSuccEquiv ℂ 3 affineEquation=equation := by
  have hv : (Fin.cases (Polynomial.X : Polynomial Coeff) (fun j => C (MvPolynomial.X j)))=
      ![X,C (MvPolynomial.X 0),C (MvPolynomial.X 1),C (MvPolynomial.X 2)] := by
    funext j; fin_cases j <;> rfl
  simp [affineEquation,equation,lower,MvPolynomial.finSuccEquiv_apply,hv,Polynomial.C_ofNat]
  ring
lemma base_expanded : EllipticCompanion.base p= MvPolynomial.X 1^6+MvPolynomial.X 2^6+1+
    MvPolynomial.C (5/7 : ℂ)*(2*MvPolynomial.X 1^5*MvPolynomial.X 2+
      2*MvPolynomial.X 1^3*MvPolynomial.X 2+MvPolynomial.X 1+3*MvPolynomial.X 2^5) := by
  apply (MvPolynomial.finSuccEquiv ℂ 2).injective
  rw [EllipticCompanion.base_univariate]
  have hv : (Fin.cases (Polynomial.X : Polynomial (MvPolynomial (Fin 2) ℂ))
      (fun j => C (MvPolynomial.X j)))=![X,C (MvPolynomial.X 0),C (MvPolynomial.X 1)] := by
    funext i; fin_cases i <;> rfl
  simp [p,MvPolynomial.finSuccEquiv_apply,Polynomial.C_ofNat,hv]
lemma new_univariate : MvPolynomial.finSuccEquiv ℂ 3 (MvPolynomial.rename reverse affineEquation)=
    EllipticCompanion.equation p := by
  have hv : (Fin.cases (Polynomial.X : Polynomial Coeff) (fun j => C (MvPolynomial.X j)))=
      ![X,C (MvPolynomial.X 0),C (MvPolynomial.X 1),C (MvPolynomial.X 2)] := by
    funext j; fin_cases j <;> rfl
  have h2 : MvPolynomial.rename reverse (2 : Poly)=2 := map_natCast _ 2
  have h3 : MvPolynomial.rename reverse (3 : Poly)=3 := map_natCast _ 3
  simp only [affineEquation,map_add,map_mul,map_pow,map_one,h2,h3,MvPolynomial.rename_X,MvPolynomial.rename_C]
  simp [EllipticCompanion.equation,base_expanded,MvPolynomial.finSuccEquiv_apply,hv,reverse,Polynomial.C_ofNat]
  ring

def presentationEquiv : Polynomial Coeff ≃+* Polynomial Coeff :=
  (MvPolynomial.finSuccEquiv ℂ 3).symm.toRingEquiv.trans
    ((MvPolynomial.renameEquiv (R:=ℂ) reverse).toRingEquiv.trans
      (MvPolynomial.finSuccEquiv ℂ 3).toRingEquiv)
lemma presentation_equation : presentationEquiv equation=EllipticCompanion.equation p := by
  rw [← old_univariate]
  change MvPolynomial.finSuccEquiv ℂ 3
    (MvPolynomial.rename reverse ((MvPolynomial.finSuccEquiv ℂ 3).symm
      (MvPolynomial.finSuccEquiv ℂ 3 affineEquation)))=_
  rw [AlgEquiv.symm_apply_apply]
  exact new_univariate
lemma equation_irreducible : Irreducible equation := by
  apply (MulEquiv.irreducible_iff presentationEquiv).mp
  rw [presentation_equation]
  exact cubic_irreducible

abbrev CoordinateRing := AdjoinRoot equation
instance : IsDomain CoordinateRing := AdjoinRoot.isDomain_of_prime equation_irreducible.prime
abbrev AffineField := FractionRing CoordinateRing
instance : CharZero AffineField :=
  charZero_of_injective_ringHom (f:=algebraMap ℂ AffineField) (algebraMap ℂ AffineField).injective
local instance : Algebra ℤ AffineField := Ring.toIntAlgebra _

def coefficientEmbedding : Coeff →+* AffineField := (algebraMap CoordinateRing AffineField).comp (AdjoinRoot.of equation)
lemma coefficientEmbedding_injective : Function.Injective coefficientEmbedding :=
  (IsFractionRing.injective CoordinateRing AffineField).comp
    (AdjoinRoot.of.injective_of_degree_ne_zero
      (ne_of_gt (equation_monic.degree_pos_of_not_isUnit equation_irreducible.not_isUnit)))
@[simp] lemma coefficientEmbedding_C (c : ℂ) : coefficientEmbedding (MvPolynomial.C c)=algebraMap ℂ AffineField c := rfl

def coordinate (i : Fin 3) : AffineField := coefficientEmbedding (MvPolynomial.X i)
def normal : AffineField := algebraMap CoordinateRing AffineField (AdjoinRoot.root equation)
lemma normal_root : equation.eval₂ coefficientEmbedding normal=0 := by
  have h := congrArg (algebraMap CoordinateRing AffineField) (AdjoinRoot.eval₂_root equation)
  rw [map_zero,Polynomial.hom_eval₂] at h
  exact h
lemma cleared_equation : SplitCompanion.H false 0 ![coordinate 0,normal,1,coordinate 1,coordinate 2]=0 := by
  have h := normal_root
  simp only [equation,lower,Polynomial.eval₂_add,Polynomial.eval₂_pow,Polynomial.eval₂_X,
    Polynomial.eval₂_mul,Polynomial.eval₂_C,map_add,map_mul,map_pow,map_one,map_ofNat,
    coefficientEmbedding_C,Polynomial.eval₂_one,Polynomial.eval₂_ofNat] at h
  have h5 : algebraMap ℂ AffineField (5/7 : ℂ)=(5/7 : AffineField) := by
    rw [map_div₀]; congr 1 <;> exact map_natCast _ _
  rw [h5] at h
  simp [SplitCompanion.H,SplitCompanion.second,coordinate]
  linear_combination 7*h

abbrev projection := CrossedMonicHypersurface.projection equation
abbrev residueMap := CrossedMonicHypersurface.residueMap equation
abbrev tangent := CrossedMonicHypersurface.tangent equation equation_monic equation_irreducible
lemma residueMap_X_zero : residueMap (MvPolynomial.X 0)=normal := CrossedMonicHypersurface.residueMap_X_zero equation
lemma residueMap_X_succ (j : Fin 3) : residueMap (MvPolynomial.X j.succ)=coordinate j := by
  rw [CrossedMonicHypersurface.residueMap_X_succ]; rfl
lemma tangent_coordinate (i j : Fin 3) : tangent i (coordinate j)=if j=i then 1 else 0 := by
  rw [← residueMap_X_succ]
  exact CrossedMonicHypersurface.tangent_parameter equation equation_monic equation_irreducible i j
@[simp] lemma tangent_base (i : Fin 3) (c : ℂ) : tangent i (algebraMap ℂ AffineField c)=0 :=
  CrossedMonicHypersurface.tangent_constant equation equation_monic equation_irreducible i c

def clearNormal : AffineField := 42*normal^5+5*(2*coordinate 0^5+2*coordinate 0^3+15*normal^4)
def clearSecondNormal : AffineField := 210*normal^4+300*normal^3
lemma clearNormal_ne_zero : clearNormal≠0 := by
  have h := CrossedMonicHypersurface.normal_ne_zero equation equation_monic equation_irreducible
  have he : MvPolynomial.finSuccEquiv ℂ 3 (integerPartial 0 affineEquation)=equation.derivative := by
    rw [← CrossedMonicHypersurface.derivative_finSuccEquiv,old_univariate]
  have hh : residueMap (integerPartial 0 affineEquation)=clearNormal/7 := by
    have h2 : integerPartial (R:=ℂ) (0 : Fin 4) (2 : Poly)=0 := (integerPartial 0).map_natCast 2
    have h3 : integerPartial (R:=ℂ) (0 : Fin 4) (3 : Poly)=0 := (integerPartial 0).map_natCast 3
    simp only [integerPartial_apply] at h2 h3
    have hp : integerPartial 0 affineEquation=6*MvPolynomial.X 0^5+
        MvPolynomial.C (5/7 : ℂ)*(2*MvPolynomial.X 1^5+2*MvPolynomial.X 1^3+15*MvPolynomial.X 0^4) := by
      simp [affineEquation,Derivation.leibniz,Derivation.leibniz_pow,smul_eq_mul,h2,h3]
      ring
    rw [hp]
    simp only [map_add,map_mul,map_pow,map_ofNat,CrossedMonicHypersurface.residueMap_C,residueMap_X_zero]
    have hx : residueMap (MvPolynomial.X 1)=coordinate 0 := residueMap_X_succ 0
    rw [hx]
    have hc : algebraMap ℂ AffineField (5/7 : ℂ)=(5/7 : AffineField) := by
      rw [map_div₀]; congr 1 <;> exact map_natCast _ _
    rw [hc]
    dsimp [clearNormal]
    field_simp
    ring
  have hf : CrossedMonicHypersurface.equation equation=affineEquation := by
    rw [CrossedMonicHypersurface.equation,← old_univariate,AlgEquiv.symm_apply_apply]
  rw [hf,hh] at h
  exact fun hz => h (by rw [hz,zero_div])

end SplitGCompanion

namespace SplitGCompanion
open Polynomial HoldoutConstruction CrossedRadialResidue
abbrev RadialField := RatFunc AffineField
local instance : Algebra ℤ RadialField := Ring.toIntAlgebra _
local instance : Algebra ℤ AffineField := Ring.toIntAlgebra _
local instance : Algebra ℤ (SplitCompanionDomain.FunctionField false) := Ring.toIntAlgebra _

def rawPolynomialMap : SplitCompanionDomain.Coeff →+* Polynomial AffineField :=
  (Polynomial.mapRingHom coefficientEmbedding).comp
    ((MvPolynomial.finSuccEquiv ℂ 3).toRingHom.comp (MvPolynomial.rename (Equiv.swap (0 : Fin 4) 1)).toRingHom)
lemma rawPolynomialMap_injective : Function.Injective rawPolynomialMap :=
  (Polynomial.map_injective coefficientEmbedding coefficientEmbedding_injective).comp
    ((MvPolynomial.finSuccEquiv ℂ 3).injective.comp
      (MvPolynomial.rename_injective (R:=ℂ) (Equiv.swap (0 : Fin 4) 1) (Equiv.swap (0 : Fin 4) 1).injective))
lemma rawPolynomialMap_C (c : ℂ) : rawPolynomialMap (MvPolynomial.C c)=Polynomial.C (algebraMap ℂ AffineField c) := by
  simp [rawPolynomialMap,MvPolynomial.rename_C,MvPolynomial.finSuccEquiv_apply]
lemma rawPolynomialMap_X (i : Fin 4) : rawPolynomialMap (MvPolynomial.X i)=
    ![C (coordinate 0),X,C (coordinate 1),C (coordinate 2)] i := by
  have hv : (Fin.cases (Polynomial.X : Polynomial Coeff) (fun j => C (MvPolynomial.X j)))=
      ![X,C (MvPolynomial.X 0),C (MvPolynomial.X 1),C (MvPolynomial.X 2)] := by
    funext j; fin_cases j <;> rfl
  fin_cases i <;> simp [rawPolynomialMap,coordinate,MvPolynomial.finSuccEquiv_apply,hv,Equiv.swap_apply_def]
def polynomialCoefficientMap : SplitCompanionDomain.Coeff →+* Polynomial AffineField :=
  rawPolynomialMap.comp CrossedWeightedRadial.monomialMap
lemma polynomialCoefficientMap_injective : Function.Injective polynomialCoefficientMap := by
  rw [polynomialCoefficientMap,RingHom.coe_comp]
  exact rawPolynomialMap_injective.comp (CrossedWeightedRadial.monomialMap_injective (R:=ℂ))
def coneCoefficientMap : SplitCompanionDomain.Coeff →+* RadialField :=
  (algebraMap (Polynomial AffineField) RadialField).comp polynomialCoefficientMap
lemma coneCoefficientMap_injective : Function.Injective coneCoefficientMap :=
  (IsFractionRing.injective (Polynomial AffineField) RadialField).comp polynomialCoefficientMap_injective

def coneCoordinate (i : Fin 5) : RadialField :=
  ![RatFunc.X*RatFunc.C (coordinate 0),RatFunc.X*RatFunc.C normal,RatFunc.X,
    RatFunc.X^2*RatFunc.C (coordinate 1),RatFunc.X^2*RatFunc.C (coordinate 2)] i
lemma coneCoefficientMap_C (c : ℂ) : coneCoefficientMap (MvPolynomial.C c)=algebraMap ℂ RadialField c := by
  rw [coneCoefficientMap,RingHom.comp_apply,polynomialCoefficientMap,RingHom.comp_apply,
    CrossedWeightedRadial.monomialMap_C,rawPolynomialMap_C]
  rfl
lemma coneCoefficientMap_X (i : Fin 4) : coneCoefficientMap (MvPolynomial.X i)=
    ![coneCoordinate 0,coneCoordinate 2,coneCoordinate 3,coneCoordinate 4] i := by
  rw [coneCoefficientMap,RingHom.comp_apply,polynomialCoefficientMap,RingHom.comp_apply,CrossedWeightedRadial.monomialMap_X]
  fin_cases i <;> simp [rawPolynomialMap_X,coneCoordinate,RatFunc.algebraMap_X,RatFunc.algebraMap_C]
  all_goals ring
lemma coneCoordinate_equation : SplitCompanion.H false 0 coneCoordinate=0 := by
  have h := congrArg (RatFunc.C : AffineField →+* RadialField) cleared_equation
  rw [map_zero,SplitCompanion.H_map,map_zero] at h
  simp [SplitCompanion.H,SplitCompanion.second,coneCoordinate] at h ⊢
  linear_combination (RatFunc.X : RadialField)^6*h
lemma cone_normal_root : (SplitCompanionDomain.equation false).eval₂ coneCoefficientMap (coneCoordinate 1)=0 := by
  have h := coneCoordinate_equation
  simp only [SplitCompanionDomain.equation,SplitCompanionDomain.lower,Bool.false_eq_true,ite_false,
    Polynomial.eval₂_add,Polynomial.eval₂_pow,Polynomial.eval₂_X,Polynomial.eval₂_mul,Polynomial.eval₂_C,
    Polynomial.eval₂_ofNat,map_add,map_mul,map_pow,map_ofNat,coneCoefficientMap_C,coneCoefficientMap_X]
  have h5 : algebraMap ℂ RadialField (5/7 : ℂ)=(5/7 : RadialField) := by
    rw [map_div₀]; congr 1 <;> exact map_natCast _ _
  rw [h5]
  simp [Matrix.cons_val_two,Matrix.cons_val_three,Matrix.vecHead,Matrix.vecTail]
  unfold SplitCompanion.H SplitCompanion.second at h
  simp only [Bool.false_eq_true,ite_false,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two] at h
  dsimp only [Matrix.vecHead,Matrix.vecTail,Function.comp_apply,Fin.succ_zero_eq_one] at *
  simp only [Matrix.cons_val_one,Matrix.cons_val_succ,Matrix.cons_val_zero] at *
  linear_combination h/7

def coneRingMap : SplitCompanionDomain.CoordinateRing false →+* RadialField :=
  AdjoinRoot.lift (f:=SplitCompanionDomain.equation false) coneCoefficientMap (coneCoordinate 1) cone_normal_root
lemma coneRingMap_injective : Function.Injective coneRingMap :=
  monic_root_embedding_injective (SplitCompanionDomain.equation false) (SplitCompanionDomain.equation_monic false)
    (SplitCompanionDomain.equation_irreducible false) coneCoefficientMap coneCoefficientMap_injective (coneCoordinate 1) cone_normal_root
def coneFieldMap : SplitCompanionDomain.FunctionField false →+* RadialField := IsFractionRing.lift coneRingMap_injective
@[simp] lemma coneFieldMap_ring (r : SplitCompanionDomain.CoordinateRing false) :
    coneFieldMap (algebraMap (SplitCompanionDomain.CoordinateRing false) (SplitCompanionDomain.FunctionField false) r)=coneRingMap r :=
  IsFractionRing.lift_algebraMap coneRingMap_injective r
@[simp] lemma coneFieldMap_base (c : ℂ) : coneFieldMap (algebraMap ℂ (SplitCompanionDomain.FunctionField false) c)=algebraMap ℂ RadialField c := by
  change coneFieldMap (algebraMap (SplitCompanionDomain.CoordinateRing false) (SplitCompanionDomain.FunctionField false)
    (AdjoinRoot.of (SplitCompanionDomain.equation false) (MvPolynomial.C c)))=_
  rw [coneFieldMap_ring]
  change AdjoinRoot.lift _ _ _ (AdjoinRoot.of _ _)=_
  rw [AdjoinRoot.lift_of,coneCoefficientMap_C]
lemma coneFieldMap_coordinate (j : Fin 5) :
    coneFieldMap (SplitCompanionDomain.residueMap false (MvPolynomial.X j))=
      ![coneCoordinate 1,coneCoordinate 0,coneCoordinate 2,coneCoordinate 3,coneCoordinate 4] j := by
  refine Fin.cases ?_ (fun i => ?_) j
  · rw [CrossedMonicHypersurface.residueMap_X_zero,coneFieldMap_ring]
    exact AdjoinRoot.lift_root cone_normal_root
  · rw [CrossedMonicHypersurface.residueMap_X_succ,coneFieldMap_ring]
    change AdjoinRoot.lift _ _ _ (AdjoinRoot.of _ _)=_
    rw [AdjoinRoot.lift_of,coneCoefficientMap_X]
    fin_cases i <;> rfl

def coneEvaluation : MvPolynomial (Fin 5) ℂ →+* RadialField := coneFieldMap.comp (SplitCompanionDomain.residueMap false)
lemma coneEvaluation_X (j : Fin 5) : coneEvaluation (MvPolynomial.X j)=
    ![coneCoordinate 1,coneCoordinate 0,coneCoordinate 2,coneCoordinate 3,coneCoordinate 4] j := coneFieldMap_coordinate j
@[simp] lemma coneEvaluation_C (c : ℂ) : coneEvaluation (MvPolynomial.C c)=algebraMap ℂ RadialField c := by
  rw [coneEvaluation,RingHom.comp_apply,CrossedMonicHypersurface.residueMap_C,coneFieldMap_base]

def radialDerivation (i : Fin 4) : Derivation ℤ RadialField RadialField := coneDerivations tangent coordinate i
lemma radialDerivation_base (i : Fin 4) (c : ℂ) : radialDerivation i (algebraMap ℂ RadialField c)=0 := by
  change radialDerivation i (RatFunc.C (algebraMap ℂ AffineField c))=0
  exact coneDerivations_constant _ _ _ (fun j => tangent_base j c) i
lemma cone_tangent_parameter (i j : Fin 4) : SplitCompanionDomain.tangent false i
    (SplitCompanionDomain.residueMap false (MvPolynomial.X j.succ))=if j=i then 1 else 0 := by
  rw [SplitCompanionDomain.tangent_apply,integerPartial_X_of_ne 0 j.succ (Fin.succ_ne_zero j)]
  simp only [map_zero,mul_zero,sub_zero]
  by_cases h : j=i
  · subst j; simp
  · have hs : j.succ≠i.succ := fun he => h (Fin.succ_injective _ he)
    simp [integerPartial_X_of_ne _ _ hs,h]
lemma cone_tangent_base (i : Fin 4) (c : ℂ) :
    SplitCompanionDomain.tangent false i (algebraMap ℂ (SplitCompanionDomain.FunctionField false) c)=0 := by
  rw [← CrossedMonicHypersurface.residueMap_C (SplitCompanionDomain.equation false),SplitCompanionDomain.tangent_apply]
  simp only [integerPartial_C,map_zero,mul_zero,sub_self]
lemma radialDerivation_compatible (i : Fin 4) (z : SplitCompanionDomain.FunctionField false) :
    radialDerivation i (coneFieldMap z)=coneFieldMap (SplitCompanionDomain.tangent false i z) := by
  apply CrossedImplicitIntertwining.quotient_fraction_intertwines
    (SplitCompanionDomain.projection false) (SplitCompanionDomain.projection_surjective false) coneFieldMap
    (SplitCompanionDomain.hypersurface false)
    ((SplitCompanionDomain.residueMap_kernel false _).mpr (dvd_refl _)) (SplitCompanionDomain.normal_ne_zero false)
    (SplitCompanionDomain.tangent false i) (radialDerivation i)
  · intro c
    change SplitCompanionDomain.tangent false i (SplitCompanionDomain.residueMap false (MvPolynomial.C c))=0
    rw [CrossedMonicHypersurface.residueMap_C,cone_tangent_base]
  · intro c
    change radialDerivation i (coneFieldMap (SplitCompanionDomain.residueMap false (MvPolynomial.C c)))=0
    rw [CrossedMonicHypersurface.residueMap_C,coneFieldMap_base,radialDerivation_base]
  · intro j
    change radialDerivation i (coneFieldMap (SplitCompanionDomain.residueMap false (MvPolynomial.X j.succ)))=
      coneFieldMap (SplitCompanionDomain.tangent false i (SplitCompanionDomain.residueMap false (MvPolynomial.X j.succ)))
    rw [cone_tangent_parameter,coneFieldMap_coordinate]
    have he : ![coneCoordinate 1,coneCoordinate 0,coneCoordinate 2,coneCoordinate 3,coneCoordinate 4] j.succ=
      independentCoordinates coordinate j := by fin_cases j <;> rfl
    rw [he,radialDerivation,coneDerivations_coordinate tangent coordinate tangent_coordinate]
    split_ifs <;> simp

end SplitGCompanion

namespace SplitGCompanion
open Polynomial HoldoutConstruction CrossedRadialResidue
local instance : Algebra ℤ AffineField := Ring.toIntAlgebra _
local instance : Algebra ℤ RadialField := Ring.toIntAlgebra _

def clearedAffineEquation : Poly := SplitCompanion.H false 0
  ![MvPolynomial.X 1,MvPolynomial.X 0,1,MvPolynomial.X 2,MvPolynomial.X 3]
abbrev evaluation : Poly →+* AffineField := residueMap
@[simp] lemma evaluation_C (c : ℂ) : evaluation (MvPolynomial.C c)=algebraMap ℂ AffineField c :=
  CrossedMonicHypersurface.residueMap_C equation c
@[simp] lemma evaluation_X_zero : evaluation (MvPolynomial.X 0)=normal := residueMap_X_zero
lemma evaluation_X_succ (i : Fin 3) : evaluation (MvPolynomial.X i.succ)=coordinate i := residueMap_X_succ i
lemma equation_zero : evaluation clearedAffineEquation=0 := by
  rw [clearedAffineEquation,SplitCompanion.H_map,map_zero]
  have hv : (fun i => evaluation
      (![MvPolynomial.X 1,MvPolynomial.X 0,1,MvPolynomial.X 2,MvPolynomial.X 3] i))=
      ![coordinate 0,normal,1,coordinate 1,coordinate 2] := by
    funext i
    fin_cases i
    · exact evaluation_X_succ 0
    · exact evaluation_X_zero
    · exact map_one _
    · exact evaluation_X_succ 1
    · exact evaluation_X_succ 2
  rw [hv]
  exact cleared_equation
lemma equation_partial : integerPartial 0 clearedAffineEquation=
    42*MvPolynomial.X 0^5+5*(2*MvPolynomial.X 1^5+2*MvPolynomial.X 1^3+15*MvPolynomial.X 0^4) := by
  have h (z : Fin 5 → Poly) : integerPartial 0 (SplitCompanion.H false 0 z)=
      ∑ i,SplitCompanion.gradient false 0 z i*integerPartial 0 (z i) :=
    SplitCompanion.H_derivation (integerPartial 0) false 0 (map_zero _) z
  rw [clearedAffineEquation,h]
  simp [SplitCompanion.gradient,Fin.sum_univ_succ]
  ring
lemma equation_hessian : integerPartial 0 (integerPartial 0 clearedAffineEquation)=
    210*MvPolynomial.X 0^4+300*MvPolynomial.X 0^3 := by
  rw [equation_partial]
  have h42 : integerPartial (R:=ℂ) (0 : Fin 4) (42 : Poly)=0 := (integerPartial 0).map_natCast 42
  have h5 : integerPartial (R:=ℂ) (0 : Fin 4) (5 : Poly)=0 := (integerPartial 0).map_natCast 5
  have h2 : integerPartial (R:=ℂ) (0 : Fin 4) (2 : Poly)=0 := (integerPartial 0).map_natCast 2
  have h15 : integerPartial (R:=ℂ) (0 : Fin 4) (15 : Poly)=0 := (integerPartial 0).map_natCast 15
  simp only [integerPartial_apply] at h42 h5 h2 h15
  simp [Derivation.leibniz,Derivation.leibniz_pow,smul_eq_mul,h42,h5,h2,h15]
  ring
lemma normal_evaluation : evaluation (integerPartial 0 clearedAffineEquation)=clearNormal := by
  rw [equation_partial]
  simp only [map_add,map_mul,map_pow,map_ofNat,evaluation_X_zero]
  rw [show evaluation (MvPolynomial.X 1)=coordinate 0 from evaluation_X_succ 0]
  rfl
lemma hessian_evaluation : evaluation (integerPartial 0 (integerPartial 0 clearedAffineEquation))=clearSecondNormal := by
  rw [equation_hessian]
  simp only [map_add,map_mul,map_pow,map_ofNat,evaluation_X_zero]
  rfl
lemma tangent_formula (i : Fin 3) (P : Poly) :
    tangent i (evaluation P)=evaluation (integerPartial i.succ P)-
      evaluation (integerPartial i.succ clearedAffineEquation)/evaluation (integerPartial 0 clearedAffineEquation)*
        evaluation (integerPartial 0 P) := by
  apply CrossedAffinePrimitiveData.tangent_formula_from_coordinates evaluation clearedAffineEquation equation_zero
    (by rw [show evaluation (MvPolynomial.pderiv 0 clearedAffineEquation)=clearNormal from normal_evaluation]; exact clearNormal_ne_zero)
    (tangent i) i
  · intro c; rw [evaluation_C,tangent_base]
  · intro j; rw [evaluation_X_succ]; exact tangent_coordinate i j

def coneSource : MvPolynomial (Fin 5) ℂ := 7*MvPolynomial.X 1^3*MvPolynomial.X 0^2
def source : Poly := 7*MvPolynomial.X 1^3*MvPolynomial.X 0^2
def affineSource : AffineField := 7*coordinate 0^3*normal^2
lemma source_partial : integerPartial 0 source=14*MvPolynomial.X 1^3*MvPolynomial.X 0 := by
  have h7 : integerPartial (R:=ℂ) (0 : Fin 4) (7 : Poly)=0 := (integerPartial 0).map_natCast 7
  simp [source,Derivation.leibniz,Derivation.leibniz_pow,smul_eq_mul,h7]
  ring
lemma source_value : evaluation source=affineSource := by
  simp only [source,map_mul,map_pow,map_ofNat,evaluation_X_zero]
  rw [show evaluation (MvPolynomial.X 1)=coordinate 0 from evaluation_X_succ 0]
  rfl
lemma source_partial_value : evaluation (integerPartial 0 source)=14*coordinate 0^3*normal := by
  rw [source_partial]
  simp only [map_mul,map_pow,map_ofNat,evaluation_X_zero]
  rw [show evaluation (MvPolynomial.X 1)=coordinate 0 from evaluation_X_succ 0]

lemma cone_normal_polynomial : integerPartial 0 (SplitCompanionDomain.hypersurface false)=
    42*MvPolynomial.X 0^5+5*(2*MvPolynomial.X 1^5+2*MvPolynomial.X 1^3*MvPolynomial.X 2^2+
      15*MvPolynomial.X 0^4*MvPolynomial.X 2) := by
  rw [SplitCompanionDomain.hypersurface_partial]
  simp [SplitCompanion.gradient,SplitCompanionDomain.coordinateSwap,Equiv.swap_apply_def]
  ring
lemma cone_hessian_polynomial : integerPartial 0 (integerPartial 0 (SplitCompanionDomain.hypersurface false))=
    210*MvPolynomial.X 0^4+300*MvPolynomial.X 0^3*MvPolynomial.X 2 := by
  rw [cone_normal_polynomial]
  have h42 : integerPartial (R:=ℂ) (0 : Fin 5) (42 : MvPolynomial (Fin 5) ℂ)=0 := (integerPartial 0).map_natCast 42
  have h5 : integerPartial (R:=ℂ) (0 : Fin 5) (5 : MvPolynomial (Fin 5) ℂ)=0 := (integerPartial 0).map_natCast 5
  have h2 : integerPartial (R:=ℂ) (0 : Fin 5) (2 : MvPolynomial (Fin 5) ℂ)=0 := (integerPartial 0).map_natCast 2
  have h15 : integerPartial (R:=ℂ) (0 : Fin 5) (15 : MvPolynomial (Fin 5) ℂ)=0 := (integerPartial 0).map_natCast 15
  simp only [integerPartial_apply] at h42 h5 h2 h15
  simp [Derivation.leibniz,Derivation.leibniz_pow,smul_eq_mul,h42,h5,h2,h15]
  ring
lemma coneEvaluation_X_chart (j : Fin 5) : coneEvaluation (MvPolynomial.X j)=
    ![RatFunc.X*RatFunc.C normal,RatFunc.X*RatFunc.C (coordinate 0),RatFunc.X,
      RatFunc.X^2*RatFunc.C (coordinate 1),RatFunc.X^2*RatFunc.C (coordinate 2)] j := by
  rw [coneEvaluation_X]; fin_cases j <;> rfl

lemma coneEvaluation_normal : coneEvaluation (integerPartial 0 (SplitCompanionDomain.hypersurface false))=
    RatFunc.X^5*RatFunc.C clearNormal := by
  rw [cone_normal_polynomial]
  simp only [map_add,map_mul,map_pow,map_ofNat,coneEvaluation_X_chart]
  change 42*(RatFunc.X*RatFunc.C normal)^5+
    5*(2*(RatFunc.X*RatFunc.C (coordinate 0))^5+
      2*(RatFunc.X*RatFunc.C (coordinate 0))^3*RatFunc.X^2+
      15*(RatFunc.X*RatFunc.C normal)^4*RatFunc.X)=RatFunc.X^5*RatFunc.C clearNormal
  simp only [clearNormal,map_add,map_mul,map_pow,map_ofNat]
  ring
lemma coneEvaluation_hessian : coneEvaluation (integerPartial 0 (integerPartial 0 (SplitCompanionDomain.hypersurface false)))=
    RatFunc.X^4*RatFunc.C clearSecondNormal := by
  rw [cone_hessian_polynomial]
  simp only [map_add,map_mul,map_pow,map_ofNat,coneEvaluation_X_chart]
  change 210*(RatFunc.X*RatFunc.C normal)^4+
    300*(RatFunc.X*RatFunc.C normal)^3*RatFunc.X=RatFunc.X^4*RatFunc.C clearSecondNormal
  simp only [clearSecondNormal,map_add,map_mul,map_pow,map_ofNat]
  ring
lemma coneSource_partial : integerPartial 0 coneSource=14*MvPolynomial.X 1^3*MvPolynomial.X 0 := by
  have h7 : integerPartial (R:=ℂ) (0 : Fin 5) (7 : MvPolynomial (Fin 5) ℂ)=0 := (integerPartial 0).map_natCast 7
  simp [coneSource,Derivation.leibniz,Derivation.leibniz_pow,smul_eq_mul,h7]
  ring
lemma coneEvaluation_source : coneEvaluation coneSource=RatFunc.X^5*RatFunc.C affineSource := by
  simp only [coneSource,map_mul,map_pow,map_ofNat,coneEvaluation_X_chart]
  simp only [coneCoordinate,Matrix.cons_val_zero,Matrix.cons_val_one]
  simp only [affineSource,map_mul,map_pow,map_ofNat]
  ring
lemma coneEvaluation_source_partial : coneEvaluation (integerPartial 0 coneSource)=
    RatFunc.X^4*RatFunc.C (14*coordinate 0^3*normal) := by
  rw [coneSource_partial]
  simp only [map_mul,map_pow,map_ofNat,coneEvaluation_X_chart]
  simp only [coneCoordinate,Matrix.cons_val_zero,Matrix.cons_val_one]
  try simp only [map_mul,map_pow,map_ofNat]
  ring

lemma cone_residue_solution : ∃ w : Fin 4 → RadialField,
    residueDivergence radialDerivation (RatFunc.X^5*RatFunc.C clearNormal) w=
      -(RatFunc.X^4*RatFunc.C (14*coordinate 0^3*normal)/(RatFunc.X^5*RatFunc.C clearNormal)-
        (RatFunc.X^5*RatFunc.C affineSource)*(RatFunc.X^4*RatFunc.C clearSecondNormal)/
          (RatFunc.X^5*RatFunc.C clearNormal)^2) := by
  obtain ⟨w,hw⟩ := SplitCompanion.companion_residue_solution false coneSource
  refine ⟨fun i => coneFieldMap (w i),?_⟩
  have hm := residueDivergence_map coneFieldMap (SplitCompanionDomain.tangent false) radialDerivation
    radialDerivation_compatible (SplitCompanionDomain.residueMap false
      (MvPolynomial.pderiv 0 (SplitCompanionDomain.hypersurface false))) w
  rw [hw] at hm
  simp only [map_neg,map_sub,map_div₀,map_mul,map_pow] at hm
  change residueDivergence radialDerivation
      (coneEvaluation (integerPartial 0 (SplitCompanionDomain.hypersurface false))) (fun i => coneFieldMap (w i))=
    -(coneEvaluation (integerPartial 0 coneSource)/coneEvaluation (integerPartial 0 (SplitCompanionDomain.hypersurface false))-
      coneEvaluation coneSource*coneEvaluation (integerPartial 0 (integerPartial 0 (SplitCompanionDomain.hypersurface false)))/
        (coneEvaluation (integerPartial 0 (SplitCompanionDomain.hypersurface false)))^2) at hm
  rw [coneEvaluation_normal,coneEvaluation_hessian,coneEvaluation_source,coneEvaluation_source_partial] at hm
  exact hm

theorem affine_residue_solution : ∃ w : Fin 3 → AffineField,
    residueDivergence tangent clearNormal w=
      -((14*coordinate 0^3*normal)/clearNormal-affineSource*clearSecondNormal/clearNormal^2) := by
  obtain ⟨w,hw⟩ := cone_residue_solution
  have hρ : (RatFunc.X : RadialField)≠0 := CrossedRationalResidue.X_ne_zero
  have hg : (RatFunc.C clearNormal : RadialField)≠0 := by
    simpa only [map_zero] using RatFunc.C_injective.ne clearNormal_ne_zero
  have he : -(RatFunc.X^4*RatFunc.C (14*coordinate 0^3*normal)/(RatFunc.X^5*RatFunc.C clearNormal)-
      (RatFunc.X^5*RatFunc.C affineSource)*(RatFunc.X^4*RatFunc.C clearSecondNormal)/(RatFunc.X^5*RatFunc.C clearNormal)^2)=
      RatFunc.C (-((14*coordinate 0^3*normal)/clearNormal-affineSource*clearSecondNormal/clearNormal^2))/RatFunc.X := by
    simp only [map_neg,map_sub,map_div₀,map_mul,map_pow]
    field_simp
  rw [he] at hw
  exact residue_solution_descends_radial tangent coordinate (fun i => by simpa using tangent_coordinate i i)
    clearNormal clearNormal_ne_zero _ w hw

theorem source_data : ∃ D N₀ : Poly,∃ N : Fin 3 → Poly,
    evaluation D≠0 ∧ (N₀*integerPartial 0 clearedAffineEquation+∑ i,N i*integerPartial i.succ clearedAffineEquation=source*D) ∧
      evaluation (residueDivNum (integerPartial 0) (fun i : Fin 3 => integerPartial i.succ) D N₀ N)=0 := by
  obtain ⟨w,hw⟩ := affine_residue_solution
  apply CrossedAffinePrimitiveData.ambient_data evaluation (integerPartial 0)
    (fun i : Fin 3 => integerPartial i.succ) tangent clearedAffineEquation source w
  · exact normal_evaluation.trans_ne clearNormal_ne_zero
  · intro i; exact integerPartial_commute i.succ 0 clearedAffineEquation
  · exact tangent_formula
  · exact residue_common_representatives projection (CrossedMonicHypersurface.projection_surjective equation) w
  · rw [← normal_evaluation,← hessian_evaluation,← source_partial_value,← source_value] at hw
    exact hw

end SplitGCompanion
