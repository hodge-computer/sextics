import Proposal.CompanionTheta
import Proposal.CompanionPoleTwo

/-! Compatible T-pivot cone and affine chart maps. Prepared with OpenAI
Codex assistance for fqlx. The exact old coordinate ring is retained. -/
noncomputable section
open scoped BigOperators
namespace SplitFCompanion
open Polynomial HoldoutConstruction

lemma cone_hypersurface_eq : SplitCompanionPoleTwo.hypersurfaceT true=
    7*CrossedMonicHypersurface.equation coneEquation := by
  apply (MvPolynomial.finSuccEquiv ℂ 4).injective
  rw [SplitCompanionPoleTwo.hypersurfaceT_explicit]
  have hv : (Fin.cases (Polynomial.X : Polynomial ConeCoeff) (fun j => C (MvPolynomial.X j)))=
      ![X,C (MvPolynomial.X 0),C (MvPolynomial.X 1),C (MvPolynomial.X 2),C (MvPolynomial.X 3)] := by
    funext i; fin_cases i <;> rfl
  have h7 : (MvPolynomial.finSuccEquiv ℂ 4) (7 : ConePoly)=7 := map_natCast _ 7
  rw [map_mul,h7,CrossedMonicHypersurface.equation,AlgEquiv.apply_symm_apply]
  simp [SplitCompanion.H,SplitCompanion.first,MvPolynomial.finSuccEquiv_apply,hv,
    coneEquation,homogeneousBase,Polynomial.C_ofNat]
  have h57 : (7 : Polynomial ConeCoeff)*C (MvPolynomial.C (5/7 : ℂ))=5 := by
    simpa only [mul_comm] using SplitCompanionDomain.scalar_five_seven
  linear_combination -(C (MvPolynomial.X 0)^5*C (MvPolynomial.X 1)+
    C (MvPolynomial.X 0)^2*C (MvPolynomial.X 1)^3*C (MvPolynomial.X 2)+
    3*C (MvPolynomial.X 0)*C (MvPolynomial.X 2)^5+
    2*C (MvPolynomial.X 1)^5*C (MvPolynomial.X 2))*h57

lemma seven_scaled_dvd (F P : ConePoly) : 7*F∣P ↔ F∣P := by
  constructor
  · exact dvd_trans (dvd_mul_left F 7)
  · rintro ⟨r,hr⟩
    refine ⟨MvPolynomial.C (1/7 : ℂ)*r,?_⟩
    rw [hr]
    have hc : (7 : ConePoly)*MvPolynomial.C (1/7 : ℂ)=1 := by
      rw [show (7 : ConePoly)=MvPolynomial.C (7 : ℂ) from rfl,← MvPolynomial.C_mul]
      norm_num
    calc
      F*r=(7*MvPolynomial.C (1/7 : ℂ))*F*r := by rw [hc]; ring
      _=7*F*(MvPolynomial.C (1/7 : ℂ)*r) := by ring

def newConeEvaluation : ConePoly →+* RadialField :=
  newConeRingMap.comp (CrossedMonicHypersurface.projection coneEquation)
lemma newConeEvaluation_kernel (P : ConePoly) : newConeEvaluation P=0 ↔
    CrossedMonicHypersurface.equation coneEquation∣P := by
  change newConeRingMap (CrossedMonicHypersurface.projection coneEquation P)=0 ↔ _
  constructor
  · intro h
    apply (CrossedMonicHypersurface.projection_kernel coneEquation P).mp
    apply newConeRingMap_injective
    simpa only [map_zero] using h
  · intro h
    rw [(CrossedMonicHypersurface.projection_kernel coneEquation P).mpr h,map_zero]
lemma cone_common_kernel (P : ConePoly) : SplitCompanionPoleTwo.projectionT true P=0 ↔
    newConeEvaluation P=0 := by
  rw [SplitCompanionPoleTwo.projectionT_kernel,cone_hypersurface_eq,seven_scaled_dvd,newConeEvaluation_kernel]

def coneRingMap : SplitCompanionDomain.CoordinateRing true →+* RadialField :=
  SplitThetaFactor.descend (SplitCompanionPoleTwo.projectionT true) newConeEvaluation
    (SplitCompanionPoleTwo.projectionT_surjective true) (fun P => (cone_common_kernel P).mp)
lemma coneRingMap_injective : Function.Injective coneRingMap :=
  SplitThetaFactor.descend_injective (SplitCompanionPoleTwo.projectionT true) newConeEvaluation
    (SplitCompanionPoleTwo.projectionT_surjective true) (fun P => (cone_common_kernel P).mp)
    (fun P => (cone_common_kernel P).mpr)
lemma coneRingMap_projection (P : ConePoly) : coneRingMap (SplitCompanionPoleTwo.projectionT true P)=
    newConeEvaluation P := SplitThetaFactor.descend_apply _ _ _ _ P

def coneFieldMap : SplitCompanionDomain.FunctionField true →+* RadialField :=
  IsFractionRing.lift coneRingMap_injective
@[simp] lemma coneFieldMap_ring (r : SplitCompanionDomain.CoordinateRing true) :
    coneFieldMap (algebraMap (SplitCompanionDomain.CoordinateRing true)
      (SplitCompanionDomain.FunctionField true) r)=coneRingMap r :=
  IsFractionRing.lift_algebraMap coneRingMap_injective r
lemma coneFieldMap_residue (P : ConePoly) :
    coneFieldMap (SplitCompanionPoleTwo.residueMapT true P)=newConeEvaluation P := by
  change coneFieldMap (algebraMap (SplitCompanionDomain.CoordinateRing true)
    (SplitCompanionDomain.FunctionField true) (SplitCompanionPoleTwo.projectionT true P))=_
  rw [coneFieldMap_ring,coneRingMap_projection]

lemma newConeEvaluation_X_zero : newConeEvaluation (MvPolynomial.X 0)=RatFunc.X^2*RatFunc.C normal := by
  change AdjoinRoot.lift (f:=coneEquation) coneCoefficientMap (RatFunc.X^2*RatFunc.C normal) cone_root
    (AdjoinRoot.mk coneEquation (MvPolynomial.finSuccEquiv ℂ 4 (MvPolynomial.X 0)))=_
  rw [MvPolynomial.finSuccEquiv_X_zero]
  change newConeRingMap (AdjoinRoot.root coneEquation)=_
  exact AdjoinRoot.lift_root cone_root
lemma newConeEvaluation_X_succ (i : Fin 4) : newConeEvaluation (MvPolynomial.X i.succ)=
    SplitThetaRadial.independentCoordinates coordinate i := by
  change AdjoinRoot.lift (f:=coneEquation) coneCoefficientMap (RatFunc.X^2*RatFunc.C normal) cone_root
    (AdjoinRoot.mk coneEquation (MvPolynomial.finSuccEquiv ℂ 4 (MvPolynomial.X i.succ)))=_
  rw [MvPolynomial.finSuccEquiv_X_succ]
  change newConeRingMap (AdjoinRoot.of coneEquation (MvPolynomial.X i))=_
  rw [newConeRingMap,AdjoinRoot.lift_of,coneCoefficientMap_X]
lemma newConeEvaluation_C (c : ℂ) : newConeEvaluation (MvPolynomial.C c)=algebraMap ℂ RadialField c := by
  change AdjoinRoot.lift (f:=coneEquation) coneCoefficientMap (RatFunc.X^2*RatFunc.C normal) cone_root
    (AdjoinRoot.mk coneEquation (MvPolynomial.finSuccEquiv ℂ 4 (MvPolynomial.C c)))=_
  rw [show (MvPolynomial.finSuccEquiv ℂ 4) (MvPolynomial.C c)=C (MvPolynomial.C c)
    from (MvPolynomial.finSuccEquiv ℂ 4).commutes c]
  change newConeRingMap (AdjoinRoot.of coneEquation (MvPolynomial.C c))=_
  rw [newConeRingMap,AdjoinRoot.lift_of,coneCoefficientMap_C]
end SplitFCompanion

#print axioms SplitFCompanion.coneFieldMap_residue

namespace SplitFCompanion
open Polynomial HoldoutConstruction
local instance : Algebra ℤ RadialField := Ring.toIntAlgebra _
local instance : Algebra ℤ (SplitCompanionDomain.FunctionField true) := Ring.toIntAlgebra _

lemma residueMapT_C (c : ℂ) : SplitCompanionPoleTwo.residueMapT true (MvPolynomial.C c)=
    algebraMap ℂ (SplitCompanionDomain.FunctionField true) c := by
  rw [SplitCompanionPoleTwo.residueMapT_old,MvPolynomial.rename_C,CrossedMonicHypersurface.residueMap_C]
lemma coneFieldMap_base (c : ℂ) : coneFieldMap
    (algebraMap ℂ (SplitCompanionDomain.FunctionField true) c)=algebraMap ℂ RadialField c := by
  rw [← residueMapT_C,coneFieldMap_residue,newConeEvaluation_C]

def radialDerivation (i : Fin 4) : Derivation ℤ RadialField RadialField :=
  SplitThetaRadial.coneDerivations tangent coordinate i
lemma radialDerivation_base (i : Fin 4) (c : ℂ) :
    radialDerivation i (algebraMap ℂ RadialField c)=0 := by
  change radialDerivation i (RatFunc.C (algebraMap ℂ AffineField c))=0
  exact SplitThetaRadial.coneDerivations_constant _ _ _ (fun j => tangent_base j c) i
lemma cone_tangent_parameter (i j : Fin 4) : SplitCompanionPoleTwo.tangentT true i
    (SplitCompanionPoleTwo.residueMapT true (MvPolynomial.X j.succ))=if j=i then 1 else 0 := by
  rw [SplitCompanionPoleTwo.tangentT_apply,integerPartial_X_of_ne 0 j.succ (Fin.succ_ne_zero j)]
  simp only [map_zero,mul_zero,sub_zero]
  by_cases h : j=i
  · subst j; simp
  · have hs : j.succ≠i.succ := fun he => h (Fin.succ_injective _ he)
    simp [integerPartial_X_of_ne _ _ hs,h]
lemma cone_tangent_base (i : Fin 4) (c : ℂ) : SplitCompanionPoleTwo.tangentT true i
    (algebraMap ℂ (SplitCompanionDomain.FunctionField true) c)=0 := by
  rw [← residueMapT_C,SplitCompanionPoleTwo.tangentT_apply]
  simp only [integerPartial_C,map_zero,mul_zero,sub_self]
lemma radialDerivation_compatible (i : Fin 4) (z : SplitCompanionDomain.FunctionField true) :
    radialDerivation i (coneFieldMap z)=coneFieldMap (SplitCompanionPoleTwo.tangentT true i z) := by
  apply CrossedImplicitIntertwining.quotient_fraction_intertwines
    (SplitCompanionPoleTwo.projectionT true) (SplitCompanionPoleTwo.projectionT_surjective true) coneFieldMap
    (SplitCompanionPoleTwo.hypersurfaceT true)
    ((SplitCompanionPoleTwo.residueMapT_kernel true _).mpr (dvd_refl _))
    (SplitCompanionPoleTwo.normal_ne_zero true) (SplitCompanionPoleTwo.tangentT true i) (radialDerivation i)
  · intro c
    change SplitCompanionPoleTwo.tangentT true i
      (SplitCompanionPoleTwo.residueMapT true (MvPolynomial.C c))=0
    rw [residueMapT_C,cone_tangent_base]
  · intro c
    change radialDerivation i (coneFieldMap (SplitCompanionPoleTwo.residueMapT true (MvPolynomial.C c)))=0
    rw [residueMapT_C,coneFieldMap_base,radialDerivation_base]
  · intro j
    change radialDerivation i (coneFieldMap (SplitCompanionPoleTwo.residueMapT true (MvPolynomial.X j.succ)))=
      coneFieldMap (SplitCompanionPoleTwo.tangentT true i
        (SplitCompanionPoleTwo.residueMapT true (MvPolynomial.X j.succ)))
    rw [cone_tangent_parameter,coneFieldMap_residue,newConeEvaluation_X_succ,radialDerivation,
      SplitThetaRadial.coneDerivations_coordinate tangent coordinate tangent_coordinate]
    split_ifs <;> simp

lemma coneFieldMap_coordinate (j : Fin 5) :
    coneFieldMap (SplitCompanionPoleTwo.residueMapT true (MvPolynomial.X j))=
      ![RatFunc.X^2*RatFunc.C normal,RatFunc.X*RatFunc.C (coordinate 0),
        RatFunc.X*RatFunc.C (coordinate 1),RatFunc.X,RatFunc.X^2*RatFunc.C (coordinate 2)] j := by
  rw [coneFieldMap_residue]
  refine Fin.cases newConeEvaluation_X_zero (fun i => ?_) j
  rw [newConeEvaluation_X_succ]
  fin_cases i <;> rfl

/-- The sole remaining input is the actual geometric q2 cone primitive,
expressed after its normal-density reduction. -/
theorem affine_residue_of_cone
    (hex : ∃ w : Fin 4 → SplitCompanionDomain.FunctionField true,
      residueDivergence (SplitCompanionPoleTwo.tangentT true)
        (SplitCompanionPoleTwo.residueMapT true
          (integerPartial 0 (SplitCompanionPoleTwo.hypersurfaceT true))) w=
      -2*(SplitCompanionPoleTwo.residueMapT true (MvPolynomial.X 1))^4*
        (SplitCompanionPoleTwo.residueMapT true (MvPolynomial.X 2))^3*
        SplitCompanionPoleTwo.residueMapT true (MvPolynomial.X 4)/
          (9*(SplitCompanionPoleTwo.residueMapT true (MvPolynomial.X 0))^5)) :
    ∃ w : Fin 3 → AffineField,residueDivergence tangent (21*normal^2) w=affineDensity := by
  obtain ⟨w,hw⟩ := hex
  have hm := residueDivergence_map coneFieldMap (SplitCompanionPoleTwo.tangentT true) radialDerivation
    radialDerivation_compatible
    (SplitCompanionPoleTwo.residueMapT true (integerPartial 0 (SplitCompanionPoleTwo.hypersurfaceT true))) w
  rw [hw] at hm
  have hnormal : coneFieldMap (SplitCompanionPoleTwo.residueMapT true
      (integerPartial 0 (SplitCompanionPoleTwo.hypersurfaceT true)))=
        RatFunc.X^4*RatFunc.C (21*normal^2) := by
    simp only [SplitCompanionPoleTwo.normal_polynomial,map_mul,map_pow,map_ofNat,coneFieldMap_coordinate]
    change (21 : RadialField)*(RatFunc.X^2*RatFunc.C normal)^2=_
    try simp only [map_mul,map_pow,map_ofNat]
    ring
  rw [hnormal] at hm
  have hsource : coneFieldMap
      (-2*(SplitCompanionPoleTwo.residueMapT true (MvPolynomial.X 1))^4*
        (SplitCompanionPoleTwo.residueMapT true (MvPolynomial.X 2))^3*
        SplitCompanionPoleTwo.residueMapT true (MvPolynomial.X 4)/
          (9*(SplitCompanionPoleTwo.residueMapT true (MvPolynomial.X 0))^5))=
        RatFunc.C affineDensity/RatFunc.X := by
    simp only [map_div₀,map_neg,map_mul,map_pow,map_ofNat,coneFieldMap_coordinate]
    change -2*(RatFunc.X*RatFunc.C (coordinate 0))^4*(RatFunc.X*RatFunc.C (coordinate 1))^3*
      (RatFunc.X^2*RatFunc.C (coordinate 2))/(9*(RatFunc.X^2*RatFunc.C normal)^5)=_
    simp only [affineDensity,map_div₀,map_neg,map_mul,map_pow,map_ofNat]
    have ht : (RatFunc.C normal : RadialField)≠0 := by
      simpa only [map_zero] using RatFunc.C_injective.ne normal_ne_zero
    field_simp [CrossedRationalResidue.X_ne_zero,ht]
  rw [hsource] at hm
  exact SplitThetaRadial.residue_solution_descends_radial tangent coordinate
    (fun i => by simpa using tangent_coordinate i i) (21*normal^2) clearNormal_ne_zero _
    (fun i => coneFieldMap (w i)) hm
end SplitFCompanion

#print axioms SplitFCompanion.affine_residue_of_cone

namespace SplitFCompanion
open HoldoutConstruction
local instance : Algebra ℤ (SplitCompanionDomain.FunctionField true) := Ring.toIntAlgebra _
/-- The exact single geometric input consumed by the first companion. -/
def ConeDensityPrimitive : Prop :=
  ∃ w : Fin 4 → SplitCompanionDomain.FunctionField true,
    residueDivergence (SplitCompanionPoleTwo.tangentT true)
      (SplitCompanionPoleTwo.residueMapT true
        (integerPartial 0 (SplitCompanionPoleTwo.hypersurfaceT true))) w=
    -2*(SplitCompanionPoleTwo.residueMapT true (MvPolynomial.X 1))^4*
      (SplitCompanionPoleTwo.residueMapT true (MvPolynomial.X 2))^3*
      SplitCompanionPoleTwo.residueMapT true (MvPolynomial.X 4)/
        (9*(SplitCompanionPoleTwo.residueMapT true (MvPolynomial.X 0))^5)
end SplitFCompanion
