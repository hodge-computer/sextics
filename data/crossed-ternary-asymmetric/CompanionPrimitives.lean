import HodgeComputer.Constructions.EllipticCompanions.CompanionAlgebra
import HodgeComputer.Constructions.EllipticCompanions.Coordinates
import Proposal.MovingConic
import HodgeComputer.Constructions.HoldoutCover.ResidueClearing
import HodgeComputer.Constructions.HoldoutCover.ResiduePiolaPullback
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic

/- Prepared with OpenAI Codex assistance for contributor 1337isnot1337.
See solution.md for the construction, provenance, and prior-work credit. -/

/- Source component: FanoRadialSources. -/
section

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace CrossedFanoRadial
open HoldoutConstruction CrossedRadialResidue CrossedConicIncidence
open scoped BigOperators
local instance : Algebra ℤ CrossedFano.FunctionField := Ring.toIntAlgebra _
local instance : Algebra ℤ AffineField := Ring.toIntAlgebra _
local instance : Algebra ℤ RadialField := Ring.toIntAlgebra _

@[simp] lemma radial_C_five : RatFunc.C (5 : AffineField)=(5 : RadialField) := map_natCast _ 5
@[simp] lemma radial_C_seven : RatFunc.C (7 : AffineField)=(7 : RadialField) := map_natCast _ 7
@[simp] lemma radial_C_ten : RatFunc.C (10 : AffineField)=(10 : RadialField) := map_natCast _ 10
@[simp] lemma radial_C_42 : RatFunc.C (42 : AffineField)=(42 : RadialField) := map_natCast _ 42
@[simp] lemma radial_C_200 : RatFunc.C (200 : AffineField)=(200 : RadialField) := map_natCast _ 200
@[simp] lemma radial_C_210 : RatFunc.C (210 : AffineField)=(210 : RadialField) := map_natCast _ 210

def clearNormal : AffineField := gradient
  ![CrossedFanoAffine.coordinate 0,CrossedFanoAffine.normal,1,
    CrossedFanoAffine.coordinate 1,CrossedFanoAffine.coordinate 2] 1

lemma coneEvaluation_normal :
    coneEvaluation (MvPolynomial.pderiv 0 CrossedFano.hypersurface)=
      RatFunc.X^5*RatFunc.C clearNormal := by
  have hp : MvPolynomial.pderiv 0 CrossedFano.hypersurface=
      42*MvPolynomial.X 0^5+5*(MvPolynomial.X 1^5+MvPolynomial.X 1^3*MvPolynomial.X 2^2+
        MvPolynomial.X 1*MvPolynomial.X 2^4+10*MvPolynomial.X 1*MvPolynomial.X 0^4) := by
    rw [← integerPartial_apply,CrossedFano.hypersurface_partial]
    rfl
  rw [hp]
  have h42 : coneEvaluation (42 : MvPolynomial (Fin 5) ℂ)=(42 : RadialField) := map_natCast _ 42
  have h5 : coneEvaluation (5 : MvPolynomial (Fin 5) ℂ)=(5 : RadialField) := map_natCast _ 5
  have h10 : coneEvaluation (10 : MvPolynomial (Fin 5) ℂ)=(10 : RadialField) := map_natCast _ 10
  simp only [map_add,map_mul,map_pow,h42,h5,h10,coneEvaluation_X]
  simp [gradient,coneCoordinate,clearNormal]
  ring

lemma clearNormal_ne_zero : clearNormal≠0 := by
  have h := (_root_.map_ne_zero coneFieldMap).mpr CrossedFano.normal_ne_zero
  change coneEvaluation (MvPolynomial.pderiv 0 CrossedFano.hypersurface)≠0 at h
  rw [coneEvaluation_normal] at h
  intro hz
  apply h
  rw [hz,map_zero,mul_zero]

def clearSecondNormal : AffineField :=
  210*CrossedFanoAffine.normal^4+200*CrossedFanoAffine.coordinate 0*CrossedFanoAffine.normal^3

lemma hessian_polynomial : MvPolynomial.pderiv (R:=ℂ) (0 : Fin 5)
    (MvPolynomial.pderiv 0 CrossedFano.hypersurface)=
    210*MvPolynomial.X 0^4+200*MvPolynomial.X 1*MvPolynomial.X 0^3 := by
  change integerPartial 0 (integerPartial 0 CrossedFano.hypersurface)=_
  rw [CrossedFano.hypersurface_partial]
  have h42 : integerPartial (R:=ℂ) (0 : Fin 5) (42 : MvPolynomial (Fin 5) ℂ)=0 :=
    (integerPartial 0).map_natCast 42
  have h5 : integerPartial (R:=ℂ) (0 : Fin 5) (5 : MvPolynomial (Fin 5) ℂ)=0 :=
    (integerPartial 0).map_natCast 5
  have h10 : integerPartial (R:=ℂ) (0 : Fin 5) (10 : MvPolynomial (Fin 5) ℂ)=0 :=
    (integerPartial 0).map_natCast 10
  simp only [integerPartial_apply] at h42 h5 h10
  simp [gradient,Derivation.leibniz,Derivation.leibniz_pow,smul_eq_mul,h42,h5,h10]
  ring

lemma coneEvaluation_hessian : coneEvaluation (MvPolynomial.pderiv 0
    (MvPolynomial.pderiv 0 CrossedFano.hypersurface))=RatFunc.X^4*RatFunc.C clearSecondNormal := by
  rw [hessian_polynomial]
  have h210 : coneEvaluation (210 : MvPolynomial (Fin 5) ℂ)=(210 : RadialField) := map_natCast _ 210
  have h200 : coneEvaluation (200 : MvPolynomial (Fin 5) ℂ)=(200 : RadialField) := map_natCast _ 200
  simp only [map_add,map_mul,map_pow,h210,h200,coneEvaluation_X]
  simp [coneCoordinate,clearSecondNormal]
  ring

def firstSource : MvPolynomial (Fin 5) ℂ := 7*MvPolynomial.X 1^4*MvPolynomial.X 0
def secondSource : MvPolynomial (Fin 5) ℂ := 7*MvPolynomial.X 1*MvPolynomial.X 3*MvPolynomial.X 4

def affineFirstSource : AffineField :=
  7*CrossedFanoAffine.coordinate 0^4*CrossedFanoAffine.normal
def affineSecondSource : AffineField :=
  7*CrossedFanoAffine.coordinate 0*CrossedFanoAffine.coordinate 1*CrossedFanoAffine.coordinate 2

lemma firstSource_partial : MvPolynomial.pderiv 0 firstSource=7*MvPolynomial.X 1^4 := by
  have h7 : MvPolynomial.pderiv (R:=ℂ) (0 : Fin 5) (7 : MvPolynomial (Fin 5) ℂ)=0 :=
    (MvPolynomial.pderiv 0).map_natCast 7
  simp [firstSource,MvPolynomial.pderiv_mul,MvPolynomial.pderiv_pow,h7]
lemma secondSource_partial : MvPolynomial.pderiv 0 secondSource=0 := by
  have h7 : MvPolynomial.pderiv (R:=ℂ) (0 : Fin 5) (7 : MvPolynomial (Fin 5) ℂ)=0 :=
    (MvPolynomial.pderiv 0).map_natCast 7
  simp [secondSource,MvPolynomial.pderiv_mul,MvPolynomial.pderiv_pow,h7]

lemma coneEvaluation_firstSource : coneEvaluation firstSource=RatFunc.X^5*RatFunc.C affineFirstSource := by
  have h7 : coneEvaluation (7 : MvPolynomial (Fin 5) ℂ)=(7 : RadialField) := map_natCast _ 7
  simp only [firstSource,map_mul,map_pow,h7,coneEvaluation_X]
  simp [coneCoordinate,affineFirstSource]
  ring

lemma coneEvaluation_secondSource : coneEvaluation secondSource=RatFunc.X^5*RatFunc.C affineSecondSource := by
  have h7 : coneEvaluation (7 : MvPolynomial (Fin 5) ℂ)=(7 : RadialField) := map_natCast _ 7
  simp only [secondSource,map_mul,map_pow,h7,coneEvaluation_X]
  simp [coneCoordinate,affineSecondSource]
  ring

lemma coneEvaluation_firstPartial : coneEvaluation (MvPolynomial.pderiv 0 firstSource)=
    RatFunc.X^4*RatFunc.C (7*CrossedFanoAffine.coordinate 0^4) := by
  rw [firstSource_partial]
  have h7 : coneEvaluation (7 : MvPolynomial (Fin 5) ℂ)=(7 : RadialField) := map_natCast _ 7
  simp only [map_mul,map_pow,h7,coneEvaluation_X]
  simp [coneCoordinate]
  ring

lemma radial_source_fraction (ρ g k A B : RadialField) (hρ : ρ≠0) (hg : g≠0) :
    -(ρ^4*B/(ρ^5*g)-(ρ^5*A)*(ρ^4*k)/(ρ^5*g)^2)=
      (-(B/g-A*k/g^2))/ρ := by
  field_simp <;> ring

lemma cone_residue_solution_radial (A : MvPolynomial (Fin 5) ℂ) :
    ∃ w : Fin 4 → RadialField,
      residueDivergence radialDerivation (RatFunc.X^5*RatFunc.C clearNormal) w=
        -(coneEvaluation (MvPolynomial.pderiv 0 A)/(RatFunc.X^5*RatFunc.C clearNormal)-
          coneEvaluation A*(RatFunc.X^4*RatFunc.C clearSecondNormal)/
            (RatFunc.X^5*RatFunc.C clearNormal)^2) := by
  obtain ⟨w,hw⟩ := CrossedFixedConic.companion_residue_solution A
  refine ⟨fun i => coneFieldMap (w i),?_⟩
  have hm := residueDivergence_map coneFieldMap CrossedFano.tangent radialDerivation
    radialDerivation_compatible (CrossedFano.residueMap (MvPolynomial.pderiv 0 CrossedFano.hypersurface)) w
  rw [hw] at hm
  simp only [map_neg,map_sub,map_div₀,map_mul,map_pow] at hm
  change residueDivergence radialDerivation
    (coneEvaluation (MvPolynomial.pderiv 0 CrossedFano.hypersurface)) (fun i => coneFieldMap (w i))=
      -(coneEvaluation (MvPolynomial.pderiv 0 A)/coneEvaluation (MvPolynomial.pderiv 0 CrossedFano.hypersurface)-
        coneEvaluation A*coneEvaluation (MvPolynomial.pderiv 0 (MvPolynomial.pderiv 0 CrossedFano.hypersurface))/
          (coneEvaluation (MvPolynomial.pderiv 0 CrossedFano.hypersurface))^2) at hm
  rw [coneEvaluation_normal,coneEvaluation_hessian] at hm
  exact hm

theorem affine_first_residue_solution :
    ∃ v : Fin 3 → AffineField,
      residueDivergence CrossedFanoAffine.tangent clearNormal v=
        -((7*CrossedFanoAffine.coordinate 0^4)/clearNormal-
          affineFirstSource*clearSecondNormal/clearNormal^2) := by
  obtain ⟨w,hw⟩ := cone_residue_solution_radial firstSource
  rw [coneEvaluation_firstSource,coneEvaluation_firstPartial] at hw
  have hρ : (RatFunc.X : RadialField)≠0 := CrossedRationalResidue.X_ne_zero
  have hg : (RatFunc.C clearNormal : RadialField)≠0 := by
    simpa only [map_zero] using RatFunc.C_injective.ne clearNormal_ne_zero
  rw [radial_source_fraction _ _ _ _ _ hρ hg] at hw
  have hr : -(RatFunc.C (7*CrossedFanoAffine.coordinate 0^4)/RatFunc.C clearNormal-
      RatFunc.C affineFirstSource*RatFunc.C clearSecondNormal/(RatFunc.C clearNormal)^2)=
      RatFunc.C (-((7*CrossedFanoAffine.coordinate 0^4)/clearNormal-
        affineFirstSource*clearSecondNormal/clearNormal^2)) := by
    simp
  rw [hr] at hw
  exact residue_solution_descends_radial CrossedFanoAffine.tangent CrossedFanoAffine.coordinate
    (fun i => by simpa using CrossedFanoAffine.tangent_coordinate i i)
    clearNormal clearNormal_ne_zero _ w hw

theorem affine_second_residue_solution :
    ∃ v : Fin 3 → AffineField,
      residueDivergence CrossedFanoAffine.tangent clearNormal v=
        affineSecondSource*clearSecondNormal/clearNormal^2 := by
  obtain ⟨w,hw⟩ := cone_residue_solution_radial secondSource
  rw [coneEvaluation_secondSource,secondSource_partial,map_zero] at hw
  have hρ : (RatFunc.X : RadialField)≠0 := CrossedRationalResidue.X_ne_zero
  have hg : (RatFunc.C clearNormal : RadialField)≠0 := by
    simpa only [map_zero] using RatFunc.C_injective.ne clearNormal_ne_zero
  have hs : -(0/(RatFunc.X^5*RatFunc.C clearNormal)-
      (RatFunc.X^5*RatFunc.C affineSecondSource)*(RatFunc.X^4*RatFunc.C clearSecondNormal)/
        (RatFunc.X^5*RatFunc.C clearNormal)^2)=
      RatFunc.C (affineSecondSource*clearSecondNormal/clearNormal^2)/RatFunc.X := by
    simp only [map_div₀,map_mul,map_pow]
    field_simp
    ring
  rw [hs] at hw
  exact residue_solution_descends_radial CrossedFanoAffine.tangent CrossedFanoAffine.coordinate
    (fun i => by simpa using CrossedFanoAffine.tangent_coordinate i i)
    clearNormal clearNormal_ne_zero _ w hw

end CrossedFanoRadial
end
end

/- Source component: FanoAffinePrimitiveData. -/
section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000
namespace CrossedFanoAffineData
open Polynomial HoldoutConstruction CrossedConicIncidence
open scoped BigOperators
abbrev Poly := MvPolynomial (Fin 4) ℂ
abbrev K := CrossedFanoAffine.FunctionField
local instance : Algebra ℤ K := Ring.toIntAlgebra _

def equation : Poly := H ![MvPolynomial.X 1,MvPolynomial.X 0,1,MvPolynomial.X 2,MvPolynomial.X 3]
def evaluation : Poly →+* K := MvPolynomial.eval₂Hom (algebraMap ℂ K)
  ![CrossedFanoAffine.normal,CrossedFanoAffine.coordinate 0,CrossedFanoAffine.coordinate 1,
    CrossedFanoAffine.coordinate 2]

@[simp] lemma evaluation_C (c : ℂ) : evaluation (MvPolynomial.C c)=algebraMap ℂ K c :=
  MvPolynomial.eval₂Hom_C _ _ c
@[simp] lemma evaluation_X_zero : evaluation (MvPolynomial.X 0)=CrossedFanoAffine.normal := by
  rw [evaluation,MvPolynomial.eval₂Hom_X']
  rfl
lemma evaluation_X_succ (j : Fin 3) : evaluation (MvPolynomial.X j.succ)=CrossedFanoAffine.coordinate j := by
  rw [evaluation,MvPolynomial.eval₂Hom_X']
  fin_cases j <;> rfl

@[simp] lemma evaluation_X_one : evaluation (MvPolynomial.X 1)=CrossedFanoAffine.coordinate 0 :=
  evaluation_X_succ 0
@[simp] lemma evaluation_X_two : evaluation (MvPolynomial.X 2)=CrossedFanoAffine.coordinate 1 :=
  evaluation_X_succ 1
@[simp] lemma evaluation_X_three : evaluation (MvPolynomial.X 3)=CrossedFanoAffine.coordinate 2 :=
  evaluation_X_succ 2

lemma evaluation_residue : evaluation=CrossedFanoAffine.residueMap := by
  apply MvPolynomial.ringHom_ext
  · intro c
    rw [evaluation_C]
    exact (CrossedMonicHypersurface.residueMap_C CrossedFanoAffine.equation c).symm
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [evaluation_X_zero]
      exact (CrossedMonicHypersurface.residueMap_X_zero CrossedFanoAffine.equation).symm
    · rw [evaluation_X_succ,CrossedFanoAffine.residueMap_coordinate]

lemma equation_zero : evaluation equation=0 := by
  rw [equation,H_map]
  have hv : (fun i => evaluation
      (![MvPolynomial.X 1,MvPolynomial.X 0,1,MvPolynomial.X 2,MvPolynomial.X 3] i))=
      ![CrossedFanoAffine.coordinate 0,CrossedFanoAffine.normal,1,
        CrossedFanoAffine.coordinate 1,CrossedFanoAffine.coordinate 2] := by
    funext i
    fin_cases i <;> simp [evaluation_X_succ,evaluation]
  rw [hv]
  exact CrossedFanoAffine.cleared_equation

lemma equation_partial : integerPartial 0 equation=
    42*MvPolynomial.X 0^5+5*(MvPolynomial.X 1^5+MvPolynomial.X 1^3+
      MvPolynomial.X 1+10*MvPolynomial.X 1*MvPolynomial.X 0^4) := by
  rw [equation,H_derivation]
  simp [gradient,Fin.sum_univ_succ]

lemma normal_evaluation : evaluation (integerPartial 0 equation)=CrossedFanoRadial.clearNormal := by
  rw [equation_partial]
  have h42 : evaluation (42 : Poly)=(42 : K) := map_natCast _ 42
  have h5 : evaluation (5 : Poly)=(5 : K) := map_natCast _ 5
  have h10 : evaluation (10 : Poly)=(10 : K) := map_natCast _ 10
  simp only [map_add,map_mul,map_pow,h42,h5,h10,evaluation_X_zero,evaluation_X_one]
  simp [CrossedFanoRadial.clearNormal,gradient]

lemma equation_hessian : integerPartial 0 (integerPartial 0 equation)=
    210*MvPolynomial.X 0^4+200*MvPolynomial.X 1*MvPolynomial.X 0^3 := by
  rw [equation_partial]
  have h42 : MvPolynomial.pderiv (R:=ℂ) (0 : Fin 4) (42 : Poly)=0 := (MvPolynomial.pderiv 0).map_natCast 42
  have h5 : MvPolynomial.pderiv (R:=ℂ) (0 : Fin 4) (5 : Poly)=0 := (MvPolynomial.pderiv 0).map_natCast 5
  have h10 : MvPolynomial.pderiv (R:=ℂ) (0 : Fin 4) (10 : Poly)=0 := (MvPolynomial.pderiv 0).map_natCast 10
  simp [integerPartial_apply,Derivation.leibniz,Derivation.leibniz_pow,smul_eq_mul,h42,h5,h10]
  ring

lemma hessian_evaluation : evaluation (integerPartial 0 (integerPartial 0 equation))=
    CrossedFanoRadial.clearSecondNormal := by
  rw [equation_hessian]
  have h210 : evaluation (210 : Poly)=(210 : K) := map_natCast _ 210
  have h200 : evaluation (200 : Poly)=(200 : K) := map_natCast _ 200
  simp only [map_add,map_mul,map_pow,h210,h200,evaluation_X_zero,evaluation_X_one]
  rfl

lemma tangent_formula (i : Fin 3) (p : Poly) :
    CrossedFanoAffine.tangent i (evaluation p)=evaluation (integerPartial i.succ p)-
      evaluation (integerPartial i.succ equation)/evaluation (integerPartial 0 equation)*
        evaluation (integerPartial 0 p) := by
  apply CrossedAffinePrimitiveData.tangent_formula_from_coordinates evaluation equation equation_zero
    (by change evaluation (integerPartial 0 equation)≠0
        rw [normal_evaluation]; exact CrossedFanoRadial.clearNormal_ne_zero)
    (CrossedFanoAffine.tangent i) i
  · intro c; rw [evaluation_C,CrossedFanoAffine.tangent_base]
  · intro j; rw [evaluation_X_succ]; exact CrossedFanoAffine.tangent_coordinate i j

theorem data_of_residue_solution (A : Poly) (w : Fin 3 → K)
    (hw : residueDivergence CrossedFanoAffine.tangent CrossedFanoRadial.clearNormal w=
      -(evaluation (integerPartial 0 A)/CrossedFanoRadial.clearNormal-
        evaluation A*CrossedFanoRadial.clearSecondNormal/CrossedFanoRadial.clearNormal^2)) :
    ∃ D N₀ : Poly,∃ N : Fin 3 → Poly,evaluation D≠0 ∧
      (N₀*integerPartial 0 equation+∑ i,N i*integerPartial i.succ equation=A*D) ∧
      evaluation (residueDivNum (integerPartial 0) (fun i : Fin 3 => integerPartial i.succ) D N₀ N)=0 := by
  apply CrossedAffinePrimitiveData.ambient_data evaluation (integerPartial 0)
    (fun i : Fin 3 => integerPartial i.succ) CrossedFanoAffine.tangent equation A w
  · rw [normal_evaluation]; exact CrossedFanoRadial.clearNormal_ne_zero
  · intro i; exact integerPartial_commute i.succ 0 equation
  · exact tangent_formula
  · rw [evaluation_residue]
    exact residue_common_representatives
      (CrossedMonicHypersurface.projection CrossedFanoAffine.equation)
      (CrossedMonicHypersurface.projection_surjective CrossedFanoAffine.equation) w
  · rw [normal_evaluation,hessian_evaluation]
    exact hw

def firstSource : Poly := 7*MvPolynomial.X 1^4*MvPolynomial.X 0
def secondSource : Poly := 7*MvPolynomial.X 1*MvPolynomial.X 2*MvPolynomial.X 3

lemma firstSource_value : evaluation firstSource=CrossedFanoRadial.affineFirstSource := by
  have h7 : evaluation (7 : Poly)=(7 : K) := map_natCast _ 7
  simp only [firstSource,map_mul,map_pow,h7,evaluation_X_zero,evaluation_X_one]
  rfl
lemma secondSource_value : evaluation secondSource=CrossedFanoRadial.affineSecondSource := by
  have h7 : evaluation (7 : Poly)=(7 : K) := map_natCast _ 7
  simp only [secondSource,map_mul,h7,evaluation_X_one,evaluation_X_two,evaluation_X_three]
  rfl

lemma firstSource_partial_value : evaluation (integerPartial 0 firstSource)=
    7*CrossedFanoAffine.coordinate 0^4 := by
  have h7 : MvPolynomial.pderiv (R:=ℂ) (0 : Fin 4) (7 : Poly)=0 := (MvPolynomial.pderiv 0).map_natCast 7
  have hp : integerPartial 0 firstSource=7*MvPolynomial.X 1^4 := by
    simp [firstSource,integerPartial_apply,h7]
  have he7 : evaluation (7 : Poly)=(7 : K) := map_natCast _ 7
  rw [hp,map_mul,map_pow,he7,evaluation_X_one]
lemma secondSource_partial_value : evaluation (integerPartial 0 secondSource)=0 := by
  have h7 : MvPolynomial.pderiv (R:=ℂ) (0 : Fin 4) (7 : Poly)=0 := (MvPolynomial.pderiv 0).map_natCast 7
  have hp : integerPartial 0 secondSource=0 := by simp [secondSource,integerPartial_apply,h7]
  rw [hp,map_zero]

theorem firstSource_data : ∃ D N₀ : Poly,∃ N : Fin 3 → Poly,evaluation D≠0 ∧
    (N₀*integerPartial 0 equation+∑ i,N i*integerPartial i.succ equation=firstSource*D) ∧
    evaluation (residueDivNum (integerPartial 0) (fun i : Fin 3 => integerPartial i.succ) D N₀ N)=0 := by
  obtain ⟨w,hw⟩ := CrossedFanoRadial.affine_first_residue_solution
  apply data_of_residue_solution firstSource w
  rw [firstSource_partial_value,firstSource_value]
  exact hw

theorem secondSource_data : ∃ D N₀ : Poly,∃ N : Fin 3 → Poly,evaluation D≠0 ∧
    (N₀*integerPartial 0 equation+∑ i,N i*integerPartial i.succ equation=secondSource*D) ∧
    evaluation (residueDivNum (integerPartial 0) (fun i : Fin 3 => integerPartial i.succ) D N₀ N)=0 := by
  obtain ⟨w,hw⟩ := CrossedFanoRadial.affine_second_residue_solution
  apply data_of_residue_solution secondSource w
  rw [secondSource_partial_value,secondSource_value,zero_div,zero_sub,neg_neg]
  exact hw

end CrossedFanoAffineData
end
end

/- Source component: FanoCubicProjection. -/
section

noncomputable section
namespace CrossedFanoCubic
open HoldoutConstruction
abbrev Poly := MvPolynomial (Fin 4) ℂ

def projection : Poly →+* CoordinateRing := (AdjoinRoot.mk equation).comp
  ((MvPolynomial.finSuccEquiv ℂ 3).toRingHom.comp (MvPolynomial.rename reverse).toRingHom)

lemma old_projection_kernel (p : Poly) :
    CrossedMonicHypersurface.projection CrossedFanoAffine.equation p=0 ↔ affineEquation ∣ p := by
  change AdjoinRoot.mk CrossedFanoAffine.equation (MvPolynomial.finSuccEquiv ℂ 3 p)=0 ↔ _
  rw [AdjoinRoot.mk_eq_zero,← old_univariate]
  exact map_dvd_iff (MvPolynomial.finSuccEquiv ℂ 3)

lemma projection_kernel (p : Poly) : projection p=0 ↔ affineEquation ∣ p := by
  change AdjoinRoot.mk equation (MvPolynomial.finSuccEquiv ℂ 3
    (MvPolynomial.rename reverse p))=0 ↔ _
  rw [AdjoinRoot.mk_eq_zero,← new_univariate]
  rw [map_dvd_iff (MvPolynomial.finSuccEquiv ℂ 3)]
  exact map_dvd_iff (MvPolynomial.renameEquiv (R:=ℂ) reverse)

lemma nonzero_of_old_evaluation (D : Poly) (hD : CrossedFanoAffineData.evaluation D≠0) :
    projection D≠0 := by
  intro h
  apply hD
  rw [CrossedFanoAffineData.evaluation_residue]
  change algebraMap CrossedFanoAffine.CoordinateRing CrossedFanoAffine.FunctionField
    (CrossedMonicHypersurface.projection CrossedFanoAffine.equation D)=0
  rw [(old_projection_kernel D).mpr ((projection_kernel D).mp h),map_zero]

lemma zero_of_old_evaluation (p : Poly) (hp : CrossedFanoAffineData.evaluation p=0) :
    projection p=0 := by
  rw [CrossedFanoAffineData.evaluation_residue] at hp
  change algebraMap CrossedFanoAffine.CoordinateRing CrossedFanoAffine.FunctionField
    (CrossedMonicHypersurface.projection CrossedFanoAffine.equation p)=0 at hp
  have hπ : CrossedMonicHypersurface.projection CrossedFanoAffine.equation p=0 := by
    apply IsFractionRing.injective CrossedFanoAffine.CoordinateRing CrossedFanoAffine.FunctionField
    simpa only [map_zero] using hp
  exact (projection_kernel p).mpr ((old_projection_kernel p).mp hπ)

end CrossedFanoCubic
end
end

/- Source component: FanoEllipticEmbedding. -/
section

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace CrossedFanoElliptic
open Polynomial HoldoutConstruction CrossedElliptic
variable {K : Type*} [Field K] [CharZero K]

def basePolynomial : MvPolynomial (Fin 2) ℂ :=
  MvPolynomial.X 0^6+MvPolynomial.X 1^6+1+
  MvPolynomial.C (5/7 : ℂ)*(MvPolynomial.X 0^5*MvPolynomial.X 1+
    MvPolynomial.X 0^3*MvPolynomial.X 1+MvPolynomial.X 0*MvPolynomial.X 1+
    2*MvPolynomial.X 0*MvPolynomial.X 1^5)

def coefficientMap (φ : MvPolynomial (Fin 2) ℂ →+* K) (u : K) : CrossedFanoCubic.Coeff →+* E K :=
  (Polynomial.eval₂RingHom (algebraMap K (E K)) (algebraMap K (E K) u*a (K:=K))).comp
    ((Polynomial.mapRingHom φ).comp (MvPolynomial.finSuccEquiv ℂ 2).toRingHom)

lemma coefficientMap_injective (φ : MvPolynomial (Fin 2) ℂ →+* K) (hφ : Function.Injective φ)
    (u : K) (hu : u≠0) : Function.Injective (coefficientMap φ u) :=
  (transcendental_iff_injective.mp (fermat_scaled_a_transcendental u hu)).comp
    ((Polynomial.map_injective φ hφ).comp (MvPolynomial.finSuccEquiv ℂ 2).injective)

lemma base_univariate : MvPolynomial.finSuccEquiv ℂ 2 CrossedFanoCubic.base=C basePolynomial := by
  have hv : (Fin.cases (Polynomial.X : Polynomial (MvPolynomial (Fin 2) ℂ))
      (fun j => C (MvPolynomial.X j)))=![X,C (MvPolynomial.X 0),C (MvPolynomial.X 1)] := by
    funext j; fin_cases j <;> rfl
  have hc2 : Polynomial.C (2 : MvPolynomial (Fin 2) ℂ)=(2 : Polynomial (MvPolynomial (Fin 2) ℂ)) := map_natCast _ 2
  simp [CrossedFanoCubic.base,basePolynomial,MvPolynomial.finSuccEquiv_apply,hv,hc2]

lemma coefficientMap_base (φ : MvPolynomial (Fin 2) ℂ →+* K) (u : K) :
    coefficientMap φ u CrossedFanoCubic.base=algebraMap K (E K) (φ basePolynomial) := by
  change Polynomial.eval₂ (algebraMap K (E K)) (algebraMap K (E K) u*a (K:=K))
    ((MvPolynomial.finSuccEquiv ℂ 2 CrossedFanoCubic.base).map φ)=_
  rw [base_univariate,Polynomial.map_C,Polynomial.eval₂_C]

lemma coefficientMap_S (φ : MvPolynomial (Fin 2) ℂ →+* K) (u : K) :
    coefficientMap φ u (MvPolynomial.X 0)=algebraMap K (E K) u*a (K:=K) := by
  change Polynomial.eval₂ (algebraMap K (E K)) (algebraMap K (E K) u*a (K:=K))
    ((MvPolynomial.finSuccEquiv ℂ 2 (MvPolynomial.X 0)).map φ)=_
  rw [MvPolynomial.finSuccEquiv_X_zero,Polynomial.map_X,Polynomial.eval₂_X]

lemma coefficientMap_X_succ (φ : MvPolynomial (Fin 2) ℂ →+* K) (u : K) (i : Fin 2) :
    coefficientMap φ u (MvPolynomial.X i.succ)=algebraMap K (E K) (φ (MvPolynomial.X i)) := by
  change Polynomial.eval₂ (algebraMap K (E K)) (algebraMap K (E K) u*a (K:=K))
    ((MvPolynomial.finSuccEquiv ℂ 2 (MvPolynomial.X i.succ)).map φ)=_
  rw [MvPolynomial.finSuccEquiv_X_succ,Polynomial.map_C,Polynomial.eval₂_C]

lemma coefficientMap_C (φ : MvPolynomial (Fin 2) ℂ →+* K) (u : K) (c : ℂ) :
    coefficientMap φ u (MvPolynomial.C c)=algebraMap K (E K) (φ (MvPolynomial.C c)) := by
  change Polynomial.eval₂ (algebraMap K (E K)) (algebraMap K (E K) u*a (K:=K))
    ((MvPolynomial.finSuccEquiv ℂ 2 (MvPolynomial.C c)).map φ)=_
  rw [show MvPolynomial.finSuccEquiv ℂ 2 (MvPolynomial.C c)=C (MvPolynomial.C c)
    from (MvPolynomial.finSuccEquiv ℂ 2).commutes c,Polynomial.map_C,Polynomial.eval₂_C]

lemma equation_root (φ : MvPolynomial (Fin 2) ℂ →+* K) (u : K) (hu : u^3=φ basePolynomial) :
    CrossedFanoCubic.equation.eval₂ (coefficientMap φ u) (algebraMap K (E K) u*b (K:=K))=0 := by
  simp only [CrossedFanoCubic.equation,Polynomial.eval₂_add,Polynomial.eval₂_pow,
    Polynomial.eval₂_X,Polynomial.eval₂_C,map_add,map_pow,coefficientMap_base,coefficientMap_S]
  rw [← hu,map_pow]
  linear_combination (algebraMap K (E K) u)^3*fermat_relation (K:=K)

def ringMap (φ : MvPolynomial (Fin 2) ℂ →+* K) (u : K) (hu : u^3=φ basePolynomial) :
    CrossedFanoCubic.CoordinateRing →+* E K :=
  AdjoinRoot.lift (f:=CrossedFanoCubic.equation) (coefficientMap φ u)
    (algebraMap K (E K) u*b (K:=K)) (equation_root φ u hu)

lemma ringMap_injective (φ : MvPolynomial (Fin 2) ℂ →+* K) (hφ : Function.Injective φ)
    (u : K) (hu0 : u≠0) (hu : u^3=φ basePolynomial) : Function.Injective (ringMap φ u hu) :=
  monic_root_embedding_injective CrossedFanoCubic.equation CrossedFanoCubic.equation_monic
    CrossedFanoCubic.equation_irreducible (coefficientMap φ u) (coefficientMap_injective φ hφ u hu0)
    (algebraMap K (E K) u*b (K:=K)) (equation_root φ u hu)

def evaluation (φ : MvPolynomial (Fin 2) ℂ →+* K) (u : K) (hu : u^3=φ basePolynomial) :
    MvPolynomial (Fin 4) ℂ →+* E K := (ringMap φ u hu).comp CrossedFanoCubic.projection

lemma evaluation_univariate (φ : MvPolynomial (Fin 2) ℂ →+* K) (u : K) (hu : u^3=φ basePolynomial)
    (p : MvPolynomial (Fin 4) ℂ) : evaluation φ u hu p=
      (MvPolynomial.finSuccEquiv ℂ 3 (MvPolynomial.rename CrossedFanoCubic.reverse p)).eval₂
        (coefficientMap φ u) (algebraMap K (E K) u*b (K:=K)) := by
  rfl

lemma evaluation_C (φ : MvPolynomial (Fin 2) ℂ →+* K) (u : K) (hu : u^3=φ basePolynomial) (c : ℂ) :
    evaluation φ u hu (MvPolynomial.C c)=algebraMap K (E K) (φ (MvPolynomial.C c)) := by
  rw [evaluation_univariate,MvPolynomial.rename_C]
  rw [show MvPolynomial.finSuccEquiv ℂ 3 (MvPolynomial.C c)=C (MvPolynomial.C c)
    from (MvPolynomial.finSuccEquiv ℂ 3).commutes c,Polynomial.eval₂_C,coefficientMap_C]

lemma evaluation_X (φ : MvPolynomial (Fin 2) ℂ →+* K) (u : K) (hu : u^3=φ basePolynomial) (i : Fin 4) :
    evaluation φ u hu (MvPolynomial.X i)=
      ![algebraMap K (E K) (φ (MvPolynomial.X 1)),algebraMap K (E K) (φ (MvPolynomial.X 0)),
        algebraMap K (E K) u*a (K:=K),algebraMap K (E K) u*b (K:=K)] i := by
  have hv : (Fin.cases (Polynomial.X : Polynomial CrossedFanoCubic.Coeff)
      (fun j => C (MvPolynomial.X j)))=![X,C (MvPolynomial.X 0),C (MvPolynomial.X 1),C (MvPolynomial.X 2)] := by
    funext j; fin_cases j <;> rfl
  have hx1 := coefficientMap_X_succ φ u 0
  have hx2 := coefficientMap_X_succ φ u 1
  change coefficientMap φ u (MvPolynomial.X 1)=_ at hx1
  change coefficientMap φ u (MvPolynomial.X 2)=_ at hx2
  rw [evaluation_univariate,MvPolynomial.rename_X]
  fin_cases i <;>
    simp [CrossedFanoCubic.reverse,MvPolynomial.finSuccEquiv_apply,hv,coefficientMap_S,hx1,hx2]

lemma evaluation_denominator_nonzero (φ : MvPolynomial (Fin 2) ℂ →+* K) (hφ : Function.Injective φ)
    (u : K) (hu0 : u≠0) (hu : u^3=φ basePolynomial) (D : MvPolynomial (Fin 4) ℂ)
    (hD : CrossedFanoAffineData.evaluation D≠0) : evaluation φ u hu D≠0 := by
  have h := (ringMap_injective φ hφ u hu0 hu).ne (CrossedFanoCubic.nonzero_of_old_evaluation D hD)
  change ringMap φ u hu (CrossedFanoCubic.projection D)≠0
  simpa only [map_zero] using h

lemma evaluation_zero_of_old (φ : MvPolynomial (Fin 2) ℂ →+* K) (u : K) (hu : u^3=φ basePolynomial)
    (p : MvPolynomial (Fin 4) ℂ) (hp : CrossedFanoAffineData.evaluation p=0) : evaluation φ u hu p=0 := by
  change ringMap φ u hu (CrossedFanoCubic.projection p)=0
  rw [CrossedFanoCubic.zero_of_old_evaluation p hp,map_zero]

end CrossedFanoElliptic
end
end
