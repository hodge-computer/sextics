import Proposal.NewEliminant
import Proposal.GoodFiberCoordinates
import HodgeComputer.Constructions.FiniteAlgebra.AdjoinRootUnits
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Tactic.LinearCombination

/-! The unspecialized finite coefficient algebra.  Specialization at
(a,b,c,d)=(2,2,1,1) proves units; the actual line lives over all four parameters. -/
namespace HoldoutQ2.NewLineAlgebra
open Polynomial NewLineChart NewEliminant
noncomputable section
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

abbrev PolynomialRing := MvPolynomial (Fin 4) ℚ
def point : PolynomialRing →+* ℚ := MvPolynomial.eval₂Hom (RingHom.id ℚ) ![2,2,1,1]
abbrev Coefficients := RegularSpecialization.Coefficients point
def specialize : Coefficients →+* ℚ := RegularSpecialization.specialize point
instance : Nontrivial Coefficients := specialize.domain_nontrivial
instance : IsDomain Coefficients :=
  IsLocalization.isDomain_of_le_nonZeroDivisors
    (M := RegularSpecialization.denominators point) Coefficients (by
    intro r hr
    apply mem_nonZeroDivisors_of_ne_zero
    intro hz
    exact hr (by rw [hz, map_zero]))

def a : Coefficients := algebraMap PolynomialRing Coefficients (MvPolynomial.X 0)
def b : Coefficients := algebraMap PolynomialRing Coefficients (MvPolynomial.X 1)
def c : Coefficients := algebraMap PolynomialRing Coefficients (MvPolynomial.X 2)
def d : Coefficients := algebraMap PolynomialRing Coefficients (MvPolynomial.X 3)

@[simp] theorem specialize_a : specialize a=2 := by
  change RegularSpecialization.specialize point (algebraMap PolynomialRing Coefficients _) = _
  rw [RegularSpecialization.specialize_algebraMap]
  simp [point]
@[simp] theorem specialize_b : specialize b=2 := by
  change RegularSpecialization.specialize point (algebraMap PolynomialRing Coefficients _) = _
  rw [RegularSpecialization.specialize_algebraMap]
  simp [point]
@[simp] theorem specialize_c : specialize c=1 := by
  change RegularSpecialization.specialize point (algebraMap PolynomialRing Coefficients _) = _
  rw [RegularSpecialization.specialize_algebraMap]
  simp [point]
@[simp] theorem specialize_d : specialize d=1 := by
  change RegularSpecialization.specialize point (algebraMap PolynomialRing Coefficients _) = _
  rw [RegularSpecialization.specialize_algebraMap]
  simp [point]

theorem isUnit_d : IsUnit d := by
  apply (RegularSpecialization.isUnit_iff_specialize_ne_zero point d).mpr
  change specialize d ≠ 0
  norm_num

theorem isUnit_leading : IsUnit (729*a^11) := by
  apply (RegularSpecialization.isUnit_iff_specialize_ne_zero point _).mpr
  change specialize (729*a^11) ≠ 0
  norm_num [map_ofNat]

def P : Polynomial Coefficients := monicPolynomial a b c d
theorem P_monic : P.Monic := monicPolynomial_monic _ _ _ _
theorem P_natDegree : P.natDegree=27 := monicPolynomial_natDegree _ _ _ _

theorem P_specialize : P.map specialize=NewSpecialization.P := by
  unfold P monicPolynomial
  simp only [Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C]
  simp only [map_mul specialize, coefficient_map specialize]
  rw [FiniteAlgebraInverse.map_ringInverse _ _ isUnit_leading]
  simp only [map_mul specialize, map_pow specialize, map_ofNat specialize,
    specialize_a,specialize_b,specialize_c,specialize_d,Ring.inverse_eq_inv]
  apply Polynomial.funext
  intro z
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_pow,
    Polynomial.eval_X,Polynomial.eval_C,Polynomial.eval_finsetSum]
  norm_num [coefficient,List.getD,coefficient0,coefficient1,coefficient2,coefficient3,coefficient4,coefficient5,coefficient6,coefficient7,coefficient8,coefficient9,coefficient10,coefficient11,coefficient12,coefficient13,coefficient14,coefficient15,coefficient16,coefficient17,coefficient18,coefficient19,coefficient20,coefficient21,coefficient22,coefficient23,coefficient24,coefficient25,coefficient26,coefficient27,
    Fin.sum_univ_succ,NewSpecialization.P,NewSpecialization.PData,CheckedPolynomialLists.encode,
    Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_X,Polynomial.eval_C]
  ring


abbrev E := AdjoinRoot P
def root : E := AdjoinRoot.root P
def toSpecial : E →+* AdjoinRoot NewSpecialization.P :=
  AdjoinRoot.map specialize P NewSpecialization.P (by
    simpa only [P_specialize] using dvd_refl NewSpecialization.P)
@[simp] theorem toSpecial_root : toSpecial root=AdjoinRoot.root NewSpecialization.P := by
  simp [toSpecial,root]
@[simp] theorem toSpecial_algebraMap (x : Coefficients) :
    toSpecial (algebraMap Coefficients E x)=
      algebraMap ℚ (AdjoinRoot NewSpecialization.P) (specialize x) := by
  simp [toSpecial,AdjoinRoot.algebraMap_eq]
theorem isUnit_of_special_isUnit (x : E) (h : IsUnit (toSpecial x)) : IsUnit x := by
  exact AdjoinRootSpecialization.isUnit_of_map_isUnit point P P_monic
    NewSpecialization.P P_specialize.symm _ x h

def ae : E := algebraMap Coefficients E a
def be : E := algebraMap Coefficients E b
def ce : E := algebraMap Coefficients E c
def de : E := algebraMap Coefficients E d
def K : E := kappa root ae be ce
def Num : E := coordinateNum root ae be ce de
def Den : E := coordinateDen root ae be ce de

def lineE : E := Num*Ring.inverse Den
def lineF : E := root*lineE
def lineG : E := de*uu root ae ce*Ring.inverse (6*K*lineE)
def lineH : E := root*lineG+K*Ring.inverse de

theorem toSpecial_K : toSpecial K=AdjoinRoot.mk NewSpecialization.P NewSpecialization.K_factor := by
  rw [NewSpecialization.K_factor_actual]
  simp only [K,kappa,map_mul,map_add,map_sub,map_pow,map_ofNat,
    toSpecial_root,ae,be,ce,de,toSpecial_algebraMap,specialize_a,specialize_b,specialize_c,specialize_d,
    AdjoinRoot.mk_X,AdjoinRoot.mk_C,← AdjoinRoot.algebraMap_eq]

theorem toSpecial_Num : toSpecial Num=AdjoinRoot.mk NewSpecialization.P NewSpecialization.Num_factor := by
  rw [NewSpecialization.Num_factor_actual]
  simp only [Num,coordinateNum,kappa,tt,uu,map_mul,map_add,map_sub,map_pow,map_ofNat,
    toSpecial_root,ae,be,ce,de,toSpecial_algebraMap,specialize_a,specialize_b,specialize_c,specialize_d,
    AdjoinRoot.mk_X,AdjoinRoot.mk_C,← AdjoinRoot.algebraMap_eq]

theorem toSpecial_Den : toSpecial Den=AdjoinRoot.mk NewSpecialization.P NewSpecialization.Den_factor := by
  rw [NewSpecialization.Den_factor_actual]
  simp only [Den,coordinateDen,kappa,tt,uu,map_mul,map_add,map_sub,map_pow,map_ofNat,
    toSpecial_root,ae,be,ce,de,toSpecial_algebraMap,specialize_a,specialize_b,specialize_c,specialize_d,
    AdjoinRoot.mk_X,AdjoinRoot.mk_C,← AdjoinRoot.algebraMap_eq]


theorem isUnit_K : IsUnit K := by
  apply isUnit_of_special_isUnit
  rw [toSpecial_K]
  exact AdjoinRootSpecialization.isUnit_mk_of_bezout _ _ _ _ NewSpecialization.K_bezout

theorem isUnit_Num : IsUnit Num := by
  apply isUnit_of_special_isUnit
  rw [toSpecial_Num]
  exact AdjoinRootSpecialization.isUnit_mk_of_bezout _ _ _ _ NewSpecialization.Num_bezout

theorem isUnit_Den : IsUnit Den := by
  apply isUnit_of_special_isUnit
  rw [toSpecial_Den]
  exact AdjoinRootSpecialization.isUnit_mk_of_bezout _ _ _ _ NewSpecialization.Den_bezout

theorem isUnit_lineE : IsUnit lineE := isUnit_Num.mul isUnit_Den.ringInverse

theorem isUnit_de : IsUnit de := isUnit_d.map (algebraMap Coefficients E)

theorem isUnit_six : IsUnit (6 : E) := by
  have h : IsUnit (6 : ℚ) := isUnit_iff_ne_zero.mpr (by norm_num)
  simpa only [map_ofNat] using h.map (algebraMap ℚ E)

theorem isUnit_eighteen : IsUnit (18 : E) := by
  have h : IsUnit (18 : ℚ) := isUnit_iff_ne_zero.mpr (by norm_num)
  simpa only [map_ofNat] using h.map (algebraMap ℚ E)

theorem eliminant_root : eliminant root ae be ce de=0 := by
  have hraw : AdjoinRoot.mk P (rawPolynomial a b c d)=0 := by
    rw [← leading_mul_monicPolynomial _ _ _ _ isUnit_leading]
    change AdjoinRoot.mk P (C _*P)=0
    simp
  have he := rawPolynomial_eval₂ (algebraMap Coefficients E) root a b c d
  rw [← aeval_def] at he
  change aeval (AdjoinRoot.root P) _ = _ at he
  rw [AdjoinRoot.aeval_eq,hraw] at he
  exact he.symm

theorem Den_mul_lineE : Den*lineE=Num := by
  dsimp [lineE]
  calc
    _ = Num*(Den*Ring.inverse Den) := by ring
    _ = Num := by rw [Ring.mul_inverse_cancel _ isUnit_Den,mul_one]

theorem quadratic_zero : quadratic root ae be ce de lineE=0 := by
  apply (isUnit_Den.pow 2).mul_right_eq_zero.mp
  calc
    _ = qa root ae be ce*(Den*lineE)^2+
        qb root ae be ce de*(Den*lineE)*Den+qc root ae ce de*Den^2 := by
      unfold quadratic
      ring
    _ = qa root ae be ce*Num^2+qb root ae be ce de*Num*Den+qc root ae ce de*Den^2 := by
      rw [Den_mul_lineE]
    _ = 0 := by
      dsimp [Num,Den]
      rw [quadratic_factor,eliminant_root,mul_zero]

theorem quartic_zero : quartic root ae be ce de lineE=0 := by
  have hqa : IsUnit (qa root ae be ce) := by
    change IsUnit (-18*K^3)
    exact isUnit_eighteen.neg.mul (isUnit_K.pow 3)
  apply (hqa.pow 3).mul_right_eq_zero.mp
  change (qa root ae be ce)^3 *
    (qe root ae be ce*lineE^4+qf root ae be ce*lineE+qh root ae ce de)=0
  rw [quartic_division (qa root ae be ce) (qb root ae be ce de) (qc root ae ce de)
    (qe root ae be ce) (qf root ae be ce) (qh root ae ce de) lineE]
  change quadratic root ae be ce de lineE * qe root ae be ce * _ + _ + _ = 0
  rw [quadratic_zero,zero_mul,zero_mul,zero_add,linearCoeff_factor,constantCoeff_factor]
  change -216*K^4*Den*lineE+216*K^4*Num=0
  calc
    _ = -216*K^4*(Den*lineE)+216*K^4*Num := by ring
    _ = 0 := by rw [Den_mul_lineE]; ring

theorem lineG_scaled : (6*K*lineE*de)*lineG=de^2*uu root ae ce := by
  have hu := (isUnit_six.mul isUnit_K).mul isUnit_lineE
  dsimp [lineG]
  calc
    _ = de^2*uu root ae ce*((6*K*lineE)*Ring.inverse (6*K*lineE)) := by ring
    _ = _ := by rw [Ring.mul_inverse_cancel _ hu,mul_one]

theorem lineH_scaled : (6*K*lineE*de)*lineH=
    root*de^2*uu root ae ce+6*K^2*lineE := by
  dsimp [lineH]
  calc
    _ = root*((6*K*lineE*de)*lineG)+6*K^2*lineE*(de*Ring.inverse de) := by ring
    _ = _ := by rw [lineG_scaled,Ring.mul_inverse_cancel _ isUnit_de,mul_one]; ring

/-- A line over the full four-parameter coefficient ring, not only at its good fiber. -/
theorem line_identity (U V : E) :
    cubic ae be ce de U V (lineE*U+lineF*V) (lineG*U+lineH*V)=0 := by
  exact line_of_common_root root ae be ce de lineE lineF lineG lineH rfl
    lineG_scaled lineH_scaled (((isUnit_six.mul isUnit_K).mul isUnit_lineE).mul isUnit_de)
    quadratic_zero quartic_zero U V

theorem rel0_zero : rel0 ae lineE lineG=0 := by
  simpa [cubic,rel0] using line_identity 1 0

theorem rel3_zero : rel3 be de lineF lineH=0 := by
  simpa [cubic,rel3] using line_identity 0 1

theorem isUnit_two : IsUnit (2 : E) := by
  have h : IsUnit (2 : ℚ) := isUnit_iff_ne_zero.mpr (by norm_num)
  simpa only [map_ofNat] using h.map (algebraMap ℚ E)

theorem rel1_zero : rel1 ce lineE lineF lineG lineH=0 := by
  apply isUnit_two.mul_right_eq_zero.mp
  have hp := line_identity 1 1
  have hm := line_identity 1 (-1)
  have h3 := rel3_zero
  unfold cubic at hp hm
  unfold rel3 at h3
  unfold rel1
  linear_combination hp-hm-2*h3

theorem rel2_zero : rel2 de lineE lineF lineG lineH=0 := by
  apply isUnit_two.mul_right_eq_zero.mp
  have hp := line_identity 1 1
  have hm := line_identity 1 (-1)
  have h0 := rel0_zero
  unfold cubic at hp hm
  unfold rel0 at h0
  unfold rel2
  linear_combination hp+hm-2*h0

/-- The generic chart agrees with the independently checked rational line. -/
theorem toSpecial_lineE : toSpecial lineE=AdjoinRoot.mk NewSpecialization.P NewSpecialization.e := by
  apply (isUnit_Den.map toSpecial).mul_left_cancel
  rw [← map_mul,Den_mul_lineE,toSpecial_Num,toSpecial_Den]
  have h := congrArg (AdjoinRoot.mk NewSpecialization.P) NewSpecialization.coordinate_e_reduction
  simp only [map_sub,map_add,map_mul,map_neg,map_one,AdjoinRoot.mk_self,zero_mul,
    NewSpecialization.coordinate_e,NewSpecialization.coordinate_eData,
    CheckedPolynomialLists.encode,map_zero,sub_zero,neg_mul,one_mul] at h
  linear_combination -h

theorem toSpecial_lineF : toSpecial lineF=AdjoinRoot.mk NewSpecialization.P NewSpecialization.f := by
  simp only [lineF,map_mul,toSpecial_root,toSpecial_lineE]
  have h := congrArg (AdjoinRoot.mk NewSpecialization.P) NewSpecialization.coordinate_f_reduction
  simp only [map_sub,map_add,map_mul,map_neg,map_one,AdjoinRoot.mk_self,zero_mul,
    NewSpecialization.coordinate_f,NewSpecialization.coordinate_fData,
    CheckedPolynomialLists.encode,map_zero,sub_zero,neg_mul,one_mul,
    NewSpecialization.rPoly,NewSpecialization.rPolyData,AdjoinRoot.mk_X] at h
  linear_combination -h

theorem lineG_mul : (6*K*lineE)*lineG=de*uu root ae ce := by
  dsimp [lineG]
  calc
    _ = de*uu root ae ce*((6*K*lineE)*Ring.inverse (6*K*lineE)) := by ring
    _ = _ := by rw [Ring.mul_inverse_cancel _ ((isUnit_six.mul isUnit_K).mul isUnit_lineE),mul_one]

theorem toSpecial_lineG : toSpecial lineG=AdjoinRoot.mk NewSpecialization.P NewSpecialization.g := by
  apply (((isUnit_six.mul isUnit_K).mul isUnit_lineE).map toSpecial).mul_left_cancel
  rw [← map_mul,lineG_mul]
  have h := congrArg (AdjoinRoot.mk NewSpecialization.P) NewSpecialization.coordinate_g_reduction
  simp only [map_sub,map_add,map_mul,map_neg,map_one,map_ofNat,AdjoinRoot.mk_self,zero_mul,
    NewSpecialization.coordinate_g,NewSpecialization.coordinate_gData,
    CheckedPolynomialLists.encode,map_zero,sub_zero,neg_mul,one_mul,
    NewSpecialization.rPoly,NewSpecialization.rPolyData,AdjoinRoot.mk_X] at h
  simp only [map_mul,map_sub,map_ofNat,uu,toSpecial_root,toSpecial_lineE,toSpecial_K,
    ae,ce,de,toSpecial_algebraMap,specialize_a,specialize_c,specialize_d,map_one,map_ofNat]
  linear_combination -h

theorem toSpecial_lineH : toSpecial lineH=AdjoinRoot.mk NewSpecialization.P NewSpecialization.h := by
  simp only [lineH,map_add,map_mul,toSpecial_root,toSpecial_lineG,toSpecial_K]
  rw [FiniteAlgebraInverse.map_ringInverse _ _ isUnit_de]
  simp only [de,toSpecial_algebraMap,specialize_d,map_one,Ring.inverse_one,mul_one]
  have h := congrArg (AdjoinRoot.mk NewSpecialization.P) NewSpecialization.coordinate_h_reduction
  simp only [map_sub,map_add,map_mul,map_neg,map_one,AdjoinRoot.mk_self,zero_mul,
    NewSpecialization.coordinate_h,NewSpecialization.coordinate_hData,
    CheckedPolynomialLists.encode,map_zero,sub_zero,neg_mul,one_mul,
    NewSpecialization.rPoly,NewSpecialization.rPolyData,AdjoinRoot.mk_X] at h
  linear_combination -h

end
end HoldoutQ2.NewLineAlgebra
