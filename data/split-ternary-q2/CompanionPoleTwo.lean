import Proposal.CompanionResidue
import HodgeComputer.Constructions.HigherResidues.NormalJetBinding
import Proposal.RationalAmbient

/- The exact companion cone in coordinates [T,x,a,y,S], with T as the
normal coordinate. The coordinate ring and finite family are the previously
proved ones; only the coordinate order changes. Prepared with OpenAI Codex
assistance for fqlx. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
namespace SplitCompanionPoleTwo
open HoldoutConstruction
open scoped BigOperators
abbrev P5 := MvPolynomial (Fin 5) ℂ
abbrev CoordinateRing := SplitCompanionDomain.CoordinateRing
abbrev FunctionField := SplitCompanionDomain.FunctionField

/-- Old order [a,x,y,S,T] to new order [T,x,a,y,S]. -/
def permutation : Equiv.Perm (Fin 5) where
  toFun := ![2,1,3,4,0]
  invFun := ![4,1,0,2,3]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def hypersurfaceT (which : Bool) : P5 :=
  MvPolynomial.rename permutation (SplitCompanionDomain.hypersurface which)
def projectionT (which : Bool) : P5 →+* CoordinateRing which :=
  (SplitCompanionDomain.projection which).comp (MvPolynomial.rename permutation.symm).toRingHom
def residueMapT (which : Bool) : P5 →+* FunctionField which :=
  (algebraMap (CoordinateRing which) (FunctionField which)).comp (projectionT which)

lemma projectionT_surjective (which : Bool) : Function.Surjective (projectionT which) :=
  (SplitCompanionDomain.projection_surjective which).comp
    (MvPolynomial.renameEquiv (R:=ℂ) permutation.symm).surjective
lemma projectionT_kernel (which : Bool) (P : P5) :
    projectionT which P=0 ↔ hypersurfaceT which ∣ P := by
  change SplitCompanionDomain.projection which (MvPolynomial.rename permutation.symm P)=0 ↔ _
  rw [SplitCompanionDomain.projection_kernel]
  have hi : MvPolynomial.rename permutation.symm (hypersurfaceT which)=
      SplitCompanionDomain.hypersurface which := by
    rw [hypersurfaceT,MvPolynomial.rename_rename,permutation.symm_comp_self,MvPolynomial.rename_id_apply]
  rw [← hi]
  exact map_dvd_iff (MvPolynomial.renameEquiv (R:=ℂ) permutation.symm)
lemma residueMapT_kernel (which : Bool) (P : P5) :
    residueMapT which P=0 ↔ hypersurfaceT which ∣ P :=
  residue_fractionMap_kernel (projectionT which) (hypersurfaceT which) (projectionT_kernel which) P
lemma residueMapT_old (which : Bool) (P : P5) : residueMapT which P=
    SplitCompanionDomain.residueMap which (MvPolynomial.rename permutation.symm P) := rfl

lemma hypersurfaceT_explicit (which : Bool) : hypersurfaceT which=
    SplitCompanion.H which 0
      ![MvPolynomial.X 1,MvPolynomial.X 2,MvPolynomial.X 3,MvPolynomial.X 4,MvPolynomial.X 0] := by
  rw [hypersurfaceT]
  have hm := SplitCompanion.H_map (R:=P5) (S:=P5) (MvPolynomial.rename permutation).toRingHom which 0
    ![MvPolynomial.X 1,MvPolynomial.X 0,MvPolynomial.X 2,MvPolynomial.X 3,MvPolynomial.X 4]
  change MvPolynomial.rename permutation (SplitCompanion.H which 0 _)=_ at hm
  rw [SplitCompanionDomain.hypersurface,hm]
  simp only [map_zero,MvPolynomial.rename_X]
  congr 1
  funext i
  fin_cases i <;> simp [permutation]

lemma normal_polynomial (which : Bool) : integerPartial 0 (hypersurfaceT which)=
    21*MvPolynomial.X 0^2 := by
  rw [hypersurfaceT_explicit,SplitCompanion.H_derivation (integerPartial 0) which 0 (map_zero _)]
  cases which <;> simp [SplitCompanion.gradient,Fin.sum_univ_succ,integerPartial_X_of_ne] <;> ring

lemma T_ne_zero (which : Bool) : residueMapT which (MvPolynomial.X 0)≠0 := by
  rw [residueMapT_old,MvPolynomial.rename_X]
  change SplitCompanionDomain.residueMap which (MvPolynomial.X (Fin.succ (3 : Fin 4)))≠0
  rw [CrossedMonicHypersurface.residueMap_X_succ]
  intro h
  have hz : AdjoinRoot.of (SplitCompanionDomain.equation which) (MvPolynomial.X 3)=0 :=
    (IsFractionRing.injective (CoordinateRing which) (FunctionField which)) (by simpa only [map_zero] using h)
  have hinj := AdjoinRoot.of.injective_of_degree_ne_zero
    (ne_of_gt ((SplitCompanionDomain.equation_monic which).degree_pos_of_not_isUnit
      (SplitCompanionDomain.equation_irreducible which).not_isUnit))
  exact MvPolynomial.X_ne_zero (R:=ℂ) 3 (hinj (by simpa only [map_zero] using hz))

lemma normal_ne_zero (which : Bool) : residueMapT which (integerPartial 0 (hypersurfaceT which))≠0 := by
  rw [normal_polynomial,map_mul,map_pow,map_ofNat]
  exact mul_ne_zero (by norm_num) (pow_ne_zero 2 (T_ne_zero which))

local instance (which : Bool) : Algebra ℤ (FunctionField which) := Ring.toIntAlgebra _
def tangentT (which : Bool) (i : Fin 4) : Derivation ℤ (FunctionField which) (FunctionField which) :=
  residueTangent (K:=FunctionField which) (projectionT which) (projectionT_surjective which)
    (integerPartial 0) (integerPartial i.succ) (hypersurfaceT which) (projectionT_kernel which) (normal_ne_zero which)
lemma tangentT_apply (which : Bool) (i : Fin 4) (P : P5) :
    tangentT which i (residueMapT which P)=residueMapT which (integerPartial i.succ P)-
      residueMapT which (integerPartial i.succ (hypersurfaceT which))/
        residueMapT which (integerPartial 0 (hypersurfaceT which))*residueMapT which (integerPartial 0 P) :=
  residueTangent_apply (K:=FunctionField which) (projectionT which) (projectionT_surjective which)
    (integerPartial 0) (integerPartial i.succ) (hypersurfaceT which) (projectionT_kernel which) (normal_ne_zero which) P

#print axioms normal_ne_zero
#print axioms tangentT_apply
end SplitCompanionPoleTwo
