import HodgeTarget
import Proposal.DeformedCoverFields
import HodgeComputer.Constructions.HoldoutCover.ResidueDerivatives

/-!
The residue chart of the protected physical polynomial. The defining
equation is HodgeSubmission.F itself, and the normal is its actual X0
partial derivative. Uses fqlx's generic quotient/fraction derivations.
Prepared with OpenAI Codex assistance for hodgepodgeconjecture.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000
namespace DeformedCover
open HoldoutConstruction Polynomial
local instance physicalModel_local_1 : Algebra ℤ PhysicalField := Ring.toIntAlgebra _
local instance physicalModel_local_2 : Algebra ℤ CoverField := Ring.toIntAlgebra _

lemma protected_univariate : MvPolynomial.finSuccEquiv ℂ 5 HodgeSubmission.F=physicalPolynomial := by
  have he : Fin.cases (X : Polynomial (MvPolynomial (Fin 5) ℂ)) (fun j => C (MvPolynomial.X j))=
      ![X,C (MvPolynomial.X 0),C (MvPolynomial.X 1),C (MvPolynomial.X 2),
        C (MvPolynomial.X 3),C (MvPolynomial.X 4)] := by
    funext i
    fin_cases i <;> rfl
  have h7 : (1/7 : ℂ)=2*(14:ℂ)⁻¹ := by norm_num
  simp [HodgeSubmission.F,h7,one_div,physicalPolynomial,DeformedGeometry.physicalPolynomial,
    DeformedGeometry.ternaryCorrection,holdoutPolynomial,MvPolynomial.finSuccEquiv_apply,he,map_ofNat]
  ring
lemma protected_irreducible : Irreducible HodgeSubmission.F := by
  apply (MulEquiv.irreducible_iff (MvPolynomial.finSuccEquiv ℂ 5)).mp
  rw [protected_univariate]
  exact DeformedGeometry.physicalPolynomial_irreducible _ _ complex_I_six

def physicalProjection : HodgeComputer.Poly →+* PhysicalRing :=
  (AdjoinRoot.mk physicalPolynomial).comp (MvPolynomial.finSuccEquiv ℂ 5).toRingHom
lemma physicalProjection_surjective : Function.Surjective physicalProjection :=
  (AdjoinRoot.mk_surjective (g := physicalPolynomial)).comp (MvPolynomial.finSuccEquiv ℂ 5).surjective
lemma physicalProjection_kernel (p : HodgeComputer.Poly) :
    physicalProjection p=0 ↔ HodgeSubmission.F ∣ p := by
  change AdjoinRoot.mk physicalPolynomial (MvPolynomial.finSuccEquiv ℂ 5 p)=0 ↔ _
  rw [AdjoinRoot.mk_eq_zero,← protected_univariate]
  exact map_dvd_iff (MvPolynomial.finSuccEquiv ℂ 5)
def physicalResidueMap : HodgeComputer.Poly →+* PhysicalField :=
  (algebraMap PhysicalRing PhysicalField).comp physicalProjection
lemma physicalResidueMap_kernel (p : HodgeComputer.Poly) :
    physicalResidueMap p=0 ↔ HodgeSubmission.F ∣ p :=
  residue_fractionMap_kernel physicalProjection HodgeSubmission.F physicalProjection_kernel p
@[simp] lemma physicalResidueMap_C (c : ℂ) :
    physicalResidueMap (MvPolynomial.C c)=algebraMap ℂ PhysicalField c := by
  change algebraMap PhysicalRing PhysicalField (AdjoinRoot.mk physicalPolynomial
    (MvPolynomial.finSuccEquiv ℂ 5 (MvPolynomial.C c)))=_
  rw [show MvPolynomial.finSuccEquiv ℂ 5 (MvPolynomial.C c)=C (MvPolynomial.C c)
    from (MvPolynomial.finSuccEquiv ℂ 5).commutes c]
  rfl
def physicalParameter (i : Fin 5) : PhysicalField := physicalResidueMap (MvPolynomial.X i.succ)
def physicalRoot : PhysicalField := physicalResidueMap (MvPolynomial.X 0)

def physicalAxis : HodgeComputer.Poly →+* Polynomial ℂ :=
  MvPolynomial.eval₂Hom C ![X,0,0,0,0,0]
lemma protected_axis : physicalAxis HodgeSubmission.F=X^6 := by
  simp [physicalAxis,HodgeSubmission.F]
lemma protected_normal_axis : physicalAxis (integerPartial 0 HodgeSubmission.F)=6*X^5 := by
  norm_num [physicalAxis,HodgeSubmission.F,integerPartial,MvPolynomial.pderiv_pow,
    MvPolynomial.pderiv_mul,Polynomial.C_ofNat,Pi.single_apply,Fin.ext_iff]
  simp [Matrix.cons_val]
lemma protected_not_dvd_normal : ¬ HodgeSubmission.F ∣ integerPartial 0 HodgeSubmission.F := by
  intro hd
  have hm := map_dvd physicalAxis hd
  rw [protected_axis,protected_normal_axis] at hm
  have hc := (Polynomial.X_pow_dvd_iff.mp hm) 5 (by decide)
  norm_num at hc
lemma physical_normal_ne_zero : physicalResidueMap (integerPartial 0 HodgeSubmission.F) ≠ 0 := by
  intro h
  exact protected_not_dvd_normal ((physicalResidueMap_kernel _).mp h)
def physicalTangent (i : Fin 5) : Derivation ℤ PhysicalField PhysicalField :=
  residueTangent (K := PhysicalField) physicalProjection physicalProjection_surjective
    (integerPartial 0) (integerPartial i.succ) HodgeSubmission.F physicalProjection_kernel physical_normal_ne_zero
lemma physicalTangent_apply (i : Fin 5) (p : HodgeComputer.Poly) :
    physicalTangent i (physicalResidueMap p)=physicalResidueMap (integerPartial i.succ p)-
      physicalResidueMap (integerPartial i.succ HodgeSubmission.F)/
        physicalResidueMap (integerPartial 0 HodgeSubmission.F)*physicalResidueMap (integerPartial 0 p) :=
  residueTangent_apply (K := PhysicalField) physicalProjection physicalProjection_surjective
    (integerPartial 0) (integerPartial i.succ) HodgeSubmission.F
    physicalProjection_kernel physical_normal_ne_zero p
lemma physicalTangents_commute (i j : Fin 5) : Function.Commute (physicalTangent i) (physicalTangent j) :=
  residueTangent_commute (K := PhysicalField) physicalProjection physicalProjection_surjective
    (integerPartial 0) (integerPartial i.succ) (integerPartial j.succ) HodgeSubmission.F
    physicalProjection_kernel physical_normal_ne_zero
    (integerPartial_commute i.succ 0) (integerPartial_commute j.succ 0) (integerPartial_commute i.succ j.succ)
@[simp] lemma physicalTangent_parameter (i j : Fin 5) :
    physicalTangent i (physicalParameter j)=if j=i then 1 else 0 := by
  rw [physicalParameter,physicalTangent_apply,integerPartial_X_of_ne 0 j.succ (Fin.succ_ne_zero j)]
  simp [integerPartial_apply,MvPolynomial.pderiv_X,Pi.single_apply,apply_ite]
@[simp] lemma physicalTangent_base (i : Fin 5) (c : ℂ) :
    physicalTangent i (algebraMap ℂ PhysicalField c)=0 := by
  rw [← physicalResidueMap_C,physicalTangent_apply]
  simp

def coverPhysicalTangent (i : Fin 5) : Derivation ℤ CoverField CoverField :=
  extendFiniteDerivation (physicalTangent i)
lemma coverPhysicalTangent_apply (i : Fin 5) (x : PhysicalField) :
    coverPhysicalTangent i (physicalFieldMap x)=physicalFieldMap (physicalTangent i x) :=
  extendFiniteDerivation_apply _ x
lemma coverPhysicalTangents_commute (i j : Fin 5) :
    Function.Commute (coverPhysicalTangent i) (coverPhysicalTangent j) :=
  extendFiniteDerivation_commute _ _ (physicalTangents_commute i j)

end DeformedCover
#print axioms DeformedCover.protected_irreducible
#print axioms DeformedCover.physical_normal_ne_zero
#print axioms DeformedCover.coverPhysicalTangents_commute
