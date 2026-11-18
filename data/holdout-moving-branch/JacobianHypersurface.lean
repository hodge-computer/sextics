import Proposal.JacobianDimension
import HodgeComputer.Constructions.HoldoutCover.ResidueDerivatives

/-! Coordinate projection and canonical tangent derivations for the exact
normalized Jacobian hypersurface. The quotient/fraction-field descent follows
fqlx's shared HoldoutCover constructions. Prepared with OpenAI Codex assistance. -/
noncomputable section
namespace CycleJacobianHypersurface
open HoldoutConstruction CycleJacobianEmbedding Polynomial
open MvPolynomial
abbrev Ambient := MvPolynomial (Fin 6) ℂ
local notation "v" => (MvPolynomial.X : Fin 6 → Ambient)
def hypersurface : Ambient :=
  v 0^2-v 5^3-MvPolynomial.C (1/4116)*CycleJacobian.a8 (v 2) (v 3) 1 (v 4) (v 1)*v 5-
    MvPolynomial.C (1/111132)*CycleJacobian.b256 (v 2) (v 3) 1 (v 4) (v 1)
lemma finSucc_C (c : ℂ) :
    MvPolynomial.finSuccEquiv ℂ 5 (MvPolynomial.C c)=Polynomial.C (MvPolynomial.C c) :=
  (MvPolynomial.finSuccEquiv ℂ 5).commutes c
lemma hypersurface_univariate :
    MvPolynomial.finSuccEquiv ℂ 5 hypersurface=CycleJacobianDomain.equation := by
  unfold hypersurface CycleJacobianDomain.equation CycleJacobianDomain.rhs
  simp only [CycleJacobian.a8,CycleJacobian.b256,map_add,map_sub,map_mul,map_pow,map_neg,
    map_one,map_ofNat,MvPolynomial.finSuccEquiv_X_zero]
  simp only [show (1:Fin 6)=(0:Fin 5).succ from rfl,
    show (2:Fin 6)=(1:Fin 5).succ from rfl,show (3:Fin 6)=(2:Fin 5).succ from rfl,
    show (4:Fin 6)=(3:Fin 5).succ from rfl,show (5:Fin 6)=(4:Fin 5).succ from rfl,
    MvPolynomial.finSuccEquiv_X_succ]
  rw [finSucc_C,finSucc_C]
  ring

def projection : Ambient →+* TargetRing :=
  (AdjoinRoot.mk CycleJacobianDomain.equation).comp (MvPolynomial.finSuccEquiv ℂ 5).toRingHom
lemma projection_surjective : Function.Surjective projection :=
  (AdjoinRoot.mk_surjective (g := CycleJacobianDomain.equation)).comp
    (MvPolynomial.finSuccEquiv ℂ 5).surjective
lemma projection_kernel (p : Ambient) : projection p=0 ↔ hypersurface ∣ p := by
  change AdjoinRoot.mk CycleJacobianDomain.equation (MvPolynomial.finSuccEquiv ℂ 5 p)=0 ↔ _
  rw [AdjoinRoot.mk_eq_zero,← hypersurface_univariate]
  exact map_dvd_iff (MvPolynomial.finSuccEquiv ℂ 5)
def residueMap : Ambient →+* TargetField :=
  (algebraMap TargetRing TargetField).comp projection
lemma residueMap_kernel (p : Ambient) : residueMap p=0 ↔ hypersurface ∣ p :=
  by
    constructor
    · intro h
      apply (projection_kernel p).mp
      apply IsFractionRing.injective TargetRing TargetField
      simpa only [residueMap,RingHom.comp_apply,map_zero] using h
    · intro h
      change algebraMap TargetRing TargetField (projection p)=0
      rw [(projection_kernel p).mpr h,map_zero]
@[simp] lemma residueMap_C (c : ℂ) : residueMap (MvPolynomial.C c)=algebraMap ℂ TargetField c := by
  change algebraMap TargetRing TargetField
    (AdjoinRoot.mk CycleJacobianDomain.equation (MvPolynomial.finSuccEquiv ℂ 5 (MvPolynomial.C c)))=_
  rw [finSucc_C]
  rfl

lemma normal_polynomial : MvPolynomial.pderiv 0 hypersurface=2*v 0 := by
  have h2 : MvPolynomial.pderiv 0 (2 : Ambient)=0 := (MvPolynomial.pderiv 0).map_natCast 2
  have h24 : MvPolynomial.pderiv 0 (24 : Ambient)=0 := (MvPolynomial.pderiv 0).map_natCast 24
  have h27 : MvPolynomial.pderiv 0 (27 : Ambient)=0 := (MvPolynomial.pderiv 0).map_natCast 27
  have h28 : MvPolynomial.pderiv 0 (28 : Ambient)=0 := (MvPolynomial.pderiv 0).map_natCast 28
  have h324 : MvPolynomial.pderiv 0 (324 : Ambient)=0 := (MvPolynomial.pderiv 0).map_natCast 324
  have h1764 : MvPolynomial.pderiv 0 (1764 : Ambient)=0 := (MvPolynomial.pderiv 0).map_natCast 1764
  have h2268 : MvPolynomial.pderiv 0 (2268 : Ambient)=0 := (MvPolynomial.pderiv 0).map_natCast 2268
  have h4116 : MvPolynomial.pderiv 0 (4116 : Ambient)=0 := (MvPolynomial.pderiv 0).map_natCast 4116
  have h10584 : MvPolynomial.pderiv 0 (10584 : Ambient)=0 := (MvPolynomial.pderiv 0).map_natCast 10584
  have h111132 : MvPolynomial.pderiv 0 (111132 : Ambient)=0 := (MvPolynomial.pderiv 0).map_natCast 111132
  have h750141 : MvPolynomial.pderiv 0 (750141 : Ambient)=0 := (MvPolynomial.pderiv 0).map_natCast 750141
  norm_num [hypersurface,CycleJacobian.a8,CycleJacobian.b256,MvPolynomial.pderiv_mul,h2,h24,h27,h28,h324,h1764,h2268,h4116,h10584,h111132,h750141,
    MvPolynomial.pderiv_pow,MvPolynomial.pderiv_X,Pi.single_apply,
    show (1:Fin 6)≠0 by decide,show (2:Fin 6)≠0 by decide,show (3:Fin 6)≠0 by decide,
    show (4:Fin 6)≠0 by decide,show (5:Fin 6)≠0 by decide]
def axis : Ambient →+* Polynomial ℂ := MvPolynomial.eval₂Hom Polynomial.C ![Polynomial.X,0,0,0,0,0]
lemma axis_hypersurface : axis hypersurface=Polynomial.X^2 := by
  simp [axis,hypersurface,CycleJacobian.a8,CycleJacobian.b256]
lemma normal_ne_zero : residueMap (integerPartial 0 hypersurface)≠0 := by
  intro h
  have hm := map_dvd axis ((residueMap_kernel _).mp h)
  rw [axis_hypersurface,integerPartial_apply,normal_polynomial] at hm
  have ha : axis (2*v 0)=2*Polynomial.X := by simp [axis]
  rw [ha] at hm
  have hc := (Polynomial.X_pow_dvd_iff.mp hm) 1 (by decide)
  norm_num at hc

local instance : Algebra ℤ TargetField := Ring.toIntAlgebra _
def tangent (i : Fin 5) : Derivation ℤ TargetField TargetField :=
  residueTangent (K := TargetField) projection projection_surjective
    (integerPartial 0) (integerPartial i.succ) hypersurface projection_kernel normal_ne_zero
lemma tangent_apply (i : Fin 5) (p : Ambient) :
    tangent i (residueMap p)=residueMap (MvPolynomial.pderiv i.succ p)-
      residueMap (MvPolynomial.pderiv i.succ hypersurface)/residueMap (MvPolynomial.pderiv 0 hypersurface)*
        residueMap (MvPolynomial.pderiv 0 p) :=
  residueTangent_apply (K := TargetField) projection projection_surjective
    (integerPartial 0) (integerPartial i.succ) hypersurface projection_kernel normal_ne_zero p
#print axioms normal_ne_zero
#print axioms tangent_apply
end CycleJacobianHypersurface
