import Proposal.JacobianDimension
import HodgeComputer.Constructions.HoldoutCover.ResidueDerivatives

/-! Coordinate projection and canonical tangent derivations for the exact
normalized Jacobian hypersurface. The quotient/fraction-field descent follows
fqlx's shared HoldoutCover constructions. Prepared with OpenAI Codex assistance. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace MixedPolarJacobianHypersurface
open HoldoutConstruction MixedPolarJacobianEmbedding Polynomial
open MvPolynomial
abbrev Ambient := MvPolynomial (Fin 6) ℂ
local notation "v" => (MvPolynomial.X : Fin 6 → Ambient)
def hypersurface : Ambient :=
  v 0^2-v 5^3-MvPolynomial.C (1/432)*MixedPolarJacobian.a8 (v 2) (v 3) 1 (v 4) (v 1)*v 5-
    MvPolynomial.C (1/432)*MixedPolarJacobian.b256 (v 2) (v 3) 1 (v 4) (v 1)
lemma finSucc_C (c : ℂ) :
    MvPolynomial.finSuccEquiv ℂ 5 (MvPolynomial.C c)=Polynomial.C (MvPolynomial.C c) :=
  (MvPolynomial.finSuccEquiv ℂ 5).commutes c
lemma hypersurface_univariate :
    MvPolynomial.finSuccEquiv ℂ 5 hypersurface=MixedPolarJacobianDomain.equation := by
  unfold hypersurface MixedPolarJacobianDomain.equation MixedPolarJacobianDomain.rhs
  simp only [MixedPolarJacobian.a8,MixedPolarJacobian.a432,MixedPolarJacobian.b256,MixedPolarJacobian.b432,map_add,map_sub,map_mul,map_pow,map_neg,
    map_one,map_ofNat,MvPolynomial.finSuccEquiv_X_zero]
  simp only [show (1:Fin 6)=(0:Fin 5).succ from rfl,
    show (2:Fin 6)=(1:Fin 5).succ from rfl,show (3:Fin 6)=(2:Fin 5).succ from rfl,
    show (4:Fin 6)=(3:Fin 5).succ from rfl,show (5:Fin 6)=(4:Fin 5).succ from rfl,
    MvPolynomial.finSuccEquiv_X_succ]
  simp only [finSucc_C]
  ring

def projection : Ambient →+* TargetRing :=
  (AdjoinRoot.mk MixedPolarJacobianDomain.equation).comp (MvPolynomial.finSuccEquiv ℂ 5).toRingHom
lemma projection_surjective : Function.Surjective projection :=
  (AdjoinRoot.mk_surjective (g := MixedPolarJacobianDomain.equation)).comp
    (MvPolynomial.finSuccEquiv ℂ 5).surjective
lemma projection_kernel (p : Ambient) : projection p=0 ↔ hypersurface ∣ p := by
  change AdjoinRoot.mk MixedPolarJacobianDomain.equation (MvPolynomial.finSuccEquiv ℂ 5 p)=0 ↔ _
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
    (AdjoinRoot.mk MixedPolarJacobianDomain.equation (MvPolynomial.finSuccEquiv ℂ 5 (MvPolynomial.C c)))=_
  rw [finSucc_C]
  rfl

lemma normal_polynomial : MvPolynomial.pderiv 0 hypersurface=2*v 0 := by
  have h4 : MvPolynomial.pderiv 0 (4 : Ambient)=0 := (MvPolynomial.pderiv 0).map_natCast 4
  have h2 : MvPolynomial.pderiv 0 (2 : Ambient)=0 := (MvPolynomial.pderiv 0).map_natCast 2
  have h3 : MvPolynomial.pderiv 0 (3 : Ambient)=0 := (MvPolynomial.pderiv 0).map_natCast 3
  have h6 : MvPolynomial.pderiv 0 (6 : Ambient)=0 := (MvPolynomial.pderiv 0).map_natCast 6
  have h16 : MvPolynomial.pderiv 0 (16 : Ambient)=0 := (MvPolynomial.pderiv 0).map_natCast 16
  have h32 : MvPolynomial.pderiv 0 (32 : Ambient)=0 := (MvPolynomial.pderiv 0).map_natCast 32
  have h54 : MvPolynomial.pderiv 0 (54 : Ambient)=0 := (MvPolynomial.pderiv 0).map_natCast 54
  have h70 : MvPolynomial.pderiv 0 (70 : Ambient)=0 := (MvPolynomial.pderiv 0).map_natCast 70
  have h108 : MvPolynomial.pderiv 0 (108 : Ambient)=0 := (MvPolynomial.pderiv 0).map_natCast 108
  have h140 : MvPolynomial.pderiv 0 (140 : Ambient)=0 := (MvPolynomial.pderiv 0).map_natCast 140
  have h216 : MvPolynomial.pderiv 0 (216 : Ambient)=0 := (MvPolynomial.pderiv 0).map_natCast 216
  have h324 : MvPolynomial.pderiv 0 (324 : Ambient)=0 := (MvPolynomial.pderiv 0).map_natCast 324
  have h432 : MvPolynomial.pderiv 0 (432 : Ambient)=0 := (MvPolynomial.pderiv 0).map_natCast 432
  have h648 : MvPolynomial.pderiv 0 (648 : Ambient)=0 := (MvPolynomial.pderiv 0).map_natCast 648
  have h2916 : MvPolynomial.pderiv 0 (2916 : Ambient)=0 := (MvPolynomial.pderiv 0).map_natCast 2916
  have h5832 : MvPolynomial.pderiv 0 (5832 : Ambient)=0 := (MvPolynomial.pderiv 0).map_natCast 5832
  have h11664 : MvPolynomial.pderiv 0 (11664 : Ambient)=0 := (MvPolynomial.pderiv 0).map_natCast 11664
  have h23328 : MvPolynomial.pderiv 0 (23328 : Ambient)=0 := (MvPolynomial.pderiv 0).map_natCast 23328
  norm_num [hypersurface,MixedPolarJacobian.a8,MixedPolarJacobian.a432,MixedPolarJacobian.b256,MixedPolarJacobian.b432,MvPolynomial.pderiv_mul,
    MvPolynomial.pderiv_pow,MvPolynomial.pderiv_X,Pi.single_apply,h4,h2,h3,h6,h16,h32,h54,h70,h108,h140,h216,h324,h432,h648,h2916,h5832,h11664,h23328,
    show (1:Fin 6)≠0 by decide,show (2:Fin 6)≠0 by decide,show (3:Fin 6)≠0 by decide,
    show (4:Fin 6)≠0 by decide,show (5:Fin 6)≠0 by decide]
def axis : Ambient →+* Polynomial ℂ := MvPolynomial.eval₂Hom Polynomial.C ![Polynomial.X,0,0,0,0,0]
lemma axis_hypersurface : axis hypersurface=Polynomial.X^2 := by
  simp [axis,hypersurface,MixedPolarJacobian.a8,MixedPolarJacobian.a432,MixedPolarJacobian.b256,MixedPolarJacobian.b432,MixedPolarJacobian.a432,MixedPolarJacobian.b432]
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
end MixedPolarJacobianHypersurface
