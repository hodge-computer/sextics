import Proposal.GeometricThreefoldMixedWedge
import Proposal.GeometricLiteralThreefoldSurfaceNormal

/-!
# The mixed one-form of an ambient conormal wedge

Multiplication by the surface Jacobian expresses the threefold volume as
a wedge whose first factor is the equation of the cubic. Inserting a
surface tangent and a transverse ambient vector gives an identity of ordinary
one-forms over any coefficient algebra of the surface patch.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2ThreefoldMixedConormal
open CycleQ2ThreefoldMixedWedge CycleQ2ThreefoldMixedCurveForm CycleQ2LiteralAbelJacobiContraction
  CycleQ2GeometricSurfaceAdjunction CycleQ2GeometricSurfaceDeterminantNaturality CycleQ2LiteralThreefoldSurfaceNormal
  CycleQ2LiteralThreefoldSurfaceAdjunction CycleQ2LiteralAbelJacobiEquations
  CycleQ2LiteralAbelJacobiMovingNormal CycleQ2LiteralThreefoldChartVolume

section Exterior
variable {Q C : Type} [CommRing Q] [CommRing C] [Algebra ℂ Q] [Algebra ℂ C]
  [Algebra Q C] [IsScalarTower ℂ Q C]

/-- The exterior identity of ordinary differentials, with arbitrary coefficients. -/
theorem mixed_conormal_wedge (x v : Derivation ℂ Q C) (h n a : Q)
    (hx : x h = 0) (hf : algebraMap Q C h = 0) :
    mixed x v (exteriorPower.ιMulti Q 3 ![KaehlerDifferential.D ℂ Q h,
      KaehlerDifferential.D ℂ Q n, KaehlerDifferential.D ℂ Q a]) =
      -(v h • (x n • KaehlerDifferential.D ℂ C (algebraMap Q C a) -
        x a • KaehlerDifferential.D ℂ C (algebraMap Q C n))) := by
  let d := KaehlerDifferential.D ℂ Q
  let m := KaehlerDifferential.map ℂ ℂ Q C
  let l := v.liftKaehlerDifferential
  let k := x.liftKaehlerDifferential
  rw [mixed_wedge, Fin.sum_univ_three]
  change (-1 : ℤ)^0 • (k (d h) • (l (d n) • m (d a) - l (d a) • m (d n))) +
    (-1 : ℤ)^1 • (k (d n) • (l (d h) • m (d a) - l (d a) • m (d h))) +
    (-1 : ℤ)^2 • (k (d a) • (l (d h) • m (d n) - l (d n) • m (d h))) = _
  simp only [k, l, d, m, Derivation.liftKaehlerDifferential_comp_D, KaehlerDifferential.map_D,
    hx, hf, map_zero, smul_zero, sub_zero, zero_smul, pow_zero, pow_one, neg_one_sq,
    one_zsmul, neg_one_zsmul, zero_add, smul_sub]
  rw [smul_comm (v h) (x n), smul_comm (v h) (x a)]
  abel

end Exterior

attribute [local instance] CycleQ2LiteralAbelJacobiContraction.fixedCommRing
  CycleQ2LiteralAbelJacobiContraction.fixedAlgebra CycleQ2LiteralAbelJacobiContraction.fixedTower
  CycleQ2LiteralThreefoldSurfaceNormal.patchAlgebra CycleQ2LiteralThreefoldSurfaceNormal.patchTower

variable (i : Fin 4) (n a : P)
private abbrev patchJac := algebraMap (SurfaceChartRing (E i)) (Patch i n a) (augmentedJacobian (E i) n a)
private abbrev mk := Ideal.Quotient.mkₐ ℂ (fixedIdeal i)
private abbrev coord := algebraMap P (Patch i n a)

private theorem cubic_vanish : algebraMap (T i) (Patch i n a) (cubicOnT i) = 0 := by
  change coord i n a (seedH i) = 0
  rw [← native_cubic, IsScalarTower.algebraMap_apply P (SurfaceChartRing (E i)) (Patch i n a)]
  have hz : algebraMap P (SurfaceChartRing (E i)) (E i 1) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨1, rfl⟩)
  rw [hz, map_zero]

private theorem surface_residue : patchJac i n a • localSurfaceResidueForm (E i) n a =
    exteriorPower.ιMulti (Patch i n a) 2 ![KaehlerDifferential.D ℂ (Patch i n a) (coord i n a n),
      KaehlerDifferential.D ℂ (Patch i n a) (coord i n a a)] := by
  apply (localSurfaceDeterminantEquiv (E i) n a).injective
  rw [map_smul, localSurfaceResidueForm_normalization, smul_eq_mul, mul_one, localSurfaceDeterminantEquiv_pair]

variable {C : Type} [CommRing C] [Algebra ℂ C] [Algebra (T i) C] [Algebra (Patch i n a) C]
  [IsScalarTower ℂ (T i) C] [IsScalarTower ℂ (Patch i n a) C] [IsScalarTower (T i) (Patch i n a) C]

/-- Evaluation as an equality in the module of ordinary differentials on C. -/
theorem mixed_on_surface (x : Derivation ℂ (Patch i n a) C) (v : Derivation ℂ (T i) C) :
    mixed (x.compAlgebraMap (T i)) v (chartVolume i) =
      -(v (cubicOnT i) • contractRestrict x (localSurfaceResidueForm (E i) n a)) := by
  let k := x.compAlgebraMap (T i)
  have hx : k (cubicOnT i) = 0 := by change x (algebraMap (T i) (Patch i n a) (cubicOnT i)) = 0; rw [cubic_vanish, map_zero]
  have hf : algebraMap (T i) C (cubicOnT i) = 0 := by
    rw [IsScalarTower.algebraMap_apply (T i) (Patch i n a) C, cubic_vanish, map_zero]
  have hj : IsUnit (algebraMap (Patch i n a) C (patchJac i n a)) :=
    (IsLocalization.Away.algebraMap_isUnit (S := Patch i n a) _).map _
  apply (IsUnit.smul_left_cancel hj).mp
  have h := congrArg (mixed k v) (jacobian_smul_chartVolume i n a)
  rw [map_smulₛₗ, mixed_conormal_wedge k v _ _ _ hx hf,
    IsScalarTower.algebraMap_apply (T i) (Patch i n a) C, toSurface_jacobian] at h
  have hr := congrArg (contractRestrict x) (surface_residue i n a)
  rw [map_smul, contractRestrict_wedge] at hr
  simp only [Derivation.liftKaehlerDifferential_comp_D, KaehlerDifferential.map_D] at hr
  rw [← IsScalarTower.algebraMap_smul C (patchJac i n a)] at hr
  rw [smul_neg, smul_comm _ (v (cubicOnT i)), hr, h]
  simp only [IsScalarTower.algebraMap_apply (T i) (Patch i n a) C]
  rfl

section Orientation
variable (j : Fin 3) {S : Type} [CommRing S] [Algebra ℂ S] [Algebra (T j.succ) S]
  [Algebra (Patch j.succ n a) S] [IsScalarTower ℂ (T j.succ) S]
  [IsScalarTower ℂ (Patch j.succ n a) S] [IsScalarTower (T j.succ) (Patch j.succ n a) S]

/-- The signed cubic identity itself requires no projectivity on the coefficient algebra. -/
theorem oriented_double_form (x : Derivation ℂ (Patch j.succ n a) S) (v : Derivation ℂ (T j.succ) S)
    (hv : v (cubicOnT j.succ) = -(algebraMap (Patch j.succ n a) S (coord j.succ n a (tangentL j.succ)))) :
    mixed (x.compAlgebraMap (T j.succ)) v (orientedVolume j.succ) =
      -(contractRestrict x (orientedCubic n a j)) := by
  have hsign : (CycleQ2SurfaceCoordinateCubicFrames.orientation j : S) = -(-1 : S)^j.succ.val := by
    fin_cases j <;> norm_num [CycleQ2SurfaceCoordinateCubicFrames.orientation]
  rw [orientedVolume, orientedCubic, map_smulₛₗ, map_pow, map_neg, map_one,
    mixed_on_surface, hv, neg_smul, neg_neg, map_smul, map_smul,
    ← IsScalarTower.algebraMap_smul S (CycleQ2SurfaceCoordinateCubicFrames.orientation j : Patch j.succ n a),
    ← IsScalarTower.algebraMap_smul S (coord j.succ n a (tangentL j.succ)), map_intCast, hsign,
    neg_smul, neg_neg]

end Orientation

end CycleQ2ThreefoldMixedConormal
end

#print axioms CycleQ2ThreefoldMixedConormal.mixed_on_surface

#print axioms CycleQ2ThreefoldMixedConormal.oriented_double_form
