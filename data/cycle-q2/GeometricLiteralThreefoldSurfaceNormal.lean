import Proposal.GeometricLiteralThreefoldSurfaceAdjunction
import Proposal.GeometricSurfaceCoordinateCubicFrames
import Proposal.GeometricLiteralAbelJacobiEquations

/-!
# The moving normal in the oriented surface residue frame

On a Jacobian open of the original seed surface, two tangent arguments kill
its cubic equation. Inserting the moving normal into the threefold volume
on those two arguments therefore computes the native surface residue
multiplied by the value of the normal on the cubic.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 900000

noncomputable section
namespace CycleQ2LiteralThreefoldSurfaceNormal

open Module MvPolynomial CycleQ2GeometricSurfaceAdjunction
  CycleQ2GeometricSurfaceDeterminantNaturality CycleQ2LiteralAbelJacobiMovingNormal
  CycleQ2LiteralAbelJacobiEquations CycleQ2LiteralAbelJacobiContraction
  CycleQ2LiteralThreefoldResidueMinors CycleQ2LiteralThreefoldChartVolume
  CycleQ2LiteralThreefoldSurfaceAdjunction CycleQ2LiteralAbelJacobiRelativeNormal

variable (i : Fin 4) (n a : P)

abbrev E := CycleQ2GeometricSurfaceDehomogenizedCharts.dehomogenizedEquations 57 1 i
abbrev Patch := AdjunctionPatch (E i) n a
private abbrev D := SurfaceChartRing (E i)
private abbrev mk := Ideal.Quotient.mkₐ ℂ (fixedIdeal i)
private abbrev loc := algebraMap (D i) (Patch i n a)
private abbrev coord := algebraMap P (Patch i n a)

theorem native_fixed : E i 0 = seedF i := by
  rw [seedF, CycleQ2IncidenceChartSeedFiber.literal_pointEquationF,
    ← CycleQ2NormalConnecting.actualSeedEquation_eq_smoothF]
  rfl

theorem native_cubic : E i 1 = seedH i := by
  rw [seedH, CycleQ2IncidenceChartSeedFiber.literal_pointEquationH, CycleQ2NormalConnecting.smoothH_eq_thetaH]
  rfl

private theorem relation (b : Fin 2) : coord i n a (E i b) = 0 := by
  rw [IsScalarTower.algebraMap_apply P (D i) (Patch i n a)]
  have hz : algebraMap P (D i) (E i b) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨b, rfl⟩)
  rw [hz, map_zero]

/-- The actual restriction of fixed-threefold functions to the surface Jacobian open. -/
def toSurface : T i →ₐ[ℂ] Patch i n a :=
  Ideal.Quotient.liftₐ (fixedIdeal i) (IsScalarTower.toAlgHom ℂ P (Patch i n a))
    (fun _ hx => ((Ideal.span_singleton_le_iff_mem _).mpr
      (show seedF i ∈ RingHom.ker (coord i n a) from (native_fixed i) ▸ relation i n a 0)) hx)

local instance patchAlgebra : Algebra (T i) (Patch i n a) := (toSurface i n a).toRingHom.toAlgebra
local instance patchTower : IsScalarTower ℂ (T i) (Patch i n a) := IsScalarTower.of_algHom (toSurface i n a)

private theorem toSurface_mk (b : P) : algebraMap (T i) (Patch i n a) (mk i b) = coord i n a b := rfl

private theorem toSurface_h : algebraMap (T i) (Patch i n a) (cubicOnT i) = 0 := by
  change coord i n a (seedH i) = 0
  rw [← native_cubic]
  exact relation i n a 1

theorem toSurface_jacobian :
    algebraMap (T i) (Patch i n a) (jacobian i n a) = loc i n a (augmentedJacobian (E i) n a) := by
  refine Eq.trans ?_ (congrArg (loc i n a) (augmentedJacobian_polynomial (E i) n a)).symm
  rw [jacobian, Pi.basisFun_det_apply, RingHom.map_det, RingHom.map_det]
  apply congrArg Matrix.det
  ext j k
  fin_cases j
  · change coord i n a (pderiv (coordIndex k) (seedF i)) = coord i n a (pderiv (coordIndex k) (E i 0))
    rw [native_fixed]
  · change coord i n a (pderiv (coordIndex k) (seedH i)) = coord i n a (pderiv (coordIndex k) (E i 1))
    rw [native_cubic]
  · rfl
  · rfl

private theorem jacobian_smul_surfaceResidue :
    loc i n a (augmentedJacobian (E i) n a) • localSurfaceResidueForm (E i) n a =
      exteriorPower.ιMulti (Patch i n a) 2 ![KaehlerDifferential.D ℂ (Patch i n a) (coord i n a n),
        KaehlerDifferential.D ℂ (Patch i n a) (coord i n a a)] := by
  apply (localSurfaceDeterminantEquiv (E i) n a).injective
  rw [map_smul, localSurfaceResidueForm_normalization, smul_eq_mul, mul_one, localSurfaceDeterminantEquiv_pair]

section Restriction

variable {S : Type} [CommRing S] [Algebra ℂ S] [Algebra (T i) S] [Algebra (Patch i n a) S]
  [IsScalarTower ℂ (T i) S] [IsScalarTower ℂ (Patch i n a) S] [IsScalarTower (T i) (Patch i n a) S]

/-- Evaluation on the transverse normal and two honest surface derivations
is the value on the fixed cubic times the normalized surface residue. -/
theorem volume_on_surface (v : Derivation ℂ (T i) S) (x y : Derivation ℂ (Patch i n a) S) :
    evaluate ![v, x.compAlgebraMap (T i), y.compAlgebraMap (T i)] (chartVolume i) =
      v (cubicOnT i) * evaluate ![x,y] (localSurfaceResidueForm (E i) n a) := by
  let j := loc i n a (augmentedJacobian (E i) n a)
  have hj : IsUnit (algebraMap (Patch i n a) S j) :=
    (IsLocalization.Away.algebraMap_isUnit (S := Patch i n a) _).map _
  have hv := tangent_evaluation i v (x.compAlgebraMap (T i)) (y.compAlgebraMap (T i)) n a
    (show x (algebraMap (T i) (Patch i n a) (cubicOnT i)) = 0 by rw [toSurface_h, map_zero])
    (show y (algebraMap (T i) (Patch i n a) (cubicOnT i)) = 0 by rw [toSurface_h, map_zero])
  have hr := congrArg (evaluate ![x,y]) (jacobian_smul_surfaceResidue i n a)
  rw [map_smulₛₗ, smul_eq_mul, evaluate_two] at hr
  rw [IsScalarTower.algebraMap_apply (T i) (Patch i n a) S, toSurface_jacobian] at hv
  apply hj.mul_left_cancel
  rw [mul_left_comm, hv]
  exact congrArg (v (cubicOnT i) * ·) hr.symm

end Restriction

section Orientation

variable (j : Fin 3)
private abbrev orientation := CycleQ2SurfaceCoordinateCubicFrames.orientation

/-- The projective threefold orientation on its native weight-one chart. -/
def orientedVolume (k : Fin 4) := (-1 : T k)^k.val • chartVolume k

/-- The residue with the chart coefficient and signs of the original global
canonical section of the retained incidence cubic. -/
def orientedCubic := (orientation j : Patch j.succ n a) •
  (coord j.succ n a (tangentL j.succ) • localSurfaceResidueForm (E j.succ) n a)

variable {S : Type} [CommRing S] [Algebra ℂ S] [Algebra (T j.succ) S] [Algebra (Patch j.succ n a) S]
  [IsScalarTower ℂ (T j.succ) S] [IsScalarTower ℂ (Patch j.succ n a) S]
  [IsScalarTower (T j.succ) (Patch j.succ n a) S]

private theorem signs : (orientation j : S) = -(-1 : S)^j.succ.val := by
  fin_cases j <;> norm_num [orientation, CycleQ2SurfaceCoordinateCubicFrames.orientation]

theorem oriented_normal_evaluation (v : Derivation ℂ (T j.succ) S)
    (hv : v (cubicOnT j.succ) = -(algebraMap (Patch j.succ n a) S (coord j.succ n a (tangentL j.succ))))
    (x y : Derivation ℂ (Patch j.succ n a) S) :
    evaluate ![v, x.compAlgebraMap (T j.succ), y.compAlgebraMap (T j.succ)] (orientedVolume j.succ) =
      evaluate ![x,y] (orientedCubic n a j) := by
  unfold orientedVolume orientedCubic
  simp only [map_smulₛₗ, smul_eq_mul, map_pow, map_neg, map_one,
    volume_on_surface, hv, signs]
  ring

/-- Inserting the surface tangent first and then the moving curve normal changes
the sign of the evaluated native cubic two-form. -/
theorem oriented_double_contraction (v : Derivation ℂ (T j.succ) S)
    (hv : v (cubicOnT j.succ) = -(algebraMap (Patch j.succ n a) S (coord j.succ n a (tangentL j.succ))))
    (x y : Derivation ℂ (Patch j.succ n a) S) :
    evaluate ![x.compAlgebraMap (T j.succ), v, y.compAlgebraMap (T j.succ)] (orientedVolume j.succ) =
      -(evaluate ![x,y] (orientedCubic n a j)) := by
  rw [evaluate_swap v, oriented_normal_evaluation n a j v hv x y]

end Orientation

end CycleQ2LiteralThreefoldSurfaceNormal
end

#print axioms CycleQ2LiteralThreefoldSurfaceNormal.volume_on_surface
#print axioms CycleQ2LiteralThreefoldSurfaceNormal.oriented_double_contraction
