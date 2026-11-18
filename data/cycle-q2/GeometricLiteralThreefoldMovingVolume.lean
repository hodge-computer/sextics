import Proposal.GeometricLiteralThreefoldSurfaceNormal
import Proposal.GeometricLiteralAbelJacobiSmoothNormal

/-!
# Evaluation of the fixed volume on the moving section curve

The coefficient ring is the actual Jacobian localization of a seed section
curve chart. Its surface and threefold maps commute with the original
restriction, and localization sends the original normal representative
to a vector along this same curve chart.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1100000

noncomputable section
namespace CycleQ2LiteralThreefoldMovingVolume

open scoped DualNumber
open CycleQ2LiteralAbelJacobiMovingNormal CycleQ2LiteralAbelJacobiContraction
  CycleQ2LiteralAbelJacobiRelativeNormal CycleQ2LiteralAbelJacobiEquations
  CycleQ2LiteralThreefoldSurfaceNormal CycleQ2GeometricSurfaceAdjunction
  CycleQ2LiteralThreefoldSurfaceAdjunction

attribute [local instance] CycleQ2IncidenceSeedFiber.seedAlgebra
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderAlgebra
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderModule
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderSMul
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderTower
  CycleQ2LiteralAbelJacobiContraction.fixedAlgebra
  CycleQ2LiteralAbelJacobiContraction.fixedTower
  CycleQ2LiteralAbelJacobiContraction.fixedCommRing
  CycleQ2LiteralAbelJacobiContraction.seedChartCommRing
  CycleQ2LiteralAbelJacobiMovingNormal.thickCommRing
  CycleQ2LiteralThreefoldSurfaceNormal.patchAlgebra
  CycleQ2LiteralThreefoldSurfaceNormal.patchTower

variable (t : Fin 3 → ℂ) (i : Fin 4) (n a : P)

private abbrev D := SurfaceChartRing (E i)

/-- The native surface presentation restricted to the original seed section curve. -/
def surfaceToCurve : D i →ₐ[ℂ] A t i :=
  Ideal.Quotient.liftₐ (surfaceChartIdeal (E i)) (toSeedChart t i) (by
    change Ideal.span (Set.range (E i)) ≤ RingHom.ker (seedChartMap t i)
    apply Ideal.span_le.mpr
    rintro _ ⟨j, rfl⟩
    fin_cases j
    · change E i 0 ∈ RingHom.ker (seedChartMap t i)
      rw [native_fixed]
      exact (sexticEquation t i).property
    · change E i 1 ∈ RingHom.ker (seedChartMap t i)
      rw [native_cubic]
      exact (cubicEquation t i).property)

/-- The original curve over the actual surface Jacobian open. -/
abbrev CurvePatch := Localization.Away (surfaceToCurve t i (augmentedJacobian (E i) n a))

local instance curvePatchRing : CommRing (CurvePatch t i n a) := inferInstance
local instance curveBaseAlgebra : Algebra (A t i) (CurvePatch t i n a) :=
  inferInstanceAs (Algebra (A t i) (Localization.Away (surfaceToCurve t i (augmentedJacobian (E i) n a))))
local instance curveBaseSMul : SMul (A t i) (CurvePatch t i n a) := (curveBaseAlgebra t i n a).toSMul
local instance curveBaseModule : Module (A t i) (CurvePatch t i n a) := (curveBaseAlgebra t i n a).toModule
local instance curveComplexAlgebra : Algebra ℂ (CurvePatch t i n a) :=
  inferInstanceAs (Algebra ℂ (Localization.Away (surfaceToCurve t i (augmentedJacobian (E i) n a))))
local instance curveComplexSMul : SMul ℂ (CurvePatch t i n a) := (curveComplexAlgebra t i n a).toSMul
local instance curveComplexModule : Module ℂ (CurvePatch t i n a) := (curveComplexAlgebra t i n a).toModule
local instance curveComplexTower : IsScalarTower ℂ (A t i) (CurvePatch t i n a) :=
  IsScalarTower.of_algebraMap_eq' rfl

private abbrev curveLoc := IsScalarTower.toAlgHom ℂ (A t i) (CurvePatch t i n a)
private abbrev surfaceMap := Localization.awayMapₐ (surfaceToCurve t i) (augmentedJacobian (E i) n a)
private abbrev fixedMap := (curveLoc t i n a).comp (toCurve t i)

local instance surfaceAlgebra : Algebra (Patch i n a) (CurvePatch t i n a) :=
  (surfaceMap t i n a).toRingHom.toAlgebra
local instance surfaceTower : IsScalarTower ℂ (Patch i n a) (CurvePatch t i n a) :=
  IsScalarTower.of_algHom (surfaceMap t i n a)
local instance fixedAlgebra : Algebra (T i) (CurvePatch t i n a) := (fixedMap t i n a).toRingHom.toAlgebra
local instance fixedSMul : SMul (T i) (CurvePatch t i n a) := (fixedAlgebra t i n a).toSMul
local instance fixedModule : Module (T i) (CurvePatch t i n a) := (fixedAlgebra t i n a).toModule
local instance fixedTower : IsScalarTower ℂ (T i) (CurvePatch t i n a) := IsScalarTower.of_algHom (fixedMap t i n a)
local instance closedTower : IsScalarTower (T i) (A t i) (CurvePatch t i n a) :=
  IsScalarTower.of_algebraMap_eq (R := T i) (S := A t i) (A := CurvePatch t i n a) fun _ => rfl

private theorem surfaceMap_mk (p : P) :
    surfaceMap t i n a (algebraMap P (Patch i n a) p) = curveLoc t i n a (seedChartMap t i p) := by
  rw [IsScalarTower.algebraMap_apply P (D i) (Patch i n a)]
  change Localization.awayMap (surfaceToCurve t i).toRingHom _
    (algebraMap (D i) (Patch i n a) (algebraMap P (D i) p)) = _
  rw [Localization.awayMap, IsLocalization.Away.map, IsLocalization.map_eq]
  rfl

local instance restrictionTower : IsScalarTower (T i) (Patch i n a) (CurvePatch t i n a) := by
  apply IsScalarTower.of_algebraMap_eq (R := T i) (S := Patch i n a) (A := CurvePatch t i n a)
  intro b
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective b
  exact (surfaceMap_mk t i n a p).symm

/-- An original ambient representative of the deformation, with its coefficients
restricted to the Jacobian open of the very same curve. -/
def restrictNormal (v : Derivation ℂ (T i) (A t i)) : Derivation ℂ (T i) (CurvePatch t i n a) :=
  ((Algebra.linearMap (A t i) (CurvePatch t i n a)).restrictScalars (T i)).compDer v

variable (j : Fin 3)

theorem moving_double_contraction [Module.Flat ℂ[ε] (B t j.succ)]
    (v : Derivation ℂ (T j.succ) (A t j.succ))
    (hv : ∀ e : idealOnT t j.succ,
      v e.val = relativeNormal t j.succ ((idealOnT t j.succ).toCotangent e))
    (x y : Derivation ℂ (Patch j.succ n a) (CurvePatch t j.succ n a)) :
    evaluate ![x.compAlgebraMap (T j.succ), restrictNormal t j.succ n a v, y.compAlgebraMap (T j.succ)]
      (orientedVolume j.succ) = -(evaluate ![x,y] (orientedCubic n a j)) := by
  apply oriented_double_contraction
  have hh := (hv (cubicClass t j.succ)).trans (relativeNormal_cubic t j.succ)
  change v (cubicOnT j.succ) = -(seedChartMap t j.succ (tangentL j.succ)) at hh
  change curveLoc t j.succ n a (v (cubicOnT j.succ)) =
    -(surfaceMap t j.succ n a (algebraMap P (Patch j.succ n a) (tangentL j.succ)))
  rw [hh, map_neg, surfaceMap_mk]

/-- A smooth original seed curve chart has an actual representative giving the
signed evaluation on all genuine surface tangent pairs on its Jacobian open. -/
theorem exists_moving_double_contraction [Module.Flat ℂ[ε] (B t j.succ)]
    [Algebra.FormallySmooth ℂ (A t j.succ)] :
    ∃ v : Derivation ℂ (T j.succ) (A t j.succ),
      (∀ e : idealOnT t j.succ,
        v e.val = relativeNormal t j.succ ((idealOnT t j.succ).toCotangent e)) ∧
      ∀ x y : Derivation ℂ (Patch j.succ n a) (CurvePatch t j.succ n a),
        evaluate ![x.compAlgebraMap (T j.succ), restrictNormal t j.succ n a v, y.compAlgebraMap (T j.succ)]
          (orientedVolume j.succ) = -(evaluate ![x,y] (orientedCubic n a j)) := by
  obtain ⟨v, hv, _⟩ := exists_moving_representative t j.succ
  exact ⟨v, hv, moving_double_contraction t n a j v hv⟩

/-- One ambient representative for an algebraically independent section evaluates
on every Jacobian open of this chart. -/
theorem independent_double_contraction (ht : AlgebraicIndependent ℚ t) :
    ∃ v : Derivation ℂ (T j.succ) (A t j.succ), ∀ (n a : P)
      (x y : Derivation ℂ (Patch j.succ n a) (CurvePatch t j.succ n a)),
      evaluate ![x.compAlgebraMap (T j.succ), restrictNormal t j.succ n a v, y.compAlgebraMap (T j.succ)]
        (orientedVolume j.succ) = -(evaluate ![x,y] (orientedCubic n a j)) := by
  have hc := CycleQ2LiteralAbelJacobiBertiniMinor.prime_minor_of_independent t ht
  have hs := (CycleQ2LiteralAbelJacobiSeedLift.smooth_neighborhood_of_seed_minors t hc).1
  have := CycleQ2LiteralAbelJacobiSmoothNormal.flat_charts_of_smooth t hs j.succ
  have := CycleQ2LiteralAbelJacobiSmoothNormal.seedChart_smooth_of_minors t hc j.succ
  obtain ⟨v, hv, _⟩ := exists_moving_representative t j.succ
  exact ⟨v, fun n a => moving_double_contraction t n a j v hv⟩

section GlobalSection

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
  CycleQ2GeometricSurfaceDehomogenizedCharts CycleQ2GeometricSurfaceJacobianCharts
  CycleQ2GeometricAffineChartSections CycleQ2GeometricPrincipalChartSections
  CycleQ2SurfaceCoordinateFrames CycleQ2SurfaceCoordinateCubicFrames
  CycleQ2IncidenceFirstOrderCanonicalH2 CycleQ2GlobalSurfaceCubics

private abbrev chart (j : Fin 3) := coordinateAffineChart 57 1 j.succ
private abbrev J (j : Fin 3) := augmentedJacobian (E j.succ) n a

/-- The localized cubic form and the global cubic section
use exactly the same coordinate in the published projective residue frame. -/
theorem global_cubic_coordinate (V : Over (principalOpen (chart j) (J n a j))) :
    (show Γ(CycleQ2SurfaceCoordinateFrames.Surface, V.left) from
      (coordinateExteriorFrame j).app V.left (V.hom.le.trans (principalOpen_le _ _))
        (CycleQ2SurfaceCoordinateFrames.CanonicalForms.val.map V.left.leTop.op
          (globalCubicSection firstOrderWeightedCubic))) =
    chartSection (principalChart (chart j) (J n a j)) V
      (localSurfaceDeterminantEquiv (E j.succ) n a (orientedCubic n a j)) := by
  have hg := coordinateExteriorFrame_globalCubic firstOrderWeightedCubic j V.left
    (V.hom.le.trans (principalOpen_le (chart j) (J n a j)))
  refine hg.trans ?_
  have hc : localSurfaceDeterminantEquiv (E j.succ) n a (orientedCubic n a j) =
      (orientation j : Patch j.succ n a) * algebraMap P (Patch j.succ n a) (tangentL j.succ) := by
    unfold orientedCubic
    simp only [map_smul, localSurfaceResidueForm_normalization, smul_eq_mul, mul_one]
  rw [hc, map_mul, map_intCast]
  congr 1
  exact (principal_chartSection (chart j) (J n a j) V
    (dehomogenizedMap 57 1 j.succ (CycleQ2GeometricSurfaceDehomogenizedCharts.dehomogenize j.succ
      firstOrderWeightedCubic.val))).symm

end GlobalSection

end CycleQ2LiteralThreefoldMovingVolume
end

#print axioms CycleQ2LiteralThreefoldMovingVolume.moving_double_contraction
#print axioms CycleQ2LiteralThreefoldMovingVolume.exists_moving_double_contraction
#print axioms CycleQ2LiteralThreefoldMovingVolume.independent_double_contraction
#print axioms CycleQ2LiteralThreefoldMovingVolume.global_cubic_coordinate
