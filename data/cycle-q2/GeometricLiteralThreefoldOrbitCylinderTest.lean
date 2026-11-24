import Proposal.GeometricLiteralThreefoldOrbitInvariance
import Proposal.GeometricLiteralThreefoldOrbitCylinderPull
import Proposal.GeometricLiteralAbelJacobiQTest
import Proposal.GeometricSheafCohomologyScalar

/-!
# The cyclic sum of the moving correspondence on the ambient test

The three translated second projections have the same pullback of the test.
An additive evaluation on their sum therefore gives three times its value on
the original family.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace CycleQ2LiteralThreefoldOrbitCylinderTest

open CategoryTheory AlgebraicGeometry CycleQ2LiteralThreefoldOrbitAction CycleQ2LiteralThreefoldOrbitCylinderPull
  CycleQ2LiteralThreefoldOrbitInvariance CycleQ2LiteralThreefoldTestClass
  CycleQ2LiteralThreefoldTestEdges CycleQ2LiteralAbelJacobiQPullback
  CycleQ2LiteralAbelJacobiQTest
  CycleQ2IncidenceEtaleParameter CycleQ2LiteralOrbitAction CycleQ2LiteralAbelJacobiTimeFamily
  CycleQ2LiteralThreefoldHodgeCech CycleQ2GeometricSheafCohomologyScalar
open CycleQ2LiteralAbelJacobiQPullbackDerived (qHodge)

local instance (S : Scheme.{0}) : HasExt.{1} (CycleQ2InjectiveCech.AbSheaf (show TopCat from S)) :=
  HasExt.standard _

variable (z : ℂ) (hz : z^3 = 1)

/-- Every translated moving-family correspondence pulls the fixed ambient
test back to the same derived two-form class on the original time family. -/
theorem translatedCylinderPull_ambientTestClass (V : parameterScheme.Opens) (t : Fin 3 → ℂ) :
    translatedCylinderPull (threefoldAction z hz) (threefoldAction_overComplex z hz) V t
      ambientTestClass = pulledTestClass V t := by
  have h := translatedCylinderPull_class (threefoldAction z hz) (threefoldAction_overComplex z hz)
    V t nativeEdge face
  exact h.trans ((congrArg (qHodge V t) (ambientTestClass_fixed z hz)).trans
    (qHodge_ambientTestClass V t))

include hz in
private theorem square_root : (z^2)^3 = 1 := by
  simpa only [pow_two] using cubeRoot_mul hz hz

theorem translatedTwice :
    (threefoldAction z hz).hom ≫ (threefoldAction z hz).hom =
      (threefoldAction (z^2) (square_root z hz)).hom := by
  simpa only [pow_two] using threefoldAction_hom_comp z z hz hz

variable (V : parameterScheme.Opens) (t : Fin 3 → ℂ)

/-- Sum of the actual pullbacks for the original and its two translates. -/
def orbitCylinderPull :=
  qHodge V t +
  translatedCylinderPull (threefoldAction z hz) (threefoldAction_overComplex z hz) V t +
  translatedCylinderPull (threefoldAction (z^2) (square_root z hz))
    (threefoldAction_overComplex _ _) V t

theorem orbitCylinderPull_test :
    orbitCylinderPull z hz V t ambientTestClass = 3 • pulledTestClass V t := by
  simp only [orbitCylinderPull, AddMonoidHom.add_apply, qHodge_ambientTestClass,
    translatedCylinderPull_ambientTestClass, three_nsmul, add_assoc]

/-- The normalized three-term average on the complex cohomology of the moving family. -/
def averagedCylinderPull : Hodge21 →+ (familyHodgeSheaf V t).H' 1 ⊤ :=
  (cohomologyScalar (family V t).sheaf (familyCoefficient V t) (familyTwoForms V t) 1 ⊤
    (3 : ℂ)⁻¹).comp (orbitCylinderPull z hz V t)

theorem averagedCylinderPull_test :
    averagedCylinderPull z hz V t ambientTestClass = pulledTestClass V t := by
  letI : Module ℂ ((familyHodgeSheaf V t).H' 1 ⊤) :=
    cohomologyModule (family V t).sheaf (familyCoefficient V t) (familyTwoForms V t) 1 ⊤
  change (3 : ℂ)⁻¹ • orbitCylinderPull z hz V t ambientTestClass = _
  rw [orbitCylinderPull_test, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  norm_num

/-- A nonzero complex evaluation on the original family detects its cyclic sum. -/
theorem orbitCylinderPull_test_detected
    (ev : (familyHodgeSheaf V t).H' 1 ⊤ →+ ℂ) (hne : ev (pulledTestClass V t) ≠ 0) :
    ev (orbitCylinderPull z hz V t ambientTestClass) ≠ 0 := by
  rw [orbitCylinderPull_test, map_nsmul, nsmul_eq_mul]
  exact mul_ne_zero (by norm_num) hne

/-- The full cubic-root average for the same primitive root used in the
three translates of the original curve. -/
theorem primitiveAverage_test :
    averagedCylinderPull CycleQ2LinkageComponentAlgebra.complexRoot
      CycleQ2LinkageComponentAlgebra.complexRoot_cube V t ambientTestClass = pulledTestClass V t :=
  averagedCylinderPull_test _ _ V t

end CycleQ2LiteralThreefoldOrbitCylinderTest
end

#print axioms CycleQ2LiteralThreefoldOrbitCylinderTest.orbitCylinderPull_test
#print axioms CycleQ2LiteralThreefoldOrbitCylinderTest.orbitCylinderPull_test_detected

#print axioms CycleQ2LiteralThreefoldOrbitCylinderTest.averagedCylinderPull_test
