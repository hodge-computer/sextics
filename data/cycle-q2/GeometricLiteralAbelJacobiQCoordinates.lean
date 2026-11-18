import Proposal.GeometricLiteralIncidenceCylinderMap
import Proposal.GeometricLiteralCylinderEvaluation
import Proposal.GeometricGradedAwaySpecialization

/-!
# Homogeneous coordinates of the moving curve in the fixed sextic

On each weight-one chart, the projection of the original section curve and
the dehomogenized map used for contraction agree on every homogeneous
fraction, both over the dual numbers and on the seed fibre.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralAbelJacobiQCoordinates

open MvPolynomial HomogeneousLocalization
open scoped DualNumber TensorProduct
open CycleQ2IncidenceUniversalChart CycleQ2IncidenceImageLine CycleQ2GeometricIncidenceProj
  CycleQ2IncidenceFamilyContainment CycleQ2IncidenceEtaleParameter CycleQ2IncidenceDehomogenizedChart
  CycleQ2RelativeConstantCurve CycleQ2RelativeCurveChart CycleQ2IncidencePolynomialJacobianBinding
  CycleQ2IncidenceTimeCurve CycleQ2LiteralIncidenceTimeCurve CycleQ2LiteralIncidenceCylinderMap
  CycleQ2GradedAwaySpecialization CycleQ2IncidenceChartSeedFiber
  CycleQ2LiteralAbelJacobiEquations CycleQ2LiteralAbelJacobiMovingNormal
  CycleQ2LiteralAbelJacobiContraction CycleQ2LiteralCylinderEvaluation
  CycleQ2IncidenceFirstOrder

attribute [local instance] CycleQ2IncidenceTimeCurve.timeParameterCommRing
  CycleQ2IncidenceSeedFiber.seedAlgebra
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderAlgebra
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderModule
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderSMul
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderTower

section Sextic

variable {R S : Type} [CommRing R] [CommRing S] [Algebra ℂ R] [Algebra ℂ S]

def sexticX (y : ParameterIndex → R) (i : Fin 4) :=
  Ideal.Quotient.mk (sexticIdeal y) (X i.castSucc)

theorem sexticX_mem (y : ParameterIndex → R) (i : Fin 4) : sexticX y i ∈ sexticGrade y 1 :=
  ⟨X i.castSucc, by
    change (X i.castSucc : MvPolynomial (Fin 5) R).IsWeightedHomogeneous geometricWeight 1
    simpa only [weight_castSucc] using isWeightedHomogeneous_X R geometricWeight i.castSucc, rfl⟩

abbrev SexticChart (y : ParameterIndex → R) (i : Fin 4) := Away (sexticGrade y) (sexticX y i)

def sexticFraction (y : ParameterIndex → R) (i : Fin 4) (n : ℕ) (p : MvPolynomial (Fin 5) R)
    (hp : p.IsWeightedHomogeneous geometricWeight n) : SexticChart y i :=
  Away.mk (sexticGrade y) (sexticX_mem y i) n (Ideal.Quotient.mk _ p)
    ⟨p, by simpa using hp, rfl⟩

theorem sexticFraction_surjective (y : ParameterIndex → R) (i : Fin 4) (a : SexticChart y i) :
    ∃ n p hp, sexticFraction y i n p hp = a := by
  obtain ⟨n, _, ⟨p, hp, rfl⟩, rfl⟩ := Away.mk_surjective (sexticGrade y) (sexticX_mem y i) a
  exact ⟨n, p, by simpa using hp, rfl⟩

variable (φ : R →+* S) (y : ParameterIndex → R) (u : ParameterIndex → S)
    (hF : map φ (pointEquationF y) = pointEquationF u)

theorem coefficientX (i : Fin 4) :
    CycleQ2ThreefoldCoefficientMap.graded φ y u hF (sexticX y i) = sexticX u i := by
  exact congrArg (Ideal.Quotient.mk (sexticIdeal u)) (MvPolynomial.map_X φ i.castSucc)

def coefficientChart (i : Fin 4) : SexticChart y i →+* SexticChart u i :=
  awayMapOfEq (CycleQ2ThreefoldCoefficientMap.graded φ y u hF) _ _ (coefficientX φ y u hF i)

theorem coefficientChart_fraction (i : Fin 4) (n : ℕ) (p : MvPolynomial (Fin 5) R)
    (hp : p.IsWeightedHomogeneous geometricWeight n) :
    coefficientChart φ y u hF i (sexticFraction y i n p hp) =
      sexticFraction u i n (map φ p) ((polynomialCoefficientMap φ).map_mem hp) := by
  unfold coefficientChart sexticFraction
  exact awayMapOfEq_mk _ _ _ _ _ (sexticX_mem u i) _ _ _

def surfaceChart (u : ParameterIndex → S) (i : Fin 4) : SexticChart u i →+* CoordinateRing u i :=
  Away.map (surfaceThreefoldRingMap u) (sexticX u i)

theorem surfaceChart_fraction (u : ParameterIndex → S) (i : Fin 4) (n : ℕ)
    (p : MvPolynomial (Fin 5) S) (hp : p.IsWeightedHomogeneous geometricWeight n) :
    surfaceChart u i (sexticFraction u i n p hp) = homogeneousFraction u i n p hp := by
  unfold surfaceChart sexticFraction
  exact Away.map_mk (surfaceThreefoldRingMap u) _ _ _ _ _

end Sextic

private abbrev seedPt := seedPoint (57 : ℂ) Complex.I
abbrev fixedCoefficient := seedMap.comp sexticToParameter

theorem fixedCoefficient_equation : map fixedCoefficient (pointEquationF universalPoint) = pointEquationF seedPt := by
  rw [fixedCoefficient, ← MvPolynomial.map_map, universal_to_incidence, CycleQ2EtaleIncidenceCurve.seed_sextic,
    literal_pointEquationF]

private def nativeOnCone (i : Fin 4) :
    CycleQ2IncidenceFamilyContainment.SexticRing seedPt →+* T i :=
  Ideal.Quotient.lift (sexticIdeal seedPt) ((Ideal.Quotient.mk (fixedIdeal i)).comp (dehomogenize i).toRingHom)
    (by
      change Ideal.span {pointEquationF seedPt} ≤ RingHom.ker
        ((Ideal.Quotient.mk (fixedIdeal i)).comp (dehomogenize i).toRingHom)
      apply (Ideal.span_singleton_le_iff_mem _).mpr
      change Ideal.Quotient.mk (fixedIdeal i) (seedF i) = 0
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _)))

private theorem nativeOnCone_X (i : Fin 4) : nativeOnCone i (sexticX seedPt i) = 1 := by
  change Ideal.Quotient.mk (fixedIdeal i) (dehomogenize i (X i.castSucc)) = 1
  rw [dehomogenize_self, map_one]

def nativeToT (i : Fin 4) : SexticChart seedPt i →+* T i :=
  (Localization.awayLift (nativeOnCone i) (sexticX seedPt i)
    (isUnit_iff_exists_inv.mpr ⟨1, by rw [nativeOnCone_X, mul_one]⟩)).comp
    (algebraMap (SexticChart seedPt i) (Localization.Away (sexticX seedPt i)))

theorem nativeToT_fraction (i : Fin 4) (n : ℕ) (p : MvPolynomial (Fin 5) ℂ)
    (hp : p.IsWeightedHomogeneous geometricWeight n) :
    nativeToT i (sexticFraction seedPt i n p hp) =
      Ideal.Quotient.mk (fixedIdeal i) (dehomogenize i p) := by
  change Localization.awayLift (nativeOnCone i) (sexticX seedPt i)
    (isUnit_iff_exists_inv.mpr ⟨1, by rw [nativeOnCone_X, mul_one]⟩)
    (Localization.mk (Ideal.Quotient.mk (sexticIdeal seedPt) p)
      ⟨sexticX seedPt i ^ n, n, rfl⟩) = _
  trans nativeOnCone i (Ideal.Quotient.mk (sexticIdeal seedPt) p)
  · simpa only [one_pow, mul_one] using
      (Localization.awayLift_mk (nativeOnCone i) (sexticX seedPt i) (Ideal.Quotient.mk _ p) 1
        (by rw [nativeOnCone_X, mul_one]) n)
  · rfl

def universalToT (i : Fin 4) : SexticChart universalPoint i →+* T i :=
  (nativeToT i).comp (coefficientChart fixedCoefficient universalPoint seedPt fixedCoefficient_equation i)

def universalToOriginal (t : Fin 3 → ℂ) (i : Fin 4) :
    SexticChart universalPoint i →+* CurveCoordinateRing incidencePoint t i :=
  (coordinateCurveMap incidencePoint t i).toRingHom.comp
    ((surfaceChart incidencePoint i).comp
      (coefficientChart sexticToParameter universalPoint incidencePoint universal_to_incidence i))

def originalToFirst (t : Fin 3 → ℂ) (i : Fin 4) :
    CurveCoordinateRing incidencePoint t i →+* B t i :=
  (Algebra.TensorProduct.includeRight (R := ParameterAlgebra) (A := ℂ[ε])
    (B := AffineCurveChart incidencePoint t i)).toRingHom.comp
      (curveCoordinateChartEquiv incidencePoint t i).toRingHom

theorem firstOrder_compatibility (t : Fin 3 → ℂ) (i : Fin 4) :
    (originalToFirst t i).comp (universalToOriginal t i) = (toFamily t i).comp (universalToT i) := by
  apply RingHom.ext
  intro a
  obtain ⟨n, p, hp, rfl⟩ := sexticFraction_surjective universalPoint i a
  change (Algebra.TensorProduct.includeRight (R := ParameterAlgebra) (A := ℂ[ε])
    (B := AffineCurveChart incidencePoint t i)) (curveCoordinateChartEquiv incidencePoint t i
      (coordinateCurveMap incidencePoint t i (surfaceChart incidencePoint i
        (coefficientChart sexticToParameter universalPoint incidencePoint universal_to_incidence i
          (sexticFraction universalPoint i n p hp))))) =
    toFamily t i (nativeToT i (coefficientChart fixedCoefficient universalPoint seedPt
      fixedCoefficient_equation i (sexticFraction universalPoint i n p hp)))
  rw [coefficientChart_fraction, coefficientChart_fraction, surfaceChart_fraction, nativeToT_fraction,
    curveCoordinateChartEquiv_map, familyCoordinateChartEquiv_homogeneousFraction]
  change relativeEval t i (dehomogenize i (map sexticToParameter p)) =
    chartMap t i (dehomogenize i (map fixedCoefficient p))
  rw [← dualEval_parameter, ← dualEval_constant, map_dehomogenize, map_dehomogenize,
    MvPolynomial.map_map, MvPolynomial.map_map, firstOrder_constant_sextic]

def originalToSeed (t : Fin 3 → ℂ) (i : Fin 4) : CurveCoordinateRing incidencePoint t i →+* A t i :=
  (CycleQ2RelativeCurveChartFiber.curveChartSpecialization t i).comp
    (curveCoordinateChartEquiv incidencePoint t i).toRingHom

theorem originalToFirst_reduction (t : Fin 3 → ℂ) (i : Fin 4) :
    (toClosed t i).comp (originalToFirst t i) = originalToSeed t i :=
  RingHom.ext fun a => CycleQ2FirstOrderChartReduction.curveChartReductionEquiv_includeRight t i
    (curveCoordinateChartEquiv incidencePoint t i a)

theorem closed_compatibility (t : Fin 3 → ℂ) (i : Fin 4) :
    (originalToSeed t i).comp (universalToOriginal t i) =
      (CycleQ2LiteralAbelJacobiContraction.toCurve t i).toRingHom.comp (universalToT i) := by
  rw [← originalToFirst_reduction, RingHom.comp_assoc, firstOrder_compatibility]
  apply RingHom.ext
  intro a
  obtain ⟨p, hp⟩ := Ideal.Quotient.mk_surjective (universalToT i a)
  simp only [RingHom.comp_apply, ← hp]
  exact chartMap_reduction t i p

end CycleQ2LiteralAbelJacobiQCoordinates

#print axioms CycleQ2LiteralAbelJacobiQCoordinates.nativeToT_fraction
#print axioms CycleQ2LiteralAbelJacobiQCoordinates.firstOrder_compatibility
#print axioms CycleQ2LiteralAbelJacobiQCoordinates.closed_compatibility
