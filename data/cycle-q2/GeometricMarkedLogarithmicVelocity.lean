import Proposal.GeometricUniversalWeightedDeRham
import Proposal.GeometricFamilyDeformation
import Proposal.GeometricLiteralThreefoldVertexMotion

/-!
# Logarithmic velocity on the marked cubic charts

On the original marked time tangent, contract the two-equation logarithmic
symbol with the coefficient of ε. Clearing the two equations and wedging with
the cubic differential leaves minus the cubic velocity times the regular
conormal wedge. On the curve this coefficient agrees with the actual motion
of the cubic in the fixed threefold.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false

noncomputable section
namespace CycleQ2MarkedLogarithmicVelocity


open CycleQ2DoubleLogarithmicClass (twoLog)
open CycleQ2LiteralAbelJacobiContraction (contractRestrict contractRestrict_wedge)
open KaehlerDifferential
open scoped DualNumber

section AlongMap
variable {P A : Type} [CommRing P] [CommRing A] [Algebra ℂ P] [Algebra ℂ A]
  [Algebra P A] [IsScalarTower ℂ P A]

/-- Clear the normal denominators of the logarithmic symbol after contraction
along a tangent at an arbitrary coefficient specialization. -/
theorem cleared_contraction (v : Derivation ℂ P A) (f g : Pˣ) :
    algebraMap P A ((f : P) * (g : P)) • contractRestrict v (twoLog (K := ℂ) f g) =
      v (f : P) • D ℂ A (algebraMap P A (g : P)) -
        v (g : P) • D ℂ A (algebraMap P A (f : P)) := by
  let ω := exteriorPower.ιMulti P 2 ![D ℂ P (f : P), D ℂ P (g : P)]
  have norm : ((f : P) * (g : P)) • twoLog (K := ℂ) f g = ω := by
    change ((f : P) * (g : P)) •
      CycleQ2ExactFrameThreeDeRham.wedgeLeft ((↑g⁻¹ : P) • D ℂ P (g : P)) ((↑f⁻¹ : P) • D ℂ P (f : P)) = _
    rw [map_smul]
    change ((f : P) * (g : P)) • ((↑f⁻¹ : P) •
      CycleQ2ExactFrameThreeDeRham.wedgeRight (D ℂ P (f : P)) ((↑g⁻¹ : P) • D ℂ P (g : P))) = _
    rw [map_smul, smul_smul, smul_smul, mul_right_comm (↑f : P) (↑g : P) (↑f⁻¹ : P), Units.mul_inv, one_mul, Units.mul_inv, one_smul]
    rfl
  rw [IsScalarTower.algebraMap_smul, ← map_smul, norm]
  dsimp only [ω]
  rw [contractRestrict_wedge, Derivation.liftKaehlerDifferential_comp_D,
    Derivation.liftKaehlerDifferential_comp_D, KaehlerDifferential.map_D, KaehlerDifferential.map_D]

end AlongMap

attribute [local instance] TrivSqZeroExt.algebraBase
local instance dualTower (A : Type) [CommRing A] [Algebra ℂ A] : IsScalarTower ℂ (DualNumber A) A :=
  ⟨fun c s a => smul_mul_assoc c s.fst a⟩

section Dual
variable {A : Type} [CommRing A] [Algebra ℂ A]

/-- The coefficient of ε is the tangent to the dual-number ambient chart
above its closed point. -/
def dualVelocity : Derivation ℂ (DualNumber A) A where
  toLinearMap := (TrivSqZeroExt.sndHom A A).restrictScalars ℂ
  map_one_eq_zero' := rfl
  leibniz' f g := by
    change f.fst * g.snd + f.snd * g.fst = f.fst * g.snd + g.fst * f.snd
    rw [mul_comm f.snd]

/-- The moving functions f+εl and g+εm, where f and g are invertible on
the double principal open, give a genuine two-log term there. -/
def movingUnit (f : Aˣ) (l : A) : (DualNumber A)ˣ :=
  (TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr (show IsUnit ((show DualNumber A from ((f : A), l)).fst) from f.isUnit)).unit

omit [Algebra ℂ A] in
theorem movingUnit_val (f : Aˣ) (l : A) : (↑(movingUnit f l) : DualNumber A) = ((f : A), l) :=
  IsUnit.unit_spec _

/-- On a dual-time chart the pole-cleared contraction is the alternating
normal-velocity numerator, with cubic velocity first. -/
theorem dual_numerator (f g : Aˣ) (l m : A) :
    ((f : A) * (g : A)) • contractRestrict (dualVelocity (A := A))
      (twoLog (K := ℂ) (movingUnit f l) (movingUnit g m)) =
      l • D ℂ A (g : A) - m • D ℂ A (f : A) := by
  have h := cleared_contraction (dualVelocity (A := A)) (movingUnit f l) (movingUnit g m)
  change ((↑(movingUnit f l) : DualNumber A).fst * (↑(movingUnit g m) : DualNumber A).fst) • _ =
    (↑(movingUnit f l) : DualNumber A).snd • D ℂ A (↑(movingUnit g m) : DualNumber A).fst -
      (↑(movingUnit g m) : DualNumber A).snd • D ℂ A (↑(movingUnit f l) : DualNumber A).fst at h
  simpa only [movingUnit_val, TrivSqZeroExt.fst_mk, TrivSqZeroExt.snd_mk] using h

end Dual

open CycleQ2GeometricSurfaceFirstOrder (dualMap)
open CycleQ2IncidenceFirstOrder
open CycleQ2IncidenceEtaleParameter
open CycleQ2IncidenceNormalForm
open CycleQ2IncidenceUniversalChart
open CycleQ2IncidencePolynomialJacobianBinding
open CycleQ2GeometricIncidenceProj
open CycleQ2IncidenceDehomogenizedChart
open CycleQ2IncidenceChartSeedFiber
open CycleQ2LiteralAbelJacobiMovingNormal
open CycleQ2LiteralAbelJacobiEquations
open CycleQ2RelativeConstantSection
open CycleQ2LiteralAbelJacobiContraction (T fixedIdeal cubicOnT)
open CycleQ2ExactFrameThreeDeRham (wedge wedgeLeft wedge_swap wedge_self)
open MvPolynomial

/-- Evaluate the coefficient jet at stationary ambient coordinates. -/
def jet {A : Type} [CommRing A] (ρ : ChartPolynomial ℂ →+* A) :
    ChartPolynomial (DualNumber ℂ) →+* DualNumber A :=
  eval₂Hom (dualMap (ρ.comp C)) (fun i => algebraMap A (DualNumber A) (ρ (X i)))

theorem jet_constant {A : Type} [CommRing A] (ρ : ChartPolynomial ℂ →+* A)
    (f : ChartPolynomial ℂ) :
    jet ρ (MvPolynomial.map (algebraMap ℂ (DualNumber ℂ)) f) = algebraMap A (DualNumber A) (ρ f) := by
  have eq : (jet ρ).comp (MvPolynomial.map (algebraMap ℂ (DualNumber ℂ))) =
      (algebraMap A (DualNumber A)).comp ρ := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp only [RingHom.comp_apply, MvPolynomial.map_C, jet, eval₂Hom_C]
      apply TrivSqZeroExt.ext
      · rfl
      · exact map_zero _
    · intro i
      simp only [RingHom.comp_apply, MvPolynomial.map_X, jet, eval₂Hom_X']
  exact RingHom.congr_fun eq f

private theorem jet_eps {A : Type} [CommRing A] (ρ : ChartPolynomial ℂ →+* A) :
    jet ρ (C ε) = ((0,1) : DualNumber A) := by
  rw [jet,eval₂Hom_C]
  apply TrivSqZeroExt.ext
  · exact map_zero _
  · exact map_one _

local instance fixedRing (i : Fin 4) : CommRing (T i) := inferInstance
abbrev fixedChartMap (i : Fin 4) : ChartPolynomial ℂ →+* T i := Ideal.Quotient.mk _

/-- The two original equations on the marked pivot after base change to the
actual time jet, evaluated in the fixed sextic ring. -/
def cubicJet (i : Fin 4) : DualNumber (T i) :=
  jet (fixedChartMap i) (MvPolynomial.map firstOrderMap.toRingHom (dehomogenizedEquations incidencePoint i 1))

def rowJet (t : Fin 3 → ℂ) (i : Fin 4) (p : CycleQ2SegreCech.Chart) : DualNumber (T i) :=
  jet (fixedChartMap i) (MvPolynomial.map firstOrderMap.toRingHom
    (dehomogenize i (relativeSectionPolynomial incidencePoint t p.1)))

theorem cubicJet_parts (i : Fin 4) :
    cubicJet i = ((cubicOnT i, fixedChartMap i (tangentL i)) : DualNumber (T i)) := by
  change jet (fixedChartMap i) (MvPolynomial.map _ (dehomogenize i (pointEquationH incidencePoint))) = _
  rw [map_dehomogenize,cubic_coefficients,map_add,map_mul,MvPolynomial.algHom_C,
    ← map_dehomogenize, ← map_dehomogenize,map_add,map_mul,jet_constant,jet_constant]
  rw [show jet (fixedChartMap i) (algebraMap ℂ[ε] (ChartPolynomial ℂ[ε]) ε) = _ from jet_eps (fixedChartMap i)]
  apply TrivSqZeroExt.ext
  · change cubicOnT i + 0 * _ = _
    rw [zero_mul,add_zero]
    rfl
  · change 0 + (0 * 0 + 1 * fixedChartMap i (tangentL i)) = _
    rw [zero_mul,one_mul,zero_add,zero_add]
    rfl

section Equations
variable {A : Type} [CommRing A] [Algebra ℂ A] (F G : DualNumber A)
abbrev overlapRing := CycleQ2NativeDoubleLocalization.T F.fst G.fst
abbrev toOverlap := algebraMap A (overlapRing F G)
private abbrev firstUnit := CycleQ2NativeDoubleLocalization.localizedF (K := ℂ) F.fst G.fst
private abbrev secondUnit := CycleQ2NativeDoubleLocalization.localizedG (K := ℂ) F.fst G.fst

private def dualRho : DualNumber A →ₐ[ℂ] DualNumber (overlapRing F G) where
  toRingHom := dualMap (toOverlap F G)
  commutes' c := by
    apply TrivSqZeroExt.ext
    · exact (IsScalarTower.algebraMap_apply ℂ A (overlapRing F G) c).symm
    · exact map_zero _

private theorem dualRho_f : dualRho F G F = (movingUnit (firstUnit F G) (toOverlap F G F.snd) : DualNumber (overlapRing F G)) := by
  rw [movingUnit_val, CycleQ2NativeDoubleLocalization.localizedF_val]
  rfl

private theorem dualRho_g : dualRho F G G = (movingUnit (secondUnit F G) (toOverlap F G G.snd) : DualNumber (overlapRing F G)) := by
  rw [movingUnit_val, CycleQ2NativeDoubleLocalization.localizedG_val]
  rfl

private theorem dualRho_isUnit : IsUnit (dualRho F G (F * G)) := by
  rw [map_mul,dualRho_f,dualRho_g]
  exact (Units.isUnit _).mul (Units.isUnit _)

def overlapMap :
    CycleQ2NativeDoubleLocalization.T F G →ₐ[ℂ] DualNumber (overlapRing F G) :=
  IsLocalization.Away.liftAlgHom (f := dualRho F G) (F*G)
    (dualRho_isUnit F G)

private theorem overlap_unit (R : DualNumber A) :
    overlapMap F G (algebraMap (DualNumber A) (CycleQ2NativeDoubleLocalization.T F G) R) =
      dualRho F G R := by
  unfold overlapMap
  exact IsLocalization.Away.lift_eq (S := CycleQ2NativeDoubleLocalization.T F G)
    (g := (dualRho F G).toRingHom) (F * G) (dualRho_isUnit F G) R

/-- Restriction of the native double-localization representative along the
dual-time morphism gives the two actual unit jets, before contracting. -/
theorem pull_actual_log :
    CycleQ2ExactFrameThreeDeRham.exteriorPullback (overlapMap F G) 2
      (CycleQ2NativeDoubleLocalization.cochain (K := ℂ) F G) =
      twoLog (K := ℂ) (movingUnit (firstUnit F G) (toOverlap F G F.snd)) (movingUnit (secondUnit F G) (toOverlap F G G.snd)) := by
  unfold CycleQ2NativeDoubleLocalization.cochain
  rw [CycleQ2DoubleLogarithmicClass.pullback_twoLog]
  congr 1
  · apply Units.ext
    change overlapMap F G (CycleQ2NativeDoubleLocalization.localizedF (K := ℂ) F G) = _
    rw [CycleQ2NativeDoubleLocalization.localizedF_val,overlap_unit,dualRho_f]
  · apply Units.ext
    change overlapMap F G (CycleQ2NativeDoubleLocalization.localizedG (K := ℂ) F G) = _
    rw [CycleQ2NativeDoubleLocalization.localizedG_val,overlap_unit,dualRho_g]

/-- Contraction of the pulled-back native logarithmic representative. -/
def mixedLog := contractRestrict (dualVelocity (A := overlapRing F G))
  (CycleQ2ExactFrameThreeDeRham.exteriorPullback (overlapMap F G) 2
    (CycleQ2NativeDoubleLocalization.cochain (K := ℂ) F G))

theorem cleared_mixed_wedge :
    let φ := toOverlap F G
    let d := D ℂ (overlapRing F G)
    wedge (φ (F.fst * G.fst) • mixedLog F G) (d (φ F.fst)) =
      -(φ F.snd) • wedge (d (φ F.fst)) (d (φ G.fst)) := by
  dsimp only
  have h := dual_numerator (firstUnit F G) (secondUnit F G) (toOverlap F G F.snd) (toOverlap F G G.snd)
  rw [← pull_actual_log] at h
  change _ • mixedLog F G = _ at h
  rw [CycleQ2NativeDoubleLocalization.localizedF_val,CycleQ2NativeDoubleLocalization.localizedG_val] at h
  rw [map_mul,h]
  let df := D ℂ (overlapRing F G) (toOverlap F G F.fst)
  let dg := D ℂ (overlapRing F G) (toOverlap F G G.fst)
  change wedgeLeft df (toOverlap F G F.snd • dg - toOverlap F G G.snd • df) = _
  rw [map_sub,map_smul,map_smul]
  change toOverlap F G F.snd • wedge dg df - toOverlap F G G.snd • wedge df df = _
  rw [wedge_self,smul_zero,sub_zero,wedge_swap df dg,smul_neg]
  exact (neg_smul (toOverlap F G F.snd) (wedge df dg)).symm

end Equations

/-- On the original marked time tangent, wedging the cleared logarithmic
contraction with the cubic conormal makes the entire section-row velocity
cancel and leaves minus the retained cubic coefficient. -/
theorem marked_pivot_log (t : Fin 3 → ℂ) (i : Fin 4) (p : CycleQ2SegreCech.Chart) :
    let F := cubicJet i
    let G := rowJet t i p
    let φ := toOverlap F G
    let d := D ℂ (overlapRing F G)
    wedge (φ (F.fst * G.fst) • mixedLog F G) (d (φ F.fst)) =
      -(φ (fixedChartMap i (tangentL i))) • wedge (d (φ F.fst)) (d (φ G.fst)) := by
  dsimp only
  have eq : (cubicJet i).snd = fixedChartMap i (tangentL i) := congrArg TrivSqZeroExt.snd (cubicJet_parts i)
  simpa only [eq] using cleared_mixed_wedge (cubicJet i) (rowJet t i p)

section CurveVelocity

open CycleQ2LiteralAbelJacobiContraction (toCurve)
open CycleQ2LiteralCylinderEvaluation (toFamily)
attribute [local instance] CycleQ2IncidenceSeedFiber.seedAlgebra
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderAlgebra
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderModule
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderSMul
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderTower
  CycleQ2LiteralCylinderEvaluation.familyRing CycleQ2LiteralCylinderEvaluation.closedRing
  CycleQ2CurveParameterTangent.chartComplexAlgebra CycleQ2LiteralCylinderEvaluation.reductionAlgebra

/-- The regular coefficient obtained from the logarithmic calculation
restricts on the marked curve to the velocity of its actual cubic equation. -/
theorem marked_curve_velocity (t : Fin 3 → ℂ) (i : Fin 4)
    (v : Derivation ℂ (B t i) (A t i))
    (hv : v (algebraMap ℂ[ε] (B t i) ε) = 1) :
    toCurve t i (-(cubicJet i).snd) = v (toFamily t i (cubicOnT i)) := by
  rw [CycleQ2LiteralThreefoldVertexMotion.chart_velocity_cubic t i v hv, cubicJet_parts, map_neg]
  rfl

end CurveVelocity

end CycleQ2MarkedLogarithmicVelocity

#print axioms CycleQ2MarkedLogarithmicVelocity.marked_pivot_log
#print axioms CycleQ2MarkedLogarithmicVelocity.marked_curve_velocity
