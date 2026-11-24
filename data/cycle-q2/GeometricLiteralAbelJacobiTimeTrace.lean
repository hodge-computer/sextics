import Proposal.GeometricLiteralAbelJacobiTimeProjection
import Proposal.GeometricLiteralMovingCurveDifferentialNonzero
import Proposal.GeometricLiteralMovingCurveKodairaSpencer

/-!
# The moving time family and the traced differential on its own seed curve

One original section vector gives the smooth proper correspondence over a
pointed fixed-sextic curve, a nonstationary embedded motion, and a genuine
class in H¹ of the seed curve's Kähler differentials with nonzero algebraic
trace. The equality on the first-order germ identifies the second projection
with the one from the original incidence construction.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace CycleQ2LiteralAbelJacobiTimeTrace

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits TopologicalSpace AlgebraicGeometry
  CycleQ2IncidenceEtaleParameter CycleQ2IncidenceSeedFiberCover
  CycleQ2IncidenceChartFiberScheme CycleQ2LiteralIncidenceTimeCurve
  CycleQ2LiteralIncidenceCylinderMap CycleQ2LiteralAbelJacobiTimeFamily
  CycleQ2LiteralAbelJacobiTimeProjection CycleQ2FirstOrderChartReduction
  CycleQ2LiteralAbelJacobiRelativeNormal CycleQ2SeedSectionAffineInjective
  CycleQ2LiteralMovingCurveDifferentialNonzero CycleQ2LiteralMovingCurveKodairaSpencer
  CycleQ2LiteralSheafOneClasses

local instance (T : TopCat.{0}) : HasExt.{1} (T.Sheaf AddCommGrpCat.{0}) := HasExt.standard _
local instance (T : TopCat.{0}) : HasExt.{1}
    (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}) := HasExt.standard _
local instance (X : Scheme.{0}) : HasExt.{1}
    (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}) := HasExt.standard _

theorem exists_smooth_time_family_with_traced_curve_class :
    ∃ t : Fin 3 → ℂ, AlgebraicIndependent ℚ t ∧
      ∃ (ht : ∀ i, ChartRegular t i) (V : parameterScheme.Opens) (hV : seedBasePoint ∈ V),
        SmoothOfRelativeDimension 1 ((timeOpen V).ι ≫ toComplex) ∧
        SmoothOfRelativeDimension 1 (projection V t) ∧
        SmoothOfRelativeDimension 2 (projection V t ≫ (timeOpen V).ι ≫ toComplex) ∧
        IsProper (projection V t) ∧ Function.Surjective (projection V t) ∧
        tangentLift V hV ≠ structureDual ≫ seedLift V hV ∧
        (firstOrderIso V t hV).hom ≫ pullback.snd _ _ ≫ q V t =
          (CycleQ2LiteralIncidenceTimeFamily.firstOrderIso t).hom ≫ pullback.snd _ _ ≫
            toFixedThreefold t ∧
        restrictContraction t kodairaSpencerDerivedClass = curveClass t ∧
        curveClass t ≠ 0 ∧ differentialTrace t ht (curveClass t) ≠ 0 ∧
        ∃ hf : ∀ i, Module.Flat (DualNumber ℂ) (FirstOrderCurveChart t i),
          ∃ j : Fin 3, @relativeNormal t j.succ (hf j.succ)
            ((idealOnT t j.succ).toCotangent (cubicClass t j.succ)) ≠ 0 := by
  obtain ⟨t, hi, ht, V, hV, hbase, hfib, htotal, hp, hs, htangent, hn⟩ := exists_smooth_time_family
  exact ⟨t, hi, ht, V, hV, hbase, hfib, htotal, hp, hs, htangent, firstOrder_to_q V t hV,
    restrictContraction_kodairaSpencer t, curveClass_ne_zero t ht, differentialTrace_curveClass_ne_zero t ht, hn⟩

end CycleQ2LiteralAbelJacobiTimeTrace
end

#print axioms CycleQ2LiteralAbelJacobiTimeTrace.exists_smooth_time_family_with_traced_curve_class
