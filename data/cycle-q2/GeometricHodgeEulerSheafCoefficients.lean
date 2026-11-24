import Proposal.GeometricHodgeTwistRatios
import Proposal.GeometricHodgeEulerChartBinding

/-!
# Coefficients of the weighted Euler and normal maps on every open

The degree-wᵢ coordinate and the degree-(6−wᵢ) gradient component are
sections in the normalized projective frames. Their contraction is zero
in the actual structure sheaf on every subopen of each chart.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2HodgeEulerSheaf

open AlgebraicGeometry CategoryTheory MvPolynomial
open CycleQ2GeometricIncidenceProj CycleQ2GeometricHodgeThreefold
open CycleQ2HodgeTwistRatios (normalized)
open CycleQ2GenericSexticGradient (CoeffRing)
open CycleQ2GeometricProjectiveCurve.Twisted (res)

variable {R : Type} [CommRing R] (φ : CoeffRing →+* R)

def partialValue (j : Fin 5) : cone φ := quotient φ (pderiv j (equation φ))

theorem partial_mem (j : Fin 5) : partialValue φ j ∈ grade φ (6 - geometricWeight j) :=
  quotient_mem_grade φ _ ((equation_homogeneous φ).pderiv (Nat.sub_add_cancel (by fin_cases j <;> decide)))

def sectionMap (i : Fin 4) (V : (threefold φ).Opens) (hi : V ≤ coordinateOpen φ i) :
    ChartRing φ i →+* Γ(threefold φ,V) :=
  (res (threefold φ).sheaf hi).comp (Proj.awayToSection (grade φ) (coord φ i.castSucc)).hom

theorem sectionMap_coordinate (i : Fin 4) (V : (threefold φ).Opens) (hi : V ≤ coordinateOpen φ i)
    (j : Fin 5) :
    sectionMap φ i V hi (CycleQ2HodgeEulerChartBinding.ratio φ i j) =
      normalized φ i (coord φ j) (coord_mem_grade φ j) V hi := rfl

theorem sectionMap_gradient (i : Fin 4) (V : (threefold φ).Opens) (hi : V ≤ coordinateOpen φ i)
    (j : Fin 5) :
    sectionMap φ i V hi (CycleQ2HodgeEulerChartBinding.gradientRatio φ i j) =
      normalized φ i (partialValue φ j) (partial_mem φ j) V hi := rfl

theorem normalized_euler (i : Fin 4) (V : (threefold φ).Opens) (hi : V ≤ coordinateOpen φ i) :
    ∑ j : Fin 5, normalized φ i (partialValue φ j) (partial_mem φ j) V hi *
      ((geometricWeight j : Γ(threefold φ,V)) * normalized φ i (coord φ j) (coord_mem_grade φ j) V hi) = 0 := by
  let e := CycleQ2HodgeEulerChartBinding.chartEquiv φ i
  have H : ∑ j : Fin 5, CycleQ2HodgeEulerChartBinding.gradientRatio φ i j *
      ((geometricWeight j : ChartRing φ i) * CycleQ2HodgeEulerChartBinding.ratio φ i j) = 0 := by
    apply e.injective
    simp only [map_sum, map_mul, map_natCast, map_zero, e, CycleQ2HodgeEulerChartBinding.chartEquiv_ratio,
      CycleQ2HodgeEulerChartBinding.chartEquiv_gradientRatio]
    exact CycleQ2HodgeEuler.radial_equation φ i
  simpa only [map_sum, map_mul, map_natCast, map_zero, sectionMap_coordinate, sectionMap_gradient] using
    congrArg (sectionMap φ i V hi) H

end CycleQ2HodgeEulerSheaf
end

#print axioms CycleQ2HodgeEulerSheaf.normalized_euler
