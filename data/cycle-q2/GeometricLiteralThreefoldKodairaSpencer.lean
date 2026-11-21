import Proposal.GeometricLiteralAbelJacobiEquations
import Proposal.GeometricCartierDeformation
import Proposal.GeometricLiteralCanonicalClass

/-!
# The ambient test deformation on the fixed threefold's Jacobian charts

On the chart of the fixed sextic where a partial derivative is invertible,
the partial derivative scaled by the test polynomial divided by that partial
lifts the test direction. Its negative graph splits the actual equation
F − ε B*. Differences of these splittings give a tangent cocycle of the
fixed hypersurface, without imposing its cubic section equation.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2LiteralThreefoldKodairaSpencer

open MvPolynomial CycleQ2IncidenceDehomogenizedChart CycleQ2LiteralAbelJacobiEquations
  CycleQ2GeometricSurfaceFirstOrder CycleQ2GeometricLiteralDirection

abbrev P := ChartPolynomial ℂ
abbrev Index := Option (Fin 3)

def test (i : Fin 4) : P := dehomogenize i ambientTest

def pivot (i : Fin 4) (j : Index) : P := pderiv j (seedF i)

def product (i : Fin 4) (s : Finset Index) : P := ∏ j ∈ s, pivot i j

abbrev Ambient (i : Fin 4) (s : Finset Index) := Localization.Away (product i s)
abbrev localF (i : Fin 4) (s : Finset Index) := algebraMap P (Ambient i s) (seedF i)
abbrev localTest (i : Fin 4) (s : Finset Index) := algebraMap P (Ambient i s) (test i)

theorem pivot_unit (i : Fin 4) (s : Finset Index) (j : Index) (hj : j ∈ s) :
    IsUnit (algebraMap P (Ambient i s) (pivot i j)) := by
  have hdiv : pivot i j ∣ product i s := Finset.dvd_prod_of_mem _ hj
  exact isUnit_of_dvd_unit (map_dvd _ hdiv)
    (IsLocalization.Away.algebraMap_isUnit (S := Ambient i s) (product i s))

/-- The ambient derivative with value exactly B* on F. -/
def lift (i : Fin 4) (s : Finset Index) (j : Index) (hj : j ∈ s) :
    Derivation ℂ (Ambient i s) (Ambient i s) :=
  (localTest i s * ((pivot_unit i s j hj).unit⁻¹ : (Ambient i s)ˣ)) •
    CycleQ2LocalizationDerivation.extend (Submonoid.powers (product i s)) (pderiv j)

theorem lift_on_F (i : Fin 4) (s : Finset Index) (j : Index) (hj : j ∈ s) :
    lift i s j hj (localF i s) = localTest i s := by
  change (localTest i s * _) * (CycleQ2LocalizationDerivation.extend
    (S := Ambient i s) (Submonoid.powers (product i s)) (pderiv j) (algebraMap P _ (seedF i))) = _
  rw [CycleQ2LocalizationDerivation.extend_map, mul_assoc]
  change localTest i s * (↑((pivot_unit i s j hj).unit⁻¹) * ↑((pivot_unit i s j hj).unit)) = _
  simp

def chartSplitting (i : Fin 4) (s : Finset Index) (j : Index) (hj : j ∈ s) :
    Closed (localF i s) →ₐ[ℂ] Deformation (localF i s) (localTest i s) :=
  splitting _ _ (lift i s j hj) (lift_on_F i s j hj)

def tangent (i : Fin 4) (s : Finset Index) (j k : Index) (hj : j ∈ s) (hk : k ∈ s) :
    Derivation ℂ (Closed (localF i s)) (Closed (localF i s)) :=
  tangentDifference _ (lift i s j hj) (lift i s k hk) ((lift_on_F i s j hj).trans
    (lift_on_F i s k hk).symm)

theorem splitting_edge (i : Fin 4) (s : Finset Index) (j k : Index) (hj : j ∈ s) (hk : k ∈ s)
    (x : Closed (localF i s)) :
    chartSplitting i s k hk x - chartSplitting i s j hj x =
      epsilon (localF i s) (localTest i s) (tangent i s j k hj hk x) :=
  splitting_difference _ _ _ _ _ _ _

theorem tangent_cocycle (i : Fin 4) (s : Finset Index) (j k l : Index)
    (hj : j ∈ s) (hk : k ∈ s) (hl : l ∈ s) :
    tangent i s j l hj hl = tangent i s j k hj hk + tangent i s k l hk hl := by
  ext x
  obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective x
  simp only [tangent, Derivation.add_apply, tangentDifference_mk, map_sub]
  abel

end CycleQ2LiteralThreefoldKodairaSpencer
end

#print axioms CycleQ2LiteralThreefoldKodairaSpencer.splitting_edge
#print axioms CycleQ2LiteralThreefoldKodairaSpencer.tangent_cocycle
