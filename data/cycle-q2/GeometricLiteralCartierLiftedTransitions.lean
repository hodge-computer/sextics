import Proposal.GeometricLiteralCartierCochainNaturality

/-!
# The six actual lifted transitions of the original Cartier cone cover

The 01 transition is -g1/g2; the 02 and 03 transitions lift f2;
the 12 and 13 transitions lift f1; the 23 transition is one.
The two complementary units are constructed from F - epsilon B*.
All comparisons are in the original localized deformed rings.

Prepared for fqlx with OpenAI ChatGPT assistance; see solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralCartierLiftedTransitions

open CycleQ2SeedTrace CycleQ2NormalConnecting CycleQ2LiteralCartierTransitionBinding
  CycleQ2GeometricSurfaceFirstOrder CycleQ2LiteralCartierSplittings
  CycleQ2LiteralCartierOverlapSplittings CycleQ2LiteralCartierKodairaSpencer
  CycleQ2LiteralCartierAtiyahFaces CycleQ2LiteralCartierCochainNaturality
  CycleQ2GeometricSquareZeroSplittings CycleQ2GeometricCartierTransitionUnits

attribute [local instance] CycleQ2LiteralCartierTransitionBinding.cubicSelfModule
  CycleQ2LiteralCartierTransitionBinding.cubicOppositeModule
  CycleQ2LiteralCartierTransitionBinding.cubicCentralScalar
  CycleQ2LiteralCartierTransitionBinding.cubicSmulCommClass
  CycleQ2GeometricSurfaceFirstOrder.reducedAlgebra
  CycleQ2GeometricKernelLocalization.localReductionAlgebra
  CycleQ2LiteralCartierSplittings.complexReductionTower
  CycleQ2LiteralCartierOverlapSplittings.baseReductionAlgebra

def coveredUnit (s : Finset (Fin 4)) (i : Fin 4) (hi : i ∈ s) : (Thick s)ˣ :=
  (polynomialMap_cover_isUnit s i hi).unit

theorem coveredUnit_value (s : Finset (Fin 4)) (i : Fin 4) (hi : i ∈ s) :
    (coveredUnit s i hi : Thick s) = polynomialMap s (coverPolynomial i) :=
  IsUnit.unit_spec _

theorem restrictUnit_mul {s t : Finset (Fin 4)} (hst : s ⊆ t) (u v : (Thick s)ˣ) :
    restrictUnit hst (u * v) = restrictUnit hst u * restrictUnit hst v :=
  map_mul _ u v

theorem restrictUnit_inv {s t : Finset (Fin 4)} (hst : s ⊆ t) (u : (Thick s)ˣ) :
    restrictUnit hst u⁻¹ = (restrictUnit hst u)⁻¹ := map_inv _ u

theorem restrictUnit_neg {s t : Finset (Fin 4)} (hst : s ⊆ t) (u : (Thick s)ˣ) :
    restrictUnit hst (-u) = -restrictUnit hst u := by
  apply Units.ext
  change thickRestriction hst (-(u : Thick s)) = -thickRestriction hst (u : Thick s)
  exact map_neg _ _

theorem restrict_covered_to_factor {s t : Finset (Fin 4)} (hst : s ⊆ t)
    (j : Fin 4) (hj : j ∈ s) (h0 : 0 ∈ t) (h1 : 1 ∈ t) (hf : 2 ∈ t ∨ 3 ∈ t)
    (i : Fin 4) (hij : coverPolynomial j = factorPolynomial i) :
    restrictUnit hst (coveredUnit s j hj) = factors t h0 h1 hf i := by
  apply Units.ext
  rw [restrictUnit_value, coveredUnit_value, polynomialMap_restrict, factors_value, hij]

theorem secondEquation_unit_on02 : IsUnit (polynomialMap {0,2} originalF2) := by
  have h := complementary_factors_are_units (kernelEquiv {0,2})
    (polynomialMap {0,2} (originalF1 57)) (polynomialMap {0,2} originalF2)
    (polynomialMap {0,2} (originalG1 57)) (polynomialMap {0,2} originalG2)
    (perturbationSection {0,2}) (actual_factorization {0,2})
    ((polynomialMap_cover_isUnit {0,2} 2 (by simp)).mul
      (polynomialMap_cover_isUnit {0,2} 0 (by simp)))
  exact h.1

theorem firstEquation_unit_on13 : IsUnit (polynomialMap {1,3} (originalF1 57)) := by
  have he : polynomialMap {1,3} originalF2 * polynomialMap {1,3} originalG2 +
      polynomialMap {1,3} (originalF1 57) * polynomialMap {1,3} (originalG1 57) =
        epsilon (kernelEquiv {1,3}) (perturbationSection {1,3}) := by
    rw [add_comm]
    exact actual_factorization {1,3}
  have h := complementary_factors_are_units (kernelEquiv {1,3})
    (polynomialMap {1,3} originalF2) (polynomialMap {1,3} (originalF1 57))
    (polynomialMap {1,3} originalG2) (polynomialMap {1,3} (originalG1 57))
    (perturbationSection {1,3}) he
    ((polynomialMap_cover_isUnit {1,3} 3 (by simp)).mul
      (polynomialMap_cover_isUnit {1,3} 1 (by simp)))
  exact h.1

def lifted01 : (Thick {0,1})ˣ :=
  transition01 (coveredUnit {0,1} 0 (by simp)) (coveredUnit {0,1} 1 (by simp))

def lifted02 : (Thick {0,2})ˣ := secondEquation_unit_on02.unit

def lifted03 : (Thick {0,3})ˣ := coveredUnit {0,3} 3 (by simp)

def lifted12 : (Thick {1,2})ˣ := coveredUnit {1,2} 2 (by simp)

def lifted13 : (Thick {1,3})ˣ := firstEquation_unit_on13.unit

def lifted23 : (Thick {2,3})ˣ := 1

theorem lifted02_value : (lifted02 : Thick {0,2}) = polynomialMap {0,2} originalF2 :=
  IsUnit.unit_spec _

theorem lifted03_value : (lifted03 : Thick {0,3}) = polynomialMap {0,3} originalF2 :=
  coveredUnit_value {0,3} 3 (by simp)

theorem lifted12_value : (lifted12 : Thick {1,2}) = polynomialMap {1,2} (originalF1 57) :=
  coveredUnit_value {1,2} 2 (by simp)

theorem lifted13_value : (lifted13 : Thick {1,3}) = polynomialMap {1,3} (originalF1 57) :=
  IsUnit.unit_spec _

theorem restrict_lifted01 {s : Finset (Fin 4)} (h01 : {0,1} ⊆ s)
    (hf : 2 ∈ s ∨ 3 ∈ s) :
    restrictUnit h01 lifted01 =
      transition01 (factors s (h01 (by simp)) (h01 (by simp)) hf 2)
        (factors s (h01 (by simp)) (h01 (by simp)) hf 3) := by
  unfold lifted01 transition01
  rw [restrictUnit_mul, restrictUnit_neg, restrictUnit_inv,
    restrict_covered_to_factor h01 0 (by simp) _ _ hf 2 rfl,
    restrict_covered_to_factor h01 1 (by simp) _ _ hf 3 rfl]

theorem restrict_lifted02 {s : Finset (Fin 4)} (h02 : {0,2} ⊆ s)
    (h0 : 0 ∈ s) (h1 : 1 ∈ s) (hf : 2 ∈ s ∨ 3 ∈ s) :
    restrictUnit h02 lifted02 = factors s h0 h1 hf 1 := by
  apply Units.ext
  rw [restrictUnit_value, lifted02_value, polynomialMap_restrict, factors_value]
  rfl

theorem restrict_lifted03 {s : Finset (Fin 4)} (h03 : {0,3} ⊆ s)
    (h0 : 0 ∈ s) (h1 : 1 ∈ s) (hf : 2 ∈ s ∨ 3 ∈ s) :
    restrictUnit h03 lifted03 = factors s h0 h1 hf 1 := by
  apply Units.ext
  rw [restrictUnit_value, lifted03_value, polynomialMap_restrict, factors_value]
  rfl

theorem restrict_lifted12 {s : Finset (Fin 4)} (h12 : {1,2} ⊆ s)
    (h0 : 0 ∈ s) (h1 : 1 ∈ s) (hf : 2 ∈ s ∨ 3 ∈ s) :
    restrictUnit h12 lifted12 = factors s h0 h1 hf 0 := by
  apply Units.ext
  rw [restrictUnit_value, lifted12_value, polynomialMap_restrict, factors_value]
  rfl

theorem restrict_lifted13 {s : Finset (Fin 4)} (h13 : {1,3} ⊆ s)
    (h0 : 0 ∈ s) (h1 : 1 ∈ s) (hf : 2 ∈ s ∨ 3 ∈ s) :
    restrictUnit h13 lifted13 = factors s h0 h1 hf 0 := by
  apply Units.ext
  rw [restrictUnit_value, lifted13_value, polynomialMap_restrict, factors_value]
  rfl

theorem second_transition_consistent {s : Finset (Fin 4)}
    (h02 : {0,2} ⊆ s) (h03 : {0,3} ⊆ s) :
    restrictUnit h02 lifted02 = restrictUnit h03 lifted03 := by
  apply Units.ext
  rw [restrictUnit_value, restrictUnit_value, lifted02_value, lifted03_value,
    polynomialMap_restrict, polynomialMap_restrict]

theorem first_transition_consistent {s : Finset (Fin 4)}
    (h12 : {1,2} ⊆ s) (h13 : {1,3} ⊆ s) :
    restrictUnit h12 lifted12 = restrictUnit h13 lifted13 := by
  apply Units.ext
  rw [restrictUnit_value, restrictUnit_value, lifted12_value, lifted13_value,
    polynomialMap_restrict, polynomialMap_restrict]

theorem restrict_lifted23 {s : Finset (Fin 4)} (h23 : {2,3} ⊆ s) :
    restrictUnit h23 lifted23 = 1 := map_one _

/-- The actual reductions of the three restricted pair transitions
satisfy the original multiplicative cocycle on face 012. -/
theorem reduced_cocycle012 :
    reducedUnit (C := ClosedRing {0,1,2})
        (restrictUnit (s := {0,1}) (t := {0,1,2}) (by decide) lifted01) *
      reducedUnit (C := ClosedRing {0,1,2})
        (restrictUnit (s := {1,2}) (t := {0,1,2}) (by decide) lifted12) =
      reducedUnit (C := ClosedRing {0,1,2})
        (restrictUnit (s := {0,2}) (t := {0,1,2}) (by decide) lifted02) := by
  rw [restrict_lifted01 _ (by simp),
    restrict_lifted12 _ (by simp) (by simp) (by simp),
    restrict_lifted02 _ (by simp) (by simp) (by simp)]
  exact transition_reduced_cocycle (kernelEquiv {0,1,2}) _ _ _ _ _
    (factors_relation {0,1,2} (by simp) (by simp) (by simp))

theorem reduced_cocycle013 :
    reducedUnit (C := ClosedRing {0,1,3})
        (restrictUnit (s := {0,1}) (t := {0,1,3}) (by decide) lifted01) *
      reducedUnit (C := ClosedRing {0,1,3})
        (restrictUnit (s := {1,3}) (t := {0,1,3}) (by decide) lifted13) =
      reducedUnit (C := ClosedRing {0,1,3})
        (restrictUnit (s := {0,3}) (t := {0,1,3}) (by decide) lifted03) := by
  rw [restrict_lifted01 _ (by simp),
    restrict_lifted13 _ (by simp) (by simp) (by simp),
    restrict_lifted03 _ (by simp) (by simp) (by simp)]
  exact transition_reduced_cocycle (kernelEquiv {0,1,3}) _ _ _ _ _
    (factors_relation {0,1,3} (by simp) (by simp) (by simp))

theorem reduced_cocycle023 :
    reducedUnit (C := ClosedRing {0,2,3})
        (restrictUnit (s := {0,2}) (t := {0,2,3}) (by decide) lifted02) *
      reducedUnit (C := ClosedRing {0,2,3})
        (restrictUnit (s := {2,3}) (t := {0,2,3}) (by decide) lifted23) =
      reducedUnit (C := ClosedRing {0,2,3})
        (restrictUnit (s := {0,3}) (t := {0,2,3}) (by decide) lifted03) := by
  rw [restrict_lifted23, show reducedUnit (C := ClosedRing {0,2,3})
    (1 : (Thick {0,2,3})ˣ) = 1 from map_one _, mul_one,
    second_transition_consistent _ (by decide)]

theorem reduced_cocycle123 :
    reducedUnit (C := ClosedRing {1,2,3})
        (restrictUnit (s := {1,2}) (t := {1,2,3}) (by decide) lifted12) *
      reducedUnit (C := ClosedRing {1,2,3})
        (restrictUnit (s := {2,3}) (t := {1,2,3}) (by decide) lifted23) =
      reducedUnit (C := ClosedRing {1,2,3})
        (restrictUnit (s := {1,3}) (t := {1,2,3}) (by decide) lifted13) := by
  rw [restrict_lifted23, show reducedUnit (C := ClosedRing {1,2,3})
    (1 : (Thick {1,2,3})ˣ) = 1 from map_one _, mul_one,
    first_transition_consistent _ (by decide)]

end CycleQ2LiteralCartierLiftedTransitions

end

#print axioms CycleQ2LiteralCartierLiftedTransitions.secondEquation_unit_on02
#print axioms CycleQ2LiteralCartierLiftedTransitions.firstEquation_unit_on13
#print axioms CycleQ2LiteralCartierLiftedTransitions.restrict_lifted01
#print axioms CycleQ2LiteralCartierLiftedTransitions.second_transition_consistent

#print axioms CycleQ2LiteralCartierLiftedTransitions.reduced_cocycle012
#print axioms CycleQ2LiteralCartierLiftedTransitions.reduced_cocycle013
#print axioms CycleQ2LiteralCartierLiftedTransitions.reduced_cocycle023
#print axioms CycleQ2LiteralCartierLiftedTransitions.reduced_cocycle123
