import Proposal.GeometricLiteralCartierKodairaSpencer

/-!
# The two original Cartier defect faces with constructed splittings

All units and splittings below belong to the actual literal r=57
localizations of F - epsilon B*. The two nonzero original Cartier
faces are expressed as the sum of actual unit-correction terms and
contraction of the actual splitting difference with universal dlog.
The closed-ring comparison retains the original polynomial coordinates
and the already proved sign of the original Cartier obstruction.

These are cone-ring two-face identities. Their projective normalization,
assembly into a global Chern/KS cup class, and Hodge comparison are
separate obligations.

Prepared for fqlx with OpenAI ChatGPT assistance; see solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralCartierAtiyahFaces

open CycleQ2SeedTrace CycleQ2NormalConnecting CycleQ2GeometricCartierNormalLift
  CycleQ2LiteralCartierTransitionBinding CycleQ2GeometricSurfaceFirstOrder
  CycleQ2LiteralCartierSplittings CycleQ2LiteralCartierOverlapSplittings
  CycleQ2LiteralCartierKodairaSpencer CycleQ2GeometricSquareZeroSplittings
  CycleQ2GeometricCartierTransitionUnits

attribute [local instance] CycleQ2LiteralCartierTransitionBinding.cubicSelfModule
  CycleQ2LiteralCartierTransitionBinding.cubicOppositeModule
  CycleQ2LiteralCartierTransitionBinding.cubicCentralScalar
  CycleQ2LiteralCartierTransitionBinding.cubicSmulCommClass
  CycleQ2GeometricSurfaceFirstOrder.reducedAlgebra
  CycleQ2GeometricKernelLocalization.localReductionAlgebra
  CycleQ2LiteralCartierSplittings.complexReductionTower
  CycleQ2LiteralCartierOverlapSplittings.baseReductionAlgebra

def polynomialMap (s : Finset (Fin 4)) : WeightedPoly →+* Thick s :=
  (localPolynomialMap equation perturbation (denominator s)).comp cubicMap

theorem polynomialMap_cover_isUnit (s : Finset (Fin 4)) (i : Fin 4) (hi : i ∈ s) :
    IsUnit (polynomialMap s (coverPolynomial i)) := by
  exact IsLocalization.Away.isUnit_of_dvd (S := Thick s) (thickDenominator s)
    (map_dvd polynomialToThick (Finset.dvd_prod_of_mem coverPolynomial hi))

def perturbationSection (s : Finset (Fin 4)) : ClosedRing s :=
  localClosedPolynomialMap equation perturbation (denominator s) perturbation

theorem perturbationSection_binding (s : Finset (Fin 4)) :
    closedRingEquiv s (perturbationSection s) = coverPolyMap 57 1 s derivativeA :=
  closedRingEquiv_polynomial s derivativeA

theorem actual_factorization (s : Finset (Fin 4)) :
    polynomialMap s (originalF1 57) * polynomialMap s (originalG1 57) +
      polynomialMap s originalF2 * polynomialMap s originalG2 =
        epsilon (kernelEquiv s) (perturbationSection s) :=
  local_factored_deformation_equation equation perturbation (denominator s)
    firstEquation secondEquation firstCofactor secondCofactor
    equation_regular equation_factorization

/-- All four original factors really are units on either nonzero
triple face. The extra unit is deduced from the square-zero equation. -/
theorem factors_are_units (s : Finset (Fin 4)) (h0 : 0 ∈ s) (h1 : 1 ∈ s)
    (hf : 2 ∈ s ∨ 3 ∈ s) :
    IsUnit (polynomialMap s (originalF1 57)) ∧
      IsUnit (polynomialMap s originalF2) ∧
      IsUnit (polynomialMap s (originalG1 57)) ∧
      IsUnit (polynomialMap s originalG2) := by
  have hg1 : IsUnit (polynomialMap s (originalG1 57)) := polynomialMap_cover_isUnit s 0 h0
  have hg2 : IsUnit (polynomialMap s originalG2) := polynomialMap_cover_isUnit s 1 h1
  rcases hf with h2 | h3
  · have hf1 : IsUnit (polynomialMap s (originalF1 57)) := polynomialMap_cover_isUnit s 2 h2
    have h := complementary_factors_are_units (kernelEquiv s)
      (polynomialMap s (originalF1 57)) (polynomialMap s originalF2)
      (polynomialMap s (originalG1 57)) (polynomialMap s originalG2)
      (perturbationSection s) (actual_factorization s) (hf1.mul hg1)
    exact ⟨hf1, h.1, hg1, hg2⟩
  · have hf2 : IsUnit (polynomialMap s originalF2) := polynomialMap_cover_isUnit s 3 h3
    have he : polynomialMap s originalF2 * polynomialMap s originalG2 +
        polynomialMap s (originalF1 57) * polynomialMap s (originalG1 57) =
          epsilon (kernelEquiv s) (perturbationSection s) := by
      rw [add_comm]
      exact actual_factorization s
    have h := complementary_factors_are_units (kernelEquiv s)
      (polynomialMap s originalF2) (polynomialMap s (originalF1 57))
      (polynomialMap s originalG2) (polynomialMap s (originalG1 57))
      (perturbationSection s) he (hf2.mul hg2)
    exact ⟨h.1, hf2, hg1, hg2⟩

def factorPolynomial : Fin 4 → WeightedPoly :=
  ![originalF1 57, originalF2, originalG1 57, originalG2]

def factors (s : Finset (Fin 4)) (h0 : 0 ∈ s) (h1 : 1 ∈ s)
    (hf : 2 ∈ s ∨ 3 ∈ s) : Fin 4 → (Thick s)ˣ :=
  let h := factors_are_units s h0 h1 hf
  ![h.1.unit, h.2.1.unit, h.2.2.1.unit, h.2.2.2.unit]

theorem factors_value (s : Finset (Fin 4)) (h0 : 0 ∈ s) (h1 : 1 ∈ s)
    (hf : 2 ∈ s ∨ 3 ∈ s) (i : Fin 4) :
    (factors s h0 h1 hf i : Thick s) = polynomialMap s (factorPolynomial i) := by
  fin_cases i
  · exact (factors_are_units s h0 h1 hf).1.unit_spec
  · exact (factors_are_units s h0 h1 hf).2.1.unit_spec
  · exact (factors_are_units s h0 h1 hf).2.2.1.unit_spec
  · exact (factors_are_units s h0 h1 hf).2.2.2.unit_spec

theorem factors_relation (s : Finset (Fin 4)) (h0 : 0 ∈ s) (h1 : 1 ∈ s)
    (hf : 2 ∈ s ∨ 3 ∈ s) :
    (factors s h0 h1 hf 0 : Thick s) * factors s h0 h1 hf 2 +
      (factors s h0 h1 hf 1 : Thick s) * factors s h0 h1 hf 3 =
        epsilon (kernelEquiv s) (perturbationSection s) := by
  simpa only [factors_value, factorPolynomial, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons] using actual_factorization s

theorem reduced_factors_binding (s : Finset (Fin 4)) (h0 : 0 ∈ s) (h1 : 1 ∈ s)
    (hf : 2 ∈ s ∨ 3 ∈ s) (i : Fin 4) :
    closedRingEquiv s (reducedUnit (C := ClosedRing s) (factors s h0 h1 hf i) : ClosedRing s) =
      coverPolyMap 57 1 s (factorPolynomial i) := by
  rw [reducedUnit_val, factors_value]
  change closedRingEquiv s (algebraMap (Thick s) (ClosedRing s)
    (localPolynomialMap equation perturbation (denominator s) (cubicMap (factorPolynomial i)))) = _
  rw [localPolynomialMap_reduction, closedRingEquiv_polynomial]

theorem reduced_factor_inverse_binding (s : Finset (Fin 4)) (h0 : 0 ∈ s) (h1 : 1 ∈ s)
    (hf : 2 ∈ s ∨ 3 ∈ s) (i j : Fin 4) (hj : j ∈ s)
    (hij : factorPolynomial i = coverPolynomial j) :
    closedRingEquiv s (↑((reducedUnit (C := ClosedRing s) (factors s h0 h1 hf i))⁻¹) :
        ClosedRing s) =
      (↑((coverUnit 57 1 s j hj)⁻¹) : CoverLocal 57 1 s) := by
  have hu : Units.map (closedRingEquiv s).toRingHom.toMonoidHom
      (reducedUnit (C := ClosedRing s) (factors s h0 h1 hf i)) = coverUnit 57 1 s j hj := by
    apply Units.ext
    change closedRingEquiv s
      (reducedUnit (C := ClosedRing s) (factors s h0 h1 hf i) : ClosedRing s) = _
    rw [reduced_factors_binding, hij, coverUnit_value]
    fin_cases j <;> rfl
  change (↑((Units.map (closedRingEquiv s).toRingHom.toMonoidHom
    (reducedUnit (C := ClosedRing s) (factors s h0 h1 hf i)))⁻¹) : CoverLocal 57 1 s) = _
  rw [hu]

def sourceDefect (s : Finset (Fin 4)) (h0 : 0 ∈ s) (h1 : 1 ∈ s)
    (hf : 2 ∈ s ∨ 3 ∈ s) : ClosedRing s :=
  cartierUnitDefect (kernelEquiv s) (factors s h0 h1 hf 0) (factors s h0 h1 hf 1)
    (factors s h0 h1 hf 2) (factors s h0 h1 hf 3)
    (perturbationSection s) (factors_relation s h0 h1 hf)

def correction (s : Finset (Fin 4)) (h0 : 0 ∈ s) (h1 : 1 ∈ s)
    (hf : 2 ∈ s ∨ 3 ∈ s) : ClosedRing s :=
  unitCorrection (kernelEquiv s) (splittingOn 1 s h1) (splittingOn_reduction 1 s h1)
      (factors s h0 h1 hf 0) -
    unitCorrection (kernelEquiv s) (splittingOn 0 s h0) (splittingOn_reduction 0 s h0)
      (factors s h0 h1 hf 1) +
    unitCorrection (kernelEquiv s) (splittingOn 0 s h0) (splittingOn_reduction 0 s h0)
      (transition01 (factors s h0 h1 hf 2) (factors s h0 h1 hf 3))

/-- Evaluation of the genuine splitting difference on the genuine
universal dlog of the reduced first-equation transition. -/
def cup (s : Finset (Fin 4)) (h0 : 0 ∈ s) (h1 : 1 ∈ s)
    (hf : 2 ∈ s ∨ 3 ∈ s) : ClosedRing s :=
  (kodairaSpencer s 0 1 h0 h1).liftKaehlerDifferential
    (logDifferential (K := ℂ) (reducedUnit (C := ClosedRing s) (factors s h0 h1 hf 0)))

theorem sourceDefect_eq_correction_add_cup (s : Finset (Fin 4)) (h0 : 0 ∈ s) (h1 : 1 ∈ s)
    (hf : 2 ∈ s ∨ 3 ∈ s) :
    sourceDefect s h0 h1 hf = correction s h0 h1 hf + cup s h0 h1 hf :=
  unitDefect_eq_boundary_add_contraction (kernelEquiv s)
    (splittingOn 0 s h0) (splittingOn 1 s h1)
    (splittingOn_reduction 0 s h0) (splittingOn_reduction 1 s h1)
    (transition01 (factors s h0 h1 hf 2) (factors s h0 h1 hf 3))
    (factors s h0 h1 hf 0) (factors s h0 h1 hf 1)
    (transition_reduced_cocycle (kernelEquiv s) _ _ _ _ _ (factors_relation s h0 h1 hf))

theorem sourceDefect012_binding :
    closedRingEquiv {0,1,2} (sourceDefect {0,1,2} (by simp) (by simp) (by simp)) =
      -boundary012 57 1 derivativeA 0 := by
  unfold sourceDefect
  rw [cartierUnitDefect_first, map_mul, map_mul]
  rw [reduced_factor_inverse_binding _ _ _ _ 2 0 (by simp) rfl,
    reduced_factor_inverse_binding _ _ _ _ 0 2 (by simp) rfl]
  rw [perturbationSection_binding, boundary012_formula]
  simp only [mul_zero, zero_sub, map_neg]
  ring

theorem sourceDefect013_binding :
    closedRingEquiv {0,1,3} (sourceDefect {0,1,3} (by simp) (by simp) (by simp)) =
      -boundary013 57 1 derivativeA 0 := by
  unfold sourceDefect
  rw [cartierUnitDefect_second, map_mul, map_mul, map_neg]
  rw [reduced_factor_inverse_binding _ _ _ _ 3 1 (by simp) rfl,
    reduced_factor_inverse_binding _ _ _ _ 1 3 (by simp) rfl]
  rw [perturbationSection_binding, boundary013_formula]
  simp only [mul_zero, zero_sub, map_neg]
  ring

/-- Source-specific 012 face identity, with constructed original
splittings and the unchanged original Cartier obstruction. -/
theorem atiyah_face012 :
    closedRingEquiv {0,1,2}
      (correction {0,1,2} (by simp) (by simp) (by simp) +
        cup {0,1,2} (by simp) (by simp) (by simp)) =
      -boundary012 57 1 derivativeA 0 := by
  rw [← sourceDefect_eq_correction_add_cup, sourceDefect012_binding]

/-- The complementary source-specific 013 face, retaining the same
sigma_1 - sigma_0 and the original opposite boundary sign. -/
theorem atiyah_face013 :
    closedRingEquiv {0,1,3}
      (correction {0,1,3} (by simp) (by simp) (by simp) +
        cup {0,1,3} (by simp) (by simp) (by simp)) =
      -boundary013 57 1 derivativeA 0 := by
  rw [← sourceDefect_eq_correction_add_cup, sourceDefect013_binding]

end CycleQ2LiteralCartierAtiyahFaces

end

#print axioms CycleQ2LiteralCartierAtiyahFaces.sourceDefect012_binding
#print axioms CycleQ2LiteralCartierAtiyahFaces.sourceDefect013_binding
#print axioms CycleQ2LiteralCartierAtiyahFaces.atiyah_face012
#print axioms CycleQ2LiteralCartierAtiyahFaces.atiyah_face013
