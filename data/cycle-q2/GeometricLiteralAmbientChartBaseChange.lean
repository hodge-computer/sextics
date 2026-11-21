import Proposal.GeometricSeedFamilyNormalized
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.RingTheory.TensorProduct.MvPolynomial

/-!
# Fiber of a normalized chart at the incidence coefficients

Specializing the cubic coefficients sends the defining relation of the normalized
ambient chart to `smoothF r Complex.I` and preserves the normalization
`X i.castSucc = 1`. The tensor-product equivalence below identifies the two
quotient algebras and tracks the specialization of every polynomial.

Prepared for `fqlx` with OpenAI ChatGPT assistance.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralAmbientChartBaseChange

open MvPolynomial CycleQ2IncidenceEquations CycleQ2SeedCubicFamily CycleQ2SeedFamilyNormalized
open scoped TensorProduct

/-- The complex coefficient field as an algebra at the incidence parameter. -/
@[instance_reducible] def incidenceAlgebra : Algebra ParameterRing ℂ :=
  (coefficientEvaluation incidenceCoefficients).toAlgebra

attribute [local instance] incidenceAlgebra

abbrev LiteralPolynomial := MvPolynomial (Fin 5) ℂ

def literalRelation (r : ℂ) (i : Fin 4) : Fin 2 → LiteralPolynomial :=
  ![smoothF r Complex.I, X i.castSucc - 1]

def literalIdeal (r : ℂ) (i : Fin 4) : Ideal LiteralPolynomial :=
  Ideal.span (Set.range (literalRelation r i))

theorem literalIdeal_eq_pair (r : ℂ) (i : Fin 4) :
    literalIdeal r i = Ideal.span {smoothF r Complex.I, X i.castSucc - 1} :=
  congrArg Ideal.span (Matrix.range_cons_cons_empty _ _ _)

abbrev LiteralRing (r : ℂ) (i : Fin 4) := LiteralPolynomial ⧸ literalIdeal r i
abbrev ChartFiber (r : ℂ) (i : Fin 4) := ℂ ⊗[ParameterRing] NormalizedRing r i

theorem map_normalizedRelation (r : ℂ) (i : Fin 4) (j : Fin 2) :
    MvPolynomial.map (coefficientEvaluation incidenceCoefficients) (normalizedRelation r i j) =
      literalRelation r i j := by
  fin_cases j
  · exact specialize_incidence r
  · change MvPolynomial.map _ (X i.castSucc - 1) = X i.castSucc - 1
    rw [map_sub, MvPolynomial.map_X, map_one]

theorem map_normalizedIdeal (r : ℂ) (i : Fin 4) :
    (normalizedIdeal r i).map (MvPolynomial.map (coefficientEvaluation incidenceCoefficients)) =
      literalIdeal r i := by
  unfold normalizedIdeal literalIdeal
  rw [Ideal.map_span, ← Set.range_comp]
  exact congrArg (fun f : Fin 2 → LiteralPolynomial => Ideal.span (Set.range f))
    (funext (map_normalizedRelation r i))

private abbrev TensorPolynomial := ℂ ⊗[ParameterRing] FamilyPolynomial

private def polynomialEquiv : TensorPolynomial ≃ₐ[ℂ] LiteralPolynomial :=
  MvPolynomial.algebraTensorAlgEquiv ParameterRing ℂ

private theorem polynomialEquiv_tmul (c : ℂ) (f : FamilyPolynomial) :
    polynomialEquiv (c ⊗ₜ[ParameterRing] f) =
      c • MvPolynomial.map (coefficientEvaluation incidenceCoefficients) f :=
  MvPolynomial.algebraTensorAlgEquiv_tmul ParameterRing ℂ c f

private def tensorIdeal (r : ℂ) (i : Fin 4) : Ideal TensorPolynomial :=
  (normalizedIdeal r i).map
    (Algebra.TensorProduct.includeRight (R := ParameterRing) (A := ℂ))

private theorem polynomialEquiv_includeRight :
    polynomialEquiv.toRingHom.comp
      (Algebra.TensorProduct.includeRight (R := ParameterRing) (A := ℂ)
        (B := FamilyPolynomial)).toRingHom =
      MvPolynomial.map (coefficientEvaluation incidenceCoefficients) := by
  apply RingHom.ext
  intro f
  change polynomialEquiv (1 ⊗ₜ[ParameterRing] f) = _
  rw [polynomialEquiv_tmul, one_smul]

private theorem map_tensorIdeal (r : ℂ) (i : Fin 4) :
    (tensorIdeal r i).map polynomialEquiv.toRingHom = literalIdeal r i := by
  unfold tensorIdeal
  exact (Ideal.map_map (I := normalizedIdeal r i)
    (Algebra.TensorProduct.includeRight (R := ParameterRing) (A := ℂ)
      (B := FamilyPolynomial)).toRingHom polynomialEquiv.toRingHom).trans
    ((congrArg (fun f : FamilyPolynomial →+* LiteralPolynomial => (normalizedIdeal r i).map f)
      polynomialEquiv_includeRight).trans (map_normalizedIdeal r i))

/-- Base change of the normalized ambient chart to the literal incidence point. -/
def normalizedFiberEquiv (r : ℂ) (i : Fin 4) : ChartFiber r i ≃ₐ[ℂ] LiteralRing r i :=
  (Algebra.TensorProduct.tensorQuotientEquiv (R := ParameterRing)
    ℂ FamilyPolynomial ℂ (normalizedIdeal r i)).trans
    (Ideal.quotientEquivAlg (tensorIdeal r i) (literalIdeal r i) polynomialEquiv
      (map_tensorIdeal r i).symm)

@[simp] theorem normalizedFiberEquiv_tmul (r : ℂ) (i : Fin 4) (c : ℂ) (f : FamilyPolynomial) :
    normalizedFiberEquiv r i (c ⊗ₜ[ParameterRing] normalizedQuotient r i f) =
      c • Ideal.Quotient.mk (literalIdeal r i)
        (MvPolynomial.map (coefficientEvaluation incidenceCoefficients) f) := by
  calc
    _ = Ideal.Quotient.mk (literalIdeal r i) (polynomialEquiv (c ⊗ₜ[ParameterRing] f)) := rfl
    _ = _ := by
      rw [polynomialEquiv_tmul]
      exact (Ideal.Quotient.mkₐ ℂ (literalIdeal r i)).toLinearMap.map_smul c _

theorem normalizedFiberEquiv_includeRight (r : ℂ) (i : Fin 4) (f : FamilyPolynomial) :
    normalizedFiberEquiv r i
      (Algebra.TensorProduct.includeRight (R := ParameterRing) (A := ℂ) (normalizedQuotient r i f)) =
      Ideal.Quotient.mk (literalIdeal r i)
        (MvPolynomial.map (coefficientEvaluation incidenceCoefficients) f) := by
  change normalizedFiberEquiv r i (1 ⊗ₜ[ParameterRing] normalizedQuotient r i f) = _
  rw [normalizedFiberEquiv_tmul, one_smul]

@[simp] theorem normalizedFiberEquiv_coordinate (r : ℂ) (i : Fin 4) (j : Fin 5) :
    normalizedFiberEquiv r i (1 ⊗ₜ[ParameterRing] normalizedCoordinate r i j) =
      Ideal.Quotient.mk (literalIdeal r i) (X j) := by
  rw [normalizedCoordinate, normalizedFiberEquiv_tmul, MvPolynomial.map_X, one_smul]

end CycleQ2LiteralAmbientChartBaseChange

end

#print axioms CycleQ2LiteralAmbientChartBaseChange.normalizedFiberEquiv
#print axioms CycleQ2LiteralAmbientChartBaseChange.normalizedFiberEquiv_includeRight
#print axioms CycleQ2LiteralAmbientChartBaseChange.normalizedFiberEquiv_coordinate
