import Proposal.GeometricIncidenceSeedFiber
import Mathlib.Algebra.DualNumber

/-!
# The actual pointed first-order path in the incidence parameter scheme

The retained seed map and the actual extended time derivation define the
complex algebra map a |-> (seedMap a, seedMap (timeDerivation a)) into the
dual numbers. Its closed point is the original seed. The original trace
parameter maps to epsilon and every original sextic coefficient has zero
epsilon part. All original incidence equations and both open conditions
hold along this actual first-order parameter point.

No curve flatness, nonemptiness, cycle-class or residue comparison is
asserted here. This constructs the precise base map to which the separate
first-order flatness criterion can eventually be applied.

Source-only draft: no Lean elaboration or kernel replay has been run.
Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md for
attribution of the geometric strategy and the protected certificate gap.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2IncidenceFirstOrder

open CategoryTheory AlgebraicGeometry MvPolynomial
open CycleQ2IncidenceNormalForm CycleQ2IncidenceMonomials
  CycleQ2IncidenceUniversalChart CycleQ2IncidencePolynomialJacobianBinding
  CycleQ2IncidenceEtaleParameter CycleQ2IncidenceTraceFamily
  CycleQ2IncidenceSeedFiber

/-- The coefficient map uses the original seed and original time vector
field, with no new tangent vector or coefficient specialization. -/
def firstOrderMap : ParameterAlgebra →ₐ[ℂ] DualNumber ℂ where
  toFun a := (seedMap a, seedMap (timeDerivation a))
  map_one' := by
    apply TrivSqZeroExt.ext
    · change seedMap 1 = 1
      exact map_one seedMap
    · change seedMap (timeDerivation 1) = 0
      rw [Derivation.map_one_eq_zero, map_zero]
  map_mul' a b := by
    apply TrivSqZeroExt.ext
    · change seedMap (a * b) = seedMap a * seedMap b
      exact map_mul seedMap a b
    · change seedMap (timeDerivation (a * b)) =
        seedMap a * seedMap (timeDerivation b) +
          seedMap (timeDerivation a) * seedMap b
      simp only [Derivation.leibniz, smul_eq_mul, map_add, map_mul]
      ring
  map_zero' := by
    apply TrivSqZeroExt.ext
    · change seedMap 0 = 0
      exact map_zero seedMap
    · change seedMap (timeDerivation 0) = 0
      rw [map_zero, map_zero]
  map_add' a b := by
    apply TrivSqZeroExt.ext
    · change seedMap (a + b) = seedMap a + seedMap b
      exact map_add seedMap a b
    · change seedMap (timeDerivation (a + b)) =
        seedMap (timeDerivation a) + seedMap (timeDerivation b)
      rw [map_add, map_add]
  commutes' c := by
    apply TrivSqZeroExt.ext
    · change seedMap (algebraMap ℂ ParameterAlgebra c) = c
      exact seedMap_complex c
    · change seedMap (timeDerivation (algebraMap ℂ ParameterAlgebra c)) = 0
      rw [Derivation.map_algebraMap, map_zero]

@[simp] theorem firstOrderMap_fst (a : ParameterAlgebra) :
    (firstOrderMap a).fst = seedMap a := rfl

@[simp] theorem firstOrderMap_snd (a : ParameterAlgebra) :
    (firstOrderMap a).snd = seedMap (timeDerivation a) := rfl

/-- Kept explicit so different coefficient specializations are never
installed as competing global algebra instances. -/
def firstOrderAlgebra : Algebra ParameterAlgebra (DualNumber ℂ) :=
  firstOrderMap.toRingHom.toAlgebra

def firstOrderIncidencePoint : ParameterIndex → DualNumber ℂ :=
  firstOrderMap ∘ incidencePoint

theorem firstOrderIncidencePoint_seed (j : ParameterIndex) :
    (firstOrderIncidencePoint j).fst = seedPoint (57 : ℂ) Complex.I j :=
  seedMap_incidencePoint j

theorem firstOrderMap_traceParameter :
    firstOrderMap (algebraMap TraceRing ParameterAlgebra traceParameter) =
      DualNumber.eps := by
  apply TrivSqZeroExt.ext
  · change seedMap (algebraMap TraceRing ParameterAlgebra traceParameter) = 0
    rw [seedMap_algebraMap]
    simp [seedEvaluation, traceParameter, baseSeed]
  · change seedMap (timeDerivation (algebraMap TraceRing ParameterAlgebra traceParameter)) = 1
    rw [timeDerivation_traceParameter, map_one]

/-- Every sextic coefficient is constant along this actual first-order
path, not just fixed modulo the closed point. -/
theorem firstOrderIncidencePoint_sextic (j : FullInvariantIndex 6) :
    firstOrderIncidencePoint (Sum.inr (Sum.inl j)) =
      TrivSqZeroExt.inl (seedPoint (57 : ℂ) Complex.I (Sum.inr (Sum.inl j))) := by
  apply TrivSqZeroExt.ext
  · exact firstOrderIncidencePoint_seed _
  · change seedMap (timeDerivation (incidencePoint (Sum.inr (Sum.inl j)))) = 0
    rw [incidence_sextic_derivative_zero, map_zero]

theorem firstOrderMap_aeval (p : ParameterPolynomial ℂ) :
    firstOrderMap (aeval incidencePoint p) = aeval firstOrderIncidencePoint p :=
  MvPolynomial.comp_aeval_apply (f := incidencePoint) firstOrderMap p

theorem firstOrder_original_equations (q : CycleQ2IncidenceCoefficientRelations.ColumnIndex) :
    aeval firstOrderIncidencePoint
      ((CycleQ2IncidencePolynomialRelations.presentation ℂ 57).equation q) = 0 := by
  rw [← firstOrderMap_aeval, CycleQ2EtaleIncidenceCurve.original_incidence_equations, map_zero]

theorem firstOrder_leading_unit :
    IsUnit (aeval firstOrderIncidencePoint (leadingProduct ℂ)) := by
  rw [← firstOrderMap_aeval]
  exact CycleQ2EtaleIncidenceCurve.leading_unit.map firstOrderMap

theorem firstOrder_basepoint_unit :
    IsUnit (aeval firstOrderIncidencePoint
      CycleQ2IncidenceBasepointOpen.basepointPolynomial) := by
  rw [← firstOrderMap_aeval]
  exact CycleQ2EtaleIncidenceCurve.basepoint_unit.map firstOrderMap

def firstOrderParameterPoint :
    Spec (CommRingCat.of (DualNumber ℂ)) ⟶ parameterScheme :=
  Spec.map (CommRingCat.ofHom firstOrderMap.toRingHom)

def firstOrderClosedPoint :
    Spec (CommRingCat.of ℂ) ⟶ Spec (CommRingCat.of (DualNumber ℂ)) :=
  Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom)

/-- The actual infinitesimal parameter point is based at the original
seed morphism into the original parameter scheme. -/
theorem firstOrderParameterPoint_at_seed :
    firstOrderClosedPoint ≫ firstOrderParameterPoint = seedPointMorphism := by
  rw [firstOrderClosedPoint, firstOrderParameterPoint, ← Spec.map_comp, seedPointMorphism]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  rfl

#print axioms firstOrderMap
#print axioms firstOrderMap_traceParameter
#print axioms firstOrderIncidencePoint_sextic
#print axioms firstOrder_original_equations
#print axioms firstOrderParameterPoint_at_seed

end CycleQ2IncidenceFirstOrder
end
