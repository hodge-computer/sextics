import Proposal.GeometricIncidenceFirstOrder
import Proposal.GeometricDualNumberRegularQuotient
import Mathlib.RingTheory.Flat.Stability
import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# Reduction of the actual first-order base change modulo epsilon

The dual-number action is the retained seed-plus-time-derivation map.
For every algebra over the original parameter algebra, reduction of its
actual first-order tensor product modulo epsilon is its retained seed
tensor product. The equivalence preserves every element from the second
tensor factor, so it also preserves the original normalized equations.

The final lemma applies the proved dual-number quotient criterion when
the ambient parameter algebra is flat and its retained seed equation is
regular. These are explicit hypotheses of the general algebra lemma;
this file makes no flatness assertion for an arbitrary surface chart or
for the curve over the full parameter base.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md for
attribution of the geometric route and the protected certificate gap.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2FirstOrderTensorReduction

open scoped DualNumber TensorProduct
open CycleQ2IncidenceEtaleParameter CycleQ2IncidenceFirstOrder
  CycleQ2DualNumberRegularQuotient

attribute [local instance] CycleQ2IncidenceSeedFiber.seedAlgebra

local instance parameterFirstOrderAlgebra : Algebra ParameterAlgebra ℂ[ε] :=
  firstOrderMap.toRingHom.toAlgebra

local instance parameterFirstOrderModule : Module ParameterAlgebra ℂ[ε] :=
  parameterFirstOrderAlgebra.toModule
local instance parameterFirstOrderSMul : SMul ParameterAlgebra ℂ[ε] :=
  parameterFirstOrderAlgebra.toSMul

local instance parameterFirstOrderTower : IsScalarTower ParameterAlgebra ParameterAlgebra ℂ[ε] :=
  ⟨fun a b c => by
    change firstOrderMap (a * b) * c = firstOrderMap a * (firstOrderMap b * c)
    rw [map_mul, mul_assoc]⟩

/-- The closed-point map is linear for the actual two parameter actions. -/
def firstOrderFst : ℂ[ε] →ₐ[ParameterAlgebra] ℂ where
  toRingHom := (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom
  commutes' _ := rfl

theorem firstOrderFst_surjective : Function.Surjective firstOrderFst :=
  fun c => ⟨TrivSqZeroExt.inl c, rfl⟩

theorem firstOrderFst_ker :
    RingHom.ker firstOrderFst = Ideal.span {ε} := by
  ext a
  change a.fst = 0 ↔ a ∈ Ideal.span {ε}
  rw [Ideal.mem_span_singleton, DualNumber.fst_eq_zero_iff_eps_dvd]

def epsilonQuotientEquiv :
    (ℂ[ε] ⧸ (Ideal.span {ε} : Ideal ℂ[ε])) ≃ₐ[ParameterAlgebra] ℂ :=
  (Ideal.quotientEquivAlgOfEq ParameterAlgebra firstOrderFst_ker.symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (f := firstOrderFst) firstOrderFst_surjective)

@[simp] theorem epsilonQuotientEquiv_mk (a : ℂ[ε]) :
    epsilonQuotientEquiv (Ideal.Quotient.mk (Ideal.span {ε}) a) = a.fst := by
  rw [epsilonQuotientEquiv, AlgEquiv.trans_apply, Ideal.quotientEquivAlgOfEq_mk,
    Ideal.quotientKerAlgEquivOfSurjective_mk]
  rfl

variable (B : Type) [CommRing B] [Algebra ParameterAlgebra B]

abbrev FirstOrderTensor := ℂ[ε] ⊗[ParameterAlgebra] B
abbrev SeedTensor := ℂ ⊗[ParameterAlgebra] B

local instance firstOrderTensorCommRing : CommRing (FirstOrderTensor B) := inferInstance
local instance seedTensorCommRing : CommRing (SeedTensor B) := inferInstance

theorem epsilonIdeal_eq_map :
    (Ideal.span {ε} : Ideal ℂ[ε]).map (algebraMap ℂ[ε] (FirstOrderTensor B)) =
      epsilonIdeal (k := ℂ) (FirstOrderTensor B) := by
  rw [Ideal.map_span, Set.image_singleton]
  rfl

/-- The exact special fiber of the tensor product along firstOrderMap. -/
def epsilonReductionEquiv :
    (FirstOrderTensor B ⧸ epsilonIdeal (k := ℂ) (FirstOrderTensor B)) ≃ₐ[ParameterAlgebra]
      SeedTensor B :=
  (Ideal.quotientEquivAlgOfEq ParameterAlgebra (epsilonIdeal_eq_map B).symm).trans
    ((Algebra.TensorProduct.quotientTensorEquiv (R := ParameterAlgebra)
      ParameterAlgebra B ℂ[ε] (Ideal.span {ε})).symm.trans
        (Algebra.TensorProduct.congr epsilonQuotientEquiv (AlgEquiv.refl : B ≃ₐ[ParameterAlgebra] B)))

@[simp] theorem epsilonReductionEquiv_tmul (a : ℂ[ε]) (b : B) :
    epsilonReductionEquiv B
      (Ideal.Quotient.mk (epsilonIdeal (k := ℂ) (FirstOrderTensor B))
        (a ⊗ₜ[ParameterAlgebra] b)) = a.fst ⊗ₜ[ParameterAlgebra] b := by
  rw [epsilonReductionEquiv, AlgEquiv.trans_apply, Ideal.quotientEquivAlgOfEq_mk,
    AlgEquiv.trans_apply, Algebra.TensorProduct.quotientTensorEquiv_symm_apply_tmul,
    Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul]
  exact congrArg (fun c : ℂ => c ⊗ₜ[ParameterAlgebra] b) (epsilonQuotientEquiv_mk a)

/-- A seed-regular equation in a flat ambient algebra defines a flat
quotient along the specific original first-order parameter path. -/
theorem firstOrder_principalQuotient_flat [Module.Flat ParameterAlgebra B] (f : B)
    (hreg : IsSMulRegular (SeedTensor B) ((1 : ℂ) ⊗ₜ[ParameterAlgebra] f)) :
    Module.Flat ℂ[ε] (FirstOrderTensor B ⧸ Ideal.span {(1 : ℂ[ε]) ⊗ₜ[ParameterAlgebra] f}) := by
  letI : Module.Flat ℂ[ε] (FirstOrderTensor B) := inferInstance
  apply quotient_flat (k := ℂ) (B := FirstOrderTensor B) ((1 : ℂ[ε]) ⊗ₜ[ParameterAlgebra] f)
  apply IsSMulRegular.of_right_eq_zero_of_smul
  intro a ha
  apply (epsilonReductionEquiv B).injective
  rw [map_zero]
  apply hreg.right_eq_zero_of_smul
  change ((1 : ℂ) ⊗ₜ[ParameterAlgebra] f) * epsilonReductionEquiv B a = 0
  change Ideal.Quotient.mk (epsilonIdeal (k := ℂ) (FirstOrderTensor B))
    ((1 : ℂ[ε]) ⊗ₜ[ParameterAlgebra] f) * a = 0 at ha
  have h := congrArg (epsilonReductionEquiv B) ha
  simpa only [map_mul, map_zero, epsilonReductionEquiv_tmul,
    TrivSqZeroExt.fst_one] using h

#print axioms firstOrderFst_ker
#print axioms epsilonReductionEquiv
#print axioms epsilonReductionEquiv_tmul
#print axioms firstOrder_principalQuotient_flat

end CycleQ2FirstOrderTensorReduction
end
