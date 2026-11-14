import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.LinearAlgebra.Charpoly.Basic
import Proposal.GeometricTarget11Part04

/-!
# Positive adjoints and rational supported projectors

Source continuation of Part III.3 of the written nonconstructive argument.
This file has not been compiled or kernel checked.

The earlier projector algebra assumes an injective operator or an
annihilating polynomial with nonzero constant coefficient. Here these inputs
are derived from a surjective map of finite-dimensional positive inner
product spaces and an injective comparison with its adjoint composite. The
comparison allows an arbitrary nonzero complex scalar, including the sign
in the transpose-correspondence convention.

The final polynomial has rational coefficients. On a complementary pair of
rational subspaces it is the required projection, and it belongs to every
composition-stable rational submodule containing the original operator.

Geometric cohomology, the polarization comparison, and the interpretation
of that submodule as divisor-supported algebraic correspondences are not
defined by this file. No conclusion about the protected residue class is
asserted here.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace CycleQ2PolarizedProjector

open CycleQ2SupportedProjectorAlgebra

section PositiveAdjoint

variable {𝕜 E F : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [NormedAddCommGroup F]
variable [InnerProductSpace 𝕜 E] [InnerProductSpace 𝕜 F]
variable [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]

/-- The actual adjoint composite on the target positive inner product space. -/
def positiveOperator (A : E →ₗ[𝕜] F) : Module.End 𝕜 F :=
  A.comp A.adjoint

/-- Positive inner products identify the range of `A A†` with that of `A`.
The inner product hypotheses are essential: nondegenerate bilinear forms
alone do not imply this statement. -/
theorem positiveOperator_range (A : E →ₗ[𝕜] F) :
    LinearMap.range (positiveOperator A) = LinearMap.range A :=
  LinearMap.range_self_comp_adjoint A

/-- Surjectivity of the correspondence map supplies the injectivity needed
by the polynomial projector construction. -/
theorem positiveOperator_injective (A : E →ₗ[𝕜] F)
    (hA : Function.Surjective A) : Function.Injective (positiveOperator A) := by
  apply (LinearMap.injective_iff_surjective (f := positiveOperator A)).mpr
  apply LinearMap.range_eq_top.mp
  rw [positiveOperator_range]
  exact LinearMap.range_eq_top.mpr hA

/-- In finite dimension the adjoint composite is an invertible endomorphism. -/
theorem positiveOperator_isUnit (A : E →ₗ[𝕜] F)
    (hA : Function.Surjective A) : IsUnit (positiveOperator A) := by
  apply (LinearMap.isUnit_iff_ker_eq_bot (positiveOperator A)).mpr
  exact LinearMap.ker_eq_bot.mpr (positiveOperator_injective A hA)

/-- Multiplication by any nonzero scalar preserves the injectivity. This
retains the possible sign in the geometric adjoint comparison. -/
theorem scaled_positiveOperator_injective (A : E →ₗ[𝕜] F)
    (hA : Function.Surjective A) (c : 𝕜) (hc : c ≠ 0) :
    Function.Injective (c • positiveOperator A) := by
  intro x y hxy
  apply positiveOperator_injective A hA
  have h := congrArg (fun z : F => c⁻¹ • z) hxy
  simpa only [LinearMap.smul_apply, smul_smul, inv_mul_cancel₀ hc,
    one_smul] using h

end PositiveAdjoint

section RationalComparison

variable {V E F : Type*}
variable [AddCommGroup V] [Module ℚ V]
variable [NormedAddCommGroup E] [NormedAddCommGroup F]
variable [InnerProductSpace ℂ E] [InnerProductSpace ℂ F]
variable [FiniteDimensional ℂ E] [FiniteDimensional ℂ F]
variable [Module ℚ F] [IsScalarTower ℚ ℂ F]

/-- An injective comparison with a positive adjoint composite proves
injectivity of the rational correspondence operator itself. Only the
injectivity and intertwining equality of the comparison are used; its
geometric construction remains an independent obligation. -/
theorem injective_of_adjoint_comparison
    (M : Module.End ℚ V) (A : E →ₗ[ℂ] F) (hA : Function.Surjective A)
    (j : V →ₗ[ℚ] F) (hj : Function.Injective j)
    (c : ℂ) (hc : c ≠ 0)
    (hcompare : ∀ v : V, j (M v) = c • positiveOperator A (j v)) :
    Function.Injective M := by
  intro x y hxy
  apply hj
  apply scaled_positiveOperator_injective A hA c hc
  change c • positiveOperator A (j x) = c • positiveOperator A (j y)
  rw [← hcompare x, ← hcompare y, hxy]

variable [FiniteDimensional ℚ V]

/-- The rational minimal polynomial has nonzero constant coefficient. This
conclusion is obtained from positivity rather than assumed as projector data. -/
theorem minpoly_coeff_zero_ne_of_adjoint_comparison
    (M : Module.End ℚ V) (A : E →ₗ[ℂ] F) (hA : Function.Surjective A)
    (j : V →ₗ[ℚ] F) (hj : Function.Injective j)
    (c : ℂ) (hc : c ≠ 0)
    (hcompare : ∀ v : V, j (M v) = c • positiveOperator A (j v)) :
    (minpoly ℚ M).coeff 0 ≠ 0 :=
  LinearMap.minpoly_coeff_zero_of_injective
    (injective_of_adjoint_comparison M A hA j hj c hc hcompare)

/-- A rational zero-constant polynomial acting as the identity on the target
sector, constructed from the actual rational operator's minimal polynomial. -/
theorem exists_rational_identity_polynomial
    (M : Module.End ℚ V) (A : E →ₗ[ℂ] F) (hA : Function.Surjective A)
    (j : V →ₗ[ℚ] F) (hj : Function.Injective j)
    (c : ℂ) (hc : c ≠ 0)
    (hcompare : ∀ v : V, j (M v) = c • positiveOperator A (j v)) :
    ∃ p : Polynomial ℚ, p.coeff 0 = 0 ∧ Polynomial.aeval M p = 1 := by
  refine ⟨projectorPolynomial (minpoly ℚ M), ?_, ?_⟩
  · exact projectorPolynomial_coeff_zero (minpoly ℚ M)
      (minpoly_coeff_zero_ne_of_adjoint_comparison M A hA j hj c hc hcompare)
  · exact projectorPolynomial_aeval M (minpoly ℚ M) (minpoly.aeval ℚ M)

end RationalComparison

section InvariantSubspace

variable {K H : Type*} [Field K] [AddCommGroup H] [Module K H]

/-- Polynomial evaluation commutes with restriction to an invariant subspace.
This transports the constructed restricted annihilator to the full operator. -/
theorem aeval_restrict_apply
    (M : Module.End K H) (U : Submodule K H)
    (hU : ∀ x ∈ U, M x ∈ U) (p : Polynomial K) (u : U) :
    ((Polynomial.aeval (M.restrict hU) p) u : H) =
      Polynomial.aeval M p (u : H) := by
  change U.subtype ((Polynomial.aeval (M.restrict hU) p) u) =
    Polynomial.aeval M p (u : H)
  simp only [Polynomial.aeval_eq_sum_range, LinearMap.sum_apply,
    LinearMap.smul_apply, map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro n hn
  congr 1
  exact congrArg (fun N : Module.End K U => (N u : H))
    (Module.End.pow_restrict n hU)

end InvariantSubspace

section SupportedProjection

variable {H E F : Type*}
variable [AddCommGroup H] [Module ℚ H] [FiniteDimensional ℚ H]
variable [NormedAddCommGroup E] [NormedAddCommGroup F]
variable [InnerProductSpace ℂ E] [InnerProductSpace ℂ F]
variable [FiniteDimensional ℂ E] [FiniteDimensional ℂ F]
variable [Module ℚ F] [IsScalarTower ℚ ℂ F]

/-- Construct the rational projector on a specified direct summand from the
positive adjoint comparison on that summand. The operator is zero on the
complement. No annihilating polynomial or invertibility is supplied as a
hypothesis: both follow from the positive comparison.

The returned polynomial has zero constant term, so its evaluation remains
in any rational submodule closed under composition on the right by `M`.
To apply this to cycles, the relevant geometric support submodule and its
closure property must still be constructed and proved. -/
theorem exists_supported_rational_projector
    (S : Submodule ℚ (Module.End ℚ H))
    (M : Module.End ℚ H) (hM : M ∈ S)
    (hmul : ∀ N ∈ S, N * M ∈ S)
    (U W : Submodule ℚ H) (hUW : IsCompl U W)
    (hU : ∀ x ∈ U, M x ∈ U)
    (hW : ∀ w : W, M (w : H) = 0)
    (A : E →ₗ[ℂ] F) (hA : Function.Surjective A)
    (j : U →ₗ[ℚ] F) (hj : Function.Injective j)
    (c : ℂ) (hc : c ≠ 0)
    (hcompare : ∀ u : U,
      j (M.restrict hU u) = c • positiveOperator A (j u)) :
    ∃ p : Polynomial ℚ,
      p.coeff 0 = 0 ∧
      Polynomial.aeval M p = U.projection W hUW ∧
      Polynomial.aeval M p ∈ S := by
  let T : Module.End ℚ U := M.restrict hU
  let q : Polynomial ℚ := minpoly ℚ T
  have hq : q.coeff 0 ≠ 0 :=
    minpoly_coeff_zero_ne_of_adjoint_comparison T A hA j hj c hc hcompare
  have hAnn : ∀ u : U, Polynomial.aeval M q (u : H) = 0 := by
    intro u
    rw [← aeval_restrict_apply M U hU q u]
    change U.subtype ((Polynomial.aeval T (minpoly ℚ T)) u) = 0
    simp only [minpoly.aeval, LinearMap.zero_apply, map_zero]
  refine ⟨projectorPolynomial q, projectorPolynomial_coeff_zero q hq, ?_, ?_⟩
  · exact projectorPolynomial_aeval_eq_projection M U W hUW q hq hAnn hW
  · exact aeval_mem_of_coeff_zero S M hM hmul (projectorPolynomial q)
      (projectorPolynomial_coeff_zero q hq)

/-- The desired projection itself belongs to the composition-stable span. -/
theorem projection_mem_of_adjoint_comparison
    (S : Submodule ℚ (Module.End ℚ H))
    (M : Module.End ℚ H) (hM : M ∈ S)
    (hmul : ∀ N ∈ S, N * M ∈ S)
    (U W : Submodule ℚ H) (hUW : IsCompl U W)
    (hU : ∀ x ∈ U, M x ∈ U)
    (hW : ∀ w : W, M (w : H) = 0)
    (A : E →ₗ[ℂ] F) (hA : Function.Surjective A)
    (j : U →ₗ[ℚ] F) (hj : Function.Injective j)
    (c : ℂ) (hc : c ≠ 0)
    (hcompare : ∀ u : U,
      j (M.restrict hU u) = c • positiveOperator A (j u)) :
    U.projection W hUW ∈ S := by
  obtain ⟨p, _, hp, hS⟩ := exists_supported_rational_projector
    S M hM hmul U W hUW hU hW A hA j hj c hc hcompare
  rw [← hp]
  exact hS

end SupportedProjection

end CycleQ2PolarizedProjector

end
