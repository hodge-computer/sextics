import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.Algebra.Module.Submodule.Ker
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# The polynomial projector step in the weighted-threefold argument

This file formalizes the finite-dimensional algebra in §3B.6.  If an
endomorphism `S` maps into a subspace `W` and is injective on `W`, its minimal
polynomial on `W` produces a polynomial with zero constant coefficient whose
evaluation at `S` is a projector onto `W`.

In the geometric application one must separately construct the cohomology
spaces, the correspondence, its surjectivity and polarization adjoint, the
cycle-class map, and the support statements.  None of these geometric facts,
nor the target `HasCertificate`, is asserted here.
-/

noncomputable section

namespace PolynomialSupportedProjector

open Polynomial

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Remove the constant term of an annihilating polynomial and normalize it.
The zero constant coefficient is what avoids introducing the identity
correspondence in the supported polynomial expression. -/
def projectorPolynomial (m : K[X]) : K[X] :=
  C (-(m.coeff 0)⁻¹) * (m - C (m.coeff 0))

@[simp] theorem projectorPolynomial_coeff_zero (m : K[X]) :
    (projectorPolynomial m).coeff 0 = 0 := by
  simp [projectorPolynomial, coeff_mul]

private theorem restrict_pow_apply
    (W : Submodule K V) (S : Module.End K V)
    (hW : ∀ x ∈ W, S x ∈ W) (n : ℕ) (w : W) :
    (((S.restrict hW)^n) w : V) = (S^n) (w : V) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simpa only [pow_succ', Module.End.mul_apply,
        LinearMap.coe_restrict_apply] using congrArg S ih

/-- Evaluating a polynomial commutes with restriction to an invariant
subspace.  The statement includes the scalar/constant term. -/
theorem aeval_restrict_apply
    (W : Submodule K V) (S : Module.End K V)
    (hW : ∀ x ∈ W, S x ∈ W) (p : K[X]) (w : W) :
    ((aeval (S.restrict hW) p) w : V) = (aeval S p) (w : V) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      simp only [map_add, LinearMap.add_apply, Submodule.coe_add, hp, hq]
  | monomial n a =>
      simp only [aeval_monomial, Module.End.mul_apply,
        Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply,
        Module.End.one_apply, Submodule.coe_smul, restrict_pow_apply]

/-- A polynomial annihilating a vector, with nonzero constant coefficient,
produces the identity on that vector after this normalization. -/
theorem projectorPolynomial_fixes
    (S : Module.End K V) (m : K[X]) (hm : m.coeff 0 ≠ 0)
    (w : V) (hw : (aeval S m) w = 0) :
    (aeval S (projectorPolynomial m)) w = w := by
  simp only [projectorPolynomial, map_mul, map_sub, aeval_C,
    Module.End.mul_apply, LinearMap.sub_apply,
    Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply,
    Module.End.one_apply, hw, zero_sub, smul_neg, neg_smul,
    LinearMap.neg_apply, neg_neg, smul_smul, inv_mul_cancel₀ hm, one_smul]

/-- Any polynomial with zero constant coefficient maps into the image
subspace of its argument endomorphism. -/
theorem aeval_mem_of_coeff_zero
    (W : Submodule K V) (S : Module.End K V)
    (himage : ∀ v, S v ∈ W) (p : K[X]) (hp : p.coeff 0 = 0) (v : V) :
    (aeval S p) v ∈ W := by
  obtain ⟨r, hr⟩ := X_dvd_iff.mpr hp
  rw [hr, map_mul, aeval_X, Module.End.mul_apply]
  exact himage _

/-- The finite-dimensional projector construction, without any assumed
projector or polynomial inverse.  Injectivity on the image subspace is the
algebraic consequence supplied by the geometric polarization argument. -/
theorem exists_polynomial_projector
    (W : Submodule K V) [FiniteDimensional K W]
    (S : Module.End K V) (himage : ∀ v, S v ∈ W)
    (hinj : ∀ w ∈ W, S w = 0 → w = 0) :
    ∃ p : K[X], p.coeff 0 = 0 ∧
      (∀ w ∈ W, (aeval S p) w = w) ∧
      LinearMap.range (aeval S p) = W ∧
      (aeval S p) * (aeval S p) = aeval S p := by
  let hW : ∀ x ∈ W, S x ∈ W := fun x _ => himage x
  let T : Module.End K W := S.restrict hW
  have hT : Function.Injective T := by
    apply (LinearMap.ker_eq_bot).mp
    apply LinearMap.ker_eq_bot'.mpr
    intro w hw
    apply Subtype.ext
    apply hinj w w.property
    exact congrArg (fun z : W => (z : V)) hw
  let m : K[X] := minpoly K T
  have hm : m.coeff 0 ≠ 0 := LinearMap.minpoly_coeff_zero_of_injective hT
  let p := projectorPolynomial m
  have hp : p.coeff 0 = 0 := projectorPolynomial_coeff_zero m
  have hfix : ∀ w ∈ W, (aeval S p) w = w := by
    intro w hw
    apply projectorPolynomial_fixes S m hm w
    have hzero : (aeval T m) (⟨w, hw⟩ : W) = 0 := by
      rw [minpoly.aeval]
      rfl
    have hcoe := congrArg (fun z : W => (z : V)) hzero
    simpa only [T, aeval_restrict_apply, Submodule.coe_zero] using hcoe
  have hmem : ∀ v, (aeval S p) v ∈ W :=
    aeval_mem_of_coeff_zero W S himage p hp
  refine ⟨p, hp, hfix, ?_, ?_⟩
  · apply le_antisymm
    · rintro w ⟨v, rfl⟩
      exact hmem v
    · intro w hw
      exact ⟨w, hfix w hw⟩
  · ext v
    exact hfix _ (hmem v)

/-- If a named projector `P` is already present, compatibility with `S`
identifies that same map with a polynomial in `S` having no constant term.
In particular no inverse correspondence is assumed as input. -/
theorem exists_polynomial_eq_projector
    (W : Submodule K V) [FiniteDimensional K W]
    (S P : Module.End K V) (himage : ∀ v, S v ∈ W)
    (hinj : ∀ w ∈ W, S w = 0 → w = 0)
    (hPimage : ∀ v, P v ∈ W) (hSP : S * P = S) :
    ∃ p : K[X], p.coeff 0 = 0 ∧ aeval S p = P := by
  obtain ⟨p, hp, hfix, _, _⟩ := exists_polynomial_projector W S himage hinj
  refine ⟨p, hp, ?_⟩
  obtain ⟨r, hr⟩ := X_dvd_iff.mpr hp
  have heval : aeval S p = aeval S r * S := by
    rw [hr, mul_comm X r, map_mul, aeval_X]
  ext v
  have hSv : S (P v) = S v := LinearMap.congr_fun hSP v
  calc
    (aeval S p) v = (aeval S r) (S v) := by rw [heval]; rfl
    _ = (aeval S r) (S (P v)) := by rw [hSv]
    _ = (aeval S p) (P v) := by rw [heval]; rfl
    _ = P v := hfix _ (hPimage v)

section InnerProduct

variable {𝕜 E H : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedAddCommGroup H]
  [InnerProductSpace 𝕜 E] [InnerProductSpace 𝕜 H]
  [FiniteDimensional 𝕜 E]

/-- Positivity supplies the missing injectivity: the Gram operator of a
surjective map between finite-dimensional real/complex inner-product
spaces is injective. This uses the actual inner-product adjoint. -/
theorem gram_injective_of_surjective [FiniteDimensional 𝕜 H]
    (Γ : E →ₗ[𝕜] H) (hΓ : Function.Surjective Γ) :
    Function.Injective (Γ.comp Γ.adjoint) := by
  apply LinearMap.injective_iff_surjective.mpr
  apply LinearMap.range_eq_top.mp
  rw [LinearMap.range_self_comp_adjoint, LinearMap.range_eq_top.mpr hΓ]

/-- Combining the positive adjoint calculation with the minimal-polynomial
construction gives an actual polynomial expression for the identity on the
target of a surjective correspondence. -/
theorem exists_polynomial_gram_identity [FiniteDimensional 𝕜 H]
    (Γ : E →ₗ[𝕜] H) (hΓ : Function.Surjective Γ) :
    ∃ p : 𝕜[X], p.coeff 0 = 0 ∧ aeval (Γ.comp Γ.adjoint) p = 1 := by
  apply exists_polynomial_eq_projector (⊤ : Submodule 𝕜 H)
    (Γ.comp Γ.adjoint) 1 (fun _ => trivial)
  · intro w _ hw
    apply gram_injective_of_surjective Γ hΓ
    simpa only [map_zero] using hw
  · intro _
    trivial
  · exact mul_one _

/-- The ambient supported-projector form.  A surjective map to `W` and an
identification of the restricted operator with its Gram operator suffice;
the injectivity hypothesis of `exists_polynomial_eq_projector` is discharged.

For cohomology, identifying the polarization with a positive inner product
and identifying the algebraic transpose with this adjoint are additional
geometric assertions. They are not supplied by this theorem. The scalar
field here is real/complex; any rational structure is also separate. -/
theorem exists_polynomial_eq_projector_of_surjective_adjoint
    (W : Submodule 𝕜 H) [FiniteDimensional 𝕜 W]
    (Γ : E →ₗ[𝕜] W) (hΓ : Function.Surjective Γ)
    (S P : Module.End 𝕜 H) (himage : ∀ v, S v ∈ W)
    (hGram : ∀ w : W, S (w : H) = (Γ (Γ.adjoint w) : H))
    (hPimage : ∀ v, P v ∈ W) (hSP : S * P = S) :
    ∃ p : 𝕜[X], p.coeff 0 = 0 ∧ aeval S p = P := by
  apply exists_polynomial_eq_projector W S P himage ?_ hPimage hSP
  intro w hw hSw
  have hz : (Γ.comp Γ.adjoint) (⟨w, hw⟩ : W) = 0 := by
    apply Subtype.ext
    exact (hGram ⟨w, hw⟩).symm.trans hSw
  have hw0 : (⟨w, hw⟩ : W) = 0 := by
    apply gram_injective_of_surjective Γ hΓ
    simpa only [map_zero] using hz
  exact congrArg (fun z : W => (z : H)) hw0

end InnerProduct

#print axioms exists_polynomial_projector
#print axioms exists_polynomial_eq_projector
#print axioms gram_injective_of_surjective
#print axioms exists_polynomial_gram_identity
#print axioms exists_polynomial_eq_projector_of_surjective_adjoint

end PolynomialSupportedProjector
