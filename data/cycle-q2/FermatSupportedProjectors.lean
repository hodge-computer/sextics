import Mathlib.LinearAlgebra.Charpoly.Basic
import Proposal.FermatJacobianHiggsForms

/-! # Self-adjoint projectors and their polynomial realization on the Fermat Jacobian -/

set_option Elab.async false

/- Uncompiled continuation: GeometricBridgeAlgebra.lean (2026-11-12). -/
section Q2UncompiledHiggsBridge

/-!
# Self-adjoint projectors on the actual Fermat Jacobian component

This file supplies an algebraic step in the reconstructed geometric argument.
The existing finite theorem `CycleQ2FermatHiggs.compatible_projector_trivial`
concerns matrices. Here it is applied to endomorphisms of the actual
`CycleQ2FermatJacobian.gradedPiece 6 1`, using the actual socle triple-product
pairings and the already constructed monomial basis.

In particular, the compatibility premise below is an equality in the actual
Fermat derivative quotient, not a premise asserting geometric support or
existence of a residue primitive. Interpreting a geometric polarized sub-VHS
projector as one of these endomorphisms remains a separate geometric theorem.

Written against the recorded project sources and the pinned mathlib source
at 0df444a360eaa60ab8c11dca51a86af692955474. Development compilation status
is recorded in solution.md.
-/

set_option autoImplicit false

noncomputable section

namespace CycleQ2GeometricBridgeAlgebra

open CycleQ2FermatJacobian

open scoped BigOperators

/-- The actual degree-six character-one component of the Fermat quotient. -/
abbrev InvariantHodgeModel := gradedPiece 6 1

/-- The actual degree-six character-zero deformation component. -/
abbrev InvariantTangentModel := gradedPiece 6 0

/-- The triple-product form on the actual quotient, linear in both inputs.
The names of the models indicate their intended geometric interpretation;
no Hodge-theoretic comparison is assumed or asserted in this definition. -/
def actualTracePairing (t : InvariantTangentModel) :
    InvariantHodgeModel →ₗ[ℂ] InvariantHodgeModel →ₗ[ℂ] ℂ where
  toFun u :=
    { toFun := fun v =>
        socleTrace ((u : JacobianRing) * (v : JacobianRing) * (t : JacobianRing))
      map_add' := by
        intro v w
        simp [mul_add, add_mul]
      map_smul' := by
        intro c v
        simp [mul_smul_comm, smul_mul_assoc] }
  map_add' := by
    intro u v
    ext w
    simp [add_mul]
  map_smul' := by
    intro c u
    ext v
    simp [smul_mul_assoc]

@[simp] theorem actualTracePairing_apply (t : InvariantTangentModel)
    (u v : InvariantHodgeModel) :
    actualTracePairing t u v =
      socleTrace ((u : JacobianRing) * (v : JacobianRing) * (t : JacobianRing)) :=
  rfl

theorem actualTracePairing_symmetric (t : InvariantTangentModel)
    (u v : InvariantHodgeModel) :
    actualTracePairing t u v = actualTracePairing t v u := by
  change socleTrace ((u : JacobianRing) * (v : JacobianRing) * (t : JacobianRing)) =
    socleTrace ((v : JacobianRing) * (u : JacobianRing) * (t : JacobianRing))
  rw [mul_comm (u : JacobianRing) (v : JacobianRing)]

@[simp] theorem actualTracePairing_flip_apply (t : InvariantTangentModel)
    (u v : InvariantHodgeModel) :
    (actualTracePairing t).flip v u = actualTracePairing t u v :=
  rfl

/-- Its matrices are the already proved finite Fermat Higgs matrices. -/
theorem actualTracePairing_basis (m : Fin 35) (i j : Fin 33) :
    actualTracePairing (degreeSixCharacterZeroBasis m)
      (degreeSixCharacterOneBasis i) (degreeSixCharacterOneBasis j) =
        CycleQ2FermatHiggs.higgsMatrix ℂ m i j :=
  actual_component_trace_matrix m i j

/-- The matrix of an actual endomorphism, with the established quotient basis. -/
def actualEndomorphismMatrix
    (P : Module.End ℂ InvariantHodgeModel) : Matrix (Fin 33) (Fin 33) ℂ :=
  LinearMap.toMatrixAlgEquiv degreeSixCharacterOneBasis P

theorem actualEndomorphismMatrix_apply
    (P : Module.End ℂ InvariantHodgeModel) (i j : Fin 33) :
    actualEndomorphismMatrix P i j =
      degreeSixCharacterOneBasis.repr (P (degreeSixCharacterOneBasis j)) i :=
  LinearMap.toMatrixAlgEquiv_apply degreeSixCharacterOneBasis P i j

theorem actualTracePairing_expand_left (t : InvariantTangentModel)
    (u v : InvariantHodgeModel) :
    actualTracePairing t u v =
      ∑ i : Fin 33, degreeSixCharacterOneBasis.repr u i *
        actualTracePairing t (degreeSixCharacterOneBasis i) v := by
  have h := congrArg ((actualTracePairing t).flip v)
    (degreeSixCharacterOneBasis.sum_repr u)
  simpa only [map_sum, map_smul, actualTracePairing_flip_apply, smul_eq_mul]
    using h.symm

theorem actualTracePairing_expand_right (t : InvariantTangentModel)
    (u v : InvariantHodgeModel) :
    actualTracePairing t u v =
      ∑ i : Fin 33, degreeSixCharacterOneBasis.repr v i *
        actualTracePairing t u (degreeSixCharacterOneBasis i) := by
  have h := congrArg (actualTracePairing t u)
    (degreeSixCharacterOneBasis.sum_repr v)
  simpa only [map_sum, map_smul, smul_eq_mul] using h.symm

/-- The left side of the finite commutant equation is evaluation of the
actual trace pairing after applying the endomorphism to its first input. -/
theorem transpose_mul_higgs_eq_actualTracePairing
    (P : Module.End ℂ InvariantHodgeModel) (m : Fin 35) (i j : Fin 33) :
    ((actualEndomorphismMatrix P).transpose *
        CycleQ2FermatHiggs.higgsMatrix ℂ m) i j =
      actualTracePairing (degreeSixCharacterZeroBasis m)
        (P (degreeSixCharacterOneBasis i)) (degreeSixCharacterOneBasis j) := by
  rw [actualTracePairing_expand_left]
  simp only [Matrix.mul_apply, Matrix.transpose_apply,
    actualEndomorphismMatrix_apply, actualTracePairing_basis]

/-- The right side of the finite commutant equation is evaluation after
applying the actual endomorphism to the second input. -/
theorem higgs_mul_eq_actualTracePairing
    (P : Module.End ℂ InvariantHodgeModel) (m : Fin 35) (i j : Fin 33) :
    (CycleQ2FermatHiggs.higgsMatrix ℂ m * actualEndomorphismMatrix P) i j =
      actualTracePairing (degreeSixCharacterZeroBasis m)
        (degreeSixCharacterOneBasis i) (P (degreeSixCharacterOneBasis j)) := by
  rw [actualTracePairing_expand_right]
  simp only [Matrix.mul_apply, actualEndomorphismMatrix_apply,
    actualTracePairing_basis]
  apply Finset.sum_congr rfl
  intro k _
  exact mul_comm _ _

/-- Self-adjointness for the genuine triple-product pairings implies the
finite matrix compatibility equations, with no geometric comparison premise. -/
theorem higgs_equations_of_actual_trace_selfAdjoint
    (P : Module.End ℂ InvariantHodgeModel)
    (hP : ∀ (t : InvariantTangentModel) (u v : InvariantHodgeModel),
      actualTracePairing t (P u) v = actualTracePairing t u (P v)) :
    ∀ m : Fin 35,
      (actualEndomorphismMatrix P).transpose *
          CycleQ2FermatHiggs.higgsMatrix ℂ m =
        CycleQ2FermatHiggs.higgsMatrix ℂ m * actualEndomorphismMatrix P := by
  intro m
  ext i j
  rw [transpose_mul_higgs_eq_actualTracePairing,
    higgs_mul_eq_actualTracePairing]
  exact hP (degreeSixCharacterZeroBasis m)
    (degreeSixCharacterOneBasis i) (degreeSixCharacterOneBasis j)

/-- An idempotent on the actual Fermat component that is self-adjoint for
every actual trace pairing is zero or the identity. This is the algebraic
projector conclusion needed at the Fermat point in the geometric Higgs
argument. It does not assert existence of a geometric subvariation projector. -/
theorem actual_trace_selfAdjoint_projector_trivial
    (P : Module.End ℂ InvariantHodgeModel)
    (hP : ∀ (t : InvariantTangentModel) (u v : InvariantHodgeModel),
      actualTracePairing t (P u) v = actualTracePairing t u (P v))
    (hIdempotent : P * P = P) : P = 0 ∨ P = 1 := by
  let e := LinearMap.toMatrixAlgEquiv degreeSixCharacterOneBasis
  have hMatrix : actualEndomorphismMatrix P * actualEndomorphismMatrix P =
      actualEndomorphismMatrix P := by
    change e P * e P = e P
    rw [← map_mul, hIdempotent]
  rcases CycleQ2FermatHiggs.compatible_projector_trivial
      (actualEndomorphismMatrix P)
      (higgs_equations_of_actual_trace_selfAdjoint P hP) hMatrix with hZero | hOne
  · left
    apply e.injective
    simpa only [actualEndomorphismMatrix, e, map_zero] using hZero
  · right
    apply e.injective
    simpa only [actualEndomorphismMatrix, e, map_one] using hOne

/-- Consequently no proper nonzero image can occur for such a projector. -/
theorem actual_trace_selfAdjoint_projector_range
    (P : Module.End ℂ InvariantHodgeModel)
    (hP : ∀ (t : InvariantTangentModel) (u v : InvariantHodgeModel),
      actualTracePairing t (P u) v = actualTracePairing t u (P v))
    (hIdempotent : P * P = P) :
    LinearMap.range P = ⊥ ∨ LinearMap.range P = ⊤ := by
  rcases actual_trace_selfAdjoint_projector_trivial P hP hIdempotent with hZero | hOne
  · left
    rw [hZero]
    simp
  · right
    rw [hOne]
    simp [Module.End.one_eq_id]

end CycleQ2GeometricBridgeAlgebra

end

end Q2UncompiledHiggsBridge

/- Component: continuation_20261112/SupportedProjectorAlgebra.lean -/
section Q2UncompiledProjectorConstruction

/-!
# Orthogonal generation and polynomial projectors for cycle-q2

DEVELOPMENT CONTINUATION, 12 November 2026. Compilation status is recorded
in solution.md. These lemmas extend the existing actual Fermat trace-pairing
bridge. They do not define a geometric variation of Hodge structure or an
algebraic cycle class map, and they do not prove residue exactness.

This component continues the actual Fermat trace-pairing bridge above.
-/

set_option autoImplicit false

noncomputable section

namespace CycleQ2GeometricBridgeAlgebra

/-- A common orthogonal direct sum for the actual socle pairings gives an
actual self-adjoint projection. The projection is constructed from the two
submodules; it is not supplied as an additional hypothesis. -/
theorem actual_trace_projection_selfAdjoint
    (U W : Submodule ℂ InvariantHodgeModel) (hUW : IsCompl U W)
    (horth : ∀ (t : InvariantTangentModel) (u : U) (w : W),
      actualTracePairing t (u : InvariantHodgeModel)
        (w : InvariantHodgeModel) = 0) :
    ∀ (t : InvariantTangentModel) (u v : InvariantHodgeModel),
      actualTracePairing t (U.projection W hUW u) v =
        actualTracePairing t u (U.projection W hUW v) := by
  intro t u v
  obtain ⟨u₁, u₂, hu, _⟩ := Submodule.existsUnique_add_of_isCompl hUW u
  obtain ⟨v₁, v₂, hv, _⟩ := Submodule.existsUnique_add_of_isCompl hUW v
  have hcross : actualTracePairing t (u₂ : InvariantHodgeModel)
      (v₁ : InvariantHodgeModel) = 0 := by
    rw [actualTracePairing_symmetric]
    exact horth t v₁ u₂
  rw [← hu, ← hv]
  simp only [map_add, LinearMap.add_apply,
    Submodule.projection_apply_left, Submodule.projection_apply_right,
    add_zero, horth t u₁ v₂, hcross]

/-- The finite Higgs result rules out a proper nonzero submodule having a
complement orthogonal for every actual socle pairing. -/
theorem actual_trace_orthogonal_direct_sum_trivial
    (U W : Submodule ℂ InvariantHodgeModel) (hUW : IsCompl U W)
    (horth : ∀ (t : InvariantTangentModel) (u : U) (w : W),
      actualTracePairing t (u : InvariantHodgeModel)
        (w : InvariantHodgeModel) = 0) :
    U = ⊥ ∨ U = ⊤ := by
  have hIdempotent : U.projection W hUW * U.projection W hUW =
      U.projection W hUW :=
    Submodule.isIdempotentElem_projection hUW
  have h := actual_trace_selfAdjoint_projector_range
    (U.projection W hUW)
    (actual_trace_projection_selfAdjoint U W hUW horth) hIdempotent
  simpa only [Submodule.range_projection] using h

/-- Once a geometric construction supplies the common orthogonal complement
of its image in the actual Fermat component, one nonzero image suffices for
surjectivity. The needed orthogonality remains an explicit algebraic premise. -/
theorem actual_trace_orthogonal_range_surjective
    {A : Type*} [AddCommGroup A] [Module ℂ A]
    (f : A →ₗ[ℂ] InvariantHodgeModel)
    (W : Submodule ℂ InvariantHodgeModel)
    (hW : IsCompl (LinearMap.range f) W)
    (horth : ∀ (t : InvariantTangentModel)
      (u : LinearMap.range f) (w : W),
      actualTracePairing t (u : InvariantHodgeModel)
        (w : InvariantHodgeModel) = 0)
    (hf : f ≠ 0) : Function.Surjective f := by
  rcases actual_trace_orthogonal_direct_sum_trivial
      (LinearMap.range f) W hW horth with hZero | hTop
  · exfalso
    apply hf
    apply LinearMap.ext
    intro x
    have hx : f x ∈ LinearMap.range f := ⟨x, rfl⟩
    rw [hZero] at hx
    simpa only [Submodule.mem_bot, LinearMap.zero_apply] using hx
  · exact LinearMap.range_eq_top.mp hTop

end CycleQ2GeometricBridgeAlgebra

namespace CycleQ2SupportedProjectorAlgebra

variable {K : Type*} [Field K]

/-- Normalization of an annihilating polynomial. Its constant coefficient
vanishes if the original constant coefficient is nonzero. -/
def projectorPolynomial (q : Polynomial K) : Polynomial K :=
  1 - Polynomial.C ((q.coeff 0)⁻¹) * q

theorem projectorPolynomial_coeff_zero (q : Polynomial K)
    (hq : q.coeff 0 ≠ 0) : (projectorPolynomial q).coeff 0 = 0 := by
  simp [projectorPolynomial, hq]

/-- Evaluation of the normalized annihilator is the identity. This is valid
in a possibly noncommutative algebra, including an endomorphism algebra. -/
theorem projectorPolynomial_aeval
    {A : Type*} [Ring A] [Algebra K A]
    (M : A) (q : Polynomial K) (hq : Polynomial.aeval M q = 0) :
    Polynomial.aeval M (projectorPolynomial q) = 1 := by
  simp [projectorPolynomial, hq]

section Endomorphisms

variable {V : Type*} [AddCommGroup V] [Module K V]

/-- A polynomial with zero constant coefficient kills every vector killed
by the endomorphism. Factoring by X makes the composition order explicit. -/
theorem aeval_apply_zero_of_coeff_zero
    (M : Module.End K V) (p : Polynomial K) (hp : p.coeff 0 = 0)
    (v : V) (hv : M v = 0) : Polynomial.aeval M p v = 0 := by
  obtain ⟨r, hr⟩ := Polynomial.X_dvd_iff.mpr hp
  rw [hr, mul_comm (Polynomial.X : Polynomial K) r, map_mul,
    Polynomial.aeval_X]
  change Polynomial.aeval M r (M v) = 0
  rw [hv, map_zero]

/-- On the kernel of the chosen annihilator, the normalized polynomial acts
as the identity even if that annihilator does not vanish on the whole space. -/
theorem projectorPolynomial_apply_of_annihilator
    (M : Module.End K V) (q : Polynomial K) (v : V)
    (hv : Polynomial.aeval M q v = 0) :
    Polynomial.aeval M (projectorPolynomial q) v = v := by
  simp only [projectorPolynomial, map_sub, map_one, map_mul,
    Polynomial.aeval_C]
  change v - (algebraMap K (Module.End K V) ((q.coeff 0)⁻¹))
    (Polynomial.aeval M q v) = v
  rw [hv, map_zero, sub_zero]

/-- The normalized polynomial selects one direct summand: its restriction
there is the identity and its restriction to the other summand is zero. -/
theorem projectorPolynomial_aeval_eq_projection
    (M : Module.End K V)
    (U W : Submodule K V) (hUW : IsCompl U W)
    (q : Polynomial K) (hq : q.coeff 0 ≠ 0)
    (hU : ∀ u : U, Polynomial.aeval M q (u : V) = 0)
    (hW : ∀ w : W, M (w : V) = 0) :
    Polynomial.aeval M (projectorPolynomial q) = U.projection W hUW := by
  ext v
  obtain ⟨u, w, hv, _⟩ := Submodule.existsUnique_add_of_isCompl hUW v
  rw [← hv, map_add, map_add, Submodule.projection_apply_left,
    Submodule.projection_apply_right]
  rw [projectorPolynomial_apply_of_annihilator M q (u : V) (hU u),
    aeval_apply_zero_of_coeff_zero M (projectorPolynomial q)
      (projectorPolynomial_coeff_zero q hq) (w : V) (hW w)]

end Endomorphisms

/-- The algebraic support argument needs only closure under sums, scalars,
and composition on the right by M. A zero-constant polynomial in M then
belongs to the same submodule. No algebraic cycle support is defined here. -/
theorem aeval_mem_of_coeff_zero
    {A : Type*} [Ring A] [Algebra K A]
    (S : Submodule K A) (M : A) (hM : M ∈ S)
    (hmul : ∀ N ∈ S, N * M ∈ S)
    (p : Polynomial K) (hp : p.coeff 0 = 0) :
    Polynomial.aeval M p ∈ S := by
  have hpowers (n : ℕ) : M ^ (n + 1) ∈ S := by
    induction n with
    | zero => simpa only [Nat.zero_add, pow_one] using hM
    | succ n ih =>
      simpa only [Nat.succ_eq_add_one, pow_succ] using hmul (M ^ (n + 1)) ih
  rw [Polynomial.aeval_eq_sum_range]
  apply S.sum_mem
  intro n hn
  cases n with
  | zero => simpa only [hp, zero_smul] using S.zero_mem
  | succ n => exact S.smul_mem (p.coeff (n + 1)) (hpowers n)

/-- A supplied algebraic correspondence operator, with its two summands and
annihilator, yields an actual idempotent in any composition-stable submodule
containing that operator. In a geometric application the submodule must be
proved to consist of classes represented on the required divisor square. -/
theorem projection_mem_of_annihilator
    {V : Type*} [AddCommGroup V] [Module K V]
    (S : Submodule K (Module.End K V))
    (M : Module.End K V) (hM : M ∈ S)
    (hmul : ∀ N ∈ S, N * M ∈ S)
    (U W : Submodule K V) (hUW : IsCompl U W)
    (q : Polynomial K) (hq : q.coeff 0 ≠ 0)
    (hU : ∀ u : U, Polynomial.aeval M q (u : V) = 0)
    (hW : ∀ w : W, M (w : V) = 0) :
    U.projection W hUW ∈ S := by
  rw [← projectorPolynomial_aeval_eq_projection M U W hUW q hq hU hW]
  exact aeval_mem_of_coeff_zero S M hM hmul
    (projectorPolynomial q) (projectorPolynomial_coeff_zero q hq)

end CycleQ2SupportedProjectorAlgebra

namespace CycleQ2GeometricBridgeAlgebra

open CycleQ2FermatJacobian
open CycleQ2SupportedProjectorAlgebra

/-- An explicit polynomial in an actual Fermat-component endomorphism.
The minimal polynomial is supplied by Mathlib's algebraic definition; its
annihilation and the nonzero constant term are established below. -/
def actualProjectorPolynomial (M : Module.End ℂ InvariantHodgeModel) :
    Polynomial ℂ :=
  projectorPolynomial (minpoly ℂ M)

theorem actualProjectorPolynomial_coeff_zero
    (M : Module.End ℂ InvariantHodgeModel) (hM : Function.Injective M) :
    (actualProjectorPolynomial M).coeff 0 = 0 := by
  letI : Module.Free ℂ InvariantHodgeModel :=
    Module.Free.of_basis degreeSixCharacterOneBasis
  letI : Module.Finite ℂ InvariantHodgeModel :=
    Module.Finite.of_basis degreeSixCharacterOneBasis
  apply projectorPolynomial_coeff_zero
  exact LinearMap.minpoly_coeff_zero_of_injective hM

theorem actualProjectorPolynomial_aeval
    (M : Module.End ℂ InvariantHodgeModel) :
    Polynomial.aeval M (actualProjectorPolynomial M) = 1 := by
  exact projectorPolynomial_aeval M (minpoly ℂ M) (minpoly.aeval ℂ M)

/-- Injectivity on the actual 33-dimensional quotient component supplies an
identity polynomial with no constant term. This is the finite-dimensional
algebra needed to keep the projector inside a divisor-supported span. -/
theorem actual_zero_constant_polynomial_identity
    (M : Module.End ℂ InvariantHodgeModel) (hM : Function.Injective M) :
    ∃ p : Polynomial ℂ, p.coeff 0 = 0 ∧ Polynomial.aeval M p = 1 :=
  ⟨actualProjectorPolynomial M, actualProjectorPolynomial_coeff_zero M hM,
    actualProjectorPolynomial_aeval M⟩

/-- The actual identity is in every composition-stable submodule of
endomorphisms containing an injective operator. Establishing the geometric
support interpretation of such a submodule remains a separate theorem. -/
theorem actual_identity_mem_of_composition_stable
    (S : Submodule ℂ (Module.End ℂ InvariantHodgeModel))
    (M : Module.End ℂ InvariantHodgeModel) (hM : M ∈ S)
    (hmul : ∀ N ∈ S, N * M ∈ S)
    (hInjective : Function.Injective M) :
    (1 : Module.End ℂ InvariantHodgeModel) ∈ S := by
  obtain ⟨p, hp, hEval⟩ := actual_zero_constant_polynomial_identity M hInjective
  rw [← hEval]
  exact aeval_mem_of_coeff_zero S M hM hmul p hp

end CycleQ2GeometricBridgeAlgebra

end

end Q2UncompiledProjectorConstruction
