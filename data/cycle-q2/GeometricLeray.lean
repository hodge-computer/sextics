import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# The algebra of the affine-curve Leray step

Source-only continuation of the written nonconstructive proof, Parts III.5
and IV.4. This module has not been elaborated or compiled.

The written proof uses a first Leray piece, a vanishing next piece, and a
correspondence acting as the identity on the associated quotient. The first
section proves that this gives identity on the actual class. The second
constructs the decomposition into a normalized hyperplane contribution and
the edge-map kernel, including preservation of an invariant submodule.
The last section combines those constructions with a restriction map.

These are statements about explicitly supplied modules and linear maps.
They do not define the geometric Leray filtration, construct a relative
algebraic correspondence, or identify a Betti class with the protected
residue form. Those geometric realizations must still be supplied before
these lemmas can be applied to `cycle-q2`.
-/

set_option autoImplicit false

namespace CycleQ2GeometricLeray

variable {R H W : Type*} [CommRing R]
variable [AddCommGroup H] [Module R H]
variable [AddCommGroup W] [Module R W]

section Filtration

/-- Equality in a quotient by the zero next filtration piece is equality
in the original module. In particular, an error term cannot remain in
that piece. -/
theorem eq_of_quotient_eq_of_next_eq_bot
    (next : Submodule R H) (hnext : next = ⊥)
    {x y : H} (hxy : next.mkQ x = next.mkQ y) : x = y := by
  have hmem : x - y ∈ next := (Submodule.Quotient.eq next).mp hxy
  have hzero : x - y = 0 := by
    simpa only [hnext, Submodule.mem_bot] using hmem
  exact sub_eq_zero.mp hzero

/-- The quotient action of a correspondence determines its action on the
first filtration piece when the next piece vanishes. No idempotence or
choice of a splitting is needed for this implication. -/
theorem fixes_first_of_graded_identity
    (first next : Submodule R H) (hnext : next = ⊥)
    (P : Module.End R H)
    (hgraded : ∀ x ∈ first, next.mkQ (P x) = next.mkQ x)
    {x : H} (hx : x ∈ first) : P x = x :=
  eq_of_quotient_eq_of_next_eq_bot next hnext (hgraded x hx)

/-- If the restriction map kills the image of a correspondence, every
class fixed by that correspondence has zero restriction. -/
theorem restriction_eq_zero_of_fixed
    (restriction : H →ₗ[R] W) (P : Module.End R H)
    (hsupport : restriction.comp P = 0)
    {x : H} (hfix : P x = x) : restriction x = 0 := by
  have hzero : restriction (P x) = 0 := by
    have h := congrArg (fun f : H →ₗ[R] W => f x) hsupport
    simpa only [LinearMap.comp_apply, LinearMap.zero_apply] using h
  simpa only [hfix] using hzero

/-- The actual first-piece class, rather than only its graded image,
vanishes after restriction when a supported correspondence is the
identity on the quotient and the next piece is zero. -/
theorem restriction_eq_zero_of_graded_identity
    (first next : Submodule R H) (hnext : next = ⊥)
    (restriction : H →ₗ[R] W) (P : Module.End R H)
    (hgraded : ∀ x ∈ first, next.mkQ (P x) = next.mkQ x)
    (hsupport : restriction.comp P = 0)
    {x : H} (hx : x ∈ first) : restriction x = 0 :=
  restriction_eq_zero_of_fixed restriction P hsupport
    (fixes_first_of_graded_identity first next hnext P hgraded hx)

end Filtration

section EdgeSplitting

/-- Remove the coefficient of a chosen lift of the scalar edge term.
When `edge h = 1`, this is the canonical projection onto `ker edge`. -/
def edgeRemainder (edge : H →ₗ[R] R) (h : H) : H →ₗ[R] H :=
  LinearMap.id - edge.smulRight h

@[simp] theorem edgeRemainder_apply (edge : H →ₗ[R] R) (h x : H) :
    edgeRemainder edge h x = x - edge x • h := rfl

/-- The remainder is in the edge kernel; its construction does not ask
for a pre-existing decomposition of the source class. -/
theorem edge_edgeRemainder
    (edge : H →ₗ[R] R) (h : H) (hh : edge h = 1) (x : H) :
    edge (edgeRemainder edge h x) = 0 := by
  rw [edgeRemainder_apply, map_sub, map_smul, hh]
  simp only [smul_eq_mul, mul_one, sub_self]

theorem edgeRemainder_mem_ker
    (edge : H →ₗ[R] R) (h : H) (hh : edge h = 1) (x : H) :
    edgeRemainder edge h x ∈ LinearMap.ker edge :=
  edge_edgeRemainder edge h hh x

/-- Subtracting an invariant lift preserves membership in the specified
invariant submodule. No action or invariance is being assumed implicitly. -/
theorem edgeRemainder_mem
    (edge : H →ₗ[R] R) (h : H) (invariants : Submodule R H)
    (hh : h ∈ invariants) {x : H} (hx : x ∈ invariants) :
    edgeRemainder edge h x ∈ invariants := by
  change x - edge x • h ∈ invariants
  exact invariants.sub_mem hx (invariants.smul_mem (edge x) hh)

/-- The source is the sum of its scalar edge contribution and its
constructed edge-kernel remainder. -/
theorem edge_decomposition (edge : H →ₗ[R] R) (h x : H) :
    x = edge x • h + edgeRemainder edge h x := by
  symm
  rw [add_comm, edgeRemainder_apply, sub_add_cancel]

theorem edgeRemainder_eq_self_of_edge_eq_zero
    (edge : H →ₗ[R] R) (h : H) {x : H} (hx : edge x = 0) :
    edgeRemainder edge h x = x := by
  rw [edgeRemainder_apply, hx, zero_smul, sub_zero]

/-- The constructed map is a projection, not merely a choice of a
representative for one source class. -/
theorem edgeRemainder_idempotent
    (edge : H →ₗ[R] R) (h : H) (hh : edge h = 1) :
    (edgeRemainder edge h).comp (edgeRemainder edge h) =
      edgeRemainder edge h := by
  apply LinearMap.ext
  intro x
  exact edgeRemainder_eq_self_of_edge_eq_zero edge h
    (edge_edgeRemainder edge h hh x)

theorem range_edgeRemainder
    (edge : H →ₗ[R] R) (h : H) (hh : edge h = 1) :
    LinearMap.range (edgeRemainder edge h) = LinearMap.ker edge := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact edgeRemainder_mem_ker edge h hh y
  · intro hx
    exact ⟨x, edgeRemainder_eq_self_of_edge_eq_zero edge h hx⟩

end EdgeSplitting

section WholeClass

/-- The entire invariant class has zero restriction. Its hyperplane
component is killed directly, while the constructed first-piece remainder
is fixed by the supported correspondence because the next piece vanishes.

In the geometric application, `edge` is the coefficient of the fibrewise
degree-four hyperplane class, `invariants` is the finite-group invariant
subspace, and `next` is the second Leray piece. This theorem proves the
linear argument once those actual objects and the displayed hypotheses
have been established; it does not supply the geometric constructions. -/
theorem invariant_class_restriction_eq_zero
    (edge : H →ₗ[R] R) (h : H) (hedge : edge h = 1)
    (invariants next : Submodule R H)
    (hh : h ∈ invariants) (hnext : next = ⊥)
    (restriction : H →ₗ[R] W) (P : Module.End R H)
    (hgraded : ∀ x ∈ invariants ⊓ LinearMap.ker edge,
      next.mkQ (P x) = next.mkQ x)
    (hsupport : restriction.comp P = 0)
    (hhyperplane : restriction h = 0)
    {x : H} (hx : x ∈ invariants) : restriction x = 0 := by
  have hfirst : edgeRemainder edge h x ∈
      invariants ⊓ LinearMap.ker edge :=
    ⟨edgeRemainder_mem edge h invariants hh hx,
      edgeRemainder_mem_ker edge h hedge x⟩
  have hzero : restriction (edgeRemainder edge h x) = 0 :=
    restriction_eq_zero_of_graded_identity
      (invariants ⊓ LinearMap.ker edge) next hnext restriction P
      hgraded hsupport hfirst
  calc
    restriction x =
        restriction (edge x • h + edgeRemainder edge h x) :=
      congrArg restriction (edge_decomposition edge h x)
    _ = edge x • restriction h + restriction (edgeRemainder edge h x) := by
      rw [map_add, map_smul]
    _ = 0 := by rw [hhyperplane, hzero, smul_zero, add_zero]

/-- Invariance descends along an injective equivariant pullback. This is
the linear step used after the finite quotient cohomology comparison;
neither the existence nor injectivity of that comparison is asserted here. -/
theorem invariant_of_injective_pullback
    (pullback : H →ₗ[R] W) (hinj : Function.Injective pullback)
    (T : Module.End R H) (S : Module.End R W)
    (hequiv : pullback.comp T = S.comp pullback)
    {x : H} (hfixed : S (pullback x) = pullback x) : T x = x := by
  apply hinj
  calc
    pullback (T x) = S (pullback x) :=
      congrArg (fun f : H →ₗ[R] W => f x) hequiv
    _ = pullback x := hfixed

end WholeClass

end CycleQ2GeometricLeray
