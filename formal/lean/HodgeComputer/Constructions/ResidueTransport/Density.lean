import HodgeComputer.Constructions.HoldoutCover.ResiduePiolaPullback

/-! Residue divergence under a change of normal density and coordinates.

The density factor g/h and the coordinate determinant are both retained.
Applications supply an invertible coordinate matrix, the chain rule, mixed
partial compatibility, and nonzero normal derivatives.

Extracted from hodgepodgeconjecture's cycle-three construction,
prepared with OpenAI Codex assistance. Piola transport is the shared
construction of fqlx and the Hodge Computer collaborators. Original
namespaces are retained; do not import the accepted copy alongside this
module. -/
noncomputable section
namespace CycleResidueTransport
open HoldoutConstruction
open scoped BigOperators
variable {K ι : Type*} [Field K] [Fintype ι]

theorem change_density (D : ι → Derivation ℤ K K)
    (g h : K) (hg : g ≠ 0) (hh : h ≠ 0) (w : ι → K) :
    residueDivergence D g (fun i => (g/h)*w i) =
      (g/h)*residueDivergence D h w := by
  have hw : (fun i => h*(w i/h)) = w := by
    funext i
    field_simp
  have hv : (fun i => (g/h)*w i) = (fun i => g*(w i/h)) := by
    funext i
    ring
  rw [hv,residueDivergence_cancel_density D g hg]
  conv_rhs => rw [← hw,residueDivergence_cancel_density D h hh]
  field_simp

variable [DecidableEq ι]

/-- The residue-volume multiplier is `g*det(M)/h` when the source and target
normal derivatives are respectively `g` and `h`. -/
theorem piola_pullback
    (D E : ι → Derivation ℤ K K) (M N : Matrix ι ι K)
    (hMN : M*N = 1) (hNM : N*M = 1) (hdet : M.det ≠ 0)
    (chain : ∀ j x, E j x = ∑ k, N k j*D k x)
    (mixed : ∀ i j k, D k (M j i) = D i (M j k))
    (g h : K) (hg : g ≠ 0) (hh : h ≠ 0) (w : ι → K) :
    residueDivergence D g (fun i => (g/h)*(M.det*(N.mulVec w) i)) =
      (g/h)*M.det*residueDivergence E h w := by
  rw [change_density D g h hg hh,
    residue_piola_pullback D E M N hMN hNM hdet chain mixed h w]
  ring

end CycleResidueTransport
#print axioms CycleResidueTransport.piola_pullback
