import Proposal.GeometricProjectiveCech
import Proposal.GeometricCechTrace

/-!
# A concrete nonzero derived class on the sparse projective curve

At theta zero and r cubed equal to two, the normalized numerator
`x0*x1^8` gives a nonzero class in the derived first cohomology of the
actual degree-one additive sheaf. The proof uses the actual Cech quotient,
its checked trace coordinate, and the Mayer-Vietoris injection. It does
not use the separate incidence example at r = 57 and theta = 1.

The target is the constructed degree-one sheaf. Its identification with
the canonical differential sheaf, and geometric Serre duality, remain
separate statements.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2GeometricProjectiveNonzero

open MvPolynomial CycleQ2SeedTrace CycleQ2GeometricProjectiveCurve
  CycleQ2GeometricCechPoleReduction CycleQ2GeometricCechTrace

private theorem root_ne_zero (r : ℂ) (hr : r ^ 3 = 2) : r ≠ 0 := by
  intro hz
  simp [hz] at hr

/-- The actual image of a homogeneous degree-nine numerator in derived
cohomology on the projective curve. -/
def degreeNineProjectiveClass (r : ℂ) (hr : r ^ 3 = 2)
    (p : Poly) (hp : p.IsHomogeneous 9) : ProjectiveSheafH1 r 0 :=
  degreeOneToProjectiveH1 r 0 (root_ne_zero r hr) (degreeNineCechClass r 0 p hp)

/-- The computed trace detects zero for these genuine derived classes. -/
theorem degreeNineProjectiveClass_eq_zero_iff_trace_zero
    (r : ℂ) (hr : r ^ 3 = 2) (p : Poly) (hp : p.IsHomogeneous 9) :
    degreeNineProjectiveClass r hr p hp = 0 ↔ traceLinear r p = 0 := by
  have hc : degreeNineProjectiveClass r hr p hp = 0 ↔
      degreeNineCechClass r 0 p hp = 0 := by
    constructor
    · intro hz
      apply degreeOneToProjectiveH1_injective r 0 (root_ne_zero r hr)
      simpa only [degreeNineProjectiveClass, map_zero] using hz
    · intro hz
      simp only [degreeNineProjectiveClass, hz, map_zero]
  exact hc.trans (degreeNineCechClass_eq_zero_iff_trace_zero r hr p hp)

/-- Complex multiples of the fixed normalization numerator, mapped to
the actual derived cohomology group. -/
def normalizedProjectiveClass (r : ℂ) (hr : r ^ 3 = 2) (c : ℂ) :
    ProjectiveSheafH1 r 0 :=
  degreeOneToProjectiveH1 r 0 (root_ne_zero r hr) (normalizedCechClass r c)

theorem normalizedProjectiveClass_injective (r : ℂ) (hr : r ^ 3 = 2) :
    Function.Injective (normalizedProjectiveClass r hr) :=
  (degreeOneToProjectiveH1_injective r 0 (root_ne_zero r hr)).comp
    (normalizedCechClass_injective r hr)

@[simp] theorem normalizedProjectiveClass_zero (r : ℂ) (hr : r ^ 3 = 2) :
    normalizedProjectiveClass r hr 0 = 0 := by
  have hz : normalizedCechClass r 0 = 0 := by
    apply (degreeNineCechClass_eq_zero_iff_trace_zero r hr _ _).mpr
    simp only [map_zero, zero_mul]
  simp only [normalizedProjectiveClass, hz, map_zero]

theorem normalizedProjectiveClass_eq_zero_iff (r : ℂ) (hr : r ^ 3 = 2) (c : ℂ) :
    normalizedProjectiveClass r hr c = 0 ↔ c = 0 := by
  constructor
  · intro hz
    apply normalizedProjectiveClass_injective r hr
    simpa only [normalizedProjectiveClass_zero] using hz
  · rintro rfl
    exact normalizedProjectiveClass_zero r hr

/-- The normalized class is nonzero in actual derived projective
cohomology for every cube root of two, with theta exactly zero. -/
theorem normalizationProjectiveClass_ne_zero (r : ℂ) (hr : r ^ 3 = 2) :
    normalizedProjectiveClass r hr 1 ≠ 0 := by
  intro hz
  exact one_ne_zero ((normalizedProjectiveClass_eq_zero_iff r hr 1).mp hz)

theorem projectiveSheafH1_nontrivial (r : ℂ) (hr : r ^ 3 = 2) :
    Nontrivial (ProjectiveSheafH1 r 0) :=
  ⟨⟨normalizedProjectiveClass r hr 1, 0, normalizationProjectiveClass_ne_zero r hr⟩⟩

end CycleQ2GeometricProjectiveNonzero

end
