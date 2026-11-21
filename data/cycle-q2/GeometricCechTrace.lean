import Proposal.GeometricCechSurjectivity
import Proposal.GeometricCurveRegularPair

/-!
# The normalized trace coordinate on the entire actual Cech quotient

The actual quartic regular-pair theorem gives the converse to the
homogeneous boundary construction. Together with arbitrary-pole reduction,
this makes the fixed normalization numerator a bijective complex scalar
coordinate on the existing degree-one Cech quotient. These are actual
localization classes; no Serre-duality identification is assumed here.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace CycleQ2GeometricCechTrace

open MvPolynomial CycleQ2SeedTrace CycleQ2SeedCechTheta CycleQ2NormalConnecting
  CycleQ2GeometricProjectiveCurve CycleQ2GeometricKoszulTrace
  CycleQ2GeometricCechPoleReduction

/-- The finite normalized trace detects exactly the zero class in the
actual homogeneous quotient, including arbitrary-pole chart boundaries. -/
theorem degreeNineCechClass_eq_zero_iff_trace_zero
    (r : ℂ) (hr : r ^ 3 = 2) (p : Poly) (hp : p.IsHomogeneous 9) :
    degreeNineCechClass r 0 p hp = 0 ↔ traceLinear r p = 0 := by
  have hr0 : r ≠ 0 := by intro h; simp [h] at hr
  constructor
  · intro hz
    have hmem := (degreeNineCechClass_eq_zero_iff_reducedIdeal r hr0
      (CycleQ2GeometricCurveRegularPair.curveG1_regular r hr0)
      (CycleQ2GeometricCurveRegularPair.curveG2_regular_mod_curveG1 r hr0) p hp).mp hz
    exact traceLinear_zero_of_mem r hr hmem
  · exact CycleQ2GeometricTraceBoundary.degreeNineCechClass_zero_of_trace_zero r hr p hp

/-- Two homogeneous numerator representatives give the same actual
Cech class exactly when their computed traces agree. -/
theorem degreeNineCechClass_eq_iff_trace_eq
    (r : ℂ) (hr : r ^ 3 = 2) (p q : Poly)
    (hp : p.IsHomogeneous 9) (hq : q.IsHomogeneous 9) :
    degreeNineCechClass r 0 p hp = degreeNineCechClass r 0 q hq ↔
      traceLinear r p = traceLinear r q := by
  calc
    degreeNineCechClass r 0 p hp = degreeNineCechClass r 0 q hq ↔
        degreeNineCechClass r 0 (p - q) (hp.sub hq) = 0 := by
      rw [degreeNineCechClass_sub, sub_eq_zero]
    _ ↔ traceLinear r (p - q) = 0 :=
      degreeNineCechClass_eq_zero_iff_trace_zero r hr (p - q) (hp.sub hq)
    _ ↔ traceLinear r p = traceLinear r q := by rw [map_sub, sub_eq_zero]

theorem normalizedCechClass_injective (r : ℂ) (hr : r ^ 3 = 2) :
    Function.Injective (normalizedCechClass r) := by
  intro c d hcd
  have hp : (C c * mon 1 8 0 0).IsHomogeneous 9 :=
    (mon_homogeneous 1 8 0 0).C_mul c
  have hq : (C d * mon 1 8 0 0).IsHomogeneous 9 :=
    (mon_homogeneous 1 8 0 0).C_mul d
  have heq := (degreeNineCechClass_eq_iff_trace_eq r hr _ _ hp hq).mp hcd
  have hnormal : traceLinear r (mon 1 8 0 0) = 1 := trace_normalized r hr
  simpa only [traceLinear_C_mul, hnormal, mul_one] using heq

/-- Every class has exactly one scalar normalization coordinate. -/
theorem normalizedCechClass_bijective (r : ℂ) (hr : r ^ 3 = 2) :
    Function.Bijective (normalizedCechClass r) :=
  ⟨normalizedCechClass_injective r hr, normalizedCechClass_surjective r hr⟩

theorem existsUnique_normalizedCechClass (r : ℂ) (hr : r ^ 3 = 2)
    (z : DegreeOneCech r 0) : ∃! c : ℂ, normalizedCechClass r c = z :=
  (normalizedCechClass_bijective r hr).existsUnique z

end CycleQ2GeometricCechTrace

end
