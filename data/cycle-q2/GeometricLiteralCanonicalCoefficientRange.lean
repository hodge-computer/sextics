import Proposal.GeometricCanonicalCoordinateCoefficients

/-!
# Recovering actual canonical sections from their coordinate coefficients

On each nonempty coordinate intersection of the literal surface, the local
frame identifies canonical two-forms with scalar sections. The signed
coordinate cube is a unit on that intersection. Hence the coefficient
determines the form, and every signed cube times a degree-zero homogeneous
fraction comes from a form.

Prepared for fqlx with OpenAI ChatGPT assistance; see solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralCanonicalCoefficientRange

open Opposite AlgebraicGeometry
open CycleQ2GeometricSurfaceCoordinates CycleQ2GeometricCartierNormalLift
  CycleQ2GeometricSeedNormalIdeals CycleQ2ProjectiveCoordinateCohomology
  CycleQ2ProjectiveCoordinateH2 CycleQ2SurfaceSectionCoefficients
  CycleQ2SurfaceCoordinateFrames CycleQ2SurfaceCoordinateCubicFrames
  CycleQ2CanonicalCoordinateCoefficients

/-- The coordinate cube, the local frame, and the homogeneous inclusion
are all cancellable on this intersection. -/
theorem canonicalCoefficientOn_injective (s : Finset (Fin 3)) (hs : s.Nonempty) :
    Function.Injective (canonicalCoefficientOn s hs) := by
  let i := hs.choose
  have hi : i ∈ s := hs.choose_spec
  let e := (coordinateExteriorFrame i).app (coordinateIntersection 57 1 s)
    (intersection_le_chart 57 1 i hi)
  let k := (orientation i : CoordinateLocal 57 1 s) *
    algebraMap (SurfaceRing 57 1) (CoordinateLocal 57 1 s) ((coordinateElement 57 1 i)^3)
  have ho : IsUnit (orientation i : CoordinateLocal 57 1 s) :=
    isUnit_iff_exists_inv.mpr ⟨_, orientation_local_mul_self s i⟩
  have hk : IsUnit k := by
    dsimp only [k]
    rw [map_pow]
    exact ho.mul ((coordinateElement_isUnit 57 1 i hi).pow 3)
  intro ω η h
  change k * sectionCoefficient 57 1 s hs (e ω) = k * sectionCoefficient 57 1 s hs (e η) at h
  apply e.injective
  apply (coordinateSections 57 1 s hs).symm.injective
  apply HomogeneousLocalization.val_injective
  exact hk.mul_left_cancel h

theorem canonicalCoefficientAt_injective (s : Finset (Fin 3)) (hs : s.Nonempty)
    (O : CycleQ2CanonicalCoordinateCoefficients.Surface.Opens)
    (hO : O = coordinateIntersection 57 1 s) :
    Function.Injective (canonicalCoefficientAt s hs O hO) := by
  subst O
  exact canonicalCoefficientOn_injective s hs

/-- Apply the inverse chart frame to the actual scalar section of the
specified homogeneous fraction. -/
theorem exists_canonicalCoefficientOn_eq (s : Finset (Fin 3)) (hs : s.Nonempty)
    (i : Fin 3) (hi : i ∈ s) (q : HomogeneousCoordinateLocal 57 1 s) :
    ∃ ω, canonicalCoefficientOn s hs ω =
      (orientation i : CoordinateLocal 57 1 s) *
      algebraMap (SurfaceRing 57 1) (CoordinateLocal 57 1 s) ((coordinateElement 57 1 i)^3) *
      q.val := by
  let e := (coordinateExteriorFrame i).app (coordinateIntersection 57 1 s)
    (intersection_le_chart 57 1 i hi)
  refine ⟨e.symm (coordinateSections 57 1 s hs q), ?_⟩
  rw [canonicalCoefficientOn_eq s hs i hi]
  change _ * _ * sectionCoefficient 57 1 s hs (e (e.symm (coordinateSections 57 1 s hs q))) = _
  rw [LinearEquiv.apply_symm_apply, sectionCoefficient_sections]

end CycleQ2LiteralCanonicalCoefficientRange

end

#print axioms CycleQ2LiteralCanonicalCoefficientRange.canonicalCoefficientAt_injective
#print axioms CycleQ2LiteralCanonicalCoefficientRange.exists_canonicalCoefficientOn_eq
