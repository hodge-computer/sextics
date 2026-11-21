import Proposal.GeometricLiteralCanonicalDegreeProjection
import Proposal.GeometricLiteralCanonicalCoefficientRange

/-!
# Homogeneous cubic fractions in a canonical frame

After clearing three additional powers of the coordinate denominator,
every weight-three fraction factors as the cube of a chart coordinate
times a genuine degree-zero fraction.

Prepared for fqlx with OpenAI ChatGPT assistance; see solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralCanonicalDegreeProjection

open CategoryTheory Opposite CycleQ2CanonicalCoordinateCoefficients CycleQ2SurfaceCoordinateCubicFrames
open CycleQ2CartierSurfaceGrading CycleQ2GeometricSeedNormalIdeals
  CycleQ2GeometricSurfaceCoordinates CycleQ2ProjectiveCoordinateCohomology
  CycleQ2ProjectiveCoordinateH2 CycleQ2GradedLocalizationProjection

theorem coordinateFraction_eq_cube_mul (s : Finset (Fin 3)) (i : Fin 3) (hi : i ∈ s)
    (n : ℕ) (a : SurfaceRing 57 1) (ha : a ∈ surfaceGrade 57 1 (3 + n * s.card)) :
    ∃ q : HomogeneousCoordinateLocal 57 1 s,
      fraction (coordinateProduct 57 1 s) n a =
        algebraMap (SurfaceRing 57 1) (CoordinateLocal 57 1 s) ((coordinateElement 57 1 i)^3) *
          q.val := by
  let g := coordinateProduct 57 1 (s.erase i)
  let f := coordinateProduct 57 1 s
  let x := coordinateElement 57 1 i
  have hf : f = x * g :=
    (Finset.mul_prod_erase s (coordinateElement 57 1) hi).symm
  have hg : g ^ 3 ∈ surfaceGrade 57 1 (3 * (s.erase i).card) := by
    simpa [g, nsmul_eq_mul] using SetLike.pow_mem_graded 3 (coordinateProduct_mem_grade 57 1 (s.erase i))
  have hcard : (s.erase i).card + 1 = s.card := Finset.card_erase_add_one hi
  have hd : 3 + n * s.card + 3 * (s.erase i).card = (n + 3) * s.card := by
    rw [Nat.add_mul]
    omega
  let q := HomogeneousLocalization.Away.mk (surfaceGrade 57 1) (coordinateProduct_mem_grade 57 1 s)
    (n + 3) (a * g^3) (hd ▸ SetLike.mul_mem_graded ha hg)
  refine ⟨q, ?_⟩
  dsimp only [q]
  rw [HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk',
    IsLocalization.mul_mk'_eq_mk'_of_mul]
  apply IsLocalization.eq.mpr
  refine ⟨1, ?_⟩
  change (1 : SurfaceRing 57 1) * (f ^ (n + 3) * a) = 1 * (f^n * (x^3 * (a * g^3)))
  rw [pow_add, hf]
  ring

/-- Every projected cubic coefficient is the coefficient of an actual canonical section. -/
theorem degreeThree_mem_range (s : Finset (Fin 3)) (hs : s.Nonempty) (p : CoordinateLocal 57 1 s) :
    degreeThree s hs p ∈ (canonicalCoefficientOn s hs).range := by
  obtain ⟨n, b, rfl⟩ := exists_fraction (coordinateProduct 57 1 s) p
  unfold degreeThree
  rw [degreePlus_fraction]
  let a := GradedRing.proj (surfaceGrade 57 1) (3 + n * s.card) b
  have ha : a ∈ surfaceGrade 57 1 (3 + n * s.card) :=
    (DirectSum.decompose (surfaceGrade 57 1) b (3 + n * s.card)).property
  let i := hs.choose
  have hi : i ∈ s := hs.choose_spec
  obtain ⟨q, hq⟩ := coordinateFraction_eq_cube_mul s i hi n a ha
  obtain ⟨ω, hω⟩ := CycleQ2LiteralCanonicalCoefficientRange.exists_canonicalCoefficientOn_eq
    s hs i hi ((orientation i : HomogeneousCoordinateLocal 57 1 s) * q)
  refine ⟨ω, hω.trans ?_⟩
  change _ = fraction (coordinateProduct 57 1 s) n a
  rw [hq, HomogeneousLocalization.val_mul, HomogeneousLocalization.val_intCast]
  calc
    _ = ((orientation i : CoordinateLocal 57 1 s) * (orientation i : CoordinateLocal 57 1 s)) *
          (algebraMap (SurfaceRing 57 1) (CoordinateLocal 57 1 s) ((coordinateElement 57 1 i)^3) * q.val) := by
      ring
    _ = _ := by rw [orientation_local_mul_self, one_mul]

end CycleQ2LiteralCanonicalDegreeProjection

end

#print axioms CycleQ2LiteralCanonicalDegreeProjection.coordinateFraction_eq_cube_mul
#print axioms CycleQ2LiteralCanonicalDegreeProjection.degreeThree_mem_range
