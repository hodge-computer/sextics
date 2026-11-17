import Proposal.GeometricCanonicalResidueNonzero

/-!
# Homogeneous weight of actual canonical sections

In the first chart frame a canonical section on the triple intersection
has coefficient `X₁³` times a degree-zero homogeneous fraction. Clearing
its denominator fixes the Laurent weight at three. Restriction to the
triple intersection preserves the Laurent coordinates for every subcover.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralCanonicalCoefficientWeight

open CategoryTheory Opposite AlgebraicGeometry MvPolynomial
  CycleQ2GeometricSeedNormalIdeals CycleQ2GeometricSurfaceCoordinates
  CycleQ2GeometricCartierNormalLift CycleQ2GeometricLaurentTop
  CycleQ2GeometricHomogeneousWeight CycleQ2CartierSurfaceGrading
  CycleQ2ProjectiveCoordinateCohomology CycleQ2ProjectiveCoordinateH2
  CycleQ2SurfaceSectionCoefficients CycleQ2CoordinateCechTrace
  CycleQ2CanonicalCoordinateCoefficients

private theorem coordinateCube_weight (q : HomogeneousCoordinateTop 57) :
    algebraMap (SurfaceRing 57 1) (CoordinateLocal 57 1 Finset.univ)
      ((coordinateElement 57 1 0)^3) * q.val ∈ coordinateLocalWeight 57 3 Finset.univ := by
  obtain ⟨n,p,hp,hfrac⟩ := homogeneous_coordinate_fraction 57 q
  let g := CycleQ2SurfaceCoordinateCubicFrames.coordinateCube 0
  have hg : g.val.IsWeightedHomogeneous CycleQ2GeometricCoordinateWeight.weight 3 :=
    g.property
  have hcube : (coordinateElement 57 1 0)^3 = quotientMap 57 1 g.val := by
    rw [coordinateElement_eq]
    change (quotientMap 57 1 (X 1))^3 = quotientMap 57 1 ((X 1)^3)
    rw [map_pow]
  apply (mem_coordinateLocalWeight_iff 57 3 Finset.univ _).mpr
  intro ab e he
  apply coordinate_fraction_weight 57 _ (g.val * p) n 3
    (by simpa only [Nat.add_comm] using hg.mul hp) ?_ ab e he
  rw [hcube, mul_assoc, hfrac]
  simp only [map_mul]

private theorem canonicalCoefficientOn_univ_weight
    (ω : CanonicalForms.val.obj (op (coordinateIntersection 57 1 Finset.univ))) :
    canonicalCoefficientOn Finset.univ (by simp) ω ∈
      coordinateLocalWeight 57 3 Finset.univ := by
  let u := coordinateIntersection 57 1 Finset.univ
  let h := intersection_le_chart 57 1 0 (Finset.mem_univ _)
  let a := (CycleQ2SurfaceCoordinateFrames.coordinateExteriorFrame 0).app u h ω
  let q := (coordinateSections 57 1 Finset.univ (by simp)).symm a
  rw [canonicalCoefficientOn_eq Finset.univ (by simp) 0 (Finset.mem_univ _)]
  change ((1 : ℤ) : CoordinateLocal 57 1 Finset.univ) * _ * q.val ∈ _
  simpa only [Int.cast_one,one_mul] using coordinateCube_weight q

/-- Every actual section of the canonical sheaf has Laurent weight three. -/
theorem canonicalCoefficientOn_weight (I : Finset (Fin 3)) (hI : I.Nonempty)
    (ω : CanonicalForms.val.obj (op (coordinateIntersection 57 1 I))) :
    canonicalCoefficientOn I hI ω ∈ coordinateLocalWeight 57 3 I := by
  let h := Finset.subset_univ I
  have hu := canonicalCoefficientOn_univ_weight
    (CanonicalForms.val.map (homOfLE (coordinateIntersection_mono 57 1 h)).op ω)
  rw [canonicalCoefficientOn_restrict hI (by simp) h] at hu
  intro ab e he
  have hz := hu ab e he
  rw [coordinateLaurent_restriction] at hz
  exact hz

theorem canonicalCoefficient_weight (s : CanonicalSheaf.obj.obj (op TripleOpen)) :
    canonicalCoefficient s ∈ coordinateLocalWeight 57 3 Finset.univ := by
  suffices ∀ (O : Surface.Opens) (ho : O = coordinateIntersection 57 1 Finset.univ)
    (ω : CanonicalForms.val.obj (op O)),
    canonicalCoefficientAt Finset.univ (by simp) O ho ω ∈
      coordinateLocalWeight 57 3 Finset.univ from
    this TripleOpen (coordinateIntersection_univ 57 1).symm s
  rintro O rfl ω
  exact canonicalCoefficientOn_univ_weight ω

end CycleQ2LiteralCanonicalCoefficientWeight

end

#print axioms CycleQ2LiteralCanonicalCoefficientWeight.canonicalCoefficientOn_weight
#print axioms CycleQ2LiteralCanonicalCoefficientWeight.canonicalCoefficient_weight
