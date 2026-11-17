import Proposal.GeometricIncidenceFirstOrderCanonicalH2
import Proposal.GeometricCanonicalResidueNonzero
import Proposal.GeometricCartierOrbitCompatibility

/-!
# Trace of the cyclic action on the retained cubic pairing

On the coordinate triple overlap, the inverse-character sum of the three
actual localized substitutions is three times the character-one component.
The incidence cubic has character zero. The coefficient defining the
canonical trace has character one. These facts determine the scalar on
the genuine canonical triple sections arising from the cubic map.

Prepared for fqlx with OpenAI ChatGPT assistance; see solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace CycleQ2LiteralOrbitTrace

open MvPolynomial CycleQ2GeometricCoordinateCharacter CycleQ2GeometricSurfaceCoordinates
  CycleQ2GeometricLaurentTop CycleQ2GeometricHomogeneousWeight
  CycleQ2OrbitTraceBridge CycleQ2SeedCyclicAction CycleQ2CoordinateCechTrace
  CycleQ2GeometricCartierNormalLift CycleQ2GeometricSeedNormalIdeals
  CycleQ2IncidenceNormalForm CycleQ2IncidenceFirstOrderTrace
  CycleQ2IncidenceFirstOrderCanonicalH2 CycleQ2CanonicalCoordinateH2
  CycleQ2CanonicalCoordinateCoefficients CycleQ2CanonicalResidueNonzero

private theorem twistedProject (ζ : ℂ) (hζ : ζ ^ 3 = 1)
    (r : ℂ) (χ : ZMod 3) (q : CoordinateLocal r 1 Finset.univ) :
    coordinateProject r Finset.univ χ (coordinateTwistedOrbit ζ hζ r q) =
      (1 + ζ ^ 2 * ζ ^ χ.val + ζ * (ζ ^ χ.val * ζ ^ χ.val)) •
        coordinateProject r Finset.univ χ q := by
  rw [coordinateProject_twistedOrbit, coordinateTwistedOrbit_eq_twistedLinear]
  simp only [twistedOrbit, coordinateLinearAction_project, map_smul,
    add_smul, one_smul, smul_smul]

/-- The equality holds for the entire localized fraction of the original
representative, before applying any trace or taking any cohomology class. -/
theorem twistedOrbit_eq_three_project (ζ : ℂ) (hζ : ζ ^ 3 = 1)
    (hprim : ζ ^ 2 + ζ + 1 = 0) (r : ℂ) (q : CoordinateLocal r 1 Finset.univ) :
    coordinateTwistedOrbit ζ hζ r q = (3 : ℕ) • coordinateProject r Finset.univ 1 q := by
  conv_lhs => rw [← coordinateProject_total r Finset.univ (coordinateTwistedOrbit ζ hζ r q)]
  change (∑ χ : Fin 3, coordinateProject r Finset.univ χ (coordinateTwistedOrbit ζ hζ r q)) = _
  rw [Fin.sum_univ_three]
  change coordinateProject r Finset.univ 0 (coordinateTwistedOrbit ζ hζ r q) +
    coordinateProject r Finset.univ 1 (coordinateTwistedOrbit ζ hζ r q) +
    coordinateProject r Finset.univ 2 (coordinateTwistedOrbit ζ hζ r q) = _
  rw [twistedProject ζ hζ r 0 q,
    coordinateProject_one_twistedOrbit ζ hζ r q, twistedProject ζ hζ r 2 q]
  have h0 : (1 : ℂ) + ζ ^ 2 * ζ ^ (0 : ZMod 3).val +
      ζ * (ζ ^ (0 : ZMod 3).val * ζ ^ (0 : ZMod 3).val) = 0 := by
    change 1 + ζ ^ 2 * ζ ^ 0 + ζ * (ζ ^ 0 * ζ ^ 0) = 0
    linear_combination hprim
  have h2 : (1 : ℂ) + ζ ^ 2 * ζ ^ (2 : ZMod 3).val +
      ζ * (ζ ^ (2 : ZMod 3).val * ζ ^ (2 : ZMod 3).val) = 0 := by
    change 1 + ζ ^ 2 * ζ ^ 2 + ζ * (ζ ^ 2 * ζ ^ 2) = 0
    linear_combination hprim + (ζ + ζ ^ 2) * hζ
  simp only [h0, h2, zero_smul, zero_add, add_zero]

theorem firstOrderCubic_character :
    firstOrderWeightedCubic.val.IsWeightedHomogeneous characterWeight 0 := by
  intro e he
  have h := fullInvariantPolynomial_homogeneous 3
    (fun j => firstOrderDirection (Sum.inl j)) he
  rw [fullGrading_weight] at h
  rw [← characterExponent_cast]
  exact congrArg Prod.snd h

private theorem fixedCoefficient_project (r : ℂ) (q : CoordinateLocal r 1 Finset.univ) :
    localCoefficient r Finset.univ (2,2) (fun _ => -1) (coordinateProject r Finset.univ 1 q) =
    localCoefficient r Finset.univ (2,2) (fun _ => -1) q := by
  change (coordinateLaurent r _ (coordinateProject r _ 1 q) _).coeff _ = _
  rw [coordinateProject_coordinates, characterPart_coeff, if_pos (by decide)]
  rfl

private theorem project_cubic (q : CoordinateLocal 57 1 Finset.univ) :
    coordinateProject 57 Finset.univ 1 (surfaceQuotient 57 1 firstOrderWeightedCubic.val • q) =
      surfaceQuotient 57 1 firstOrderWeightedCubic.val • coordinateProject 57 Finset.univ 1 q := by
  have hsmul (u : CoordinateLocal 57 1 Finset.univ) :
      surfaceQuotient 57 1 firstOrderWeightedCubic.val • u =
        algebraMap (SurfaceRing 57 1) (CoordinateLocal 57 1 Finset.univ)
          (quotientMap 57 1 firstOrderWeightedCubic.val) * u :=
    Algebra.smul_def (surfaceQuotient 57 1 firstOrderWeightedCubic.val) u
  rw [hsmul q, hsmul (coordinateProject 57 Finset.univ 1 q)]
  exact coordinateProject_mul_invariant 57 q firstOrderWeightedCubic.val 1 firstOrderCubic_character

/-- The squared normal character from the deformation cancels the
character of the trace coordinate, already before multiplying the
projected section by the incidence cubic. -/
theorem project_normalAction (z : ℂ) (hz : z^3 = 1)
    (q : CoordinateLocal 57 1 Finset.univ) :
    coordinateProject 57 Finset.univ 1 (z^2 • coordinateLinearAction z hz 57 q) =
      coordinateProject 57 Finset.univ 1 q := by
  rw [coordinateProject_complex_smul, coordinateProject_action_eigen, smul_smul]
  change (z ^ 2 * z ^ 1) • _ = _
  rw [pow_one, ← pow_succ, hz, one_smul]

theorem normalAction_cubic_trace (z : ℂ) (hz : z^3 = 1)
    (q t : HomogeneousCoordinateTop 57)
    (ht : t.val = z^2 • coordinateLinearAction z hz 57 q.val) :
    canonicalSectionTrace (cubicTripleSection firstOrderWeightedCubic t) =
      canonicalSectionTrace (cubicTripleSection firstOrderWeightedCubic q) := by
  let L := localCoefficient 57 Finset.univ (2,2) (fun _ => -1)
  let p := surfaceQuotient 57 1 firstOrderWeightedCubic.val
  change L (canonicalCoefficient _) = L (canonicalCoefficient _)
  rw [canonicalCoefficient_cubicTripleSection, canonicalCoefficient_cubicTripleSection]
  calc
    L (p • t.val) = L (coordinateProject 57 Finset.univ 1 (p • t.val)) :=
      (fixedCoefficient_project 57 _).symm
    _ = L (coordinateProject 57 Finset.univ 1 (p • q.val)) := by
      dsimp only [p]
      rw [project_cubic, project_cubic, ht, project_normalAction]
    _ = L (p • q.val) := fixedCoefficient_project 57 _

/-- A genuine homogeneous triple section representing the full twisted orbit. -/
def orbitSection (q : HomogeneousCoordinateTop 57) : HomogeneousCoordinateTop 57 :=
  (3 : ℕ) • homogeneousProject 57 1 q

theorem orbitSection_val (ζ : ℂ) (hζ : ζ ^ 3 = 1)
    (hprim : ζ ^ 2 + ζ + 1 = 0) (q : HomogeneousCoordinateTop 57) :
    (orbitSection q).val = coordinateTwistedOrbit ζ hζ 57 q.val := by
  rw [orbitSection, HomogeneousLocalization.val_nsmul, homogeneousProject_val,
    twistedOrbit_eq_three_project ζ hζ hprim]

/-- The fixed canonical trace on triple sections determines the factor
three for the original, unprojected cubic pairing. -/
theorem orbitSection_cubic_trace (q : HomogeneousCoordinateTop 57) :
    canonicalSectionTrace (cubicTripleSection firstOrderWeightedCubic (orbitSection q)) =
      (3 : ℕ) • canonicalSectionTrace (cubicTripleSection firstOrderWeightedCubic q) := by
  change localCoefficient 57 Finset.univ (2,2) (fun _ => -1)
    (canonicalCoefficient (cubicTripleSection firstOrderWeightedCubic (orbitSection q))) =
    (3 : ℕ) • localCoefficient 57 Finset.univ (2,2) (fun _ => -1)
      (canonicalCoefficient (cubicTripleSection firstOrderWeightedCubic q))
  rw [canonicalCoefficient_cubicTripleSection, canonicalCoefficient_cubicTripleSection,
    orbitSection, HomogeneousLocalization.val_nsmul, homogeneousProject_val]
  have hlinearity (a : SurfaceRing 57 1) (b : CoordinateLocal 57 1 Finset.univ) :
      a • ((3 : ℕ) • b) = (3 : ℕ) • (a • b) := by
    simp only [three_nsmul, Algebra.smul_def a, mul_add]
  rw [hlinearity, map_nsmul, ← project_cubic, fixedCoefficient_project]

end CycleQ2LiteralOrbitTrace
end

#print axioms CycleQ2LiteralOrbitTrace.orbitSection_val
#print axioms CycleQ2LiteralOrbitTrace.orbitSection_cubic_trace
