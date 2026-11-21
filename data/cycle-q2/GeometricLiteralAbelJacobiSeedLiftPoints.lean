import Proposal.GeometricRelativeCurveSeedFiberCover
import Proposal.GeometricFirstOrderCurveChartFlat
import Proposal.GeometricFirstOrderCurveCharts

/-!
# Seed primes and their images in the original moving curve charts

The weight-one charts cover every point of the specialized projective curve.
On each chart its map to the moving curve contracts the seed prime along
the coefficient specialization. This contraction preserves avoidance of
polynomials, matrix pivots and Jacobian minors of the specialized equations.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralAbelJacobiSeedLiftPoints

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open CycleQ2GeometricIncidenceProj CycleQ2IncidenceUniversalChart CycleQ2IncidenceImageLine CycleQ2IncidenceEtaleParameter
  CycleQ2IncidencePolynomialJacobianBinding CycleQ2IncidenceDehomogenizedChart
  CycleQ2IncidenceChartFiberScheme CycleQ2RelativeCurveChart CycleQ2RelativeCurveChartScheme
  CycleQ2RelativeConstantCurve CycleQ2SpecializedProjectiveCurve
  CycleQ2SpecializedCurveCoordinateChart CycleQ2RelativeCurveChartFiber
  CycleQ2RelativeCurveSeedProj CycleQ2RelativeCurveSeedChart CycleQ2RelativeCurveSeedFiberCover
  CycleQ2FirstOrderCurveChartFlat CycleQ2RelativeConstantSection CycleQ2IncidenceChartSeedFiber

attribute [local instance] CycleQ2RelativeCurveChartFiber.incidenceCurveChartCommRing
  CycleQ2RelativeCurveChartFiber.seedCurveChartCommRing

private abbrev seed := seedPoint (57 : ℂ) Complex.I

variable (t : Fin 3 → ℂ) (i : Fin 4)

def seedChartToCurve :
    Spec (CommRingCat.of (AffineCurveChart seed t i)) ⟶ specializedCurve seed t :=
  (specializedCoordinateAffineChart seed t i).inv ≫ (specializedCoordinatePatch seed t i).ι

abbrev movingChartToCurve :
    Spec (CommRingCat.of (AffineCurveChart incidencePoint t i)) ⟶ relativeCurve incidencePoint t :=
  CycleQ2FirstOrderCurveCharts.originalCurveChart t i

def movingPrime (z : PrimeSpectrum (AffineCurveChart seed t i)) :
    PrimeSpectrum (AffineCurveChart incidencePoint t i) :=
  PrimeSpectrum.comap (curveChartSpecialization t i) z

theorem movingChartToCurve_movingPrime (z : PrimeSpectrum (AffineCurveChart seed t i)) :
    movingChartToCurve t i (movingPrime t i z) = seedCurveToRelative t (seedChartToCurve t i z) := by
  exact (congrArg (fun f : Spec (CommRingCat.of (AffineCurveChart seed t i)) ⟶
    relativeCurve incidencePoint t => f z) (seedCurveToRelative_on_coordinateChart t i)).symm

theorem exists_seedChart_prime (x : specializedCurve seed t) :
    ∃ (i : Fin 4) (z : PrimeSpectrum (AffineCurveChart seed t i)),
      seedChartToCurve t i z = x ∧
        movingChartToCurve t i (movingPrime t i z) = seedCurveToRelative t x := by
  have hx : seedCurveToFiber t x ∈ ⨆ j : Fin 4, fiberCoordinatePatch t j := by
    rw [iSup_fiberCoordinatePatch]
    trivial
  obtain ⟨j, hj⟩ := Opens.mem_iSup.mp hx
  have hp : x ∈ specializedCoordinatePatch seed t j := by
    rw [← seedCurveToFiber_preimage_coordinatePatch]
    exact hj
  let u : (specializedCoordinatePatch seed t j).toScheme := ⟨x, hp⟩
  let z := (specializedCoordinateAffineChart seed t j).hom u
  have hz : seedChartToCurve t j z = x := by
    change (specializedCoordinatePatch seed t j).ι
      (((specializedCoordinateAffineChart seed t j).hom ≫
        (specializedCoordinateAffineChart seed t j).inv) u) = x
    rw [Iso.hom_inv_id]
    rfl
  exact ⟨j, z, hz, (movingChartToCurve_movingPrime t j z).trans (congrArg _ hz)⟩

/-- Evaluate a polynomial in the two surface equations' quotient followed by
the quotient by the three original section rows. -/
def curvePolynomialMap {S : Type} [CommRing S] [Algebra ℂ S] (y : ParameterIndex → S) :
    ChartPolynomial S →+* AffineCurveChart y t i :=
  (Ideal.Quotient.mk (affineSectionIdeal y t i)).comp (dehomogenizedMap y i)

theorem curveChartSpecialization_polynomial (a : ChartPolynomial ParameterAlgebra) :
    curveChartSpecialization t i (curvePolynomialMap t i incidencePoint a) =
      curvePolynomialMap t i seed (MvPolynomial.map seedMap a) := by
  change curveChartSpecialization t i (Ideal.Quotient.mk _ (dehomogenizedMap _ _ a)) = _
  rw [curveChartSpecialization_mk, seedChartSpecialization_polynomial]
  rfl

theorem polynomial_notMem_movingPrime_iff
    (z : PrimeSpectrum (AffineCurveChart seed t i)) (a : ChartPolynomial ParameterAlgebra) :
    curvePolynomialMap t i incidencePoint a ∉ (movingPrime t i z).asIdeal ↔
      curvePolynomialMap t i seed (MvPolynomial.map seedMap a) ∉ z.asIdeal := by
  change curveChartSpecialization t i (curvePolynomialMap t i incidencePoint a) ∉ z.asIdeal ↔ _
  rw [curveChartSpecialization_polynomial]

theorem pivot_notMem_movingPrime_iff (z : PrimeSpectrum (AffineCurveChart seed t i))
    (p : CycleQ2SegreCech.Chart) :
    Ideal.Quotient.mk (affineSectionIdeal incidencePoint t i) (affineMatrixEntry incidencePoint i p) ∉
        (movingPrime t i z).asIdeal ↔
      Ideal.Quotient.mk (affineSectionIdeal seed t i) (seedPivot i p) ∉ z.asIdeal := by
  change curveChartSpecialization t i (Ideal.Quotient.mk (affineSectionIdeal incidencePoint t i)
    (affineMatrixEntry incidencePoint i p)) ∉ z.asIdeal ↔ _
  rw [curveChartSpecialization_mk, seedChartSpecialization_affineMatrixEntry]

/-- Every prime of a seed curve chart misses one of the nine matrix entries.
The chosen weight-one coordinate equals one under dehomogenization. -/
theorem exists_seedPivot_notMem (z : PrimeSpectrum (AffineCurveChart seed t i)) :
    ∃ p : CycleQ2SegreCech.Chart,
      Ideal.Quotient.mk (affineSectionIdeal seed t i) (seedPivot i p) ∉ z.asIdeal := by
  let f : PointSurface seed →+* AffineCurveChart seed t i :=
    (Ideal.Quotient.mk (affineSectionIdeal seed t i)).comp (surfaceToDehomogenized seed i)
  let P := PrimeSpectrum.comap f z
  letI : P.asIdeal.IsPrime := P.isPrime
  have hcoord : ∃ j : Fin 5,
      CycleQ2IncidenceBasepointOpen.curveCoordinate (pointMap seed) j ∉ P.asIdeal := by
    refine ⟨i.castSucc, ?_⟩
    change Ideal.Quotient.mk (affineSectionIdeal seed t i) (surfaceToDehomogenized seed i
      (surfaceQuotient seed (X i.castSucc))) ∉ z.asIdeal
    rw [surfaceToDehomogenized_self, map_one]
    exact z.isPrime.one_notMem
  obtain ⟨j, k, hp⟩ := CycleQ2IncidenceBasepointOpen.specialized_prime_pivot_cover
    (pointMap seed) CycleQ2SpecializedSectionIdeal.seed_basepoint_unit P.asIdeal hcoord
  exact ⟨(j, k), hp⟩

theorem sectionRows_map (j : Fin 3) :
    (fun k : Fin 3 => MvPolynomial.map seedMap (Fin.snoc (α := fun _ => ChartPolynomial ParameterAlgebra)
      (dehomogenizedEquations incidencePoint i)
      (dehomogenize i (relativeSectionPolynomial incidencePoint t j)) k)) =
    Fin.snoc (α := fun _ => ChartPolynomial ℂ) (dehomogenizedEquations seed i)
      (dehomogenize i (relativeSectionPolynomial seed t j)) := by
  funext k
  refine Fin.lastCases ?_ (fun a => ?_) k
  · simp only [Fin.snoc_last, map_dehomogenize, relativeSectionPolynomial_seed]
  · simpa only [Fin.snoc_castSucc] using dehomogenizedEquations_seed i a

theorem pivotPolynomial_map (p : CycleQ2SegreCech.Chart) :
    MvPolynomial.map seedMap (dehomogenize i (pointMatrixPolynomial incidencePoint p.1 p.2)) =
      dehomogenize i (pointMatrixPolynomial seed p.1 p.2) := by
  rw [map_dehomogenize, pointMatrixPolynomial_seed]

/-- A square minor, with columns selected from the four affine coordinates. -/
def jacobianMinor {S : Type} [CommRing S] {n : ℕ} (rows : Fin n → ChartPolynomial S)
    (cols : Fin n → Option (Fin 3)) : ChartPolynomial S :=
  (Matrix.of fun c r => pderiv (cols c) (rows r)).det

theorem jacobianMinor_map {S T : Type} [CommRing S] [CommRing T] (f : S →+* T) {n : ℕ}
    (rows : Fin n → ChartPolynomial S) (cols : Fin n → Option (Fin 3)) :
    MvPolynomial.map f (jacobianMinor rows cols) =
      jacobianMinor (fun r => MvPolynomial.map f (rows r)) cols := by
  simp only [jacobianMinor, RingHom.map_det]
  apply congrArg Matrix.det
  apply Matrix.ext
  intro r c
  exact (pderiv_map (φ := f) (i := cols r) (f := rows c)).symm

theorem jacobianMinor_notMem_movingPrime_iff (z : PrimeSpectrum (AffineCurveChart seed t i))
    {n : ℕ} (rows : Fin n → ChartPolynomial ParameterAlgebra) (cols : Fin n → Option (Fin 3)) :
    curvePolynomialMap t i incidencePoint (jacobianMinor rows cols) ∉ (movingPrime t i z).asIdeal ↔
      curvePolynomialMap t i seed
        (jacobianMinor (fun r => MvPolynomial.map seedMap (rows r)) cols) ∉ z.asIdeal := by
  rw [polynomial_notMem_movingPrime_iff, jacobianMinor_map]

#print axioms exists_seedChart_prime
#print axioms exists_seedPivot_notMem
#print axioms polynomial_notMem_movingPrime_iff
#print axioms pivot_notMem_movingPrime_iff
#print axioms jacobianMinor_notMem_movingPrime_iff

end CycleQ2LiteralAbelJacobiSeedLiftPoints
end
