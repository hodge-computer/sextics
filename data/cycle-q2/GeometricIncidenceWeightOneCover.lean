import Proposal.GeometricIncidenceChartSeedFiber
import Proposal.GeometricSeedCoordinateCover
import Mathlib.RingTheory.MvPolynomial.Ideal

/-!
# Coordinate covers of the actual incidence surface and its literal seed

Status: source-only proof draft. No elaboration or kernel replay was run.

The five original geometric coordinates cover the actual projective
incidence surface for every coefficient algebra and every parameter y.
At the original literal seed, the existing seed equations show that the
three coordinates X1, X2, X3 already meet every relevant prime. Therefore
the four weight-one coordinate opens cover that actual seed surface.

The general five-coordinate argument adapts the existing Cartier cover
proof to the unchanged incidence quotient grading. This module does not
assert that the weight-one opens cover the full relative incidence
surface, or identify the literal seed with its scheme-theoretic fiber.

The geometric strategy is due to Ben Diamond and the collaborators cited
in solution.md. Prepared for fqlx with OpenAI ChatGPT assistance.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2IncidenceWeightOneCover

open MvPolynomial TopologicalSpace AlgebraicGeometry
open CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations
  CycleQ2IncidenceUniversalChart CycleQ2IncidencePolynomialJacobianBinding
  CycleQ2IncidenceImageLine CycleQ2GeometricIncidenceProj
  CycleQ2IncidenceDehomogenizedChart CycleQ2IncidenceChartSeedFiber

variable {S : Type} [CommRing S] [Algebra ℂ S]

def allCoordinatePatch (y : ParameterIndex → S) (j : Fin 5) : (surface y).Opens :=
  Proj.basicOpen (surfaceGrade y) (surfaceQuotient y (X j))

/-- Every positive-degree homogeneous class is in the ideal generated
by the images of the five original geometric coordinates. -/
theorem irrelevant_le_coordinateIdeal (y : ParameterIndex → S) :
    (HomogeneousIdeal.irrelevant (surfaceGrade y)).toIdeal ≤
      Ideal.span (Set.range (fun j : Fin 5 => surfaceQuotient y (X j))) := by
  apply (HomogeneousIdeal.toIdeal_irrelevant_le _).mpr
  intro n hn q hq
  obtain ⟨p, hp, rfl⟩ := hq
  have hpI : p ∈ MvPolynomial.idealOfVars (Fin 5) S := by
    have hpow : p ∈ MvPolynomial.idealOfVars (Fin 5) S ^ 1 := by
      apply (MvPolynomial.mem_pow_idealOfVars_iff' 1 p).mpr
      intro e he
      have he0 : e = 0 := (Finsupp.degree_eq_zero_iff e).mp (by omega)
      subst e
      by_contra hc
      have hz : 0 = n := by simpa only [map_zero] using hp hc
      omega
    simpa only [pow_one] using hpow
  have hmap : MvPolynomial.idealOfVars (Fin 5) S ≤
      (Ideal.span (Set.range (fun j : Fin 5 => surfaceQuotient y (X j)))).comap
        (surfaceQuotient y) := by
    apply Ideal.span_le.mpr
    rintro _ ⟨j, rfl⟩
    exact Ideal.subset_span ⟨j, rfl⟩
  exact hmap hpI

theorem allCoordinatePatches_cover (y : ParameterIndex → S) :
    (⨆ j : Fin 5, allCoordinatePatch y j) = ⊤ :=
  Proj.iSup_basicOpen_eq_top (surfaceGrade y) _ (irrelevant_le_coordinateIdeal y)

theorem exists_coordinate_not_mem (y : ParameterIndex → S) (q : surface y) :
    ∃ j : Fin 5, surfaceQuotient y (X j) ∉ q.asHomogeneousIdeal.toIdeal := by
  have hq : q ∈ ⨆ j : Fin 5, allCoordinatePatch y j := by
    rw [allCoordinatePatches_cover]
    trivial
  exact Opens.mem_iSup.mp hq

/-- The actual weight-one coordinate opens cover the original literal
seed surface. No comparison with an abstract replacement surface is used. -/
theorem seed_weightOne_cover :
    (⨆ i : Fin 4, familyCoordinatePatch (seedPoint (57 : ℂ) Complex.I) i) = ⊤ := by
  apply top_le_iff.mp
  intro q _
  obtain ⟨j, hj⟩ := exists_coordinate_not_mem (seedPoint (57 : ℂ) Complex.I) q
  letI : q.asHomogeneousIdeal.toIdeal.IsPrime := q.isPrime
  let P : Ideal (Poly ℂ) :=
    Ideal.comap (surfaceQuotient (seedPoint (57 : ℂ) Complex.I)) q.asHomogeneousIdeal.toIdeal
  letI : P.IsPrime := inferInstance
  have hF : smoothF (57 : ℂ) Complex.I ∈ P := by
    change surfaceQuotient (seedPoint (57 : ℂ) Complex.I)
      (smoothF (57 : ℂ) Complex.I) ∈ q.asHomogeneousIdeal.toIdeal
    rw [← literal_pointEquationF]
    have hz : surfaceQuotient (seedPoint (57 : ℂ) Complex.I)
        (pointEquationF (seedPoint (57 : ℂ) Complex.I)) = 0 :=
      surfaceQuotient_equation (seedPoint (57 : ℂ) Complex.I) 0
    rw [hz]
    exact q.asHomogeneousIdeal.toIdeal.zero_mem
  have hH : smoothH Complex.I ∈ P := by
    change surfaceQuotient (seedPoint (57 : ℂ) Complex.I)
      (smoothH Complex.I) ∈ q.asHomogeneousIdeal.toIdeal
    rw [← literal_pointEquationH]
    have hz : surfaceQuotient (seedPoint (57 : ℂ) Complex.I)
        (pointEquationH (seedPoint (57 : ℂ) Complex.I)) = 0 :=
      surfaceQuotient_equation (seedPoint (57 : ℂ) Complex.I) 1
    rw [hz]
    exact q.asHomogeneousIdeal.toIdeal.zero_mem
  have hx : ∃ a : Fin 5, X a ∉ P := ⟨j, hj⟩
  rcases CycleQ2SeedCoordinateCover.seedPrime_coordinate_cover (57 : ℂ) Complex.I
      P hH hF hx with h1 | h2 | h3
  · exact Opens.mem_iSup.mpr ⟨1, h1⟩
  · exact Opens.mem_iSup.mpr ⟨2, h2⟩
  · exact Opens.mem_iSup.mpr ⟨3, h3⟩

end CycleQ2IncidenceWeightOneCover

end

#print axioms CycleQ2IncidenceWeightOneCover.allCoordinatePatches_cover
#print axioms CycleQ2IncidenceWeightOneCover.exists_coordinate_not_mem
#print axioms CycleQ2IncidenceWeightOneCover.seed_weightOne_cover
