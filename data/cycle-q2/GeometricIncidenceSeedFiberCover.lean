import Proposal.GeometricIncidenceFiberCoefficients
import Proposal.GeometricIncidenceSeedPrimeTransport
import Proposal.GeometricIncidenceWeightOneCover
import Proposal.GeometricIncidenceSeedFiberGoodOpen

/-!
# The whole actual seed fiber lies in the relative smooth good open

For a point of the original projective incidence surface over the actual
seed base point, its homogeneous prime contains the seed coefficient
kernel. Contraction to the original polynomial ring preserves primality,
contains both original equations, and remains relevant by the five
coordinate cover. The proved prime-specialization argument therefore
places the point in a weight-one coordinate open.

The exact affine seed-fiber comparison and normalized-minor cover then
place every such point in the existing goodOpen. All morphisms, rings,
coordinates, and equations are the original constructions. No geometric
assumption or global projective base-change isomorphism is introduced.

The geometric strategy is due to Ben Diamond and the collaborators cited
in solution.md. Prepared for fqlx with OpenAI ChatGPT assistance.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2IncidenceSeedFiberCover

open AlgebraicGeometry MvPolynomial
open CycleQ2IncidenceNormalForm CycleQ2IncidenceImageLine
  CycleQ2IncidenceEtaleParameter CycleQ2GeometricIncidenceProj
  CycleQ2IncidenceDehomogenizedChart CycleQ2IncidenceChartFiberScheme
  CycleQ2IncidenceFiberCoefficients CycleQ2IncidenceSeedPrimeTransport
  CycleQ2IncidenceWeightOneCover CycleQ2IncidenceSmoothSchemeOpens
  CycleQ2IncidenceSeedFiberGoodOpen

/-- The base point defined by the original seedMap. -/
def seedBasePoint : Spec (CommRingCat.of ParameterAlgebra) :=
  seedParameterMorphism (default : Spec (CommRingCat.of ℂ))

/-- Every point of the actual projective seed fiber belongs to an
original weight-one coordinate open. -/
theorem exists_weightOne_of_over_seed (x : surface incidencePoint)
    (hx : surfaceToBase incidencePoint x = seedBasePoint) :
    ∃ i : Fin 4, x ∈ familyCoordinatePatch incidencePoint i := by
  letI : x.asHomogeneousIdeal.toIdeal.IsPrime := x.isPrime
  let P : Ideal (MvPolynomial (Fin 5) ParameterAlgebra) :=
    Ideal.comap (surfaceQuotient incidencePoint) x.asHomogeneousIdeal.toIdeal
  letI : P.IsPrime := inferInstance
  have hcoeff : ∀ a : ParameterAlgebra, seedMap a = 0 → C a ∈ P := by
    intro a ha
    change algebraMap ParameterAlgebra (PointSurface incidencePoint) a ∈
      x.asHomogeneousIdeal.toIdeal
    exact seed_kernel_mem_of_over_seed x default hx a ha
  have hH : pointEquationH incidencePoint ∈ P := by
    change surfaceQuotient incidencePoint (pointEquationH incidencePoint) ∈
      x.asHomogeneousIdeal.toIdeal
    have hz : surfaceQuotient incidencePoint (pointEquationH incidencePoint) = 0 :=
      surfaceQuotient_equation incidencePoint 1
    rw [hz]
    exact x.asHomogeneousIdeal.toIdeal.zero_mem
  have hF : pointEquationF incidencePoint ∈ P := by
    change surfaceQuotient incidencePoint (pointEquationF incidencePoint) ∈
      x.asHomogeneousIdeal.toIdeal
    have hz : surfaceQuotient incidencePoint (pointEquationF incidencePoint) = 0 :=
      surfaceQuotient_equation incidencePoint 0
    rw [hz]
    exact x.asHomogeneousIdeal.toIdeal.zero_mem
  have hrelevant : ∃ j : Fin 5, (X j : MvPolynomial (Fin 5) ParameterAlgebra) ∉ P := by
    obtain ⟨j, hj⟩ := exists_coordinate_not_mem incidencePoint x
    exact ⟨j, hj⟩
  obtain ⟨i, hi⟩ := seed_fiber_prime_coordinate_cover P hcoeff hH hF hrelevant
  refine ⟨i, ?_⟩
  change surfaceQuotient incidencePoint (X i.castSucc) ∉
    x.asHomogeneousIdeal.toIdeal
  exact hi

/-- The whole actual fiber over seedBasePoint is contained in the union
of the explicit relative smooth minor opens. -/
theorem seedFiber_mem_goodOpen (x : surface incidencePoint)
    (hx : surfaceToBase incidencePoint x = seedBasePoint) :
    x ∈ goodOpen incidencePoint := by
  obtain ⟨i, hi⟩ := exists_weightOne_of_over_seed x hx
  exact mem_goodOpen_of_seed_of_mem_coordinatePatch x i hx hi

end CycleQ2IncidenceSeedFiberCover

end

#print axioms CycleQ2IncidenceSeedFiberCover.exists_weightOne_of_over_seed
#print axioms CycleQ2IncidenceSeedFiberCover.seedFiber_mem_goodOpen
