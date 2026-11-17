import Proposal.GeometricIncidenceChartFiberScheme

/-!
# Coefficient primes of the actual incidence surface

The original surfaceToBase is defined through Proj.toSpecZero and the
canonical coefficient map into degree zero. This component computes its
map on points: a coefficient belongs to the base prime exactly when its
image in the original PointSurface belongs to the homogeneous prime.

The proof uses the canonical D₊(1) map. It needs no coordinate cover and
no identification of the global projective seed fiber. Consequently, a
point lying over the actual seedMap image contains every coefficient
annihilated by seedMap. This is the precise coefficient condition used
for transporting its polynomial prime to the literal seed.

The geometric strategy is due to Ben Diamond and the collaborators cited
in solution.md. Prepared for fqlx with OpenAI ChatGPT assistance.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2IncidenceFiberCoefficients

open CategoryTheory AlgebraicGeometry HomogeneousLocalization
open CycleQ2IncidenceUniversalChart CycleQ2IncidenceImageLine
  CycleQ2GeometricIncidenceProj CycleQ2IncidenceEtaleParameter
  CycleQ2IncidenceChartFiberScheme

variable {S : Type} [CommRing S] [Algebra ℂ S]

/-- The newer scheme-level basic-open map is the original locally ringed
space map whose prime is calculated in ProjectiveSpectrum.Scheme. The
proof is the same canonical-adjunction comparison used by Mathlib's
Proj.basicOpenIsoSpec; it does not require positive degree. -/
private theorem basicOpenToSpec_toLRSHom (y : ParameterIndex → S)
    (f : PointSurface y) :
    (Proj.basicOpenToSpec (surfaceGrade y) f).toLRSHom =
      ProjectiveSpectrum.Proj.toSpec (surfaceGrade y) f := by
  refine Eq.trans ?_
    (ΓSpec.locallyRingedSpaceAdjunction.homEquiv_apply _ _ _).symm
  dsimp [Proj.basicOpenToSpec, Scheme.Opens.toSpecΓ]
  simp only [Category.assoc, ← Spec.map_comp]
  rfl

/-- Exact coefficient membership for the original relative surface
structure morphism. The coefficient image is the original algebraMap. -/
theorem coefficient_mem_iff (y : ParameterIndex → S) (x : surface y) (a : S) :
    a ∈ (surfaceToBase y x).asIdeal ↔
      algebraMap S (PointSurface y) a ∈ x.asHomogeneousIdeal.toIdeal := by
  let x₁ : (Proj.basicOpen (surfaceGrade y) (1 : PointSurface y)).toScheme :=
    ((Scheme.topIso (surface y)).inv ≫
      (Scheme.isoOfEq (surface y) (Proj.basicOpen_one (surfaceGrade y))).inv) x
  have hx₁ : x₁.1 = x := by
    change ((Scheme.topIso (surface y)).inv ≫
      (Scheme.isoOfEq (surface y) (Proj.basicOpen_one (surfaceGrade y))).inv ≫
        (Proj.basicOpen (surfaceGrade y) (1 : PointSurface y)).ι) x = x
    erw [Scheme.isoOfEq_inv_ι, Scheme.toIso_inv_ι]
    rfl
  change fromZeroRingHom (surfaceGrade y) (Submonoid.powers (1 : PointSurface y))
      (surfaceCoefficient y a) ∈
        ((Proj.basicOpenToSpec (surfaceGrade y) (1 : PointSurface y)).toLRSHom.base
          x₁).asIdeal ↔ _
  rw [basicOpenToSpec_toLRSHom]
  change HomogeneousLocalization.mk
      (⟨0, surfaceCoefficient y a, 1, one_mem _⟩ :
        NumDenSameDeg (surfaceGrade y) (Submonoid.powers (1 : PointSurface y))) ∈
        ((ProjectiveSpectrum.Proj.toSpec (surfaceGrade y) (1 : PointSurface y)).base
          x₁).asIdeal ↔ _
  rw [ProjectiveSpectrum.Proj.mk_mem_toSpec_base_apply]
  simp only [surfaceCoefficient_val]
  change algebraMap S (PointSurface y) a ∈ x₁.1.asHomogeneousIdeal.toIdeal ↔
    algebraMap S (PointSurface y) a ∈ x.asHomogeneousIdeal.toIdeal
  rw [hx₁]

/-- Every coefficient killed by the original seed map belongs to the
homogeneous prime of every actual surface point over that seed point.
The complex point is explicit, so this does not depend on a choice of
the unique point of Spec ℂ or on a global fiber isomorphism. -/
theorem seed_kernel_mem_of_over_seed
    (x : surface incidencePoint) (s : Spec (CommRingCat.of ℂ))
    (hx : surfaceToBase incidencePoint x = seedParameterMorphism s)
    (a : ParameterAlgebra) (ha : seedMap a = 0) :
    algebraMap ParameterAlgebra (PointSurface incidencePoint) a ∈
      x.asHomogeneousIdeal.toIdeal := by
  apply (coefficient_mem_iff incidencePoint x a).mp
  rw [hx]
  change seedMap a ∈ s.asIdeal
  rw [ha]
  exact Ideal.zero_mem _

/-- The same coefficient condition as an inclusion of ideals, with the
canonical original coefficient map on the surface ring. -/
theorem seed_kernel_le_of_over_seed
    (x : surface incidencePoint) (s : Spec (CommRingCat.of ℂ))
    (hx : surfaceToBase incidencePoint x = seedParameterMorphism s) :
    RingHom.ker seedMap ≤
      x.asHomogeneousIdeal.toIdeal.comap
        (algebraMap ParameterAlgebra (PointSurface incidencePoint)) := by
  intro a ha
  exact seed_kernel_mem_of_over_seed x s hx a ha

end CycleQ2IncidenceFiberCoefficients

end

#print axioms CycleQ2IncidenceFiberCoefficients.coefficient_mem_iff
#print axioms CycleQ2IncidenceFiberCoefficients.seed_kernel_mem_of_over_seed
#print axioms CycleQ2IncidenceFiberCoefficients.seed_kernel_le_of_over_seed
