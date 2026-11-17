import Proposal.GeometricIncidenceChartFiberScheme
import Proposal.GeometricIncidenceSeedMinorSpecialization
import Proposal.GeometricIncidenceSeedChartMinorCover
import Proposal.GeometricIncidenceSmoothSchemeOpens
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Points of the actual seed fiber in a coordinate chart lie in the good open

A point of an actual incidence chart lying over the original seed lifts
to its scheme pullback with Spec complex. The exact affine fiber
isomorphism turns the lift into a prime of the original seed chart.
The seed minor cover and exact minor specialization then put the
original point in one of the actual relative smooth minor opens.

The final theorem assumes membership in a weight-one coordinate open.
Covering the whole scheme-theoretic fiber by those coordinate opens is
a separate component; no smoothness premise is supplied here.

The geometric strategy is due to Ben Diamond and the collaborators cited
in solution.md. Prepared for fqlx with OpenAI ChatGPT assistance.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2IncidenceSeedFiberGoodOpen

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial
open scoped TensorProduct
open CycleQ2IncidencePolynomialJacobianBinding CycleQ2IncidenceEtaleParameter
  CycleQ2GeometricIncidenceProj CycleQ2IncidenceDehomogenizedChart
  CycleQ2IncidenceChartMinor CycleQ2IncidenceChartSeedFiber
  CycleQ2IncidenceChartFiberScheme CycleQ2IncidenceSeedMinorSpecialization
  CycleQ2IncidenceSeedChartMinorCover CycleQ2IncidenceSmoothSchemeOpens

attribute [local instance] CycleQ2IncidenceSeedFiber.seedAlgebra

local instance incidenceChartCommRing (i : Fin 4) :
    CommRing (DehomogenizedRing incidencePoint i) := inferInstance
local instance seedChartCommRing (i : Fin 4) :
    CommRing (DehomogenizedRing (seedPoint (57 : ℂ) Complex.I) i) := inferInstance

/-- The exact specialization appearing in the scheme projection
preserves each original normalized minor. -/
theorem seedChartSpecialization_normalizedMinor (i : Fin 4) (j k : Fin 5) :
    seedChartSpecialization i (normalizedMinor incidencePoint i j k) =
      normalizedMinor (seedPoint (57 : ℂ) Complex.I) i j k := by
  change seedChartFiberEquiv i
    (1 ⊗ₜ[ParameterAlgebra] normalizedMinor incidencePoint i j k) = _
  exact seedChartFiberEquiv_normalizedMinor i j k

/-- A point in the actual affine chart over the original seed lies in
the explicit union of relative smooth principal opens. -/
theorem affine_mem_goodOpen_of_seed (i : Fin 4)
    (a : Spec (CommRingCat.of (DehomogenizedRing incidencePoint i)))
    (ha : relativeChartToParameters i a = seedParameterMorphism default) :
    affineChartToSurface incidencePoint i a ∈ goodOpen incidencePoint := by
  obtain ⟨z, _, hza⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := seedParameterMorphism) (g := relativeChartToParameters i)
    default a ha.symm
  let p : Spec (CommRingCat.of
      (DehomogenizedRing (seedPoint (57 : ℂ) Complex.I) i)) :=
    (affineChartSeedFiberIso i).hom z
  have hpmap : Spec.map (CommRingCat.ofHom (R := DehomogenizedRing incidencePoint i)
      (S := DehomogenizedRing (seedPoint (57 : ℂ) Complex.I) i) (seedChartSpecialization i)) p = a := by
    have h := congrArg
      (fun f : AffineChartSeedFiber i ⟶
        Spec (CommRingCat.of (DehomogenizedRing incidencePoint i)) => f z)
      (affineChartSeedFiberIso_hom_snd i)
    change Spec.map (CommRingCat.ofHom (R := DehomogenizedRing incidencePoint i)
      (S := DehomogenizedRing (seedPoint (57 : ℂ) Complex.I) i) (seedChartSpecialization i)) p =
      pullback.snd seedParameterMorphism (relativeChartToParameters i) z at h
    exact h.trans hza
  letI : p.asIdeal.IsPrime := p.isPrime
  obtain ⟨j, k, hjk, hp⟩ := seed_prime_normalizedMinor_cover i p.asIdeal
  have haMinor : normalizedMinor incidencePoint i j k ∉ a.asIdeal := by
    have h : normalizedMinor incidencePoint i j k ∉
        (Spec.map (CommRingCat.ofHom (R := DehomogenizedRing incidencePoint i)
      (S := DehomogenizedRing (seedPoint (57 : ℂ) Complex.I) i) (seedChartSpecialization i)) p).asIdeal := by
      rw [Spec.map_apply, PrimeSpectrum.comap_asIdeal]
      simp only [CommRingCat.hom_ofHom, Ideal.mem_comap]
      intro hm
      exact hp ((seedChartSpecialization_normalizedMinor i j k) ▸ hm)
    exact hpmap ▸ h
  have hminor : affineChartToSurface incidencePoint i a ∈
      minorOpen incidencePoint i j k := by
    change a ∈ affineChartToSurface incidencePoint i ⁻¹ᵁ
      minorOpen incidencePoint i j k
    rw [affineChartToSurface_preimage_minorOpen]
    exact haMinor
  have hpair : Function.Injective (![j, k] : Fin 2 → Fin 5) := by
    intro u v huv
    fin_cases u <;> fin_cases v
    · rfl
    · exact (hjk (by simpa using huv)).elim
    · exact (hjk (by simpa using huv.symm)).elim
    · rfl
  exact minorOpen_le_goodOpen incidencePoint i ⟨![j, k], hpair⟩ hminor

/-- Local whole-fiber membership on an actual projective coordinate
open. The separate coordinate-cover argument discharges hx globally. -/
theorem mem_goodOpen_of_seed_of_mem_coordinatePatch
    (x : surface incidencePoint) (i : Fin 4)
    (hs : surfaceToBase incidencePoint x = seedParameterMorphism default)
    (hx : x ∈ familyCoordinatePatch incidencePoint i) :
    x ∈ goodOpen incidencePoint := by
  let u : (familyCoordinatePatch incidencePoint i).toScheme := ⟨x, hx⟩
  let a : Spec (CommRingCat.of (DehomogenizedRing incidencePoint i)) :=
    (familyCoordinateAffineChart incidencePoint i).hom u
  have ha : affineChartToSurface incidencePoint i a = x := by
    have h : (familyCoordinateAffineChart incidencePoint i).inv
        ((familyCoordinateAffineChart incidencePoint i).hom u) = u := by
      change ((familyCoordinateAffineChart incidencePoint i).hom ≫
        (familyCoordinateAffineChart incidencePoint i).inv) u = u
      rw [Iso.hom_inv_id]
      rfl
    change (familyCoordinatePatch incidencePoint i).ι
      ((familyCoordinateAffineChart incidencePoint i).inv
        ((familyCoordinateAffineChart incidencePoint i).hom u)) = x
    rw [h]
    rfl
  have hbase : relativeChartToParameters i a = seedParameterMorphism default := by
    have h := congrArg
      (fun f : Spec (CommRingCat.of (DehomogenizedRing incidencePoint i)) ⟶
        Spec (CommRingCat.of ParameterAlgebra) => f a)
      (affineChartToSurface_overBase incidencePoint i)
    change surfaceToBase incidencePoint (affineChartToSurface incidencePoint i a) =
      relativeChartToParameters i a at h
    rw [ha, hs] at h
    exact h.symm
  have hgood := affine_mem_goodOpen_of_seed i a hbase
  rwa [ha] at hgood

end CycleQ2IncidenceSeedFiberGoodOpen

end

#print axioms CycleQ2IncidenceSeedFiberGoodOpen.seedChartSpecialization_normalizedMinor
#print axioms CycleQ2IncidenceSeedFiberGoodOpen.affine_mem_goodOpen_of_seed
#print axioms CycleQ2IncidenceSeedFiberGoodOpen.mem_goodOpen_of_seed_of_mem_coordinatePatch
