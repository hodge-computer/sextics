import Proposal.GeometricCartierOrbit

section SourceCartierProjectionLinear

set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace CycleQ2GeometricCoordinateCharacter

open MvPolynomial CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations
  CycleQ2SeedQuotientFiniteFree CycleQ2SeedCechThreeOpen
  CycleQ2SeedCechLocalization CycleQ2SeedCechLocalizedBasis
  CycleQ2GeometricCartierNormalLift CycleQ2GeometricSurfaceCoordinates
  CycleQ2GeometricLaurentTop CycleQ2GeometricSeedNormalIdeals CycleQ2SegreTangentLocal

/-- The fixed original quotient/localization equivalence preserves the
actual complex coefficient maps. -/
theorem seedCoordinateEquiv_complex (r : ℂ) (s : Finset (Fin 3)) (c : ℂ) :
    seedCoordinateEquiv r s (algebraMap ℂ (CoordinateLocal r 1 s) c) =
      algebraMap ℂ (SeedLocal ℂ r Complex.I s) c := by
  rw [IsScalarTower.algebraMap_apply ℂ (SurfaceRing r 1) (CoordinateLocal r 1 s),
    seedCoordinateEquiv_base, (seedRingEquiv r).commutes,
    ← IsScalarTower.algebraMap_apply ℂ (SeedRing r Complex.I) (SeedLocal ℂ r Complex.I s)]

def seedCoordinateAlgEquiv (r : ℂ) (s : Finset (Fin 3)) :
    CoordinateLocal r 1 s ≃ₐ[ℂ] SeedLocal ℂ r Complex.I s where
  __ := seedCoordinateEquiv r s
  commutes' := seedCoordinateEquiv_complex r s

theorem coordinate_complex_constant (r : ℂ) (c : ℂ) :
    algebraMap ℂ (CoordinateLocal r 1 Finset.univ) c =
      algebraMap (SurfaceRing r 1) (CoordinateLocal r 1 Finset.univ)
        (quotientMap r 1 (C c)) := by
  rw [IsScalarTower.algebraMap_apply ℂ (SurfaceRing r 1) (CoordinateLocal r 1 Finset.univ)]
  rfl

theorem coordinateProject_complex_smul (r : ℂ) (χ : ZMod 3) (c : ℂ)
    (q : CoordinateLocal r 1 Finset.univ) :
    coordinateProject r Finset.univ χ (c • q) =
      c • coordinateProject r Finset.univ χ q := by
  have hs (v : CoordinateLocal r 1 Finset.univ) : c • v =
      algebraMap (SurfaceRing r 1) (CoordinateLocal r 1 Finset.univ)
        (quotientMap r 1 (C c)) * v := by
    rw [Algebra.smul_def, coordinate_complex_constant]
  rw [hs q, hs (coordinateProject r Finset.univ χ q)]
  exact coordinateProject_mul_invariant r q (C c) χ (isWeightedHomogeneous_C _ _)

def coordinateProjectLinear (r : ℂ) (χ : ZMod 3) :
    CoordinateLocal r 1 Finset.univ →ₗ[ℂ] CoordinateLocal r 1 Finset.univ where
  __ := coordinateProjectHom r Finset.univ χ
  map_smul' c q := coordinateProject_complex_smul r χ c q

/-- The actual coordinate projections are mutually orthogonal. -/
theorem coordinateProject_project (r : ℂ) (s : Finset (Fin 3))
    (χ τ : ZMod 3) (q : CoordinateLocal r 1 s) :
    coordinateProject r s χ (coordinateProject r s τ q) =
      if χ = τ then coordinateProject r s χ q else 0 := by
  classical
  by_cases h : χ = τ
  · subst τ
    rw [if_pos rfl]
    apply coordinateLaurent_injective r s
    ext ab e
    simp only [coordinateProject_coordinates, characterPart_coeff]
    split <;> simp_all
  · rw [if_neg h]
    apply coordinateLaurent_injective r s
    ext ab e
    simp only [coordinateProject_coordinates, characterPart_coeff, map_zero,
      Pi.zero_apply, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
    by_cases he : (shiftedGrade ab e).2 = χ
    · simp [he, h]
    · simp [he]

/-- The decomposition reconstructs each original localized section. -/
theorem coordinateProject_total (r : ℂ) (s : Finset (Fin 3))
    (q : CoordinateLocal r 1 s) : (∑ χ : ZMod 3, coordinateProject r s χ q) = q := by
  classical
  apply coordinateLaurent_injective r s
  ext ab e
  simp only [map_sum, Finset.sum_apply, coordinateProject_coordinates,
    AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, characterPart_coeff]
  simp

end CycleQ2GeometricCoordinateCharacter

#print axioms CycleQ2GeometricCoordinateCharacter.seedCoordinateAlgEquiv
#print axioms CycleQ2GeometricCoordinateCharacter.coordinateProjectLinear
#print axioms CycleQ2GeometricCoordinateCharacter.coordinateProject_project
#print axioms CycleQ2GeometricCoordinateCharacter.coordinateProject_total

end
end SourceCartierProjectionLinear

section SourceCartierOrbitProjection

set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace CycleQ2GeometricCoordinateCharacter

open CycleQ2SeedCechThreeOpen CycleQ2GeometricSurfaceCoordinates
  CycleQ2GeometricLaurentTop CycleQ2GeometricHomogeneousWeight
  CycleQ2GeometricCartierCech CycleQ2GeometricFourOpenCech
  CycleQ2NormalConnecting CycleQ2OrbitTraceBridge

/-- The original localized action under the fixed complex-linear
coordinate equivalence, with no assumed cohomology action. -/
def coordinateLinearAction (ζ : ℂ) (hζ : ζ ^ 3 = 1) (r : ℂ) :
    CoordinateLocal r 1 Finset.univ →ₗ[ℂ] CoordinateLocal r 1 Finset.univ :=
  (seedCoordinateAlgEquiv r Finset.univ).symm.toLinearMap.comp
    ((localLinearAction ζ hζ r Complex.I Finset.univ).comp
      (seedCoordinateAlgEquiv r Finset.univ).toLinearMap)

theorem coordinateLinearAction_project (ζ : ℂ) (hζ : ζ ^ 3 = 1)
    (r : ℂ) (χ : ZMod 3) (q : CoordinateLocal r 1 Finset.univ) :
    coordinateLinearAction ζ hζ r (coordinateProject r Finset.univ χ q) =
      ζ ^ χ.val • coordinateProject r Finset.univ χ q := by
  change (seedCoordinateAlgEquiv r Finset.univ).symm
      (CycleQ2SeedCyclicLocalization.localAction ζ hζ r Complex.I Finset.univ
        (seedCoordinateEquiv r Finset.univ (coordinateProject r Finset.univ χ q))) = _
  rw [projected_localAction]
  change (seedCoordinateAlgEquiv r Finset.univ).symm
      (ζ ^ χ.val • (seedCoordinateAlgEquiv r Finset.univ)
        (coordinateProject r Finset.univ χ q)) = _
  rw [map_smul, AlgEquiv.symm_apply_apply]

theorem coordinateLinearAction_decomposition (ζ : ℂ) (hζ : ζ ^ 3 = 1)
    (r : ℂ) (q : CoordinateLocal r 1 Finset.univ) :
    coordinateLinearAction ζ hζ r q =
      ∑ χ : ZMod 3, ζ ^ χ.val • coordinateProject r Finset.univ χ q := by
  have h := congrArg (coordinateLinearAction ζ hζ r)
    (coordinateProject_total r Finset.univ q)
  rw [map_sum] at h
  calc
    coordinateLinearAction ζ hζ r q =
        ∑ χ : ZMod 3, coordinateLinearAction ζ hζ r
          (coordinateProject r Finset.univ χ q) := h.symm
    _ = _ := Finset.sum_congr rfl (fun χ _ => coordinateLinearAction_project ζ hζ r χ q)

theorem coordinateProject_action_eigen (ζ : ℂ) (hζ : ζ ^ 3 = 1)
    (r : ℂ) (χ : ZMod 3) (q : CoordinateLocal r 1 Finset.univ) :
    coordinateProject r Finset.univ χ (coordinateLinearAction ζ hζ r q) =
      ζ ^ χ.val • coordinateProject r Finset.univ χ q := by
  classical
  change coordinateProjectLinear r χ (coordinateLinearAction ζ hζ r q) = _
  rw [coordinateLinearAction_decomposition, map_sum]
  simp only [map_smul]
  change (∑ τ : ZMod 3, ζ ^ τ.val • coordinateProject r Finset.univ χ
    (coordinateProject r Finset.univ τ q)) = _
  rw [Finset.sum_eq_single χ]
  · simp [coordinateProject_project]
  · intro τ _ hτ
    rw [coordinateProject_project, if_neg (Ne.symm hτ), smul_zero]
  · simp

/-- Projecting the original action agrees with acting on the projection. -/
theorem coordinateProject_action (ζ : ℂ) (hζ : ζ ^ 3 = 1)
    (r : ℂ) (χ : ZMod 3) (q : CoordinateLocal r 1 Finset.univ) :
    coordinateProject r Finset.univ χ (coordinateLinearAction ζ hζ r q) =
      coordinateLinearAction ζ hζ r (coordinateProject r Finset.univ χ q) :=
  (coordinateProject_action_eigen ζ hζ r χ q).trans
    (coordinateLinearAction_project ζ hζ r χ q).symm

theorem coordinateTwistedOrbit_eq_twistedLinear (ζ : ℂ) (hζ : ζ ^ 3 = 1)
    (r : ℂ) (q : CoordinateLocal r 1 Finset.univ) :
    coordinateTwistedOrbit ζ hζ r q = twistedOrbit ζ (coordinateLinearAction ζ hζ r) q := by
  let E := seedCoordinateAlgEquiv r Finset.univ
  let g := localLinearAction ζ hζ r Complex.I Finset.univ
  have hcomm (v : CoordinateLocal r 1 Finset.univ) :
      E (coordinateLinearAction ζ hζ r v) = g (E v) := by
    change E (E.symm (g (E v))) = g (E v)
    exact E.apply_symm_apply _
  apply E.injective
  change E (E.symm (twistedOrbit ζ g (E q))) =
    E (twistedOrbit ζ (coordinateLinearAction ζ hζ r) q)
  rw [AlgEquiv.apply_symm_apply]
  simp only [twistedOrbit, map_add, map_smul, hcomm]

/-- This is the exact comparison required for the actual orbital image
class: project after taking the orbit of the original section. -/
theorem coordinateProject_twistedOrbit (ζ : ℂ) (hζ : ζ ^ 3 = 1)
    (r : ℂ) (χ : ZMod 3) (q : CoordinateLocal r 1 Finset.univ) :
    coordinateProject r Finset.univ χ (coordinateTwistedOrbit ζ hζ r q) =
      coordinateTwistedOrbit ζ hζ r (coordinateProject r Finset.univ χ q) := by
  rw [coordinateTwistedOrbit_eq_twistedLinear, coordinateTwistedOrbit_eq_twistedLinear]
  simp only [twistedOrbit, coordinateProject_add, coordinateProject_complex_smul,
    coordinateProject_action]

theorem coordinateProject_one_twistedOrbit (ζ : ℂ) (hζ : ζ ^ 3 = 1)
    (r : ℂ) (q : CoordinateLocal r 1 Finset.univ) :
    coordinateProject r Finset.univ 1 (coordinateTwistedOrbit ζ hζ r q) =
      (3 : ℕ) • coordinateProject r Finset.univ 1 q := by
  rw [coordinateProject_twistedOrbit, coordinateTwistedOrbit_projected]

/-- The unprojected orbit of the original Cartier descendant itself
has a nonzero negative coefficient. -/
theorem literal_original_twistedOrbit_negative (ζ : ℂ) (hζ : ζ ^ 3 = 1)
    (d : TwoCocycles (coordinateScalarSystem 57))
    (hcd : CartierCoordinateDescent 57 (cartierCycle 57 1 derivativeA 0) d)
    (q : HomogeneousCoordinateTop 57)
    (hq : q.val = coordinateTopRepresentative 57 d) :
    ∃ ab e, (∀ i, e i < 0) ∧
      (coordinateLaurent 57 Finset.univ (coordinateTwistedOrbit ζ hζ 57 q.val) ab).coeff e ≠ 0 := by
  obtain ⟨ab, e, he, hc⟩ := literal_projected_twistedOrbit_negative ζ hζ d hcd q hq
  refine ⟨ab, e, he, ?_⟩
  intro hz
  apply hc
  rw [← coordinateProject_twistedOrbit]
  simp only [coordinateProject_coordinates, characterPart_coeff]
  split <;> simp [hz]

end CycleQ2GeometricCoordinateCharacter

#print axioms CycleQ2GeometricCoordinateCharacter.coordinateProject_action
#print axioms CycleQ2GeometricCoordinateCharacter.coordinateProject_one_twistedOrbit
#print axioms CycleQ2GeometricCoordinateCharacter.literal_original_twistedOrbit_negative

end
end SourceCartierOrbitProjection
