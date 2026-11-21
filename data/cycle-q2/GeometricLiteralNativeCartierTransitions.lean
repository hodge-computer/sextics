import Proposal.GeometricLiteralNativeCartierFrames

/-!
# Native transitions of the original inverse Cartier ideal

All sixteen oriented pairs use the original six lifted units, their
inverses, or the original coordinate changes on a single Cartier open.
Their reductions carry the original restricted generator at the target
to the original restricted generator at the source. Regularity of those
same generators proves the multiplicative cocycle on every triple,
including repeated original Cartier indices.

Prepared for fqlx with OpenAI ChatGPT assistance; see solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralNativeCartierTransitions

open HomogeneousLocalization CycleQ2SeedTrace CycleQ2NormalConnecting
  CycleQ2GeometricSeedNormalIdeals CycleQ2GeometricCartierNormalLift
  CycleQ2LiteralGradedDeformation CycleQ2LiteralGradedReduction
  CycleQ2LiteralProjectiveDeformation CycleQ2LiteralProjectiveIntersections
  CycleQ2LiteralProjectiveIntersectionProjection CycleQ2LiteralProjectiveIntersectionRestrictions
  CycleQ2LiteralProjectiveIntersectionSplittings CycleQ2LiteralConeIntersectionTransport
  CycleQ2LiteralNativeHomogeneousFractions CycleQ2LiteralNativeTransitionUnits
  CycleQ2LiteralNativeCartierFrames CycleQ2LiteralCartierLiftedTransitions

def reduceUnit (s : Finset Vertex) : (ThickRing s)ˣ →* (ClosedRing s)ˣ :=
  Units.map (nativeReduction s).toMonoidHom

theorem reduceUnit_value (s : Finset Vertex) (u : (ThickRing s)ˣ) :
    (reduceUnit s u : ClosedRing s) = nativeReduction s (u : ThickRing s) := rfl

theorem normalizedConeUnit_value (s : Finset Vertex) (v : Vertex) (hv : v ∈ s)
    {k : ℕ} (p : GradedDeformation) (hp : p ∈ deformationGrade k)
    (u : (ThickCone s)ˣ) (hu : (u : ThickCone s) = algebraMap GradedDeformation (ThickCone s) p) :
    (normalizedConeUnit s v hv p hp u hu : ThickRing s) = normalized s v hv p hp :=
  normalizedUnit_value s v hv p hp (hu ▸ u.isUnit)

def closedPolynomial (s : Finset Vertex) (p : WeightedPoly) : ClosedCone s :=
  algebraMap (SurfaceRing 57 1) (ClosedCone s) (surfaceQuotient 57 1 p)

theorem reduction_cartierUnit (s : Finset Vertex) (a : Fin 4) (ha : Admissible s a) :
    ordinaryReduction s (cartierUnit s a ha : ThickCone s) =
      closedPolynomial s (CycleQ2LiteralCartierSplittings.coverPolynomial a) := by
  rw [cartierUnit_value, CycleQ2LiteralProjectiveIntersectionRestrictions.ordinaryReduction_base,
    reduction_cartierElement]
  fin_cases a <;> rfl

theorem closed_factorization (s : Finset Vertex) :
    closedPolynomial s (originalF1 57) * closedPolynomial s (originalG1 57) +
      closedPolynomial s originalF2 * closedPolynomial s originalG2 = 0 := by
  have h := congrArg (algebraMap (SurfaceRing 57 1) (ClosedCone s)) (surfaceQuotient_F 57 1)
  simpa only [actualSeedEquation, map_add, map_mul, surfaceQuotient_h, zero_mul,
    add_zero, map_zero, closedPolynomial] using h

theorem reduced_lifted01_generator (s : Finset Vertex) (l m : Fin 3)
    (hv : (0,l) ∈ s) (hw : (1,m) ∈ s) :
    ordinaryReduction s (transportedUnit s {0,1} (admits_pair s (0,l) (1,m) hv hw) lifted01 : ThickCone s) *
      closedPolynomial s (originalF1 57) = closedPolynomial s originalF2 := by
  have ht : transportedUnit s {0,1} (admits_pair s (0,l) (1,m) hv hw) lifted01 *
      cartierUnit s 1 ⟨m,hw⟩ = -cartierUnit s 0 ⟨l,hv⟩ := by
    rw [transported_lifted01 s l m hv hw, mul_assoc, inv_mul_cancel, mul_one]
  have h := congrArg (fun u : (ThickCone s)ˣ => ordinaryReduction s (u : ThickCone s)) ht
  simp only [Units.val_mul, Units.val_neg, map_mul, map_neg, reduction_cartierUnit] at h
  change ordinaryReduction s (transportedUnit s {0,1} (admits_pair s (0,l) (1,m) hv hw) lifted01 : ThickCone s) *
    closedPolynomial s originalG2 = -closedPolynomial s (originalG1 57) at h
  have hu : IsUnit (closedPolynomial s originalG2) := by
    have hunit := (cartierUnit s 1 ⟨m,hw⟩).isUnit.map (ordinaryReduction s)
    rw [reduction_cartierUnit] at hunit
    exact hunit
  apply hu.mul_right_cancel
  linear_combination closedPolynomial s (originalF1 57) * h - closed_factorization s

theorem native01_generator (s : Finset Vertex) (l m : Fin 3)
    (hv : (0,l) ∈ s) (hw : (1,m) ∈ s) :
    (reduceUnit s (native01 s l m hv hw) : ClosedRing s) * generator s (1,m) hw = generator s (0,l) hv := by
  apply HomogeneousLocalization.val_injective
  rw [val_mul]
  apply ((closedCoordinateValue_isUnit s (0,l) hv).pow 2).mul_right_cancel
  have hn := congrArg (fun u : (ThickCone s)ˣ => ordinaryReduction s (u : ThickCone s))
    (native01_mul s l m hv hw)
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, valueUnit_value, coordinateUnit_value,
    map_mul, map_pow, ordinaryReduction_val, reduction_coordinateValue] at hn
  change (nativeReduction s (native01 s l m hv hw : ThickRing s)).val *
    (generator s (1,m) hw).val * closedCoordinateValue s (0,l) ^ 2 = _
  calc
    (nativeReduction s (native01 s l m hv hw : ThickRing s)).val *
        (generator s (1,m) hw).val * closedCoordinateValue s (0,l) ^ 2 =
      (generator s (1,m) hw).val *
        ((nativeReduction s (native01 s l m hv hw : ThickRing s)).val * closedCoordinateValue s (0,l) ^ 2) := by ring
    _ = (generator s (1,m) hw).val *
        (ordinaryReduction s (transportedUnit s {0,1} (admits_pair s (0,l) (1,m) hv hw) lifted01 : ThickCone s) * closedCoordinateValue s (1,m) ^ 2) := by rw [hn]
    _ = ordinaryReduction s (transportedUnit s {0,1} (admits_pair s (0,l) (1,m) hv hw) lifted01 : ThickCone s) *
        ((generator s (1,m) hw).val * closedCoordinateValue s (1,m) ^ 2) := by ring
    _ = ordinaryReduction s (transportedUnit s {0,1} (admits_pair s (0,l) (1,m) hv hw) lifted01 : ThickCone s) *
        closedPolynomial s (originalF1 57) := by
      rw [generator_second_mul]
      rfl
    _ = closedPolynomial s originalF2 := reduced_lifted01_generator s l m hv hw
    _ = (generator s (0,l) hv).val * closedCoordinateValue s (0,l) ^ 2 :=
      (generator_first_mul s l hv).symm

theorem native02_generator (s : Finset Vertex) (l m : Fin 3)
    (hv : (0,l) ∈ s) (hw : (2,m) ∈ s) :
    (reduceUnit s (native02 s l m hv hw) : ClosedRing s) * generator s (2,m) hw = generator s (0,l) hv := by
  rw [generator_third, mul_one]
  change nativeReduction s (normalizedConeUnit s (0,l) hv (cartierElement 3)
    (cartierElement_homogeneous 3) _ _ : ThickRing s) = _
  rw [normalizedConeUnit_value]
  exact reduced_normalized_first_generator s l hv

theorem native03_generator (s : Finset Vertex) (l m : Fin 3)
    (hv : (0,l) ∈ s) (hw : (3,m) ∈ s) :
    (reduceUnit s (native03 s l m hv hw) : ClosedRing s) * generator s (3,m) hw = generator s (0,l) hv := by
  rw [generator_fourth, mul_one]
  change nativeReduction s (normalizedConeUnit s (0,l) hv (cartierElement 3)
    (cartierElement_homogeneous 3) (cartierUnit s 3 ⟨m,hw⟩) (cartierUnit_value s 3 ⟨m,hw⟩) : ThickRing s) = _
  rw [normalizedConeUnit_value]
  exact reduced_normalized_first_generator s l hv

theorem native12_generator (s : Finset Vertex) (l m : Fin 3)
    (hv : (1,l) ∈ s) (hw : (2,m) ∈ s) :
    (reduceUnit s (native12 s l m hv hw) : ClosedRing s) * generator s (2,m) hw = generator s (1,l) hv := by
  rw [generator_third, mul_one]
  change nativeReduction s (normalizedConeUnit s (1,l) hv (cartierElement 2)
    (cartierElement_homogeneous 2) (cartierUnit s 2 ⟨m,hw⟩) (cartierUnit_value s 2 ⟨m,hw⟩) : ThickRing s) = _
  rw [normalizedConeUnit_value]
  exact reduced_normalized_second_generator s l hv

theorem native13_generator (s : Finset Vertex) (l m : Fin 3)
    (hv : (1,l) ∈ s) (hw : (3,m) ∈ s) :
    (reduceUnit s (native13 s l m hv hw) : ClosedRing s) * generator s (3,m) hw = generator s (1,l) hv := by
  rw [generator_fourth, mul_one]
  change nativeReduction s (normalizedConeUnit s (1,l) hv (cartierElement 2)
    (cartierElement_homogeneous 2) _ _ : ThickRing s) = _
  rw [normalizedConeUnit_value]
  exact reduced_normalized_second_generator s l hv

theorem native23_generator (s : Finset Vertex) (l m : Fin 3)
    (hv : (2,l) ∈ s) (hw : (3,m) ∈ s) :
    (reduceUnit s (native23 s) : ClosedRing s) * generator s (3,m) hw = generator s (2,l) hv := by
  rw [generator_fourth, generator_third]
  change nativeReduction s 1 * 1 = 1
  rw [map_one, one_mul]

theorem coordinate_change_generator (s : Finset Vertex) (v w : Vertex) (hv : v ∈ s) (hw : w ∈ s)
    (hg : (generator s w hw).val * closedCoordinateValue s w ^ 2 =
      (generator s v hv).val * closedCoordinateValue s v ^ 2) :
    (reduceUnit s (coordinateRatio s v w hv hw ^ 2) : ClosedRing s) * generator s w hw = generator s v hv := by
  apply HomogeneousLocalization.val_injective
  rw [val_mul]
  apply ((closedCoordinateValue_isUnit s v hv).pow 2).mul_right_cancel
  have hc := congrArg (fun u : (ThickCone s)ˣ => ordinaryReduction s (u : ThickCone s))
    (congrArg (fun u : (ThickCone s)ˣ => u ^ 2) (coordinateRatio_mul s v w hv hw))
  simp only [Units.val_pow_eq_pow_val, Units.val_mul, valueUnit_value, coordinateUnit_value,
    map_pow, map_mul, ordinaryReduction_val, reduction_coordinateValue, mul_pow] at hc
  change (nativeReduction s (↑(coordinateRatio s v w hv hw ^ 2) : ThickRing s)).val *
    (generator s w hw).val * closedCoordinateValue s v ^ 2 = _
  have hp : (nativeReduction s (↑(coordinateRatio s v w hv hw ^ 2) : ThickRing s)).val *
      closedCoordinateValue s v ^ 2 = closedCoordinateValue s w ^ 2 := by
    simpa only [Units.val_pow_eq_pow_val, map_pow, val_pow] using hc
  calc
    (nativeReduction s (↑(coordinateRatio s v w hv hw ^ 2) : ThickRing s)).val *
        (generator s w hw).val * closedCoordinateValue s v ^ 2 =
      (generator s w hw).val * ((nativeReduction s
        (↑(coordinateRatio s v w hv hw ^ 2) : ThickRing s)).val * closedCoordinateValue s v ^ 2) := by ring
    _ = (generator s w hw).val * closedCoordinateValue s w ^ 2 := by rw [hp]
    _ = (generator s v hv).val * closedCoordinateValue s v ^ 2 := hg

def nativeTransition (s : Finset Vertex) (v w : Vertex) (hv : v ∈ s) (hw : w ∈ s) : (ThickRing s)ˣ := by
  rcases v with ⟨a,l⟩
  rcases w with ⟨b,m⟩
  refine CycleQ2FourToFiniteCech.fourCases
    (P := fun a => ∀ b : Fin 4, (a,l) ∈ s → (b,m) ∈ s → (ThickRing s)ˣ)
    ?_ ?_ ?_ ?_ a b hv hw
  · intro b
    refine CycleQ2FourToFiniteCech.fourCases
      (P := fun b => (0,l) ∈ s → (b,m) ∈ s → (ThickRing s)ˣ) ?_ ?_ ?_ ?_ b
    · intro hv hw
      exact coordinateRatio s (0,l) (0,m) hv hw ^ 2
    · intro hv hw
      exact native01 s l m hv hw
    · intro hv hw
      exact native02 s l m hv hw
    · intro hv hw
      exact native03 s l m hv hw
  · intro b
    refine CycleQ2FourToFiniteCech.fourCases
      (P := fun b => (1,l) ∈ s → (b,m) ∈ s → (ThickRing s)ˣ) ?_ ?_ ?_ ?_ b
    · intro hv hw
      exact (native01 s m l hw hv)⁻¹
    · intro hv hw
      exact coordinateRatio s (1,l) (1,m) hv hw ^ 2
    · intro hv hw
      exact native12 s l m hv hw
    · intro hv hw
      exact native13 s l m hv hw
  · intro b
    refine CycleQ2FourToFiniteCech.fourCases
      (P := fun b => (2,l) ∈ s → (b,m) ∈ s → (ThickRing s)ˣ) ?_ ?_ ?_ ?_ b
    · intro hv hw
      exact (native02 s m l hw hv)⁻¹
    · intro hv hw
      exact (native12 s m l hw hv)⁻¹
    · intro hv hw
      exact 1
    · intro hv hw
      exact native23 s
  · intro b
    refine CycleQ2FourToFiniteCech.fourCases
      (P := fun b => (3,l) ∈ s → (b,m) ∈ s → (ThickRing s)ˣ) ?_ ?_ ?_ ?_ b
    · intro hv hw
      exact (native03 s m l hw hv)⁻¹
    · intro hv hw
      exact (native13 s m l hw hv)⁻¹
    · intro hv hw
      exact (native23 s)⁻¹
    · intro hv hw
      exact 1

def transition (s : Finset Vertex) (v w : Vertex) (hv : v ∈ s) (hw : w ∈ s) : (ClosedRing s)ˣ :=
  reduceUnit s (nativeTransition s v w hv hw)

theorem inverse_generator {R : Type*} [CommRing R] (u : Rˣ) (p q : R) (h : (u : R) * p = q) :
    (↑(u⁻¹) : R) * q = p := by
  rw [← h, ← mul_assoc, Units.inv_mul, one_mul]

theorem transition_generator (s : Finset Vertex) (v w : Vertex) (hv : v ∈ s) (hw : w ∈ s) :
    (transition s v w hv hw : ClosedRing s) * generator s w hw = generator s v hv := by
  rcases v with ⟨a,l⟩
  rcases w with ⟨b,m⟩
  fin_cases a <;> fin_cases b
  · apply coordinate_change_generator s (0,l) (0,m) hv hw
    rw [generator_first_mul, generator_first_mul]
  · exact native01_generator s l m hv hw
  · exact native02_generator s l m hv hw
  · exact native03_generator s l m hv hw
  · change (reduceUnit s ((native01 s m l hw hv)⁻¹) : ClosedRing s) * _ = _
    rw [map_inv]
    exact inverse_generator _ _ _ (native01_generator s m l hw hv)
  · apply coordinate_change_generator s (1,l) (1,m) hv hw
    rw [generator_second_mul, generator_second_mul]
  · exact native12_generator s l m hv hw
  · exact native13_generator s l m hv hw
  · change (reduceUnit s ((native02 s m l hw hv)⁻¹) : ClosedRing s) * _ = _
    rw [map_inv]
    exact inverse_generator _ _ _ (native02_generator s m l hw hv)
  · change (reduceUnit s ((native12 s m l hw hv)⁻¹) : ClosedRing s) * _ = _
    rw [map_inv]
    exact inverse_generator _ _ _ (native12_generator s m l hw hv)
  · change (reduceUnit s 1 : ClosedRing s) * _ = _
    rw [map_one, Units.val_one, one_mul]
    change generator s (2,m) hw = generator s (2,l) hv
    rw [generator_third s m hw, generator_third s l hv]
  · exact native23_generator s l m hv hw
  · change (reduceUnit s ((native03 s m l hw hv)⁻¹) : ClosedRing s) * _ = _
    rw [map_inv]
    exact inverse_generator _ _ _ (native03_generator s m l hw hv)
  · change (reduceUnit s ((native13 s m l hw hv)⁻¹) : ClosedRing s) * _ = _
    rw [map_inv]
    exact inverse_generator _ _ _ (native13_generator s m l hw hv)
  · change (reduceUnit s ((native23 s)⁻¹) : ClosedRing s) * _ = _
    rw [map_inv]
    exact inverse_generator _ _ _ (native23_generator s m l hw hv)
  · change (reduceUnit s 1 : ClosedRing s) * _ = _
    rw [map_one, Units.val_one, one_mul]
    change generator s (3,m) hw = generator s (3,l) hv
    rw [generator_fourth s m hw, generator_fourth s l hv]

theorem transition_cocycle (s : Finset Vertex) (v w z : Vertex)
    (hv : v ∈ s) (hw : w ∈ s) (hz : z ∈ s) :
    transition s v w hv hw * transition s w z hw hz = transition s v z hv hz := by
  apply Units.ext
  apply generator_regular s z hz
  change generator s z hz * ((transition s v w hv hw : ClosedRing s) *
    (transition s w z hw hz : ClosedRing s)) = generator s z hz * (transition s v z hv hz : ClosedRing s)
  calc
    generator s z hz * ((transition s v w hv hw : ClosedRing s) *
        (transition s w z hw hz : ClosedRing s)) =
      (transition s v w hv hw : ClosedRing s) * ((transition s w z hw hz : ClosedRing s) * generator s z hz) := by ring
    _ = (transition s v w hv hw : ClosedRing s) * generator s w hw := by rw [transition_generator]
    _ = generator s v hv := transition_generator s v w hv hw
    _ = generator s z hz * (transition s v z hv hz : ClosedRing s) := by
      rw [mul_comm, transition_generator]

end CycleQ2LiteralNativeCartierTransitions

end

#print axioms CycleQ2LiteralNativeCartierTransitions.reduced_lifted01_generator
#print axioms CycleQ2LiteralNativeCartierTransitions.transition_generator
#print axioms CycleQ2LiteralNativeCartierTransitions.transition_cocycle
