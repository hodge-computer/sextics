import Proposal.GeometricLiteralNativeCartierTransitions

/-!
# Restriction of the original native Cartier transitions

The explicit normalized fractions, all six original forward lifts,
their oriented extensions, and the original Cartier generators commute
with the actual native structure-sheaf restrictions. Consequently the
closed transitions form the genuine compatible multiplicative cocycle
of the original inverse-ideal frames on the refined cover.

Prepared for fqlx with OpenAI ChatGPT assistance; see solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralNativeTransitionNaturality

open HomogeneousLocalization CycleQ2CartierSurfaceGrading
  CycleQ2LiteralGradedDeformation CycleQ2LiteralProjectiveDeformation
  CycleQ2LiteralProjectiveIntersections CycleQ2LiteralProjectiveIntersectionRestrictions
  CycleQ2LiteralProjectiveIntersectionSplittings CycleQ2LiteralNativeHomogeneousFractions
  CycleQ2LiteralNativeTransitionUnits CycleQ2LiteralNativeCartierFrames
  CycleQ2LiteralNativeCartierTransitions

def restrictThickUnit {s t : Finset Vertex} (hst : s ⊆ t) : (ThickRing s)ˣ →* (ThickRing t)ˣ :=
  Units.map (thickRestriction hst).toMonoidHom

def restrictClosedUnit {s t : Finset Vertex} (hst : s ⊆ t) : (ClosedRing s)ˣ →* (ClosedRing t)ˣ :=
  Units.map (closedRestriction hst).toMonoidHom

theorem restrictThickUnit_neg {s t : Finset Vertex} (hst : s ⊆ t) (u : (ThickRing s)ˣ) :
    restrictThickUnit hst (-u) = -restrictThickUnit hst u := mapUnit_neg (thickRestriction hst) u

theorem normalizedConeUnit_restrict {s t : Finset Vertex} (hst : s ⊆ t) (v : Vertex) (hv : v ∈ s)
    {k : ℕ} (p : GradedDeformation) (hp : p ∈ deformationGrade k)
    (u : (ThickCone s)ˣ) (hu : (u : ThickCone s) = algebraMap GradedDeformation (ThickCone s) p)
    (u' : (ThickCone t)ˣ) (hu' : (u' : ThickCone t) = algebraMap GradedDeformation (ThickCone t) p) :
    restrictThickUnit hst (normalizedConeUnit s v hv p hp u hu) =
      normalizedConeUnit t v (hst hv) p hp u' hu' := by
  apply Units.ext
  change thickRestriction hst (normalizedConeUnit s v hv p hp u hu : ThickRing s) =
    (normalizedConeUnit t v (hst hv) p hp u' hu' : ThickRing t)
  rw [normalizedConeUnit_value, normalizedConeUnit_value, normalized_restrict]

theorem coordinateRatio_restrict {s t : Finset Vertex} (hst : s ⊆ t)
    (v w : Vertex) (hv : v ∈ s) (hw : w ∈ s) :
    restrictThickUnit hst (coordinateRatio s v w hv hw) = coordinateRatio t v w (hst hv) (hst hw) :=
  normalizedConeUnit_restrict hst v hv (coordinateElement w.2) (coordinateElement_homogeneous w.2)
    (coordinateUnit s w hw) (coordinateUnit_value s w hw)
    (coordinateUnit t w (hst hw)) (coordinateUnit_value t w (hst hw))

theorem normalizedCartierUnit_restrict {s t : Finset Vertex} (hst : s ⊆ t)
    (v : Vertex) (hv : v ∈ s) (a : Fin 4) (ha : Admissible s a) :
    restrictThickUnit hst (normalizedCartierUnit s v hv a ha) =
      normalizedCartierUnit t v (hst hv) a (admissible_mono hst ha) :=
  normalizedConeUnit_restrict hst v hv (cartierElement a) (cartierElement_homogeneous a)
    (cartierUnit s a ha) (cartierUnit_value s a ha)
    (cartierUnit t a (admissible_mono hst ha)) (cartierUnit_value t a (admissible_mono hst ha))

theorem native01_restrict {s t : Finset Vertex} (hst : s ⊆ t) (l m : Fin 3)
    (hv : (0,l) ∈ s) (hw : (1,m) ∈ s) :
    restrictThickUnit hst (native01 s l m hv hw) = native01 t l m (hst hv) (hst hw) := by
  change restrictThickUnit hst (-(normalizedCartierUnit s (0,l) hv 0 ⟨l,hv⟩) *
    (normalizedCartierUnit s (0,l) hv 1 ⟨m,hw⟩)⁻¹ * coordinateRatio s (0,l) (1,m) hv hw ^ 2) =
    -(normalizedCartierUnit t (0,l) (hst hv) 0 ⟨l,hst hv⟩) *
    (normalizedCartierUnit t (0,l) (hst hv) 1 ⟨m,hst hw⟩)⁻¹ *
      coordinateRatio t (0,l) (1,m) (hst hv) (hst hw) ^ 2
  rw [map_mul, map_mul, map_inv, map_pow, restrictThickUnit_neg,
    normalizedCartierUnit_restrict, normalizedCartierUnit_restrict, coordinateRatio_restrict]

theorem native02_restrict {s t : Finset Vertex} (hst : s ⊆ t) (l m : Fin 3)
    (hv : (0,l) ∈ s) (hw : (2,m) ∈ s) :
    restrictThickUnit hst (native02 s l m hv hw) = native02 t l m (hst hv) (hst hw) :=
  normalizedConeUnit_restrict hst (0,l) hv (cartierElement 3) (cartierElement_homogeneous 3)
    _ _ _ _

theorem native03_restrict {s t : Finset Vertex} (hst : s ⊆ t) (l m : Fin 3)
    (hv : (0,l) ∈ s) (hw : (3,m) ∈ s) :
    restrictThickUnit hst (native03 s l m hv hw) = native03 t l m (hst hv) (hst hw) :=
  normalizedCartierUnit_restrict hst (0,l) hv 3 ⟨m,hw⟩

theorem native12_restrict {s t : Finset Vertex} (hst : s ⊆ t) (l m : Fin 3)
    (hv : (1,l) ∈ s) (hw : (2,m) ∈ s) :
    restrictThickUnit hst (native12 s l m hv hw) = native12 t l m (hst hv) (hst hw) :=
  normalizedCartierUnit_restrict hst (1,l) hv 2 ⟨m,hw⟩

theorem native13_restrict {s t : Finset Vertex} (hst : s ⊆ t) (l m : Fin 3)
    (hv : (1,l) ∈ s) (hw : (3,m) ∈ s) :
    restrictThickUnit hst (native13 s l m hv hw) = native13 t l m (hst hv) (hst hw) :=
  normalizedConeUnit_restrict hst (1,l) hv (cartierElement 2) (cartierElement_homogeneous 2)
    _ _ _ _

theorem nativeTransition_restrict {s t : Finset Vertex} (hst : s ⊆ t)
    (v w : Vertex) (hv : v ∈ s) (hw : w ∈ s) :
    restrictThickUnit hst (nativeTransition s v w hv hw) =
      nativeTransition t v w (hst hv) (hst hw) := by
  rcases v with ⟨a,l⟩
  rcases w with ⟨b,m⟩
  fin_cases a <;> fin_cases b
  · change restrictThickUnit hst (coordinateRatio s (0,l) (0,m) hv hw ^ 2) = coordinateRatio t (0,l) (0,m) (hst hv) (hst hw) ^ 2
    rw [map_pow, coordinateRatio_restrict]
  · change restrictThickUnit hst (native01 s l m hv hw) = native01 t l m (hst hv) (hst hw)
    rw [native01_restrict]
  · change restrictThickUnit hst (native02 s l m hv hw) = native02 t l m (hst hv) (hst hw)
    rw [native02_restrict]
  · change restrictThickUnit hst (native03 s l m hv hw) = native03 t l m (hst hv) (hst hw)
    rw [native03_restrict]
  · change restrictThickUnit hst ((native01 s m l hw hv)⁻¹) = (native01 t m l (hst hw) (hst hv))⁻¹
    rw [map_inv, native01_restrict]
  · change restrictThickUnit hst (coordinateRatio s (1,l) (1,m) hv hw ^ 2) = coordinateRatio t (1,l) (1,m) (hst hv) (hst hw) ^ 2
    rw [map_pow, coordinateRatio_restrict]
  · change restrictThickUnit hst (native12 s l m hv hw) = native12 t l m (hst hv) (hst hw)
    rw [native12_restrict]
  · change restrictThickUnit hst (native13 s l m hv hw) = native13 t l m (hst hv) (hst hw)
    rw [native13_restrict]
  · change restrictThickUnit hst ((native02 s m l hw hv)⁻¹) = (native02 t m l (hst hw) (hst hv))⁻¹
    rw [map_inv, native02_restrict]
  · change restrictThickUnit hst ((native12 s m l hw hv)⁻¹) = (native12 t m l (hst hw) (hst hv))⁻¹
    rw [map_inv, native12_restrict]
  · change restrictThickUnit hst (1) = 1
    rw [map_one]
  · change restrictThickUnit hst (1) = 1
    rw [map_one]
  · change restrictThickUnit hst ((native03 s m l hw hv)⁻¹) = (native03 t m l (hst hw) (hst hv))⁻¹
    rw [map_inv, native03_restrict]
  · change restrictThickUnit hst ((native13 s m l hw hv)⁻¹) = (native13 t m l (hst hw) (hst hv))⁻¹
    rw [map_inv, native13_restrict]
  · change restrictThickUnit hst (1) = 1
    rw [map_one]
  · change restrictThickUnit hst (1) = 1
    rw [map_one]

theorem generator_restrict {s t : Finset Vertex} (hst : s ⊆ t) (v : Vertex) (hv : v ∈ s) :
    closedRestriction hst (generator s v hv) = generator t v (hst hv) := by
  rcases v with ⟨a,l⟩
  fin_cases a
  · change closedRestriction hst (generator s (0,l) hv) = generator t (0,l) (hst hv)
    rw [← reduced_normalized_first_generator s l hv, ← nativeReduction_restrict,
      normalized_restrict, reduced_normalized_first_generator]
  · change closedRestriction hst (generator s (1,l) hv) = generator t (1,l) (hst hv)
    rw [← reduced_normalized_second_generator s l hv, ← nativeReduction_restrict,
      normalized_restrict, reduced_normalized_second_generator]
  · change closedRestriction hst (generator s (2,l) hv) = generator t (2,l) (hst hv)
    rw [generator_third s l hv, generator_third t l (hst hv), map_one]
  · change closedRestriction hst (generator s (3,l) hv) = generator t (3,l) (hst hv)
    rw [generator_fourth s l hv, generator_fourth t l (hst hv), map_one]

theorem transition_restrict {s t : Finset Vertex} (hst : s ⊆ t)
    (v w : Vertex) (hv : v ∈ s) (hw : w ∈ s) :
    restrictClosedUnit hst (transition s v w hv hw) = transition t v w (hst hv) (hst hw) := by
  apply Units.ext
  change closedRestriction hst (nativeReduction s (nativeTransition s v w hv hw : ThickRing s)) =
    nativeReduction t (nativeTransition t v w (hst hv) (hst hw) : ThickRing t)
  rw [← nativeReduction_restrict]
  exact congrArg (fun u : (ThickRing t)ˣ => nativeReduction t (u : ThickRing t))
    (nativeTransition_restrict hst v w hv hw)

theorem transition_self (s : Finset Vertex) (v : Vertex) (hv : v ∈ s) : transition s v v hv hv = 1 := by
  apply Units.ext
  apply generator_regular s v hv
  change generator s v hv * (transition s v v hv hv : ClosedRing s) = generator s v hv * 1
  rw [mul_comm, transition_generator, mul_one]

theorem transition_reverse (s : Finset Vertex) (v w : Vertex) (hv : v ∈ s) (hw : w ∈ s) :
    transition s w v hw hv = (transition s v w hv hw)⁻¹ := by
  have h := transition_cocycle s v w v hv hw hv
  rw [transition_self] at h
  exact eq_inv_of_mul_eq_one_left
    ((mul_comm (transition s w v hw hv) (transition s v w hv hw)).trans h)

end CycleQ2LiteralNativeTransitionNaturality

end

#print axioms CycleQ2LiteralNativeTransitionNaturality.nativeTransition_restrict
#print axioms CycleQ2LiteralNativeTransitionNaturality.generator_restrict
#print axioms CycleQ2LiteralNativeTransitionNaturality.transition_restrict
#print axioms CycleQ2LiteralNativeTransitionNaturality.transition_self
#print axioms CycleQ2LiteralNativeTransitionNaturality.transition_reverse
