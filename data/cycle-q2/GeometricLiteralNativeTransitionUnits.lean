import Proposal.GeometricLiteralNativeHomogeneousFractions
import Proposal.GeometricLiteralCartierLiftedTransitions

/-!
# The six original lifted transitions as native projective units

The original cone units are transported through the fixed-coordinate
localization maps. The actual projective frames have degrees 2,2,0,0.
Their transition units include the original coordinate ratios, and the
identities below retain these factors in the ordinary localization.
The complementary quadratic units come from the original equation
F - epsilon B*, rather than a new invertibility hypothesis.

Prepared for fqlx with OpenAI ChatGPT assistance; see solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralNativeTransitionUnits

open HomogeneousLocalization CycleQ2CartierSurfaceGrading
  CycleQ2LiteralGradedDeformation CycleQ2LiteralProjectiveDeformation
  CycleQ2LiteralProjectiveIntersections CycleQ2LiteralProjectiveIntersectionRestrictions
  CycleQ2LiteralProjectiveIntersectionSplittings CycleQ2LiteralConeIntersectionTransport
  CycleQ2LiteralNativeHomogeneousFractions CycleQ2LiteralCartierLiftedTransitions

def valueUnit (s : Finset Vertex) : (ThickRing s)ˣ →* (ThickCone s)ˣ :=
  Units.map (algebraMap (ThickRing s) (ThickCone s)).toMonoidHom

theorem valueUnit_value (s : Finset Vertex) (u : (ThickRing s)ˣ) :
    (valueUnit s u : ThickCone s) = (u : ThickRing s).val := rfl

theorem mapUnit_neg {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (u : Rˣ) : Units.map f.toMonoidHom (-u) = -Units.map f.toMonoidHom u := by
  apply Units.ext
  exact map_neg f (u : R)

theorem valueUnit_neg (s : Finset Vertex) (u : (ThickRing s)ˣ) :
    valueUnit s (-u) = -valueUnit s u :=
  mapUnit_neg (algebraMap (ThickRing s) (ThickCone s)) u

def transportedUnit (s : Finset Vertex) (t : Finset (Fin 4)) (ht : Admits s t)
    (u : (OldThick t)ˣ) : (ThickCone s)ˣ := Units.map (thickMap s t ht).toMonoidHom u

theorem transportedUnit_value (s : Finset Vertex) (t : Finset (Fin 4)) (ht : Admits s t)
    (u : (OldThick t)ˣ) : (transportedUnit s t ht u : ThickCone s) = thickMap s t ht (u : OldThick t) := rfl

def cartierUnit (s : Finset Vertex) (a : Fin 4) (ha : Admissible s a) : (ThickCone s)ˣ :=
  (IsLocalization.Away.isUnit_of_dvd (S := ThickCone s) (thickProduct s) (thickCartier_dvd ha)).unit

theorem cartierUnit_value (s : Finset Vertex) (a : Fin 4) (ha : Admissible s a) :
    (cartierUnit s a ha : ThickCone s) = algebraMap GradedDeformation (ThickCone s) (cartierElement a) :=
  IsUnit.unit_spec _

theorem transported_covered (s : Finset Vertex) (t : Finset (Fin 4)) (ht : Admits s t)
    (a : Fin 4) (ha : a ∈ t) :
    transportedUnit s t ht (coveredUnit t a ha) = cartierUnit s a (ht a ha) := by
  apply Units.ext
  rw [transportedUnit_value, coveredUnit_value, thickMap_polynomial, cartierUnit_value]
  rfl

def normalizedConeUnit (s : Finset Vertex) (v : Vertex) (hv : v ∈ s)
    {k : ℕ} (p : GradedDeformation) (hp : p ∈ deformationGrade k)
    (u : (ThickCone s)ˣ) (hu : (u : ThickCone s) = algebraMap GradedDeformation (ThickCone s) p) :
    (ThickRing s)ˣ :=
  normalizedUnit s v hv p hp (hu ▸ u.isUnit)

theorem normalizedConeUnit_mul (s : Finset Vertex) (v : Vertex) (hv : v ∈ s)
    {k : ℕ} (p : GradedDeformation) (hp : p ∈ deformationGrade k)
    (u : (ThickCone s)ˣ) (hu : (u : ThickCone s) = algebraMap GradedDeformation (ThickCone s) p) :
    valueUnit s (normalizedConeUnit s v hv p hp u hu) * coordinateUnit s v hv ^ k = u := by
  apply Units.ext
  change (normalizedConeUnit s v hv p hp u hu : ThickRing s).val *
      (coordinateUnit s v hv : ThickCone s) ^ k = (u : ThickCone s)
  rw [coordinateUnit_value]
  change (normalized s v hv p hp).val * coordinateValue s v ^ k = (u : ThickCone s)
  rw [normalized_val_mul, hu]

def coordinateRatio (s : Finset Vertex) (v w : Vertex) (hv : v ∈ s) (hw : w ∈ s) : (ThickRing s)ˣ :=
  normalizedConeUnit s v hv (coordinateElement w.2) (coordinateElement_homogeneous w.2)
    (coordinateUnit s w hw) (coordinateUnit_value s w hw)

theorem coordinateRatio_mul (s : Finset Vertex) (v w : Vertex) (hv : v ∈ s) (hw : w ∈ s) :
    valueUnit s (coordinateRatio s v w hv hw) * coordinateUnit s v hv = coordinateUnit s w hw := by
  simpa only [coordinateRatio, pow_one] using normalizedConeUnit_mul s v hv
    (coordinateElement w.2) (coordinateElement_homogeneous w.2)
    (coordinateUnit s w hw) (coordinateUnit_value s w hw)

def normalizedCartierUnit (s : Finset Vertex) (v : Vertex) (hv : v ∈ s)
    (a : Fin 4) (ha : Admissible s a) : (ThickRing s)ˣ :=
  normalizedConeUnit s v hv (cartierElement a) (cartierElement_homogeneous a)
    (cartierUnit s a ha) (cartierUnit_value s a ha)

theorem normalizedCartierUnit_mul (s : Finset Vertex) (v : Vertex) (hv : v ∈ s)
    (a : Fin 4) (ha : Admissible s a) :
    valueUnit s (normalizedCartierUnit s v hv a ha) * coordinateUnit s v hv ^ coverDegree a =
      cartierUnit s a ha :=
  normalizedConeUnit_mul s v hv (cartierElement a) (cartierElement_homogeneous a)
    (cartierUnit s a ha) (cartierUnit_value s a ha)

def native01 (s : Finset Vertex) (l m : Fin 3) (hv : (0,l) ∈ s) (hw : (1,m) ∈ s) : (ThickRing s)ˣ :=
  -(normalizedCartierUnit s (0,l) hv 0 ⟨l,hv⟩) *
    (normalizedCartierUnit s (0,l) hv 1 ⟨m,hw⟩)⁻¹ *
    coordinateRatio s (0,l) (1,m) hv hw ^ 2

theorem transported_lifted01 (s : Finset Vertex) (l m : Fin 3)
    (hv : (0,l) ∈ s) (hw : (1,m) ∈ s) :
    transportedUnit s {0,1} (admits_pair s (0,l) (1,m) hv hw) lifted01 =
      -(cartierUnit s 0 ⟨l,hv⟩) * (cartierUnit s 1 ⟨m,hw⟩)⁻¹ := by
  unfold lifted01 CycleQ2GeometricCartierTransitionUnits.transition01 transportedUnit
  rw [map_mul, map_inv, mapUnit_neg]
  change -(transportedUnit s {0,1} _ (coveredUnit {0,1} 0 (by simp))) *
    (transportedUnit s {0,1} _ (coveredUnit {0,1} 1 (by simp)))⁻¹ = _
  rw [transported_covered, transported_covered]

theorem native01_mul (s : Finset Vertex) (l m : Fin 3)
    (hv : (0,l) ∈ s) (hw : (1,m) ∈ s) :
    valueUnit s (native01 s l m hv hw) * coordinateUnit s (0,l) hv ^ 2 =
      transportedUnit s {0,1} (admits_pair s (0,l) (1,m) hv hw) lifted01 *
        coordinateUnit s (1,m) hw ^ 2 := by
  have h0 := normalizedCartierUnit_mul s (0,l) hv 0 ⟨l,hv⟩
  have h1 := normalizedCartierUnit_mul s (0,l) hv 1 ⟨m,hw⟩
  change valueUnit s (normalizedCartierUnit s (0,l) hv 0 ⟨l,hv⟩) *
    coordinateUnit s (0,l) hv ^ 4 = _ at h0
  change valueUnit s (normalizedCartierUnit s (0,l) hv 1 ⟨m,hw⟩) *
    coordinateUnit s (0,l) hv ^ 4 = _ at h1
  have hratio : valueUnit s (normalizedCartierUnit s (0,l) hv 0 ⟨l,hv⟩) *
      (valueUnit s (normalizedCartierUnit s (0,l) hv 1 ⟨m,hw⟩))⁻¹ =
        cartierUnit s 0 ⟨l,hv⟩ * (cartierUnit s 1 ⟨m,hw⟩)⁻¹ := by
    rw [← h0, ← h1, mul_inv_rev]
    simp only [mul_assoc, mul_inv_cancel_left]
  have hsign : valueUnit s (-(normalizedCartierUnit s (0,l) hv 0 ⟨l,hv⟩) *
      (normalizedCartierUnit s (0,l) hv 1 ⟨m,hw⟩)⁻¹) =
        transportedUnit s {0,1} (admits_pair s (0,l) (1,m) hv hw) lifted01 := by
    rw [map_mul, map_inv, valueUnit_neg, neg_mul, hratio,
      transported_lifted01 s l m hv hw, neg_mul]
  change valueUnit s ((-(normalizedCartierUnit s (0,l) hv 0 ⟨l,hv⟩) *
    (normalizedCartierUnit s (0,l) hv 1 ⟨m,hw⟩)⁻¹ *
    coordinateRatio s (0,l) (1,m) hv hw ^ 2)) * coordinateUnit s (0,l) hv ^ 2 = _
  rw [map_mul, map_pow, hsign, mul_assoc, ← mul_pow, coordinateRatio_mul]

theorem transported_lifted02_value (s : Finset Vertex) (l m : Fin 3)
    (hv : (0,l) ∈ s) (hw : (2,m) ∈ s) :
    (transportedUnit s {0,2} (admits_pair s (0,l) (2,m) hv hw) lifted02 : ThickCone s) =
      algebraMap GradedDeformation (ThickCone s) (cartierElement 3) := by
  rw [transportedUnit_value, lifted02_value, thickMap_polynomial]
  rfl

theorem transported_lifted13_value (s : Finset Vertex) (l m : Fin 3)
    (hv : (1,l) ∈ s) (hw : (3,m) ∈ s) :
    (transportedUnit s {1,3} (admits_pair s (1,l) (3,m) hv hw) lifted13 : ThickCone s) =
      algebraMap GradedDeformation (ThickCone s) (cartierElement 2) := by
  rw [transportedUnit_value, lifted13_value, thickMap_polynomial]
  rfl

def native02 (s : Finset Vertex) (l m : Fin 3) (hv : (0,l) ∈ s) (hw : (2,m) ∈ s) : (ThickRing s)ˣ :=
  normalizedConeUnit s (0,l) hv (cartierElement 3) (cartierElement_homogeneous 3)
    (transportedUnit s {0,2} (admits_pair s (0,l) (2,m) hv hw) lifted02)
    (transported_lifted02_value s l m hv hw)

def native03 (s : Finset Vertex) (l m : Fin 3) (hv : (0,l) ∈ s) (hw : (3,m) ∈ s) : (ThickRing s)ˣ :=
  normalizedCartierUnit s (0,l) hv 3 ⟨m,hw⟩

def native12 (s : Finset Vertex) (l m : Fin 3) (hv : (1,l) ∈ s) (hw : (2,m) ∈ s) : (ThickRing s)ˣ :=
  normalizedCartierUnit s (1,l) hv 2 ⟨m,hw⟩

def native13 (s : Finset Vertex) (l m : Fin 3) (hv : (1,l) ∈ s) (hw : (3,m) ∈ s) : (ThickRing s)ˣ :=
  normalizedConeUnit s (1,l) hv (cartierElement 2) (cartierElement_homogeneous 2)
    (transportedUnit s {1,3} (admits_pair s (1,l) (3,m) hv hw) lifted13)
    (transported_lifted13_value s l m hv hw)

def native23 (s : Finset Vertex) : (ThickRing s)ˣ := 1

theorem native02_mul (s : Finset Vertex) (l m : Fin 3)
    (hv : (0,l) ∈ s) (hw : (2,m) ∈ s) :
    valueUnit s (native02 s l m hv hw) * coordinateUnit s (0,l) hv ^ 2 =
      transportedUnit s {0,2} (admits_pair s (0,l) (2,m) hv hw) lifted02 :=
  normalizedConeUnit_mul s (0,l) hv (cartierElement 3) (cartierElement_homogeneous 3)
    (transportedUnit s {0,2} (admits_pair s (0,l) (2,m) hv hw) lifted02)
    (transported_lifted02_value s l m hv hw)

theorem native03_mul (s : Finset Vertex) (l m : Fin 3)
    (hv : (0,l) ∈ s) (hw : (3,m) ∈ s) :
    valueUnit s (native03 s l m hv hw) * coordinateUnit s (0,l) hv ^ 2 =
      transportedUnit s {0,3} (admits_pair s (0,l) (3,m) hv hw) lifted03 := by
  exact (normalizedCartierUnit_mul s (0,l) hv 3 ⟨m,hw⟩).trans
    (transported_covered s {0,3} (admits_pair s (0,l) (3,m) hv hw) 3 (by simp)).symm

theorem native12_mul (s : Finset Vertex) (l m : Fin 3)
    (hv : (1,l) ∈ s) (hw : (2,m) ∈ s) :
    valueUnit s (native12 s l m hv hw) * coordinateUnit s (1,l) hv ^ 2 =
      transportedUnit s {1,2} (admits_pair s (1,l) (2,m) hv hw) lifted12 := by
  exact (normalizedCartierUnit_mul s (1,l) hv 2 ⟨m,hw⟩).trans
    (transported_covered s {1,2} (admits_pair s (1,l) (2,m) hv hw) 2 (by simp)).symm

theorem native13_mul (s : Finset Vertex) (l m : Fin 3)
    (hv : (1,l) ∈ s) (hw : (3,m) ∈ s) :
    valueUnit s (native13 s l m hv hw) * coordinateUnit s (1,l) hv ^ 2 =
      transportedUnit s {1,3} (admits_pair s (1,l) (3,m) hv hw) lifted13 :=
  normalizedConeUnit_mul s (1,l) hv (cartierElement 2) (cartierElement_homogeneous 2)
    (transportedUnit s {1,3} (admits_pair s (1,l) (3,m) hv hw) lifted13)
    (transported_lifted13_value s l m hv hw)

theorem native23_value (s : Finset Vertex) (l m : Fin 3)
    (hv : (2,l) ∈ s) (hw : (3,m) ∈ s) :
    valueUnit s (native23 s) = transportedUnit s {2,3} (admits_pair s (2,l) (3,m) hv hw) lifted23 := by
  exact (map_one _).trans (map_one _).symm

end CycleQ2LiteralNativeTransitionUnits

end

#print axioms CycleQ2LiteralNativeTransitionUnits.native01_mul
#print axioms CycleQ2LiteralNativeTransitionUnits.native02_mul
#print axioms CycleQ2LiteralNativeTransitionUnits.native03_mul
#print axioms CycleQ2LiteralNativeTransitionUnits.native12_mul
#print axioms CycleQ2LiteralNativeTransitionUnits.native13_mul
#print axioms CycleQ2LiteralNativeTransitionUnits.native23_value
