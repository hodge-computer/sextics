import Proposal.CanonicalFractionCoordinates
import Proposal.SymmetricPiolaTransport
import Proposal.WeightedPrimitiveTransport
import Proposal.SymmetricAffineJacobian

/-!
# A concrete ambient field for the reflection-chart transport

The six independent field coordinates are `(a,lambda,b,c,d,v)`.
The original polynomial ring is embedded by its actual reflection chart;
the inverse Jacobian constructs compatible original-coordinate derivations.
All coordinate and coefficient rules are proved for the canonical fraction
field. No existence of a relative primitive is used here.
-/

noncomputable section

namespace SymmetricChartField

open MvPolynomial HoldoutConstruction SymmetricPiolaTransport
open scoped BigOperators

set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

abbrev Ambient := HodgeComputer.AmbientPoly 5
abbrev Poly := WeightedPrimitiveTransport.Poly
abbrev K := CanonicalFractionCoordinates.RationalFunctionField 5

def embed : Ambient →+* K := algebraMap Ambient K
def coefficientMap : ℂ →+* K := embed.comp C
def x (i : Fin 6) : K := embed (X i)
def delta (i : Fin 6) : Derivation ℤ K K :=
  (CanonicalFractionCoordinates.coordinateDerivative 5 i).restrictScalars ℤ

theorem embed_injective : Function.Injective embed := IsFractionRing.injective _ _

@[simp] theorem delta_embed (i : Fin 6) (p : Ambient) :
    delta i (embed p) = embed (pderiv i p) :=
  CanonicalFractionCoordinates.coordinateDerivative_polynomial 5 i p

@[simp] theorem delta_coefficient (i : Fin 6) (c : ℂ) :
    delta i (coefficientMap c) = 0 := by
  simp [coefficientMap]

theorem delta_coordinate (i j : Fin 6) :
    delta i (x j) = if i = j then 1 else 0 := by
  simp [x, pderiv_X, Pi.single_apply, eq_comm]

theorem coordinate_ne_zero (i : Fin 6) : x i ≠ 0 := by
  intro h
  have hz : (X i : Ambient) = 0 := embed_injective (by simpa [x] using h)
  exact (X_ne_zero i) hz

/-- Embed the five affine variables, in the prescribed order, after `a`. -/
def affineMap : Poly →+* K := embed.comp (rename Fin.succ).toRingHom

@[simp] theorem affineMap_C (c : ℂ) : affineMap (C c) = coefficientMap c := by
  simp [affineMap, coefficientMap]

@[simp] theorem affineMap_X (i : Fin 5) : affineMap (X i) = x i.succ := by
  simp [affineMap, x]

theorem affineMap_as_eval :
    affineMap = eval₂Hom coefficientMap (fun i : Fin 5 => x i.succ) := by
  ext i <;> simp

theorem affineMap_injective : Function.Injective affineMap := by
  rw [affineMap_as_eval]
  apply ResidueCoordinateIndependence.injective_of_coordinate_derivations
    coefficientMap (fun i : Fin 5 => x i.succ) (fun i => delta i.succ)
  · exact fun i c => delta_coefficient i.succ c
  · intro i j
    simp [delta_coordinate, eq_comm]

@[simp] theorem delta_affineMap (i : Fin 5) (p : Poly) :
    delta i.succ (affineMap p) = affineMap (pderiv i p) := by
  change delta i.succ (embed (rename Fin.succ p)) =
    embed (rename Fin.succ (pderiv i p))
  rw [delta_embed, pderiv_rename (Fin.succ_injective 5)]

def physicalMap : Ambient →+* K := eval₂Hom coefficientMap (chartCoordinates x)
def theta : Fin 6 → Derivation ℤ K K :=
  physicalDerivative delta (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)

theorem physicalMap_injective : Function.Injective physicalMap :=
  physicalPolynomialMap_injective coefficientMap delta x delta_coefficient
    delta_coordinate (coordinate_ne_zero 0) (coordinate_ne_zero 5)

@[simp] theorem theta_physicalMap (i : Fin 6) (p : Ambient) :
    theta i (physicalMap p) = physicalMap (pderiv i p) :=
  physicalPolynomialMap_compatible coefficientMap delta x delta_coefficient
    delta_coordinate (coordinate_ne_zero 0) (coordinate_ne_zero 5) i p

@[simp] theorem physicalMap_C (c : ℂ) : physicalMap (C c) = coefficientMap c := by
  simp [physicalMap]

@[simp] theorem physicalMap_X (i : Fin 6) : physicalMap (X i) = chartCoordinates x i := by
  simp [physicalMap]

/-- The exact protected equation, not an abstract homogeneous placeholder. -/
theorem physicalMap_F : physicalMap HodgeSubmission.F =
    (x 0)^6 * affineMap WeightedPrimitiveTransport.chartEquation := by
  rw [SymmetricReflections.exactF_compact]
  simp [SymmetricReflections.compactF, SymmetricReflections.QX, SymmetricReflections.QY,
    WeightedPrimitiveTransport.chartEquation, WeightedPrimitiveTransport.rawWeighted,
    WeightedPrimitiveTransport.leftQuadric, WeightedPrimitiveTransport.rightQuadric,
    WeightedPrimitiveTransport.squareLift, chartCoordinates, map_ofNat]
  ring

/-- The extra `4v` is the projective volume factor. -/
theorem physicalMap_A : 4*x 5*physicalMap HodgeSubmission.A =
    (x 0)^6 * affineMap WeightedPrimitiveTransport.chartSource := by
  rw [SymmetricReflections.exactA_compact]
  simp [SymmetricReflections.compactA, WeightedPrimitiveTransport.chartSource,
    WeightedPrimitiveTransport.reflectedSource, WeightedPrimitiveTransport.rawSource,
    WeightedPrimitiveTransport.squareLift, chartCoordinates, map_ofNat]
  ring

section Quotients

variable {σ : Type*} [Fintype σ]
variable (φ : MvPolynomial σ ℂ →+* K) (E : σ → Derivation ℤ K K)
variable (compatible : ∀ i p, E i (φ p) = φ (pderiv i p))

include compatible

theorem quotient_contraction (D F : MvPolynomial σ ℂ)
    (N : σ → MvPolynomial σ ℂ) :
    (∑ i, (φ (N i)/φ D)*E i (φ F)) = φ (HodgeTestbed.directional F N)/φ D := by
  simp only [compatible, HodgeTestbed.directional, map_sum, map_mul, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem quotient_divergence (D : MvPolynomial σ ℂ) (N : σ → MvPolynomial σ ℂ) :
    fieldDivergence E (fun i => φ (N i)/φ D) =
      φ (HodgeTestbed.divergenceNumerator D N)/(φ D)^2 := by
  simp only [fieldDivergence, Derivation.leibniz_div, compatible, smul_eq_mul,
    ]
  rw [← Finset.mul_sum]
  have hs : (∑ i, (φ D*φ (pderiv i (N i))-φ (N i)*φ (pderiv i D))) =
      φ (HodgeTestbed.divergenceNumerator D N) := by
    simp only [HodgeTestbed.divergenceNumerator, HodgeTestbed.divergence,
      HodgeTestbed.directional, map_sub, map_mul, map_sum, Finset.mul_sum,
      Finset.sum_sub_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hs]
  simp only [div_eq_mul_inv, inv_pow]
  ring

end Quotients

/-- Exact normalized affine polynomial equations give the corresponding
field equations in this canonical six-coordinate ambient field. -/
theorem affine_current_equations
    (D H AH Q : Poly) (N : Fin 5 → Poly) (hD : D ≠ 0)
    (hnormal : HodgeTestbed.directional H N = AH*D)
    (hdiv : HodgeTestbed.divergenceNumerator D N = H*Q) :
    (∑ i : Fin 5, (affineMap (N i)/affineMap D)*delta i.succ (affineMap H)) =
        affineMap AH ∧
      (∑ i : Fin 5, delta i.succ (affineMap (N i)/affineMap D)) =
        affineMap H * (affineMap Q/(affineMap D)^2) := by
  have hd : affineMap D ≠ 0 := fun h => hD (affineMap_injective (by simpa using h))
  constructor
  · rw [quotient_contraction affineMap (fun i : Fin 5 => delta i.succ)
      delta_affineMap, hnormal, map_mul]
    field_simp
  · change fieldDivergence (fun i : Fin 5 => delta i.succ) _ = _
    rw [quotient_divergence affineMap (fun i : Fin 5 => delta i.succ)
      delta_affineMap, hdiv, map_mul]
    ring

#print axioms physicalMap_injective
#print axioms physicalMap_F
#print axioms physicalMap_A
#print axioms affine_current_equations

end SymmetricChartField
