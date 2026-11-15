import Proposal.GeometricSeedProjectiveImageChart

/-!
# The original homogeneous curve in every component of the seed orbit ideal

Source-only continuation: no Lean elaboration or kernel replay has been run
for this file. All statements use the literal seed `(r, theta) = (57, 1)`.

The old chart calculation identifies the first linkage component with the
original curve. Here all three components are identified with the images of
the same original homogeneous curve ideal under the literal polynomial
action, followed by the actual projective dehomogenization. Consequently
the orbit ideal is the product of the three original-curve translates on
every chart. No Chern-class or Abel--Jacobi comparison is assumed or asserted.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2SeedOrbitDivisor

open MvPolynomial
open CycleQ2SeedTrace CycleQ2NormalConnecting CycleQ2ConormalJacobian
  CycleQ2GeometricCartierNormalLift CycleQ2GeometricSurfaceCoordinates
  CycleQ2SegreTangentLocal CycleQ2SeedCechLocalization
  CycleQ2SeedLinkageOrbitCover CycleQ2SeedLinkageComponents
  CycleQ2LinkageComponentDecomposition CycleQ2LinkageComponentAlgebra
  CycleQ2SeedCyclicAction CycleQ2SeedCyclicLocalization
  CycleQ2SeedProjectiveImageChart

/-- The original homogeneous curve ideal, on the original coordinate
localization before passing to the degree-zero projective chart. -/
def originalConeCurveIdeal (i : Fin 3) : Ideal (ConeRing i) :=
  (ambientCurveIdeal 57 1).map (conePolynomial i)

private theorem conePolynomial_cubic (i : Fin 3) :
    conePolynomial i (thetaH 1) = 0 := by
  rw [← coneCoordinateEquiv_polynomial i (thetaH 1), surfaceQuotient_h,
    map_zero, map_zero]

private theorem originalConeCurveIdeal_generators (i : Fin 3) :
    originalConeCurveIdeal i = Ideal.span (Set.range (fun j : Fin 2 =>
      conePolynomial i (![originalF1 57, originalF2] j))) := by
  rw [originalConeCurveIdeal, ambientCurveIdeal, Ideal.map_span, ← Set.range_comp]
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨j, rfl⟩
    fin_cases j
    · exact Ideal.subset_span ⟨0, rfl⟩
    · exact Ideal.subset_span ⟨1, rfl⟩
    · change conePolynomial i (thetaH 1) ∈ _
      rw [conePolynomial_cubic]
      exact Ideal.zero_mem _
  · apply Ideal.span_le.mpr
    rintro _ ⟨j, rfl⟩
    fin_cases j
    · exact Ideal.subset_span ⟨0, rfl⟩
    · exact Ideal.subset_span ⟨1, rfl⟩

/-- Component 1 is the full original homogeneous curve ideal, including
its cubic equation, on the actual cone chart. -/
theorem originalConeCurveIdeal_eq_component_one (i : Fin 3) :
    originalConeCurveIdeal i = localComponent .left (57 : ℂ) Complex.I {i} 1 := by
  let g : Fin 2 → ConeRing i := componentGenerator
    (localScalar (57 : ℂ) Complex.I {i} 1)
    (algebraMap (SeedRing (57 : ℂ) Complex.I) (ConeRing i) (linkageA 57 Complex.I))
    (algebraMap (SeedRing (57 : ℂ) Complex.I) (ConeRing i) (linkageB 57 Complex.I))
    (algebraMap (SeedRing (57 : ℂ) Complex.I) (ConeRing i) (linkageC 57 Complex.I))
    (algebraMap (SeedRing (57 : ℂ) Complex.I) (ConeRing i) (linkageD 57 Complex.I))
  have hg (j : Fin 2) : g j = conePolynomial i (![originalF1 57, originalF2] j) := by
    fin_cases j
    · change conePolynomial i (X 0 ^ 2) -
        localScalar (57 : ℂ) Complex.I {i} 1 *
          conePolynomial i (C 57 * X 1 * X 3) =
        conePolynomial i (X 0 ^ 2 - C 57 * X 1 * X 3)
      rw [map_one, one_mul, map_sub]
    · change conePolynomial i (X 4) +
        (localScalar (57 : ℂ) Complex.I {i} 1) ^ 2 *
          conePolynomial i (X 2 ^ 2) = conePolynomial i (X 4 + X 2 ^ 2)
      rw [map_one, one_pow, one_mul, map_add]
  rw [originalConeCurveIdeal_generators]
  change Ideal.span (Set.range (fun j : Fin 2 =>
      conePolynomial i (![originalF1 57, originalF2] j))) = Ideal.span (Set.range g)
  exact congrArg Ideal.span (congrArg Set.range (funext hg)).symm

/-- An original-curve translate on an actual projective chart. The action
is applied to its homogeneous equations before dehomogenization. -/
def originalCurveTranslateIdeal (i : Fin 3) (z : ℂ) : Ideal (AffineRing i) :=
  (ambientCurveIdeal 57 1).map
    ((affinePolynomial i).comp (polynomialAction z).toRingHom)

theorem coneAction_polynomial (i : Fin 3) (z : ℂ) (hz : z ^ 3 = 1)
    (p : WeightedPoly) :
    localAction z hz (57 : ℂ) Complex.I {i} (conePolynomial i p) =
      conePolynomial i (polynomialAction z p) :=
  localAction_mk z hz (57 : ℂ) Complex.I {i} p

/-- Every linkage component is the actual original curve acted on by the
specified cube root. This is an equality of ideals in the actual affine
projective coordinate ring, not an isomorphism of abstract presentations. -/
theorem originalCurveTranslateIdeal_eq_component (i : Fin 3) (z : ℂ)
    (hz : z ^ 3 = 1) :
    originalCurveTranslateIdeal i z = affineComponentIdeal i z := by
  have hmap : ((coneToChart i).comp
      (localAction z hz (57 : ℂ) Complex.I {i})).comp (conePolynomial i) =
      (affinePolynomial i).comp (polynomialAction z).toRingHom := by
    apply RingHom.ext
    intro p
    change coneToChart i
      (localAction z hz (57 : ℂ) Complex.I {i} (conePolynomial i p)) =
      affinePolynomial i (polynomialAction z p)
    rw [coneAction_polynomial, coneToChart_polynomial]
  calc
    originalCurveTranslateIdeal i z =
        ((originalConeCurveIdeal i).map
          (localAction z hz (57 : ℂ) Complex.I {i})).map (coneToChart i) := by
      rw [originalCurveTranslateIdeal, originalConeCurveIdeal,
        Ideal.map_map, Ideal.map_map, hmap]
    _ = affineComponentIdeal i z := by
      rw [originalConeCurveIdeal_eq_component_one,
        CycleQ2SeedLinkageOrbitProduct.localAction_component_map_eq]
      rfl

@[simp] theorem originalCurveTranslateIdeal_one (i : Fin 3) :
    originalCurveTranslateIdeal i 1 = originalAffineCurveIdeal i := by
  rw [originalCurveTranslateIdeal_eq_component i 1 (by norm_num),
    affineComponentIdeal_one_eq_original]

/-- The positive orbit divisor has one copy of each original-curve
translate. There is no factor 3 at the level of this ideal identity. -/
theorem orbitIdeal_eq_originalCurveTranslate_product (i : Fin 3) :
    OrbitIdeal i = originalCurveTranslateIdeal i 1 *
      originalCurveTranslateIdeal i complexRoot *
      originalCurveTranslateIdeal i (complexRoot ^ 2) := by
  rw [originalCurveTranslateIdeal_eq_component i 1 (by norm_num),
    originalCurveTranslateIdeal_eq_component i complexRoot complexRoot_cube,
    originalCurveTranslateIdeal_eq_component i (complexRoot ^ 2)
      (rootValues_cube complexRoot complexRoot_quadratic 2)]
  exact orbitIdeal_eq_component_product i

end CycleQ2SeedOrbitDivisor

#print axioms CycleQ2SeedOrbitDivisor.originalConeCurveIdeal_eq_component_one
#print axioms CycleQ2SeedOrbitDivisor.originalCurveTranslateIdeal_eq_component
#print axioms CycleQ2SeedOrbitDivisor.orbitIdeal_eq_originalCurveTranslate_product
