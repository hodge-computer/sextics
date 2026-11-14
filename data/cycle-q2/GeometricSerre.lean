import Mathlib.Algebra.Module.Submodule.Equiv
import Proposal.SolutionSupport08Part06

/-!
# Graded normal pairing in the actual seed Cech quotient

Source-only continuation of Part II.2--3 of the written proof. This file has
not been elaborated or compiled.

The degree-nine Koszul boundary already lands in the quotient by all actual
localization coboundaries. Here it is proved to be a linear equivalence onto
its image, and the normalized trace on that image is constructed. Multiplying
a genuine normal class represented by a sextic numerator by a homogeneous
cubic lands in this image. The resulting bilinear pairing is defined on the
actual normal classes, so its value is independent of the chosen numerator
or local lifts. Its value is the existing quotient trace of (kL-A)*sigma.
The ambient-test pairing is bound to the literal paired normal overlap and
proved nonzero.

The condition r^3=2 belongs to the sparse trace seed. It does not silently
specialize to the distinct literal complex parameter r=57 used by the large
incidence matrix. The definitions retain the ungraded localization quotient
as their ambient module. Neither the full projective H^1(C,O_C(1)) nor its
Serre trace is introduced by definition here. The further identification
requires the twisted-sheaf Cech comparison, the Koszul boundary's projective
surjectivity, and duality; those geometric constructions remain outstanding.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
-- These explicit dependent submodule maps need more elaboration steps.
set_option maxHeartbeats 1000000

noncomputable section

namespace CycleQ2GeometricSerre

open MvPolynomial CycleQ2SeedTrace CycleQ2ConormalJacobian
  CycleQ2NormalConnecting CycleQ2ActualNormalCech CycleQ2NormalKoszulBridge
  CycleQ2SeedCechTheta CycleQ2SeedBoundaryProjection

/-! ## The actual degree-nine boundary and its normalized trace -/

/-- Restriction of the constructed Koszul boundary to the actual homogeneous
degree-nine component of the reduced seed algebra. -/
def degreeNineBoundary (r : ℂ) (hr : r ≠ 0) :
    degreeNinePiece r →ₗ[ℂ] ScalarCech r 0 :=
  (reducedScalarBoundary r hr).comp (degreeNinePiece r).subtype

/-- This is an image inside the existing quotient by unrestricted actual
localization coboundaries, rather than a new cohomology type. -/
def canonicalImage (r : ℂ) (hr : r ≠ 0) :
    Submodule ℂ (ScalarCech r 0) :=
  LinearMap.range (degreeNineBoundary r hr)

/-- No additional degree-nine relation is introduced by allowing all
localization coboundaries. The nonzero normalization class is essential. -/
theorem degreeNineBoundary_injective (r : ℂ) (hr : r ≠ 0)
    (hcube : r ^ 3 = 2) : Function.Injective (degreeNineBoundary r hr) := by
  intro x y hxy
  have hzero : degreeNineBoundary r hr (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  change reducedScalarBoundary r hr
    ((x - y : degreeNinePiece r) : ReducedAlgebra r) = 0 at hzero
  rw [reducedScalarBoundary_degreeNine r hr hcube (x - y).property] at hzero
  have htrace : reducedTrace r hcube
      ((x - y : degreeNinePiece r) : ReducedAlgebra r) = 0 :=
    (smul_eq_zero.mp hzero).resolve_right
      (normalizationCechClass_ne_zero r hr hcube)
  apply sub_eq_zero.mp
  apply Subtype.ext
  change ((x - y : degreeNinePiece r) : ReducedAlgebra r) = 0
  rw [degreeNine_class_eq_trace_smul r hcube (x - y).property,
    htrace, zero_smul]

/-- The actual boundary, with its proved injectivity, identifies the finite
degree-nine quotient with its literal Cech image. -/
def canonicalBoundaryEquiv (r : ℂ) (hr : r ≠ 0) (hcube : r ^ 3 = 2) :
    degreeNinePiece r ≃ₗ[ℂ] canonicalImage r hr :=
  LinearEquiv.ofInjective (degreeNineBoundary r hr)
    (degreeNineBoundary_injective r hr hcube)

@[simp] theorem canonicalBoundaryEquiv_coe (r : ℂ) (hr : r ≠ 0)
    (hcube : r ^ 3 = 2) (x : degreeNinePiece r) :
    (canonicalBoundaryEquiv r hr hcube x : ScalarCech r 0) =
      reducedScalarBoundary r hr (x : ReducedAlgebra r) := rfl

def canonicalNormalization (r : ℂ) (hr : r ≠ 0) : canonicalImage r hr :=
  ⟨normalizationCechClass r hr, ⟨degreeNineNormalization r, rfl⟩⟩

@[simp] theorem canonicalBoundaryEquiv_normalization (r : ℂ) (hr : r ≠ 0)
    (hcube : r ^ 3 = 2) :
    canonicalBoundaryEquiv r hr hcube (degreeNineNormalization r) =
      canonicalNormalization r hr := by
  apply Subtype.ext
  rfl

/-- A constructed trace on the actual Cech image. No trace or comparison map
is supplied as an assumption. -/
def cechTrace (r : ℂ) (hr : r ≠ 0) (hcube : r ^ 3 = 2) :
    canonicalImage r hr →ₗ[ℂ] ℂ :=
  (degreeNineTrace r hcube).comp
    (canonicalBoundaryEquiv r hr hcube).symm.toLinearMap

@[simp] theorem cechTrace_boundary (r : ℂ) (hr : r ≠ 0)
    (hcube : r ^ 3 = 2) (x : degreeNinePiece r) :
    cechTrace r hr hcube (canonicalBoundaryEquiv r hr hcube x) =
      degreeNineTrace r hcube x := by
  simp only [cechTrace, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    LinearEquiv.symm_apply_apply]

@[simp] theorem cechTrace_normalized (r : ℂ) (hr : r ≠ 0)
    (hcube : r ^ 3 = 2) :
    cechTrace r hr hcube (canonicalNormalization r hr) = 1 := by
  rw [← canonicalBoundaryEquiv_normalization r hr hcube,
    cechTrace_boundary, degreeNineTrace_normalized]

/-- Every class in this actual Cech image is its computed trace times the
specific nonzero normalization class. -/
theorem canonical_eq_trace_smul (r : ℂ) (hr : r ≠ 0)
    (hcube : r ^ 3 = 2) (z : canonicalImage r hr) :
    z = cechTrace r hr hcube z • canonicalNormalization r hr := by
  obtain ⟨x, rfl⟩ := (canonicalBoundaryEquiv r hr hcube).surjective z
  apply Subtype.ext
  rw [cechTrace_boundary]
  exact reducedScalarBoundary_degreeNine r hr hcube x.property

theorem cechTrace_injective (r : ℂ) (hr : r ≠ 0)
    (hcube : r ^ 3 = 2) : Function.Injective (cechTrace r hr hcube) := by
  intro x y hxy
  calc
    x = cechTrace r hr hcube x • canonicalNormalization r hr :=
      canonical_eq_trace_smul r hr hcube x
    _ = cechTrace r hr hcube y • canonicalNormalization r hr := by rw [hxy]
    _ = y := (canonical_eq_trace_smul r hr hcube y).symm

theorem cechTrace_surjective (r : ℂ) (hr : r ≠ 0)
    (hcube : r ^ 3 = 2) : Function.Surjective (cechTrace r hr hcube) := by
  intro c
  refine ⟨c • canonicalNormalization r hr, ?_⟩
  rw [map_smul, cechTrace_normalized, smul_eq_mul, mul_one]

/-- The normalization determines the trace on actual classes uniquely. -/
theorem cechTrace_unique (r : ℂ) (hr : r ≠ 0) (hcube : r ^ 3 = 2)
    (t : canonicalImage r hr →ₗ[ℂ] ℂ)
    (ht : t (canonicalNormalization r hr) = 1) :
    t = cechTrace r hr hcube := by
  ext z
  calc
    t z = t (cechTrace r hr hcube z • canonicalNormalization r hr) :=
      congrArg t (canonical_eq_trace_smul r hr hcube z)
    _ = cechTrace r hr hcube z := by
      rw [map_smul, ht, smul_eq_mul, mul_one]

/-! ## Multiplication of genuine normal classes by homogeneous cubics -/

abbrev Cubics := homogeneousSubmodule (Fin 4) ℂ 3
abbrev Sextics := homogeneousSubmodule (Fin 4) ℂ 6

/-- The already constructed normal-kernel trivialization, with scalars
restricted to the ground field. -/
def normalCoordinates (r : ℂ) : NormalCech r 0 ≃ₗ[ℂ] ScalarCech r 0 :=
  (normalCechEquivalence r 0).restrictScalars ℂ

/-- A homogeneous sextic divided by g1*g2 is a normal coefficient of degree
minus two. The target remains the genuine normal-kernel Cech quotient. -/
def normalSixBoundary (r : ℂ) : Sextics →ₗ[ℂ] NormalCech r 0 :=
  (normalCoordinates r).symm.toLinearMap.comp
    (((simplePoleClass r 0).restrictScalars ℂ).comp
      (polynomialLift.toLinearMap.comp Sextics.subtype))

@[simp] theorem normalSixBoundary_coordinates (r : ℂ) (p : Sextics) :
    normalCoordinates r (normalSixBoundary r p) =
      simplePoleClass r 0 (polynomialLift (p : Poly)) := by
  change normalCoordinates r
    ((normalCoordinates r).symm
      (simplePoleClass r 0 (polynomialLift (p : Poly)))) = _
  exact (normalCoordinates r).apply_symm_apply _

/-- This subspace uses equality of genuine normal Cech classes; it does not
quotient by a chosen finite list of polynomial relations. -/
def normalSixImage (r : ℂ) : Submodule ℂ (NormalCech r 0) :=
  LinearMap.range (normalSixBoundary r)

def normalNumeratorClass (r : ℂ) (p : Sextics) : normalSixImage r :=
  ⟨normalSixBoundary r p, ⟨p, rfl⟩⟩

theorem normalSixBoundary_eq_connecting (r : ℂ) (p : Sextics) :
    normalSixBoundary r p =
      connectingClass r 0 (-(polynomialLift (p : Poly))) 0 := by
  rw [connectingClass_eq_simplePole]
  simp only [mul_zero, zero_sub, neg_neg]
  rfl

private theorem cubicNormalClass_mem (r : ℂ) (hr : r ≠ 0)
    (s : Cubics) (n : normalSixImage r) :
    polynomialLift (s : Poly) • normalCoordinates r (n : NormalCech r 0) ∈
      canonicalImage r hr := by
  obtain ⟨p, hp⟩ := n.property
  change normalSixBoundary r p = (n : NormalCech r 0) at hp
  rw [← hp, normalSixBoundary_coordinates]
  have hmul : polynomialLift (s : Poly) •
        simplePoleClass r 0 (polynomialLift (p : Poly)) =
      simplePoleClass r 0 (polynomialLift ((s : Poly) * (p : Poly))) := by
    rw [map_mul]
    exact ((simplePoleClass r 0).map_smul
      (polynomialLift (s : Poly)) (polynomialLift (p : Poly))).symm
  rw [hmul]
  refine ⟨⟨reducedQuotient r ((s : Poly) * (p : Poly)),
    ⟨(s : Poly) * (p : Poly), s.property.mul p.property, rfl⟩⟩, ?_⟩
  rfl

/-- Cubic multiplication on the actual normal classes. All representatives
of the same genuine Cech class give exactly the same value. -/
def cubicNormalClass (r : ℂ) (hr : r ≠ 0) :
    Cubics →ₗ[ℂ] normalSixImage r →ₗ[ℂ] canonicalImage r hr where
  toFun s :=
    { toFun n := ⟨polynomialLift (s : Poly) •
          normalCoordinates r (n : NormalCech r 0), cubicNormalClass_mem r hr s n⟩
      map_add' n m := by
        apply Subtype.ext
        change polynomialLift (s : Poly) •
            normalCoordinates r ((n : NormalCech r 0) + (m : NormalCech r 0)) =
          polynomialLift (s : Poly) • normalCoordinates r (n : NormalCech r 0) +
            polynomialLift (s : Poly) • normalCoordinates r (m : NormalCech r 0)
        rw [(normalCoordinates r).map_add, smul_add]
      map_smul' c n := by
        apply Subtype.ext
        change polynomialLift (s : Poly) •
            normalCoordinates r (c • (n : NormalCech r 0)) =
          c • (polynomialLift (s : Poly) • normalCoordinates r (n : NormalCech r 0))
        rw [(normalCoordinates r).map_smul]
        exact smul_comm _ _ _ }
  map_add' s t := by
    apply LinearMap.ext
    intro n
    apply Subtype.ext
    change polynomialLift ((s : Poly) + (t : Poly)) •
        normalCoordinates r (n : NormalCech r 0) =
      polynomialLift (s : Poly) • normalCoordinates r (n : NormalCech r 0) +
        polynomialLift (t : Poly) • normalCoordinates r (n : NormalCech r 0)
    have hadd : polynomialLift ((s : Poly) + (t : Poly)) =
        polynomialLift (s : Poly) + polynomialLift (t : Poly) :=
      map_add polynomialLift _ _
    rw [hadd, add_smul]
  map_smul' c s := by
    apply LinearMap.ext
    intro n
    apply Subtype.ext
    change polynomialLift (c • (s : Poly)) •
        normalCoordinates r (n : NormalCech r 0) =
      c • (polynomialLift (s : Poly) • normalCoordinates r (n : NormalCech r 0))
    rw [map_smul, smul_assoc]

@[simp] theorem cubicNormalClass_numerator_coe (r : ℂ) (hr : r ≠ 0)
    (s : Cubics) (p : Sextics) :
    (cubicNormalClass r hr s (normalNumeratorClass r p) : ScalarCech r 0) =
      simplePoleClass r 0 (polynomialLift ((s : Poly) * (p : Poly))) := by
  change polynomialLift (s : Poly) • normalCoordinates r (normalSixBoundary r p) = _
  rw [normalSixBoundary_coordinates, map_mul]
  exact ((simplePoleClass r 0).map_smul
    (polynomialLift (s : Poly)) (polynomialLift (p : Poly))).symm

theorem cubicNormalClass_numerator (r : ℂ) (hr : r ≠ 0)
    (hcube : r ^ 3 = 2) (s : Cubics) (p : Sextics) :
    cubicNormalClass r hr s (normalNumeratorClass r p) =
      canonicalBoundaryEquiv r hr hcube
        ⟨reducedQuotient r ((s : Poly) * (p : Poly)),
          ⟨(s : Poly) * (p : Poly), s.property.mul p.property, rfl⟩⟩ := by
  apply Subtype.ext
  rw [cubicNormalClass_numerator_coe, canonicalBoundaryEquiv_coe,
    reducedScalarBoundary_mk]

/-- The trace pairing descends to genuine normal Cech classes before its
polynomial formula is proved. -/
def normalTracePairing (r : ℂ) (hr : r ≠ 0) (hcube : r ^ 3 = 2) :
    Cubics →ₗ[ℂ] normalSixImage r →ₗ[ℂ] ℂ where
  toFun s := (cechTrace r hr hcube).comp (cubicNormalClass r hr s)
  map_add' s t := by
    ext n
    simp only [LinearMap.comp_apply, map_add, LinearMap.add_apply]
  map_smul' c s := by
    ext n
    simp only [LinearMap.comp_apply, map_smul, LinearMap.smul_apply, RingHom.id_apply]

@[simp] theorem normalTracePairing_numerator (r : ℂ) (hr : r ≠ 0)
    (hcube : r ^ 3 = 2) (s : Cubics) (p : Sextics) :
    normalTracePairing r hr hcube s (normalNumeratorClass r p) =
      traceLinear r ((s : Poly) * (p : Poly)) := by
  change cechTrace r hr hcube
    (cubicNormalClass r hr s (normalNumeratorClass r p)) = _
  rw [cubicNormalClass_numerator r hr hcube, cechTrace_boundary]
  rfl

/-! ## Binding to the actual normal connecting class -/

/-- The sextic numerator is the existing actual local-lift difference,
eliminated by w=-x2^2. -/
def connectingInImage (r : ℂ) (A L : P)
    (hdegree : (substitute (originalK * L - A)).IsHomogeneous 6) :
    normalSixImage r :=
  normalNumeratorClass r ⟨substitute (originalK * L - A), hdegree⟩

@[simp] theorem connectingInImage_coe (r : ℂ) (A L : P)
    (hdegree : (substitute (originalK * L - A)).IsHomogeneous 6) :
    (connectingInImage r A L hdegree : NormalCech r 0) =
      connectingClass r 0 A L := by
  apply (normalCechEquivalence r 0).injective
  change normalCoordinates r
      (normalSixBoundary r ⟨substitute (originalK * L - A), hdegree⟩) = _
  rw [normalSixBoundary_coordinates, connectingClass_eq_seedNormalBoundary,
    normalCechEquivalence_seedNormalBoundary, seedScalarBoundary_mk]
  exact (simplePoleClass_substitute r (originalK * L - A)).symm

/-- The paired trace is exactly the existing five-variable quotient trace
of (kL-A)*sigma, with no separately supplied comparison constant or map. -/
theorem normalTracePairing_connecting (r : ℂ) (hr : r ≠ 0)
    (hcube : r ^ 3 = 2) (A L : P)
    (hdegree : (substitute (originalK * L - A)).IsHomogeneous 6) (s : Cubics) :
    normalTracePairing r hr hcube s (connectingInImage r A L hdegree) =
      seedTrace r hcube
        (seedQuotient r (polynomialLift (s : Poly) * (originalK * L - A))) := by
  rw [connectingInImage, normalTracePairing_numerator, seedTrace_mk]
  change traceLinear r ((s : Poly) * substitute (originalK * L - A)) =
    traceLinear r (substitute (polynomialLift (s : Poly) * (originalK * L - A)))
  have hm : substitute (polynomialLift (s : Poly) * (originalK * L - A)) =
      substitute (polynomialLift (s : Poly)) * substitute (originalK * L - A) :=
    map_mul substitute _ _
  rw [hm, substitute_polynomialLift]

theorem ambientNumerator_homogeneous :
    (substitute (originalK * 0 - derivativeA)).IsHomogeneous 6 := by
  have he : substitute derivativeA = (-X 2 ^ 3 * X 3 ^ 3 : Poly) := by
    simpa only [derivativeNumerator, mul_one] using substitute_derivativeA (1 : Poly)
  rw [mul_zero, zero_sub, map_neg, he]
  exact (((isHomogeneous_X_pow (2 : Fin 4) 3).neg).mul
    (isHomogeneous_X_pow (3 : Fin 4) 3)).neg

def ambientNormalClass (r : ℂ) : normalSixImage r :=
  connectingInImage r derivativeA 0 ambientNumerator_homogeneous

@[simp] theorem ambientNormalClass_coe (r : ℂ) :
    (ambientNormalClass r : NormalCech r 0) =
      connectingClass r 0 derivativeA 0 :=
  connectingInImage_coe r derivativeA 0 ambientNumerator_homogeneous

def deformationCubic (v : Fin 9 → ℂ) : Cubics :=
  ⟨cubicDeformation v, cubicDeformation_homogeneous v⟩

/-- The cubic pairing of the actual ambient-test normal class is precisely
the previously constructed overlap representative, modulo all boundaries. -/
theorem ambientPairing_coe (r : ℂ) (hr : r ≠ 0) (v : Fin 9 → ℂ) :
    (cubicNormalClass r hr (deformationCubic v) (ambientNormalClass r) :
      ScalarCech r 0) =
      (Submodule.Quotient.mk
        (pairedNormalOverlap r 0 (cubicDeformation v)) : ScalarCech r 0) := by
  change (cubicNormalClass r hr (deformationCubic v)
    (normalNumeratorClass r
      ⟨substitute (originalK * 0 - derivativeA), ambientNumerator_homogeneous⟩) :
        ScalarCech r 0) = _
  rw [cubicNormalClass_numerator_coe]
  have hn : cubicDeformation v * substitute (originalK * 0 - derivativeA) =
      -derivativeNumerator (cubicDeformation v) := by
    rw [mul_zero, zero_sub, map_neg, mul_comm]
    exact fixed_h_paired_numerator (cubicDeformation v)
  change simplePoleClass r 0 (polynomialLift
    (cubicDeformation v * substitute (originalK * 0 - derivativeA))) = _
  rw [hn, simplePoleClass_apply, simplePoleRepresentative_lift_derivative]

/-- Nonvanishing is a conclusion about the constructed trace of the actual
normal class, obtained from the explicit all-poles residue obstruction. -/
theorem ambientTracePairing_ne_zero (r : ℂ) (hr : r ≠ 0)
    (hcube : r ^ 3 = 2) (v : Fin 9 → ℂ)
    (hv : derivativeTrace 0 v ≠ 0) :
    normalTracePairing r hr hcube (deformationCubic v) (ambientNormalClass r) ≠ 0 := by
  intro hz
  have htrace : cechTrace r hr hcube
      (cubicNormalClass r hr (deformationCubic v) (ambientNormalClass r)) =
      cechTrace r hr hcube 0 := by
    change cechTrace r hr hcube
      (cubicNormalClass r hr (deformationCubic v) (ambientNormalClass r)) = 0 at hz
    simpa only [map_zero] using hz
  have hzero := cechTrace_injective r hr hcube htrace
  have hscalar := congrArg
    (fun z : canonicalImage r hr => (z : ScalarCech r 0)) hzero
  rw [ambientPairing_coe] at hscalar
  exact pairedScalarClass_ne_zero r 0 hr v hv hscalar

theorem selectedAmbientTracePairing_ne_zero (r : ℂ) (hr : r ≠ 0)
    (hcube : r ^ 3 = 2) :
    normalTracePairing r hr hcube (deformationCubic selectedTangent)
      (ambientNormalClass r) ≠ 0 := by
  apply ambientTracePairing_ne_zero r hr hcube
  rw [selectedTangent_trace]
  norm_num

end CycleQ2GeometricSerre

end
