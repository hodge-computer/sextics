import Proposal.GeometricSeedProjectiveFamily
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor

/-!
# The actual projective seed maps to the genuine zero-parameter fiber

Evaluation of every cubic coefficient at zero sends the universal equation
to the original zero-cubic equation. It induces a degree-preserving map of
the actual cone quotients. Every target homogeneous class has a homogeneous
lift of the same degree, obtained by lifting its complex coefficients.
This proves the irrelevant-ideal condition for the native `Proj.map`.

The resulting global morphism commutes with the original coefficient-base
maps. It therefore factors through their actual scheme-theoretic pullback.
This file constructs that canonical fiber morphism and both projections;
it does not assert that the fiber morphism is an isomorphism. Such an
identification still requires the chartwise base-change comparison.

Status: source-only proof draft; no Lean elaboration, compilation, or
kernel replay has been run. Prepared for `fqlx` with OpenAI ChatGPT
assistance, following Ben Diamond's geometric seed construction and the
earlier canonical incidence-specialization constructions in this project.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2SeedProjectiveSpecialization

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial
open HomogeneousLocalization
open CycleQ2GeometricSeedSmooth CycleQ2GeometricIncidenceProj
  CycleQ2SeedFermatCone CycleQ2SeedFermatProj
  CycleQ2SeedCubicFamily CycleQ2SeedProjectiveFamily

/-- The origin of the full invariant-cubic coefficient space. -/
def zeroCoefficientMap : ParameterRing →+* ℂ :=
  coefficientEvaluation (fun _ => 0)

@[simp] theorem zeroCoefficientMap_complex (c : ℂ) :
    zeroCoefficientMap (algebraMap ℂ ParameterRing c) = c :=
  coefficientEvaluation_algebraMap (fun _ => 0) c

def zeroPolynomialSpecialization : FamilyPolynomial →+* SeedPolynomial :=
  MvPolynomial.map zeroCoefficientMap

@[simp] theorem zeroPolynomialSpecialization_equation (r : ℂ) :
    zeroPolynomialSpecialization (familyEquation r) = seedFamily r 0 :=
  specialize_zero r

theorem familyIdeal_le_specialization_kernel (r : ℂ) :
    familyIdeal r ≤ RingHom.ker ((coneQuotient r).comp zeroPolynomialSpecialization) := by
  apply Ideal.span_le.mpr
  intro p hp
  obtain rfl := Set.mem_singleton_iff.mp hp
  change coneQuotient r (zeroPolynomialSpecialization (familyEquation r)) = 0
  rw [zeroPolynomialSpecialization_equation]
  exact coneEquation r

/-- Specialization through the original one-equation cone quotients. -/
def seedRingSpecialization (r : ℂ) : FamilyRing r →+* ConeRing r :=
  Ideal.Quotient.lift (familyIdeal r)
    ((coneQuotient r).comp zeroPolynomialSpecialization)
    (fun _ hp => familyIdeal_le_specialization_kernel r hp)

@[simp] theorem seedRingSpecialization_quotient (r : ℂ) (p : FamilyPolynomial) :
    seedRingSpecialization r (familyQuotient r p) =
      coneQuotient r (zeroPolynomialSpecialization p) := rfl

@[simp] theorem seedRingSpecialization_coefficient (r : ℂ) (a : ParameterRing) :
    seedRingSpecialization r (algebraMap ParameterRing (FamilyRing r) a) =
      algebraMap ℂ (ConeRing r) (zeroCoefficientMap a) := by
  change seedRingSpecialization r (familyQuotient r (C a)) = _
  rw [seedRingSpecialization_quotient]
  change coneQuotient r (MvPolynomial.map zeroCoefficientMap (C a)) = _
  rw [MvPolynomial.map_C]
  rfl

@[simp] theorem seedRingSpecialization_coordinate (r : ℂ) (j : Fin 5) :
    seedRingSpecialization r (familyCoordinate r j) = coordinateClass r j := by
  change coneQuotient r (MvPolynomial.map zeroCoefficientMap (X j)) = _
  rw [MvPolynomial.map_X]
  rfl

private theorem weightedHomogeneous_map {R S : Type} [CommRing R] [CommRing S]
    (f : R →+* S) {p : MvPolynomial (Fin 5) R} {n : ℕ}
    (hp : p.IsWeightedHomogeneous geometricWeight n) :
    (MvPolynomial.map f p).IsWeightedHomogeneous geometricWeight n := by
  intro d hd
  apply hp
  intro hz
  apply hd
  rw [MvPolynomial.coeff_map, hz, map_zero]

theorem seedRingSpecialization_homogeneous (r : ℂ) {n : ℕ} {a : FamilyRing r}
    (ha : a ∈ familyGrade r n) :
    seedRingSpecialization r a ∈ coneGrade r n := by
  obtain ⟨p, hp, rfl⟩ := ha
  rw [seedRingSpecialization_quotient]
  exact ⟨MvPolynomial.map zeroCoefficientMap p,
    weightedHomogeneous_map zeroCoefficientMap hp, rfl⟩

def seedGradedMap (r : ℂ) : familyGrade r →+*ᵍ coneGrade r where
  toRingHom := seedRingSpecialization r
  map_mem := fun _ _ ha => seedRingSpecialization_homogeneous r ha

/-- Lift each coefficient through the original complex algebra structure. -/
def coefficientLift : SeedPolynomial →+* FamilyPolynomial :=
  MvPolynomial.map (algebraMap ℂ ParameterRing)

@[simp] theorem zeroPolynomialSpecialization_coefficientLift (p : SeedPolynomial) :
    zeroPolynomialSpecialization (coefficientLift p) = p :=
  coefficientEvaluation_constantPolynomial (fun _ => 0) p

/-- The specialization is surjective in every original weighted degree. -/
theorem seedGradedMap_homogeneous_surjective (r : ℂ) (n : ℕ)
    (b : ConeRing r) (hb : b ∈ coneGrade r n) :
    ∃ a : FamilyRing r, a ∈ familyGrade r n ∧ seedGradedMap r a = b := by
  obtain ⟨p, hp, rfl⟩ := hb
  refine ⟨familyQuotient r (coefficientLift p),
    ⟨_, weightedHomogeneous_map (algebraMap ℂ ParameterRing) hp, rfl⟩, ?_⟩
  change seedRingSpecialization r (familyQuotient r (coefficientLift p)) = _
  rw [seedRingSpecialization_quotient, zeroPolynomialSpecialization_coefficientLift]

theorem irrelevant_le_map_seedGradedMap (r : ℂ) :
    HomogeneousIdeal.irrelevant (coneGrade r) ≤
      (HomogeneousIdeal.irrelevant (familyGrade r)).map (seedGradedMap r) := by
  apply HomogeneousIdeal.toIdeal_le_toIdeal_iff.mp
  apply (HomogeneousIdeal.toIdeal_irrelevant_le _).mpr
  intro n hn b hb
  obtain ⟨a, ha, rfl⟩ := seedGradedMap_homogeneous_surjective r n b hb
  exact Ideal.mem_map_of_mem (seedGradedMap r)
    (HomogeneousIdeal.mem_irrelevant_of_mem (familyGrade r) hn ha)

/-- The canonical global morphism uses native projective functoriality. -/
def seedToFamily (r : ℂ) : threefold r ⟶ family r :=
  Proj.map (seedGradedMap r) (irrelevant_le_map_seedGradedMap r)

def zeroParameterMorphism : Spec (CommRingCat.of ℂ) ⟶ parameterScheme :=
  Spec.map (CommRingCat.ofHom zeroCoefficientMap)

private theorem seedAway_coefficient (r : ℂ) (s : FamilyRing r) (a : ParameterRing) :
    Away.map (seedGradedMap r) s
        (fromZeroRingHom (familyGrade r) (Submonoid.powers s)
          (parameterCoefficient r a)) =
      fromZeroRingHom (coneGrade r) (Submonoid.powers (seedGradedMap r s))
        (coefficient r (zeroCoefficientMap a)) := by
  apply HomogeneousLocalization.val_injective
  simp only [Away.map, fromZeroRingHom, HomogeneousLocalization.map_mk,
    HomogeneousLocalization.val_mk, seedGradedMap, parameterCoefficient_coe,
    coefficient_coe, map_one, seedRingSpecialization_coefficient]

/-- The canonical global specialization respects the original parameter map. -/
theorem seedToFamily_overBase (r : ℂ) :
    seedToFamily r ≫ familyToParameters r =
      threefoldToComplex r ≫ zeroParameterMorphism := by
  refine (Proj.mapAffineOpenCover (seedGradedMap r)
    (irrelevant_le_map_seedGradedMap r)).openCover.hom_ext _ _ fun s => ?_
  simp only [Scheme.AffineOpenCover.openCover_f, Proj.mapAffineOpenCover_f,
    seedToFamily, familyToParameters, threefoldToComplex, Category.assoc,
    Proj.awayι_comp_map_assoc, Proj.awayι_toSpecZero_assoc, Proj.awayι_toSpecZero,
    zeroParameterMorphism, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  exact seedAway_coefficient r (s.2 : FamilyRing r) a

/-- The genuine scheme-theoretic fiber over zero cubic coefficients. -/
abbrev ZeroFiber (r : ℂ) := pullback zeroParameterMorphism (familyToParameters r)

/-- The original projective seed maps canonically into the actual zero fiber.
Proving that this map is an isomorphism is a separate base-change obligation. -/
def seedToZeroFiber (r : ℂ) : threefold r ⟶ ZeroFiber r :=
  pullback.lift (threefoldToComplex r) (seedToFamily r) (seedToFamily_overBase r).symm

@[reassoc, simp] theorem seedToZeroFiber_fst (r : ℂ) :
    seedToZeroFiber r ≫ pullback.fst zeroParameterMorphism (familyToParameters r) =
      threefoldToComplex r := by
  simp [seedToZeroFiber]

@[reassoc, simp] theorem seedToZeroFiber_snd (r : ℂ) :
    seedToZeroFiber r ≫ pullback.snd zeroParameterMorphism (familyToParameters r) =
      seedToFamily r := by
  simp [seedToZeroFiber]

end CycleQ2SeedProjectiveSpecialization

end

#print axioms CycleQ2SeedProjectiveSpecialization.seedGradedMap_homogeneous_surjective
#print axioms CycleQ2SeedProjectiveSpecialization.irrelevant_le_map_seedGradedMap
#print axioms CycleQ2SeedProjectiveSpecialization.seedToFamily_overBase
#print axioms CycleQ2SeedProjectiveSpecialization.seedToZeroFiber
#print axioms CycleQ2SeedProjectiveSpecialization.seedToZeroFiber_fst
#print axioms CycleQ2SeedProjectiveSpecialization.seedToZeroFiber_snd
