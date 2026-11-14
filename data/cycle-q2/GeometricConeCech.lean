import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.ShortComplex.Ab
import Mathlib.CategoryTheory.Sites.SheafCohomology.MayerVietoris
import Mathlib.Topology.Sheaves.MayerVietoris
import Proposal.GeometricSerre
import Proposal.GeometricSheafHZero

/-!
# The actual cone cover and its structure-sheaf Cech quotient

This source-only continuation has not been elaborated or compiled.

The curve ring already used by the normal calculation is the homogeneous
coordinate ring of the ordinary (2,3) curve after eliminating w=-x2^2.
Here its punctured affine cone is constructed as an actual open subscheme
of Spec of that ring. The existing two denominator functions cover it.

The localizations occurring in the normal calculation are canonically
identified with sections of the actual structure sheaf on this cover,
and those identifications commute with both restriction maps. Consequently
the existing quotient by all localization coboundaries is equivalent to
the quotient by the actual sheaf-section coboundaries. An explicit
degree-zero Yoneda comparison and the Mayer-Vietoris exact sequence then
inject this quotient into actual derived sheaf cohomology of the punctured
open. Its normal and normalization classes remain nonzero there. This
injection does not assume that the patches have vanishing higher cohomology.

This is the punctured-cone Cech quotient, with all degrees retained. It is
not defined to be H^1 of a projective twist. Extracting the appropriate
homogeneous degree, comparing with projective O_C(1), and identifying its
geometric trace remain separate constructions.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

noncomputable section

namespace CycleQ2GeometricConeCech

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite TopologicalSpace AlgebraicGeometry
open MvPolynomial CycleQ2SeedTrace CycleQ2ConormalJacobian
  CycleQ2NormalConnecting CycleQ2SeedCechTheta CycleQ2ActualNormalCech

/-! ## The punctured cone and its two actual opens -/

def cone (r θ : ℂ) : Scheme :=
  Spec (CommRingCat.of (CurveRing r θ))

def coordinatePatch (r θ : ℂ) (j : Fin 4) : (cone r θ).Opens :=
  PrimeSpectrum.basicOpen (curveMap r θ (X j))

def puncturedOpen (r θ : ℂ) : (cone r θ).Opens :=
  ⨆ j : Fin 4, coordinatePatch r θ j

def firstPatch (r θ : ℂ) : (cone r θ).Opens :=
  PrimeSpectrum.basicOpen (curveG1 r θ)

def secondPatch (r θ : ℂ) : (cone r θ).Opens :=
  PrimeSpectrum.basicOpen (curveG2 r θ)

def overlapPatch (r θ : ℂ) : (cone r θ).Opens :=
  PrimeSpectrum.basicOpen (curveG1 r θ * curveG2 r θ)

theorem overlapPatch_eq (r θ : ℂ) :
    overlapPatch r θ = firstPatch r θ ⊓ secondPatch r θ :=
  PrimeSpectrum.basicOpen_mul _ _

theorem firstPatch_le_coordinate (r θ : ℂ) :
    firstPatch r θ ≤ coordinatePatch r θ 1 := by
  change PrimeSpectrum.basicOpen
    (ambientCurveMap r θ (originalG1 r)) ≤ _
  rw [ambientCurveMap_g1, map_mul, map_pow]
  calc
    PrimeSpectrum.basicOpen
        (curveMap r θ (C (3 * r ^ 2)) *
          curveMap r θ CycleQ2SeedCech.curveA ^ 2) ≤
        PrimeSpectrum.basicOpen (curveMap r θ CycleQ2SeedCech.curveA ^ 2) :=
      PrimeSpectrum.basicOpen_mul_le_right _ _
    _ = PrimeSpectrum.basicOpen (curveMap r θ CycleQ2SeedCech.curveA) :=
      PrimeSpectrum.basicOpen_pow _ 2 (by decide)
    _ ≤ coordinatePatch r θ 1 := by
      change PrimeSpectrum.basicOpen (curveMap r θ (X 1 * X 3)) ≤ _
      rw [map_mul]
      exact PrimeSpectrum.basicOpen_mul_le_left _ _

theorem secondPatch_le_coordinate (r θ : ℂ) :
    secondPatch r θ ≤ coordinatePatch r θ 2 := by
  change PrimeSpectrum.basicOpen (ambientCurveMap r θ originalG2) ≤ _
  rw [ambientCurveMap_g2, map_mul, map_pow]
  exact (PrimeSpectrum.basicOpen_mul_le_right _ _).trans
    (le_of_eq (PrimeSpectrum.basicOpen_pow _ 4 (by decide)))

theorem firstPatch_le_punctured (r θ : ℂ) :
    firstPatch r θ ≤ puncturedOpen r θ :=
  (firstPatch_le_coordinate r θ).trans (le_iSup (coordinatePatch r θ) 1)

theorem secondPatch_le_punctured (r θ : ℂ) :
    secondPatch r θ ≤ puncturedOpen r θ :=
  (secondPatch_le_coordinate r θ).trans (le_iSup (coordinatePatch r θ) 2)

/-- This is equality of actual Zariski opens, not an assumed cover. -/
theorem puncturedOpen_eq_union (r θ : ℂ) (hr : r ≠ 0) :
    puncturedOpen r θ = firstPatch r θ ⊔ secondPatch r θ := by
  apply le_antisymm
  · intro q hq
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp hq
    exact CycleQ2SeedTwoOpenCover.relevant_prime_cover r θ hr q.asIdeal ⟨j, hj⟩
  · exact sup_le (firstPatch_le_punctured r θ) (secondPatch_le_punctured r θ)

def puncturedCone (r θ : ℂ) : Scheme := (puncturedOpen r θ).toScheme

def puncturedInclusion (r θ : ℂ) : puncturedCone r θ ⟶ cone r θ :=
  (puncturedOpen r θ).ι

instance puncturedInclusion_isOpenImmersion (r θ : ℂ) :
    IsOpenImmersion (puncturedInclusion r θ) := by
  change IsOpenImmersion (puncturedOpen r θ).ι
  infer_instance

/-- The actual four opens and their inclusions form a Mayer-Vietoris square. -/
def coneMayerVietoris (r θ : ℂ) (hr : r ≠ 0) :
    (Opens.grothendieckTopology (cone r θ)).MayerVietorisSquare :=
  Opens.mayerVietorisSquare'
    { X₁ := overlapPatch r θ
      X₂ := firstPatch r θ
      X₃ := secondPatch r θ
      X₄ := puncturedOpen r θ
      f₁₂ := homOfLE (PrimeSpectrum.basicOpen_mul_le_left _ _)
      f₁₃ := homOfLE (PrimeSpectrum.basicOpen_mul_le_right _ _)
      f₂₄ := homOfLE (firstPatch_le_punctured r θ)
      f₃₄ := homOfLE (secondPatch_le_punctured r θ)
      fac := Subsingleton.elim _ _ }
    (puncturedOpen_eq_union r θ hr) (overlapPatch_eq r θ)

/-! ## Genuine structure-sheaf sections and restrictions -/

abbrev Sections (r θ : ℂ) (U : (cone r θ).Opens) := Γ(cone r θ, U)

instance sectionsCurveAlgebra (r θ : ℂ) (U : (cone r θ).Opens) :
    Algebra (CurveRing r θ) (Sections r θ U) :=
  AlgebraicGeometry.StructureSheaf.openAlgebra (R := CurveRing r θ) (op U)

/-- The ambient polynomial action is induced by the literal curve map. -/
def sectionAmbientMap (r θ : ℂ) (U : (cone r θ).Opens) : P →+* Sections r θ U :=
  (algebraMap (CurveRing r θ) (Sections r θ U)).comp (ambientCurveMap r θ)

instance sectionsAmbientAlgebra (r θ : ℂ) (U : (cone r θ).Opens) :
    Algebra P (Sections r θ U) := (sectionAmbientMap r θ U).toAlgebra

/-- This is the restriction map of the scheme's actual structure sheaf. -/
def sectionRestriction (r θ : ℂ) (U V : (cone r θ).Opens) (h : V ≤ U) :
    Sections r θ U →ₐ[P] Sections r θ V where
  __ := ((cone r θ).presheaf.map (homOfLE h).op).hom
  commutes' p := rfl

@[simp] theorem sectionRestriction_base (r θ : ℂ)
    (U V : (cone r θ).Opens) (h : V ≤ U) (x : CurveRing r θ) :
    sectionRestriction r θ U V h (algebraMap (CurveRing r θ) (Sections r θ U) x) =
      algebraMap (CurveRing r θ) (Sections r θ V) x := rfl

abbrev FirstSections (r θ : ℂ) := Sections r θ (firstPatch r θ)
abbrev SecondSections (r θ : ℂ) := Sections r θ (secondPatch r θ)
abbrev OverlapSections (r θ : ℂ) := Sections r θ (overlapPatch r θ)

instance firstSectionsLocalization (r θ : ℂ) :
    IsLocalization.Away (curveG1 r θ) (FirstSections r θ) :=
  AlgebraicGeometry.StructureSheaf.IsLocalization.to_basicOpen
    (CurveRing r θ) (curveG1 r θ)

instance secondSectionsLocalization (r θ : ℂ) :
    IsLocalization.Away (curveG2 r θ) (SecondSections r θ) :=
  AlgebraicGeometry.StructureSheaf.IsLocalization.to_basicOpen
    (CurveRing r θ) (curveG2 r θ)

instance overlapSectionsLocalization (r θ : ℂ) :
    IsLocalization.Away (curveG1 r θ * curveG2 r θ) (OverlapSections r θ) :=
  AlgebraicGeometry.StructureSheaf.IsLocalization.to_basicOpen
    (CurveRing r θ) (curveG1 r θ * curveG2 r θ)

def firstSectionsRestriction (r θ : ℂ) :
    FirstSections r θ →ₐ[P] OverlapSections r θ :=
  sectionRestriction r θ _ _ (PrimeSpectrum.basicOpen_mul_le_left _ _)

def secondSectionsRestriction (r θ : ℂ) :
    SecondSections r θ →ₐ[P] OverlapSections r θ :=
  sectionRestriction r θ _ _ (PrimeSpectrum.basicOpen_mul_le_right _ _)

/-- The canonical localization isomorphism with actual sections on D(g1). -/
def firstSectionsEquiv (r θ : ℂ) : FirstOpen r θ ≃ₐ[P] FirstSections r θ where
  __ := (IsLocalization.algEquiv (Submonoid.powers (curveG1 r θ))
    (FirstOpen r θ) (FirstSections r θ)).toRingEquiv
  commutes' p := (IsLocalization.algEquiv (Submonoid.powers (curveG1 r θ))
    (FirstOpen r θ) (FirstSections r θ)).commutes (ambientCurveMap r θ p)

/-- The canonical localization isomorphism with actual sections on D(g2). -/
def secondSectionsEquiv (r θ : ℂ) : SecondOpen r θ ≃ₐ[P] SecondSections r θ where
  __ := (IsLocalization.algEquiv (Submonoid.powers (curveG2 r θ))
    (SecondOpen r θ) (SecondSections r θ)).toRingEquiv
  commutes' p := (IsLocalization.algEquiv (Submonoid.powers (curveG2 r θ))
    (SecondOpen r θ) (SecondSections r θ)).commutes (ambientCurveMap r θ p)

/-- The overlap is D(g1*g2), with its own actual structure-sheaf sections. -/
def overlapSectionsEquiv (r θ : ℂ) : Overlap r θ ≃ₐ[P] OverlapSections r θ where
  __ := (IsLocalization.algEquiv (Submonoid.powers (curveG1 r θ * curveG2 r θ))
    (Overlap r θ) (OverlapSections r θ)).toRingEquiv
  commutes' p :=
    (IsLocalization.algEquiv (Submonoid.powers (curveG1 r θ * curveG2 r θ))
      (Overlap r θ) (OverlapSections r θ)).commutes (ambientCurveMap r θ p)

@[simp] theorem firstSectionsEquiv_base (r θ : ℂ) (x : CurveRing r θ) :
    firstSectionsEquiv r θ (algebraMap (CurveRing r θ) (FirstOpen r θ) x) =
      algebraMap (CurveRing r θ) (FirstSections r θ) x :=
  (IsLocalization.algEquiv (Submonoid.powers (curveG1 r θ))
    (FirstOpen r θ) (FirstSections r θ)).commutes x

@[simp] theorem secondSectionsEquiv_base (r θ : ℂ) (x : CurveRing r θ) :
    secondSectionsEquiv r θ (algebraMap (CurveRing r θ) (SecondOpen r θ) x) =
      algebraMap (CurveRing r θ) (SecondSections r θ) x :=
  (IsLocalization.algEquiv (Submonoid.powers (curveG2 r θ))
    (SecondOpen r θ) (SecondSections r θ)).commutes x

@[simp] theorem overlapSectionsEquiv_base (r θ : ℂ) (x : CurveRing r θ) :
    overlapSectionsEquiv r θ (algebraMap (CurveRing r θ) (Overlap r θ) x) =
      algebraMap (CurveRing r θ) (OverlapSections r θ) x :=
  (IsLocalization.algEquiv (Submonoid.powers (curveG1 r θ * curveG2 r θ))
    (Overlap r θ) (OverlapSections r θ)).commutes x

/-- First localization restriction is the actual sheaf restriction. -/
theorem first_restriction_compatibility (r θ : ℂ) (x : FirstOpen r θ) :
    firstSectionsRestriction r θ (firstSectionsEquiv r θ x) =
      overlapSectionsEquiv r θ (firstRestriction r θ x) := by
  have hh : (firstSectionsRestriction r θ).toRingHom.comp
        (firstSectionsEquiv r θ).toRingHom =
      (overlapSectionsEquiv r θ).toRingHom.comp (firstRestriction r θ) := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (curveG1 r θ))
    apply RingHom.ext
    intro a
    change firstSectionsRestriction r θ
        (firstSectionsEquiv r θ (algebraMap (CurveRing r θ) (FirstOpen r θ) a)) =
      overlapSectionsEquiv r θ
        (firstRestriction r θ (algebraMap (CurveRing r θ) (FirstOpen r θ) a))
    rw [firstSectionsEquiv_base, firstRestriction, IsLocalization.Away.awayToAwayRight_eq,
      overlapSectionsEquiv_base] <;> rfl
  exact RingHom.congr_fun hh x

/-- Second localization restriction is the actual sheaf restriction. -/
theorem second_restriction_compatibility (r θ : ℂ) (x : SecondOpen r θ) :
    secondSectionsRestriction r θ (secondSectionsEquiv r θ x) =
      overlapSectionsEquiv r θ (secondRestriction r θ x) := by
  have hh : (secondSectionsRestriction r θ).toRingHom.comp
        (secondSectionsEquiv r θ).toRingHom =
      (overlapSectionsEquiv r θ).toRingHom.comp (secondRestriction r θ) := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (curveG2 r θ))
    apply RingHom.ext
    intro a
    change secondSectionsRestriction r θ
        (secondSectionsEquiv r θ (algebraMap (CurveRing r θ) (SecondOpen r θ) a)) =
      overlapSectionsEquiv r θ
        (secondRestriction r θ (algebraMap (CurveRing r θ) (SecondOpen r θ) a))
    rw [secondSectionsEquiv_base, secondRestriction, IsLocalization.Away.awayToAwayLeft_eq,
      overlapSectionsEquiv_base] <;> rfl
  exact RingHom.congr_fun hh x

/-! ## Equality with the actual sheaf-section coboundaries -/

/-- The usual difference of the two restrictions on actual sections. -/
def sectionCoboundary (r θ : ℂ) :
    FirstSections r θ × SecondSections r θ →ₗ[P] OverlapSections r θ :=
  (firstSectionsRestriction r θ).toLinearMap.comp (LinearMap.fst P _ _) -
    (secondSectionsRestriction r θ).toLinearMap.comp (LinearMap.snd P _ _)

@[simp] theorem sectionCoboundary_apply (r θ : ℂ)
    (x : FirstSections r θ) (y : SecondSections r θ) :
    sectionCoboundary r θ (x, y) =
      firstSectionsRestriction r θ x - secondSectionsRestriction r θ y := rfl

def sectionBoundaries (r θ : ℂ) : Submodule P (OverlapSections r θ) :=
  LinearMap.range (sectionCoboundary r θ)

theorem sectionBoundaries_eq_sup (r θ : ℂ) :
    sectionBoundaries r θ =
      LinearMap.range (firstSectionsRestriction r θ).toLinearMap ⊔
        LinearMap.range (secondSectionsRestriction r θ).toLinearMap := by
  ext z
  constructor
  · rintro ⟨⟨x, y⟩, rfl⟩
    exact Submodule.sub_mem _
      (le_sup_left (a := LinearMap.range (firstSectionsRestriction r θ).toLinearMap)
        (b := LinearMap.range (secondSectionsRestriction r θ).toLinearMap) (show firstSectionsRestriction r θ x ∈
        LinearMap.range (firstSectionsRestriction r θ).toLinearMap from ⟨x, rfl⟩))
      (le_sup_right (a := LinearMap.range (firstSectionsRestriction r θ).toLinearMap)
        (b := LinearMap.range (secondSectionsRestriction r θ).toLinearMap) (show secondSectionsRestriction r θ y ∈
        LinearMap.range (secondSectionsRestriction r θ).toLinearMap from ⟨y, rfl⟩))
  · intro hz
    obtain ⟨x, ⟨a, rfl⟩, y, ⟨b, rfl⟩, hxy⟩ := Submodule.mem_sup.mp hz
    refine ⟨(a, -b), ?_⟩
    change firstSectionsRestriction r θ a + secondSectionsRestriction r θ b = z at hxy
    simpa only [sectionCoboundary_apply, map_neg, sub_neg_eq_add] using hxy

private theorem map_first_boundaries (r θ : ℂ) :
    (LinearMap.range (firstRestrictionAlg r θ).toLinearMap).map
        (overlapSectionsEquiv r θ).toLinearEquiv.toLinearMap =
      LinearMap.range (firstSectionsRestriction r θ).toLinearMap := by
  ext z
  constructor
  · rintro ⟨x, ⟨a, rfl⟩, rfl⟩
    exact ⟨firstSectionsEquiv r θ a, first_restriction_compatibility r θ a⟩
  · rintro ⟨x, rfl⟩
    obtain ⟨a, rfl⟩ := (firstSectionsEquiv r θ).surjective x
    exact ⟨firstRestriction r θ a, ⟨a, rfl⟩,
      (first_restriction_compatibility r θ a).symm⟩

private theorem map_second_boundaries (r θ : ℂ) :
    (LinearMap.range (secondRestrictionAlg r θ).toLinearMap).map
        (overlapSectionsEquiv r θ).toLinearEquiv.toLinearMap =
      LinearMap.range (secondSectionsRestriction r θ).toLinearMap := by
  ext z
  constructor
  · rintro ⟨x, ⟨a, rfl⟩, rfl⟩
    exact ⟨secondSectionsEquiv r θ a, second_restriction_compatibility r θ a⟩
  · rintro ⟨x, rfl⟩
    obtain ⟨a, rfl⟩ := (secondSectionsEquiv r θ).surjective x
    exact ⟨secondRestriction r θ a, ⟨a, rfl⟩,
      (second_restriction_compatibility r θ a).symm⟩

theorem scalarBoundaries_map (r θ : ℂ) :
    (scalarBoundaries r θ).map
        (overlapSectionsEquiv r θ).toLinearEquiv.toLinearMap =
      sectionBoundaries r θ := by
  rw [scalarBoundaries, Submodule.map_sup, map_first_boundaries,
    map_second_boundaries, sectionBoundaries_eq_sup]

/-- Degree-one Cech cohomology of the two actual structure-sheaf patches.
The cover is normalized, so all one-cochains are cocycles. -/
abbrev SectionCech (r θ : ℂ) :=
  OverlapSections r θ ⧸ sectionBoundaries r θ

/-- The comparison is induced by the canonical localization/section maps
and respects every actual coboundary on both sides. -/
def scalarCechSectionsEquiv (r θ : ℂ) : ScalarCech r θ ≃ₗ[P] SectionCech r θ :=
  Submodule.Quotient.equiv (scalarBoundaries r θ) (sectionBoundaries r θ)
    (overlapSectionsEquiv r θ).toLinearEquiv (scalarBoundaries_map r θ)

@[simp] theorem scalarCechSectionsEquiv_mk (r θ : ℂ) (x : Overlap r θ) :
    scalarCechSectionsEquiv r θ (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (overlapSectionsEquiv r θ x) := rfl

/-- The genuine normal-kernel quotient reaches the same actual section
quotient through its previously proved normal trivialization. -/
def normalCechSectionsEquiv (r θ : ℂ) : NormalCech r θ ≃ₗ[P] SectionCech r θ :=
  (normalCechEquivalence r θ).trans (scalarCechSectionsEquiv r θ)

/-! ## The section quotient is actual cochain-complex homology -/

/-- The normalized two-open Cech complex has actual sections in degrees
zero and one and a zero tail. -/
def sectionComplexObject (r θ : ℂ) : ℕ → ModuleCat P
  | 0 => ModuleCat.of P (FirstSections r θ × SecondSections r θ)
  | 1 => ModuleCat.of P (OverlapSections r θ)
  | _ + 2 => ModuleCat.of P (Fin 0 → P)

def sectionComplexDifferential (r θ : ℂ) :
    (n : ℕ) → (sectionComplexObject r θ n ⟶ sectionComplexObject r θ (n + 1))
  | 0 => ModuleCat.ofHom (sectionCoboundary r θ)
  | _ + 1 => 0

theorem sectionComplexDifferential_comp (r θ : ℂ) (n : ℕ) :
    sectionComplexDifferential r θ n ≫
      sectionComplexDifferential r θ (n + 1) = 0 := by
  cases n with
  | zero =>
      change ModuleCat.ofHom (sectionCoboundary r θ) ≫ 0 = 0
      exact CategoryTheory.Limits.comp_zero
  | succ n =>
      change (0 : sectionComplexObject r θ (n + 1) ⟶
        sectionComplexObject r θ (n + 2)) ≫ 0 = 0
      exact CategoryTheory.Limits.zero_comp

def sectionComplex (r θ : ℂ) : CochainComplex (ModuleCat P) ℕ :=
  CochainComplex.of (sectionComplexObject r θ) (sectionComplexDifferential r θ)
    (sectionComplexDifferential_comp r θ)

@[simp] theorem sectionComplex_d_zero (r θ : ℂ) :
    (sectionComplex r θ).d 0 1 = ModuleCat.ofHom (sectionCoboundary r θ) :=
  CochainComplex.of_d (sectionComplexObject r θ) (sectionComplexDifferential r θ) 0

@[simp] theorem sectionComplex_d_one (r θ : ℂ) :
    (sectionComplex r θ).d 1 2 = 0 :=
  CochainComplex.of_d (sectionComplexObject r θ) (sectionComplexDifferential r θ) 1

abbrev sectionShortComplex (r θ : ℂ) : ShortComplex (ModuleCat P) :=
  (sectionComplex r θ).sc' 0 1 2

def sectionOpcyclesIso (r θ : ℂ) :
    (sectionShortComplex r θ).opcycles ≅ ModuleCat.of P (SectionCech r θ) := by
  have hf : (sectionShortComplex r θ).f.hom = sectionCoboundary r θ :=
    congrArg ModuleCat.Hom.hom (sectionComplex_d_zero r θ)
  have h := (sectionShortComplex r θ).moduleCatOpcyclesIso
  change (sectionShortComplex r θ).opcycles ≅
    ModuleCat.of P ((OverlapSections r θ) ⧸
      LinearMap.range (sectionShortComplex r θ).f.hom) at h
  rw [hf] at h
  exact h

def sectionShortHomologyIso (r θ : ℂ) :
    (sectionShortComplex r θ).homology ≅ ModuleCat.of P (SectionCech r θ) :=
  (sectionShortComplex r θ).asIsoHomologyι (sectionComplex_d_one r θ) ≪≫
    sectionOpcyclesIso r θ

/-- This is Mathlib homology of the complex of actual sheaf sections;
it is not declared to be derived sheaf cohomology. -/
def sectionHomologyIso (r θ : ℂ) :
    (sectionComplex r θ).homology 1 ≅ ModuleCat.of P (SectionCech r θ) :=
  (sectionComplex r θ).homologyIsoSc' 0 1 2
    ((ComplexShape.up ℕ).prev_eq' (show (ComplexShape.up ℕ).Rel 0 1 from rfl))
    ((ComplexShape.up ℕ).next_eq' (show (ComplexShape.up ℕ).Rel 1 2 from rfl)) ≪≫
      sectionShortHomologyIso r θ

def scalarToSectionHomology (r θ : ℂ) :
    ScalarCech r θ →ₗ[P] (sectionComplex r θ).homology 1 :=
  (sectionHomologyIso r θ).inv.hom.comp
    (scalarCechSectionsEquiv r θ).toLinearMap

@[simp] theorem sectionHomologyIso_scalar (r θ : ℂ) (z : ScalarCech r θ) :
    (sectionHomologyIso r θ).hom (scalarToSectionHomology r θ z) =
      scalarCechSectionsEquiv r θ z := by
  change (sectionHomologyIso r θ).hom
    ((sectionHomologyIso r θ).inv (scalarCechSectionsEquiv r θ z)) = _
  have h := congrArg
    (fun f : ModuleCat.of P (SectionCech r θ) ⟶ ModuleCat.of P (SectionCech r θ) =>
      f (scalarCechSectionsEquiv r θ z)) (sectionHomologyIso r θ).inv_hom_id
  change (sectionHomologyIso r θ).hom
    ((sectionHomologyIso r θ).inv (scalarCechSectionsEquiv r θ z)) =
      scalarCechSectionsEquiv r θ z at h
  exact h

theorem scalarToSectionHomology_injective (r θ : ℂ) :
    Function.Injective (scalarToSectionHomology r θ) := by
  intro x y hxy
  apply (scalarCechSectionsEquiv r θ).injective
  have h := congrArg (fun z => (sectionHomologyIso r θ).hom z) hxy
  change (sectionHomologyIso r θ).hom (scalarToSectionHomology r θ x) =
    (sectionHomologyIso r θ).hom (scalarToSectionHomology r θ y) at h
  exact (sectionHomologyIso_scalar r θ x).symm.trans
    (h.trans (sectionHomologyIso_scalar r θ y))

/-! ## The existing nonzero classes as actual sheaf-section classes -/

open CycleQ2GeometricSerre CycleQ2NormalKoszulBridge
  CycleQ2SeedBoundaryProjection

def normalizationSectionClass (r : ℂ) (hr : r ≠ 0) : SectionCech r 0 :=
  scalarCechSectionsEquiv r 0 (normalizationCechClass r hr)

theorem normalizationSectionClass_ne_zero (r : ℂ) (hr : r ≠ 0)
    (hcube : r ^ 3 = 2) : normalizationSectionClass r hr ≠ 0 := by
  intro h
  apply normalizationCechClass_ne_zero r hr hcube
  apply (scalarCechSectionsEquiv r 0).injective
  simpa only [normalizationSectionClass, map_zero] using h

def ambientPairingSectionClass (r : ℂ) (hr : r ≠ 0) (v : Fin 9 → ℂ) :
    SectionCech r 0 :=
  scalarCechSectionsEquiv r 0
    (cubicNormalClass r hr (deformationCubic v) (ambientNormalClass r) : ScalarCech r 0)

/-- The selected polynomial fraction represents the same actual section
class as the trace pairing of the normal connecting class. -/
theorem ambientPairingSectionClass_eq (r : ℂ) (hr : r ≠ 0) (v : Fin 9 → ℂ) :
    ambientPairingSectionClass r hr v =
      Submodule.Quotient.mk
        (overlapSectionsEquiv r 0 (pairedNormalOverlap r 0 (cubicDeformation v))) := by
  rw [ambientPairingSectionClass, ambientPairing_coe, scalarCechSectionsEquiv_mk]

theorem ambientPairingSectionClass_ne_zero (r : ℂ) (hr : r ≠ 0)
    (v : Fin 9 → ℂ) (hv : derivativeTrace 0 v ≠ 0) :
    ambientPairingSectionClass r hr v ≠ 0 := by
  intro h
  apply pairedScalarClass_ne_zero r 0 hr v hv
  apply (scalarCechSectionsEquiv r 0).injective
  simpa only [ambientPairingSectionClass, ambientPairing_coe, map_zero] using h

theorem selectedAmbientSectionClass_ne_zero (r : ℂ) (hr : r ≠ 0) :
    ambientPairingSectionClass r hr selectedTangent ≠ 0 := by
  apply ambientPairingSectionClass_ne_zero r hr
  rw [selectedTangent_trace]
  norm_num

/-! ## From actual sections to derived sheaf cohomology -/


/-- The actual structure sheaf, with only its additive group retained. -/
def additiveStructureSheaf (r θ : ℂ) :
    Sheaf (Opens.grothendieckTopology (cone r θ)) AddCommGrpCat :=
  (sheafCompose _ (forget₂ CommRingCat RingCat ⋙
    forget₂ RingCat AddCommGrpCat)).obj (cone r θ).sheaf

/-- The standard derived category supplies Ext without an affine
acyclicity or geometric vanishing hypothesis. -/
local instance coneSheavesHasExt (r θ : ℂ) :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology (cone r θ)) AddCommGrpCat.{0}) :=
  HasExt.standard _

/-- Actual derived sheaf cohomology of the punctured open, in Mathlib's
`H'` convention, with the restricted structure sheaf. -/
abbrev ConeSheafH1 (r θ : ℂ) :=
  (additiveStructureSheaf r θ).H' 1 (puncturedOpen r θ)

/-- The genuine Mayer-Vietoris connecting map applied to an overlap
section using the canonical H^0/sections comparison. -/
def sectionsConnecting (r θ : ℂ) (hr : r ≠ 0) :
    OverlapSections r θ →+ ConeSheafH1 r θ :=
  ((coneMayerVietoris r θ hr).δ (additiveStructureSheaf r θ) 0 1 rfl).hom.comp
    (HZero.sectionsEquiv (additiveStructureSheaf r θ) (overlapPatch r θ)).symm.toAddMonoidHom

private theorem fromBiprod_sections (r θ : ℂ) (hr : r ≠ 0)
    (a : (additiveStructureSheaf r θ).H' 0 (firstPatch r θ))
    (b : (additiveStructureSheaf r θ).H' 0 (secondPatch r θ)) :
    HZero.sectionsEquiv (additiveStructureSheaf r θ) (overlapPatch r θ)
      ((coneMayerVietoris r θ hr).fromBiprod (additiveStructureSheaf r θ) 0
        ((AddCommGrpCat.biprodIsoProd _ _).inv (a, b))) =
      firstSectionsRestriction r θ
          (HZero.sectionsEquiv (additiveStructureSheaf r θ) (firstPatch r θ) a) -
        secondSectionsRestriction r θ
          (HZero.sectionsEquiv (additiveStructureSheaf r θ) (secondPatch r θ) b) := by
  rw [GrothendieckTopology.MayerVietorisSquare.fromBiprod_biprodIsoProd_inv_apply,
    map_sub]
  have ha := HZero.sectionsEquiv_naturality (additiveStructureSheaf r θ)
    (g := homOfLE (PrimeSpectrum.basicOpen_mul_le_left (curveG1 r θ) (curveG2 r θ))) a
  have hb := HZero.sectionsEquiv_naturality (additiveStructureSheaf r θ)
    (g := homOfLE (PrimeSpectrum.basicOpen_mul_le_right (curveG1 r θ) (curveG2 r θ))) b
  exact congrArg₂ (· - ·) ha hb

theorem sectionsConnecting_coboundary (r θ : ℂ) (hr : r ≠ 0)
    (x : FirstSections r θ) (y : SecondSections r θ) :
    sectionsConnecting r θ hr (sectionCoboundary r θ (x, y)) = 0 := by
  let F := additiveStructureSheaf r θ
  let S := coneMayerVietoris r θ hr
  let a := (HZero.sectionsEquiv F (firstPatch r θ)).symm x
  let b := (HZero.sectionsEquiv F (secondPatch r θ)).symm y
  let z := (AddCommGrpCat.biprodIsoProd _ _).inv (a, b)
  have hz : (HZero.sectionsEquiv F (overlapPatch r θ)).symm
      (sectionCoboundary r θ (x, y)) = S.fromBiprod F 0 z := by
    apply (HZero.sectionsEquiv F (overlapPatch r θ)).injective
    rw [AddEquiv.apply_symm_apply]
    change sectionCoboundary r θ (x, y) =
      HZero.sectionsEquiv (additiveStructureSheaf r θ) (overlapPatch r θ)
        ((coneMayerVietoris r θ hr).fromBiprod (additiveStructureSheaf r θ) 0
          ((AddCommGrpCat.biprodIsoProd _ _).inv (a, b)))
    rw [fromBiprod_sections]
    dsimp only [a, b, F]
    simp only [AddEquiv.apply_symm_apply, sectionCoboundary_apply]
  change S.δ F 0 1 rfl
    ((HZero.sectionsEquiv F (overlapPatch r θ)).symm
      (sectionCoboundary r θ (x, y))) = 0
  rw [hz]
  have h := congrArg
    (fun f : (F.H' 0 (firstPatch r θ) ⊞ F.H' 0 (secondPatch r θ)) ⟶
      ConeSheafH1 r θ => f z) (S.fromBiprod_δ F 0 1 rfl)
  exact h

/-- Exactness of Mayer-Vietoris identifies the entire kernel. No
vanishing of H^1 on either patch is needed for this injection. -/
theorem sectionsConnecting_ker (r θ : ℂ) (hr : r ≠ 0) :
    (sectionsConnecting r θ hr).ker = (sectionBoundaries r θ).toAddSubgroup := by
  ext z
  constructor
  · intro hz
    let F := additiveStructureSheaf r θ
    let S := coneMayerVietoris r θ hr
    have hz' : S.δ F 0 1 rfl
        ((HZero.sectionsEquiv F (overlapPatch r θ)).symm z) = 0 := hz
    obtain ⟨w, hw⟩ := (ShortComplex.ab_exact_iff _).mp
      ((S.sequence_exact F 0 1 rfl).exact 1)
        ((HZero.sectionsEquiv F (overlapPatch r θ)).symm z) hz'
    have hw' : S.fromBiprod F 0 w =
        (HZero.sectionsEquiv F (overlapPatch r θ)).symm z := hw
    obtain ⟨⟨a, b⟩, rfl⟩ :=
      (AddCommGrpCat.biprodIsoProd _ _).addCommGroupIsoToAddEquiv.symm.surjective w
    refine ⟨(HZero.sectionsEquiv F (firstPatch r θ) a,
      HZero.sectionsEquiv F (secondPatch r θ) b), ?_⟩
    have hh := congrArg (HZero.sectionsEquiv F (overlapPatch r θ)) hw'
    change HZero.sectionsEquiv (additiveStructureSheaf r θ) (overlapPatch r θ)
      ((coneMayerVietoris r θ hr).fromBiprod (additiveStructureSheaf r θ) 0
        ((AddCommGrpCat.biprodIsoProd _ _).inv (a, b))) =
      HZero.sectionsEquiv F (overlapPatch r θ)
        ((HZero.sectionsEquiv F (overlapPatch r θ)).symm z) at hh
    rw [fromBiprod_sections, AddEquiv.apply_symm_apply] at hh
    simpa only [sectionCoboundary_apply] using hh
  · rintro ⟨⟨x, y⟩, rfl⟩
    exact sectionsConnecting_coboundary r θ hr x y

/-- The actual section Cech quotient injects into actual derived sheaf
cohomology by the Mayer-Vietoris connecting homomorphism. -/
def sectionToSheafH1 (r θ : ℂ) (hr : r ≠ 0) :
    SectionCech r θ →+ ConeSheafH1 r θ :=
  QuotientAddGroup.lift (sectionBoundaries r θ).toAddSubgroup
    (sectionsConnecting r θ hr) (sectionsConnecting_ker r θ hr).symm.le

theorem sectionToSheafH1_injective (r θ : ℂ) (hr : r ≠ 0) :
    Function.Injective (sectionToSheafH1 r θ hr) :=
  (QuotientAddGroup.injective_lift_iff _ _ _).2
    (sectionsConnecting_ker r θ hr).symm

def scalarToSheafH1 (r θ : ℂ) (hr : r ≠ 0) :
    ScalarCech r θ →+ ConeSheafH1 r θ :=
  (sectionToSheafH1 r θ hr).comp
    (scalarCechSectionsEquiv r θ).toLinearMap.toAddMonoidHom

theorem scalarToSheafH1_injective (r θ : ℂ) (hr : r ≠ 0) :
    Function.Injective (scalarToSheafH1 r θ hr) :=
  (sectionToSheafH1_injective r θ hr).comp (scalarCechSectionsEquiv r θ).injective

def normalizationSheafClass (r : ℂ) (hr : r ≠ 0) : ConeSheafH1 r 0 :=
  scalarToSheafH1 r 0 hr (normalizationCechClass r hr)

theorem normalizationSheafClass_ne_zero (r : ℂ) (hr : r ≠ 0)
    (hcube : r ^ 3 = 2) : normalizationSheafClass r hr ≠ 0 := by
  intro h
  apply normalizationCechClass_ne_zero r hr hcube
  apply scalarToSheafH1_injective r 0 hr
  simpa only [normalizationSheafClass, map_zero] using h

def ambientPairingSheafClass (r : ℂ) (hr : r ≠ 0) (v : Fin 9 → ℂ) :
    ConeSheafH1 r 0 :=
  sectionToSheafH1 r 0 hr (ambientPairingSectionClass r hr v)

theorem ambientPairingSheafClass_ne_zero (r : ℂ) (hr : r ≠ 0)
    (v : Fin 9 → ℂ) (hv : derivativeTrace 0 v ≠ 0) :
    ambientPairingSheafClass r hr v ≠ 0 := by
  intro h
  apply ambientPairingSectionClass_ne_zero r hr v hv
  apply sectionToSheafH1_injective r 0 hr
  simpa only [ambientPairingSheafClass, map_zero] using h

theorem selectedAmbientSheafClass_ne_zero (r : ℂ) (hr : r ≠ 0) :
    ambientPairingSheafClass r hr selectedTangent ≠ 0 := by
  apply ambientPairingSheafClass_ne_zero r hr
  rw [selectedTangent_trace]
  norm_num

/-! ## The literal incidence seed and its actual fixed-sextic tangent

These classes use theta = 1 and literal r = 57. Their cubic comes from the
proved kernel of the actual incidence Jacobian, rather than an unrelated
test vector. No relation r^3 = 2 is used.
-/

def incidenceCubicCoefficients : Fin 9 → ℂ := fun j =>
  CycleQ2IncidenceTraceDirection.parameterDirection
    (Sum.inl (CycleQ2SegreModularDetectorMatrixBinding.cubicIndex j))

theorem incidenceCubic_trace_one : derivativeTrace 1 incidenceCubicCoefficients = 1 :=
  CycleQ2IncidenceTraceDirection.traceWeights_eq_checked_seed_trace.symm.trans
    CycleQ2IncidenceTraceDirection.traceWeights_parameterDirection

/-- The four-variable cubic is the restriction of the actual invariant
cubic part of the chosen fixed-sextic incidence tangent. -/
theorem incidenceCubic_eq :
    cubicDeformation incidenceCubicCoefficients =
      substitute (CycleQ2IncidenceNormalForm.fullInvariantPolynomial 3
        (fun j => CycleQ2IncidenceTraceDirection.parameterDirection (Sum.inl j))) :=
  (CycleQ2IncidenceCubicCechTrace.substitute_cubic
    (fun j => CycleQ2IncidenceTraceDirection.parameterDirection (Sum.inl j))).symm

/-- The actual ambient-test normal connecting representative, paired with
the actual incidence tangent's cubic, modulo every localization boundary. -/
def incidenceScalarClass : ScalarCech 57 1 :=
  Submodule.Quotient.mk
    (pairedConnectingRepresentative 57 1 (cubicDeformation incidenceCubicCoefficients))

theorem incidenceScalarClass_eq : incidenceScalarClass =
    (Submodule.Quotient.mk
      (pairedNormalOverlap 57 1 (cubicDeformation incidenceCubicCoefficients)) :
        ScalarCech 57 1) := by
  rw [incidenceScalarClass, pairedConnectingRepresentative_eq]

theorem incidenceScalarClass_ne_zero : incidenceScalarClass ≠ 0 := by
  rw [incidenceScalarClass_eq]
  apply pairedScalarClass_ne_zero 57 1 (by norm_num)
  rw [incidenceCubic_trace_one]
  norm_num

/-- The paired normal class at the literal incidence seed in actual
derived structure-sheaf cohomology of the punctured cone. -/
def incidenceSheafClass : ConeSheafH1 57 1 :=
  scalarToSheafH1 57 1 (by norm_num) incidenceScalarClass

theorem incidenceSheafClass_ne_zero : incidenceSheafClass ≠ 0 := by
  intro h
  apply incidenceScalarClass_ne_zero
  apply scalarToSheafH1_injective 57 1 (by norm_num)
  simpa only [incidenceSheafClass, map_zero] using h

end CycleQ2GeometricConeCech

end
