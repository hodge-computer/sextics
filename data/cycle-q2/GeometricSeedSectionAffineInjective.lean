import Proposal.GeometricSeedSectionIdealComparison
import Proposal.GeometricSeedSectionSheafEvaluation

/-!
# The original section functional is injective on each whole affine chart

The same regularity witness previously supplied on all nine matrix-pivot
refinements now proves injectivity on the original affine ring itself.
Vanishing after each localization implies vanishing before localization:
the radical of the element's annihilator contains the pivot ideal, which
is the unit ideal. No injectivity of an individual localization is used.

The resulting linear equivalence has the original three-row ideal as its
target. Its value is the original functional. Injectivity is transported
to every associated-sheaf section, every original projective chart, and
the actual pushed-forward evaluation morphisms.

Source-only draft: no Lean elaboration, Lake build, or kernel replay was
run. Prepared for fqlx with OpenAI ChatGPT assistance; see solution.md
for the geometric route, attribution, and remaining exactness obligation.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2SeedSectionAffineInjective

open CategoryTheory AlgebraicGeometry Matrix
open CycleQ2SegreFactorSequence CycleQ2SegreLinkageDuality
  CycleQ2SeedProjectiveImageChart CycleQ2SeedImageLocalization
  CycleQ2SeedSectionInverse CycleQ2SeedSectionIdealComparison
  CycleQ2SeedSectionBalance

section LocalizationCover

variable {R : Type*} [CommRing R]

/-- A family of principal localizations whose elements generate the unit
ideal jointly detects zero, including in rings with zero divisors. -/
theorem eq_zero_of_away_cover {ι : Type*} (p : ι → R)
    (hp : Ideal.span (Set.range p) = ⊤) (x : R)
    (hx : ∀ i, algebraMap R (Localization.Away (p i)) x = 0) : x = 0 := by
  let J : Ideal R :=
    { carrier := {a | a * x = 0}
      zero_mem' := by simp
      add_mem' := by
        intro a b ha hb
        change a * x = 0 at ha
        change b * x = 0 at hb
        change (a + b) * x = 0
        rw [add_mul, ha, hb, add_zero]
      smul_mem' := by
        intro a b hb
        change b * x = 0 at hb
        change (a * b) * x = 0
        rw [mul_assoc, hb, mul_zero] }
  have hrad : ∀ i, p i ∈ J.radical := by
    intro i
    obtain ⟨s, hs⟩ := (IsLocalization.map_eq_zero_iff
      (Submonoid.powers (p i)) (Localization.Away (p i)) x).mp (hx i)
    obtain ⟨n, hn⟩ := s.property
    refine ⟨n, ?_⟩
    change p i ^ n * x = 0
    rw [hn]
    exact hs
  have hle : Ideal.span (Set.range p) ≤ J.radical := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact hrad i
  have hone : (1 : R) ∈ J.radical := hle (by rw [hp]; trivial)
  obtain ⟨n, hn⟩ := hone
  change (1 : R) ^ n * x = 0 at hn
  simpa only [one_pow, one_mul] using hn

end LocalizationCover

section OriginalFunctional

variable {R S : Type*} [CommRing R] [CommRing S]

/-- The actual functional commutes with the literal coefficient map and
the original extended-ideal map, with the same coefficient vector. -/
theorem sectionFunctional_baseChange (F : FactorData R) (f : R →+* S)
    (hf : Function.Injective (fun z : S => f F.linkage * z))
    (t : Fin 3 → R) (x : F.leftIdeal) :
    sectionFunctional (mapFactorData F f hf) (fun b => f (t b))
        (mappedLeft F f hf x) = f (sectionFunctional F t x) := by
  apply (mapFactorData F f hf).regular
  calc
    _ = (mappedLeft F f hf x : S) *
        ∑ b, f (t b) * (mapFactorData F f hf).right b :=
      sectionFunctional_balance (mapFactorData F f hf)
        (fun b => f (t b)) (mappedLeft F f hf x)
    _ = f ((x : R) * ∑ b, t b * F.right b) := by
      change f (x : R) * (∑ b, f (t b) * f (F.right b)) = _
      simp only [map_mul, map_sum]
    _ = f (F.linkage * sectionFunctional F t x) :=
      congrArg f (sectionFunctional_balance F t x).symm
    _ = _ := map_mul f _ _

abbrev PivotRing (F : FactorData R) (p : Fin 3 × Fin 3) :=
  Localization.Away (F.matrix p.1 p.2)

def pivotData (F : FactorData R) (p : Fin 3 × Fin 3) :
    FactorData (PivotRing F p) :=
  localizedFactorData F (Submonoid.powers (F.matrix p.1 p.2)) (PivotRing F p)

def pivotVector (F : FactorData R) (t : Fin 3 → R) (p : Fin 3 × Fin 3) :
    Fin 3 → PivotRing F p :=
  fun b => algebraMap R (PivotRing F p) (t b)

theorem pivotFunctional_original (F : FactorData R) (t : Fin 3 → R)
    (p : Fin 3 × Fin 3) (x : F.leftIdeal) :
    sectionFunctional (pivotData F p) (pivotVector F t p)
        (localizedLeft F (Submonoid.powers (F.matrix p.1 p.2)) (PivotRing F p) x) =
      algebraMap R (PivotRing F p) (sectionFunctional F t x) :=
  sectionFunctional_baseChange F (algebraMap R (PivotRing F p))
    (localization_linkage_regular F
      (Submonoid.powers (F.matrix p.1 p.2)) (PivotRing F p)) t x

/-- The actual nine-pivot regularity premise proves injectivity on the
whole original ideal, rather than only on its refinements. -/
theorem sectionFunctional_injective_of_pivot_regular (F : FactorData R)
    (t : Fin 3 → R)
    (hreg : ∀ p : Fin 3 × Fin 3, IsSMulRegular (PivotRing F p)
      (((pivotData F p).matrix *ᵥ pivotVector F t p) p.1)) :
    Function.Injective (sectionFunctional F t) := by
  intro x y hxy
  apply Subtype.ext
  apply sub_eq_zero.mp
  apply eq_zero_of_away_cover (fun p : Fin 3 × Fin 3 => F.matrix p.1 p.2)
    F.entries_generate
  intro p
  have he :
      localizedLeft F (Submonoid.powers (F.matrix p.1 p.2)) (PivotRing F p) x =
      localizedLeft F (Submonoid.powers (F.matrix p.1 p.2)) (PivotRing F p) y := by
    apply sectionFunctional_injective_of_regular_row
      (pivotData F p) (pivotVector F t p) p.1 (hreg p)
    rw [pivotFunctional_original, pivotFunctional_original, hxy]
  have hv := congrArg Subtype.val he
  change algebraMap R (PivotRing F p) (x : R) =
    algebraMap R (PivotRing F p) (y : R) at hv
  rw [map_sub, hv, sub_self]

end OriginalFunctional

/-! ## Binding the same regular vector to the original affine charts -/

def ChartRegular (t : Fin 3 → ℂ) (i : Fin 3) : Prop :=
  ∀ p : Pivot, IsSMulRegular (LinkageRefinement i p)
    (((refinedFactorData i p).matrix *ᵥ refinedVector t i p) p.1)

theorem affineFunctional_injective (t : Fin 3 → ℂ) (i : Fin 3)
    (hreg : ChartRegular t i) :
    Function.Injective (sectionFunctional (chartFactorData i)
      (fun b => algebraMap ℂ (AffineRing i) (t b))) := by
  apply sectionFunctional_injective_of_pivot_regular
  intro p
  have ht : pivotVector (chartFactorData i)
      (fun b => algebraMap ℂ (AffineRing i) (t b)) p = refinedVector t i p := by
    funext b
    change algebraMap (AffineRing i) (LinkageRefinement i p)
      (algebraMap ℂ (AffineRing i) (t b)) =
        algebraMap ℂ (LinkageRefinement i p) (t b)
    exact (IsScalarTower.algebraMap_apply ℂ (AffineRing i)
      (LinkageRefinement i p) (t b)).symm
  change IsSMulRegular (LinkageRefinement i p)
    (((refinedFactorData i p).matrix *ᵥ pivotVector (chartFactorData i)
      (fun b => algebraMap ℂ (AffineRing i) (t b)) p) p.1)
  rw [ht]
  exact hreg p

/-- The target is the original row ideal on the entire coordinate chart. -/
def affineSectionIdealEquiv (t : Fin 3 → ℂ) (i : Fin 3)
    (hreg : ChartRegular t i) :
    OrbitIdeal i ≃ₗ[AffineRing i]
      rowIdeal (chartFactorData i) (fun b => algebraMap ℂ (AffineRing i) (t b)) :=
  (LinearEquiv.ofInjective
      (sectionFunctional (chartFactorData i) (fun b => algebraMap ℂ (AffineRing i) (t b)))
      (affineFunctional_injective t i hreg)).trans
    (LinearEquiv.ofEq _ _ (sectionFunctional_range _ _))

theorem affineSectionIdealEquiv_val (t : Fin 3 → ℂ) (i : Fin 3)
    (hreg : ChartRegular t i) (x : OrbitIdeal i) :
    (affineSectionIdealEquiv t i hreg x : AffineRing i) =
      sectionFunctional (chartFactorData i)
        (fun b => algebraMap ℂ (AffineRing i) (t b)) x := rfl

/-! ## Injectivity on the actual sheaves and all their section modules -/

open CycleQ2SeedSectionSheaf CycleQ2SeedSectionSheafEvaluation
  CycleQ2SeedImageSheafEmbedding CycleQ2SeedProjectiveImageCocycle
  CycleQ2GeometricSurfaceDehomogenizedCharts

theorem affineEvaluation_app_injective (t : Fin 3 → ℂ) (i : Fin 3)
    (hreg : ChartRegular t i) (U : (Spec (CommRingCat.of (AffineRing i))).Opens) :
    Function.Injective ((affineEvaluation t i).app U) := by
  intro s r h
  apply tilde_map_app_injective
    (ModuleCat.ofHom (sectionFunctional (chartFactorData i)
      (fun b => algebraMap ℂ (AffineRing i) (t b))))
    (affineFunctional_injective t i hreg) U
  apply iso_app_injective (tildeSelf (R := CommRingCat.of (AffineRing i))) U
  exact h

theorem chartEvaluation_app_injective (t : Fin 3 → ℂ) (i : Fin 3)
    (hreg : ChartRegular t i) (U : (Patch i).toScheme.Opens) :
    Function.Injective ((chartEvaluation t i).app U) := by
  intro s r h
  have he := iso_app_injective
    (Scheme.Modules.restrictUnitIso (coordinateAffineChart 57 1 i.succ).hom) U h
  exact affineEvaluation_app_injective t i hreg
    ((coordinateAffineChart 57 1 i.succ).hom ''ᵁ U) he

theorem patchEvaluation_app_injective (t : Fin 3 → ℂ) (i : Fin 3)
    (hreg : ChartRegular t i) (V : Surface.Opens) :
    Function.Injective ((patchEvaluation t i).app V) :=
  chartEvaluation_app_injective t i hreg ((Patch i).ι ⁻¹ᵁ V)

/-- The original simultaneous choice now gives whole-chart ideal
equivalences, retaining the first-order regularity of the same vector. -/
theorem exists_one_vector_with_affine_ideal_equivalences :
    ∃ t : Fin 3 → ℂ, t ≠ 0 ∧
      (∀ (i : Fin 4) (p : Pivot),
        IsSMulRegular (CycleQ2FirstOrderCurveChartFlat.SeedRefinement i p)
          (CycleQ2FirstOrderCurveChartFlat.seedRefinedEquation t i p)) ∧
      ∀ i : Fin 3, ChartRegular t i ∧
        ∃ e : OrbitIdeal i ≃ₗ[AffineRing i]
          rowIdeal (chartFactorData i) (fun b => algebraMap ℂ (AffineRing i) (t b)),
          ∀ x, (e x : AffineRing i) = sectionFunctional (chartFactorData i)
            (fun b => algebraMap ℂ (AffineRing i) (t b)) x := by
  obtain ⟨t, ht, hfirst, hlinkage⟩ := exists_one_vector_regular
  refine ⟨t, ht, hfirst, ?_⟩
  intro i
  exact ⟨hlinkage i, affineSectionIdealEquiv t i (hlinkage i),
    affineSectionIdealEquiv_val t i (hlinkage i)⟩

end CycleQ2SeedSectionAffineInjective

end

#print axioms CycleQ2SeedSectionAffineInjective.eq_zero_of_away_cover
#print axioms CycleQ2SeedSectionAffineInjective.sectionFunctional_injective_of_pivot_regular
#print axioms CycleQ2SeedSectionAffineInjective.affineSectionIdealEquiv
#print axioms CycleQ2SeedSectionAffineInjective.patchEvaluation_app_injective
#print axioms CycleQ2SeedSectionAffineInjective.exists_one_vector_with_affine_ideal_equivalences
