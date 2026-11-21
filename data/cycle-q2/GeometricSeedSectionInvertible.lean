import Proposal.GeometricSeedSectionDivisorTransitions
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

/-!
# Local rank-one trivializations of the actual global source and curve ideal

The original matrix pivots give actual basic opens of the original
projective surface. They cover it, by the original unit-ideal certificate.
The previously constructed kernel generators form compatible families
on every subopen and therefore define native sheaf morphisms from the
structure module. These morphisms are isomorphisms, checked on sections
of every open, not just on global sections of a chart.

Consequently the independently defined twisted source and the native
ideal of every regular original section curve have rank-one local
trivializations around every point of the actual surface.

Prepared for fqlx with OpenAI ChatGPT assistance; see solution.md for
the geometric attribution and the separate protected residue gap.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2SeedSectionInvertible

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open CycleQ2SeedProjectiveImageChart CycleQ2SeedProjectiveImageCocycle
  CycleQ2SeedSectionSheaf CycleQ2SeedSectionSheafLocal
  CycleQ2SeedSectionSheafGlobal CycleQ2SeedSectionDivisorFrames
  CycleQ2SeedSectionDivisorTransitions CycleQ2SeedSectionSheafIso
  CycleQ2SeedSectionSheafKernel CycleQ2SeedSectionAffineInjective

variable {U : Surface.Opens}

abbrev sourceOn (U : Surface.Opens) : U.toScheme.Modules :=
  (Scheme.Modules.restrictFunctor U.ι).obj twistedIdeal

theorem image_le (U : Surface.Opens) (W : U.toScheme.Opens) : U.ι ''ᵁ W ≤ U := by
  simpa only [Scheme.Opens.opensRange_ι] using U.ι.image_le_opensRange W

/-- A compatible family of the original generators on the actual open subscheme. -/
def frameSections (f : FrameData U) : SheafOfModules.sections (sourceOn U) :=
  PresheafOfModules.sectionsMk
    (fun O => sourceGenerator f.chart (U.ι ''ᵁ O.unop)
      ((image_le U O.unop).trans f.within) f.pivot.1)
    (by
      intro O P h
      have hPO : U.ι ''ᵁ P.unop ≤ U.ι ''ᵁ O.unop :=
        leOfHom (U.ι.opensFunctor.map h.unop)
      change moduleRes twistedIdeal hPO
        (sourceGenerator f.chart (U.ι ''ᵁ O.unop)
          ((image_le U O.unop).trans f.within) f.pivot.1) = _
      exact sourceGenerator_restrict f.chart (U.ι ''ᵁ O.unop) (U.ι ''ᵁ P.unop)
        hPO ((image_le U O.unop).trans f.within) f.pivot.1)

/-- A morphism of the existing sheaves, obtained from the actual compatible section. -/
def frameHom (f : FrameData U) : structureModule U.toScheme ⟶ sourceOn U :=
  (SheafOfModules.unitHomEquiv (sourceOn U)).symm (frameSections f)

theorem frameHom_app (f : FrameData U) (W : U.toScheme.Opens)
    (r : Γ(U.toScheme, W)) :
    (frameHom f).app W r =
      (U.ι.appIso W).inv r • sourceGenerator f.chart (U.ι ''ᵁ W)
        ((image_le U W).trans f.within) f.pivot.1 := rfl

theorem frameHom_app_bijective (f : FrameData U) (W : U.toScheme.Opens) :
    Function.Bijective ((frameHom f).app W) := by
  let g : FrameData (U.ι ''ᵁ W) := f.restrict (image_le U W)
  have hframe : Function.Bijective
      (fun r : Γ(Surface, U.ι ''ᵁ W) => r • generator g) :=
    ⟨generator_scalar_injective g,
      sourceFrameMap_surjective g.chart (U.ι ''ᵁ W) g.within
        g.pivot g.pivotUnit g.pivot_eq⟩
  exact hframe.comp (ConcreteCategory.bijective_of_isIso (U.ι.appIso W).inv)

instance frameHom_isIso (f : FrameData U) : IsIso (frameHom f) :=
  Scheme.Modules.Hom.isIso_iff_isIso_app.mpr fun W =>
    (ConcreteCategory.isIso_iff_bijective _).mpr (frameHom_app_bijective f W)

/-- A genuine local sheaf isomorphism, with the previously specified generator. -/
def sourceIso (f : FrameData U) : structureModule U.toScheme ≅ sourceOn U :=
  asIso (frameHom f)

/-! ## Actual basic opens covering the original surface -/

section UnitIdeal

variable {R S : Type*} [CommRing R] [CommRing S]

theorem span_map_top {ι : Type*} (a : ι → R)
    (ha : Ideal.span (Set.range a) = ⊤) (φ : R →+* S) :
    Ideal.span (Set.range (fun i => φ (a i))) = ⊤ := by
  have h := congrArg (Ideal.map φ) ha
  simpa only [Ideal.map_span, ← Set.range_comp, Ideal.map_top, Function.comp_def] using h

theorem exists_unit_of_span_top {ι : Type*} [IsLocalRing R] (a : ι → R)
    (ha : Ideal.span (Set.range a) = ⊤) : ∃ i, IsUnit (a i) := by
  classical
  by_contra! h
  have hle : Ideal.span (Set.range a) ≤ IsLocalRing.maximalIdeal R := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact (IsLocalRing.mem_maximalIdeal (R := R) (a i)).mpr (h i)
  have hone : (1 : R) ∈ IsLocalRing.maximalIdeal R := hle (by rw [ha]; trivial)
  exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top
    (Ideal.eq_top_of_isUnit_mem _ hone isUnit_one)

end UnitIdeal

def pivotOpen (i : Fin 3) (p : Fin 3 × Fin 3) : Surface.Opens :=
  Surface.basicOpen (sectionMatrix i (Patch i) le_rfl p.1 p.2)

theorem pivotOpen_le (i : Fin 3) (p : Fin 3 × Fin 3) : pivotOpen i p ≤ Patch i :=
  Surface.basicOpen_le _

theorem pivotOpen_pivot_unit (i : Fin 3) (p : Fin 3 × Fin 3) :
    IsUnit (sectionMatrix i (pivotOpen i p) (pivotOpen_le i p) p.1 p.2) := by
  have h := RingedSpace.isUnit_res_basicOpen Surface.toLocallyRingedSpace.toRingedSpace
    (sectionMatrix i (Patch i) le_rfl p.1 p.2)
  change IsUnit (targetRes (pivotOpen_le i p) (sectionMatrix i (Patch i) le_rfl p.1 p.2)) at h
  rwa [sectionMatrix_restrict] at h

def pivotFrameData (i : Fin 3) (p : Fin 3 × Fin 3) : FrameData (pivotOpen i p) where
  chart := i
  within := pivotOpen_le i p
  pivot := p
  pivotUnit := (pivotOpen_pivot_unit i p).unit
  pivot_eq := (pivotOpen_pivot_unit i p).unit_spec

theorem exists_pivotOpen_at (x : Surface) :
    ∃ (i : Fin 3) (p : Fin 3 × Fin 3), x ∈ pivotOpen i p := by
  have hx : x ∈ ⨆ i : Fin 3, Patch i := by rw [patch_cover]; trivial
  obtain ⟨i, hxi⟩ := Opens.mem_iSup.mp hx
  let φ : AffineRing i →+* Surface.presheaf.stalk x :=
    (Surface.presheaf.germ (Patch i) x hxi).hom.comp (chartSectionMap i (Patch i) le_rfl)
  have hspan := span_map_top (fun p : Fin 3 × Fin 3 =>
    (chartFactorData i).matrix p.1 p.2) (chartFactorData i).entries_generate φ
  obtain ⟨p, hp⟩ := exists_unit_of_span_top _ hspan
  refine ⟨i, p, ?_⟩
  exact (Surface.mem_basicOpen _ x hxi).mpr hp

/-- Every actual point has a rank-one trivialization of the original global kernel. -/
theorem exists_source_local_trivialization (x : Surface) :
    ∃ U : Surface.Opens, x ∈ U ∧ Nonempty (structureModule U.toScheme ≅ sourceOn U) := by
  obtain ⟨i, p, hx⟩ := exists_pivotOpen_at x
  exact ⟨pivotOpen i p, hx, ⟨sourceIso (pivotFrameData i p)⟩⟩

/-- The same native curve ideal is invertible around every original surface point. -/
theorem exists_curveIdeal_local_trivialization (t : Fin 3 → ℂ)
    (hreg : ∀ i : Fin 3, ChartRegular t i) (x : Surface) :
    ∃ U : Surface.Opens, x ∈ U ∧ Nonempty
      (structureModule U.toScheme ≅ (Scheme.Modules.restrictFunctor U.ι).obj (curveIdeal t)) := by
  obtain ⟨U, hx, ⟨e⟩⟩ := exists_source_local_trivialization x
  exact ⟨U, hx, ⟨e ≪≫ (Scheme.Modules.restrictFunctor U.ι).mapIso
    (twistedIdealCurveIso t hreg)⟩⟩

open CycleQ2FirstOrderCurve CycleQ2FirstOrderCurveSeedFiber
  CycleQ2FirstOrderCurveChartFlat CycleQ2SpecializedProjectiveCurve
  CycleQ2IncidencePolynomialJacobianBinding CycleQ2SeedSectionIdealComparison

attribute [local instance] CycleQ2IncidenceFirstOrder.firstOrderAlgebra

/-- The existing simultaneous witness has an invertible native curve ideal.
No second section vector, local-freeness premise, or replacement curve is used. -/
theorem exists_flat_curve_and_invertible_ideal_in_principal_open
    (P : MvPolynomial (Fin 3) ℂ) (hP : P ≠ 0) :
    ∃ t : Fin 3 → ℂ, MvPolynomial.eval t P ≠ 0 ∧ t ≠ 0 ∧
      AlgebraicGeometry.Flat (firstOrderCurveToBase t) ∧
      AlgebraicGeometry.IsProper (firstOrderCurveToBase t) ∧
      Nonempty (specializedCurve
        (seedPoint (57 : ℂ) Complex.I) t ≅ FirstOrderCurveSeedFiber t) ∧
      Nonempty (specializedCurve (seedPoint (57 : ℂ) Complex.I) t) ∧
      Nonempty (FirstOrderCurveSeedFiber t) ∧
      (∀ (i : Fin 4) (p : Pivot),
        IsSMulRegular (SeedRefinement i p) (seedRefinedEquation t i p)) ∧
      (∀ i : Fin 3, ChartRegular t i) ∧ Mono (globalEvaluation t) ∧
      Nonempty (twistedIdeal ≅ curveIdeal t) ∧
      (∀ x : Surface, ∃ U : Surface.Opens, x ∈ U ∧ Nonempty
        (structureModule U.toScheme ≅
          (Scheme.Modules.restrictFunctor U.ι).obj (curveIdeal t))) := by
  obtain ⟨t, htP, ht, hflat, hproper, hiso, hseed, hfiber, hfirst, hreg, hmono, hideal⟩ :=
    exists_flat_curve_and_global_ideal_iso_in_principal_open P hP
  exact ⟨t, htP, ht, hflat, hproper, hiso, hseed, hfiber, hfirst,
    hreg, hmono, hideal, exists_curveIdeal_local_trivialization t hreg⟩

end CycleQ2SeedSectionInvertible

end

#print axioms CycleQ2SeedSectionInvertible.sourceIso
#print axioms CycleQ2SeedSectionInvertible.exists_source_local_trivialization
#print axioms CycleQ2SeedSectionInvertible.exists_curveIdeal_local_trivialization
#print axioms CycleQ2SeedSectionInvertible.exists_flat_curve_and_invertible_ideal_in_principal_open
