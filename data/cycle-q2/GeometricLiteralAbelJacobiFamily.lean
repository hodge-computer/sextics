import Proposal.GeometricFirstOrderCurveSeedFiber
import Proposal.GeometricRelativeRegularSection
import Proposal.GeometricSeedSectionNonempty
import Mathlib.AlgebraicGeometry.Morphisms.SmoothFiber
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.DualNumber

/-!
# Smooth neighborhoods of the original section curve

A field-valued point of the dual numbers kills the square-zero summand.
Consequently every residue fiber of the first-order section curve is obtained
by base change from its specialized projective seed curve. The fiber criterion
for smoothness then reduces smoothness to flatness and smoothness of that seed.

For the full incidence family, properness supplies the largest base open over
which the family is smooth. Checking the stalks of the original family along
the specialized projective curve determines whether this open contains the
seed. In that case, shrinking to the smooth image gives nonempty fibers.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralAbelJacobiFamily

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CycleQ2IncidencePolynomialJacobianBinding CycleQ2IncidenceFirstOrder
  CycleQ2FirstOrderCurve CycleQ2FirstOrderCurveSeedFiber CycleQ2SpecializedProjectiveCurve

private theorem factorThroughReduction {K : Type*} [Field K] (φ : DualNumber ℂ →+* K) :
    (φ.comp (algebraMap ℂ (DualNumber ℂ))).comp
      (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom = φ := by
  apply RingHom.ext
  intro x
  have h : φ (TrivSqZeroExt.inr x.snd) = 0 :=
    ((TrivSqZeroExt.isNilpotent_inr x.snd).map φ).eq_zero
  change φ (TrivSqZeroExt.inl x.fst) = φ x
  simpa only [map_add, h, add_zero] using congrArg φ x.inl_fst_add_inr_snd_eq

private theorem residuePoint_factor (y : Spec (CommRingCat.of (DualNumber ℂ))) :
    ∃ g : Spec ((Spec (CommRingCat.of (DualNumber ℂ))).residueField y) ⟶
      Spec (CommRingCat.of ℂ),
      g ≫ firstOrderClosedPoint =
        (Spec (CommRingCat.of (DualNumber ℂ))).fromSpecResidueField y := by
  let R := CommRingCat.of (DualNumber ℂ)
  let φ := algebraMap (DualNumber ℂ) y.asIdeal.ResidueField
  let a := Spec.map (Scheme.Spec.residueFieldIso R y).inv
  let b := CommRingCat.ofHom (φ.comp (algebraMap ℂ (DualNumber ℂ)))
  refine ⟨a ≫ Spec.map b, ?_⟩
  rw [← Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField, Category.assoc]
  congr 1
  rw [firstOrderClosedPoint, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  exact factorThroughReduction φ

/-- The original section family over the dual numbers is smooth precisely when
it is flat and its original complex projective section is smooth. -/
theorem firstOrderCurve_smooth_iff_flat_and_smooth_seed (t : Fin 3 → ℂ) :
    Smooth (firstOrderCurveToBase t) ↔
      Flat (firstOrderCurveToBase t) ∧
      Smooth (specializedCurveToBase (seedPoint (57 : ℂ) Complex.I) t) := by
  constructor
  · intro h
    refine ⟨inferInstance, ?_⟩
    rw [← firstOrderCurveSeedFiberIso_hom_fst]
    infer_instance
  · rintro ⟨hf, hs⟩
    have := firstOrderCurveToBase_proper t
    have : LocallyOfFinitePresentation (firstOrderCurveToBase t) :=
      LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr inferInstance
    have : Smooth (pullback.fst firstOrderClosedPoint (firstOrderCurveToBase t)) := by
      rw [← firstOrderCurveSeedFiberIso_inv_fst]
      infer_instance
    have : Smooth (pullback.snd (firstOrderCurveToBase t) firstOrderClosedPoint) := by
      rw [← pullbackSymmetry_hom_comp_fst (firstOrderCurveToBase t) firstOrderClosedPoint]
      infer_instance
    apply Smooth.of_smooth_fiberToSpecResidueField
    intro y
    change Smooth (pullback.snd (firstOrderCurveToBase t) (_))
    obtain ⟨g, hg⟩ := residuePoint_factor y
    rw [← hg, ← pullbackLeftPullbackSndIso_inv_snd_snd (firstOrderCurveToBase t)
      firstOrderClosedPoint g]
    infer_instance

open CycleQ2IncidenceEtaleParameter CycleQ2IncidenceChartFiberScheme
  CycleQ2IncidenceSeedFiberCover CycleQ2RelativeConstantCurve CycleQ2RelativeCurveNeighborhood
  CycleQ2RelativeCurveSeedProj CycleQ2RelativeCurveSeedFiberIso
  CycleQ2IncidenceProperNeighborhood

local instance relativeCurveProper (t : Fin 3 → ℂ) : IsProper (relativeCurveToBase incidencePoint t) :=
  relativeCurveToBase_proper incidencePoint t

local instance relativeCurveLfp (t : Fin 3 → ℂ) :
    LocallyOfFinitePresentation (relativeCurveToBase incidencePoint t) := by
  have := CycleQ2RelativeRegularSection.parameter_noetherian
  exact LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr inferInstance

/-- The largest open of the original incidence base over which every point
of the original section family is relatively smooth. -/
def smoothCurveBase (t : Fin 3 → ℂ) : parameterScheme.Opens :=
  properBaseNeighborhood (relativeCurveToBase incidencePoint t)
    (relativeCurveToBase incidencePoint t).smoothLocus

theorem le_smoothCurveBase_iff (t : Fin 3 → ℂ) (V : parameterScheme.Opens) :
    V ≤ smoothCurveBase t ↔ Smooth ((relativeCurveToBase incidencePoint t) ∣_ V) := by
  let f := relativeCurveToBase incidencePoint t
  let U := f ⁻¹ᵁ V
  rw [smoothCurveBase, le_properBaseNeighborhood_iff]
  constructor
  · intro hu
    have hs : Smooth (U.ι ≫ f) := by
      apply Scheme.Hom.smoothLocus_eq_top_iff.mp
      rw [← Scheme.Hom.preimage_smoothLocus_eq, ← top_le_iff]
      intro x _
      exact hu x.2
    apply MorphismProperty.of_postcomp (W' := @IsOpenImmersion) @Smooth (f ∣_ V) V.ι inferInstance
    simpa only [morphismRestrict_ι] using hs
  · intro hs
    have hcomp : Smooth (U.ι ≫ f) := by
      rw [← morphismRestrict_ι f V]
      infer_instance
    have he := (Scheme.Hom.smoothLocus_eq_top (U.ι ≫ f))
    rw [← Scheme.Hom.preimage_smoothLocus_eq] at he
    intro x hx
    change (⟨x, hx⟩ : U) ∈ U.ι ⁻¹ᵁ f.smoothLocus
    rw [he]
    trivial

/-- A check on the actual points of the specialized complex curve determines
whether the smooth open of the original moving family contains the seed. -/
theorem seed_mem_smoothCurveBase_iff (t : Fin 3 → ℂ) :
    seedBasePoint ∈ smoothCurveBase t ↔
      ∀ x : specializedCurve (seedPoint (57 : ℂ) Complex.I) t,
        ((relativeCurveToBase incidencePoint t).stalkMap (seedCurveToRelative t x)).hom.FormallySmooth := by
  rw [smoothCurveBase, mem_properBaseNeighborhood_iff]
  constructor
  · intro h x
    apply h
    rw [← Scheme.Hom.comp_apply, seedCurveToRelative_overBase, Scheme.Hom.comp_apply]
    exact congrArg seedParameterMorphism (Subsingleton.elim _ _)
  · intro h x hx
    obtain ⟨z, _, hz⟩ := Scheme.Pullback.exists_preimage_pullback
      (f := seedParameterMorphism) (g := relativeCurveToBase incidencePoint t)
      (default : Spec (CommRingCat.of ℂ)) x hx.symm
    have hpoint := h ((seedCurveFiberIso t).inv z)
    have he : seedCurveToRelative t ((seedCurveFiberIso t).inv z) = x := by
      rw [← Scheme.Hom.comp_apply, ← seedCurveFiberIso_hom_snd, Iso.inv_hom_id_assoc]
      exact hz
    rwa [he] at hpoint

/-- The original curve admits a smooth proper neighborhood with nonempty
fibers precisely when its original relative stalk maps are formally smooth
along the specialized seed. -/
theorem exists_smooth_proper_surjective_neighborhood_iff (t : Fin 3 → ℂ) :
    (∃ V : parameterScheme.Opens, seedBasePoint ∈ V ∧
      Smooth ((relativeCurveToBase incidencePoint t) ∣_ V) ∧
      IsProper ((relativeCurveToBase incidencePoint t) ∣_ V) ∧
      Function.Surjective ((relativeCurveToBase incidencePoint t) ∣_ V)) ↔
    ∀ x : specializedCurve (seedPoint (57 : ℂ) Complex.I) t,
      ((relativeCurveToBase incidencePoint t).stalkMap (seedCurveToRelative t x)).hom.FormallySmooth := by
  rw [← seed_mem_smoothCurveBase_iff]
  constructor
  · rintro ⟨V, hv, hs, _, _⟩
    exact (le_smoothCurveBase_iff t V).mpr hs hv
  · intro hs
    let f := relativeCurveToBase incidencePoint t
    let U := f ⁻¹ᵁ smoothCurveBase t
    have : Smooth (f ∣_ smoothCurveBase t) := (le_smoothCurveBase_iff t _).mp le_rfl
    have : Smooth (U.ι ≫ f) := by
      rw [← morphismRestrict_ι f (smoothCurveBase t)]
      infer_instance
    let V : parameterScheme.Opens := ⟨Set.range (U.ι ≫ f), (U.ι ≫ f).isOpenMap.isOpen_range⟩
    obtain ⟨x⟩ := CycleQ2SeedSectionNonempty.seed_specializedCurve_nonempty t
    have hx : f (seedCurveToRelative t x) = seedBasePoint := by
      change relativeCurveToBase incidencePoint t (seedCurveToRelative t x) = _
      rw [← Scheme.Hom.comp_apply, seedCurveToRelative_overBase, Scheme.Hom.comp_apply]
      exact congrArg seedParameterMorphism (Subsingleton.elim _ _)
    have hV : V ≤ smoothCurveBase t := by
      rintro _ ⟨z, rfl⟩
      exact z.2
    refine ⟨V, ⟨⟨seedCurveToRelative t x, ?_⟩, hx⟩, (le_smoothCurveBase_iff t V).mp hV,
      inferInstance, ?_⟩
    · change f (seedCurveToRelative t x) ∈ smoothCurveBase t
      rwa [hx]
    · rintro ⟨y, z, rfl⟩
      let w : f ⁻¹ᵁ V := ⟨z.1, ⟨z, rfl⟩⟩
      refine ⟨w, Subtype.ext ?_⟩
      exact congrArg (fun a : (f ⁻¹ᵁ V).toScheme ⟶ parameterScheme => a w)
        (morphismRestrict_ι f V)

end CycleQ2LiteralAbelJacobiFamily

end

#print axioms CycleQ2LiteralAbelJacobiFamily.firstOrderCurve_smooth_iff_flat_and_smooth_seed
#print axioms CycleQ2LiteralAbelJacobiFamily.le_smoothCurveBase_iff
#print axioms CycleQ2LiteralAbelJacobiFamily.seed_mem_smoothCurveBase_iff
#print axioms CycleQ2LiteralAbelJacobiFamily.exists_smooth_proper_surjective_neighborhood_iff
