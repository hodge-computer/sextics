import Proposal.GeometricMarkedCylinderGerm
import Mathlib.RingTheory.Unramified.LocalStructure
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-!
# A quasi-finite point of the original relative incidence cylinder

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace CycleQ2MarkedSeedCylinderFiber
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

private theorem quasiFiniteAt_iff_isolated {X Y : Scheme.{0}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] (x : X) :
    f.QuasiFiniteAt x ↔ ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ ∀ z ∈ U, f z = f x → z = x := by
  rw [Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber,
    ← (f.fiberHomeo (f x)).isOpen_image, Set.image_singleton]
  simp only [Scheme.Hom.asFiber,Homeomorph.apply_symm_apply]
  let p : f ⁻¹' ({f x} : Set Y) := ⟨x,rfl⟩
  change IsOpen ({p} : Set (f ⁻¹' {f x})) ↔ _
  rw [Topology.IsInducing.subtypeVal.isOpen_iff]
  constructor
  · rintro ⟨U,hU,h⟩
    have hh (w : f ⁻¹' ({f x} : Set Y)) : w.val ∈ U ↔ w = p :=
      Set.ext_iff.mp h w
    refine ⟨U,hU,(hh p).mpr rfl,fun z hz hfx => ?_⟩
    exact congrArg Subtype.val ((hh ⟨z,hfx⟩).mp hz)
  · rintro ⟨U,hU,hx,h⟩
    refine ⟨U,hU,?_⟩
    ext z
    change z.val ∈ U ↔ z = p
    exact ⟨fun hz => Subtype.ext (h z.val hz z.property),fun he => he ▸ hx⟩

/-- Base change along a closed immersion preserves the underlying fibers at the
points in its image, including whether the given point is isolated in the fiber. -/
theorem quasiFiniteAt_of_closed_pullback {X Y X' Y' : Scheme.{0}}
    {f : X ⟶ Y} {g : X' ⟶ Y'} {i : X' ⟶ X} {j : Y' ⟶ Y}
    (H : IsPullback g i j f) [IsClosedImmersion j] [LocallyOfFiniteType f] (x : X') :
    g.QuasiFiniteAt x ↔ f.QuasiFiniteAt (i x) := by
  have : LocallyOfFiniteType g := MorphismProperty.of_isPullback H.flip inferInstance
  have : IsClosedImmersion i := MorphismProperty.of_isPullback H inferInstance
  have he (w : X') : j (g w) = f (i w) := congrArg (fun (a : _ ⟶ Y) => a w) H.w
  have hr : Set.range i = f ⁻¹' Set.range j := by
    rw [← H.isoPullback_hom_snd, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      H.isoPullback.hom.surjective.range_eq, Set.image_univ, AlgebraicGeometry.Scheme.Pullback.range_snd]
  rw [quasiFiniteAt_iff_isolated,quasiFiniteAt_iff_isolated]
  constructor
  · rintro ⟨U,hU,hx,his⟩
    obtain ⟨W,hW,rfl⟩ := i.isClosedEmbedding.isInducing.isOpen_iff.mp hU
    refine ⟨W,hW,hx,fun z hz hfz => ?_⟩
    have hz' : z ∈ Set.range i := hr.symm ▸ (show f z ∈ Set.range j from ⟨g x,(he x).trans hfz.symm⟩)
    obtain ⟨v,rfl⟩ := hz'
    exact congrArg i (his v hz (j.isClosedEmbedding.injective ((he v).trans (hfz.trans (he x).symm))))
  · rintro ⟨W,hW,hx,his⟩
    refine ⟨i ⁻¹' W,hW.preimage i.continuous,hx,fun z hz hfz => ?_⟩
    exact i.isClosedEmbedding.injective (his _ hz ((he z).symm.trans ((congrArg j hfz).trans (he x))))

open CycleQ2LiteralIncidenceRelativeSpread CycleQ2LiteralIncidenceNormalizedSlice
open CycleQ2LiteralIncidenceRelativeCylinder CycleQ2LiteralAbelJacobiTimeProjection
open CycleQ2LiteralIncidenceTimeCurve CycleQ2IncidenceEtaleParameter
open CycleQ2LiteralAbelJacobiTimeFamily

theorem seed_square (V : parameterScheme.Opens) (t : Fin 3 → ℂ) :
    IsPullback (q V t) (fixedToSurface toRaw V t seedPoint seedPoint_toRaw)
      (fixedToAmbient toRaw seedPoint seedPoint_toRaw) (relativeQ toRaw V t) := by
  apply IsPullback.of_right _ (fixed_q toRaw V t seedPoint seedPoint_toRaw).symm
    (fixed_ambient_square toRaw seedPoint seedPoint_toRaw)
  simpa only [q_overComplex,relativeQ_fst] using fixed_surface_square toRaw V t seedPoint seedPoint_toRaw

theorem seed_quasiFiniteAt_iff (V : parameterScheme.Opens) (t : Fin 3 → ℂ)
    [LocallyOfFiniteType (relativeQ toRaw V t)] (x : family V t) :
    (q V t).QuasiFiniteAt x ↔ (relativeQ toRaw V t).QuasiFiniteAt
      (fixedToSurface toRaw V t seedPoint seedPoint_toRaw x) := by
  have : IsClosedImmersion seedPoint := IsClosedImmersion.spec_of_surjective _ (fun z =>
    ⟨MvPolynomial.C z, MvPolynomial.eval_C z⟩)
  have : IsClosedImmersion (fixedToAmbient toRaw seedPoint seedPoint_toRaw) :=
    MorphismProperty.of_isPullback (fixed_ambient_square toRaw seedPoint seedPoint_toRaw) inferInstance
  exact quasiFiniteAt_of_closed_pullback (seed_square V t) x

end CycleQ2MarkedSeedCylinderFiber

namespace CycleQ2MarkedCylinderQuasiFinite
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits IsLocalRing

/-- Surjectivity onto a quotient with quadratic kernel kills all relative differentials
at an essentially finite type surface stalk. -/
theorem unramified_of_surjective_mod_quadratic {R B C : Type} [CommRing R] [CommRing B]
    [CommRing C] [IsLocalRing B] (f : R →+* B) (h : B →+* C)
    (hf : f.EssFiniteType) (hs : Function.Surjective (h.comp f)) (hk : RingHom.ker h ≤ maximalIdeal B ^ 2) :
    f.FormallyUnramified := by
  algebraize [f]
  have : Algebra.EssFiniteType R B := by rwa [← RingHom.essFiniteType_algebraMap, RingHom.algebraMap_toAlgebra]
  change Algebra.FormallyUnramified R B
  let M := KaehlerDifferential R B
  let N := (⊤ : Submodule B M)
  let m := maximalIdeal B
  let D := KaehlerDifferential.D R B
  have hdiff {y : B} (hy : y ∈ m ^ 2) : D y ∈ m • N := by
    rw [pow_two] at hy
    refine Submodule.mul_induction_on hy ?_ ?_
    · intro x hx y hy
      rw [Derivation.leibniz]
      exact add_mem (Submodule.smul_mem_smul hx (Submodule.mem_top : D y ∈ N))
        (Submodule.smul_mem_smul hy (Submodule.mem_top : D x ∈ N))
    · intro x y hx hy
      rw [map_add]
      exact add_mem hx hy
  have hN : N ≤ m • N := by
    change (⊤ : Submodule B M) ≤ _
    rw [← KaehlerDifferential.span_range_derivation, Submodule.span_le]
    rintro _ ⟨b,rfl⟩
    obtain ⟨a,ha⟩ := hs (h b)
    have hmem : b - f a ∈ RingHom.ker h := by
      change h (b - f a) = 0
      rw [map_sub, show h (f a) = h b from ha,sub_self]
    have hb := hdiff (hk hmem)
    simpa [D,show f a = algebraMap R B a from rfl] using hb
  have hz : N = ⊥ := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot m N Module.Finite.fg_top hN
    (by rw [IsLocalRing.jacobson_eq_maximalIdeal _ bot_ne_top])
  exact ⟨(Submodule.subsingleton_iff B).mp (subsingleton_of_top_eq_bot hz)⟩

private theorem quasi_of_unramified {R B : Type} [CommRing R] [CommRing B]
    (f : R →+* B) (hf : f.EssFiniteType) (hu : f.FormallyUnramified) : f.QuasiFinite := by
  algebraize [f]
  have : Algebra.EssFiniteType R B := by rwa [← RingHom.essFiniteType_algebraMap, RingHom.algebraMap_toAlgebra]
  have : Algebra.FormallyUnramified R B := hu
  exact (inferInstance : Algebra.QuasiFinite R B)

theorem quasiFiniteAt_of_chart {A X Y : Scheme.{0}} (i : A ⟶ X) (q : X ⟶ Y)
    [LocallyOfFiniteType q] (z : A) (hs : Function.Surjective ((i ≫ q).stalkMap z))
    (hk : RingHom.ker (i.stalkMap z).hom ≤ maximalIdeal (X.presheaf.stalk (i z)) ^ 2) :
    q.QuasiFiniteAt (i z) := by
  let f := (q.stalkMap (i z)).hom
  let h := (i.stalkMap z).hom
  have hf : f.EssFiniteType := LocallyOfFiniteType.stalkMap q (i z)
  have hs' : Function.Surjective (h.comp f) := by
    rw [Scheme.Hom.stalkMap_comp] at hs
    exact hs
  have hu := unramified_of_surjective_mod_quadratic f h hf hs' hk
  exact quasi_of_unramified f hf hu

open CycleQ2LiteralIncidenceRelativeSpread CycleQ2LiteralIncidenceNormalizedSlice
  CycleQ2LiteralIncidenceRelativeCylinder CycleQ2LiteralAbelJacobiTimeProjection
  CycleQ2LiteralIncidenceTimeCurve CycleQ2IncidenceEtaleParameter
  CycleQ2LiteralAbelJacobiTimeFamily CycleQ2IncidenceSeedFiberCover
  CycleQ2RelativeCurveNeighborhood CycleQ2RelativeConstantCurve CycleQ2LiteralAbelJacobiTimeCharts
  CycleQ2MarkedThickCylinderChart CycleQ2MarkedSeedCylinderFiber CycleQ2MarkedSurfaceTangentSquare

private theorem relative_finiteType (V : parameterScheme.Opens) (t : Fin 3 → ℂ) :
    LocallyOfFiniteType (relativeQ toRaw V t) := by
  have := timeMap_smooth toRaw V
  have : Smooth (timeMap toRaw V) := SmoothOfRelativeDimension.smooth 1 _
  have := relativeCurveToBase_proper
    incidencePoint t
  have : LocallyOfFiniteType (curveMap toRaw V t) := by dsimp [curveMap]; infer_instance
  have : LocallyOfFiniteType (relativeQ toRaw V t ≫ pullback.fst toRaw _) := by
    rw [relativeQ_fst]; infer_instance
  exact locallyOfFiniteType_of_comp _ (pullback.fst toRaw _)

/-- The same independent original section has a seed detector in every open
parameter neighborhood of the marked point. -/
theorem exists_quasiFiniteAt_seed_and_relative :
    ∃ t : Fin 3 → ℂ, AlgebraicIndependent ℚ t ∧ ∀ (V : parameterScheme.Opens),
      seedBasePoint ∈ V → ∃ x : family V t, (q V t).QuasiFiniteAt x ∧ (relativeQ toRaw V t).QuasiFiniteAt
        (fixedToSurface toRaw V t seedPoint seedPoint_toRaw x) := by
  obtain ⟨t,j,_,_,hi,⟨z⟩,_⟩ := exists_nonempty_embedded_thick_chart
  refine ⟨t,hi,?_⟩
  intro V hV
  have himm := actual_thick_immersion t j.succ V hV
  let i := chartOpen t j.succ ≫ thickChart V t hV j.succ
  have : IsImmersion (i ≫ q V t) := by simpa only [i,Category.assoc] using himm
  have := relative_finiteType V t
  have : LocallyOfFiniteType (q V t) := MorphismProperty.of_isPullback (seed_square V t).flip inferInstance
  have hq : (q V t).QuasiFiniteAt (i z) := quasiFiniteAt_of_chart i _ z ((i ≫ q V t).stalkMap_surjective z)
    (marked_chart_kernel_le_square V hV t j.succ z)
  exact ⟨i z,hq,(seed_quasiFiniteAt_iff V t _).mp hq⟩

/-- Every time test in the selected nonempty open has a point in the original
relative quasi-finite locus above every one of its own points. -/
theorem exists_time_open_meeting_quasiFinite :
    ∃ (t : Fin 3 → ℂ), AlgebraicIndependent ℚ t ∧ ∀ (V : parameterScheme.Opens),
      seedBasePoint ∈ V → Smooth (curveMap toRaw V t) →
      ∃ W : (Time toRaw V).Opens, (W : Set (Time toRaw V)).Nonempty ∧
        ∀ {D : Scheme} (a : D ⟶ Time toRaw V), Set.range a ⊆ (W : Set (Time toRaw V)) →
        ∀ d : D, ∃ z : (pullback a (curveMap toRaw V t) : Scheme),
          (pullback.fst a (curveMap toRaw V t)) z = d ∧
          (relativeQ toRaw V t).QuasiFiniteAt ((pullback.snd a (curveMap toRaw V t)) z) := by
  obtain ⟨t,hi,ht⟩ := exists_quasiFiniteAt_seed_and_relative
  refine ⟨t,hi,?_⟩
  intro V hV hcurve
  obtain ⟨x,_,hx⟩ := ht V hV
  let s := curveMap toRaw V t
  let q := relativeQ toRaw V t
  have : LocallyOfFiniteType q := relative_finiteType V t
  let L := q.quasiFiniteLocus
  let W : (Time toRaw V).Opens := ⟨s '' (L : Set _), s.isOpenMap _ L.isOpen⟩
  refine ⟨W,⟨_,_,hx,rfl⟩,?_⟩
  intro D a ha d
  obtain ⟨y,hy,hy'⟩ := ha ⟨d,rfl⟩
  obtain ⟨z,hz,hz'⟩ := Scheme.Pullback.exists_preimage_pullback (f := a) (g := s) d y hy'.symm
  exact ⟨z,hz,hz' ▸ hy⟩

end CycleQ2MarkedCylinderQuasiFinite

#print axioms CycleQ2MarkedCylinderQuasiFinite.exists_time_open_meeting_quasiFinite
