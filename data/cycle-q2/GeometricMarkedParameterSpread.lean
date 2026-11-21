import Proposal.GeometricMonicGenericSupport
import Proposal.GeometricSmoothAffineIntegralNeighborhood
import Proposal.GeometricMarkedRelativeCylinderDetector

/-!
# A common marked time neighborhood and its proper generic parameter curve

For the monic incidence family a prescribed neighborhood of the marked point
contains an integral affine open carrying the first-order seed and an integral
generic fiber. On the normalized time model this generic fiber shares a dense
open with the proper smooth generic curve.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
noncomputable section
namespace CycleQ2MarkedParameterSpread
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
  CycleQ2IncidenceEtaleParameter CycleQ2LiteralIncidenceRelativeSpread
  CycleQ2LiteralIncidenceNormalizedSlice CycleQ2LiteralIncidenceRelativeCylinder
  CycleQ2LiteralIncidenceGenericModel CycleQ2IncidenceSeedFiberCover
  CycleQ2LiteralAbelJacobiTimeFamily CycleQ2IncidenceFirstOrder

variable (V : parameterScheme.Opens) (hV : seedBasePoint ∈ V)

abbrev marked := (seedLift V hV ≫ fixedToTime toRaw V seedPoint seedPoint_toRaw)
  (default : Spec (CommRingCat.of ℂ))

abbrev tangent := relativeTangent toRaw V seedPoint seedPoint_toRaw hV

private theorem tangent_through (W : (Time toRaw V).Opens) (hx : marked V hV ∈ W) :
    ∃ e : Spec (CommRingCat.of (DualNumber ℂ)) ⟶ W.toScheme,
      e ≫ W.ι = tangent V hV := by
  have hR : Set.range (tangent V hV) ⊆ Set.range W.ι := by
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι, CycleQ2FirstOrderNeighborhood.firstOrderPoint_eq_closedPoint y]
    change (firstOrderClosedPoint ≫ relativeTangent toRaw V seedPoint seedPoint_toRaw hV) _ ∈ W
    rw [tangent_seed]
    exact hx
  exact ⟨IsOpenImmersion.lift W.ι _ hR, IsOpenImmersion.lift_fac W.ι _ hR⟩

private instance : IsPreimmersion genericMorphism :=
  IsPreimmersion.of_isLocalization (S := K) (nonZeroDivisors MonicRing)

/-- An integral smooth open over the monic coefficient base retains integrality on the
actual generic coefficient fiber. -/
private theorem integral_generic {Y : Scheme} [IsIntegral Y] (p : Y ⟶ monicBase)
    [hp : SmoothOfRelativeDimension 1 p] : IsIntegral (pullback genericMorphism p) := by
  have : Smooth p := SmoothOfRelativeDimension.smooth 1 p
  have hB : IrreducibleSpace monicBase :=
    inferInstanceAs (IrreducibleSpace (Spec (CommRingCat.of MonicRing)))
  have hd : DenseRange p := IsOpenMap.denseRange_of_isPreirreducibleSpace _ p.isOpenMap
  have hgen : IsGenericPoint (p (genericPoint Y)) Set.univ := by
    simpa only [Set.image_univ, hd.closure_range] using (genericPoint_spec Y).image p.continuous
  obtain ⟨z, _, hz⟩ := Scheme.Pullback.exists_preimage_pullback (f := genericMorphism) (g := p)
    default (genericPoint Y) ((generic_value default).eq hgen)
  let j := pullback.snd genericMorphism p
  have hz' : IsGenericPoint z Set.univ := isGenericPoint_iff_specializes.mpr fun y =>
    ⟨fun _ => trivial, fun _ => j.isEmbedding.isInducing.specializes_iff.mp (by
      change pullback.snd genericMorphism p z ⤳ _
      rw [hz]
      exact genericPoint_specializes (j y))⟩
  have : IrreducibleSpace (pullback genericMorphism p : Scheme) :=
    (irreducibleSpace_def _).mpr hz'.isIrreducible
  let q := pullback.fst genericMorphism p
  have hq : SmoothOfRelativeDimension 1 q :=
    (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback
      (IsPullback.of_hasPullback genericMorphism p).flip hp
  have := CycleQ2LiteralIncidenceRelativeNormalization.reduced_of_smooth_over_domain 1 q
  exact isIntegral_of_irreducibleSpace_of_isReduced _

open CycleQ2LiteralIncidenceGenericSmoothCurve

theorem integral_normalized_pullback (U : (Time toRaw V).Opens) [IsIntegral U.toScheme] :
    IsIntegral ((testMap V) ⁻¹ᵁ U).toScheme := by
  let b := CycleQ2LiteralIncidenceRelativeNormalization.openInclusion V
  let p := CycleQ2LiteralIncidenceRelativeNormalization.normalizedMap V
  have ht := (IsPullback.of_hasPullback (pullback.snd genericMorphism p) b).flip.paste_vert
    (IsPullback.of_hasPullback genericMorphism p).flip
  have hw := (isPullback_morphismRestrict (testMap V) U).paste_vert ht
  have pb : IsPullback (((testMap V) ⁻¹ᵁ U).ι ≫ inclusion V ≫ projection V)
      ((testMap V) ∣_ U) genericMorphism (U.ι ≫ timeMap toRaw V) := by
    simpa only [b,p, CycleQ2LiteralIncidenceRelativeNormalization.open_over] using hw.flip
  have := timeMap_smooth toRaw V
  have : SmoothOfRelativeDimension 1 (U.ι ≫ timeMap toRaw V) := by
    simpa only [Nat.zero_add] using smoothOfRelativeDimension_comp 0 1 U.ι (timeMap toRaw V)
  have := integral_generic (U.ι ≫ timeMap toRaw V)
  exact IsIntegral.of_isIso pb.isoPullback.inv

theorem exists_compatible (W : (Time toRaw V).Opens) (hx : marked V hV ∈ W) :
    ∃ U : (Time toRaw V).Opens, U ≤ W ∧ IsAffineOpen U ∧ marked V hV ∈ U ∧
      IsIntegral U.toScheme ∧
      (∃ e : Spec (CommRingCat.of (DualNumber ℂ)) ⟶ U.toScheme, e ≫ U.ι = tangent V hV) ∧
      IsIntegral ((testMap V) ⁻¹ᵁ U).toScheme := by
  have := timeMap_smooth toRaw V
  let p : Time toRaw V ⟶ Spec (CommRingCat.of MonicRing) := timeMap toRaw V
  have : Smooth p := (timeMap_smooth toRaw V).smooth
  obtain ⟨_, ⟨A, ha, rfl⟩, hxA, hAW⟩ :=
    (Time toRaw V).isBasis_affineOpens.exists_subset_of_mem_open hx W.isOpen
  obtain ⟨U, hUA, hU, hxU, hI⟩ :=
    CycleQ2SmoothAffineIntegralNeighborhood.exists_integral_chart (R := MonicRing) p A ha _ hxA
  exact ⟨U, hUA.trans hAW, hU, hxU, hI, tangent_through V hV U hxU, integral_normalized_pullback V U⟩

theorem normalized_completion (U : (Time toRaw V).Opens) [IsIntegral U.toScheme] :
    ∃ (C : Scheme) (r : C ⟶ Fiber V), IsIntegral C ∧ IsProper (r ≫ projection V) ∧
      SmoothOfRelativeDimension 1 (r ≫ projection V) ∧
      (∃ q : C ⟶ CycleQ2LaurentProjectiveLine.line K, IsFinite q ∧ IsDominant q ∧
        q ≫ CycleQ2ProjectiveLineStructure.structureMap K = r ≫ projection V) ∧
      ∃ (D : Scheme) (a : D ⟶ ((testMap V) ⁻¹ᵁ U).toScheme) (b : D ⟶ C),
        IsOpenImmersion a ∧ IsDominant a ∧ IsOpenImmersion b ∧ IsDominant b ∧
        a ≫ ((testMap V) ⁻¹ᵁ U).ι ≫ inclusion V = b ≫ r := by
  have := integral_normalized_pullback V U
  have hU : (U : Set (Time toRaw V)).Nonempty := Set.nonempty_coe_sort.mp (inferInstance : Nonempty U.toScheme)
  obtain ⟨L, hle, hL, hI, hC, hn, hp, hs, hsur, hd, D, hD, b, hbo, hbd, hds, hbn, hbi, _⟩ :=
    test_proper_smooth_curve V U hU
  let n := @CycleQ2IntegralCurveNormalization.normalize _ hI
  let m := (L.ι ≫ inclusion V).imageι
  let r := n ≫ m
  let a := D.ι ≫ (TimeFiber V).homOfLE hle
  have : Nonempty D.toScheme := hD.to_subtype
  have : IsOpenImmersion a := inferInstanceAs (IsOpenImmersion (D.ι ≫ (TimeFiber V).homOfLE hle))
  have ha : IsDominant a := ⟨IsOpenMap.denseRange_of_isPreirreducibleSpace _ a.isOpenMap⟩
  let Y := CycleQ2IncidenceIntegralComponent.Model (inclusion V) L
  let p := CycleQ2IncidenceIntegralComponent.toBase (inclusion V) (projection V) L
  let j := CycleQ2IncidenceIntegralComponent.openInclusion (inclusion V) L
  have : NoetherianSpace (Fiber V) := noetherian_of_proper (projection V)
  have : NoetherianSpace (TimeFiber V) := (inclusion V).isOpenEmbedding.isInducing.noetherianSpace
  have : NoetherianSpace L.toScheme := NoetherianSpace.set (L : Set (TimeFiber V))
  have : SmoothOfRelativeDimension 1 (j ≫ p) := by
    rw [CycleQ2IncidenceIntegralComponent.openInclusion_over]
    exact smoothOfRelativeDimension_comp 0 1 L.ι (inclusion V ≫ projection V)
  have hdim (A : Y.affineOpens) : Ring.KrullDimLE 1 Γ(Y,A.1) :=
    CycleQ2CurveChartDimension.chart_dimension j p A.2
  obtain ⟨hc, q, hqf, hqd, hq⟩ := CycleQ2NormalizedCurveProjection.projection K p hdim hd b
  change SmoothOfRelativeDimension 1 (n ≫ p) at hc
  change q ≫ CycleQ2ProjectiveLineStructure.structureMap K = n ≫ p at hq
  refine ⟨_, r, hC, ?_, ?_, ⟨q, hqf, hqd, ?_⟩, _, a, b, inferInstance, ha, hbo, hbd, ?_⟩
  · simpa only [r, m, p, Category.assoc, CycleQ2IncidenceIntegralComponent.toBase] using hp
  · simpa only [r, m, p, Category.assoc, CycleQ2IncidenceIntegralComponent.toBase] using hc
  · simpa only [r, m, p, Category.assoc, CycleQ2IncidenceIntegralComponent.toBase] using hq
  · simpa only [a, r, m, Category.assoc, Scheme.homOfLE_ι_assoc] using hbi.symm

/-- The same marked affine neighborhood can be taken inside the actual quasi-finite
detector open for an algebraically independent seed. -/
theorem exists_detected :
    ∃ t : Fin 3 → ℂ, AlgebraicIndependent ℚ t ∧ CycleQ2MarkedThickCylinderChart.HasTracedSeedCurve t ∧
      ∃ (V : parameterScheme.Opens) (hV : seedBasePoint ∈ V),
        SmoothOfRelativeDimension 1 (curveMap toRaw V t) ∧
        ∃ U : (Time toRaw V).Opens, IsAffineOpen U ∧ marked V hV ∈ U ∧
          IsIntegral U.toScheme ∧ IsIntegral ((testMap V) ⁻¹ᵁ U).toScheme ∧
          (∃ e : Spec (CommRingCat.of (DualNumber ℂ)) ⟶ U.toScheme, e ≫ U.ι = tangent V hV) ∧
          ∀ {T : Scheme} (a : T ⟶ Time toRaw V), Set.range a ⊆ (U : Set (Time toRaw V)) →
            ∀ x : T, ∃ z : (pullback a (curveMap toRaw V t) : Scheme),
              (pullback.fst a (curveMap toRaw V t)) z = x ∧
                (relativeQ toRaw V t).QuasiFiniteAt ((pullback.snd a (curveMap toRaw V t)) z) := by
  obtain ⟨t, ht, htrace, hw⟩ := CycleQ2MarkedCylinderQuasiFinite.exists_marked_time_open_meeting_quasiFinite
  have : IrreducibleSpace monicBase := inferInstanceAs (IrreducibleSpace (Spec (CommRingCat.of MonicRing)))
  obtain ⟨V, hV, _, hcurve, _⟩ := spread_of_independent toRaw seedPoint seedPoint_toRaw t ht
  obtain ⟨W, hx, hW⟩ := hw V hV hcurve.smooth
  obtain ⟨U, hUW, hA, hxU, hI, he, hg⟩ := exists_compatible V hV W hx
  refine ⟨t, ht, htrace, V, hV, hcurve, U, hA, hxU, hI, hg, he, ?_⟩
  intro T a ha x
  exact hW a (ha.trans hUW) x

end CycleQ2MarkedParameterSpread

#print axioms CycleQ2MarkedParameterSpread.exists_detected
#print axioms CycleQ2MarkedParameterSpread.normalized_completion
