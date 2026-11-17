import Proposal.GeometricLiteralAbelJacobiSeedLift

/-!
# Relative dimension of the moving section curves

The two surface equations and the chosen section row give smooth affine
patches of relative dimension one where their Jacobian minor is invertible.
Their images in the original projective curve contain its seed fiber.
Properness then gives a neighborhood in the incidence base over which the
whole curve has relative dimension one.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralAbelJacobiSeedLiftDimension

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace MvPolynomial
open CycleQ2IncidenceDehomogenizedChart CycleQ2LiteralAbelJacobiSeedLift

private def dimensionLocus {X Y : Scheme} (f : X ⟶ Y) : X.Opens :=
  ⨆ U : { U : X.Opens // SmoothOfRelativeDimension 1 (U.ι ≫ f) }, U.1

private theorem mem_dimensionLocus {X Y : Scheme} (f : X ⟶ Y) (x : X) :
    x ∈ dimensionLocus f ↔ ∃ U : X.Opens, x ∈ U ∧ SmoothOfRelativeDimension 1 (U.ι ≫ f) := by
  rw [dimensionLocus, Opens.mem_iSup]
  constructor
  · rintro ⟨U, hx⟩
    exact ⟨U.1, hx, U.2⟩
  · rintro ⟨U, hx, hU⟩
    exact ⟨⟨U, hU⟩, hx⟩

private theorem mem_of_patch {X Y T : Scheme} (f : X ⟶ Y) (j : T ⟶ X) [IsOpenImmersion j]
    (hj : SmoothOfRelativeDimension 1 (j ≫ f)) (x : T) : j x ∈ dimensionLocus f := by
  apply (mem_dimensionLocus f _).mpr
  refine ⟨j.opensRange, ⟨x, rfl⟩, ?_⟩
  have hr : Set.range j = Set.range j.opensRange.ι :=
    congrArg Opens.carrier j.opensRange.opensRange_ι.symm
  rw [← IsOpenImmersion.isoOfRangeEq_inv_fac j j.opensRange.ι hr, Category.assoc]
  exact smoothOfRelativeDimension_comp 0 1 _ _

private theorem mem_open_iff {X Y T : Scheme} (j : T ⟶ X) [IsOpenImmersion j]
    (f : X ⟶ Y) (x : T) : j x ∈ dimensionLocus f ↔ x ∈ dimensionLocus (j ≫ f) := by
  constructor
  · intro hx
    obtain ⟨U, hU, hs⟩ := (mem_dimensionLocus f _).mp hx
    apply (mem_dimensionLocus _ _).mpr
    refine ⟨j ⁻¹ᵁ U, hU, ?_⟩
    rw [← Category.assoc, ← morphismRestrict_ι, Category.assoc]
    exact smoothOfRelativeDimension_comp 0 1 _ _
  · intro hx
    obtain ⟨U, hU, hs⟩ := (mem_dimensionLocus _ _).mp hx
    rw [← Category.assoc] at hs
    exact mem_of_patch f (U.ι ≫ j) hs (⟨x, hU⟩ : U)

private theorem dimension_of_cover {X Y : Scheme} (f : X ⟶ Y)
    (h : ∀ x : X, x ∈ dimensionLocus f) : SmoothOfRelativeDimension 1 f := by
  classical
  choose U hU hs using fun x => (mem_dimensionLocus f x).mp (h x)
  apply IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension 1) U _ hs
  apply top_le_iff.mp
  exact fun x _ => Opens.mem_iSup.mpr ⟨x, hU x⟩

private abbrev specToBase (S A : Type) [CommRing S] [CommRing A] [Algebra S A] :=
  Spec.map (CommRingCat.ofHom (algebraMap S A))

private def specAway {A : Type} [CommRing A] (u : A) :=
  Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away u)))

private instance {A : Type} [CommRing A] (u : A) : IsOpenImmersion (specAway u) :=
  IsOpenImmersion.of_isLocalization u

private theorem exists_lift_away {A : Type} [CommRing A] (u : A)
    (z : Spec (CommRingCat.of A)) (hu : u ∉ z.asIdeal) :
    ∃ x, specAway u x = z := by
  change z ∈ Set.range (PrimeSpectrum.comap (algebraMap A (Localization.Away u)))
  rw [PrimeSpectrum.localization_away_comap_range (Localization.Away u) u]
  exact hu

private theorem at_minor {S : Type} [CommRing S] (v : Fin 3 → ChartPolynomial S)
    (q : Fin 3 ↪ Option (Fin 3)) (z : PrimeSpectrum (EquationRing v))
    (hz : Ideal.Quotient.mk (Ideal.span (Set.range v)) (minorPolynomial v q) ∉ z.asIdeal) :
    z ∈ dimensionLocus (specToBase S (EquationRing v)) := by
  let u := (threeRowPresentation v q).jacobian
  obtain ⟨x, rfl⟩ := exists_lift_away u z (by rwa [show u = _ from threeRowPresentation_jacobian v q])
  apply mem_of_patch _ (specAway u) _ x
  have hcomp : specAway u ≫ specToBase S (EquationRing v) = specToBase S (JacobianRing v q) := by
    rw [specAway, specToBase, ← Spec.map_comp]
    apply congrArg Spec.map
    exact CommRingCat.hom_ext (IsScalarTower.algebraMap_eq S (EquationRing v) (JacobianRing v q)).symm
  rw [hcomp]
  apply (HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension 1)).mpr
  apply RingHom.locally_of (RingHom.isStandardSmoothOfRelativeDimension_respectsIso (n := 1))
  exact (RingHom.isStandardSmoothOfRelativeDimension_algebraMap 1).mpr (jacobianRing_standardSmooth v q)

private theorem at_pivot {S Q A : Type} [CommRing S] [CommRing Q] [CommRing A]
    [Algebra S Q] [Algebra S A] (π : Q →ₐ[S] A) (u : Q)
    (e : Localization.Away u ≃ₐ[S] Localization.Away (π u))
    (he : ∀ a, e (algebraMap Q (Localization.Away u) a) =
      algebraMap A (Localization.Away (π u)) (π a)) (z : Spec (CommRingCat.of A))
    (hu : π u ∉ z.asIdeal) (hz : (Spec.map (CommRingCat.ofHom π.toRingHom)) z ∈
      dimensionLocus (specToBase S Q)) : z ∈ dimensionLocus (specToBase S A) := by
  obtain ⟨x, rfl⟩ := exists_lift_away (π u) z hu
  let k := (Scheme.Spec.mapIso e.toRingEquiv.toCommRingCatIso.op).hom
  let j := k ≫ specAway u
  have : IsOpenImmersion j := by dsimp only [j, k]; infer_instance
  have hj : j = specAway (π u) ≫ Spec.map (CommRingCat.ofHom π.toRingHom) := by
    change Spec.map (CommRingCat.ofHom e.toRingHom) ≫ _ = _
    dsimp only [specAway]
    rw [← Spec.map_comp, ← Spec.map_comp]
    apply congrArg Spec.map
    exact CommRingCat.hom_ext (RingHom.ext he)
  have hjx : j x ∈ dimensionLocus (specToBase S Q) := by rw [hj]; exact hz
  have hs := (mem_open_iff j (specToBase S Q) x).mp hjx
  apply (mem_open_iff (specAway (π u)) (specToBase S A) x).mpr
  have hbase : Spec.map (CommRingCat.ofHom π.toRingHom) ≫ specToBase S Q = specToBase S A := by
    rw [specToBase, ← Spec.map_comp]
    apply congrArg Spec.map
    exact CommRingCat.hom_ext π.comp_algebraMap
  rwa [hj, Category.assoc, hbase] at hs

open CycleQ2IncidencePolynomialJacobianBinding CycleQ2RelativeCurveChart
  CycleQ2RelativeCurveChartFiber CycleQ2FirstOrderCurveChartFlat
  CycleQ2RelativeCurveSeedProj CycleQ2SpecializedProjectiveCurve
  CycleQ2LiteralAbelJacobiFamily CycleQ2LiteralAbelJacobiSeedLiftPoints
  CycleQ2LiteralAbelJacobiSeedLiftChart CycleQ2IncidenceEtaleParameter
  CycleQ2SpecializedCurveCoordinateChart CycleQ2RelativeConstantCurve
  CycleQ2IncidenceSeedFiberCover CycleQ2IncidenceProperNeighborhood
  CycleQ2RelativeCurveSeedFiberIso CycleQ2IncidenceChartFiberScheme

attribute [local instance] CycleQ2RelativeCurveChartFiber.incidenceCurveChartCommRing
  CycleQ2RelativeCurveChartFiber.seedCurveChartCommRing

private abbrev seed := seedPoint (57 : ℂ) Complex.I

/-- The Jacobian cover certifies the actual projective seed curve's dimension. -/
theorem smooth_seed_of_seedMinorCover (t : Fin 3 → ℂ) (h : SeedMinorCover t) :
    SmoothOfRelativeDimension 1 (specializedCurveToBase seed t) := by
  apply dimension_of_cover
  intro x
  obtain ⟨i, z, hx, _⟩ := exists_seedChart_prime t x
  obtain ⟨p, q, hp, hq⟩ := h i z
  let π := toCurve seed t i p
  have hp' : π (rowPivot seed t i p) ∉ z.asIdeal := by
    rw [show π (rowPivot seed t i p) = _ from toCurve_rowPivot seed t i p]
    exact hp
  have hs := at_minor (chartEquations seed t i p) q (PrimeSpectrum.comap π.toRingHom z) hq
  have hloc := at_pivot π (rowPivot seed t i p) (seedPivotEquiv t i p)
    (seedPivotEquiv_algebraMap t i p) z hp' hs
  rw [← hx]
  let j := seedChartToCurve t i
  have : IsOpenImmersion j := by dsimp only [j, seedChartToCurve]; infer_instance
  apply (mem_open_iff j _ z).mpr
  have hj : j ≫ specializedCurveToBase seed t = specToBase ℂ (AffineCurveChart seed t i) := by
    dsimp only [j, seedChartToCurve]
    rw [Category.assoc, specializedCoordinateAffineChart_overBase]
  rwa [hj]

private theorem seed_point_mem_dimensionLocus (t : Fin 3 → ℂ) (h : SeedMinorCover t)
    (x : specializedCurve seed t) :
    seedCurveToRelative t x ∈ dimensionLocus (relativeCurveToBase incidencePoint t) := by
  obtain ⟨i, z, _, hx⟩ := exists_seedChart_prime t x
  obtain ⟨p, q, hp, hq⟩ := h i z
  let v := chartEquations incidencePoint t i p
  let π := toCurve incidencePoint t i p
  let y := movingPrime t i z
  let j := movingChartToCurve t i
  let f := relativeCurveToBase incidencePoint t
  have hj : j ≫ f = specToBase ParameterAlgebra (AffineCurveChart incidencePoint t i) :=
    CycleQ2FirstOrderCurveCharts.originalCurveChart_overBase t i
  have hp' : π (rowPivot incidencePoint t i p) ∉ y.asIdeal := by
    rw [show π (rowPivot incidencePoint t i p) = _ from toCurve_rowPivot incidencePoint t i p]
    exact (pivot_notMem_movingPrime_iff t i z p).mpr hp
  have hq' : curvePolynomialMap t i incidencePoint (minorPolynomial v q) ∉ y.asIdeal := by
    apply (jacobianMinor_notMem_movingPrime_iff t i z v q).mpr
    change curvePolynomialMap t i seed (jacobianMinor
      (fun k => MvPolynomial.map seedMap (chartEquations incidencePoint t i p k)) q) ∉ z.asIdeal
    rw [chartEquations, sectionRows_map]
    exact hq
  have hs := at_minor v q (PrimeSpectrum.comap π.toRingHom y) hq'
  have hloc := at_pivot π (rowPivot incidencePoint t i p) (pivotEquiv t i p)
    (pivotEquiv_algebraMap t i p) y hp' hs
  rw [← hx]
  apply (mem_open_iff j f y).mpr
  rwa [hj]

private theorem dimension_on_restriction {X Y : Scheme} (f : X ⟶ Y) (V : Y.Opens)
    (h : f ⁻¹ᵁ V ≤ dimensionLocus f) : SmoothOfRelativeDimension 1 (f ∣_ V) := by
  letI := smoothOfRelativeDimension_isStableUnderBaseChange 1
  apply MorphismProperty.of_postcomp (W' := @IsOpenImmersion) (@SmoothOfRelativeDimension 1)
    (f ∣_ V) V.ι (inferInstance : IsOpenImmersion V.ι)
  rw [morphismRestrict_ι]
  apply dimension_of_cover
  intro x
  exact (mem_open_iff (f ⁻¹ᵁ V).ι f x).mp (h x.2)

/-- The same vector gives proper nonempty smooth curves of relative dimension
one over a neighborhood of the original incidence seed. -/
theorem dimension_one_neighborhood_of_seedMinorCover (t : Fin 3 → ℂ) (h : SeedMinorCover t) :
    ∃ V : parameterScheme.Opens, seedBasePoint ∈ V ∧
      SmoothOfRelativeDimension 1 ((relativeCurveToBase incidencePoint t) ∣_ V) ∧
      IsProper ((relativeCurveToBase incidencePoint t) ∣_ V) ∧
      Function.Surjective ((relativeCurveToBase incidencePoint t) ∣_ V) := by
  let f := relativeCurveToBase incidencePoint t
  have : IsProper f := CycleQ2RelativeCurveNeighborhood.relativeCurveToBase_proper incidencePoint t
  let W := properBaseNeighborhood f (dimensionLocus f)
  have hW : seedBasePoint ∈ W := by
    apply (mem_properBaseNeighborhood_iff f (dimensionLocus f) seedBasePoint).mpr
    intro x hx
    obtain ⟨z, _, hz⟩ := Scheme.Pullback.exists_preimage_pullback
      (f := seedParameterMorphism) (g := relativeCurveToBase incidencePoint t)
      (default : Spec (CommRingCat.of ℂ)) x hx.symm
    have hp := seed_point_mem_dimensionLocus t h ((seedCurveFiberIso t).inv z)
    have he : seedCurveToRelative t ((seedCurveFiberIso t).inv z) = x := by
      rw [← Scheme.Hom.comp_apply, ← seedCurveFiberIso_hom_snd, Iso.inv_hom_id_assoc]
      exact hz
    rwa [he] at hp
  obtain ⟨V₀, hV₀, _, _, hs⟩ := (smooth_neighborhood_of_seed_minors t h).2
  let V := W ⊓ V₀
  refine ⟨V, ⟨hW, hV₀⟩, dimension_on_restriction f V
    ((le_properBaseNeighborhood_iff f (dimensionLocus f) V).mp inf_le_left), inferInstance, ?_⟩
  intro y
  obtain ⟨a, ha⟩ := hs (⟨y.1, y.2.2⟩ : V₀)
  have hpoint : f a.1 = y.1 := by
    have h₁ := congrArg (fun g : (f ⁻¹ᵁ V₀).toScheme ⟶ parameterScheme => g a)
      (morphismRestrict_ι f V₀)
    exact h₁.symm.trans (congrArg Subtype.val ha)
  let b : (f ⁻¹ᵁ V).toScheme := ⟨a.1, (show f a.1 ∈ V by rw [hpoint]; exact y.2)⟩
  refine ⟨b, Subtype.ext ?_⟩
  have h₂ := congrArg (fun g : (f ⁻¹ᵁ V).toScheme ⟶ parameterScheme => g b)
    (morphismRestrict_ι f V)
  exact h₂.trans hpoint

end CycleQ2LiteralAbelJacobiSeedLiftDimension

end

#print axioms CycleQ2LiteralAbelJacobiSeedLiftDimension.smooth_seed_of_seedMinorCover
#print axioms CycleQ2LiteralAbelJacobiSeedLiftDimension.dimension_one_neighborhood_of_seedMinorCover
