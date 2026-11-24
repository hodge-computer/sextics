import Proposal.GeometricLiteralAbelJacobiFamily
import Proposal.GeometricIncidenceChartDimension
import Proposal.GeometricLiteralAbelJacobiSeedLiftChart
import Proposal.GeometricLiteralAbelJacobiSeedLiftPoints
import Proposal.GeometricLiteralAbelJacobiSeedLiftConverse

/-!
# Jacobian smoothness of a one-row section on the incidence surface

On a matrix-pivot open the two surface equations and the selected section
row cut out the curve. A nonvanishing minor of these three equations gives
a relative dimension-one Jacobian patch over the original coefficient base.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralAbelJacobiSeedLift

open MvPolynomial CategoryTheory AlgebraicGeometry
open CycleQ2IncidenceDehomogenizedChart

section Jacobian

variable {S : Type} [CommRing S]
variable (v : Fin 3 → ChartPolynomial S) (q : Fin 3 ↪ Option (Fin 3))

abbrev EquationRing := ChartPolynomial S ⧸ Ideal.span (Set.range v)

def minorPolynomial : ChartPolynomial S :=
  (Matrix.of fun i j : Fin 3 => pderiv (q i) (v j)).det

def threeRowPresentation :
    Algebra.PreSubmersivePresentation S (EquationRing v) (Option (Fin 3)) (Fin 3) :=
  Algebra.PreSubmersivePresentation.naive (v := v) q q.injective

theorem threeRowPresentation_jacobian :
    (threeRowPresentation v q).jacobian =
      Ideal.Quotient.mk (Ideal.span (Set.range v)) (minorPolynomial v q) := by
  rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]
  apply congrArg (Ideal.Quotient.mk (Ideal.span (Set.range v)))
  apply congrArg Matrix.det
  ext a b : 1
  rw [Algebra.PreSubmersivePresentation.jacobiMatrix_apply]
  rfl

abbrev JacobianRing := Localization.Away (threeRowPresentation v q).jacobian

theorem jacobianRing_standardSmooth : Algebra.IsStandardSmoothOfRelativeDimension 1 S
    (JacobianRing v q) := by
  let P := threeRowPresentation v q
  let Q : Algebra.SubmersivePresentation S (JacobianRing v q)
      (Unit ⊕ Option (Fin 3)) (Unit ⊕ Fin 3) := {
    toPreSubmersivePresentation :=
      (Algebra.PreSubmersivePresentation.localizationAway (JacobianRing v q) P.jacobian).comp P
    jacobian_isUnit := by
      have hu : IsUnit (algebraMap (EquationRing v) (JacobianRing v q) P.jacobian) :=
        IsLocalization.Away.algebraMap_isUnit P.jacobian
      simpa only [Algebra.PreSubmersivePresentation.comp_jacobian_eq_jacobian_smul_jacobian,
        Algebra.PreSubmersivePresentation.localizationAway_jacobian, Algebra.smul_def] using hu.mul hu }
  apply Q.isStandardSmoothOfRelativeDimension
  change Nat.card (Unit ⊕ Option (Fin 3)) - Nat.card (Unit ⊕ Fin 3) = 1
  norm_num [Nat.card_eq_fintype_card]

end Jacobian

private abbrev specToBase (S A : Type) [CommRing S] [CommRing A] [Algebra S A] :=
  Spec.map (CommRingCat.ofHom (algebraMap S A))

private theorem mem_smoothLocus_openImmersion_iff {X Y U : Scheme}
    (j : U ⟶ X) [IsOpenImmersion j] (f : X ⟶ Y) [LocallyOfFinitePresentation f] (x : U) :
    j x ∈ f.smoothLocus ↔ x ∈ (j ≫ f).smoothLocus := by
  change x ∈ j ⁻¹ᵁ f.smoothLocus ↔ _
  rw [Scheme.Hom.preimage_smoothLocus_eq]

private def specAway {A : Type} [CommRing A] (u : A) :=
  Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away u)))

private instance specAwayOpen {A : Type} [CommRing A] (u : A) :
    IsOpenImmersion (specAway u) :=
  IsOpenImmersion.of_isLocalization u

private theorem exists_lift_away {A : Type} [CommRing A] (u : A)
    (z : Spec (CommRingCat.of A)) (hu : u ∉ z.asIdeal) :
    ∃ x, specAway u x = z := by
  change z ∈ Set.range (PrimeSpectrum.comap (algebraMap A (Localization.Away u)))
  rw [PrimeSpectrum.localization_away_comap_range (Localization.Away u) u]
  exact hu

theorem smoothAt_threeRowMinor {S : Type} [CommRing S] (v : Fin 3 → ChartPolynomial S)
    (q : Fin 3 ↪ Option (Fin 3))
    [LocallyOfFinitePresentation (specToBase S (EquationRing v))]
    (z : Spec (CommRingCat.of (EquationRing v)))
    (hz : Ideal.Quotient.mk (Ideal.span (Set.range v)) (minorPolynomial v q) ∉ z.asIdeal) :
    z ∈ (specToBase S (EquationRing v)).smoothLocus := by
  let u := (threeRowPresentation v q).jacobian
  obtain ⟨x, rfl⟩ := exists_lift_away u z (by rwa [show u = _ from threeRowPresentation_jacobian v q])
  apply (mem_smoothLocus_openImmersion_iff (specAway u) _ x).mpr
  have hcomp : specAway u ≫ specToBase S (EquationRing v) = specToBase S (JacobianRing v q) := by
    rw [specAway, specToBase, ← Spec.map_comp]
    apply congrArg Spec.map
    exact CommRingCat.hom_ext (IsScalarTower.algebraMap_eq S (EquationRing v) (JacobianRing v q)).symm
  have hdim : SmoothOfRelativeDimension 1 (specToBase S (JacobianRing v q)) := by
    apply (HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension 1)).mpr
    apply RingHom.locally_of (RingHom.isStandardSmoothOfRelativeDimension_respectsIso (n := 1))
    exact (RingHom.isStandardSmoothOfRelativeDimension_algebraMap 1).mpr (jacobianRing_standardSmooth v q)
  have hs : Smooth (specToBase S (JacobianRing v q)) :=
    SmoothOfRelativeDimension.smooth 1 _
  have : Smooth (specAway u ≫ specToBase S (EquationRing v)) := hcomp ▸ hs
  rw [Scheme.Hom.smoothLocus_eq_top]
  trivial

private theorem specMap_toBase {S Q A : Type} [CommRing S] [CommRing Q] [CommRing A]
    [Algebra S Q] [Algebra S A] (π : Q →ₐ[S] A) :
    Spec.map (CommRingCat.ofHom π.toRingHom) ≫ specToBase S Q = specToBase S A := by
  rw [specToBase, ← Spec.map_comp]
  apply congrArg Spec.map
  exact CommRingCat.hom_ext π.comp_algebraMap

private theorem smoothAt_of_pivotEquiv {S Q A : Type} [CommRing S] [CommRing Q] [CommRing A]
    [Algebra S Q] [Algebra S A]
    [LocallyOfFinitePresentation (specToBase S Q)] [LocallyOfFinitePresentation (specToBase S A)]
    (π : Q →ₐ[S] A) (u : Q)
    (e : Localization.Away u ≃ₐ[S] Localization.Away (π u))
    (he : ∀ a, e (algebraMap Q (Localization.Away u) a) =
      algebraMap A (Localization.Away (π u)) (π a)) (z : Spec (CommRingCat.of A))
    (hu : π u ∉ z.asIdeal) (hz : (Spec.map (CommRingCat.ofHom π.toRingHom)) z ∈
      (specToBase S Q).smoothLocus) : z ∈ (specToBase S A).smoothLocus := by
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
  have hjx : j x ∈ (specToBase S Q).smoothLocus := by rw [hj]; exact hz
  have hs := (mem_smoothLocus_openImmersion_iff j (specToBase S Q) x).mp hjx
  apply (mem_smoothLocus_openImmersion_iff (specAway (π u)) (specToBase S A) x).mpr
  change ((specAway (π u) ≫ specToBase S A).stalkMap x).hom.FormallySmooth
  change ((j ≫ specToBase S Q).stalkMap x).hom.FormallySmooth at hs
  have hcomp : j ≫ specToBase S Q = specAway (π u) ≫ specToBase S A := by
    rw [hj, Category.assoc, specMap_toBase]
  rw [hcomp] at hs
  exact hs

open CategoryTheory.Limits
open CycleQ2IncidenceEtaleParameter CycleQ2IncidenceSeedFiberCover CycleQ2IncidenceFirstOrder
  CycleQ2FirstOrderCurve CycleQ2FirstOrderNeighborhood CycleQ2RelativeConstantCurve

/-- The original infinitesimal parameter factors through every open containing
its seed. As a result the original first-order curve inherits smoothness from
the relative family on any such open, for the same section vector. -/
theorem firstOrderCurve_smooth_of_neighborhood (t : Fin 3 → ℂ) (V : parameterScheme.Opens)
    (hseed : seedBasePoint ∈ V) (hs : Smooth ((relativeCurveToBase incidencePoint t) ∣_ V)) :
    Smooth (firstOrderCurveToBase t) := by
  let f := relativeCurveToBase incidencePoint t
  let j := IsOpenImmersion.lift V.ι firstOrderParameterPoint (by
    rintro _ ⟨z, rfl⟩
    exact ⟨⟨firstOrderParameterPoint z, (firstOrderParameterPoint_apply z).symm ▸ hseed⟩, rfl⟩)
  have hj : j ≫ V.ι = firstOrderParameterPoint := IsOpenImmersion.lift_fac _ _ _
  have hsq := (IsPullback.of_hasPullback (f ∣_ V) j).paste_horiz (isPullback_morphismRestrict f V).flip
  rw [hj] at hsq
  rw [← (firstOrderCurve_isPullback t).isoIsPullback_hom_snd _ _ hsq]
  infer_instance

open CycleQ2IncidencePolynomialJacobianBinding CycleQ2RelativeCurveChart
  CycleQ2RelativeCurveChartFiber CycleQ2FirstOrderCurveChartFlat
  CycleQ2RelativeCurveSeedProj CycleQ2SpecializedProjectiveCurve
  CycleQ2LiteralAbelJacobiFamily CycleQ2LiteralAbelJacobiSeedLiftPoints
  CycleQ2LiteralAbelJacobiSeedLiftChart

attribute [local instance] CycleQ2RelativeCurveChartFiber.incidenceCurveChartCommRing
  CycleQ2RelativeCurveChartFiber.seedCurveChartCommRing

private abbrev seed := seedPoint (57 : ℂ) Complex.I

/-- Pointwise Jacobian criterion on the actual seed chart primes for a fixed
vector. The selected row has an invertible matrix entry at the same prime. -/
def SeedMinorCover (t : Fin 3 → ℂ) : Prop :=
  ∀ (i : Fin 4) (z : PrimeSpectrum (AffineCurveChart seed t i)),
    ∃ (p : CycleQ2SegreCech.Chart) (q : Fin 3 ↪ Option (Fin 3)),
      Ideal.Quotient.mk (affineSectionIdeal seed t i) (seedPivot i p) ∉ z.asIdeal ∧
      curvePolynomialMap t i seed (minorPolynomial (chartEquations seed t i p) q) ∉ z.asIdeal

private instance equationRingLfp {S : Type} [CommRing S] (v : Fin 3 → ChartPolynomial S) :
    LocallyOfFinitePresentation (specToBase S (EquationRing v)) := by
  apply (LocallyOfFinitePresentation.SpecMap_iff _).mpr
  apply RingHom.finitePresentation_algebraMap.mpr
  exact Algebra.FinitePresentation.quotient (Submodule.fg_span (Set.finite_range v))

private instance incidenceCurveLfp (t : Fin 3 → ℂ) :
    LocallyOfFinitePresentation (relativeCurveToBase incidencePoint t) := by
  have := CycleQ2RelativeRegularSection.parameter_noetherian
  have := CycleQ2RelativeCurveNeighborhood.relativeCurveToBase_proper incidencePoint t
  exact LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr inferInstance

theorem seed_mem_smoothCurveBase_of_minors (t : Fin 3 → ℂ) (h : SeedMinorCover t) :
    seedBasePoint ∈ smoothCurveBase t := by
  apply (seed_mem_smoothCurveBase_iff t).mpr
  intro x
  obtain ⟨i, z, _, hx⟩ := exists_seedChart_prime t x
  obtain ⟨p, q, hp, hq⟩ := h i z
  let v := chartEquations incidencePoint t i p
  let π := toCurve incidencePoint t i p
  let y := movingPrime t i z
  let j := movingChartToCurve t i
  let f := relativeCurveToBase incidencePoint t
  have hj : j ≫ f = specToBase ParameterAlgebra (AffineCurveChart incidencePoint t i) :=
    CycleQ2FirstOrderCurveCharts.originalCurveChart_overBase t i
  have : LocallyOfFinitePresentation (specToBase ParameterAlgebra (AffineCurveChart incidencePoint t i)) := by
    rw [← hj]
    infer_instance
  have hp' : π (rowPivot incidencePoint t i p) ∉ y.asIdeal := by
    rw [show π (rowPivot incidencePoint t i p) = _ from toCurve_rowPivot incidencePoint t i p]
    exact (pivot_notMem_movingPrime_iff t i z p).mpr hp
  have hq' : curvePolynomialMap t i incidencePoint (minorPolynomial v q) ∉ y.asIdeal := by
    apply (jacobianMinor_notMem_movingPrime_iff t i z v q).mpr
    change curvePolynomialMap t i seed (jacobianMinor
      (fun k => MvPolynomial.map seedMap (chartEquations incidencePoint t i p k)) q) ∉ z.asIdeal
    rw [chartEquations, sectionRows_map]
    exact hq
  have hs := smoothAt_threeRowMinor v q (PrimeSpectrum.comap π.toRingHom y) hq'
  have hloc := smoothAt_of_pivotEquiv π (rowPivot incidencePoint t i p) (pivotEquiv t i p)
    (pivotEquiv_algebraMap t i p) y hp' hs
  change (f.stalkMap (seedCurveToRelative t x)).hom.FormallySmooth
  rw [← hx]
  apply (mem_smoothLocus_openImmersion_iff j f y).mpr
  change ((j ≫ f).stalkMap y).hom.FormallySmooth
  rw [hj]
  exact hloc

/-- A smooth dimension-one original seed member supplies all the concrete
Jacobian minors of the same section after restricting to its matrix pivots. -/
theorem seedMinorCover_of_smooth_seed (t : Fin 3 → ℂ)
    (hs : SmoothOfRelativeDimension 1 (specializedCurveToBase seed t)) : SeedMinorCover t := by
  intro i z
  obtain ⟨p, hp⟩ := exists_seedPivot_notMem t i z
  let v := chartEquations seed t i p
  let π := toCurve seed t i p
  let P := z.asIdeal.comap π.toRingHom
  have hu : rowPivot seed t i p ∉ P := by
    change π (rowPivot seed t i p) ∉ z.asIdeal
    rw [show π (rowPivot seed t i p) = _ from toCurve_rowPivot seed t i p]
    exact hp
  obtain ⟨q, hq⟩ := CycleQ2LiteralAbelJacobiSeedLiftConverse.exists_minor_notMem_of_smooth_away
    v (by decide) P _ hu (seedRowPivot_smoothOfRelativeDimension t i p hs)
  refine ⟨p, q, hp, ?_⟩
  have htranspose : minorPolynomial v q = (Matrix.of fun a b : Fin 3 => pderiv (q b) (v a)).det :=
    Matrix.det_transpose _
  change Ideal.Quotient.mk (Ideal.span (Set.range v)) (minorPolynomial v q) ∉ P
  rwa [htranspose]

/-- The original section family and its unchanged first-order germ are smooth
once the three original equations pass the Jacobian test at the seed. -/
theorem smooth_neighborhood_of_seed_minors (t : Fin 3 → ℂ) (h : SeedMinorCover t) :
    Smooth (firstOrderCurveToBase t) ∧
    ∃ V : parameterScheme.Opens, seedBasePoint ∈ V ∧
      Smooth ((relativeCurveToBase incidencePoint t) ∣_ V) ∧
      IsProper ((relativeCurveToBase incidencePoint t) ∣_ V) ∧
      Function.Surjective ((relativeCurveToBase incidencePoint t) ∣_ V) := by
  have hx := (seed_mem_smoothCurveBase_iff t).mp (seed_mem_smoothCurveBase_of_minors t h)
  obtain ⟨V, hV, hs, hp, hsurj⟩ := (exists_smooth_proper_surjective_neighborhood_iff t).mpr hx
  exact ⟨firstOrderCurve_smooth_of_neighborhood t V hV hs, V, hV, hs, hp, hsurj⟩

/-- Smoothness of the original specialized seed in the expected dimension
gives a smooth proper surjective neighborhood of the same moving curve. -/
theorem smooth_neighborhood_of_smooth_seed (t : Fin 3 → ℂ)
    (hs : SmoothOfRelativeDimension 1 (specializedCurveToBase seed t)) :
    ∃ V : parameterScheme.Opens, seedBasePoint ∈ V ∧
      Smooth ((relativeCurveToBase incidencePoint t) ∣_ V) ∧
      IsProper ((relativeCurveToBase incidencePoint t) ∣_ V) ∧
      Function.Surjective ((relativeCurveToBase incidencePoint t) ∣_ V) :=
  (smooth_neighborhood_of_seed_minors t (seedMinorCover_of_smooth_seed t hs)).2

end CycleQ2LiteralAbelJacobiSeedLift

#print axioms CycleQ2LiteralAbelJacobiSeedLift.firstOrderCurve_smooth_of_neighborhood
#print axioms CycleQ2LiteralAbelJacobiSeedLift.seed_mem_smoothCurveBase_of_minors
#print axioms CycleQ2LiteralAbelJacobiSeedLift.seedMinorCover_of_smooth_seed
#print axioms CycleQ2LiteralAbelJacobiSeedLift.smooth_neighborhood_of_seed_minors
#print axioms CycleQ2LiteralAbelJacobiSeedLift.smooth_neighborhood_of_smooth_seed

end
