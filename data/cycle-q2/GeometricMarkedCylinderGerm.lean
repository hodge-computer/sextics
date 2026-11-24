import Proposal.GeometricLiteralMovingCurveDifferentialNonzero
import Proposal.GeometricMonicGenericSupport
import Proposal.GeometricLiteralAbelJacobiEvaluationFiber
import Proposal.GeometricLiteralThreefoldVertexMotion
import Proposal.GeometricLiteralAbelJacobiQChart
import Proposal.GeometricLiteralAbelJacobiSeedLiftRegular
import Proposal.GeometricLiteralAbelJacobiSmoothNormal

/-!
# The marked dual-time chart and the tangent space of the full surface

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace CycleQ2MarkedThickCylinderChart

open AlgebraicGeometry CategoryTheory
open scoped DualNumber
open CycleQ2LiteralAbelJacobiMovingNormal CycleQ2LiteralAbelJacobiEquations
  CycleQ2LiteralAbelJacobiContraction CycleQ2LiteralAbelJacobiRelativeNormal
  CycleQ2LiteralCylinderEvaluation CycleQ2FirstOrderChartReduction
  CycleQ2DualNumberRegularQuotient

attribute [local instance] CycleQ2IncidenceSeedFiber.seedAlgebra
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderAlgebra
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderModule
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderSMul
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderTower
  CycleQ2LiteralAbelJacobiMovingNormal.thickCommRing
  CycleQ2LiteralAbelJacobiContraction.fixedCommRing
  CycleQ2LiteralAbelJacobiContraction.seedChartCommRing

private theorem clear_parameter {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (e : S) (l h : R) (he : e * e = 0) (hh : f h = -(e * f l))
    (hred : Function.Surjective ((Ideal.Quotient.mk (Ideal.span {e})).comp f)) :
    Function.Surjective (Localization.awayMap f l) := by
  have normal (x : S) : ∃ r : R, ∃ z : S, x = f r + e * z := by
    obtain ⟨r,hr⟩ := hred (Ideal.Quotient.mk _ x)
    have hx : x - f r ∈ Ideal.span {e} :=
      Ideal.Quotient.eq.mp (show Ideal.Quotient.mk _ x = Ideal.Quotient.mk _ (f r) from hr.symm)
    obtain ⟨z,hz⟩ := Ideal.mem_span_singleton.mp hx
    exact ⟨r,z, by linear_combination hz⟩
  apply Localization.awayMap_surjective_iff.mpr
  intro x
  obtain ⟨r,z,hr⟩ := normal x
  obtain ⟨s,w,hs⟩ := normal z
  refine ⟨l*r - h*s,1,?_⟩
  rw [map_sub,map_mul,map_mul,hh,hr,hs,pow_one]
  linear_combination -(f l * w) * he

variable (t : Fin 3 → ℂ) (i : Fin 4)
abbrev detector := Ideal.Quotient.mk (fixedIdeal i) (tangentL i)
abbrev localizedChart := Localization.awayMap (toFamily t i) (detector i)

theorem localizedChart_surjective : Function.Surjective (localizedChart t i) := by
  let e := algebraMap ℂ[ε] (B t i) ε
  apply clear_parameter (toFamily t i) e (detector i) (cubicOnT i)
  · change algebraMap ℂ[ε] (B t i) ε * algebraMap ℂ[ε] (B t i) ε = 0
    rw [← map_mul,DualNumber.eps_mul_eps,map_zero]
  · exact chartMap_H t i
  · intro b
    obtain ⟨r,hr⟩ := seedChartMap_surjective t i (curveChartReductionEquiv t i b)
    refine ⟨Ideal.Quotient.mk _ r, (curveChartReductionEquiv t i).injective ?_⟩
    exact (chartMap_reduction t i r).trans hr

theorem localizedChart_closed :
    IsClosedImmersion (Spec.map (CommRingCat.ofHom (localizedChart t i))) :=
  IsClosedImmersion.spec_of_surjective _ (localizedChart_surjective t i)

open CycleQ2LiteralAbelJacobiTimeProjection CycleQ2LiteralAbelJacobiTimeFamily
  CycleQ2IncidenceEtaleParameter CycleQ2IncidenceSeedFiberCover CycleQ2LiteralIncidenceCylinderMap
  CycleQ2LiteralAbelJacobiQChart CycleQ2LiteralAmbientCylinder CycleQ2LiteralAbelJacobiTimeCharts
  CycleQ2LiteralAmbientCharts CycleQ2LiteralIncidenceTimeCurve
open CycleQ2LiteralAbelJacobiContraction (seedChartTower)
open CategoryTheory.Limits
attribute [local instance] CycleQ2CurveParameterTangent.chartComplexAlgebra

private theorem seed_chart_smooth (hi : AlgebraicIndependent ℚ t) :
    SmoothOfRelativeDimension 1 (Spec.map (CommRingCat.ofHom (algebraMap ℂ (A t i)))) := by
  let seed := CycleQ2SeedConeSection.seed
  have hs := CycleQ2LiteralAbelJacobiSeedLiftDimension.smooth_seed_of_seedMinorCover t
    (CycleQ2LiteralAbelJacobiBertiniMinor.prime_minor_of_independent t hi)
  let j := (CycleQ2SpecializedCurveCoordinateChart.specializedCoordinateAffineChart seed t i).inv ≫
    (CycleQ2SpecializedCurveCoordinateChart.specializedCoordinatePatch seed t i).ι
  have : IsOpenImmersion j := by dsimp [j]; infer_instance
  have hc : SmoothOfRelativeDimension 1 (j ≫ CycleQ2SpecializedProjectiveCurve.specializedCurveToBase seed t) :=
    smoothOfRelativeDimension_comp 0 1 _ _
  dsimp only [j] at hc
  rw [Category.assoc, CycleQ2SpecializedCurveCoordinateChart.specializedCoordinateAffineChart_overBase] at hc
  exact hc


private theorem thick_chart_nonempty (hi : AlgebraicIndependent ℚ t)
    (hne : seedChartMap t i (tangentL i) ≠ 0) :
    Nonempty (PrimeSpectrum (Localization.Away (toFamily t i (detector i)))) := by
  have hs := seed_chart_smooth t i hi
  have : _root_.IsReduced (A t i) :=
    CycleQ2LiteralAbelJacobiSeedLiftRegular.reduced_of_smoothDimension 1 _
      ((HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension 1)).mp hs)
  have hn : (PrimeSpectrum.basicOpen (seedChartMap t i (tangentL i))) ≠ ⊥ := fun h =>
    hne ((PrimeSpectrum.basicOpen_eq_bot_iff _).mp h).eq_zero
  obtain ⟨x,hx⟩ := (PrimeSpectrum.basicOpen _).ne_bot_iff_nonempty.mp hn
  let g := toFamily t i (detector i)
  let y := PrimeSpectrum.comap (toClosed t i) x
  have hy : y ∈ PrimeSpectrum.basicOpen g := by
    change toClosed t i (chartMap t i (tangentL i)) ∉ x.asIdeal
    simpa [toClosed,chartMap_reduction] using hx
  change y ∈ (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum (B t i))) at hy
  rw [← PrimeSpectrum.localization_away_comap_range (Localization.Away g) g] at hy
  obtain ⟨z,_⟩ := hy
  exact ⟨z⟩

abbrev chartOpen := Spec.map (CommRingCat.ofHom (algebraMap (B t i)
  (Localization.Away (toFamily t i (detector i)))))

theorem actual_thick_immersion (V : parameterScheme.Opens) (hV : seedBasePoint ∈ V) :
    IsImmersion (chartOpen t i ≫ thickChart V t hV i ≫ q V t) := by
  let h := toFamily t i
  let u := detector i
  let j := Spec.map (CommRingCat.ofHom (algebraMap (T i) (Localization.Away u)))
  have : IsOpenImmersion j := IsOpenImmersion.of_isLocalization u
  let g := Spec.map (CommRingCat.ofHom (localizedChart t i))
  have : IsClosedImmersion g := localizedChart_closed t i
  have hm : chartOpen t i ≫ Spec.map (CommRingCat.ofHom h) = g ≫ j := by
    unfold chartOpen g j
    rw [← Spec.map_comp, ← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    change algebraMap _ _ (h x) = Localization.awayMap h u (algebraMap _ _ x)
    simp [Localization.awayMap,IsLocalization.Away.map]
  apply (IsImmersion.comp_iff _ fixedIso.hom).mp
  simp only [Category.assoc, thickChart_toSmoothThreefold]
  change IsImmersion (chartOpen t i ≫ Spec.map (CommRingCat.ofHom h) ≫ CycleQ2LiteralAmbientCharts.chartInclusion i)
  rw [← Category.assoc, hm, Category.assoc]
  infer_instance

open CycleQ2LiteralMovingCurveDifferentialNonzero

/-- The contracted differential on this particular seed curve has nonzero trace. -/
def HasTracedSeedCurve (t : Fin 3 → ℂ) : Prop :=
  ∃ h : ∀ i, CycleQ2SeedSectionAffineInjective.ChartRegular t i,
    differentialTrace t h (curveClass t) ≠ 0

theorem exists_traced_embedded_thick_chart :
    ∃ (t : Fin 3 → ℂ) (j : Fin 3) (V : parameterScheme.Opens) (hV : seedBasePoint ∈ V), AlgebraicIndependent ℚ t ∧ HasTracedSeedCurve t ∧
      Nonempty (PrimeSpectrum (Localization.Away (toFamily t j.succ (detector j.succ)))) ∧
      IsImmersion (chartOpen t j.succ ≫ thickChart V t hV j.succ ≫ q V t) := by
  obtain ⟨t,ht,hreg,V,hV,_,_,_,_,_,_,hf,j,hn⟩ := exists_smooth_time_family
  have := hf j.succ
  rw [relativeNormal_cubic] at hn
  exact ⟨t,j,V,hV,ht,⟨hreg,differentialTrace_curveClass_ne_zero t hreg⟩,thick_chart_nonempty t j.succ ht (neg_ne_zero.mp hn),actual_thick_immersion t j.succ V hV⟩

theorem exists_nonempty_embedded_thick_chart :
    ∃ (t : Fin 3 → ℂ) (j : Fin 3) (V : parameterScheme.Opens) (hV : seedBasePoint ∈ V), AlgebraicIndependent ℚ t ∧
      Nonempty (PrimeSpectrum (Localization.Away (toFamily t j.succ (detector j.succ)))) ∧
      IsImmersion (chartOpen t j.succ ≫ thickChart V t hV j.succ ≫ q V t) := by
  obtain ⟨t,j,V,hV,ht,_,hz,hi⟩ := exists_traced_embedded_thick_chart
  exact ⟨t,j,V,hV,ht,hz,hi⟩

end CycleQ2MarkedThickCylinderChart

namespace CycleQ2MarkedTimeTangentSquare

open CategoryTheory AlgebraicGeometry IsLocalRing
open CycleQ2LiteralIncidenceTimeCurve CycleQ2IncidenceFirstOrder CycleQ2IncidenceEtaleParameter
open CycleQ2IncidencePolynomialJacobianBinding CycleQ2IncidenceSeedFiberCover CycleQ2IncidenceTraceFamily
open CycleQ2FirstOrderNeighborhood
open scoped DualNumber

private theorem kernel_le_square {R S : Type*} [CommRing R] [IsLocalRing R] [CommRing S]
    (f : R →+* S) (hp : (maximalIdeal R).IsPrincipal)
    (e : R) (he : f e ≠ 0) (hn : ¬ IsUnit (f e)) : RingHom.ker f ≤ maximalIdeal R ^ 2 := by
  obtain ⟨π,hπ : maximalIdeal R = Ideal.span {π}⟩ := hp
  have hm : e ∈ maximalIdeal R := fun h => hn (h.map f)
  obtain ⟨w,hw⟩ := Ideal.mem_span_singleton.mp (hπ ▸ hm)
  have hnπ : f π ≠ 0 := by
    intro h
    exact he (by rw [hw,map_mul,h,zero_mul])
  intro x hx
  have hx' : f x = 0 := hx
  have hm' : x ∈ maximalIdeal R := by
    intro h
    exact hn (by
      have hzero : IsUnit (0 : S) := hx' ▸ h.map f
      exact isUnit_of_dvd_unit (dvd_zero _) hzero)
  obtain ⟨a,ha⟩ := Ideal.mem_span_singleton.mp (hπ ▸ hm')
  have ham : a ∈ maximalIdeal R := by
    intro h
    apply hnπ
    have : f π * f a = 0 := by rwa [ha,map_mul] at hx'
    exact (h.map f).isRegular.2 (by simpa using this)
  rw [pow_two,ha]
  exact Ideal.mul_mem_mul (hπ.symm ▸ Ideal.subset_span (Set.mem_singleton _)) ham

private theorem stalk_principal (x : Curve) : (maximalIdeal (Curve.presheaf.stalk x)).IsPrincipal := by
  have := smooth_parameter_curve
  obtain ⟨R, j, hj, q, rfl, φ, _, hφ⟩ :=
    CycleQ2SweptSupport.exists_standard_affine_chart 1 toComplex x
  obtain ⟨g, _, hg⟩ := hφ.exists_etale_mvPolynomial
  let P := MvPolynomial (Fin 1) ℂ
  let : Algebra P R := g.toAlgebra
  have : Algebra.Etale P R := hg
  let p := q.asIdeal.under P
  let : Algebra (Localization.AtPrime p) (Localization.AtPrime q.asIdeal) :=
    Localization.AtPrime.algebraOfLiesOver p q.asIdeal
  let e := (MvPolynomial.uniqueAlgEquiv ℂ (Fin 1)).symm.toRingEquiv
  have : IsPrincipalIdealRing P := IsPrincipalIdealRing.of_surjective e e.surjective
  have h := ((Algebra.isUnramifiedAt_iff_map_eq P p q.asIdeal).mp inferInstance).2
  have hq : (maximalIdeal (Localization.AtPrime q.asIdeal)).IsPrincipal := h ▸
    (IsPrincipalIdealRing.principal p).map_ringHom (algebraMap P (Localization.AtPrime q.asIdeal))
  let e' : Localization.AtPrime q.asIdeal ≃+* Curve.presheaf.stalk (j q) :=
    (StructureSheaf.stalkIso R q).toRingEquiv.trans (asIso (j.stalkMap q)).symm.commRingCatIsoToRingEquiv
  exact (IsLocalRing.map_ringEquiv_maximalIdeal e') ▸ hq.map_ringHom e'

private instance dualLocal : IsLocalRing ℂ[ε] := by
  apply IsLocalRing.of_unique_max_ideal
  obtain ⟨I,hI⟩ := Ideal.exists_maximal (α := ℂ[ε])
  refine ⟨I,hI,fun J hJ => ?_⟩
  exact (dualNumber_prime_ideal ⟨J,hJ.isPrime⟩).trans (dualNumber_prime_ideal ⟨I,hI.isPrime⟩).symm

open CycleQ2LiteralAbelJacobiTimeFamily

/-- At the marked point, the kernel of the dual-time immersion lies in the square
of the maximal ideal of the original time curve. -/
theorem tangentLift_ker_le_square (V : parameterScheme.Opens) (hV : seedBasePoint ∈ V)
    (z : Spec (CommRingCat.of ℂ[ε])) :
    RingHom.ker ((tangentLift V hV).stalkMap z).hom ≤
      maximalIdeal ((timeOpen V).toScheme.presheaf.stalk (tangentLift V hV z)) ^ 2 := by
  let k := CommRingCat.of ℂ[ε]
  let τ := tangentLift V hV
  let a := (timeOpen V).ι ≫ toIncidence
  have hτ : τ ≫ a = firstOrderParameterPoint := by simp [τ,a]
  have hs : Function.Surjective (τ.stalkMap z) := by
    have h := firstOrderParameterPoint.stalkMap_surjective z
    rw [← hτ,Scheme.Hom.stalkMap_comp] at h
    exact Function.Surjective.of_comp h
  have hz : z = closedPoint ℂ[ε] :=
    (firstOrderPoint_eq_closedPoint z).trans (firstOrderPoint_eq_closedPoint _).symm
  subst z
  let u := (stalkClosedPointIso k).commRingCatIsoToRingEquiv
  obtain ⟨e,he⟩ := hs (u.symm ε)
  let z := τ (closedPoint ℂ[ε])
  let e' := (asIso ((timeOpen V).ι.stalkMap z)).commRingCatIsoToRingEquiv
  have hp : (maximalIdeal ((timeOpen V).toScheme.presheaf.stalk z)).IsPrincipal :=
    (map_ringEquiv_maximalIdeal e') ▸ (stalk_principal ((timeOpen V).ι z)).map_ringHom e'
  apply kernel_le_square _ hp e
  · rw [show (τ.stalkMap _).hom e = _ from he]
    intro hz
    have hh := congrArg (fun a => TrivSqZeroExt.snd (u a)) hz
    simp at hh
  · rw [show (τ.stalkMap _).hom e = _ from he]
    intro hu
    have he' : IsUnit (ε : ℂ[ε]) := by
      rw [← u.apply_symm_apply (ε : ℂ[ε])]
      exact hu.map u.toRingHom
    have hn : IsNilpotent (ε : ℂ[ε]) := ⟨2, by rw [pow_two,DualNumber.eps_mul_eps]⟩
    exact hn.not_isUnit he'

end CycleQ2MarkedTimeTangentSquare

namespace CycleQ2MarkedSurfaceTangentSquare
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing

private theorem through_stalk {R : CommRingCat.{0}} [IsLocalRing R] {X : Scheme.{0}}
    (u : Spec R ⟶ X) (x : X) (h : u (closedPoint R) = x) :
    ∃ φ : X.presheaf.stalk x ⟶ R, Spec.map φ ≫ X.fromSpecStalk x = u := by
  subst x
  exact ⟨Scheme.stalkClosedPointTo u, Scheme.Spec_stalkClosedPointTo_fromSpecStalk u⟩

private theorem through_other_stalk {X S : Scheme.{0}} (p : X ⟶ S)
    (x : X) (s : S) (h : s = p x) :
    ∃ t : S.presheaf.stalk s ⟶ X.presheaf.stalk x, IsLocalHom t.hom ∧
      Spec.map t ≫ S.fromSpecStalk s = X.fromSpecStalk x ≫ p := by
  subst s
  exact ⟨p.stalkMap x, inferInstance, Scheme.SpecMap_stalkMap_fromSpecStalk p⟩

private theorem quotient_factor {R S A : Type} [CommRing R] [CommRing S] [CommRing A]
    (f : R →+* S) (hf : Function.Surjective f) (g : R →+* A) (h : RingHom.ker f ≤ RingHom.ker g) :
    ∃ l : S →+* A, l.comp f = g := by
  let l := (Ideal.Quotient.lift (RingHom.ker f) g h).comp (RingHom.quotientKerEquivOfSurjective hf).symm.toRingHom
  exact ⟨l, RingHom.ext (fun x => by simp [l])⟩

/-- The infinitesimal test ring of the source gives base change of the square-order
stalk-kernel condition without an explicit isomorphism between the two ideal sheaves. -/
theorem pullback_square_kernel {M U X S : Scheme.{0}} {v : M ⟶ U} {i : M ⟶ X}
    {j : U ⟶ S} {p : X ⟶ S} (H : IsPullback v i j p) (z : M)
    (hi : Function.Injective i)
    (hs : Function.Surjective (j.stalkMap (v z)))
    (hk : RingHom.ker (j.stalkMap (v z)).hom ≤ maximalIdeal (S.presheaf.stalk (j (v z))) ^ 2) :
    RingHom.ker (i.stalkMap z).hom ≤ maximalIdeal (X.presheaf.stalk (i z)) ^ 2 := by
  let B := X.presheaf.stalk (i z)
  let m := maximalIdeal B
  let R := CommRingCat.of (B ⧸ m ^ 2)
  let k : B ⟶ R := CommRingCat.ofHom (Ideal.Quotient.mk (m ^ 2))
  have hproper : m ^ 2 ≠ ⊤ := ne_top_of_le_ne_top (maximalIdeal.isMaximal B).ne_top
    (Ideal.pow_le_self (by decide))
  let : Nontrivial R := Ideal.Quotient.nontrivial_iff.mpr hproper
  let : IsLocalRing R := IsLocalRing.of_surjective' k.hom Ideal.Quotient.mk_surjective
  have : IsLocalHom k.hom := IsLocalHom.of_surjective k.hom Ideal.Quotient.mk_surjective
  let a : Spec R ⟶ X := Spec.map k ≫ X.fromSpecStalk (i z)
  have haz : a (closedPoint R) = i z := by
    change (Spec.map k ≫ X.fromSpecStalk (i z)) (closedPoint R) = i z
    rw [Scheme.Hom.comp_apply, Spec_closedPoint, Scheme.fromSpecStalk_closedPoint]
  have he : j (v z) = p (i z) := congrArg (fun (f : _ ⟶ S) => f z) H.w
  obtain ⟨t,ht,htp⟩ := through_other_stalk p (i z) (j (v z)) he
  have hmap : (maximalIdeal (S.presheaf.stalk (j (v z))) ^ 2).map t.hom ≤ m ^ 2 := by
    rw [Ideal.map_pow]
    exact pow_le_pow_left' (map_maximalIdeal_le t.hom) 2
  have hker : RingHom.ker (j.stalkMap (v z)).hom ≤ RingHom.ker (t ≫ k).hom := by
    intro x hx
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (hmap (Ideal.mem_map_of_mem t.hom (hk hx)))
  obtain ⟨l,hl⟩ := quotient_factor (j.stalkMap (v z)).hom hs (t ≫ k).hom hker
  let b : Spec R ⟶ U := Spec.map (CommRingCat.ofHom l) ≫ U.fromSpecStalk (v z)
  have hcomm : b ≫ j = a ≫ p := by
    change (Spec.map _ ≫ _) ≫ _ = (Spec.map _ ≫ _) ≫ _
    rw [Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk, ← Spec.map_comp_assoc]
    have hcat : j.stalkMap (v z) ≫ CommRingCat.ofHom l = t ≫ k := CommRingCat.hom_ext hl
    rw [hcat, Spec.map_comp_assoc, htp, Category.assoc]
  let u := H.lift b a hcomm
  have hui : u ≫ i = a := H.lift_snd _ _ _
  have hu : u (closedPoint R) = z := hi ((congrArg (fun (g : Spec R ⟶ X) => g (closedPoint R)) hui).trans haz)
  obtain ⟨ψ,hψ⟩ := through_stalk u z hu
  have hmaps : Spec.map (i.stalkMap z ≫ ψ) ≫ X.fromSpecStalk (i z) = Spec.map k ≫ X.fromSpecStalk (i z) := by
    rw [Spec.map_comp_assoc, Scheme.SpecMap_stalkMap_fromSpecStalk, ← Category.assoc, hψ, hui]
  have eq : i.stalkMap z ≫ ψ = k := Spec.map_inj.mp ((cancel_mono (X.fromSpecStalk (i z))).mp hmaps)
  intro x hx
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  change k.hom x = 0
  rw [← eq, CommRingCat.hom_comp,RingHom.comp_apply,show (i.stalkMap z).hom x = 0 from hx,map_zero]

open CycleQ2LiteralAbelJacobiTimeFamily CycleQ2LiteralAbelJacobiTimeCharts
  CycleQ2IncidenceEtaleParameter CycleQ2IncidenceSeedFiberCover CycleQ2LiteralIncidenceTimeCurve
  CycleQ2IncidenceFirstOrder CycleQ2LiteralIncidenceCylinderMap CycleQ2MarkedTimeTangentSquare
  CycleQ2MarkedThickCylinderChart CycleQ2FirstOrderCurveCharts

attribute [local instance] CycleQ2IncidenceSeedFiber.seedAlgebra
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderAlgebra
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderModule
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderSMul
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderTower
  CycleQ2LiteralAbelJacobiMovingNormal.thickCommRing
  CycleQ2LiteralAbelJacobiContraction.fixedCommRing

private theorem time_immersion (V : parameterScheme.Opens) (hV : seedBasePoint ∈ V) :
    IsImmersion (tangentLift V hV) := by
  let a := (timeOpen V).ι ≫ toIncidence
  have : IsImmersion (tangentLift V hV ≫ a) := by
    rw [show tangentLift V hV ≫ a = firstOrderParameterPoint by simp [a]]
    infer_instance
  exact IsImmersion.of_comp _ a

theorem surface_kernel_le_square (V : parameterScheme.Opens) (hV : seedBasePoint ∈ V)
    (t : Fin 3 → ℂ) (z : (pullback (tangentLift V hV) (projection V t) : Scheme.{0})) :
    RingHom.ker ((pullback.snd (tangentLift V hV) (projection V t)).stalkMap z).hom ≤
      maximalIdeal ((family V t).presheaf.stalk ((pullback.snd (tangentLift V hV) (projection V t)) z)) ^ 2 := by
  have := time_immersion V hV
  exact pullback_square_kernel (IsPullback.of_hasPullback (tangentLift V hV) (projection V t)) z
    (pullback.snd (tangentLift V hV) (projection V t)).isEmbedding.injective ((tangentLift V hV).stalkMap_surjective _)
    (tangentLift_ker_le_square V hV _)

private theorem ker_open_comp {U Z X : Scheme.{0}} (e : U ⟶ Z) (f : Z ⟶ X)
    [IsOpenImmersion e] (z : U) :
    RingHom.ker ((e ≫ f).stalkMap z).hom = RingHom.ker (f.stalkMap (e z)).hom := by
  rw [Scheme.Hom.stalkMap_comp, CommRingCat.hom_comp, RingHom.ker_comp_of_injective]
  exact (ConcreteCategory.bijective_of_isIso (e.stalkMap z)).injective

/-- At the actual localized dual-time chart the surface-to-chart stalk kernel is
quadratic in the maximal ideal of the original fixed-sextic surface. -/
theorem marked_chart_kernel_le_square (V : parameterScheme.Opens) (hV : seedBasePoint ∈ V)
    (t : Fin 3 → ℂ) (i : Fin 4) (z : Spec (CommRingCat.of (Localization.Away (CycleQ2LiteralCylinderEvaluation.toFamily t i (detector i))))) :
    RingHom.ker ((chartOpen t i ≫ thickChart V t hV i).stalkMap z).hom ≤
      maximalIdeal ((family V t).presheaf.stalk ((chartOpen t i ≫ thickChart V t hV i) z)) ^ 2 := by
  let e := chartOpen t i ≫ firstOrderChartToCurve t i ≫ (firstOrderIso V t hV).hom
  let f := pullback.snd (tangentLift V hV) (projection V t)
  have : IsOpenImmersion (chartOpen t i) := IsOpenImmersion.of_isLocalization (CycleQ2LiteralCylinderEvaluation.toFamily t i (detector i))
  have : IsOpenImmersion e := by dsimp [e]; infer_instance
  have he : chartOpen t i ≫ thickChart V t hV i = e ≫ f := by simp only [e,f,thickChart,Category.assoc]
  rw [he, ker_open_comp]
  exact surface_kernel_le_square V hV t (e z)

end CycleQ2MarkedSurfaceTangentSquare

#print axioms CycleQ2MarkedSurfaceTangentSquare.marked_chart_kernel_le_square
