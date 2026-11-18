import Proposal.GeometricLiteralIncidenceCylinderMap
import Proposal.GeometricLiteralAmbientSurface
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-!
# The fixed-sextic section as an embedded time correspondence

The scheme map on each homogeneous chart is determined by the parameter
coefficients and the fractions with monomial numerators of coefficient one.
These are respectively detected by the two projections of the correspondence.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2LiteralTimeFamilyEmbedding

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial HomogeneousLocalization
open CycleQ2IncidenceNormalForm CycleQ2IncidenceUniversalChart CycleQ2IncidenceImageLine
  CycleQ2IncidenceGenericPointSemantics CycleQ2GeometricIncidenceProj
  CycleQ2IncidenceFamilyContainment CycleQ2ThreefoldCoefficientMap

section Charts
variable {R S : Type} [CommRing R] [CommRing S] [Algebra ℂ R] [Algebra ℂ S]
  (φ : R →+* S) (y : ParameterIndex → R) (u : ParameterIndex → S)
  (hF : MvPolynomial.map φ (pointEquationF y) = pointEquationF u)

private abbrev scalarOnChart (b : SexticRing u) : S →+* Away (sexticGrade u) b :=
  (fromZeroRingHom (sexticGrade u) (Submonoid.powers b)).comp (algebraMap S (sexticGrade u 0))

/-- On a standard chart the coefficient functions and the universal homogeneous
fractions jointly determine every ring homomorphism. -/
private theorem chart_ext {D : Type} [CommRing D] {d : ℕ} {a : SexticRing y} (ha : a ∈ sexticGrade y d)
    (g h : Away (sexticGrade u) (graded φ y u hF a) →+* D)
    (hc : ∀ s, g (scalarOnChart u _ s) = h (scalarOnChart u _ s))
    (he : ∀ z, g (Away.map (graded φ y u hF) a z) = h (Away.map (graded φ y u hF) a z)) :
    g = h := by
  classical
  let f := graded φ y u hF
  let b := f a
  have hb : b ∈ sexticGrade u d := f.2 ha
  apply RingHom.ext
  intro z
  obtain ⟨n, q, hq, rfl⟩ := Away.mk_surjective (sexticGrade u) hb z
  obtain ⟨p, hp, rfl⟩ := hq
  let term (e : p.support) : Away (sexticGrade y) a :=
    Away.mk _ ha n (Ideal.Quotient.mk (sexticIdeal y) (monomial e.val 1))
      ⟨_, isWeightedHomogeneous_monomial _ _ _ (hp (mem_support_iff.mp e.property)), rfl⟩
  have hz : Away.mk (sexticGrade u) hb n (Ideal.Quotient.mk _ p) ⟨p, hp, rfl⟩ =
      ∑ e : p.support, scalarOnChart u b (coeff e.val p) * Away.map f a (term e) := by
    apply HomogeneousLocalization.val_injective
    change (Away.mk (sexticGrade u) hb n (Ideal.Quotient.mk _ p) _).val =
      algebraMap (Away (sexticGrade u) b) (Localization.Away b)
        (∑ e : p.support, scalarOnChart u b (coeff e.val p) * Away.map f a (term e))
    rw [map_sum]
    have ht (e : p.support) :
        algebraMap (Away (sexticGrade u) b) (Localization.Away b)
          (scalarOnChart u b (coeff e.val p) * Away.map f a (term e)) =
        Localization.mk (Ideal.Quotient.mk _ (monomial e.val (coeff e.val p)))
          (Submonoid.pow b n) := by
      dsimp only [term]
      rw [map_mul, Away.map_mk]
      change Localization.mk (Ideal.Quotient.mk _ (C (coeff e.val p))) 1 *
          Localization.mk (Ideal.Quotient.mk _ (MvPolynomial.map φ (monomial e.val 1)))
            (Submonoid.pow b n) = _
      rw [Localization.mk_mul, one_mul, ← map_mul, MvPolynomial.map_monomial, map_one,
        C_mul_monomial, mul_one]
    simp_rw [ht]
    change Localization.mk _ (Submonoid.pow b n) = _
    rw [← Localization.mk_sum, ← map_sum]
    congr 2
    apply congrArg (Ideal.Quotient.mk (sexticIdeal u))
    exact p.as_sum.trans (Finset.sum_coe_sort (s := p.support) (f := fun e => monomial e (coeff e p))).symm
  apply (congrArg g hz).trans
  apply Eq.trans _ (congrArg h hz).symm
  rw [map_sum, map_sum]
  exact Finset.sum_congr rfl (fun e _ => by rw [map_mul, map_mul, hc, he])


private def ringAt {W : Scheme} {A : Type} [CommRing A] (v : W ⟶ Spec (CommRingCat.of A)) :
    CommRingCat.of A ⟶ Γ(W, ⊤) := (Scheme.ΓSpecIso _).inv ≫ v.appTop

private theorem ringAt_comp {W : Scheme} {A B : Type} [CommRing A] [CommRing B]
    (v : W ⟶ Spec (CommRingCat.of B)) (α : A →+* B) :
    ringAt (v ≫ Spec.map (CommRingCat.ofHom α)) = CommRingCat.ofHom α ≫ ringAt v := by
  simp only [ringAt, Scheme.Hom.comp_appTop, Scheme.ΓSpecIso_inv_naturality_assoc]

private theorem ringAt_congr {W : Scheme} {A B : Type} [CommRing A] [CommRing B]
    (r s : W ⟶ Spec (CommRingCat.of B)) (α : A →+* B)
    (H : r ≫ Spec.map (CommRingCat.ofHom α) = s ≫ Spec.map (CommRingCat.ofHom α)) (a : A) :
    (ringAt r).hom (α a) = (ringAt s).hom (α a) := by
  have e := congrArg ringAt H
  simp only [ringAt_comp] at e
  exact ConcreteCategory.congr_hom e a

/-- The coefficient change and the structural projection of the weighted
hypersurface jointly detect maps of arbitrary schemes. -/
theorem coefficient_joint_ext {W : Scheme} (g h : W ⟶ weightedThreefold u)
    (hbase : g ≫ weightedThreefoldToBase u = h ≫ weightedThreefoldToBase u)
    (hproj : g ≫ morphism φ y u hF = h ≫ morphism φ y u hF) : g = h := by
  change W ⟶ Proj (sexticGrade u) at g h
  let f := graded φ y u hF
  let hf := irrelevant_le φ y u hF
  let U := (Proj.mapAffineOpenCover f hf).openCover
  apply Scheme.Cover.hom_ext (U.pullback₁ g)
  intro i
  let a : SexticRing y := i.2
  let d : ℕ := i.1
  have ha : a ∈ sexticGrade y d := i.2.2
  have hd : 0 < d := i.1.2
  let A := Proj.awayι (sexticGrade y) a ha hd
  let B := Proj.awayι (sexticGrade u) (f a) (f.2 ha) hd
  let l := Spec.map (CommRingCat.ofHom (Away.map f a))
  have sq : IsPullback l B A (morphism φ y u hF) := by
    apply IsOpenImmersion.isPullback
    · exact Proj.awayι_comp_map f hf hd a ha
    · simp only [A, B, Proj.opensRange_awayι, morphism, Proj.map_preimage_basicOpen, f]
  let j := (U.pullback₁ g).f i
  let G := U.pullbackHom g i
  have hG : G ≫ B = j ≫ g := U.pullbackHom_map g i
  obtain ⟨H, hHl, hHB⟩ := sq.exists_lift (G ≫ l) (j ≫ h) (by
    rw [Category.assoc, sq.w, ← Category.assoc, hG, Category.assoc, hproj, Category.assoc])
  have hB : B ≫ weightedThreefoldToBase u =
      Spec.map (CommRingCat.ofHom (scalarOnChart u (f a))) := by
    dsimp only [B, weightedThreefoldToBase]
    rw [Proj.awayι_toSpecZero_assoc, ← Spec.map_comp]
    rfl
  have hpt : G = H := by
    apply ext_to_Spec
    apply CommRingCat.hom_ext
    apply chart_ext φ y u hF ha (ringAt G).hom (ringAt H).hom
    · apply ringAt_congr
      rw [← hB, ← Category.assoc, ← Category.assoc, hG, hHB, Category.assoc,
        Category.assoc, hbase]
    · exact ringAt_congr _ _ _ hHl.symm
  exact hG.symm.trans ((congrArg (· ≫ B) hpt).trans hHB)

end Charts

open CycleQ2IncidencePolynomialJacobianBinding CycleQ2LiteralIncidenceTimeCurve
  CycleQ2LiteralIncidenceTimeFamily CycleQ2LiteralIncidenceCylinderMap
  CycleQ2RelativeConstantCurve CycleQ2IncidenceTimeCurve CycleQ2IncidenceEtaleParameter

attribute [local instance] CycleQ2IncidenceTimeCurve.timeParameterCommRing

private abbrev inclusion (t : Fin 3 → ℂ) :=
  relativeCurveToSurface incidencePoint t ≫ surfaceToThreefold incidencePoint

private theorem surface_closed : IsClosedImmersion (surfaceToThreefold incidencePoint) := by
  apply CycleQ2LiteralAmbientSurface.projectiveMap_closedImmersion
  rintro n b ⟨p, hp, rfl⟩
  exact ⟨Ideal.Quotient.mk (sexticIdeal incidencePoint) p, ⟨p, hp, rfl⟩, rfl⟩

/-- Product of the original fixed-sextic time curve with the fixed threefold. -/
abbrev Product := pullback toComplex (pullback.fst seedSextic universalAmbientToBase)

def joint (t : Fin 3 → ℂ) : Family t ⟶ Product :=
  pullback.lift (toCurve t) (toFixedThreefold t) (toFixedThreefold_overComplex t).symm

@[reassoc (attr := simp)] theorem joint_toCurve (t : Fin 3 → ℂ) :
    joint t ≫ pullback.fst _ _ = toCurve t := pullback.lift_fst _ _ _

@[reassoc (attr := simp)] theorem joint_toFixedThreefold (t : Fin 3 → ℂ) :
    joint t ≫ pullback.snd _ _ = toFixedThreefold t := pullback.lift_snd _ _ _

theorem joint_mono (t : Fin 3 → ℂ) : Mono (joint t) := by
  constructor
  intro W g h he
  have hcurve : g ≫ toCurve t = h ≫ toCurve t := by
    simpa only [joint, Category.assoc, pullback.lift_fst] using
      congrArg (· ≫ pullback.fst _ _) he
  have hfixed : g ≫ toFixedThreefold t = h ≫ toFixedThreefold t := by
    simpa only [joint, Category.assoc, pullback.lift_snd] using
      congrArg (· ≫ pullback.snd _ _) he
  apply pullback.hom_ext hcurve
  let := surface_closed
  apply (cancel_mono (inclusion t)).mp
  apply coefficient_joint_ext sexticToParameter universalPoint incidencePoint universal_to_incidence
  · have e := pullback.condition (f := toIncidence) (g := relativeCurveToBase incidencePoint t)
    change toCurve t ≫ toIncidence = toOriginal t ≫ relativeCurveToBase incidencePoint t at e
    simpa only [Category.assoc, inclusion, relativeCurveToBase, surfaceToThreefold_toBase,
      e, toOriginal] using congrArg (· ≫ toIncidence) hcurve
  · simpa only [Category.assoc, toFixedThreefold_original, originalToAmbient, inclusion, toOriginal] using
      congrArg (· ≫ pullback.snd seedSextic universalAmbientToBase) hfixed


/-- The original proper family agrees scheme-theoretically with its embedded
correspondence in the product. -/
theorem joint_isClosedImmersion (t : Fin 3 → ℂ) : IsClosedImmersion (joint t) := by
  apply (IsClosedImmersion.iff_isProper_and_mono _).mpr
  refine ⟨?_, joint_mono t⟩
  have : IsSeparated universalAmbientToBase := by
    unfold universalAmbientToBase weightedThreefoldToBase
    infer_instance
  have : IsProper (joint t ≫ pullback.fst _ _) := by
    rw [joint, pullback.lift_fst]
    exact family_proper t
  exact IsProper.of_comp (joint t) (pullback.fst _ _)

#print axioms coefficient_joint_ext
#print axioms joint_isClosedImmersion

end CycleQ2LiteralTimeFamilyEmbedding
end
