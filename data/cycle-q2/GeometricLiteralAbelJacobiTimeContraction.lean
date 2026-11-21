import Proposal.GeometricCurveNormalContraction
import Proposal.GeometricLiteralAbelJacobiSeedLiftDimension
import Proposal.GeometricLiteralAbelJacobiSeedLiftRegular
import Proposal.GeometricLiteralAbelJacobiSmoothNormal
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.LocalProperties.Submodule

/-!
# Contraction on every original smooth seed curve chart

On a standard smooth curve patch every differential is a multiple of a single
generator. Clearing the denominators of two such expressions shows that
their exterior product vanishes locally. The principal cover detects zero
on the original affine chart, even when its cotangent line has no global basis.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralAbelJacobiTimeContraction

section Local

variable {R : Type} [CommRing R] [Algebra ℂ R]

private theorem one_generator [Algebra.IsStandardSmoothOfRelativeDimension 1 ℂ R] :
    ∃ g : KaehlerDifferential ℂ R, ∀ x, ∃ a : R, a • g = x := by
  rcases subsingleton_or_nontrivial R with _ | _
  · have := Module.subsingleton R (KaehlerDifferential ℂ R)
    exact ⟨0, fun x => ⟨0, Subsingleton.elim _ _⟩⟩
  have : Algebra.IsStandardSmooth ℂ R := Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth 1
  have hr := Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential (R := ℂ) (S := R) 1
  have hd : Module.finrank R (KaehlerDifferential ℂ R) = 1 := by simp [Module.finrank, hr]
  obtain ⟨g, _, hg⟩ := (finrank_eq_one_iff' (K := R) (V := KaehlerDifferential ℂ R)).mp hd
  exact ⟨g, hg⟩

omit [Algebra ℂ R] in
private theorem clear_generator {S M N : Type*} [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N] [Module R N]
    [IsScalarTower R S N] (U : Submonoid R) [IsLocalization U S]
    (f : M →ₗ[R] N) [IsLocalizedModule U f] (g : N) (m x : M)
    (s : U) (hs : (s : R) • g = f m) (a : S) (ha : a • g = f x) :
    ∃ d : U, ∃ b : R, (d : R) • x = b • m := by
  obtain ⟨⟨b,t⟩, ht⟩ := IsLocalization.surj U a
  change a * algebraMap R S (t : R) = algebraMap R S b at ht
  have hf : f (((s * t : U) : R) • x) = f (b • m) := by
    simp only [map_smul, Submonoid.coe_mul, mul_smul, ← ha, ← hs]
    rw [smul_comm (t : R) a, ← IsScalarTower.algebraMap_smul S (t : R) g, smul_smul, ht,
      IsScalarTower.algebraMap_smul, smul_comm (s : R) b]
  obtain ⟨k, hk⟩ := (IsLocalizedModule.eq_iff_exists U f).mp hf
  exact ⟨k * (s * t), (k : R) * b, by simpa only [Submonoid.smul_def, Submonoid.coe_mul, mul_smul] using hk⟩

/-- The exterior square vanishes on an affine chart that is locally standard smooth of
relative dimension one. This does not require the cotangent module to be globally free. -/
theorem exteriorTwo_subsingleton_of_curve
    (h : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1) (algebraMap ℂ R)) :
    Subsingleton (⋀[R]^2 (KaehlerDifferential ℂ R)) := by
  classical
  let Ω := KaehlerDifferential ℂ R
  let W := ⋀[R]^2 Ω
  obtain ⟨s, hs, hloc⟩ := h
  have hz (v : Fin 2 → Ω) : exteriorPower.ιMulti R 2 v = 0 := by
    apply Module.eq_zero_of_isLocalized_span s hs
      (fun r : s => LocalizedModule (.powers r.val) W)
      (fun r : s => LocalizedModule.mkLinearMap (.powers r.val) W)
    intro r
    let S := Localization.Away r.val
    let U := Submonoid.powers r.val
    have hstd := hloc r.val r.property
    rw [← IsScalarTower.algebraMap_eq ℂ R S] at hstd
    have : Algebra.IsStandardSmoothOfRelativeDimension 1 ℂ S :=
      (RingHom.isStandardSmoothOfRelativeDimension_algebraMap 1).mp hstd
    let f := KaehlerDifferential.map ℂ ℂ R S
    obtain ⟨g, hg⟩ := one_generator (R := S)
    obtain ⟨⟨m,d⟩, hmd⟩ := IsLocalizedModule.surj U f g
    choose a ha using fun j => hg (f (v j))
    choose k b hkb using fun j => clear_generator U f g m (v j) d hmd (a j) (ha j)
    rw [← map_zero (LocalizedModule.mkLinearMap (.powers r.val) W)]
    apply (IsLocalizedModule.eq_iff_exists U _).mpr
    refine ⟨∏ j, k j, ?_⟩
    change ((∏ j, k j : U) : R) • exteriorPower.ιMulti R 2 v = _
    rw [Submonoid.coe_finsetProd, ← AlternatingMap.map_smul_univ]
    simp only [hkb, AlternatingMap.map_smul_univ, smul_zero]
    rw [(exteriorPower.ιMulti R 2).map_eq_zero_of_eq (fun _ => m) (i := 0) (j := 1) rfl (by decide),
      smul_zero]
  have hb : (⊤ : Submodule R W) ≤ ⊥ := by
    rw [← exteriorPower.ιMulti_span R 2 Ω, Submodule.span_le]
    rintro _ ⟨v, rfl⟩
    exact hz v
  exact (subsingleton_iff_forall_eq 0).mpr fun w => hb (Submodule.mem_top (x := w))

end Local

open CycleQ2SeedConeSection (seed)
open CategoryTheory AlgebraicGeometry
open CycleQ2LiteralAbelJacobiEquations CycleQ2LiteralAbelJacobiMovingNormal
  CycleQ2LiteralAbelJacobiContraction CycleQ2LiteralAbelJacobiRelativeNormal
  CycleQ2LiteralAbelJacobiSeedLift CycleQ2LiteralAbelJacobiSeedLiftDimension
  CycleQ2LiteralAbelJacobiSeedLiftRegular CycleQ2SpecializedProjectiveCurve
  CycleQ2SpecializedCurveCoordinateChart
open scoped DualNumber

attribute [local instance] CycleQ2IncidenceSeedFiber.seedAlgebra
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderAlgebra
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderModule
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderSMul
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderTower
  CycleQ2LiteralAbelJacobiMovingNormal.thickCommRing
  CycleQ2LiteralAbelJacobiContraction.fixedCommRing
  CycleQ2LiteralAbelJacobiContraction.seedChartCommRing
  CycleQ2LiteralAbelJacobiMovingNormal.closedAlgebra
  CycleQ2LiteralAbelJacobiContraction.fixedAlgebra
  CycleQ2LiteralAbelJacobiContraction.fixedTower
  CycleQ2LiteralAbelJacobiContraction.fixedSeedTower

theorem seedChart_exteriorTwo (t : Fin 3 → ℂ) (ht : AlgebraicIndependent ℚ t) (i : Fin 4) :
    Subsingleton (⋀[A t i]^2 (KaehlerDifferential ℂ (A t i))) := by
  have hs := smooth_seed_of_seedMinorCover t (CycleQ2LiteralAbelJacobiBertiniMinor.prime_minor_of_independent t ht)
  let j := (specializedCoordinateAffineChart seed t i).inv ≫ (specializedCoordinatePatch seed t i).ι
  have : IsOpenImmersion j := by dsimp [j]; infer_instance
  have hc : SmoothOfRelativeDimension 1 (j ≫ specializedCurveToBase seed t) :=
    smoothOfRelativeDimension_comp 0 1 _ _
  dsimp only [j] at hc
  rw [Category.assoc, specializedCoordinateAffineChart_overBase] at hc
  exact exteriorTwo_subsingleton_of_curve ((HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension 1)).mp hc)

/-- All four original charts of the same seed section have a unique contraction of
ambient two-forms for the original moving normal. -/
theorem contraction_unique_of_independent (t : Fin 3 → ℂ) (ht : AlgebraicIndependent ℚ t) :
    ∃ hf : ∀ i : Fin 4, Module.Flat ℂ[ε] (B t i), ∀ i : Fin 4,
      ∃! f : (⋀[T i]^2 (KaehlerDifferential ℂ (T i))) →ₗ[T i] KaehlerDifferential ℂ (A t i),
        (∀ v : Derivation ℂ (T i) (A t i),
          (∀ x : idealOnT t i, v x.val = @relativeNormal t i (hf i) ((idealOnT t i).toCotangent x)) →
          f = contractRestrict v) ∧
        ∀ β : KaehlerDifferential ℂ (T i),
          f (exteriorPower.ιMulti (T i) 2 ![KaehlerDifferential.D ℂ (T i) (cubicOnT i), β]) =
            -(seedChartMap t i (tangentL i)) • KaehlerDifferential.map ℂ ℂ (T i) (A t i) β := by
  have h := CycleQ2LiteralAbelJacobiBertiniMinor.prime_minor_of_independent t ht
  have hs := smooth_seed_of_seedMinorCover t h
  refine ⟨firstOrderCurveChart_flat_of_smooth_seed t hs, fun i => ?_⟩
  have := firstOrderCurveChart_flat_of_smooth_seed t hs i
  have := CycleQ2LiteralAbelJacobiSmoothNormal.seedChart_smooth_of_minors t h i
  have := seedChart_exteriorTwo t ht i
  exact CycleQ2CurveNormalContraction.moving_normal_contraction_unique t i

end CycleQ2LiteralAbelJacobiTimeContraction

end

#print axioms CycleQ2LiteralAbelJacobiTimeContraction.contraction_unique_of_independent
