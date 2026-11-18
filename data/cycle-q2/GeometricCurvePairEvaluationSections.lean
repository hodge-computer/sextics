import Proposal.GeometricLiteralAbelJacobiEvaluationWedge
import Proposal.GeometricLiteralAbelJacobiQAffineForms

/-!
# Realization of a localized curve velocity in the original affine evaluation

On any affine-chart subopen, functions from a presentation of the moving and
reduced coordinate rings determine sections and their universal differentials.
When the coefficient square and the given velocities agree on functions,
the original sheaf evaluation of any realized two-form is the ordinary
one-form obtained from the localized ring contraction.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1400000

noncomputable section
namespace CycleQ2CurvePairEvaluationSections

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
  CycleQ2GeometricDifferentialSheaf CycleQ2GeometricExteriorSheaf
  CycleQ2GeometricSheafKaehlerMap CycleQ2GeometricAffineDifferentialSheaf
  CycleQ2GeometricAffineKahlerSheaf CycleQ2ExteriorSectionNaturality
  CycleQ2LiteralAbelJacobiQPullback CycleQ2LiteralAbelJacobiEvaluationAffine
  CycleQ2LiteralAbelJacobiEvaluationWedge CycleQ2LiteralAbelJacobiContraction

attribute [local instance] CycleQ2GeometricExteriorSheaf.exteriorObjectModule

variable {B A P Q : Type} [CommRing B] [CommRing A] [CommRing P] [CommRing Q]
  [Algebra ℂ B] [Algebra ℂ A] [Algebra ℂ P] [Algebra ℂ Q] [Algebra B A] [Algebra P Q]
  [IsScalarTower ℂ B A] [IsScalarTower ℂ P Q]
  (U : (Spec (CommRingCat.of B)).Opens)

private abbrev reducedOpen := reduction B A ⁻¹ᵁ U
private abbrev functionsAt {S : Type} [CommRing S] (V : (Spec (CommRingCat.of S)).Opens) := AffineSections S V
abbrev compatible {R S : Type} [CommRing R] [CommRing S] [Algebra ℂ R] [Algebra ℂ S]
    (V : (Spec (CommRingCat.of S)).Opens) (φ : R →+* functionsAt V) :=
  ∀ z : ℂ, φ (algebraMap ℂ R z) = coefficientOn (Spec.structureSheaf S) (affineCoefficient S) V z

abbrev oneSection {R S : Type} [CommRing R] [CommRing S] [Algebra ℂ R] [Algebra ℂ S]
    (V : (Spec (CommRingCat.of S)).Opens) (φ : R →+* functionsAt V) (hφ : compatible V φ) :=
  sectionLiftSemilinear (Spec.structureSheaf S) (affineCoefficient S) (affineDifferentialSheaf S)
    (affineUniversalDifferential S) V φ hφ

abbrev twoSection {R S : Type} [CommRing R] [CommRing S] [Algebra ℂ R] [Algebra ℂ S]
    (V : (Spec (CommRingCat.of S)).Opens) (φ : R →+* functionsAt V) (hφ : compatible V φ) :=
  exteriorSectionLift (Spec.structureSheaf S) (affineCoefficient S) (affineDifferentialSheaf S)
    (affineUniversalDifferential S) V φ hφ 2

private theorem realized_wedge (φ : P →+* functionsAt U) (hφ : compatible U φ)
    (ψ : Q →+* functionsAt (reducedOpen (A := A) U)) (hψ : compatible _ ψ)
    (v : Derivation ℂ B A) (w : Derivation ℂ P Q)
    (hred : ∀ x : P, (reduction B A).app U (φ x) = ψ (algebraMap P Q x))
    (hvel : ∀ x : P, velocityOn v U (φ x) = ψ (w x))
    (r : Fin 2 → P) :
    let ω := exteriorPower.ιMulti P 2 ![KaehlerDifferential.D ℂ P (r 0), KaehlerDifferential.D ℂ P (r 1)]
    onSections (reduction B A) (evaluation v) U (twoSection U φ hφ ω) =
      oneSection (reducedOpen (A := A) U) ψ hψ (contractRestrict w ω) := by
  dsimp only
  let d := KaehlerDifferential.D ℂ P
  rw [contractRestrict_wedge, map_sub, map_smulₛₗ, map_smulₛₗ]
  simp only [Derivation.liftKaehlerDifferential_comp_D, KaehlerDifferential.map_D]
  let a := ![φ (r 0), φ (r 1)]
  have hform : twoSection U φ hφ (exteriorPower.ιMulti P 2 ![d (r 0),d (r 1)]) =
      exactWedge _ _ U a := by
    rw [twoSection, exteriorSectionLift_wedge]
    apply congrArg (wedgeSection _ _ 2 U)
    funext i
    fin_cases i
    · exact sectionLift_D _ _ _ _ _ _ _ _
    · exact sectionLift_D _ _ _ _ _ _ _ _
  rw [hform]
  refine (evaluation_exactWedge v U a).trans ?_
  simp only [a, Matrix.cons_val_zero, Matrix.cons_val_one, hred, hvel]
  change _ = _ • sectionLift _ _ _ _ _ _ _ (KaehlerDifferential.D ℂ Q _) -
    _ • sectionLift _ _ _ _ _ _ _ (KaehlerDifferential.D ℂ Q _)
  rw [sectionLift_D, sectionLift_D]

theorem realized_evaluation (φ : P →+* functionsAt U) (hφ : compatible U φ)
    (ψ : Q →+* functionsAt (reducedOpen (A := A) U)) (hψ : compatible _ ψ)
    (v : Derivation ℂ B A) (w : Derivation ℂ P Q)
    (hred : ∀ x : P, (reduction B A).app U (φ x) = ψ (algebraMap P Q x))
    (hvel : ∀ x : P, velocityOn v U (φ x) = ψ (w x))
    (ω : ⋀[P]^2 (KaehlerDifferential ℂ P)) :
    (evaluation v).val.app (op U) (twoSection U φ hφ ω) =
      oneSection (reducedOpen (A := A) U) ψ hψ (contractRestrict w ω) := by
  change onSections (reduction B A) (evaluation v) U (twoSection U φ hφ ω) = _
  let d := KaehlerDifferential.D ℂ P
  have hω : ω ∈ Submodule.span P (exteriorPower.ιMulti P 2 ''
      {m : Fin 2 → KaehlerDifferential ℂ P | Set.range m ⊆ Set.range d}) := by
    rw [exteriorPower.ιMulti_span_of_span P 2 _ (KaehlerDifferential.span_range_derivation ℂ P)]
    trivial
  induction hω using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨m,hm,rfl⟩ := hz
    choose r hr using (fun i : Fin 2 => hm (Set.mem_range_self i))
    have he : m = ![d (r 0),d (r 1)] := by
      funext i
      fin_cases i
      · exact (hr 0).symm
      · exact (hr 1).symm
    rw [he]
    exact realized_wedge U φ hφ ψ hψ v w hred hvel r
  | zero => simp only [map_zero]
  | add x y _ _ hx hy => simp only [map_add, hx, hy]
  | smul r x _ hx =>
    rw [map_smulₛₗ, map_smulₛₗ, hx, map_smul,
      ← IsScalarTower.algebraMap_smul Q r _, map_smulₛₗ, hred]

end CycleQ2CurvePairEvaluationSections
end

#print axioms CycleQ2CurvePairEvaluationSections.realized_evaluation
