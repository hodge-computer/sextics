import Proposal.GeometricIsoDifferentialSections
import Proposal.GeometricHodgeCotangentOneFormPrimitives
import Proposal.GeometricLiteralThreefoldFirstDifferential
import Proposal.GeometricFiniteCechOrbitPullback
import Proposal.GeometricExteriorPullComposition

/-!
# One-form primitives on the original fixed threefold

The normalized-model primitive is transported by the canonical scheme
differential map. Each remaining logarithmic term is the logarithm of an
actual unit of the original section ring. The global first differential
therefore removes it on every common subopen of the original cover.

Prepared for fqlx with OpenAI ChatGPT assistance; see solution.md.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 3000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2LiteralThreefoldOneFormPrimitives
open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open CycleQ2GeometricHodgeThreefold CycleQ2GeometricHodgeThreefoldIncidence
open CycleQ2LiteralThreefoldFirstDifferential
open CycleQ2LiteralAmbientCharts (fixedOpen)
open CycleQ2GeometricAffineChartSections (schemeCoefficient coefficientOn_app)
open CycleQ2GeometricDifferentialSheaf (coefficientOn universalDifferential)
open CycleQ2GeometricSectionDifferentials (toSheaf toSheaf_D)
open CycleQ2InjectiveCech (Sections)
open CycleQ2FiniteInjectiveCech (IsOneCocycle edgeValue)
open CycleQ2FiniteCechDescent (Zero)
open CycleQ2GeometricSheafLocalIso (res res_comp res_self)

abbrev NormalForms := CycleQ2HodgeCotangentOneFormPrimitives.Forms
abbrev normalCoeff := schemeCoefficient (toBase literalEval)

abbrev coefficient_compatible := CycleQ2IsoDifferentialSections.compatible_over literalIso
  (toBase literalEval) structural literalIso_overComplex

theorem pre_le {W V : X.Opens} (h : W ≤ V) : literalIso.hom ⁻¹ᵁ W ≤ literalIso.hom ⁻¹ᵁ V :=
  fun _ hx => h hx

abbrev pull := CycleQ2IsoDifferentialSections.pull (X := threefold literalEval) (Y := X)
  literalIso normalCoeff coeff coefficient_compatible

theorem pull_bijective (W : X.Opens) : Function.Bijective (pull W) :=
  CycleQ2IsoDifferentialSections.pull_bijective (X := threefold literalEval) (Y := X)
    literalIso normalCoeff coeff coefficient_compatible W

theorem pull_restrict {W V : X.Opens} (h : V ≤ W) (s : Sections One W) :
    pull V (res One h s) = res NormalForms (pre_le h) (pull W s) :=
  CycleQ2IsoDifferentialSections.pull_restrict (X := threefold literalEval) (Y := X)
    literalIso normalCoeff coeff coefficient_compatible h s

def pullMap : CycleQ2LiteralThreefoldFirstDifferential.One ⟶
    CycleQ2FiniteCechOrbitPullback.push literalIso.hom.base NormalForms :=
  CycleQ2IsoDifferentialSections.pullMap literalIso normalCoeff coeff coefficient_compatible

abbrev preCover := CycleQ2FiniteCechOrbitPullback.cover literalIso.hom.base fixedOpen

theorem preCover_eq : preCover = CycleQ2HodgeCotangentOneFormPrimitives.cover :=
  funext literalIso_preimage

theorem normalized_primitive (V : Fin 4 → (threefold literalEval).Opens)
    (hV : V = CycleQ2HodgeCotangentOneFormPrimitives.cover)
    (u : CycleQ2FiniteInjectiveCech.One NormalForms V) (hu : IsOneCocycle NormalForms V u) :
    ∃ c : ℂ, ∃ p : Zero NormalForms V,
      ∀ i k W (hi : W ≤ V i) (hk : W ≤ V k),
        res NormalForms hk (p k) - res NormalForms hi (p i) =
          edgeValue NormalForms V u i k W hi hk -
            CycleQ2HodgeCotangentOneFormPrimitives.scalarLog literalEval c i k W
              (hi.trans_eq (congrFun hV i)) (hk.trans_eq (congrFun hV k)) := by
  subst V
  exact CycleQ2HodgeCotangentOneFormPrimitives.one_primitive u hu

def ringEquiv (W : X.Opens) : Γ(X,W) ≃+* Γ(threefold literalEval,literalIso.hom ⁻¹ᵁ W) :=
  CycleQ2IsoDifferentialSections.ringEquiv literalIso W

def logUnit (i k : Fin 4) (W : X.Opens) (hi : W ≤ fixedOpen i) (hk : W ≤ fixedOpen k) : Γ(X,W)ˣ :=
  CycleQ2IsoDifferentialSections.inverseUnit literalIso W
    (CycleQ2HodgeTwistRatios.transition literalEval i k (literalIso.hom ⁻¹ᵁ W)
      ((pre_le hi).trans_eq (literalIso_preimage i))
      ((pre_le hk).trans_eq (literalIso_preimage k)))

section Normalized
attribute [local instance] CycleQ2HodgeCotangentAtlasForms.complexOn

theorem normalized_scaledLog_eq (φ : CycleQ2GenericSexticGradient.CoeffRing →+* ℂ)
    (i k : Fin 4) (W : (threefold φ).Opens)
    (hi : W ≤ CycleQ2HodgeTwistRatios.U φ i) (hk : W ≤ CycleQ2HodgeTwistRatios.U φ k)
    (a : Γ(threefold φ,W)) :
    (CycleQ2HodgeCotangentOneFormPrimitives.scaledLog φ i k W hi hk a :
      (CycleQ2IsoDifferentialSections.target (X := threefold φ) (schemeCoefficient (toBase φ))).val.obj (op W)) =
      CycleQ2IsoDifferentialSections.scaledLog (X := threefold φ) (schemeCoefficient (toBase φ)) W a
        (CycleQ2HodgeTwistRatios.transition φ i k W hi hk) := by
  unfold CycleQ2HodgeCotangentOneFormPrimitives.scaledLog CycleQ2IsoDifferentialSections.scaledLog
  refine ((toSheaf (threefold φ).sheaf (schemeCoefficient (toBase φ)) W).map_smul a
    (CycleQ2HodgeCotangentEulerDlog.logarithmic φ i k W hi hk)).trans ?_
  apply congrArg (fun z => a • z)
  exact (toSheaf (threefold φ).sheaf (schemeCoefficient (toBase φ)) W).map_smul
    ((CycleQ2HodgeTwistRatios.transition φ i k W hi hk)⁻¹ : Γ(threefold φ,W)ˣ).val
    (KaehlerDifferential.D ℂ Γ(threefold φ,W) (CycleQ2HodgeTwistRatios.transition φ i k W hi hk : Γ(threefold φ,W)))

theorem normalized_scalarLog_eq (φ : CycleQ2GenericSexticGradient.CoeffRing →+* ℂ)
    (c : ℂ) (i k : Fin 4) (W : (threefold φ).Opens)
    (hi : W ≤ CycleQ2HodgeTwistRatios.U φ i) (hk : W ≤ CycleQ2HodgeTwistRatios.U φ k) :
    (CycleQ2HodgeCotangentOneFormPrimitives.scalarLog φ c i k W hi hk :
      (CycleQ2IsoDifferentialSections.target (X := threefold φ) (schemeCoefficient (toBase φ))).val.obj (op W)) =
      CycleQ2IsoDifferentialSections.scalarLog (X := threefold φ) (schemeCoefficient (toBase φ)) W c
        (CycleQ2HodgeTwistRatios.transition φ i k W hi hk) :=
  normalized_scaledLog_eq φ i k W hi hk (coefficientOn (threefold φ).sheaf (schemeCoefficient (toBase φ)) W c)

end Normalized

theorem original_scaledLog_eq (W : X.Opens) (a : Γ(X,W)) (v : Γ(X,W)ˣ) :
    scaledLog W a v = CycleQ2IsoDifferentialSections.scaledLog (X := X) coeff W a v := rfl

theorem original_scalarLog_eq (W : X.Opens) (c : ℂ) (v : Γ(X,W)ˣ) :
    scalarLog W c v = CycleQ2IsoDifferentialSections.scalarLog (X := X) coeff W c v :=
  original_scaledLog_eq W (coefficientOn X.sheaf coeff W c) v

theorem pull_scalarLog (c : ℂ) (i k : Fin 4) (W : X.Opens)
    (hi : W ≤ fixedOpen i) (hk : W ≤ fixedOpen k) :
    pull W (scalarLog W c (logUnit i k W hi hk)) =
      CycleQ2HodgeCotangentOneFormPrimitives.scalarLog literalEval c i k (literalIso.hom ⁻¹ᵁ W)
        ((pre_le hi).trans_eq (literalIso_preimage i))
        ((pre_le hk).trans_eq (literalIso_preimage k)) := by
  have h0 := congrArg (pull W) (original_scalarLog_eq W c (logUnit i k W hi hk))
  dsimp only [logUnit] at h0
  have h := CycleQ2IsoDifferentialSections.pull_scalarLog_inverseUnit (X := threefold literalEval) (Y := X)
    literalIso normalCoeff coeff
    coefficient_compatible W c
    (CycleQ2HodgeTwistRatios.transition literalEval i k (literalIso.hom ⁻¹ᵁ W)
      ((pre_le hi).trans_eq (literalIso_preimage i))
      ((pre_le hk).trans_eq (literalIso_preimage k)))
  have h2 := normalized_scalarLog_eq literalEval c i k
    (literalIso.hom ⁻¹ᵁ W) ((pre_le hi).trans_eq (literalIso_preimage i))
    ((pre_le hk).trans_eq (literalIso_preimage k))
  have hh := h.trans h2.symm
  exact h0.trans hh

/-- The primitive uses the original four opens; its remainder is an actual
canonical scalar times the logarithm of an original section-ring unit. -/
theorem one_primitive (u : CycleQ2FiniteInjectiveCech.One One fixedOpen)
    (hu : IsOneCocycle One fixedOpen u) :
    ∃ c : ℂ, ∃ p : Zero One fixedOpen,
      ∀ i k W (hi : W ≤ fixedOpen i) (hk : W ≤ fixedOpen k),
        res One hk (p k) - res One hi (p i) = edgeValue One fixedOpen u i k W hi hk -
          scalarLog W c (logUnit i k W hi hk) := by
  let n := CycleQ2FiniteCechOrbitPullback.pullOne literalIso.hom.base pullMap fixedOpen u
  have hn := CycleQ2FiniteCechOrbitPullback.pullOne_closed literalIso.hom.base pullMap fixedOpen u hu
  obtain ⟨c,q,hq⟩ := normalized_primitive preCover preCover_eq n hn
  choose p hp using fun i => (pull_bijective (fixedOpen i)).surjective (q i)
  refine ⟨c,p,fun i k W hi hk => ?_⟩
  apply (pull_bijective W).injective
  rw [map_sub,map_sub,pull_scalarLog,pull_restrict,pull_restrict,hp,hp]
  dsimp only [n,preCover,pullMap] at hq
  have he' := CycleQ2IsoDifferentialSections.pull_edge (X := threefold literalEval) (Y := X)
    literalIso normalCoeff coeff coefficient_compatible
    fixedOpen u i k W hi hk
  exact (hq i k (literalIso.hom ⁻¹ᵁ W) (pre_le hi) (pre_le hk)).trans
    (congrArg (fun z => z - CycleQ2HodgeCotangentOneFormPrimitives.scalarLog literalEval c i k
      (literalIso.hom ⁻¹ᵁ W) ((pre_le hi).trans_eq (literalIso_preimage i))
      ((pre_le hk).trans_eq (literalIso_preimage k))) he')

/-- The actual global first differential turns every closed one-form
cochain into the boundary of actual two-form sections on the same cover. -/
theorem differential_primitive (u : CycleQ2FiniteInjectiveCech.One One fixedOpen)
    (hu : IsOneCocycle One fixedOpen u) :
    ∃ p : Zero Two fixedOpen,
      ∀ i k W (hi : W ≤ fixedOpen i) (hk : W ≤ fixedOpen k),
        res Two hk (p k) - res Two hi (p i) =
          differential.hom.app (op W) (edgeValue One fixedOpen u i k W hi hk) := by
  obtain ⟨c,p,hp⟩ := one_primitive u hu
  refine ⟨fun i => differential.hom.app (op (fixedOpen i)) (p i),fun i k W hi hk => ?_⟩
  have h := congrArg (differential.hom.app (op W)) (hp i k W hi hk)
  rw [map_sub,map_sub,scalar_log_closed,sub_zero] at h
  exact (congrArg₂ (· - ·)
    (CycleQ2CechTwoToDerived.app_res differential hk (p k)).symm
    (CycleQ2CechTwoToDerived.app_res differential hi (p i)).symm).trans h

end CycleQ2LiteralThreefoldOneFormPrimitives
end
#print axioms CycleQ2LiteralThreefoldOneFormPrimitives.pull_scalarLog
#print axioms CycleQ2LiteralThreefoldOneFormPrimitives.one_primitive
#print axioms CycleQ2LiteralThreefoldOneFormPrimitives.differential_primitive
