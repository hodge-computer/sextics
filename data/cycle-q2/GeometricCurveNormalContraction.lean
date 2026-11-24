import Proposal.GeometricLiteralAbelJacobiRelativeNormal
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent

/-!
# Contracting ambient two-forms along a curve

For a quotient chart the difference of two ambient derivations with the same
normal component descends to a derivation of the curve. If its second exterior
power of differentials vanishes, contracting any ambient two-form with this
difference gives zero after restriction.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace CycleQ2CurveNormalContraction

open CycleQ2LiteralAbelJacobiContraction

variable {P A : Type*} [CommRing P] [CommRing A] [Algebra ℂ P] [Algebra ℂ A]
    [Algebra P A] [IsScalarTower ℂ P A]

local notation "ΩP" => KaehlerDifferential ℂ P
local notation "ΩA" => KaehlerDifferential ℂ A

/-- A derivation along a quotient with zero normal part descends to the quotient ring. -/
theorem exists_tangent_derivation {M : Type*} [AddCommGroup M] [Module ℂ M]
    [Module P M] [Module A M] [IsScalarTower P A M] (d : Derivation ℂ P M)
    (hs : Function.Surjective (algebraMap P A))
    (hk : ∀ r ∈ RingHom.ker (algebraMap P A), d r = 0) :
    ∃ e : Derivation ℂ A M, ∀ x : P, e (algebraMap P A x) = d x := by
  let g : A → M := fun a => d (hs a).choose
  have hg (x : P) : g (algebraMap P A x) = d x := by
    apply sub_eq_zero.mp
    change d (hs (algebraMap P A x)).choose - d x = 0
    rw [← map_sub]
    apply hk
    rw [RingHom.mem_ker, map_sub, (hs _).choose_spec, sub_self]
  let e : Derivation ℂ A M :=
    { toFun := g
      map_add' := by
        rintro a b
        obtain ⟨x, rfl⟩ := hs a
        obtain ⟨y, rfl⟩ := hs b
        rw [← map_add, hg, map_add, hg, hg]
      map_smul' := by
        intro c a
        obtain ⟨x, rfl⟩ := hs a
        change g (c • algebraMap P A x) = c • g (algebraMap P A x)
        rw [← show algebraMap P A (c • x) = c • algebraMap P A x from
          (IsScalarTower.toAlgHom ℂ P A).toLinearMap.map_smul c x, hg, hg]
        exact d.toLinearMap.map_smul c x
      map_one_eq_zero' := by
        change g 1 = 0
        rw [← map_one (algebraMap P A), hg, d.map_one_eq_zero]
      leibniz' := by
        intro a b
        change g (a * b) = a • g b + b • g a
        obtain ⟨x, rfl⟩ := hs a
        obtain ⟨y, rfl⟩ := hs b
        rw [← map_mul, hg, d.leibniz, hg, hg]
        simp only [IsScalarTower.algebraMap_smul] }
  exact ⟨e, hg⟩

private theorem self_differential_map (α : ΩA) :
    KaehlerDifferential.map ℂ ℂ A A α = α := by
  have he : KaehlerDifferential.map ℂ ℂ A A = LinearMap.id := by
    apply Derivation.liftKaehlerDifferential_unique
    ext x
    change KaehlerDifferential.map ℂ ℂ A A (KaehlerDifferential.D ℂ A x) = _
    rw [KaehlerDifferential.map_D]
    rfl
  rw [he, LinearMap.id_apply]

/-- An ambient two-form gives the same restricted one-form for any two lifts of the
same normal functional on a quotient curve chart with vanishing second exterior power. -/
theorem contractRestrict_eq_of_normal_eq
    (v w : Derivation ℂ P A) (hs : Function.Surjective (algebraMap P A))
    [Subsingleton (⋀[A]^2 ΩA)]
    (hn : normalComponent v (RingHom.ker (algebraMap P A)) le_rfl =
      normalComponent w (RingHom.ker (algebraMap P A)) le_rfl) :
    contractRestrict v = contractRestrict w := by
  obtain ⟨e, he⟩ := exists_tangent_derivation (v - w) hs (by
    intro r hr
    apply sub_eq_zero.mpr
    exact DFunLike.congr_fun hn ((RingHom.ker (algebraMap P A)).toCotangent ⟨r, hr⟩))
  let pull := KaehlerDifferential.map ℂ ℂ P A
  have hl : v.liftKaehlerDifferential - w.liftKaehlerDifferential =
      (e.liftKaehlerDifferential.restrictScalars P).comp pull := by
    apply Derivation.liftKaehlerDifferential_unique
    ext x
    change v.liftKaehlerDifferential (KaehlerDifferential.D ℂ P x) -
      w.liftKaehlerDifferential (KaehlerDifferential.D ℂ P x) =
      e.liftKaehlerDifferential (KaehlerDifferential.map ℂ ℂ P A (KaehlerDifferential.D ℂ P x))
    rw [KaehlerDifferential.map_D]
    simp only [Derivation.liftKaehlerDifferential_comp_D]
    exact (he x).symm
  have hm (α : ΩP) : v.liftKaehlerDifferential α - w.liftKaehlerDifferential α =
      e.liftKaehlerDifferential (pull α) := DFunLike.congr_fun hl α
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro m
  change contractRestrict v (exteriorPower.ιMulti P 2 m) =
    contractRestrict w (exteriorPower.ιMulti P 2 m)
  have hvec : m = ![m 0, m 1] := by ext i; fin_cases i <;> rfl
  rw [hvec, contractRestrict_wedge, contractRestrict_wedge]
  have hz := Subsingleton.elim (exteriorPower.ιMulti A 2 ![pull (m 0), pull (m 1)]) 0
  have ht := congrArg (contractRestrict e) hz
  rw [contractRestrict_wedge, map_zero, self_differential_map, self_differential_map] at ht
  change v.liftKaehlerDifferential (m 0) • pull (m 1) -
    v.liftKaehlerDifferential (m 1) • pull (m 0) =
    w.liftKaehlerDifferential (m 0) • pull (m 1) - w.liftKaehlerDifferential (m 1) • pull (m 0)
  rw [← hm, ← hm, sub_smul, sub_smul] at ht
  abel_nf at ht ⊢
  grind

/-- The hypothesis on the exterior square holds on any chart where the cotangent
module is generated by a single one-form. -/
theorem exteriorTwo_subsingleton_of_one_generator (g : ΩA)
    (hg : Submodule.span A {g} = ⊤) : Subsingleton (⋀[A]^2 ΩA) := by
  let v : Fin 1 → ΩA := fun _ => g
  have hv : Submodule.span A (Set.range v) = ⊤ := by simpa [v] using hg
  let : IsEmpty (Set.powersetCard (Fin 1) 2) :=
    ⟨fun s => by have hc := Finset.card_le_univ (s : Finset (Fin 1)); simp at hc⟩
  have hbot : (⊥ : Submodule A (⋀[A]^2 ΩA)) = ⊤ := by
    simpa only [Set.range_eq_empty, Submodule.span_empty] using
      (exteriorPower.ιMulti_family_span_of_span A (n := 2) hv)
  exact (subsingleton_iff_forall_eq 0).2 fun z => by
    simpa only [Submodule.mem_bot] using
      (show z ∈ (⊥ : Submodule A (⋀[A]^2 ΩA)) from hbot.symm ▸ Submodule.mem_top)

/-- In particular the exterior-square hypothesis is automatic on every
standard smooth curve chart over the complex numbers. -/
theorem exteriorTwo_subsingleton_of_standardSmoothCurve
    [Algebra.IsStandardSmoothOfRelativeDimension 1 ℂ A] : Subsingleton (⋀[A]^2 ΩA) := by
  rcases subsingleton_or_nontrivial A with _ | _
  · exact Module.subsingleton A _
  have : Algebra.IsStandardSmooth ℂ A := Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth 1
  have hr := Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential
    (R := ℂ) (S := A) 1
  have hd : Module.finrank A ΩA = 1 := by simp [Module.finrank, hr]
  obtain ⟨g, _, hg⟩ := (finrank_eq_one_iff' (K := A) (V := ΩA)).mp hd
  apply exteriorTwo_subsingleton_of_one_generator g (top_unique fun x _ => ?_)
  exact Submodule.mem_span_singleton.mpr (hg x)

section Literal

open scoped DualNumber
open CycleQ2LiteralAbelJacobiMovingNormal CycleQ2LiteralAbelJacobiEquations
  CycleQ2LiteralAbelJacobiRelativeNormal

local notation "CurveRing" => CycleQ2LiteralAbelJacobiMovingNormal.A

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

/-- On a smooth one-dimensional seed chart with its flat motion, the moving normal
defines a unique contraction of all two-forms of the fixed threefold. It sends
the cubic conormal wedge to the negative retained tangent times the restricted form. -/
theorem moving_normal_contraction_unique (t : Fin 3 → ℂ) (i : Fin 4)
    [Module.Flat ℂ[ε] (B t i)] [Algebra.FormallySmooth ℂ (CurveRing t i)]
    [Subsingleton (⋀[CurveRing t i]^2
      (KaehlerDifferential ℂ (CurveRing t i)))] :
    ∃! f : (⋀[T i]^2 (KaehlerDifferential ℂ (T i))) →ₗ[T i]
        KaehlerDifferential ℂ (CurveRing t i),
      (∀ v : Derivation ℂ (T i) (CurveRing t i),
        (∀ x : idealOnT t i, v x.val = relativeNormal t i ((idealOnT t i).toCotangent x)) →
          f = contractRestrict v) ∧
      ∀ β : KaehlerDifferential ℂ (T i),
        f (exteriorPower.ιMulti (T i) 2 ![KaehlerDifferential.D ℂ (T i) (cubicOnT i), β]) =
          -(seedChartMap t i (tangentL i)) •
            KaehlerDifferential.map ℂ ℂ (T i) (CurveRing t i) β := by
  obtain ⟨v, hv, hw⟩ := exists_moving_representative t i
  refine ⟨contractRestrict v, ⟨?_, hw⟩, fun f hf => hf.1 v hv⟩
  intro w hw
  apply contractRestrict_eq_of_normal_eq v w (toCurve_surjective t i)
  apply LinearMap.ext
  intro u
  obtain ⟨x, rfl⟩ := (RingHom.ker (toCurve t i).toRingHom).toCotangent_surjective u
  change v x.val = w x.val
  let y : idealOnT t i := ⟨x.val, (idealOnT_eq_ker t i).symm ▸ x.property⟩
  exact (hv y).trans (hw y).symm

end Literal

end CycleQ2CurveNormalContraction

end

#print axioms CycleQ2CurveNormalContraction.contractRestrict_eq_of_normal_eq
#print axioms CycleQ2CurveNormalContraction.moving_normal_contraction_unique
