import Proposal.GeometricLiteralAbelJacobiContraction
import Proposal.GeometricExteriorSheaf

/-!
# Evaluating the pullback of a two-form along a curve motion

For an ambient chart mapping to a family chart, the pullback of a two-form
followed by contraction against a parameter lift agrees with contraction
against the induced vector along the ambient chart. When a fixed equation
restricts to minus epsilon times a coefficient, this evaluates its conormal
wedge as minus that coefficient times the restricted differential.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2CurveCylinderPullback

open CycleQ2GeometricExteriorSheaf CycleQ2LiteralAbelJacobiContraction

variable {P B A : Type} [CommRing P] [CommRing B] [CommRing A]
    [Algebra ℂ P] [Algebra ℂ B] [Algebra ℂ A]
    [Algebra P B] [Algebra B A] [Algebra P A]
    [IsScalarTower ℂ P B] [IsScalarTower ℂ B A]
    [IsScalarTower ℂ P A] [IsScalarTower P B A]

private def differentialPullback (P B : Type) [CommRing P] [CommRing B]
    [Algebra ℂ P] [Algebra ℂ B] [Algebra P B] [IsScalarTower ℂ P B] :
    KaehlerDifferential ℂ P →ₛₗ[algebraMap P B] KaehlerDifferential ℂ B where
  toFun := KaehlerDifferential.map ℂ ℂ P B
  map_add' := map_add _
  map_smul' r x := (map_smul (KaehlerDifferential.map ℂ ℂ P B) r x).trans
    (IsScalarTower.algebraMap_smul B r _).symm

/-- Pullback of ambient two-forms to the family chart. -/
def pullTwo (P B : Type) [CommRing P] [CommRing B]
    [Algebra ℂ P] [Algebra ℂ B] [Algebra P B] [IsScalarTower ℂ P B] :=
  exteriorMap (algebraMap P B) (differentialPullback P B) 2

private theorem differential_tower (α : KaehlerDifferential ℂ P) :
    KaehlerDifferential.map ℂ ℂ B A (KaehlerDifferential.map ℂ ℂ P B α) =
      KaehlerDifferential.map ℂ ℂ P A α := by
  let f := ((KaehlerDifferential.map ℂ ℂ B A).restrictScalars P).comp
    (KaehlerDifferential.map ℂ ℂ P B)
  have h : f = KaehlerDifferential.map ℂ ℂ P A := by
    apply Derivation.liftKaehlerDifferential_unique
    ext x
    change KaehlerDifferential.map ℂ ℂ B A
      (KaehlerDifferential.map ℂ ℂ P B (KaehlerDifferential.D ℂ P x)) = _
    simp [IsScalarTower.algebraMap_apply P B A]
  exact LinearMap.congr_fun h α

private theorem tangent_tower (v : Derivation ℂ B A) (α : KaehlerDifferential ℂ P) :
    v.liftKaehlerDifferential (KaehlerDifferential.map ℂ ℂ P B α) =
      (v.compAlgebraMap P).liftKaehlerDifferential α := by
  let f := (v.liftKaehlerDifferential.restrictScalars P).comp (KaehlerDifferential.map ℂ ℂ P B)
  have h : f = (v.compAlgebraMap P).liftKaehlerDifferential := by
    apply Derivation.liftKaehlerDifferential_unique
    ext x
    change v.liftKaehlerDifferential (KaehlerDifferential.map ℂ ℂ P B (KaehlerDifferential.D ℂ P x)) =
      (v.compAlgebraMap P).liftKaehlerDifferential (KaehlerDifferential.D ℂ P x)
    simp only [KaehlerDifferential.map_D, Derivation.liftKaehlerDifferential_comp_D]
    rfl
  exact LinearMap.congr_fun h α

/-- The mixed component of the pulled back two-form is the contraction with
the chart's actual induced ambient tangent. -/
theorem contract_pullTwo (v : Derivation ℂ B A) (ω : ⋀[P]^2 (KaehlerDifferential ℂ P)) :
    contractRestrict v (pullTwo P B ω) = contractRestrict (v.compAlgebraMap P) ω := by
  have hω : ω ∈ Submodule.span P (Set.range (exteriorPower.ιMulti P 2)) := by
    rw [exteriorPower.ιMulti_span]
    trivial
  induction hω using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨m, rfl⟩ := hx
      rw [pullTwo, exteriorMap_wedge]
      have hm : m = ![m 0, m 1] := by ext i; fin_cases i <;> rfl
      rw [hm]
      change contractRestrict v (exteriorPower.ιMulti B 2
        ![KaehlerDifferential.map ℂ ℂ P B (m 0), KaehlerDifferential.map ℂ ℂ P B (m 1)]) = _
      rw [contractRestrict_wedge, contractRestrict_wedge, tangent_tower, tangent_tower,
        differential_tower, differential_tower]
  | zero => simp
  | add x y _ _ hx hy => simp only [map_add, hx, hy]
  | smul r x _ hx =>
      rw [map_smulₛₗ, map_smul, map_smul, hx, IsScalarTower.algebraMap_smul]

/-- A parameter derivative evaluating to one on epsilon extracts the actual
negative coefficient of a moving equation when the two-form starts with its
conormal differential. -/
theorem contract_pullTwo_moving_equation (v : Derivation ℂ B A) (e : B)
    (he : algebraMap B A e = 0) (hv : v e = 1) (h : P) (l : B)
    (hh : algebraMap P B h = -(e * l)) (β : KaehlerDifferential ℂ P) :
    contractRestrict v (pullTwo P B (exteriorPower.ιMulti P 2 ![KaehlerDifferential.D ℂ P h, β])) =
      -(algebraMap B A l) • KaehlerDifferential.map ℂ ℂ P A β := by
  have hzero : algebraMap P A h = 0 := by
    rw [IsScalarTower.algebraMap_apply P B A, hh, map_neg, map_mul, he, zero_mul, neg_zero]
  rw [contract_pullTwo, contractRestrict_conormal _ h hzero]
  change v (algebraMap P B h) • _ = _
  rw [hh, map_neg, v.leibniz, Algebra.smul_def, Algebra.smul_def, he, hv]
  simp

end CycleQ2CurveCylinderPullback
end

#print axioms CycleQ2CurveCylinderPullback.contract_pullTwo
#print axioms CycleQ2CurveCylinderPullback.contract_pullTwo_moving_equation
