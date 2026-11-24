import Proposal.GeometricLiteralThreefoldCartan
import Proposal.GeometricLiteralThreefoldDeformedVolume
import Mathlib.RingTheory.TensorProduct.IsBaseChangePi
import Mathlib.RingTheory.Kaehler.TensorProduct

/-! Constant and infinitesimal components of a relative Kähler three-form
on a dual-number algebra with an exact cotangent frame.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2LiteralThreefoldDeformedFrame
open Module CycleQ2LiteralThreefoldChartLift CycleQ2GeometricExteriorSheaf
  CycleQ2LiteralThreefoldDeformedVolume CycleQ2ExteriorTopBaseChange
  CycleQ2LiteralThreefoldCartan
open scoped TensorProduct

attribute [local instance] CycleQ2LiteralThreefoldDeformedVolume.dualAlgebra
  CycleQ2LiteralThreefoldDeformedVolume.dualTower
variable {A : Type} [CommRing A] [Algebra ℂ A]

/-- Extending the coefficient ring of the dual numbers extends both components. -/
theorem jet_pushout : Algebra.IsPushout ℂ Dual A (Jet A) := by
  apply Algebra.IsPushout.symm
  constructor
  exact IsBaseChange.prodMap (Algebra.linearMap ℂ A) (Algebra.linearMap ℂ A)
    (IsBaseChange.linearMap ℂ A) (IsBaseChange.linearMap ℂ A)

local instance : Algebra.IsPushout ℂ Dual A (Jet A) := jet_pushout

def baseDifferential : KaehlerDifferential ℂ A →ₛₗ[algebraMap A (Jet A)]
    KaehlerDifferential Dual (Jet A) where
  toFun := KaehlerDifferential.map ℂ Dual A (Jet A)
  map_add' := map_add _
  map_smul' a m := (map_smul _ a m).trans (IsScalarTower.algebraMap_smul (Jet A) a _).symm

def baseForms (n : ℕ) : CycleQ2LiteralThreefoldCartan.Forms A n →ₛₗ[algebraMap A (Jet A)]
    JetForms A n := exteriorMap _ baseDifferential n

def jetBasis (b : Basis (Fin 3) A (OneForms A)) :
    Basis (Fin 3) (Jet A) (KaehlerDifferential Dual (Jet A)) :=
  (b.baseChange (Jet A)).map (KaehlerDifferential.tensorKaehlerEquiv ℂ Dual A (Jet A))

variable (b : Basis (Fin 3) A (OneForms A)) (u : Fin 3 → A)
    (hu : ∀ j, b j = KaehlerDifferential.D ℂ A (u j))

include hu in
theorem jetBasis_apply (j : Fin 3) :
    jetBasis b j = KaehlerDifferential.D Dual (Jet A) (algebraMap A (Jet A) (u j)) := by
  simp only [jetBasis, Basis.map_apply, Basis.baseChange_apply, hu,
    KaehlerDifferential.tensorKaehlerEquiv_tmul_D]
  exact one_smul (Jet A) (KaehlerDifferential.D Dual (Jet A) (algebraMap A (Jet A) (u j)))

include hu in
theorem base_orderedVolume : baseForms 3 (orderedVolume b) =
    exteriorPower.ιMulti (Jet A) 3 (jetBasis b) := by
  rw [orderedVolume, baseForms, exteriorMap_wedge]
  apply congrArg (exteriorPower.ιMulti (Jet A) 3)
  funext j
  rw [jetBasis_apply b u hu, hu]
  exact KaehlerDifferential.map_D ℂ Dual A (Jet A) _

include hu in
theorem evaluate_jetBasis :
    evaluateJetVolume b (exteriorPower.ιMulti (Jet A) 3 (jetBasis b)) = 1 := by
  let x : Fin 3 → Jet A := fun j => algebraMap A (Jet A) (u j)
  have hmat : jetJacobian b x = 1 := by
    apply Matrix.ext
    intro j k
    apply TrivSqZeroExt.ext
    · change b.repr (KaehlerDifferential.D ℂ A (u k)) j = ((1 : Matrix (Fin 3) (Fin 3) (Jet A)) j k).fst
      rw [← hu, Basis.repr_self, Matrix.one_apply]
      by_cases h : j = k <;> simp [h]
    · change coordinateDerivation b j 0 = ((1 : Matrix (Fin 3) (Fin 3) (Jet A)) j k).snd
      rw [map_zero, Matrix.one_apply]
      split <;> rfl
  have h := evaluate_liftedVolume b 1 x
  rw [hmat, Matrix.det_one, one_mul, liftedVolume, one_smul] at h
  simpa only [x, ← jetBasis_apply b u hu] using h

include hu in
theorem evaluate_injective : Function.Injective (evaluateJetVolume b) := by
  let B := jetBasis b
  intro a c h
  have he (z : JetForms A 3) : evaluateJetVolume b z = topCoordinate B z := by
    conv_lhs => rw [← topCoordinate_smul_wedge B z]
    rw [map_smul, evaluate_jetBasis b u hu, smul_eq_mul, mul_one]
  exact (topCoordinateEquiv B).injective ((he a).symm.trans (h.trans (he c)))

include hu in
theorem evaluate_base (w : CycleQ2LiteralThreefoldCartan.Forms A 3) :
    evaluateJetVolume b (baseForms 3 w) = algebraMap A (Jet A) (topCoordinate b w) := by
  conv_lhs => rw [← topCoordinate_smul_wedge b w]
  change evaluateJetVolume b (baseForms 3 (topCoordinate b w • orderedVolume b)) = _
  rw [map_smulₛₗ, map_smul, base_orderedVolume b u hu, evaluate_jetBasis b u hu, smul_eq_mul, mul_one]

private theorem reduce_D (a : Jet A) :
    reduceDifferential (KaehlerDifferential.D Dual (Jet A) a) = KaehlerDifferential.D ℂ A a.fst := by
  let : Algebra Dual ℂ := TrivSqZeroExt.algebraBase ℂ ℂ
  let : Algebra (Jet A) A := TrivSqZeroExt.algebraBase A A
  let : Algebra Dual A :=
    ((algebraMap ℂ A).comp (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom).toAlgebra
  let : IsScalarTower Dual ℂ A := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : SMul Dual (Jet A) := (dualAlgebra (S := A)).toSMul
  let : IsScalarTower Dual (Jet A) A :=
    IsScalarTower.of_algebraMap_eq (R := Dual) (S := Jet A) (A := A) fun _ => rfl
  exact KaehlerDifferential.map_D Dual ℂ (Jet A) A _

include hu in
theorem reduce_jetBasis : reduceForms 3 (exteriorPower.ιMulti (Jet A) 3 (jetBasis b)) = orderedVolume b := by
  rw [reduceForms, exteriorMap_wedge, orderedVolume]
  apply congrArg (exteriorPower.ιMulti A 3)
  funext j
  rw [jetBasis_apply b u hu, hu]
  exact reduce_D _

/-- Extract the infinitesimal coefficient as an actual three-form. -/
def firstVariation (w : JetForms A 3) : CycleQ2LiteralThreefoldCartan.Forms A 3 :=
  (evaluateJetVolume b w).snd • orderedVolume b

include hu in
theorem jet_expansion (w : JetForms A 3) :
    evaluateJetVolume b w • exteriorPower.ιMulti (Jet A) 3 (jetBasis b) = w := by
  apply evaluate_injective b u hu
  rw [map_smul, evaluate_jetBasis b u hu, smul_eq_mul, mul_one]

include hu in
theorem reduce_eq (w : JetForms A 3) :
    reduceForms 3 w = (evaluateJetVolume b w).fst • orderedVolume b := by
  conv_lhs => rw [← jet_expansion b u hu w]
  rw [map_smulₛₗ, reduce_jetBasis b u hu]
  rfl

include hu in
/-- Every relative top form has its original reduction as constant term, and
a unique ordinary three-form as the coefficient of the infinitesimal parameter. -/
theorem decompose (w : JetForms A 3) :
    baseForms 3 (reduceForms 3 w) + epsilon A • baseForms 3 (firstVariation b w) = w := by
  let c := evaluateJetVolume b w
  have hc : algebraMap A (Jet A) c.fst + epsilon A * algebraMap A (Jet A) c.snd = c := by
    apply TrivSqZeroExt.ext
    · change c.fst + 0 * c.snd = c.fst
      simp
    · change 0 + (0 * 0 + 1 * c.snd) = c.snd
      simp
  rw [reduce_eq b u hu, firstVariation, map_smulₛₗ, map_smulₛₗ, base_orderedVolume b u hu,
    smul_smul, ← add_smul]
  exact (congrArg (fun a : Jet A => a • exteriorPower.ιMulti (Jet A) 3 (jetBasis b)) hc).trans
    (jet_expansion b u hu w)

include hu in
theorem epsilon_base_injective : Function.Injective
    (fun w : CycleQ2LiteralThreefoldCartan.Forms A 3 => epsilon A • baseForms 3 w) := by
  intro w z h
  apply (topCoordinateEquiv b).injective
  change topCoordinate b w = topCoordinate b z
  have e := congrArg (evaluateJetVolume b) h
  change evaluateJetVolume b (epsilon A • baseForms 3 w) =
    evaluateJetVolume b (epsilon A • baseForms 3 z) at e
  rw [map_smul, map_smul, evaluate_base b u hu, evaluate_base b u hu] at e
  have es := congrArg TrivSqZeroExt.snd e
  change 0 * 0 + 1 * topCoordinate b w = 0 * 0 + 1 * topCoordinate b z at es
  simpa only [zero_mul, zero_add, one_mul] using es

include hu in
theorem firstVariation_unique (w : JetForms A 3) (a : CycleQ2LiteralThreefoldCartan.Forms A 3)
    (h : baseForms 3 (reduceForms 3 w) + epsilon A • baseForms 3 a = w) :
    firstVariation b w = a :=
  epsilon_base_injective b u hu (add_left_cancel ((decompose b u hu w).trans h.symm))

include hu in
theorem firstVariation_independent (b' : Basis (Fin 3) A (OneForms A))
    (v : Fin 3 → A) (hv : ∀ j, b' j = KaehlerDifferential.D ℂ A (v j)) (w : JetForms A 3) :
    firstVariation b w = firstVariation b' w :=
  firstVariation_unique b u hu w _ (decompose b' v hv w)

include hu in
theorem reduce_base (w : CycleQ2LiteralThreefoldCartan.Forms A 3) :
    reduceForms 3 (baseForms 3 w) = w := by
  rw [reduce_eq b u hu, evaluate_base b u hu]
  exact topCoordinate_smul_wedge b w

section Restriction

open CycleQ2LiteralThreefoldLiftTransition CycleQ2ExteriorSectionNaturality CycleQ2GeometricAffineOverlap
variable {B : Type} [CommRing B] [Algebra ℂ B] (g : A →ₐ[ℂ] B)

private theorem base_D (a : A) : baseDifferential (KaehlerDifferential.D ℂ A a) =
    KaehlerDifferential.D Dual (Jet A) (algebraMap A (Jet A) a) :=
  KaehlerDifferential.map_D ℂ Dual A (Jet A) a

private theorem relMap_D (a : Jet A) :
    mapDifferential g (KaehlerDifferential.D Dual (Jet A) a) =
      KaehlerDifferential.D Dual (Jet B) (jetMap g a) := by
  let : Algebra Dual Dual := Algebra.id Dual
  let : SMul Dual Dual := (Algebra.id Dual).toSMul
  let : IsScalarTower Dual Dual (Jet B) :=
    IsScalarTower.of_algebraMap_eq (R := Dual) (S := Dual) (A := Jet B) fun _ => rfl
  let := (relativeJetMap g).toRingHom.toAlgebra
  let : IsScalarTower Dual (Jet A) (Jet B) := IsScalarTower.of_algHom (relativeJetMap g)
  exact KaehlerDifferential.map_D Dual Dual (Jet A) (Jet B) a

private theorem jetMap_inl (a : A) :
    jetMap g (algebraMap A (Jet A) a) = algebraMap B (Jet B) (g a) := by
  apply TrivSqZeroExt.ext
  · rfl
  · exact map_zero g

private theorem map_base_exact (z : Fin 3 → A) :
    let w := exteriorPower.ιMulti A 3 (fun j => KaehlerDifferential.D ℂ A (z j))
    mapForms g 3 (baseForms 3 w) = baseForms 3 (exteriorDifferentialMap g 3 w) := by
  dsimp only
  simp only [baseForms, mapForms, exteriorMap_wedge, exteriorDifferentialMap_wedge,
    differentialMap_D, base_D, relMap_D, jetMap_inl]

include hu in
theorem baseForms_map (w : CycleQ2LiteralThreefoldCartan.Forms A 3) :
    mapForms g 3 (baseForms 3 w) = baseForms 3 (exteriorDifferentialMap g 3 w) := by
  have hw : mapForms g 3 (baseForms 3 (orderedVolume b)) =
      baseForms 3 (exteriorDifferentialMap g 3 (orderedVolume b)) := by
    simpa only [orderedVolume, funext hu] using map_base_exact g u
  conv_lhs => rw [← topCoordinate_smul_wedge b w]
  conv_rhs => rw [← topCoordinate_smul_wedge b w]
  simp only [map_smulₛₗ]
  change jetMap g (algebraMap A (Jet A) (topCoordinate b w)) •
      mapForms g 3 (baseForms 3 (orderedVolume b)) = _
  rw [jetMap_inl, hw]
  rfl

variable (b' : Basis (Fin 3) B (OneForms B)) (v : Fin 3 → B)
    (hv : ∀ j, b' j = KaehlerDifferential.D ℂ B (v j))

include hu hv in
/-- Pullback to another exact chart commutes with the intrinsic infinitesimal
component, including changes to a different system of local parameters. -/
theorem firstVariation_map (w : JetForms A 3) :
    firstVariation b' (mapForms g 3 w) = exteriorDifferentialMap g 3 (firstVariation b w) := by
  have e := congrArg (mapForms g 3) (decompose b u hu w)
  change mapForms g 3 (baseForms 3 (reduceForms 3 w) + epsilon A • baseForms 3 (firstVariation b w)) =
    mapForms g 3 w at e
  rw [map_add, map_smulₛₗ, baseForms_map b u hu, baseForms_map b u hu] at e
  have hε : (relativeJetMap g).toRingHom (epsilon A) = epsilon B := by
    apply TrivSqZeroExt.ext
    · exact map_zero g
    · exact map_one g
  rw [hε] at e
  have h₀ : reduceForms 3 (mapForms g 3 w) = exteriorDifferentialMap g 3 (reduceForms 3 w) := by
    rw [← e, map_add, map_smulₛₗ, reduce_base b' v hv]
    change _ + (0 : B) • _ = _
    rw [zero_smul, add_zero]
  apply firstVariation_unique b' v hv
  rw [h₀]
  exact e

end Restriction

end CycleQ2LiteralThreefoldDeformedFrame
end

#print axioms CycleQ2LiteralThreefoldDeformedFrame.decompose
#print axioms CycleQ2LiteralThreefoldDeformedFrame.firstVariation_independent
#print axioms CycleQ2LiteralThreefoldDeformedFrame.firstVariation_map
