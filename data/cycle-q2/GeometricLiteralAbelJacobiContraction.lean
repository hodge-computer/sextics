import Proposal.GeometricLiteralAbelJacobiMovingNormal
import Mathlib.LinearAlgebra.ExteriorPower.Basic
import Mathlib.RingTheory.Smooth.Basic

/-!
# Contraction of a conormal two-form on the moving curve chart

The exterior-square construction pairs an ambient derivation along the curve
with the first slot of a two-form and restricts the remaining slot to the curve.
On a wedge starting with the differential of a defining equation it depends
only on the normal coefficient of that equation.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralAbelJacobiContraction

open scoped TensorProduct

section Contraction

variable {P A : Type*} [CommRing P] [CommRing A] [Algebra ℂ P] [Algebra ℂ A]
    [Algebra P A] [IsScalarTower ℂ P A]

local notation "ΩP" => KaehlerDifferential ℂ P
local notation "ΩA" => KaehlerDifferential ℂ A

/-- Inserting the vector in the first slot and restricting the second slot to the curve. -/
def contractRestrict (v : Derivation ℂ P A) : (⋀[P]^2 ΩP) →ₗ[P] ΩA :=
  exteriorPower.alternatingMapLinearEquiv
    { toFun := fun m => v.liftKaehlerDifferential (m 0) • KaehlerDifferential.map ℂ ℂ P A (m 1) -
          v.liftKaehlerDifferential (m 1) • KaehlerDifferential.map ℂ ℂ P A (m 0)
      map_update_add' := by
        intro _ m i x y
        fin_cases i <;> simp [Function.update, add_smul, smul_add] <;> abel
      map_update_smul' := by
        intro _ m i r x
        fin_cases i <;> simp [Function.update, smul_sub, smul_assoc, smul_comm (v.liftKaehlerDifferential _) (_ : P)]
      map_eq_zero_of_eq' := by
        intro m i j he hne
        fin_cases i <;> fin_cases j <;> simp_all }

theorem contractRestrict_wedge (v : Derivation ℂ P A) (α β : ΩP) :
    contractRestrict v (exteriorPower.ιMulti P 2 ![α, β]) =
      v.liftKaehlerDifferential α • KaehlerDifferential.map ℂ ℂ P A β -
        v.liftKaehlerDifferential β • KaehlerDifferential.map ℂ ℂ P A α := by
  rw [contractRestrict, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  rfl

theorem contractRestrict_conormal (v : Derivation ℂ P A) (h : P)
    (hh : algebraMap P A h = 0) (β : ΩP) :
    contractRestrict v (exteriorPower.ιMulti P 2 ![KaehlerDifferential.D ℂ P h, β]) =
      v h • KaehlerDifferential.map ℂ ℂ P A β := by
  rw [contractRestrict_wedge, Derivation.liftKaehlerDifferential_comp_D,
    KaehlerDifferential.map_D, hh, map_zero, smul_zero, sub_zero]

/-- A normal functional evaluates the conormal slot without choosing an ambient lift. -/
def normalContraction (I : Ideal P) (ν : I.Cotangent →ₗ[P] A) :
    I.Cotangent ⊗[P] ΩA →ₗ[P] ΩA :=
  TensorProduct.lift ((Algebra.lsmul P P ΩA).toLinearMap.comp ν)

@[simp] theorem normalContraction_tmul (I : Ideal P) (ν : I.Cotangent →ₗ[P] A)
    (e : I.Cotangent) (β : ΩA) :
    normalContraction I ν (e ⊗ₜ[P] β) = ν e • β := rfl

/-- The normal component of a vector along a closed curve. Leibniz kills
products in the square of its defining ideal. -/
def normalComponent (v : Derivation ℂ P A) (I : Ideal P)
    (hI : I ≤ RingHom.ker (algebraMap P A)) : I.Cotangent →ₗ[P] A := by
  let n : I →ₗ[P] A :=
    { toFun := fun e => v e.val
      map_add' := fun x y => v.map_add x.val y.val
      map_smul' := by
        intro r e
        change v (r * e.val) = r • v e.val
        rw [v.leibniz, Algebra.smul_def e.val, show algebraMap P A e.val = 0 from hI e.property,
          zero_mul, add_zero] }
  refine (I • ⊤ : Submodule P I).liftQ n (Submodule.smul_le.mpr ?_)
  intro r hr e _
  change n (r • e) = 0
  rw [map_smul, Algebra.smul_def r, show algebraMap P A r = 0 from hI hr, zero_mul]

omit [IsScalarTower ℂ P A] in
@[simp] theorem normalComponent_equation (v : Derivation ℂ P A) (I : Ideal P)
    (hI : I ≤ RingHom.ker (algebraMap P A)) (e : I) :
    normalComponent v I hI (I.toCotangent e) = v e.val := rfl

/-- A representative of a normal functional gives the same contraction on
every defining equation; the result is expressed on the quotient conormal module. -/
theorem normalContraction_eq_contractRestrict (v : Derivation ℂ P A)
    (I : Ideal P) (hI : I ≤ RingHom.ker (algebraMap P A)) (e : I) (β : ΩP) :
    normalContraction I (normalComponent v I hI) (I.toCotangent e ⊗ₜ[P] KaehlerDifferential.map ℂ ℂ P A β) =
      contractRestrict v (exteriorPower.ιMulti P 2 ![KaehlerDifferential.D ℂ P (e : P), β]) := by
  rw [normalContraction_tmul, normalComponent_equation, contractRestrict_conormal v e (hI e.property)]

/-- Two ambient representatives give the same one-form if their normal
components agree on the class of the defining equation. -/
theorem contractRestrict_eq_of_normalComponent (v w : Derivation ℂ P A)
    (I : Ideal P) (hI : I ≤ RingHom.ker (algebraMap P A)) (e : I) (β : ΩP)
    (he : normalComponent v I hI (I.toCotangent e) =
      normalComponent w I hI (I.toCotangent e)) :
    contractRestrict v (exteriorPower.ιMulti P 2 ![KaehlerDifferential.D ℂ P (e : P), β]) =
      contractRestrict w (exteriorPower.ιMulti P 2 ![KaehlerDifferential.D ℂ P (e : P), β]) := by
  rw [contractRestrict_conormal v e (hI e.property), contractRestrict_conormal w e (hI e.property)]
  exact congrArg (fun a : A => a • KaehlerDifferential.map ℂ ℂ P A β) he

/-- A normal field on a smooth affine curve has an actual ambient representative.
Smoothness splits the first infinitesimal neighborhood of the closed curve. -/
theorem exists_normal_representative [Algebra.FormallySmooth ℂ A]
    (hsurj : Function.Surjective (algebraMap P A))
    (ν : (RingHom.ker (algebraMap P A)).Cotangent →ₗ[P] A) :
    ∃ v : Derivation ℂ P A,
      normalComponent v (RingHom.ker (algebraMap P A)) le_rfl = ν := by
  let f := IsScalarTower.toAlgHom ℂ P A
  have hs : Function.Surjective f.kerSquareLift :=
    Ideal.Quotient.lift_surjective_of_surjective _ _ hsurj
  have hz : RingHom.ker f.kerSquareLift.toRingHom ^ 2 = ⊥ := by
    rw [AlgHom.ker_kerSquareLift, Ideal.cotangentIdeal_square]
  let g := Algebra.FormallySmooth.liftOfSurjective (AlgHom.id ℂ A) f.kerSquareLift hs ⟨2, hz⟩
  obtain ⟨l, hl⟩ := (retractionKerCotangentToTensorEquivSection (R := ℂ) hsurj).symm
    ⟨g, Algebra.FormallySmooth.comp_liftOfSurjective _ _ _ _⟩
  refine ⟨(ν ∘ₗ l ∘ₗ TensorProduct.mk P A ΩP 1).compDer (KaehlerDifferential.D ℂ P), ?_⟩
  apply LinearMap.ext
  intro e
  obtain ⟨x, rfl⟩ := (RingHom.ker (algebraMap P A)).toCotangent_surjective e
  exact congrArg ν (LinearMap.congr_fun hl ((RingHom.ker (algebraMap P A)).toCotangent x))

end Contraction

section Chart

open scoped DualNumber
open CycleQ2IncidencePolynomialJacobianBinding CycleQ2IncidenceDehomogenizedChart
  CycleQ2IncidenceUniversalChart CycleQ2RelativeCurveChart
  CycleQ2LiteralAbelJacobiMovingNormal CycleQ2LiteralAbelJacobiEquations

attribute [local instance] CycleQ2IncidenceSeedFiber.seedAlgebra
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderAlgebra
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderModule
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderSMul
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderTower


variable (t : Fin 3 → ℂ) (i : Fin 4)

/-- The affine chart of the fixed weighted sextic threefold. -/
abbrev fixedIdeal (i : Fin 4) : Ideal P := Ideal.span {seedF i}
abbrev T (i : Fin 4) := P ⧸ fixedIdeal i

local instance fixedCommRing : CommRing (T i) := inferInstance
local instance seedChartCommRing : CommRing (A t i) := inferInstance
attribute [local instance] CycleQ2LiteralAbelJacobiMovingNormal.closedAlgebra

def toSeedChart : P →ₐ[ℂ] A t i :=
  (Ideal.Quotient.mkₐ ℂ (affineSectionIdeal (seedPoint (57 : ℂ) Complex.I) t i)).comp
    (Ideal.Quotient.mkₐ ℂ (chartIdeal (dehomogenizedEquations (seedPoint (57 : ℂ) Complex.I) i)))

local instance seedChartTower : IsScalarTower ℂ P (A t i) :=
  IsScalarTower.of_algebraMap_eq (R := ℂ) (S := P) (A := A t i)
    fun z => ((toSeedChart t i).commutes z).symm

theorem fixedIdeal_le_curveIdeal : fixedIdeal i ≤ curveIdeal t i :=
  (Ideal.span_singleton_le_iff_mem (curveIdeal t i)).mpr (sexticEquation t i).property

/-- Restriction of functions on the fixed threefold to the actual section curve. -/
def toCurve : T i →ₐ[ℂ] A t i :=
  Ideal.Quotient.liftₐ (fixedIdeal i) (toSeedChart t i) fun _ hx =>
    fixedIdeal_le_curveIdeal t i hx

@[simp] theorem toCurve_mk (x : P) : toCurve t i (Ideal.Quotient.mk _ x) =
    seedChartMap t i x := rfl

local instance fixedAlgebra : Algebra (T i) (A t i) := (toCurve t i).toRingHom.toAlgebra

local instance fixedTower : IsScalarTower ℂ (T i) (A t i) :=
  IsScalarTower.of_algebraMap_eq (R := ℂ) (S := T i) (A := A t i)
    fun z => ((toCurve t i).commutes z).symm

local instance fixedSeedTower : IsScalarTower P (T i) (A t i) :=
  IsScalarTower.of_algebraMap_eq (R := P) (S := T i) (A := A t i) fun _ => rfl

theorem toCurve_surjective : Function.Surjective (toCurve t i) := by
  intro a
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective b
  exact ⟨Ideal.Quotient.mk _ p, rfl⟩

abbrev cubicOnT (i : Fin 4) : T i := Ideal.Quotient.mk _ (seedH i)

theorem cubicOnT_zero : algebraMap (T i) (A t i) (cubicOnT i) = 0 :=
  (cubicEquation t i).property

/-- The form lives in the exterior square of the Kähler differentials of the
fixed threefold; contraction and restriction leave only the normal coefficient. -/
theorem contractRestrict_cubicOnT (v : Derivation ℂ (T i) (A t i))
    (β : KaehlerDifferential ℂ (T i)) :
    contractRestrict (P := T i) (A := A t i) v (exteriorPower.ιMulti (T i) 2
      ![KaehlerDifferential.D ℂ (T i) (cubicOnT i), β]) =
      v (cubicOnT i) • KaehlerDifferential.map ℂ ℂ (T i) (A t i) β :=
  contractRestrict_conormal (P := T i) (A := A t i) v _ (cubicOnT_zero t i) β

/-- The normal functional from the original flat deformation contracts the
cubic conormal class to minus the retained incidence cubic times the one-form. -/
theorem movingNormal_contraction [Module.Flat ℂ[ε] (B t i)]
    (β : KaehlerDifferential ℂ (A t i)) :
    normalContraction (curveIdeal t i) (chartNormal t i)
      ((curveIdeal t i).toCotangent (cubicEquation t i) ⊗ₜ[P] β) =
        -(seedChartMap t i (tangentL i)) • β := by
  rw [normalContraction_tmul, chartNormal_H]

end Chart

end CycleQ2LiteralAbelJacobiContraction

end

#print axioms CycleQ2LiteralAbelJacobiContraction.exists_normal_representative
#print axioms CycleQ2LiteralAbelJacobiContraction.normalContraction_eq_contractRestrict
#print axioms CycleQ2LiteralAbelJacobiContraction.contractRestrict_cubicOnT
#print axioms CycleQ2LiteralAbelJacobiContraction.movingNormal_contraction
