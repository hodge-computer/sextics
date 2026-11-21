import Proposal.GeometricRelativeConormal
import Proposal.GeometricLiteralAbelJacobiContraction

/-!
# The intrinsic normal field inside the fixed sextic threefold

The normal field of the original infinitesimal curve kills the fixed sextic.
Exactness of the ideal conormal sequence therefore descends the field to
the defining ideal of the curve inside the quotient by that sextic.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralAbelJacobiRelativeNormal

open CycleQ2GeometricRelativeConormal

section PrincipalQuotient

variable {P : Type*} [CommRing P] {S : Type*} [AddCommGroup S] [Module P S]
  (I : Ideal P) (F : I) (ν : I.Cotangent →ₗ[P] S) (hF : ν (I.toCotangent F) = 0)

private abbrev hypersurfaceIdeal := Ideal.span ({(F : P)} : Set P)

private theorem hypersurface_le : hypersurfaceIdeal I F ≤ I :=
  (Ideal.span_singleton_le_iff_mem I).mpr F.property

include hF in
private theorem ker_quotient_le :
    LinearMap.ker (quotientConormalMap (hypersurfaceIdeal I F) I) ≤ LinearMap.ker ν := by
  rw [quotientConormalMap_kernel _ _ (hypersurface_le I F)]
  rintro _ ⟨z, rfl⟩
  obtain ⟨y, rfl⟩ := (hypersurfaceIdeal I F).toCotangent_surjective z
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton.mp y.property
  have he : (⟨y.val, hypersurface_le I F y.property⟩ : I) = a • F := by
    apply Subtype.ext
    change y.val = a * (F : P)
    simpa only [mul_comm] using ha
  rw [LinearMap.mem_ker, inclusion_toCotangent, he, map_smul, map_smul, hF, smul_zero]

/-- The descended linear map, before promoting the scalars to the quotient. -/
private def descend (hF : ν (I.toCotangent F) = 0) :
    (relativeIdeal (hypersurfaceIdeal I F) I).Cotangent →ₗ[P] S :=
  ((LinearMap.ker (quotientConormalMap (hypersurfaceIdeal I F) I)).liftQ ν
    (ker_quotient_le I F ν hF)).comp
      ((quotientConormalMap (hypersurfaceIdeal I F) I).quotKerEquivOfSurjective
        (quotientConormalMap_surjective _ _)).symm.toLinearMap

private theorem descend_quotient (x : I.Cotangent) :
    descend I F ν hF (quotientConormalMap (hypersurfaceIdeal I F) I x) = ν x := by
  simp only [descend, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearMap.quotKerEquivOfSurjective_symm_apply, Submodule.liftQ_apply]

end PrincipalQuotient

section Curve

open scoped DualNumber TensorProduct
open CycleQ2LiteralAbelJacobiMovingNormal CycleQ2LiteralAbelJacobiEquations
  CycleQ2LiteralAbelJacobiContraction

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

variable (t : Fin 3 → ℂ) (i : Fin 4)

/-- The image ideal of the embedded seed curve inside its fixed sextic chart. -/
abbrev idealOnT : Ideal (T i) := relativeIdeal (fixedIdeal i) (curveIdeal t i)

/-- This is the defining kernel of the original restriction to the seed curve. -/
theorem idealOnT_eq_ker : idealOnT t i = RingHom.ker (toCurve t i).toRingHom := by
  change Ideal.map (Ideal.Quotient.mk (fixedIdeal i))
    (Ideal.comap (Ideal.Quotient.mk (fixedIdeal i)) (RingHom.ker (toCurve t i).toRingHom)) = _
  exact Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective _

/-- The original deformation normal as a functional linear over the fixed threefold. -/
def relativeNormal [Module.Flat ℂ[ε] (B t i)] : (idealOnT t i).Cotangent →ₗ[T i] A t i :=
  let φ : (idealOnT t i).Cotangent →ₗ[P] A t i :=
    descend (curveIdeal t i) (sexticEquation t i) (chartNormal t i) (chartNormal_F t i)
  φ.extendScalarsOfSurjective
    (show Function.Surjective (algebraMap P (T i)) from Ideal.Quotient.mk_surjective)

/-- On every ambient conormal class this is the original moving-curve functional. -/
theorem relativeNormal_quotient [Module.Flat ℂ[ε] (B t i)] (x : (curveIdeal t i).Cotangent) :
    relativeNormal t i (quotientConormalMap (fixedIdeal i) (curveIdeal t i) x) =
      chartNormal t i x :=
  descend_quotient (curveIdeal t i) (sexticEquation t i) (chartNormal t i) (chartNormal_F t i) x

/-- The same cubic viewed in the defining ideal inside the fixed threefold. -/
def cubicClass : idealOnT t i :=
  ⟨cubicOnT i, Ideal.mem_map_of_mem (Ideal.Quotient.mk (fixedIdeal i)) (cubicEquation t i).property⟩

theorem relativeNormal_cubic [Module.Flat ℂ[ε] (B t i)] :
    relativeNormal t i ((idealOnT t i).toCotangent (cubicClass t i)) =
      -(seedChartMap t i (tangentL i)) :=
  (relativeNormal_quotient t i ((curveIdeal t i).toCotangent (cubicEquation t i))).trans
    (chartNormal_H t i)

/-- Contraction of the cubic conormal class is intrinsic to the fixed sextic chart. -/
theorem relativeNormal_contraction [Module.Flat ℂ[ε] (B t i)] (β : KaehlerDifferential ℂ (A t i)) :
    normalContraction (idealOnT t i) (relativeNormal t i)
      ((idealOnT t i).toCotangent (cubicClass t i) ⊗ₜ[T i] β) =
      -(seedChartMap t i (tangentL i)) • β := by
  rw [normalContraction_tmul, relativeNormal_cubic]

private theorem exists_representative_of_ideal {Q S : Type*} [CommRing Q] [CommRing S]
    [Algebra ℂ Q] [Algebra ℂ S] [Algebra Q S] [IsScalarTower ℂ Q S]
    [Algebra.FormallySmooth ℂ S] (hsurj : Function.Surjective (algebraMap Q S))
    (I : Ideal Q) (hI : I = RingHom.ker (algebraMap Q S)) (ν : I.Cotangent →ₗ[Q] S) :
    ∃ v : Derivation ℂ Q S, ∀ x : I, v x.val = ν (I.toCotangent x) := by
  subst I
  obtain ⟨v, hv⟩ := exists_normal_representative hsurj ν
  exact ⟨v, fun x => LinearMap.congr_fun hv ((RingHom.ker (algebraMap Q S)).toCotangent x)⟩

/-- On a smooth seed chart, an actual ambient vector along the curve represents
the deformation on every equation and contracts the cubic wedge with its fixed sign. -/
theorem exists_moving_representative [Module.Flat ℂ[ε] (B t i)] [Algebra.FormallySmooth ℂ (A t i)] :
    ∃ v : Derivation ℂ (T i) (A t i),
      (∀ x : idealOnT t i, v x.val = relativeNormal t i ((idealOnT t i).toCotangent x)) ∧
      ∀ β : KaehlerDifferential ℂ (T i),
        contractRestrict (P := T i) (A := A t i) v (exteriorPower.ιMulti (T i) 2
          ![KaehlerDifferential.D ℂ (T i) (cubicOnT i), β]) =
          -(seedChartMap t i (tangentL i)) • KaehlerDifferential.map ℂ ℂ (T i) (A t i) β := by
  obtain ⟨v, hv⟩ := exists_representative_of_ideal (Q := T i) (S := A t i)
    (toCurve_surjective t i) (idealOnT t i) (idealOnT_eq_ker t i) (relativeNormal t i)
  refine ⟨v, hv, fun β => ?_⟩
  rw [contractRestrict_cubicOnT, show v (cubicOnT i) = _ from
    (hv (cubicClass t i)).trans (relativeNormal_cubic t i)]

end Curve

end CycleQ2LiteralAbelJacobiRelativeNormal
end

#print axioms CycleQ2LiteralAbelJacobiRelativeNormal.relativeNormal_quotient
#print axioms CycleQ2LiteralAbelJacobiRelativeNormal.relativeNormal_contraction

#print axioms CycleQ2LiteralAbelJacobiRelativeNormal.exists_moving_representative
