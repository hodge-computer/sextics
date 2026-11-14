import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# The normal module of a closed subscheme of an actual quotient

For ideals `J ≤ I` of `P`, put `A = P/J` and `K = I A`.  The natural
conormal sequence `J/J² → I/I² → K/K² → 0` is right exact.  Its scalar
extension identifies the dual of the actual relative conormal module
with the kernel of the ambient normal map.

The comparison is induced by the literal quotient map on ideal classes.
No regular-sequence, Cartier, basis, or geometric comparison hypothesis is
used.  When the coefficient algebra is an `A`-algebra, the final comparison
uses tensor product over `A`, as required for the normal module on the
actual quotient surface.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
open scoped TensorProduct

namespace CycleQ2GeometricRelativeConormal

variable {P : Type*} [CommRing P] (J I : Ideal P)

/-- The ideal of the smaller closed subscheme in the actual quotient by `J`. -/
def relativeIdeal : Ideal (P ⧸ J) := I.map (Ideal.Quotient.mk J)

/-- The conormal map induced by the identity of the ambient ring. -/
def inclusion (hJI : J ≤ I) : J.Cotangent →ₗ[P] I.Cotangent :=
  Ideal.mapCotangent J I (AlgHom.id P P) (by
    intro x hx
    exact hJI hx)

@[simp] theorem inclusion_toCotangent (hJI : J ≤ I) (x : J) :
    inclusion J I hJI (J.toCotangent x) = I.toCotangent ⟨x, hJI x.property⟩ := rfl

/-- The quotient-induced map to the actual relative ideal cotangent. -/
def quotientConormalMap : I.Cotangent →ₗ[P] (relativeIdeal J I).Cotangent :=
  Ideal.mapCotangent I (relativeIdeal J I) (Algebra.ofId P (P ⧸ J)) (by
    change I ≤ (I.map (Ideal.Quotient.mk J)).comap (Ideal.Quotient.mk J)
    exact Ideal.le_comap_map)

@[simp] theorem quotientConormalMap_toCotangent (x : I) :
    quotientConormalMap J I (I.toCotangent x) =
      (relativeIdeal J I).toCotangent
        ⟨Ideal.Quotient.mk J x, Ideal.mem_map_of_mem _ x.property⟩ := rfl

private theorem relativeIdeal_comap :
    (relativeIdeal J I).comap (algebraMap P (P ⧸ J)) =
      RingHom.ker (algebraMap P (P ⧸ J)) ⊔ I := by
  change (I.map (Ideal.Quotient.mk J)).comap (Ideal.Quotient.mk J) =
    RingHom.ker (Ideal.Quotient.mk J) ⊔ I
  rw [Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective, sup_comm]

theorem quotientConormalMap_surjective : Function.Surjective (quotientConormalMap J I) := by
  exact Ideal.mapCotangent_surjective_of_comap_eq
    (show Function.Surjective (algebraMap P (P ⧸ J)) from Ideal.Quotient.mk_surjective)
    (relativeIdeal_comap J I)

/-- Exactness at the ambient curve conormal module, with the actual quotient map. -/
theorem quotientConormalMap_kernel (hJI : J ≤ I) :
    LinearMap.ker (quotientConormalMap J I) = LinearMap.range (inclusion J I hJI) := by
  have hk := Ideal.mapCotangent_ker_of_surjective
    (show Function.Surjective (algebraMap P (P ⧸ J)) from Ideal.Quotient.mk_surjective)
    (relativeIdeal_comap J I)
  change LinearMap.ker (quotientConormalMap J I) = _ at hk
  rw [hk]
  change (Submodule.comap I.subtype
      ((RingHom.ker (Ideal.Quotient.mk J)) ⊓ I)).map I.toCotangent = _
  rw [Ideal.mk_ker, inf_eq_left.mpr hJI]
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨J.toCotangent ⟨x, hx⟩, rfl⟩
  · rintro ⟨y, rfl⟩
    obtain ⟨y, rfl⟩ := J.toCotangent_surjective y
    exact ⟨⟨y, hJI y.property⟩, y.property, rfl⟩

theorem conormal_exact (hJI : J ≤ I) :
    Function.Exact (inclusion J I hJI) (quotientConormalMap J I) :=
  LinearMap.exact_iff.mpr (quotientConormalMap_kernel J I hJI)

section ScalarExtension

variable (S : Type*) [CommRing S] [Algebra P S]

/-- Right exactness remains true after scalar extension to any coefficient algebra. -/
theorem baseChange_exact (hJI : J ≤ I) :
    Function.Exact ((inclusion J I hJI).baseChange S)
      ((quotientConormalMap J I).baseChange S) :=
  lTensor_exact S (conormal_exact J I hJI)
    (quotientConormalMap_surjective J I)

theorem baseChange_quotient_surjective :
    Function.Surjective ((quotientConormalMap J I).baseChange S) :=
  LinearMap.baseChange_surjective S (quotientConormalMap_surjective J I)

theorem normal_range_eq_kernel (hJI : J ≤ I) :
    LinearMap.range ((quotientConormalMap J I).baseChange S).dualMap =
      LinearMap.ker ((inclusion J I hJI).baseChange S).dualMap := by
  rw [LinearMap.range_dualMap_eq_dualAnnihilator_ker_of_surjective _
    (baseChange_quotient_surjective J I S),
    (baseChange_exact J I S hJI).linearMap_ker_eq,
    LinearMap.ker_dualMap_eq_dualAnnihilator_range]

/-- The relative conormal dual is canonically the kernel of the ambient normal map. -/
def normalEquiv (hJI : J ≤ I) :
    (S ⊗[P] (relativeIdeal J I).Cotangent →ₗ[S] S) ≃ₗ[S]
      LinearMap.ker ((inclusion J I hJI).baseChange S).dualMap :=
  (LinearEquiv.ofInjective ((quotientConormalMap J I).baseChange S).dualMap
    (LinearMap.dualMap_injective_of_surjective
      (baseChange_quotient_surjective J I S))).trans
    (LinearEquiv.ofEq _ _ (normal_range_eq_kernel J I S hJI))

@[simp] theorem normalEquiv_apply (hJI : J ≤ I)
    (φ : S ⊗[P] (relativeIdeal J I).Cotangent →ₗ[S] S)
    (z : S ⊗[P] I.Cotangent) :
    (normalEquiv J I S hJI φ).val z = φ (((quotientConormalMap J I).baseChange S) z) := rfl

/-- The inverse comparison is determined on the actual ideal representatives. -/
theorem normalEquiv_symm_toCotangent (hJI : J ≤ I)
    (φ : LinearMap.ker ((inclusion J I hJI).baseChange S).dualMap)
    (s : S) (x : I) :
    (normalEquiv J I S hJI).symm φ
        (s ⊗ₜ[P] (relativeIdeal J I).toCotangent
          ⟨Ideal.Quotient.mk J x, Ideal.mem_map_of_mem _ x.property⟩) =
      φ.val (s ⊗ₜ[P] I.toCotangent x) := by
  have h := congrArg (fun ψ : LinearMap.ker ((inclusion J I hJI).baseChange S).dualMap =>
      ψ.val (s ⊗ₜ[P] I.toCotangent x)) ((normalEquiv J I S hJI).apply_symm_apply φ)
  simpa only [normalEquiv_apply, LinearMap.baseChange_tmul,
    quotientConormalMap_toCotangent] using h

section QuotientScalars

variable [Algebra (P ⧸ J) S] [IsScalarTower P (P ⧸ J) S]

/-- Tensoring the actual relative ideal cotangent over the quotient or the ambient ring
gives the same module, because the ambient-to-surface map is surjective. -/
def relativeTensorEquiv :
    S ⊗[P ⧸ J] (relativeIdeal J I).Cotangent ≃ₗ[S]
      S ⊗[P] (relativeIdeal J I).Cotangent := by
  letI : TensorProduct.CompatibleSMul P (P ⧸ J) S (relativeIdeal J I).Cotangent :=
    TensorProduct.CompatibleSMul.of_algebraMap_surjective S (relativeIdeal J I).Cotangent
      (show Function.Surjective (algebraMap P (P ⧸ J)) from Ideal.Quotient.mk_surjective)
  exact TensorProduct.equivOfCompatibleSMul P (P ⧸ J) S S (relativeIdeal J I).Cotangent

@[simp] theorem relativeTensorEquiv_tmul (s : S) (x : (relativeIdeal J I).Cotangent) :
    relativeTensorEquiv J I S (s ⊗ₜ[P ⧸ J] x) = s ⊗ₜ[P] x := rfl

/-- The normal module over the actual quotient surface, with its canonical ambient-kernel
identification.  In applications `S` is an actual curve chart algebra. -/
def relativeNormalEquiv (hJI : J ≤ I) :
    (S ⊗[P ⧸ J] (relativeIdeal J I).Cotangent →ₗ[S] S) ≃ₗ[S]
      LinearMap.ker ((inclusion J I hJI).baseChange S).dualMap :=
  (relativeTensorEquiv J I S).symm.dualMap.trans (normalEquiv J I S hJI)

theorem relativeNormalEquiv_symm_toCotangent (hJI : J ≤ I)
    (φ : LinearMap.ker ((inclusion J I hJI).baseChange S).dualMap)
    (s : S) (x : I) :
    (relativeNormalEquiv J I S hJI).symm φ
        (s ⊗ₜ[P ⧸ J] (relativeIdeal J I).toCotangent
          ⟨Ideal.Quotient.mk J x, Ideal.mem_map_of_mem _ x.property⟩) =
      φ.val (s ⊗ₜ[P] I.toCotangent x) := by
  change (normalEquiv J I S hJI).symm φ
    (relativeTensorEquiv J I S
      (s ⊗ₜ[P ⧸ J] (relativeIdeal J I).toCotangent
        ⟨Ideal.Quotient.mk J x, Ideal.mem_map_of_mem _ x.property⟩)) = _
  rw [relativeTensorEquiv_tmul, normalEquiv_symm_toCotangent]

end QuotientScalars
end ScalarExtension
end CycleQ2GeometricRelativeConormal
