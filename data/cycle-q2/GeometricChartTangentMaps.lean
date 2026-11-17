import Proposal.GeometricAffineDerivations
import Proposal.GeometricDifferentialChartTransport
import Proposal.GeometricIntrinsicNormal

/-!
# Genuine local tangent maps from arbitrary affine derivations

An arbitrary complex derivation transports through the actual affine
chart to all subopens. The proved restricted universal property lifts it
to a local morphism from the original differential sheaf to the original
structure sheaf. Its value on each original affine differential is the
given derivation's Kähler contraction.

Prepared for fqlx with OpenAI ChatGPT assistance; see solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2GeometricChartTangentMaps

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
  CycleQ2GeometricDifferentialSheaf CycleQ2GeometricDifferentialRestriction
  CycleQ2GeometricAffineChartSections CycleQ2GeometricDifferentialChartTransport
  CycleQ2GeometricSheafKaehlerMap CycleQ2GeometricIntrinsicNormal

variable {X : Scheme.{0}} {U : X.Opens} {A : Type} [CommRing A] [Algebra ℂ A]
  (e : U.toScheme ≅ Spec (CommRingCat.of A))
  (f : X ⟶ Spec (CommRingCat.of ℂ))
  (h : e.inv ≫ U.ι ≫ f = Spec.map (CommRingCat.ofHom (algebraMap ℂ A)))

def chartDerivation (δ : Derivation ℂ A A) :
    ChartDerivation f (ChartStructureModule (X := X) (U := U)) :=
  CycleQ2GeometricDerivationTransport.structureDerivation
    (chartSourceRingSheaf X U) (Spec.structureSheaf A) (chartOpensEquiv e)
    (chartSectionsIso e) (overCoefficient X.sheaf (schemeCoefficient f) U)
    (coefficientMap (Spec.structureSheaf A)
      (CycleQ2GeometricAffineDifferentialSheaf.affineCoefficient A))
    (fun V c => chartSectionsIso_coefficient e f h V.unop c)
    (CycleQ2GeometricAffineDerivations.structureSheafDerivation δ)

theorem chartDerivation_section (δ : Derivation ℂ A A) (V : Over U) (a : A) :
    (chartDerivation e f h δ).d (X := op V) (chartSection e V a) =
      chartSection e V (δ a) := by
  change (chartSectionIso e V).inv
    (CycleQ2GeometricAffineDerivations.sectionDerivative δ ((chartOpensEquiv e).functor.obj V)
      ((chartSectionIso e V).hom ((chartSectionIso e V).inv
        (algebraMap A (CycleQ2GeometricAffineDerivations.AffineSections
          ((chartOpensEquiv e).functor.obj V)) a)))) = _
  rw [Iso.inv_hom_id_apply, CycleQ2GeometricAffineDerivations.sectionDerivative_algebraMap]
  rfl

def chartLinearMap (δ : Derivation ℂ A A) :
    ChartDifferentialModule f ⟶ ChartStructureModule (X := X) (U := U) :=
  restrictedLift X.sheaf (schemeCoefficient f) U (ChartStructureModule (X := X) (U := U))
    (chartDerivation e f h δ)

theorem chartLinearMap_D (δ : Derivation ℂ A A) (V : Over U) (a : Γ(X,V.left)) :
    (chartLinearMap e f h δ).val.app (op V)
      ((universalDifferential X.sheaf (schemeCoefficient f)).d (X := op V.left) a) =
        (chartDerivation e f h δ).d (X := op V) a :=
  PresheafOfModules.Derivation.congr_d
    (restrictedLift_fac X.sheaf (schemeCoefficient f) U
      (ChartStructureModule (X := X) (U := U)) (chartDerivation e f h δ)) a

def tangentSection (δ : Derivation ℂ A A) :
    LocalLinearHom X.sheaf (differentialSheaf X.sheaf (schemeCoefficient f))
      (SheafOfModules.unit (ringSheaf X.sheaf)) U :=
  ⟨(PresheafOfModules.toPresheaf ((ringSheaf X.sheaf).over U).obj).map
      (chartLinearMap e f h δ).val,
    fun V a m => ((chartLinearMap e f h δ).val.app (op V)).hom.map_smul a m⟩

theorem tangentSection_on_form (δ : Derivation ℂ A A) (ω : KaehlerDifferential ℂ A) :
    localLinearHomEvaluate X.sheaf (differentialSheaf X.sheaf (schemeCoefficient f))
      (SheafOfModules.unit (ringSheaf X.sheaf)) U (tangentSection e f h δ)
      (sectionLift X.sheaf (schemeCoefficient f)
        (differentialSheaf X.sheaf (schemeCoefficient f))
        (universalDifferential X.sheaf (schemeCoefficient f)) U
        (chartSection e (chartTop U)) (chartSection_complex e f h (chartTop U)) ω) =
      chartSection e (chartTop U) (δ.liftKaehlerDifferential ω) := by
  have hω : ω ∈ Submodule.span A (Set.range (KaehlerDifferential.D ℂ A)) := by
    rw [KaehlerDifferential.span_range_derivation]
    trivial
  induction hω using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      rw [sectionLift_D]
      change (chartLinearMap e f h δ).val.app (op (chartTop U))
        ((universalDifferential X.sheaf (schemeCoefficient f)).d _) = _
      exact (chartLinearMap_D e f h δ (chartTop U) _).trans
        ((chartDerivation_section e f h δ (chartTop U) a).trans
          (congrArg (chartSection e (chartTop U)) (δ.liftKaehlerDifferential_comp_D a).symm))
  | zero => simp only [map_zero]
  | add x y _ _ hx hy => simp only [map_add, hx, hy]
  | smul a x _ hx =>
      rw [sectionLift_smul, map_smul, hx, map_smul]
      change chartSection e (chartTop U) a * chartSection e (chartTop U) _ =
        chartSection e (chartTop U) (a * _)
      exact (map_mul _ _ _).symm

end CycleQ2GeometricChartTangentMaps

end

#print axioms CycleQ2GeometricChartTangentMaps.tangentSection
#print axioms CycleQ2GeometricChartTangentMaps.tangentSection_on_form
