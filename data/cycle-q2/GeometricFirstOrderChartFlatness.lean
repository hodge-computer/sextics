import Proposal.GeometricFirstOrderSurface
import Proposal.GeometricFirstOrderChartReduction
import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Actual first-order affine charts and their ambient flatness

An affine chart of the original parameterized scheme is pulled back to
the actual first-order scheme. Pasting the two genuine pullback squares
identifies this chart with the spectrum of its original coordinate ring
tensored along the retained firstOrderMap. Both projections are explicit.
Its open image is exactly the preimage of the original chart image.

Applied to the original incidence surface, the existing smooth
first-order surface proves flatness of every actual first-order affine
chart over the dual numbers. No flatness of the original chart over the
full incidence parameter algebra is assumed or inferred.

Prepared for fqlx with OpenAI ChatGPT assistance, following Ben Diamond
and the geometric strategy credited in solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2FirstOrderChartFlatness

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct
open CycleQ2IncidenceEtaleParameter CycleQ2IncidenceFirstOrder
  CycleQ2FirstOrderTensorReduction CycleQ2FirstOrderChartReduction
  CycleQ2FirstOrderSurface CycleQ2IncidenceDehomogenizedChart
  CycleQ2GeometricIncidenceProj

attribute [local instance] CycleQ2FirstOrderTensorReduction.parameterFirstOrderAlgebra
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderModule
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderSMul
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderTower
  CycleQ2FirstOrderTensorReduction.firstOrderTensorCommRing

local instance incidenceChartCommRing (i : Fin 4) :
    CommRing (DehomogenizedRing incidencePoint i) := inferInstance

local instance firstOrderTensorModule (B : Type) [CommRing B] [Algebra ParameterAlgebra B] :
    Module (DualNumber ℂ) (FirstOrderTensor B) :=
  (inferInstance : Algebra (DualNumber ℂ) (FirstOrderTensor B)).toModule

local instance firstOrderTensorSMul (B : Type) [CommRing B] [Algebra ParameterAlgebra B] :
    SMul (DualNumber ℂ) (FirstOrderTensor B) :=
  (inferInstance : Algebra (DualNumber ℂ) (FirstOrderTensor B)).toSMul

section ActualAffineBaseChange

variable (B : Type) [CommRing B] [Algebra ParameterAlgebra B]
variable {X Xε : Scheme}
variable (f : X ⟶ Spec (CommRingCat.of ParameterAlgebra))
  (p : Xε ⟶ X) (q : Xε ⟶ Spec (CommRingCat.of (DualNumber ℂ)))
  (h : IsPullback p q f firstOrderParameterPoint)
  (e : Spec (CommRingCat.of B) ⟶ X)
  (he : e ≫ f = Spec.map (CommRingCat.ofHom (algebraMap ParameterAlgebra B)))

/-- The original affine chart pulled back to the actual first-order scheme. -/
abbrev ChartPullback := pullback e p

include h he in
/-- The outer square identifies the same source as an affine base change. -/
theorem chartPullback_isPullback :
    IsPullback (pullback.snd e p ≫ q) (pullback.fst e p)
      firstOrderParameterPoint
      (Spec.map (CommRingCat.ofHom (algebraMap ParameterAlgebra B))) := by
  have hh := ((IsPullback.of_hasPullback e p).paste_vert h).flip
  rw [he] at hh
  exact hh

/-- The actual chart pullback is the spectrum of the retained tensor algebra. -/
def chartPullbackIso :
    ChartPullback B p e ≅ Spec (CommRingCat.of (FirstOrderTensor B)) :=
  (chartPullback_isPullback B f p q h e he).isoPullback ≪≫
    pullbackSpecIso ParameterAlgebra (DualNumber ℂ) B

def tensorChartToBase :
    Spec (CommRingCat.of (FirstOrderTensor B)) ⟶
      Spec (CommRingCat.of (DualNumber ℂ)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (DualNumber ℂ) (FirstOrderTensor B)))

def tensorChartToOriginal :
    Spec (CommRingCat.of (FirstOrderTensor B)) ⟶ Spec (CommRingCat.of B) :=
  Spec.map (CommRingCat.ofHom
    (Algebra.TensorProduct.includeRight
      (R := ParameterAlgebra) (A := DualNumber ℂ) (B := B)).toRingHom)

@[reassoc] theorem chartPullbackIso_inv_base :
    (chartPullbackIso B f p q h e he).inv ≫ (pullback.snd e p ≫ q) =
      tensorChartToBase B := by
  change ((pullbackSpecIso ParameterAlgebra (DualNumber ℂ) B).inv ≫
      (chartPullback_isPullback B f p q h e he).isoPullback.inv) ≫
        (pullback.snd e p ≫ q) = _
  rw [Category.assoc, IsPullback.isoPullback_inv_fst]
  exact pullbackSpecIso_inv_fst' ParameterAlgebra (DualNumber ℂ) B

@[reassoc] theorem chartPullbackIso_inv_original :
    (chartPullbackIso B f p q h e he).inv ≫ pullback.fst e p =
      tensorChartToOriginal B := by
  change ((pullbackSpecIso ParameterAlgebra (DualNumber ℂ) B).inv ≫
      (chartPullback_isPullback B f p q h e he).isoPullback.inv) ≫
        pullback.fst e p = _
  rw [Category.assoc, IsPullback.isoPullback_inv_snd]
  exact pullbackSpecIso_inv_snd ParameterAlgebra (DualNumber ℂ) B

def tensorChartToSource :
    Spec (CommRingCat.of (FirstOrderTensor B)) ⟶ Xε :=
  (chartPullbackIso B f p q h e he).inv ≫ pullback.snd e p

instance tensorChartToSource_isOpenImmersion [IsOpenImmersion e] :
    IsOpenImmersion (tensorChartToSource B f p q h e he) := by
  dsimp only [tensorChartToSource]
  infer_instance

@[reassoc] theorem tensorChartToSource_overBase :
    tensorChartToSource B f p q h e he ≫ q = tensorChartToBase B := by
  exact (Category.assoc _ _ _).trans
    (chartPullbackIso_inv_base B f p q h e he)

@[reassoc] theorem tensorChartToSource_original :
    tensorChartToSource B f p q h e he ≫ p = tensorChartToOriginal B ≫ e := by
  rw [tensorChartToSource, Category.assoc, ← pullback.condition,
    ← Category.assoc, chartPullbackIso_inv_original]

/-- The tensor chart is the actual open base change of the original chart. -/
theorem tensorChartToSource_isPullback :
    IsPullback (tensorChartToOriginal B) (tensorChartToSource B f p q h e he) e p := by
  apply (IsPullback.of_hasPullback e p).of_iso'
    (chartPullbackIso B f p q h e he).symm (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · simpa only [Iso.symm_hom, Iso.refl_hom, Category.comp_id] using
      chartPullbackIso_inv_original B f p q h e he
  · simp only [Iso.symm_hom, Iso.refl_hom, Category.comp_id, tensorChartToSource]
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]

theorem tensorChartToSource_opensRange [IsOpenImmersion e] :
    (tensorChartToSource B f p q h e he).opensRange = p ⁻¹ᵁ e.opensRange := by
  dsimp only [tensorChartToSource]
  rw [Scheme.Hom.opensRange_comp_of_isIso,
    Scheme.Hom.opensRange_pullbackSnd]

include h he in
/-- Flatness is used only on the actual first-order scheme over the dual numbers. -/
theorem tensorChart_flat [IsOpenImmersion e] [AlgebraicGeometry.Flat q] :
    Module.Flat (DualNumber ℂ) (FirstOrderTensor B) := by
  apply RingHom.flat_algebraMap_iff.mp
  apply (HasRingHomProperty.Spec_iff (P := @AlgebraicGeometry.Flat)
    (φ := CommRingCat.ofHom (R := DualNumber ℂ) (S := FirstOrderTensor B)
      (algebraMap (DualNumber ℂ) (FirstOrderTensor B)))).mp
  change AlgebraicGeometry.Flat (tensorChartToBase B)
  rw [← tensorChartToSource_overBase B f p q h e he]
  infer_instance

end ActualAffineBaseChange

/-- The original weight-one affine chart, including its actual open inclusion. -/
def originalSurfaceChart (i : Fin 4) :
    Spec (CommRingCat.of (DehomogenizedRing incidencePoint i)) ⟶ surface incidencePoint :=
  (familyCoordinateAffineChart incidencePoint i).inv ≫
    (familyCoordinatePatch incidencePoint i).ι

instance originalSurfaceChart_isOpenImmersion (i : Fin 4) :
    IsOpenImmersion (originalSurfaceChart i) := by
  dsimp only [originalSurfaceChart]
  infer_instance

theorem originalSurfaceChart_overBase (i : Fin 4) :
    originalSurfaceChart i ≫ surfaceToBase incidencePoint =
      Spec.map (CommRingCat.ofHom
        (algebraMap ParameterAlgebra (DehomogenizedRing incidencePoint i))) := by
  exact (Category.assoc _ _ _).trans
    (familyCoordinateAffineChart_overBase incidencePoint i)

theorem originalSurfaceChart_opensRange (i : Fin 4) :
    (originalSurfaceChart i).opensRange = familyCoordinatePatch incidencePoint i := by
  dsimp only [originalSurfaceChart]
  rw [Scheme.Hom.opensRange_comp_of_isIso]
  exact (familyCoordinatePatch incidencePoint i).opensRange_ι

/-- The actual first-order coordinate chart maps openly into the retained surface. -/
def firstOrderChartToSurface (i : Fin 4) :
    Spec (CommRingCat.of (FirstOrderSurfaceChart i)) ⟶ firstOrderSurface :=
  tensorChartToSource (DehomogenizedRing incidencePoint i) (surfaceToBase incidencePoint)
    firstOrderSurfaceToSurface firstOrderSurfaceToBase firstOrderSurface_isPullback
    (originalSurfaceChart i) (originalSurfaceChart_overBase i)

instance firstOrderChartToSurface_isOpenImmersion (i : Fin 4) :
    IsOpenImmersion (firstOrderChartToSurface i) := by
  dsimp only [firstOrderChartToSurface]
  infer_instance

@[reassoc] theorem firstOrderChartToSurface_overBase (i : Fin 4) :
    firstOrderChartToSurface i ≫ firstOrderSurfaceToBase =
      Spec.map (CommRingCat.ofHom
        (algebraMap (DualNumber ℂ) (FirstOrderSurfaceChart i))) :=
  tensorChartToSource_overBase (DehomogenizedRing incidencePoint i)
    (surfaceToBase incidencePoint) firstOrderSurfaceToSurface firstOrderSurfaceToBase
    firstOrderSurface_isPullback (originalSurfaceChart i) (originalSurfaceChart_overBase i)

theorem firstOrderChartToSurface_opensRange (i : Fin 4) :
    (firstOrderChartToSurface i).opensRange =
      firstOrderSurfaceToSurface ⁻¹ᵁ familyCoordinatePatch incidencePoint i := by
  dsimp only [firstOrderChartToSurface]
  rw [tensorChartToSource_opensRange,
    originalSurfaceChart_opensRange]

/-- Unconditional ambient flatness of the actual tensor chart along the retained tangent. -/
theorem firstOrderSurfaceChart_flat (i : Fin 4) :
    Module.Flat (DualNumber ℂ) (FirstOrderSurfaceChart i) := by
  letI := firstOrderSurfaceToBase_flat
  exact tensorChart_flat (DehomogenizedRing incidencePoint i)
    (surfaceToBase incidencePoint) firstOrderSurfaceToSurface firstOrderSurfaceToBase
    firstOrderSurface_isPullback (originalSurfaceChart i) (originalSurfaceChart_overBase i)

#print axioms tensorChartToSource_isPullback
#print axioms tensorChartToSource_opensRange
#print axioms firstOrderChartToSurface_overBase
#print axioms firstOrderSurfaceChart_flat

end CycleQ2FirstOrderChartFlatness
end
