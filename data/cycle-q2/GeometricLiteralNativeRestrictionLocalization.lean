import Proposal.GeometricLiteralProjectiveIntersectionComplex
import Proposal.GeometricLocalizedDifferentials

/-!
# Native intersection restrictions are actual localizations

For a nonempty native source intersection, restriction to a further
intersection inverts the standard degree-zero homogeneous fraction.
The actual localization theorem for Kähler modules consequently shows
that linear contractions on the larger intersection are determined by
their values on differentials from the original intersection ring.

Prepared for fqlx with OpenAI ChatGPT assistance; see solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralNativeRestrictionLocalization

open HomogeneousLocalization CycleQ2CartierSurfaceGrading
  CycleQ2LiteralProjectiveIntersections CycleQ2LiteralProjectiveIntersectionRestrictions
  CycleQ2LiteralProjectiveIntersectionComplex

attribute [local instance] CycleQ2LiteralProjectiveIntersectionComplex.closedComplexAlgebra
  CycleQ2LiteralProjectiveIntersectionComplex.closedComplexSMul
  CycleQ2LiteralProjectiveIntersectionComplex.closedComplexModule

def restrictionElement (s t : Finset Vertex) : ClosedRing s :=
  Away.isLocalizationElem (closedProduct_homogeneous s) (closedProduct_homogeneous (t \ s))

theorem closedRestriction_isLocalization {s t : Finset Vertex} (hst : s ⊆ t) (hs : s.Nonempty) :
    letI := (closedRestrictionAlgHom hst).toRingHom.toAlgebra
    IsLocalization.Away (restrictionElement s t) (ClosedRing t) := by
  exact Away.isLocalization_mul (closedProduct_homogeneous s) (closedProduct_homogeneous (t \ s))
    (closedProduct_factor hst) (Nat.ne_of_gt (productDegree_pos hs))

theorem nativeDifferential_ext {s t : Finset Vertex} (hst : s ⊆ t) (hs : s.Nonempty)
    (f g : KaehlerDifferential ℂ (ClosedRing t) →ₗ[ClosedRing t] ClosedRing t)
    (h : ∀ a : ClosedRing s,
      f (KaehlerDifferential.D ℂ (ClosedRing t) (closedRestrictionAlgHom hst a)) =
        g (KaehlerDifferential.D ℂ (ClosedRing t) (closedRestrictionAlgHom hst a))) : f = g := by
  let := (closedRestrictionAlgHom hst).toRingHom.toAlgebra
  let : IsScalarTower ℂ (ClosedRing s) (ClosedRing t) :=
    IsScalarTower.of_algHom (closedRestrictionAlgHom hst)
  let : IsLocalization.Away (restrictionElement s t) (ClosedRing t) :=
    closedRestriction_isLocalization hst hs
  apply LinearMap.restrictScalars_injective (ClosedRing s)
  apply IsLocalizedModule.linearMap_ext (Submonoid.powers (restrictionElement s t))
    (KaehlerDifferential.map ℂ ℂ (ClosedRing s) (ClosedRing t)) (Algebra.linearMap (ClosedRing s) (ClosedRing t))
  apply Derivation.liftKaehlerDifferential_unique
  apply DFunLike.ext
  intro a
  change f (KaehlerDifferential.map ℂ ℂ (ClosedRing s) (ClosedRing t)
      (KaehlerDifferential.D ℂ (ClosedRing s) a)) =
    g (KaehlerDifferential.map ℂ ℂ (ClosedRing s) (ClosedRing t)
      (KaehlerDifferential.D ℂ (ClosedRing s) a))
  rw [KaehlerDifferential.map_D]
  exact h a

end CycleQ2LiteralNativeRestrictionLocalization

end

#print axioms CycleQ2LiteralNativeRestrictionLocalization.closedRestriction_isLocalization
#print axioms CycleQ2LiteralNativeRestrictionLocalization.nativeDifferential_ext
