import Proposal.GeometricLiteralCartierAtiyahFaces

/-!
# Naturality of the actual Cartier correction terms

The original polynomial maps, closed-ring comparison, normalized units,
and their genuine epsilon coefficients all commute with the actual
localization restrictions. These equalities use the same constructed
singleton splittings and the same original epsilon identification.

Prepared for fqlx with OpenAI ChatGPT assistance; see solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralCartierCochainNaturality

open CycleQ2SeedTrace CycleQ2NormalConnecting CycleQ2ConormalJacobian
  CycleQ2GeometricSeedNormalIdeals CycleQ2GeometricCartierNormalLift
  CycleQ2LiteralCartierTransitionBinding CycleQ2GeometricSurfaceFirstOrder
  CycleQ2LiteralCartierSplittings CycleQ2LiteralCartierOverlapSplittings
  CycleQ2LiteralCartierKodairaSpencer CycleQ2LiteralCartierAtiyahFaces
  CycleQ2GeometricSquareZeroSplittings

attribute [local instance] CycleQ2LiteralCartierTransitionBinding.cubicSelfModule
  CycleQ2LiteralCartierTransitionBinding.cubicOppositeModule
  CycleQ2LiteralCartierTransitionBinding.cubicCentralScalar
  CycleQ2LiteralCartierTransitionBinding.cubicSmulCommClass
  CycleQ2GeometricSurfaceFirstOrder.reducedAlgebra
  CycleQ2GeometricKernelLocalization.localReductionAlgebra
  CycleQ2LiteralCartierSplittings.complexReductionTower
  CycleQ2LiteralCartierOverlapSplittings.baseReductionAlgebra

theorem polynomialMap_restrict {s t : Finset (Fin 4)} (hst : s ⊆ t) (p : WeightedPoly) :
    thickRestriction hst (polynomialMap s p) = polynomialMap t p :=
  thickRestriction_base hst (polynomialToThick p)

theorem closedRingEquiv_base (s : Finset (Fin 4)) (x : ClosedBase) :
    closedRingEquiv s (algebraMap ClosedBase (ClosedRing s) x) =
      algebraMap (SurfaceRing 57 1) (CoverLocal 57 1 s) (closedEquiv x) :=
  localizedClosedEquiv_base (denominator s) s (denominator_binding s) x

/-- The original polynomial-preserving ring equivalences form a
commuting square with the two actual closed restriction maps. -/
theorem closedRingEquiv_restrict {s t : Finset (Fin 4)} (hst : s ⊆ t) (x : ClosedRing s) :
    coverRestriction 57 1 hst (closedRingEquiv s x) =
      closedRingEquiv t (closedRestriction hst x) := by
  have h : (coverRestriction 57 1 hst).toRingHom.comp (closedRingEquiv s).toRingHom =
      (closedRingEquiv t).toRingHom.comp (closedRestriction hst).toRingHom := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (closedDenominator s))
    apply RingHom.ext
    intro z
    change coverRestriction 57 1 hst (closedRingEquiv s _) =
      closedRingEquiv t (closedRestriction hst _)
    rw [closedRingEquiv_base, coverRestriction_base, closedRestriction_base, closedRingEquiv_base]
  exact RingHom.congr_fun h x

def restrictUnit {s t : Finset (Fin 4)} (hst : s ⊆ t) (u : (Thick s)ˣ) : (Thick t)ˣ :=
  Units.map (thickRestriction hst).toMonoidHom u

theorem restrictUnit_value {s t : Finset (Fin 4)} (hst : s ⊆ t) (u : (Thick s)ˣ) :
    (restrictUnit hst u : Thick t) = thickRestriction hst (u : Thick s) := rfl

theorem reducedUnit_restrict {s t : Finset (Fin 4)} (hst : s ⊆ t) (u : (Thick s)ˣ) :
    Units.map (closedRestriction hst).toMonoidHom (reducedUnit (C := ClosedRing s) u) =
      reducedUnit (C := ClosedRing t) (restrictUnit hst u) := by
  apply Units.ext
  exact reductionMap_restriction hst (u : Thick s)

theorem reducedUnit_inverse_restrict {s t : Finset (Fin 4)} (hst : s ⊆ t)
    (u : (Thick s)ˣ) :
    closedRestriction hst (↑((reducedUnit (C := ClosedRing s) u)⁻¹) : ClosedRing s) =
      (↑((reducedUnit (C := ClosedRing t) (restrictUnit hst u))⁻¹) : ClosedRing t) := by
  have h := congrArg (fun v : (ClosedRing t)ˣ => (↑(v⁻¹) : ClosedRing t))
    (reducedUnit_restrict hst u)
  exact h

theorem normalizedUnitValue_restrict {s t : Finset (Fin 4)} (hst : s ⊆ t)
    (i : Fin 4) (hi : i ∈ s) (u : (Thick s)ˣ) :
    thickRestriction hst (normalizedUnitValue (splittingOn i s hi) u) =
      normalizedUnitValue (splittingOn i t (hst hi)) (restrictUnit hst u) := by
  unfold normalizedUnitValue
  rw [map_mul, splittingOn_restrict, reducedUnit_inverse_restrict]
  rfl

/-- A correction coefficient is restricted through the original
faithful epsilon maps; it is not chosen afresh on an overlap. -/
theorem unitCorrection_restrict {s t : Finset (Fin 4)} (hst : s ⊆ t)
    (i : Fin 4) (hi : i ∈ s) (u : (Thick s)ˣ) :
    closedRestriction hst
      (unitCorrection (kernelEquiv s) (splittingOn i s hi) (splittingOn_reduction i s hi) u) =
    unitCorrection (kernelEquiv t) (splittingOn i t (hst hi))
      (splittingOn_reduction i t (hst hi)) (restrictUnit hst u) := by
  apply epsilon_injective (kernelEquiv t)
  rw [← epsilon_restriction, epsilon_unitCorrection, map_sub,
    normalizedUnitValue_restrict, map_one, epsilon_unitCorrection]

/-- The coefficient identity after passage to the original surface
localization rings used by the original Cech complex. -/
theorem comparedCorrection_restrict {s t : Finset (Fin 4)} (hst : s ⊆ t)
    (i : Fin 4) (hi : i ∈ s) (u : (Thick s)ˣ) :
    coverRestriction 57 1 hst (closedRingEquiv s
      (unitCorrection (kernelEquiv s) (splittingOn i s hi) (splittingOn_reduction i s hi) u)) =
    closedRingEquiv t (unitCorrection (kernelEquiv t) (splittingOn i t (hst hi))
      (splittingOn_reduction i t (hst hi)) (restrictUnit hst u)) := by
  rw [closedRingEquiv_restrict, unitCorrection_restrict]

theorem factors_restrict {s t : Finset (Fin 4)} (hst : s ⊆ t)
    (h0 : 0 ∈ s) (h1 : 1 ∈ s) (hf : 2 ∈ s ∨ 3 ∈ s) (i : Fin 4) :
    restrictUnit hst (factors s h0 h1 hf i) =
      factors t (hst h0) (hst h1) (hf.imp (fun h => hst h) (fun h => hst h)) i := by
  apply Units.ext
  rw [restrictUnit_value, factors_value, polynomialMap_restrict, factors_value]

end CycleQ2LiteralCartierCochainNaturality

end

#print axioms CycleQ2LiteralCartierCochainNaturality.closedRingEquiv_restrict
#print axioms CycleQ2LiteralCartierCochainNaturality.unitCorrection_restrict
#print axioms CycleQ2LiteralCartierCochainNaturality.comparedCorrection_restrict
