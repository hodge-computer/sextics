import Proposal.GeometricLiteralCartierOverlapSplittings

/-!
# Actual splitting differences on the literal original Cartier cover

The four singleton splittings are constructed from the proved smoothness
of the original literal r=57 localizations. On every overlap they are
extended by the genuine localization maps of F - epsilon B*. Their
normalized differences are actual complex derivations of the original
closed rings. The derivations commute with restriction and obey the
Cech cocycle equation with the explicit sign sigma_j - sigma_i.

These are cone-ring representatives. This file does not identify them
with a projective Kodaira--Spencer or Hodge class.

Prepared for fqlx with OpenAI ChatGPT assistance; see solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralCartierKodairaSpencer

open CycleQ2LiteralCartierTransitionBinding CycleQ2GeometricSurfaceFirstOrder
  CycleQ2LiteralCartierSplittings CycleQ2LiteralCartierOverlapSplittings
  CycleQ2GeometricSquareZeroSplittings

attribute [local instance] CycleQ2LiteralCartierTransitionBinding.cubicSelfModule
  CycleQ2LiteralCartierTransitionBinding.cubicOppositeModule
  CycleQ2LiteralCartierTransitionBinding.cubicCentralScalar
  CycleQ2LiteralCartierTransitionBinding.cubicSmulCommClass
  CycleQ2GeometricSurfaceFirstOrder.reducedAlgebra
  CycleQ2GeometricKernelLocalization.localReductionAlgebra
  CycleQ2LiteralCartierSplittings.complexReductionTower
  CycleQ2LiteralCartierOverlapSplittings.baseReductionAlgebra

/-- The original faithful epsilon normalization commutes with the actual
restriction maps of both the deformed and the closed intersection. -/
theorem epsilon_restriction {s t : Finset (Fin 4)} (hst : s ⊆ t)
    (x : ClosedRing s) :
    thickRestriction hst (epsilon (kernelEquiv s) x) =
      epsilon (kernelEquiv t) (closedRestriction hst x) := by
  change thickRestriction hst ((kernelEquiv s) x).val =
    ((kernelEquiv t) (closedRestriction hst x)).val
  unfold CycleQ2LiteralCartierOverlapSplittings.thickRestriction
    CycleQ2LiteralCartierOverlapSplittings.thickRestrictionOverBase
    CycleQ2LiteralCartierOverlapSplittings.closedRestriction
    CycleQ2LiteralCartierOverlapSplittings.closedRestrictionOverBase
    CycleQ2LiteralCartierSplittings.kernelEquiv
    CycleQ2GeometricSurfaceFirstOrder.localKernelEquiv
  let e0 : ClosedBase ≃ₗ[ThickBase] RingHom.ker
      (@algebraMap ThickBase ClosedBase (inferInstance : CommSemiring ThickBase)
        (inferInstance : Semiring ClosedBase) baseReductionAlgebra) :=
    kernelEquivOverDeformation equation perturbation equation_regular
  have h := @CycleQ2GeometricKernelLocalization.localizedKernelEquiv_restriction
    ThickBase ClosedBase (inferInstance : CommRing ThickBase)
    (inferInstance : CommRing ClosedBase) baseReductionAlgebra e0
    (thickDenominator s) (thickDenominator t) (thickDenominator_divides hst) x
  set_option backward.isDefEq.respectTransparency true in
    exact h

/-- Extend the same chosen singleton splitting to each overlap containing it. -/
def splittingOn (i : Fin 4) (s : Finset (Fin 4)) (hi : i ∈ s) :
    ClosedRing s →ₐ[ℂ] Thick s :=
  overlapSplitting (s := {i}) (by simp) (by simpa only [Finset.singleton_subset_iff] using hi)

theorem splittingOn_reduction (i : Fin 4) (s : Finset (Fin 4)) (hi : i ∈ s)
    (x : ClosedRing s) :
    algebraMap (Thick s) (ClosedRing s) (splittingOn i s hi x) = x :=
  overlapSplitting_reduction (s := {i}) (by simp)
    (by simpa only [Finset.singleton_subset_iff] using hi) x

theorem splittingOn_restrict (i : Fin 4) {s t : Finset (Fin 4)} (hst : s ⊆ t)
    (hi : i ∈ s) (x : ClosedRing s) :
    thickRestriction hst (splittingOn i s hi x) =
      splittingOn i t (hst hi) (closedRestriction hst x) :=
  overlapSplitting_restrict (s := {i}) (by simp)
    (by simpa only [Finset.singleton_subset_iff] using hi) hst x

/-- The genuine epsilon coefficient of sigma_j - sigma_i. No derivation
on the ambient polynomial ring is asserted to descend to the surface. -/
def kodairaSpencer (s : Finset (Fin 4)) (i j : Fin 4) (hi : i ∈ s) (hj : j ∈ s) :
    Derivation ℂ (ClosedRing s) (ClosedRing s) :=
  difference (kernelEquiv s) (splittingOn i s hi) (splittingOn j s hj)
    (splittingOn_reduction i s hi) (splittingOn_reduction j s hj)

theorem epsilon_kodairaSpencer (s : Finset (Fin 4)) (i j : Fin 4)
    (hi : i ∈ s) (hj : j ∈ s) (x : ClosedRing s) :
    epsilon (kernelEquiv s) (kodairaSpencer s i j hi hj x) =
      splittingOn j s hj x - splittingOn i s hi x :=
  epsilon_difference _ _ _ _ _ _

/-- The actual normalized derivations agree after restriction. -/
theorem kodairaSpencer_restrict {s t : Finset (Fin 4)} (hst : s ⊆ t)
    (i j : Fin 4) (hi : i ∈ s) (hj : j ∈ s) (x : ClosedRing s) :
    closedRestriction hst (kodairaSpencer s i j hi hj x) =
      kodairaSpencer t i j (hst hi) (hst hj) (closedRestriction hst x) := by
  apply epsilon_injective (kernelEquiv t)
  rw [← epsilon_restriction, epsilon_kodairaSpencer, map_sub,
    splittingOn_restrict, splittingOn_restrict, epsilon_kodairaSpencer]

/-- The Cech law uses the actual original epsilon identification on
all three splitting differences. -/
theorem kodairaSpencer_trans (s : Finset (Fin 4)) (i j k : Fin 4)
    (hi : i ∈ s) (hj : j ∈ s) (hk : k ∈ s) :
    kodairaSpencer s i k hi hk =
      kodairaSpencer s i j hi hj + kodairaSpencer s j k hj hk :=
  difference_trans _ _ _ _ _ _ _

theorem kodairaSpencer_self (s : Finset (Fin 4)) (i : Fin 4) (hi : i ∈ s) :
    kodairaSpencer s i i hi hi = 0 := by
  ext x
  apply epsilon_injective (kernelEquiv s)
  rw [epsilon_kodairaSpencer, sub_self]
  exact (map_zero _).symm

theorem kodairaSpencer_reverse (s : Finset (Fin 4)) (i j : Fin 4)
    (hi : i ∈ s) (hj : j ∈ s) :
    kodairaSpencer s j i hj hi = -kodairaSpencer s i j hi hj := by
  have h := kodairaSpencer_trans s i j i hi hj hi
  rw [kodairaSpencer_self] at h
  exact eq_neg_of_add_eq_zero_right h.symm

end CycleQ2LiteralCartierKodairaSpencer

end

#print axioms CycleQ2LiteralCartierKodairaSpencer.epsilon_restriction
#print axioms CycleQ2LiteralCartierKodairaSpencer.kodairaSpencer_restrict
#print axioms CycleQ2LiteralCartierKodairaSpencer.kodairaSpencer_trans
