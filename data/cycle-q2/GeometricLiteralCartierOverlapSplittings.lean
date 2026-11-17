import Proposal.GeometricLiteralCartierSplittings

/-!
# Compatible overlap extensions of the original Cartier-cover splittings

Restriction maps below are the actual localization maps of the original
ambient-test deformation and its actual reduction. A singleton splitting
extends to an intersection by the localization universal property. Its
new denominators are units because their reductions are units and the
actual reduction kernel is square zero. The extension is unique on the
original closed numerators, and commutes with further restriction.

Prepared for fqlx with OpenAI ChatGPT assistance; see solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralCartierOverlapSplittings

open MvPolynomial
open CycleQ2SeedTrace CycleQ2NormalConnecting
open CycleQ2LiteralCartierTransitionBinding CycleQ2GeometricSurfaceFirstOrder
  CycleQ2GeometricKernelLocalization CycleQ2LiteralCartierSplittings

attribute [local instance] CycleQ2LiteralCartierTransitionBinding.cubicSelfModule
  CycleQ2LiteralCartierTransitionBinding.cubicOppositeModule
  CycleQ2LiteralCartierTransitionBinding.cubicCentralScalar
  CycleQ2LiteralCartierTransitionBinding.cubicSmulCommClass
  CycleQ2GeometricSurfaceFirstOrder.reducedAlgebra
  CycleQ2GeometricKernelLocalization.localReductionAlgebra
  CycleQ2LiteralCartierSplittings.complexReductionTower

abbrev ThickBase : Type := Deformation equation perturbation
abbrev ClosedBase : Type := Closed equation

local instance baseReductionAlgebra : Algebra ThickBase ClosedBase :=
  CycleQ2GeometricSurfaceFirstOrder.reducedAlgebra equation perturbation

abbrev thickDenominator (s : Finset (Fin 4)) : ThickBase :=
  deformationCoordinate equation perturbation (denominator s)

abbrev closedDenominator (s : Finset (Fin 4)) : ClosedBase :=
  @Algebra.algebraMap ThickBase ClosedBase
    (inferInstance : CommSemiring ThickBase) (inferInstance : Semiring ClosedBase)
    baseReductionAlgebra (thickDenominator s)

def polynomialToThick : WeightedPoly →+* ThickBase :=
  (Algebra.algebraMap CubicRing ThickBase).comp cubicMap

theorem thickDenominator_divides {s t : Finset (Fin 4)} (hst : s ⊆ t) :
    thickDenominator s ∣ thickDenominator t :=
  map_dvd polynomialToThick (Finset.prod_dvd_prod_of_subset s t coverPolynomial hst)

theorem closedDenominator_divides {s t : Finset (Fin 4)} (hst : s ⊆ t) :
    closedDenominator s ∣ closedDenominator t :=
  map_dvd (@Algebra.algebraMap ThickBase ClosedBase
    (inferInstance : CommSemiring ThickBase) (inferInstance : Semiring ClosedBase)
    baseReductionAlgebra) (thickDenominator_divides hst)

def thickRestrictionOverBase {s t : Finset (Fin 4)} (hst : s ⊆ t) :
    Thick s →ₐ[ThickBase] Thick t :=
  CycleQ2GeometricKernelLocalization.thickRestriction ThickBase
    (thickDenominator_divides hst)

def thickRestriction {s t : Finset (Fin 4)} (hst : s ⊆ t) :
    Thick s →ₐ[ℂ] Thick t := (thickRestrictionOverBase hst).restrictScalars ℂ

theorem thickRestriction_base {s t : Finset (Fin 4)} (hst : s ⊆ t) (z : ThickBase) :
    thickRestriction hst (@Algebra.algebraMap ThickBase (Thick s)
      (inferInstance : CommSemiring ThickBase) (inferInstance : Semiring (Thick s))
      inferInstance z) =
      @Algebra.algebraMap ThickBase (Thick t)
      (inferInstance : CommSemiring ThickBase) (inferInstance : Semiring (Thick t))
      inferInstance z :=
  (thickRestrictionOverBase hst).commutes z

def closedRestrictionOverBase {s t : Finset (Fin 4)} (hst : s ⊆ t) :
    ClosedRing s →ₐ[ClosedBase] ClosedRing t :=
  CycleQ2GeometricKernelLocalization.closedRestriction ThickBase ClosedBase
    (thickDenominator_divides hst)

def closedRestriction {s t : Finset (Fin 4)} (hst : s ⊆ t) :
    ClosedRing s →ₐ[ℂ] ClosedRing t := (closedRestrictionOverBase hst).restrictScalars ℂ

theorem closedRestriction_base {s t : Finset (Fin 4)} (hst : s ⊆ t) (z : ClosedBase) :
    closedRestriction hst (Algebra.algebraMap ClosedBase (ClosedRing s) z) =
      Algebra.algebraMap ClosedBase (ClosedRing t) z :=
  (closedRestrictionOverBase hst).commutes z

def reductionMap (s : Finset (Fin 4)) : Thick s →ₐ[ℂ] ClosedRing s :=
  IsScalarTower.toAlgHom ℂ (Thick s) (ClosedRing s)

theorem reductionMap_base (s : Finset (Fin 4)) (z : ThickBase) :
    reductionMap s (@Algebra.algebraMap ThickBase (Thick s)
      (inferInstance : CommSemiring ThickBase) (inferInstance : Semiring (Thick s))
      inferInstance z) =
      Algebra.algebraMap ClosedBase (ClosedRing s) (@Algebra.algebraMap ThickBase ClosedBase
    (inferInstance : CommSemiring ThickBase) (inferInstance : Semiring ClosedBase)
    baseReductionAlgebra z) :=
  localReduction_base ThickBase ClosedBase (thickDenominator s) z

theorem reductionMap_restriction {s t : Finset (Fin 4)} (hst : s ⊆ t)
    (z : Thick s) :
    closedRestriction hst (reductionMap s z) = reductionMap t (thickRestriction hst z) := by
  have h : (closedRestriction hst).toRingHom.comp (reductionMap s).toRingHom =
      (reductionMap t).toRingHom.comp (thickRestriction hst).toRingHom := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (thickDenominator s))
    apply RingHom.ext
    intro x
    change closedRestriction hst (reductionMap s _) =
      reductionMap t (thickRestriction hst _)
    rw [reductionMap_base, thickRestriction_base, reductionMap_base, closedRestriction_base]
  exact RingHom.congr_fun h z

theorem thickRestriction_comp {s t u : Finset (Fin 4)} (hst : s ⊆ t) (htu : t ⊆ u)
    (z : Thick s) :
    thickRestriction htu (thickRestriction hst z) = thickRestriction (hst.trans htu) z := by
  have h : (thickRestriction htu).comp (thickRestriction hst) =
      thickRestriction (hst.trans htu) := by
    apply AlgHom.coe_ringHom_injective
    apply IsLocalization.ringHom_ext (Submonoid.powers (thickDenominator s))
    apply RingHom.ext
    intro x
    change thickRestriction htu (thickRestriction hst _) =
      thickRestriction (hst.trans htu) _
    rw [thickRestriction_base, thickRestriction_base, thickRestriction_base]
  exact AlgHom.congr_fun h z

/-- A unit of the actual closed intersection lifts to a unit in its
actual ambient-test thickening; the proof uses the genuine square-zero kernel. -/
theorem isUnit_of_reduction (s : Finset (Fin 4)) (z : Thick s)
    (hz : IsUnit (reductionMap s z)) : IsUnit z := by
  obtain ⟨u, hu⟩ := hz
  obtain ⟨b, hb⟩ := CycleQ2LiteralCartierSplittings.reduction_surjective s
    (↑(u⁻¹) : ClosedRing s)
  have hkernel : Algebra.algebraMap (Thick s) (ClosedRing s) (z * b - 1) = 0 := by
    rw [map_sub, map_mul, map_one, hb]
    change reductionMap s z * (↑(u⁻¹) : ClosedRing s) - 1 = 0
    rw [← hu, Units.mul_inv, sub_self]
  have hn : IsNilpotent (z * b - 1) := by
    refine ⟨2, ?_⟩
    rw [pow_two]
    exact CycleQ2GeometricSquareZeroSplittings.kernel_mul_zero
      (CycleQ2LiteralCartierSplittings.kernelEquiv s) _ _ hkernel hkernel
  have hp : IsUnit (z * b) := by
    have h := hn.isUnit_add_left_of_commute
      (isUnit_one : IsUnit (1 : Thick s)) (Commute.all _ _)
    have he : (1 : Thick s) + (z * b - 1) = z * b := by ring
    rwa [he] at h
  exact isUnit_of_mul_isUnit_left hp

/-- The original singleton/intersection splitting, restricted on its
deformed side, before extending its closed side to a larger intersection. -/
def splittingBase {s t : Finset (Fin 4)} (hs : s.Nonempty) (hst : s ⊆ t) :
    ClosedBase →ₐ[ℂ] Thick t :=
  (thickRestriction hst).comp ((CycleQ2LiteralCartierSplittings.splitting s hs).comp
    (IsScalarTower.toAlgHom ℂ ClosedBase (ClosedRing s)))

theorem splittingBase_reduction {s t : Finset (Fin 4)} (hs : s.Nonempty)
    (hst : s ⊆ t) (z : ClosedBase) :
    reductionMap t (splittingBase hs hst z) = Algebra.algebraMap ClosedBase (ClosedRing t) z := by
  change reductionMap t (thickRestriction hst
    (CycleQ2LiteralCartierSplittings.splitting s hs
      (Algebra.algebraMap ClosedBase (ClosedRing s) z))) = _
  rw [← reductionMap_restriction]
  change closedRestriction hst (Algebra.algebraMap (Thick s) (ClosedRing s)
    (CycleQ2LiteralCartierSplittings.splitting s hs
      (Algebra.algebraMap ClosedBase (ClosedRing s) z))) = _
  rw [CycleQ2LiteralCartierSplittings.splitting_reduction, closedRestriction_base]

theorem splittingBase_denominator_unit {s t : Finset (Fin 4)} (hs : s.Nonempty)
    (hst : s ⊆ t) : IsUnit (splittingBase hs hst (closedDenominator t)) := by
  apply isUnit_of_reduction
  rw [splittingBase_reduction]
  exact IsLocalization.Away.algebraMap_isUnit (closedDenominator t)

/-- The canonical overlap extension of the already chosen original splitting. -/
def overlapSplitting {s t : Finset (Fin 4)} (hs : s.Nonempty) (hst : s ⊆ t) :
    ClosedRing t →ₐ[ℂ] Thick t where
  __ := IsLocalization.Away.lift (S := ClosedRing t) (g := (splittingBase hs hst).toRingHom)
    (closedDenominator t) (splittingBase_denominator_unit hs hst)
  commutes' z := by
    rw [IsScalarTower.algebraMap_apply ℂ ClosedBase (ClosedRing t)]
    change IsLocalization.Away.lift (S := ClosedRing t)
      (g := (splittingBase hs hst).toRingHom) (closedDenominator t)
      (splittingBase_denominator_unit hs hst)
        (Algebra.algebraMap ClosedBase (ClosedRing t) (Algebra.algebraMap ℂ ClosedBase z)) = _
    rw [IsLocalization.Away.lift_eq]
    exact (splittingBase hs hst).commutes z

theorem overlapSplitting_base {s t : Finset (Fin 4)} (hs : s.Nonempty)
    (hst : s ⊆ t) (z : ClosedBase) :
    overlapSplitting hs hst (Algebra.algebraMap ClosedBase (ClosedRing t) z) =
      splittingBase hs hst z :=
  IsLocalization.Away.lift_eq (closedDenominator t)
    (splittingBase_denominator_unit hs hst) z

theorem overlapSplitting_reduction {s t : Finset (Fin 4)} (hs : s.Nonempty)
    (hst : s ⊆ t) (x : ClosedRing t) :
    reductionMap t (overlapSplitting hs hst x) = x := by
  have h : (reductionMap t).comp (overlapSplitting hs hst) = AlgHom.id ℂ (ClosedRing t) := by
    apply AlgHom.coe_ringHom_injective
    apply IsLocalization.ringHom_ext (Submonoid.powers (closedDenominator t))
    apply RingHom.ext
    intro z
    change reductionMap t (overlapSplitting hs hst _) = _
    rw [overlapSplitting_base, splittingBase_reduction]
    rfl
  exact AlgHom.congr_fun h x

/-- Extending the same original splitting commutes with each further localization. -/
theorem overlapSplitting_restrict {s t u : Finset (Fin 4)} (hs : s.Nonempty)
    (hst : s ⊆ t) (htu : t ⊆ u) (x : ClosedRing t) :
    thickRestriction htu (overlapSplitting hs hst x) =
      overlapSplitting hs (hst.trans htu) (closedRestriction htu x) := by
  have h : (thickRestriction htu).comp (overlapSplitting hs hst) =
      (overlapSplitting hs (hst.trans htu)).comp (closedRestriction htu) := by
    apply AlgHom.coe_ringHom_injective
    apply IsLocalization.ringHom_ext (Submonoid.powers (closedDenominator t))
    apply RingHom.ext
    intro z
    change thickRestriction htu (overlapSplitting hs hst _) =
      overlapSplitting hs (hst.trans htu) (closedRestriction htu _)
    rw [overlapSplitting_base, closedRestriction_base, overlapSplitting_base]
    change thickRestriction htu (thickRestriction hst _) =
      thickRestriction (hst.trans htu) _
    exact thickRestriction_comp hst htu _
  exact AlgHom.congr_fun h x

end CycleQ2LiteralCartierOverlapSplittings

end

#print axioms CycleQ2LiteralCartierOverlapSplittings.overlapSplitting_reduction
#print axioms CycleQ2LiteralCartierOverlapSplittings.overlapSplitting_restrict
