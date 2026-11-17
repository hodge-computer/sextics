import Proposal.GeometricCartierDeformation
import Proposal.GeometricLiteralSurfaceSmooth

/-!
# Actual smooth rings on the original Cartier cover

The original four Cartier functions are positive-degree polynomials.
Their nonempty principal intersections avoid the cone vertex. The
literal seed Jacobian certificate therefore proves smoothness of each
actual localization used by the original Cartier cochain. The actual
closed rings of F - epsilon B* are compared with those localizations
through the original polynomial-preserving equivalences.

The algebra splittings below are chosen from this proved smoothness,
the genuine reduction, and its already constructed square-zero kernel.
No splitting or Chern/Kodaira--Spencer comparison is assumed.

Prepared for fqlx with OpenAI ChatGPT assistance; see solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralCartierSplittings

open MvPolynomial
open CycleQ2SeedTrace CycleQ2NormalConnecting CycleQ2ConormalJacobian
  CycleQ2GeometricCartierNormalLift CycleQ2LiteralSurfaceSmooth
  CycleQ2LiteralCartierTransitionBinding CycleQ2GeometricSurfaceFirstOrder
  CycleQ2GeometricKernelLocalization

attribute [local instance] CycleQ2LiteralCartierTransitionBinding.cubicSelfModule
  CycleQ2LiteralCartierTransitionBinding.cubicOppositeModule
  CycleQ2LiteralCartierTransitionBinding.cubicCentralScalar
  CycleQ2LiteralCartierTransitionBinding.cubicSmulCommClass
  CycleQ2GeometricSurfaceFirstOrder.reducedAlgebra
  CycleQ2GeometricKernelLocalization.localReductionAlgebra

def coverPolynomial : Fin 4 → WeightedPoly :=
  ![originalG1 57, originalG2, originalF1 57, originalF2]

def polynomialProduct (s : Finset (Fin 4)) : WeightedPoly :=
  ∏ i ∈ s, coverPolynomial i

theorem coverPolynomial_mem (P : Ideal WeightedPoly)
    (hx : ∀ j : Fin 5, X j ∈ P) (i : Fin 4) : coverPolynomial i ∈ P := by
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  have hX (j : Fin 5) : Ideal.Quotient.mk P (X j) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (hx j)
  fin_cases i <;>
    simp [coverPolynomial, originalG1, originalG2, originalF1, originalF2, hX]

theorem polynomialProduct_relevant (s : Finset (Fin 4)) (hs : s.Nonempty)
    (P : Ideal WeightedPoly) (ht : polynomialProduct s ∉ P) :
    ∃ j : Fin 5, X j ∉ P := by
  by_contra! hx
  apply ht
  obtain ⟨i, hi⟩ := hs
  have hdiv : coverPolynomial i ∣ polynomialProduct s :=
    Finset.dvd_prod_of_mem coverPolynomial hi
  obtain ⟨q, hq⟩ := hdiv
  rw [hq]
  exact P.mul_mem_right q (coverPolynomial_mem P hx i)

theorem polynomialProduct_map (s : Finset (Fin 4)) :
    surfaceQuotient 57 1 (polynomialProduct s) = coverProduct 57 1 s := by
  simp only [polynomialProduct, coverProduct, map_prod]
  apply Finset.prod_congr rfl
  intro i _
  fin_cases i <;> rfl

/-- Smoothness of every nonempty intersection of the original four
Cartier cone opens, with the literal complex parameter 57. -/
theorem coverLocal_smooth (s : Finset (Fin 4)) (hs : s.Nonempty) :
    Algebra.Smooth ℂ (CoverLocal 57 1 s) := by
  change Algebra.Smooth ℂ (Localization.Away (coverProduct 57 1 s))
  rw [← polynomialProduct_map]
  apply coneLocalization_smooth_of_minor_cover (surfaceEquations 57 1) (polynomialProduct s)
  intro P hP hv ht
  have : P.IsPrime := hP
  obtain ⟨j, k, hm⟩ := CycleQ2SeedSurfaceGradient.actual_prime_normal_cover P
    (hv 0) (hv 1) (polynomialProduct_relevant s hs P ht)
  have hjk : j ≠ k := by
    intro he
    subst k
    apply hm
    simp only [CycleQ2SeedSurfaceGradient.actualNormalMinor, Matrix.det_fin_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, sub_self]
    exact P.zero_mem
  let p : Fin 2 → Fin 5 := ![j, k]
  refine ⟨p, ?_, ?_⟩
  · intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [p]
  · simpa only [equationMinor, p, surfaceEquations,
      CycleQ2SeedSurfaceGradient.actualNormalMinor, Matrix.det_fin_two,
      Matrix.cons_val_zero, Matrix.cons_val_one] using hm

def denominator (s : Finset (Fin 4)) : CubicRing := cubicMap (polynomialProduct s)

theorem denominator_binding (s : Finset (Fin 4)) :
    closedEquiv (closedCoordinate (denominator s)) = coverProduct 57 1 s := by
  rw [denominator, closedCoordinate_polynomial, polynomialProduct_map]

abbrev Thick (s : Finset (Fin 4)) := LocalDeformation equation perturbation (denominator s)
abbrev ClosedRing (s : Finset (Fin 4)) := LocalClosed equation perturbation (denominator s)

def closedRingEquiv (s : Finset (Fin 4)) : ClosedRing s ≃+* CoverLocal 57 1 s :=
  localizedClosedEquiv (denominator s) s (denominator_binding s)

theorem closedRingEquiv_polynomial (s : Finset (Fin 4)) (p : WeightedPoly) :
    closedRingEquiv s
      (localClosedPolynomialMap equation perturbation (denominator s) (cubicMap p)) =
      coverPolyMap 57 1 s p :=
  localizedClosedEquiv_polynomial (denominator s) s (denominator_binding s) p

/-- The original ring comparison preserves the actual complex constants. -/
def closedRingAlgEquiv (s : Finset (Fin 4)) : ClosedRing s ≃ₐ[ℂ] CoverLocal 57 1 s where
  __ := closedRingEquiv s
  commutes' z := by
    exact closedRingEquiv_polynomial s (C z)

theorem closedRing_formallySmooth (s : Finset (Fin 4)) (hs : s.Nonempty) :
    Algebra.FormallySmooth ℂ (ClosedRing s) := by
  have : Algebra.Smooth ℂ (CoverLocal 57 1 s) := coverLocal_smooth s hs
  exact Algebra.FormallySmooth.of_equiv (closedRingAlgEquiv s).symm

local instance complexReductionTower (s : Finset (Fin 4)) :
    IsScalarTower ℂ (Thick s) (ClosedRing s) := by
  apply IsScalarTower.of_algebraMap_eq
  intro z
  change algebraMap ℂ (ClosedRing s) z =
    localReduction (Deformation equation perturbation) (Closed equation)
      (deformationCoordinate equation perturbation (denominator s))
        (algebraMap ℂ (Thick s) z)
  rw [IsScalarTower.algebraMap_apply ℂ (Deformation equation perturbation) (Thick s),
    localReduction_base]
  rfl

/-- The genuine localized epsilon kernel, with its original coefficient action. -/
def kernelEquiv (s : Finset (Fin 4)) :
    ClosedRing s ≃ₗ[Thick s] RingHom.ker (algebraMap (Thick s) (ClosedRing s)) :=
  localKernelEquiv equation perturbation (denominator s) equation_regular

theorem reduction_surjective (s : Finset (Fin 4)) :
    Function.Surjective (algebraMap (Thick s) (ClosedRing s)) :=
  localReduction_surjective (Deformation equation perturbation) (Closed equation)
    (CycleQ2GeometricSurfaceFirstOrder.reduction_surjective equation perturbation)
    (deformationCoordinate equation perturbation (denominator s))

/-- A constructed complex-algebra splitting of the actual ambient-test
deformation on every nonempty original Cartier intersection. -/
def splitting (s : Finset (Fin 4)) (hs : s.Nonempty) : ClosedRing s →ₐ[ℂ] Thick s := by
  have : Algebra.FormallySmooth ℂ (ClosedRing s) := closedRing_formallySmooth s hs
  exact CycleQ2GeometricSquareZeroSplittings.smoothSplitting
    (K := ℂ) (kernelEquiv s) (reduction_surjective s)

theorem splitting_reduction (s : Finset (Fin 4)) (hs : s.Nonempty)
    (x : ClosedRing s) :
    algebraMap (Thick s) (ClosedRing s) (splitting s hs x) = x := by
  have : Algebra.FormallySmooth ℂ (ClosedRing s) := closedRing_formallySmooth s hs
  exact CycleQ2GeometricSquareZeroSplittings.reduction_smoothSplitting
    (K := ℂ) (kernelEquiv s) (reduction_surjective s) x

end CycleQ2LiteralCartierSplittings

end

#print axioms CycleQ2LiteralCartierSplittings.coverLocal_smooth
#print axioms CycleQ2LiteralCartierSplittings.closedRing_formallySmooth
#print axioms CycleQ2LiteralCartierSplittings.splitting_reduction
