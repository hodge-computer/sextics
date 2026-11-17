import Proposal.GeometricLiteralGradedDeformationEquiv

/-!
# The actual graded reduction and faithful epsilon kernel

Reduction of the weight-zero epsilon presentation is the original
weighted surface ring. It agrees with the independent original
F - epsilon B* reduction under the fixed-coordinate equivalence.
The original faithful epsilon identification is transported through
that equivalence, with its genuine reduced multiplication action.
Both reduction and epsilon preserve homogeneous components.

Prepared for fqlx with OpenAI ChatGPT assistance; see solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralGradedReduction

open MvPolynomial CycleQ2SeedTrace CycleQ2NormalConnecting CycleQ2ConormalJacobian
  CycleQ2GeometricSeedNormalIdeals CycleQ2GeometricCartierNormalLift CycleQ2CartierSurfaceGrading
  CycleQ2LiteralCartierTransitionBinding CycleQ2GeometricSurfaceFirstOrder
  CycleQ2LiteralCartierOverlapSplittings CycleQ2LiteralGradedDeformation
  CycleQ2LiteralGradedDeformationEquiv

attribute [local instance] CycleQ2LiteralCartierTransitionBinding.cubicSelfModule
  CycleQ2LiteralCartierTransitionBinding.cubicOppositeModule
  CycleQ2LiteralCartierTransitionBinding.cubicCentralScalar
  CycleQ2LiteralCartierTransitionBinding.cubicSmulCommClass
  CycleQ2GeometricSurfaceFirstOrder.reducedAlgebra

local instance thickComplexModule : Module ℂ ThickBase :=
  @Algebra.toModule ℂ ThickBase (inferInstance : CommSemiring ℂ)
    (inferInstance : Semiring ThickBase) inferInstance

local instance thickCubicModule : Module CubicRing ThickBase :=
  @Algebra.toModule CubicRing ThickBase (inferInstance : CommSemiring CubicRing)
    (inferInstance : Semiring ThickBase) inferInstance

def surfacePolynomialMap : WeightedPoly →ₐ[ℂ] SurfaceRing 57 1 :=
  Ideal.Quotient.mkₐ ℂ (surfaceIdeal 57 1)

def rawVariable : Option (Fin 5) → SurfaceRing 57 1 :=
  Option.elim' 0 (fun i => surfaceQuotient 57 1 (X i))

def rawReduction : AmbientPoly →ₐ[ℂ] SurfaceRing 57 1 := aeval rawVariable

theorem rawReduction_include (p : WeightedPoly) :
    rawReduction (includePolynomial p) = surfaceQuotient 57 1 p := by
  have h : rawReduction.comp includePolynomial = surfacePolynomialMap := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [rawReduction, rawVariable, includePolynomial, surfacePolynomialMap]
    rfl
  exact AlgHom.congr_fun h p

theorem rawReduction_epsilon : rawReduction epsilonPolynomial = 0 := by
  simp [rawReduction, rawVariable, epsilonPolynomial]

theorem rawReduction_relations (i : Fin 3) : rawReduction (relations i) = 0 := by
  fin_cases i
  · change rawReduction (includePolynomial (thetaH 1)) = 0
    rw [rawReduction_include]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨1, rfl⟩)
  · change rawReduction (includePolynomial (actualSeedEquation 57 1) -
      epsilonPolynomial * includePolynomial derivativeA) = 0
    rw [map_sub, map_mul, rawReduction_epsilon, zero_mul, sub_zero, rawReduction_include]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨0, rfl⟩)
  · change rawReduction (epsilonPolynomial ^ 2) = 0
    rw [map_pow, rawReduction_epsilon, zero_pow (by decide)]

def reduction : GradedDeformation →ₐ[ℂ] SurfaceRing 57 1 :=
  Ideal.Quotient.liftₐ ambientIdeal rawReduction (by
    intro p hp
    have hI : ambientIdeal ≤ RingHom.ker rawReduction.toRingHom :=
      Ideal.span_le.mpr (by rintro p ⟨i,rfl⟩; exact rawReduction_relations i)
    exact hI hp)

theorem reduction_polynomial (p : WeightedPoly) :
    reduction (polynomialInGraded p) = surfaceQuotient 57 1 p :=
  rawReduction_include p

theorem reduction_epsilon : reduction epsilonElement = 0 := rawReduction_epsilon

theorem rawVariable_homogeneous (i : Option (Fin 5)) :
    rawVariable i ∈ surfaceGrade 57 1 (ambientWeight i) := by
  cases i with
  | none => exact Submodule.zero_mem _
  | some i => exact surfaceQuotient_mem_grade 57 1 (isWeightedHomogeneous_X ℂ weight i)

theorem rawReduction_homogeneous {n : ℕ} {p : AmbientPoly} (hp : p ∈ AmbientGrade n) :
    rawReduction p ∈ surfaceGrade 57 1 n := by
  induction hp using MvPolynomial.IsWeightedHomogeneous.induction_on with
  | zero => simpa only [map_zero] using (surfaceGrade 57 1 n).zero_mem
  | add p q hp hq ihp ihq =>
    simpa only [map_add] using (surfaceGrade 57 1 n).add_mem ihp ihq
  | monomial d c hd =>
    rw [rawReduction, aeval_monomial]
    have hc : algebraMap ℂ (SurfaceRing 57 1) c ∈ surfaceGrade 57 1 0 := by
      change surfaceQuotient 57 1 (C c) ∈ surfaceGrade 57 1 0
      exact surfaceQuotient_mem_grade 57 1 (isWeightedHomogeneous_C weight c)
    have hm : d.prod (fun i k => rawVariable i ^ k) ∈ surfaceGrade 57 1 n := by
      rw [← hd]
      exact SetLike.prod_mem_graded (surfaceGrade 57 1)
        (fun i => d i • ambientWeight i) (fun i => rawVariable i ^ d i)
        (fun i _ => SetLike.pow_mem_graded (d i) (rawVariable_homogeneous i))
    simpa only [zero_add] using SetLike.mul_mem_graded hc hm

def reductionGraded : deformationGrade →+*ᵍ surfaceGrade 57 1 where
  toRingHom := reduction.toRingHom
  map_mem hp := by
    obtain ⟨p,hp,rfl⟩ := hp
    exact rawReduction_homogeneous hp

/-- Surjectivity retains a lift in the same homogeneous component. -/
theorem reduction_homogeneous_surjective (n : ℕ) (x : SurfaceRing 57 1)
    (hx : x ∈ surfaceGrade 57 1 n) :
    ∃ y ∈ deformationGrade n, reduction y = x := by
  obtain ⟨p,hp,rfl⟩ := hx
  exact ⟨polynomialInGraded p, quotientMap_mem_grade (includePolynomial_homogeneous hp),
    reduction_polynomial p⟩

theorem reduction_surjective : Function.Surjective reduction := by
  intro x
  obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective x
  exact ⟨polynomialInGraded p, reduction_polynomial p⟩

def closedAlgEquiv : ClosedBase ≃ₐ[ℂ] SurfaceRing 57 1 where
  __ := closedEquiv
  commutes' c := closedEquiv_polynomial (C c)

theorem closedAlgEquiv_symm_polynomial (p : WeightedPoly) :
    closedAlgEquiv.symm (surfaceQuotient 57 1 p) =
      Ideal.Quotient.mk (Ideal.span ({equation} : Set CubicRing)) (cubicMap p) := by
  apply closedAlgEquiv.injective
  rw [AlgEquiv.apply_symm_apply]
  exact (closedEquiv_polynomial p).symm

/-- Reduction is the original ambient-test reduction under the
independently proved polynomial- and epsilon-preserving equivalence. -/
theorem reduction_eq_original (x : GradedDeformation) :
    reduction x = closedAlgEquiv
      (CycleQ2GeometricSurfaceFirstOrder.reduction equation perturbation (toOriginal x)) := by
  have h : reduction = closedAlgEquiv.toAlgHom.comp
      (((CycleQ2GeometricSurfaceFirstOrder.reduction equation perturbation).restrictScalars ℂ).comp
        toOriginal) := by
    apply Ideal.Quotient.algHom_ext ℂ
    apply MvPolynomial.algHom_ext
    intro i
    cases i with
    | none =>
      change reduction epsilonElement = closedAlgEquiv
        (CycleQ2GeometricSurfaceFirstOrder.reduction equation perturbation (toOriginal epsilonElement))
      rw [reduction_epsilon, toOriginal_epsilon]
      change (0 : SurfaceRing 57 1) = closedAlgEquiv (Ideal.Quotient.mk _ 0)
      rw [map_zero, map_zero]
    | some i =>
      change reduction (coordinate i) = closedAlgEquiv
        (CycleQ2GeometricSurfaceFirstOrder.reduction equation perturbation (toOriginal (coordinate i)))
      rw [toOriginal_coordinate]
      change rawReduction (X (some i)) =
        closedEquiv (Ideal.Quotient.mk _ (cubicMap (X i)))
      rw [closedEquiv_polynomial]
      simp [rawReduction, rawVariable]
  exact AlgHom.congr_fun h x

def epsilonCoefficient : SurfaceRing 57 1 →ₗ[ℂ] GradedDeformation :=
  fromOriginal.toLinearMap.comp
    (((CycleQ2GeometricSurfaceFirstOrder.epsilon equation perturbation).restrictScalars ℂ).comp
      closedAlgEquiv.symm.toLinearMap)

theorem epsilonCoefficient_apply (x : SurfaceRing 57 1) :
    epsilonCoefficient x = fromOriginal
      (CycleQ2GeometricSurfaceFirstOrder.epsilon equation perturbation (closedAlgEquiv.symm x)) := rfl

theorem toOriginal_epsilonCoefficient (x : SurfaceRing 57 1) :
    toOriginal (epsilonCoefficient x) =
      CycleQ2GeometricSurfaceFirstOrder.epsilon equation perturbation (closedAlgEquiv.symm x) := by
  rw [epsilonCoefficient_apply, toOriginal_fromOriginal]

theorem epsilonCoefficient_polynomial (p : WeightedPoly) :
    epsilonCoefficient (surfaceQuotient 57 1 p) = epsilonElement * polynomialInGraded p := by
  rw [epsilonCoefficient_apply, closedAlgEquiv_symm_polynomial, epsilon_mk]
  change dualToGraded (TrivSqZeroExt.inr (cubicMap p)) = _
  rw [dualToGraded_inr, cubicToGraded_polynomial]

theorem epsilonCoefficient_injective : Function.Injective epsilonCoefficient :=
  originalAlgEquiv.symm.injective.comp
    ((CycleQ2GeometricSurfaceFirstOrder.epsilon_injective equation perturbation equation_regular).comp
      closedAlgEquiv.symm.injective)

theorem reduction_epsilonCoefficient (x : SurfaceRing 57 1) :
    reduction (epsilonCoefficient x) = 0 := by
  rw [reduction_eq_original, toOriginal_epsilonCoefficient,
    CycleQ2GeometricSurfaceFirstOrder.reduction_epsilon, map_zero]

/-- Every element of the genuine reduction kernel has a unique original
epsilon coefficient; no formal-flatness hypothesis is assumed. -/
theorem reduction_zero_iff_epsilonCoefficient (z : GradedDeformation) :
    reduction z = 0 ↔ ∃ x : SurfaceRing 57 1, epsilonCoefficient x = z := by
  constructor
  · intro hz
    have ho : CycleQ2GeometricSurfaceFirstOrder.reduction equation perturbation (toOriginal z) = 0 := by
      apply closedAlgEquiv.injective
      rw [map_zero, ← reduction_eq_original, hz]
    obtain ⟨x,hx⟩ := (CycleQ2GeometricSurfaceFirstOrder.reduction_eq_zero_iff
      equation perturbation (toOriginal z)).mp ho
    refine ⟨closedAlgEquiv x, ?_⟩
    rw [epsilonCoefficient_apply, AlgEquiv.symm_apply_apply, hx, fromOriginal_toOriginal]
  · rintro ⟨x,rfl⟩
    exact reduction_epsilonCoefficient x

theorem closedAlgEquiv_symm_reduction (z : GradedDeformation) :
    closedAlgEquiv.symm (reduction z) =
      CycleQ2GeometricSurfaceFirstOrder.reduction equation perturbation (toOriginal z) := by
  apply closedAlgEquiv.injective
  rw [AlgEquiv.apply_symm_apply]
  exact reduction_eq_original z

/-- The actual multiplication action on epsilon coefficients is the
actual reduced surface multiplication. -/
theorem mul_epsilonCoefficient (z : GradedDeformation) (x : SurfaceRing 57 1) :
    epsilonCoefficient (reduction z * x) = z * epsilonCoefficient x := by
  apply originalAlgEquiv.injective
  change toOriginal (epsilonCoefficient _) = toOriginal (z * epsilonCoefficient x)
  rw [toOriginal_epsilonCoefficient, map_mul toOriginal, toOriginal_epsilonCoefficient,
    map_mul, closedAlgEquiv_symm_reduction]
  exact (CycleQ2GeometricSurfaceFirstOrder.mul_epsilon equation perturbation
    (toOriginal z) (closedAlgEquiv.symm x)).symm

theorem epsilonCoefficient_mul_epsilonCoefficient (x y : SurfaceRing 57 1) :
    epsilonCoefficient x * epsilonCoefficient y = 0 := by
  rw [← mul_epsilonCoefficient, reduction_epsilonCoefficient, zero_mul, map_zero]

/-- Epsilon has weight zero in the original degree-six perturbation. -/
theorem epsilonCoefficient_homogeneous {n : ℕ} {x : SurfaceRing 57 1}
    (hx : x ∈ surfaceGrade 57 1 n) : epsilonCoefficient x ∈ deformationGrade n := by
  obtain ⟨p,hp,rfl⟩ := hx
  change epsilonCoefficient (surfaceQuotient 57 1 p) ∈ deformationGrade n
  rw [epsilonCoefficient_polynomial]
  simpa only [zero_add, polynomialInGraded, AlgHom.comp_apply] using
    SetLike.mul_mem_graded epsilonElement_mem_grade
    (quotientMap_mem_grade (includePolynomial_homogeneous hp))

theorem epsilonCoefficient_one : epsilonCoefficient 1 = epsilonElement := by
  have h := epsilonCoefficient_polynomial 1
  simpa only [map_one, mul_one] using h

theorem epsilonCoefficient_reduction (z : GradedDeformation) :
    epsilonCoefficient (reduction z) = epsilonElement * z := by
  have h := mul_epsilonCoefficient z 1
  simpa only [mul_one, epsilonCoefficient_one, mul_comm z] using h

/-- Faithfulness identifies the annihilator of the original epsilon
with the actual reduction kernel, before localization or projection. -/
theorem epsilon_mul_eq_zero_iff (z : GradedDeformation) :
    epsilonElement * z = 0 ↔ reduction z = 0 := by
  rw [← epsilonCoefficient_reduction]
  exact epsilonCoefficient_injective.eq_iff' (map_zero epsilonCoefficient)

theorem kernel_mul_zero (x y : GradedDeformation)
    (hx : reduction x = 0) (hy : reduction y = 0) : x * y = 0 := by
  obtain ⟨a,rfl⟩ := (reduction_zero_iff_epsilonCoefficient x).mp hx
  obtain ⟨b,rfl⟩ := (reduction_zero_iff_epsilonCoefficient y).mp hy
  exact epsilonCoefficient_mul_epsilonCoefficient a b

theorem reduction_kernel_principal :
    RingHom.ker reduction.toRingHom = Ideal.span ({epsilonElement} : Set GradedDeformation) := by
  ext z
  change reduction z = 0 ↔ _
  constructor
  · intro hz
    obtain ⟨x,hx⟩ := (reduction_zero_iff_epsilonCoefficient z).mp hz
    obtain ⟨y,hy⟩ := reduction_surjective x
    apply Ideal.mem_span_singleton'.mpr
    refine ⟨y, ?_⟩
    rw [mul_comm, ← epsilonCoefficient_reduction, hy, hx]
  · intro hz
    obtain ⟨y,rfl⟩ := Ideal.mem_span_singleton'.mp hz
    rw [map_mul, reduction_epsilon, mul_zero]

local instance reductionAlgebra : Algebra GradedDeformation (SurfaceRing 57 1) :=
  reduction.toAlgebra

def epsilonKernelEquiv : SurfaceRing 57 1 ≃ₗ[GradedDeformation] RingHom.ker reduction.toRingHom :=
  LinearEquiv.ofBijective
    (show SurfaceRing 57 1 →ₗ[GradedDeformation] RingHom.ker reduction.toRingHom from
      { toFun := fun x => ⟨epsilonCoefficient x, reduction_epsilonCoefficient x⟩
        map_add' := fun x y => Subtype.ext (epsilonCoefficient.map_add x y)
        map_smul' := fun r x => by
          apply Subtype.ext
          change epsilonCoefficient (reduction r * x) = r * epsilonCoefficient x
          exact mul_epsilonCoefficient r x })
    (by
      constructor
      · intro x y hxy
        exact epsilonCoefficient_injective (congrArg Subtype.val hxy)
      · rintro ⟨z,hz⟩
        obtain ⟨x,hx⟩ := (reduction_zero_iff_epsilonCoefficient z).mp hz
        exact ⟨x, Subtype.ext hx⟩)

end CycleQ2LiteralGradedReduction

end

#print axioms CycleQ2LiteralGradedReduction.reductionGraded
#print axioms CycleQ2LiteralGradedReduction.reduction_eq_original
#print axioms CycleQ2LiteralGradedReduction.epsilonCoefficient_homogeneous
#print axioms CycleQ2LiteralGradedReduction.epsilonKernelEquiv
