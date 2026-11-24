import Proposal.GeometricLiteralNativeTransitionNaturality

/-!
# The original epsilon normalization on the actual product localizations

The ordinary intersection reduction has exactly the original epsilon
annihilator. Its faithful coefficient equivalence is constructed with
the actual reduced module action. The genuine degree-zero projection
preserves it. Transport of the original cone coefficient map has the
same normalization, including all possible localization torsion.

Prepared for fqlx with OpenAI ChatGPT assistance; see solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralIntersectionEpsilonTransport

open HomogeneousLocalization CycleQ2GeometricSeedNormalIdeals
  CycleQ2LiteralGradedDeformation CycleQ2LiteralGradedDeformationEquiv
  CycleQ2LiteralGradedReduction CycleQ2LiteralProjectiveDeformation
  CycleQ2LiteralProjectiveIntersections CycleQ2LiteralProjectiveIntersectionKernel
  CycleQ2LiteralProjectiveIntersectionProjection CycleQ2LiteralProjectiveIntersectionRestrictions
  CycleQ2LiteralProjectiveIntersectionSplittings CycleQ2LiteralConeIntersectionTransport
  CycleQ2GradedLocalizationProjection CycleQ2LiteralCartierTransitionBinding
  CycleQ2LiteralCartierOverlapSplittings

attribute [local instance] CycleQ2LiteralCartierTransitionBinding.cubicSelfModule
  CycleQ2LiteralCartierTransitionBinding.cubicOppositeModule
  CycleQ2LiteralCartierTransitionBinding.cubicCentralScalar
  CycleQ2LiteralCartierTransitionBinding.cubicSmulCommClass
  CycleQ2GeometricSurfaceFirstOrder.reducedAlgebra
  CycleQ2GeometricKernelLocalization.localReductionAlgebra
  CycleQ2LiteralCartierSplittings.complexReductionTower
  CycleQ2LiteralCartierOverlapSplittings.baseReductionAlgebra

def ordinaryEpsilon (s : Finset Vertex) : ThickCone s :=
  algebraMap GradedDeformation (ThickCone s) epsilonElement

theorem ordinaryEpsilon_native (s : Finset Vertex) :
    ordinaryEpsilon s = (nativeEpsilon s).val := (nativeEpsilon_val s).symm

theorem ordinaryEpsilon_mul_eq_zero_iff (s : Finset Vertex) (x : ThickCone s) :
    ordinaryEpsilon s * x = 0 ↔ ordinaryReduction s x = 0 := by
  obtain ⟨n,p,rfl⟩ := exists_fraction (thickProduct s) x
  change algebraMap GradedDeformation (ThickCone s) epsilonElement *
    IsLocalization.mk' (ThickCone s) p (powerDenominator (thickProduct s) n) = 0 ↔ _
  rw [IsLocalization.mul_mk'_eq_mk'_of_mul, IsLocalization.mk'_eq_zero_iff,
    ordinaryReduction_fraction_eq_zero_iff]
  constructor
  · rintro ⟨⟨b,hb⟩,hz⟩
    obtain ⟨k,rfl⟩ := hb
    refine ⟨k, (epsilon_mul_eq_zero_iff _).mp ?_⟩
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hz
  · rintro ⟨k,hk⟩
    refine ⟨⟨thickProduct s ^ k,
      Submonoid.pow_mem _ (Submonoid.mem_powers _) _⟩, ?_⟩
    have hz := (epsilon_mul_eq_zero_iff _).mpr hk
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hz

theorem ordinaryReduction_epsilon (s : Finset Vertex) :
    ordinaryReduction s (ordinaryEpsilon s) = 0 := by
  rw [ordinaryEpsilon_native, ordinaryReduction_val, nativeReduction_epsilon, val_zero]

def ordinaryLift (s : Finset Vertex) (x : ClosedCone s) : ThickCone s :=
  (ordinaryReduction_surjective s x).choose

theorem ordinaryLift_reduction (s : Finset Vertex) (x : ClosedCone s) :
    ordinaryReduction s (ordinaryLift s x) = x := (ordinaryReduction_surjective s x).choose_spec

def ordinaryCoefficient (s : Finset Vertex) (x : ClosedCone s) : ThickCone s :=
  ordinaryEpsilon s * ordinaryLift s x

theorem ordinaryCoefficient_of_reduction (s : Finset Vertex) (z : ThickCone s) :
    ordinaryCoefficient s (ordinaryReduction s z) = ordinaryEpsilon s * z := by
  apply sub_eq_zero.mp
  rw [ordinaryCoefficient, ← mul_sub, ordinaryEpsilon_mul_eq_zero_iff,
    map_sub, ordinaryLift_reduction, sub_self]

theorem ordinaryCoefficient_reduction (s : Finset Vertex) (x : ClosedCone s) :
    ordinaryReduction s (ordinaryCoefficient s x) = 0 := by
  rw [ordinaryCoefficient, map_mul, ordinaryReduction_epsilon, zero_mul]

local instance ordinaryReductionAlgebra (s : Finset Vertex) : Algebra (ThickCone s) (ClosedCone s) :=
  (ordinaryReduction s).toAlgebra

def ordinaryCoefficientLinear (s : Finset Vertex) : ClosedCone s →ₗ[ThickCone s] ThickCone s where
  toFun := ordinaryCoefficient s
  map_add' x y := by
    obtain ⟨u,rfl⟩ := ordinaryReduction_surjective s x
    obtain ⟨v,rfl⟩ := ordinaryReduction_surjective s y
    rw [← map_add, ordinaryCoefficient_of_reduction, ordinaryCoefficient_of_reduction,
      ordinaryCoefficient_of_reduction, mul_add]
  map_smul' z x := by
    obtain ⟨u,rfl⟩ := ordinaryReduction_surjective s x
    change ordinaryCoefficient s (ordinaryReduction s z * ordinaryReduction s u) =
      z * ordinaryCoefficient s (ordinaryReduction s u)
    rw [← map_mul, ordinaryCoefficient_of_reduction, ordinaryCoefficient_of_reduction]
    ring

theorem ordinaryCoefficient_injective (s : Finset Vertex) : Function.Injective (ordinaryCoefficient s) := by
  intro x y hxy
  apply sub_eq_zero.mp
  obtain ⟨u,hu⟩ := ordinaryReduction_surjective s (x - y)
  rw [← hu]
  apply (ordinaryEpsilon_mul_eq_zero_iff s u).mp
  rw [← ordinaryCoefficient_of_reduction, hu]
  change ordinaryCoefficientLinear s (x - y) = 0
  rw [map_sub]
  exact sub_eq_zero.mpr hxy

def ordinaryKernelEquiv (s : Finset Vertex) :
    ClosedCone s ≃ₗ[ThickCone s] RingHom.ker (ordinaryReduction s) :=
  LinearEquiv.ofBijective
    ((ordinaryCoefficientLinear s).codRestrict _ (ordinaryCoefficient_reduction s)) (by
      constructor
      · intro x y hxy
        exact ordinaryCoefficient_injective s (congrArg Subtype.val hxy)
      · rintro ⟨z,hz⟩
        have hm : z ∈ Ideal.span ({ordinaryEpsilon s} : Set (ThickCone s)) := by
          change z ∈ Ideal.span ({algebraMap GradedDeformation (ThickCone s) epsilonElement} : Set (ThickCone s))
          rw [← ordinaryKernel_principal]
          exact hz
        obtain ⟨u,hu⟩ := Ideal.mem_span_singleton'.mp hm
        refine ⟨ordinaryReduction s u, Subtype.ext ?_⟩
        change ordinaryCoefficient s (ordinaryReduction s u) = z
        rw [ordinaryCoefficient_of_reduction, mul_comm, hu])

theorem projection_ordinaryCoefficient (s : Finset Vertex) (x : ClosedCone s) :
    thickProjection s (ordinaryCoefficient s x) =
      CycleQ2LiteralProjectiveIntersectionKernel.epsilonCoefficient s (closedProjection s x) := by
  obtain ⟨z,rfl⟩ := ordinaryReduction_surjective s x
  rw [ordinaryCoefficient_of_reduction, ordinaryEpsilon_native, ← projection_reduction,
    CycleQ2LiteralProjectiveIntersectionKernel.epsilonCoefficient_of_reduction]
  exact degreeZero_mul_homogeneous deformationGrade (thickProduct_homogeneous s) (nativeEpsilon s) z

theorem ordinaryEpsilon_restrict {s t : Finset Vertex} (hst : s ⊆ t) :
    thickConeRestriction hst (ordinaryEpsilon s) = ordinaryEpsilon t := thickConeRestriction_base hst epsilonElement

theorem ordinaryCoefficient_restrict {s t : Finset Vertex} (hst : s ⊆ t) (x : ClosedCone s) :
    thickConeRestriction hst (ordinaryCoefficient s x) =
      ordinaryCoefficient t (closedConeRestriction hst x) := by
  obtain ⟨z,rfl⟩ := ordinaryReduction_surjective s x
  rw [ordinaryCoefficient_of_reduction, map_mul, ordinaryEpsilon_restrict,
    ← ordinaryReduction_restrict, ordinaryCoefficient_of_reduction]

theorem transported_epsilon_one (s : Finset Vertex) (t : Finset (Fin 4)) (ht : Admits s t) :
    thickMap s t ht (CycleQ2GeometricSquareZeroSplittings.epsilon
      (CycleQ2LiteralCartierSplittings.kernelEquiv t) 1) = ordinaryEpsilon s := by
  have hb := CycleQ2GeometricSurfaceFirstOrder.localKernelEquiv_base
    equation perturbation (CycleQ2LiteralCartierSplittings.denominator t) equation_regular (1 : ClosedBase)
  rw [map_one] at hb
  change thickMap s t ht ((CycleQ2GeometricSurfaceFirstOrder.localKernelEquiv
    equation perturbation (CycleQ2LiteralCartierSplittings.denominator t) equation_regular) 1).val = _
  rw [hb]
  change thickMap s t ht (@Algebra.algebraMap ThickBase (OldThick t)
    (inferInstance : CommSemiring ThickBase) (inferInstance : Semiring (OldThick t)) inferInstance
      (CycleQ2GeometricSurfaceFirstOrder.epsilon equation perturbation 1)) = _
  rw [thickMap_base]
  change algebraMap GradedDeformation (ThickCone s)
    (fromOriginal (CycleQ2GeometricSurfaceFirstOrder.epsilon equation perturbation 1)) = _
  have he := CycleQ2LiteralGradedReduction.epsilonCoefficient_one
  change fromOriginal (CycleQ2GeometricSurfaceFirstOrder.epsilon equation perturbation
    (closedAlgEquiv.symm 1)) = epsilonElement at he
  rw [map_one] at he
  rw [he]
  rfl

theorem transported_epsilon (s : Finset Vertex) (t : Finset (Fin 4)) (ht : Admits s t)
    (x : OldClosed t) :
    thickMap s t ht (CycleQ2GeometricSquareZeroSplittings.epsilon
      (CycleQ2LiteralCartierSplittings.kernelEquiv t) x) = ordinaryCoefficient s (closedMap s t ht x) := by
  obtain ⟨z,rfl⟩ := CycleQ2LiteralCartierSplittings.reduction_surjective t x
  have he := (CycleQ2GeometricSquareZeroSplittings.mul_epsilon
    (CycleQ2LiteralCartierSplittings.kernelEquiv t) z 1).symm
  rw [mul_one] at he
  rw [he, map_mul, transported_epsilon_one]
  change thickMap s t ht z * ordinaryEpsilon s =
    ordinaryCoefficient s (closedMap s t ht (reductionMap t z))
  rw [← reduction_thickMap, ordinaryCoefficient_of_reduction]
  exact mul_comm _ _

theorem projected_transported_epsilon (s : Finset Vertex) (t : Finset (Fin 4)) (ht : Admits s t)
    (x : OldClosed t) :
    thickProjection s (thickMap s t ht (CycleQ2GeometricSquareZeroSplittings.epsilon
      (CycleQ2LiteralCartierSplittings.kernelEquiv t) x)) =
      CycleQ2LiteralProjectiveIntersectionKernel.epsilonCoefficient s (closedProjection s (closedMap s t ht x)) := by
  rw [transported_epsilon, projection_ordinaryCoefficient]

end CycleQ2LiteralIntersectionEpsilonTransport

end

#print axioms CycleQ2LiteralIntersectionEpsilonTransport.ordinaryKernelEquiv
#print axioms CycleQ2LiteralIntersectionEpsilonTransport.projection_ordinaryCoefficient
#print axioms CycleQ2LiteralIntersectionEpsilonTransport.transported_epsilon
