import Proposal.GeometricRelativeConstantSection
import Proposal.GeometricSpecializedProjectiveCurve

/-!
# The exact seed fiber of the relative constant-section quotient

The fixed complex vector is retained over the original incidence algebra.
Its quotient is then tensored along the actual seedMap. The resulting
complex algebra is identified with the existing SpecializedCurveRing of
the literal seed and the same vector, preserving all geometric variables
and the original coefficient map.

This is a tensor-product fiber theorem, not only a specialization map.
It does not yet identify the projective scheme fiber, prove nonemptiness,
or prove that the curve morphism is flat over the incidence parameters.

Source-only draft: no Lean elaboration or kernel replay has been run.
Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md for
attribution of the geometric route and the protected certificate gap.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2RelativeConstantCurveFiber

open MvPolynomial
open scoped TensorProduct
open CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations
  CycleQ2IncidenceUniversalChart CycleQ2IncidenceImageLine
  CycleQ2IncidenceGenericPointSemantics
  CycleQ2GeometricIncidenceProj CycleQ2IncidenceEtaleParameter
  CycleQ2IncidencePolynomialJacobianBinding CycleQ2IncidenceChartSeedFiber
  CycleQ2IncidenceSeedFiber CycleQ2RegularSeedSection
  CycleQ2SpecializedSectionIdeal CycleQ2SpecializedProjectiveCurve
  CycleQ2RelativeConstantSection
open CycleQ2SeedTrace CycleQ2NormalConnecting CycleQ2GeometricSeedNormalIdeals
  CycleQ2ConormalJacobian

attribute [local instance] CycleQ2IncidenceSeedFiber.seedAlgebra

/-- The old full-polynomial seed ideal is the equation ideal of the
literal parameter point used by the regular seed-section construction. -/
theorem seedIdeal_eq_pointEquations :
    seedIdeal = pointEquations (seedPoint (57 : ℂ) Complex.I) := by
  change Ideal.span {smoothH Complex.I, smoothF (57 : ℂ) Complex.I} =
    Ideal.span {pointEquationH (seedPoint (57 : ℂ) Complex.I),
      pointEquationF (seedPoint (57 : ℂ) Complex.I)}
  rw [literal_pointEquationH, literal_pointEquationF]

/-- The existing actual tensor-product surface fiber, with its target
written as the exact PointSurface used by SpecializedCurveRing. -/
def literalSurfaceFiberEquiv :
    SeedFiber ≃ₐ[ℂ] PointSurface (seedPoint (57 : ℂ) Complex.I) :=
  seedFiberEquiv.trans (Ideal.quotientEquivAlgOfEq ℂ seedIdeal_eq_pointEquations)

@[simp] theorem literalSurfaceFiberEquiv_tmul
    (c : ℂ) (p : MvPolynomial (Fin 5) ParameterAlgebra) :
    literalSurfaceFiberEquiv
      (c ⊗ₜ[ParameterAlgebra] Ideal.Quotient.mk (pointEquations incidencePoint) p) =
        c • Ideal.Quotient.mk (pointEquations (seedPoint (57 : ℂ) Complex.I))
          (MvPolynomial.map seedMap p) := by
  rw [literalSurfaceFiberEquiv, AlgEquiv.trans_apply, seedFiberEquiv_tmul,
    map_smul, Ideal.quotientEquivAlgOfEq_mk]

def seedSurfaceSpecialization :
    PointSurface incidencePoint →+* PointSurface (seedPoint (57 : ℂ) Complex.I) :=
  literalSurfaceFiberEquiv.toRingHom.comp
    (Algebra.TensorProduct.includeRight (R := ParameterAlgebra) (A := ℂ)).toRingHom

@[simp] theorem seedSurfaceSpecialization_mk
    (p : MvPolynomial (Fin 5) ParameterAlgebra) :
    seedSurfaceSpecialization (Ideal.Quotient.mk (pointEquations incidencePoint) p) =
      Ideal.Quotient.mk (pointEquations (seedPoint (57 : ℂ) Complex.I))
        (MvPolynomial.map seedMap p) := by
  change literalSurfaceFiberEquiv
    (1 ⊗ₜ[ParameterAlgebra] Ideal.Quotient.mk (pointEquations incidencePoint) p) = _
  rw [literalSurfaceFiberEquiv_tmul, one_smul]

/-- Specialization retains the exact constant equation already proved
regular at the seed, with its coefficient vector unchanged. -/
theorem seedSurfaceSpecialization_equation (t : Fin 3 → ℂ) (i : Fin 3) :
    seedSurfaceSpecialization (relativeEquation incidencePoint t i) =
      constantEquation (seedPoint (57 : ℂ) Complex.I) t i := by
  change seedSurfaceSpecialization (Ideal.Quotient.mk (pointEquations incidencePoint)
    (relativeSectionPolynomial incidencePoint t i)) = _
  rw [seedSurfaceSpecialization_mk, relativeSectionPolynomial_seed]
  exact relativeEquation_complex (seedPoint (57 : ℂ) Complex.I) t i

theorem relativeSectionIdeal_seed (t : Fin 3 → ℂ) :
    (relativeSectionIdeal incidencePoint t).map seedSurfaceSpecialization =
      specializedSectionIdeal (seedPoint (57 : ℂ) Complex.I) t := by
  rw [relativeSectionIdeal, specializedSectionIdeal, Ideal.map_span]
  congr 1
  ext a
  constructor
  · rintro ⟨b, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, (seedSurfaceSpecialization_equation t i).symm⟩
  · rintro ⟨i, rfl⟩
    exact ⟨relativeEquation incidencePoint t i, ⟨i, rfl⟩,
      seedSurfaceSpecialization_equation t i⟩

def tensorRelativeSectionIdeal (t : Fin 3 → ℂ) : Ideal SeedFiber :=
  (relativeSectionIdeal incidencePoint t).map
    (Algebra.TensorProduct.includeRight (R := ParameterAlgebra) (A := ℂ))

theorem tensorRelativeSectionIdeal_map (t : Fin 3 → ℂ) :
    (tensorRelativeSectionIdeal t).map literalSurfaceFiberEquiv.toRingHom =
      specializedSectionIdeal (seedPoint (57 : ℂ) Complex.I) t := by
  rw [tensorRelativeSectionIdeal, Ideal.map_map]
  exact relativeSectionIdeal_seed t

abbrev RelativeCurveSeedFiber (t : Fin 3 → ℂ) :=
  ℂ ⊗[ParameterAlgebra] RelativeCurveRing incidencePoint t

/-- The actual tensor-product fiber of the relative quotient is the
existing specialized curve ring of the same literal seed and vector. -/
def relativeCurveSeedFiberEquiv (t : Fin 3 → ℂ) :
    RelativeCurveSeedFiber t ≃ₐ[ℂ]
      SpecializedCurveRing (seedPoint (57 : ℂ) Complex.I) t :=
  (Algebra.TensorProduct.tensorQuotientEquiv (R := ParameterAlgebra)
    ℂ (PointSurface incidencePoint) ℂ (relativeSectionIdeal incidencePoint t)).trans
      (Ideal.quotientEquivAlg (tensorRelativeSectionIdeal t)
        (specializedSectionIdeal (seedPoint (57 : ℂ) Complex.I) t)
        literalSurfaceFiberEquiv (tensorRelativeSectionIdeal_map t).symm)

@[simp] theorem relativeCurveSeedFiberEquiv_tmul (t : Fin 3 → ℂ)
    (c : ℂ) (a : PointSurface incidencePoint) :
    relativeCurveSeedFiberEquiv t
      (c ⊗ₜ[ParameterAlgebra] Ideal.Quotient.mk (relativeSectionIdeal incidencePoint t) a) =
        c • Ideal.Quotient.mk
          (specializedSectionIdeal (seedPoint (57 : ℂ) Complex.I) t)
          (seedSurfaceSpecialization a) := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [relativeCurveSeedFiberEquiv, AlgEquiv.trans_apply,
    Algebra.TensorProduct.tensorQuotientEquiv_apply_tmul,
    Ideal.quotientEquivAlg_mk, literalSurfaceFiberEquiv_tmul,
    seedSurfaceSpecialization_mk]
  exact (Ideal.Quotient.mkₐ ℂ
    (specializedSectionIdeal (seedPoint (57 : ℂ) Complex.I) t)).map_smul c _

@[simp] theorem relativeCurveSeedFiberEquiv_coordinate
    (t : Fin 3 → ℂ) (j : Fin 5) :
    relativeCurveSeedFiberEquiv t
      (1 ⊗ₜ[ParameterAlgebra] Ideal.Quotient.mk (relativeSectionIdeal incidencePoint t)
        (Ideal.Quotient.mk (pointEquations incidencePoint) (X j))) =
      Ideal.Quotient.mk (specializedSectionIdeal (seedPoint (57 : ℂ) Complex.I) t)
        (Ideal.Quotient.mk (pointEquations (seedPoint (57 : ℂ) Complex.I)) (X j)) := by
  rw [relativeCurveSeedFiberEquiv_tmul, seedSurfaceSpecialization_mk,
    MvPolynomial.map_X, one_smul]

@[simp] theorem relativeCurveSeedFiberEquiv_coefficient
    (t : Fin 3 → ℂ) (a : ParameterAlgebra) :
    relativeCurveSeedFiberEquiv t
      (1 ⊗ₜ[ParameterAlgebra] algebraMap ParameterAlgebra
        (RelativeCurveRing incidencePoint t) a) =
      algebraMap ℂ (SpecializedCurveRing (seedPoint (57 : ℂ) Complex.I) t)
        (seedMap a) := by
  change relativeCurveSeedFiberEquiv t
    (1 ⊗ₜ[ParameterAlgebra] Ideal.Quotient.mk (relativeSectionIdeal incidencePoint t)
      (Ideal.Quotient.mk (pointEquations incidencePoint) (C a))) = _
  rw [relativeCurveSeedFiberEquiv_tmul, seedSurfaceSpecialization_mk,
    MvPolynomial.map_C, one_smul]
  rfl

#print axioms seedSurfaceSpecialization_equation
#print axioms relativeSectionIdeal_seed
#print axioms relativeCurveSeedFiberEquiv
#print axioms relativeCurveSeedFiberEquiv_coordinate
#print axioms relativeCurveSeedFiberEquiv_coefficient

end CycleQ2RelativeConstantCurveFiber
end
