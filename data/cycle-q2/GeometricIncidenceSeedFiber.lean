import Proposal.GeometricEtaleIncidenceCurve
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.RingTheory.TensorProduct.MvPolynomial

/-!
# The actual incidence-surface coordinate ring after seed base change

The original surface coordinate ring is tensored along the actual seed
map out of ParameterAlgebra. The resulting algebra is identified with
the literal five-variable quotient by smoothH I and smoothF 57 I.
The equivalence preserves each original geometric coordinate and the
specialization of every coefficient. This is an actual tensor-product
comparison, rather than only a map from the total-space coordinate ring.

No projective-spectrum base-change isomorphism, smoothness of the total
family, or flatness neighborhood is asserted here.

The geometric strategy is due to Ben Diamond and the collaborators cited
in solution.md. Prepared for fqlx with OpenAI ChatGPT assistance.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2IncidenceSeedFiber

open MvPolynomial
open scoped TensorProduct
open CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations
  CycleQ2IncidenceUniversalChart CycleQ2IncidenceImageLine
  CycleQ2GeometricIncidenceProj CycleQ2IncidenceGenericPointSemantics
  CycleQ2IncidenceEtaleParameter CycleQ2IncidenceTraceFamily
open CycleQ2SeedTrace CycleQ2NormalConnecting CycleQ2GeometricSeedNormalIdeals
  CycleQ2ConormalJacobian

@[simp] theorem seedMap_complex (a : ℂ) :
    seedMap (algebraMap ℂ ParameterAlgebra a) = a := by
  rw [IsScalarTower.algebraMap_apply ℂ TraceRing ParameterAlgebra,
    seedMap_algebraMap]
  simp [seedEvaluation]

/-- The original seed specialization, with its complex-algebra structure
made explicit. -/
def seedAlgHom : ParameterAlgebra →ₐ[ℂ] ℂ where
  toRingHom := seedMap
  commutes' := seedMap_complex

/-- This specialization is installed only locally in this module. It
does not change global coefficient-algebra inference in other modules. -/
@[instance_reducible] def seedAlgebra : Algebra ParameterAlgebra ℂ := seedMap.toAlgebra

attribute [local instance] seedAlgebra

abbrev SurfacePolynomial := MvPolynomial (Fin 5) ParameterAlgebra
abbrev SeedPolynomial := MvPolynomial (Fin 5) ℂ

def seedIdeal : Ideal SeedPolynomial :=
  Ideal.span {smoothH Complex.I, smoothF (57 : ℂ) Complex.I}

abbrev SeedSurfaceRing := SeedPolynomial ⧸ seedIdeal

/-- The base change uses the retained seedMap, not an arbitrary complex
point or a specialization of a function field. -/
abbrev SeedFiber := ℂ ⊗[ParameterAlgebra] PointSurface incidencePoint

abbrev SeedTensorPolynomial := ℂ ⊗[ParameterAlgebra] SurfacePolynomial

local instance seedFiberCommRing : CommRing SeedFiber := inferInstance
local instance seedTensorCommRing : CommRing SeedTensorPolynomial := inferInstance
local instance seedSurfaceCommRing : CommRing SeedSurfaceRing := inferInstance

/-- Exact equality of the two original defining equations after taking
their coefficient images at the literal seed. -/
theorem seed_pointEquations :
    (pointEquations incidencePoint).map (MvPolynomial.map seedMap) = seedIdeal := by
  change (Ideal.span {pointEquationH incidencePoint, pointEquationF incidencePoint}).map
      (MvPolynomial.map seedMap) =
        Ideal.span {smoothH Complex.I, smoothF (57 : ℂ) Complex.I}
  rw [Ideal.map_span, Set.image_insert_eq, Set.image_singleton,
    CycleQ2EtaleIncidenceCurve.seed_cubic,
    CycleQ2EtaleIncidenceCurve.seed_sextic]

def seedPolynomialEquiv : SeedTensorPolynomial ≃ₐ[ℂ] SeedPolynomial :=
  MvPolynomial.algebraTensorAlgEquiv ParameterAlgebra ℂ

@[simp] theorem seedPolynomialEquiv_tmul (c : ℂ) (p : SurfacePolynomial) :
    seedPolynomialEquiv (c ⊗ₜ[ParameterAlgebra] p) =
      c • MvPolynomial.map seedMap p :=
  MvPolynomial.algebraTensorAlgEquiv_tmul ParameterAlgebra ℂ c p

def tensorEquationIdeal : Ideal SeedTensorPolynomial :=
  (pointEquations incidencePoint).map
    (Algebra.TensorProduct.includeRight (R := ParameterAlgebra) (A := ℂ))

theorem seedPolynomialEquiv_includeRight :
    seedPolynomialEquiv.toRingHom.comp
      (Algebra.TensorProduct.includeRight (R := ParameterAlgebra) (A := ℂ)
        (B := SurfacePolynomial)).toRingHom = MvPolynomial.map seedMap := by
  apply RingHom.ext
  intro p
  change seedPolynomialEquiv (1 ⊗ₜ[ParameterAlgebra] p) = MvPolynomial.map seedMap p
  rw [seedPolynomialEquiv_tmul, one_smul]

theorem tensorEquationIdeal_map :
    tensorEquationIdeal.map seedPolynomialEquiv.toRingHom = seedIdeal := by
  unfold tensorEquationIdeal
  exact (Ideal.map_map (I := pointEquations incidencePoint)
    (Algebra.TensorProduct.includeRight (R := ParameterAlgebra) (A := ℂ)
      (B := SurfacePolynomial)).toRingHom seedPolynomialEquiv.toRingHom).trans
      ((congrArg (fun f : SurfacePolynomial →+* SeedPolynomial =>
        (pointEquations incidencePoint).map f) seedPolynomialEquiv_includeRight).trans
          seed_pointEquations)

/-- The actual tensor-product fiber of the surface coordinate ring is
the original full-incidence seed quotient, as a complex algebra. -/
def seedFiberEquiv : SeedFiber ≃ₐ[ℂ] SeedSurfaceRing :=
  (Algebra.TensorProduct.tensorQuotientEquiv (R := ParameterAlgebra)
    ℂ SurfacePolynomial ℂ (pointEquations incidencePoint)).trans
      (Ideal.quotientEquivAlg tensorEquationIdeal seedIdeal seedPolynomialEquiv
        tensorEquationIdeal_map.symm)

/-- Both coefficient specialization and every geometric polynomial are
retained by the actual fiber equivalence. -/
@[simp] theorem seedFiberEquiv_tmul (c : ℂ) (p : SurfacePolynomial) :
    seedFiberEquiv
      (c ⊗ₜ[ParameterAlgebra] Ideal.Quotient.mk (pointEquations incidencePoint) p) =
        c • Ideal.Quotient.mk seedIdeal (MvPolynomial.map seedMap p) := by
  calc
    _ = Ideal.Quotient.mk seedIdeal
        (seedPolynomialEquiv (c ⊗ₜ[ParameterAlgebra] p)) := rfl
    _ = Ideal.Quotient.mk seedIdeal (c • MvPolynomial.map seedMap p) :=
      congrArg (Ideal.Quotient.mk seedIdeal) (seedPolynomialEquiv_tmul c p)
    _ = _ := (Ideal.Quotient.mkₐ ℂ seedIdeal).toLinearMap.map_smul c (MvPolynomial.map seedMap p)

@[simp] theorem seedFiberEquiv_coordinate (j : Fin 5) :
    seedFiberEquiv
      (1 ⊗ₜ[ParameterAlgebra]
        Ideal.Quotient.mk (pointEquations incidencePoint) (X j)) =
          Ideal.Quotient.mk seedIdeal (X j) := by
  rw [seedFiberEquiv_tmul, MvPolynomial.map_X, one_smul]

@[simp] theorem seedFiberEquiv_coefficient (a : ParameterAlgebra) :
    seedFiberEquiv
      (1 ⊗ₜ[ParameterAlgebra]
        Ideal.Quotient.mk (pointEquations incidencePoint) (C a)) =
          algebraMap ℂ SeedSurfaceRing (seedMap a) := by
  rw [seedFiberEquiv_tmul, MvPolynomial.map_C, one_smul]
  rfl

@[simp] theorem seedFiberEquiv_complex (c : ℂ) :
    seedFiberEquiv (algebraMap ℂ SeedFiber c) =
      algebraMap ℂ SeedSurfaceRing c := seedFiberEquiv.commutes c

@[simp] theorem seedFiberEquiv_symm_coordinate (j : Fin 5) :
    seedFiberEquiv.symm (Ideal.Quotient.mk seedIdeal (X j)) =
      1 ⊗ₜ[ParameterAlgebra]
        Ideal.Quotient.mk (pointEquations incidencePoint) (X j) := by
  apply seedFiberEquiv.injective
  rw [AlgEquiv.apply_symm_apply, seedFiberEquiv_coordinate]

/-- The full seed polynomial quotient is the same existing literal
surface ring used by the normal, Cartier, and smoothness constructions. -/
theorem seedIdeal_eq_literalSurfaceIdeal : seedIdeal = surfaceIdeal (57 : ℂ) 1 := by
  change equationsIdeal (smoothH Complex.I) (smoothF (57 : ℂ) Complex.I) = _
  exact (CycleQ2GeometricSurfaceCoordinates.surfaceIdeal_eq_seedIdeal 57).symm

def seedSurfaceRingEquiv : SeedSurfaceRing ≃ₐ[ℂ] SurfaceRing (57 : ℂ) 1 :=
  Ideal.quotientEquivAlgOfEq ℂ seedIdeal_eq_literalSurfaceIdeal

@[simp] theorem seedSurfaceRingEquiv_mk (p : SeedPolynomial) :
    seedSurfaceRingEquiv (Ideal.Quotient.mk seedIdeal p) =
      Ideal.Quotient.mk (surfaceIdeal (57 : ℂ) 1) p :=
  Ideal.quotientEquivAlgOfEq_mk ℂ seedIdeal_eq_literalSurfaceIdeal p

/-- The tensor-product fiber lands in the original literal surface ring,
with the original five geometric coordinates unchanged. -/
def seedFiberLiteralEquiv : SeedFiber ≃ₐ[ℂ] SurfaceRing (57 : ℂ) 1 :=
  seedFiberEquiv.trans seedSurfaceRingEquiv

@[simp] theorem seedFiberLiteralEquiv_coordinate (j : Fin 5) :
    seedFiberLiteralEquiv
      (1 ⊗ₜ[ParameterAlgebra]
        Ideal.Quotient.mk (pointEquations incidencePoint) (X j)) =
          Ideal.Quotient.mk (surfaceIdeal (57 : ℂ) 1) (X j) := by
  rw [seedFiberLiteralEquiv, AlgEquiv.trans_apply,
    seedFiberEquiv_coordinate, seedSurfaceRingEquiv_mk]

@[simp] theorem seedFiberLiteralEquiv_coefficient (a : ParameterAlgebra) :
    seedFiberLiteralEquiv
      (1 ⊗ₜ[ParameterAlgebra]
        Ideal.Quotient.mk (pointEquations incidencePoint) (C a)) =
          algebraMap ℂ (SurfaceRing (57 : ℂ) 1) (seedMap a) := by
  rw [seedFiberLiteralEquiv, AlgEquiv.trans_apply, seedFiberEquiv_coefficient]
  exact seedSurfaceRingEquiv.commutes (seedMap a)

#print axioms seed_pointEquations
#print axioms seedFiberEquiv
#print axioms seedFiberEquiv_coordinate
#print axioms seedFiberLiteralEquiv
#print axioms seedFiberLiteralEquiv_coordinate

end CycleQ2IncidenceSeedFiber
end
