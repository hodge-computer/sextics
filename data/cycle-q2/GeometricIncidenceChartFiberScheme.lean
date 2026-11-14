import Proposal.GeometricIncidenceChartSeedFiber
import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# The exact affine scheme fiber of each incidence surface chart

Status: source-only proof draft. No elaboration or kernel replay was run.

The existing tensor-quotient algebra equivalence identifies the actual
pullback of the chart coefficient morphism along the original seedMap
with the spectrum of the original seed chart ring. The pullback is
written in seed-first order, so its second projection is the projection
to the original incidence chart. Both projections are identified exactly.

The specialization homomorphism preserves the original affine variables
and sends each parameter coefficient through seedMap. No flatness or
global projective fiber comparison is assumed or asserted here.

The geometric strategy is due to Ben Diamond and the collaborators cited
in solution.md. Prepared for fqlx with OpenAI ChatGPT assistance.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2IncidenceChartFiberScheme

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial
open scoped TensorProduct
open CycleQ2IncidenceUniversalChart CycleQ2IncidencePolynomialJacobianBinding
  CycleQ2IncidenceEtaleParameter CycleQ2IncidenceDehomogenizedChart
  CycleQ2IncidenceChartSeedFiber

attribute [local instance] CycleQ2IncidenceSeedFiber.seedAlgebra

def seedParameterMorphism :
    Spec (CommRingCat.of ℂ) ⟶ Spec (CommRingCat.of ParameterAlgebra) :=
  Spec.map (CommRingCat.ofHom seedMap)

def relativeChartToParameters (i : Fin 4) :
    Spec (CommRingCat.of (DehomogenizedRing incidencePoint i)) ⟶
      Spec (CommRingCat.of ParameterAlgebra) :=
  Spec.map (CommRingCat.ofHom
    (algebraMap ParameterAlgebra (DehomogenizedRing incidencePoint i)))

def literalChartToComplex (i : Fin 4) :
    Spec (CommRingCat.of (DehomogenizedRing (seedPoint (57 : ℂ) Complex.I) i)) ⟶
      Spec (CommRingCat.of ℂ) :=
  Spec.map (CommRingCat.ofHom
    (algebraMap ℂ (DehomogenizedRing (seedPoint (57 : ℂ) Complex.I) i)))

/-- The original chart specialization, using the proved tensor equivalence. -/
def seedChartSpecialization (i : Fin 4) :
    DehomogenizedRing incidencePoint i →+*
      DehomogenizedRing (seedPoint (57 : ℂ) Complex.I) i :=
  (seedChartFiberEquiv i).toRingHom.comp
    (Algebra.TensorProduct.includeRight (R := ParameterAlgebra) (A := ℂ)
      (B := DehomogenizedRing incidencePoint i)).toRingHom

@[simp] theorem seedChartSpecialization_polynomial (i : Fin 4)
    (p : ChartPolynomial ParameterAlgebra) :
    seedChartSpecialization i (dehomogenizedMap incidencePoint i p) =
      dehomogenizedMap (seedPoint (57 : ℂ) Complex.I) i (MvPolynomial.map seedMap p) := by
  change seedChartFiberEquiv i
    (1 ⊗ₜ[ParameterAlgebra] dehomogenizedMap incidencePoint i p) = _
  rw [seedChartFiberEquiv_tmul, one_smul]

@[simp] theorem seedChartSpecialization_variable (i : Fin 4) (j : Option (Fin 3)) :
    seedChartSpecialization i (dehomogenizedMap incidencePoint i (X j)) =
      dehomogenizedMap (seedPoint (57 : ℂ) Complex.I) i (X j) := by
  rw [seedChartSpecialization_polynomial, MvPolynomial.map_X]

@[simp] theorem seedChartSpecialization_coefficient (i : Fin 4) (a : ParameterAlgebra) :
    seedChartSpecialization i
      (algebraMap ParameterAlgebra (DehomogenizedRing incidencePoint i) a) =
        algebraMap ℂ (DehomogenizedRing (seedPoint (57 : ℂ) Complex.I) i) (seedMap a) := by
  change seedChartFiberEquiv i
    (1 ⊗ₜ[ParameterAlgebra]
      algebraMap ParameterAlgebra (DehomogenizedRing incidencePoint i) a) = _
  exact seedChartFiberEquiv_coefficient i a

theorem seedChartSpecialization_dehomogenizedPolynomial (i : Fin 4)
    (p : MvPolynomial (Fin 5) ParameterAlgebra) :
    seedChartSpecialization i
      (dehomogenizedMap incidencePoint i (dehomogenize i p)) =
        dehomogenizedMap (seedPoint (57 : ℂ) Complex.I) i
          (dehomogenize i (MvPolynomial.map seedMap p)) := by
  rw [seedChartSpecialization_polynomial, map_dehomogenize]

/-- This is the actual scheme pullback, in seed-first order. -/
abbrev AffineChartSeedFiber (i : Fin 4) :=
  pullback seedParameterMorphism (relativeChartToParameters i)

/-- The tensor construction is the scheme-theoretic seed fiber of the
original affine chart coefficient map. -/
def affineChartSeedFiberIso (i : Fin 4) :
    AffineChartSeedFiber i ≅
      Spec (CommRingCat.of (DehomogenizedRing (seedPoint (57 : ℂ) Complex.I) i)) :=
  pullbackSpecIso ParameterAlgebra ℂ (DehomogenizedRing incidencePoint i) ≪≫
    Scheme.Spec.mapIso (seedChartFiberEquiv i).toRingEquiv.toCommRingCatIso.symm.op

/-- The projection to the original chart is the exact specialization map. -/
@[reassoc] theorem affineChartSeedFiberIso_inv_snd (i : Fin 4) :
    (affineChartSeedFiberIso i).inv ≫
      pullback.snd seedParameterMorphism (relativeChartToParameters i) =
        Spec.map (CommRingCat.ofHom (seedChartSpecialization i)) := by
  change (Spec.map (CommRingCat.ofHom (seedChartFiberEquiv i).toRingHom) ≫
      (pullbackSpecIso ParameterAlgebra ℂ (DehomogenizedRing incidencePoint i)).inv) ≫
        pullback.snd _ _ = _
  rw [Category.assoc, pullbackSpecIso_inv_snd, ← Spec.map_comp]
  rfl

/-- The projection to the base-change field is its canonical coefficient map. -/
@[reassoc] theorem affineChartSeedFiberIso_inv_fst (i : Fin 4) :
    (affineChartSeedFiberIso i).inv ≫
      pullback.fst seedParameterMorphism (relativeChartToParameters i) =
        literalChartToComplex i := by
  change (Spec.map (CommRingCat.ofHom (seedChartFiberEquiv i).toRingHom) ≫
      (pullbackSpecIso ParameterAlgebra ℂ (DehomogenizedRing incidencePoint i)).inv) ≫
        pullback.fst _ _ = _
  rw [Category.assoc, pullbackSpecIso_inv_fst', ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro c
  exact (seedChartFiberEquiv i).commutes c

@[reassoc] theorem affineChartSeedFiberIso_hom_snd (i : Fin 4) :
    (affineChartSeedFiberIso i).hom ≫
      Spec.map (CommRingCat.ofHom (seedChartSpecialization i)) =
        pullback.snd seedParameterMorphism (relativeChartToParameters i) := by
  rw [← affineChartSeedFiberIso_inv_snd, Iso.hom_inv_id_assoc]

@[reassoc] theorem affineChartSeedFiberIso_hom_fst (i : Fin 4) :
    (affineChartSeedFiberIso i).hom ≫ literalChartToComplex i =
      pullback.fst seedParameterMorphism (relativeChartToParameters i) := by
  rw [← affineChartSeedFiberIso_inv_fst, Iso.hom_inv_id_assoc]

end CycleQ2IncidenceChartFiberScheme

end

#print axioms CycleQ2IncidenceChartFiberScheme.affineChartSeedFiberIso
#print axioms CycleQ2IncidenceChartFiberScheme.affineChartSeedFiberIso_inv_snd
#print axioms CycleQ2IncidenceChartFiberScheme.affineChartSeedFiberIso_inv_fst
