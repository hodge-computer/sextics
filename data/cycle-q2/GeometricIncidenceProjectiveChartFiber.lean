import Proposal.GeometricIncidenceChartFiberScheme

/-!
# Exact seed fibers of the original projective coordinate opens

Status: source-only proof draft. No elaboration or kernel replay was run.

The relative affine chart equivalence respects the original surfaceToBase.
Consequently it induces an isomorphism between their actual scheme
pullbacks along seedMap. Composing with the affine tensor comparison
identifies the seed fiber of each original projective coordinate open
with the spectrum of its original seed chart ring.

Both pullback projections are tracked. The map to the original
projective open is the spectrum of the exact specialization followed
by the inverse affine chart map. No global Proj fiber comparison,
covering, smoothness, or flatness premise is supplied here.

The geometric strategy is due to Ben Diamond and the collaborators cited
in solution.md. Prepared for fqlx with OpenAI ChatGPT assistance.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2IncidenceProjectiveChartFiber

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CycleQ2IncidencePolynomialJacobianBinding CycleQ2IncidenceEtaleParameter
  CycleQ2GeometricIncidenceProj CycleQ2IncidenceDehomogenizedChart
  CycleQ2IncidenceChartFiberScheme

attribute [local instance] CycleQ2IncidenceSeedFiber.seedAlgebra

def projectiveChartToParameters (i : Fin 4) :
    (familyCoordinatePatch incidencePoint i).toScheme ⟶
      Spec (CommRingCat.of ParameterAlgebra) :=
  (familyCoordinatePatch incidencePoint i).ι ≫ surfaceToBase incidencePoint

theorem familyCoordinateAffineChart_hom_overParameters (i : Fin 4) :
    (familyCoordinateAffineChart incidencePoint i).hom ≫ relativeChartToParameters i =
      projectiveChartToParameters i := by
  change (familyCoordinateAffineChart incidencePoint i).hom ≫
      Spec.map (CommRingCat.ofHom
        (algebraMap ParameterAlgebra (DehomogenizedRing incidencePoint i))) =
    (familyCoordinatePatch incidencePoint i).ι ≫ surfaceToBase incidencePoint
  rw [← familyCoordinateAffineChart_overBase incidencePoint i]
  simp only [Iso.hom_inv_id_assoc]

/-- The actual seed pullback of the original projective basic open. -/
abbrev ProjectiveChartSeedFiber (i : Fin 4) :=
  pullback seedParameterMorphism (projectiveChartToParameters i)

/-- Changing the chart through its existing isomorphism over the base
preserves the actual scheme pullback. -/
def projectiveChartFiberToAffineFiber (i : Fin 4) :
    ProjectiveChartSeedFiber i ≅ AffineChartSeedFiber i :=
  asIso (pullback.map seedParameterMorphism (projectiveChartToParameters i)
    seedParameterMorphism (relativeChartToParameters i)
    (𝟙 _) (familyCoordinateAffineChart incidencePoint i).hom (𝟙 _)
    (by simp) (by simpa using (familyCoordinateAffineChart_hom_overParameters i).symm))

@[reassoc] theorem projectiveChartFiberToAffineFiber_hom_snd (i : Fin 4) :
    (projectiveChartFiberToAffineFiber i).hom ≫
      pullback.snd seedParameterMorphism (relativeChartToParameters i) =
        pullback.snd seedParameterMorphism (projectiveChartToParameters i) ≫
          (familyCoordinateAffineChart incidencePoint i).hom := by
  simp [projectiveChartFiberToAffineFiber]

@[reassoc] theorem projectiveChartFiberToAffineFiber_hom_fst (i : Fin 4) :
    (projectiveChartFiberToAffineFiber i).hom ≫
      pullback.fst seedParameterMorphism (relativeChartToParameters i) =
        pullback.fst seedParameterMorphism (projectiveChartToParameters i) := by
  simp [projectiveChartFiberToAffineFiber]

@[reassoc] theorem projectiveChartFiberToAffineFiber_inv_snd (i : Fin 4) :
    (projectiveChartFiberToAffineFiber i).inv ≫
      pullback.snd seedParameterMorphism (projectiveChartToParameters i) =
        pullback.snd seedParameterMorphism (relativeChartToParameters i) ≫
          (familyCoordinateAffineChart incidencePoint i).inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, projectiveChartFiberToAffineFiber_hom_snd]
  simp

@[reassoc] theorem projectiveChartFiberToAffineFiber_inv_fst (i : Fin 4) :
    (projectiveChartFiberToAffineFiber i).inv ≫
      pullback.fst seedParameterMorphism (projectiveChartToParameters i) =
        pullback.fst seedParameterMorphism (relativeChartToParameters i) := by
  rw [Iso.inv_comp_eq]
  exact (projectiveChartFiberToAffineFiber_hom_fst i).symm

/-- The exact scheme-theoretic seed fiber of the original coordinate open. -/
def projectiveChartSeedFiberIso (i : Fin 4) :
    ProjectiveChartSeedFiber i ≅
      Spec (CommRingCat.of (DehomogenizedRing (seedPoint (57 : ℂ) Complex.I) i)) :=
  projectiveChartFiberToAffineFiber i ≪≫ affineChartSeedFiberIso i

@[reassoc] theorem projectiveChartSeedFiberIso_inv_snd (i : Fin 4) :
    (projectiveChartSeedFiberIso i).inv ≫
      pullback.snd seedParameterMorphism (projectiveChartToParameters i) =
        Spec.map (CommRingCat.ofHom (seedChartSpecialization i)) ≫
          (familyCoordinateAffineChart incidencePoint i).inv := by
  change ((affineChartSeedFiberIso i).inv ≫
      (projectiveChartFiberToAffineFiber i).inv) ≫
        pullback.snd seedParameterMorphism (projectiveChartToParameters i) = _
  rw [Category.assoc, projectiveChartFiberToAffineFiber_inv_snd,
    ← Category.assoc, affineChartSeedFiberIso_inv_snd]

@[reassoc] theorem projectiveChartSeedFiberIso_inv_fst (i : Fin 4) :
    (projectiveChartSeedFiberIso i).inv ≫
      pullback.fst seedParameterMorphism (projectiveChartToParameters i) =
        literalChartToComplex i := by
  change ((affineChartSeedFiberIso i).inv ≫
      (projectiveChartFiberToAffineFiber i).inv) ≫
        pullback.fst seedParameterMorphism (projectiveChartToParameters i) = _
  rw [Category.assoc, projectiveChartFiberToAffineFiber_inv_fst,
    affineChartSeedFiberIso_inv_fst]

end CycleQ2IncidenceProjectiveChartFiber

end

#print axioms CycleQ2IncidenceProjectiveChartFiber.projectiveChartSeedFiberIso
#print axioms CycleQ2IncidenceProjectiveChartFiber.projectiveChartSeedFiberIso_inv_snd
#print axioms CycleQ2IncidenceProjectiveChartFiber.projectiveChartSeedFiberIso_inv_fst
