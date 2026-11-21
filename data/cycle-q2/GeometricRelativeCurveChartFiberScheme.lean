import Proposal.GeometricRelativeCurveChartFiber
import Proposal.GeometricRelativeCurveChartScheme

/-!
# Scheme-theoretic seed fibers of the actual projective curve charts

The canonical tensor chart fiber is the scheme pullback along the
original seedMap. The already constructed affine chart isomorphism over
the original incidence base transports that pullback to the actual
coordinate open of the relative projective curve. Both projections are
computed, retaining the exact fixed vector and the original coefficient
specialization.

This is a local scheme fiber comparison on actual projective opens.
Global gluing, flatness of the curve family, and nonemptiness are not
asserted here.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md for
attribution of the geometric route and the protected certificate gap.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2RelativeCurveChartFiberScheme

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CycleQ2IncidencePolynomialJacobianBinding CycleQ2IncidenceEtaleParameter
  CycleQ2IncidenceChartFiberScheme CycleQ2RelativeConstantCurve
  CycleQ2RelativeCurveChart CycleQ2RelativeCurveChartFiber CycleQ2RelativeCurveChartScheme

attribute [local instance] CycleQ2IncidenceSeedFiber.seedAlgebra

variable (t : Fin 3 → ℂ) (i : Fin 4)

local instance incidenceCurveChartCommRing :
    CommRing (AffineCurveChart incidencePoint t i) := inferInstance
local instance seedCurveChartCommRing :
    CommRing (AffineCurveChart (seedPoint (57 : ℂ) Complex.I) t i) := inferInstance
local instance curveChartSeedFiberCommRing : CommRing (CurveChartSeedFiber t i) := inferInstance

def affineCurveChartToParameters :
    Spec (CommRingCat.of (AffineCurveChart incidencePoint t i)) ⟶
      Spec (CommRingCat.of ParameterAlgebra) :=
  Spec.map (CommRingCat.ofHom (R := ParameterAlgebra) (S := AffineCurveChart incidencePoint t i)
    (algebraMap ParameterAlgebra (AffineCurveChart incidencePoint t i)))

def seedAffineCurveChartToComplex :
    Spec (CommRingCat.of (AffineCurveChart (seedPoint (57 : ℂ) Complex.I) t i)) ⟶
      Spec (CommRingCat.of ℂ) :=
  Spec.map (CommRingCat.ofHom (R := ℂ)
    (S := AffineCurveChart (seedPoint (57 : ℂ) Complex.I) t i)
    (algebraMap ℂ (AffineCurveChart (seedPoint (57 : ℂ) Complex.I) t i)))

abbrev AffineCurveChartSeedFiberScheme :=
  pullback seedParameterMorphism (affineCurveChartToParameters t i)

def affineCurveChartSeedFiberIso :
    AffineCurveChartSeedFiberScheme t i ≅
      Spec (CommRingCat.of (AffineCurveChart (seedPoint (57 : ℂ) Complex.I) t i)) :=
  pullbackSpecIso ParameterAlgebra ℂ (AffineCurveChart incidencePoint t i) ≪≫
    Scheme.Spec.mapIso (curveChartSeedFiberEquiv t i).toRingEquiv.toCommRingCatIso.symm.op

@[reassoc] theorem affineCurveChartSeedFiberIso_inv_snd :
    (affineCurveChartSeedFiberIso t i).inv ≫
      pullback.snd seedParameterMorphism (affineCurveChartToParameters t i) =
        Spec.map (CommRingCat.ofHom (curveChartSpecialization t i)) := by
  change (Spec.map (CommRingCat.ofHom (curveChartSeedFiberEquiv t i).toRingHom) ≫
      (pullbackSpecIso ParameterAlgebra ℂ (AffineCurveChart incidencePoint t i)).inv) ≫
        pullback.snd _ _ = _
  rw [Category.assoc, pullbackSpecIso_inv_snd, ← Spec.map_comp]
  rfl

@[reassoc] theorem affineCurveChartSeedFiberIso_inv_fst :
    (affineCurveChartSeedFiberIso t i).inv ≫
      pullback.fst seedParameterMorphism (affineCurveChartToParameters t i) =
        seedAffineCurveChartToComplex t i := by
  change (Spec.map (CommRingCat.ofHom (curveChartSeedFiberEquiv t i).toRingHom) ≫
      (pullbackSpecIso ParameterAlgebra ℂ (AffineCurveChart incidencePoint t i)).inv) ≫
        pullback.fst _ _ = _
  rw [Category.assoc, pullbackSpecIso_inv_fst', ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro c
  exact (curveChartSeedFiberEquiv t i).commutes c

def projectiveCurveChartToParameters :
    (curveCoordinatePatch incidencePoint t i).toScheme ⟶
      Spec (CommRingCat.of ParameterAlgebra) :=
  (curveCoordinatePatch incidencePoint t i).ι ≫ relativeCurveToBase incidencePoint t

theorem curveCoordinateAffineChart_hom_overParameters :
    (curveCoordinateAffineChart incidencePoint t i).hom ≫ affineCurveChartToParameters t i =
      projectiveCurveChartToParameters t i := by
  change (curveCoordinateAffineChart incidencePoint t i).hom ≫
      Spec.map (CommRingCat.ofHom
        (algebraMap ParameterAlgebra (AffineCurveChart incidencePoint t i))) =
    (curveCoordinatePatch incidencePoint t i).ι ≫ relativeCurveToBase incidencePoint t
  rw [← curveCoordinateAffineChart_overBase incidencePoint t i]
  simp only [Iso.hom_inv_id_assoc]

abbrev ProjectiveCurveChartSeedFiber :=
  pullback seedParameterMorphism (projectiveCurveChartToParameters t i)

def projectiveCurveChartFiberToAffineFiber :
    ProjectiveCurveChartSeedFiber t i ≅ AffineCurveChartSeedFiberScheme t i :=
  asIso (pullback.map seedParameterMorphism (projectiveCurveChartToParameters t i)
    seedParameterMorphism (affineCurveChartToParameters t i)
    (𝟙 _) (curveCoordinateAffineChart incidencePoint t i).hom (𝟙 _)
    (by simp) (by simpa using (curveCoordinateAffineChart_hom_overParameters t i).symm))

@[reassoc] theorem projectiveCurveChartFiberToAffineFiber_hom_snd :
    (projectiveCurveChartFiberToAffineFiber t i).hom ≫
      pullback.snd seedParameterMorphism (affineCurveChartToParameters t i) =
        pullback.snd seedParameterMorphism (projectiveCurveChartToParameters t i) ≫
          (curveCoordinateAffineChart incidencePoint t i).hom := by
  simp [projectiveCurveChartFiberToAffineFiber]

@[reassoc] theorem projectiveCurveChartFiberToAffineFiber_hom_fst :
    (projectiveCurveChartFiberToAffineFiber t i).hom ≫
      pullback.fst seedParameterMorphism (affineCurveChartToParameters t i) =
        pullback.fst seedParameterMorphism (projectiveCurveChartToParameters t i) := by
  simp [projectiveCurveChartFiberToAffineFiber]

@[reassoc] theorem projectiveCurveChartFiberToAffineFiber_inv_snd :
    (projectiveCurveChartFiberToAffineFiber t i).inv ≫
      pullback.snd seedParameterMorphism (projectiveCurveChartToParameters t i) =
        pullback.snd seedParameterMorphism (affineCurveChartToParameters t i) ≫
          (curveCoordinateAffineChart incidencePoint t i).inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, projectiveCurveChartFiberToAffineFiber_hom_snd]
  simp

@[reassoc] theorem projectiveCurveChartFiberToAffineFiber_inv_fst :
    (projectiveCurveChartFiberToAffineFiber t i).inv ≫
      pullback.fst seedParameterMorphism (projectiveCurveChartToParameters t i) =
        pullback.fst seedParameterMorphism (affineCurveChartToParameters t i) := by
  rw [Iso.inv_comp_eq]
  exact (projectiveCurveChartFiberToAffineFiber_hom_fst t i).symm

/-- The exact seed pullback of the actual original projective curve
coordinate open, with its literal fixed-vector affine seed equations. -/
def projectiveCurveChartSeedFiberIso :
    ProjectiveCurveChartSeedFiber t i ≅
      Spec (CommRingCat.of (AffineCurveChart (seedPoint (57 : ℂ) Complex.I) t i)) :=
  projectiveCurveChartFiberToAffineFiber t i ≪≫ affineCurveChartSeedFiberIso t i

@[reassoc] theorem projectiveCurveChartSeedFiberIso_inv_snd :
    (projectiveCurveChartSeedFiberIso t i).inv ≫
      pullback.snd seedParameterMorphism (projectiveCurveChartToParameters t i) =
        Spec.map (CommRingCat.ofHom (curveChartSpecialization t i)) ≫
          (curveCoordinateAffineChart incidencePoint t i).inv := by
  change ((affineCurveChartSeedFiberIso t i).inv ≫
      (projectiveCurveChartFiberToAffineFiber t i).inv) ≫
        pullback.snd seedParameterMorphism (projectiveCurveChartToParameters t i) = _
  rw [Category.assoc, projectiveCurveChartFiberToAffineFiber_inv_snd,
    ← Category.assoc, affineCurveChartSeedFiberIso_inv_snd]

@[reassoc] theorem projectiveCurveChartSeedFiberIso_inv_fst :
    (projectiveCurveChartSeedFiberIso t i).inv ≫
      pullback.fst seedParameterMorphism (projectiveCurveChartToParameters t i) =
        seedAffineCurveChartToComplex t i := by
  change ((affineCurveChartSeedFiberIso t i).inv ≫
      (projectiveCurveChartFiberToAffineFiber t i).inv) ≫
        pullback.fst seedParameterMorphism (projectiveCurveChartToParameters t i) = _
  rw [Category.assoc, projectiveCurveChartFiberToAffineFiber_inv_fst,
    affineCurveChartSeedFiberIso_inv_fst]

#print axioms projectiveCurveChartSeedFiberIso
#print axioms projectiveCurveChartSeedFiberIso_inv_snd
#print axioms projectiveCurveChartSeedFiberIso_inv_fst

end CycleQ2RelativeCurveChartFiberScheme
end
