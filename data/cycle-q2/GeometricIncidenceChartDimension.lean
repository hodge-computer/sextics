import Proposal.GeometricIncidenceSmoothSchemeOpens
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent

/-!
# Dimension-two Jacobian patches of the original incidence charts

The four-variable dehomogenized incidence equation ring, localized at one
of its own two-by-two Jacobian determinants, has an explicit submersive
presentation of relative dimension two. This gives the actual standard
smoothness property and the rank of its module of relative differentials.
The spectrum is mapped into the original projective surface using the
existing affine chart, and its original base morphism is smooth of
relative dimension two.

These determinants differentiate the shifted dehomogenized equations.
They are distinct from the normalized five-variable cone determinants
used in goodOpen. Comparing their covers, and hence extending this
dimension statement to the entire previously constructed neighborhood,
is a separate obligation.

Source-only draft: no elaboration or kernel replay has been run.
Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md for
attribution of the geometric strategy and the protected certificate gap.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2IncidenceChartDimension

open MvPolynomial CategoryTheory AlgebraicGeometry
open CycleQ2IncidenceUniversalChart CycleQ2GeometricIncidenceProj
  CycleQ2IncidenceDehomogenizedChart CycleQ2IncidenceSmoothSchemeOpens

variable {S : Type} [CommRing S] [Algebra ℂ S]

/-- The determinant of the actual two shifted affine equations. -/
def chartMinor (y : ParameterIndex → S) (i : Fin 4)
    (q : Fin 2 → Option (Fin 3)) : DehomogenizedRing y i :=
  dehomogenizedMap y i
    (pderiv (q 0) (dehomogenizedEquations y i 0) *
        pderiv (q 1) (dehomogenizedEquations y i 1) -
      pderiv (q 1) (dehomogenizedEquations y i 0) *
        pderiv (q 0) (dehomogenizedEquations y i 1))

def prePresentation (y : ParameterIndex → S) (i : Fin 4)
    (q : Fin 2 → Option (Fin 3)) (hq : Function.Injective q) :
    Algebra.PreSubmersivePresentation S (DehomogenizedRing y i)
      (Option (Fin 3)) (Fin 2) :=
  Algebra.PreSubmersivePresentation.naive
    (v := dehomogenizedEquations y i) q hq

theorem prePresentation_jacobian (y : ParameterIndex → S) (i : Fin 4)
    (q : Fin 2 → Option (Fin 3)) (hq : Function.Injective q) :
    (prePresentation y i q hq).jacobian = chartMinor y i q := by
  rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det,
    Matrix.det_fin_two]
  simp only [Algebra.PreSubmersivePresentation.jacobiMatrix_apply]
  change dehomogenizedMap y i
      (pderiv (q 0) (dehomogenizedEquations y i 0) *
          pderiv (q 1) (dehomogenizedEquations y i 1) -
        pderiv (q 0) (dehomogenizedEquations y i 1) *
          pderiv (q 1) (dehomogenizedEquations y i 0)) = _
  apply congrArg (dehomogenizedMap y i)
  dsimp only [chartMinor]
  rw [mul_comm (pderiv (q 0) (dehomogenizedEquations y i 1))
    (pderiv (q 1) (dehomogenizedEquations y i 0))]

abbrev JacobianPatch (y : ParameterIndex → S) (i : Fin 4)
    (q : Fin 2 → Option (Fin 3)) (hq : Function.Injective q) :=
  Localization.Away (prePresentation y i q hq).jacobian

/-- An explicit presentation, including the one localization variable
and its one relation, of the actual affine Jacobian patch. -/
def presentation (y : ParameterIndex → S) (i : Fin 4)
    (q : Fin 2 → Option (Fin 3)) (hq : Function.Injective q) :
    Algebra.SubmersivePresentation S (JacobianPatch y i q hq)
      (Unit ⊕ Option (Fin 3)) (Unit ⊕ Fin 2) where
  toPreSubmersivePresentation :=
    (Algebra.PreSubmersivePresentation.localizationAway
      (JacobianPatch y i q hq) (prePresentation y i q hq).jacobian).comp
        (prePresentation y i q hq)
  jacobian_isUnit := by
    have hu : IsUnit (algebraMap (DehomogenizedRing y i) (JacobianPatch y i q hq)
        (prePresentation y i q hq).jacobian) :=
      IsLocalization.Away.algebraMap_isUnit _
    simpa only [Algebra.PreSubmersivePresentation.comp_jacobian_eq_jacobian_smul_jacobian,
      Algebra.PreSubmersivePresentation.localizationAway_jacobian, Algebra.smul_def]
      using hu.mul hu

theorem presentation_dimension (y : ParameterIndex → S) (i : Fin 4)
    (q : Fin 2 → Option (Fin 3)) (hq : Function.Injective q) :
    (presentation y i q hq).dimension = 2 := by
  change Nat.card (Unit ⊕ Option (Fin 3)) - Nat.card (Unit ⊕ Fin 2) = 2
  norm_num [Nat.card_eq_fintype_card]

/-- Genuine standard smoothness of relative dimension two, from the
explicit submersive presentation; no smoothness hypothesis is supplied. -/
theorem patch_standardSmooth (y : ParameterIndex → S) (i : Fin 4)
    (q : Fin 2 → Option (Fin 3)) (hq : Function.Injective q) :
    Algebra.IsStandardSmoothOfRelativeDimension 2 S (JacobianPatch y i q hq) :=
  (presentation y i q hq).isStandardSmoothOfRelativeDimension
    (presentation_dimension y i q hq)

theorem patch_differential_rank (y : ParameterIndex → S) (i : Fin 4)
    (q : Fin 2 → Option (Fin 3)) (hq : Function.Injective q)
    [Nontrivial (JacobianPatch y i q hq)] :
    Module.rank (JacobianPatch y i q hq) Ω[JacobianPatch y i q hq⁄S] = 2 := by
  letI := patch_standardSmooth y i q hq
  exact Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential 2

def patchToAffine (y : ParameterIndex → S) (i : Fin 4)
    (q : Fin 2 → Option (Fin 3)) (hq : Function.Injective q) :
    Spec (CommRingCat.of (JacobianPatch y i q hq)) ⟶
      Spec (CommRingCat.of (DehomogenizedRing y i)) :=
  Spec.map (CommRingCat.ofHom
    (algebraMap (DehomogenizedRing y i) (JacobianPatch y i q hq)))

instance patchToAffine_isOpenImmersion (y : ParameterIndex → S) (i : Fin 4)
    (q : Fin 2 → Option (Fin 3)) (hq : Function.Injective q) :
    IsOpenImmersion (patchToAffine y i q hq) :=
  IsOpenImmersion.of_isLocalization (prePresentation y i q hq).jacobian

def patchToSurface (y : ParameterIndex → S) (i : Fin 4)
    (q : Fin 2 → Option (Fin 3)) (hq : Function.Injective q) :
    Spec (CommRingCat.of (JacobianPatch y i q hq)) ⟶ surface y :=
  patchToAffine y i q hq ≫ affineChartToSurface y i

instance patchToSurface_isOpenImmersion (y : ParameterIndex → S) (i : Fin 4)
    (q : Fin 2 → Option (Fin 3)) (hq : Function.Injective q) :
    IsOpenImmersion (patchToSurface y i q hq) := by
  dsimp only [patchToSurface]
  infer_instance

theorem patchToSurface_overBase (y : ParameterIndex → S) (i : Fin 4)
    (q : Fin 2 → Option (Fin 3)) (hq : Function.Injective q) :
    patchToSurface y i q hq ≫ surfaceToBase y =
      Spec.map (CommRingCat.ofHom (algebraMap S (JacobianPatch y i q hq))) := by
  rw [patchToSurface, Category.assoc, affineChartToSurface_overBase,
    patchToAffine, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro c
  exact (IsScalarTower.algebraMap_apply S (DehomogenizedRing y i)
    (JacobianPatch y i q hq) c).symm

/-- This is the original base map of an actual open subscheme of the
original incidence surface, with its relative dimension now specified. -/
theorem patchToSurface_smoothOfRelativeDimension (y : ParameterIndex → S) (i : Fin 4)
    (q : Fin 2 → Option (Fin 3)) (hq : Function.Injective q) :
    AlgebraicGeometry.SmoothOfRelativeDimension 2
      (patchToSurface y i q hq ≫ surfaceToBase y) := by
  rw [patchToSurface_overBase]
  apply (HasRingHomProperty.Spec_iff
    (P := @AlgebraicGeometry.SmoothOfRelativeDimension 2)).mpr
  apply RingHom.locally_of (RingHom.isStandardSmoothOfRelativeDimension_respectsIso (n := 2))
  exact (RingHom.isStandardSmoothOfRelativeDimension_algebraMap 2).mpr
    (patch_standardSmooth y i q hq)

end CycleQ2IncidenceChartDimension

end

#print axioms CycleQ2IncidenceChartDimension.patch_standardSmooth
#print axioms CycleQ2IncidenceChartDimension.patch_differential_rank
#print axioms CycleQ2IncidenceChartDimension.patchToSurface_overBase
#print axioms CycleQ2IncidenceChartDimension.patchToSurface_smoothOfRelativeDimension
